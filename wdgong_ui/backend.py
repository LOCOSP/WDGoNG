"""Real ESP32 / GPS / loot backend for the WatchDogsGo raylib UI.

Reuses the renderer-agnostic managers from the OG game package `watchdogs`
(serial_manager, gps_manager, network_manager, loot_manager, config) so the new
UI drives the exact same firmware protocol and loot persistence as the pyxel app.

Degrades gracefully:
  - no `watchdogs` package importable  -> ok=False, UI runs in pure-demo mode
  - no ESP32 attached                  -> connected=False, loot/GPS still work
  - loot dir not writable (non-sudo)   -> existing loot_db.json still imported

Env overrides:
  WDGO_APP_DIR  game dir that holds watchdogs/ and loot/ (import source)
  WDGO_PORT     force an ESP32 serial device instead of auto-detect
"""

import csv
import json
import os
import re
import sys
import threading
import time
from concurrent.futures import CancelledError
from pathlib import Path
from urllib.parse import parse_qs

# ---------------------------------------------------------------------------
# Locate the OG game package + loot root, then import the reusable managers
# ---------------------------------------------------------------------------

def _locate_repo() -> Path | None:
    env = os.environ.get("WDGO_APP_DIR")
    cands = []
    if env:
        cands.append(Path(env))
    here = Path(__file__).resolve().parent          # wdgong_ui/
    cands += [
        here.parent,                                 # <repo>/ (wdgong_ui lives in repo)
    ]
    for c in cands:
        try:
            if (c / "watchdogs" / "serial_manager.py").is_file():
                return c
        except OSError:
            continue
    return None

# Rank ladder (xp_threshold, title) — mirrors app.py LEVEL_TABLE
LEVEL_TABLE = [
    (0, "NOOB"), (100, "SCRIPT_KIDDIE"), (500, "SKIDDIE+"), (1500, "WANNABE"),
    (3000, "PACKET_MONKEY"), (6000, "WARDRIVER"), (10000, "HACKER"), (20000, "NETRUNNER"),
    (35000, "PHREAKER"), (50000, "EXPLOIT_DEV"), (75000, "ELITE"), (100000, "SHADOW_OPS"),
    (150000, "GHOST"), (250000, "ZERO_DAY"), (400000, "APT_AGENT"), (600000, "CYBER_DEMON"),
    (1000000, "CYBER_GOD"), (2500000, "DIGITAL_DEITY"), (5000000, "MATRIX_BREAKER"),
    (10000000, "FINAL_BOSS"),
]
# badge id -> short HUD label (mirrors app.py _BADGE_HUD)
BADGE_HUD = {
    "flipper": "FLP", "wardriver": "WDR", "meshcore": "MSH", "handshake_hunter": "HS",
    "wpasec_uploader": "WPA", "evil_twin": "ET", "skywatch": "ADB", "iot_hunter": "433",
    "emergency": "SVC",
}

import re as _re
_BLE_RE = _re.compile(r"^([0-9A-Fa-f]{2}(?::[0-9A-Fa-f]{2}){5})\s+(-?\d+)\s*(.*)$")
# firmware list format: "1. 02:00:00:00:00:01  RSSI: -80 dBm"  [optional trailing name/tag]
_BLE_LIST_RE = _re.compile(
    r"^\s*\d+\.\s+([0-9A-Fa-f]{2}(?::[0-9A-Fa-f]{2}){5})\s+RSSI:\s*(-?\d+)\s*dBm\s*(.*)$")
_AIRTAG_COUNT_RE = _re.compile(r"^\s*(\d+)\s*,\s*(\d+)\s*$")
# firmware summary: "Summary: 10 AirTags, 3 SmartTags, 153 total devices"
_BLE_SUMMARY_RE = _re.compile(
    r"Summary:\s*(\d+)\s*AirTags?,\s*(\d+)\s*SmartTags?", _re.IGNORECASE)

# LoRa mesh settings (stack + per-stack region/preset/name), one per install folder.
MESH_SETTINGS_NAME = ".watchdogs_mesh.json"

REPO = _locate_repo()
HAVE_BACKEND = False
IMPORT_ERROR = ""

if REPO is not None:
    if str(REPO) not in sys.path:
        sys.path.insert(0, str(REPO))
    try:
        from watchdogs.app_state import AppState, Network
        from watchdogs.serial_manager import SerialManager, detect_esp32_port
        from watchdogs.network_manager import NetworkManager
        from watchdogs.gps_manager import GpsManager
        from watchdogs.loot_manager import LootManager
        from watchdogs.portals import get_all_portals, upload_html_to_esp32
        from watchdogs import config as CFG
        HAVE_BACKEND = True
    except Exception as exc:                         # pragma: no cover
        IMPORT_ERROR = f"{type(exc).__name__}: {exc}"
else:
    IMPORT_ERROR = "watchdogs package not found"


def _snapshot(coll):
    """Thread-safe snapshot of a dict's values (or a list) that another thread may
    be mutating concurrently — retry past the 'changed size during iteration'
    RuntimeError instead of letting it crash the render loop."""
    for _ in range(4):
        try:
            return list(coll.values()) if isinstance(coll, dict) else list(coll)
        except RuntimeError:
            continue
    return []


class Backend:
    """Owns the shared AppState + managers and exposes simple data for the UI."""

    # Makes the check-and-set of _mesh_switching atomic, so a stack switch and a
    # region retune of the shared SX1262 can never run at the same time.
    _MESH_GUARD = threading.Lock()

    def __init__(self) -> None:
        self.ok = HAVE_BACKEND
        self.app_dir = str(REPO) if REPO else os.getcwd()
        self.connected = False          # ESP32 serial open
        self._reconnect_t = 0.0         # last background serial-reconnect attempt
        self.esp_ready = False          # firmware responded to probe
        self.gps_on = False             # GPS port open
        self._sdr_rail = False          # AIO SDR power rail (RTL dongle) on/off
        self.term: list[tuple[str, str, str]] = []   # (hh:mm:ss, text, kind)
        self._mode = "idle"             # routing for incoming serial: scan|sniffer|idle
        self._last_recalc = 0.0
        self._rabbits: list = []         # WDGWars white-rabbit targets (enriched)
        self._rabbits_t = 0.0            # last /api/rabbits fetch time
        self._rabbits_fetching = False
        self._rabbits_seen = False       # printed the ranged one-time note yet
        self._rabbits_nofix_noted = False  # printed the "enable GPS" note yet
        self._pair_active = False        # device-pair flow running
        self._pair_attempt = 0           # monotonic id: a worker only owns state while current
        self._pair_status = ""           # ""|requesting|waiting|done|expired|error
        self._pair_code = ""             # short code the player types on the portal
        self._pair_poll = ""             # poll secret
        self._pair_user = ""             # username once linked
        self._pair_expires = 0.0
        self._gs = {}                    # /api/game-state: me/uconsole_rank/team/contracts
        self._gs_decay = []              # decay_nearby, kept across null responses
        self._gs_t = 0.0
        self._gs_fetching = False
        self._gs_seen = False
        self._profile_pulled = False     # pulled /api/me (identity + server badges) yet
        self._status = ""               # last action / status string for the UI
        self._db_totals: dict = {}
        self._db_xp = 0
        self._app_dir = self.app_dir
        self.captures: list[str] = []   # parsed Evil Twin / portal credentials
        self._attack_lock = threading.Lock()
        self._attack_cancel = None      # each worker owns a distinct, one-use event
        self._attack_worker = None
        self._mgrs: dict = {}           # lazily-built host-side managers
        self._scan_done_pulse = False   # one-shot WiFi-scan-finished flag for UI
        self._wardrive = None           # "scan_networks"/"scan_bt" => host-loop wardriving (legacy)
        self._wardrive_serial = None    # "wifi"/"bt"/"all" => firmware serial-wardrive streaming
        self._wd_seen = set()           # MACs seen this loot session (live new-detection + XP gate)
        # radios: ESP32 (serial) and/or a host Wi-Fi card (AC1200). The matrix routes
        # each Wi-Fi function to a radio; with one radio present it all resolves to it.
        try:
            from watchdogs import radio_detect
            from watchdogs.radio_arbiter import RadioArbiter
            self._radio = RadioArbiter(radio_detect.detect())
            self._radio_boot_msg = "radio: " + radio_detect.summary(self._radio.detect)
        except Exception:
            self._radio = None
            self._radio_boot_msg = ""
        self._host_wifi = None          # watchdogs.host_wifi.HostWifi, built on demand
        self._cluster = False           # cluster-core serial mode active
        self._cluster_nodes = {}        # mac -> node telemetry dict (from CNODE lines)
        self._cluster_joins = []        # pending JOIN MACs awaiting operator ACCEPT
        self._cluster_recs = 0          # fleet records (CWD) ingested this run
        self._cluster_lock = threading.Lock()   # guards node dict mutate/prune vs render
        self._loot_lock = threading.RLock()      # serialises session create + all loot-db saves
        self._loot_frozen = False                # True while a restore replaces loot/ (no new session)
        self._gps_starting = False               # guard: one background GPS bring-up at a time
        self._wigle_lock = threading.Lock()      # one WiGLE upload at a time (manual + cluster auto)
        self._gps_fix_mono = 0.0                 # monotonic time of last valid GPS fix (staleness)
        self._GPS_STALE_SECS = 8.0               # invalidate a fix with no fresh NMEA for this long
        self._cluster_rec_marks = []    # (t, total) ring for fleet rec/min rate calc
        self._cluster_wifi_seen = set() # unique WiFi BSSIDs seen by the fleet this run
        self._cluster_ble_seen = set()  # unique BLE MACs seen by the fleet this run
        self._cluster_ble_random = set()  # subset: locally-administered (randomised) BLE MACs
        self._cluster_sim_stop = None   # threading.Event when the demo simulator runs
        self._cluster_demo = False      # WDGO_CLUSTER_SIM: drive the UI only, never
                                        # touch real loot / XP / badges (no data pollution)
        # Real ENOW bridge (projectZero bridge mode on the game's own ESP32): the
        # host-side brain lives here and talks over the same serial. Gated behind
        # WDGO_CLUSTER_BRIDGE so normal play / the demo are unaffected until the
        # firmware ships. See cluster_brain / cluster_link / cluster_enow.
        self._cluster_bridge = False
        self._cluster_link = None       # cluster_link.ClusterLink when the bridge runs
        self._cluster_brain = None      # cluster_brain.ClusterBrain when the bridge runs
        self._cluster_bridge_stop = None  # threading.Event for the tick thread
        # A node unheard longer than this is shown STALE; longer still, retired from
        # the fleet view. A real node reports only once per ~20 s CAPTURE cycle, so
        # 12 s/45 s showed healthy nodes STALE and retired them after two missed
        # reports -> the fleet flickered and vanished. Match the firmware's 90 s
        # ENOW_NODE_TIMEOUT. The demo simulator runs on a faster clock and overrides
        # these at start.
        self._cluster_stale_s = 30.0
        self._cluster_retire_s = 90.0
        self._wardrive_done_t = 0.0     # when the last wardrive scan finished (rescan timer)
        self._WARDRIVE_INTERVAL = 2.0   # seconds between auto-repeat scans (like OG)
        self._xp = 0                    # live XP
        self._xp_dirty = False
        self._db_badges: set = set()
        self._badges: set = set()
        self._last_xp_save = 0.0
        self.mc_log: list = []          # MeshCore chat: (dir, text, kind)
        self.wd_log: list = []          # WDGWars chat: (dir, text, kind)
        self._hwid_cache = None          # device fingerprint, computed lazily
        self._wd = None                 # ReticulumManager (lazy)
        self._wl = None                 # WhitelistManager (lazy)
        # per-screen logs / state for the ported companion screens
        self.flipper_log: list = []
        self.subghz_log: list = []
        self.watch_log: list = []
        self.mitm_state = "idle"        # idle|scanning|running
        self.game_log: list = []
        self._game_remote = ""
        self._game_busy = False
        self._game_update = False        # a newer version is on GitHub (origin)
        self._game_latest = ""           # subject of the newest remote commit
        self._game_changelog = []        # subjects of all new remote commits (newest first)
        self._game_check_t = 0.0         # last update-check time (for periodic re-check)
        self._game_restart = False       # set after a successful install -> UI re-execs
        self._backup_busy = False        # export/import in progress
        self._backup_path = ""           # last backup file written
        self._fw_remote = ""            # latest firmware version on GitHub (stripped 'v')
        self._fw_update = False         # True when ESP firmware < latest release
        self._fw_version = ""           # ESP firmware version (parsed from serial)
        self._fw_check_t = 0.0          # last firmware-update check time
        self._stopping = False          # set in close(): background loops bail out
        self.ble_devices: list = []     # parsed BLE scan results (mac,rssi,name,tag)
        self.airtags = 0
        self.smarttags = 0
        self.sniffer_aps: list = []
        self._loot_points_cache: list = []
        self._loot_points_ts = 0.0
        self._loot_points_building = False    # background loot-points refresh in flight
        self._watch_scan_busy = False         # one PipBoy BT scan at a time (runs off UI loop)
        self.battery_pct = -1
        self.batt_mv = 0                 # battery voltage (mV) - the honest low-batt signal
        self._batt_warned = False        # hysteresis latch for the low-voltage warning
        self._bat_ts = 0.0
        self.mc_bubble = None           # (text, expire_time) for the radio toast
        self._notify_pulse = None       # one-shot sound cue consumed by the UI thread
        self._pwn_seen = set()          # BSSIDs already announced as cracked this session
        self._mc_nodes = {}             # node_id -> {lat,lon,name,type} for map icons
        self._mt_nodes = {}             # Meshtastic node_id -> {lat,lon,name,type}
        self._mesh_switching = False    # guard: one LoRa-stack switch at a time
        # In-memory mesh defaults BEFORE the demo early-return below, so the LoRa
        # Mesh screen (mesh_stack()/region/preset) works in demo mode too. The full
        # backend path overlays persisted settings via _load_mesh_settings().
        self._mesh = {"stack": "", "mc_region": "eu_uk_default",
                      "mt_region": "EU_868", "mt_preset": "LONG_FAST", "mt_name": "",
                      "last_stack": "", "cfg_mc": False, "cfg_mt": False}
        self.state = None
        self.serial = None
        self.gps = None
        self.net = None
        self.loot = None
        if not HAVE_BACKEND:
            self._term(f"backend offline ({IMPORT_ERROR}) - demo mode", "warn")
            from collections import namedtuple
            N = namedtuple("N", "index ssid vendor bssid channel auth rssi band")
            self._demo_nets = [
                N("1", "HomeNet_5G", "", "AA:BB:CC:11:22:01", "36", "WPA2", "-42", "5"),
                N("2", "Linksys_2A", "", "AA:BB:CC:11:22:02", "1",  "WPA2", "-67", "2.4"),
                N("3", "FREE_WIFI",  "", "AA:BB:CC:11:22:03", "6",  "OPEN", "-55", "2.4"),
                N("4", "corp-secure","", "AA:BB:CC:11:22:04", "11", "WPA3", "-71", "2.4"),
                N("5", "NETGEAR_9c", "", "AA:BB:CC:11:22:05", "6",  "WPA2", "-60", "2.4"),
            ]
            self._xp = 245605
            self._badges = {"wardriver", "handshake_hunter", "evil_twin", "meshcore",
                            "wpasec_uploader", "flipper", "skywatch", "emergency"}
            self._demo_prox = [
                {"label": "WDG-A1B2", "mutual": True, "state": 3, "trend": 1, "bar": 16, "ema": -58, "rssi": -58},
                {"label": "WDG-FF01", "mutual": False, "state": 2, "trend": 0, "bar": 9, "ema": -74},
                {"label": "WDG-9C3D", "mutual": False, "state": 1, "trend": -1, "bar": 4, "ema": -86},
            ]
            return
        self.state = AppState()
        try:
            self.gps = GpsManager()
        except Exception:
            self.gps = None
        self.net = NetworkManager(self.state)
        # Import the loot database for display WITHOUT creating a write session.
        # LootManager's constructor makes a new loot/<ts>/ dir every launch, so
        # we read loot_db.json directly here and only spin up a real LootManager
        # (write session) lazily, when an actual capture command is fired.
        self._app_dir = os.environ.get("WDGO_APP_DIR", self.app_dir)
        self._load_mesh_settings()      # persisted LoRa mesh stack + region/preset
        self._fix_db_adsb(self._app_dir)        # one-time: ADS-B totals = aircraft, not rows
        self._db_totals, self._db_xp, self._db_badges = self._read_db(self._app_dir)
        self._xp = self._db_xp          # live XP (base + gains this session)
        self._xp_dirty = False
        self._badges = set(self._db_badges)
        self._last_xp_save = time.time()
        t = self._db_totals
        self._term(
            "loot imported - %d sessions, %d nets, %d HS, %d pwd (read-only)"
            % (t.get("sessions", 0), t.get("wardriving", 0),
               t.get("hc22000", 0) or t.get("hccapx", 0), t.get("passwords", 0)),
            "ok",
        )
        # bootstrap XP + badges from existing loot (like the OG), in-memory
        if self._xp == 0:
            self._xp = (t.get("wardriving", 0) * 15 + t.get("bt_devices", 0) * 10
                        + t.get("pcap", 0) * 200 + t.get("et_captures", 0) * 150
                        + t.get("passwords", 0) * 150 + t.get("cracked", 0) * 150)
        for cond, badge in ((t.get("wardriving") or t.get("bt_devices"), "wardriver"),
                            (t.get("pcap") or t.get("hccapx"), "handshake_hunter"),
                            (t.get("et_captures") or t.get("passwords"), "evil_twin"),
                            (t.get("mc_nodes") or t.get("mc_messages"), "meshcore"),
                            (t.get("cracked"), "wpasec_uploader")):
            if cond:
                self._badges.add(badge)
        # Snapshot the AIO rail state at launch, BEFORE the game powers anything
        # (e.g. the USB rail), so the RADIO indicator is correct AND the quit
        # prompt can offer "restore pre-launch state". Cheap, once.
        self._entry_rails = {}
        try:
            aio = self._mgr("aio")
            if aio and aio.is_installed():
                st = aio.get_status() or {}
                # Only REAL readings: a pin pinctrl could not read (None) or did
                # not report is left out, so 'restore' never drives it blindly.
                self._entry_rails = {k: st[k] for k in ("gps", "lora", "sdr", "usb")
                                     if isinstance(st.get(k), bool)}
                self._sdr_rail = self._entry_rails.get("sdr", False)
        except Exception:
            pass
        # OTA: check GitHub (origin) for a newer game version at launch (async)
        try:
            self.check_game_update()
        except Exception:
            pass
        # consolidate the chat identity under loot/ so one folder holds ALL user data
        try:
            self._reticulum_configdir()
        except Exception:
            pass
        # WDGWars proximity runs as a background service from launch (default on)
        try:
            self.prox_autostart()
        except Exception:
            pass

    @staticmethod
    def _fix_db_adsb(app_dir: str) -> None:
        """Older loot_db.json files hold ADS-B per session as rows of the track log.
        Recount ONLY that field as distinct aircraft (ICAO), recompute the totals,
        mark the file, write it atomically. XP, badges and all other counters are
        left exactly as they are. Runs at startup, before anything else writes the DB."""
        p = Path(app_dir) / "loot" / "loot_db.json"
        try:
            with open(p, "r", encoding="utf-8") as fh:
                db = json.load(fh)
        except Exception:
            return
        if not isinstance(db, dict) or db.get("adsb_unique") or not isinstance(db.get("sessions"), dict):
            return
        try:
            from watchdogs.loot_manager import LootManager
            lm = LootManager.__new__(LootManager)
            lm._base = p.parent
            lm._db_path = p
            lm._fix_adsb_counts(db)                 # recount + recalc totals + flag + atomic save
        except Exception:
            pass

    @staticmethod
    def _read_db(app_dir: str) -> tuple[dict, int, set]:
        """Read loot/loot_db.json totals + xp + badges without touching the dir."""
        try:
            p = Path(app_dir) / "loot" / "loot_db.json"
            with open(p, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            totals = dict(data.get("totals", {}) or {})
            totals.setdefault("sessions", len(data.get("sessions", {})))
            try:
                cp = Path(app_dir) / "loot" / "passwords" / "wpasec_cracked.json"
                if cp.is_file():
                    with open(cp, encoding="utf-8") as cfh:
                        totals["cracked"] = int(json.load(cfh).get("count", 0))
            except Exception:
                pass
            return totals, int(data.get("xp", 0)), set(data.get("badges", []))
        except Exception:
            return {}, 0, set()

    # ------------------------------------------------------------------
    # XP / level / badges
    # ------------------------------------------------------------------

    def gain_xp(self, amount: int) -> None:
        if amount <= 0:
            return
        self._xp += amount
        self._xp_dirty = True

    def level(self) -> int:
        lvl = 1
        for i, (thr, _) in enumerate(LEVEL_TABLE):
            if self._xp >= thr:
                lvl = i + 1
        return lvl

    def level_title(self) -> str:
        title = LEVEL_TABLE[0][1]
        for thr, t in LEVEL_TABLE:
            if self._xp >= thr:
                title = t
        return title

    def xp_bar(self) -> tuple[int, int]:
        """(xp_in_level, span_to_next) for a progress bar."""
        cur_thr = 0; nxt_thr = None
        for thr, _ in LEVEL_TABLE:
            if self._xp >= thr:
                cur_thr = thr
            elif nxt_thr is None:
                nxt_thr = thr
        if nxt_thr is None:
            return (1, 1)
        return (self._xp - cur_thr, max(1, nxt_thr - cur_thr))

    def badges(self) -> set:
        return set(self._badges)

    def earn_badge(self, badge: str) -> None:
        if badge in self._badges:
            return
        self._badges.add(badge)
        self._term("[BADGE] earned: " + BADGE_HUD.get(badge, badge), "ok")
        self.set_status("BADGE: " + BADGE_HUD.get(badge, badge))
        if self.loot:
            try:
                with self._loot_lock:            # serialise with other loot-db writers
                    self.loot.save_badge(badge)
            except Exception:
                pass
        else:
            # Earned before any write session exists: persist to the top-level
            # loot db so the badge is not lost on quit.
            self._persist_sessionless(badge=badge)

    # ------------------------------------------------------------------
    # WDGWars portal sync (community server) — NG's headless uploader
    # ------------------------------------------------------------------
    def _portal_sync(self):
        """Lazily build the PortalSync helper. None if it can't be created."""
        if getattr(self, "_portal", None) is not None:
            return self._portal
        try:
            from pathlib import Path as _P
            try:
                from portal_sync import PortalSync   # game runs wdgong_ui/main.py as a script
            except ImportError:
                from wdgong_ui.portal_sync import PortalSync  # imported as a package
            ver = self.game_version()
            if not (ver and ver[0].isdigit()):
                ver = "0.0.0"
            loot_base = (_P(self.loot._base) if self.loot
                         else _P(self._app_dir) / "loot")
            self._portal = PortalSync(
                version=ver,
                loot_base=loot_base,
                state_path=_P(self._app_dir) / ".portal_sync_state.json",
                active_session=lambda: (_P(self.loot.session_path).name
                                        if self.loot else ""),
                log=self._portal_log,
                get_game_badges=self.badges,
                apply_badge=self.earn_badge,
                get_xp=lambda: self._xp,
                node_tag=self._hw_id(),
            )
        except Exception as exc:
            self._term(f"WDGWars sync unavailable: {exc}", "warn")
            self._portal = None
        return self._portal

    def _portal_log(self, msg, level="raw") -> None:
        """Portal messages go to the game terminal AND to portal_sync.log in the game
        folder (kept under ~256 KB), so an upload error can be read back later."""
        self._term(msg, level)
        try:
            path = os.path.join(self._app_dir, "portal_sync.log")
            if os.path.exists(path) and os.path.getsize(path) > 256 * 1024:
                os.replace(path, path + ".1")
            with open(path, "a", encoding="utf-8") as f:
                f.write("%s [%s] %s\n" % (time.strftime("%Y-%m-%d %H:%M:%S"), level, msg))
        except Exception:
            pass

    def wdgwars_sync(self) -> None:
        """Upload pending loot sessions to the WDGWars portal (background thread)."""
        p = self._portal_sync()
        if p is not None:
            p.sync(all_sessions=True)

    def wdgwars_profile(self) -> None:
        """Fetch /api/me and print the player's portal identity/stats."""
        p = self._portal_sync()
        if p is not None:
            p.show_profile()

    # ------------------------------------------------------------------
    # WDGWars device pairing (/api/device-pair) — code instead of 64-hex key
    # ------------------------------------------------------------------
    def pair_start(self) -> None:
        if self._pair_active:
            return
        p = self._portal_sync()
        if p is None:
            self._term("WDGWars pairing unavailable", "warn")
            return
        self._pair_active = True
        self._pair_attempt += 1          # per-attempt id: ignore results from old/cancelled runs
        attempt = self._pair_attempt
        self._pair_status = "requesting"
        self._pair_code = ""
        self._pair_user = ""
        import threading as _th
        _th.Thread(target=self._pair_worker, args=(p, attempt), daemon=True).start()

    def _pair_worker(self, p, attempt) -> None:
        # This worker only owns the shared pairing state while it is the current
        # attempt. A cancel (ESC) or a quick re-open bumps _pair_attempt, so a late
        # network result from a stale run can neither adopt a key nor clobber the
        # new attempt's fields.
        def current() -> bool:
            return self._pair_active and self._pair_attempt == attempt
        try:
            r = p.request_pair()
            if not current():
                return
            if not r or not r.get("code"):
                self._pair_status = "error"
                return
            self._pair_code = r["code"]
            self._pair_poll = r.get("poll", "")
            self._pair_expires = time.time() + int(r.get("expires_in", 600))
            self._pair_status = "waiting"
            self._term("[PAIR] code %s — enter it at wdgwars.pl/profile → API keys"
                       % self._pair_code, "tx")
            while current() and time.time() < self._pair_expires:
                time.sleep(3)
                if not current():
                    return
                res = p.poll_pair(self._pair_code, self._pair_poll)
                if not current():        # cancelled/superseded during the network call
                    return
                if res.get("api_key"):
                    # Success only once the key is durably saved (adopt_api_key
                    # returns True); never log the key or an error that may hold it.
                    try:
                        saved = p.adopt_api_key(res["api_key"]) is True
                    except Exception as exc:
                        saved = False
                        self._term("[PAIR] key save raised %s" % type(exc).__name__, "warn")
                    if not current():    # cancelled/superseded while saving
                        return
                    if not saved:
                        self._pair_status = "error"
                        self._term("[PAIR] could not save the key to secrets.conf - "
                                   "pairing will not survive a restart", "err")
                        self.set_status("WDGWars: could not save the key")
                        return
                    self._pair_user = res.get("username", "")
                    self._pair_status = "done"
                    self._term("[PAIR] linked as %s" % (self._pair_user or "?"), "ok")
                    self.set_status("WDGWars: paired")
                    return
                if res.get("error") == "bad_request":
                    self._pair_status = "expired"
                    return
            if current() and self._pair_status == "waiting":
                self._pair_status = "expired"
        except Exception:
            if current():
                self._pair_status = "error"
        finally:
            if self._pair_attempt == attempt:
                self._pair_active = False

    def pair_cancel(self) -> None:
        self._pair_active = False
        self._pair_attempt += 1          # invalidate any in-flight pairing worker

    def pair_status(self) -> str:
        return self._pair_status

    def pair_code(self) -> str:
        return self._pair_code

    def pair_user(self) -> str:
        return self._pair_user

    def pair_seconds_left(self) -> int:
        if self._pair_status != "waiting":
            return 0
        return max(0, int(self._pair_expires - time.time()))

    # ------------------------------------------------------------------
    # WDGWars "Chase the White Rabbit" targets (/api/rabbits)
    # ------------------------------------------------------------------
    _COMPASS = ["N", "NE", "E", "SE", "S", "SW", "W", "NW"]

    @staticmethod
    def _haversine_km(lat1, lon1, lat2, lon2):
        import math
        p1, p2 = math.radians(lat1), math.radians(lat2)
        dphi = math.radians(lat2 - lat1)
        dlmb = math.radians(lon2 - lon1)
        a = (math.sin(dphi / 2) ** 2
             + math.cos(p1) * math.cos(p2) * math.sin(dlmb / 2) ** 2)
        return 2 * 6371.0 * math.asin(min(1.0, math.sqrt(a)))

    @staticmethod
    def _bearing(lat1, lon1, lat2, lon2):
        import math
        p1, p2 = math.radians(lat1), math.radians(lat2)
        dl = math.radians(lon2 - lon1)
        y = math.sin(dl) * math.cos(p2)
        x = math.cos(p1) * math.sin(p2) - math.sin(p1) * math.cos(p2) * math.cos(dl)
        return (math.degrees(math.atan2(y, x)) + 360) % 360

    def _enrich_rabbits(self, rabbits) -> None:
        """Add dist_km + compass computed from the device GPS (not the server's
        'area'), then sort nearest-first."""
        st = self.state
        has_fix = bool(getattr(st, "gps_fix_valid", False))
        plat = getattr(st, "gps_latitude", 0.0) or 0.0
        plon = getattr(st, "gps_longitude", 0.0) or 0.0
        for r in rabbits:
            if has_fix and (plat or plon):
                d = self._haversine_km(plat, plon, r["lat"], r["lon"])
                b = self._bearing(plat, plon, r["lat"], r["lon"])
                r["dist_km"] = d
                r["compass"] = self._COMPASS[int((b + 22.5) % 360 // 45)]
            else:
                r["dist_km"] = None
                r["compass"] = None
        rabbits.sort(key=lambda x: (x.get("dist_km") is None, x.get("dist_km") or 0.0))

    def _fetch_rabbits_worker(self, p) -> None:
        try:
            out = []
            for r in p.fetch_rabbits():
                lat = r.get("lat")
                lon = r.get("lng", r.get("lon"))     # server uses 'lng'
                if lat is None or lon is None:
                    continue
                try:
                    flat = float(lat)
                    flon = float(lon)
                except (TypeError, ValueError):
                    continue
                # drop null-island / out-of-range placeholders defensively
                if (flat == 0.0 and flon == 0.0) or not (
                        -90 <= flat <= 90 and -180 <= flon <= 180):
                    continue
                d = dict(r)
                d["lat"] = flat
                d["lon"] = flon
                out.append(d)
            self._enrich_rabbits(out)
            self._rabbits = out
            # Honest one-time note. /api/rabbits returns a wide set (dozens), NOT
            # only close ones — so don't call them "nearby". Lead with the real
            # nearest distance and how many actually fall inside the map view
            # (~12 km at the widest REGION zoom); the rest are off-map.
            if out:
                near = out[0]
                dk = near.get("dist_km")
                if dk is None:
                    if not self._rabbits_nofix_noted:
                        self._rabbits_nofix_noted = True
                        self._term("[RABBIT] %d portal target(s) — enable GPS to "
                                   "range them" % len(out), "tx")
                elif not self._rabbits_seen:
                    self._rabbits_seen = True
                    in_range = sum(1 for r in out
                                   if (r.get("dist_km") or 1e9) <= 12.0)
                    where = ("%d in map range" % in_range if in_range
                             else "none in view")
                    self._term("[RABBIT] %d portal target(s); nearest %.1f km %s; %s"
                               % (len(out), dk, near.get("compass") or "", where),
                               "tx")
        except Exception:
            pass
        finally:
            self._rabbits_fetching = False

    def rabbits(self) -> list:
        """Nearest-first white-rabbit targets (each has lat/lon/need/state and,
        when GPS has a fix, dist_km + compass)."""
        return self._rabbits

    # ------------------------------------------------------------------
    # WDGWars game-state (/api/game-state) — rank, team, decay tiles, contracts
    # ------------------------------------------------------------------
    def _fetch_gs_worker(self, p) -> None:
        try:
            st = self.state
            fix = bool(getattr(st, "gps_fix_valid", False))
            lat = getattr(st, "gps_latitude", 0.0) if fix else None
            lon = getattr(st, "gps_longitude", 0.0) if fix else None
            res = p.fetch_game_state(lat, lon)
            if not res:
                return
            self._gs = res
            decay = res.get("decay_nearby")
            if decay is not None:        # null = server hasn't computed it -> keep last
                self._gs_decay = decay
            if not self._gs_seen:
                self._gs_seen = True
                me = res.get("me") or {}
                rk = res.get("uconsole_rank") or {}
                pos = rk.get("position")
                where = "#%d of %d" % (pos, rk.get("of", 0)) if pos else "unranked yet"
                self._term("[WDGWars] %s lvl %s — uConsole rank %s"
                           % (me.get("username", "?"), me.get("level", "?"), where), "tx")
        except Exception:
            pass
        finally:
            self._gs_fetching = False

    def game_state(self) -> dict:
        return self._gs

    def gs_me(self) -> dict:
        return self._gs.get("me") or {}

    def gs_rank(self) -> dict:
        return self._gs.get("uconsole_rank") or {}

    def gs_contracts(self) -> list:
        return self._gs.get("contracts") or []

    def gs_decay(self) -> list:
        return self._gs_decay

    def _persist_sessionless(self, xp=None, badge=None) -> None:
        """Write xp/badges straight to loot/loot_db.json when there is no write
        session yet, so progress earned before the first capture (e.g. 50 XP on the
        historical-points map) survives a quit. A LootManager built later loads this
        file in its constructor, so the state reconciles. Atomic (tmp + fsync + rename)."""
        if not HAVE_BACKEND or getattr(self, "_loot_frozen", False):
            return                               # a restore is replacing loot/ - don't write over it
        p = Path(self._app_dir) / "loot" / "loot_db.json"
        try:
            with self._loot_lock:
                try:
                    with open(p, "r", encoding="utf-8") as fh:
                        db = json.load(fh)
                    if not isinstance(db, dict):
                        db = {}
                except Exception:
                    db = {}
                changed = False
                if xp is not None and db.get("xp") != int(xp):
                    db["xp"] = int(xp); changed = True
                if badge is not None:
                    badges = set(db.get("badges", []))
                    if badge not in badges:
                        badges.add(badge); db["badges"] = sorted(badges); changed = True
                if not changed:
                    return
                p.parent.mkdir(parents=True, exist_ok=True)
                tmp = p.with_suffix(".tmp")
                with open(tmp, "w", encoding="utf-8") as fh:
                    json.dump(db, fh)
                    fh.flush(); os.fsync(fh.fileno())
                tmp.replace(p)
        except Exception:
            pass

    def _save_xp(self) -> None:
        if not self._xp_dirty:
            return
        if self.loot:
            try:
                with self._loot_lock:            # serialise with other loot-db writers
                    self.loot.save_xp(self._xp)
                self._xp_dirty = False
            except Exception:
                pass
        else:
            # No write session yet: persist to the top-level loot db so a quit
            # right after a map/XP gain does not lose it.
            self._persist_sessionless(xp=self._xp)
            self._xp_dirty = False

    def ensure_session(self) -> None:
        """Lazily start a real loot write-session (first actual capture only).

        The whole check-create-publish runs under one lock so two first events
        (e.g. a MeshCore message and a UI scan start) can't each build a manager
        for the same second-resolution directory and orphan one. A restore in
        progress blocks session creation so the old manager can't write its db
        over the just-restored data."""
        if self.loot is not None or not HAVE_BACKEND:
            return
        if getattr(self, "_loot_frozen", False):
            return                               # a restore/restart is replacing loot/
        with self._loot_lock:
            if self.loot is not None or getattr(self, "_loot_frozen", False):
                return                           # lost the race / froze meanwhile
            lm = None
            try:
                lm = LootManager(self._app_dir, self.gps)
                if not getattr(lm, "active", True):
                    # Out of space / unwritable: don't publish a dead manager (the
                    # counters would keep ticking with nothing saved). Allow a retry.
                    try:
                        lm.close()
                    except Exception:
                        pass
                    self._term("loot session inactive (disk full/unwritable?) - not recording", "warn")
                    return
                self._wd_seen = set()            # one "seen" set per loot session
                self.loot = lm                   # publish only a live manager
                self._term("loot capture session started", "ok")
            except Exception as exc:
                if lm is not None:
                    try:
                        lm.close()
                    except Exception:
                        pass
                self.loot = None
                self._term(f"loot session failed: {exc}", "warn")

    # ------------------------------------------------------------------
    # Lifecycle
    # ------------------------------------------------------------------

    def connect(self) -> None:
        """Open ESP32 serial + GPS. Non-fatal on failure."""
        if not HAVE_BACKEND:
            return
        if getattr(self, "_radio_boot_msg", "") and not getattr(self, "_radio_boot_said", False):
            self._radio_boot_said = True
            self._term("[SYS] " + self._radio_boot_msg, "ok")
        if getattr(self, "_flash_running", False) and not getattr(self, "_flash_connect_ok", False):
            return      # the flasher owns the serial port until it hands it back
        try:
            # AIO v2: power the USB rail (GPIO23) BEFORE detecting the ESP32. The XIAO
            # is powered THROUGH that rail, so without it the board never enumerates and
            # no serial port appears (neither in the system nor the game). Mirror OG app.py.
            usb_just_on = False
            try:
                aio = self._mgr("aio")
                if aio and aio.is_installed():
                    # Ensure-ON target, not a toggle: an unknown reading (None) also
                    # drives HIGH, which is a no-op when the rail is already up.
                    if (aio.get_status() or {}).get("usb") is not True:
                        if aio.toggle("usb", True):
                            usb_just_on = True
                            self._term("[USB] AIO v2 rail ON - waiting for ESP32 boot...", "ok")
                            time.sleep(6)   # ESP32 cold boot + USB enumerate on CM5
            except Exception as exc:
                self._term(f"[USB] AIO enable failed: {exc}", "warn")
            port = os.environ.get("WDGO_PORT") or detect_esp32_port()
            if not port:
                # The XIAO can enumerate a few seconds after power (or a reboot) even
                # when the USB rail was already on. Retry a bounded window so the ESP32
                # is connected by the time the boot splash finishes — connect() runs on
                # the pre-splash worker, so the loader just animates a little longer.
                for _ in range(4):
                    time.sleep(1.5)
                    port = os.environ.get("WDGO_PORT") or detect_esp32_port()
                    if port:
                        break
            if port:
                self.serial = SerialManager(port)
                self.serial.setup()
                self.connected = self.serial.is_open
                self.state.device = port
                self.state.connected = self.connected
                if self.connected:
                    self._term(f"serial open {port} @115200", "ok")
                    self.esp_ready = self.serial.probe()
                    self.state.esp32_ready = self.esp_ready
                    try:
                        self.serial.send_command("version")   # capture FW version for the update notice
                    except Exception:
                        pass
            else:
                self._term("no ESP32 detected - attach board + run as root", "warn")
        except PermissionError:
            self._term("serial permission denied - run with sudo", "warn")
            self.connected = False
        except Exception as exc:
            self._term(f"serial error: {exc}", "warn")
            self.connected = False
        try:
            if self.gps and self.gps.setup():
                self.gps_on = True
                self.state.gps_available = True
                self._term(f"GPS open {self.gps.device}", "ok")
        except Exception:
            self.gps_on = False

    def poll(self) -> None:
        """Call once per frame: drain serial + GPS, route lines, refresh loot."""
        if not HAVE_BACKEND:
            return
        self._adsb_rx_log()
        if self.serial and self.serial.is_open:
            try:
                for line in self.serial.read_available():
                    self._on_serial(line)
            except Exception as exc:
                # device likely vanished (USB rail toggled / unplugged) -> drop the
                # port so the background reconnect below reopens it automatically.
                self._term(f"serial read error: {exc}", "warn")
                try:
                    self.serial.close()
                except Exception:
                    pass
                self.serial = None
                self.connected = False
                if self.state:
                    self.state.connected = False
        elif (not getattr(self, "_flash_running", False)
              and time.time() - self._reconnect_t > 3.0):
            # Self-healing serial: the ESP32/XIAO isn't open — late enumeration at
            # startup, a USB-rail toggle, or a hot-unplug. Re-detect and reopen in the
            # background every few seconds so the user never has to restart the game.
            # The flasher owns the port while it runs, so skip then.
            self._reconnect_t = time.time()
            try:
                from watchdogs.serial_manager import SerialManager, detect_esp32_port
                port = os.environ.get("WDGO_PORT") or detect_esp32_port()
                if port:
                    self.serial = SerialManager(port)
                    self.serial.setup()
                    self.connected = bool(self.serial.is_open)
                    if self.state:
                        self.state.device = port
                        self.state.connected = self.connected
                    if self.connected:
                        self._term(f"serial reconnected {port} @115200", "ok")
                        self.esp_ready = self.serial.probe()
                        if self.state:
                            self.state.esp32_ready = self.esp_ready
                        try:
                            self.serial.send_command("version")
                        except Exception:
                            pass
                        # a power-cycle rebooted the XIAO out of bridge mode -> re-arm
                        if self._cluster and self._cluster_link is not None:
                            try:
                                self._cluster_link.start()
                                self._term("[CLUSTER] serial back - re-arming ENOW bridge", "ok")
                            except Exception:
                                pass
            except Exception:
                self.connected = False
        # Continuous wardriving: when a wardrive scan has finished, auto-repeat it after
        # WARDRIVE_INTERVAL so the sweep runs non-stop until the user stops it (like OG).
        if (self._wardrive and self._mode == "idle" and self._wardrive_done_t > 0
                and time.time() - self._wardrive_done_t >= self._WARDRIVE_INTERVAL):
            self._wardrive_done_t = 0.0
            self._mode = "scan" if self._wardrive == "scan_networks" else "idle"
            try:
                if self.serial and self.serial.is_open:
                    self.serial.send_command(self._wardrive)
            except Exception:
                pass
        if self.gps and self.gps_on:
            if not self.gps.available and hasattr(self.gps, "reopen"):
                # GpsManager closed the port after a read error (unplugged / cable
                # fault): drop the position now and retry the same port every 5 s.
                if self.state and self.state.gps_fix_valid:
                    self.state.gps_fix_valid = False
                    sdr = self._mgrs.get("sdr")
                    if sdr is not None:
                        try:
                            sdr.update_gps(0.0, 0.0)
                        except Exception:
                            pass
                now_r = time.monotonic()
                if now_r - getattr(self, "_gps_reopen_t", 0.0) > 5.0:
                    self._gps_reopen_t = now_r
                    try:
                        if self.gps.reopen():
                            self._term("[GPS] reconnected", "ok")
                    except Exception:
                        pass
            try:
                sents = self.gps.read_available()
                now_m = time.monotonic()
                if sents:
                    self.gps.process_sentences(sents)
                    f = self.gps.fix
                    self.state.gps_fix_valid = f.valid
                    self.state.gps_latitude = f.latitude
                    self.state.gps_longitude = f.longitude
                    self.state.gps_satellites = f.satellites
                    self.state.gps_satellites_visible = f.satellites_visible
                    # EXTRAS read these through ctx.gps.fix() (speed_kmh, heading)
                    self.state.gps_speed_kmh = f.speed_knots * 1.852
                    self.state.gps_heading = f.course_deg
                    # Feed the live fix to the SDR loggers. start_emergency/433/adsb
                    # only got the position ONCE at start (0,0 before the first fix),
                    # and nothing refreshed it — so every emergency_rf.csv row was
                    # tagged 0,0 even after GPS locked. Push each new fix through.
                    if f.valid:
                        self._gps_fix_mono = now_m    # last time we confirmed a position
                        sdr = self._mgrs.get("sdr")
                        if sdr is not None:
                            try:
                                sdr.update_gps(f.latitude, f.longitude)
                            except Exception:
                                pass
                else:
                    # No fresh NMEA this frame. A live GPS emits ~1 Hz, so if the last
                    # confirmed fix is older than the stale window the receiver is gone
                    # or lost signal — but GpsManager still holds the old fix forever.
                    # Age it ourselves so loot + SDR stop stamping new observations with
                    # a position that is no longer true. (GpsManager exposes no fix age;
                    # see the report for what it could add.)
                    f = self.gps.fix
                    if (f.valid and self._gps_fix_mono
                            and now_m - self._gps_fix_mono > self._GPS_STALE_SECS):
                        f.valid = False
                        if self.state:
                            self.state.gps_fix_valid = False
                        sdr = self._mgrs.get("sdr")
                        if sdr is not None:
                            try:
                                sdr.update_gps(0.0, 0.0)   # drop the stale position
                            except Exception:
                                pass
            except Exception:
                pass
        # OTA: periodically re-check GitHub for a newer game version (every 30 min)
        if not self._game_busy and time.time() - self._game_check_t > 1800:
            self.check_game_update()
        # firmware update re-check (once we know the ESP version, until an update is found)
        if self._fw_version and not self._fw_update and time.time() - self._fw_check_t > 1800:
            self.check_fw_update()
        # WDGWars "Chase the White Rabbit": refresh nearest targets every 60 s
        # in the background (rabbits don't move; 60 s is plenty, 120/min limit).
        if not self._rabbits_fetching and time.time() - self._rabbits_t > 60:
            self._rabbits_t = time.time()
            p = self._portal_sync()
            if p is not None and p.configured:
                self._rabbits_fetching = True
                import threading as _th
                _th.Thread(target=self._fetch_rabbits_worker, args=(p,),
                           daemon=True).start()
        # WDGWars game-state: rank/team/decay/contracts for the HUD, every 45 s.
        if not self._gs_fetching and time.time() - self._gs_t > 45:
            self._gs_t = time.time()
            p = self._portal_sync()
            if p is not None and p.configured:
                self._gs_fetching = True
                import threading as _th
                _th.Thread(target=self._fetch_gs_worker, args=(p,), daemon=True).start()
        # WDGWars profile: pull identity + server badges once at startup so the
        # account's awarded badges (uConsole Pioneer, etc.) and gang show without a
        # manual refresh. Read-only (/api/me) — no upload.
        if not self._profile_pulled:
            p = self._portal_sync()
            if p is not None and p.configured:
                self._profile_pulled = True
                p.show_profile()
        # proximity needs a periodic tick to drive its BLE scan/cadence
        _px = self._mgrs.get("prox")
        if _px is not None and getattr(_px, "enabled", False):
            try:
                _px.tick()
            except Exception:
                pass
        # drain host-side subsystem events into the terminal
        for key in ("sdr", "subghz", "watch", "prox", "lora"):
            m = self._mgrs.get(key)
            if m is None:
                continue
            pe = getattr(m, "poll_events", None)
            if not callable(pe):
                continue
            try:
                for ev in pe():
                    etype, data = ev if isinstance(ev, tuple) and len(ev) == 2 else ("ev", ev)
                    self._term("[%s] %s" % (key.upper(), str(data)[:80]),
                               "warn" if etype == "error" else "raw")
            except Exception:
                pass
        # Expire stale ADS-B aircraft / 433 sensors so a long SDR session does not
        # pile them up and progressively lag the radar. prune_stale() is thread-safe
        # and self-throttled, so calling it every poll() (per frame) is cheap and
        # keeps the live radar + aircraft_total() honest without a view toggle.
        _sdr = self._mgrs.get("sdr")
        if _sdr is not None:
            try:
                _sdr.prune_stale()
            except Exception:
                pass
        now = time.time()
        if self.loot and self.loot.active and now - self._last_recalc > 3.0:
            try:
                with self._loot_lock:            # serialise with mesh/radio-thread writers
                    self.loot.update_session_loot()
            except Exception:
                pass
            self._last_recalc = now
        if self._xp_dirty and now - self._last_xp_save > 5.0:
            self._save_xp()
            self._last_xp_save = now

    def close(self, modules: str = "off") -> None:
        """Quit teardown. `modules` picks what happens to the hardware:
          'off'     -> stop activity and power every module down (default; also
                       used by non-quit exits, so behaviour is unchanged there),
          'leave'   -> touch no hardware (modules keep running after exit),
          'restore' -> stop activity and put the AIO rails back to the snapshot
                       captured at launch (undo whatever the game changed)."""
        # Signal background loops to stop, then PERSIST progress before anything
        # else — a quit right after an XP gain must not lose it (the periodic
        # save only runs every 5s). save_xp is atomic (tmp + fsync + rename).
        self._stopping = True
        try:
            self._save_xp()
        except Exception:
            pass
        # Never tear down under a running flash: the esptool child would be orphaned
        # mid-write. Wait for the flasher to actually finish — a single run can take
        # FLASH_TOTAL_S, and there are up to two attempts plus boot/confirm, so a flat
        # 60 s could quit mid-write. Cap at the flasher's own worst case so a wedged
        # run can't block exit forever (the flasher enforces per-run timeouts).
        if getattr(self, "_flash_running", False):
            self._term("[SYS] waiting for the ESP32 flash to finish before exit...", "warn")
            cap = 2 * self.FLASH_TOTAL_S + 180.0      # both attempts + boot + confirm
            end = time.time() + cap
            while getattr(self, "_flash_running", False) and time.time() < end:
                time.sleep(0.1)
        # Proximity child procs (BLE scan + advertiser) are game-owned and must die
        # on EVERY exit — even LEAVE ON, which only means "leave the module RAILS
        # powered", not "orphan our processes". shutdown() keeps the on/off preference
        # so a relaunch restarts proximity if it was enabled.
        try:
            _px = self._mgrs.get("prox")
            if _px is not None:
                _px.shutdown()
        except Exception:
            pass
        if modules in ("off", "restore"):
            try:
                self.stop_attacks()       # halt host + ESP attacks/scans first
            except Exception:
                pass
            try:
                if modules == "off":
                    self._set_modules({"gps": False, "lora": False, "sdr": False})
                elif self._entry_rails:
                    self._set_modules(self._entry_rails)
            except Exception:
                pass
        # 'leave' -> leave all hardware exactly as it is (OS closes our fds on exit)
        try:
            if self.loot:
                self.loot.close()
        except Exception:
            pass

    def _set_modules(self, targets: dict) -> None:
        """Drive each AIO module to an on/off target. Turning a module OFF also
        stops its software; turning it ON only powers the rail (no stack is
        auto-started on the way out). USB is deliberately never touched — the
        game must always keep the XIAO's USB rail powered. A missing key or a None
        (rail state unknown at launch) is skipped, never treated as 'off'."""
        for feat in ("sdr", "gps", "lora"):
            want = targets.get(feat)
            if not isinstance(want, bool):
                continue
            try:
                self._apply_rail_target(feat, want)
            except Exception:
                pass

    def _apply_rail_target(self, feat: str, on: bool) -> None:
        aio = self._mgr("aio")
        _have_aio = bool(aio and aio.is_installed())
        if feat == "lora":
            if on:
                self._aio_lora(True)
            else:
                try:
                    mt = self._mgrs.get("meshtastic")
                    if mt and getattr(mt, "running", False):
                        mt.stop()                # stops OUR daemon only
                except Exception:
                    pass
                holder = self._meshtasticd_holder()
                if holder:                       # outside meshtasticd: keep its power
                    self._report_radio_held(holder, "[LoRa]")
                    return
                if not self._release_lora_spi():  # MeshCore still running: keep the rail
                    return
                self._aio_lora(False)
        elif feat == "sdr":
            if on:
                self._aio_sdr(True)
            else:
                try:
                    sdr = self._mgrs.get("sdr")
                    if sdr and getattr(sdr, "running", False):
                        sdr.stop()
                except Exception:
                    pass
                self._aio_sdr(False)
        elif feat == "gps":
            if not on:
                try:
                    if self.gps and self.gps_on:
                        self.gps.close(); self.gps_on = False
                except Exception:
                    pass
            if _have_aio:
                aio.toggle("gps", on)

    # ---- live module state for the quit prompt ----
    def rail_status(self) -> dict:
        """Current AIO rail state per gps/lora/sdr/usb: True/False, or "?" when the
        pin could not be read. {} without AIO/pinctrl. One pinctrl read."""
        try:
            aio = self._mgr("aio")
            if aio and aio.is_installed():
                st = aio.get_status()
                if st is None:
                    return {}
                return {k: (st[k] if isinstance(st.get(k), bool) else "?")
                        for k in ("gps", "lora", "sdr", "usb")}
        except Exception:
            pass
        return {}

    def entry_rails(self) -> dict:
        """AIO rail snapshot captured at launch (for the 'restore' quit option)."""
        return dict(getattr(self, "_entry_rails", {}) or {})

    def active_modules(self) -> list:
        """Labels of modules currently powered/running, for the quit prompt."""
        st = self.rail_status()
        mods = []
        if self.gps_on or st.get("gps") is True:          # "?" (unknown) is not "on"
            mods.append("GPS")
        if self.lora_on() or self.mt_running() or st.get("lora") is True:
            mods.append("LoRa")
        if self.sdr_on() or self._sdr_rail or st.get("sdr") is True:
            mods.append("SDR")
        return mods          # USB intentionally omitted — the XIAO rail stays on

    # ------------------------------------------------------------------
    # Serial line routing
    # ------------------------------------------------------------------

    def _on_serial(self, line: str) -> None:
        # Loot manager auto-detects handshakes / pcap streams / etc. from the
        # raw serial log, exactly like the OG game.
        if self.loot:
            try:
                self.loot.log_serial(self._redact(line))
            except Exception:
                pass
        # Firmware crash watch
        try:
            if SerialManager.is_crash_line(line):
                self.state.firmware_crashed = True
                self._term("!! firmware crash detected", "err")
        except Exception:
            pass
        # ESP firmware version (boot banner / version cmd / ping) -> arms the FW-update notice
        if not self._fw_version:
            _vm = (re.search(r"(?:JanOS|WatchDogsGo) version:\s*v?(\d+\.\d+\.\d+)", line)
                   or re.search(r"APP_MAIN START \(v?(\d+\.\d+\.\d+)\)", line)
                   or re.search(r"pong\s+v?(\d+\.\d+\.\d+)", line))
            if _vm:
                self._fw_version = _vm.group(1)
                self._term("[FW] firmware v%s" % self._fw_version, "ok")
                self.check_fw_update()
        # Cluster-serial (fleet core): the XIAO-core streams fleet records + node
        # telemetry + join events. CWD=record, CNODE=telemetry, CJOIN=pairing, CEVT=event.
        # Bridge mode: the ESP32 emits raw ENOW frames; the brain turns them into
        # CNODE/CWD/CJOIN (fed back through _ingest_cluster_line) and answers nodes.
        if (self._cluster_bridge and self._cluster_link is not None
                and line.lstrip("> ").startswith("ENOW,")):   # first frame can carry the '> ' prompt
            self._cluster_link.feed_line(line)
            return
        if self._cluster and line.startswith(("CWD,", "CNODE,", "CJOIN,", "CEVT,")):
            if self._cluster_bridge and line.startswith("CJOIN,"):
                return       # bridge mode: joins come only from the brain's validated pool
            self._ingest_cluster_line(line)
            return
        low = line.lower()
        # Firmware serial-wardrive (CORE model): the XIAO node streams full WiGLE 1.6 rows
        # (MAC-first, ending in ,WIFI / ,BLE). The host stamps its own GPS + time and
        # persists. The node already did the promiscuous capture + dedup.
        if self._wardrive_serial and (low.endswith(",wifi") or low.endswith(",ble")) and ":" in line[:18]:
            self._ingest_wardrive_row(line, low.endswith(",ble"))
            return
        # Evil Twin / portal credential capture
        if "post data" in low or "form submission" in low:
            if self.loot:
                try:
                    with self._loot_lock:
                        if self.state.evil_twin_running:
                            self.loot.save_evil_twin_event(line)
                        else:
                            self.loot.save_portal_event(line)
                except Exception:
                    pass
            creds = self._parse_post_fields(line)
            if creds:
                self.captures.append(creds)
                self.state.submitted_forms += 1
                self.gain_xp(150); self.earn_badge("evil_twin")
                self._term("CAPTURED  " + creds, "ok")
                self.set_status("captured: " + creds[:40])
            return
        # Serial markers do not confirm a new, complete file. Award no handshake XP here.
        if "hccapx" in low or "handshake captured" in low or "eapol" in low and "saved" in low:
            self.earn_badge("handshake_hunter")
        # BLE scan results, firmware list format "N. MAC  RSSI: X dBm"
        bl = _BLE_LIST_RE.match(line)
        if bl:
            mac, rssi, rest = bl.group(1).upper(), bl.group(2), bl.group(3).strip()
            tag = "AirTag" if "airtag" in low else ("SmartTag" if "smarttag" in low else "")
            if not any(d[0] == mac for d in self.ble_devices):
                self.ble_devices.append((mac, rssi, rest[:24], tag))
                self.ble_devices[:] = self.ble_devices[-300:]
                self.gain_xp(1)
                if self.loot:
                    try:
                        with self._loot_lock:
                            self.loot.save_bt_device(mac, int(rssi), rest[:24], tag == "AirTag", tag == "SmartTag")
                            self.loot.save_wardriving_bt(mac, int(rssi), rest[:24])
                    except Exception: pass
                if self._wardrive:   # continuous BT wardrive -> flowing log
                    self._term("[BLE] %-17s %sdBm %s" % (mac, rssi, (rest[:16] or tag)), "raw")
            return
        # BLE summary -> AirTag/SmartTag counts AND the true end of a BLE scan
        bs = _BLE_SUMMARY_RE.search(line)
        if bs:
            self.airtags, self.smarttags = int(bs.group(1)), int(bs.group(2))
            self._scan_done_pulse = True
            self._mode = "idle"
            if self._wardrive:
                self._wardrive_done_t = time.time()   # arm rescan
            n = len(self.ble_devices)
            self._term("BLE scan done: %d devices (%d AirTags, %d SmartTags)"
                       % (n, self.airtags, self.smarttags), "ok")
            self.set_status("BLE scan: %d devices" % n)
            return
        # BLE scan results -> device list (for markers/radar/counters)
        mb = _BLE_RE.match(line)
        if mb and ":" in mb.group(1):
            mac, rssi, name = mb.group(1).upper(), mb.group(2), mb.group(3).strip()
            tag = "AirTag" if "[airtag]" in low else ("SmartTag" if "[smarttag]" in low else "")
            if not any(d[0] == mac for d in self.ble_devices):
                self.ble_devices.append((mac, rssi, name[:24], tag))
                self.ble_devices[:] = self.ble_devices[-80:]
                self.gain_xp(10)
                if self.loot:
                    try:
                        with self._loot_lock:
                            self.loot.save_bt_device(mac, int(rssi), name, tag == "AirTag", tag == "SmartTag")
                            self.loot.save_wardriving_bt(mac, int(rssi), name)
                    except Exception: pass
                if self._wardrive:   # continuous BT wardrive -> flowing log
                    self._term("[BLE] %-17s %sdBm %s" % (mac, rssi, (name[:16] or tag)), "raw")
            return
        # AirTag/SmartTag count line "airtags,smarttags"
        ma = _AIRTAG_COUNT_RE.match(line)
        if ma:
            self.airtags, self.smarttags = int(ma.group(1)), int(ma.group(2))
            if self.loot:
                try:
                    with self._loot_lock:
                        self.loot.save_bt_airtag_event(self.airtags, self.smarttags)
                except Exception: pass
            return
        # sniffer AP line "SSID, CHn: count"
        if self._mode == "sniffer" and self.net:
            try:
                self.net.parse_sniffer_results([line])
                if self.state.sniffer_aps:
                    self.sniffer_aps = list(self.state.sniffer_aps)
            except Exception:
                pass
        # Route scan CSV rows into the network list
        if self._mode == "scan" and self.net:
            try:
                before = len(self.state.networks)
                if self.net.add_network(line):
                    net = self.state.networks[-1]
                    self.state.scan_done = True
                    # Ignore-list: a whitelisted BSSID is never persisted or rewarded
                    # on the wardrive sweep. Drop it from the live list too.
                    if self._wardrive:
                        try:
                            wl = self._wl_mgr()
                            if wl is not None and wl.is_blocked(getattr(net, "bssid", "")):
                                del self.state.networks[-1]
                                return
                        except Exception:
                            pass
                    self._check_pwned(net)   # cracked-password AP? notify + map mark
                    # Wardrive re-sweeps re-see the same APs: dedup the display list by
                    # BSSID (keep the latest sighting) so it GROWS on new finds, and only
                    # new BSSIDs earn XP / hit the flowing log. Loot CSV dedups separately.
                    dup = next((i for i in range(before)
                                if self.state.networks[i].bssid == net.bssid), -1)
                    if dup >= 0:
                        del self.state.networks[dup]
                    else:
                        self.gain_xp(2)
                        if self._wardrive:   # growing wardrive log: only new networks
                            self._term("[WiFi] %-20s ch%-3s %sdBm"
                                       % ((net.ssid or "<hidden>")[:20], net.channel, net.rssi), "raw")
                    if self.loot:
                        try:
                            with self._loot_lock:
                                self.loot.save_wardriving_network(net)
                        except Exception: pass
                    return
            except Exception:
                pass
        # WiFi scan FINISHED -> pulse UI + stop scanning. NOTE: the firmware prints
        # "WiFi scan completed. Found N networks" as a HEADER *before* streaming the CSV
        # rows, and "Scan results printed." at the true end. Matching "scan complete" here
        # flipped _mode to idle too early, so the rows were never parsed into networks().
        if ("scan results printed" in low or "scan done" in low
                or ("scan complete" in low and "found" not in low)):
            n = len(self.state.networks) if self.state else 0
            self._scan_done_pulse = True
            self._mode = "idle"
            if self._wardrive:
                self._wardrive_done_t = time.time()   # arm rescan
            self.gain_xp(n)            # scan reward
            if n:
                self.earn_badge("wardriver")
            self._term("WiFi scan done: %d networks" % n, "ok")
            self.set_status("WiFi scan: %d networks found" % n)
            return
        kind = "ok" if ("ready" in low or "ok" in low[:4]) else "raw"
        self._term(line, kind)

    # the console font has no typographic punctuation: show ASCII instead of "?"
    _TERM_ASCII = str.maketrans({"\u2014": "-", "\u2013": "-", "\u2192": "->", "\u2190": "<-",
                                 "\u2026": "...", "\u201c": '"', "\u201d": '"', "\u201e": '"',
                                 "\u2018": "'", "\u2019": "'", "\u00b7": "-", "\u2022": "*"})

    @staticmethod
    def _redact(line: str) -> str:
        """Mask fleet-bridge frame payloads (a JOIN_GRANT carries the raw fleet key)
        before a line reaches the terminal or a log file."""
        if not line or ("enow_tx" not in line and "ENOW," not in line):
            return line
        try:
            from cluster_enow import redact_line
        except Exception:                        # noqa: BLE001
            import re as _re
            return _re.sub(r"(enow_tx\s+\S+\s+)[0-9A-Fa-f]+", r"\1<redacted>", line)
        return redact_line(line)

    def _term(self, msg: str, kind: str = "raw") -> None:
        msg = self._redact(str(msg)).translate(self._TERM_ASCII)
        self.term.append((time.strftime("%H:%M:%S"), msg, kind))
        if len(self.term) > 300:
            self.term = self.term[-300:]
            self.mc_log = self.mc_log[-300:]   # grows from the LoRa reader thread; cap like term
            self.wd_log = self.wd_log[-300:]   # grows from the Reticulum thread; cap like term

    # ------------------------------------------------------------------
    # Commands
    # ------------------------------------------------------------------

    _CAPTURE_CMDS = ("scan", "start_sniffer", "start_handshake", "start_deauth",
                     "start_blackout", "sae_overflow", "start_evil", "start_portal",
                     "start_wardrive")

    def send(self, cmd: str) -> None:
        self._term(f"> {cmd}", "tx")
        # a real capture command => make sure a loot write-session exists so the
        # firmware output gets persisted (handshakes, wardriving, portal, ...)
        if any(cmd.startswith(p) for p in self._CAPTURE_CMDS):
            # Single radio: a scan/wardrive/sniffer/attack can't run while the ENOW
            # bridge owns it, so the cluster yields automatically. (None of the
            # bridge's own commands — enow_tx / start_cluster_bridge / stop — match
            # _CAPTURE_CMDS, so this never fights the running bridge.)
            if self._cluster:
                self._term("[CLUSTER] yielding the radio to a capture op — fleet stopped", "warn")
                self.stop_cluster()
            self.ensure_session()
        if self.serial and self.serial.is_open:
            try:
                self.serial.send_command(cmd)
            except Exception as exc:
                self._term(f"tx error: {exc}", "warn")

    def set_mode(self, mode: str) -> None:
        self._mode = mode

    # ---- radio matrix (ESP32 vs host Wi-Fi card) ----------------------
    def radio_detect_refresh(self) -> None:
        if self._radio is not None:
            try:
                from watchdogs import radio_detect
                self._radio.detect = radio_detect.detect()
            except Exception:
                pass

    def radio_rows(self) -> list:
        return self._radio.rows() if self._radio is not None else []

    def radio_cycle(self, cap: str) -> str:
        return self._radio.cycle(cap) if self._radio is not None else ""

    def radio_both(self) -> bool:
        return bool(self._radio and self._radio.detect.get("both"))

    def radio_summary(self) -> str:
        if self._radio is None:
            return ""
        try:
            from watchdogs import radio_detect
            return radio_detect.summary(self._radio.detect)
        except Exception:
            return ""

    def set_wardrive(self, cmd) -> None:
        """Enable continuous wardriving for `cmd` ('scan_networks'/'scan_bt'), or None to stop."""
        self._wardrive = cmd
        self._wardrive_done_t = 0.0

    def is_wardriving(self) -> bool:
        return self._wardrive is not None

    # ---- firmware serial-wardrive (node streams, host tags GPS) -----------
    def start_wardrive_serial(self, kind: str) -> None:
        """Start a continuous wardrive. kind: 'wifi'|'bt'|'all'. The radio matrix picks
        the source: the ESP32 node (promiscuous sweep streamed over serial) or a host
        Wi-Fi card (periodic scan). Either way the host stamps GPS + time and the same
        ingest writes wardriving.csv."""
        self.ensure_session()
        self.ensure_gps("Wardrive")
        if kind != "bt" and self._radio is not None and self._radio.resolve("wardrive") == "host":
            if self._start_host_wifi_scan():
                self._wardrive_serial = kind
                self.set_status("Wardrive %s - host card (%s)" % (kind, self._radio.host_iface()))
                return
        # _wd_seen is NOT reset here: it lives as long as the loot session (reset in
        # ensure_session), so restarting a wardrive or a parallel source (cluster,
        # host card) does not re-award XP or re-count APs already seen this session.
        bands = {"wifi": "wifi24,wifi5", "bt": "ble",
                 "all": "wifi24,wifi5,ble"}.get(kind, "wifi24,wifi5,ble")
        self.send("set_wardrive_bands " + bands)
        self.send("start_wardrive_serial")
        self._wardrive_serial = kind
        self.set_status("Wardrive (serial) %s - node streaming" % kind)

    def _start_host_wifi_scan(self) -> bool:
        """Begin a Wi-Fi scan/wardrive on the host card, feeding the normal ingest."""
        try:
            from watchdogs.host_wifi import HostWifi
            iface = self._radio.host_iface()
            if not iface:
                return False
            self._host_wifi = HostWifi(
                iface,
                on_row=lambda row, bt: self._ingest_wardrive_row(row, bt),
                msg=lambda t, l="raw": self._term(t, l))
            self._host_wifi.start_scan()
            return True
        except Exception as exc:
            self._term("[host-wifi] could not start: %s" % exc, "warn")
            return False

    def stop_wardrive_serial(self) -> None:
        if self._host_wifi is not None:
            try:
                self._host_wifi.stop()
            except Exception:
                pass
            self._host_wifi = None
            self._wardrive_serial = None
            self.set_status("wardrive stopped (host card)")
            return
        if self._wardrive_serial:
            self.send("stop")
            self._wardrive_serial = None
            self.set_status("wardrive stopped")

    def is_wardrive_serial(self) -> bool:
        return self._wardrive_serial is not None

    def _ingest_wardrive_row(self, line: str, is_bt: bool, persist: bool = True) -> None:
        """One streamed WiGLE 1.6 row from the node -> stamp GPS + persist + live log.

        persist=False (the WDGO_CLUSTER_SIM demo) drives the live UI only — no disk
        write, no XP, no badge — so exploring the fleet screen never pollutes real loot."""
        try:
            parts = next(csv.reader([line.strip()]))
        except Exception:
            return
        if len(parts) < 14:
            return
        mac, ssid, ch, rssi = parts[0].upper(), parts[1], parts[4], parts[6]
        # Ignore-list: a whitelisted MAC must never be persisted or rewarded, on
        # ANY wardrive path (node serial, host card, fleet). Drop it before disk/XP.
        if persist:
            try:
                wl = self._wl_mgr()
                if wl is not None and wl.is_blocked(mac):
                    return
            except Exception:
                pass
        if persist and self.loot:
            try:
                with self._loot_lock:
                    self.loot.append_wardrive_wigle(line)   # stamps host GPS + time, dedups
            except Exception:
                pass
        if mac in self._wd_seen:
            return                       # re-observation: persisted, keep the live log clean
        self._wd_seen.add(mac)
        if is_bt:
            if not any(d[0] == mac for d in self.ble_devices):
                self.ble_devices.append((mac, rssi, ssid[:24], ""))
                self.ble_devices[:] = self.ble_devices[-300:]
            if persist:
                self.gain_xp(1)
            self._term("[BLE] %-17s %sdBm %s" % (mac, rssi, ssid[:16]), "raw")
        else:
            if persist:
                self.gain_xp(2)
                self.earn_badge("wardriver")
            self._term("[WiFi] %-20s ch%-3s %sdBm"
                       % ((ssid or "<hidden>")[:20], ch, rssi), "raw")
        self.set_status("Wardrive: %d unique" % len(self._wd_seen))

    # ------------------------------------------------------------------
    # Cluster-serial: the connected XIAO acts as the ESP-NOW core for a node
    # fleet (channel/role assignment, telemetry) and streams fleet records +
    # node telemetry + join events over serial. This host drives the UI, stamps
    # GPS, and persists. projectZero core-mode firmware is pending — protocol in
    # the cluster-serial protocol; the line format here matches it.
    # ------------------------------------------------------------------
    def start_cluster(self) -> None:
        self.ensure_session()
        self._cluster_nodes = {}
        self._cluster_joins = []
        self._cluster_recs = 0
        self._cluster_rec_marks = []
        self._cluster_wifi_seen = set()
        self._cluster_ble_seen = set()
        self._cluster_ble_random = set()
        self._cluster = True
        self.ensure_gps("Cluster wardrive")
        self._term("[CLUSTER] core mode requested — coordinating node fleet", "tx")
        self.set_status("Cluster: starting core")
        # Demo / hardware-free validation: WDGO_CLUSTER_SIM synthesises a realistic
        # XIAO fleet straight into the serial ingest, so the whole UI/UX + map path
        # runs end-to-end with no nodes attached. Faster liveness windows match the
        # quicker synthetic clock.
        if os.environ.get("WDGO_CLUSTER_SIM"):
            self._cluster_demo = True            # synthetic fleet — never persist to loot/XP
            self._cluster_stale_s = 8.0
            self._cluster_retire_s = 20.0
            self._cluster_sim_stop = threading.Event()
            self._thread(self._cluster_sim_loop, "cluster-sim")
            self._term("[CLUSTER] demo simulator running (WDGO_CLUSTER_SIM)", "dim")
            return
        # Real ENOW bridge: the XIAO-C5 in the uConsole runs projectZero's bridge
        # mode (a thin ESP-NOW pipe); the brain lives HERE and speaks over the same
        # serial. 'ENOW,...' lines come up through the normal RX path (routed to the
        # link), and the link writes 'enow_tx'/ADMIN back via self.send.
        # Default to the bridge whenever a fleet key is present (or WDGO_CLUSTER_BRIDGE
        # forces it): the XIAO runs projectZero's bridge mode and the brain here drives
        # the fleet. Fall back to the legacy external-core stream only with no key.
        key = None
        try:
            import cluster_enow
            import cluster_brain
            import cluster_link
            key = cluster_enow.FleetKey.load()
        except Exception as e:                   # noqa: BLE001
            self._term("[CLUSTER] bridge modules unavailable: %s" % e, "err")
        force = bool(os.environ.get("WDGO_CLUSTER_BRIDGE"))
        if key is not None and (key.present or force):
            if not key.present:
                self._term("[CLUSTER] brak klucza floty (~/.wdgo/fleet.key) — "
                           "nody zaadoptowane nie odpowiedzą", "warn")
            self._cluster_brain = cluster_brain.ClusterBrain(key)
            self._cluster_link = cluster_link.ClusterLink(
                self._cluster_brain, write=self.send, ingest=self._ingest_cluster_line)
            self._cluster_bridge = True
            self._cluster_bridge_stop = threading.Event()
            self._cluster_link.start()           # sends start_cluster_bridge
            self._thread(self._cluster_bridge_tick, "cluster-bridge-tick")
            self._term("[CLUSTER] ENOW bridge active (fleet key %s)" % key.fingerprint, "ok")
            return
        # Legacy: an external Marauder core streaming CWD/CNODE directly over serial.
        self.send("start_cluster_serial")

    def stop_cluster(self) -> None:
        if self._cluster:
            self.send("stop")                    # tears down bridge mode on the ESP32 too
            self._cluster = False
            if self._cluster_bridge_stop is not None:
                self._cluster_bridge_stop.set()
                self._cluster_bridge_stop = None
            self._cluster_bridge = False
            self._cluster_link = None
            self._cluster_brain = None
            if self._cluster_sim_stop is not None:
                self._cluster_sim_stop.set()
                self._cluster_sim_stop = None
            self._term("[CLUSTER] stopped", "warn")
            self.set_status("Cluster stopped")
            if not getattr(self, "_cluster_demo", False):
                self._cluster_auto_upload()

    def _cluster_auto_upload(self) -> None:
        """After the fleet stops, send what it collected without a trip to the menu:
        WDGWars portal + WiGLE, each only if configured, in the background. Rows
        without GPS are skipped by both uploads; the active session stays pending
        so rows added later are offered again."""
        try:
            p = self._portal_sync()
            if p is not None and p.configured:
                self._term("[CLUSTER] auto-upload: WDGWars", "tx")
                p.sync(all_sessions=True)
        except Exception as exc:                     # noqa: BLE001
            self._term("[CLUSTER] auto-upload WDGWars: %s" % exc, "warn")
        self._act_wigle_up(quiet_unconfigured=True)

    def cluster_accept(self, mac: str) -> None:
        mac = (mac or "").strip()
        if not mac:
            return
        link = self._cluster_link
        if self._cluster_bridge and link is not None:
            # Bridge mode: the brain decides (fresh, source-checked JOIN_REQUEST,
            # consumed once) and its pending list is the only source of truth.
            mac = mac.lower()
            self._cluster_joins = [m for m in self._cluster_joins if m != mac]
            if not (self.serial and getattr(self.serial, "is_open", False)):
                self._term("[CLUSTER] cannot accept %s: bridge serial not connected" % mac, "warn")
                return
            try:
                granted = link.accept(mac)       # brain unicasts a signed JOIN_GRANT
            except Exception as exc:             # noqa: BLE001
                self._term("[CLUSTER] JOIN_GRANT for %s not sent: %s" % (mac, exc), "warn")
                return
            if granted:
                self._term("[CLUSTER] accepting node %s" % mac, "ok")
            else:
                self._term("[CLUSTER] join request from %s expired / not found - "
                           "wait for the node to ask again" % mac, "warn")
            return
        # Serial core / simulator: the core firmware does the final check; only
        # forward a request this host still lists (a second [A] is a no-op).
        if mac not in self._cluster_joins:
            self._term("[CLUSTER] join request from %s expired / not found" % mac, "warn")
            return
        self._cluster_joins = [m for m in self._cluster_joins if m != mac]
        self.send("cluster_accept %s" % mac)
        self._term("[CLUSTER] accepting node %s (sent to core)" % mac, "ok")

    def cluster_release(self, mac: str) -> None:
        """Release one node from the fleet: a signed RELEASE tells it to drop the
        fleet key and fall back to JOIN_REQUEST, so another rig (e.g. a phone) can
        adopt it. Only meaningful in bridge mode with a key present."""
        mac = (mac or "").strip().lower()
        if not mac:
            return
        if self._cluster_bridge and self._cluster_link is not None:
            self._cluster_link.release(mac)
        else:
            self.send("cluster_release %s" % mac)
        with self._cluster_lock:
            self._cluster_nodes.pop(mac, None)
        self._cluster_joins = [m for m in self._cluster_joins if m != mac]
        self._term("[CLUSTER] releasing node %s" % mac, "warn")

    def cluster_release_all(self) -> None:
        """Release every node currently in the fleet."""
        if self._cluster_bridge and self._cluster_link is not None:
            self._cluster_link.release_all()
        else:
            self.send("cluster_release all")
        with self._cluster_lock:
            self._cluster_nodes = {}
        self._cluster_joins = []
        self._term("[CLUSTER] releasing ALL nodes", "warn")

    def fleet_key_export(self) -> "Optional[str]":
        """The fleet key as a QR/paste line 'WDGFLEET1:<32hex>:<label>' for a phone
        to import, or None when no key is present. SECRET: only call this from an
        explicit operator action (it reveals the raw key); never log the result."""
        try:
            import cluster_enow
            key = cluster_enow.FleetKey.load()
            raw = key.raw() if key.present else None
        except Exception:                        # noqa: BLE001
            raw = None
        if not raw:
            return None
        import re
        import socket
        label = re.sub(r"[^A-Za-z0-9 _-]", "", socket.gethostname())[:24]
        return "WDGFLEET1:%s:%s" % (raw.hex(), label)

    FLEET_IMPORT_FILE = os.path.expanduser("~/.wdgo/fleet_import.txt")

    def fleet_key_import(self, text: str) -> tuple:
        """Install the fleet key from a WDGFLEET1:<32hex>:<label> line (typed, pasted,
        or - when `text` is empty - read from ~/.wdgo/fleet_import.txt, also under
        SUDO_USER's home). A trailing ' force' replaces a DIFFERENT existing key (the
        old one is copied aside). Refused while the cluster runs: one fleet, many
        cores, only ONE core active at a time. -> (ok, message). Never logs the key."""
        if self._cluster:
            return False, "stop the cluster first ([X] on the fleet screen)"
        s = (text or "").strip()
        force = False
        if s.lower().endswith(" force"):
            s, force = s[:-6].strip(), True
        if not s:
            paths = [self.FLEET_IMPORT_FILE]
            su = os.environ.get("SUDO_USER")
            if su:
                try:
                    import pwd
                    paths.append(os.path.join(pwd.getpwnam(su).pw_dir, ".wdgo", "fleet_import.txt"))
                except Exception:                # noqa: BLE001
                    pass
            for p in paths:
                try:
                    s = open(p).read().strip()
                    if s:
                        break
                except OSError:
                    continue
            if not s:
                return False, "nothing typed and no ~/.wdgo/fleet_import.txt"
            if s.lower().endswith(" force"):
                s, force = s[:-6].strip(), True
        try:
            import cluster_enow
            ok, msg = cluster_enow.import_fleet_line(s, force=force)
        except Exception as e:                   # noqa: BLE001
            ok, msg = False, "import failed: %s" % e
        self._term("[CLUSTER] fleet key import: %s" % msg, "ok" if ok else "warn")
        return ok, msg

    def cluster_active(self) -> bool:
        return self._cluster

    def cluster_nodes(self) -> list:
        """Node telemetry rows (thread-safe), enriched with liveness and ordered by
        node index. Each row gains: age (s since its last line), stale (unheard past
        the stale window), fresh (checked in < 3 s ago, for a join/activity pulse).
        Nodes unheard past the retire window are dropped from the fleet view."""
        now = time.time()
        retired, out = [], []
        for n in _snapshot(self._cluster_nodes):
            age = now - n.get("seen", now)
            if age >= self._cluster_retire_s:
                retired.append(n.get("mac"))
                continue
            n = dict(n)
            n["age"] = age
            n["stale"] = age >= self._cluster_stale_s
            n["fresh"] = age < 3.0
            n["pin"] = (self._band_name(self._cluster_brain.node_window(n.get("mac")))
                        if self._cluster_brain is not None else None)
            out.append(n)
        if retired:
            with self._cluster_lock:
                for m in retired:
                    self._cluster_nodes.pop(m, None)
        out.sort(key=lambda n: n.get("idx", 99))
        return out

    # Operator channel bands for the fleet screen: (label, ENOW_CHANNELS index
    # window or None for auto). AUTO hands the node back to the brain's split.
    _CLUSTER_BANDS = [("AUTO", None), ("BLE", "ble"), ("2.4G", (0, 13)), ("5G", (14, 39)),
                      ("5G-lo", (14, 21)), ("5G-hi", (22, 39))]

    @classmethod
    def _band_name(cls, window):
        for label, win in cls._CLUSTER_BANDS:
            if win == window:
                return None if label == "AUTO" else label
        return "CUST"                    # a custom window set some other way

    def cluster_cycle_band(self, mac: str, step: int) -> None:
        """Cycle one node's manual task (operator override of the auto split):
        AUTO -> BLE -> 2.4G -> 5G -> slices. AUTO hands it back to the brain, BLE
        forces it onto Bluetooth duty. step +1 / -1. No-op outside bridge mode.
        Backward-compatible: if the brain lacks the BLE pin API, BLE is skipped."""
        if not mac or self._cluster_brain is None:
            return
        brain = self._cluster_brain
        on_ble = bool(getattr(brain, "node_is_ble", lambda _m: False)(mac))
        cur_label = "BLE" if on_ble else (self._band_name(brain.node_window(mac)) or "AUTO")
        labels = [lab for lab, _ in self._CLUSTER_BANDS]
        idx = labels.index(cur_label) if cur_label in labels else 0
        idx = (idx + step) % len(self._CLUSTER_BANDS)
        label, win = self._CLUSTER_BANDS[idx]
        if label == "BLE" and not hasattr(brain, "set_node_ble"):
            idx = (idx + step) % len(self._CLUSTER_BANDS)   # old brain: skip BLE
            label, win = self._CLUSTER_BANDS[idx]
        if hasattr(brain, "set_node_ble"):
            brain.set_node_ble(mac, label == "BLE")
        if label != "BLE":
            brain.set_node_channels(mac, win)               # None=AUTO, else (lo,hi)
        self._term("[CLUSTER] node %s band -> %s" % (mac[-4:], label), "tx")

    def cluster_joins(self) -> list:
        link = self._cluster_link
        if self._cluster_bridge and link is not None:
            try:
                return link.pending_joins()      # the brain's live, unexpired requests
            except Exception:                    # noqa: BLE001
                return []
        return _snapshot(self._cluster_joins)

    def cluster_recs(self) -> int:
        return self._cluster_recs

    def _cluster_host_rate(self) -> int:
        """Fleet records/min as measured BY THE HOST over the CWD stream (ground truth,
        independent of what the nodes self-report): CWD timestamps seen in the last 60 s."""
        now = time.time()
        marks = _snapshot(self._cluster_rec_marks)
        return sum(1 for t in marks if now - t <= 60.0)

    @staticmethod
    def _ble_is_random(mac: str) -> bool:
        """True for a randomised/private BLE address (locally-administered U/L bit set
        in the first octet). Phones/wearables rotate these every ~15 min, so they
        inflate 'unique device' counts; public (OUI-assigned) addresses are stable."""
        try:
            return (int(mac.split(":")[0], 16) & 0x02) != 0
        except Exception:
            return False

    def cluster_summary(self) -> dict:
        """Fleet aggregate for the header strip."""
        nodes = self.cluster_nodes()
        rec_min = 0
        for n in nodes:
            try:
                rec_min += int(n.get("rec_min") or 0)
            except (TypeError, ValueError):
                pass
        return {
            "online": sum(1 for n in nodes if not n.get("stale")),
            "total": len(nodes),
            "stale": sum(1 for n in nodes if n.get("stale")),
            "ble": sum(1 for n in nodes if (n.get("role") or "").lower() == "ble"),
            "rec_min": rec_min,
            "host_rate": self._cluster_host_rate(),
            "recs": self._cluster_recs,
            "uniques": len(self._wd_seen),
            "wifi_nets": len(self._cluster_wifi_seen),
            "ble_devs": len(self._cluster_ble_seen),
            "ble_random": len(self._cluster_ble_random),
            "ble_public": len(self._cluster_ble_seen) - len(self._cluster_ble_random),
            "joins": len(self.cluster_joins()),
            "gps": bool(self.state and self.state.gps_fix_valid),
            "active": self._cluster,
        }

    # Channel table mirrored from the fleet firmware (wdg_cluster.h ENOW_CHANNELS),
    # so a claimed slice index maps to the same real channel the node scans.
    _SIM_CHANNELS = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
                     36, 40, 44, 48, 52, 56, 60, 64,
                     100, 112, 116, 120, 124, 128, 132, 136, 140, 144,
                     149, 153, 157, 161, 165, 169, 173, 177]

    def _cluster_bridge_tick(self) -> None:
        """Periodic pump for the real ENOW bridge: re-advertises the channel split
        (ADMIN) and keeps assignments fresh. The link self-gates on its interval."""
        stop = self._cluster_bridge_stop
        while stop is not None and not stop.is_set():
            try:
                link = self._cluster_link
                if link is not None:
                    link.poll()
            except Exception as e:                   # noqa: BLE001
                self._term("[CLUSTER] bridge tick error: %s" % e, "warn")
            stop.wait(1.0)

    def _cluster_sim_loop(self) -> None:
        """Hardware-free fleet: synthesise a realistic XIAO cluster straight into the
        serial ingest. Exercises every UI path — live telemetry, health/stale/retire,
        dropout+rejoin, a join request awaiting [A], and GPS-stamped fleet hits on the
        map — with no nodes attached. Lines are byte-identical to the firmware's, so
        this tests the real parser, not a shortcut."""
        import random
        import base64
        stop = self._cluster_sim_stop
        # idx, MAC (locally administered test MACs, not real devices), role, channel-slice
        fleet = [
            (0, "02:57:44:00:00:A1", "wifi", (0, 5)),
            (1, "02:57:44:00:00:B2", "wifi", (6, 13)),
            (2, "02:57:44:00:00:C3", "wifi", (14, 21)),
            (3, "02:57:44:00:00:D4", "wifi", (22, 31)),
            (4, "02:57:44:00:00:E5", "ble",  (0, 0)),
        ]
        joiner = (5, "02:57:44:00:00:F6", "wifi", (32, 39))
        st = {}
        for idx, mac, role, sl in fleet:
            st[mac] = {"idx": idx, "role": role, "slice": sl, "boot": time.time(),
                       "dedup": random.randint(4, 18), "temp": random.randint(41, 48),
                       "dropped": 0, "dropouts": 0, "last_gap": 0, "buffered": 0,
                       "down_until": 0.0, "alive": True, "joined": False, "active": True}
        st[joiner[1]] = {"idx": joiner[0], "role": joiner[2], "slice": joiner[3],
                         "boot": time.time(), "dedup": 6, "temp": 44, "dropped": 0,
                         "dropouts": 0, "last_gap": 0, "buffered": 0, "down_until": 0.0,
                         "alive": True, "joined": False, "active": False}
        ssids = ["FRITZ!Box 7590", "UPC1234567", "", "eduroam", "TP-LINK_A4F2",
                 "iPhone (Demo)", "Orange_Swiatlowod", "", "Play_5G_88", "ESP_Portal",
                 "AndroidAP", "HUAWEI-B525", "", "Vectra-WiFi-2.4", "net_guest"]
        auths = ["[WPA2-PSK-CCMP]", "[WPA2-PSK-CCMP]", "[WPA3-SAE]",
                 "[WPA2-EAP]", "[OPEN]", "[WPA/WPA2]"]
        t_join_req = time.time() + 11.0        # the 6th node asks to join after a bit
        t_evt = time.time() + 7.0
        emit = self._ingest_cluster_line
        while not (stop and stop.is_set()):
            now = time.time()
            # --- per-node telemetry (CNODE) ---
            for idx, mac, role, sl in fleet + [joiner]:
                s = st[mac]
                if not s["active"]:
                    # the joiner only comes alive once the operator accepts it
                    if mac not in self._cluster_joins and s["joined"]:
                        s["active"] = True; s["boot"] = now
                        self._term("[CLUSTER] node %s adopted — scanning slice"
                                   % mac[-4:], "ok")
                    else:
                        continue
                # random dropout: a node goes quiet for a few seconds, returns rebooted
                if s["down_until"] > now:
                    continue
                if s["alive"] and random.random() < 0.012:
                    s["alive"] = False
                    s["down_until"] = now + random.uniform(9, 16)
                    s["last_gap"] = int(s["down_until"] - now)
                    continue
                if not s["alive"]:                 # just came back
                    s["alive"] = True
                    s["dropouts"] += 1
                    if random.random() < 0.6:      # brown-out: uptime resets
                        s["boot"] = now
                uptime = int(now - s["boot"])
                s["dedup"] = min(100, s["dedup"] + random.choice([0, 0, 1]))
                s["temp"] = max(38, min(63, s["temp"] + random.choice([-1, 0, 0, 1])))
                s["buffered"] = max(0, s["buffered"] + random.randint(-12, 10))
                if s["dedup"] >= 100 and random.random() < 0.3:
                    s["dropped"] += random.randint(1, 5)
                rec_min = 0 if role == "ble" else random.randint(28, 95)
                ble_min = random.randint(6, 24) if role == "ble" else 0
                lo, hi = sl
                line = "CNODE,%d,%s,%s,%d,%d,%d,%d,%d,%d,%d,%s,%d,%d,%d,%d,%d,1,0" % (
                    idx, mac, role, lo, hi,
                    random.randint(88, 100),                       # cov%
                    rec_min or ble_min, s["buffered"], s["temp"], uptime,
                    "v31", s["dropped"], s["dedup"],
                    random.randint(40, 180),                       # hops/min
                    s["dropouts"], s["last_gap"])
                emit(line)
            # --- fleet wardrive hits (CWD) ---
            live = [f for f in fleet if st[f[1]]["alive"] and st[f[1]]["down_until"] <= now]
            if st[joiner[1]]["active"] and st[joiner[1]]["alive"]:
                live.append(joiner)
            for _ in range(random.randint(2, 7)):
                if not live:
                    break
                idx, mac, role, sl = random.choice(live)
                lo, hi = sl
                if role == "ble":
                    band, ch, freq = "ble", 0, 0
                    bssid = "%02X:%02X:%02X:%02X:%02X:%02X" % tuple(
                        random.randint(0, 255) for _ in range(6))
                    ssid = random.choice(["Tile", "", "Galaxy Buds", "Mi Band 7", ""])
                    auth = "[BLE]"
                else:
                    ci = random.randint(lo, hi)
                    ch = self._SIM_CHANNELS[ci % len(self._SIM_CHANNELS)]
                    band = "2.4" if ch <= 14 else "5"
                    freq = 2407 + ch * 5 if ch <= 14 else 5000 + ch * 5
                    bssid = "%02X:%02X:%02X:%02X:%02X:%02X" % tuple(
                        random.randint(0, 255) for _ in range(6))
                    ssid = random.choice(ssids)
                    auth = random.choice(auths)
                rssi = random.randint(-92, -38)
                b64 = base64.b64encode(ssid.encode()).decode() if ssid else ""
                # CWD field 2 is the SCANNED AP's BSSID (the node is identified by idx),
                # not the node's own MAC.
                emit("CWD,%d,%s,%s,%s,%d,%d,%d,%s" % (idx, bssid, b64, auth, ch, freq, rssi, band))
            # --- a 6th node asks to join (awaits operator [A]) ---
            if t_join_req and now >= t_join_req:
                jm = joiner[1]
                if not st[jm]["joined"] and not st[jm]["active"]:
                    st[jm]["joined"] = True
                    emit("CJOIN,%s" % jm)
                t_join_req = 0.0
            # re-ask every few s until accepted
            if (st[joiner[1]]["joined"] and not st[joiner[1]]["active"]
                    and joiner[1] not in self._cluster_joins
                    and random.random() < 0.25):
                emit("CJOIN,%s" % joiner[1])
            # --- occasional fleet event (CEVT) ---
            if t_evt and now >= t_evt:
                m = random.choice(fleet)[1]
                emit("CEVT,%s,%s" % (m[-4:], random.choice(
                    ["channel rebalance", "dedup table full — oldest evicted",
                     "watchdog reboot recovered", "PSRAM ring 80%"])))
                t_evt = now + random.uniform(18, 40)
            if stop:
                stop.wait(1.4)
            else:
                time.sleep(1.4)

    def _ingest_cluster_line(self, line: str) -> None:
        """Parse one cluster-serial line (see the cluster-serial protocol)."""
        try:
            parts = line.rstrip("\r\n").split(",")
            kind = parts[0]
            if kind == "CNODE" and len(parts) >= 13:
                # Final format (cluster-serial protocol), from the node's
                # CLAIM: idx,MAC,role,claim_lo,claim_hi,cov,rec_min,buffered,temp_c,
                # uptime_s,fw,dropped,dedup_pct,hops_min,dropouts,last_gap_s,
                # assigned_by_core,serial_drop. Older firmware sends fewer -> default.
                g = lambda i, d="": parts[i] if i < len(parts) else d

                def _i(v):
                    try:
                        return int(v)
                    except (TypeError, ValueError):
                        return 0
                mac = g(2)
                dedup = _i(g(13))
                temp = g(9)
                _nd = {
                    "idx": _i(g(1)), "mac": mac, "role": g(3),
                    "ch": "%s-%s" % (g(4, "?"), g(5, "?")),
                    "lo": _i(g(4)), "hi": _i(g(5)),
                    "cov": g(6), "rec_min": g(7), "buffered": g(8),
                    "temp": "--" if temp in ("-128", "", "?") else temp,
                    "uptime": g(10), "fw": g(11), "drops": g(12),
                    "dedup": dedup, "full": dedup >= 70,
                    "hops": g(14), "dropouts": g(15), "last_gap": g(16),
                    "by_core": g(17) in ("1", "true", "True"),
                    "serial_drop": g(18),
                    "seen": time.time(),
                }
                with self._cluster_lock:
                    _prev = self._cluster_nodes.get(mac)
                    if _prev is not None:       # keep the moment it first checked in
                        _nd["joined"] = _prev.get("joined", _nd["seen"])
                    else:
                        _nd["joined"] = _nd["seen"]
                        self._term("[CLUSTER] node %s online (slice %s)"
                                   % (mac[-4:], _nd["ch"]), "ok")
                    self._cluster_nodes[mac] = _nd
            elif kind == "CJOIN" and len(parts) >= 2:
                mac = parts[1]
                if self._cluster_bridge:
                    # Bridge mode: only the brain emits CJOIN here and it keeps the
                    # pending list itself (cluster_joins); just announce it.
                    if mac:
                        self._term("[CLUSTER] node %s wants to join — [A] to accept" % mac, "tx")
                elif mac and mac not in self._cluster_joins:
                    self._cluster_joins.append(mac)
                    self._term("[CLUSTER] node %s wants to join — [A] to accept" % mac, "tx")
            elif kind == "CEVT" and len(parts) >= 2:
                self._term("[CLUSTER] node %s: %s" % (parts[1], ",".join(parts[2:])), "warn")
            elif kind == "CWD" and len(parts) >= 9:
                # Fleet record -> reuse the wardrive ingest (host stamps GPS+time,
                # dedups). CWD,idx,MAC,SSID_b64,AUTH,CH,FREQ,RSSI,BAND[,age_ms].
                # TODO(age): place at now-age via a host route-history once the
                # firmware sends age_ms (mirrors the Marauder record-age fix).
                self._cluster_recs += 1
                _nowr = time.time()
                self._cluster_rec_marks.append(_nowr)
                if len(self._cluster_rec_marks) > 4000:          # ~ keep 60 s worth
                    self._cluster_rec_marks = [
                        t for t in self._cluster_rec_marks if _nowr - t <= 60.0]
                try:
                    import base64
                    import io as _io
                    ssid = (base64.b64decode(parts[3]).decode("utf-8", "replace")
                            if parts[3] else "")
                    band = parts[8].lower()
                    typ = "BLE" if band == "ble" else "WIFI"
                    _mac_u = parts[2].upper()                      # normalise MAC case
                    if typ == "BLE":
                        self._cluster_ble_seen.add(_mac_u)
                        if self._ble_is_random(_mac_u):            # rotating/private address
                            self._cluster_ble_random.add(_mac_u)
                    else:
                        self._cluster_wifi_seen.add(_mac_u)
                    buf = _io.StringIO()
                    csv.writer(buf).writerow(
                        [parts[2], ssid, parts[4], "", parts[5], parts[6],
                         parts[7], "", "", "", "", "", "", typ])
                    self._ingest_wardrive_row(buf.getvalue().strip(), typ == "BLE",
                                              persist=not self._cluster_demo)
                except Exception:
                    pass
                if self._cluster_recs % 25 == 0:
                    self.set_status("Cluster: %d recs, %d nodes"
                                    % (self._cluster_recs, len(self._cluster_nodes)))
        except Exception:
            pass

    # ------------------------------------------------------------------
    # Evil Twin / Evil Portal (serial-driven, like the OG app)
    # ------------------------------------------------------------------

    @staticmethod
    def _parse_post_fields(line: str) -> str:
        """Parse 'Received POST data: k=v&k2=v2' into 'Email: x | Password: y'."""
        m = re.search(r"post data:\s*(.+)$", line, re.IGNORECASE)
        if not m:
            m = re.search(r"submission:\s*(.+)$", line, re.IGNORECASE)
        if not m:
            return ""
        try:
            fields = {k: v[0] for k, v in parse_qs(m.group(1)).items()}
        except Exception:
            return ""
        parts = []
        for key in ("username", "email", "login", "user"):
            if key in fields:
                parts.append("%s: %s" % (key.title(), fields[key]))
        if "password" in fields:
            parts.append("Password: " + fields["password"])
        for k, v in fields.items():
            if k not in ("username", "email", "login", "user", "password"):
                parts.append("%s: %s" % (k, v))
        return " | ".join(parts)

    def _scan_hist_captures(self) -> list:
        res = []
        try:
            base = Path(self._app_dir) / "loot"
            logs = list(base.glob("*/evil_twin_capture.log")) + list(base.glob("*/portal_passwords.log"))
            for lg in logs:
                try:
                    for line in open(lg, encoding="utf-8", errors="replace"):
                        low = line.lower()
                        if "post data" in low or "form submission" in low:
                            c = self._parse_post_fields(line)
                            if c:
                                res.append(c)
                except Exception:
                    pass
        except Exception:
            pass
        return res

    def captures_all(self) -> list:
        """Session + historical captured credentials (deduped, cached 5s)."""
        now = time.time()
        if now - getattr(self, "_cap_ts", 0) > 5:
            self._cap_hist = self._scan_hist_captures()
            self._cap_ts = now
        seen = set(); out = []
        for c in list(getattr(self, "_cap_hist", [])) + list(self.captures):
            if c not in seen:
                seen.add(c); out.append(c)
        return out

    def cracked_wifi(self) -> list:
        """Cracked WPA-sec passwords for the Captured Data viewer (cached 5s):
        a list of {ssid, password, ap_mac}. Source: loot/passwords/
        wpasec_cracked.json (or the potfile), via Download WPA-SEC."""
        now = time.time()
        if now - getattr(self, "_crk_ts", 0) > 5:
            out = []
            try:
                from watchdogs import upload_manager as UM
                data = UM.load_wpasec_passwords(Path(self._app_dir) / "loot")
                # wpa-sec writes one potfile line per CLIENT seen on an AP, so the
                # same SSID+password repeats many times (121 lines, ~57 nets). Show
                # each cracked credential ONCE, keyed by (ssid, password); keep the
                # first AP MAC and count how many raw rows collapsed.
                seen = {}
                for ssid, entries in (data.get("by_ssid") or {}).items():
                    for e in (entries or []):
                        pw = e.get("password", "")
                        k = (ssid, pw)
                        if k in seen:
                            seen[k]["n"] += 1
                        else:
                            seen[k] = {"ssid": ssid, "password": pw,
                                       "ap_mac": e.get("ap_mac", ""), "n": 1}
                out = list(seen.values())
            except Exception:
                pass
            out.sort(key=lambda x: x["ssid"].lower())
            self._crk_cache = out
            self._crk_ts = now
        return getattr(self, "_crk_cache", [])

    @staticmethod
    def _norm_mac(s: str) -> str:
        """MAC/BSSID down to its 12 hex chars, lowercase (colon-insensitive), so a
        scan's 'aa:bb:..' matches a potfile's 'aabb..'."""
        return "".join(c for c in (s or "").lower() if c in "0123456789abcdef")

    def cracked_bssids(self) -> dict:
        """{normalized_bssid: {ssid, password}} for every cracked AP (cached 5s).
        Built from ALL potfile rows (not the SSID-deduped view) so every AP MAC is
        matchable."""
        now = time.time()
        if now - getattr(self, "_crkb_ts", 0) > 5:
            m = {}
            try:
                from watchdogs import upload_manager as UM
                data = UM.load_wpasec_passwords(Path(self._app_dir) / "loot")
                for ssid, entries in (data.get("by_ssid") or {}).items():
                    for e in (entries or []):
                        k = self._norm_mac(e.get("ap_mac", ""))
                        if len(k) == 12:
                            m[k] = {"ssid": ssid, "password": e.get("password", "")}
            except Exception:
                pass
            self._crkb_cache = m
            self._crkb_ts = now
        return getattr(self, "_crkb_cache", {})

    def crack_match(self, bssid: str):
        """The cracked {ssid, password} for this BSSID, or None (any colon/case form)."""
        if not bssid:
            return None
        return self.cracked_bssids().get(self._norm_mac(bssid))

    def pwned_points(self) -> list:
        """Wardrive GPS points whose BSSID we have a cracked password for — the
        'pwned AP' map markers. [{lat, lon, ssid, password}], cached 5s."""
        now = time.time()
        if now - getattr(self, "_pwnpts_ts", 0) > 5:
            out = []
            crk = self.cracked_bssids()
            if crk:
                seen = set()
                for p in self.loot_points():
                    if p.get("type") != "wifi":
                        continue
                    k = self._norm_mac(p.get("bssid", ""))
                    if k in seen:
                        continue                 # one marker per AP, not per sighting
                    hit = crk.get(k)
                    if hit:
                        seen.add(k)
                        out.append({"lat": p["lat"], "lon": p["lon"],
                                    "ssid": p.get("label") or hit["ssid"],
                                    "password": hit["password"]})
            self._pwnpts_cache = out
            self._pwnpts_ts = now
        return getattr(self, "_pwnpts_cache", [])

    def _check_pwned(self, net) -> None:
        """Called as scan/wardrive networks arrive: if a BSSID is in our cracked
        list, fire a one-shot notification (terminal + status + toast + sound).
        The map shows the location via pwned_points()."""
        try:
            bssid = getattr(net, "bssid", "") or ""
            key = self._norm_mac(bssid)
            if not key or key in self._pwn_seen:
                return
            hit = self.cracked_bssids().get(key)
            if not hit:
                return
            self._pwn_seen.add(key)
            ssid = (getattr(net, "ssid", "") or hit.get("ssid") or "<hidden>")
            self._term("[PWNED] %s (%s) - password known (WPA-sec crack)!"
                       % (ssid[:28], bssid), "ok")
            self.set_status("PWNED: %s - password on file" % ssid[:24])
            self.mc_bubble = ("PWNED  %s  -  password known" % ssid[:26],
                              time.time() + 6.0)
            self._notify_pulse = "emergency"
        except Exception:
            pass

    def portal_ssid(self) -> str:
        if self.state:
            return self.state.evil_twin_ssid or self.state.portal_ssid or "-"
        return "-"

    def get_portals(self) -> list:
        """(name, html|None) built-in + custom portals from loot/portals/."""
        if not HAVE_BACKEND:
            return [("Default (firmware)", None)]
        try:
            return get_all_portals(Path(self._app_dir) / "loot")
        except Exception:
            return [("Default (firmware)", None)]

    def _start_attack_worker(self, name, sequence):
        with self._attack_lock:
            if self._attack_worker and self._attack_worker.is_alive():
                return
            self.ensure_session()
            self.captures = []
            cancelled = threading.Event()

            def send(cmd):
                # The HTML uploader also uses this callback for every chunk.
                with self._attack_lock:
                    if cancelled.is_set():
                        raise CancelledError
                    self.send(cmd)

            def run():
                try:
                    sequence(cancelled, send)
                except CancelledError:
                    pass

            self._attack_cancel = cancelled
            self._attack_worker = threading.Thread(target=run, name=name, daemon=True)
            self._attack_worker.start()

    def run_evil_twin(self, select_args: str, html, ssid: str) -> None:
        """Threaded: stop -> select_networks -> (upload html) -> start_evil_twin."""
        def seq(cancelled, send):
            if html is not None:
                self._term("[ET] uploading portal HTML...", "tx")
                upload_html_to_esp32(html, send)
                if cancelled.wait(0.4):
                    return
            self._term("[ET] stop (clean state)", "tx")
            send("stop")
            if cancelled.wait(1.5):
                return
            with self._attack_lock:
                if cancelled.is_set():
                    return
                if self.serial and self.serial.is_open:
                    try:
                        self.serial.read_available()  # drain stale
                    except Exception:
                        pass
                self.send("select_networks " + select_args)
            if cancelled.wait(0.5):
                return
            with self._attack_lock:
                if cancelled.is_set():
                    return
                self.send("start_evil_twin")
                if self.state:
                    self.state.evil_twin_running = True
                    self.state.evil_twin_ssid = ssid
                self.set_status("Evil Twin live - SSID " + ssid)
                self._term("[ET] running - SSID " + ssid, "warn")

        self._start_attack_worker("evil-twin", seq)

    def run_evil_portal(self, ssid: str, html) -> None:
        """Threaded: (upload html) -> start_portal <ssid>."""
        def seq(cancelled, send):
            if html is not None:
                self._term("[EP] uploading portal HTML...", "tx")
                upload_html_to_esp32(html, send)
                if cancelled.wait(0.4):
                    return
            with self._attack_lock:
                if cancelled.is_set():
                    return
                self.send("start_portal " + ssid)
                if self.state:
                    self.state.portal_running = True
                    self.state.portal_ssid = ssid
                self.set_status("Evil Portal live - SSID " + ssid)
                self._term("[EP] running - SSID " + ssid, "warn")

        self._start_attack_worker("evil-portal", seq)

    def stop_attacks(self) -> None:
        """Unified hard STOP: ESP32 + host-side data sources + fleet. Safe to call
        repeatedly (map 'S', menu STOP ALL, exit all route here)."""
        with self._attack_lock:
            worker = self._attack_worker
            if self._attack_cancel is not None:
                self._attack_cancel.set()
            self.send("stop")
            # Stop the host data producers FIRST so a late scan/fleet callback can't
            # re-populate state right after we clear it. Both are idempotent.
            try:
                self.stop_wardrive_serial()     # host Wi-Fi scanner thread
            except Exception:
                pass
            try:
                self.stop_cluster()             # node fleet controller
            except Exception:
                pass
            self._wardrive_serial = None
            if self.state:
                self.state.evil_twin_running = False
                self.state.portal_running = False
        if worker and worker is not threading.current_thread():
            worker.join(timeout=1.0)
        # stop any host-side subsystems we started
        for name in ("sdr", "lora", "dragon", "mitm", "subghz"):
            m = self._mgrs.get(name)
            if m is None:
                continue
            try:
                (getattr(m, "stop", None) or (lambda: None))()
            except Exception:
                pass

    # ------------------------------------------------------------------
    # Host-side subsystems (reuse the OG manager classes, run in threads)
    # ------------------------------------------------------------------

    def _mgr(self, name: str):
        """Lazily build + cache a manager. Heavy deps (scapy/bleak/SDR) import
        only on first use so a missing optional dep never breaks startup."""
        if name in self._mgrs:
            return self._mgrs[name]
        # dragon/mitm capture the loot handle at CONSTRUCTION time, so the write
        # session must exist before they are built — otherwise they'd log to
        # nothing. Any action that produces logs starts its own session.
        if name in ("dragon", "mitm"):
            self.ensure_session()
        obj = None
        try:
            if name == "dragon":
                from watchdogs.dragon_drain import DragonDrainAttack
                obj = DragonDrainAttack(msg_fn=lambda s, *a: self._term(s, "raw"), loot=self.loot)
            elif name == "mitm":
                from watchdogs.mitm import MITMAttack
                obj = MITMAttack(msg_fn=lambda s, *a: self._term(s, "raw"), loot=self.loot)
            elif name == "sdr":
                from watchdogs.sdr_manager import SDRManager
                obj = SDRManager()
            elif name == "lora":
                from watchdogs.lora_manager import LoRaManager
                obj = LoRaManager()
            elif name == "meshtastic":
                from watchdogs.meshtastic_manager import MeshtasticManager
                _kmap = {"error": "err", "dim": "raw"}
                obj = MeshtasticManager(
                    emit=lambda m, k="dim": self._term("[MT] " + m, _kmap.get(k, k)),
                    on_node=self._mt_on_node,
                    on_message=self._mt_on_message)
            elif name == "flipper":
                from watchdogs.flipper_manager import FlipperManager
                obj = FlipperManager()
            elif name == "subghz":
                from watchdogs.subghz_manager import SubGhzManager
                obj = SubGhzManager()
            elif name == "watch":
                from watchdogs.watch_manager import WatchManager
                obj = WatchManager()
            elif name == "prox":
                from watchdogs.proximity_manager import ProximityManager
                obj = ProximityManager()
            elif name == "aio":
                from watchdogs.aio_manager import AioManager
                obj = AioManager
        except Exception as exc:
            self._term(f"{name} unavailable: {exc}", "warn")
            obj = None
        self._mgrs[name] = obj
        return obj

    def _thread(self, fn, name="host"):
        threading.Thread(target=fn, name=name, daemon=True).start()

    def host_action(self, cmd: str, target=None) -> bool:
        """Dispatch a `_`-prefixed menu command to the right subsystem.
        `target` = optionally the selected Network (for bssid-based attacks)."""
        table = {
            "_toggle_gps": self._act_gps,
            "_toggle_lora": self._act_lora,
            "_toggle_sdr": self._act_sdr,
            "_sdr_adsb": lambda: self._act_sdr_mode("adsb"),
            "_sdr_433": lambda: self._act_sdr_mode("433"),
            "_sdr_emergency": lambda: self._act_sdr_mode("emergency"),
            "_sdr_keyhunt": lambda: self._act_sdr_mode("keyhunt"),
            "_keyhunt_beep": self._act_keyhunt_beep,
            "_sdr_grab433": lambda: self._act_sdr_mode("grab433"),
            "_dragon_drain": lambda: self._act_dragon(target),
            "_mitm": self._act_mitm,
            "_meshcore": self._act_meshcore,
            "_wdgwars": self._act_meshcore,
            "_flipper": self._act_flipper,
            "_subghz": self._act_subghz,
            "_watch_connect": self._act_watch,
            "_wpasec_upload": self._act_wpasec_up,
            "_wpasec_download": self._act_wpasec_dl,
            "_wigle_upload": self._act_wigle_up,
            "_flash_esp32": self._act_flash,
            "_update_game": self._act_update,
            "_reboot_esp32": lambda: self.send("reboot"),
            "_mute_toggle": self._act_mute,
            "_toggle_usb": self._act_usb,
            "_meshcore_region": self._act_mc_region,
            "_prox_toggle": self._act_prox,
            "_prox_view": self._act_prox_view,
            "_whitelist": self._act_whitelist,
            "_bd_wip": lambda: self._term("[BD] BlueDucky BLE-HID - WIP (D-Bus, run OG game)", "warn"),
            "_race_wip": lambda: self._term("[RACE] Airoha BT exploit - WIP (bleak, run OG game)", "warn"),
            "_bt_hid_wip": lambda: self._term("[HID] BLE HID keyboard - WIP (run OG game)", "warn"),
            "_srv_wiki": lambda: self._act_srv("wiki"),
            "_srv_ctos": lambda: self._act_srv("ctos"),
            "_srv_nav": lambda: self._act_srv("nav"),
            "_srv_status": lambda: self._act_srv("status"),
            "_backup_export": self.export_userdata,
            "_backup_import": self.import_userdata,
        }
        fn = table.get(cmd)
        if fn is None:
            return False
        try:
            fn()
        except Exception as exc:
            self._term(f"{cmd} error: {exc}", "warn")
        return True

    # ---- SYSTEM toggles ----
    def _aio_gps(self, on: bool) -> None:
        """Power the AIO v2 GPS rail (GPIO27) on/off. The GPS module is unpowered
        without it, so this MUST run before gps.setup() - same as the LoRa/SDR rails.
        This is what the OG game did on every GPS toggle; NG had lost it."""
        aio = self._mgr("aio")
        try:
            if aio and aio.is_installed():
                aio.toggle("gps", on)
                if on:
                    time.sleep(0.3)
        except Exception as exc:
            self._term(f"[GPS] AIO rail toggle: {exc}", "warn")

    def _gps_bring_up(self) -> bool:
        """Power the rail and open the GPS, waiting a few seconds for the module to
        start emitting NMEA after a cold rail power-on. Returns True when open."""
        if not self.gps:
            return False
        if self.gps_on:
            return True
        self._aio_gps(True)
        for _ in range(6):                       # ~6 s: a cold GPS needs time to talk
            try:
                if self.gps.setup():
                    self.gps_on = True
                    if self.state:
                        self.state.gps_available = True
                    return True
            except Exception:
                pass
            time.sleep(1.0)
        return False

    def _act_gps(self):
        if self.gps and self.gps_on:
            self.gps.close(); self.gps_on = False
            if self.state: self.state.gps_fix_valid = False
            self._aio_gps(False)                 # cut the rail, like the OG game
            self._term("[SYS] GPS disabled", "warn")
        else:
            try:
                self._term("[SYS] enabling GPS (powering the AIO rail)...", "raw")
                if self._gps_bring_up():
                    self._term("[SYS] GPS enabled %s" % (self.gps.device or ""), "ok")
                else:
                    self._term("[SYS] GPS: no device after powering the rail "
                               "(check the AIO GPS antenna / module)", "warn")
            except Exception as exc:
                self._term(f"[SYS] GPS error: {exc}", "warn")

    def ensure_gps(self, reason: str) -> bool:
        """A capability that needs GPS calls this first. Powers up and opens the GPS
        if it is off (like the SDR check for ADS-B), and says whether there is a fix
        yet. Returns True if GPS is on (a fix may still be pending - wardriving records
        either way and geotags rows once the fix arrives)."""
        if not self.gps_on:
            # Bring GPS up in the BACKGROUND: _gps_bring_up() can block for several
            # seconds (cold rail + per-port setup waits), which would freeze the UI
            # loop (no frames, no STOP, no serial drain). Data collection starts now;
            # rows geotag once the fix arrives. One attempt at a time.
            if not getattr(self, "_gps_starting", False):
                self._gps_starting = True
                self._term("[%s] needs GPS - enabling it in the background..." % reason, "warn")
                def _bring():
                    try:
                        if self._gps_bring_up():
                            self._term("[SYS] GPS enabled %s" % (self.gps.device or ""), "ok")
                        else:
                            self._term("[%s] GPS could not start - rows will have no "
                                       "position until GPS works" % reason, "warn")
                    finally:
                        self._gps_starting = False
                self._thread(_bring, "gps-start")
            return False
        if not (self.state and getattr(self.state, "gps_fix_valid", False)):
            self._term("[%s] GPS searching for a fix - rows geotag once it locks" % reason, "raw")
        return True

    def _lora_region(self) -> str:
        return getattr(self, "_mc_region", None) or os.environ.get("WDG_MC_REGION", "eu_uk_default")

    def _aio_lora(self, on: bool) -> None:
        """Power the AIO v2 LoRa rail on/off — REQUIRED before SX1262 init."""
        aio = self._mgr("aio")
        try:
            if aio and aio.is_installed():
                aio.toggle("lora", on)
                if on:
                    time.sleep(0.4)
        except Exception as exc:
            self._term(f"[LoRa] AIO toggle: {exc}", "warn")

    def _act_lora(self):
        lora = self._mgr("lora")
        if lora is None:
            self._term("[LoRa] manager unavailable", "warn"); return
        if not self._claim_mesh_op():               # serialized with stack switches
            self._term("[LoRa] radio switch already in progress...", "warn"); return
        def run():
            try:
                if getattr(lora, "running", False):
                    try:
                        stopped = lora.stop()
                    except Exception as exc:
                        self._term(f"[LoRa] stop failed: {exc}", "warn")
                        stopped = False
                    if stopped is False:            # thread still up: rail stays on
                        self._report_radio_busy()
                        return
                    self._cut_lora_rail(); self._term("[LoRa] stopped", "warn")
                else:
                    holder = self._meshtasticd_holder()
                    if holder:                      # meshtasticd owns the SX1262
                        self._report_radio_held(holder, "[LoRa]")
                        return
                    self._aio_lora(True)                    # power the SX1262 rail FIRST
                    lora.start_meshcore(self._lora_region())
                    self._wire_meshcore()
                    if getattr(lora, "running", False):
                        self._term("[LoRa] MeshCore started", "ok")
                    else:
                        self._cut_lora_rail()
                        self._term("[LoRa] SX1262 init failed (AIO/antenna?)", "warn")
            except Exception as exc:
                self._term(f"[LoRa] {exc}", "warn")
            finally:
                self._mesh_switching = False
        try:
            self._thread(run, "lora")
        except Exception:
            self._mesh_switching = False
            raise

    def _aio_sdr(self, on: bool) -> None:
        """Power the AIO v2 SDR rail on/off — the RTL dongle is dead without it,
        so this MUST run before dump1090/rtl_433 start (same story as the LoRa rail)."""
        aio = self._mgr("aio")
        try:
            if aio and aio.is_installed():
                aio.toggle("sdr", on)
                self._sdr_rail = on
                if on:
                    time.sleep(0.4)
        except Exception as exc:
            self._term(f"[SDR] AIO toggle: {exc}", "warn")

    def _act_sdr(self):
        aio = self._mgr("aio")
        try:
            if aio and aio.is_installed():
                cur = (aio.get_status() or {}).get("sdr")
                if not isinstance(cur, bool):     # a toggle needs a real reading
                    self._term("[SDR] rail state unknown (GPIO read failed) - not toggling", "warn")
                    return
                new = not cur
                aio.toggle("sdr", new)
                self._sdr_rail = new
                if not new:
                    sdr = self._mgrs.get("sdr")
                    if sdr and getattr(sdr, "running", False):
                        sdr.stop()         # no power -> stop any running mode too
                self._term("[SDR] rail " + ("ON" if new else "off"), "ok")
            else:
                self._term("[SDR] AIO v2 not available", "warn")
        except Exception as exc:
            self._term(f"[SDR] {exc}", "warn")

    # ---- addon hardware dependencies (check + enable before launching) ----
    def module_ready(self, kind: str) -> bool:
        """Is the hardware module an addon needs powered/running? kind: lora|sdr|gps."""
        aio = self._mgr("aio")
        st = (aio.get_status() or {}) if (aio and aio.is_installed()) else {}
        if kind == "lora":
            return bool(st.get("lora", False))
        if kind == "sdr":
            return bool(self._sdr_rail or st.get("sdr", False))
        if kind == "gps":
            return bool(self.gps_on or st.get("gps", False))
        return True

    def enable_module(self, kind: str) -> None:
        """Power on the module rail for an addon (LoRa/SDR/GPS via AIO v2)."""
        try:
            if kind == "lora":
                self._aio_lora(True)
            elif kind == "sdr":
                self._aio_sdr(True)
            elif kind == "gps" and not self.gps_on:
                self._act_gps()
            self._term("[DEP] %s module enabled" % kind.upper(), "ok")
        except Exception as exc:
            self._term("[DEP] %s enable failed: %s" % (kind, exc), "warn")

    def _act_sdr_mode(self, mode):
        sdr = self._mgr("sdr")
        if sdr is None:
            self._term("[SDR] manager unavailable", "warn"); return
        def run():
            try:
                if getattr(sdr, "running", False) and mode in getattr(sdr, "mode", ""):
                    sdr.stop(); self._term(f"[SDR] {mode} stopped", "warn"); return
                # power the RTL dongle's rail FIRST (OG makes you enable SDR by hand;
                # we do it automatically so the mode — and the RADIO indicator — light up)
                self._aio_sdr(True)
                # Start a real loot session so the scan actually gets logged. The
                # loot session is lazy (first-capture only); without this an SDR
                # scan run on a fresh launch wrote to loot_dir="" -> NO logs saved.
                self.ensure_session()
                loot_dir = self.loot.session_dir if (self.loot and self.loot.active) else ""
                lat = self.state.gps_latitude if (self.state and self.state.gps_fix_valid) else 0.0
                lon = self.state.gps_longitude if (self.state and self.state.gps_fix_valid) else 0.0
                if mode == "adsb":
                    if not self.gps_on:
                        self._term("[ADS-B] tip: enable GPS for receiver position + range "
                                   "(aircraft are still logged without it)", "raw")
                    ok = sdr.start_adsb(loot_dir)
                elif mode == "433":
                    ok = sdr.start_433(loot_dir, lat, lon)
                elif mode == "keyhunt":
                    ok = sdr.start_key_hunt(loot_dir, lat, lon)
                elif mode == "grab433":
                    ok = sdr.start_433_grab(loot_dir, lat, lon)
                else:
                    ok = sdr.start_emergency(loot_dir, lat, lon)
                if ok:
                    self._term(f"[SDR] {mode} active — RADIO {mode.upper()}", "ok")
                else:
                    shown = False
                    for etype, data in sdr.poll_events():
                        if etype == "error":
                            self._term(f"[SDR] {data}", "warn"); shown = True
                    if not shown:
                        tool = ("dump1090" if mode == "adsb"
                                else "rtl_433" if mode == "433" else "rtl_power")
                        self._term(f"[SDR] {mode} failed to start (check {tool} + RTL dongle)", "warn")
            except Exception as exc:
                self._term(f"[SDR] {mode}: {exc}", "warn")
        self._thread(run, "sdr")

    # ---- attacks ----
    def _act_dragon(self, target):
        dd = self._mgr("dragon")
        if dd is None:
            self._term("[DD] scapy/root required", "warn"); return
        def run():
            try:
                if getattr(dd, "running", False):
                    dd.stop(); self._term("[DD] stopped", "warn"); return
                mons = dd.detect_monitor_ifaces()
                iface = mons[0] if mons else ""
                if not iface:
                    mgd = dd.detect_managed_ifaces()
                    if mgd and dd.enable_monitor(mgd[0][0]):
                        iface = mgd[0][0]
                if not iface:
                    self._term("[DD] no monitor-capable WiFi iface", "warn"); return
                bssid = getattr(target, "bssid", "") if target else ""
                if not bssid:
                    found = dd.scan_wpa3(iface, 8)
                    if found:
                        bssid = found[0].get("bssid", "")
                if not bssid:
                    self._term("[DD] no WPA3 target (scan+select one)", "warn"); return
                if dd.start(bssid, iface):
                    self._term(f"[DD] Dragon Drain -> {bssid} on {iface}", "ok")
            except Exception as exc:
                self._term(f"[DD] {exc}", "warn")
        self._thread(run, "dragon")

    def _act_mitm(self):
        mm = self._mgr("mitm")
        if mm is None:
            self._term("[MITM] scapy/root required", "warn"); return
        def run():
            try:
                if getattr(mm, "running", False):
                    mm.stop(); self._term("[MITM] stopped", "warn"); return
                ifaces = mm.get_interfaces()
                if not ifaces:
                    self._term("[MITM] no network interface", "warn"); return
                iface = ifaces[0][0]
                if mm.start(iface):
                    self._term(f"[MITM] ARP spoof on {iface}", "ok")
            except Exception as exc:
                self._term(f"[MITM] {exc}", "warn")
        self._thread(run, "mitm")

    # ---- LoRa mesh ----
    def _act_meshcore(self):
        lora = self._mgr("lora")
        if lora is None:
            self._term("[MC] LoRa manager unavailable", "warn"); return
        if not self._claim_mesh_op():               # serialized with stack switches
            self._term("[MC] radio switch already in progress...", "warn"); return
        def run():
            try:
                if not getattr(lora, "running", False):
                    holder = self._meshtasticd_holder()
                    if holder:                      # meshtasticd owns the SX1262
                        self._report_radio_held(holder, "[MC]")
                        return
                    self._aio_lora(True)                    # power rail first
                    lora.start_meshcore(self._lora_region())
                self._wire_meshcore()
                if getattr(lora, "running", False):
                    self._term("[MC] MeshCore messenger ready", "ok")
                else:
                    self._cut_lora_rail("[MC]")
                    self._term("[MC] SX1262 init failed (enable AIO/antenna)", "warn")
            except Exception as exc:
                self._term(f"[MC] {exc}", "warn")
            finally:
                self._mesh_switching = False
        try:
            self._thread(run, "meshcore")
        except Exception:
            self._mesh_switching = False
            raise

    # ---- Messengers: MeshCore (LoRa) + WDGWars (Reticulum/LXMF) ----
    def _mc_on_message(self, channel, message, rssi=0, hops=0):
        self.mc_log.append(("in", str(message), "in"))
        self.mc_bubble = (str(message)[:60], time.time() + 5.0)
        self._notify_pulse = "mesh"           # UI plays the notify sound on the main thread
        self.earn_badge("meshcore")
        try:                                  # persist to loot (was UI-only before)
            self.ensure_session()
            if self.loot:
                with self._loot_lock:
                    self.loot.save_meshcore_message(str(channel), str(message), float(rssi or 0))
        except Exception:
            pass

    def _mc_on_dm(self, from_id, message, rssi=0, hops=0):
        self.mc_log.append(("in", "[DM] " + str(message), "dm"))
        self.mc_bubble = ("[DM] " + str(message)[:54], time.time() + 5.0)
        self._notify_pulse = "mesh"
        try:                                  # persist DMs too (was UI-only; channel msgs already save)
            self.ensure_session()
            if self.loot:
                with self._loot_lock:
                    self.loot.save_meshcore_message("DM:" + str(from_id), str(message), float(rssi or 0))
        except Exception:
            pass

    def is_muted(self) -> bool:
        return bool(getattr(self, "_muted", False))

    def consume_notify(self) -> str:
        """Return a one-shot notification kind ('mesh'|'emergency'|…) then clear it —
        the UI plays the matching sound on the main thread (audio isn't thread-safe)."""
        p = getattr(self, "_notify_pulse", None)
        self._notify_pulse = None
        return p

    def _wire_meshcore(self):
        lora = self._mgrs.get("lora")
        if lora is not None:
            try:
                lora._on_message = self._mc_on_message
                lora._on_dm = self._mc_on_dm
                lora._on_node = self._mc_on_node
            except Exception:
                pass

    def _mc_on_node(self, node_id, ntype=0, name="", lat=0.0, lon=0.0, rssi=0, snr=0, pubkey=b""):
        # pubkey is the 8th arg LoRaManager passes for MeshCore adverts; accept it
        # (the old 7-arg signature raised TypeError on every advert, silently caught
        # in lora_manager, so NO node ever reached loot/map/WDGWars).
        try:
            lat, lon = float(lat or 0), float(lon or 0)
            nm = str(name or node_id)[:16]
            if lat or lon:
                self._mc_nodes[str(node_id)] = {
                    "lat": lat, "lon": lon, "name": nm, "type": ntype}
            self._log_mesh_node(str(node_id), str(ntype), nm, lat, lon, rssi, snr)
            if self.loot:                     # fill the CONTACTS panel/counter (store was never populated)
                with self._loot_lock:
                    self.loot.save_contact(str(node_id), {"name": nm, "type": ntype,
                                                          "lat": lat, "lon": lon,
                                                          "rssi": rssi, "snr": snr})
        except Exception:
            pass

    def _log_mesh_node(self, node_id, ntype, name, lat, lon, rssi=0, snr=0) -> None:
        """Persist a seen mesh node (MeshCore OR Meshtastic) to loot so it's
        counted and uploaded to WDGWars, like OG MeshCore. Dedup lives in
        loot_manager (by node_id). Positioned nodes also light up the map."""
        try:
            self.ensure_session()
            if self.loot:
                with self._loot_lock:
                    self.loot.save_meshcore_node(node_id, ntype, name,
                                                 float(lat or 0), float(lon or 0),
                                                 float(rssi or 0), float(snr or 0))
        except Exception:
            pass

    def mc_nodes(self) -> list:
        """MeshCore nodes that advertised a GPS position (for map icons)."""
        return _snapshot(getattr(self, "_mc_nodes", {}))

    # ---- Meshtastic (native, via meshtasticd) ----
    def _mt_on_node(self, rec) -> None:
        try:
            nid = str(rec.get("id"))
            lat = float(rec.get("lat") or 0)
            lon = float(rec.get("lon") or 0)
            nm = str(rec.get("name") or nid)[:16]
            if lat or lon:
                self._mt_nodes[nid] = {"lat": lat, "lon": lon, "name": nm, "type": "mt"}
            self._log_mesh_node(nid, "meshtastic", nm, lat, lon,
                                rec.get("rssi"), rec.get("snr"))
        except Exception:
            pass

    def _mt_on_message(self, name, text) -> None:
        self.mc_bubble = (("MT %s: %s" % (name, text))[:60], time.time() + 5.0)
        self._notify_pulse = "mesh"
        self.earn_badge("meshcore")

    def mt_nodes(self) -> list:
        """Meshtastic nodes with a GPS position (for map icons)."""
        return _snapshot(getattr(self, "_mt_nodes", {}))

    def mt_available(self) -> bool:
        try:
            from watchdogs.meshtastic_manager import MeshtasticManager
            return MeshtasticManager.available()
        except Exception:
            return False

    def mt_running(self) -> bool:
        m = self._mgrs.get("meshtastic")
        return bool(m and getattr(m, "running", False))

    def mt_messages(self) -> list:
        m = self._mgrs.get("meshtastic")
        return _snapshot(getattr(m, "messages", [])) if m else []

    def mt_send(self, text: str) -> None:
        m = self._mgrs.get("meshtastic")
        if m and getattr(m, "running", False):
            m.send(text)

    def mt_regions(self) -> list:
        from watchdogs.meshtastic_manager import MT_REGIONS
        return list(MT_REGIONS)

    def mt_presets(self) -> list:
        from watchdogs.meshtastic_manager import MT_PRESETS
        return list(MT_PRESETS)

    def mt_region_current(self) -> str:
        return self._mesh.get("mt_region", "EU_868")

    def mt_preset_current(self) -> str:
        return self._mesh.get("mt_preset", "LONG_FAST")

    def mt_set_region(self, key: str) -> None:
        self._mesh["mt_region"] = key
        self._save_mesh_settings()
        m = self._mgrs.get("meshtastic")
        if m and getattr(m, "running", False):
            self._thread(lambda: m.set_region(key), "mt-cfg")

    def mt_set_preset(self, key: str) -> None:
        self._mesh["mt_preset"] = key
        self._save_mesh_settings()
        m = self._mgrs.get("meshtastic")
        if m and getattr(m, "running", False):
            self._thread(lambda: m.set_preset(key), "mt-cfg")

    def mt_name(self) -> str:
        m = self._mgrs.get("meshtastic")
        return (getattr(m, "my_name", "") if m else "") or self._mesh.get("mt_name", "")

    def mt_set_name(self, long_name: str, short_name: str = "") -> None:
        self._mesh["mt_name"] = long_name
        self._save_mesh_settings()
        m = self._mgrs.get("meshtastic")
        if m and getattr(m, "running", False):
            self._thread(lambda: m.set_owner(long_name, short_name), "mt-cfg")

    # ---- LoRa Mesh stack arbiter (MeshCore <-> Meshtastic on the shared SX1262) ----
    def mesh_stack(self) -> str:
        return self._mesh.get("stack", "")

    def start_mesh(self, stack: str) -> None:
        """Switch the active LoRa mesh stack in the background: 'meshcore',
        'meshtastic', or 'off'. One at a time on the shared SX1262. The new stack
        is published (mesh_stack() + settings) only once it is really up; until
        then the UI keeps showing the previous one."""
        if not self._claim_mesh_op():
            self._term("[MESH] switch already in progress...", "warn")
            return
        def _run():
            try:
                self._start_mesh(stack)
            finally:
                self._mesh_switching = False
        try:
            self._thread(_run, "mesh-switch")
        except Exception:
            self._mesh_switching = False
            raise

    def _claim_mesh_op(self) -> bool:
        """Atomically take the one-at-a-time LoRa switch/retune slot."""
        with Backend._MESH_GUARD:
            if getattr(self, "_mesh_switching", False):
                return False
            self._mesh_switching = True
            return True

    def _publish_live_stack(self) -> None:
        """After a failed or refused switch, publish what is REALLY on the radio."""
        lora = self._mgrs.get("lora")
        mt = self._mgrs.get("meshtastic")
        if lora is not None and getattr(lora, "running", False):
            live = "meshcore"
        elif mt is not None and getattr(mt, "running", False):
            live = "meshtastic"
        else:
            live = ""
        if self._mesh.get("stack", "") != live:
            self._mesh["stack"] = live
            self._save_mesh_settings()

    @staticmethod
    def _meshtasticd_holder() -> str:
        """'' when no meshtasticd can be holding the SX1262, else who holds it
        ('meshtasticd (pid 1234)', or the API port when no process is visible).
        Called after the game stopped its OWN daemon, so whatever is left was not
        started by the game (or refused to die) and must not lose the radio."""
        pids = []
        try:
            for d in os.listdir("/proc"):
                if not d.isdigit():
                    continue
                try:
                    with open("/proc/%s/comm" % d) as f:
                        if f.read().strip() == "meshtasticd":
                            pids.append(int(d))
                except OSError:
                    continue
        except OSError:
            pass
        if pids:
            return "meshtasticd (pid %s)" % ", ".join(str(x) for x in sorted(pids))
        try:
            from watchdogs.meshtastic_manager import MeshtasticManager, MT_API_PORT
            if MeshtasticManager._port_open():
                return "a meshtasticd API on port %d" % MT_API_PORT
        except Exception:
            pass
        return ""

    def _report_radio_held(self, holder: str, tag: str = "[MESH]") -> None:
        self._term("%s SX1262 still held by %s (not stopped by the game) - "
                   "stop it first (e.g. sudo systemctl stop meshtasticd); "
                   "nothing switched, LoRa rail left as is" % (tag, holder), "warn")
        self.set_status("LoRa radio held by %s" % holder)

    def _cut_lora_rail(self, tag: str = "[LoRa]") -> bool:
        """Power the LoRa rail down unless an outside meshtasticd still uses the
        SX1262 (cutting it would crash that daemon's radio)."""
        holder = self._meshtasticd_holder()
        if holder:
            self._report_radio_held(holder, tag)
            return False
        self._aio_lora(False)
        return True

    def _report_radio_busy(self, tag: str = "[LoRa]") -> None:
        self._term("%s radio busy - the MeshCore thread has not exited yet; "
                   "nothing was switched, try again in a moment" % tag, "warn")
        self.set_status("LoRa radio busy - try again")

    def _release_lora_spi(self, release_gpio: bool = False) -> bool:
        """Fully release the SX1262 SPI so the other stack (meshtasticd) can claim
        it. LoRaManager.stop() ends the worker but LoRaRF keeps /dev/spidev1.0
        open, which blocks meshtasticd's radio init — close it and drop the
        manager so MeshCore rebuilds a fresh one next time.

        When handing the radio to meshtasticd (release_gpio=True) also free the
        SX1262 control GPIO lines. LoRaRF drives RESET/BUSY/IRQ via RPi.GPIO and
        LoRaManager deliberately keeps them claimed (to preserve BCM pin mode for
        a fast MeshCore restart). meshtasticd's libgpiod then can't request those
        lines and its SX126x init aborts (gpiod_line_request assertion -> SIGABRT,
        stack shows OFF). Release just those pins (cleanup([...]) keeps the global
        BCM mode, so a later MeshCore begin() still works).

        Returns False (and touches nothing: handle, SPI, GPIO and rail stay as
        they are) when the MeshCore thread did not confirm its exit — stop() is
        always called on an existing manager, also while its thread is still
        winding down, so a later retry can wait for it again."""
        lora = self._mgrs.get("lora")
        if lora is not None:
            try:
                stopped = lora.stop()
            except Exception as exc:
                self._term("[LoRa] stop failed: %s" % exc, "warn")
                stopped = False
            if stopped is False:
                self._report_radio_busy()
                return False
        try:
            from LoRaRF import SX126x as _sx
            _sx.spi.close()
        except Exception:
            pass
        if release_gpio:
            try:
                from LoRaRF.SX126x import gpio as _g
                from watchdogs.lora_manager import PIN_RESET, PIN_BUSY, PIN_IRQ
                for _p in (PIN_RESET, PIN_BUSY, PIN_IRQ):     # free them for meshtasticd
                    try:
                        _g.cleanup(_p)
                    except Exception:
                        pass
            except Exception:
                pass
        self._mgrs.pop("lora", None)
        return True

    def _start_mesh(self, stack: str) -> None:
        try:
            mt = self._mgrs.get("meshtastic")
            if stack != "meshtastic":
                # The SX1262 must be free of meshtasticd before MeshCore / power-off.
                # Attached to a daemon the game did not start: disconnecting our
                # client would not free the radio, so refuse without touching it.
                if (mt is not None and getattr(mt, "running", False)
                        and not getattr(mt, "owns_daemon", getattr(mt, "_proc", None) is not None)):
                    holder = self._meshtasticd_holder()
                    if holder:
                        self._report_radio_held(holder)
                        return
                if mt is not None and getattr(mt, "running", False):
                    mt.stop()                            # stops OUR daemon only
                holder = self._meshtasticd_holder()      # also when our client was idle
                if holder:
                    self._report_radio_held(holder)
                    self._publish_live_stack()
                    return
            if stack == "off":
                if not self._release_lora_spi():
                    self._publish_live_stack()
                    return
                self._aio_lora(False)                    # holder checked above
                self._mesh["stack"] = ""
                self._save_mesh_settings()
                self._term("[MESH] radio off", "warn")
                return
            if stack == "meshtastic":
                if not self._release_lora_spi(release_gpio=True):  # SPI + GPIO for meshtasticd
                    self._publish_live_stack()
                    return
                time.sleep(0.8)
            self._aio_lora(True)                         # power the SX1262 rail
            if stack == "meshcore":
                lora = self._mgr("lora")
                if lora and not getattr(lora, "running", False):
                    lora.start_meshcore(self._lora_region())
                    self._wire_meshcore()
                ok = bool(lora and getattr(lora, "running", False))
            else:                                        # meshtastic
                mt = self._mgr("meshtastic")
                ok = bool(mt and mt.start(
                    self._mesh.get("mt_region", "EU_868"),
                    self._mesh.get("mt_preset", "LONG_FAST"),
                    owner_long=(self._mesh.get("mt_name") or self.node_name())))
            if ok:
                self._mesh["stack"] = stack              # publish only once it is up
                self._mesh["last_stack"] = stack        # remember for auto-resume
                self._mesh["cfg_mc" if stack == "meshcore" else "cfg_mt"] = True
                self._save_mesh_settings()
                self._term("[MESH] %s active" % stack, "ok")
            else:
                self._cut_lora_rail("[MESH]")            # not under an outside meshtasticd
                self._term("[MESH] %s failed to start" % stack, "warn")
                self._publish_live_stack()
        except Exception as exc:
            self._term("[MESH] %s" % exc, "warn")
            try:
                self._publish_live_stack()
            except Exception:
                pass

    def _lora_rail_on(self) -> bool:
        """True iff the physical AIO LoRa rail (GPIO16) is already powered.
        Read-only — never toggles. False when pinctrl/AIO is absent (e.g. dev)."""
        try:
            aio = self._mgr("aio")
            if aio and aio.is_installed():
                return bool((aio.get_status() or {}).get("lora"))
        except Exception:
            pass
        return False

    def auto_resume_mesh(self) -> None:
        """At game launch, bring up a mesh stack ONLY if the LoRa radio is
        already powered in the system (GPIO16 rail on). Then:
          - last-used configured stack starts (both configured -> last used;
            Meshtastic needs mt_available(), else falls back to the other);
          - rail on but nothing configured -> radio just stays powered, idle;
          - rail off -> nothing happens at all.
        Never powers the rail on itself. One radio: one stack (Ctrl+T flips)."""
        try:
            if not self._lora_rail_on():
                return                                   # radio off in system -> mesh idle
            lora = self._mgrs.get("lora")
            mt = self._mgrs.get("meshtastic")
            if (self._mesh_switching
                    or (lora and getattr(lora, "running", False))
                    or (mt and getattr(mt, "running", False))):
                return                                   # a stack is already live
            cfg = []
            if self._mesh.get("cfg_mc"):
                cfg.append("meshcore")
            if self._mesh.get("cfg_mt") and self.mt_available():
                cfg.append("meshtastic")
            if not cfg:
                return                                   # rail powered but nothing configured -> idle
            last = self._mesh.get("last_stack", "")
            pick = last if last in cfg else cfg[0]
            self._term("[MESH] auto-resume %s (LoRa rail on)" % pick, "ok")
            self.start_mesh(pick)                        # backgrounded + guarded
        except Exception:
            pass

    # ---- mesh settings persistence (stack + per-stack region/band/preset/name) ----
    def _mesh_path(self):
        return Path(self._app_dir) / MESH_SETTINGS_NAME

    def _load_mesh_settings(self) -> None:
        self._mesh = {"stack": "", "mc_region": "eu_uk_default",
                      "mt_region": "EU_868", "mt_preset": "LONG_FAST", "mt_name": "",
                      "last_stack": "", "cfg_mc": False, "cfg_mt": False}
        try:
            p = self._mesh_path()
            if p.is_file():
                data = json.loads(p.read_text()) or {}
                for k in self._mesh:
                    if k in data:
                        self._mesh[k] = data[k]
        except Exception:
            pass
        self._mc_region = self._mesh.get("mc_region") or getattr(self, "_mc_region", None)

    def _save_mesh_settings(self) -> None:
        try:
            self._mesh["mc_region"] = (getattr(self, "_mc_region", None)
                                       or self._mesh.get("mc_region"))
            self._mesh_path().write_text(json.dumps(self._mesh))
        except Exception:
            pass

    def aircraft(self) -> list:
        """Live ADS-B aircraft WITH a position (for the map radar): position,
        altitude, callsign, ICAO id, ground track (heading) and speed (kt)."""
        m = self._mgrs.get("sdr")
        out = []
        if m is not None:
            try:
                for ac in list(m.aircraft.values()):   # snapshot: _sbs_reader mutates from another thread
                    if getattr(ac, "has_position", False):
                        out.append({"lat": ac.lat, "lon": ac.lon, "alt": int(ac.altitude),
                                    "cs": (ac.callsign or ac.icao or "?"),
                                    "icao": ac.icao,
                                    "track": int(getattr(ac, "heading", 0) or 0),
                                    "spd": int(getattr(ac, "speed", 0) or 0)})
            except Exception:
                pass
        return out

    def aircraft_total(self) -> int:
        """Count of ALL aircraft currently tracked (including transponders heard
        without a decoded position), for the radar header."""
        m = self._mgrs.get("sdr")
        try:
            return len(m.aircraft) if m is not None else 0
        except Exception:
            return 0

    def sensors_433(self) -> list:
        """433 MHz sensors (weather/TPMS/remotes) tagged with a GPS position."""
        m = self._mgrs.get("sdr")
        out = []
        if m is not None:
            try:
                for s in list(m.sensors.values()):   # snapshot: _rtl433_reader mutates from another thread
                    if getattr(s, "lat", 0) or getattr(s, "lon", 0):
                        out.append({"lat": s.lat, "lon": s.lon, "sid": getattr(s, "sid", ""),
                                    "model": getattr(s, "model", "")})
            except Exception:
                pass
        return out

    def emergency_active(self) -> tuple:
        """(active, service_band, rssi) for the loudest live emergency signal."""
        m = self._mgrs.get("sdr")
        if m is None or not getattr(m, "emergency_active", False):
            return (False, "", 0)
        try:
            sigs = [s for s in list(m.emergency.values()) if getattr(s, "active", False)]
            if sigs:
                top = max(sigs, key=lambda s: getattr(s, "rssi", -999))
                return (True, str(getattr(top, "band", "")), int(getattr(top, "rssi", 0)))
        except Exception:
            pass
        return (False, "", 0)

    def grab_state(self) -> dict:
        """433 Capture readout: {count, last, dir} (empty if not capturing)."""
        m = self._mgrs.get("sdr")
        if m is None or "grab433" not in getattr(m, "mode", ""):
            return {}
        try:
            return {"count": int(getattr(m, "grab_count", 0)),
                    "last": str(getattr(m, "grab_last", "")),
                    "dir": str(getattr(m, "grab_dir", ""))}
        except Exception:
            return {}

    def keyhunt_beep_level(self) -> int:
        """433 Hunter beep volume: 0=off, 1=low, 2=loud (default loud)."""
        return int(getattr(self, "_keyhunt_beep", 2))

    def _act_keyhunt_beep(self):
        lvl = (int(getattr(self, "_keyhunt_beep", 2)) + 2) % 3   # 2->1->0->2 (loud->low->off)
        self._keyhunt_beep = lvl
        self._term("[433] beep " + ("off" if lvl == 0 else "low" if lvl == 1 else "loud"), "ok")

    def keyhunt_state(self) -> dict:
        """Live Key Hunter readout for the UI (empty dict if not running)."""
        m = self._mgrs.get("sdr")
        if m is None or "keyhunt" not in getattr(m, "mode", ""):
            return {}
        kh = getattr(m, "keyhunt", None)
        if kh is None:
            return {}
        try:
            return {"rssi": kh.rssi, "floor": kh.floor, "jump": kh.jump,
                    "peak_freq": kh.peak_freq, "hot": kh.hot, "best": kh.best,
                    "burst": kh.burst, "hits": kh.hits,
                    "last_burst": kh.last_burst, "sweeps": kh.sweeps,
                    "target_mhz": getattr(kh, "target_mhz", 0.0), "learning": getattr(kh, "learning", False),
                    "other_mhz": getattr(kh, "other_mhz", 0.0), "other_db": getattr(kh, "other_db", 0.0),
                    "overload": getattr(kh, "overload", False)}
        except Exception:
            return {}

    def keyhunt_learn(self) -> None:
        m = self._mgrs.get("sdr")
        if m is not None and "keyhunt" in getattr(m, "mode", ""):
            m.keyhunt_learn()
            self._term("[433] learning: press the remote you want to hunt", "warn")

    def keyhunt_reset_target(self) -> None:
        m = self._mgrs.get("sdr")
        if m is not None and "keyhunt" in getattr(m, "mode", ""):
            m.keyhunt_reset_target()
            self._term("[433] hunting the car key again", "ok")

    def keyhunt_waterfall(self) -> tuple:
        """(rows, axis) for the Key Hunter waterfall — rows = list of dB-bin lists,
        axis = matching freq (MHz). Empty when not running."""
        m = self._mgrs.get("sdr")
        if m is None or "keyhunt" not in getattr(m, "mode", ""):
            return ([], [])
        try:
            return (list(m.keyhunt_wf), list(m.keyhunt_axis))
        except Exception:
            return ([], [])

    def mc_send(self, text: str) -> None:
        lora = self._mgrs.get("lora")
        if lora is not None and getattr(lora, "running", False):
            try:
                lora.send_meshcore_message(text, self.mc_node_name())
                self.mc_log.append(("out", text, "out"))
            except Exception as exc:
                self._term(f"[MC] send: {exc}", "warn")
        else:
            self._term("[MC] enable LoRa first (SYSTEM > LoRa)", "warn")

    def _user_home(self) -> str:
        """The login user's home — deterministic even under sudo (where HOME may be
        /root). Backups and the legacy chat-identity dir live here, not /root."""
        user = os.environ.get("SUDO_USER")
        if user:
            try:
                import pwd
                return pwd.getpwnam(user).pw_dir
            except Exception:
                return "/home/" + user
        return os.path.expanduser("~")

    def _reticulum_configdir(self) -> str:
        """Keep the WDGWars/Reticulum chat identity under loot/ so ALL user data lives
        in one folder. Migrates the legacy ~/.watchdogs_reticulum once."""
        new = os.path.join(self._app_dir, "loot", "reticulum")
        old = os.path.join(self._user_home(), ".watchdogs_reticulum")
        try:
            if not os.path.isdir(new):
                os.makedirs(os.path.join(self._app_dir, "loot"), exist_ok=True)
                if os.path.isdir(old):
                    import shutil
                    # COPY (never move) so the original is preserved as a fallback —
                    # losing a chat identity/group_creds to a bad migration is not ok
                    shutil.copytree(old, new)
                    self._term("[DATA] chat identity consolidated -> loot/reticulum", "ok")
                else:
                    os.makedirs(new, exist_ok=True)
        except Exception as exc:
            self._term("[DATA] reticulum consolidate failed: %s" % exc, "warn")
            return old if os.path.isdir(old) else new
        return new

    # ------------------------------------------------------------------
    # Device identity / display name (shared by WDGWars chat + MeshCore + portal)
    # ------------------------------------------------------------------
    def _hw_id(self) -> str:
        """6-char fingerprint of THIS physical device, stable across reinstalls.
        Derived from the board/CPU serial + machine-id so every uConsole is unique
        (not random). Falls back to the primary MAC, then the hostname."""
        cached = getattr(self, "_hwid_cache", None)
        if cached:
            return cached
        import hashlib
        seed = ""
        try:
            with open("/proc/cpuinfo", "r", errors="replace") as f:
                for ln in f:
                    if ln.lower().startswith("serial"):
                        seed += ln.split(":")[-1].strip()
                        break
        except Exception:
            pass
        for src in ("/sys/firmware/devicetree/base/serial-number", "/etc/machine-id"):
            try:
                with open(src, "rb") as f:
                    seed += f.read().decode("utf-8", "replace").strip("\x00 \n")
            except Exception:
                pass
        if not seed:
            try:
                import uuid
                seed = "%012x" % uuid.getnode()           # MAC fallback
            except Exception:
                seed = getattr(os, "uname", lambda: None)() and os.uname().nodename or "unknown"
        alpha = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"         # 32 chars, no 0/O/1/I
        digest = hashlib.sha256(seed.encode("utf-8")).digest()
        out = "".join(alpha[b % 32] for b in digest[:6])
        self._hwid_cache = out
        return out

    def hw_tag(self) -> str:
        """Public device tag, e.g. 'uConsole-W4GF32' — unique per board. Used in
        the portal User-Agent platform hint so each uConsole is distinguishable."""
        return "uConsole-%s" % self._hw_id()

    def _account_name(self) -> str:
        """WDGWars account username if known — live from game-state, else cached
        in ~/.watchdogs_node_id.json so it survives before the first game-state poll."""
        path = os.path.expanduser("~/.watchdogs_node_id.json")
        user = (self.gs_me().get("username") or "").strip()
        if user:
            try:
                import json as _json
                data = {}
                if os.path.isfile(path):
                    with open(path) as f:
                        data = _json.load(f) or {}
                if data.get("account") != user:
                    data["account"] = user
                    with open(path, "w") as f:
                        _json.dump(data, f)
            except Exception:
                pass
            return user
        try:
            import json as _json
            if os.path.isfile(path):
                with open(path) as f:
                    return (_json.load(f).get("account") or "").strip()
        except Exception:
            pass
        return ""

    def node_name(self) -> str:
        """Unique per-device identity for chat / mesh / portal:
        'uConsole-<hwid>' with no WDGWars key, '<account>-uConsole-<hwid>' with one.
        WDG_NICK env overrides entirely."""
        env = os.environ.get("WDG_NICK")
        if env:
            return env
        hwid = self._hw_id()
        account = self._account_name()
        return ("%s-uConsole-%s" % (account, hwid)) if account else ("uConsole-%s" % hwid)

    def mc_node_name(self) -> str:
        """MeshCore node name — same device identity; WDG_MC_NODE env overrides."""
        return os.environ.get("WDG_MC_NODE") or self.node_name()

    def wdg_username(self) -> str:
        """WDGWars account username, if a key is configured — live from game-state
        (/api/me), else the account cached in ~/.watchdogs_node_id.json. Cached in
        memory so the HUD can call it every frame without disk I/O."""
        u = (self.gs_me().get("username") or "").strip()
        if u:
            self._wdg_user_cache = u
            return u
        c = getattr(self, "_wdg_user_cache", None)
        if c is None:
            c = self._account_name()          # one-time file read, then memoized
            self._wdg_user_cache = c
        return c or ""

    def start_wdgwars(self):
        if self._wd is not None:
            return self._wd
        if not HAVE_BACKEND:
            return None
        try:
            from watchdogs.reticulum_manager import ReticulumManager
            wd = ReticulumManager(nick=self.node_name(),
                                  configdir=self._reticulum_configdir())
            wd._on_message = self._wd_on_message
            wd._on_status = lambda text: self.wd_log.append(("sys", str(text), "sys"))
            wd._on_delivered = lambda tok: None
            wd._on_failed = lambda tok: self.wd_log.append(("sys", "message delivery failed", "sys"))
            wd.start()
            self._wd = wd
            self.wd_log.append(("sys", "connecting to #general...", "sys"))
        except Exception as exc:
            self._term(f"[WD] {exc}", "warn")
            self._wd = None
        return self._wd

    def _wd_on_message(self, nick, text):
        self.wd_log.append(("in", "%s: %s" % (nick, text), "in"))
        try:                                  # persist WDGWars chat (was UI-only -> lost on exit)
            self.ensure_session()
            if self.loot:
                with self._loot_lock:
                    self.loot.save_wdgwars_message(str(nick), str(text))
        except Exception:
            pass

    def wd_send(self, text: str) -> None:
        wd = self.start_wdgwars()
        if wd is None:
            self._term("[WD] Reticulum unavailable", "warn"); return
        try:
            wd.send(text)
            self.wd_log.append(("out", "%s: %s" % (getattr(wd, "nick", "you"), text), "out"))
            try:                              # persist our own outgoing chat too
                self.ensure_session()
                if self.loot:
                    with self._loot_lock:
                        self.loot.save_wdgwars_message(str(getattr(wd, "nick", "you")), str(text))
            except Exception:
                pass
        except Exception as exc:
            self._term(f"[WD] send: {exc}", "warn")

    def wd_nick(self) -> str:
        return getattr(self._wd, "nick", None) or self.node_name()

    def mc_regions(self) -> list:
        """[(key, label, freq_hz), ...] from MESHCORE_PRESETS."""
        try:
            from watchdogs.lora_manager import MESHCORE_PRESETS
            out = []
            for k, v in MESHCORE_PRESETS.items():
                label = v[4] if len(v) > 4 else k
                freq = v[0] if len(v) > 0 else 0
                out.append((k, label, freq))
            return out
        except Exception:
            return [("eu_uk_default", "EU/UK 869.525 MHz", 869525000)]

    def mc_region_current(self) -> str:
        return self._lora_region()

    def mc_set_region(self, key: str) -> None:
        """Set the MeshCore region. With MeshCore on air the radio is retuned in
        the background (serialized with stack switches) and the new region is
        published only after the restart succeeded."""
        if not self._claim_mesh_op():
            self._term("[MC] radio switch in progress - region unchanged", "warn")
            return
        lora = self._mgrs.get("lora")
        if not (lora and getattr(lora, "running", False)):
            try:                                 # nothing on air: just a preference
                self._commit_mc_region(key)
                self._term("[MC] region -> " + key, "ok")
            finally:
                self._mesh_switching = False
            return
        def _run():
            try:
                self._retune_meshcore(lora, key)
            finally:
                self._mesh_switching = False
        try:
            self._thread(_run, "mc-retune")
        except Exception:
            self._mesh_switching = False
            raise

    def _commit_mc_region(self, key: str) -> None:
        self._mc_region = key
        self._mesh["mc_region"] = key          # persist across sessions
        self._save_mesh_settings()

    def _retune_meshcore(self, lora, key: str) -> None:
        try:
            stopped = lora.stop()
        except Exception as exc:
            self._term(f"[MC] retune: stop failed: {exc}", "warn")
            stopped = False
        if stopped is False:                   # old thread still on the radio
            self._report_radio_busy("[MC]")
            return
        try:
            lora.start_meshcore(key)
            self._wire_meshcore()
        except Exception as exc:
            self._term(f"[MC] retune: {exc}", "warn")
        if getattr(lora, "running", False):
            self._commit_mc_region(key)
            self._term("[MC] retuned -> " + key, "ok")
        else:
            self._term("[MC] retune to %s failed - MeshCore stopped (region kept: %s)"
                       % (key, self._lora_region()), "warn")
            self._publish_live_stack()

    def mc_contacts(self) -> list:
        try:
            p = Path(self._app_dir) / "loot" / "loot_db.json"
            with open(p, encoding="utf-8") as f:
                return list(json.load(f).get("mc_contacts", {}).values())
        except Exception:
            return []

    # ---- Flipper / SubGhz / Watch ----
    def _act_flipper(self):
        fl = self._mgr("flipper")
        if fl is None:
            self._term("[FLIP] manager unavailable", "warn"); return
        def run():
            try:
                if fl.connect():
                    self._term(f"[FLIP] connected {fl.port}", "ok")
                else:
                    self._term("[FLIP] no Flipper Zero found", "warn")
            except Exception as exc:
                self._term(f"[FLIP] {exc}", "warn")
        self._thread(run, "flipper")

    def _act_subghz(self):
        sg = self._mgr("subghz")
        if sg is None:
            self._term("[SUBGHZ] manager unavailable", "warn"); return
        def run():
            try:
                if sg.connect():
                    self._term("[SUBGHZ] Monster RF connected - scanning", "ok")
                    sg.cmd_scan()
                else:
                    self._term("[SUBGHZ] no CC1101 board found", "warn")
            except Exception as exc:
                self._term(f"[SUBGHZ] {exc}", "warn")
        self._thread(run, "subghz")

    def _act_watch(self):
        w = self._mgr("watch")
        if w is None:
            self._term("[WATCH] bleak/BLE required", "warn"); return
        def run():
            try:
                existing = w.check_existing()
                if existing:
                    w.connect(existing); self._term(f"[WATCH] connecting {existing}", "ok")
                else:
                    w.scan(); self._term("[WATCH] scanning for PipBoy...", "ok")
            except Exception as exc:
                self._term(f"[WATCH] {exc}", "warn")
        self._thread(run, "watch")

    # ---- WPA-sec ----
    def _wpasec_key_msg(self) -> str:
        """Friendlier 'no key' line: if WDG_WPASEC_KEY (or legacy JANOS_WPASEC_KEY)
        sits in secrets.conf COMMENTED OUT, say so instead of 'not configured' —
        a '#'-prefixed key reads as absent and silently disables upload."""
        try:
            from portal_sync import commented_key_value
        except Exception:
            try:
                from wdgong_ui.portal_sync import commented_key_value
            except Exception:
                commented_key_value = lambda *_a, **_k: ""
        sp = Path(self._app_dir) / "secrets.conf"
        for k in ("WDG_WPASEC_KEY", "JANOS_WPASEC_KEY"):
            if commented_key_value(k, sp):
                return ("[WPA-SEC] %s is in secrets.conf but COMMENTED OUT - "
                        "remove the leading '#' to enable upload." % k)
        return "[WPA-SEC] no key - add WDG_WPASEC_KEY to secrets.conf."

    def _wpasec_blocked_macs(self, loot_dir: Path) -> set[str]:
        # WhitelistManager.load() logs read errors and can return a partial list.
        # A missing file is the normal "no ignore list yet" state (same as the
        # manager) -> no exclusions; a file that exists but cannot be read or
        # parsed still raises, so the upload stops instead of ignoring the list.
        path = loot_dir / "whitelist.json"
        rows = []
        if path.exists():
            with path.open(encoding="utf-8") as fh:
                rows = json.load(fh)
        if not isinstance(rows, list):
            raise ValueError("expected a list")
        macs = [row["mac"] for row in rows]
        if self._wl is not None:
            # An in-memory addition still applies if the manager failed to save it.
            macs.extend(entry.mac for entry in self._wl.entries)
        blocked = set()
        for mac in macs:
            digits = mac.strip().replace(":", "").replace("-", "").upper()
            if not re.fullmatch(r"[0-9A-F]{12}", digits):
                raise ValueError("invalid MAC address")
            blocked.add(":".join(digits[i:i + 2] for i in range(0, 12, 2)))
        return blocked

    def _act_wpasec_up(self):
        if not HAVE_BACKEND:
            return
        from watchdogs import upload_manager as UM
        def run():
            try:
                loot_dir = Path(self._app_dir) / "loot"
                try:
                    blocked_macs = self._wpasec_blocked_macs(loot_dir)
                except (OSError, ValueError, KeyError, TypeError, AttributeError) as exc:
                    self._term(f"[WPA-SEC] upload stopped: cannot read ignore list: {exc}", "warn")
                    return
                up, total, msg = UM.upload_wpasec_all(loot_dir, blocked_macs=blocked_macs)
                if "not configured" in msg.lower():
                    self._term(self._wpasec_key_msg(), "warn")
                else:
                    self._term(f"[WPA-SEC] uploaded {up}/{total} - {msg}", "ok")
            except Exception as exc:
                self._term(f"[WPA-SEC] upload: {exc}", "warn")
        self._thread(run, "wpasec-up")

    def _act_wpasec_dl(self):
        if not HAVE_BACKEND:
            return
        from watchdogs import upload_manager as UM
        def run():
            try:
                loot_dir = Path(self._app_dir) / "loot"
                ok, count, msg = UM.download_wpasec_potfile(loot_dir)
                if not ok and "not configured" in msg.lower():
                    self._term(self._wpasec_key_msg(), "warn")
                else:
                    self._term(f"[WPA-SEC] {count} cracked - {msg}", "ok" if ok else "warn")
                if self.loot:
                    try: self.loot.invalidate_cracked_cache()
                    except Exception: pass
                self._db_totals, self._db_xp, _ = self._read_db(self._app_dir)
            except Exception as exc:
                self._term(f"[WPA-SEC] download: {exc}", "warn")
        self._thread(run, "wpasec-dl")

    def _wigle_key_msg(self) -> str:
        try:
            from portal_sync import commented_key_value
        except Exception:
            try:
                from wdgong_ui.portal_sync import commented_key_value
            except Exception:
                commented_key_value = lambda *_a, **_k: ""
        sp = Path(self._app_dir) / "secrets.conf"
        for k in ("WDG_WIGLE_NAME", "WDG_WIGLE_TOKEN"):
            if commented_key_value(k, sp):
                return ("[WiGLE] %s is in secrets.conf but COMMENTED OUT - "
                        "remove the leading '#' to enable upload." % k)
        return "[WiGLE] no key - add WDG_WIGLE_NAME + WDG_WIGLE_TOKEN to secrets.conf."

    def _act_wigle_up(self, quiet_unconfigured: bool = False):
        if not HAVE_BACKEND:
            return
        from watchdogs import upload_manager as UM
        def run():
            # One WiGLE upload at a time across BOTH entry points (menu + cluster
            # auto-upload), else the same session can be sent twice and burn quota.
            if not self._wigle_lock.acquire(blocking=False):
                if not quiet_unconfigured:
                    self._term("[WiGLE] an upload is already running", "warn")
                return
            try:
                if not UM.wigle_configured():
                    if not quiet_unconfigured:
                        self._term(self._wigle_key_msg(), "warn")
                    return
                loot_dir = Path(self._app_dir) / "loot"
                self._term("[WiGLE] uploading wardriving sessions...", "tx")
                try:
                    active = self.loot._session.name if self.loot and self.loot._session else ""
                except Exception:                    # noqa: BLE001
                    active = ""
                up, total, msg = UM.upload_wigle_all(loot_dir, self._app_dir, keep_pending=active)
                if "not configured" in msg.lower():
                    self._term(self._wigle_key_msg(), "warn")
                else:
                    self._term("[WiGLE] uploaded %d/%d - %s" % (up, total, msg),
                               "ok" if up else "warn")
            except Exception as exc:
                self._term("[WiGLE] upload: %s" % exc, "warn")
            finally:
                self._wigle_lock.release()
        self._thread(run, "wigle-up")

    # ---- flash / update ----
    def flash_boards(self) -> list:
        if not HAVE_BACKEND:
            return [("wroom", "ESP32-C5 WROOM-1 (Dev Kit)"), ("xiao", "XIAO ESP32-C5 (USB-JTAG)")]
        try:
            return [(k, v.get("label", k)) for k, v in CFG.FLASH_BOARDS.items()]
        except Exception:
            return []

    def flash_default_board(self) -> str:
        return "xiao" if "ACM" in (self.state.device if self.state else "") else "wroom"

    def flash_busy(self) -> bool:
        return getattr(self, "_flash_running", False)

    def flash_start(self, board: str) -> None:
        if getattr(self, "_flash_running", False):
            return
        self._term(f"[FLASH] starting ({board}) - do not unplug", "warn")
        self._thread(lambda: self.flash_esp32(board), "flash")

    def _act_flash(self):
        self.flash_start(self.flash_default_board())

    # ------------------------------------------------------------------
    # ESP32 flasher: preflight -> verified download -> supervised esptool run ->
    # safe retry -> guaranteed cleanup -> 3-step proof (written+hash, back on USB,
    # firmware answers the release version). Nothing is touched until the
    # preflight and the download both check out.
    # ------------------------------------------------------------------
    FLASH_TOTAL_S = 300.0       # hard cap for one esptool run
    FLASH_STALL_S = 60.0        # no esptool output for this long -> abort the run
    ESPTOOL_MIN = (5, 0, 0)

    class _FlashError(Exception):
        """A flash step failed with a message meant for the player."""

    def flash_progress(self) -> tuple:
        """(stage, pct) for the flash screen. stage: preflight|download|connect|
        write|boot|done|failed ('' when idle); pct 0-100, or -1 = indeterminate."""
        return (getattr(self, "_flash_stage", ""), getattr(self, "_flash_pct", -1))

    def flash_result(self) -> tuple:
        """(level, message) of the last flash; level ok|warn|err, ('', '') if none."""
        return getattr(self, "_flash_last", ("", ""))

    def _flash_set(self, stage: str, pct=None) -> None:
        self._flash_stage = stage
        if pct is not None:
            self._flash_pct = pct

    def flash_esp32(self, board: str) -> None:
        self._flash_running = True
        self._flash_last = ("", "")
        self._flash_set("preflight", -1)
        try:
            self._flash_do(board)
        except self._FlashError as exc:
            self._flash_set("failed")
            self._flash_last = ("err", str(exc))
            self._term(f"[FLASH] FAILED: {exc}", "warn")
        except Exception as exc:
            self._flash_set("failed")
            self._flash_last = ("err", f"unexpected error: {exc}")
            self._term(f"[FLASH] unexpected error: {exc}", "warn")
        finally:
            self._flash_running = False
            if getattr(self, "_flash_stage", "") not in ("done", "failed"):
                self._flash_set("failed")

    def _flash_do(self, board: str) -> None:
        profile = CFG.FLASH_BOARDS[board]
        # ---- A. preflight: esptool new enough, firmware downloaded + verified ----
        self._flash_set("preflight", -1)
        ver = self._esptool_version()
        if ver is None:
            raise self._FlashError(
                "esptool not found for the game's Python - run setup.sh "
                "(or: %s -m pip install 'esptool>=5')" % sys.executable)
        if ver < self.ESPTOOL_MIN:
            raise self._FlashError(
                "esptool %s is too old (need >= %s) - run: %s -m pip install -U 'esptool>=5'"
                % (".".join(map(str, ver)), ".".join(map(str, self.ESPTOOL_MIN)), sys.executable))
        self._term("[FLASH] esptool %s OK" % ".".join(map(str, ver)), "tx")
        # ---- B. verified download into a fresh dir (per-tag last-known-good cache) ----
        self._flash_set("download", -1)
        tag, fw_dir = self._flash_fetch(board, profile)
        want = tag.lstrip("v")
        segs = sorted(profile["offsets"].items(), key=lambda kv: int(kv[1], 16))
        files = [(off, fw_dir / fn) for fn, off in segs]
        sizes = [p.stat().st_size for _, p in files]
        aio = self._mgr("aio")
        use_rail = board == "xiao" and aio is not None and aio.is_installed()
        port = self._flash_port(aio if use_rail else None)
        if not port:
            raise self._FlashError(
                "no ESP32 serial port found - plug the board in, then press ENTER")
        # Bind the whole run to THIS board's USB identity so a USB power-cycle or a
        # second ESP32-C5 (XIAO + Monster RF, etc.) can never divert the write to a
        # different board. '' identity = chip exposes none; we then simply never
        # auto-switch away from the chosen port.
        flash_ident = self._port_identity(port)
        if flash_ident[0] or flash_ident[1]:
            self._term("[FLASH] bound to %s (id %s)"
                       % (port, flash_ident[0] or flash_ident[1]), "tx")
        released = written = False
        try:
            # ---- from here the flasher OWNS the port (connect() is blocked) ----
            if self.serial and self.serial.is_open:
                self.serial.close()
            self.connected = False
            if self.state:
                self.state.connected = False
            released = True
            self._term(f"[FLASH] released {port}", "tx")
            attempts = [("normal", profile["baud"]), ("slow retry", 115200)]
            res = None
            for i, (label, baud) in enumerate(attempts):
                if use_rail:
                    self._term("[FLASH] USB power cycle...", "tx")
                    aio.toggle("usb", False); time.sleep(2); aio.toggle("usb", True)
                    port = self._wait_identity(flash_ident, port, 6.0)
                elif flash_ident[0] or flash_ident[1]:
                    # Re-resolve the SAME board only (never jump to another ESP32).
                    port = self._find_by_identity(flash_ident) or ""
                # else: no stable id -> keep the originally selected port as-is.
                if not port or not Path(port).exists():
                    raise self._FlashError(
                        "the selected ESP32 disappeared before writing - nothing was "
                        "flashed. Reconnect the SAME board and press ENTER.")
                after = "no-reset" if use_rail else "hard-reset"
                cmd = [sys.executable, "-m", "esptool", "-p", port, "-b", str(baud),
                       "--before", profile["before"], "--after", after, "--chip", "esp32c5",
                       "--no-stub", "write-flash", "--flash-mode", "dio", "--flash-freq", "80m",
                       "--flash-size", "detect"]
                for off, path in files:
                    cmd += [off, str(path)]
                self._term(f"[FLASH] flashing v{want} ({label}, {baud} baud)...", "warn")
                self._flash_set("connect", -1)
                res = self._flash_run(cmd, sizes)
                if res["rc"] == 0 and not res["timed_out"] and not res["stalled"]:
                    written = True
                    break
                why = ("hard timeout" if res["timed_out"] else
                       "no progress" if res["stalled"] else f"esptool error {res['rc']}")
                if res["wrote"]:
                    # D. died DURING the write -> never retry blindly
                    raise self._FlashError(
                        f"write interrupted at {max(res['pct'], 0)}% ({why}). The ESP32 ROM "
                        "bootloader can't be damaged - press ENTER to flash again.")
                if i + 1 < len(attempts):
                    self._term(f"[FLASH] connect failed ({why}) - nothing written, "
                               "retrying once more slowly...", "warn")
                else:
                    raise self._FlashError(
                        f"could not connect to the ESP32 ({why}); nothing was written. "
                        "Check the cable/board, then press ENTER to try again.")
            n = len(files)
            if res["verified"] >= n:
                self._term(f"[FLASH] write OK, hash verified {res['verified']}/{n}", "ok")
            else:
                self._term(f"[FLASH] write OK (esptool reported {res['verified']}/{n} "
                           "hash checks)", "warn")
        finally:
            # ---- E. ALWAYS: power back, hand the port back, reconnect ----
            if released:
                self._flash_set("boot", -1)
                try:
                    if use_rail:   # after=no-reset on the rail path -> cycle it to boot
                        aio.toggle("usb", False); time.sleep(2); aio.toggle("usb", True)
                        time.sleep(4)
                except Exception:
                    pass
                self._fw_version = ""; self._fw_update = False; self._fw_check_t = 0.0
                time.sleep(3)
                self._flash_connect_ok = True
                try:
                    self.connect()
                finally:
                    self._flash_connect_ok = False
        # ---- F. proof: back on USB + firmware answers with the release version ----
        if written:
            self._flash_confirm(want)

    def _flash_confirm(self, want: str) -> None:
        self._flash_set("boot", -1)
        if not (self.serial and self.serial.is_open):
            self._flash_set("done", 100)
            self._flash_last = ("warn", f"v{want} written + verified, but the ESP32 did not "
                                        "come back on USB - replug it")
            self._term("[FLASH] " + self._flash_last[1], "warn")
            return
        deadline = time.time() + 20.0
        nxt = 0.0
        while time.time() < deadline and not self._fw_version:
            if time.time() >= nxt:
                try:
                    self.serial.send_command("version")
                except Exception:
                    pass
                nxt = time.time() + 4.0
            time.sleep(0.25)
        got = self._fw_version
        self._flash_set("done", 100)
        if got == want:
            self._flash_last = ("ok", f"firmware v{want} flashed & confirmed running")
            self._term("[FLASH] complete! " + self._flash_last[1], "ok")
        elif got:
            self._flash_last = ("warn", f"written, but the ESP32 reports v{got} "
                                        f"(expected v{want})")
            self._term("[FLASH] " + self._flash_last[1], "warn")
        else:
            self._flash_last = ("warn", f"v{want} written + verified, but the firmware did "
                                        "not answer 'version' within 20 s")
            self._term("[FLASH] " + self._flash_last[1], "warn")

    def _esptool_version(self):
        """esptool version for the game's own Python as a tuple, or None."""
        import subprocess
        try:
            r = subprocess.run([sys.executable, "-m", "esptool", "version"],
                               capture_output=True, text=True, timeout=45)
        except Exception:
            return None
        out = (r.stdout or "") + "\n" + (r.stderr or "")
        for ln in reversed(out.strip().splitlines()):
            m = re.fullmatch(r"\s*v?(\d+)\.(\d+)(?:\.(\d+))?\s*", ln)
            if m:
                return tuple(int(x or 0) for x in m.groups())
        m = re.search(r"esptool(?:\.py)?\s+v?(\d+)\.(\d+)(?:\.(\d+))?", out)
        if m:
            return tuple(int(x or 0) for x in m.groups())
        return None

    def _flash_port(self, aio=None) -> str:
        port = (self.state.device if self.state else "") or os.environ.get("WDGO_PORT") or ""
        if port and Path(port).exists():
            return port
        port = detect_esp32_port() or ""
        if port or aio is None:
            return port
        try:
            aio.toggle("usb", True)      # XIAO is powered through the AIO USB rail
        except Exception:
            pass
        return self._wait_port("", 8.0)

    def _wait_port(self, port: str, secs: float) -> str:
        end = time.time() + secs
        while time.time() < end:
            if port and Path(port).exists():
                return port
            p = detect_esp32_port()
            if p:
                return p
            time.sleep(0.2)
        return port

    @staticmethod
    def _port_identity(dev: str):
        """(serial_number, usb_location) for a device path. Either may be '' on
        chips that don't expose it. Used to re-bind to the SAME physical board
        across USB power-cycles instead of grabbing whatever ESP32 is visible."""
        try:
            import serial.tools.list_ports as _lp
            for p in _lp.comports():
                if p.device == dev:
                    return (getattr(p, "serial_number", None) or "",
                            getattr(p, "location", None) or "")
        except Exception:
            pass
        return ("", "")

    @staticmethod
    def _find_by_identity(ident) -> str:
        """Device path whose USB identity matches `ident` (serial first, then USB
        topology location). '' when the selected board is not present."""
        sn, loc = ident
        if not (sn or loc):
            return ""
        try:
            import serial.tools.list_ports as _lp
            ports = list(_lp.comports())
        except Exception:
            return ""
        if sn:
            for p in ports:
                if (getattr(p, "serial_number", None) or "") == sn:
                    return p.device
        if loc:
            for p in ports:
                if (getattr(p, "location", None) or "") == loc:
                    return p.device
        return ""

    def _wait_identity(self, ident, fallback: str, secs: float) -> str:
        """Wait up to `secs` for the SELECTED board (by USB identity) to reappear.
        Returns its current path, or '' if it never comes back. When the board has
        no stable identity, fall back to the plain port wait."""
        if not (ident[0] or ident[1]):
            return self._wait_port(fallback, secs)
        end = time.time() + secs
        while time.time() < end:
            dev = self._find_by_identity(ident)
            if dev:
                return dev
            time.sleep(0.2)
        return ""

    def _flash_fetch(self, board: str, profile: dict):
        """Latest release -> download the board zip -> VERIFY (GitHub sha256 digest,
        size, exact file set) in a FRESH dir -> promote to a per-tag cache. Offline:
        reuse the newest verified cache for this board."""
        import json as _json, hashlib, shutil
        from urllib.request import Request, urlopen
        root = Path(self._app_dir) / "firmware_cache"
        root.mkdir(exist_ok=True)
        needed = list(profile["offsets"].keys())
        try:
            req = Request(CFG.FIRMWARE_RELEASE_URL); req.add_header("User-Agent", "WatchDogsGo")
            with urlopen(req, timeout=15) as r:
                rel = _json.loads(r.read())
        except Exception as exc:
            cached = self._flash_cached(root, board, needed)
            if cached:
                self._term(f"[FLASH] offline ({exc}) - using verified cache {cached[0]}", "warn")
                return cached
            raise self._FlashError(
                f"can't reach GitHub releases ({exc}) and no verified firmware is cached")
        tag = rel["tag_name"]
        self._term(f"[FLASH] release {tag}", "tx")
        good = root / f"{tag}-{board}"
        if (good / ".verified").exists() and all((good / fn).exists() for fn in needed):
            self._term(f"[FLASH] using verified cache {tag}", "tx")
            return tag, good
        suffix = "-xiao" if board == "xiao" else ""
        exact = f"projectzerobylocosp{suffix}-{tag.lstrip('v')}.zip"
        asset = next((a for a in rel.get("assets", [])
                      if a.get("name", "").lower() == exact), None)
        if asset is None:   # looser match, but never let 'wroom' pick the -xiao zip
            for a in rel.get("assets", []):
                n = a.get("name", "").lower()
                if (n.startswith(f"projectzerobylocosp{suffix}") and n.endswith(".zip")
                        and "fap" not in n and "with" not in n
                        and (suffix or "-xiao" not in n)):
                    asset = a
                    break
        if asset is None:
            raise self._FlashError(f"release {tag} has no firmware zip for board '{board}'")
        size = asset.get("size") or 0
        digest = asset.get("digest") or ""
        want_sha = digest.split(":", 1)[1].lower() if digest.startswith("sha256:") else ""
        attempt = root / f".attempt-{os.getpid()}-{int(time.time())}"
        shutil.rmtree(attempt, ignore_errors=True)
        attempt.mkdir()
        try:
            zp = attempt / "fw.zip"
            self._term(f"[FLASH] downloading {asset['name']}...", "tx")
            h = hashlib.sha256(); got = 0
            req = Request(asset["browser_download_url"]); req.add_header("User-Agent", "WatchDogsGo")
            with urlopen(req, timeout=120) as r, open(zp, "wb") as f:
                while True:
                    chunk = r.read(65536)
                    if not chunk:
                        break
                    f.write(chunk); h.update(chunk); got += len(chunk)
                    if size:
                        self._flash_set("download", min(100, int(got * 100 / size)))
            self._flash_verify_extract(zp, h.hexdigest(), got, want_sha, size, needed,
                                       attempt / "files")
            shutil.rmtree(good, ignore_errors=True)
            (attempt / "files").rename(good)
            (good / ".verified").write_text(want_sha or "size+files")
            self._term("[FLASH] download verified (%s)"
                       % ("sha256 + size" if want_sha else "size + files"), "ok")
            return tag, good
        finally:
            shutil.rmtree(attempt, ignore_errors=True)

    def _flash_verify_extract(self, zp, got_sha, got_size, want_sha, want_size, needed, dest):
        """Reject a bad download; extract ONLY the files we flash, flat, by basename."""
        import zipfile, shutil
        if want_size and got_size != want_size:
            raise self._FlashError(
                f"download size mismatch ({got_size} != {want_size} bytes) - try again")
        if want_sha and got_sha.lower() != want_sha.lower():
            raise self._FlashError("download checksum (sha256) mismatch - corrupted, try again")
        Path(dest).mkdir(parents=True, exist_ok=True)
        try:
            with zipfile.ZipFile(zp) as zf:
                members = {Path(i.filename).name: i for i in zf.infolist() if not i.is_dir()}
                missing = [fn for fn in needed if fn not in members]
                if missing:
                    raise self._FlashError("firmware zip is missing: " + ", ".join(missing))
                for fn in needed:
                    with zf.open(members[fn]) as src, open(Path(dest) / fn, "wb") as out:
                        shutil.copyfileobj(src, out)
                    if (Path(dest) / fn).stat().st_size == 0:
                        raise self._FlashError(f"firmware file {fn} is empty")
        except zipfile.BadZipFile:
            raise self._FlashError("downloaded firmware is not a valid zip - try again")

    def _flash_cached(self, root, board: str, needed):
        best = None
        for d in Path(root).glob(f"*-{board}"):
            if d.is_dir() and (d / ".verified").exists() and all((d / fn).exists() for fn in needed):
                if best is None or d.stat().st_mtime > best.stat().st_mtime:
                    best = d
        if best is None:
            return None
        return best.name[: -len(f"-{board}")], best

    def _flash_run(self, cmd, sizes=None) -> dict:
        """Run esptool under a watchdog (TOTAL cap + STALL cap on silence), killing
        the whole process group on expiry. Parses 'Writing at ... NN.N%' progress
        and 'Hash of data verified.'. Never blocks forever."""
        import subprocess, threading, queue
        res = {"rc": None, "wrote": False, "pct": -1, "verified": 0,
               "timed_out": False, "stalled": False}
        env = dict(os.environ, NO_COLOR="1", TERM="dumb", PYTHONUNBUFFERED="1")
        try:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    env=env, start_new_session=True)
        except Exception as exc:
            raise self._FlashError(f"can't start esptool: {exc}")
        q = queue.Queue()

        def _reader():
            fd = proc.stdout.fileno()
            while True:
                try:
                    b = os.read(fd, 512)
                except OSError:
                    break
                if not b:
                    break
                q.put(b)
            q.put(None)
        threading.Thread(target=_reader, daemon=True).start()
        sizes = list(sizes or [])
        total = float(sum(sizes)) or 0.0
        pct_re = re.compile(r"(\d{1,3}(?:\.\d+)?)\s*%")
        start = last = time.time()
        buf = ""; eof = False; seg_pct = 0.0; logged = -10
        while True:
            try:
                chunk = q.get(timeout=0.5)
            except queue.Empty:
                chunk = b""
            if chunk is None:
                eof = True
            elif chunk:
                if chunk.strip():
                    last = time.time()          # any esptool output = alive
                buf += chunk.decode("utf-8", errors="replace")
                parts = re.split(r"[\r\n]", buf)
                buf = parts.pop()[-2000:]
                for seg in parts:
                    seg = seg.strip()
                    if not seg:
                        continue
                    if "Writing at" in seg:
                        if not res["wrote"]:
                            res["wrote"] = True
                        m = pct_re.search(seg)
                        if m:
                            seg_pct = float(m.group(1))
                            k = min(res["verified"], len(sizes) - 1) if sizes else 0
                            if total:
                                ov = (sum(sizes[:k]) + seg_pct / 100.0 * sizes[k]) / total * 100
                            else:
                                ov = seg_pct
                            res["pct"] = int(ov)
                            self._flash_set("write", res["pct"])
                            if res["pct"] >= logged + 10 or res["pct"] >= 100:
                                logged = res["pct"] - res["pct"] % 10
                                self._term("[FLASH] writing %d%%" % res["pct"], "raw")
                        continue
                    if "Hash of data verified" in seg:
                        res["verified"] += 1
                        seg_pct = 0.0
                    elif "Connecting" in seg and not res["wrote"]:
                        self._flash_set("connect", -1)
                    self._term("[FLASH] " + seg[:88], "raw")
            if eof and proc.poll() is not None:
                break
            now = time.time()
            if now - start > self.FLASH_TOTAL_S:
                res["timed_out"] = True
                break
            if now - last > self.FLASH_STALL_S:
                res["stalled"] = True
                break
        if res["timed_out"] or res["stalled"]:
            self._term("[FLASH] %s - stopping esptool"
                       % (f"hard timeout {int(self.FLASH_TOTAL_S)} s" if res["timed_out"]
                          else f"no output for {int(self.FLASH_STALL_S)} s"), "warn")
            self._flash_kill(proc)
        try:
            res["rc"] = proc.wait(timeout=5)
        except Exception:
            self._flash_kill(proc)
            res["rc"] = proc.poll()
        if res["rc"] is None:
            res["rc"] = -9
        return res

    def _flash_kill(self, proc) -> None:
        """SIGTERM then SIGKILL the whole esptool process group (bounded waits)."""
        import signal
        for sig, wait in ((signal.SIGTERM, 5), (signal.SIGKILL, 5)):
            if proc.poll() is not None:
                return
            try:
                os.killpg(proc.pid, sig)
            except Exception:
                try:
                    proc.send_signal(sig)
                except Exception:
                    pass
            try:
                proc.wait(timeout=wait)
            except Exception:
                pass

    def _act_update(self):
        import subprocess
        if getattr(self, "_flash_running", False):
            self._term("[UPD] flash in progress - try again after it finishes", "warn")
            return
        self._save_xp()      # don't let a code pull/restart drop the latest XP
        def run():
            try:
                r = subprocess.run(["git", "-C", self._app_dir, "pull", "--ff-only"],
                                   capture_output=True, text=True, timeout=60)
                out = (r.stdout + r.stderr).strip().splitlines()
                self._term("[UPD] " + (out[-1] if out else "done"), "ok" if r.returncode == 0 else "warn")
            except Exception as exc:
                self._term(f"[UPD] {exc}", "warn")
        self._thread(run, "update")

    def _act_mute(self):
        self._muted = not getattr(self, "_muted", False)
        self._term("[SYS] sounds " + ("muted" if self._muted else "on"), "ok")

    def _act_usb(self):
        aio = self._mgr("aio")
        try:
            if aio and aio.is_installed():
                cur = (aio.get_status() or {}).get("usb")
                if not isinstance(cur, bool):     # a toggle needs a real reading
                    self._term("[USB] rail state unknown (GPIO read failed) - not toggling", "warn")
                    return
                new = not cur
                aio.toggle("usb", new)
                self._term("[USB] " + ("on" if new else "off"), "ok")
            else:
                self._term("[USB] AIO v2 not available", "warn")
        except Exception as exc:
            self._term(f"[USB] {exc}", "warn")

    def _act_mc_region(self):
        """Cycle the MeshCore region preset (OG has a picker; we cycle 1:1 outcome)."""
        try:
            from watchdogs.lora_manager import MESHCORE_PRESETS
            keys = list(MESHCORE_PRESETS.keys())
        except Exception:
            self._term("[MC] region presets unavailable", "warn"); return
        cur = getattr(self, "_mc_region", keys[0])
        nxt = keys[(keys.index(cur) + 1) % len(keys)] if cur in keys else keys[0]
        self.mc_set_region(nxt)       # same guarded retune + publish-after-success path

    def _act_prox(self):
        p = self._mgr("prox")
        if p is None:
            self._term("[PROX] manager unavailable", "warn"); return
        try:
            p.toggle()
            self._term("[PROX] " + ("ON" if getattr(p, "enabled", False) else "OFF"), "ok")
        except Exception as exc:
            self._term(f"[PROX] {exc}", "warn")

    def _act_prox_view(self):
        self._mgr("prox")   # ensure built; the UI opens the radar screen

    # ---- proximity accessors for the radar screen ----
    def prox_ensure(self):
        return self._mgr("prox")

    def prox_autostart(self):
        """Run WDGWars proximity as a background service from launch (default ON;
        respects a remembered OFF via the menu). Spawns the peer subprocess (root)."""
        def run():
            try:
                p = self._mgr("prox")
                if p is None:
                    return
                if p.wanted() and not getattr(p, "enabled", False):
                    p.start()
                    self._term("[PROX] proximity service running in background", "ok")
            except Exception as exc:
                self._term("[PROX] autostart: %s" % exc, "warn")
        self._thread(run, "proxauto")

    def prox_pause(self):
        """Yield hci0 to a host-BT operation (Watch/BLE-HID/RACE). The proximity peer
        is killed but stays 'enabled' so prox_resume() brings it back."""
        try:
            p = self._mgrs.get("prox")
            if p is not None and getattr(p, "enabled", False) and not getattr(p, "paused", False):
                p.pause()
                self._term("[PROX] paused (BT in use)", "warn")
        except Exception:
            pass

    def prox_resume(self):
        """Give hci0 back to proximity once the host-BT operation is done."""
        try:
            p = self._mgrs.get("prox")
            if p is not None and getattr(p, "enabled", False) and getattr(p, "paused", False):
                p.resume()
                self._term("[PROX] resumed", "ok")
        except Exception:
            pass

    def prox_on(self) -> bool:
        if getattr(self, "_demo_prox", None):
            return True
        p = self._mgrs.get("prox"); return bool(p and getattr(p, "enabled", False))

    def prox_rows(self) -> list:
        if getattr(self, "_demo_prox", None):
            return self._demo_prox
        p = self._mgrs.get("prox")
        try:
            return list(p.rows()) if p else []
        except Exception:
            return []

    def prox_info(self) -> tuple:
        """(status_text, state, my_ident)."""
        if getattr(self, "_demo_prox", None):
            return ("ON", "ok", "A1B2C3")
        p = self._mgrs.get("prox")
        if p is None:
            return ("OFF", "off", "------")
        try:
            if getattr(p, "paused", False): st, sc = "HOLD (BT busy)", "warn"
            elif not getattr(p, "enabled", False): st, sc = "OFF", "off"
            elif not p.fresh(): st, sc = "starting", "warn"
            else: st, sc = "ON", "ok"
            ident = p.my_ident() or "------"
        except Exception:
            st, sc, ident = "?", "off", "------"
        return (st, sc, ident)

    def prox_meeting(self):
        p = self._mgrs.get("prox")
        try:
            return p.meeting() if p else None
        except Exception:
            return None

    def prox_strangers(self) -> list:
        """Unresolved WDG peers labelled <Model>-XXXX (radar list only; the
        pager/HUD keep treating them as 'unknown')."""
        if getattr(self, "_demo_prox", None):
            return []
        p = self._mgrs.get("prox")
        try:
            return list(p.strangers()) if p and hasattr(p, "strangers") else []
        except Exception:
            return []

    def prox_unknown(self) -> int:
        p = self._mgrs.get("prox")
        try:
            return int(p.unknown()) if p else 0
        except Exception:
            return 0

    def prox_toggle(self):
        self._act_prox()

    # ---- whitelist (MAC ignore list) ----
    def _wl_mgr(self):
        if self._wl is None and HAVE_BACKEND:
            try:
                from watchdogs.whitelist_manager import WhitelistManager
                self._wl = WhitelistManager(Path(self._app_dir) / "loot" / "whitelist.json")
                self._wl.load()
            except Exception as exc:
                self._term(f"[WL] {exc}", "warn")
        return self._wl

    def wl_entries(self) -> list:
        m = self._wl_mgr()
        if not m:
            return []
        try:
            return [(getattr(e, "type", ""), getattr(e, "mac", ""), getattr(e, "name", "")) for e in m.entries]
        except Exception:
            return []

    def wl_add(self, etype: str, mac: str, name: str) -> bool:
        m = self._wl_mgr()
        if not m:
            return False
        try:
            ok = m.add(etype, mac, name)
            self._term("[WL] %s %s" % ("added" if ok else "exists", mac[-8:]), "ok" if ok else "warn")
            return ok
        except Exception as exc:
            self._term(f"[WL] {exc}", "warn"); return False

    def wl_remove(self, idx: int) -> None:
        m = self._wl_mgr()
        if not m:
            return
        try:
            m.remove(idx); self._term("[WL] entry removed", "warn")
        except Exception as exc:
            self._term(f"[WL] {exc}", "warn")

    def _act_whitelist(self):
        if not HAVE_BACKEND:
            return
        try:
            from watchdogs.whitelist_manager import WhitelistManager
            wl = WhitelistManager(Path(self._app_dir) / "loot" / "whitelist.json")
            wl.load()
            self._term("[WL] %d whitelisted MACs:" % wl.count, "ok")
            for e in wl.entries[:6]:
                self._term("[WL] %s %s %s" % (getattr(e, "entry_type", ""),
                           getattr(e, "mac", ""), getattr(e, "name", "")), "raw")
        except Exception as exc:
            self._term(f"[WL] {exc}", "warn")

    def _gui_prefix(self):
        """The UI runs under sudo (root) for serial/GPIO. Chromium won't run as
        root and OrganicMaps is a *user* flatpak, so drop back to the login user
        with their display env. Returns [] when we're not root (dev/Mac)."""
        try:
            if os.geteuid() != 0:
                return []
        except AttributeError:
            return []
        user = os.environ.get("SUDO_USER")
        if not user:
            return []
        uid = os.environ.get("SUDO_UID") or "1000"
        envs = [
            "DISPLAY=" + os.environ.get("DISPLAY", ":0"),
            "WAYLAND_DISPLAY=" + os.environ.get("WAYLAND_DISPLAY", "wayland-0"),
            "XDG_RUNTIME_DIR=/run/user/%s" % uid,
            "XAUTHORITY=" + os.environ.get("XAUTHORITY", "/home/%s/.Xauthority" % user),
        ]
        return ["sudo", "-u", user, "env"] + envs

    def _srv_launch(self, argv, label):
        import subprocess
        try:
            subprocess.Popen(self._gui_prefix() + argv,
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            self._term("[CRISIS] " + label, "ok")
        except FileNotFoundError:
            self._term("[CRISIS] %s not installed" % argv[0], "warn")
        except Exception as exc:
            self._term("[CRISIS] %s" % exc, "warn")

    def _act_srv(self, which):
        browser = getattr(CFG, "SURVIVAL_BROWSER", "chromium")
        if which == "wiki":
            # Kiwix offline Wikipedia -> kiosk browser (mirrors kiwix-wiedza.desktop)
            self._srv_launch([browser, "--app=" + CFG.SURVIVAL_WIKI_URL],
                             "Wikipedia (Kiwix) offline")
        elif which == "ctos":
            # WDGWorldMap = our Offline Navigation System (mirrors ctos-map.desktop)
            self._srv_launch([browser, "--app=" + CFG.SURVIVAL_CTOS_MAP_URL,
                              "--start-fullscreen", "--autoplay-policy=no-user-gesture-required",
                              "--noerrdialogs"],
                             "WDGWorldMap - Offline Navigation System")
        elif which == "nav":
            self._srv_launch(list(CFG.SURVIVAL_NAV_CMD), "Organic Maps (offline nav)")
        else:
            self._thread(self._srv_status_worker, "srvstatus")

    def _srv_status_worker(self):
        import socket
        for label, url in (("Wikipedia/Kiwix", CFG.SURVIVAL_WIKI_URL),
                           ("WDGWorldMap/Nav", CFG.SURVIVAL_CTOS_MAP_URL)):
            host, port = "localhost", 80
            try:
                rest = url.split("://", 1)[-1].split("/", 1)[0]
                if ":" in rest:
                    host, port = rest.split(":", 1); port = int(port)
            except Exception:
                pass
            up = False
            try:
                with socket.create_connection((host, port), timeout=2):
                    up = True
            except Exception:
                up = False
            self._term("[CRISIS] %-16s %s" % (label, "UP :%s" % port if up else "DOWN"),
                       "ok" if up else "warn")

    # ==================================================================
    # Companion-screen support (Update Game / Flipper / SubGHz / Watch / MITM)
    # ==================================================================

    # ---- Update Game ----
    def game_version(self) -> str:
        try:
            import importlib
            m = importlib.import_module("watchdogs")
            return getattr(m, "__version__", "?")
        except Exception:
            return "?"

    def _git(self, *args) -> list:
        """A git argv for the game repo. The UI runs as root (sudo) but root has no
        GitHub credentials for the private repo, so drop to the login user who does."""
        base = ["git", "-C", self._app_dir, *args]
        try:
            if os.geteuid() == 0 and os.environ.get("SUDO_USER"):
                return ["sudo", "-u", os.environ["SUDO_USER"], "-H", *base]
        except AttributeError:
            pass
        return base

    def check_game_update(self) -> None:
        self._game_check_t = time.time()
        def run():
            try:
                import subprocess
                subprocess.run(self._git("fetch", "--quiet"), timeout=45)
                r = subprocess.run(self._git("rev-list", "--count", "HEAD..@{u}"),
                                   capture_output=True, text=True, timeout=10)
                n = int((r.stdout or "0").strip() or "0")
                was = self._game_update
                self._game_update = n > 0
                self._game_remote = "%d update(s) available" % n if n else "up to date"
                if n > 0:
                    s = subprocess.run(self._git("log", "-1", "--format=%s", "@{u}"),
                                       capture_output=True, text=True, timeout=10)
                    self._game_latest = (s.stdout or "").strip()[:60]
                    # full changelog: every new remote commit subject (newest first)
                    cl = subprocess.run(self._git("log", "HEAD..@{u}", "--format=%s",
                                                  "--max-count=40"),
                                        capture_output=True, text=True, timeout=10)
                    self._game_changelog = [ln.strip() for ln in (cl.stdout or "").splitlines()
                                            if ln.strip()]
                    if not was:
                        self._term("[UPD] new version available (%d new): %s"
                                   % (n, self._game_latest), "ok")
                else:
                    self._game_changelog = []
            except Exception as exc:
                self._game_remote = "check failed: %s" % exc
        self._thread(run, "gamechk")

    def game_update_available(self) -> bool:
        return bool(self._game_update)

    def game_update_latest(self) -> str:
        return self._game_latest

    def game_changelog(self) -> list:
        return list(self._game_changelog)

    def consume_restart(self) -> bool:
        """True exactly once after a successful install — UI re-execs on it."""
        if self._game_restart:
            self._game_restart = False
            return True
        return False

    def game_update_info(self) -> tuple:
        return (self._game_remote, self._game_busy, list(self.game_log))

    def game_update_run(self) -> None:
        if self._game_busy:
            return
        self._game_busy = True
        self.game_log = ["[UPD] checking + installing latest..."]
        def run():
            ok = False
            try:
                import subprocess, shutil
                def g(*a, to=180):
                    r = subprocess.run(self._git(*a), capture_output=True,
                                       text=True, timeout=to)
                    for ln in (r.stdout + r.stderr).splitlines():
                        if ln.strip():
                            self.game_log.append(ln)
                    return r
                g("fetch", "--quiet")
                cnt = subprocess.run(self._git("rev-list", "--count", "HEAD..@{u}"),
                                     capture_output=True, text=True, timeout=15)
                n = int((cnt.stdout or "0").strip() or "0")
                if n == 0:
                    self.game_log.append("[UPD] already up to date")
                else:
                    # this is a pure consumer checkout (never pushes), so force the
                    # working tree to match GitHub — robust against deploy-dirtied files
                    rc = g("reset", "--hard", "@{u}").returncode
                    if rc == 0:
                        for sub in ("wdgong_ui", "watchdogs"):
                            shutil.rmtree(os.path.join(self._app_dir, sub, "__pycache__"),
                                          ignore_errors=True)
                        ok = True
                        self._game_update = False
                        self._game_remote = "up to date"
                        self.game_log.append("[UPD] installed %d update(s) - restarting..." % n)
                    else:
                        self.game_log.append("[UPD] install failed (git reset)")
            except Exception as exc:
                self.game_log.append("[UPD] error: %s" % exc)
            finally:
                self._game_busy = False
                if ok:
                    self._game_restart = True
        self._thread(run, "gameupd")

    # ==================================================================
    # User-data backup / restore — ONE portable file with everything the
    # player owns: loot/ (XP, badges, totals, captures, passwords, portals,
    # whitelist, + the consolidated loot/reticulum chat identity) + secrets.conf
    # + .watchdogs_mesh.json (LoRa mesh stack, MeshCore region, Meshtastic
    # region/preset/name). That file lives in the install folder, so without it
    # a move to a new install comes back on the EU defaults.
    # ==================================================================
    def _chown_user(self, path: str) -> None:
        """Hand a root-created file back to the login user so they can copy it
        off without sudo (the game runs as root)."""
        try:
            if os.geteuid() == 0 and os.environ.get("SUDO_UID"):
                uid = int(os.environ["SUDO_UID"]); gid = int(os.environ.get("SUDO_GID", uid))
                os.chown(path, uid, gid)
        except Exception:
            pass

    def backup_busy(self) -> bool:
        return self._backup_busy

    def export_userdata(self) -> None:
        if self._backup_busy:
            return
        self._backup_busy = True
        def run():
            try:
                import tarfile, tempfile
                ts = time.strftime("%Y-%m-%d_%H-%M-%S")
                home = self._user_home()
                final = os.path.join(home, "wdgo-backup-%s.tar.gz" % ts)
                loot = os.path.join(self._app_dir, "loot")
                secrets = os.path.join(self._app_dir, "secrets.conf")
                mesh = str(self._mesh_path())
                self._term("[DATA] exporting backup...", "tx")
                # Create a UNIQUE private file on a fresh descriptor: O_EXCL (mkstemp)
                # never follows a symlink or truncates an existing file, and 0600 keeps
                # the bundled secrets.conf + chat identity unreadable to other accounts
                # under umask 022. Everything is written and chowned through the SAME
                # fd (no path re-resolution), and only published under the final name
                # after a clean close.
                fd, tmp = tempfile.mkstemp(prefix=".wdgo-backup-%s-" % ts,
                                           suffix=".part", dir=home)
                try:
                    os.fchmod(fd, 0o600)
                    try:                     # hand to the login user via the fd itself
                        if os.geteuid() == 0 and os.environ.get("SUDO_UID"):
                            uid = int(os.environ["SUDO_UID"])
                            gid = int(os.environ.get("SUDO_GID", uid))
                            os.fchown(fd, uid, gid)
                    except Exception:
                        pass
                    rawf = os.fdopen(fd, "wb")
                    fd = -1                   # fdopen owns the descriptor now
                    with rawf:
                        with tarfile.open(fileobj=rawf, mode="w:gz") as tar:
                            if os.path.isdir(loot):
                                tar.add(loot, arcname="loot")
                            if os.path.isfile(secrets):
                                tar.add(secrets, arcname="secrets.conf")
                            if os.path.isfile(mesh):
                                tar.add(mesh, arcname=MESH_SETTINGS_NAME)
                    os.replace(tmp, final)    # atomic publish after the archive is closed
                    tmp = None
                finally:
                    if fd != -1:
                        try: os.close(fd)
                        except Exception: pass
                    if tmp and os.path.exists(tmp):
                        try: os.unlink(tmp)
                        except Exception: pass
                mb = os.path.getsize(final) / 1e6
                self._backup_path = final
                self._term("[DATA] backup saved: %s (%.1f MB)" % (final, mb), "ok")
            except Exception as exc:
                self._term("[DATA] backup failed: %s" % exc, "warn")
            finally:
                self._backup_busy = False
        self._thread(run, "backup")

    @staticmethod
    def _safe_backup_member(m) -> bool:
        """Accept ONLY regular files/dirs under loot/, or a single top-level
        secrets.conf or .watchdogs_mesh.json. Reject symlinks/hardlinks/devices,
        absolute paths, '..' escapes and anything else — enforced on EVERY Python version (no reliance
        on tar's data filter), so a crafted archive can never write app code."""
        name = m.name or ""
        if name.startswith("/") or "\\" in name or "\x00" in name:
            return False
        parts = [p for p in name.split("/") if p not in ("", ".")]
        if not parts or any(p == ".." for p in parts):
            return False
        if os.path.isabs(os.path.normpath(name)):
            return False
        if not (m.isreg() or m.isdir()):     # no links/devices/fifos
            return False
        top = parts[0]
        if top in ("secrets.conf", MESH_SETTINGS_NAME):
            return len(parts) == 1 and m.isreg()
        return top == "loot"

    def import_userdata(self) -> None:
        """Restore the newest ~/wdgo-backup-*.tar.gz, then relaunch to apply.

        The archive is extracted into a private temp dir and fully validated BEFORE
        the live loot/ and secrets.conf are touched, so a truncated or hostile
        backup can never delete or overwrite good data. The previous data is kept as
        *.pre-restore until success. The in-memory loot manager is frozen + detached
        first so its db can't be written over the restored files during the restart."""
        if self._backup_busy:
            return
        self._backup_busy = True
        def run():
            import tarfile, glob, shutil, tempfile
            restored = False
            tmpdir = None
            froze = False
            try:
                home = self._user_home()
                cands = sorted(glob.glob(os.path.join(home, "wdgo-backup-*.tar.gz")))
                if not cands:
                    self._term("[DATA] no backup found (%s/wdgo-backup-*.tar.gz)" % home, "warn")
                    return
                src = cands[-1]
                self._term("[DATA] restoring %s ..." % os.path.basename(src), "tx")

                # 1) Extract into a PRIVATE temp dir, member by member, validated.
                tmpdir = tempfile.mkdtemp(prefix=".wdgo-restore-", dir=self._app_dir)
                with tarfile.open(src, "r:gz") as tar:
                    for m in tar.getmembers():
                        if not self._safe_backup_member(m):
                            raise ValueError("unsafe archive entry: %r" % (m.name,))
                        # set_attrs=False: don't let the archive dictate mode/owner
                        # (e.g. a setuid bit); names validated, so it stays in tmpdir.
                        tar.extract(m, tmpdir, set_attrs=False)
                new_loot = os.path.join(tmpdir, "loot")
                new_secrets = os.path.join(tmpdir, "secrets.conf")
                new_mesh = os.path.join(tmpdir, MESH_SETTINGS_NAME)
                if not (os.path.isdir(new_loot) or os.path.isfile(new_secrets)):
                    raise ValueError("backup has no loot/ or secrets.conf")

                # 2) Freeze loot production + detach the live manager so neither the
                #    periodic save nor the restart teardown can write its stale db
                #    over the data we are about to restore.
                self._loot_frozen = True
                froze = True
                old_mgr = self.loot
                self.loot = None
                if old_mgr is not None:
                    try: old_mgr.close()     # its final write lands in the pre-restore undo
                    except Exception: pass

                # 3) Swap in, each piece with its own rollback. Validation already
                #    passed, so this is the only step that mutates live data.
                def _swap_in(src_path, dst_path, is_dir):
                    bak = dst_path + ".pre-restore"
                    if is_dir:
                        shutil.rmtree(bak, ignore_errors=True)
                    elif os.path.lexists(bak):
                        os.remove(bak)
                    had = os.path.lexists(dst_path)
                    if had:
                        shutil.move(dst_path, bak)   # keep old data as undo
                    try:
                        shutil.move(src_path, dst_path)
                        # The archive was extracted with the process umask, so force
                        # private perms: secrets.conf 0600, the loot tree 0700.
                        try:
                            os.chmod(dst_path, 0o700 if is_dir else 0o600)
                        except OSError:
                            pass
                    except Exception:
                        if had:                      # restore the original on failure
                            if os.path.lexists(dst_path):
                                (shutil.rmtree(dst_path, ignore_errors=True)
                                 if is_dir else os.remove(dst_path))
                            shutil.move(bak, dst_path)
                        raise

                loot_dir = os.path.join(self._app_dir, "loot")
                sec_file = os.path.join(self._app_dir, "secrets.conf")
                if os.path.isdir(new_loot):
                    _swap_in(new_loot, loot_dir, True)
                restored = True                      # loot (or secrets-only) is now in place
                if os.path.isfile(new_secrets):
                    try:
                        _swap_in(new_secrets, sec_file, False)
                    except Exception as exc:
                        self._term("[DATA] secrets.conf not restored: %s" % exc, "warn")
                if os.path.isfile(new_mesh):
                    try:
                        with open(new_mesh, encoding="utf-8") as f:
                            if not isinstance(json.load(f), dict):
                                raise ValueError("not a settings object")
                        _swap_in(new_mesh, str(self._mesh_path()), False)
                    except Exception as exc:
                        self._term("[DATA] mesh settings not restored: %s" % exc, "warn")
                self._term("[DATA] restored (previous data kept at *.pre-restore) - restarting...", "ok")
            except Exception as exc:
                self._term("[DATA] restore failed - data left unchanged: %s" % exc, "warn")
                if froze and not restored:
                    self._loot_frozen = False        # recover: nothing was swapped
            finally:
                if tmpdir and os.path.isdir(tmpdir):
                    shutil.rmtree(tmpdir, ignore_errors=True)
                self._backup_busy = False
                if restored:
                    self._game_restart = True        # UI re-execs with the restored data
        self._thread(run, "restore")

    # ---- Flipper ----
    def flipper_connected(self) -> bool:
        f = self._mgrs.get("flipper"); return bool(f and getattr(f, "connected", False))

    def flipper_info(self) -> tuple:
        f = self._mgrs.get("flipper")
        return (getattr(f, "device_name", "") or "Flipper", getattr(f, "firmware", "") or "") if f else ("", "")

    def flipper_send(self, cmd: str) -> None:
        f = self._mgr("flipper")
        if not f:
            return
        def run():
            try:
                for ln in (f.send(cmd) or []):
                    self.flipper_log.append(str(ln))
            except Exception as exc:
                self.flipper_log.append("err: %s" % exc)
            self.flipper_log[:] = self.flipper_log[-400:]
        self._thread(run, "flip")

    def flipper_subghz(self, freq: int = 433920000, raw: bool = False) -> None:
        f = self._mgr("flipper")
        if not f:
            return
        try:
            f.start_rx(lambda ln: self.flipper_log.append(str(ln)))
            (f.subghz_rx_raw if raw else f.subghz_rx)(freq)
            self.flipper_log.append("[FLIP] SubGHz RX %d%s" % (freq, " RAW" if raw else ""))
        except Exception as exc:
            self.flipper_log.append("err: %s" % exc)

    def flipper_stop(self) -> None:
        f = self._mgrs.get("flipper")
        try:
            if f:
                f.subghz_stop(); self.flipper_log.append("[FLIP] stopped")
        except Exception:
            pass

    # ---- SubGHz (Monster RF) ----
    def subghz_connected(self) -> bool:
        s = self._mgrs.get("subghz"); return bool(s and getattr(s, "port", None))

    def subghz_rssi(self) -> int:
        s = self._mgrs.get("subghz"); return int(getattr(s, "rssi", -120)) if s else -120

    def subghz_catches(self) -> int:
        s = self._mgrs.get("subghz"); return int(getattr(s, "key_count", 0)) if s else 0

    def subghz_cmd(self, which: str, freq: int = 0) -> None:
        s = self._mgr("subghz")
        if not s:
            self.subghz_log.append("[SUBGHZ] no board"); return
        try:
            if which == "scan": s.cmd_scan()
            elif which == "rx": s.cmd_rx()
            elif which == "analyzer": s.cmd_analyzer()
            elif which == "stop": s.cmd_stop()
            elif which == "save": s.cmd_save()
            elif which == "status": s.cmd_status()
            elif which == "freq" and freq: s.cmd_freq(freq)
            self.subghz_log.append("[SUBGHZ] " + which)
        except Exception as exc:
            self.subghz_log.append("err: %s" % exc)

    # ---- Watch (PipBoy) ----
    def watch_scan(self) -> None:
        w = self._mgr("watch")
        if not w:
            return
        # w.scan() does blocking bluetoothctl calls (5 s timeouts + a 3 s settle), so
        # run it OFF the UI loop and refuse a duplicate while one is already running.
        if getattr(self, "_watch_scan_busy", False):
            return
        self._watch_scan_busy = True
        def run():
            try:
                self.watch_log.append("[WATCH] scanning...")
                w.scan()
            except Exception as exc:
                self.watch_log.append("err: %s" % exc)
            finally:
                self._watch_scan_busy = False
        self._thread(run, "watch-scan")

    def watch_connected(self) -> bool:
        w = self._mgrs.get("watch"); return bool(w and getattr(w, "connected", False))

    def watch_scanning(self) -> bool:
        w = self._mgrs.get("watch"); return bool(w and getattr(w, "scanning", False))

    def _watch_contract_error(self, what: str, exc: Exception) -> None:
        """Report a WatchManager API mismatch ONCE (this is polled every frame), so
        a broken contract shows up in the terminal instead of as a silent empty list."""
        seen = self.__dict__.setdefault("_watch_errs", set())
        if what not in seen:
            seen.add(what)
            self._term("[WATCH] %s unavailable: %s" % (what, exc), "err")

    def watch_results(self) -> list:
        w = self._mgrs.get("watch")
        if w is None:
            return []
        try:
            return list(w.scan_results)          # property on WatchManager
        except Exception as exc:
            self._watch_contract_error("scan_results", exc)
            return []

    def watch_connect(self, addr: str) -> None:
        w = self._mgr("watch")
        if w:
            try: w.connect(addr); self.watch_log.append("[WATCH] connecting " + addr)
            except Exception as exc: self.watch_log.append("err: %s" % exc)

    def watch_pin_requested(self) -> bool:
        w = self._mgrs.get("watch")
        if w is None:
            return False
        try:
            return bool(w.pin_requested)         # property on WatchManager
        except Exception as exc:
            self._watch_contract_error("pin_requested", exc)
            return False

    def watch_provide_pin(self, pin: int) -> None:
        w = self._mgrs.get("watch")
        try:
            if w: w.provide_pin(pin)
        except Exception: pass

    def watch_send(self, cmd: str) -> None:
        w = self._mgrs.get("watch")
        try:
            if w: w.send_command(cmd); self.watch_log.append("[WATCH] > " + cmd)
        except Exception as exc: self.watch_log.append("err: %s" % exc)

    def watch_battery(self) -> int:
        w = self._mgrs.get("watch"); return int(getattr(w, "battery", -1)) if w else -1

    # ---- MITM ----
    def mitm_ifaces(self) -> list:
        m = self._mgr("mitm")
        try: return list(m.get_interfaces()) if m else []
        except Exception: return []

    def mitm_running(self) -> bool:
        m = self._mgrs.get("mitm"); return bool(m and getattr(m, "running", False))

    def mitm_packets(self) -> int:
        m = self._mgrs.get("mitm"); return int(getattr(m, "packets", 0)) if m else 0

    def mitm_start(self, iface: str, victim: str = "") -> None:
        m = self._mgr("mitm")
        if not m:
            self._term("[MITM] scapy/root required", "warn"); return
        def run():
            try:
                self.mitm_state = "running"
                if m.start(iface, victim_ip=victim):
                    self._term("[MITM] ARP spoof on %s" % iface, "ok")
                else:
                    self.mitm_state = "idle"
            except Exception as exc:
                self.mitm_state = "idle"; self._term(f"[MITM] {exc}", "warn")
        self._thread(run, "mitm")

    def mitm_stop(self) -> None:
        m = self._mgrs.get("mitm")
        try:
            if m: m.stop()
        except Exception: pass
        self.mitm_state = "idle"; self._term("[MITM] stopped", "warn")

    # ---- derived HUD data ----
    def hat_profile(self) -> tuple:
        """(name, color) identity chip: WHITE/BLUE/GREY/RED/BLACK by attack ratio."""
        t = self.totals()
        scan = t.get("wardriving", 0) + t.get("bt_devices", 0)
        hs = t.get("pcap", 0) or t.get("hccapx", 0)
        creds = t.get("passwords", 0) + t.get("et_captures", 0)
        attack = hs * 3 + creds * 10
        ratio = attack / max(1, scan + attack)
        if creds >= 5 or ratio > 0.6: return ("BLACK HAT", (20, 20, 24))
        if hs >= 10 or ratio > 0.35:  return ("RED HAT", (255, 59, 48))
        if hs >= 3 or ratio > 0.15:   return ("GREY HAT", (150, 160, 172))
        if scan > 50:                 return ("BLUE HAT", (90, 150, 255))
        return ("WHITE HAT", (235, 245, 255))

    def read_battery(self) -> int:
        now = time.time()
        if now - self._bat_ts > 20:
            self._bat_ts = now
            try:
                for base in ("/sys/class/power_supply/axp20x-battery",
                             "/sys/class/power_supply/BAT0", "/sys/class/power_supply/battery"):
                    cap = Path(base) / "capacity"
                    if cap.is_file():
                        self.battery_pct = int(cap.read_text().strip())
                        vp = Path(base) / "voltage_now"
                        if vp.is_file():
                            self.batt_mv = int(vp.read_text().strip()) // 1000   # uV -> mV
                        break
            except Exception:
                pass
            # The AXP223 fuel gauge reports capacity% unreliably (it can read ~100%
            # while the cell is actually sagging under load). Voltage is the honest
            # signal, so warn on VOLTAGE, with hysteresis. A low pack is also exactly
            # what makes the uConsole speaker amp hiss/crackle, so the hint says so.
            if self.batt_mv:
                if self.batt_mv < 3450 and not self._batt_warned:
                    self._batt_warned = True
                    self._term("[BATT] voltage low %.2fV - connect power (low batt also causes speaker crackle)"
                               % (self.batt_mv / 1000.0), "warn")
                elif self.batt_mv > 3650:
                    self._batt_warned = False      # recovered / on charger -> re-arm
        return self.battery_pct

    def battery_mv(self) -> int:
        return self.batt_mv

    def loot_points(self) -> list:
        """All-sessions saved GPS points for the map clusters (cached 30s). Read-only
        — scans loot/*/wardriving.csv + bt_devices.csv WITHOUT creating a LootManager
        write-session (reuses LootManager.get_gps_points on a tiny read-only stand-in)."""
        now = time.time()
        # Stale-while-revalidate: the scan walks every loot/*/ CSV and can take a
        # while on an SD card, so do it in the BACKGROUND and keep returning the last
        # complete list — the frame thread never blocks on disk.
        if (now - self._loot_points_ts > 30
                and not getattr(self, "_loot_points_building", False)):
            self._loot_points_ts = now
            self._loot_points_building = True
            app_dir = self._app_dir
            def _refresh():
                try:
                    from watchdogs.loot_manager import LootManager

                    class _RO:
                        _base = Path(app_dir) / "loot"
                        _gps_points_cache = None
                        _gps_points_ts = 0.0
                    self._loot_points_cache = LootManager.get_gps_points(_RO()) or []
                except Exception as exc:
                    self._term("[MAP] loot points unavailable: %s" % exc, "warn")
                    # keep the previous cache rather than blanking the map
                finally:
                    self._loot_points_building = False
            self._thread(_refresh, "lootpts")
        return self._loot_points_cache

    def check_fw_update(self) -> None:
        """Background: fetch the latest firmware release tag and flag an update when the
        ESP's reported version is older (semver). Needs _fw_version from the serial stream."""
        self._fw_check_t = time.time()
        def run():
            try:
                import json as _j
                from urllib.request import Request, urlopen
                req = Request(CFG.FIRMWARE_RELEASE_URL); req.add_header("User-Agent", "WatchDogsGo")
                with urlopen(req, timeout=12) as r:
                    tag = _j.loads(r.read()).get("tag_name", "")
                self._fw_remote = tag.lstrip("v")
                local = self._fw_version.lstrip("v")
                if self._fw_remote and local:
                    try:
                        r_parts = [int(x) for x in self._fw_remote.split(".")]
                        l_parts = [int(x) for x in local.split(".")]
                        if r_parts > l_parts:
                            self._fw_update = True
                            self._term("[FW] update available: v%s -> v%s"
                                       % (local, self._fw_remote), "warn")
                    except ValueError:
                        pass
            except Exception:
                pass
        self._thread(run, "fwchk")

    def fw_remote(self) -> str:
        return self._fw_remote

    def fw_update_available(self) -> bool:
        return bool(self._fw_update)

    def fw_latest(self) -> str:
        return self._fw_remote

    def fw_current(self) -> str:
        return self._fw_version

    def mc_bubble_active(self):
        if self.mc_bubble and time.time() < self.mc_bubble[1]:
            return self.mc_bubble[0]
        return None

    # ------------------------------------------------------------------
    # Data accessors for the UI
    # ------------------------------------------------------------------

    def networks(self, limit=None) -> list:
        import itertools
        src = self.state.networks if self.state else getattr(self, "_demo_nets", [])
        if limit is not None:
            return list(itertools.islice(src, max(0, int(limit))))
        return list(src)

    def network_count(self) -> int:
        src = self.state.networks if self.state else getattr(self, "_demo_nets", [])
        return len(src)

    def totals(self) -> dict:
        if self.loot:
            try:
                return dict(self.loot.loot_totals or {})
            except Exception:
                pass
        return dict(self._db_totals)

    # ------------------------------------------------------------------
    # Session journal — per-session archive for the loot screen. Hundreds of
    # session dirs can exist, so it is indexed once in a background thread.
    # ------------------------------------------------------------------
    def _session_counts(self, d) -> dict:
        def _data_lines(name, header=1):
            try:
                with open(d / name, encoding="utf-8", errors="replace") as f:
                    return max(0, sum(1 for _ in f) - header)
            except Exception:
                return 0
        hs = 0
        hsd = d / "handshakes"
        if hsd.is_dir():
            try:
                hs = sum(1 for f in hsd.iterdir()
                         if f.suffix in (".pcap", ".cap", ".pcapng"))
            except Exception:
                hs = 0
        # wardriving.csv (WiGLE 1.6) holds BOTH WiFi and BLE rows — split them by
        # the Type column (the last field) instead of counting the whole file as WiFi.
        # BLE MACs go into a set so a device recorded in BOTH wardriving.csv and
        # bt_devices.csv is counted ONCE (union), not twice.
        wd_wifi = 0
        ble_macs: set = set()
        try:
            with open(d / "wardriving.csv", encoding="utf-8", errors="replace") as f:
                for ln in f:
                    fields = ln.rstrip("\r\n").split(",")
                    t = fields[-1].strip().upper() if fields else ""
                    if t == "BLE":
                        mac = fields[0].strip().upper()
                        if ":" in mac:
                            ble_macs.add(mac)
                    elif t == "WIFI":
                        wd_wifi += 1
        except Exception:
            pass
        try:
            with open(d / "bt_devices.csv", encoding="utf-8", errors="replace") as f:
                for i, ln in enumerate(f):
                    if i == 0:
                        continue                 # header
                    mac = ln.split(",", 1)[0].strip().upper()
                    if ":" in mac:
                        ble_macs.add(mac)
        except Exception:
            pass
        return {
            "wifi": wd_wifi,
            "bt": len(ble_macs),
            "hs": hs,
            "mc": _data_lines("meshcore_nodes.csv", 1),
            "adsb": self._adsb_unique(d / "adsb_aircraft.csv"),
            # Sessions with ONLY SDR alerts or ONLY mesh messages were hidden before
            # (n==0); count these so their files stay reachable from the journal.
            "mc_msgs": _data_lines("meshcore_messages.log", 0),   # no header
            "emergency": _data_lines("emergency_rf.csv", 1),
        }

    def _adsb_unique(self, path) -> int:
        """Aircraft in a session = distinct ICAO codes. adsb_aircraft.csv is a TRACK log
        (one row per position update), so its line count is not a number of aircraft.
        Cached per file size + mtime: the file grows to MBs during a long session."""
        try:
            st = path.stat()
        except OSError:
            return 0
        cache = self.__dict__.setdefault("_adsb_cache", {})
        key = (str(path), st.st_size, st.st_mtime_ns)
        if cache.get(str(path), (None,))[0] == key:
            return cache[str(path)][1]
        seen = set()
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                next(f, None)                                  # header
                for ln in f:
                    parts = ln.split(",", 2)
                    if len(parts) > 1 and parts[1].strip():
                        seen.add(parts[1].strip().upper())
        except OSError:
            return 0
        cache[str(path)] = (key, len(seen))
        return len(seen)

    def _build_sessions(self) -> None:
        out = []
        try:
            base = Path(self._app_dir) / "loot"
            if base.is_dir():
                dirs = [p for p in base.iterdir()
                        if p.is_dir() and not p.is_symlink()      # never index a symlinked session
                        and len(p.name) >= 10 and p.name[:4].isdigit()]
                for d in sorted(dirs, key=lambda p: p.name, reverse=True):
                    c = self._session_counts(d)
                    out.append({"name": d.name, "counts": c,
                                "n": (c["wifi"] + c["bt"] + c["hs"] + c["mc"] + c["adsb"]
                                      + c["mc_msgs"] + c["emergency"])})
        except Exception:
            pass
        # The journal is an EVENT log: keep only sessions that captured something
        # (the game creates a dir on every launch, so most are empty noise).
        self._sessions_cache = [x for x in out if x["n"]]
        self._sessions_empty = len(out) - len(self._sessions_cache)
        self._sessions_building = False

    def sessions_empty(self) -> int:
        return int(getattr(self, "_sessions_empty", 0))

    def sessions(self):
        """Per-session journal, newest first. None while still indexing (built
        once in the background), then a cached list of
        {name, counts{wifi,bt,hs,mc,adsb}, n}."""
        cache = getattr(self, "_sessions_cache", None)
        if cache is not None:
            return cache
        if not getattr(self, "_sessions_building", False):
            self._sessions_building = True
            import threading as _th
            _th.Thread(target=self._build_sessions, daemon=True).start()
        return None

    def sessions_refresh(self) -> None:
        """Re-index in the background, swapping the cache in atomically when done
        (keeps the old list visible meanwhile — no 'indexing...' flicker)."""
        if not getattr(self, "_sessions_building", False):
            self._sessions_building = True
            import threading as _th
            _th.Thread(target=self._build_sessions, daemon=True).start()

    def _adsb_rx_log(self) -> None:
        """While ADS-B runs with a GPS fix, note where the receiver is (every 30 s) in
        the session's adsb_receiver.csv - range/coverage are measured from it."""
        now = time.time()
        if now - getattr(self, "_adsb_rx_t", 0.0) < 30.0:
            return
        self._adsb_rx_t = now
        try:
            m = self._mgrs.get("sdr")
            st = self.state
            if not (m and getattr(m, "running", False) and "adsb" in str(getattr(m, "mode", ""))):
                return
            if not (st and st.gps_fix_valid and self.loot and self.loot.active):
                return
            path = os.path.join(self.loot.session_dir, "adsb_receiver.csv")
            new = not os.path.exists(path)
            with open(path, "a", encoding="utf-8") as f:
                if new:
                    f.write("timestamp,lat,lon\n")
                f.write("%d,%.6f,%.6f\n" % (int(now), st.gps_latitude, st.gps_longitude))
        except Exception:
            pass

    def adsb_tracks(self, name: str):
        """Tracks + coverage of one session (see adsb_tracks.load), or None."""
        base = Path(self._app_dir) / "loot" / name
        if not (base / "adsb_aircraft.csv").is_file():
            return None
        try:
            import adsb_tracks
            st = self.state
            fix = (st.gps_latitude, st.gps_longitude) if (st and st.gps_fix_valid) else None
            return adsb_tracks.load(str(base), current_fix=fix)
        except Exception as exc:
            self._term("[ADS-B] cannot read tracks: %s" % exc, "warn")
            return None

    def adsb_export_kml(self, name: str, data) -> str:
        """Write loot/<session>/adsb_tracks.kml; returns its path or ''."""
        try:
            import adsb_tracks
            p = adsb_tracks.write_kml(str(Path(self._app_dir) / "loot" / name), data)
            self._term("[ADS-B] KML saved: %s" % p, "ok")
            return p
        except Exception as exc:
            self._term("[ADS-B] KML export failed: %s" % exc, "warn")
            return ""

    def session_files(self, name: str) -> list:
        """Files inside one session dir, for the drill-in view: [{name, size}]."""
        out = []
        root = (Path(self._app_dir) / "loot").resolve()
        sess = Path(self._app_dir) / "loot" / name
        if sess.is_symlink():                      # never follow a symlinked session
            return out
        base = sess.resolve()
        if base.parent != root or not base.is_dir():
            return out
        try:
            for root, _dirs, files in os.walk(base):
                for fn in files:
                    fp = Path(root) / fn
                    try:
                        sz = fp.stat().st_size
                    except Exception:
                        sz = 0
                    out.append({"name": str(fp.relative_to(base)), "size": sz})
        except Exception:
            pass
        out.sort(key=lambda x: x["name"])
        return out

    def file_preview(self, name: str, rel: str, max_bytes: int = 65536) -> dict:
        """Preview one file inside a session: text lines, or a hex dump for binary.
        Returns {kind: text|binary|error, lines: [...], size, truncated}."""
        root = (Path(self._app_dir) / "loot").resolve()
        sess = Path(self._app_dir) / "loot" / name
        if sess.is_symlink():                         # never read through a symlinked session
            return {"kind": "error", "lines": ["symlinked session refused"], "size": 0}
        base = sess.resolve()
        if base.parent != root or not base.is_dir():
            return {"kind": "error", "lines": ["invalid session"], "size": 0}
        try:
            fp = (base / rel).resolve()
            # path-component check (not startswith): a sibling like loot/<name>-x must
            # not pass, and a symlink pointing outside resolves out of base and fails.
            if not fp.is_relative_to(base):
                return {"kind": "error", "lines": ["invalid path"], "size": 0}
            if not fp.is_file():
                return {"kind": "error", "lines": ["not a file"], "size": 0}
            size = fp.stat().st_size
            with open(fp, "rb") as f:
                raw = f.read(max_bytes)
        except Exception as exc:
            return {"kind": "error", "lines": [str(exc)], "size": 0}
        ext = fp.suffix.lower()
        text_ext = {".csv", ".log", ".json", ".txt", ".potfile", ".22000",
                    ".conf", ".cfg", ".ini", ".md", ".nmea", ""}
        is_text = ext in text_ext
        if not is_text:                                # sniff: mostly-printable => text
            sample = raw[:1024]
            nonprint = sum(1 for b in sample if b < 9 or 13 < b < 32)
            is_text = bool(sample) and (nonprint / len(sample)) < 0.05
        if is_text:
            txt = raw.decode("utf-8", "replace")
            return {"kind": "text", "lines": txt.splitlines(),
                    "size": size, "truncated": size > len(raw)}
        hexlines = []
        for off in range(0, min(len(raw), 1024), 16):
            chunk = raw[off:off + 16]
            hx = " ".join("%02x" % b for b in chunk)
            asc = "".join(chr(b) if 32 <= b < 127 else "." for b in chunk)
            hexlines.append("%04x  %-47s  %s" % (off, hx, asc))
        return {"kind": "binary", "lines": hexlines, "size": size,
                "truncated": len(raw) < size}

    def active_session_name(self) -> str:
        """Name of the loot dir currently being written to ("" if none). The
        session manager protects this one from deletion — it's still growing."""
        try:
            if self.loot and getattr(self.loot, "active", False):
                return Path(self.loot.session_path).name
        except Exception:
            pass
        return ""

    def uploaded_sessions(self) -> set:
        """Cached set of fully-uploaded session names (.portal_sync_state.json),
        3s TTL — the LOOT journal and the delete dialog query this per frame, so
        it must not hit disk every time."""
        now = time.time()
        if now - getattr(self, "_upl_ts", 0) > 3:
            s = set()
            try:
                sp = Path(self._app_dir) / ".portal_sync_state.json"
                if sp.is_file():
                    s = set(json.loads(sp.read_text()).get("uploaded", []))
            except Exception:
                pass
            self._upl_cache = s
            self._upl_ts = now
        return getattr(self, "_upl_cache", set())

    def session_uploaded(self, name: str) -> bool:
        """True if the portal uploader has fully acknowledged this session
        (every batch confirmed). Lets the journal tag rows and the delete dialog
        warn when data hasn't reached the portal yet."""
        return name in self.uploaded_sessions()

    def session_size(self, name: str) -> int:
        """Total bytes on disk for one session dir (0 on any error)."""
        root = (Path(self._app_dir) / "loot").resolve()
        sess = Path(self._app_dir) / "loot" / name
        if sess.is_symlink():
            return 0
        base = sess.resolve()
        if base.parent != root or not base.is_dir():
            return 0
        total = 0
        try:
            for r, _d, files in os.walk(base):
                for fn in files:
                    try:
                        total += (Path(r) / fn).stat().st_size
                    except Exception:
                        pass
        except Exception:
            pass
        return total

    def delete_session(self, name: str) -> tuple:
        """Permanently delete one loot session dir. Refuses the active session
        and anything outside loot/ (path-escape guard). Returns (ok, message).
        This erases capture data for good — the UI confirms before calling it."""
        if not name:
            return False, "no session selected"
        root = (Path(self._app_dir) / "loot").resolve()
        link = Path(self._app_dir) / "loot" / name
        # A symlinked "session" could point at the real active session (or anywhere):
        # refuse it outright instead of resolving and deleting its target.
        if link.is_symlink():
            return False, "symlinked session refused"
        target = link.resolve()
        # must be a direct, real child of loot/ and actually a dir
        if target.parent != root or not target.is_dir():
            return False, "invalid session"
        # Compare REAL paths with the active session so a crafted name can't delete it.
        act = self.active_session_name()
        if name == act:
            return False, "active session - stop recording first"
        if act:
            try:
                if target == (Path(self._app_dir) / "loot" / act).resolve():
                    return False, "active session - stop recording first"
            except Exception:
                pass
        import shutil as _shutil
        try:
            _shutil.rmtree(target)
        except Exception as exc:
            return False, "delete failed: %s" % exc
        # drop it from the uploader's done-set so the name can't shadow a future
        # session, and re-index the journal in the background.
        try:
            sp = Path(self._app_dir) / ".portal_sync_state.json"
            if sp.is_file():
                data = json.loads(sp.read_text())
                up = set(data.get("uploaded", []))
                if name in up:
                    up.discard(name)
                    data["uploaded"] = sorted(up)
                    sp.write_text(json.dumps(data))
        except Exception:
            pass
        self._upl_ts = 0            # invalidate the uploaded-sessions cache
        try:
            self.sessions_refresh()
        except Exception:
            pass
        return True, "deleted %s" % name

    def xp(self) -> int:
        return int(self._xp)

    def gps_text(self) -> str:
        if self.state and self.state.gps_fix_valid:
            la, lo = self.state.gps_latitude, self.state.gps_longitude
            return "%.5f%s %.5f%s" % (
                abs(la), "N" if la >= 0 else "S",
                abs(lo), "E" if lo >= 0 else "W",
            )
        return "NO GPS FIX"

    def gps_sats(self) -> int:
        return self.state.gps_satellites if self.state else 0

    # ---- live subsystem state for the HUD ----
    def lora_on(self) -> bool:
        m = self._mgrs.get("lora"); return bool(m and getattr(m, "running", False))

    def sdr_on(self) -> bool:
        m = self._mgrs.get("sdr"); return bool(m and getattr(m, "running", False))

    def sdr_mode(self) -> str:
        m = self._mgrs.get("sdr"); return str(getattr(m, "mode", "")) if m else ""

    def sdr_enabled(self) -> bool:
        """True when the AIO SDR power rail is on (RTL dongle powered) — mirrors the
        OG top ('SDR', _sdr_enabled) indicator. Cheap cached flag, no GPIO read/frame."""
        return bool(self._sdr_rail)

    def scan_count(self) -> int:
        return len(self.state.networks) if self.state else 0

    def contacts_count(self) -> int:
        # The LOOT screen reads this every frame, so cache it (3 s TTL) instead of
        # opening + parsing loot_db.json on each render.
        now = time.time()
        if now - getattr(self, "_contacts_ct_ts", 0.0) > 3.0:
            self._contacts_ct_ts = now
            try:
                p = Path(self._app_dir) / "loot" / "loot_db.json"
                with open(p, encoding="utf-8") as f:
                    self._contacts_ct = len(json.load(f).get("mc_contacts", {}))
            except Exception:
                self._contacts_ct = getattr(self, "_contacts_ct", 0)
        return getattr(self, "_contacts_ct", 0)

    def consume_scan_done(self) -> bool:
        """One-shot: True once after a WiFi scan finishes (for UI feedback)."""
        v = getattr(self, "_scan_done_pulse", False)
        self._scan_done_pulse = False
        return v

    def system_check(self) -> list:
        """Boot dependency + hardware probe, like the OG preflight.
        Returns [(label, status, state)] with state in ok|warn|fail|info."""
        import importlib, shutil as _sh
        rows = []

        def dep(label, mod, required, attr="__version__"):
            try:
                m = importlib.import_module(mod)
                ver = getattr(m, attr, None) or getattr(m, "VERSION", None) or "OK"
                rows.append((label, str(ver), "ok"))
            except Exception:
                rows.append((label, "NOT INSTALLED", "fail" if required else "warn"))

        v = sys.version_info
        rows.append(("Python 3.10+", "%d.%d.%d" % (v.major, v.minor, v.micro),
                     "ok" if v >= (3, 10) else "fail"))
        dep("raylib", "pyray", True, "__version__")
        dep("pyserial", "serial", True)
        dep("requests", "requests", False)
        dep("scapy", "scapy", False, "VERSION")
        dep("bleak", "bleak", False)
        dep("dbus-python", "dbus", False)
        dep("LoRaRF", "LoRaRF", False)
        dep("reticulum (rns)", "RNS", False)
        dep("lxmf", "LXMF", False)
        dep("esptool", "esptool", False)
        rows.append(("dump1090", "OK" if _sh.which("dump1090") else "NOT INSTALLED",
                     "ok" if _sh.which("dump1090") else "warn"))
        rows.append(("rtl_433", "OK" if _sh.which("rtl_433") else "NOT INSTALLED",
                     "ok" if _sh.which("rtl_433") else "warn"))
        # hardware + data
        if HAVE_BACKEND:
            try:
                port = os.environ.get("WDGO_PORT") or detect_esp32_port()
            except Exception:
                port = None
            rows.append(("ESP32 serial", port or "not detected", "ok" if port else "warn"))
            gdev = getattr(CFG, "GPS_DEVICE", "/dev/ttyAMA0")
            rows.append(("GPS device", gdev if os.path.exists(gdev) else "none", "ok" if os.path.exists(gdev) else "info"))
            s = self._db_totals.get("sessions", 0)
            rows.append(("loot database", "%d sessions" % s, "ok" if s else "info"))
        else:
            rows.append(("backend", "DEMO (no watchdogs)", "warn"))
        return rows

    def status(self) -> str:
        return self._status

    def set_status(self, s: str) -> None:
        self._status = s
