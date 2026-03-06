#!/usr/bin/env python3
"""
rom-assets-manager.py
  Manage a ROM library: cover art, backgrounds, deduplication, completeness checks,
  filename normalisation, and cross-system exclusives filtering.

  Cross-platform (Windows / Linux / macOS) · Python 3.8+ · no external pip deps
  Run with no arguments for the interactive wizard, or --help for CLI options.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WIZARD TASKS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  [1] Check duplicate ROMs (hash-based)
        Four-stage pipeline: group by size → CRC32 → SHA-1 → same-title name
        matching. Byte-identical files are confirmed exact duplicates.
        Same-title pairs with different content (regional variants, patches)
        are surfaced separately.
        Deletion strategies: shortest name · smallest size · oldest · newest ·
        preferred region (USA > World > Europe > Japan).
        Bad-tagged files (Beta, Demo, Proto, [b]/[h]/[t]) are auto-removed when
        a clean copy exists in the same group.

  [2] Normalize ROM filenames
        Strips region / revision tags, moves trailing articles to the front.
          "Legend of Zelda, The (USA) (Rev A).nes"  →  "The Legend of Zelda.nes"
          "Final Fantasy VII (Disc 2) (USA).iso"    →  "Final Fantasy VII (Disc 2).iso"
        Dry-run by default; prompts before renaming.

  [3] Filter non-exclusives across systems
        Given a "main" system, removes games from sibling system folders that
        also exist in the main collection. Only compares systems in the same
        generation family (8-bit, 16-bit, handhelds, 32-bit, 128-bit).

  [4] Check ROM set completeness
        Compare a ROM folder against a No-Intro Logiqx XML DAT file.
        Region modes: USA (1G1R) · Europe (1G1R) · Japan (1G1R) ·
                      Japan exclusives · Full set (no filter).
        Outputs a CSV report and an optional plain-text want-list.
        DAT files: https://dat-o-matic.no-intro.org

  [5] Download covers + backgrounds
  [6] Download covers only
  [7] Download backgrounds only
        Sources (in priority order):
          libretro-thumbnails (GitHub)  — high-quality boxart with system logo
          SteamGridDB                   — requires a free API key
          LaunchBox GamesDB             — no key required
        Cover styles:
          with_logo     Box art with system logo overlay (default)
          without_logo  Clean grid art (SGDB) or screenshot (LaunchBox)
          game_logo     Title / game logo art
        Background styles:
          fanart   SGDB Heroes → LaunchBox Fanart-Background (1920×1080)
          boxart   Box art letterboxed to 1920×1080
        Download modes:
          missing  Download only ROMs without a cover yet (default)
          all      Re-download and overwrite every cover
        Pre-existing wrong-sized covers are resized in "missing" mode.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  DEPENDENCIES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  ImageMagick   Required for cover/background conversion and resizing.
                  Windows : winget install ImageMagick.Q16-HDRI
                  Linux   : sudo apt install imagemagick
                  macOS   : brew install imagemagick

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  KEY CLI FLAGS  (non-wizard use)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  --roms <dir>              ROMs root folder
  --covers <dir>            Covers root folder
  --backgrounds <dir>       Backgrounds root folder
  --no-dry-run              Apply changes (default is dry run)
  --check-duplicates        Run hash-based duplicate scan (task 1)
  --check-completeness      Run completeness check against a DAT (task 4)
  --dat <file>              No-Intro DAT file (with --check-completeness)
  --download-mode           missing | all | skip  (default: missing)
  --cover-style             with_logo | without_logo | game_logo
  --bg-style                fanart | boxart
  --region                  any | usa | europe | japan | world
  --sgdb-key <key>          SteamGridDB API key  (or set SGDB_KEY env var)
  --github-token <tok>      GitHub token for higher rate limits
                            (or set GITHUB_TOKEN env var)
  --delete-orphans          Remove covers/backgrounds with no matching ROM
  --report <file>           Report output path  (pass 'none' to disable)
  --threshold <0.0-1.0>     Fuzzy match threshold  (default 0.4)
  --parallel-jobs <n>       Download workers  (default 6)
"""

from __future__ import annotations

import argparse
import csv
import dataclasses
import functools
import getpass
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import zipfile
import zlib
from collections import Counter, defaultdict
from collections.abc import Callable
from typing import IO, TextIO
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path

# Aliases wired up after the name-based dedup helpers section below.
_COMPANION_TOOLS = True

# =============================================================================
# ANSI COLOURS  (auto-disabled when not supported)
# =============================================================================
def _ansi(code): return f"\033[{code}m"

def _try_enable_windows_ansi() -> bool:
    """Enable ANSI VT processing on Windows (SetConsoleMode). Returns True on success."""
    try:
        import ctypes, ctypes.wintypes
        STD_OUTPUT_HANDLE    = -11
        ENABLE_VT_PROCESSING = 0x0004
        handle = ctypes.windll.kernel32.GetStdHandle(STD_OUTPUT_HANDLE)
        if handle == ctypes.wintypes.HANDLE(-1).value:
            return False
        mode = ctypes.wintypes.DWORD()
        if not ctypes.windll.kernel32.GetConsoleMode(handle, ctypes.byref(mode)):
            return False
        if mode.value & ENABLE_VT_PROCESSING:
            return True
        return bool(ctypes.windll.kernel32.SetConsoleMode(
            handle, mode.value | ENABLE_VT_PROCESSING))
    except Exception:
        return False

def _detect_color_support() -> bool:
    """Return True if the terminal is likely to render ANSI escape codes."""
    if not sys.stdout.isatty():
        return False
    if os.name != "nt":
        return True
    if _try_enable_windows_ansi():
        return True
    # Fallback for third-party wrappers that handle ANSI themselves.
    return (
        "WT_SESSION" in os.environ                     # Windows Terminal
        or "ANSICON" in os.environ
        or os.environ.get("TERM_PROGRAM") == "vscode"
    )

USE_COLOR = _detect_color_support()

class C:
    # "D" prefix = bright variant
    RESET   = _ansi(0)   if USE_COLOR else ""
    CYAN    = _ansi(36)  if USE_COLOR else ""
    GREEN   = _ansi(32)  if USE_COLOR else ""
    YELLOW  = _ansi(33)  if USE_COLOR else ""
    RED     = _ansi(31)  if USE_COLOR else ""
    MAGENTA = _ansi(35)  if USE_COLOR else ""
    GRAY    = _ansi(90)  if USE_COLOR else ""
    DCYAN   = _ansi(96)  if USE_COLOR else ""
    DRED    = _ansi("1;31") if USE_COLOR else ""
    DYELLOW = _ansi(93)  if USE_COLOR else ""

def cprint(color, msg, end="\n"):
    print(f"{color}{msg}{C.RESET}", end=end)

_ANSI_RE = re.compile(r'\x1b\[[0-9;]*m')

def _strip_ansi(s: str) -> str:
    """Remove ANSI colour escape sequences from a string."""
    return _ANSI_RE.sub("", s)

class ReportTee:
    """Context manager: tees sys.stdout to a plain-text file (ANSI stripped)."""
    _orig: TextIO
    _fh:   IO[str]

    def __init__(self, path: Path):
        self.path = path

    def __enter__(self):
        self._orig = sys.stdout
        self._fh   = open(self.path, "w", encoding="utf-8")
        sys.stdout = self
        return self

    def write(self, s: str):
        self._orig.write(s)
        self._fh.write(_strip_ansi(s))

    def flush(self):
        self._orig.flush()
        self._fh.flush()

    def isatty(self) -> bool:
        return self._orig.isatty()

    def __exit__(self, *_):
        sys.stdout = self._orig
        self._fh.close()

# =============================================================================
# SYSTEM MAP  --  local folder name -> libretro-thumbnails repo name
# =============================================================================
SYSTEM_MAP = {
    # ── Nintendo ──────────────────────────────────────────────────────────
    "nes":              "Nintendo_-_Nintendo_Entertainment_System",
    "fds":              "Nintendo_-_Family_Computer_Disk_System",
    "snes":             "Nintendo_-_Super_Nintendo_Entertainment_System",
    "virtualboy":       "Nintendo_-_Virtual_Boy",
    "n64":              "Nintendo_-_Nintendo_64",
    "gamecube":         "Nintendo_-_GameCube",
    "wii":              "Nintendo_-_Wii",
    "wiiu":             "Nintendo_-_Wii_U",
    "gb":               "Nintendo_-_Game_Boy",
    "gbc":              "Nintendo_-_Game_Boy_Color",
    "gba":              "Nintendo_-_Game_Boy_Advance",
    "ds":               "Nintendo_-_Nintendo_DS",
    "3ds":              "Nintendo_-_Nintendo_3DS",
    # ── Sega ──────────────────────────────────────────────────────────────
    "genesis":          "Sega_-_Mega_Drive_-_Genesis",
    "megadrive":        "Sega_-_Mega_Drive_-_Genesis",   # alias
    "32x":              "Sega_-_32X",
    "sega-cd":          "Sega_-_Mega-CD_-_Sega_CD",
    "game-gear":        "Sega_-_Game_Gear",
    "master-system":    "Sega_-_Master_System_-_Mark_III",
    "saturn":           "Sega_-_Saturn",
    "dc":               "Sega_-_Dreamcast",
    # ── Sony ──────────────────────────────────────────────────────────────
    "psx":              "Sony_-_PlayStation",
    "ps2":              "Sony_-_PlayStation_2",
    "ps3":              "Sony_-_PlayStation_3",
    "ps4":              "Sony_-_PlayStation_4",
    "psp":              "Sony_-_PlayStation_Portable",
    # ── Atari ─────────────────────────────────────────────────────────────
    "atari2600":        "Atari_-_2600",
    "atari5200":        "Atari_-_5200",
    "atari7800":        "Atari_-_7800",
    "atari-st":         "Atari_-_ST",
    "atarist":          "Atari_-_ST",                    # alias (no hyphen)
    "jaguar":           "Atari_-_Jaguar",
    "lynx":             "Atari_-_Lynx",
    # ── NEC ───────────────────────────────────────────────────────────────
    "pce":              "NEC_-_PC_Engine_-_TurboGrafx_16",
    "pcengine":         "NEC_-_PC_Engine_-_TurboGrafx_16",  # alias
    "pce-cd":           "NEC_-_PC_Engine_CD_-_TurboGrafx-CD",
    "pcecd":            "NEC_-_PC_Engine_CD_-_TurboGrafx-CD",  # alias
    # ── SNK ───────────────────────────────────────────────────────────────
    "neogeo":           "SNK_-_Neo_Geo",
    "neogeocd":         "SNK_-_Neo_Geo_CD",
    "ngp":              "SNK_-_Neo_Geo_Pocket",
    "ngpc":             "SNK_-_Neo_Geo_Pocket_Color",
    # ── Bandai ────────────────────────────────────────────────────────────
    "wonderswan":       "Bandai_-_WonderSwan",
    "wonderswancolor":  "Bandai_-_WonderSwan_Color",
    # ── Coleco / GCE / Microsoft / Sharp ──────────────────────────────────
    "coleco":           "Coleco_-_ColecoVision",
    "colecovision":     "Coleco_-_ColecoVision",         # alias
    "vectrex":          "GCE_-_Vectrex",
    "msx":              "Microsoft_-_MSX",
    "msx2":             "Microsoft_-_MSX2",
    "x68000":           "Sharp_-_X68000",
    # ── Multi-system ──────────────────────────────────────────────────────
    "scummvm":          "ScummVM",
}

# ---------------------------------------------------------------------------
# Folder-name resolver — three-tier lookup: folder name → libretro-thumbnails repo.
# Tier 1 — exact:   folder.lower() is a SYSTEM_MAP key (e.g. "snes", "n64").
# Tier 2 — alias:   normalized name matches FOLDER_ALIASES (handles long-form
#                   names, spaces/underscores/hyphens, ES/Batocera/Recalbox variants).
# Tier 3 — content: inspect files in the folder:
#   3a. Extension profiling: unambiguous extensions counted; ≥60% share wins.
#   3b. Header sniffing: read magic bytes from up to 5 ambiguous (.bin/.iso/…)
#       files; unanimous agreement required.
# Unresolved folders fall through to SGDB/LaunchBox only.
# ---------------------------------------------------------------------------

# Normalized variant → SYSTEM_MAP key (lowercase, non-alphanumeric collapsed to space).
FOLDER_ALIASES: dict[str, str] = {
    # NES / Famicom
    "nintendo entertainment system": "nes",
    "famicom":                        "nes",
    "fc":                             "nes",
    "famicom disk system":            "fds",
    # SNES
    "super nintendo":                        "snes",
    "super nintendo entertainment system":   "snes",
    "super famicom":                         "snes",
    "superfamicom":                          "snes",
    # N64
    "nintendo 64":   "n64",
    "nintendo64":    "n64",
    # GameCube / Wii / Wii U
    "gcn":                "gamecube",
    "gc":                 "gamecube",
    "nintendo gamecube":  "gamecube",
    "nintendo wii":       "wii",
    "wii u":              "wiiu",
    "nintendo wii u":     "wiiu",
    # Game Boy family
    "game boy":            "gb",
    "gameboy":             "gb",
    "game boy color":      "gbc",
    "gameboy color":       "gbc",
    "game boy advance":    "gba",
    "gameboy advance":     "gba",
    # DS / 3DS
    "nintendo ds":   "ds",
    "nds":           "ds",
    "nintendo 3ds":  "3ds",
    # Mega Drive / Genesis
    "sega genesis":     "genesis",
    "sega mega drive":  "megadrive",
    "mega drive":       "megadrive",
    # Sega misc
    "sega 32x":           "32x",
    "32 x":               "32x",
    "sega cd":            "sega-cd",
    "segacd":             "sega-cd",
    "mega cd":            "sega-cd",
    "megacd":             "sega-cd",
    "game gear":          "game-gear",
    "gamegear":           "game-gear",
    "sega game gear":     "game-gear",
    "master system":      "master-system",
    "mastersystem":       "master-system",
    "sega master system": "master-system",
    "mark iii":           "master-system",
    "sega saturn":        "saturn",
    "dreamcast":          "dc",
    "sega dreamcast":     "dc",
    # PlayStation
    "playstation":        "psx",
    "ps1":                "psx",
    "playstation 1":      "psx",
    "sony playstation":   "psx",
    "playstation 2":      "ps2",
    "sony playstation 2": "ps2",
    "playstation 3":      "ps3",
    "playstation portable": "psp",
    "sony psp":             "psp",
    # PC Engine / TurboGrafx
    "pc engine":      "pce",
    "turbografx":     "pce",
    "turbografx 16":  "pce",
    "turbografx16":   "pce",
    "pc engine cd":   "pce-cd",
    "turbografx cd":  "pce-cd",
    "turbo cd":       "pce-cd",
    # Neo Geo
    "neo geo":            "neogeo",
    "snk neo geo":        "neogeo",
    "neo geo cd":         "neogeocd",
    "neo geo pocket":     "ngp",
    "neo geo pocket color": "ngpc",
    # WonderSwan
    "wonder swan":        "wonderswan",
    "wonder swan color":  "wonderswancolor",
    # Atari
    "atari 2600":  "atari2600",
    "2600":        "atari2600",
    "atari 5200":  "atari5200",
    "5200":        "atari5200",
    "atari 7800":  "atari7800",
    "7800":        "atari7800",
    "atari st":    "atari-st",
    "atarist":     "atari-st",
    "atari jaguar": "jaguar",
    "atari lynx":   "lynx",
    # ColecoVision / Vectrex
    "colecovision":  "coleco",
    "coleco vision": "coleco",
    # MSX
    "microsoft msx":   "msx",
    "microsoft msx2":  "msx2",
    "msx 2":           "msx2",
    # ScummVM
    "scumm vm": "scummvm",
}

_FOLDER_NORM_RE = re.compile(r"[^a-z0-9]+")

def _norm_folder(name: str) -> str:
    """Lowercase and collapse non-alphanumeric runs to a single space."""
    return _FOLDER_NORM_RE.sub(" ", name.lower()).strip()

# Unambiguous extension → SYSTEM_MAP key. Ambiguous ones (.bin .iso etc.) handled by Tier 3b.
_EXT_TO_SYSTEM_KEY: dict[str, str] = {
    ".nes": "nes",      ".fds": "fds",
    ".sfc": "snes",     ".smc": "snes",
    ".vb":  "virtualboy",
    ".n64": "n64",      ".z64": "n64",      ".v64": "n64",
    ".gb":  "gb",       ".gbc": "gbc",      ".gba": "gba",
    ".nds": "ds",       ".3ds": "3ds",      ".cci": "3ds",
    ".gcz": "gamecube", ".rvz": "gamecube",
    ".wbfs": "wii",
    ".md":  "megadrive", ".smd": "megadrive", ".gen": "genesis",
    ".32x": "32x",
    ".gg":  "game-gear", ".sms": "master-system",
    ".cdi": "dc",       ".gdi": "dc",
    ".pbp": "psp",      ".cso": "psp",
    ".pce": "pce",
    ".ngp": "ngp",      ".ngc": "ngpc",
    ".ws":  "wonderswan", ".wsc": "wonderswancolor",
    ".a26": "atari2600", ".a52": "atari5200", ".a78": "atari7800",
    ".j64": "jaguar",   ".lnx": "lynx",
    ".col": "coleco",   ".vec": "vectrex",
}

_AMBIGUOUS_EXTS: frozenset[str] = frozenset({
    ".iso", ".bin", ".cue", ".img", ".chd", ".ecm", ".rom",
})

# ROM magic signatures: (byte_offset, magic_bytes, system_key).
# Order matters: longer/more-specific prefixes must precede shorter ones.
_ROM_MAGIC: tuple[tuple[int, bytes, str], ...] = (
    (0,   b"NES\x1a",             "nes"),       # iNES header
    (0,   b"\x80\x37\x12\x40", "n64"),       # N64 .z64 big-endian
    (0,   b"\x37\x80\x40\x12", "n64"),       # N64 .n64 little-endian
    (0,   b"\x40\x12\x37\x80", "n64"),       # N64 .v64 byte-swapped
    (16,  b"SEGADISCSYSTEM",       "sega-cd"),   # Sega CD — precedes generic SEGA
    (256, b"SEGA 32X",             "32x"),       # 32X — precedes generic SEGA
    (256, b"SEGA GENESIS",         "megadrive"),
    (256, b"SEGA MEGA DRIVE",      "megadrive"),
)
_ROM_MAGIC_READ_SIZE: int = max(o + len(m) for o, m, _ in _ROM_MAGIC) + 1

def _sniff_rom_header(path: Path) -> str | None:
    """Return the SYSTEM_MAP key for path based on ROM magic bytes, or None."""
    try:
        with open(path, "rb") as f:
            header = f.read(_ROM_MAGIC_READ_SIZE)
    except OSError:
        return None
    for offset, magic, key in _ROM_MAGIC:
        end = offset + len(magic)
        if len(header) >= end and header[offset:end] == magic:
            return key
    return None

def _profile_folder_contents(rom_dir: Path) -> tuple[str, str]:
    """Inspect files in rom_dir to infer the system. Returns (system_key, tier).
    Tier 3a: extension profiling — ≥60% share wins.
    Tier 3b: header sniffing — unanimous agreement across up to 5 files.
    """

    ext_votes: Counter = Counter()
    ambiguous_files: list[Path] = []

    for p in rom_dir.iterdir():
        if not p.is_file():
            continue
        ext = p.suffix.lower()
        if ext in _AMBIGUOUS_EXTS:
            ambiguous_files.append(p)
        else:
            key = _EXT_TO_SYSTEM_KEY.get(ext)
            if key:
                ext_votes[key] += 1

    # Tier 3a: extension plurality
    if ext_votes:
        top_key, top_count = ext_votes.most_common(1)[0]
        total = sum(ext_votes.values())
        if top_count / total >= 0.6:
            return top_key, "content-ext"

    # Tier 3b: header sniffing (only when no unambiguous extensions found)
    if not ext_votes and ambiguous_files:
        header_votes: Counter = Counter()
        for p in ambiguous_files[:5]:
            key = _sniff_rom_header(p)
            if key:
                header_votes[key] += 1
        if header_votes:
            top_key, top_count = header_votes.most_common(1)[0]
            total = sum(header_votes.values())
            if top_count == total:  # unanimous agreement only
                return top_key, "content-header"

    return "", ""

def _tier_msg(folder: str, repo_name: str, match_tier: str, kind: str = "covers") -> None:
    """Print a resolver info line for non-exact matches."""
    fallback = "SGDB/LaunchBox only" if kind == "covers" else "LaunchBox fanart only"
    if match_tier == "alias":
        cprint(C.GRAY, f"  [{folder}] → libretro repo '{repo_name}' (alias)")
    elif match_tier in ("content-ext", "content-header"):
        label = "extension profiling" if match_tier == "content-ext" else "header sniffing"
        cprint(C.GRAY, f"  [{folder}] → libretro repo '{repo_name}' (content: {label})")
    elif not repo_name:
        cprint(C.GRAY, f"  [{folder}] → unrecognised folder — {fallback}")

def resolve_system_folder(folder: str, rom_dir: Path | None = None) -> tuple[str, str]:
    """Map a ROM folder name to (repo_name, tier).
    repo_name: libretro-thumbnails repo slug, or "" if unresolved.
    tier:      "exact" | "alias" | "content-ext" | "content-header" | ""
    """
    # Tier 1: exact SYSTEM_MAP key
    key = folder.lower()
    if key in SYSTEM_MAP:
        return SYSTEM_MAP[key], "exact"

    # Tier 2: normalize separators and check alias table
    alias_key = FOLDER_ALIASES.get(_norm_folder(folder))
    if alias_key:
        return SYSTEM_MAP[alias_key], "alias"

    # Tier 3: content-based identification
    if rom_dir and rom_dir.is_dir():
        content_key, content_tier = _profile_folder_contents(rom_dir)
        if content_key and content_key in SYSTEM_MAP:
            return SYSTEM_MAP[content_key], content_tier

    return "", ""

BASE_RAW_URL = "https://raw.githubusercontent.com/libretro-thumbnails"
BASE_API_URL = "https://api.github.com/repos/libretro-thumbnails"

SGDB_API_BASE = "https://www.steamgriddb.com/api/v2"

# LaunchBox GamesDB — public Metadata.zip, updated daily, no API key required
LBDB_METADATA_URL = "https://gamesdb.launchbox-app.com/Metadata.zip"
LBDB_IMG_BASE      = "https://images.launchbox-app.com/"

# Valid background dimensions; anything else is letterboxed to 1920x1080
VALID_BG_DIMS = {"1920x1080", "1280x720"}

# =============================================================================
# REGION PREFERENCE
# =============================================================================
# Canonical region key → substrings found in libretro-thumbnails filenames.
REGION_KEYWORDS: dict[str, set[str]] = {
    "usa":    {"usa", "north america"},
    "europe": {"europe", "germany", "france", "spain", "italy",
               "sweden", "netherlands", "australia", "uk",
               "united kingdom", "scandinavia"},
    "japan":  {"japan", "jpn"},
    "world":  {"world"},
}

# Human-readable label for display
REGION_LABELS: dict[str, str] = {
    "usa":    "USA / North America",
    "europe": "Europe",
    "japan":  "Japan",
    "world":  "World",
    "any":    "No preference",
}

_COVER_STYLE_LABELS: dict[str, str] = {
    "with_logo":    "with logo",
    "without_logo": "without logo (SGDB)",
    "game_logo":    "game logo",
}

_BG_STYLE_LABELS: dict[str, str] = {
    "fanart": "fanart/heroes",
    "boxart": "box art (letterboxed)",
}

_REGION_TAG_RE = re.compile(r'\(([^)]+)\)')

def region_of(name: str) -> str | None:
    """Return the canonical region key for a repo filename, or None.
    First listed region in multi-value tags wins: "(Japan, USA)" → "japan".
    """
    for m in _REGION_TAG_RE.finditer(name):
        for part in m.group(1).split(','):
            part = part.strip().lower()
            for key, keywords in REGION_KEYWORDS.items():
                if any(part == kw for kw in keywords):
                    return key
    return None

def sort_by_region(candidates: list[tuple[str, float]],
                   preferred: str) -> list[tuple[str, float]]:
    """Re-sort ranked_matches output to prefer a region.
    Score bonuses: preferred +0.10, world +0.05, other 0.
    The 0.10 bonus exceeds the smallest tier gap (0.02), so a preferred-region
    candidate at 0.88 beats a non-preferred one at 0.90 — intentional.
    """
    if not preferred or preferred == "any":
        return candidates

    def sort_key(item: tuple[str, float]) -> float:
        name, score = item
        r = region_of(name)
        if r == preferred:  bonus = 0.10
        elif r == "world":  bonus = 0.05
        else:               bonus = 0.00
        return -(score + bonus)   # negative → descending

    return sorted(candidates, key=sort_key)

# =============================================================================
# FUZZY MATCHING
# =============================================================================
_TAG_RE          = re.compile(r"\s*[\(\[].*?[\)\]]")
_SEQNUM_RE       = re.compile(r"_\d+$")        # strip trailing _1, _2 …
_WORD_RE         = re.compile(r"\W+")           # word tokenizer for Jaccard
_WS_RE           = re.compile(r"\s+")
_SUBTITLE_SEP_RE = re.compile(r"\s+-\s+")      # "Title - Subtitle" → "Title Subtitle"
_NONALNUM_RE     = re.compile(r"[^a-z0-9]")    # compact key for dedup grouping

def strip_tags(name: str) -> str:
    """Remove parenthesized/bracketed tags (region, revision, etc.) and collapse whitespace."""
    return _WS_RE.sub(" ", _TAG_RE.sub("", name)).strip()

def normalize(name: str) -> str:
    """Strip region/revision tags and trailing sequence numbers (_1, _2…) for cover matching."""
    return _SEQNUM_RE.sub("", strip_tags(name)).strip()

_ARTICLE_TRAIL_RE = re.compile(r',\s*(?:the|a|an)$', re.IGNORECASE)
_ARTICLE_LEAD_RE  = re.compile(r'^(?:the|a|an)\s+',  re.IGNORECASE)

def _norm_for_dedup(stem: str) -> str:
    """Normalize a ROM stem for same-title grouping in duplicate detection.
    Like normalize() but also strips leading/trailing articles so
    'The Legend of Zelda' and 'Legend of Zelda, The' map to the same key.
    """
    s = strip_tags(stem)
    s = _SEQNUM_RE.sub("", s)
    s = _SUBTITLE_SEP_RE.sub(" ", s)
    s = _ARTICLE_TRAIL_RE.sub("", s)
    s = _ARTICLE_LEAD_RE.sub("", s)
    return s.strip().lower()

def _similarity_prenorm(a_low: str, a_norm: str, b_low: str, b_norm: str) -> float:
    """Similarity score on pre-lowercased, pre-normalized strings."""
    if a_low == b_low:                              return 1.00  # exact match
    if a_norm and a_norm == b_norm:                 return 0.95  # equal after tag/seq strip
    if b_low  and a_low.startswith(b_low):          return 0.90  # raw prefix
    if b_norm and a_norm.startswith(b_norm):        return 0.88  # normalized prefix

    shorter = a_norm if len(a_norm) <= len(b_norm) else b_norm
    longer  = b_norm if len(a_norm) <= len(b_norm) else a_norm
    containment_ok = len(shorter) >= 6 and len(shorter) >= len(longer) * 0.4
    if containment_ok:
        if b_low  in a_low  or a_low  in b_low:    return 0.85  # raw substring
        if b_norm in a_norm or a_norm in b_norm:    return 0.80  # normalized substring

    words_a = {w for w in _WORD_RE.split(a_norm) if len(w) > 1}
    words_b = {w for w in _WORD_RE.split(b_norm) if len(w) > 1}
    if not words_a or not words_b:                  return 0.0
    common = len(words_a & words_b)
    if common < 2:                                  return 0.0  # require ≥2 shared words
    union = len(words_a | words_b)
    return round(common / union, 4) if union else 0.0           # Jaccard index

def similarity(a: str, b: str) -> float:
    """Similarity score between two ROM/cover names (0.0–1.0)."""
    return _similarity_prenorm(
        a.lower().strip(), normalize(a).lower(),
        b.lower().strip(), normalize(b).lower()
    )

PNG_SIGNATURE  = b'\x89PNG\r\n\x1a\n'
WEBP_SIGNATURE = b'WEBP'  # bytes 8-11 (after RIFF + 4-byte size)

def is_valid_png(data: bytes) -> bool:
    """Check PNG magic bytes."""
    return data[:8] == PNG_SIGNATURE

def is_webp(data: bytes) -> bool:
    """Check WebP magic bytes (RIFF....WEBP)."""
    return len(data) >= 12 and data[8:12] == WEBP_SIGNATURE

def build_normalized_candidates(candidates: list[str]) -> list[tuple[str, str]]:
    """Pre-compute normalized form of every repo filename. Call once per system."""
    return [(c, normalize(c).lower()) for c in candidates]

def ranked_matches(rom: str, candidates: list[str],
                   threshold: float, top_n: int = 5,
                   _norm_cache: list[tuple[str, str]] | None = None) -> list[tuple[str, float]]:
    """Return up to top_n candidates above threshold, sorted best-first.
    Pass _norm_cache=build_normalized_candidates(candidates) to avoid re-normalizing on every call.
    """
    rom_low  = rom.lower().strip()
    rom_norm = normalize(rom).lower()

    results = []
    norm_pairs = _norm_cache if _norm_cache is not None else [(c, normalize(c).lower()) for c in candidates]

    for orig, c_norm in norm_pairs:
        c_low = orig.lower().strip()
        score = _similarity_prenorm(c_low, c_norm, rom_low, rom_norm)
        if score >= threshold:
            results.append((orig, score))
            if score == 1.0:
                break  # exact match — no better score possible

    return sorted(results, key=lambda x: x[1], reverse=True)[:top_n]

# =============================================================================
# IMAGEMAGICK
# =============================================================================
def find_magick() -> str | None:
    """Return 'magick' (v7) or 'convert' (v6) if a working ImageMagick binary is found.
    Runs '<cmd> -version' to verify the binary is functional, not just on PATH.
    """
    for cmd in ("magick", "convert"):
        if not shutil.which(cmd):
            continue
        try:
            result = subprocess.run(
                [cmd, "-version"],
                capture_output=True, timeout=5
            )
            if result.returncode == 0:
                return cmd
        except Exception:
            pass  # binary exists but is non-functional — try next
    return None

def magick_resize(magick: str, src: str, dst: str,
                  dims: str = "512x512", gravity: str = "center") -> None:
    """Letterbox-resize src → dst. gravity: 'center' (covers/fanart) or 'East' (boxart BGs)."""
    subprocess.run(
        [magick, src, "-resize", dims, "-gravity", gravity,
         "-background", "black", "-extent", dims, dst],
        check=True, capture_output=True
    )

def batch_identify(magick: str, jpg_list: list[Path],
                   chunk_size: int = 200,
                   label: str = "Identifying") -> dict[Path, str | None]:
    """Return {path: 'WxH' | None} for every jpg. Chunked to stay within Windows CLI limit."""
    dims_map: dict[Path, str | None] = {p: None for p in jpg_list}
    total = len(jpg_list)
    done  = 0
    for i in range(0, total, chunk_size):
        chunk = jpg_list[i : i + chunk_size]
        result = subprocess.run(
            [magick, "identify", "-format", "%i %wx%h\n"] + [str(p) for p in chunk],
            capture_output=True, text=True
        )
        if result.returncode == 0:
            for line in result.stdout.splitlines():
                parts = line.rsplit(" ", 1)
                if len(parts) == 2:
                    dims_map[Path(parts[0])] = parts[1].strip()  # Path() normalizes separators
        done = min(i + chunk_size, total)
        print(progress_bar(done, total, label=label), end="", flush=True)
    if total:
        print()  # newline after progress bar
    return dims_map

# =============================================================================
# STEAMGRIDDB  (API docs / free key: steamgriddb.com/api/v2)
# =============================================================================
def _sgdb_get_json(url: str, key: str, context: str = "") -> dict | None:
    """Fetch a SGDB JSON endpoint. Returns parsed dict or None on any error."""
    try:
        raw  = _http_get(url, key, bearer=True)
        return json.loads(raw)
    except urllib.error.HTTPError as e:
        if e.code == 401:
            cprint(C.DRED, "  SGDB: invalid API key (HTTP 401) — "
                           "get a free key at steamgriddb.com/profile/preferences")
        elif e.code == 429:
            cprint(C.YELLOW, f"  SGDB rate limited (HTTP 429){f' — {context}' if context else ''} skipped.")
        else:
            cprint(C.YELLOW, f"  SGDB HTTP {e.code}{f' ({context})' if context else ''}: {e.reason}")
    except Exception as e:
        cprint(C.GRAY, f"  SGDB unexpected error{f' ({context})' if context else ''}: {e}")
    return None

def sgdb_search_game(name: str, key: str) -> int | None:
    """Return the first SteamGridDB game_id matching name, or None."""
    term = normalize(name).strip() or name.strip()
    url  = f"{SGDB_API_BASE}/search/autocomplete/{urllib.parse.quote(term)}"
    data = _sgdb_get_json(url, key, context=f"search {name!r}")
    if data and data.get("success") and data.get("data"):
        return int(data["data"][0]["id"])
    return None

def sgdb_get_cover_url(game_id: int, key: str) -> str | None:
    """Return the URL of the highest-voted vertical grid for game_id, or None."""
    url = (f"{SGDB_API_BASE}/grids/game/{game_id}"
           f"?dimensions=600x900,342x482"
           f"&types=static&nsfw=false&humor=false&epilepsy=false")
    data = _sgdb_get_json(url, key, context=f"grids game_id={game_id}")
    if data and data.get("success") and data.get("data"):
        return data["data"][0]["url"]
    return None

def sgdb_get_hero_url(game_id: int, key: str) -> str | None:
    """Return the best SGDB hero URL for game_id, or None.
    No ?dimensions= filter — SGDB hero dims differ from cover dims and trigger HTTP 400.
    """
    url = (f"{SGDB_API_BASE}/heroes/game/{game_id}"
           f"?types=static&nsfw=false&humor=false&epilepsy=false")
    data = _sgdb_get_json(url, key, context=f"heroes game_id={game_id}")
    if data and data.get("success") and data.get("data"):
        return data["data"][0]["url"]
    return None

# =============================================================================
# LAUNCHBOX GAMESDB — offline XML database (Metadata.zip, updated daily)
# Cached as JSON; image URL: https://images.launchbox-app.com/{FileName}
# =============================================================================

# LB Region field values → our canonical region keys
_LBDB_REGION_MAP: dict[str, str] = {
    "north america":  "usa",
    "united states":  "usa",
    "usa":            "usa",
    "europe":         "europe",
    "germany":        "europe",
    "france":         "europe",
    "spain":          "europe",
    "italy":          "europe",
    "united kingdom": "europe",
    "australia":      "europe",
    "world":          "world",
    "japan":          "japan",
}

_LBDB_TYPE_COVER = "Box - Front"
_LBDB_TYPE_BG    = "Fanart - Background"
_LBDB_TYPE_LOGO       = "Clear Logo"
_LBDB_TYPE_SCREENSHOT = "Screenshot - Game Title"
_LBDB_REGION_PRIORITY: list[str] = ["world", "usa", "europe", "japan"]

LbIndex = dict  # normalized_name -> {img_type -> [(region_key, filename)]}

def _lbdb_region_rank(preferred: str) -> dict[str, int]:
    """Return {region_key: sort_rank} with preferred first."""
    order = [preferred] + [r for r in _LBDB_REGION_PRIORITY if r != preferred]
    return {r: i for i, r in enumerate(order)}

_LBDB_INDEXED_TYPES: frozenset[str] = frozenset((
    _LBDB_TYPE_COVER, _LBDB_TYPE_BG, _LBDB_TYPE_LOGO, _LBDB_TYPE_SCREENSHOT,
))

def _lbdb_parse_zip(zip_bytes: bytes) -> LbIndex:
    """Parse Metadata.zip into { normalized_name: { img_type: [(region_key, filename)] } }.
    Streams with ET.iterparse; elem.clear() bounds memory.
    """
    index: dict = {}
    with zipfile.ZipFile(io.BytesIO(zip_bytes)) as zf:
        xml_names = [n for n in zf.namelist() if n.endswith(".xml")]
        for xml_name in xml_names:
            db_id_to_norm: dict[str, str] = {}
            try:
                for _event, elem in ET.iterparse(zf.open(xml_name), events=("end",)):
                    tag = elem.tag
                    if tag == "Game":
                        db_id = (elem.findtext("DatabaseID") or "").strip()
                        name  = (elem.findtext("Name") or "").strip()
                        if db_id and name:
                            norm = normalize(strip_tags(name)).lower().strip()
                            if norm:
                                db_id_to_norm[db_id] = norm
                        elem.clear()

                    elif tag == "GameImage":
                        db_id    = (elem.findtext("DatabaseID") or "").strip()
                        filename = (elem.findtext("FileName") or "").strip()
                        img_type = (elem.findtext("Type") or "").strip()
                        region   = (elem.findtext("Region") or "").strip().lower()
                        if db_id and filename and img_type in _LBDB_INDEXED_TYPES:
                            norm = db_id_to_norm.get(db_id)
                            if norm:
                                region_key = _LBDB_REGION_MAP.get(region, "")
                                index.setdefault(norm, {}).setdefault(img_type, []).append(
                                    (region_key, filename)
                                )
                        elem.clear()

            except Exception:
                # Malformed XML in one file — skip it, keep whatever was indexed
                continue
    return index

def sgdb_get_logo_url(game_id: int, key: str) -> str | None:
    """Return the best SteamGridDB logo URL for game_id, or None.
    """
    url = (f"{SGDB_API_BASE}/logos/game/{game_id}"
           f"?types=static&nsfw=false&humor=false&epilepsy=false")
    data = _sgdb_get_json(url, key, context=f"logos game_id={game_id}")
    if data and data.get("success") and data.get("data"):
        return data["data"][0]["url"]
    return None

def lbdb_load_index(
    ttl_hours: int,
    script_stem: str,
    timeout: int = 90,
) -> LbIndex:
    """Download + cache LaunchBox Metadata.zip; return in-memory index.
    Returns {} on any failure so callers degrade gracefully.
    """
    cache_dir = Path(tempfile.gettempdir()) / "rom-assets-manager"
    cache_dir.mkdir(exist_ok=True)
    cache_path = cache_dir / f"{script_stem}_launchbox.json"

    if cache_path.exists():
        try:
            data    = json.loads(cache_path.read_text(encoding="utf-8"))
            fetched = datetime.fromisoformat(data["fetched"])
            if fetched.tzinfo is None:
                fetched = fetched.replace(tzinfo=timezone.utc)
            age_h = (datetime.now(timezone.utc) - fetched).total_seconds() / 3600
            if age_h < ttl_hours:
                index = {
                    name: {t: [tuple(e) for e in es]
                           for t, es in types.items()}
                    for name, types in data["index"].items()
                }
                cprint(C.GRAY,
                       f"  LaunchBox DB: cache hit ({age_h:.1f}h old, "
                       f"TTL {ttl_hours}h, {len(index):,} games)")
                return index
            cprint(C.GRAY, "  LaunchBox DB: cache expired — refreshing...")
        except Exception:
            cprint(C.GRAY, "  LaunchBox DB: cache unreadable — re-downloading...")

    cprint(C.GRAY, "  Downloading LaunchBox Metadata.zip (~150 MB, please wait)...")
    try:
        zip_bytes = _http_get(LBDB_METADATA_URL, None, timeout=timeout)
    except Exception as e:
        cprint(C.YELLOW, f"  WARNING: Could not download LaunchBox DB: {e}")
        return {}

    cprint(C.GRAY, "  Parsing LaunchBox XML...")
    try:
        index = _lbdb_parse_zip(zip_bytes)
    except Exception as e:
        cprint(C.YELLOW, f"  WARNING: Could not parse LaunchBox DB: {e}")
        return {}

    cprint(C.GRAY, f"  LaunchBox DB loaded: {len(index):,} games")

    try:
        payload = {"fetched": datetime.now(timezone.utc).isoformat(), "index": index}
        tmp = cache_path.with_suffix(".tmp")
        tmp.write_text(json.dumps(payload, ensure_ascii=False), encoding="utf-8")
        tmp.replace(cache_path)
        cprint(C.GRAY, f"  LaunchBox DB cached → {cache_path.name}")
    except Exception as e:
        cprint(C.YELLOW, f"  WARNING: Could not write LaunchBox DB cache: {e}")

    return index

def lbdb_find_url(
    rom_stem: str,
    lb_index: LbIndex,
    img_type: str,
    preferred_region: str,
    threshold: float = 0.70,
) -> str | None:
    """Offline LaunchBox lookup: exact match → 4-char prefix fuzzy → region sort."""
    if not lb_index:
        return None
    norm = normalize(strip_tags(rom_stem)).lower().strip()
    if not norm:
        return None

    entries_by_type = lb_index.get(norm)

    if entries_by_type is None:
        prefix     = norm[:4]
        candidates = [k for k in lb_index if k[:4] == prefix] or list(lb_index.keys())
        hits       = ranked_matches(norm, candidates, threshold)
        for hit_name, _score in hits:
            if img_type in lb_index[hit_name]:
                entries_by_type = lb_index[hit_name]
                break

    if entries_by_type is None or img_type not in entries_by_type:
        return None

    entries = entries_by_type[img_type]
    if not entries:
        return None

    rank = _lbdb_region_rank(preferred_region)
    best = min(entries, key=lambda e: rank.get(e[0], len(rank)))
    return f"{LBDB_IMG_BASE}{best[1]}"

def lbdb_find_cover_url(rom_stem: str, lb_index: LbIndex,
                        preferred_region: str = "any") -> str | None:
    """Return the best LaunchBox Box-Front URL for rom_stem, or None."""
    return lbdb_find_url(rom_stem, lb_index, _LBDB_TYPE_COVER, preferred_region)

def lbdb_find_logo_url(rom_stem: str, lb_index: LbIndex,
                       preferred_region: str = "any") -> str | None:
    """Return the best LaunchBox Clear Logo URL for rom_stem, or None."""
    return lbdb_find_url(rom_stem, lb_index, _LBDB_TYPE_LOGO, preferred_region)

def lbdb_find_screenshot_url(rom_stem: str, lb_index: LbIndex,
                              preferred_region: str = "any") -> str | None:
    """Return the best LaunchBox Screenshot-Game-Title URL for rom_stem, or None."""
    return lbdb_find_url(rom_stem, lb_index, _LBDB_TYPE_SCREENSHOT, preferred_region)

def lbdb_find_bg_url(rom_stem: str, lb_index: LbIndex,
                     preferred_region: str = "any") -> str | None:
    """Return the best LaunchBox Fanart-Background URL for rom_stem, or None."""
    return lbdb_find_url(rom_stem, lb_index, _LBDB_TYPE_BG, preferred_region)

# =============================================================================
# GITHUB API + DISK CACHE
# =============================================================================
def _http_get(url: str, token: str | None, bearer: bool = False,
              timeout: int = 30, max_retries: int = 3) -> bytes:
    """Fetch URL with optional auth and retry (429/5xx/network errors). Raises on 4xx."""
    req = urllib.request.Request(url, headers={"User-Agent": "rom-assets-manager-py"})
    if token:
        req.add_header("Authorization", f"{'Bearer' if bearer else 'token'} {token}")
    last_exc: Exception | None = None
    for attempt in range(max_retries):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read()
        except urllib.error.HTTPError as e:
            if e.code == 429:
                wait = int(e.headers.get("Retry-After") or 2 ** attempt)
                cprint(C.YELLOW, f"  Rate limited (HTTP 429), waiting {wait}s...")
                time.sleep(wait)
                last_exc = e
            elif 500 <= e.code < 600:
                last_exc = e
                time.sleep(2 ** attempt)
            else:
                raise  # 4xx client errors: no point retrying
        except (urllib.error.URLError, OSError) as e:
            # Network-level errors (timeout, connection refused, DNS) → retry
            last_exc = e
            time.sleep(2 ** attempt)
    raise last_exc  # type: ignore[misc]  # exhausted all retries

def get_repo_file_list(repo: str, token: str | None,
                       ttl_hours: int, script_stem: str,
                       folder_name: str = "Named_Boxarts") -> list[str]:
    """Fetch the file list for folder_name in a libretro-thumbnails repo (cached)."""
    folder_tag = "logos" if folder_name == "Named_Logos" else "boxarts"
    cache_dir = Path(tempfile.gettempdir()) / "rom-assets-manager"
    cache_dir.mkdir(exist_ok=True)
    cache_path = cache_dir / f"{script_stem}_{repo}_{folder_tag}.json"

    if cache_path.exists():
        try:
            data = json.loads(cache_path.read_text(encoding="utf-8"))
            fetched = datetime.fromisoformat(data["fetched"])
            # Make both offset-aware for comparison
            if fetched.tzinfo is None:
                fetched = fetched.replace(tzinfo=timezone.utc)
            age_h = (datetime.now(timezone.utc) - fetched).total_seconds() / 3600
            if age_h < ttl_hours:
                cprint(C.GRAY, f"  Cache hit: {repo} ({age_h:.1f}h old, TTL {ttl_hours}h)")
                return data["files"]
            cprint(C.GRAY, f"  Cache expired for {repo} — refreshing from API")
        except Exception:
            cprint(C.GRAY, f"  Cache unreadable for {repo} — re-fetching")

    cprint(C.GRAY, f"  Fetching file list from GitHub API: {repo} ...")
    url = f"{BASE_API_URL}/{repo}/git/trees/master?recursive=1"
    try:
        raw    = _http_get(url, token)
        parsed = json.loads(raw)
    except urllib.error.HTTPError as e:
        if e.code in (403, 429):
            cprint(C.YELLOW, f"  WARNING: GitHub rate limit hit for {repo} "
                             f"(HTTP {e.code}). "
                             f"Set GITHUB_TOKEN to raise limit (5000 vs 60 req/h).")
        else:
            cprint(C.YELLOW, f"  WARNING: GitHub API HTTP {e.code} for {repo}: {e.reason}")
        return []
    except Exception as e:
        cprint(C.YELLOW, f"  WARNING: Could not fetch file list for {repo}: {e}")
        return []
    if parsed.get("truncated"):
        cprint(C.YELLOW, f"  WARNING: GitHub API returned a truncated tree for {repo} -- some {folder_tag} may be missing")
    names = [
        Path(item["path"]).stem
        for item in parsed["tree"]
        if item["path"].startswith(f"{folder_name}/") and item["path"].endswith(".png")
    ]
    try:
        payload   = {"fetched": datetime.now(timezone.utc).isoformat(), "files": names}
        tmp_cache = cache_path.with_suffix(".tmp")
        tmp_cache.write_text(json.dumps(payload), encoding="utf-8")
        tmp_cache.replace(cache_path)
        cprint(C.GRAY, f"  Found {len(names)} {folder_tag} -- cached to {cache_path.name}")
    except Exception as e:
        cprint(C.YELLOW, f"  WARNING: Could not write cache for {repo}: {e} (continuing without cache)")
        cprint(C.GRAY,   f"  Found {len(names)} {folder_tag} (not cached)")
    return names

# =============================================================================
# HELPERS
# =============================================================================
def _ensure_art_dir(path: Path, label: str, dry_run: bool) -> None:
    """Create art directory if absent; in dry-run just log what would happen."""
    if path.exists():
        return
    if not dry_run:
        path.mkdir(parents=True, exist_ok=True)
        cprint(C.CYAN, f"  Created {label} folder: {path}")
    else:
        cprint(C.MAGENTA, f"  [DRY RUN] Would create {label} folder: {path}")

def _scan_roms(roms_path: Path) -> dict[str, Path]:
    """Scan roms_path recursively; return {stem: path}. Skips .sbi; warns on duplicate stems."""
    result: dict[str, Path] = {}
    for p in roms_path.rglob("*.*"):   # *.*  skips bare directories efficiently
        if not p.is_file() or p.suffix.lower() == ".sbi":
            continue
        if p.stem in result:
            cprint(C.YELLOW,
                   f"  WARNING: duplicate ROM stem '{p.stem}' "
                   f"(keeping {result[p.stem].relative_to(roms_path)}, "
                   f"ignoring {p.relative_to(roms_path)})")
        else:
            result[p.stem] = p
    return result

# =============================================================================
# PROMPTS
# =============================================================================
def prompt_path(label: str, initial: str = "", must_exist: bool = True) -> str:
    """Prompt until a non-empty path is entered. Validates existence when must_exist=True."""
    value = initial
    while not value or (must_exist and not Path(value).exists()):
        if value and must_exist and not Path(value).exists():
            cprint(C.RED, f"  Path not found: '{value}'")
        try:
            value = input(f"  Enter {label} path: ").strip().strip('"')
        except KeyboardInterrupt:
            print()
            raise
    return value

def prompt_choice(question: str, options: dict[str, str]) -> str:
    """options = {'1': 'label', ...}  Returns the chosen key."""
    print(question)
    for k, v in options.items():
        print(f"    [{k}] {v}")
    print()
    choice = None
    while choice not in options:
        if choice:
            cprint(C.RED, f"  Invalid choice: {choice!r} — please enter one of: {list(options)}")
        try:
            choice = input(f"  Enter choice [{'/'  .join(options)}]: ").strip()
        except KeyboardInterrupt:
            print()
            raise
    return choice

def prompt_system() -> str:
    known = ", ".join(sorted(SYSTEM_MAP))
    cprint(C.GRAY, f"  Known systems: {known}")
    print()
    system = ""
    while not system or system not in SYSTEM_MAP:
        if system:
            cprint(C.RED, f"  '{system}' not found in system map.")
        try:
            system = input("  Enter system name (e.g. snes, psx, gba): ").strip().lower()
        except KeyboardInterrupt:
            print()
            raise
    return system

# =============================================================================
# THREAD-SAFE COUNTERS
# =============================================================================
class Counters:
    __slots__ = ('_lock', 'renamed', 'deleted', 'missing',
                 'downloaded', 'skipped', 'converted', 'duplicates')

    def __init__(self):
        self._lock      = threading.Lock()
        self.renamed    = 0
        self.deleted    = 0
        self.missing    = 0
        self.downloaded = 0
        self.skipped    = 0
        self.converted  = 0
        self.duplicates = 0

    def inc(self, field: str, n: int = 1):
        with self._lock:
            setattr(self, field, getattr(self, field) + n)

# =============================================================================
# SYNC CONFIGURATION
# =============================================================================
@dataclasses.dataclass(frozen=True)
class SyncConfig:
    """Immutable per-run settings passed to all folder processors."""
    dry_run:          bool
    delete_orphans:   bool
    download_mode:    str
    threshold:        float
    magick:           str | None
    parallel_jobs:    int
    github_token:     str | None
    preferred_region: str
    cover_style:      str          # "with_logo" | "without_logo" | "game_logo"
    bg_style:         str          # "fanart" | "boxart"
    sgdb_key:         str | None
    http_timeout:     int

# =============================================================================
# MATCH RESULTS
# =============================================================================
@dataclasses.dataclass
class LibretroMatch:
    """A ROM with ≥1 candidate in the libretro-thumbnails repo."""
    rom_stem:   str
    jpg_path:   Path
    candidates: list[tuple[str, float]]   # (repo_filename, score), best-first

@dataclasses.dataclass
class LibretroNoMatch:
    """A ROM with no usable candidate in the libretro-thumbnails repo."""
    rom_stem: str
    hint:     str   # "best='x' score=0.23" | "no files in repo"

# =============================================================================
# PROGRESS BAR
# =============================================================================
def progress_bar(done: int, total: int, width: int = 40, label: str = "") -> str:
    filled = int(width * done / total) if total else width
    bar    = "█" * filled + "░" * (width - filled)
    pct    = int(100 * done / total) if total else 100
    return f"\r  {label}[{bar}] {done}/{total} ({pct}%)"

# =============================================================================
# COVER / BACKGROUND PIPELINE HELPERS
# =============================================================================

class _ProgressTracker:
    """Thread-safe (done, total) counter shared across download workers."""
    __slots__ = ("_lock", "total", "label", "_done")

    def __init__(self, total: int, label: str = "") -> None:
        self._lock = threading.Lock()
        self._done = 0
        self.total = total
        self.label = label

    def tick(self, n: int = 1) -> tuple[int, int]:
        """Increment done by n; return (done, total)."""
        with self._lock:
            self._done += n
            return self._done, self.total

def _run_thread_pool(
    parallel_jobs: int,
    items: "list",
    worker: "Callable",
    *,
    max_workers: int | None = None,
    interrupt_msg: str = "  Interrupted — cancelling...",
) -> None:
    """Run worker(item) for each item in a thread pool. Cancels on KeyboardInterrupt."""
    n_workers = min(parallel_jobs, max_workers) if max_workers else parallel_jobs
    with ThreadPoolExecutor(max_workers=n_workers) as pool:
        futures = [pool.submit(worker, item) for item in items]
        try:
            for fut in as_completed(futures):
                fut.result()
        except KeyboardInterrupt:
            cprint(C.YELLOW, f"\n{interrupt_msg}")
            pool.shutdown(wait=False, cancel_futures=True)
            raise

def _progress_ok(
    tracker: "_ProgressTracker",
    lock: "threading.Lock",
    msg: str,
    color: str = "",
) -> None:
    """Tick tracker, redraw progress bar, then print msg.  Thread-safe."""
    color = color or C.GREEN
    dd, dt = tracker.tick()
    with lock:
        print(progress_bar(dd, dt, label=tracker.label), end="", flush=True)
        cprint(color, msg)

def _reconcile_art_files(
    existing: dict[str, Path],
    roms: dict[str, Path],
    folder_path: Path,
    cfg: SyncConfig,
    counters: Counters,
    orphans: list[str],
    kind: str = "cover",
    dims: str = "512x512",
    gravity: str = "center",
) -> bool:
    """Fuzzy-rename art files to match ROM stems. Returns True if any rename occurred."""
    mismatched = [s for s in existing if s not in roms]
    did_rename  = False

    for stem in mismatched:
        path    = existing[stem]
        matches = ranked_matches(stem, list(roms.keys()), cfg.threshold, top_n=1)
        name, score = matches[0] if matches else (None, 0.0)

        if name and score >= cfg.threshold:
            new_name = name + path.suffix
            new_path = folder_path / new_name
            if not cfg.dry_run:
                if not new_path.exists():
                    print(f"  {C.YELLOW}RENAME{C.RESET}  '{stem}'{path.suffix}"
                          f"  ->  '{new_name}'  (score: {score:.2f})")
                    shutil.move(str(path), str(new_path))  # shutil.move handles cross-filesystem moves
                    if cfg.magick:
                        try:
                            magick_resize(cfg.magick, str(new_path), str(new_path),
                                          dims=dims, gravity=gravity)
                        except Exception:
                            pass  # resize failure is non-fatal; _resize_pass will catch it
                    existing.pop(stem)
                    existing[name] = new_path
                    counters.inc("renamed")
                    did_rename = True
                else:
                    if cfg.delete_orphans:
                        print(f"  {C.DRED}DUPLICATE{C.RESET}  '{stem}'{path.suffix}"
                              f"  (same game as '{new_name}' already present — will delete)")
                        orphans.append(str(path))
                    else:
                        cprint(C.DYELLOW,
                               f"  DUPLICATE {kind.upper()}  '{stem}'{path.suffix}"
                               f" → '{new_name}' already exists"
                               f" -- run --delete-orphans to remove")
                    counters.inc("duplicates")
            else:  # dry run
                if new_path.exists():
                    del_hint = (" (would delete)" if cfg.delete_orphans
                                else " (run --delete-orphans to remove)")
                    cprint(C.DYELLOW,
                           f"  [DRY RUN] DUPLICATE {kind.upper()}  '{stem}'{path.suffix}"
                           f" → '{new_name}' already exists{del_hint}")
                    counters.inc("duplicates")
                else:
                    print(f"  {C.MAGENTA}[DRY RUN]{C.RESET} {C.YELLOW}RENAME{C.RESET}"
                          f"  '{stem}'{path.suffix}"
                          f"  ->  '{new_name}'  (score: {score:.2f})")
                    counters.inc("renamed")
        else:
            score_info = (f"closest: '{name}' score={score:.2f}" if name
                          else "no ROM candidate")
            if cfg.delete_orphans:
                prefix = f"{C.MAGENTA}  [DRY RUN] {C.RESET}" if cfg.dry_run else "  "
                print(f"{prefix}{C.DRED}DELETE{C.RESET}  "
                      f"'{stem}'{path.suffix}  [{score_info}]")
                orphans.append(str(path))
            else:
                cprint(C.RED, f"  NO MATCH  '{stem}' -- {score_info}")
            counters.inc("missing")

    return did_rename

def _write_and_convert(
    raw: bytes,
    work_dir: Path,
    stem: str,
    jpg_path: Path,
    magick: str,
    counters: Counters,
    dims: str = "512x512",
    gravity: str = "center",
) -> None:
    """Write raw bytes to a temp file, resize to jpg_path, then clean up.
    Raises CalledProcessError if magick fails (counter rolled back, tmp removed).
    """
    ext = ".png" if is_valid_png(raw) else (".webp" if is_webp(raw) else ".jpg")
    tmp = work_dir / f"{stem}.tmp{ext}"
    tmp.write_bytes(raw)
    counters.inc("downloaded")
    try:
        magick_resize(magick, str(tmp), str(jpg_path), dims=dims, gravity=gravity)
    except subprocess.CalledProcessError:
        tmp.unlink(missing_ok=True)
        counters.inc("downloaded", -1)  # undo — bad PNG, caller tries next candidate
        raise
    except Exception:
        tmp.unlink(missing_ok=True)     # clean up on any unexpected error
        counters.inc("downloaded", -1)
        raise
    tmp.unlink(missing_ok=True)
    counters.inc("converted")

def _match_libretro_roms(
    roms_to_dl: list[str],
    covers_path: Path,
    repo_files: list[str],
    cfg: SyncConfig,
) -> tuple[list[LibretroMatch], list[LibretroNoMatch], int]:
    """Match ROMs against the libretro-thumbnails repo. Pure — no I/O.
    Returns (matches, no_matches, n_skipped).
    """
    norm_cache = build_normalized_candidates(repo_files)
    exact_variants: dict[str, list[str]] = defaultdict(list)
    for orig, nc in norm_cache:
        exact_variants[nc].append(orig)

    matches:    list[LibretroMatch]   = []
    no_matches: list[LibretroNoMatch] = []
    n_skipped = 0

    for rom_stem in roms_to_dl:
        jpg_path = covers_path / f"{rom_stem}.jpg"
        rom_norm   = normalize(rom_stem).lower()
        exact_hits = exact_variants.get(rom_norm)
        if exact_hits:
            candidates = sort_by_region([(h, 0.95) for h in exact_hits],
                                        cfg.preferred_region)[:5]
        else:
            candidates = sort_by_region(
                ranked_matches(rom_stem, repo_files, cfg.threshold,
                               _norm_cache=norm_cache),
                cfg.preferred_region,
            )

        if candidates:
            matches.append(LibretroMatch(
                rom_stem=rom_stem, jpg_path=jpg_path, candidates=candidates))
        else:
            best_name, best_score = None, 0.0
            for orig, c_norm in norm_cache:
                s = _similarity_prenorm(orig.lower(), c_norm,
                                        rom_stem.lower().strip(), rom_norm)
                if s > best_score:
                    best_score, best_name = s, orig
            hint = (f"best='{best_name}' score={best_score:.2f}" if best_name
                    else "no files in repo")
            no_matches.append(LibretroNoMatch(rom_stem=rom_stem, hint=hint))

    return matches, no_matches, n_skipped

def _download_covers_without_logo(
    roms_to_dl: list[str],
    covers_path: Path,
    folder: str,
    cfg: SyncConfig,
    counters: Counters,
    failed_covers: list[tuple[str, str, str]],
    lb_index: LbIndex | None = None,
) -> None:
    """Download clean cover art for without_logo style.
    With SGDB key  : SteamGridDB grid → LaunchBox Screenshot-Game-Title fallback.
    Without SGDB key: LaunchBox Screenshot-Game-Title only.
    """
    _lb = lb_index or {}
    source_desc = ("SteamGridDB grids → LaunchBox Screenshot fallback"
                   if cfg.sgdb_key else "LaunchBox Screenshot-Game-Title")
    cprint(C.GRAY, f"  {len(roms_to_dl)} ROM(s) queued — source: {source_desc}")

    if cfg.dry_run:
        for rom_stem in roms_to_dl:
            cprint(C.MAGENTA, f"  [DRY RUN] QUEUED (clean cover)  '{rom_stem}'")
        return

    magick = cfg.magick
    assert magick  # non-None guaranteed — caller guards with `if not cfg.magick: return`
    cprint(C.CYAN, f"  Downloading {len(roms_to_dl)} cover(s) via {source_desc}...")
    print_lock = threading.Lock()
    tracker    = _ProgressTracker(len(roms_to_dl), label="Downloading ")

    def _worker(rom_stem: str) -> None:
        jpg_path = covers_path / f"{rom_stem}.jpg"
        url = _find_fallback_url(
            rom_stem, _lb, cfg,
            lb_finder=lbdb_find_screenshot_url,
            sgdb_fn=sgdb_get_cover_url,
            sgdb_first=True,
        )
        if url is None:
            tracker.tick()
            with print_lock:
                cprint(C.DYELLOW, f"  NO COVER  '{rom_stem}'")
                failed_covers.append((folder, rom_stem, "no match: no clean cover found"))
            return
        try:
            raw = _http_get(url, None, timeout=cfg.http_timeout)
            _write_and_convert(raw, covers_path, rom_stem, jpg_path, magick, counters)
            _progress_ok(tracker, print_lock, f"  OK  {rom_stem}")
        except Exception as e:
            tracker.tick()
            with print_lock:
                cprint(C.DRED, f"  FAIL  '{rom_stem}': {e}")
                failed_covers.append((folder, rom_stem, f"download failed: {e}"))

    _run_thread_pool(cfg.parallel_jobs, roms_to_dl, _worker, max_workers=4,
                     interrupt_msg="  Interrupted -- cancelling remaining downloads...")
    print()

def _find_fallback_url(
    rom_stem:   str,
    lb_index:   LbIndex,
    cfg:        SyncConfig,
    lb_finder:  "Callable[[str, LbIndex, str], str | None]",
    sgdb_fn:    "Callable[[int, str], str | None] | None",
    *,
    sgdb_first: bool = False,
) -> str | None:
    """Two-source fallback: lb_finder ↔ sgdb_fn.  sgdb_first reverses priority.
    SGDB is skipped when no key is set or sgdb_fn is None.
    """
    def _try_sgdb() -> str | None:
        if not (sgdb_fn and cfg.sgdb_key):
            return None
        game_id = sgdb_search_game(rom_stem, cfg.sgdb_key)
        return sgdb_fn(game_id, cfg.sgdb_key) if game_id else None

    def _try_lb() -> str | None:
        return lb_finder(rom_stem, lb_index, cfg.preferred_region)

    if sgdb_first:
        return _try_sgdb() or _try_lb() or None
    return _try_lb() or _try_sgdb() or None

def _download_art_batch(
    matches:          list[LibretroMatch],
    covers_path:      Path,
    repo_name:        str,
    cfg:              SyncConfig,
    counters:         Counters,
    failed_covers:    list[tuple[str, str, str]],
    folder:           str,
    lb_folder:        str,
    lb_fallback_finder: "Callable[[str, LbIndex, str], str | None]",
    sgdb_fn:          "Callable[[int, str], str | None] | None" = None,
    lb_index:         LbIndex | None = None,
    direct_roms:      list[str] | None = None,
    dims:             str = "512x512",
    gravity:          str = "center",
) -> None:
    """Download covers/backgrounds via libretro-thumbnails with LB + SGDB fallbacks."""
    _direct = direct_roms or []
    lb_idx  = lb_index or {}
    magick  = cfg.magick
    assert magick  # non-None guaranteed — caller guards with `if not cfg.magick: return`
    cprint(C.CYAN, f"  Downloading {len(matches) + len(_direct)} cover(s)...")
    print_lock = threading.Lock()
    tracker    = _ProgressTracker(len(matches) + len(_direct), label="Downloading ")

    def _worker(item: LibretroMatch) -> None:
        rom_stem   = item.rom_stem
        jpg_path   = item.jpg_path
        candidates = item.candidates

        # Step 1: SGDB (primary when key is set)
        if sgdb_fn and cfg.sgdb_key:
            game_id = sgdb_search_game(rom_stem, cfg.sgdb_key)
            if game_id:
                sgdb_url = sgdb_fn(game_id, cfg.sgdb_key)
                if sgdb_url:
                    try:
                        raw = _http_get(sgdb_url, None, timeout=cfg.http_timeout)
                        _write_and_convert(raw, covers_path, rom_stem, jpg_path,
                                           magick, counters, dims=dims, gravity=gravity)
                        _progress_ok(tracker, print_lock, f"  OK (SGDB)  {rom_stem}")
                        return
                    except Exception as e:
                        with print_lock:
                            cprint(C.GRAY, f"  SGDB failed  '{rom_stem}': {e}")

        # Step 2: libretro candidates
        for attempt, (match_name, _) in enumerate(candidates):
            url = (f"{BASE_RAW_URL}/{repo_name}/master/{lb_folder}/"
                   f"{urllib.parse.quote(match_name)}.png")
            try:
                raw = _http_get(url, cfg.github_token, timeout=cfg.http_timeout)
            except Exception as e:
                with print_lock:
                    cprint(C.DRED, f"  FAIL  '{rom_stem}' <- '{match_name}': {e}")
                continue  # try next candidate

            if not is_valid_png(raw):
                with print_lock:
                    cprint(C.YELLOW,
                           f"  BAD PNG  '{rom_stem}' <- '{match_name}' "
                           f"(invalid header, trying next candidate...)")
                continue

            try:
                _write_and_convert(raw, covers_path, rom_stem, jpg_path,
                                   magick, counters, dims=dims, gravity=gravity)
            except subprocess.CalledProcessError:
                with print_lock:
                    cprint(C.YELLOW,
                           f"  BAD IMAGE  '{rom_stem}' <- '{match_name}' "
                           f"(ImageMagick error, trying next candidate...)")
                continue

            dd, dt = tracker.tick()
            with print_lock:
                attempt_note = f" (attempt {attempt+1})" if attempt > 0 else ""
                print(progress_bar(dd, dt, label=tracker.label), end="", flush=True)
                cprint(C.GREEN, f"  OK  {rom_stem}{attempt_note}")
            return  # success — stop trying candidates

        # Step 3: LB fallback
        _fallback_url = lb_fallback_finder(rom_stem, lb_idx, cfg.preferred_region)
        if _fallback_url:
            try:
                raw = _http_get(_fallback_url, None, timeout=cfg.http_timeout)
                _write_and_convert(raw, covers_path, rom_stem, jpg_path,
                                   magick, counters, dims=dims, gravity=gravity)
                _progress_ok(tracker, print_lock, f"  OK (fallback)  {rom_stem}")
                return
            except Exception as lbe:
                with print_lock:
                    cprint(C.GRAY, f"  Fallback download failed  '{rom_stem}': {lbe}")

        # All sources exhausted — advance the bar so it reaches 100%
        dd, dt = tracker.tick()
        with print_lock:
            print(progress_bar(dd, dt, label=tracker.label), end="", flush=True)
            cprint(C.DRED,
                   f"  GIVE UP  '{rom_stem}' -- all {len(candidates)} candidate(s) failed")
            failed_covers.append((folder, rom_stem,
                                  f"download failed ({len(candidates)} candidate(s) tried)"))

    def _worker_direct(rom_stem: str) -> None:
        """ROMs with no libretro match: try sgdb_fn then lb_fallback_finder."""
        jpg_path = covers_path / f"{rom_stem}.jpg"
        url = _find_fallback_url(
            rom_stem, lb_idx, cfg,
            lb_finder=lb_fallback_finder,
            sgdb_fn=sgdb_fn,
            sgdb_first=True,
        )
        if url:
            try:
                raw = _http_get(url, None, timeout=cfg.http_timeout)
                _write_and_convert(raw, covers_path, rom_stem, jpg_path,
                                   magick, counters, dims=dims, gravity=gravity)
                _progress_ok(tracker, print_lock, f"  OK (fallback)  {rom_stem}")
                return
            except Exception as e:
                with print_lock:
                    cprint(C.GRAY, f"  Fallback failed  '{rom_stem}': {e}")
        dd, dt = tracker.tick()
        with print_lock:
            print(progress_bar(dd, dt, label=tracker.label), end="", flush=True)
            cprint(C.DRED, f"  NO IMAGE  '{rom_stem}'")
            failed_covers.append((folder, rom_stem, "no match: no image found"))

    with ThreadPoolExecutor(max_workers=cfg.parallel_jobs) as pool:
        futures  = [pool.submit(_worker, m) for m in matches]
        futures += [pool.submit(_worker_direct, r) for r in _direct]
        try:
            for fut in as_completed(futures):
                fut.result()
        except KeyboardInterrupt:
            cprint(C.YELLOW, "\n  Interrupted — cancelling remaining downloads...")
            pool.shutdown(wait=False, cancel_futures=True)
            raise
    print()  # newline after progress bar

def _download_bg_images(
    roms_to_dl: list[str],
    bgs_path: Path,
    folder: str,
    cfg: SyncConfig,
    bg_counters: Counters,
    failed_bgs: list[tuple[str, str, str]],
    lb_index: LbIndex | None = None,
) -> None:
    """Download background images from SGDB Heroes with LaunchBox Fanart fallback."""
    source_desc = ("SteamGridDB Heroes → LaunchBox Fanart fallback"
                   if cfg.sgdb_key else "LaunchBox Fanart-Background")
    cprint(C.CYAN, f"  Downloading {len(roms_to_dl)} background(s) via {source_desc}...")

    if cfg.dry_run:
        source_label = "SGDB hero → LaunchBox fallback" if cfg.sgdb_key else "LaunchBox fanart"
        for rom_stem in roms_to_dl:
            cprint(C.MAGENTA, f"  [DRY RUN] QUEUED ({source_label})  '{rom_stem}'")
        return

    magick     = cfg.magick
    assert magick  # non-None guaranteed — caller guards with `if not cfg.magick: return`
    print_lock = threading.Lock()
    tracker    = _ProgressTracker(len(roms_to_dl), label="Backgrounds")
    lb_idx     = lb_index or {}

    def _worker(rom_stem: str) -> None:
        jpg_path    = bgs_path / f"{rom_stem}.jpg"
        hero_url:   str | None = None
        used_source = "none"
        # game_id is only meaningful when sgdb_key is set; initialise to None
        # so the error-reason branch below never risks a NameError.
        game_id: int | None = None

        if cfg.sgdb_key:
            game_id = sgdb_search_game(rom_stem, cfg.sgdb_key)
            if game_id is None:
                with print_lock:
                    cprint(C.DYELLOW, f"  NO SGDB MATCH  '{rom_stem}' — trying LaunchBox...")
            else:
                hero_url = sgdb_get_hero_url(game_id, cfg.sgdb_key)
                if hero_url is None:
                    with print_lock:
                        cprint(C.DYELLOW,
                               f"  NO SGDB HERO  '{rom_stem}' (game_id={game_id})"
                               " — trying LaunchBox...")
                else:
                    used_source = "SGDB hero"

        if hero_url is None:
            lb_bg_url = lbdb_find_bg_url(rom_stem, lb_idx, cfg.preferred_region)
            if lb_bg_url is None:
                if not cfg.sgdb_key:
                    source_note = "no fanart (no SGDB key, LaunchBox: no fanart)"
                elif game_id is None:
                    source_note = "no match: SGDB game not found, LaunchBox: no fanart"
                else:
                    source_note = "no match: SGDB no hero, LaunchBox: no fanart"
                with print_lock:
                    failed_bgs.append((folder, rom_stem, source_note))
                tracker.tick()  # still advance so bar stays accurate
                return
            hero_url    = lb_bg_url
            used_source = "LaunchBox"
            with print_lock:
                source = "LaunchBox" if not cfg.sgdb_key else "LaunchBox (SGDB fallback)"
                cprint(C.GRAY, f"  {source} BG  '{rom_stem}'")

        try:
            raw = _http_get(hero_url, None, timeout=cfg.http_timeout)
            _write_and_convert(raw, bgs_path, rom_stem, jpg_path, magick, bg_counters,
                               dims="1920x1080")
            _progress_ok(tracker, print_lock, f"  OK  {rom_stem}")
        except Exception as e:
            tracker.tick()
            with print_lock:
                cprint(C.DRED, f"  FAIL  '{rom_stem}': {e}")
                failed_bgs.append((folder, rom_stem, f"{used_source} download failed: {e}"))

    _run_thread_pool(cfg.parallel_jobs, roms_to_dl, _worker, max_workers=4,
                     interrupt_msg="  Interrupted -- cancelling remaining background downloads...")
    print()  # newline after progress bar

# =============================================================================
# ORCHESTRATORS
# =============================================================================
def process_folder(folder: str, roms_path: Path, covers_path: Path,
                   cfg: SyncConfig,
                   repo_files: list[str], repo_name: str,
                   counters: Counters,
                   orphans: list[str],
                   failed_covers: list[tuple[str, str, str]],
                   lb_index: LbIndex | None = None) -> None:
    """Process one system folder: rename mismatched covers, download missing ones."""
    cprint(C.CYAN, f"\n=== {folder} ===")

    if not roms_path.exists():
        cprint(C.YELLOW, f"  WARNING: ROM folder not found, skipping: {roms_path}")
        return

    roms = _scan_roms(roms_path)

    _ensure_art_dir(covers_path, "covers", cfg.dry_run)

    covers = (
        {p.stem: p for p in covers_path.iterdir() if p.is_file()}
        if covers_path.exists() else {}
    )

    # Step 1 — fuzzy-rename mismatched covers
    if _reconcile_art_files(covers, roms, covers_path, cfg, counters, orphans,
                            dims="512x512", gravity="center"):
        covers = {p.stem: p for p in covers_path.iterdir() if p.is_file()}

    # Step 2 — downloads
    if cfg.download_mode == "skip":
        missing = [r for r in roms if r not in covers]
        if missing:
            cprint(C.GRAY, f"  SKIP  {len(missing)} ROM(s) without cover (download skipped)")
            counters.inc("skipped", len(missing))
        else:
            cprint(C.GREEN, "  All ROMs have covers!")
        return

    roms_to_dl = (
        list(roms.keys()) if cfg.download_mode == "all"
        else [r for r in roms if r not in covers]
    )
    if not roms_to_dl:
        cprint(C.GREEN, "  All ROMs have covers!")
        return

    if not cfg.magick:
        cprint(C.DYELLOW,
               f"  Skipping {len(roms_to_dl)} download(s): ImageMagick not found. "
               "Install it to enable PNG→JPG conversion.")
        return

    lb_idx = lb_index or {}  # resolved once; used by all three cover styles below

    if cfg.cover_style == "without_logo":
        _download_covers_without_logo(roms_to_dl, covers_path, folder, cfg, counters,
                               failed_covers, lb_index=lb_idx)
        return

    # with_logo / game_logo: libretro-thumbnails primary, LB + optional SGDB fallbacks.
    if cfg.cover_style == "game_logo":
        _lb_folder, _sgdb_fn, _lb_fallback = (
            "Named_Logos", sgdb_get_logo_url, lbdb_find_logo_url)
    else:  # with_logo
        _lb_folder, _sgdb_fn, _lb_fallback = (
            "Named_Boxarts", None, lbdb_find_cover_url)

    if not repo_files:
        if _sgdb_fn is None:
            # with_logo: no libretro repo — fall through to LaunchBox Box-Front.
            # _worker_direct calls lbdb_find_cover_url for every ROM.
            cprint(C.GRAY,
                   f"  No libretro repo for {folder} — falling back to LaunchBox Box-Front...")
            if not cfg.dry_run:
                _download_art_batch(
                    [], covers_path, repo_name, cfg, counters, failed_covers, folder,
                    lb_folder=_lb_folder, sgdb_fn=None, lb_fallback_finder=_lb_fallback,
                    lb_index=lb_idx, direct_roms=roms_to_dl,
                )
            else:
                for r in roms_to_dl:
                    cprint(C.MAGENTA, f"  [DRY RUN] QUEUED (LB Box-Front)  '{r}'")
            return
        # game_logo: no Named_Logos for this system; SGDB + LB may still have logos.
        cprint(C.GRAY, f"  No Named_Logos for {folder} — trying SGDB + LaunchBox logos...")
        if not cfg.dry_run:
            _download_art_batch(
                [], covers_path, repo_name, cfg, counters, failed_covers, folder,
                lb_folder=_lb_folder, sgdb_fn=_sgdb_fn, lb_fallback_finder=_lb_fallback,
                lb_index=lb_idx, direct_roms=roms_to_dl,
            )
        else:
            for r in roms_to_dl:
                cprint(C.MAGENTA, f"  [DRY RUN] QUEUED (SGDB/LB logo)  '{r}'")
        return

    matches, no_matches, n_skipped = _match_libretro_roms(
        roms_to_dl, covers_path, repo_files, cfg)

    if n_skipped:
        counters.inc("skipped", n_skipped)

    # No-libretro-match ROMs: route to direct fallback when a non-libretro
    # source exists (game_logo has SGDB + LB); mark as failed for with_logo.
    direct_roms: list[str] = []
    for nm in no_matches:
        if _sgdb_fn is not None:
            cprint(C.GRAY, f"  No libretro match  '{nm.rom_stem}' — trying SGDB/LB...")
            direct_roms.append(nm.rom_stem)
        else:
            cprint(C.DYELLOW, f"  NO DOWNLOAD MATCH  '{nm.rom_stem}' -- {nm.hint}")
            failed_covers.append((folder, nm.rom_stem, f"no match: no repo match ({nm.hint})"))

    # Report queued
    prefix = f"{C.MAGENTA}  [DRY RUN] {C.RESET}" if cfg.dry_run else "  "
    for m in matches:
        top_name, top_score = m.candidates[0]
        fallback_note = f" (+{len(m.candidates)-1} fallback)" if len(m.candidates) > 1 else ""
        if cfg.preferred_region and cfg.preferred_region != "any":
            picked = region_of(top_name)
            if picked == cfg.preferred_region:
                region_note = f"  {C.GREEN}[{picked} ✓]{C.RESET}"
            elif picked:
                region_note = (f"  {C.YELLOW}[{cfg.preferred_region} wanted"
                               f" → {picked} used]{C.RESET}")
            else:
                region_note = (f"  {C.YELLOW}[{cfg.preferred_region} wanted"
                               f" → no region tag]{C.RESET}")
        else:
            region_note = ""
        print(f"{prefix}{C.CYAN}QUEUED{C.RESET}  '{m.rom_stem}'"
              f"  ->  '{top_name}'  (score: {top_score:.2f}){fallback_note}{region_note}")

    if (matches or direct_roms) and not cfg.dry_run:
        _download_art_batch(
            matches, covers_path, repo_name, cfg, counters, failed_covers, folder,
            lb_folder=_lb_folder, sgdb_fn=_sgdb_fn, lb_fallback_finder=_lb_fallback,
            lb_index=lb_idx, direct_roms=direct_roms or None,
        )

def process_bg_folder(folder: str, roms_path: Path, bgs_path: Path,
                      cfg: SyncConfig,
                      bg_counters: Counters,
                      bg_orphans: list[str],
                      failed_bgs: list[tuple[str, str, str]],
                      lb_index: LbIndex | None = None,
                      repo_files: list[str] | None = None,
                      repo_name: str = "") -> None:
    """Process one system folder for background art.  Always produces 1920x1080 JPEGs.
    bg_style=="fanart": SGDB Heroes → LaunchBox Fanart-Background.
    bg_style=="boxart": libretro Named_Boxarts → LaunchBox Box-Front (letterboxed).
    """
    cprint(C.CYAN, f"\n=== {folder} [backgrounds] ===")

    if not roms_path.exists():
        cprint(C.YELLOW, f"  WARNING: ROM folder not found, skipping: {roms_path}")
        return

    roms = _scan_roms(roms_path)

    _ensure_art_dir(bgs_path, "backgrounds", cfg.dry_run)

    bgs = (
        {p.stem: p for p in bgs_path.iterdir() if p.is_file()}
        if bgs_path.exists() else {}
    )

    # Step 1 — fuzzy-rename mismatched backgrounds
    bg_gravity = "East" if cfg.bg_style == "boxart" else "center"
    if _reconcile_art_files(bgs, roms, bgs_path, cfg, bg_counters, bg_orphans,
                            kind="background", dims="1920x1080", gravity=bg_gravity):
        bgs = {p.stem: p for p in bgs_path.iterdir() if p.is_file()}

    # Step 2 — downloads
    if cfg.download_mode == "skip":
        missing_bgs = [r for r in roms if r not in bgs]
        if missing_bgs:
            cprint(C.GRAY,
                   f"  SKIP  {len(missing_bgs)} ROM(s) without background (download skipped)")
            bg_counters.inc("skipped", len(missing_bgs))
        else:
            cprint(C.GREEN, "  All ROMs have backgrounds!")
        return

    roms_to_dl = (
        list(roms.keys()) if cfg.download_mode == "all"
        else [r for r in roms if r not in bgs]
    )
    if not roms_to_dl:
        cprint(C.GREEN, "  All ROMs have backgrounds!")
        return

    if not cfg.magick:
        cprint(C.DYELLOW,
               f"  Skipping {len(roms_to_dl)} download(s): ImageMagick not found. "
               "Install it to enable background processing.")
        return

    if cfg.bg_style == "boxart":
        if not repo_files:
            cprint(C.GRAY,
                   f"  No libretro repo for {folder} — falling back to LaunchBox Box-Front...")
        cprint(C.CYAN, f"  Downloading {len(roms_to_dl)} background(s) via box art (libretro + LaunchBox)...")
        if cfg.dry_run:
            for r in roms_to_dl:
                cprint(C.MAGENTA, f"  [DRY RUN] QUEUED (boxart BG)  '{r}'")
            return
        lb_idx = lb_index or {}
        matches_bg, no_matches_bg, n_skipped_bg = _match_libretro_roms(
            roms_to_dl, bgs_path, repo_files or [], cfg)
        if n_skipped_bg:
            bg_counters.inc("skipped", n_skipped_bg)
        direct_lb = [nm.rom_stem for nm in no_matches_bg]
        _download_art_batch(
            matches_bg, bgs_path, repo_name, cfg, bg_counters, failed_bgs, folder,
            lb_folder="Named_Boxarts", lb_fallback_finder=lbdb_find_cover_url,
            sgdb_fn=None, lb_index=lb_idx, direct_roms=direct_lb or None,
            dims="1920x1080", gravity="East",
        )
    else:
        _download_bg_images(roms_to_dl, bgs_path, folder, cfg, bg_counters, failed_bgs,
                            lb_index=lb_index)

# =============================================================================
# CRC32 DUPLICATE DETECTION
# =============================================================================
ROM_EXTENSIONS = {
    # Nintendo
    ".nes", ".fds",
    ".sfc", ".smc",                  # SNES (headerless/headered — see _smc_header_offset)
    ".vb",
    ".gb", ".gbc", ".gba",
    ".nds",
    ".3ds", ".cci",
    ".gcz", ".rvz", ".wbfs",        # GameCube / Wii
    ".xci", ".nsp", ".nsz",         # Switch
    ".n64", ".z64", ".v64",         # N64 byte-order variants
    # Sega
    ".md", ".smd", ".gen",
    ".32x",
    ".gg", ".sms",
    ".cdi",                          # Dreamcast (.gdi excluded — text sidecar)
    # Sony
    ".pbp", ".cso",                  # PSP
    # NEC / SNK
    ".pce",
    ".ngp", ".ngc",                  # Neo Geo Pocket / Color
    # Atari
    ".a26", ".a52", ".a78",
    ".j64", ".lnx",
    # Other
    ".ws", ".wsc",
    ".col", ".vec",
    # Generic disc/multi-system
    ".iso",
    ".bin",                          # raw sector image (.cue excluded — text sidecar)
    ".img", ".ecm", ".chd",
    ".rom",
}

# =============================================================================
# NAME-BASED DEDUPLICATION & FILENAME NORMALISATION
# =============================================================================

_NRM_ARTICLE_RE = re.compile(r',\s*(The|A|An)$', re.IGNORECASE)
_NRM_DISC_RE    = re.compile(r'[\(\[](Disc|Disk|CD)\s*\d+[\)\]]', re.IGNORECASE)

def normalize_filename(filename: str) -> str:
    """Strip all tags except disc number; move trailing articles to the front."""
    base, ext = os.path.splitext(filename)
    base = re.sub(r'_\d+$', '', base)
    base = re.sub(r"_s\b", "'s", base, flags=re.IGNORECASE)
    base = base.replace('_', ' ')
    disc_match = _NRM_DISC_RE.search(base)
    disc_tag   = f" {disc_match.group(0)}" if disc_match else ""
    title = re.split(r'\s*[\(\[]', base)[0].strip()
    # Split on subtitle separator so ", The" before " - Subtitle" is detected.
    parts = re.split(r'\s+-\s+', title, maxsplit=1)
    m = _NRM_ARTICLE_RE.search(parts[0])
    if m:
        parts[0] = m.group(1) + ' ' + parts[0][:m.start()].strip()
    title = ' - '.join(parts)
    title = re.sub(r'  +', ' ', title).strip()
    return title + disc_tag + ext

def collect_renames(folder_path: str) -> list[tuple[str, str]]:
    """Walk folder; return [(old_path, new_path)] for files whose name would change."""
    renames = []
    for dirpath, _, filenames in os.walk(folder_path):
        for filename in filenames:
            new_name = normalize_filename(filename)
            if new_name != filename:
                renames.append((
                    os.path.join(dirpath, filename),
                    os.path.join(dirpath, new_name),
                ))
    return renames

# Non-ROM extensions skipped during name-based grouping.
_DEDUP_NON_ROM_EXTS: frozenset[str] = frozenset({
    '.sav', '.srm', '.state', '.sta',
    '.ss0', '.ss1', '.ss2', '.ss3', '.ss4', '.ss5', '.ss6', '.ss7', '.ss8', '.ss9',
    '.png', '.jpg', '.jpeg', '.bmp',
    '.xml', '.json', '.dat', '.txt',
    '.m3u',
})

# Generation families for cross-system exclusives filtering.
_DEDUP_DEFAULT_FAMILIES: dict[str, list[str]] = {
    "8bit":      ["NES", "SMS", "MasterSystem", "Famicom"],
    "16bit":     ["SegaGenesis", "Genesis", "MegaDrive", "SNES", "SuperNintendo", "PCEngine", "TG16"],
    "handhelds": ["GB", "GBC", "GBA", "GameBoy", "GameGear", "Lynx"],
    "32bit":     ["PlayStation", "PSX", "PS1", "Saturn", "SegaSaturn", "N64", "Nintendo64"],
    "128bit":    ["PS2", "GameCube", "GCN", "Xbox", "Dreamcast", "SDC"],
}

def detect_family(system_name: str,
                  families: dict[str, list[str]] | None = None) -> tuple[str | None, list[str]]:
    """Return (family_name, member_list) for the given system, or (None, [])."""
    if families is None:
        families = _DEDUP_DEFAULT_FAMILIES
    name_lower = system_name.lower()
    for family, members in families.items():
        if any(m.lower() == name_lower for m in members):
            return family, members
    return None, []

def normalize_basename(filename: str) -> str:
    """Strip extension, tags, and articles; lowercase. e.g. 'Aladdin (USA).gbc' → 'aladdin'."""
    return _norm_for_dedup(os.path.splitext(filename)[0])

def get_files_by_basename(folder_path: str) -> dict[str, list[str]]:
    """Group files in a folder (recursively) by normalized base name."""
    groups: dict[str, list[str]] = defaultdict(list)
    for dirpath, _, filenames in os.walk(folder_path):
        for filename in filenames:
            if os.path.splitext(filename)[1].lower() in _DEDUP_NON_ROM_EXTS:
                continue
            groups[normalize_basename(filename)].append(
                os.path.join(dirpath, filename)
            )
    return groups

def find_name_duplicates(folder_path: str) -> dict[str, list[str]]:
    """Return groups of files sharing the same base name within a folder."""
    return {k: v for k, v in get_files_by_basename(folder_path).items() if len(v) > 1}

@functools.lru_cache(maxsize=64)
def _dedup_tag_pattern(tag: str) -> re.Pattern:
    return re.compile(
        r'[\(\[][^\)\]]*\b' + re.escape(tag) + r'[^\)\]]*[\)\]]', re.IGNORECASE
    )

def _dedup_matches_tag(filename: str, tag: str) -> bool:
    return bool(_dedup_tag_pattern(tag).search(filename))

def _dedup_auto_pick(paths: list[str], preferences: list[str]) -> str | None:
    """Return the first file matching a preference tag (in priority order), or None."""
    for pref in preferences:
        for path in paths:
            if _dedup_matches_tag(os.path.basename(path), pref):
                return path
    return None

def _dedup_filter_excluded(paths: list[str], excludes: list[str]) -> list[str]:
    return [p for p in paths if not any(_dedup_matches_tag(os.path.basename(p), ex)
                                        for ex in excludes)]

def _dedup_is_multidisc(paths: list[str]) -> bool:
    """True if every file has a distinct disc number tag (not a duplicate)."""
    pattern = re.compile(r'[\(\[](Disc|Disk|CD)\s*\d+[\)\]]', re.IGNORECASE)
    tags = [pattern.search(os.path.basename(p)) for p in paths]
    if not all(tags):
        return False
    return len({t.group(0).lower() for t in tags if t}) == len(paths)  # type: ignore[union-attr]

def _dedup_path_label(path: str, use_label: bool) -> str:
    """Format a file path for display: '[parentfolder] filename' or just 'filename'."""
    if use_label:
        return f"[{os.path.basename(os.path.dirname(path))}] {os.path.basename(path)}"
    return os.path.basename(path)

def _dedup_ask_ext(extensions: list[str]) -> str | None:
    """Ask once which extension to keep. Returns None if skipped."""
    ext_list = sorted(extensions)
    for i, ext in enumerate(ext_list, 1):
        print(f"  [{i}] {ext}")
    while True:
        choice = input(f"  Keep which extension? (1-{len(ext_list)}, s=skip): ").strip().lower()
        if choice == 's':
            return None
        if choice.isdigit() and 1 <= int(choice) <= len(ext_list):
            return ext_list[int(choice) - 1]
        print("  Invalid choice.")

def _dedup_ask_keep(paths: list[str], preferences: list[str] | None = None,
                    use_label: bool = False) -> str | None:
    """Try preference auto-pick first, then ask interactively."""
    name_fn = functools.partial(_dedup_path_label, use_label=use_label)
    if preferences:
        pick = _dedup_auto_pick(paths, preferences)
        if pick:
            print(f"  Auto-selected (preference): {name_fn(pick)}")
            return pick
    for i, path in enumerate(paths, 1):
        print(f"  [{i}] {name_fn(path)}")
    while True:
        choice = input(f"  Keep which file? (1-{len(paths)}, s=skip): ").strip().lower()
        if choice == 's':
            return None
        if choice.isdigit() and 1 <= int(choice) <= len(paths):
            return paths[int(choice) - 1]
        print("  Invalid choice.")

def _dedup_delete_files(paths: list[str], total: int,
                        use_label: bool = False) -> int:
    name_fn = functools.partial(_dedup_path_label, use_label=use_label)
    for path in paths:
        print(f"  Deleting: {name_fn(path)}")
        try:
            os.remove(path)
            total += 1
        except PermissionError:
            print(f"  ERROR (permission denied): {name_fn(path)}")
        except OSError as e:
            print(f"  ERROR: {name_fn(path)} — {e}")
    return total

def delete_name_duplicates(
    duplicates: dict[str, list[str]],
    dry_run: bool = True,
    preferences: list[str] | None = None,
    excludes: list[str] | None = None,
    ext_preference: dict | None = None,
    use_label: bool = False,
    keep_from: str | None = None,
) -> int:
    """Interactive deletion for name-based duplicate groups. Returns deleted count."""
    total = 0
    if ext_preference is None:
        ext_preference = {}
    name_fn = functools.partial(_dedup_path_label, use_label=use_label)

    for base_name, paths in sorted(duplicates.items()):
        print(f"\n[{base_name}]")

        if _dedup_is_multidisc(paths):
            for p in paths:
                print(f"  Multi-disc: {name_fn(p)}")
            print("  Skipped (multi-disc set).")
            continue

        if keep_from and not dry_run:
            to_delete = [p for p in paths
                         if not os.path.abspath(p).startswith(os.path.abspath(keep_from))]
            to_keep   = [p for p in paths if p not in to_delete]
            if to_delete:
                total = _dedup_delete_files(to_delete, total, use_label)
            for p in to_keep:
                print(f"  Kept:     {name_fn(p)}")
            continue

        if dry_run:
            for p in paths:
                print(f"  {name_fn(p)}")
            continue

        # Remove excluded files from candidates
        if excludes:
            valid    = _dedup_filter_excluded(paths, excludes)
            excluded = [p for p in paths if p not in valid]
            if not valid:
                total = _dedup_delete_files(excluded, total, use_label)
                continue
            if excluded:
                total = _dedup_delete_files(excluded, total, use_label)
                if len(valid) == 1:
                    print(f"  Kept:     {name_fn(valid[0])}")
                    continue
                paths = valid

        # Group by extension
        by_ext: dict[str, list[str]] = defaultdict(list)
        for p in paths:
            by_ext[os.path.splitext(p)[1].lower()].append(p)
        extensions = set(by_ext.keys())

        if len(extensions) > 1:
            pref_pick = _dedup_auto_pick(paths, preferences) if preferences else None
            if pref_pick:
                keep_ext = os.path.splitext(pref_pick)[1].lower()
                print(f"  Auto-selected (preference): {name_fn(pref_pick)}")
            else:
                ext_key = frozenset(extensions)
                if ext_key not in ext_preference:
                    print(f"  Conflict: {', '.join(name_fn(p) for p in paths)}")
                    ext_preference[ext_key] = _dedup_ask_ext(list(extensions))
                keep_ext = ext_preference[ext_key]

            if keep_ext is None:
                print("  Skipped.")
                continue

            to_keep   = by_ext[keep_ext]
            to_delete = [p for ext, ps in by_ext.items() if ext != keep_ext for p in ps]
            total = _dedup_delete_files(to_delete, total, use_label)

            if len(to_keep) > 1:
                print(f"  Multiple {keep_ext} files remain, pick one:")
                keep = _dedup_ask_keep(to_keep, preferences, use_label)
                if keep:
                    total = _dedup_delete_files([p for p in to_keep if p != keep],
                                                total, use_label)
                    print(f"  Kept:     {name_fn(keep)}")
                else:
                    print("  Skipped.")
            else:
                print(f"  Kept:     {name_fn(to_keep[0])}")
        else:
            print(f"  Same extension ({list(extensions)[0]}), pick one:")
            keep = _dedup_ask_keep(paths, preferences, use_label)
            if keep is None:
                print("  Skipped.")
                continue
            total = _dedup_delete_files([p for p in paths if p != keep], total, use_label)
            print(f"  Kept:     {name_fn(keep)}")

    return total

# ── companion aliases (used by wizard tasks 6 / 7) ────────────────────────────
_companion_collect_renames    = collect_renames
_companion_get_files_by_base  = get_files_by_basename
_companion_detect_family      = detect_family
_companion_DEFAULT_FAMILIES   = _DEDUP_DEFAULT_FAMILIES

# =============================================================================
# CDDA audio tracks ("Track N.bin") are raw PCM and can be byte-identical
# across unrelated games — excluded from duplicate detection.
_CDDA_TRACK_RE = re.compile(r'\btrack\s*\d+\b', re.IGNORECASE)

# Disc-number tag for multi-disc detection in Stage 4.
_DISC_TAG_RE = re.compile(r'\b(?:disc|disk|cd)\s*\d+\b', re.IGNORECASE)

# SNES copier header: 512 bytes prepended to ROM data (size % 1024 == 512).
# Without normalisation, headered and headerless copies differ in size and
# would never be grouped in Stage 1.
_SMC_HEADER_SIZE: int       = 512
_SMC_HEADER_EXTS: frozenset = frozenset({".smc", ".sfc"})

def _smc_header_offset(path: Path, size: int) -> int:
    """Return 512 if path is a headered SNES ROM, else 0."""
    return (
        _SMC_HEADER_SIZE
        if (size > _SMC_HEADER_SIZE
            and size % 1024 == _SMC_HEADER_SIZE
            and path.suffix.lower() in _SMC_HEADER_EXTS)
        else 0
    )

def _hash_file(path: Path, offset: int = 0,
               chunk_size: int = 1 << 20) -> tuple[str, str] | None:
    """Compute (crc32_hex, sha1_hex) for path, skipping leading offset bytes.
    Returns None on any error.
    """
    try:
        crc = 0
        try:
            sha = hashlib.sha1(usedforsecurity=False)  # usedforsecurity: FIPS compat (Python 3.9+)
        except TypeError:
            sha = hashlib.sha1()
        with open(path, "rb") as f:
            if offset:
                f.seek(offset)
            while chunk := f.read(chunk_size):
                crc = zlib.crc32(chunk, crc)
                sha.update(chunk)
        return f"{crc & 0xFFFFFFFF:08X}", sha.hexdigest().upper()
    except Exception:
        return None

def _build_suspected(eligible_files: list[Path],
                     confirmed_paths: set[Path],
                     file_sizes: dict[Path, int]) -> list[list[Path]]:
    """Return groups that share a normalized title but differ in content.
    Groups are skipped if: already confirmed duplicates, size ratio >2×,
    or all members have distinct disc-number tags (multi-disc game).
    """
    name_groups: dict[tuple[str, str], list[Path]] = defaultdict(list)
    for p in eligible_files:
        if p in confirmed_paths:
            continue
        norm_name = _norm_for_dedup(p.stem)
        if not norm_name:
            continue
        compact = _NONALNUM_RE.sub("", norm_name)  # "Choro Q" == "ChoroQ"
        key = (compact, p.suffix.lower())
        name_groups[key].append(p)

    suspected: list[list[Path]] = []
    for paths in name_groups.values():
        if len(paths) < 2:
            continue
        # Size >2× difference → almost certainly different games
        if file_sizes:
            sizes = [file_sizes[p] for p in paths if p in file_sizes]
            if sizes and max(sizes) > 2 * min(sizes):
                continue
        disc_nums = []
        for p in paths:
            m = _DISC_TAG_RE.search(p.stem)
            disc_nums.append(m.group(0).lower() if m else None)
        all_have_disc = all(d is not None for d in disc_nums)
        all_disc_different = len(set(disc_nums)) == len(disc_nums)
        if all_have_disc and all_disc_different:
            continue
        suspected.append(sorted(paths))

    return suspected

def _build_size_similar(
    by_size:        dict[int, list[tuple[Path, int, int]]],
    confirmed_paths: set[Path],
    suspected_paths: set[Path],
    threshold: float = 0.70,
) -> list[list[Path]]:
    """Surface same-size pairs with similar but differently-normalized names.
    Uses union-find for connected-component grouping (A~B and B~C → {A,B,C}).
    """
    new_groups: list[list[Path]] = []
    for entries in by_size.values():
        if len(entries) < 2:
            continue
        by_ext: dict[str, list[Path]] = defaultdict(list)
        for p, _, _ in entries:
            if p in confirmed_paths or p in suspected_paths:
                continue
            by_ext[p.suffix.lower()].append(p)
        for paths in by_ext.values():
            if len(paths) < 2:
                continue
            parent = list(range(len(paths)))

            def find(x: int) -> int:
                while parent[x] != x:
                    parent[x] = parent[parent[x]]
                    x = parent[x]
                return x

            for i in range(len(paths)):
                for j in range(i + 1, len(paths)):
                    if find(i) != find(j) and similarity(paths[i].stem, paths[j].stem) >= threshold:
                        parent[find(i)] = find(j)

            components: dict[int, list[Path]] = defaultdict(list)
            for i, p in enumerate(paths):
                components[find(i)].append(p)
            for component in components.values():
                if len(component) >= 2:
                    new_groups.append(sorted(component))
    return new_groups

def check_duplicates(roms_base: Path, common: list[str],
                     single_system: bool, parallel_jobs: int,
                     dry_run: bool = True) -> None:
    """Four-stage duplicate detection: size → CRC32 → SHA-1 → same-title name matching.
    Exact duplicates require size+CRC32+SHA-1 agreement. Empty files reported separately.
    """
    print()
    cprint(C.CYAN, "=============================================")
    cprint(C.CYAN, "  DUPLICATE ROM DETECTION")
    cprint(C.CYAN, "  (size → CRC32 → SHA-1, then title-name matching)")
    cprint(C.CYAN, "=============================================")
    print()

    # ------------------------------------------------------------------
    # Stage 0: collect files
    # ------------------------------------------------------------------
    all_rom_files: list[Path] = []
    for folder in common:
        rom_dir = roms_base if single_system else roms_base / folder
        if not rom_dir.exists():
            cprint(C.YELLOW, f"  WARNING: folder not found, skipping: {rom_dir}")
            continue
        for p in rom_dir.rglob("*.*"):
            if p.is_file() and p.suffix.lower() in ROM_EXTENSIONS:
                if _CDDA_TRACK_RE.search(p.stem):  # skip CDDA audio tracks
                    continue
                all_rom_files.append(p)

    if not all_rom_files:
        cprint(C.YELLOW, "  No ROM files found.")
        return

    cprint(C.CYAN, f"  Found {len(all_rom_files)} ROM file(s).")
    print()

    # ------------------------------------------------------------------
    # Stage 1: group by normalized size.
    # Groups by header-stripped size so headered/headerless SNES copies
    # are compared (see _smc_header_offset).
    # ------------------------------------------------------------------
    cprint(C.GRAY, "  Stage 1/4 — grouping by file size...")
    empty_files: list[Path] = []
    unreadable:  list[Path] = []
    by_size: dict[int, list[tuple[Path, int, int]]] = defaultdict(list)  # norm_sz → [(path, raw_sz, offset)]

    for p in all_rom_files:
        try:
            sz = p.stat().st_size
        except OSError:
            unreadable.append(p)
            continue
        if sz == 0:
            empty_files.append(p)
        else:
            offset  = _smc_header_offset(p, sz)
            norm_sz = sz - offset
            by_size[norm_sz].append((p, sz, offset))

    size_candidates: list[tuple[Path, int, int]] = [
        (p, sz, off)
        for entries in by_size.values() if len(entries) > 1
        for p, sz, off in entries
    ]
    size_unique = sum(1 for entries in by_size.values() if len(entries) == 1)

    cprint(C.GRAY,
           f"    {size_unique} unique-size files skipped  |  "
           f"{len(size_candidates)} candidate(s) need hashing"
           + (f"  |  {len(empty_files)} empty file(s)" if empty_files else ""))
    print()

    if not size_candidates:
        # No exact-size candidates, but name-based matches may still exist.
        confirmed_paths: set[Path] = set()
        empty_set  = set(empty_files)
        unread_set = set(unreadable)
        file_sizes = {p: norm_sz for norm_sz, entries in by_size.items() for p, _, _ in entries}
        eligible   = [p for p in all_rom_files if p not in empty_set and p not in unread_set]
        suspected  = _build_suspected(eligible, confirmed_paths, file_sizes)
        print()
        _report_duplicates([], suspected, empty_files, unreadable, all_rom_files, dry_run=dry_run)
        return

    # ------------------------------------------------------------------
    # Stage 2: CRC32 + SHA-1 on candidates only (parallel, with progress)
    # Both hashes computed in a single sequential read per file.
    # ------------------------------------------------------------------
    cprint(C.GRAY, f"  Stage 2/4 — hashing {len(size_candidates)} candidate(s)...")

    # (norm_size, crc32) -> [(path, sha1), ...]
    hash_results: dict[tuple[int, str], list[tuple[Path, str]]] = defaultdict(list)
    hash_lock  = threading.Lock()
    done_count = 0
    total      = len(size_candidates)

    def hash_one(path: Path, raw_size: int, offset: int) -> None:
        hashes = _hash_file(path, offset=offset)
        norm_sz = raw_size - offset
        with hash_lock:
            if hashes is None:
                unreadable.append(path)
            else:
                crc, sha = hashes
                hash_results[(norm_sz, crc)].append((path, sha))

    with ThreadPoolExecutor(max_workers=parallel_jobs) as pool:
        futures = {pool.submit(hash_one, p, sz, off): p for p, sz, off in size_candidates}
        try:
            for fut in as_completed(futures):
                try:
                    fut.result()
                except Exception as e:
                    cprint(C.YELLOW, f"  WARNING: hash error: {e}")
                finally:
                    done_count += 1
                    dc = done_count
                    print(progress_bar(dc, total, label="Hashing   "), end="", flush=True)
        except KeyboardInterrupt:
            print()
            cprint(C.YELLOW, "  Interrupted — cancelling remaining hash operations...")
            pool.shutdown(wait=False, cancel_futures=True)
            raise
    print()  # newline after progress bar

    # ------------------------------------------------------------------
    # Stage 3: SHA-1 confirmation (size+CRC32+SHA-1 → exact duplicate)
    # ------------------------------------------------------------------
    cprint(C.GRAY, "  Stage 3/4 — confirming by SHA-1...")
    confirmed:      list[list[tuple[Path, str, str, int]]] = []  # (path, crc32, sha1, size)
    near_collisions: list[tuple[int, str, list[Path]]] = []  # (size, crc, paths)

    for (sz, crc), entries in hash_results.items():
        if len(entries) < 2:
            continue
        sha_groups: dict[str, list[tuple[Path, str, str, int]]] = defaultdict(list)
        for path, sha1_hex in entries:
            sha_groups[sha1_hex].append((path, crc, sha1_hex, sz))
        real_dup_groups = [g for g in sha_groups.values() if len(g) > 1]
        confirmed_paths_here: set[Path] = set()
        for group in real_dup_groups:
            confirmed.append(group)
            confirmed_paths_here.update(p for p, _, _, _ in group)
        if len(sha_groups) > 1:
            # Same size+CRC32 but different SHA-1 → CRC32 collision, not a duplicate
            nc_paths = [p for g in sha_groups.values() for p, _, _, _ in g
                        if p not in confirmed_paths_here]
            if nc_paths:
                near_collisions.append((sz, crc, nc_paths))

    # ------------------------------------------------------------------
    # Stage 4: name-based fuzzy detection (same title, different bytes)
    # Surfaces regional/revision pairs like "Asterix.smc" vs "Asterix (NTSC).smc".
    # ------------------------------------------------------------------
    confirmed_paths: set[Path] = {p for g in confirmed for p, _, _, _ in g}
    empty_set  = set(empty_files)
    unread_set = set(unreadable)
    file_sizes = {p: norm_sz for norm_sz, entries in by_size.items() for p, _, _ in entries}
    eligible   = [p for p in all_rom_files if p not in empty_set and p not in unread_set]
    suspected  = _build_suspected(eligible, confirmed_paths, file_sizes)
    suspected_paths: set[Path] = {p for g in suspected for p in g}
    suspected.extend(_build_size_similar(by_size, confirmed_paths, suspected_paths))

    print()
    if near_collisions:
        cprint(C.YELLOW, f"  {len(near_collisions)} CRC32 collision(s) resolved by SHA-1"
                         " (same CRC32, different content — not duplicates):")
        for sz, crc, paths in near_collisions:
            cprint(C.YELLOW, f"    CRC32:{crc} size:{sz:,}B")
            for p in sorted(paths):
                cprint(C.GRAY, f"      - {p}")
        print()

    _report_duplicates(confirmed, suspected, empty_files, unreadable, all_rom_files, dry_run=dry_run)

def _report_duplicates(confirmed: list[list[tuple[Path, str, str, int]]],
                       suspected: list[list[Path]],
                       empty_files: list[Path],
                       unreadable: list[Path],
                       all_rom_files: list[Path],
                       dry_run: bool = True) -> None:
    """Print the duplicate report and prompt for deletion."""

    if empty_files:
        cprint(C.YELLOW, f"  {len(empty_files)} empty (0-byte) file(s) — likely corrupt or placeholder:")
        for p in sorted(empty_files):
            cprint(C.YELLOW, f"    - {p}")
        print()

    if unreadable:
        cprint(C.YELLOW, f"  {len(unreadable)} file(s) could not be read:")
        for p in sorted(unreadable):
            cprint(C.YELLOW, f"    - {p}")
        print()

    if not confirmed:
        cprint(C.GREEN, "  No exact duplicates found!")
    else:
        cprint(C.DRED, f"  Found {len(confirmed)} group(s) of confirmed duplicate ROMs:")
        total_wasted = 0
        for group in sorted(confirmed, key=lambda g: sorted(p for p, _, _, _ in g)[0]):
            sizes  = [sz  for _, _, _, sz  in group]
            crc    = group[0][1]
            sha    = group[0][2]
            wasted = sum(sizes) - min(sizes)
            total_wasted += wasted
            hash_tag = f"CRC32:{crc}  SHA1:{sha[:10]}…"
            cprint(C.DRED,
                   f"\n  {hash_tag}  "
                   f"({len(group)} copies, {wasted:,} bytes wasted)")
            for p, _, _, sz in sorted(group, key=lambda t: t[0]):
                cprint(C.RED, f"    - {p}  ({sz:,} bytes)")
        print()
        cprint(C.YELLOW,
               f"  Total recoverable space: {total_wasted / (1024 * 1024):.1f} MB")

    # -- Suspected duplicates (same title, different bytes) ---------------
    if suspected:
        print()
        cprint(C.DYELLOW, f"  {len(suspected)} group(s) of same-title ROMs with different content:")
        cprint(C.GRAY,    "  (different region/version/patch — review manually)")
        for group in sorted(suspected, key=lambda g: g[0]):
            cprint(C.DYELLOW, f"\n  '{normalize(group[0].stem)}'")
            for p in group:
                try:
                    sz = p.stat().st_size
                except OSError:
                    sz = 0
                cprint(C.YELLOW, f"    - {p}  ({sz:,} bytes)")
        print()

    dup_paths    = {fp for g in confirmed for fp, _, _, _ in g}
    empty_set    = set(empty_files)
    unread_set   = set(unreadable)
    n_unique     = sum(
        1 for p in all_rom_files
        if p not in dup_paths
        and p not in empty_set
        and p not in unread_set
    )
    print()
    distinct_games = n_unique + len(confirmed)  # unique + 1 per dup group
    cprint(C.CYAN, f"  Total scanned    : {len(all_rom_files)}")
    cprint(C.CYAN, f"  Distinct games   : {distinct_games}")
    cprint(C.CYAN, f"  Unique files     : {n_unique}")
    cprint(C.CYAN, f"  Exact duplicates : {len(confirmed)}")
    cprint(C.CYAN, f"  Same-title pairs : {len(suspected)}")
    cprint(C.CYAN, f"  Empty files      : {len(empty_files)}")
    cprint(C.CYAN, f"  Unreadable       : {len(unreadable)}")
    cprint(C.CYAN, "=============================================")
    print()

    if not confirmed and not suspected:
        return

    if not sys.stdout.isatty():
        return  # skip interactive prompts in piped/CI contexts

    if confirmed:
        confirmed_paths_only = [[p for p, _, _, _ in g] for g in confirmed]
        _prompt_delete_group("CLEANUP — EXACT DUPLICATES", confirmed_paths_only, dry_run)

    if suspected:
        cprint(C.DYELLOW,
               "  Same-title pairs have DIFFERENT content (regional variant / patch).")
        cprint(C.DYELLOW,
               "  Review carefully — you may want to keep both versions.")
        _prompt_delete_group("CLEANUP — SAME-TITLE PAIRS", suspected, dry_run)

# Keep-strategy sort keys: first element after sorting is the file to KEEP.
_REGION_KEEP_PRIORITY: dict[str, int] = {
    "usa": 0, "world": 1, "europe": 2, "japan": 3,
}

def _region_keep_key(p: Path) -> tuple:
    r = region_of(p.name) or ""
    return (_REGION_KEEP_PRIORITY.get(r, 99), len(p.name), p.name)

# Bad-dump / pre-release tags (GoodTools + No-Intro). Auto-deleted when a clean copy exists.
_BAD_TAG_RE = re.compile(
    r'[\(\[]\s*(?:Beta|Demo|Proto(?:type)?|Sample|Hack|b|h|t|o)\s*[\d.]*\s*[\)\]]',
    re.IGNORECASE,
)

def _split_bad_tags(group: list[Path]) -> tuple[list[Path], list[Path]]:
    """Return (clean, bad) split on _BAD_TAG_RE.
    If all are bad-tagged, returns (group, []) — nothing obviously superior.
    """
    clean = [p for p in group if not _BAD_TAG_RE.search(p.name)]
    bad   = [p for p in group if     _BAD_TAG_RE.search(p.name)]
    if not clean:           # all are bad-tagged — don't auto-delete any
        return group, []
    return clean, bad

_KEEP_STRATEGIES: dict[str, tuple[str, "Callable[[Path], tuple] | None"]] = {
    "1": ("shortest filename",                        lambda p: (len(p.name), p.name)),
    "2": ("smallest file size",                       lambda p: (p.stat().st_size, p.name)),
    "3": ("oldest file",                              lambda p: (p.stat().st_mtime, p.name)),
    "4": ("newest file",                              lambda p: (-p.stat().st_mtime, p.name)),
    "5": ("preferred region (USA > World > Europe > Japan)", _region_keep_key),
    "6": ("choose per group (interactive)",           None),
}

def _prompt_delete_group(title: str,
                         groups: list[list[Path]],
                         dry_run: bool) -> None:
    """Interactive deletion prompt: review/auto-strategy/skip → preview → confirm."""
    print()
    cprint(C.CYAN, "─" * 45)
    cprint(C.CYAN, f"  {title}")
    cprint(C.CYAN, "─" * 45)
    print()

    action_ch = prompt_choice("  What would you like to do?", {
        "r": f"{C.CYAN}Review each group{C.RESET}  — choose which file to keep per group",
        "a": f"{C.YELLOW}Auto-select{C.RESET}        — apply a keep-strategy to all groups",
        "n": f"{C.GREEN}Skip{C.RESET}               — leave everything in place",
    })
    if action_ch == "n":
        cprint(C.GRAY, "  No files were changed.")
        return
    per_group = action_ch == "r"
    print()

    # Bad-tag pre-filter: auto-schedule Beta/Demo/Proto/hack files for deletion.
    auto_delete: list[Path] = []
    filtered_groups: list[list[Path]] = []
    for group in groups:
        clean, bad = _split_bad_tags(group)
        auto_delete.extend(bad)
        if len(clean) > 1:
            filtered_groups.append(clean)

    if auto_delete:
        cprint(C.DYELLOW,
               f"  {len(auto_delete)} bad-tagged file(s) (Beta/Demo/Proto/hack) "
               "will be auto-deleted:")
        for p in sorted(auto_delete):
            cprint(C.YELLOW, f"    AUTO-DELETE  {p.name}  ({p.parent})")
        print()
    # Extension conflicts (e.g. .smc vs .sfc): one-time format question per pair.
    if filtered_groups:
        ext_pref: dict[frozenset[str], str | None] = {}
        resolved: list[list[Path]] = []
        for group in filtered_groups:
            exts = {p.suffix.lower() for p in group}
            if len(exts) > 1:
                ext_key = frozenset(exts)
                if ext_key not in ext_pref:
                    cprint(C.DYELLOW,
                           f"  Extension conflict ({', '.join(sorted(exts))}) "
                           f"— first seen in group '{_norm_for_dedup(group[0].stem)}':")
                    for p in sorted(group):
                        try:
                            sz = p.stat().st_size
                        except OSError:
                            sz = 0
                        cprint(C.GRAY, f"    {p.name}  ({sz:,} bytes)")
                    ext_pref[ext_key] = _dedup_ask_ext(sorted(exts))
                    print()
                keep_ext = ext_pref[ext_key]
                if keep_ext is None:
                    resolved.append(group)   # skipped — leave intact
                    continue
                rejected  = [p for p in group if p.suffix.lower() != keep_ext]
                remaining = [p for p in group if p.suffix.lower() == keep_ext]
                auto_delete.extend(rejected)
                if len(remaining) > 1:
                    resolved.append(remaining)
                # len == 1: single copy left, nothing more to decide
            else:
                resolved.append(group)
        filtered_groups = resolved

    plan: list[tuple[list[Path], list[Path]]] = []
    strategy_label = ""
    if filtered_groups:
        if per_group:
            strategy_label = "choose per group"
            sort_key = None
        else:
            auto_strategies = {k: v for k, v in _KEEP_STRATEGIES.items() if k != "6"}
            strat_ch = prompt_choice("  Which file to keep from each group?", {
                k: f"{C.CYAN}{lbl}{C.RESET}" for k, (lbl, _) in auto_strategies.items()
            })
            strategy_label, sort_key = _KEEP_STRATEGIES[strat_ch]
        print()

        if sort_key is None:
            # ── Interactive: decide per group ─────────────────────────
            for group in filtered_groups:
                cprint(C.CYAN, f"\n  [{_norm_for_dedup(group[0].stem)}]")
                for i, p in enumerate(group, 1):
                    try:
                        sz = p.stat().st_size
                    except OSError:
                        sz = 0
                    print(f"    [{i}] {p.name}  ({sz:,} bytes)  ({p.parent})")
                while True:
                    try:
                        raw = input(f"  Keep which? (1-{len(group)}, or e.g. 1,3 to keep multiple, s=skip): ").strip().lower()
                    except KeyboardInterrupt:
                        print()
                        raise
                    if raw == 's':
                        break
                    parts = [p.strip() for p in raw.split(",")]
                    indices = []
                    valid = True
                    for part in parts:
                        if part.isdigit() and 1 <= int(part) <= len(group):
                            idx = int(part) - 1
                            if idx not in indices:
                                indices.append(idx)
                        else:
                            valid = False
                            break
                    if valid and indices:
                        keeps = [group[i] for i in indices]
                        to_del = [p for p in group if p not in keeps]
                        if to_del:
                            plan.append((keeps, to_del))
                        break
                    print("  Invalid choice.")
            print()
        else:
            for group in filtered_groups:
                ordered = sorted(group, key=sort_key)
                plan.append(([ordered[0]], ordered[1:]))

    n_to_delete = len(auto_delete) + sum(len(d) for _, d in plan)
    if strategy_label:
        cprint(C.CYAN, f"  Preview — strategy: {strategy_label}")
    print()
    for keeps, to_del in plan:
        for keep in keeps:
            cprint(C.GREEN, f"  KEEP    {keep.name}  ({keep.parent})")
        for p in to_del:
            cprint(C.RED, f"  DELETE  {p.name}  ({p.parent})")
    print()
    cprint(C.YELLOW, f"  {n_to_delete} file(s) will be permanently deleted.")
    print()

    confirm_ch = prompt_choice("  Proceed?", {
        "y": f"{C.RED}Yes, delete now{C.RESET}",
        "n": f"{C.GREEN}No, cancel{C.RESET}",
    })
    if confirm_ch == "n":
        cprint(C.GRAY, "  Cancelled — no files were changed.")
        return

    print()
    if dry_run:
        cprint(C.MAGENTA, "  [DRY RUN] No files were changed.")
        cprint(C.MAGENTA, "  Re-run with --no-dry-run to apply.")
        print()
        return

    deleted = 0
    for path in auto_delete:
        try:
            path.unlink()
            cprint(C.RED, f"  DELETED {path}")
            deleted += 1
        except OSError as e:
            cprint(C.YELLOW, f"  FAILED  {path}: {e}")
    for keeps, to_del in plan:
        for keep in keeps:
            cprint(C.GREEN, f"  KEPT    {keep.name}")
        for path in to_del:
            try:
                path.unlink()
                cprint(C.RED, f"  DELETED {path}")
                deleted += 1
            except OSError as e:
                cprint(C.YELLOW, f"  FAILED  {path}: {e}")
    print()
    cprint(C.CYAN, f"  Done — {deleted} file(s) deleted.")
    print()

# =============================================================================
# ROM COMPLETENESS CHECKER
# Independent of check_duplicates — _hash_file and _dat_crc32 must never mix.
# =============================================================================
# Narrower than ROM_EXTENSIONS: cartridge systems only.
# Disc systems (cue+bin, TOC, etc.) need multi-file verification — out of scope.
_DAT_ROM_EXTENSIONS: frozenset[str] = frozenset({
    ".nes", ".fds",        # NES / Famicom Disk System
    ".sfc", ".smc",        # SNES (headerless / headered)
    ".gb", ".gbc", ".gba", # Game Boy / Color / Advance
    ".gg",                 # Sega Game Gear
    ".sms",                # Sega Master System
    ".md", ".smd", ".gen", # Sega Mega Drive / Genesis (raw / SMD interleaved)
})

# No-Intro retail filter — excludes pre-release, unlicensed, hacks, bad dumps.
# Covers both modern No-Intro parenthesized tags and legacy GoodTools bracket tags.
_DAT_RETAIL_PAREN_RE: re.Pattern = re.compile(
    r'\((?:Beta(?:[- ]\d+)?|Proto(?:type)?|Alpha|Demo|Sample|Unl|Unlicensed|Hack)\)',
    re.IGNORECASE,
)
_DAT_RETAIL_BRACKET_RE: re.Pattern = re.compile(
    r'\[(?:b\d*|h[^\]]*|t\d*|p\d*|o\d*)\]',
    re.IGNORECASE,
)

# Human-readable labels for the completeness report header.
_COMPLETENESS_REGION_LABELS: dict[str, str] = {
    "usa":             "USA / North America  (1G1R)",
    "europe":          "Europe  (1G1R)",
    "japan":           "Japan  (1G1R)",
    "japan_exclusive": "Japan exclusives  (never released in USA / Europe / World)",
    "all":             "All regions  (no 1G1R — full set)",
}

# SMD de-interleaving constants.
_SMD_BLOCK_SIZE: int = 16_384   # 16 KB per interleaved block
_SMD_HALF_SIZE:  int = _SMD_BLOCK_SIZE // 2   # 8 KB per half

@dataclasses.dataclass(frozen=True)
class DatGame:
    """One cartridge entry from a No-Intro Logiqx XML DAT file.
    crc32 is uppercase 8-char hex.  clone_of is "" for parents, parent name for clones.
    """
    name:     str
    crc32:    str
    clone_of: str

# ---------------------------------------------------------------------------
# Retail filter
# ---------------------------------------------------------------------------
def _is_retail(name: str) -> bool:
    """Return True if the game name passes the retail filter (no pre-release/hack/bad-dump tags)."""
    return (
        not _DAT_RETAIL_PAREN_RE.search(name)
        and not _DAT_RETAIL_BRACKET_RE.search(name)
    )

def _smd_deinterleave(data: bytes) -> bytes:
    """Convert SMD-interleaved bytes to raw Mega Drive ROM bytes (16 KB blocks)."""
    if not data:
        return b""
    result = bytearray(len(data))
    for block_start in range(0, len(data), _SMD_BLOCK_SIZE):
        block = data[block_start : block_start + _SMD_BLOCK_SIZE]
        blen  = len(block)
        half  = blen // 2
        if half == 0:
            result[block_start] = block[0]
            continue
        result[block_start     : block_start + blen : 2] = block[half:]   # even positions
        result[block_start + 1 : block_start + blen : 2] = block[:half]   # odd  positions
    return bytes(result)

# ---------------------------------------------------------------------------
# DAT-matchable CRC32 — used ONLY by check_completeness (never by check_duplicates).
# ---------------------------------------------------------------------------
def _dat_crc32(path: Path, chunk_size: int = 1 << 20) -> str | None:
    """Return the No-Intro DAT-matchable CRC32 (uppercase 8-char hex) for a ROM, or None on error.
    Strips format-specific headers (.nes iNES, .fds fwNES, .smc/.sfc SMC copier, .smd SMD).
    """
    try:
        ext = path.suffix.lower()

        # .smd must be fully loaded for de-interleaving.
        if ext == ".smd":
            raw = path.read_bytes()
            # SMD header: bytes 8–9 == 0xAA 0xBB; absent → treat as raw binary.
            if len(raw) >= 512 and len(raw) >= 10 and raw[8] == 0xAA and raw[9] == 0xBB:
                payload = _smd_deinterleave(raw[512:])
            else:
                payload = raw
            return f"{zlib.crc32(payload) & 0xFFFFFFFF:08X}"

        offset = 0

        if ext == ".nes":
            # iNES: 16-byte header (magic b"NES\x1a"); +512 bytes if trainer flag set.
            try:
                with open(path, "rb") as _f:
                    hdr = _f.read(16)
            except OSError:
                hdr = None
            if hdr and len(hdr) >= 8 and hdr[:4] == b"NES\x1a":
                trainer = bool(hdr[6] & 0x04)
                offset = 16 + (512 if trainer else 0)

        elif ext == ".fds":
            # fwNES: 16-byte header (magic b"FDS\x1a").
            try:
                with open(path, "rb") as _f:
                    hdr = _f.read(4)
            except OSError:
                hdr = None
            if hdr and hdr[:4] == b"FDS\x1a":
                offset = 16

        elif ext in (".smc", ".sfc"):
            # SMC copier header: 512 bytes when size % 1024 == 512.
            try:
                size = path.stat().st_size
            except OSError:
                size = 0
            if size > 512 and size % 1024 == 512:
                offset = 512

        crc = 0
        with open(path, "rb") as f:
            if offset:
                f.seek(offset)
            while chunk := f.read(chunk_size):
                crc = zlib.crc32(chunk, crc)
        return f"{crc & 0xFFFFFFFF:08X}"

    except Exception:
        return None

# ---------------------------------------------------------------------------
# Logiqx XML DAT parser
# ---------------------------------------------------------------------------
def parse_dat(dat_path: Path) -> list[DatGame]:
    """Parse a No-Intro Logiqx XML DAT file; return DatGame list.
    Accepts <game> or <machine> elements under a <datafile> root.
    Raises FileNotFoundError, ET.ParseError, or ValueError on bad input.
    """
    tree = ET.parse(dat_path)
    root = tree.getroot()

    # Logiqx root must be <datafile> (case-insensitive in some community DATs).
    if root.tag.lower() != "datafile":
        raise ValueError(
            f"Not a Logiqx XML DAT (expected <datafile> root, found <{root.tag}>).\n"
            "Only No-Intro Logiqx XML format is supported.\n"
            "Download DAT files from https://dat-o-matic.no-intro.org"
        )

    games: list[DatGame] = []
    for elem in root:
        if elem.tag.lower() not in ("game", "machine"):
            continue

        game_name = (elem.get("name") or "").strip()
        clone_of  = (elem.get("cloneOf") or "").strip()
        if not game_name:
            continue

        # Take the first <rom> child with a valid crc attribute.
        crc = ""
        for rom_elem in elem:
            if rom_elem.tag.lower() != "rom":
                continue
            raw_crc = (rom_elem.get("crc") or "").strip()
            if not raw_crc:
                continue
            try:
                crc = f"{int(raw_crc, 16):08X}"   # normalise to uppercase 8-char hex
            except ValueError:
                continue   # malformed CRC — try the next <rom> element
            break          # first valid CRC wins

        if crc:
            games.append(DatGame(name=game_name, crc32=crc, clone_of=clone_of))

    return games

# ---------------------------------------------------------------------------
# 1G1R selection and region filtering
# ---------------------------------------------------------------------------
def _build_parent_groups(games: list[DatGame]) -> dict[str, list[DatGame]]:
    """Group DatGames by their parent entry.  Key is clone_of or the game's own name.
    Orphan clones (parent absent after retail filter) form single-member groups.
    """
    groups: dict[str, list[DatGame]] = defaultdict(list)
    for game in games:
        key = game.clone_of if game.clone_of else game.name
        groups[key].append(game)
    return dict(groups)

def _pick_best_in_group(group: list[DatGame],
                        region_priority: list[str]) -> DatGame:
    """Select the best DatGame from a parent group by region_priority index.
    Games not in priority list rank last; iteration order breaks ties (parent wins).
    """
    priority_index: dict[str, int] = {r: i for i, r in enumerate(region_priority)}
    sentinel = len(region_priority)

    def _rank(game: DatGame) -> int:
        r = region_of(game.name)    # reuse the existing region_of() function
        return priority_index.get(r, sentinel) if r else sentinel

    return min(group, key=_rank)

# Per-mode configuration: which regions include a group, which exclude it,
# and the 1G1R priority list.  Defined at module level to avoid
# reconstructing dicts on every call.
_MODE_INCLUDE: dict[str, set[str]] = {
    "usa":             {"usa", "world"},
    "europe":          {"europe", "world"},
    "japan":           {"japan", "world"},
    "japan_exclusive": {"japan"},
}
_MODE_EXCLUDE: dict[str, set[str]] = {
    "usa":             set(),
    "europe":          set(),
    "japan":           set(),
    "japan_exclusive": {"usa", "europe", "world"},
}
_MODE_PRIORITY: dict[str, list[str]] = {
    "usa":             ["usa", "world", "europe", "japan"],
    "europe":          ["europe", "world", "usa", "japan"],
    "japan":           ["japan", "world"],
    "japan_exclusive": ["japan"],
}

def _filter_and_select(
    games: list[DatGame],
    region_mode: str,
) -> list[DatGame]:
    """Apply retail filter then select entries by region_mode.
    usa/europe/japan: 1G1R — groups with a matching or World release, best region picked.
    japan_exclusive:  groups where NO member has a USA/EUR/World release.
    all:              all retail entries, no 1G1R.
    """
    retail = [g for g in games if _is_retail(g.name)]

    if region_mode == "all":
        return retail

    include_any = _MODE_INCLUDE[region_mode]
    exclude_any = _MODE_EXCLUDE[region_mode]
    priority    = _MODE_PRIORITY[region_mode]

    result: list[DatGame] = []
    for group in _build_parent_groups(retail).values():
        group_regions: set[str | None] = {region_of(g.name) for g in group}

        # japan_exclusive: reject groups that contain any USA/EUR/World release.
        if exclude_any and group_regions & exclude_any:
            continue

        # Require at least one member from an included region.
        if not (group_regions & include_any):
            continue

        result.append(_pick_best_in_group(group, priority))

    return result

# ---------------------------------------------------------------------------
# Completeness checker — main entry point
# ---------------------------------------------------------------------------
def check_completeness(
    dat_path:    Path,
    rom_dir:     Path,
    region_mode: str,
    script_dir:  Path,
    want_list:   bool = False,
) -> None:
    """Check a ROM folder against a No-Intro Logiqx XML DAT file.
    Writes a timestamped CSV (FOUND/MISSING/UNUSED) next to the script and
    prints a terminal summary.  want_list=True also writes a plain-text list
    of MISSING titles.  region_mode: "usa"|"europe"|"japan"|"japan_exclusive"|"all".
    """
    print()
    cprint(C.CYAN, "=============================================")
    cprint(C.CYAN, "  ROM COMPLETENESS CHECK")
    cprint(C.CYAN, "=============================================")
    print()

    # ── Validate ROM folder first (fast) before doing any expensive DAT work ──
    if not rom_dir.is_dir():
        cprint(C.DRED, f"  ERROR: ROM folder not found: {rom_dir}")
        sys.exit(1)

    # ── Parse DAT ────────────────────────────────────────────────────────────
    cprint(C.GRAY, f"  Parsing DAT: {dat_path.name}")
    try:
        all_games = parse_dat(dat_path)
    except FileNotFoundError:
        cprint(C.DRED, f"  ERROR: DAT file not found: {dat_path}")
        sys.exit(1)
    except ET.ParseError as exc:
        cprint(C.DRED, f"  ERROR: Malformed XML in DAT file: {exc}")
        sys.exit(1)
    except ValueError as exc:
        cprint(C.DRED, f"  ERROR: {exc}")
        sys.exit(1)

    if not all_games:
        cprint(C.YELLOW, "  No games found in DAT file — check the file format.")
        return

    cprint(C.GRAY, f"    {len(all_games)} entries in DAT (before filtering)")

    # ── Apply retail filter + region mode ────────────────────────────────────
    target_games = _filter_and_select(all_games, region_mode)
    if not target_games:
        cprint(C.YELLOW,
               f"  No games matched region mode '{region_mode}' after filtering.")
        return

    region_label = _COMPLETENESS_REGION_LABELS.get(region_mode, region_mode)
    cprint(C.GRAY,
           f"    {len(target_games)} target entries after retail filter "
           f"and region selection")
    cprint(C.GRAY, f"    Mode: {region_label}")
    print()

    # Build the primary lookup: crc32 → DatGame.
    # Duplicate CRCs in the DAT (should not happen, but be defensive) keep last.
    dat_by_crc: dict[str, DatGame] = {g.crc32: g for g in target_games}

    # ── Scan ROM folder ──────────────────────────────────────────────────────

    rom_files: list[Path] = sorted(
        p for p in rom_dir.rglob("*")
        if p.is_file() and p.suffix.lower() in _DAT_ROM_EXTENSIONS
    )
    cprint(C.GRAY, f"  Scanning {len(rom_files)} ROM file(s) in: {rom_dir}")
    print()

    # ── Hash ROM files and match against DAT ─────────────────────────────────
    found:   list[tuple[DatGame, Path]] = []   # (dat_entry, rom_path)
    unused:  list[Path]                  = []   # ROM with no DAT match
    unread:  list[Path]                  = []   # ROM that could not be hashed
    matched_crcs: set[str]               = set()

    n_total = len(rom_files)
    for i, rom_path in enumerate(rom_files, 1):
        print(progress_bar(i, n_total, label="Hashing   "), end="", flush=True)
        crc = _dat_crc32(rom_path)
        if crc is None:
            unread.append(rom_path)
        elif crc in dat_by_crc:
            found.append((dat_by_crc[crc], rom_path))
            matched_crcs.add(crc)
        else:
            unused.append(rom_path)
    print()   # newline after progress bar

    # ── Determine MISSING (DAT entries with no matched ROM) ──────────────────
    missing: list[DatGame] = [g for g in target_games if g.crc32 not in matched_crcs]

    # ── Report ───────────────────────────────────────────────────────────────
    _report_completeness(
        found         = found,
        missing       = missing,
        unused        = unused,
        unread        = unread,
        region_mode   = region_mode,
        dat_path      = dat_path,
        rom_dir       = rom_dir,
        target_total  = len(target_games),
        script_dir    = script_dir,
        want_list     = want_list,
        system_name   = rom_dir.name,
    )

def _report_completeness(
    found:        list[tuple[DatGame, Path]],
    missing:      list[DatGame],
    unused:       list[Path],
    unread:       list[Path],
    region_mode:  str,
    dat_path:     Path,
    rom_dir:      Path,
    target_total: int,
    script_dir:   Path,
    want_list:    bool,
    system_name:  str = "",
) -> None:
    """Write CSV report + optional want-list, then print a terminal summary."""
    ts          = datetime.now().strftime("%Y%m%d_%H%M%S")
    # Sanitise system_name for use in a filename: keep only alphanumeric, dash, underscore.
    safe_system = re.sub(r"[^\w\-]", "_", system_name).strip("_") if system_name else ""
    stem        = f"completeness_{safe_system}_{ts}" if safe_system else f"completeness_{ts}"
    csv_path    = script_dir / f"{stem}.csv"
    wl_stem     = f"wantlist_{safe_system}_{ts}" if safe_system else f"wantlist_{ts}"
    wl_path: Path | None = script_dir / f"{wl_stem}.txt" if want_list else None

    # ── CSV ──────────────────────────────────────────────────────────────────
    with open(csv_path, "w", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh)
        writer.writerow(["Status", "Game Name", "Region", "Your File"])

        for dat_game, rom_path in sorted(found, key=lambda t: t[0].name.lower()):
            r = region_of(dat_game.name) or ""
            writer.writerow(["FOUND", dat_game.name, r, rom_path.name])

        for dat_game in sorted(missing, key=lambda g: g.name.lower()):
            r = region_of(dat_game.name) or ""
            writer.writerow(["MISSING", dat_game.name, r, ""])

        for rom_path in sorted(unused, key=lambda p: p.name.lower()):
            writer.writerow(["UNUSED", "", "", rom_path.name])

    # ── Want-list ─────────────────────────────────────────────────────────────
    if wl_path is not None and missing:
        with open(wl_path, "w", encoding="utf-8") as fh:
            fh.write(f"# Missing ROMs — {dat_path.name}\n")
            fh.write(f"# Mode: {_COMPLETENESS_REGION_LABELS.get(region_mode, region_mode)}\n")
            fh.write(f"# Generated: {datetime.now(timezone.utc).isoformat()}\n\n")
            for game in sorted(missing, key=lambda g: g.name.lower()):
                fh.write(f"{game.name}\n")

    # ── Terminal summary ─────────────────────────────────────────────────────
    n_found   = len(found)
    n_missing = len(missing)
    n_unused  = len(unused)
    n_unread  = len(unread)
    pct       = (n_found / target_total * 100) if target_total else 0.0

    print()
    cprint(C.CYAN, "=============================================")
    cprint(C.CYAN, "  COMPLETENESS REPORT")
    cprint(C.CYAN, f"  DAT  : {dat_path.name}")
    cprint(C.CYAN, f"  ROMs : {rom_dir}")
    cprint(C.CYAN, f"  Mode : {_COMPLETENESS_REGION_LABELS.get(region_mode, region_mode)}")
    cprint(C.CYAN, "=============================================")
    cprint(C.GREEN,  f"  Found   : {n_found:>5} / {target_total}  ({pct:.1f}%)")
    cprint(C.DRED,   f"  Missing : {n_missing:>5}")
    cprint(C.YELLOW, f"  Unused  : {n_unused:>5}  (no DAT match — ROM hack / bad dump?)")
    if n_unread:
        cprint(C.YELLOW, f"  Unread  : {n_unread:>5}  (could not hash)")
    cprint(C.CYAN, "=============================================")
    print()
    cprint(C.GREEN, f"  CSV saved to : {csv_path}")
    if wl_path is not None:
        if missing:
            cprint(C.GREEN, f"  Want-list    : {wl_path}")
        else:
            cprint(C.GRAY,  "  (no want-list written — collection is complete!)")
    print()

def _detect_systems(roms_base: Path, system_arg: str,
                    rom_ext_filter: set[str] | None = None) -> tuple[list[str], bool]:
    """Return (common, single_system) based on roms_base layout and --system arg.
    common        : list of system-folder names (or [system] in single mode)
    single_system : True when ROMs live directly in roms_base (no subfolders)
    rom_ext_filter: if given, used to detect ROM files in base dir (duplicate mode);
                    if None, any non-.sbi file counts (cover-sync mode).
    """
    rom_subs = {p.name for p in roms_base.iterdir() if p.is_dir()}

    # any() short-circuits on first hit — no need to stat every file
    if rom_ext_filter is not None:
        has_roms_in_base = any(
            p.is_file() and p.suffix.lower() in rom_ext_filter
            for p in roms_base.iterdir()
        )
    else:
        has_roms_in_base = any(
            p.is_file() and p.suffix.lower() != ".sbi"
            for p in roms_base.iterdir()
        )

    system = system_arg.strip().lower()

    if system and system in rom_subs:
        # --system names a subfolder → treat as single-system within multi layout
        return [system], False
    elif system or has_roms_in_base:
        # --system given (no matching subfolder), OR ROM files live directly in base.
        # The presence of other subdirectories (e.g. asset/, convert/) is irrelevant —
        # if there are ROM files in the root, this is a single-system layout.
        return [system] if system else [], True
    else:
        return sorted(rom_subs), False

def _resize_pass(
    base: Path, cfg: SyncConfig, counters: Counters,
    target_dims: str = "512x512",
    valid_dims: frozenset[str] | None = None,
    label: str = "JPG",
    gravity: str = "center",
) -> None:
    """Resize all JPGs under base that aren't already the target size."""
    if not cfg.magick:
        return
    magick = cfg.magick  # narrowed to str after the guard above
    if valid_dims is None:
        valid_dims = frozenset({target_dims})
    all_jpgs = list({                               # set() deduplicates on
        p                                           # case-insensitive FSes
        for pattern in ("*.jpg", "*.jpeg", "*.JPG", "*.JPEG")
        for p in base.rglob(pattern)
        if p.is_file()
    })
    cprint(C.CYAN, f"\n--- Checking {len(all_jpgs)} {label}(s) for resize (target {target_dims}) ---")

    dims_map         = batch_identify(cfg.magick, all_jpgs, label="Identifying")
    needs_resize:     list[Path] = []
    identify_skipped: int        = 0
    for jpg, dims in dims_map.items():
        if dims is None:
            identify_skipped += 1
            cprint(C.YELLOW, f"  SKIP (identify failed)  {jpg}")
        elif dims not in valid_dims:
            needs_resize.append(jpg)

    already_ok = len(all_jpgs) - len(needs_resize) - identify_skipped
    cprint(C.CYAN, f"  {len(needs_resize)} to resize, {already_ok} already correct"
                   + (f", {identify_skipped} skipped (identify failed)" if identify_skipped else ""))

    if not needs_resize:
        return

    print_lock = threading.Lock()
    tracker    = _ProgressTracker(len(needs_resize), label="Resizing  ")

    def resize_one(jpg: Path):
        try:
            magick_resize(magick, str(jpg), str(jpg), dims=target_dims, gravity=gravity)
            counters.inc("converted")
            _progress_ok(tracker, print_lock, f"  RESIZED  {jpg}", color=C.DCYAN)
        except Exception as e:
            tracker.tick()
            with print_lock:
                cprint(C.DRED, f"  RESIZE FAIL  {jpg}: {e}")

    _run_thread_pool(cfg.parallel_jobs, needs_resize, resize_one,
                     interrupt_msg="  Interrupted — cancelling remaining resize operations...")
    print()  # newline after progress bar

def _print_counters_block(
    counters: Counters,
    failed: list[tuple[str, str, str]],
    label: str,            # "cover" | "background"
    dup_label: str,        # "covers" | "BGs"
    delete_orphans: bool,
    dry_run: bool,
    *,
    fail_tip: str = "",
    extra_fail_keys: "dict[str, str] | None" = None,
) -> None:
    """Shared stats block for covers and backgrounds.
    extra_fail_keys: optional {substring: display_label} for additional failure
                     categories (e.g. "no hero" for background-specific reporting).
    """
    cprint(C.YELLOW, f"  Renamed (or would) : {counters.renamed}")
    if counters.duplicates:
        hint = "run --delete-orphans to remove" if not delete_orphans else "deleted"
        cprint(C.DRED, f"  Duplicate {dup_label:<7}: {counters.duplicates} ({hint})")
    cprint(C.CYAN,  f"  Downloaded         : {counters.downloaded}")
    cprint(C.GRAY,  f"  Skipped (exist)    : {counters.skipped}")
    if failed:
        n_no_match = sum(1 for _, _, r in failed if "no match" in r)
        n_dl_fail  = sum(1 for _, _, r in failed if "download failed" in r)
        if n_dl_fail:
            cprint(C.DRED, f"  Download failures  : {n_dl_fail}")
        if n_no_match:
            cprint(C.DRED, f"  No repo match      : {n_no_match}")
        for substr, disp in (extra_fail_keys or {}).items():
            n = sum(1 for _, _, r in failed if substr in r)
            if n:
                cprint(C.DRED, f"  {disp:<19}: {n}")
        cprint(C.DRED, f"  Missing {label}s     : {len(failed)} total")
    cprint(C.DCYAN, f"  Converted+Resized  : {counters.converted}")
    if delete_orphans:
        cprint(C.DRED, f"  Deleted (or would) : {counters.deleted}")
    else:
        cprint(C.RED,  f"  Unmatched kept     : {counters.missing}")

def _print_summary(
    counters: Counters,
    common: list[str],
    cfg: SyncConfig,
    failed_covers: list[tuple[str, str, str]],
    bg_counters: Counters | None = None,
    failed_bgs: list[tuple[str, str, str]] | None = None,
) -> None:
    """Print run summary box, failed-covers report, and optional backgrounds summary."""
    dry_run        = cfg.dry_run
    delete_orphans = cfg.delete_orphans

    print()
    cprint(C.CYAN, "=============================================")
    if dry_run:
        cprint(C.MAGENTA, "  DRY RUN complete - nothing was changed")
        cprint(C.MAGENTA, "  Run with --no-dry-run to apply changes")
    else:
        cprint(C.GREEN, "  LIVE RUN complete")
    cprint(C.CYAN, f"  Download mode      : {cfg.download_mode}")
    _STYLE_LABELS = {
        "with_logo":    "With logo (libretro/LaunchBox)",
        "without_logo": "Without logo (SGDB)",
        "game_logo":    "Game logo (libretro/LaunchBox/SGDB)",
    }
    cprint(C.CYAN, f"  Cover style        : {_STYLE_LABELS.get(cfg.cover_style, cfg.cover_style)}")
    cprint(C.CYAN, f"  Folders processed  : {len(common)}")
    _print_counters_block(counters, failed_covers, "cover", "covers",
                          delete_orphans, dry_run)
    if not delete_orphans and counters.missing:
        cprint(C.GRAY, "  Tip: run with --delete-orphans to remove them")
    cprint(C.CYAN, "=============================================")

    _print_failed_items("cover", failed_covers, dry_run,
                        tip="covers can be added manually to the system covers folder, "
                            "renamed to match the ROM filename exactly (e.g. game.jpg).")
    print()

    # ----------------------------------------------------------------
    # Backgrounds summary (only shown when --backgrounds was used)
    # ----------------------------------------------------------------
    if bg_counters is not None:
        print()
        cprint(C.CYAN, "=============================================")
        cprint(C.CYAN, "  BACKGROUNDS SUMMARY")
        _BG_STYLE_LABELS = {"fanart": "Fanart/Heroes", "boxart": "Box art (letterboxed)"}
        cprint(C.CYAN,
               f"  BG source          : {_BG_STYLE_LABELS.get(cfg.bg_style, cfg.bg_style)}")
        cprint(C.CYAN, "=============================================")
        _print_counters_block(
            bg_counters, failed_bgs or [], "background", "BGs",
            delete_orphans, dry_run,
            extra_fail_keys={"no game match": "No SGDB match", "no hero": "No hero found"},
        )
        cprint(C.CYAN, "=============================================")
        _print_failed_items("background", failed_bgs or [], dry_run)
        print()

def _print_failed_items(
    label: str,
    failed: list[tuple[str, str, str]],
    dry_run: bool,
    tip: str = "",
) -> None:
    """Print a failed-items-by-system breakdown.  label = 'cover' or 'background'."""
    if not failed or dry_run:
        return
    print()
    cprint(C.DRED, f"  {len(failed)} ROM(s) could not get a {label} — manual lookup needed:")
    by_sys: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for sys_name, rom_stem, reason in failed:
        by_sys[sys_name].append((rom_stem, reason))
    for sys_name, entries in sorted(by_sys.items()):
        cprint(C.YELLOW, f"\n  [{sys_name}]")
        for rom_stem, reason in sorted(entries):
            cprint(C.RED,  f"    - {rom_stem}")
            cprint(C.GRAY, f"      ({reason})")
    print()
    if tip:
        cprint(C.GRAY, f"  Tip: {tip}")

# =============================================================================
# EXECUTION CORE  (called by both wizard and CLI paths)
# =============================================================================
def _run_sync(
    *,
    task: str,          # "covers" | "backgrounds" | "both"
    roms_base: Path,
    covers_base: Path | None,
    bgs_base: Path | None,
    cfg: SyncConfig,
    common: list[str],
    single_system: bool,
    cache_ttl: int,
    script_stem: str,
    report_path: Path | None,
) -> None:
    """Run the sync pipeline for the resolved configuration.
    All per-run settings (dry_run, download_mode, magick, etc.) come from cfg.
    """
    counters      = Counters()
    orphans: list[str] = []
    failed_covers: list[tuple[str,str,str]] = []
    bg_counters:  Counters | None = None
    failed_bgs:   list[tuple[str,str,str]] = []
    bg_orphans:   list[str] = []

    # Load LaunchBox offline index once; passed to all cover + bg workers.
    lb_index = lbdb_load_index(cache_ttl, script_stem)

    # ----------------------------------------------------------------
    # Covers pass
    # ----------------------------------------------------------------
    if task in ("covers", "both") and covers_base is not None:
        for folder in common:
            roms_path   = roms_base   if single_system else roms_base   / folder
            covers_path = covers_base if single_system else covers_base / folder

            repo_name: str = ""
            repo_files: list[str] = []
            if cfg.cover_style != "without_logo" and cfg.download_mode != "skip":
                repo_name, match_tier = resolve_system_folder(folder, roms_path)
                _tier_msg(folder, repo_name, match_tier, kind="covers")
                if repo_name:
                    libretro_folder = ("Named_Logos"
                                       if cfg.cover_style == "game_logo"
                                       else "Named_Boxarts")
                    repo_files = get_repo_file_list(
                        repo_name, cfg.github_token, cache_ttl, script_stem,
                        folder_name=libretro_folder,
                    )

            # Wrap per-folder work so a single failure never aborts the orphan
            # cleanup phase below.  orphans is accumulated across all folders.
            try:
                process_folder(
                    folder, roms_path, covers_path,
                    cfg, repo_files, repo_name,
                    counters, orphans, failed_covers,
                    lb_index=lb_index,
                )
            except KeyboardInterrupt:
                raise  # let Ctrl-C propagate normally
            except Exception as exc:
                cprint(C.DRED, f"  ERROR processing folder '{folder}': {exc}")

        # Orphan cleanup — always reached even if individual folders errored above.
        if cfg.delete_orphans and orphans:
            cprint(C.DRED, f"\n--- Deleting {len(orphans)} orphan cover(s) ---")
            for path in orphans:
                if not cfg.dry_run:
                    Path(path).unlink(missing_ok=True)
                counters.inc("deleted")
            print()

        if not cfg.dry_run and cfg.download_mode == "missing":
            # "all" mode: every downloaded file was already resized by _write_and_convert
            # and renamed files were resized by _reconcile_art_files.
            # Only "missing" mode leaves pre-existing covers untouched.
            _resize_pass(covers_base, cfg, counters)

    # ----------------------------------------------------------------
    # Backgrounds pass
    # ----------------------------------------------------------------
    if task in ("backgrounds", "both") and bgs_base is not None:
        bg_counters = Counters()

        print()
        cprint(C.CYAN, "=============================================")
        cprint(C.CYAN, "  BACKGROUND SYNC")
        if cfg.bg_style == "boxart":
            cprint(C.GRAY, "  (source: box art, letterboxed to 1920x1080)")
        elif not cfg.sgdb_key:
            cprint(C.GRAY, "  (no SGDB key — LaunchBox Fanart-Background only)")
        cprint(C.CYAN, "=============================================")

        for folder in common:
            roms_path = roms_base if single_system else roms_base / folder
            bgs_path  = bgs_base  if single_system else bgs_base  / folder
            bg_repo_name:  str       = ""
            bg_repo_files: list[str] = []
            if cfg.bg_style == "boxart" and cfg.download_mode != "skip":
                bg_repo_name, bg_match_tier = resolve_system_folder(folder, roms_path)
                _tier_msg(folder, bg_repo_name, bg_match_tier, kind="backgrounds")
                if bg_repo_name:
                    bg_repo_files = get_repo_file_list(
                        bg_repo_name, cfg.github_token, cache_ttl,
                        script_stem,
                        folder_name="Named_Boxarts",
                    )
            # Same guard: ensure bg_orphans accumulate regardless of per-folder errors.
            try:
                process_bg_folder(
                    folder, roms_path, bgs_path,
                    cfg, bg_counters, bg_orphans, failed_bgs,
                    lb_index=lb_index,
                    repo_files=bg_repo_files,
                    repo_name=bg_repo_name,
                )
            except KeyboardInterrupt:
                raise
            except Exception as exc:
                cprint(C.DRED, f"  ERROR processing bg folder '{folder}': {exc}")

        # Orphan cleanup — always reached.
        if cfg.delete_orphans and bg_orphans:
            cprint(C.DRED, f"\n--- Deleting {len(bg_orphans)} orphan background(s) ---")
            for path in bg_orphans:
                if not cfg.dry_run:
                    Path(path).unlink(missing_ok=True)
                bg_counters.inc("deleted")
            print()

        if not cfg.dry_run and cfg.download_mode == "missing":
            _resize_pass(bgs_base, cfg, bg_counters, target_dims="1920x1080",
                         valid_dims=frozenset(VALID_BG_DIMS), label="background JPG",
                         gravity="East" if cfg.bg_style == "boxart" else "center")

    # ----------------------------------------------------------------
    # Summary + report
    # ----------------------------------------------------------------
    if report_path:
        with ReportTee(report_path) as tee:
            _print_summary(counters, common, cfg, failed_covers,
                           bg_counters=bg_counters,
                           failed_bgs=failed_bgs or None)
        cprint(C.GREEN, f"  Report saved to: {tee.path}")
        print()
    else:
        _print_summary(counters, common, cfg, failed_covers,
                       bg_counters=bg_counters,
                       failed_bgs=failed_bgs or None)

# =============================================================================
# WIZARD  (interactive guided flow, used when no substantive args are given)
# =============================================================================

_SECTION = "  ─────────────────────────────────────────"

def _wiz_banner(dry_run: bool) -> None:
    print()
    cprint(C.CYAN, "  ╔══════════════════════════════════════╗")
    cprint(C.CYAN, "  ║         rom-assets-manager  wizard   ║")
    cprint(C.CYAN, "  ╚══════════════════════════════════════╝")
    print()
    if dry_run:
        cprint(C.MAGENTA, "  ⚠  DRY-RUN mode  (no files will change)")
        cprint(C.GRAY,    "     Re-run with --no-dry-run to apply changes.")
    else:
        cprint(C.RED, "  ⚡  LIVE mode  — files WILL be written/deleted")
    print()

def _wiz_confirm(dry_run: bool, task: str, opts: dict[str, str]) -> None:
    """Print a compact summary of what's about to run, then pause."""
    print()
    cprint(C.CYAN, _SECTION)
    cprint(C.CYAN, "  Ready to run:")
    cprint(C.CYAN, f"    Task         : {task}")
    for k, v in opts.items():
        cprint(C.CYAN, f"    {k:<13}: {v}")
    mode_label = "DRY-RUN (nothing will change)" if dry_run else "LIVE"
    cprint(C.CYAN if not dry_run else C.MAGENTA, f"    Mode         : {mode_label}")
    cprint(C.CYAN, _SECTION)
    print()
    try:
        input("  Press Enter to start (Ctrl+C to abort)...")
    except KeyboardInterrupt:
        print()
        raise
    print()

def _prompt_sgdb_key(existing: str, required: bool = False) -> str | None:
    """Prompt for SteamGridDB API key with echo suppressed (like a password).
    required=False (default): key is optional; returns "" if skipped.
    required=True: legacy — warns more strongly but still allows skipping.
    """
    if existing:
        cprint(C.GREEN, "  SGDB key     : set (from env/--sgdb-key)")
        return existing
    print()
    cprint(C.YELLOW, "  SteamGridDB API key not set.")
    cprint(C.GRAY,   "  Get a free key: https://www.steamgriddb.com/profile/preferences")
    if required:
        cprint(C.GRAY, "  Without a key, SGDB will be skipped (LaunchBox fallback still works).")
    else:
        cprint(C.GRAY, "  Leave blank to use LaunchBox only.")
    print()
    prompt = "  Enter SGDB key: " if required else "  Enter SGDB key (or press Enter to skip): "
    try:
        # getpass suppresses terminal echo — key never appears on screen or in scrollback.
        key = getpass.getpass(prompt).strip()
    except KeyboardInterrupt:
        print(); raise
    return (key or None) if required else key

def _wiz_cover_options(
    need_covers: bool,
    need_bgs:    bool,
    sgdb_key:    str,
) -> tuple[str, str, str, str]:
    """Wizard steps 8-9: prompt for cover style, region, bg style, and SGDB key.
    Returns (cover_style, preferred_region, sgdb_key, bg_style).
    """
    cover_style      = "with_logo"
    preferred_region = "any"
    bg_style         = "fanart"

    if need_covers:
        style_ch = prompt_choice("  Cover art style:", {
            "1": f"{C.GREEN}With logo{C.RESET}      — official box art        (libretro-thumbnails + LaunchBox)",
            "2": f"{C.CYAN}Without logo{C.RESET}   — clean fan-art            (SteamGridDB → LB Screenshot, key optional)",
            "3": f"{C.YELLOW}Game logo{C.RESET}      — title/logo art, no box  (libretro + LaunchBox + SGDB optional)",
        })
        cover_style = {"1": "with_logo", "2": "without_logo", "3": "game_logo"}[style_ch]
        print()

        if cover_style in ("with_logo", "game_logo"):
            region_ch = prompt_choice("  Preferred cover region:", {
                "1": f"{C.CYAN}No preference{C.RESET}",
                "2": f"{C.GREEN}USA{C.RESET}           — USA / North America",
                "3": f"{C.YELLOW}Europe{C.RESET}        — Europe (incl. AU, individual EU countries)",
                "4": f"{C.MAGENTA}Japan{C.RESET}         — Japan",
                "5": f"{C.CYAN}World{C.RESET}         — World / multi-region",
            })
            preferred_region = {"1":"any","2":"usa","3":"europe","4":"japan","5":"world"}[region_ch]
            print()
            if cover_style == "game_logo":
                # SGDB is the primary source for game_logo when a key is set
                sgdb_key = _prompt_sgdb_key(sgdb_key, required=False) or ""
                print()
        else:
            # without_logo: SGDB grids → LB Screenshot fallback. Key is optional.
            sgdb_key = _prompt_sgdb_key(sgdb_key, required=False) or ""
            print()

    # ── Background art style ──────────────────────────────────────────────
    if need_bgs:
        bg_ch = prompt_choice("  Background art style:", {
            "1": f"{C.GREEN}Fanart{C.RESET}         — SGDB Heroes → LaunchBox Fanart-Background",
            "2": f"{C.YELLOW}Box art{C.RESET}        — official box art, letterboxed to 1920x1080",
        })
        bg_style = {"1": "fanart", "2": "boxart"}[bg_ch]
        print()

    # Step 9: SGDB key for backgrounds.
    # Only ask when fanart mode AND cover style has not already prompted for a key.
    # - with_logo + fanart  : no SGDB prompt above → ask here
    # - with_logo + boxart  : boxart uses libretro/LB, SGDB not needed for bgs
    # - without_logo        : already prompted (optional) → skip
    # - game_logo           : already prompted (optional) → skip
    if need_bgs and not sgdb_key and cover_style == "with_logo" and bg_style == "fanart":
        sgdb_key = _prompt_sgdb_key(sgdb_key) or ""
        print()

    return cover_style, preferred_region, sgdb_key, bg_style

def _wiz_build_confirm_opts(
    roms_base:        Path,
    covers_base:      "Path | None",
    bgs_base:         "Path | None",
    download_mode:    str,
    need_covers:      bool,
    cover_style:      str,
    preferred_region: str,
    sgdb_key:         str,
    delete_orphans:   bool,
    report_path:      "Path | None",
    bg_style:         str = "fanart",
    need_bgs:         bool = False,
) -> dict[str, str]:
    """Assemble the ordered confirmation summary dict for _wiz_confirm.
    Pure function — no I/O, no prompts. Returns {label: value} for display.
    """
    _STYLE_CONFIRM = {
        "with_logo":    "with logo",
        "without_logo": "without logo (SGDB)",
        "game_logo":    "game logo",
    }
    opts: dict[str, str] = {"ROMs": str(roms_base)}
    if covers_base:
        opts["Covers"] = str(covers_base)
    if bgs_base:
        opts["Backgrounds"] = str(bgs_base)
    opts["Download"] = download_mode
    if need_covers:
        opts["Style"] = _STYLE_CONFIRM.get(cover_style, cover_style)
    if need_covers and cover_style in ("with_logo", "game_logo") and preferred_region != "any":
        opts["Region"] = REGION_LABELS.get(preferred_region, preferred_region)
    if need_bgs:
        opts["BG style"] = "box art (letterboxed)" if bg_style == "boxart" else "fanart/heroes"
    if sgdb_key:
        opts["SGDB key"] = "set"
    opts["Delete orphans"] = "yes" if delete_orphans else "no"
    if report_path:
        opts["Report"] = str(report_path)
    return opts

def _wizard(
    dry_run:     bool,
    magick:      str | None,
    token:       str | None,
    args,
    script_dir:  Path,
    script_stem: str,
) -> None:
    """Fully interactive guided flow."""
    _wiz_banner(dry_run)

    # ── 1. What do you want to do? ────────────────────────────────────
    _extra = {
        "2": f"{C.YELLOW}Normalize ROM filenames{C.RESET}",
        "3": f"{C.YELLOW}Filter non-exclusives across systems{C.RESET}",
    } if _COMPANION_TOOLS else {}
    task_ch = prompt_choice("  What would you like to do?", {
        "1": f"{C.GREEN}Check duplicate ROMs{C.RESET}",
        **_extra,
        "4": f"{C.YELLOW}Check ROM set completeness{C.RESET}",
        "5": f"{C.CYAN}Download covers + backgrounds{C.RESET}",
        "6": f"{C.CYAN}Download covers only{C.RESET}",
        "7": f"{C.CYAN}Download backgrounds only{C.RESET}",
        "h": f"{C.GRAY}Help — show usage, cover styles, options{C.RESET}",
    })
    print()

    if task_ch == "h":
        # Print the module docstring (__doc__) — no file I/O needed.
        print(__doc__)
        sys.exit(0)

    need_covers     = task_ch in ("5", "6")
    need_bgs        = task_ch in ("5", "7")
    is_dup          = task_ch == "1"
    is_completeness = task_ch == "4"

    # ── Completeness check (early exit — single folder + DAT, no system detection) ──
    if is_completeness:
        cprint(C.CYAN, _SECTION)
        cprint(C.CYAN, "  ROM set completeness")
        cprint(C.CYAN, _SECTION)
        print()
        cprint(C.GRAY, "  DAT files can be downloaded from: https://dat-o-matic.no-intro.org")
        print()

        rom_dir  = Path(prompt_path("ROM folder (single system)"))
        print()
        dat_path = Path(prompt_path("No-Intro DAT file"))
        if not dat_path.is_file():
            cprint(C.RED, f"  DAT file not found: '{dat_path}'")
            sys.exit(1)
        print()

        cprint(C.CYAN, _SECTION)
        cprint(C.CYAN, "  Region mode")
        cprint(C.CYAN, _SECTION)
        print()
        region_ch = prompt_choice("  Which releases to check against?", {
            "1": f"{C.GREEN}USA / North America{C.RESET}      — games released in USA or World  (1G1R)",
            "2": f"{C.CYAN}Europe{C.RESET}                   — games released in Europe or World  (1G1R)",
            "3": f"{C.YELLOW}Japan exclusives{C.RESET}         — games never released in USA or Europe",
            "4": f"{C.YELLOW}Japan (full){C.RESET}             — all Japanese releases incl. JP versions of western games  (1G1R)",
            "5": f"{C.GRAY}Full set{C.RESET}                 — all regions, all variants (no 1G1R filter)",
        })
        region_mode = {"1": "usa", "2": "europe", "3": "japan_exclusive",
                       "4": "japan", "5": "all"}[region_ch]
        print()

        want_ch = prompt_choice("  Save a want-list of missing titles?", {
            "y": f"{C.GREEN}Yes{C.RESET} — write a plain-text list of missing ROMs alongside the CSV",
            "n": f"{C.GRAY}No{C.RESET}",
        })
        want_list = want_ch == "y"
        print()

        check_completeness(
            dat_path    = dat_path,
            rom_dir     = rom_dir,
            region_mode = region_mode,
            script_dir  = script_dir,
            want_list   = want_list,
        )
        sys.exit(0)

    # ── Task 2: Normalize ROM filenames ───────────────────────────────
    if task_ch == "2":
        cprint(C.CYAN, _SECTION)
        cprint(C.CYAN, "  Normalize ROM filenames")
        cprint(C.CYAN, _SECTION)
        print()
        cprint(C.GRAY, "  Strips region/revision tags, moves trailing articles to the front.")
        cprint(C.GRAY, "  e.g. 'Legend of Zelda, The (USA) (Rev A).nes'  ->  'The Legend of Zelda.nes'")
        print()
        rom_dir = Path(prompt_path("ROM folder"))
        print()
        renames = _companion_collect_renames(str(rom_dir))
        if not renames:
            cprint(C.GREEN, "  All filenames are already normalized.")
            sys.exit(0)
        print(f"  {len(renames)} file(s) would be renamed:\n")
        for old, new in sorted(renames):
            cprint(C.GRAY, f"    {os.path.basename(old)}")
            print(f"    -> {os.path.basename(new)}\n")
        if dry_run:
            cprint(C.YELLOW, "  Dry-run mode — pass --rename (or rerun without --dry-run) to apply.")
            sys.exit(0)
        apply_ch = prompt_choice("  Apply renames?", {
            "y": f"{C.GREEN}Yes{C.RESET} — rename the files now",
            "n": f"{C.GRAY}No{C.RESET}  — cancel",
        })
        if apply_ch != "y":
            print("  Cancelled.")
            sys.exit(0)
        skipped, renamed = [], 0
        for old, new in renames:
            if os.path.exists(new):
                cprint(C.YELLOW, f"  SKIP (target exists): {os.path.basename(old)}")
                skipped.append(old)
            else:
                os.rename(old, new)
                renamed += 1
        cprint(C.GREEN, f"\n  Renamed {renamed} file(s)." + (f"  {len(skipped)} skipped." if skipped else ""))
        if skipped:
            del_ch = prompt_choice(f"  Delete the {len(skipped)} skipped source(s) (already-renamed duplicates)?", {
                "y": f"{C.DRED}Yes{C.RESET} — delete them",
                "n": f"{C.GRAY}No{C.RESET}  — keep them",
            })
            if del_ch == "y":
                for path in skipped:
                    try:
                        os.remove(path)
                        print(f"  Deleted: {os.path.basename(path)}")
                    except OSError as e:
                        cprint(C.RED, f"  ERROR: {os.path.basename(path)} — {e}")
        sys.exit(0)

    # ── Task 3: Filter non-exclusives across systems ──────────────────
    if task_ch == "3":
        cprint(C.CYAN, _SECTION)
        cprint(C.CYAN, "  Filter non-exclusives across systems")
        cprint(C.CYAN, _SECTION)
        print()
        cprint(C.GRAY, "  Finds games in sibling system folders that also exist in a 'main' system.")
        cprint(C.GRAY, "  Only systems in the same generation family are compared.")
        print()
        roms_root = Path(prompt_path("ROMs root folder (contains system subfolders)"))
        print()
        all_subs = sorted(d for d in os.listdir(str(roms_root)) if os.path.isdir(os.path.join(str(roms_root), d)))
        if not all_subs:
            cprint(C.RED, "  No system subfolders found.")
            sys.exit(1)
        print("  Available systems:")
        for i, name in enumerate(all_subs, 1):
            print(f"    [{i}] {name}")
        print()
        main_raw = input("  Main system (number or folder name): ").strip()
        if main_raw.isdigit() and 1 <= int(main_raw) <= len(all_subs):
            main_name = all_subs[int(main_raw) - 1]
        else:
            main_name = main_raw
        main_folder = os.path.join(str(roms_root), main_name)
        if not os.path.isdir(main_folder):
            cprint(C.RED, f"  Folder not found: {main_folder}")
            sys.exit(1)
        print()
        family_name, family_members = _companion_detect_family(main_name, _companion_DEFAULT_FAMILIES)
        if family_name:
            family_lower = {m.lower() for m in family_members}
            to_scan = [d for d in all_subs if d != main_name and d.lower() in family_lower]
            skipped_sys = [d for d in all_subs if d != main_name and d.lower() not in family_lower]
            cprint(C.CYAN, f"  Main system : {main_name}")
            cprint(C.CYAN, f"  Family      : {family_name}")
            if skipped_sys:
                cprint(C.GRAY, f"  Skipped     : {', '.join(skipped_sys)}  (different generation)")
        else:
            to_scan = [d for d in all_subs if d != main_name]
            cprint(C.CYAN, f"  Main system : {main_name}")
            cprint(C.GRAY, "  Family      : none detected — comparing all sibling systems")
        print()
        main_names = set(_companion_get_files_by_base(main_folder).keys())
        cprint(C.GREEN, f"  {len(main_names)} unique game(s) in {main_name}")
        print()
        to_delete = []
        for folder_name in to_scan:
            folder_path = os.path.join(str(roms_root), folder_name)
            non_excl = [
                p for name, paths in _companion_get_files_by_base(folder_path).items()
                if name in main_names for p in paths
            ]
            if not non_excl:
                print(f"  [{folder_name}] — all games are exclusive, nothing to remove.")
                continue
            print(f"  [{folder_name}] — {len(non_excl)} non-exclusive(s):")
            for p in sorted(non_excl):
                print(f"    {'DELETE' if not dry_run else '      '} {os.path.basename(p)}")
            to_delete.extend(non_excl)
        if not to_delete:
            cprint(C.GREEN, "\n  No non-exclusives found.")
            sys.exit(0)
        print()
        if dry_run:
            cprint(C.YELLOW, f"  {len(to_delete)} file(s) would be deleted. Dry-run — re-run with --no-dry-run to apply.")
            sys.exit(0)
        del_ch = prompt_choice(f"  Delete {len(to_delete)} non-exclusive(s)?", {
            "y": f"{C.DRED}Yes{C.RESET} — delete them now",
            "n": f"{C.GRAY}No{C.RESET}  — cancel",
        })
        if del_ch == "y":
            for p in to_delete:
                os.remove(p)
            cprint(C.GREEN, f"  Deleted {len(to_delete)} file(s).")
        else:
            print("  Cancelled.")
        sys.exit(0)

    # ── 2. ROMs path (always) ─────────────────────────────────────────
    cprint(C.CYAN, _SECTION)
    cprint(C.CYAN, "  Paths")
    cprint(C.CYAN, _SECTION)
    print()
    roms_base = Path(prompt_path("ROMs root folder"))
    print()

    # ── 3. Covers path ────────────────────────────────────────────────
    covers_base: Path | None = None
    if need_covers:
        covers_base = Path(prompt_path("Covers root folder"))
        print()

    # ── 4. Backgrounds path ───────────────────────────────────────────
    bgs_base: Path | None = None
    if need_bgs:
        bgs_base = Path(prompt_path("Backgrounds root folder"))
        print()

    # ── 5. System detection ───────────────────────────────────────────
    system_arg = args.system.strip().lower() if args.system else ""
    common, single_system = _detect_systems(
        roms_base, system_arg,
        rom_ext_filter=ROM_EXTENSIONS if is_dup else None,
    )
    if single_system and not common:
        cprint(C.CYAN, "  ROMs found directly in folder (single-system mode).")
        system = prompt_system()
        common = [system]
        single_system = True
    elif not common and not is_dup:
        cprint(C.RED, f"  No ROM subfolders found in: {roms_base}")
        cprint(C.YELLOW, "  Point --roms at the root containing console subfolders,")
        cprint(C.YELLOW, "  or add --system <name> for a single-system layout.")
        sys.exit(1)

    # ── 6. Duplicate check (early exit) ──────────────────────────────
    if is_dup:
        print()
        check_duplicates(roms_base, common, single_system, args.parallel_jobs,
                         dry_run=dry_run)
        sys.exit(0)

    # ── 7. Download options ───────────────────────────────────────────
    print()
    cprint(C.CYAN, _SECTION)
    cprint(C.CYAN, "  Download options")
    cprint(C.CYAN, _SECTION)
    print()

    dl_ch = prompt_choice("  Download mode:", {
        "1": f"{C.GREEN}Missing only{C.RESET}   — only ROMs without a file (fast, safe to re-run)",
        "2": f"{C.YELLOW}All{C.RESET}            — re-download and overwrite everything",
    })
    download_mode = {"1": "missing", "2": "all"}[dl_ch]
    print()

    # ── 8-9. Cover style, region, SGDB key ──────────────────────────────
    sgdb_key = (args.sgdb_key or "").strip()
    args.sgdb_key = None   # scrub — credential no longer needed in namespace
    cover_style, preferred_region, sgdb_key, bg_style = _wiz_cover_options(
        need_covers, need_bgs, sgdb_key
    )

    # ── 10. Delete orphans? ───────────────────────────────────────────
    orphan_ch = prompt_choice("  Covers/backgrounds with no matching ROM:", {
        "1": f"{C.GRAY}Keep them{C.RESET}      — leave unmatched files in place",
        "2": f"{C.DRED}Delete them{C.RESET}    — remove files that don't match any ROM",
    })
    delete_orphans = orphan_ch == "2"
    print()

    # ── 11. Report path ───────────────────────────────────────────────
    report_arg = (args.report or "").strip()
    if report_arg.lower() == "none":
        report_path: Path | None = None
    elif report_arg:
        report_path = Path(report_arg)
    else:
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        report_path = script_dir / f"rom-assets-manager_report_{ts}.txt"

    # ── 12. Confirm ───────────────────────────────────────────────────
    task_label = {
        "5": "covers + backgrounds",
        "6": "covers only",
        "7": "backgrounds only",
    }[task_ch]

    confirm_opts = _wiz_build_confirm_opts(
        roms_base        = roms_base,
        covers_base      = covers_base,
        bgs_base         = bgs_base,
        download_mode    = download_mode,
        need_covers      = need_covers,
        cover_style      = cover_style,
        preferred_region = preferred_region,
        sgdb_key         = sgdb_key,
        delete_orphans   = delete_orphans,
        report_path      = report_path,
        bg_style         = bg_style,
        need_bgs         = need_bgs,
    )
    _wiz_confirm(dry_run, task_label, confirm_opts)

    # ── 13. Create dirs if needed ─────────────────────────────────────
    for base, label in [(covers_base, "covers"), (bgs_base, "backgrounds")]:
        if base:
            _ensure_art_dir(base, label, dry_run)

    # ── 14. Build cfg and run ─────────────────────────────────────────
    cfg = SyncConfig(
        dry_run          = dry_run,
        delete_orphans   = delete_orphans,
        download_mode    = download_mode,
        threshold        = args.threshold,
        magick           = magick,
        parallel_jobs    = args.parallel_jobs,
        github_token     = token,
        preferred_region = preferred_region,
        cover_style      = cover_style,
        bg_style         = bg_style,
        sgdb_key         = sgdb_key or None,
        http_timeout     = args.http_timeout,
    )

    _run_sync(
        task        = {"5":"both","6":"covers","7":"backgrounds"}[task_ch],
        roms_base   = roms_base,
        covers_base = covers_base,
        bgs_base    = bgs_base,
        cfg         = cfg,
        common      = common,
        single_system = single_system,
        cache_ttl   = args.cache_ttl,
        script_stem = script_stem,
        report_path = report_path,
    )

# =============================================================================
# MAIN
# =============================================================================
def main() -> None:
    script_path = Path(__file__).resolve()
    script_dir  = script_path.parent
    script_stem = script_path.stem

    parser = argparse.ArgumentParser(
        prog="rom-assets-manager.py",
        description=(
            "ROM library manager: cover art, backgrounds, deduplication,\n"
            "completeness checks, filename normalisation, exclusives filtering.\n\n"
            "Run with no arguments to launch the interactive wizard (recommended).\n\n"
            "Art sources: libretro-thumbnails · SteamGridDB · LaunchBox GamesDB\n"
            "Requires ImageMagick for image conversion/resizing:\n"
            "  Windows : winget install ImageMagick.Q16-HDRI\n"
            "  Linux   : sudo apt install imagemagick\n"
            "  macOS   : brew install imagemagick"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--roms",             default="",
                        help="ROMs root folder")
    parser.add_argument("--covers",           default="",
                        help="Covers root folder")
    parser.add_argument("--backgrounds",      default="",
                        help="Backgrounds root folder")
    parser.add_argument("--system",           default="",
                        help="Single-system mode: e.g. snes, psx")
    parser.add_argument("--no-dry-run",       action="store_true",
                        help="Apply changes (default is dry run)")
    parser.add_argument("--delete-orphans",   action="store_true",
                        help="Delete covers/backgrounds with no matching ROM")
    parser.add_argument("--download-mode",    default="missing",
                        choices=["missing", "all", "skip"],
                        help="Download behaviour (default: missing)")
    parser.add_argument("--cover-style",      default="with_logo",
                        choices=["with_logo", "without_logo", "game_logo"],
                        help="Cover art style: with_logo (box art + system logo, default), "
                             "without_logo (SGDB grids / LB Screenshot), "
                             "game_logo (title art)")
    parser.add_argument("--bg-style",         default="fanart",
                        choices=["fanart", "boxart"],
                        help="Background art style: fanart (SGDB Heroes/LB Fanart) or boxart (box art letterboxed to 1920x1080)")
    parser.add_argument("--region",           default="any",
                        choices=["any", "usa", "europe", "japan", "world"],
                        help="Preferred cover region (default: any)")
    parser.add_argument("--sgdb-key",         default=os.environ.get("SGDB_KEY", ""),
                        help="SteamGridDB API key (prefer SGDB_KEY env var over CLI to avoid leaking in process lists).")
    parser.add_argument("--check-duplicates", action="store_true",
                        help="Scan ROMs for duplicates (runs instead of cover sync)")
    parser.add_argument("--check-completeness", action="store_true",
                        help="Check ROM folder against a No-Intro Logiqx XML DAT file")
    parser.add_argument("--dat",               default="",
                        help="Path to No-Intro Logiqx XML DAT file "
                             "(required with --check-completeness)")
    parser.add_argument("--completeness-region", default="usa",
                        choices=["usa", "europe", "japan", "japan_exclusive", "all"],
                        help="Region/1G1R mode for completeness check (default: usa). "
                             "japan_exclusive = never released in USA/Europe/World. "
                             "all = every retail entry, no 1G1R.")
    parser.add_argument("--want-list",         action="store_true",
                        help="Save a plain-text list of MISSING titles alongside the CSV "
                             "(used with --check-completeness)")

    parser.add_argument("--threshold",        type=float, default=0.4,
                        help="Fuzzy match threshold 0.0-1.0 (default 0.4)")
    parser.add_argument("--parallel-jobs",    type=int,   default=6,
                        help="Parallel download workers (default 6)")
    parser.add_argument("--cache-ttl",        type=int,   default=24,
                        help="GitHub API cache TTL in hours (default 24)")
    parser.add_argument("--http-timeout",     type=int,   default=30,
                        help="HTTP request timeout in seconds (default 30)")
    parser.add_argument("--github-token",     default=os.environ.get("GITHUB_TOKEN", ""),
                        help="GitHub personal access token (prefer GITHUB_TOKEN env var over CLI to avoid leaking in process lists).")
    parser.add_argument("--report",           default="",
                        help="Report file path. Defaults to rom-assets-manager_report_YYYYMMDD_HHMMSS.txt "
                             "next to the script. Pass 'none' to disable.")
    args = parser.parse_args()

    # Extract credentials immediately and scrub them from args so they don't
    # linger in argparse.Namespace.__repr__ (visible in tracebacks / logs).
    # Prefer env vars; --sgdb-key / --github-token are kept for convenience
    # but users should favour the env var form to avoid shell history leaks.
    dry_run = not args.no_dry_run
    magick  = find_magick()
    token   = args.github_token or None
    args.github_token = None   # scrub — credential no longer needed in namespace

    # ------------------------------------------------------------------
    # Wizard mode: no substantive args provided
    # ------------------------------------------------------------------
    wizard_mode = (
        not args.roms
        and not args.covers
        and not args.backgrounds
        and not args.check_duplicates
        and not args.check_completeness
    )

    if wizard_mode:
        _wizard(dry_run, magick, token, args, script_dir, script_stem)
        return

    # ------------------------------------------------------------------
    # CLI mode: all args provided on command line
    # ------------------------------------------------------------------

    if args.check_duplicates:
        roms_raw = args.roms.strip().strip('"') or prompt_path("ROMs root")
        roms_base = Path(roms_raw)
        if not roms_base.exists():
            cprint(C.RED, f"  ROMs path not found: '{roms_base}'")
            sys.exit(1)
        common, single_system = _detect_systems(
            roms_base, args.system, rom_ext_filter=ROM_EXTENSIONS)
        if single_system and not common:
            common = [prompt_system()]
        check_duplicates(roms_base, common, single_system, args.parallel_jobs,
                         dry_run=dry_run)
        sys.exit(0)

    if args.check_completeness:
        dat_raw = (args.dat or "").strip().strip('"')
        if not dat_raw:
            cprint(C.RED,  "  --dat is required with --check-completeness.")
            cprint(C.GRAY, "  Example: --dat '/path/to/Nintendo - SNES.dat'")
            cprint(C.GRAY, "  Download DAT files from: https://dat-o-matic.no-intro.org")
            sys.exit(1)
        dat_path = Path(dat_raw)
        if not dat_path.is_file():
            cprint(C.RED, f"  DAT file not found: '{dat_path}'")
            sys.exit(1)

        roms_raw_c = (args.roms or "").strip().strip('"')
        if not roms_raw_c:
            roms_raw_c = prompt_path("ROM folder to check")
        rom_dir = Path(roms_raw_c)
        if not rom_dir.is_dir():
            cprint(C.RED, f"  ROM folder not found: '{rom_dir}'")
            sys.exit(1)

        check_completeness(
            dat_path    = dat_path,
            rom_dir     = rom_dir,
            region_mode = args.completeness_region,
            script_dir  = script_dir,
            want_list   = args.want_list,
        )
        sys.exit(0)

    # Resolve required paths
    roms_raw   = args.roms.strip().strip('"')
    covers_raw = args.covers.strip().strip('"')
    if not roms_raw:
        cprint(C.RED, "  --roms is required in CLI mode.")
        sys.exit(1)
    if not covers_raw and not args.backgrounds:
        cprint(C.RED, "  --covers or --backgrounds (or both) required in CLI mode.")
        sys.exit(1)

    roms_base    = Path(roms_raw)
    covers_base  = Path(covers_raw) if covers_raw else None
    bgs_raw      = args.backgrounds.strip().strip('"')
    bgs_base     = Path(bgs_raw)    if bgs_raw    else None

    if not roms_base.exists():
        cprint(C.RED, f"  ROMs path not found: '{roms_base}'"); sys.exit(1)

    download_mode    = args.download_mode
    cover_style      = args.cover_style
    preferred_region = args.region
    sgdb_key         = args.sgdb_key or None
    args.sgdb_key    = None   # scrub — credential no longer needed in namespace
    delete_orphans   = args.delete_orphans

    if covers_base and bgs_base:
        task = "both"
    elif bgs_base:
        task = "backgrounds"
    else:
        task = "covers"

    common, single_system = _detect_systems(roms_base, args.system)
    if single_system and not common:
        common = [prompt_system()]
    elif not common:
        cprint(C.RED, f"  No ROM subfolders found in: {roms_base}")
        sys.exit(1)

    for base, label in [(covers_base, "covers"), (bgs_base, "backgrounds")]:
        if base:
            _ensure_art_dir(base, label, dry_run)

    print()
    cprint(C.CYAN, "=============================================")
    cprint(C.CYAN, "  rom-assets-manager.py  (CLI mode)")
    cprint(C.CYAN, f"  Platform    : {sys.platform}")
    cprint(C.CYAN, f"  Python      : {sys.version.split()[0]}")
    cprint(C.MAGENTA if dry_run else C.RED,
           f"  Mode        : {'DRY RUN' if dry_run else 'LIVE — files WILL be changed'}")
    cprint(C.CYAN, f"  Task        : {task}")
    cprint(C.CYAN, f"  ROMs        : {roms_base}")
    if covers_base:
        cprint(C.CYAN, f"  Covers      : {covers_base}")
    if bgs_base:
        cprint(C.CYAN, f"  Backgrounds : {bgs_base}")
    cprint(C.CYAN, f"  Download    : {download_mode}")
    if task in ("covers","both"):
        cprint(C.CYAN, f"  Style       : {_COVER_STYLE_LABELS.get(cover_style, cover_style)}")
    if task in ("backgrounds", "both"):
        cprint(C.CYAN, f"  BG style    : {_BG_STYLE_LABELS.get(args.bg_style, args.bg_style)}")
    if preferred_region != "any":
        cprint(C.CYAN, f"  Region      : {REGION_LABELS.get(preferred_region, preferred_region)}")
    cprint(C.GREEN if sgdb_key else C.GRAY,
           f"  SGDB key    : {'set' if sgdb_key else 'not set'}")
    cprint(C.GREEN if magick else C.YELLOW,
           f"  ImageMagick : {magick or 'NOT FOUND'}")
    cprint(C.CYAN, "=============================================")
    print()

    # Report path
    report_arg = (args.report or "").strip()
    if report_arg.lower() == "none":
        report_path: Path | None = None
    elif report_arg:
        report_path = Path(report_arg)
    else:
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        report_path = script_dir / f"rom-assets-manager_report_{ts}.txt"

    cfg = SyncConfig(
        dry_run          = dry_run,
        delete_orphans   = delete_orphans,
        download_mode    = download_mode,
        threshold        = args.threshold,
        magick           = magick,
        parallel_jobs    = args.parallel_jobs,
        github_token     = token,
        preferred_region = preferred_region,
        cover_style      = cover_style,
        bg_style         = args.bg_style,
        sgdb_key         = sgdb_key,
        http_timeout     = args.http_timeout,
    )

    _run_sync(
        task        = task,
        roms_base   = roms_base,
        covers_base = covers_base,
        bgs_base    = bgs_base,
        cfg         = cfg,
        common      = common,
        single_system = single_system,
        cache_ttl   = args.cache_ttl,
        script_stem = script_stem,
        report_path = report_path,
    )

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print()
        cprint(C.YELLOW, "  Interrupted — exiting.")
        sys.exit(130)