#!/usr/bin/env python3
"""
sync-covers.py  —  sync cover art and backgrounds to your ROM library
Windows / Linux / macOS  ·  Python 3.8+  ·  no external dependencies

─────────────────────────────────────────────────────
 QUICKSTART
─────────────────────────────────────────────────────
  Just run it — the wizard will ask for everything:

    python sync-covers.py

  Nothing is written until you confirm. Use --no-dry-run to apply.

─────────────────────────────────────────────────────
 COVER STYLES  (--cover-style)
─────────────────────────────────────────────────────
  with-logo    Official box art + system logo  (default)
               libretro-thumbnails → LaunchBox

  without-logo Clean cover art, no logo
               SteamGridDB → LaunchBox screenshot  (key optional)

  game-logo    Game title / logo art, no box
               With key:  SteamGridDB → libretro → LaunchBox Clear Logo
               No key:    libretro → LaunchBox Clear Logo

─────────────────────────────────────────────────────
 BACKGROUND STYLES  (--bg-style)
─────────────────────────────────────────────────────
  fanart       Hero art at 1920×1080  (default)
               With key:  SteamGridDB Heroes → LaunchBox Fanart
               No key:    LaunchBox Fanart-Background only

  boxart       Box art letterboxed to 1920×1080
               libretro Named_Boxarts → LaunchBox Box-Front

─────────────────────────────────────────────────────
 EXAMPLES
─────────────────────────────────────────────────────
  # First run — let the wizard guide you
  python sync-covers.py

  # Download missing box-art covers (Linux/macOS)
  python sync-covers.py --no-dry-run \
      --roms ~/retro/roms --covers ~/retro/covers

  # Game logos + fanart backgrounds in one pass (Linux/macOS)
  python sync-covers.py --no-dry-run \
      --roms ~/retro/roms --covers ~/retro/covers \
      --backgrounds ~/retro/backgrounds \
      --cover-style game-logo --sgdb-key YOUR_KEY

  # Same on Windows (use ^ to continue lines)
  python sync-covers.py --no-dry-run ^
      --roms "E:/tico/roms" --covers "E:/tico/assets/covers" ^
      --backgrounds "E:/tico/assets/backgrounds" ^
      --cover-style game-logo --sgdb-key YOUR_KEY

  # European covers; falls back to whatever region is available
  python sync-covers.py --no-dry-run --region europe \
      --roms ~/retro/roms --covers ~/retro/covers

  # One system only (ROMs directly in the folder, not in subfolders)
  python sync-covers.py --no-dry-run --system snes \
      --roms ~/retro/roms/snes --covers ~/retro/covers/snes

  # Remove covers that have no matching ROM
  python sync-covers.py --no-dry-run --delete-orphans \
      --roms ~/retro/roms --covers ~/retro/covers

─────────────────────────────────────────────────────
 NOTES
─────────────────────────────────────────────────────
  GitHub token   Without one you get 60 API requests/hour (5 000 with).
                 export GITHUB_TOKEN=ghp_xxxx  or  --github-token ghp_xxxx

  SGDB key       Free at https://www.steamgriddb.com/profile/preferences
                 export SGDB_KEY=YOUR_KEY  or  --sgdb-key YOUR_KEY

  ImageMagick    Required for image conversion and resizing.
                 Windows: winget install ImageMagick.Q16-HDRI
                 Linux:   sudo apt install imagemagick
"""



from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import io
import xml.etree.ElementTree as ET
import zipfile
import zlib
from collections import defaultdict
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path

# =============================================================================
# ANSI COLOURS  (auto-disabled on Windows if not supported)
# =============================================================================
def _ansi(code): return f"\033[{code}m"

USE_COLOR = sys.stdout.isatty() and (
    os.name != "nt"                       # non-Windows always try ANSI
    or "WT_SESSION"  in os.environ        # Windows Terminal
    or "ANSICON"     in os.environ        # ANSICON wrapper
    or os.environ.get("TERM_PROGRAM") == "vscode"  # VS Code terminal
)

class C:
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
    """Context manager: duplicates sys.stdout to a plain-text report file.
    Terminal output keeps ANSI colour codes; the file receives ANSI-stripped text.
    Usage::
        with ReportTee(path) as tee:
            _print_summary(...)
        print(f"  Report saved to: {tee.path}")
    """
    def __init__(self, path: Path):
        self.path  = path
        self._orig = None
        self._fh   = None

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
    "32x":             "Sega_-_32X",
    "3ds":             "Nintendo_-_Nintendo_3DS",
    "atari2600":       "Atari_-_2600",
    "atari7800":       "Atari_-_7800",
    "dc":              "Sega_-_Dreamcast",
    "ds":              "Nintendo_-_Nintendo_DS",
    "gba":             "Nintendo_-_Game_Boy_Advance",
    "gbc":             "Nintendo_-_Game_Boy_Color",
    "gb":              "Nintendo_-_Game_Boy",
    "gamecube":        "Nintendo_-_GameCube",
    "game-gear":       "Sega_-_Game_Gear",
    "genesis":         "Sega_-_Mega_Drive_-_Genesis",
    "megadrive":       "Sega_-_Mega_Drive_-_Genesis",
    "pce":             "NEC_-_PC_Engine_-_TurboGrafx_16",
    "pcengine":        "NEC_-_PC_Engine_-_TurboGrafx_16",
    "lynx":            "Atari_-_Lynx",
    "master-system":   "Sega_-_Master_System_-_Mark_III",
    "n64":             "Nintendo_-_Nintendo_64",
    "nes":             "Nintendo_-_Nintendo_Entertainment_System",
    "neogeo":          "SNK_-_Neo_Geo",
    "ngp":             "SNK_-_Neo_Geo_Pocket",
    "ngpc":            "SNK_-_Neo_Geo_Pocket_Color",
    "psx":             "Sony_-_PlayStation",
    "ps2":             "Sony_-_PlayStation_2",
    "psp":             "Sony_-_PlayStation_Portable",
    "saturn":          "Sega_-_Saturn",
    "sega-cd":         "Sega_-_Mega-CD_-_Sega_CD",
    "snes":            "Nintendo_-_Super_Nintendo_Entertainment_System",
    "virtualboy":      "Nintendo_-_Virtual_Boy",
    "wii":             "Nintendo_-_Wii",
    "wonderswan":      "Bandai_-_WonderSwan",
    "wonderswancolor": "Bandai_-_WonderSwan_Color",
}

BASE_RAW_URL = "https://raw.githubusercontent.com/libretro-thumbnails"
BASE_API_URL = "https://api.github.com/repos/libretro-thumbnails"

# SteamGridDB (clean fan-art covers, no console logos)
SGDB_API_BASE = "https://www.steamgriddb.com/api/v2"

# LaunchBox GamesDB — public Metadata.zip (no scraping, no API key required)
LBDB_METADATA_URL = "https://gamesdb.launchbox-app.com/Metadata.zip"
LBDB_IMG_BASE      = "https://images.launchbox-app.com/"

# Valid background dimensions (anything else gets letterboxed to 1920x1080)
VALID_BG_DIMS = {"1920x1080", "1280x720"}

# =============================================================================
# REGION PREFERENCE
# =============================================================================
# Maps the canonical region key the user picks -> tag substrings that identify
# that region inside a libretro-thumbnails filename like "Game (USA, Europe)".
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

_REGION_TAG_RE = re.compile(r'\(([^)]+)\)')

def region_of(name: str) -> str | None:
    """Return the canonical region key for a repo filename, or None.
    Splits multi-value tags by comma so the first listed region wins:
    e.g. "Game (Japan, USA)" -> "japan", "Game (World)" -> "world".
    """
    for m in _REGION_TAG_RE.finditer(name):
        # Split "Japan, USA" -> ["Japan", "USA"] so first listed wins
        for part in m.group(1).split(','):
            part = part.strip().lower()
            for key, keywords in REGION_KEYWORDS.items():
                if any(part == kw for kw in keywords):
                    return key
    return None


def sort_by_region(candidates: list[tuple[str, float]],
                   preferred: str) -> list[tuple[str, float]]:
    """Stable re-sort of ranked_matches output to prefer a region.

    Adds a small bonus to the sort key so that a preferred-region cover
    beats same-score variants without overriding a genuinely better-scoring
    different title.  Bonuses:
      preferred region  +0.10
      "world" (neutral) +0.05   (good fallback if preferred not found)
      anything else      0.00
    The bonus (0.10) exceeds the smallest tier gap (0.02: 0.90→0.88), so
    a preferred-region candidate at 0.88 will beat a non-preferred one at
    0.90 — intentional, since region is a meaningful signal. To reduce
    false promotions on ambiguous matches, consider --threshold 0.5 when
    using --region.
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
_TAG_RE    = re.compile(r"\s*[\(\[].*?[\)\]]")
_SEQNUM_RE = re.compile(r"_\d+$")   # strips _1, _2 ... (duplicate ROM suffixes)
_WORD_RE   = re.compile(r"\W+")       # word tokenizer for Jaccard scoring
_WS_RE     = re.compile(r"\s+")       # whitespace collapser for strip_tags

def strip_tags(name: str) -> str:
    return _WS_RE.sub(" ", _TAG_RE.sub("", name)).strip()

def normalize(name: str) -> str:
    """Strip region/language tags AND trailing sequence numbers (_1, _2...)."""
    return _SEQNUM_RE.sub("", strip_tags(name)).strip()

def _similarity_prenorm(a_low: str, a_norm: str, b_low: str, b_norm: str) -> float:
    """Core similarity logic operating on pre-lowercased, pre-normalized strings."""
    if a_low == b_low:                              return 1.00
    if a_norm and a_norm == b_norm:                 return 0.95
    if b_low  and a_low.startswith(b_low):          return 0.90
    if b_norm and a_norm.startswith(b_norm):        return 0.88

    shorter = a_norm if len(a_norm) <= len(b_norm) else b_norm
    longer  = b_norm if len(a_norm) <= len(b_norm) else a_norm
    containment_ok = len(shorter) >= 6 and len(shorter) >= len(longer) * 0.4
    if containment_ok:
        if b_low  in a_low  or a_low  in b_low:    return 0.85
        if b_norm in a_norm or a_norm in b_norm:    return 0.80

    words_a = {w for w in _WORD_RE.split(a_norm) if len(w) > 1}
    words_b = {w for w in _WORD_RE.split(b_norm) if len(w) > 1}
    if not words_a or not words_b:                  return 0.0
    common = len(words_a & words_b)
    if common < 2:                                  return 0.0
    union = len(words_a | words_b)
    return round(common / union, 4) if union else 0.0

def similarity(a: str, b: str) -> float:
    """Public similarity score between two ROM/cover names (0.0–1.0).
    Useful for callers and testing; internally _similarity_prenorm is used.
    """
    return _similarity_prenorm(
        a.lower().strip(), normalize(a).lower(),
        b.lower().strip(), normalize(b).lower()
    )

PNG_SIGNATURE  = b'\x89PNG\r\n\x1a\n'
WEBP_SIGNATURE = b'WEBP'  # bytes 8-12 of a WebP file (after RIFF + 4-byte size)

def is_valid_png(data: bytes) -> bool:
    """Check PNG magic bytes -- fast, zero cost, no dependencies."""
    return data[:8] == PNG_SIGNATURE

def is_webp(data: bytes) -> bool:
    """Check WebP magic bytes (RIFF....WEBP)."""
    return len(data) >= 12 and data[8:12] == WEBP_SIGNATURE

# Pre-normalized candidate list: list of (original_name, normalized_name) tuples.
# Build once per repo with build_normalized_candidates(), pass to ranked_matches().
def build_normalized_candidates(candidates: list[str]) -> list[tuple[str, str]]:
    """Pre-compute normalized form of every repo filename. Call once per system."""
    return [(c, normalize(c).lower()) for c in candidates]

def ranked_matches(rom: str, candidates: list[str],
                   threshold: float, top_n: int = 5,
                   _norm_cache: list[tuple[str, str]] | None = None) -> list[tuple[str, float]]:
    """Return up to top_n candidates above threshold, sorted best-first.
    Pass _norm_cache=build_normalized_candidates(candidates) to avoid
    re-normalizing the same repo filenames on every call.
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
                break  # OPTI B: exact match, no point scanning further

    return sorted(results, key=lambda x: x[1], reverse=True)[:top_n]


# =============================================================================
# IMAGEMAGICK
# =============================================================================
def find_magick() -> str | None:
    """Probe for a working ImageMagick binary.

    Tries 'magick' (v7) then 'convert' (v6) in order.
    shutil.which() only confirms the binary is on PATH; it cannot detect a
    broken alias (wrong architecture, missing shared libs, etc.).  We
    therefore actually execute '<cmd> -version' and accept the command only
    if it exits cleanly.  This costs one subprocess call at startup but
    prevents every subsequent resize from failing silently.
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

def magick_resize(magick: str, src: str, dst: str, dims: str = "512x512") -> None:
    """Letterbox-resize src -> dst at dims (e.g. '512x512', '1920x1080')."""
    subprocess.run(
        [magick, src, "-resize", dims, "-gravity", "center",
         "-background", "black", "-extent", dims, dst],
        check=True, capture_output=True
    )

def batch_identify(magick: str, jpg_list: list[Path],
                   chunk_size: int = 200) -> dict[Path, str | None]:
    """Return {path: 'WxH' | None} for every jpg in jpg_list.
    Chunks into batches of chunk_size to stay within Windows 32k CLI limit."""
    dims_map: dict[Path, str | None] = {p: None for p in jpg_list}
    for i in range(0, len(jpg_list), chunk_size):
        chunk = jpg_list[i : i + chunk_size]
        result = subprocess.run(
            [magick, "identify", "-format", "%i %wx%h\n"] + [str(p) for p in chunk],
            capture_output=True, text=True
        )
        if result.returncode == 0:
            for line in result.stdout.splitlines():
                parts = line.rsplit(" ", 1)
                if len(parts) == 2:
                    # Normalize path separators: magick may output forward
                    # slashes on Windows while dims_map keys use Path objects
                    # with backslashes.  Path(s) normalizes on construction.
                    dims_map[Path(parts[0])] = parts[1].strip()
    return dims_map

# =============================================================================
# STEAMGRIDDB  --  clean fan-art covers (no console/game logo overlay)
# API docs: https://www.steamgriddb.com/api/v2
# Requires a free API key: https://www.steamgriddb.com/profile/preferences
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
    """Return the URL of the best SGDB hero image for game_id, or None.
    Note: do NOT filter by ?dimensions= — SGDB hero dimensions (1920x620,
    3840x1240, 1600x650) differ from cover dims and trigger HTTP 400.
    We take the highest-voted static hero and let magick_resize letterbox it.
    """
    url = (f"{SGDB_API_BASE}/heroes/game/{game_id}"
           f"?types=static&nsfw=false&humor=false&epilepsy=false")
    data = _sgdb_get_json(url, key, context=f"heroes game_id={game_id}")
    if data and data.get("success") and data.get("data"):
        return data["data"][0]["url"]
    return None


# =============================================================================
# LAUNCHBOX GAMESDB — offline XML database
# LaunchBox publishes a complete Metadata.zip at a stable public URL (updated
# daily).  We download it once and cache an extracted JSON index next to this
# script — same TTL/cache pattern as the GitHub repo file-list cache.
#
# XML schema (inside the zip):
#   <Game>
#     <DatabaseID>12345</DatabaseID>
#     <Name>Mario &amp; Luigi: Dream Team Bros.</Name>
#   </Game>
#   <GameImage>
#     <DatabaseID>12345</DatabaseID>
#     <FileName>e3752148-0f5a-4f99-b1a9-e0d01fe8364b.jpg</FileName>
#     <Type>Box - Front</Type>      <!-- or "Fanart - Background" -->
#     <Region>North America</Region>
#   </GameImage>
#
# Image URL: https://images.launchbox-app.com/{FileName}
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


def _lbdb_parse_zip(zip_bytes: bytes) -> LbIndex:
    """Parse Metadata.zip bytes into the in-memory index.

    Returns: { normalized_name: { img_type: [(region_key, filename), ...] } }
    """
    index: dict = {}
    with zipfile.ZipFile(io.BytesIO(zip_bytes)) as zf:
        xml_names = [n for n in zf.namelist() if n.endswith(".xml")]
        for xml_name in xml_names:
            try:
                root = ET.fromstring(zf.read(xml_name))
            except Exception:
                continue

            # DatabaseID → normalized name
            db_id_to_norm: dict[str, str] = {}
            for game in root.iter("Game"):
                db_id = (game.findtext("DatabaseID") or "").strip()
                name  = (game.findtext("Name") or "").strip()
                if db_id and name:
                    norm = normalize(strip_tags(name)).lower().strip()
                    if norm:
                        db_id_to_norm[db_id] = norm

            # GameImage entries
            for img in root.iter("GameImage"):
                db_id    = (img.findtext("DatabaseID") or "").strip()
                filename = (img.findtext("FileName") or "").strip()
                img_type = (img.findtext("Type") or "").strip()
                region   = (img.findtext("Region") or "").strip().lower()
                _INDEXED_TYPES = (
                    _LBDB_TYPE_COVER, _LBDB_TYPE_BG,
                    _LBDB_TYPE_LOGO, _LBDB_TYPE_SCREENSHOT,
                )
                if not (db_id and filename and img_type in _INDEXED_TYPES):
                    continue
                norm = db_id_to_norm.get(db_id)
                if not norm:
                    continue
                region_key = _LBDB_REGION_MAP.get(region, "")
                index.setdefault(norm, {}).setdefault(img_type, []).append(
                    (region_key, filename)
                )
    return index


def sgdb_get_logo_url(game_id: int, key: str) -> str | None:
    """Return the URL of the best SteamGridDB logo image for game_id, or None.
    Logos are transparent PNGs with the game title art — no system logo.
    """
    url = (f"{SGDB_API_BASE}/logos/game/{game_id}"
           f"?types=static&nsfw=false&humor=false&epilepsy=false")
    data = _sgdb_get_json(url, key, context=f"logos game_id={game_id}")
    if data and data.get("success") and data.get("data"):
        return data["data"][0]["url"]
    return None


def lbdb_load_index(
    ttl_hours: int,
    script_dir: Path,
    script_stem: str,
    timeout: int = 90,
) -> LbIndex:
    """Download + cache LaunchBox Metadata.zip; return in-memory index.

    Cache: <script_dir>/<script_stem>_launchbox.json  (same pattern as GitHub cache)
    TTL  : same as --cache-ttl (default 24 h).
    Returns {} on any failure so callers degrade gracefully.
    """
    cache_path = script_dir / f"{script_stem}_launchbox.json"

    # ── Disk cache ───────────────────────────────────────────────────────
    if cache_path.exists():
        try:
            data    = json.loads(cache_path.read_text(encoding="utf-8"))
            fetched = datetime.fromisoformat(data["fetched"])
            if fetched.tzinfo is None:
                fetched = fetched.replace(tzinfo=timezone.utc)
            age_h = (datetime.now(timezone.utc) - fetched).total_seconds() / 3600
            if age_h < ttl_hours:
                # JSON round-trip: lists-of-lists → tuples
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

    # ── Download ─────────────────────────────────────────────────────────
    cprint(C.GRAY, "  Downloading LaunchBox Metadata.zip (~150 MB, please wait)...")
    try:
        zip_bytes = _http_get(LBDB_METADATA_URL, None, timeout=timeout)
    except Exception as e:
        cprint(C.YELLOW, f"  WARNING: Could not download LaunchBox DB: {e}")
        return {}

    # ── Parse ────────────────────────────────────────────────────────────
    cprint(C.GRAY, "  Parsing LaunchBox XML...")
    try:
        index = _lbdb_parse_zip(zip_bytes)
    except Exception as e:
        cprint(C.YELLOW, f"  WARNING: Could not parse LaunchBox DB: {e}")
        return {}

    cprint(C.GRAY, f"  LaunchBox DB loaded: {len(index):,} games")

    # ── Write cache ──────────────────────────────────────────────────────
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
    """Offline LaunchBox lookup.

    1. Normalise rom_stem.
    2. Exact-match against index keys (O(1)).
    3. Fuzzy-match against names sharing the first 4-char prefix if no exact hit.
       (Reduces candidates from ~100k to ~500 — same algorithm as libretro matching.)
    4. Sort by region preference, return best URL or None.
    """
    if not lb_index:
        return None
    norm = normalize(strip_tags(rom_stem)).lower().strip()
    if not norm:
        return None

    # 1. Exact match
    entries_by_type = lb_index.get(norm)

    # 2. Fuzzy match with prefix pre-filter
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
    """Fetch URL with retry-on-transient-error and optional Bearer/token auth.

    Retries on: connection errors, HTTP 429 (rate limit), HTTP 5xx.
    Raises immediately on 4xx (except 429) — permanent client errors.
    Backoff: 2^attempt seconds (1s, 2s, 4s).
    """
    req = urllib.request.Request(url, headers={"User-Agent": "sync-covers-py"})
    if token:
        req.add_header("Authorization", f"{'Bearer' if bearer else 'token'} {token}")
    last_exc: Exception | None = None
    for attempt in range(max_retries):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read()
        except urllib.error.HTTPError as e:
            if e.code == 429:
                wait = int(e.headers.get("Retry-After", 2 ** attempt))
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
                       ttl_hours: int, script_dir: Path, script_stem: str,
                       folder_name: str = "Named_Boxarts") -> list[str]:
    """Fetch the file list for `folder_name` inside a libretro-thumbnails repo.
    folder_name: "Named_Boxarts" (with_logo) or "Named_Logos" (game_logo).
    Cache key includes folder so they stay separate.
    """
    # Encode folder_name in cache filename so logos and boxarts cache separately.
    folder_tag = "logos" if folder_name == "Named_Logos" else "boxarts"
    cache_path = script_dir / f"{script_stem}_{repo}_{folder_tag}.json"

    # Try disk cache first
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
            else:
                cprint(C.GRAY, f"  Cache expired for {repo} -- refreshing from API")
        except Exception:
            cprint(C.GRAY, f"  Cache unreadable for {repo} -- re-fetching")

    # Fetch from GitHub Trees API
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
    # Cache write is separate: a write failure should not obscure a successful fetch
    try:
        payload   = {"fetched": datetime.now(timezone.utc).isoformat(), "files": names}
        tmp_cache = cache_path.with_suffix(".tmp")
        tmp_cache.write_text(json.dumps(payload), encoding="utf-8")
        tmp_cache.replace(cache_path)  # atomic on POSIX, near-atomic on Windows
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
    """Scan roms_path recursively, return {stem: path}.
    Skips .sbi files. Warns on duplicate stems (keeps first encountered).
    """
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
    """Prompt until a non-empty path is entered.
    When must_exist=True (default), rejects paths that don't exist.
    When must_exist=False, accepts any non-empty string (path created later).
    """
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
        self._lock     = threading.Lock()
        self.renamed   = 0
        self.deleted   = 0
        self.missing   = 0
        self.downloaded = 0
        self.skipped   = 0
        self.converted = 0
        self.duplicates = 0

    def inc(self, field: str, n: int = 1):
        with self._lock:
            # __slots__ prevents silent typo-attribute creation
            setattr(self, field, getattr(self, field) + n)

# =============================================================================
# SYNC CONFIGURATION  (immutable per-run settings, passed to process_folder)
# =============================================================================
@dataclasses.dataclass(frozen=True)
class SyncConfig:
    """Immutable settings constant across all system folders in a run.
    cover_style : "with_logo"    -- libretro-thumbnails (box art, with system logo)
                                     + LaunchBox GamesDB fallback
                  "without_logo" -- SteamGridDB clean fan-art covers (no logo)
                  "game_logo"    -- game logo/title art
                                     libretro Named_Logos → LaunchBox Clear Logo
                                     → SteamGridDB Logos (key optional)
    sgdb_key    : SteamGridDB Bearer token, optional for all styles.
                  without_logo: SGDB grid (primary) → LB Screenshot-Game-Title
                  game_logo   : SGDB logo (primary) → libretro → LB Clear Logo
                  with_logo   : SGDB for backgrounds only (fanart mode)
    bg_style    : "fanart"  -- SGDB Heroes → LaunchBox Fanart-Background (default)
                  "boxart"  -- libretro Named_Boxarts → LaunchBox Box-Front,
                              letterboxed to 1920x1080
    """
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
    sgdb_key:         str | None   # SteamGridDB API key
    http_timeout:     int          # per-request HTTP timeout in seconds


# =============================================================================
# MATCH RESULTS  (structured return types for pure matching functions)
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
# PROGRESS BAR  (stdlib only, \r overwrites same line in terminal)
# =============================================================================
def progress_bar(done: int, total: int, width: int = 40, label: str = "") -> str:
    filled = int(width * done / total) if total else width
    bar    = "█" * filled + "░" * (width - filled)
    pct    = int(100 * done / total) if total else 100
    return f"\r  {label}[{bar}] {done}/{total} ({pct}%)"


# =============================================================================
# COVER / BACKGROUND PIPELINE HELPERS
# =============================================================================

def _fuzzy_rename_pass(
    existing: dict[str, Path],
    roms: dict[str, Path],
    folder_path: Path,
    cfg: SyncConfig,
    counters: Counters,
    orphans: list[str],
    kind: str = "cover",
) -> bool:
    """Fuzzy-rename cover/background files to match ROM stems.

    Modifies `existing` in-place for successful renames.
    Returns True if any rename occurred (caller should re-read the directory).
    `kind` is used in log messages: "cover" or "background".
    """
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
                    shutil.move(str(path), str(new_path))  # shutil.move handles cross-filesystem moves; path.rename does not
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
) -> None:
    """Write raw bytes to a temp file, magick-resize to jpg_path, then clean up.

    Increments counters.downloaded (+1) and counters.converted (+1) on success.
    Raises subprocess.CalledProcessError if magick fails (tmp cleaned up, counter rolled back).
    Always runs magick — ensures output is always a correctly-sized JPEG regardless
    of source format or original resolution.
    """
    ext = ".png" if is_valid_png(raw) else (".webp" if is_webp(raw) else ".jpg")
    tmp = work_dir / f"{stem}.tmp{ext}"
    tmp.write_bytes(raw)
    counters.inc("downloaded")
    try:
        magick_resize(magick, str(tmp), str(jpg_path), dims=dims)
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
    """Match ROMs against the libretro-thumbnails repo. Pure — no I/O or printing.

    Returns (matches, no_matches, n_skipped).
    n_skipped: ROMs already covered and skipped (non-zero only in 'missing' mode).
    Caller is responsible for displaying results and updating counters.
    """
    # Pre-normalise once: avoids re-running regexes for every ROM × every candidate
    norm_cache = build_normalized_candidates(repo_files)
    exact_variants: dict[str, list[str]] = defaultdict(list)
    for orig, nc in norm_cache:
        exact_variants[nc].append(orig)

    matches:    list[LibretroMatch]   = []
    no_matches: list[LibretroNoMatch] = []
    n_skipped = 0

    for rom_stem in roms_to_dl:
        jpg_path = covers_path / f"{rom_stem}.jpg"
        if cfg.download_mode == "missing" and jpg_path.exists():
            n_skipped += 1
            continue

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


def _download_clean_covers(
    roms_to_dl: list[str],
    covers_path: Path,
    folder: str,
    cfg: SyncConfig,
    counters: Counters,
    failed_covers: list[tuple[str, str, str]],
    lb_index: LbIndex = None,
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

    cprint(C.CYAN, f"  Downloading {len(roms_to_dl)} cover(s) via {source_desc}...")
    print_lock = threading.Lock()
    dl_done    = 0
    dl_total   = len(roms_to_dl)
    dl_lock    = threading.Lock()

    def _worker(rom_stem: str) -> None:
        nonlocal dl_done
        jpg_path = covers_path / f"{rom_stem}.jpg"

        url = _find_cover_fallback(rom_stem, _lb, cfg)
        if url is None:
            with print_lock:
                cprint(C.DYELLOW, f"  NO COVER  '{rom_stem}'")
                failed_covers.append((folder, rom_stem, "no match: no clean cover found"))
            with dl_lock:
                dl_done += 1
            return

        try:
            raw = _http_get(url, None, timeout=cfg.http_timeout)
            _write_and_convert(raw, covers_path, rom_stem, jpg_path, cfg.magick, counters)
            with dl_lock:
                dl_done += 1
                dd, dt = dl_done, dl_total
            with print_lock:
                print(progress_bar(dd, dt, label="Downloading "), end="", flush=True)
                cprint(C.GREEN, f"  OK  {rom_stem}")
        except Exception as e:
            with dl_lock:
                dl_done += 1
            with print_lock:
                cprint(C.DRED, f"  FAIL  '{rom_stem}': {e}")
                failed_covers.append((folder, rom_stem, f"download failed: {e}"))

    with ThreadPoolExecutor(max_workers=min(cfg.parallel_jobs, 4)) as pool:
        futures = [pool.submit(_worker, r) for r in roms_to_dl]
        try:
            for fut in as_completed(futures):
                fut.result()
        except KeyboardInterrupt:
            cprint(C.YELLOW, "\n  Interrupted -- cancelling remaining downloads...")
            pool.shutdown(wait=False, cancel_futures=True)
            raise
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
    """Generic two-source fallback resolver.

    lb_finder  : one of lbdb_find_*_url — called with (rom_stem, lb_index, region).
    sgdb_fn    : one of sgdb_get_*_url  — called with (game_id, key).
                 Pass None to skip SGDB entirely.
    sgdb_first : when True, SGDB is attempted before lb_finder.
                 When False (default), lb_finder runs first.
    SGDB is only attempted when a key is set and sgdb_fn is not None.
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




def _find_cover_fallback(rom_stem: str, lb_index: LbIndex,
                          cfg: SyncConfig) -> str | None:
    """Fallback chain for without_logo: SGDB grid → LB Screenshot-Game-Title.

    Mirrors fanart background priority: SGDB is the primary source when a key
    is set; LB Screenshot is the fallback (or the only source with no key).
    """
    return _find_fallback_url(
        rom_stem, lb_index, cfg,
        lb_finder=lbdb_find_screenshot_url,
        sgdb_fn=sgdb_get_cover_url,
        sgdb_first=True,
    )


def _download_libretro_covers(
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
    lb_index:         LbIndex = None,
    direct_roms:      list[str] | None = None,
) -> None:
    """Download covers using libretro-thumbnails with LB + optional SGDB fallbacks.

    lb_folder         : libretro subfolder, e.g. "Named_Boxarts" or "Named_Logos".
    lb_fallback_finder: lbdb_find_*_url to call after libretro candidates exhausted.
    sgdb_fn           : sgdb_get_*_url to call as the PRIMARY source before libretro
                        when a key is set. Pass None to skip SGDB entirely.
    direct_roms       : ROM stems that skip libretro (no repo match) and go
                        straight to sgdb_fn → lb_fallback_finder.
    """
    _direct = direct_roms or []
    lb_idx  = lb_index or {}
    cprint(C.CYAN, f"  Downloading {len(matches) + len(_direct)} cover(s)...")
    print_lock = threading.Lock()
    dl_done    = 0
    dl_total   = len(matches) + len(_direct)
    dl_lock    = threading.Lock()

    def _worker(item: LibretroMatch) -> None:
        nonlocal dl_done
        rom_stem   = item.rom_stem
        jpg_path   = item.jpg_path
        candidates = item.candidates

        # Step 1: SGDB primary — try before libretro when key is set
        if sgdb_fn and cfg.sgdb_key:
            game_id = sgdb_search_game(rom_stem, cfg.sgdb_key)
            if game_id:
                sgdb_url = sgdb_fn(game_id, cfg.sgdb_key)
                if sgdb_url:
                    try:
                        raw = _http_get(sgdb_url, None, timeout=cfg.http_timeout)
                        _write_and_convert(raw, covers_path, rom_stem, jpg_path,
                                           cfg.magick, counters)
                        with dl_lock:
                            dl_done += 1; dd, dt = dl_done, dl_total
                        with print_lock:
                            print(progress_bar(dd, dt, label="Downloading "),
                                  end="", flush=True)
                            cprint(C.GREEN, f"  OK (SGDB)  {rom_stem}")
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
                _write_and_convert(raw, covers_path, rom_stem, jpg_path, cfg.magick, counters)
            except subprocess.CalledProcessError:
                with print_lock:
                    cprint(C.YELLOW,
                           f"  BAD IMAGE  '{rom_stem}' <- '{match_name}' "
                           f"(ImageMagick error, trying next candidate...)")
                continue

            with dl_lock:
                dl_done += 1
                dd, dt = dl_done, dl_total
            with print_lock:
                attempt_note = f" (attempt {attempt+1})" if attempt > 0 else ""
                print(progress_bar(dd, dt, label="Downloading "), end="", flush=True)
                cprint(C.GREEN, f"  OK  {rom_stem}{attempt_note}")
            return  # success — stop trying candidates

        # Step 3: LB fallback — SGDB was already tried at step 1 (if applicable)
        _fallback_url = lb_fallback_finder(rom_stem, lb_idx, cfg.preferred_region)
        if _fallback_url:
            try:
                raw = _http_get(_fallback_url, None, timeout=cfg.http_timeout)
                _write_and_convert(raw, covers_path, rom_stem, jpg_path, cfg.magick, counters)
                with dl_lock:
                    dl_done += 1; dd, dt = dl_done, dl_total
                with print_lock:
                    print(progress_bar(dd, dt, label="Downloading "), end="", flush=True)
                    cprint(C.GREEN, f"  OK (fallback)  {rom_stem}")
                return
            except Exception as lbe:
                with print_lock:
                    cprint(C.GRAY, f"  Fallback download failed  '{rom_stem}': {lbe}")

        # All sources exhausted — still count this slot so the bar reaches 100%
        with dl_lock:
            dl_done += 1; dd, dt = dl_done, dl_total
        with print_lock:
            print(progress_bar(dd, dt, label="Downloading "), end="", flush=True)
            cprint(C.DRED,
                   f"  GIVE UP  '{rom_stem}' -- all {len(candidates)} candidate(s) failed")
            failed_covers.append((folder, rom_stem,
                                  f"download failed ({len(candidates)} candidate(s) tried)"))

    def _worker_direct(rom_stem: str) -> None:
        """ROMs that skip libretro: try sgdb_fn first, then lb_fallback_finder."""
        nonlocal dl_done
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
                                   cfg.magick, counters)
                with dl_lock:
                    dl_done += 1; dd, dt = dl_done, dl_total
                with print_lock:
                    print(progress_bar(dd, dt, label="Downloading "), end="", flush=True)
                    cprint(C.GREEN, f"  OK (fallback)  {rom_stem}")
                return
            except Exception as e:
                with print_lock:
                    cprint(C.GRAY, f"  Fallback failed  '{rom_stem}': {e}")
        with dl_lock:
            dl_done += 1; dd, dt = dl_done, dl_total
        with print_lock:
            print(progress_bar(dd, dt, label="Downloading "), end="", flush=True)
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


def _download_bg_boxart(
    roms_to_dl: list[str],
    bgs_path: Path,
    repo_name: str,
    repo_files: list[str],
    folder: str,
    cfg: SyncConfig,
    bg_counters: Counters,
    failed_bgs: list[tuple[str, str, str]],
    lb_index: LbIndex = None,
) -> None:
    """Download backgrounds using box art (libretro Named_Boxarts → LaunchBox Box-Front).
    Images are letterboxed to 1920x1080 by _write_and_convert.
    Shares the same matching + fallback logic as covers, only the output
    path, dimensions, and progress label differ.
    """
    cprint(C.CYAN, f"  Downloading {len(roms_to_dl)} background(s) via box art (libretro + LaunchBox)...")

    if cfg.dry_run:
        for rom_stem in roms_to_dl:
            cprint(C.MAGENTA, f"  [DRY RUN] QUEUED (boxart BG)  '{rom_stem}'")
        return

    lb_idx     = lb_index or {}
    print_lock = threading.Lock()
    bg_done    = 0
    bg_total   = len(roms_to_dl)
    bg_lock    = threading.Lock()

    # Match ROMs against libretro repo (Named_Boxarts), same algorithm as covers.
    matches, no_matches, n_skipped = _match_libretro_roms(
        roms_to_dl, bgs_path, repo_files, cfg)
    if n_skipped:
        bg_counters.inc("skipped", n_skipped)

    # ROMs with no libretro match go straight to the LaunchBox fallback.
    direct_lb: list[str] = [nm.rom_stem for nm in no_matches]

    def _worker_match(item: LibretroMatch) -> None:
        nonlocal bg_done
        rom_stem   = item.rom_stem
        jpg_path   = bgs_path / f"{rom_stem}.jpg"
        for attempt, (match_name, _) in enumerate(item.candidates):
            url = (f"{BASE_RAW_URL}/{repo_name}/master/Named_Boxarts/"
                   f"{urllib.parse.quote(match_name)}.png")
            try:
                raw = _http_get(url, cfg.github_token, timeout=cfg.http_timeout)
            except Exception as e:
                with print_lock:
                    cprint(C.DRED, f"  FAIL  '{rom_stem}' <- '{match_name}': {e}")
                continue
            if not is_valid_png(raw):
                continue
            try:
                _write_and_convert(raw, bgs_path, rom_stem, jpg_path,
                                   cfg.magick, bg_counters, dims="1920x1080")
            except Exception:
                continue
            with bg_lock:
                bg_done += 1; dd, dt = bg_done, bg_total
            with print_lock:
                attempt_note = f" (attempt {attempt+1})" if attempt > 0 else ""
                print(progress_bar(dd, dt, label="BG boxart "), end="", flush=True)
                cprint(C.GREEN, f"  OK  {rom_stem}{attempt_note}")
            return  # success
        # Libretro exhausted — try LaunchBox Box-Front
        lb_url = lbdb_find_cover_url(rom_stem, lb_idx, cfg.preferred_region)
        if lb_url:
            try:
                raw = _http_get(lb_url, None, timeout=cfg.http_timeout)
                _write_and_convert(raw, bgs_path, rom_stem, jpg_path,
                                   cfg.magick, bg_counters, dims="1920x1080")
                with bg_lock:
                    bg_done += 1; dd, dt = bg_done, bg_total
                with print_lock:
                    print(progress_bar(dd, dt, label="BG boxart "), end="", flush=True)
                    cprint(C.GREEN, f"  OK (LaunchBox fallback)  {rom_stem}")
                return
            except Exception as e:
                with print_lock:
                    cprint(C.GRAY, f"  LaunchBox fallback failed  '{rom_stem}': {e}")
        with bg_lock:
            bg_done += 1; dd, dt = bg_done, bg_total
        with print_lock:
            print(progress_bar(dd, dt, label="BG boxart "), end="", flush=True)
            cprint(C.DRED, f"  NO IMAGE  '{rom_stem}'")
            failed_bgs.append((folder, rom_stem, "no match: no boxart found"))

    def _worker_direct(rom_stem: str) -> None:
        """LaunchBox-only worker for ROMs with no libretro match."""
        nonlocal bg_done
        jpg_path = bgs_path / f"{rom_stem}.jpg"
        lb_url   = lbdb_find_cover_url(rom_stem, lb_idx, cfg.preferred_region)
        if lb_url:
            try:
                raw = _http_get(lb_url, None, timeout=cfg.http_timeout)
                _write_and_convert(raw, bgs_path, rom_stem, jpg_path,
                                   cfg.magick, bg_counters, dims="1920x1080")
                with bg_lock:
                    bg_done += 1; dd, dt = bg_done, bg_total
                with print_lock:
                    print(progress_bar(dd, dt, label="BG boxart "), end="", flush=True)
                    cprint(C.GREEN, f"  OK (LaunchBox)  {rom_stem}")
                return
            except Exception as e:
                with print_lock:
                    cprint(C.GRAY, f"  LaunchBox failed  '{rom_stem}': {e}")
        with bg_lock:
            bg_done += 1; dd, dt = bg_done, bg_total
        with print_lock:
            print(progress_bar(dd, dt, label="BG boxart "), end="", flush=True)
            cprint(C.DRED, f"  NO IMAGE  '{rom_stem}'")
            failed_bgs.append((folder, rom_stem, "no match: no boxart found"))

    with ThreadPoolExecutor(max_workers=min(cfg.parallel_jobs, 4)) as pool:
        futures  = [pool.submit(_worker_match,  m) for m in matches]
        futures += [pool.submit(_worker_direct, r) for r in direct_lb]
        try:
            for fut in as_completed(futures):
                fut.result()
        except KeyboardInterrupt:
            cprint(C.YELLOW, "\n  Interrupted -- cancelling remaining background downloads...")
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
    lb_index: LbIndex = None,
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

    print_lock = threading.Lock()
    bg_done    = 0
    bg_total   = len(roms_to_dl)
    bg_lock    = threading.Lock()

    def _worker(rom_stem: str) -> None:
        nonlocal bg_done
        jpg_path  = bgs_path / f"{rom_stem}.jpg"
        hero_url: str | None = None
        lb_bg_url: str | None = None

        # Track where this image came from for accurate error reporting
        used_source = "none"
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
            lb_bg_url = lbdb_find_bg_url(rom_stem, lb_index or {}, cfg.preferred_region)
            if lb_bg_url is None:
                # Compose reason string based on what was actually tried
                if not cfg.sgdb_key:
                    source_note = "no fanart (no SGDB key, LaunchBox: no fanart)"
                elif game_id is None:
                    source_note = "no match: SGDB game not found, LaunchBox: no fanart"
                else:
                    source_note = "no match: SGDB no hero, LaunchBox: no fanart"
                with print_lock:
                    failed_bgs.append((folder, rom_stem, source_note))
                return
            hero_url  = lb_bg_url
            used_source = "LaunchBox"
            with print_lock:
                source = "LaunchBox" if not cfg.sgdb_key else "LaunchBox (SGDB fallback)"
                cprint(C.GRAY, f"  {source} BG  '{rom_stem}'")

        try:
            raw = _http_get(hero_url, None, timeout=cfg.http_timeout)
            _write_and_convert(raw, bgs_path, rom_stem, jpg_path, cfg.magick, bg_counters,
                               dims="1920x1080")
            with bg_lock:
                bg_done += 1
                dd, dt = bg_done, bg_total
            with print_lock:
                print(progress_bar(dd, dt, label="Backgrounds"), end="", flush=True)
                cprint(C.GREEN, f"  OK  {rom_stem}")
        except Exception as e:
            with print_lock:
                cprint(C.DRED, f"  FAIL  '{rom_stem}': {e}")
                failed_bgs.append((folder, rom_stem, f"{used_source} download failed: {e}"))

    with ThreadPoolExecutor(max_workers=min(cfg.parallel_jobs, 4)) as pool:
        futures = [pool.submit(_worker, r) for r in roms_to_dl]
        try:
            for fut in as_completed(futures):
                fut.result()
        except KeyboardInterrupt:
            cprint(C.YELLOW,
                   "\n  Interrupted -- cancelling remaining background downloads...")
            pool.shutdown(wait=False, cancel_futures=True)
            raise
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
                   lb_index: LbIndex = None) -> None:
    """Process one system folder: rename mismatched covers, then download missing ones.

    Dispatches to the SGDB (without_logo) or libretro-thumbnails+LaunchBox (with_logo)
    download pipeline based on cfg.cover_style.
    """
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
    if _fuzzy_rename_pass(covers, roms, covers_path, cfg, counters, orphans):
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

    if cfg.cover_style == "without_logo":
        _download_clean_covers(roms_to_dl, covers_path, folder, cfg, counters,
                               failed_covers, lb_index=lb_idx)
        return

    # with_logo / game_logo: libretro-thumbnails primary, LB + optional SGDB fallbacks.
    lb_idx = lb_index or {}   # hoisted: needed by both the early-exit and normal paths
    if cfg.cover_style == "game_logo":
        _lb_folder, _sgdb_fn, _lb_fallback = (
            "Named_Logos", sgdb_get_logo_url, lbdb_find_logo_url)
    else:  # with_logo
        _lb_folder, _sgdb_fn, _lb_fallback = (
            "Named_Boxarts", None, lbdb_find_cover_url)

    if not repo_files:
        if _sgdb_fn is None:
            cprint(C.DYELLOW,
                   f"  No repo file list available -- skipping downloads for {folder}")
            return
        # game_logo: no Named_Logos for this system; SGDB + LB may still have logos.
        cprint(C.GRAY, f"  No Named_Logos for {folder} — trying SGDB + LaunchBox logos...")
        if not cfg.dry_run:
            _download_libretro_covers(
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
        _download_libretro_covers(
            matches, covers_path, repo_name, cfg, counters, failed_covers, folder,
            lb_folder=_lb_folder, sgdb_fn=_sgdb_fn, lb_fallback_finder=_lb_fallback,
            lb_index=lb_idx, direct_roms=direct_roms or None,
        )


def process_bg_folder(folder: str, roms_path: Path, bgs_path: Path,
                      cfg: SyncConfig,
                      bg_counters: Counters,
                      bg_orphans: list[str],
                      failed_bgs: list[tuple[str, str, str]],
                      lb_index: LbIndex = None,
                      repo_files: list[str] | None = None,
                      repo_name: str = "") -> None:
    """Process one system folder for background art.

    bg_style=="fanart": SGDB Heroes → LaunchBox Fanart-Background.
    bg_style=="boxart": libretro Named_Boxarts → LaunchBox Box-Front (letterboxed).
    Always produces 1920x1080 JPEGs; the resize pass accepts 1280x720 as-is.
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
    if _fuzzy_rename_pass(bgs, roms, bgs_path, cfg, bg_counters, bg_orphans,
                          kind="background"):
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
            cprint(C.DYELLOW,
                   f"  No repo file list available for boxart BG — skipping downloads for {folder}")
            return
        _download_bg_boxart(
            roms_to_dl, bgs_path, repo_name, repo_files or [],
            folder, cfg, bg_counters, failed_bgs, lb_index=lb_index,
        )
    else:
        _download_bg_images(roms_to_dl, bgs_path, folder, cfg, bg_counters, failed_bgs,
                            lb_index=lb_index)


# =============================================================================
# CRC32 DUPLICATE DETECTION
# =============================================================================
ROM_EXTENSIONS = {
    ".sfc", ".smc", ".nes", ".gb", ".gbc", ".gba", ".n64", ".z64", ".v64",
    ".nds", ".md", ".smd", ".gen", ".gg", ".sms", ".pce", ".iso", ".bin",
    ".cue", ".img", ".chd", ".pbp", ".cso", ".rom", ".a26", ".lnx", ".ws",
    ".wsc", ".ngp", ".ngc",
}

# ---------------------------------------------------------------------------
# Hashing helpers
# ---------------------------------------------------------------------------
def _hash_file(path: Path, chunk_size: int = 1 << 20) -> tuple[str, str] | None:
    """
    Read path once, computing CRC32 and SHA-1 simultaneously.
    Returns (crc32_hex, sha1_hex) or None on any read error.
    Single-pass keeps I/O cost identical to the old CRC32-only approach.
    """
    # Single outer guard: returns None on ANY failure (I/O, FIPS init, etc.)
    try:
        crc = 0
        # usedforsecurity=False: SHA-1 used for deduplication, not cryptography.
        # Required on FIPS-enabled systems (RHEL/CentOS); kwarg added in Python 3.9.
        try:
            sha = hashlib.sha1(usedforsecurity=False)
        except TypeError:  # Python 3.8 lacks the kwarg
            sha = hashlib.sha1()
        with open(path, "rb") as f:
            while chunk := f.read(chunk_size):
                crc = zlib.crc32(chunk, crc)
                sha.update(chunk)
        return f"{crc & 0xFFFFFFFF:08X}", sha.hexdigest().upper()
    except Exception:  # OSError, MemoryError, unexpected hashlib error, etc.
        return None


def check_duplicates(roms_base: Path, common: list[str],
                     single_system: bool, parallel_jobs: int) -> None:
    """
    Three-stage duplicate detection:
      1. Group by file size    (free — stat() already needed for reporting)
      2. CRC32 + SHA-1 on size-candidates only  (skip unique-size files)
      3. Confirm by (size, CRC32, SHA-1) agreement

    Empty files (size == 0) are reported separately as broken/placeholder ROMs
    rather than being falsely grouped as duplicates of each other.
    A file is only reported as a duplicate when size + CRC32 + SHA-1 all agree.
    """
    print()
    cprint(C.CYAN, "=============================================")
    cprint(C.CYAN, "  DUPLICATE ROM DETECTION")
    cprint(C.CYAN, "  (size → CRC32 → SHA-1 pipeline)")
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
        for p in rom_dir.rglob("*.*"):   # *.*  skips bare directories efficiently
            if p.is_file() and p.suffix.lower() in ROM_EXTENSIONS:
                all_rom_files.append(p)

    if not all_rom_files:
        cprint(C.YELLOW, "  No ROM files found.")
        return

    cprint(C.CYAN, f"  Found {len(all_rom_files)} ROM file(s).")
    print()

    # ------------------------------------------------------------------
    # Stage 1: group by size (free — no I/O beyond stat)
    # ------------------------------------------------------------------
    cprint(C.GRAY, "  Stage 1/3 — grouping by file size...")
    empty_files: list[Path]       = []
    unreadable:  list[Path]       = []
    by_size:     dict[int, list[Path]] = defaultdict(list)

    for p in all_rom_files:
        try:
            sz = p.stat().st_size
        except OSError:
            unreadable.append(p)
            continue
        if sz == 0:
            empty_files.append(p)
        else:
            by_size[sz].append(p)

    # Only files sharing their size with ≥1 other file need hashing
    size_candidates: list[tuple[Path, int]] = [
        (p, sz) for sz, paths in by_size.items() if len(paths) > 1 for p in paths
    ]
    size_unique = sum(1 for paths in by_size.values() if len(paths) == 1)

    cprint(C.GRAY,
           f"    {size_unique} unique-size files skipped  |  "
           f"{len(size_candidates)} candidate(s) need hashing"
           + (f"  |  {len(empty_files)} empty file(s)" if empty_files else ""))
    print()

    if not size_candidates:
        _report_duplicates([], empty_files, unreadable, all_rom_files)
        return

    # ------------------------------------------------------------------
    # Stage 2: CRC32 + SHA-1 on candidates only (parallel, with progress)
    # Both hashes computed in a single sequential read per file.
    # ------------------------------------------------------------------
    cprint(C.GRAY, f"  Stage 2/3 — hashing {len(size_candidates)} candidate(s)...")

    # (size, crc32) -> [(path, sha1), ...]
    hash_results: dict[tuple[int, str], list[tuple[Path, str]]] = defaultdict(list)
    hash_lock  = threading.Lock()
    done_count = 0
    total      = len(size_candidates)

    def hash_one(path: Path, known_size: int) -> None:
        # known_size comes from stage-1 stat() — no second syscall needed
        hashes = _hash_file(path)
        with hash_lock:
            if hashes is None:
                unreadable.append(path)
            else:
                crc, sha = hashes
                hash_results[(known_size, crc)].append((path, sha))

    with ThreadPoolExecutor(max_workers=parallel_jobs) as pool:
        futures = {pool.submit(hash_one, p, sz): p for p, sz in size_candidates}
        try:
            for fut in as_completed(futures):
                try:
                    fut.result()
                except Exception as e:
                    cprint(C.YELLOW, f"  WARNING: hash error: {e}")
                finally:
                    done_count += 1  # main-thread only: as_completed drives this loop
                    dc = done_count
                    print(progress_bar(dc, total, label="Hashing   "), end="", flush=True)
        except KeyboardInterrupt:
            print()
            cprint(C.YELLOW, "  Interrupted — cancelling remaining hash operations...")
            pool.shutdown(wait=False, cancel_futures=True)
            raise
    print()  # newline after progress bar

    # ------------------------------------------------------------------
    # Stage 3: SHA-1 confirmation — group by (size, crc32, sha1)
    # Any bucket where 2+ files share size+CRC32+SHA-1 is a true duplicate.
    # CRC32-only matches that differ on SHA-1 are reported as near-collisions.
    # ------------------------------------------------------------------
    cprint(C.GRAY, "  Stage 3/3 — confirming by SHA-1...")
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
            # Same size+CRC32 but different SHA-1 — CRC32 collision, not duplicate
            # Exclude paths already reported as confirmed duplicates
            nc_paths = [p for g in sha_groups.values() for p, _, _, _ in g
                        if p not in confirmed_paths_here]
            if nc_paths:
                near_collisions.append((sz, crc, nc_paths))

    print()
    if near_collisions:
        cprint(C.YELLOW, f"  {len(near_collisions)} CRC32 collision(s) resolved by SHA-1"
                         " (same CRC32, different content — not duplicates):")
        for sz, crc, paths in near_collisions:
            cprint(C.YELLOW, f"    CRC32:{crc} size:{sz:,}B")
            for p in sorted(paths):
                cprint(C.GRAY, f"      - {p}")
        print()

    _report_duplicates(confirmed, empty_files, unreadable, all_rom_files)


def _report_duplicates(confirmed: list[list[tuple[Path, str, str, int]]],
                       empty_files: list[Path],
                       unreadable: list[Path],
                       all_rom_files: list[Path]) -> None:
    """Print the final duplicate report.
    confirmed: list of groups, each group is [(path, crc32_hex, sha1_hex, size_bytes), ...].
    """

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
        cprint(C.GREEN, "  No duplicates found!")
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
    cprint(C.CYAN, f"  Duplicate groups : {len(confirmed)}")
    cprint(C.CYAN, f"  Empty files      : {len(empty_files)}")
    cprint(C.CYAN, f"  Unreadable       : {len(unreadable)}")
    cprint(C.CYAN, "=============================================")
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
) -> None:
    """Resize all JPGs under base that aren't already the right size.

    target_dims : magick resize target (e.g. '512x512', '1920x1080').
    valid_dims  : set of already-correct dimension strings; defaults to {target_dims}.
    label       : display label used in progress messages.
    """
    if not cfg.magick:
        return
    if valid_dims is None:
        valid_dims = frozenset({target_dims})
    all_jpgs = list({                               # set() deduplicates on
        p                                           # case-insensitive FSes
        for pattern in ("*.jpg", "*.jpeg", "*.JPG", "*.JPEG")
        for p in base.rglob(pattern)
        if p.is_file()
    })
    cprint(C.CYAN, f"\n--- Checking {len(all_jpgs)} {label}(s) for resize (target {target_dims}) ---")

    dims_map         = batch_identify(cfg.magick, all_jpgs)
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

    print_lock   = threading.Lock()
    resize_done  = 0
    resize_total = len(needs_resize)
    resize_lock  = threading.Lock()

    def resize_one(jpg: Path):
        nonlocal resize_done
        try:
            magick_resize(cfg.magick, str(jpg), str(jpg), dims=target_dims)
            counters.inc("converted")
            with resize_lock:
                resize_done += 1
                rd = resize_done
            with print_lock:  # progress bar + filename printed atomically
                print(progress_bar(rd, resize_total, label="Resizing  "), end="", flush=True)
                cprint(C.DCYAN, f"  RESIZED  {jpg}")
        except Exception as e:
            with print_lock:
                cprint(C.DRED, f"  RESIZE FAIL  {jpg}: {e}")

    with ThreadPoolExecutor(max_workers=cfg.parallel_jobs) as pool:
        futures = [pool.submit(resize_one, jpg) for jpg in needs_resize]
        try:
            for fut in as_completed(futures):
                fut.result()
        except KeyboardInterrupt:
            cprint(C.YELLOW, "\n  Interrupted — cancelling remaining resize operations...")
            pool.shutdown(wait=False, cancel_futures=True)
            raise
    print()  # newline after progress bar


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
    download_mode  = cfg.download_mode
    cover_style    = cfg.cover_style
    delete_orphans = cfg.delete_orphans
    print()
    cprint(C.CYAN, "=============================================")
    if dry_run:
        cprint(C.MAGENTA, "  DRY RUN complete - nothing was changed")
        cprint(C.MAGENTA, "  Run with --no-dry-run to apply changes")
    else:
        cprint(C.GREEN, "  LIVE RUN complete")
    cprint(C.CYAN,    f"  Download mode      : {download_mode}")
    _STYLE_LABELS = {
        "with_logo":    "With logo (libretro/LaunchBox)",
        "without_logo": "Without logo (SGDB)",
        "game_logo":    "Game logo (libretro/LaunchBox/SGDB)",
    }
    cprint(C.CYAN,    f"  Cover style        : {_STYLE_LABELS.get(cover_style, cover_style)}")
    cprint(C.CYAN,    f"  Folders processed  : {len(common)}")
    cprint(C.YELLOW,  f"  Renamed (or would) : {counters.renamed}")
    if counters.duplicates:
        cprint(C.DRED,    f"  Duplicate covers   : {counters.duplicates} (run --delete-orphans to remove)" if not delete_orphans
                          else f"  Duplicate covers   : {counters.duplicates} (deleted)")
    cprint(C.CYAN,    f"  Downloaded         : {counters.downloaded}")
    cprint(C.GRAY,    f"  Skipped (exist)    : {counters.skipped}")
    if failed_covers:
        n_no_match = sum(1 for _, _, r in failed_covers if r.startswith("no match"))
        n_dl_fail  = sum(1 for _, _, r in failed_covers if r.startswith("download failed"))
        if n_dl_fail:
            cprint(C.DRED, f"  Download failures  : {n_dl_fail}")
        if n_no_match:
            cprint(C.DRED, f"  No repo match      : {n_no_match}")
        cprint(C.DRED, f"  Missing covers     : {len(failed_covers)} total (see report below)")
    cprint(C.DCYAN,   f"  Converted+Resized  : {counters.converted}")
    if delete_orphans:
        cprint(C.DRED, f"  Deleted (or would) : {counters.deleted}")
    else:
        cprint(C.RED,  f"  Unmatched kept     : {counters.missing}")
        if counters.missing:
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
        cprint(C.CYAN, f"  BG source          : {_BG_STYLE_LABELS.get(cfg.bg_style, cfg.bg_style)}")
        cprint(C.CYAN, "=============================================")
        cprint(C.YELLOW,  f"  Renamed (or would) : {bg_counters.renamed}")
        if bg_counters.duplicates:
            cprint(C.DRED,    f"  Duplicate BGs      : {bg_counters.duplicates}"
                              + (" (run --delete-orphans to remove)" if not cfg.delete_orphans
                                 else " (deleted)"))
        cprint(C.CYAN,    f"  Downloaded         : {bg_counters.downloaded}")
        cprint(C.GRAY,    f"  Skipped (exist)    : {bg_counters.skipped}")
        if failed_bgs:
            n_no_match = sum(1 for _, _, r in failed_bgs if "no game match" in r)
            n_no_hero  = sum(1 for _, _, r in failed_bgs if "no hero" in r)
            n_dl_fail  = sum(1 for _, _, r in failed_bgs if "download failed" in r)
            if n_dl_fail:
                cprint(C.DRED, f"  Download failures  : {n_dl_fail}")
            if n_no_match:
                cprint(C.DRED, f"  No SGDB match      : {n_no_match}")
            if n_no_hero:
                cprint(C.DRED, f"  No hero found      : {n_no_hero}")
            cprint(C.DRED, f"  Missing BGs        : {len(failed_bgs)} total")
        cprint(C.DCYAN,   f"  Converted+Resized  : {bg_counters.converted}")
        if delete_orphans:
            cprint(C.DRED, f"  Deleted (or would) : {bg_counters.deleted}")
        else:
            cprint(C.RED,  f"  Unmatched kept     : {bg_counters.missing}")
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
    script_dir: Path,
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
    lb_index = lbdb_load_index(cache_ttl, script_dir, script_stem)

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
                repo_name  = SYSTEM_MAP.get(folder.lower(), "")
                if repo_name:
                    libretro_folder = ("Named_Logos"
                                       if cfg.cover_style == "game_logo"
                                       else "Named_Boxarts")
                    repo_files = get_repo_file_list(
                        repo_name, cfg.github_token, cache_ttl, script_dir, script_stem,
                        folder_name=libretro_folder,
                    )

            process_folder(
                folder, roms_path, covers_path,
                cfg, repo_files, repo_name,
                counters, orphans, failed_covers,
                lb_index=lb_index,
            )

        if cfg.delete_orphans and orphans:
            cprint(C.DRED, f"\n--- Deleting {len(orphans)} orphan cover(s) ---")
            for path in orphans:
                if not cfg.dry_run:
                    Path(path).unlink(missing_ok=True)
                counters.inc("deleted")
            print()

        if not cfg.dry_run:
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
                bg_repo_name = SYSTEM_MAP.get(folder.lower(), "")
                if bg_repo_name:
                    bg_repo_files = get_repo_file_list(
                        bg_repo_name, cfg.github_token, cache_ttl,
                        script_dir, script_stem,
                        folder_name="Named_Boxarts",
                    )
            process_bg_folder(
                folder, roms_path, bgs_path,
                cfg, bg_counters, bg_orphans, failed_bgs,
                lb_index=lb_index,
                repo_files=bg_repo_files,
                repo_name=bg_repo_name,
            )

        if cfg.delete_orphans and bg_orphans:
            cprint(C.DRED, f"\n--- Deleting {len(bg_orphans)} orphan background(s) ---")
            for path in bg_orphans:
                if not cfg.dry_run:
                    Path(path).unlink(missing_ok=True)
                bg_counters.inc("deleted")
            print()

        if not cfg.dry_run:
            _resize_pass(bgs_base, cfg, bg_counters, target_dims="1920x1080", valid_dims=frozenset(VALID_BG_DIMS), label="background JPG")

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
    cprint(C.CYAN, "  ║         sync-covers  wizard          ║")
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
    """Prompt for SteamGridDB API key.

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
        key = input(prompt).strip()
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
    Contains all branching logic for cover and background styles so _wizard
    stays at a high level.
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
                # SGDB logos are a tertiary fallback for game_logo — key is optional
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
        sgdb_key = _prompt_sgdb_key(sgdb_key)
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
    task_ch = prompt_choice("  What would you like to do?", {
        "1": f"{C.GREEN}Check duplicate ROMs{C.RESET}",
        "2": f"{C.CYAN}Download covers + backgrounds{C.RESET}",
        "3": f"{C.CYAN}Download covers only{C.RESET}",
        "4": f"{C.CYAN}Download backgrounds only{C.RESET}",
    })
    print()

    need_covers = task_ch in ("2", "3")
    need_bgs    = task_ch in ("2", "4")
    is_dup      = task_ch == "1"

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
        check_duplicates(roms_base, common, single_system, args.parallel_jobs)
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
        report_path = script_dir / f"sync-covers_report_{ts}.txt"

    # ── 12. Confirm ───────────────────────────────────────────────────
    task_label = {
        "2": "covers + backgrounds",
        "3": "covers only",
        "4": "backgrounds only",
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
        task        = {"2":"both","3":"covers","4":"backgrounds"}[task_ch],
        roms_base   = roms_base,
        covers_base = covers_base,
        bgs_base    = bgs_base,
        cfg         = cfg,
        common      = common,
        single_system = single_system,
        cache_ttl   = args.cache_ttl,
        script_dir  = script_dir,
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
        description="Sync cover art to ROM library.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
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
    parser.add_argument("--cover-style",      default="with-logo",
                        choices=["with-logo", "without-logo", "game-logo"],
                        help="Cover art style: with-logo (box art), without-logo (SGDB grids → LB Screenshot, key optional), game-logo (title art)")
    parser.add_argument("--bg-style",         default="fanart",
                        choices=["fanart", "boxart"],
                        help="Background art style: fanart (SGDB Heroes/LB Fanart) or boxart (box art letterboxed to 1920x1080)")
    parser.add_argument("--region",           default="any",
                        choices=["any", "usa", "europe", "japan", "world"],
                        help="Preferred cover region (default: any)")
    parser.add_argument("--sgdb-key",         default=os.environ.get("SGDB_KEY", ""),
                        help="SteamGridDB API key. Also read from SGDB_KEY env var.")
    parser.add_argument("--check-duplicates", action="store_true",
                        help="Scan ROMs for duplicates (runs instead of cover sync)")
    parser.add_argument("--threshold",        type=float, default=0.4,
                        help="Fuzzy match threshold 0.0-1.0 (default 0.4)")
    parser.add_argument("--parallel-jobs",    type=int,   default=6,
                        help="Parallel download workers (default 6)")
    parser.add_argument("--cache-ttl",        type=int,   default=24,
                        help="GitHub API cache TTL in hours (default 24)")
    parser.add_argument("--http-timeout",     type=int,   default=30,
                        help="HTTP request timeout in seconds (default 30)")
    parser.add_argument("--github-token",     default=os.environ.get("GITHUB_TOKEN", ""),
                        help="GitHub personal access token")
    parser.add_argument("--report",           default="",
                        help="Report file path. Defaults to sync-covers_report_YYYYMMDD_HHMMSS.txt "
                             "next to the script. Pass 'none' to disable.")
    args = parser.parse_args()

    dry_run = not args.no_dry_run
    magick  = find_magick()
    token   = args.github_token or None

    # ------------------------------------------------------------------
    # Wizard mode: no substantive args provided
    # ------------------------------------------------------------------
    wizard_mode = not args.roms and not args.covers and not args.backgrounds and not args.check_duplicates

    if wizard_mode:
        _wizard(dry_run, magick, token, args, script_dir, script_stem)
        return

    # ------------------------------------------------------------------
    # CLI mode: all args provided on command line
    # ------------------------------------------------------------------

    # Duplicate detection
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
        check_duplicates(roms_base, common, single_system, args.parallel_jobs)
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
    cover_style      = args.cover_style.replace("-", "_")
    preferred_region = args.region
    sgdb_key         = args.sgdb_key or None
    delete_orphans   = args.delete_orphans

    # Determine task
    if covers_base and bgs_base:
        task = "both"
    elif bgs_base:
        task = "backgrounds"
    else:
        task = "covers"

    # System detection
    common, single_system = _detect_systems(roms_base, args.system)
    if single_system and not common:
        common = [prompt_system()]
    elif not common:
        cprint(C.RED, f"  No ROM subfolders found in: {roms_base}")
        sys.exit(1)

    # Create dirs
    for base, label in [(covers_base, "covers"), (bgs_base, "backgrounds")]:
        if base:
            _ensure_art_dir(base, label, dry_run)

    # Banner
    print()
    cprint(C.CYAN, "=============================================")
    cprint(C.CYAN, "  sync-covers.py  (CLI mode)")
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
        _STYLE_LABELS_CLI = {
            "with_logo":    "with logo",
            "without_logo": "without logo (SGDB)",
            "game_logo":    "game logo",
        }
        cprint(C.CYAN, f"  Style       : {_STYLE_LABELS_CLI.get(cover_style, cover_style)}")
    if task in ("backgrounds", "both"):
        _BG_STYLE_LABELS_CLI = {"fanart": "fanart/heroes", "boxart": "box art (letterboxed)"}
        cprint(C.CYAN, f"  BG style    : {_BG_STYLE_LABELS_CLI.get(args.bg_style, args.bg_style)}")
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
        report_path = script_dir / f"sync-covers_report_{ts}.txt"

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
        script_dir  = script_dir,
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
