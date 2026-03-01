# rom-assets-manager

Download and sync cover art, backgrounds, and game logos to a ROM library.

**Sources:** libretro-thumbnails (GitHub) · SteamGridDB · LaunchBox GamesDB
**Requires:** Python 3.8+ · ImageMagick · no external pip dependencies

---

## Features

- **Cover art sync** — fetches box art from the [libretro-thumbnails](https://github.com/libretro-thumbnails) GitHub repos and falls back to SteamGridDB / LaunchBox GamesDB for missing titles
- **Background sync** — downloads hero/fanart images (SGDB Heroes or LaunchBox Fanart-Background) or letterboxes box art to 1920×1080
- **Game logos** — downloads transparent title-art logos from libretro-thumbnails (`Named_Logos`) or SteamGridDB
- **Smart system detection** — three-tier folder resolver: exact name → alias table → content inspection (extension profiling + ROM header sniffing)
- **Fuzzy matching** — multi-stage similarity scoring (exact → prefix → substring → Jaccard) with optional region preference (USA / Europe / Japan / World)
- **Duplicate ROM detection** — four-stage pipeline: file size → CRC32 → SHA-1 → title-name fuzzy grouping; interactive cleanup prompt
- **Completeness checker** — compare a ROM folder against a No-Intro Logiqx XML DAT file; outputs a CSV and optional want-list
- **Orphan cleanup** — optionally deletes covers/backgrounds that have no matching ROM
- **Image resizing** — auto-resizes covers to 512×512 and backgrounds to 1920×1080 via ImageMagick (letterboxed, black bars)
- **Parallel downloads** — configurable worker pool (default: 6)
- **TTL-cached API responses** — GitHub tree lists and LaunchBox Metadata cached to `%TEMP%/rom-assets-manager/` to avoid redundant requests
- **Dry-run mode** — preview all changes without touching any file
- **Run report** — summary written to a plain-text file alongside the script
- **Interactive wizard** — guided step-by-step setup when launched with no arguments
- **Cross-platform** — Windows, Linux, macOS; ANSI colour auto-enabled on Windows 10+

---

## Requirements

### Python
Python 3.8 or newer. No `pip install` needed — the script uses only the standard library.

### ImageMagick
Required for image conversion and resizing.

```bash
# Windows
winget install ImageMagick.Q16-HDRI

# Debian / Ubuntu
sudo apt install imagemagick

# macOS
brew install imagemagick
```

### API keys (optional but recommended)

| Key | Where to get it | Used for |
|-----|----------------|----------|
| `GITHUB_TOKEN` | [github.com/settings/tokens](https://github.com/settings/tokens) | Raises GitHub API rate limit from 60 to 5000 req/h |
| `SGDB_KEY` | [steamgriddb.com/profile/preferences](https://www.steamgriddb.com/profile/preferences) | SteamGridDB cover/hero/logo downloads |

Set them as environment variables (recommended) or pass them via CLI flags:

```bash
export GITHUB_TOKEN=ghp_...
export SGDB_KEY=...
```

---

## Usage

### Interactive wizard

Run with no arguments to launch the guided setup:

```bash
python rom-assets-manager.py
```

### CLI mode

```
python rom-assets-manager.py [OPTIONS]
python rom-assets-manager.py --help
```

#### Core paths

| Flag | Description |
|------|-------------|
| `--roms PATH` | ROMs root folder |
| `--covers PATH` | Covers output folder |
| `--backgrounds PATH` | Backgrounds output folder |
| `--system NAME` | Limit to a single system (e.g. `snes`, `psx`, `gba`) |

#### Sync behaviour

| Flag | Default | Description |
|------|---------|-------------|
| `--no-dry-run` | *(dry run)* | Apply changes — without this flag nothing is written |
| `--download-mode` | `missing` | `missing` · `all` · `skip` |
| `--delete-orphans` | off | Delete art files that have no matching ROM |
| `--cover-style` | `with_logo` | `with_logo` (box art + system logo) · `without_logo` (SGDB grids / LB screenshot) · `game_logo` (transparent title art) |
| `--bg-style` | `fanart` | `fanart` (SGDB Heroes / LB Fanart-Background) · `boxart` (box art letterboxed to 1920×1080) |
| `--region` | `any` | `any` · `usa` · `europe` · `japan` · `world` |

#### Matching & performance

| Flag | Default | Description |
|------|---------|-------------|
| `--threshold` | `0.4` | Fuzzy match threshold 0.0–1.0 |
| `--parallel-jobs` | `6` | Parallel download workers |
| `--cache-ttl` | `24` | GitHub API cache TTL in hours |
| `--http-timeout` | `30` | Per-request HTTP timeout in seconds |

#### Credentials

| Flag | Description |
|------|-------------|
| `--github-token TOKEN` | GitHub PAT (prefer `GITHUB_TOKEN` env var) |
| `--sgdb-key KEY` | SteamGridDB API key (prefer `SGDB_KEY` env var) |

#### Extra tools

| Flag | Description |
|------|-------------|
| `--check-duplicates` | Scan ROMs for duplicates instead of syncing art |
| `--check-completeness` | Compare ROMs against a No-Intro DAT file |
| `--dat PATH` | Path to No-Intro Logiqx XML DAT (required with `--check-completeness`) |
| `--completeness-region` | `usa` · `europe` · `japan` · `japan_exclusive` · `all` |
| `--want-list` | Save a plain-text list of missing titles (with `--check-completeness`) |
| `--report PATH` | Report output path; pass `none` to disable |

---

## Examples

```bash
# Wizard (recommended for first run)
python rom-assets-manager.py

# Sync missing covers for all systems — dry run (preview only)
python rom-assets-manager.py --roms /media/roms --covers /media/covers

# Apply the sync for real
python rom-assets-manager.py --roms /media/roms --covers /media/covers --no-dry-run

# Sync backgrounds only, using SGDB Heroes
python rom-assets-manager.py --roms /media/roms --backgrounds /media/bgs --no-dry-run

# Sync both covers and backgrounds, prefer USA region
python rom-assets-manager.py \
  --roms /media/roms \
  --covers /media/covers \
  --backgrounds /media/bgs \
  --region usa \
  --no-dry-run

# Single-system cover sync
python rom-assets-manager.py \
  --roms /media/roms/snes \
  --covers /media/covers/snes \
  --system snes \
  --no-dry-run

# Check for duplicate ROMs
python rom-assets-manager.py --roms /media/roms --check-duplicates

# Check SNES collection completeness against a No-Intro DAT
python rom-assets-manager.py \
  --roms /media/roms/snes \
  --check-completeness \
  --dat "Nintendo - Super Nintendo Entertainment System.dat" \
  --completeness-region usa \
  --want-list
```

---

## Supported systems

The following folder names are recognised automatically (case-insensitive, separators flexible):

| Key | System |
|-----|--------|
| `nes` | Nintendo Entertainment System |
| `fds` | Family Computer Disk System |
| `snes` | Super Nintendo Entertainment System |
| `virtualboy` | Virtual Boy |
| `n64` | Nintendo 64 |
| `gamecube` | GameCube |
| `wii` | Wii |
| `wiiu` | Wii U |
| `gb` / `gbc` / `gba` | Game Boy / Color / Advance |
| `ds` / `3ds` | Nintendo DS / 3DS |
| `genesis` / `megadrive` | Sega Mega Drive / Genesis |
| `32x` | Sega 32X |
| `sega-cd` | Sega CD / Mega-CD |
| `game-gear` | Game Gear |
| `master-system` | Master System |
| `saturn` | Sega Saturn |
| `dc` | Dreamcast |
| `psx` / `ps2` / `ps3` / `ps4` | PlayStation 1–4 |
| `psp` | PlayStation Portable |
| `atari2600` / `atari5200` / `atari7800` | Atari 2600 / 5200 / 7800 |
| `atari-st` | Atari ST |
| `jaguar` / `lynx` | Atari Jaguar / Lynx |
| `pce` / `pce-cd` | PC Engine / TurboGrafx-16 / CD |
| `neogeo` / `neogeocd` | Neo Geo / CD |
| `ngp` / `ngpc` | Neo Geo Pocket / Color |
| `wonderswan` / `wonderswancolor` | WonderSwan / Color |
| `coleco` | ColecoVision |
| `vectrex` | Vectrex |
| `msx` / `msx2` | MSX / MSX2 |
| `x68000` | Sharp X68000 |
| `scummvm` | ScummVM |

Many common naming variants (e.g. `"Nintendo 64"`, `"Super Nintendo"`, `"Sega Genesis"`, `"PlayStation 2"`) are resolved automatically via an alias table. Folders that don't match by name are identified by ROM file extensions and, as a last resort, by reading ROM header magic bytes.

---

## How art sources are prioritised

### Covers (`--cover-style with_logo` — default)
1. **libretro-thumbnails** (`Named_Boxarts`) — fuzzy-matched against the repo file list
2. **LaunchBox GamesDB** — offline XML index (Box-Front images)
3. **SteamGridDB** — vertical grids (600×900 or 342×482), requires `SGDB_KEY`

### Covers (`--cover-style without_logo`)
1. **SteamGridDB grids** (no system logo overlay), requires `SGDB_KEY`
2. **LaunchBox GamesDB** Screenshot-Game-Title

### Covers (`--cover-style game_logo`)
1. **libretro-thumbnails** (`Named_Logos`) — transparent title art
2. **SteamGridDB logos**, requires `SGDB_KEY`
3. **LaunchBox GamesDB** Clear Logo

### Backgrounds (`--bg-style fanart` — default)
1. **SteamGridDB Heroes**, requires `SGDB_KEY`
2. **LaunchBox GamesDB** Fanart-Background

### Backgrounds (`--bg-style boxart`)
1. **libretro-thumbnails** (`Named_Boxarts`) — letterboxed to 1920×1080

---

## File layout

The script is a single self-contained file. Caches are written to your system temp directory and are never committed:

```
rom-assets-manager.py        ← the script
rom-assets-manager_report_YYYYMMDD_HHMMSS.txt   ← run report (auto-generated)

%TEMP%/rom-assets-manager/   ← API response cache (auto-managed)
```

---

## License

[MIT](LICENSE)
