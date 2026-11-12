#!/bin/bash
# Sidenote for Mac - installer
# Installs what Sidenote needs and adds it to the Claude desktop app.
set -e
DIR="$(cd "$(dirname "$0")" && pwd)"
VENV="$DIR/.venv"
echo "Installing Sidenote from: $DIR"

# Find a Python 3.10+ that includes tkinter (python.org installer has both)
PY=""
for c in /Library/Frameworks/Python.framework/Versions/Current/bin/python3 /opt/homebrew/bin/python3 /usr/local/bin/python3 python3; do
  if command -v "$c" >/dev/null 2>&1 && "$c" -c 'import sys, tkinter; sys.exit(0 if sys.version_info >= (3, 10) else 1)' >/dev/null 2>&1; then
    PY="$c"; break
  fi
done
if [ -z "$PY" ]; then
  echo "Sidenote needs Python 3.10 or newer."
  echo "Install it from https://www.python.org/downloads/ (the macOS installer), then run this again."
  exit 1
fi
echo "Using $("$PY" --version) at $PY"
[ -d "$VENV" ] || "$PY" -m venv "$VENV"
"$VENV/bin/python" -m pip install --quiet --upgrade pip
"$VENV/bin/python" -m pip install --quiet mcp pyobjc-framework-ApplicationServices pyobjc-framework-Cocoa pyobjc-framework-Quartz pyobjc-framework-AVFoundation sounddevice numpy faster-whisper
echo "Libraries installed."

"$VENV/bin/python" - "$VENV/bin/python" "$DIR/sidenote.py" <<'PY'
import json, os, sys, shutil, time
python, script = sys.argv[1], sys.argv[2]
cfg_dir = os.path.expanduser("~/Library/Application Support/Claude")
cfg = os.path.join(cfg_dir, "claude_desktop_config.json")
os.makedirs(cfg_dir, exist_ok=True)
data = {}
if os.path.exists(cfg):
    shutil.copy(cfg, cfg + f".backup-{int(time.time())}")
    try:
        with open(cfg) as f:
            data = json.load(f)
    except Exception:
        print("Warning: the existing Claude config could not be read; a backup was kept.")
        data = {}
data.setdefault("mcpServers", {})["sidenote"] = {"command": python, "args": [script]}
with open(cfg, "w") as f:
    json.dump(data, f, indent=2)
print("Added Sidenote to the Claude desktop app.")
PY

echo ""
echo "Done. Next:"
echo "  1. Quit Claude completely (Cmd+Q) and open it again."
echo "  2. System Settings > Privacy & Security > Device Control and Data Access"
echo "     (called Accessibility on older macOS): turn ON Claude."
echo "  3. In Claude, type: open Sidenote"
echo "  4. Google Meet: Sidenote turns on Meet's captions by itself (press CC if"
echo "     they don't come on). For other apps, it turns on macOS Live Captions."
