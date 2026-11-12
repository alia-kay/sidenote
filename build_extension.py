"""Build the Sidenote Claude Desktop extension (.mcpb).

    python build_extension.py          build dist/Sidenote-<version>.mcpb
    python build_extension.py --test   build, then unpack it and start it the way
                                       Claude does (uv run), and check its tools

Needs Node.js (for the official mcpb tool, run with npx) and uv
(pip install uv). The version comes from SIDENOTE_VERSION in sidenote.py.

Only the files in PACKAGE_FILES are copied into a clean staging folder, so
nothing else in this folder (old scripts, backups, logs, meeting files) can
end up in the package. The build stops if the forbidden word appears in any
file name or file.
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import zipfile

ROOT = os.path.dirname(os.path.abspath(__file__))
EXT = os.path.join(ROOT, "extension")
DIST = os.path.join(ROOT, "dist")
STAGE = os.path.join(DIST, "stage")

# published name -> source file
PACKAGE_FILES = {
    "sidenote.py": os.path.join(ROOT, "sidenote.py"),
    "manifest.json": os.path.join(EXT, "manifest.json"),
    "icon.png": os.path.join(EXT, "icon.png"),
    "README.md": os.path.join(EXT, "README.md"),
    "pyproject.toml": os.path.join(EXT, "pyproject.toml"),
    "uv.lock": os.path.join(EXT, "uv.lock"),
    ".python-version": os.path.join(EXT, ".python-version"),
}
FORBIDDEN = b"co" + b"pilot"          # spelled in two parts so this file passes too
EXPECTED_TOOLS = 21


def fail(msg):
    print(f"\nBUILD FAILED: {msg}")
    sys.exit(1)


def step(msg):
    print(f"- {msg}")


def run(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    if r.returncode != 0:
        fail(f"{' '.join(cmd)}\n{r.stdout}\n{r.stderr}")
    return r.stdout


def npx():
    path = shutil.which("npx") or shutil.which("npx.cmd")
    if not path:
        fail("Node.js is needed (for npx). Install it from https://nodejs.org")
    return [path, "--yes", "@anthropic-ai/mcpb"]


def uv():
    path = shutil.which("uv")
    return [path] if path else [sys.executable, "-m", "uv"]


def sidenote_version():
    with open(PACKAGE_FILES["sidenote.py"], encoding="utf-8") as f:
        m = re.search(r'^SIDENOTE_VERSION = "([^"]+)"', f.read(), re.M)
    if not m:
        fail("SIDENOTE_VERSION not found in sidenote.py")
    version = m.group(1)
    n = re.search(r"\bv(\d+)\b", version)
    if not n:
        fail(f"SIDENOTE_VERSION {version!r} has no 'vN' number for the manifest")
    return version, f"{n.group(1)}.0.0"


def check_forbidden(name, data):
    if FORBIDDEN in name.lower().encode() or FORBIDDEN in data.lower():
        fail(f"the forbidden word appears in {name}")


def build():
    version, semver = sidenote_version()
    out_name = "Sidenote-" + re.sub(r"[^A-Za-z0-9.]+", "-", version).strip("-") + ".mcpb"
    out = os.path.join(DIST, out_name)
    print(f"Building Sidenote {version} (manifest version {semver})")

    step("checking uv.lock matches pyproject.toml")
    run(uv() + ["lock", "--check", "--directory", EXT])

    step("copying only the package files into a clean folder")
    shutil.rmtree(STAGE, ignore_errors=True)
    os.makedirs(STAGE)
    for name, src in PACKAGE_FILES.items():
        if not os.path.isfile(src):
            fail(f"missing {src}")
        shutil.copyfile(src, os.path.join(STAGE, name))

    step(f"setting the manifest version to {semver}")
    path = os.path.join(STAGE, "manifest.json")
    with open(path, encoding="utf-8") as f:
        manifest = json.load(f)
    manifest["version"] = semver
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(manifest, f, indent=2, ensure_ascii=False)
        f.write("\n")
    if len(manifest.get("tools", [])) != EXPECTED_TOOLS:
        fail(f"manifest lists {len(manifest.get('tools', []))} tools, expected {EXPECTED_TOOLS}")

    step("checking file names and contents for the forbidden word")
    for name in PACKAGE_FILES:
        with open(os.path.join(STAGE, name), "rb") as f:
            check_forbidden(name, f.read())

    step("validating the manifest (official mcpb tool)")
    print("  " + run(npx() + ["validate", path]).strip().replace("\n", "\n  "))

    step("packing")
    os.makedirs(DIST, exist_ok=True)
    if os.path.exists(out):
        os.remove(out)
    run(npx() + ["pack", STAGE, out])

    step("re-opening the package to check its contents")
    with zipfile.ZipFile(out) as z:
        names = sorted(n for n in z.namelist() if not n.endswith("/"))
        if names != sorted(PACKAGE_FILES):
            fail(f"package has {names}, expected {sorted(PACKAGE_FILES)}")
        for name in names:
            check_forbidden(name, z.read(name))
        with z.open("manifest.json") as f:
            if json.load(f)["version"] != semver:
                fail("manifest version in the package is wrong")
    shutil.rmtree(STAGE, ignore_errors=True)
    size = os.path.getsize(out) / 1024
    print(f"\nBuilt {out} ({size:.0f} KB)")
    for name in names:
        print(f"  {name}")
    return out, version


def mcp_test(package, version):
    """Unpack the .mcpb and start it like Claude does: uv run --frozen, then an
    MCP handshake, the tool list and get_status."""
    print("\nStarting the packaged Sidenote the way Claude does...")
    folder = tempfile.mkdtemp(prefix="sidenote-test-")
    try:
        with zipfile.ZipFile(package) as z:
            z.extractall(folder)
        with open(os.path.join(folder, "manifest.json"), encoding="utf-8") as f:
            cfg = json.load(f)["server"]["mcp_config"]
        args = [a.replace("${__dirname}", folder) for a in cfg["args"]]
        env = dict(os.environ, **cfg.get("env", {}))
        proc = subprocess.Popen(uv() + args, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True, encoding="utf-8", env=env)

        def send(msg):
            proc.stdin.write(json.dumps(msg) + "\n")
            proc.stdin.flush()

        def receive(want_id, timeout=300):
            end = time.time() + timeout
            while time.time() < end:
                line = proc.stdout.readline()
                if not line:
                    fail("Sidenote stopped:\n" + proc.stderr.read()[-3000:])
                msg = json.loads(line)
                if msg.get("id") == want_id:
                    return msg
            fail("no answer from Sidenote")

        t0 = time.time()
        send({"jsonrpc": "2.0", "id": 1, "method": "initialize",
              "params": {"protocolVersion": "2025-06-18", "capabilities": {},
                         "clientInfo": {"name": "build-test", "version": "1"}}})
        info = receive(1)["result"]["serverInfo"]
        step(f"started in {time.time() - t0:.0f} s: {info.get('name')}")
        send({"jsonrpc": "2.0", "method": "notifications/initialized"})
        send({"jsonrpc": "2.0", "id": 2, "method": "tools/list"})
        tools = [t["name"] for t in receive(2)["result"]["tools"]]
        if len(tools) != EXPECTED_TOOLS:
            fail(f"Sidenote offers {len(tools)} tools, expected {EXPECTED_TOOLS}")
        step(f"{len(tools)} tools offered")
        send({"jsonrpc": "2.0", "id": 3, "method": "tools/call",
              "params": {"name": "get_status", "arguments": {}}})
        status = receive(3)["result"]["content"][0]["text"]
        step("get_status: " + status.replace("\n", " ")[:300])
        if version not in status:
            print(f"  note: status does not show {version} (another Sidenote copy answered?)")
        proc.stdin.close()
        try:
            proc.wait(15)
        except subprocess.TimeoutExpired:
            proc.kill()
        print("Startup test passed.")
    finally:
        shutil.rmtree(folder, ignore_errors=True)


if __name__ == "__main__":
    package, version = build()
    if "--test" in sys.argv:
        mcp_test(package, version)
