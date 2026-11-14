#!/usr/bin/env python3
"""The private-import firewall, checked against Lake: what an edit rebuilds is what `deps.py` says.

  python3 -I tools/firewall-canary.py        (after a build of lean_vm's `LeanVMTests`)

The per-function layout (`notes/per-function-cone.md`) rests on Lake's rule that a module sees its
imports' public closures only, so that a private `import` stops a rebuild. The canary
(`lean_vm/tests/LeanVMTests/Firewall/`: `Data`, `Check` publicly importing it, `Link` importing
`Check` privately, `Use` importing `Link`, `Legacy` outside the module system) edits `Data` twice,
its interface (a declaration added) and a proof only, builds the canary (a few seconds: it imports
nothing else), and fails unless the modules Lake rebuilds are those `deps.py` names and `Use` is
never among them. (`lake build --no-build` cannot tell: it calls stale whatever is below a module
that needs a build.) `Data` is restored and the canary rebuilt after each edit, so the run leaves
the build as it found it.
"""
import os
import re
import subprocess
import sys

TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
import deps  # noqa: E402

LEAN_VM = os.path.join(deps.ROOT, "lean_vm")
PREFIX = "LeanVMTests.Firewall."
MODS = [PREFIX + m for m in ("Data", "Check", "Link", "Use", "Legacy")]
DATA = os.path.join(LEAN_VM, "tests", "LeanVMTests", "Firewall", "Data.lean")
EDITS = {
    "interface": ("end\nend LeanVMTests.Firewall\n",
                  "def stamp : Nat := 0\n\nend\nend LeanVMTests.Firewall\n"),
    "proof": ("theorem value_pos : 0 < value := by decide\n",
              "theorem value_pos : 0 < value := Nat.one_pos\n"),
}


def build():
    """The canary's modules Lake builds now."""
    r = subprocess.run(["lake", "build", *MODS], cwd=LEAN_VM, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"firewall-canary: the canary does not build:\n{r.stdout}{r.stderr}")
    return set(re.findall(r"Built (" + re.escape(PREFIX) + r"\w+)", r.stdout + r.stderr))


def main():
    edges, _, legacy = deps.read_graph()
    if not all(m in edges for m in MODS):
        sys.exit("firewall-canary: the canary's modules are missing")
    g = deps.Graph(edges, legacy)
    src = PREFIX + "Data"
    expect = {
        "interface": {src} | (g.cone([src]) & set(MODS)),
        "proof": {src} | (g.cone([src], any_edit=True) & set(MODS)),
    }
    if PREFIX + "Use" in expect["interface"] | expect["proof"]:
        sys.exit("firewall-canary: deps.py sees through the private import")
    build()
    original = open(DATA, encoding="utf-8").read()
    failed = False
    try:
        for kind, (old, new) in EDITS.items():
            assert original.count(old) == 1, kind
            with open(DATA, "w", encoding="utf-8") as f:
                f.write(original.replace(old, new))
            got = build()
            with open(DATA, "w", encoding="utf-8") as f:
                f.write(original)
            build()
            ok = got == expect[kind]
            failed |= not ok
            print(f"{kind} edit of Data: rebuilt {sorted(m[len(PREFIX):] for m in got)}"
                  + ("" if ok else f", expected {sorted(m[len(PREFIX):] for m in expect[kind])}"))
    finally:
        with open(DATA, "w", encoding="utf-8") as f:
            f.write(original)
    if failed:
        sys.exit("firewall-canary: Lake's rebuilds differ from deps.py's rule")
    print("firewall-canary: ok")


if __name__ == "__main__":
    main()
