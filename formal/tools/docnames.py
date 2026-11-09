#!/usr/bin/env python3
"""Names the documentation cites that no Lean file declares or mentions.

  python3 -I tools/docnames.py [FILE ...]     (default: statement.tex and every README.md)

A backticked name that looks like a Lean declaration (`foo_bar`, `Foo.barBaz`, `fooBar`) and does not
appear in any `.lean` file of the six projects is printed with its place: most are declarations
renamed or removed since the prose was written. The prose also cites leanVM's Rust and Python, so
some hits are not Lean names; read them, do not trust the list blindly.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROJECTS = ["Statement", "common", "lean_xmss", "lean_sphincs", "lean_da", "lean_vm"]
CITED = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.]*[A-Za-z0-9_'])`")
LEANISH = re.compile(r"(_|[a-z][A-Z]|\.[A-Za-z])")
NOT_LEAN = re.compile(r"\.(lean|md|py|rs|toml|sh|tex|json|txt|bin|yml)$|^(crates|scripts|tests)\b")


def docs(args):
    if args:
        return args
    found = [os.path.join(ROOT, "statement.tex")]
    for top, dirs, names in os.walk(ROOT):
        dirs[:] = [d for d in dirs if not d.startswith(".") and d not in ("scripts",)]
        found += [os.path.join(top, n) for n in names if n == "README.md"]
    return [f for f in found if os.path.exists(f)]


def lean_words():
    words = set()
    for project in PROJECTS:
        for top, dirs, names in os.walk(os.path.join(ROOT, project)):
            dirs[:] = [d for d in dirs if d != ".lake"]
            for n in names:
                if n.endswith(".lean"):
                    with open(os.path.join(top, n), encoding="utf-8") as f:
                        words.update(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", f.read()))
    # a qualified name is found when its last components are
    parts = set()
    for w in words:
        pieces = w.split(".")
        for i in range(len(pieces)):
            parts.add(".".join(pieces[i:]))
    return parts


def main():
    known = lean_words()
    missing = 0
    for path in docs(sys.argv[1:]):
        with open(path, encoding="utf-8") as f:
            for n, line in enumerate(f, 1):
                for name in CITED.findall(line):
                    if NOT_LEAN.search(name) or not LEANISH.search(name):
                        continue
                    if name in known or name.split(".")[-1] in known:
                        continue
                    print(f"{os.path.relpath(path, ROOT)}:{n}: `{name}`")
                    missing += 1
    print(f"{missing} cited names found in no Lean file", file=sys.stderr)


if __name__ == "__main__":
    main()
