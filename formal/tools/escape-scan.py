#!/usr/bin/env python3
"""Forbid proof escapes in the `.lean` files under the given directories.

  python3 -I tools/escape-scan.py DIR...

Fails, listing each hit as `file:line: text`, on any of these outside comments:

* `sorry`, `sorryAx`, `admit`, `admitGoal`, `native_decide`, `decide +native` (`+native`), `unsafe`,
  `implemented_by`, `@[extern]` and `#exit`;
* the keyword `axiom` anywhere, so an `axiom` declaration whatever comes before it (`private axiom`,
  `meta axiom`, `@[simp] axiom`, `open Nat in axiom`, ...);
* the ways to skip the kernel that `#print axioms` cannot see: `skipKernelTC`, `addDeclCore`,
  `addDeclWithoutChecking`, `doCheck`, `ofReduceBool`, `trustCompiler`, and adding to the environment
  past `addDecl`: `addConstAsync`, `commitConst`, `Kernel.Environment.add`, `setEnv` (`ALLOWED` lists
  the benign uses).

Comments (`--` to the end of the line, `/- ... -/` nested, docstrings included) are blanked
before the search, keeping the lines, so a forbidden word in a comment passes and one in code
after a comment on the same line does not. String, raw string (`r"..."`, `r#"..."#`) and character
literals are kept as code (a `--` or `/-` inside one opens no comment). Directories named `.lake`
are skipped, and symbolic links are not followed. `.lean` files only, so `lake-build.py`'s `--dev`,
which names `skipKernelTC`, is exempt. The CI (`.github/workflows/lean.yml`) and `check-all.sh` both
run it.
"""
import os
import re
import sys

WORDS = ("sorry|sorryAx|admit|admitGoal|native_decide|unsafe|implemented_by|skipKernelTC|addDeclCore|"
         "addDeclWithoutChecking|doCheck|ofReduceBool|trustCompiler|addConstAsync|commitConst|"
         "Environment\\.add|setEnv")
PATTERN = re.compile(
    r"\b(?:" + WORDS + r")\b"
    r"|#exit\b"
    r"|\+native\b"
    r"|(?:@|\battribute\s*)\[[^\]]*\bextern\b"
    r"|(?<![.«`'])\baxiom\b(?!['?!])")

# Every hit contains one of these words, and blanking comments only removes text: a file without
# any of them needs no scan.
QUICK = re.compile(r"(?:" + WORDS + r"|#exit|\+native|extern|axiom)")

# The benign uses, by file (its path's end) and word: `copyDecl` sets compiler attributes on a
# declaration `addDecl` added.
ALLOWED = {("LeanVM/Prover/Fast/Copy.lean", "setEnv")}

RAW = re.compile(r'r(#*)"')

CHAR = re.compile(r"'(?:\\[^']{1,8}|[^'\\\n])'")


def strip_comments(text: str) -> str:
    """The text with every comment's characters replaced by spaces (newlines kept)."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        c = text[i]
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif c == "r" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'!?.")) \
                and RAW.match(text, i):
            m = RAW.match(text, i)
            j = text.find('"' + m.group(1), m.end())
            j = n if j < 0 else j + 1 + len(m.group(1))
            out.append(text[i:j])
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif c == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'!?")) \
                and CHAR.match(text, i):
            m = CHAR.match(text, i)
            out.append(m.group(0))
            i = m.end()
        else:
            out.append(c)
            i += 1
    return "".join(out)


def scan(path: str) -> list[str]:
    with open(path, encoding="utf-8") as f:
        text = f.read()
    if not QUICK.search(text):
        return []
    hits = []
    original = text.split("\n")
    allowed = {w for f, w in ALLOWED if path.replace(os.sep, "/").endswith(f)}
    for k, line in enumerate(strip_comments(text).split("\n")):
        if any(m.group(0) not in allowed for m in PATTERN.finditer(line)):
            hits.append(f"{path}:{k + 1}: {original[k].strip()}")
    return hits


def main(dirs: list[str]) -> int:
    if not dirs:
        print(__doc__, file=sys.stderr)
        return 2
    hits = []
    for d in dirs:
        if os.path.isfile(d):
            hits += scan(d)
            continue
        for root, subdirs, files in os.walk(d):
            subdirs[:] = sorted(s for s in subdirs if s != ".lake")
            for name in sorted(files):
                if name.endswith(".lean"):
                    hits += scan(os.path.join(root, name))
    for h in hits:
        print(h)
    if hits:
        print(f"error: {len(hits)} proof escape(s)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
