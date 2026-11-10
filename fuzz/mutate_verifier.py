"""Mutants of the native verifier for `mutants.sh`: one check disabled each.

    mutate_verifier.py list <src-dir>             one mutant per line: `<id>\t<file>:<line>\t<kind>\t<code>`
    mutate_verifier.py apply <src-dir> <id>       rewrite that mutant's file in place

A `require(cond, error)` becomes `require(true, error)`; a block behind `transcript.checked()` (or `self.checked`) is
never entered, and one behind its negation always is.
"""

import os
import re
import sys


def sources(root):
    for name in sorted(os.listdir(root)):
        if name.endswith(".rs"):
            yield os.path.join(root, name)


def condition_end(text, start):
    """The index of the comma that ends a `require(` condition beginning at `start`, at bracket depth zero."""
    depth = 0
    for i in range(start, len(text)):
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "," and depth == 0:
            return i
    raise ValueError("unbalanced require(")


GUARDS = [
    (r"if transcript\.checked\(\)", "if false"),
    (r"if self\.checked\b", "if false"),
    (r"if !transcript\.checked\(\)", "if true"),
]


def mutants(root):
    for path in sources(root):
        text = open(path).read()
        rel = os.path.relpath(path, root)
        for m in re.finditer(r"\brequire\(", text):
            if text[: m.start()].rstrip().endswith("fn"):
                continue
            start = m.end()
            end = condition_end(text, start)
            line = text.count("\n", 0, m.start()) + 1
            yield (f"{rel}:{line}:require", path, line, "require", (start, end, "true"))
        for pattern, replacement in GUARDS:
            for m in re.finditer(pattern, text):
                line = text.count("\n", 0, m.start()) + 1
                yield (f"{rel}:{line}:guard", path, line, "guard", (m.start(), m.end(), replacement))


def main():
    command, root = sys.argv[1], sys.argv[2]
    if command == "list":
        for ident, path, line, kind, _ in mutants(root):
            code = open(path).read().splitlines()[line - 1].strip()
            print(f"{ident}\t{os.path.relpath(path, root)}:{line}\t{kind}\t{code}")
    elif command == "apply":
        wanted = sys.argv[3]
        for ident, path, _, _, (start, end, replacement) in mutants(root):
            if ident == wanted:
                text = open(path).read()
                open(path, "w").write(text[:start] + replacement + text[end:])
                return
        sys.exit(f"no mutant {wanted}")


if __name__ == "__main__":
    main()
