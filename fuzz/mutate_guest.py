"""Mutants of the recursion guest for `mutants.sh --subject guest`: one explicit check neutralized each.

    mutate_guest.py list <guest.py>            one mutant per line: `<id>\t<file>:<line>\t<kind>\t<code>`
    mutate_guest.py apply <guest.py> <id>      rewrite that line in place

Each `assert ...`, `assert_in_k(...)` and `assert_gpow(...)` statement becomes `assert 0 == 0`, which compiles and
constrains nothing, keeping the block's indentation. Implicit checks (a store into a written cell) are out of reach of a
line edit and of this list.
"""

import os
import re
import sys

CHECK = re.compile(r"^(\s*)(assert |assert_in_k\(|assert_gpow\()")


def mutants(path):
    name = os.path.basename(path)
    for i, text in enumerate(open(path).read().split("\n")):
        m = CHECK.match(text)
        if m:
            yield (f"{name}:{i + 1}:check", i, m.group(1), text.strip())


def main():
    command, path = sys.argv[1], sys.argv[2]
    if command == "list":
        for ident, i, _, code in mutants(path):
            print(f"{ident}\t{os.path.basename(path)}:{i + 1}\tcheck\t{code}")
    elif command == "apply":
        wanted = sys.argv[3]
        lines = open(path).read().split("\n")
        for ident, i, indent, _ in mutants(path):
            if ident == wanted:
                lines[i] = f"{indent}assert 0 == 0"
                open(path, "w").write("\n".join(lines))
                return
        sys.exit(f"no mutant {wanted}")


if __name__ == "__main__":
    main()
