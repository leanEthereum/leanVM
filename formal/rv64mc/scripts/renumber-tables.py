#!/usr/bin/env python3
"""Renumbers the function indices the `Rv64mc/Table/*.lean` modules write as literals, after a regeneration that added
or removed a function: `renumber-tables.py PROJECT OLD_INDEX_TSV`.

An index next to its module's name (`(liftProg fns) N Needs.<M>`, `env _ N [arg] _ <M>.tmpl_eq`) becomes the new
`Gen/index.tsv`'s index of `<M>`; any other `(liftProg fns) N` (a statement's or a callee hypothesis's) is taken
through OLD_INDEX_TSV (the `index.tsv` the tables were written against) to its module, then to the new index. Run it
once per regeneration: the second kind is not idempotent. A table entry for a removed function is the author's to
delete first. Prints the lines changed per file.
"""

import re
import sys
from pathlib import Path


def read_index(path: Path) -> list[tuple[str, str]]:
    return [(l.split("\t")[0], l.split("\t")[1]) for l in path.read_text(encoding="utf-8").splitlines()[1:]]


def main() -> None:
    root, old_path = Path(sys.argv[1]), Path(sys.argv[2])
    new = dict(read_index(root / "Rv64mc/Gen/index.tsv"))
    old = {i: m for m, i in read_index(old_path)}
    total = 0
    for f in sorted((root / "Rv64mc/Table").glob("*.lean")):
        s = f.read_text(encoding="utf-8")
        t = re.sub(r"\(liftProg fns\) (\d+)(\s+)Needs\.([\w.]+)",
                   lambda m: f"(liftProg fns) {new[m.group(3)]}{m.group(2)}Needs.{m.group(3)}", s)
        t = re.sub(r"env _ (\d+)(\s+)((?:\w+\s+)?)_ ([\w.]+)\.tmpl_eq",
                   lambda m: f"env _ {new[m.group(4)]}{m.group(2)}{m.group(3)}_ {m.group(4)}.tmpl_eq", t)
        t = re.sub(r"\(liftProg fns\) (\d+)(?!\d)(?!\s+Needs\.)", lambda m: f"(liftProg fns) {new[old[m.group(1)]]}", t)
        changed = sum(1 for x, y in zip(s.splitlines(), t.splitlines()) if x != y)
        total += changed
        f.write_text(t, encoding="utf-8")
        print(f"{f.name}\t{changed}")
    print(f"lines changed\t{total}")


if __name__ == "__main__":
    main()
