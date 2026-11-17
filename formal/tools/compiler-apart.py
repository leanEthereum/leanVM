#!/usr/bin/env python3
"""Keep the program-generic trees apart from the guest: no module of `lean_vm/LeanVM/Core/` (the core IR,
its semantics, its memory model and the front end) or of `lean_vm/LeanVM/Compiler/` (the verified
compiler) imports, directly or through other modules, a module of the guest.

  python3 -I tools/compiler-apart.py

Both are stated and proved for any program, never over one. Fails, printing an import chain from the
tree to each forbidden module it reaches, if a tree's import cone (from `tools/deps.py`'s graph of
the six projects) holds any of `FORBIDDEN`: a module of `LeanVM.Guest` (the guest's proofs, its
compiled instance `LeanVM.Guest.Compiled`, its generated data `LeanVM.Guest.Data`, `Pack`,
`Deployed`, the end theorems' layers `B1`, `Budget`, `Count`, `End`), the statement's data
(`Statement.Data`) and guest (`Statement.LeanVmGuest`), or the cost layer (`LeanVM.Cost`). The CI
(`.github/workflows/lean.yml`) runs it.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import deps  # noqa: E402

TREES = ["LeanVM.Core", "LeanVM.Compiler"]
FORBIDDEN = re.compile(r"^(LeanVM\.Guest|LeanVM\.Cost|Statement\.Data|Statement\.LeanVmGuest)(\.|$|[A-Z])")


def main():
    edges, _, _ = deps.read_graph()
    imports = {m: [e[0] for e in ii] for m, ii in edges.items()}
    failed = 0
    for tree in TREES:
        roots = sorted(m for m in edges if m == tree or m.startswith(tree + "."))
        if not roots:
            sys.exit(f"compiler-apart: no module {tree}.*")
        parent = {m: None for m in roots}
        todo = list(roots)
        while todo:
            m = todo.pop()
            for i in imports[m]:
                if i not in parent:
                    parent[i] = m
                    todo.append(i)
        bad = sorted(m for m in parent if FORBIDDEN.match(m))
        for m in bad:
            chain = [m]
            while parent[chain[-1]] is not None:
                chain.append(parent[chain[-1]])
            print(f"compiler-apart: {' <- '.join(chain)}")
        if bad:
            print(f"compiler-apart: {tree} imports {len(bad)} module(s) of the guest")
            failed += 1
        else:
            print(f"compiler-apart: ok, {len(roots)} modules of {tree}, {len(parent)} in their cone, none of the guest")
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()
