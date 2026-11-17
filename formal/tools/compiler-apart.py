#!/usr/bin/env python3
"""Keep the verified compiler apart from the guest: no module of `lean_vm/LeanVM/Compiler/` imports,
directly or through other modules, a module of the guest's instance or data.

  python3 -I tools/compiler-apart.py

The compiler (`LeanVM.Compiler`, its soundness and completeness for any program) is stated and
proved over the core IR and its semantics (`LeanVM.Guest.Core`, `Logic`, `Memory`, `Expand`, ...),
never over one program. Fails, printing an import chain from the compiler to each forbidden module
it reaches, if its import cone (from `tools/deps.py`'s graph of the six projects) holds any of
`FORBIDDEN`: the compiled guest's proofs (`LeanVM.Guest.Compiled`), the guest's generated data
(`Statement.Data`, `LeanVM.Guest.Data`, `LeanVM.Guest.Pack`, `LeanVM.Guest.Deployed`), its
statement (`Statement.LeanVmGuest`), and the end theorems' layers (`B1`, `Budget`, `Count`, `End`,
`Cost`). The CI (`.github/workflows/lean.yml`) runs it.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import deps  # noqa: E402

COMPILER = "LeanVM.Compiler"
FORBIDDEN = re.compile(r"^(LeanVM\.Guest\.(Compiled|Data|Pack|Deployed|B1|Budget|Count|End)"
                       r"|LeanVM\.Cost|Statement\.Data|Statement\.LeanVmGuest)(\.|$|[A-Z])")


def main():
    edges, _, _ = deps.read_graph()
    imports = {m: [e[0] for e in ii] for m, ii in edges.items()}
    roots = sorted(m for m in edges if m == COMPILER or m.startswith(COMPILER + "."))
    if not roots:
        sys.exit(f"compiler-apart: no module {COMPILER}.*")
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
        sys.exit(f"compiler-apart: the compiler imports {len(bad)} module(s) of the guest")
    print(f"compiler-apart: ok, {len(roots)} modules of {COMPILER}, {len(parent)} in their cone, none of the guest")


if __name__ == "__main__":
    main()
