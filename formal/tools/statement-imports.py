#!/usr/bin/env python3
"""The statement's imports: Mathlib, VCVio, CompPoly, Lean's `Init` and itself, and `import all` only of its own
generated data (`Statement.Data`).

  python3 -I tools/statement-imports.py DIR

Every `.lean` file under `DIR` (`.lake` skipped) has its header parsed by Lean itself (`lean --deps-json`, run in
`DIR` so that its toolchain is the project's), which gives each import's module and whether it is `import all`; a
header Lean cannot parse fails, and so does an import outside the list. Lists each offending file.
"""
import json
import os
import subprocess
import sys

ALLOWED = ("Mathlib.", "VCVio.", "CompPoly.", "Statement.", "Init.")
ALL_ALLOWED = ("Statement.Data.",)


def offences(module: str, import_all: bool) -> list[str]:
    found = []
    if module != "Init" and not module.startswith(ALLOWED):
        found.append(f"imports {module}")
    if import_all and not module.startswith(ALL_ALLOWED):
        found.append(f"`import all` of {module}")
    return found


def main(root: str) -> int:
    files = []
    for top, dirs, names in os.walk(root):
        dirs[:] = [d for d in dirs if d != ".lake"]
        files += [os.path.relpath(os.path.join(top, name), root) for name in names if name.endswith(".lean")]
    files.sort()
    if not files:
        print(f"statement-imports: no .lean file under {root}", file=sys.stderr)
        return 1
    bad = 0
    for i in range(0, len(files), 200):
        batch = files[i:i + 200]
        out = subprocess.run(["lean", "--deps-json", *batch], cwd=root, check=True, capture_output=True, text=True)
        results = json.loads(out.stdout)["imports"]
        if len(results) != len(batch):
            print("statement-imports: lean --deps-json answered for another number of files", file=sys.stderr)
            return 1
        for path, result in zip(batch, results):
            problems = list(result.get("errors") or [])
            if not result.get("result"):
                problems.append("no header parsed")
            for imp in (result.get("result") or {}).get("imports", []):
                problems += offences(imp["module"], imp["importAll"])
            for problem in problems:
                print(f"{os.path.join(root, path)}: {problem}")
            bad += bool(problems)
    if bad:
        print(f"statement-imports: {bad} files import more than Mathlib, VCVio, CompPoly, Init and the statement, "
              f"or `import all` beyond Statement.Data", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1]))
