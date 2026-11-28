#!/usr/bin/env python3
"""Keep the statement apart from the proofs.

  python3 -I tools/statement-imports.py

Reads every module header under `Statement/` and `fast_fields/` with Lean's own parser
(`lean --deps-json`, so an import after a comment or another import on its line counts) and fails,
listing each, on an import of `Statement/` beyond Mathlib, VCVio, CompPoly, `fast_fields` and
itself, an `import all` beyond `Statement.Data`, or an import of `fast_fields/` beyond Mathlib,
CompPoly and itself. Run from `formal/`, with `lean` on the path; `check-all.sh` and the CI run it.
"""
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# Per directory: the module prefixes it may import, and those it may `import all`.
RULES = {
    "Statement": (("Mathlib.", "VCVio.", "CompPoly.", "FastFields.", "Statement."), ("Statement.Data.",)),
    "fast_fields": (("Mathlib.", "CompPoly.", "FastFields."), ()),
}


def sources(directory):
    for top, dirs, names in os.walk(os.path.join(ROOT, directory)):
        dirs[:] = sorted(d for d in dirs if d != ".lake")
        yield from (os.path.join(top, n) for n in sorted(names) if n.endswith(".lean"))


def headers(files):
    for i in range(0, len(files), 200):
        batch = files[i:i + 200]
        out = subprocess.run(["lean", "--deps-json", *batch], capture_output=True, text=True, check=True).stdout
        for path, entry in zip(batch, json.loads(out)["imports"]):
            if entry["errors"]:
                yield path, None
            else:
                yield path, entry["result"]["imports"]


def main():
    bad = []
    for directory, (allowed, allowed_all) in RULES.items():
        for path, imports in headers(list(sources(directory))):
            where = os.path.relpath(path, ROOT)
            if imports is None:
                bad.append(f"{where}: its header does not parse")
                continue
            for i in imports:
                module = i["module"]
                if module == "Init":
                    continue
                if not module.startswith(allowed) or (i["importAll"] and not module.startswith(allowed_all)):
                    bad.append(f"{where}: import{' all' if i['importAll'] else ''} {module}")
    for line in bad:
        print(line)
    if bad:
        print("error: Statement imports more than Mathlib, VCVio, CompPoly, fast_fields and itself, `import all` "
              "beyond Statement.Data, or fast_fields more than Mathlib, CompPoly and itself", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
