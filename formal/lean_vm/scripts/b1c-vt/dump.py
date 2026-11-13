# usage: python3 -I dump.py <lean_vm>/LeanVM/Guest/Data vt_ir.txt
# Writes verify_tables' body (its namespace `core{j}`, chunks c0, c1, …) one statement a line, indexed;
# the function is found by its name in the core IR (`scripts/coredata.py`).
import re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import coredata
data = Path(sys.argv[1])
data = data if data.is_dir() else data.parent
for src in coredata.legacy_texts(data):
    m = re.search(r'^noncomputable def (core\d+) : Core\.Fn where\n  name := "verify_tables"$', src, re.M)
    if m:
        break
else:
    sys.exit(f'dump.py: no verify_tables in the core IR of {data}')
i = src.index(f'namespace {m.group(1)}\n')
j = src.index(f'end {m.group(1)}', i)
sec = src[i:j]
chunks = {}
for m in re.finditer(r'noncomputable def (c\d+) : List Core.Stmt := \(\n(.*?)\n  \[\]\)', sec, re.S):
    chunks[m.group(1)] = m.group(2)
stmts = []
for c in sorted(chunks, key=lambda c: int(c[1:])):
    body = chunks[c]
    depth = 0; cur = ''; k = 0
    while k < len(body):
        ch = body[k]
        if ch in '([': depth += 1
        elif ch in ')]': depth -= 1
        if depth == 0 and body.startswith(' ::\n', k):
            stmts.append(cur.strip()); cur = ''; k += 4; continue
        cur += ch; k += 1
    if cur.strip(): stmts.append(cur.strip())
with open(sys.argv[2], 'w') as out:
    for k, s in enumerate(stmts):
        out.write(f'{k}: {re.sub(chr(92)+"s+", " ", s)}\n')
print(len(stmts))
