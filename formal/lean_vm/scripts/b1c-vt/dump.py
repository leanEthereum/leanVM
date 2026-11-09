# usage: python3 -I dump.py <lean_vm>/LeanVM/Guest/Data/Core00.lean vt_ir.txt
# Writes verify_tables' body (namespace core11, its chunks c0, c1, …) one statement a line, indexed.
import re, sys
src = open(sys.argv[1]).read()
i = src.index('namespace core11\n')
j = src.index('end core11', i)
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
