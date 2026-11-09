# Library: verify_tables' evaluation list (`vtEvL`: top-level ites' branches inline) with the
# checker's counter at each statement, from vt_ir.txt (dump.py). Used by genstores.py.
import re, os
def vs(t): return [int(x) for x in re.findall(r'\.n (\d+)', t)]
def chkS(c, s):
    old = lambda v: v < c
    if s.startswith('.call ') or s.startswith('.dispatch'):
        lists = re.findall(r'\[([^\[\]]*)\]', s)
        args = vs(lists[-2]); rets = vs(lists[-1])
        return c + len(rets)
    if s.startswith('.callIf') or s.startswith('.ret'): return c
    m = re.match(r'\.atom \(\.(\w+) (.*)\)$', s)
    op, rest = m.group(1), m.group(2)
    v = vs(rest)
    if op in ('const', 'add', 'copy'): return c + 1
    if op == 'mul': return c + 1
    if op == 'load': return c + 1 if v[0] == c else c
    if op in ('assertEq', 'assertInK'): return c
    if op == 'assertNe': return c + 1  # fixNe: read as the product .mul p x i
    if op == 'rangeCheck': return c + 3
    if op == 'keccak': return c + 13
    if op == 'hint':
        k = re.match(r'\(\.(\w+)', rest).group(1)
        if k == 'limbs': return c + len(v) - 1
        if k in ('inverse', 'alloc', 'allocDyn', 'log2Ceil'): return c + 1
        if '.heap' in rest: return c
        if k == 'witness': return c + len(v)
        if k in ('bits', 'bitsExp'): return c + len(v) - 1
    raise Exception('unknown ' + s[:80])
def split_items(inner):
    items = []; depth = 0; cur = ''
    for ch in inner:
        if ch in '([': depth += 1
        elif ch in ')]': depth -= 1
        if ch == ',' and depth == 0: items.append(cur.strip()); cur = ''; continue
        cur += ch
    if cur.strip(): items.append(cur.strip())
    return items
def branches(s):
    rest = s[s.index(')') + 2:]
    parts = []; depth = 0; cur = ''
    for ch in rest:
        if ch == '[': depth += 1
        if depth > 0: cur += ch
        if ch == ']':
            depth -= 1
            if depth == 0: parts.append(cur); cur = ''
    return [split_items(p[1:-1].strip()) for p in parts]
def load(path=None):
    path = path or os.environ.get('VT_IR', os.path.join(os.path.dirname(__file__), 'vt_ir.txt'))
    top = [re.sub(r' ::$', '', l.rstrip('\n').split(': ', 1)[1]) for l in open(path)]
    top = [s for s in top if not s.startswith('.ret')]
    flat = []  # (top-level position, statement)
    for k, s in enumerate(top):
        if s.startswith('.ite'):
            for b in branches(s): flat += [(k, t) for t in b]
        else: flat.append((k, s))
    c = 20; ctr = []
    for k, s in flat:
        ctr.append(c); c = chkS(c, s)
    return top, flat, ctr, c
