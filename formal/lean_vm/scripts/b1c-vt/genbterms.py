import os, sys, re
# usage: python3 -I genbterms.py  rewrites the guest's baked data in Tables/Vt/FormsData.lean (each
# table block's coordinate terms, `vtBTerms{side}{table}`, from `COORD_TERM_*` and `TERM_*`) and
# Tables/Vt/FormsPad.lean (each block's `COORD_PADDING`, `vtPads{side}{table}`, and the count
# columns `vtCountCols`), from the guest's constants in LeanVM/Guest/Data/Source.lean.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gendiff import A, blocks, VT_LEAN

def block_ids(sd, t):
    return [b for b in range(len(A['BLOCK_SIDE'])) if A['BLOCK_SIDE'][b] == sd and A['BLOCK_TABLE'][b] == t]

def lit_blocks(blks):
    def coord(c): return '[' + ', '.join('([' + ', '.join(map(str, m)) + '], ' + str(v) + ')' for m, v in c) + ']'
    return '[' + ',\n    '.join('[' + ', '.join(coord(c) for c in blk) + ']' for blk in blks) + ']'

def wrap(items):
    """A list literal of the items' texts, broken between items at 98 columns."""
    lines, cur = [], '  ['
    for i, x in enumerate(items):
        piece = x + (', ' if i + 1 < len(items) else ']')
        if len(cur) + len(piece.rstrip()) > 98:
            lines.append(cur.rstrip()); cur = '    '
        cur += piece
    lines.append(cur)
    return '\n'.join(lines)

def replace_def(s, name, body):
    a = s.index(f'def {name} ')
    a = s.index(':=\n', a) + 3
    b = s.index('\n\n', a)
    return s[:a] + body + s[b:]

def pads(sd, t):
    out = []
    for b in block_ids(sd, t):
        o, n = A['BLOCK_COORD_OFF'][b], A['BLOCK_COORD_COUNT'][b]
        out.append([A['COORD_PADDING'][o + i] for i in range(n)])
    return out

if __name__ == '__main__':
    f = os.path.join(VT_LEAN, 'FormsData.lean'); s = open(f).read()
    for sd in range(3):
        for t in range(6):
            ids = block_ids(sd, t)
            s = re.sub(r'/-- Side %d, table %d: blocks \d+ \.\. \d+\. -/' % (sd, t),
                       f'/-- Side {sd}, table {t}: blocks {ids[0]} .. {ids[-1]}. -/', s)
            s = replace_def(s, f'vtBTerms{sd}{t}', '  ' + lit_blocks(blocks(sd, t)))
    open(f, 'w').write(s)
    f = os.path.join(VT_LEAN, 'FormsPad.lean'); s = open(f).read()
    for sd in (0, 2):
        for t in range(6):
            s = replace_def(s, f'vtPads{sd}{t}', wrap([repr(x) for x in pads(sd, t)]))
    cc = []
    for t in range(6):
        cols = [blk[0][0][0][0] for blk in blocks(2, t)]
        assert all(len(blk) == 1 and blk[0] == [([c], 1)] for blk, c in zip(blocks(2, t), cols))
        cc.append(cols)
    s5 = cc[5]
    last = f'(List.range {len(s5)}).map ({s5[0]} + ·)' if s5 == list(range(s5[0], s5[0] + len(s5))) else repr(s5)
    txt = '[' + ', '.join(repr(c) for c in cc[:5]) + ',\n    ' + last + ']'
    s = replace_def(s, 'vtCountCols', '  ' + txt)
    open(f, 'w').write(s)
    print('ok')
