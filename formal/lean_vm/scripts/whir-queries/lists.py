"""Rewrite the deployed specializations' lists the WHIR queries' proofs read, from the guest data:
`openingQueriesShapes` (`B1/Opening/Interface.lean`), `openingQueriesLoops`
(`B1/Opening/Witness.lean`), `walkPathNames` (`B1/Opening/QueriesT.lean`) and
`queryWindowsShapes` (`B1/Bits/QueryWindowsT.lean`), each in the core IR's order.

    python3 -I scripts/whir-queries/lists.py LEAN_VM
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen

B1 = os.path.join(sys.argv[1], 'LeanVM', 'Guest', 'B1')


def shape(d):
    return '⟨%d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, [%s]⟩' % (
        d['odd'], d['base'], d['folds'], d['leaf'], d['depth'], d['cd'], d['mu'], d['vanish'], d['nhs'],
        d['hsb'], d['final'], ', '.join(map(str, d['vs'])))


def replace_list(path, name, items):
    s = open(path, encoding='utf-8').read()
    i = s.index('def %s ' % name)
    j = s.index(':=', i) + 2
    k = s.index(']\n', j) + 1
    body = '\n  [' + ',\n    '.join(items) + ']'
    s = s[:j] + body + s[k:]
    open(path, 'w', encoding='utf-8').write(s)


specs = gen.oq_specs()
replace_list(os.path.join(B1, 'Opening', 'Interface.lean'), 'openingQueriesShapes',
             ['("%s", %s)' % (d['name'], shape(d)) for d in specs])
replace_list(os.path.join(B1, 'Opening', 'Witness.lean'), 'openingQueriesLoops',
             ['("%s", name%% «%s»,\n      %s)' % (d['name'], gen.stable[d['loop']], shape(d)) for d in specs])
wps = sorted((i, n) for n, i in gen.fns.items() if n.startswith('walk_path__L'))
replace_list(os.path.join(B1, 'Opening', 'QueriesT.lean'), 'walkPathNames',
             ['(%s, %s, "%s")' % (*n[len('walk_path__L'):].split('_L'), n) for _, n in wps])
qws = sorted((tuple(map(int, n[len('decode_query_windows__L'):].split('_L'))), n)
             for n, i in gen.fns.items() if n.startswith('decode_query_windows__L'))
replace_list(os.path.join(B1, 'Bits', 'QueryWindowsT.lean'), 'queryWindowsShapes',  # sorted as genqwdata's
             ['("%s", %s, %s)' % (n, *n[len('decode_query_windows__L'):].split('_L')) for _, n in qws])
print(len(specs), len(wps), len(qws))
