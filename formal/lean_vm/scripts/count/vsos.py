"""`Count/VsOs*.lean`: `open_stacked`'s words at each of its arms (`Count.osC m`, the arm of
stack log `B1.Whir.minOpenLog + m`), by the kernel, one module per arm, and `Count/VsOsAll.lean` putting them
together with the arms' callees' words bounds (`Count.osLeafBounds`).

    python3 -I scripts/count/vsos.py LEAN_VM

The numbers come from a mirror of `B1.osBos` at `B2C.fs` and `wSB` (`B1.osSizesL`, and for each call
statement of the arm's core IR, which `Whir/Data*.lean` check equal to `osBody (osCfg m)`, the
largest of its callees' frames and constants); a mirror the Lean definitions disagree with fails
the module's `decide +kernel`."""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen

LV = sys.argv[1]
g = gen.G(LV, None)
ARMS = len(g.os_names())
fsd = g.fs_words(); w = g.words_certs()
fs = lambda n: fsd.get(n, 2)
def SB(n):
    c = w.get(n); return c[2][0] if c and c[0] == 'stat' else 0
def SKt(n):
    """`wSK n - B2C.fs n` (`wSKt`): a loop's words per iteration, its run's phantom frame apart."""
    c = w.get(n); return c[3][0] if c and c[0] == 'loop' else 0
B1 = os.path.join(LV, 'LeanVM', 'Guest', 'B1')
def names(name):
    """The names of the list `name` (`List (String × ℕ)`), wherever under `B1` it is defined."""
    for root, _, files in os.walk(B1):
        for f in files:
            if not f.endswith('.lean'): continue
            s = open(os.path.join(root, f), encoding='utf-8').read()
            m = re.search(r'def %s : List \(String × ℕ\) :=\s*\[(.*?)\]\n' % name, s, re.S)
            if m: return re.findall(r'\("([^"]+)", \d+\)', m.group(1))
    sys.exit('vsos.py: `%s`, which `osKindTable` (B1/Place/OsMean.lean) reads, is defined nowhere under B1' % name)
def kinds():
    """`B1.osKindTable`'s names: its literal entries and the name lists it maps."""
    s = open(os.path.join(B1, 'Place', 'OsMean.lean'), encoding='utf-8').read()
    body = re.search(r'def osKindTable : List \(String × OsKind\) :=\n(.*?)\n\n', s, re.S).group(1)
    return set(re.findall(r'\("([^"]+)", \.', body) + [n for r in re.findall(r'(\w+Names)\.map', body)
                                                          for n in names(r)])
KINDS = kinds()
Bnd = lambda n: SB(n) if n in KINDS else 0
src = open(os.path.join(LV, 'LeanVM', 'Guest', 'Data', 'Source.lean'), encoding='utf-8').read()
def arr(name):
    m = re.search(r'def arr_%s : List \(Nat × Nat\) :=\s*\[(.*?)\]\n' % name, src, re.S)
    return [int(x) for x in re.findall(r'\((\d+), \d+\)', m.group(1))]
A = {k: arr(k) for k in ['LIG_N_LEVELS', 'LIG_CAP_LEN', 'LIG_YR_LEN', 'LIG_YR_LEVEL', 'LIG_TOTAL_FOLDS',
                         'LIG_POSITIONS_LEN', 'LIG_MAX_SQUEEZES', 'LIG_FOLDS', 'LIG_QUERIES',
                         'LIG_TREE_DEPTH', 'LIG_SQUEEZES', 'LIG_LEAF_CELLS', 'LIG_CAP_DEPTH']}
lig = lambda a, i: A[a][i] if i < len(A[a]) else 0
oql = {}
for m in re.finditer(r'\("(opening_queries__[^"]+)", "(__loop\d+)"',
                     open(os.path.join(B1, 'Opening', 'Witness.lean'), encoding='utf-8').read()):
    oql[m.group(1)] = m.group(2)
def nlev(m): return lig('LIG_N_LEVELS', m)
def loopBase(m): return 41 + sum(2 * nlev(k) - 1 for k in range(m))  # `B1.Whir.loopBase`


def sizes(m):
    """`B1.osSizesL (osCfg m)`."""
    n = lig('LIG_N_LEVELS', m)
    return ([lig('LIG_YR_LEN', m), 2 * n, lig('LIG_TOTAL_FOLDS', m), n, n, n * POS_CAP, n * POS_CAP, 128,
             n * COLS_CAP, n * OOD_SLOTS] + [lig('LIG_MAX_INTERLEAVE', m)] * n
            + [YR_LOG_CAP, POINT_CAP, POINT_CAP, n * COLS_CAP, n, n + 1])


def callees(name):
    """`B1.osCallees`: each call statement's callees, in order."""
    out = []
    for s in g.fns[g.by[name]]['body']:
        if s[0] == 'call': out.append([s[1]])
        elif s[0] == 'callIf': out.append([s[2]])
        elif s[0] == 'dispatch': out.append(s[2])
        else: assert s[0] in ('atom', 'ret'), s[0]
    return out


def osBos(m):
    name = 'open_stacked__L%d' % m
    nl = nlev(m); capLen = lig('LIG_CAP_LEN', m); yrLen = lig('LIG_YR_LEN', m); nF = lig('LIG_TOTAL_FOLDS', m)
    posLen = lig('LIG_POSITIONS_LEN', m); maxSq = lig('LIG_MAX_SQUEEZES', m); last = lig('LIG_YR_LEVEL', m)
    folds = lambda l: lig('LIG_FOLDS', m * 6 + l)
    # `B1.osSizesF` (hsStride 8, ligColsCap 22, yrLogCap 5, pointCap 40, resBatch 8)
    sizes = ([4 * capLen, capLen, yrLen + folds(last), 2 * nl, nF, 2 * nF, nl, nl, nl * 8, nl * 22, nl,
              posLen, posLen]
             + [x for l in range(nl) for x in ([] if l == last else [2 + folds(l)]) + [(maxSq + 1) * 5]
                + ([yrLen + folds(l)] if l == last else [])]
             + [5, 40, 40, nl * 22, nl, nl, 2 * nl]
             + [2 * (lig('LIG_QUERIES', m * 6 + l) // 8 + 1) for l in range(last)])
    sp = {}
    for l in range(nl):
        i = m * 6 + l
        q = lig('LIG_QUERIES', i); depth = lig('LIG_TREE_DEPTH', i); sq = lig('LIG_SQUEEZES', i)
        lc = lig('LIG_LEAF_CELLS', i); cd = lig('LIG_CAP_DEPTH', i)
        sqL = '__loop%d' % (loopBase(m) + l); resL = '__loop%d' % (loopBase(m) + nl + l)
        sp[sqL] = sp.get(sqL, 0) + (sq + 1) * fs(sqL) + sq * fs('decode_query_windows__L%d_L%d' % (depth, cd))
        # level `l`'s `opening_queries`: the `l`-th one `open_stacked` calls, its eleven Const
        # parameters `(odd, base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits,
        # final)` in its name
        oq = [f for f in calls(name) if f.startswith('opening_queries__')][l]
        odd, base = [int(x) for x in oq[len('opening_queries__L'):].split('_L')][:2]
        assert (odd, base) == (q % 2 * (1 if l == 0 else 0), 1 if l == 0 else 0), oq
        N = q // (1 + base)
        # `B1.oqBound`: its frame, chain buffer, `N + 1` iterations and a `walk_path` frame a query
        # (`oqWalkCount`: `odd + 2N` at level 0, `N` deeper)
        wk = odd + 2 * N if base == 1 else N
        sp[oq] = (sp.get(oq, 0) + fs(oq) + (N + 1) + (N + 1) * fs(oql.get(oq, ''))
                  + wk * fs('walk_path__L%d_L%d' % (depth - cd, cd)))
        # `B1.osSpB`: the residual loop's run, `q / 8` iterations and its one phantom frame
        if l < lig('LIG_YR_LEVEL', m):
            sp[resL] = sp.get(resL, 0) + q // 8 * SKt(resL) + fs(resL)
    return fs(name) + sum(sizes), [max(fs(f), Bnd(f) + sp.get(f, 0)) for f in calls(name)]


HDR = '''/-
  LeanVM.Guest.Count.%s

  Generated by `scripts/count/vsos.py`; do not edit.
  %s
-/

module

%s
namespace LeanVM.Guest.Count

@[expose] public section
%s
end
end LeanVM.Guest.Count
'''
D = os.path.join(LV, 'LeanVM', 'Guest', 'Count')
for f in os.listdir(D):
    if re.fullmatch(r'VsOs\d\d[abcn]?\.lean', f): os.remove(os.path.join(D, f))
def mod(name, doc, imports, body):
    open(os.path.join(D, name + '.lean'), 'w', encoding='utf-8').write(HDR % (name, doc, imports, body))
total, comb, names = [], [], []
imp = 'public import LeanVM.Guest.Count.VsOsDefs\n'
th = 'set_option maxRecDepth 100000 in\ntheorem %s : %s := by\n  decide +kernel\n'
for m in range(ARMS):
    t = osBos(m)
    total.append(t)
    mod('VsOs%02d' % m, '`open_stacked`\'s words at the arm %d (`osCF`), and its callees\' words certificates, by '
        'the kernel.' % m, imp,
        '\n' + th % ('osCF_%d' % m, 'osCF %d = %d' % (m, t))
        + '\n' + th % ('osNames_ok_%d' % m, '(B1.osCalleeNames (B1.Whir.osCfg %d)).all (fun f => wOkB (wIdx f) f) = true' % m))
    comb.append('/-- `open_stacked`\'s words at the arm %d. -/\ntheorem osC_%d : osC %d = %d := by\n'
                '  rw [osC_eq_fast, osCF_%d]\n' % (m, m, m, t, m))
    names.append('osNames_ok_%d' % m)
imports = 'public import LeanVM.Guest.Count.VsBoundBase\n' + ''.join(
    'public import LeanVM.Guest.Count.VsOs%02d\n' % m for m in range(ARMS))
body = '\n' + '\n'.join(comb) + '''
/-- Every arm's callees have constant words certificates. -/
theorem osNames_ok {m : ℕ} (hm : m < B1.osArms) :
    (B1.osCalleeNames (B1.Whir.osCfg m)).all (fun f => wOkB (wIdx f) f) = true := by
  interval_cases m
  exacts [%s]

/-- **Every arm's callees within `wSB`.** -/
theorem osLeafBounds : B1.OsLeafBounds B2C.fs wSB := fun _ hm f hf =>
  wSB_totalLe (List.all_eq_true.mp (osNames_ok hm) f hf)
''' % ', '.join(names)
mod('VsOsAll', '`open_stacked`\'s words at each arm (`osC m`), and its callees\' words bounds.', imports, body)
print('osC', total)
print('wSB', [SB('open_stacked__L%d' % m) for m in range(ARMS)])
