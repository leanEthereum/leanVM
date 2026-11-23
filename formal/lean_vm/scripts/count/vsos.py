"""`Count/VsOs*.lean`: `open_stacked`'s words at each of its arms (`Count.osC m`, the arm of
stack log `B1.Whir.minOpenLog + m`), by the kernel, one module per arm, and `Count/VsOsAll.lean` putting them
together with the arms' callees' words bounds (`Count.osLeafBounds`).

    python3 -I scripts/count/vsos.py LEAN_VM

The numbers come from a mirror of `B1.osBos` at `B2C.fs` and `wSBos` (`B1.osSizesL`, and for each call
statement of the arm's core IR, which `Whir/Data*.lean` check equal to `osBody (osCfg m)`, the
largest of its callees' frames and words bounds); a mirror the Lean definitions disagree with fails
the module's `decide +kernel`. A callee whose words certificate reads its arguments' exponents
(`level_positions`, `level_residual`) is bounded by `Count/VsOsTab.lean`'s `osRtTab`: the largest of its
certificate's bound over the exponents the arms pass it (`Count.osAsgs`, mirroring `B1.osArgsOk`)."""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen

LV = sys.argv[1]
g = gen.G(LV, None)
ARMS = len(g.os_names())
fsd = g.fs_words(); w = g.words_certs()
fs = lambda n: fsd.get(n, 2)
def SB(n):
    c = w.get(n); assert c and c[0] == 'stat' and c[1] == [] and c[2][1] == [], n
    return c[2][0]
src = open(os.path.join(LV, 'LeanVM', 'Guest', 'Data', 'Consts.lean'), encoding='utf-8').read()
def arr(name):
    m = re.search(r'def arr_%s : List \(Nat × Nat\) :=\s*\[(.*?)\]\n' % name, src, re.S)
    return [int(x) for x in re.findall(r'\((\d+), \d+\)', m.group(1))]
A = {k: arr(k) for k in ['LIG_N_LEVELS', 'LIG_YR_LEN', 'LIG_TOTAL_FOLDS', 'LIG_YR_LEVEL', 'LIG_FOLDS', 'LIG_SQUEEZES',
                         'LIG_TREE_DEPTH', 'LIG_CAP_DEPTH', 'LIG_QUERIES', 'LIG_LOG_MSG_COLS', 'LIG_HIGH_BITS']}
lig = lambda a, i: A[a][i] if i < len(A[a]) else 0
# `B1.Whir`'s buffer caps, read off its sources so a change there reaches the mirror.
def _whir(f):
    return open(os.path.join(LV, 'LeanVM', 'Guest', 'B1', 'Whir', f), encoding='utf-8').read()
def _abbrev(src, name):
    return int(re.search(r'abbrev %s : (?:Nat|ℕ) := (\d+)' % name, src).group(1))
# `Whir/Config.lean`'s caps read the guest's constants (`guest_const%`), exported to `Data/Consts.lean`.
_src = src
def _const(name):
    return int(re.search(r'def const_%s : Nat := (\d+)' % name, _src).group(1))
COLS_CAP, YR_LOG_CAP, MAX_LEVELS, N_RATES = (_const(n) for n in (
    'LIG_LOG_MSG_COLS_CAP', 'YR_LOG_CAP', 'LIG_MAX_LEVELS', 'LIG_N_RATES'))
HS_STRIDE = 2 ** _const('HIGH_BITS_CAP')
N_SIZES, RES_BATCH = _const('LIG_N_LOG_SIZES'), _const('RES_BATCH')
POINT_CAP = _abbrev(_whir('Split.lean'), 'pointCap')


def sizes(m, ri):
    """`B1.osSizesL (osCfgR m ri)`."""
    n = lig('LIG_N_LEVELS', m)
    yr = lig('LIG_YR_LEVEL', m)
    folds = lambda l: lig('LIG_FOLDS', m * MAX_LEVELS + l)
    lane = lig('LIG_YR_LEN', m) + folds(yr)
    nf = lig('LIG_TOTAL_FOLDS', m)
    # `B1.osPosTotal`: the levels' squeezes times their words' positions, at the rate
    row = lambda l: (ri * N_SIZES + m) * MAX_LEVELS + l
    pt = sum(lig('LIG_SQUEEZES', row(l)) * (128 // lig('LIG_TREE_DEPTH', row(l))) for l in range(n))
    return ([lane, 2 * n, nf, 2 * nf, n, n, n * HS_STRIDE, n * COLS_CAP, n, N_RATES, pt, pt]
            + [2 + folds(l) for l in range(min(yr, n))]
            + [lane, YR_LOG_CAP, POINT_CAP, POINT_CAP, n * COLS_CAP, n, n, 2 * n])


def callees(name):
    """`B1.osCallees`: each call statement's callees, in order."""
    out = []
    for s in g.fns[g.by[name]]['body']:
        if s[0] == 'call': out.append([s[1]])
        elif s[0] == 'callIf': out.append([s[2]])
        elif s[0] == 'dispatch': out.append(s[2])
        else: assert s[0] in ('atom', 'ret', 'match'), s[0]
    return out


def asgs(m, f):
    """`Count.osAsgs m f`: the exponents arm `m` can pass callee `f` at the arguments its certificate reads, one
    assignment per rate and level whose row names `f` (`B1.osArgsOk`)."""
    row = lambda r, l: (r * N_SIZES + m) * MAX_LEVELS + l
    i = lambda l: m * MAX_LEVELS + l
    pos = lambda r, l: 'level_positions__L%d_L%d' % (lig('LIG_TREE_DEPTH', row(r, l)), lig('LIG_CAP_DEPTH', row(r, l)))
    res = lambda l: 'level_residual__L%d_L%d_L%d' % (lig('LIG_LOG_MSG_COLS', i(l)), lig('LIG_FOLDS', i(l)),
                                                    lig('LIG_HIGH_BITS', i(l)))
    out = [[(9, lig('LIG_SQUEEZES', row(r, l)))]
           for r in range(N_RATES) for l in range(lig('LIG_N_LEVELS', m)) if f == pos(r, l)]
    out = out or [[(4, q // RES_BATCH), (5, q % RES_BATCH)]
                  for r in range(N_RATES) for l in range(lig('LIG_YR_LEVEL', m)) if f == res(l)
                  for q in [lig('LIG_QUERIES', row(r, l))]]
    return out or [[]]


def stat_at(c, asg):
    """`Count.statAtB`'s bound: the certificate's bound at the assignment, `None` where it fails."""
    assert c and c[0] == 'stat', c
    _, pre, (b, cs), _ = c
    look = dict(asg)
    for k, a in pre:
        if k not in look or look[k] >= gen.checker.ORD or not gen.checker.pre_lt(a, look[k]): return None
    if any(k not in look for k, _ in cs): return None
    return b + sum(a * look[k] for k, a in cs)


RT = {}
for m in range(ARMS):
    for fl in callees('open_stacked__L%d' % m):
        for f in fl:
            c = w.get(f)
            if c and c[0] == 'stat' and c[1] == [] and c[2][1] == []: continue
            vals = [stat_at(c, a) for a in asgs(m, f)]
            assert vals and None not in vals, (m, f, c, asgs(m, f))
            RT[f] = max(vals + [RT.get(f, 0)])


def Bnd(n):
    """`Count.wSBos`."""
    return RT[n] if n in RT else SB(n)


def osBos(m):
    name = 'open_stacked__L%d' % m
    hs = g.fns[g.by[name]]['body']
    nh = sum(1 for s in hs if s[0] == "atom" and s[1] in ("alloc", "allocDyn"))
    assert nh == len(sizes(m, 0)), (m, nh, len(sizes(m, 0)))
    kids = sum(max(max(fs(f), Bnd(f)) for f in fl) for fl in callees(name))
    # `B1.osBosAt`: the largest over the rates
    return max(fs(name) + sum(sizes(m, ri)) + kids for ri in range(N_RATES))


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
mod('VsOsTab', '`open_stacked`\'s runtime-sized callees\' words bounds by core index (`Count.wSBos`).', '',
    '\n/-- The callees of `open_stacked` whose words read their arguments\' exponents, by core index: the largest bound '
    'of their certificates at the exponents the arms pass them. -/\ndef osRtTab : List (Nat × Nat) := [%s]\n'
    % ', '.join('(%d, %d)' % (g.by[f], RT[f]) for f in sorted(RT, key=lambda f: g.by[f])))
total, comb, names = [], [], []
imp = 'public import LeanVM.Guest.Count.VsOsDefs\n'
th = 'set_option maxRecDepth 100000 in\ntheorem %s : %s := by\n  decide +kernel\n'
for m in range(ARMS):
    t = osBos(m)
    total.append(t)
    mod('VsOs%02d' % m, '`open_stacked`\'s words at the arm %d (`osCF`), and its callees\' words certificates, by '
        'the kernel.' % m, imp,
        '\n' + th % ('osCF_%d' % m, 'osCF %d = %d' % (m, t))
        + '\n' + th % ('osNames_ok_%d' % m, '(B1.osCalleeNames (B1.Whir.osCfg %d)).all (leafOkB %d) = true' % (m, m)))
    comb.append('/-- `open_stacked`\'s words at the arm %d. -/\ntheorem osC_%d : osC %d = %d := by\n'
                '  rw [osC_eq_fast, osCF_%d]\n' % (m, m, m, t, m))
    names.append('osNames_ok_%d' % m)
comb.append('/-- `open_stacked`\'s words at the arms, in order. -/\ndef osCs : List ℕ := [%s]\n\n'
            '/-- `open_stacked`\'s words at an arm, from the table. -/\n'
            'theorem osC_getD {m : ℕ} (hm : m < %d) : osC m = osCs.getD m 0 := by\n'
            '  interval_cases m\n  exacts [%s]\n' % (', '.join(map(str, total)), ARMS,
                                                    ', '.join('osC_%d' % m for m in range(ARMS))))
imports = 'public import LeanVM.Guest.Count.VsBoundBase\npublic import LeanVM.Guest.Count.VsOsLeaf\n' + ''.join(
    'public import LeanVM.Guest.Count.VsOs%02d\n' % m for m in range(ARMS))
body = '\n' + '\n'.join(comb) + '''
/-- Every arm's callees' certificates check within `wSBos`. -/
theorem osNames_ok {m : ℕ} (hm : m < B1.osArms) :
    (B1.osCalleeNames (B1.Whir.osCfg m)).all (leafOkB m) = true := by
  interval_cases m
  exacts [%s]

/-- **Every arm's callees within `wSBos`** on the arguments the arm passes them. -/
theorem osLeafBounds : B1.OsLeafBounds B2C.fs wSBos := fun _ hm f hf =>
  leafOkB_sound (List.all_eq_true.mp (osNames_ok hm) f hf)
''' % ', '.join(names)
mod('VsOsAll', '`open_stacked`\'s words at each arm (`osC m`), and its callees\' words bounds.', imports, body)
print('osC', total)
print('osRtTab', len(RT))
