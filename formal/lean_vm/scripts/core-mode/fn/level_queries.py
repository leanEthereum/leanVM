"""`level_queries`' contracts (`sigc.py`): `level_queries__L{n}_L{base}_L{folds}_L{leaf}_L{depth}_L{cap}_L{mu}_L{hs}_L{hb}_L{fin}(lam,
lam_inv, coefs, hs, positions, win_ptrs)` reads its `2·folds` round coefficients, its `hs` high parts, its `n` queries'
positions and window pointers (at level `0`, `base = 1`, in pairs, past an odd first query), each pointer at its query's
`n_win` windows, and returns `lam^n` (`retV`); the bus era's shape."""
from fnrules import guest_const
from sigseed import sig, num, run, ptrs

QW = guest_const('QW')


def c(o, k, hp=None):
    return '⟨0, %d, [((%s), 1)]⟩' % (k, '.fr %d' % o if hp is None else '.hp %d %d' % (o, hp))


def r(o, hi, S=1, d=0):
    return run('⟨0, 0, [((.fr %d), 1)]⟩' % o, num(0), num(hi), S, d)


def contract(n, base, folds, depth, cap, n_hs):
    nw = (depth - cap + QW - 1) // QW + 2
    nc = 2 * folds
    if base == 1:
        p, odd = n // 2, n % 2
        pre = []
        for k in range(max(nc, nw)):
            if k < nc:
                pre.append(c(4, k))
            if odd and k == 0:
                pre += [c(6, 0), c(7, 0)]
            if odd and k < nw:
                pre.append(c(7, k, 0))
        ds = (1, 2) if odd else (0, 1)
        pos, wins = [r(6, p, 2, d) for d in ds], [r(7, p, 2, d) for d in ds]
        post = [c(6, 0), c(7, 0)] + [c(7, k, 0) for k in range(nw)] if odd else []
        postR = [r(4, nc)] + pos + ([r(6, p + 1, 2, 0)] if odd else []) + wins + ([r(7, p + 1, 2, 0)] if odd else [])
    else:
        pre = []
        for k in range(max(nc, n_hs)):
            if k < nc:
                pre.append(c(4, k))
            if k < n_hs:
                pre.append(c(5, k))
        pos, wins, post = [r(6, n)], [r(7, n)], []
        postR = [r(4, nc)] + ([r(5, n_hs)] if n_hs else []) + pos + wins
    pp = [ptrs(w, range(nw)) for w in wins]
    return sig(range(8), None, [8, 9, 10, 11], pre=pre, preR=pos + wins, post=post, postR=postR, preP=pp, postP=pp,
               retV=['(11, ⟨0, 0, [((.fr 2), %d)]⟩)' % n])


def of_name(k):
    n, base, folds, _, depth, cap, _, n_hs, _, _ = map(int, k.split('__L')[1].split('_L'))
    return contract(n, base, folds, depth, cap, n_hs)


# the specializations whose contracts the bus era did not write (or wrote for another shape)
NEW = '''L110_L1_L6_L32_L14_L2 L110_L1_L6_L32_L15_L3 L111_L1_L6_L32_L13_L7 L112_L1_L6_L32_L12_L6 L220_L1_L6_L32_L14_L8
L222_L1_L6_L32_L13_L7 L225_L1_L6_L32_L12_L6 L230_L1_L6_L32_L11_L5 L55_L1_L6_L32_L15_L3 L55_L1_L6_L32_L16_L4
L55_L1_L6_L32_L17_L5 L56_L1_L6_L32_L14_L2 L73_L1_L6_L32_L15_L3 L73_L1_L6_L32_L16_L4 L74_L1_L6_L32_L13_L7
L74_L1_L6_L32_L14_L2'''.split()
NEW = ['level_queries__%s_L0_L0_L0_L0' % k for k in NEW] + ['level_queries__' + k for k in '''
L26_L0_L4_L16_L14_L2_L5_L36_L6_L1 L28_L0_L4_L16_L12_L6_L3_L12_L4_L1 L30_L0_L4_L16_L11_L5_L2_L8_L3_L1
L32_L0_L4_L16_L11_L5_L3_L12_L4_L1 L35_L0_L4_L16_L10_L4_L2_L8_L3_L1 L37_L0_L4_L16_L14_L2_L0_L0_L0_L0
L37_L0_L4_L16_L15_L3_L0_L0_L0_L0 L38_L0_L4_L16_L10_L4_L3_L12_L4_L1 L38_L0_L4_L16_L13_L7_L0_L0_L0_L0
L39_L0_L4_L16_L12_L6_L0_L0_L0_L0 L42_L0_L4_L16_L9_L3_L2_L8_L3_L1 L45_L0_L4_L16_L13_L7_L0_L0_L0_L0
L45_L0_L4_L16_L14_L2_L0_L0_L0_L0 L46_L0_L4_L16_L12_L6_L0_L0_L0_L0 L47_L0_L4_L16_L11_L5_L0_L0_L0_L0
L56_L0_L4_L16_L13_L7_L0_L0_L0_L0 L57_L0_L4_L16_L12_L6_L0_L0_L0_L0 L58_L0_L4_L16_L11_L5_L0_L0_L0_L0
L60_L0_L4_L16_L10_L4_L0_L0_L0_L0 L27_L0_L4_L16_L13_L7_L4_L20_L5_L1 L29_L0_L4_L16_L13_L7_L5_L36_L6_L1
L31_L0_L4_L16_L12_L6_L4_L20_L5_L1 L34_L0_L4_L16_L12_L6_L5_L36_L6_L1 L35_L0_L4_L16_L11_L5_L4_L20_L5_L1'''.split()]
CONTRACTS = {k: of_name(k) for k in NEW}

OWN = []
