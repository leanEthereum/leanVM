"""`verify_keccak`'s rules: its family (`CoreMode.vkQC`): its layers' returned cursors (step `s`'s, `CoreMode.vkCurs`),
the stream parameter, and the values whose exponents its `tau_g = g^τ`, `9 <= τ <= 28`, fixes (`CoreMode.vkE`)."""

# its layers' runs at their records' words (`postQ`), loads naming stored words (`hv`), runs made up for its reads and
# its callees' runs (`der`)
FEATURES = {'verify_keccak': [{'postQ', 'hv', 'der'}]}

from fnrules import val, lean_def

CAPE = 2 ** 62
# its layers' returned cursors, as its Lean data says, and its stream
VK_CURS = lean_def('verify_keccak', 'Fam', 'vkCurs')
VK_STREAM = val('verify_keccak', 'stream')
# the order of `g`, and the exponents at `τ` (`CoreMode.vkTab`), as its Lean data says
VK_ORD = lean_def('verify_keccak', 'Fam', 'gOrd')


_VK_E = {}


def vk_e(t):
    """`CoreMode.vkTab`: the exponents at `τ = t` (`pack_g~0` is `g^-4`, modulo the order `2^64 - 1`)."""
    if t not in _VK_E:
        _VK_E[t] = dict(lean_def('verify_keccak', 'Fam', 'vkTab', t))
    return _VK_E[t]


def vk_ev(E, c):
    """`CoreMode.vkEv`: a cell over known values' exponent, modulo the order (`None`: an unknown base)."""
    t = c[1]
    for x, e in c[0]:
        if x not in E:
            return None
        t += E[x] * e
    return t % VK_ORD


def vk_idx(E, i):
    if i[0] == 'num':
        return vk_ev(E, ((), i[1]))
    if i[0] == 'val':
        return vk_ev(E, (((i[1], 1),), 0))
    return vk_ev(E, i[1])


def vk_split(E, c):
    """`CoreMode.vkSplit`: a cell's unknown bases (in order) and its known part's exponent."""
    u = tuple(b for b in c[0] if b[0] not in E)
    return u, vk_ev(E, (tuple(b for b in c[0] if b[0] in E), c[1]))


def vk_at(t, r):
    """`CoreMode.vkAt`: the residual decided at `τ = t`."""
    E = vk_e(t)
    if r[0] == 'under':
        return vk_at(t, r[2])
    if r[0] == 'lt':
        a, b = vk_idx(E, r[1]), vk_idx(E, r[2])
        return a is not None and b is not None and a < CAPE and b < CAPE and a < b
    if r[0] == 'subR':
        (qb, qS, ql, qh), (rb, rS, rl, rh) = r[1], r[2]
        uq, kq = vk_split(E, qb)
        ur, kr = vk_split(E, rb)
        lq, hq, lr, hr = vk_idx(E, ql), vk_idx(E, qh), vk_idx(E, rl), vk_idx(E, rh)
        if uq != ur or None in (kq, kr, lq, hq, lr, hr) or not 0 < rS or not hq - lq <= 64:
            return False
        if not all(v < CAPE for v in (kq, kr, lq, hq, lr, hr)) or not kq + qS * hq < CAPE:
            return False
        for j in range(lq, hq):
            x = kq + qS * j
            if x < kr or (x - kr) % rS or not lr <= (x - kr) // rS < hr:
                return False
        return True
    return False


def fam(k, r):
    """`CoreMode.vkQC`: a read `c < (11 - s)·96 + 97` words past step `s`'s returned cursor, one of the stream's
    `[stream]·[0, 8192)`; else a residual true at every `τ` (`vk_at`)."""
    if k != 'verify_keccak':
        return False
    rr = r[2] if r[0] == 'under' else r
    if rr[0] == 'sub':
        c, q = rr[1], rr[2]
        return q == ((((VK_STREAM, 1),), 0), 1, ('num', 0), ('num', 8192)) and len(c[0]) == 1 and \
            c[0][0][1] == 1 and c[0][0][0] in VK_CURS and c[1] < (11 - VK_CURS.index(c[0][0][0])) * 96 + 97
    return all(vk_at(t, r) for t in range(9, 29))


def arg_bound(k, x):
    """Its exponent bound of `x` (`vkQC`), plus one."""
    if k != 'verify_keccak':
        return None
    es = [vk_e(t).get(x) for t in range(9, 29)]
    return None if None in es or max(es) >= CAPE else max(es) + 1


# ---- its counts (`scripts/count`)

# counted within a ratio of these words (`verify_sub`'s `vsCountT`) and its ratios checked (`Count/RatioV`): order,
# Lean name
RATIO_WORDS = {'verify_keccak': 56404}
RATIOV = {'verify_keccak': (1, 'Vk')}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
