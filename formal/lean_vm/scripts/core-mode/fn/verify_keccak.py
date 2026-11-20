"""`verify_keccak`'s rules: its family (`CoreMode.vkQC`): its layers' returned cursors (step `s`'s, `CoreMode.vkCurs`),
the stream parameter, and the values whose exponents its `tau_g = g^τ`, `9 <= τ <= 28`, fixes (`CoreMode.vkE`)."""

# its layers' runs at their records' words (`postQ`), loads naming stored words (`hv`), runs made up for its reads and
# its callees' runs (`der`)
FEATURES = {'verify_keccak': [{'postQ', 'hv', 'der'}]}

CAPE = 2 ** 62
VK_CURS = [483, 518, 552, 595, 636, 679, 712, 753, 791, 834, 875, 915]
VK_STREAM = 12
VK_ORD = 2 ** 64 - 1


def vk_e(t):
    """`CoreMode.vkE`: the exponents at `τ = t` (`18` is `g^-4`, modulo the order `2^64 - 1`)."""
    y = t - 3
    b = [(y >> i) & 1 for i in range(5)]
    return {6: t, 18: VK_ORD - 4, 19: t - 4, 21: t - 3, 35: y // 8, 49: y % 8, 30: b[3], 34: 2 * b[4], 39: b[0],
            43: 2 * b[1], 48: 4 * b[2]}


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
    `[12]·[0, 8192)`; else a residual true at every `τ` (`vk_at`)."""
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

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/ResVk*.lean',
    'LeanVM/Guest/CoreMode/Fam/ResSt.lean',
    'LeanVM/Guest/EndExecCoreVk.lean',
    'LeanVM/Guest/CoreMode/Fn/verify_keccak/*.lean',
]
