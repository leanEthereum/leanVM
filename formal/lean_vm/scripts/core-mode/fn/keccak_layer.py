"""`keccak_layer`'s rules (`sigc.py`, `callcres.py`): `keccak_layer__L{first}(fs0, .., fs4, p0, p1, cursor, y_g, step_g,
rem_g, claim, out, iota, tabs)` reads the claim's cells `claim[g^KC_*]` and `KC_MU + i`, `i < KECCAK_PACK`, the
product's words and its nonce past `cursor` (`P` words), then the two `layer_rounds` dispatches' words: on `step_g`
(arms `0` and `KR_STEP` rounds, `2` words a round) the `2·KR_STEP` residue runs `[cursor]·g^(P + d)·[0, e(step_g))`,
on `rem_g` the `2` residue runs past `ret₁ = cursor·step_g^(2·KR_STEP)·g^P` below `e(rem_g)`, and the local rounds'
words past `ret₂ = ret₁·rem_g^2`; the point `prev_point`, the word at `claim·g^KC_POINT`, through both dispatches
(`KR_STEP` residue runs below `e(step_g)`, then past `prev_point·step_g^KR_STEP` below `e(rem_g)`); the lanes and
(`first = 0`) the local point the claim names, as pointer facts (`preP`); with the grind the windows table `tabs`. It
writes `out`'s cells, its lanes, local point and flips as pointer facts (`postP`), its point at `out·g^KC_POINT` as the
next layer reads it and whole (`postR`), and returns its cursor `ret₂·g^T`. The dispatches' returned cursors are named by equation residuals (`RES_EQ`, the pass
seeding the environment with them), which its own family proves (`CoreMode/Fn/keccak_layer/Fam.lean`)."""
from fnrules import guest_const
from sigseed import sig, cell, num, run, ptrs

KC = {n: guest_const('KC_' + n) for n in ('VALUE', 'KAPPA', 'POINT', 'LANES', 'LOCAL', 'FLIPS', 'MU', 'SIZE')}
PACK, STEP = guest_const('KECCAK_PACK'), guest_const('KR_STEP')
LANES, ZB = guest_const('KECCAK_LANES'), guest_const('KECCAK_Z_BITS')
LOCAL, IOTA = guest_const('KECCAK_LOCAL_BITS'), guest_const('KECCAK_IOTA_BITS')
WIN = 2 ** guest_const('WIN_TAB_BITS')
# the product's words and the grind's nonce; the local rounds' words and the last three (no grind: `ROUND3_GRIND_BITS`
# and `KECCAK_BETA_GRIND_BITS` are `0`)
P = guest_const('KECCAK_PROD_BITS') + 1
T = 3 * guest_const('KECCAK_LOCAL_BITS') + 3
assert guest_const('ROUND3_GRIND_BITS') == 0 and guest_const('KECCAK_BETA_GRIND_BITS') == 0
# frame cells of `cursor`, `y_g`, `step_g`, `rem_g`, `claim`, `out`, `tabs` (parameter `i` at `2 + i`)
CUR, YG, STP, REM, CLM, OUT, TABS = 9, 10, 11, 12, 13, 14, 16


def hp(o, bs=()):
    """The monomial `Π [b]^e·[claim·g^o]`, a word the claim points at; the frame cells first, as the translation
    (`CoreMode.rngL`, unsorted) puts the word's ghost slot past the parameters."""
    return '⟨0, 0, [%s((.hp %d %d), 1)]⟩' % (''.join('((.fr %d), %d), ' % b for b in bs), CLM, o)


def ex(o):
    return '(.ex (.fr %d) 0)' % o


def contract(first):
    reads = [KC['VALUE'], KC['KAPPA'], KC['POINT'], KC['LANES']] + ([KC['LOCAL']] if first == 0 else []) + \
        [KC['MU'] + i for i in range(PACK)]
    r1, r2 = [(CUR, 1), (STP, 2 * STEP)], [(CUR, 1), (STP, 2 * STEP), (REM, 2)]
    runs = [run(cell(0, [(CUR, 1)]), num(0), num(P), 1, 0)] + \
        [run(cell(P, [(CUR, 1)]), num(0), ex(STP), 2 * STEP, d) for d in range(2 * STEP)] + \
        [run(cell(P, r1), num(0), ex(REM), 2, d) for d in range(2)] + \
        [run(cell(P, r2), num(0), num(T), 1, 0)] + \
        [run(hp(KC['POINT']), num(0), ex(STP), STEP, d) for d in range(STEP)] + \
        [run(hp(KC['POINT'], [(STP, STEP)]), num(0), ex(REM), 1, 0)] + \
        [run(cell(0, [(TABS, 1)]), num(0), num(WIN), 1, 0)]
    # the claim's lanes and (`first = 0`) local point as pointer facts, which its caller meets with the previous
    # layer's (`postP`: its own buffers `lanes`, `local`, `flips`)
    one = lambda b, o: run(cell(o, [(b, 1)]), num(0), num(1), 1, 0)
    preP = [ptrs(one(CLM, KC['LANES']), range(LANES))] + \
        ([ptrs(one(CLM, KC['LOCAL']), range(ZB))] if first == 0 else [])
    postP = [ptrs(one(OUT, KC['LANES']), range(LANES)), ptrs(one(OUT, KC['LOCAL']), range(LOCAL)),
             ptrs(one(OUT, KC['FLIPS']), range(IOTA))]
    # a pointer fact's own cells among the runs (`callc.callee_sig`, `fitB`)
    runs += [p for p, _ in [(one(CLM, KC['LANES']), 0)] + ([(one(CLM, KC['LOCAL']), 0)] if first == 0 else [])]
    # its point at `out·g^KC_POINT` (`point`), as its two dispatches write it (the next layer's point runs), and whole,
    # `[0, e(y_g))` (`y_g = step_g^KR_STEP·rem_g`, `RES_EQ`): runs at the stored word
    hq = lambda bs=(): '⟨0, 0, [%s((.hp %d %d), 1)]⟩' % (''.join('((.fr %d), %d), ' % b for b in bs), OUT, KC['POINT'])
    postR = [run(hq(), num(0), ex(STP), STEP, d) for d in range(STEP)] + \
        [run(hq([(STP, STEP)]), num(0), ex(REM), 1, 0), run(hq(), num(0), ex(YG), 1, 0)]
    return sig(range(17), None, range(17, 23), pre=[cell(o, [(CLM, 1)]) for o in reads], preR=runs,
               post=[cell(o, [(OUT, 1)]) for o in range(KC['SIZE'])], postR=postR, preP=preP, postP=postP,
               retV=['(22, %s)' % cell(P + T, r2)])


CONTRACTS = {'keccak_layer__L%d' % f: contract(f) for f in (0, 1)}

# the two dispatches' returned cursors (values `ret₁`, `ret₂`), over the values `cursor` (7), `step_g` (9), `rem_g`
# (10): `ret₁ = cursor·step_g^(2·KR_STEP)·g^P`, `ret₂ = ret₁·rem_g^2`
RET = {'keccak_layer__L0': (790, 803), 'keccak_layer__L1': (810, 823)}
# and the point's length `y_g` (value `8`), `step_g^KR_STEP·rem_g`, as its caller computes them (`EndExec.KlQ`)
RES_EQ = {k: [((((a, 1),), 0), (((7, 1), (9, 2 * STEP)), P)), ((((b, 1),), 0), (((7, 1), (9, 2 * STEP), (10, 2)), P)),
              ((((8, 1),), 0), (((9, STEP), (10, 1)), 0))]
          for k, (a, b) in RET.items()}
# its dispatch on `step_g` has two arms: the point's block they write, as residue runs (`armblock2`)
FEATURES = {k: [{'armblock', 'armblock2'}] for k in RET}


# `e(y_g) < YB` (`EndExec.KlQ`), the bound of its whole point's run
YB = 32


def sel_bound(k, x):
    return YB if k in RET and x == 8 else None


def fam(k, r):
    """Its equation residuals (`RES_EQ`) and `e(y_g) < m`, `YB <= m` (`sel_bound`) (`Fam.lean`'s `retEqs`, `ygFam`)."""
    if r[0] == 'lt':
        # `e(y_g) < m`, and `e(step_g^16) < m` (the dispatches' blocks joined at `step_g^16`, `catM`)
        return r[1] in (('val', 8), ('mono', (((9, STEP),), 0))) and r[2][0] == 'num' and k in RET and \
            YB <= r[2][1] < 2 ** 62
    return r[0] == 'eq' and (r[1], r[2]) in RES_EQ.get(k, ())


OWN = []
