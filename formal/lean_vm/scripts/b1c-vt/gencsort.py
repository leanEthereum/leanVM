# usage: python3 -I gencsort.py  — writes Tables/VtC/SGrpT.lean: each block group's key and size
# statements (G:2141-2145 at 40f877dc) hold on the honest valuation (`vtc_grp{gi}`), from
# vt_ir.txt (dump.py). The completeness twin of gensort.py's `vt_grp{gi}`.
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from symev import IR, parse_atom

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'LeanVM', 'Guest', 'B1',
                   'Tables', 'VtC', 'SGrpT.lean')
GSTART = [0, 1, 2, 3, 8, 13, 16, 21, 26, 54, 55, 56, 57, 62, 67, 70, 75, 80, 108, 112, 116, 118, 122,
          126, 153]
SRC = [0, 1, 0, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7]


def atom(p): return parse_atom(IR[p])


def segs(lo, hi):
    out = []; cur = []
    for p in range(lo, hi):
        a = atom(p); cur.append((p, a))
        if a and a[0] == 'load' and a[1][1] in (36, 37):
            out.append(cur); cur = []
    assert not cur
    return out


def eq_of(p, a):
    op, args = a
    if op == 'const':
        d, (x, y, z) = args
        return f'σv (.n {d}) = word {x} {y} {z}'
    if op == 'mul':
        d, x, y = args
        assert x < d and y < d, (p, a)
        return f'σv (.n {d}) = σv (.n {x}) * σv (.n {y})'
    raise ValueError((p, a))


def stmt(p): return IR[p]


def group(gi, K, Z):
    a = K[0][0]; L = Z[-1][0] + 1 - a
    b0 = GSTART[gi]; ln = GSTART[gi + 1] - b0
    adj = K[0][1][0] == 'const'
    L_ = []
    def have_eq(p, a_):
        L_.append(f'  have q{p} : {eq_of(p, a_)} := by\n'
                  f'    have h := vt_goodAt (rd := rd) (w := w) hl {p} ({stmt(p)}) (by decide +kernel)\n'
                  f'    simpa only [GoodS, fixNe, fixA, Good, Nat.reduceLT, and_self, ↓reduceIte] using h')
    for p, a_ in K + Z:
        if a_[0] in ('const', 'mul'): have_eq(p, a_)
    if adj:
        (pc, c), (pk, mk) = K[0], K[1]
        kvar = mk[1][0]
        L_.append(f'  have hk : σv (.n {kvar}) = gen ^ κ := by\n'
                  f'    rw [q{pk}, q{pc}, show ({c[1][1][0]} : ℕ) = 2 ^ 19 by norm_num, tb_word_two_pow (by norm_num)]\n'
                  f'    exact hkx')
        kv = 28; adjv = 19; rest = K[2:]
    else:
        kvar = K[0][1][1][2]
        L_.append(f'  have hk : σv (.n {kvar}) = gen ^ κ := by simpa using hkx')
        kv = kvar; adjv = 0; rest = K
    # key: mul a 12 kvar; load rk a 178; [const W; mul key rk W]; load key 36 gi
    (pm, mm), (pr, lr) = rest[0], rest[1]
    assert mm == ('mul', [mm[1][0], 12, kvar]) and lr[0] == 'load' and lr[1][1] == mm[1][0] and lr[1][2] == 178
    rkv = lr[1][0]
    L_.append(f'  have r1 := vt_readAt (rd := rd) (w := w) hl {pr} (d := .n {lr[1][0]}) (p := .n {lr[1][1]}) (off := {lr[1][2]}) (by decide +kernel) (by decide +kernel)\n'
              f'    (v := gen ^ (κ * 254)) (by rw [q{pm}, hk]; exact hrk)')
    pks = rest[-1][0]
    if len(rest) == 3:
        assert b0 == 0
        keyproof = f'show LoadHolds rd _ _ _\n    rw [r1.1]; simpa using hkey'
    else:
        (pw, cw), (pmk, mk2) = rest[2], rest[3]
        W = cw[1][1][0]
        keyproof = (f'show LoadHolds rd _ _ _\n'
                    f'    rw [q{pmk}, r1.1, q{pw}, eq_inv_of_mul_eq_one_left (vt_wInv (W := {W}) (b := {b0}) (by decide +kernel))]\n'
                    f'    exact hkey')
    # size: mul a 12 kvar; load sq a 0; chain; load sz 37 gi
    (pzm, zm), (pzr, zr) = Z[0], Z[1]
    assert zm == ('mul', [zm[1][0], 12, kvar]) and zr[0] == 'load' and zr[1][2] == 0
    sqv = zr[1][0]
    L_.append(f'  have r2 := vt_readAt (rd := rd) (w := w) hl {pzr} (d := .n {zr[1][0]}) (p := .n {zr[1][1]}) (off := {zr[1][2]}) (by decide +kernel) (by decide +kernel)\n'
              f'    (v := gen ^ 2 ^ κ) (by rw [q{pzm}, hk]; exact hsq)')
    chain = Z[2:-1]
    szv = Z[-1][1][1][0]
    if chain:
        rws = ', '.join(f'q{p}' for p, _ in reversed(chain))
        L_.append(f'  have hsz2 : σv (.n {szv}) = σv (.n {sqv}) ^ {ln} := by rw [{rws}]; ring')
    else:
        assert szv == sqv and ln == 1
        L_.append(f'  have hsz2 : σv (.n {szv}) = σv (.n {sqv}) ^ {ln} := by rw [pow_one]')
    pzs = Z[-1][0]
    rl = [pr, pks, pzr, pzs]
    restl = ',\n    '.join(stmt(p) for p in rl)
    L_.append(f'  refine vt_blockR hl {a} {L} [\n    {restl}] (by decide +kernel) ?_\n'
              f'  intro s hs _\n'
              f'  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs\n'
              f'  rcases hs with rfl | rfl | rfl | rfl\n'
              f'  · exact r1.2\n'
              f'  · {keyproof}\n'
              f'  · exact r2.2\n'
              f'  · show LoadHolds rd _ _ _\n'
              f'    rw [hsz2, r2.1, ← pow_mul, Nat.mul_comm]; exact hsz')
    i = gi if gi < 9 else gi - 9
    pre = (f'  rw [show vtKv {i} = {kv} from rfl, show vtAdj {i} = {adjv} from rfl] at hkx\n'
           f'  rw [show vtGi {i} = {gi} from rfl, show vtB0 {i} = {b0} from rfl] at hkey\n'
           f'  rw [show vtGi {i} = {gi} from rfl, show vtLen {i} = {ln} from rfl] at hsz\n'
           f'  rw [show vtGrpA {i} = {a} from rfl, show vtGrpL {i} = {L} from rfl]')
    L_.insert(0, pre)
    head = (f'set_option maxRecDepth 100000 in\n'
            f'/-- Group `{gi}`\'s key and size statements (`{a} ..< {a + L}`). -/\n'
            f'theorem vtc_grp{gi} (hl : args.length = 20) {{κ : ℕ}}\n'
            f'    (hkx : σv (.n (vtKv {i})) * gen ^ vtAdj {i} = gen ^ κ)\n'
            f'    (hrk : LoadHolds rd (σv (.n 12) * gen ^ κ) 178 (gen ^ (κ * 254)))\n'
            f'    (hsq : LoadHolds rd (σv (.n 12) * gen ^ κ) 0 (gen ^ 2 ^ κ))\n'
            f'    (hkey : LoadHolds rd (σv (.n 36)) (vtGi {i}) (gen ^ (κ * 254) * (gen ^ vtB0 {i})⁻¹))\n'
            f'    (hsz : LoadHolds rd (σv (.n 37)) (vtGi {i}) (gen ^ (vtLen {i} * 2 ^ κ))) :\n'
            f'    ∀ s ∈ (vtPre.drop (vtGrpA {i})).take (vtGrpL {i}), VSH (coreProgram.Rel rd) rd σv s := by')
    return head + '\n' + '\n'.join(L_), (gi, a, L, kv, adjv, b0, ln)


HDR = '''/-
  LeanVM.Guest.B1.Tables.VtC.SGrpT

  Each block group's key and size statements hold on the honest valuation. Generated by
  `scripts/b1c-vt/gencsort.py`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SBase

/-!
# The block groups' keys and sizes, honestly (G:2124-2128)

`vtc_grp{gi}`: with `kappa_g = g^κ` (the group's `kappa_base` variable, times `g^19` for the
bytecode's group `2`), the exponent tables' rank key `g^(254 κ)` and square `g^(2^κ)` at `κ`, and
`group_key[gi]`, `group_size[gi]` holding the group's key `g^(254 κ - b0)` and size
`g^(len·2^κ)`, the group's statements hold: two reads, two stores.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

local notation "σv" => vtσ rd w args

'''


def main():
    s = segs(21, 113) + segs(342, 406)
    gis = list(range(9)) + list(range(18, 24))
    out = []; data = []
    for i, gi in enumerate(gis):
        txt, d = group(gi, s[2 * i], s[2 * i + 1]); out.append(txt); data.append(d)
    A = ', '.join(str(d[1]) for d in data); Ls = ', '.join(str(d[2]) for d in data)
    defs = (f'/-- Group `k`\'s first statement and its number of statements (`k < 15`, `vtGi`). -/\n'
            f'def vtGrpA (k : ℕ) : ℕ := [{A}].getD k 0\n'
            f'def vtGrpL (k : ℕ) : ℕ := [{Ls}].getD k 0\n\n')
    disp = ('/-- **Every group\'s key and size statements**, by group. -/\n'
            'theorem vtc_grps (hl : args.length = 20) {k : ℕ} (hk : k < 15) {κ : ℕ}\n'
            '    (hkx : σv (.n (vtKv k)) * gen ^ vtAdj k = gen ^ κ)\n'
            '    (hrk : LoadHolds rd (σv (.n 12) * gen ^ κ) 178 (gen ^ (κ * 254)))\n'
            '    (hsq : LoadHolds rd (σv (.n 12) * gen ^ κ) 0 (gen ^ 2 ^ κ))\n'
            '    (hkey : LoadHolds rd (σv (.n 36)) (vtGi k) (gen ^ (κ * 254) * (gen ^ vtB0 k)⁻¹))\n'
            '    (hsz : LoadHolds rd (σv (.n 37)) (vtGi k) (gen ^ (vtLen k * 2 ^ κ))) :\n'
            '    ∀ s ∈ (vtPre.drop (vtGrpA k)).take (vtGrpL k), VSH (coreProgram.Rel rd) rd σv s := by\n'
            '  interval_cases k\n' +
            ''.join(f'  · exact vtc_grp{gi} hl hkx hrk hsq hkey hsz\n' for gi in gis))
    with open(OUT, 'w') as f:
        f.write(HDR.replace('section\nvariable', defs + 'section\nvariable', 1) + '\n\n'.join(out) + '\n\n' + disp + '\nend\n\nend\nend LeanVM.Guest.B1.Tables\n')
    for d in data: print(d)


main()
