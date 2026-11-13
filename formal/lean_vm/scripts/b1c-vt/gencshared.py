# usage: python3 -I gencshared.py  — writes Tables/VtC/SShT.lean: each table's shared selector
# tables' statements (G:2318-2325) hold on the honest valuation (`vtc_sh{t}`), and the
# tables' pointers (`vtc_shptr`), from vt_ir.txt (dump.py). The completeness twin of genshared.py.
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from symev import IR, parse_atom

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'LeanVM', 'Guest', 'B1',
                   'Tables', 'VtC', 'SShT.lean')
W = {8589934592: None, 299140177199104: 'vtW288_eq', 21299200: 'vtW144_eq'}


def atom(p): return parse_atom(IR[p])


def slices():
    out = []; p = 697
    while p <= 764:
        q = p
        while not IR[q].startswith('.call "shared_selector_tables"'): q += 1
        out.append((p, q)); p = q + 1
    assert len(out) == 6, out
    return out


def defs():
    d = {}
    for p in range(695, 765):
        a = atom(p)
        if a is None: continue
        op, args = a
        if op == 'mul' and args[1] < args[0] and args[2] < args[0]: d[args[0]] = (p, 'mul', args[1:])
        elif op == 'const': d[args[0]] = (p, 'const', args[1])
        elif op == 'copy': d[args[0]] = (p, 'copy', args[1:])
    return d


D = defs()


def ptr_rws(v, base):
    """rewrites taking σ v down to σ base times words, positions used."""
    rws = []
    while v != base:
        p, op, args = D[v]
        assert op == 'mul', (v, op)
        x, y = args
        rws.append(f'vt_mulAt hl {p} (d := {v}) (x := {x}) (y := {y}) (by norm_num) (by norm_num) (by decide +kernel)')
        c = D[y]
        assert c[1] == 'const'
        rws.append(f'vt_constAt hl {c[0]} (d := .n {y}) (e := word {c[2][0]} 0) (by decide +kernel)')
        rws.append(W[c[2][0]])
        v = x
    return rws


def gen():
    S = slices()
    L = []
    # pointers
    call_args = []
    for (p, q) in S:
        import re
        a = [int(x) for x in re.findall(r'\.n (\d+)', IR[q])]
        call_args.append(a)
    eqv = [a[0] for a in call_args]; gv = [a[1] for a in call_args]
    cases = []
    for t in range(6):
        r1 = ptr_rws(eqv[t], 701); r2 = ptr_rws(gv[t], 702)
        def pr(rws):
            if not rws: return 'by ring'
            tail = '' if len(rws) == 3 else '\n      ring'
            return 'by\n      rw [' + ',\n        '.join(rws) + ']' + tail
        cases.append(f'  · show σv (.n {eqv[t]}) = σv (.n 701) * gen ^ (288 * {t}) ∧\n'
                     f'      σv (.n {gv[t]}) = σv (.n 702) * gen ^ (144 * {t})\n'
                     f'    exact ⟨{pr(r1)},\n      {pr(r2)}⟩')
    L.append('set_option maxRecDepth 100000 in\n'
             '/-- **The tables\' pointers**: table `t`\'s nibble tables at `shared_eq·g^(288 t)`, '
             '`shared_g·g^(144 t)`. -/\n'
             'theorem vtc_shptr (hl : args.length = 20) : ∀ t < 6,\n'
             '    σv (.n (vtEqV t)) = σv (.n 701) * gen ^ (288 * t) ∧\n'
             '      σv (.n (vtGV t)) = σv (.n 702) * gen ^ (144 * t) := by\n'
             '  intro t ht\n  interval_cases t\n' + '\n'.join(cases))
    for t, (p, q) in enumerate(S):
        Lt = []
        a0 = atom(p); assert a0[0] == 'mul' and a0[1][0] == 9 and a0[1][2] == 27 + t
        v = a0[1][1]
        a1 = atom(p + 1); assert a1 == ('copy', [v + 1, v])
        a2 = atom(p + 2); assert a2[0] == 'const' and a2[1][1][0] == 8589934592
        k = a2[1][0]
        rc = IR[p + 3]; assert rc.startswith('.atom (.rangeCheck (.n %d)' % (v + 1))
        import re
        rv = [int(x) for x in re.findall(r'\.n (\d+)', rc)]
        x_, y_, t1, t2, k_ = rv; assert k_ == k and k < y_
        zp, z1p, sqp = call_args[t][2], call_args[t][3], call_args[t][4]
        def mulq(var, src):
            pp, op, args = D[var]
            assert op == 'mul' and args == [src, 27 + t], (var, D[var])
            return f'vt_mulAt hl {pp} (d := {var}) (x := {src}) (y := {27 + t}) (by norm_num) (by norm_num) (by decide +kernel)'
        Lt.append(f'  have qd : σv (.n {v}) = σv (.n 9) * (σv (.n {27 + t}))⁻¹ := by\n'
                  f'    have h := vt_goodAt (rd := rd) (w := w) hl {p} (.atom (.mul (.n 9) (.n {v}) (.n {27 + t}))) (by decide +kernel)\n'
                  f'    simpa only [GoodS, fixNe, Good, Nat.reduceLT, and_false, false_and, ↓reduceIte] using h')
        Lt.append(f'  have ev : σv (.n {v}) = gen ^ (μ - τ) := by rw [qd, h9, hkb, gen_pow_div hτμ]')
        Lt.append(f'  have ec : σv (.n {v + 1}) = gen ^ (μ - τ) := by rw [vt_copyAt hl {p + 1} (d := .n {v + 1}) (x := .n {v}) (by decide +kernel), ev]')
        Lt.append(f'  have qr := vt_goodAt (rd := rd) (w := w) hl {p + 3} ({rc}) (by decide +kernel)\n'
                  f'  simp only [GoodS, fixNe, Good, Nat.reduceLT, ↓reduceIte] at qr\n'
                  f'  obtain ⟨r1, r2, r3⟩ := qr\n'
                  f'  obtain ⟨hrc, -⟩ := rc_holds (κ := 14) hlow r1 r2 r3 ec\n'
                  f'    (by rw [vt_constAt hl {p + 2} (d := .n {k}) (e := word 8589934592 0) (by decide +kernel), ← vtW33, vtW33_gen])\n'
                  f'    (by omega) (by norm_num)')
        Lt.append(f'  obtain ⟨pe, pg⟩ := vtc_shptr hl {t} (by norm_num)')
        Lt.append(f'  have ez : σv (.n {zp}) = σv (.n 8) * gen ^ τ := by rw [{mulq(zp, 8)}, hkb]')
        Lt.append(f'  have ez1 : σv (.n {z1p}) = σv (.n 699) * gen ^ τ := by rw [{mulq(z1p, 699)}, hkb]')
        Lt.append(f'  have esq : σv (.n {sqp}) = σv (.n 12) * gen ^ τ := by rw [{mulq(sqp, 12)}, hkb]')
        call = IR[q]
        Lt.append(f'  refine ⟨vt_blockR hl {p} {q + 1 - p} [\n'
                  f'    .atom (.mul (.n 9) (.n {v}) (.n {27 + t})),\n'
                  f'    {rc},\n'
                  f'    {call}] (by decide +kernel) ?_, by\n'
                  f'      rw [show vtShLen {t} = {v + 1} from rfl]; exact ec⟩\n'
                  f'  intro s hs _\n'
                  f'  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs\n'
                  f'  rcases hs with rfl | rfl | rfl\n'
                  f'  · exact mulDiv_holds (rd := rd) qd (by rw [hkb]; exact gen_pow_ne_zero _)\n'
                  f'  · exact hrc\n'
                  f'  · show coreProgram.Rel rd _ _ _\n'
                  f'    simp only [List.map_cons, List.map_nil]\n'
                  f'    rw [show vtEqV {t} = {call_args[t][0]} from rfl] at pe\n'
                  f'    rw [show vtGV {t} = {call_args[t][1]} from rfl] at pg\n'
                  f'    rw [pe, pg, ez, ez1, esq, ec]\n'
                  f'    exact sh_call hμ hμ33 hτμ (tbReadsAt_drop hz τ)\n'
                  f'      (tbReadsAt_drop hz1 τ) (tbReadsAt_take (tbReadsAt_drop hsq τ) _) hrun')
        head = (f'set_option maxRecDepth 100000 in\n'
                f'/-- **Table `{t}`\'s shared selector tables** (`{p} ..< {q + 1}`). -/\n'
                f'theorem vtc_sh{t} (hl : args.length = 20) (hlow : LowDefB 14 rd) {{μ τ : ℕ}} {{point : List E}}\n'
                f'    (hkb : σv (.n {27 + t}) = gen ^ τ) (h9 : σv (.n 9) = gen ^ μ) (hμ : point.length = μ)\n'
                f'    (hμ33 : μ < 33) (hτμ : τ ≤ μ) (hz : TbReadsAt rd (σv (.n 8)) point)\n'
                f'    (hz1 : TbReadsAt rd (σv (.n 699)) (point.map (1 + ·)))\n'
                f'    (hsq : TbReadsAt rd (σv (.n 12)) gSquaresList)\n'
                f'    (hrun : RunTables rd (σv (.n 701) * gen ^ (288 * {t})) (σv (.n 702) * gen ^ (144 * {t})) (μ - τ)\n'
                f'      (point.drop τ) ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take (μ - τ))) :\n'
                f'    (∀ s ∈ (vtPre.drop {p}).take {q + 1 - p}, VSH (coreProgram.Rel rd) rd σv s) ∧\n'
                f'      σv (.n (vtShLen {t})) = gen ^ (μ - τ) := by')
        L.append(head + '\n' + '\n'.join(Lt))
    return L, S


HDR = '''/-
  LeanVM.Guest.B1.Tables.VtC.SShT

  Each table's shared selector tables' statements hold on the honest valuation. Generated by
  `scripts/b1c-vt/gencshared.py`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SShared

/-!
# The shared selector tables, honestly (G:2318-2325)

`vtc_shptr`: table `t`'s nibble tables' pointers, `shared_eq·g^(288 t)` and `shared_g·g^(144 t)`.
`vtc_sh{t}`: with `kappa_base[2 + t] = g^τ`, `g_bus_mu = g^μ`, the bus point at `zeta`, `1 + ζ` at
`zeta1`, the squares at `g_squares`, and the table's nibble tables holding their words
(`RunTables`), its statements hold and `shared_len[t] = g^(μ - τ)`.
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

L, S = gen()
with open(OUT, 'w') as f:
    f.write(HDR + '\n\n'.join(L) + '\n\nend\n\nend\nend LeanVM.Guest.B1.Tables\n')
print(S)
