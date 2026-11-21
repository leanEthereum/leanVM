# usage: python3 -I gencshared.py  — writes Tables/VtC/SShT.lean: each table's shared selector
# tables' statements hold on the honest valuation (`vtc_sh{t}`), and the
# tables' pointers (`vtc_shptr`), from vt_ir.txt (dump.py). The completeness twin of genshared.py.
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from symev import IR, parse_atom

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'LeanVM', 'Guest', 'B1',
                   'Tables', 'VtC', 'SShT.lean')
from anchors import SH_CALLS, SH_RUN, SH_Q, SH_EQA, SH_GA, SH_EQ, SH_G


def atom(p): return parse_atom(IR[p])


def slices():
    """table `t`'s statements: from its `shared_len` to the copies of its two tables."""
    return [(r - 4, q) for r, q in zip(SH_RUN, SH_CALLS)]


def defs():
    d = {}
    for p in range(SH_RUN[0] - 4, SH_CALLS[-1] + 3):
        a = atom(p)
        if a is None: continue
        op, args = a
        if op == 'mul' and args[1] < args[0] and args[2] < args[0]: d[args[0]] = (p, 'mul', args[1:])
        elif op == 'const': d[args[0]] = (p, 'const', args[1])
        elif op == 'copy': d[args[0]] = (p, 'copy', args[1:])
    return d


D = defs()


def gen():
    import re
    S = slices()
    L = []
    call_args = [[int(x) for x in re.findall(r'\.n (\d+)', IR[q])] for _, q in S]
    cases = []
    for t, (p, q) in enumerate(S):
        ea, ga = SH_EQA[t], SH_GA[t]
        assert D[SH_EQ[t]] == (q + 1, 'copy', [ea]) and D[SH_G[t]] == (q + 2, 'copy', [ga])
        cases.append(f'  · exact ⟨by\n'
                     f'      show σv (.n {SH_EQ[t]}) = w {ea}\n'
                     f'      rw [vt_copyAt hl {q + 1} (d := .n {SH_EQ[t]}) (x := .n {ea}) (by decide +kernel),\n'
                     f'        vt_allocDynAt hl {q - 5} (d := .n {ea}) (s := .n {SH_Q[t] + 7}) (by decide +kernel)],\n'
                     f'    by\n'
                     f'      show σv (.n {SH_G[t]}) = w {ga}\n'
                     f'      rw [vt_copyAt hl {q + 2} (d := .n {SH_G[t]}) (x := .n {ga}) (by decide +kernel),\n'
                     f'        vt_allocDynAt hl {q - 4} (d := .n {ga}) (s := .n {SH_Q[t] + 6}) (by decide +kernel)]⟩')
    L.append('set_option maxRecDepth 100000 in\n'
             '/-- **The tables\' pointers**: table `t`\'s nibble tables are the two buffers it allocated,\n'
             'the oracle\'s answers. -/\n'
             'theorem vtc_shptr (hl : args.length = 20) : ∀ t < 6,\n'
             '    σv (.n (vtEqV t)) = w (vtEqV t - 5) ∧ σv (.n (vtGV t)) = w (vtGV t - 5) := by\n'
             '  intro t ht\n  interval_cases t\n' + '\n'.join(cases))
    for t, (p, q) in enumerate(S):
        Lt = []
        a0 = atom(p); assert a0[0] == 'mul' and a0[1][0] == 9 and a0[1][2] == 27 + t
        v = a0[1][1]
        a1 = atom(p + 1); assert a1 == ('copy', [v + 1, v])
        a2 = atom(p + 2); assert a2[0] == 'const' and a2[1][1][0] == 8589934592
        k = a2[1][0]
        rc = IR[p + 3]; assert rc.startswith('.atom (.rangeCheck (.n %d)' % (v + 1))
        rv = [int(x) for x in re.findall(r'\.n (\d+)', rc)]
        x_, y_, t1, t2, k_ = rv; assert k_ == k and k < y_
        ea, ga, zp, z1p, sqp, lenv, qv = call_args[t]
        assert lenv == v + 1 and qv == SH_Q[t] and p + 4 == SH_RUN[t]
        run = IR[p + 4]
        c2 = atom(p + 5); assert c2 == ('const', [qv + 1, (2, 0)]), c2
        chain = [(p + 6, qv + 2, qv, qv + 1)] + [(p + 6 + i, qv + 2 + i, qv + 1 + i, qv + 1 + i) for i in range(1, 6)]
        for pp, d, x, y in chain:
            assert atom(pp) == ('mul', [d, x, y]), (pp, IR[pp])
        def mulq(var, src):
            pp, op, args = D[var]
            assert op == 'mul' and args == [src, 27 + t], (var, D[var])
            return f'vt_mulAt hl {pp} (d := {var}) (x := {src}) (y := {27 + t}) (by norm_num) (by norm_num) (by decide +kernel)'
        def mulc(pp, d, x, y):
            return f'vt_mulAt hl {pp} (d := {d}) (x := {x}) (y := {y}) (by norm_num) (by norm_num) (by decide +kernel)'
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
        Lt.append(f'  have eq : σv (.n {qv}) = gen ^ ((μ - τ) / 4) := by\n'
                  f'    rw [vtc_ret1 (rd := rd) (w := w) hl {p + 4} "selector_run_nibbles" [.n {lenv}] {qv} (by decide +kernel), hq]')
        Lt.append(f'  have e1 : σv (.n {qv + 2}) = gen ^ ((μ - τ) / 4 + 1) := by\n'
                  f'    rw [{mulc(*chain[0])}, eq,\n'
                  f'      vt_constAt hl {p + 5} (d := .n {qv + 1}) (e := word 2 0) (by decide +kernel), tb_word_gen, pow_succ]')
        prev = 'e1'
        for i in range(1, 6):
            pp, d, x, y = chain[i]
            Lt.append(f'  have e{i + 1} : σv (.n {d}) = gen ^ ({2 ** i} * ((μ - τ) / 4 + 1)) := by\n'
                      f'    rw [{mulc(pp, d, x, y)}, {prev}]; ring')
            prev = f'e{i + 1}'
        Lt.append(f'  have ez : σv (.n {zp}) = σv (.n 8) * gen ^ τ := by rw [{mulq(zp, 8)}, hkb]')
        Lt.append(f'  have ez1 : σv (.n {z1p}) = σv (.n 699) * gen ^ τ := by rw [{mulq(z1p, 699)}, hkb]')
        Lt.append(f'  have esq : σv (.n {sqp}) = σv (.n 12) * gen ^ τ := by rw [{mulq(sqp, 12)}, hkb]')
        Lt.append(f'  have ea : σv (.n {ea}) = w {ea} := vt_allocDynAt hl {p + 12} (d := .n {ea}) (s := .n {qv + 7}) (by decide +kernel)')
        Lt.append(f'  have ega : σv (.n {ga}) = w {ga} := vt_allocDynAt hl {p + 13} (d := .n {ga}) (s := .n {qv + 6}) (by decide +kernel)')
        call = IR[q]
        Lt.append(f'  refine ⟨vt_blockR hl {p} {q + 3 - p} [\n'
                  f'    .atom (.mul (.n 9) (.n {v}) (.n {27 + t})),\n'
                  f'    {rc},\n'
                  f'    {run},\n'
                  f'    {call}] (by decide +kernel) ?_, by\n'
                  f'      rw [show vtShLen {t} = {v + 1} from rfl]; exact ec, e6, e5⟩\n'
                  f'  intro s hs _\n'
                  f'  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs\n'
                  f'  rcases hs with rfl | rfl | rfl | rfl\n'
                  f'  · exact mulDiv_holds (rd := rd) qd (by rw [hkb]; exact gen_pow_ne_zero _)\n'
                  f'  · exact hrc\n'
                  f'  · show coreProgram.Rel rd _ _ _\n'
                  f'    simp only [List.map_cons, List.map_nil]\n'
                  f'    rw [ec, eq]\n'
                  f'    exact sr_call (by omega)\n'
                  f'  · show coreProgram.Rel rd _ _ _\n'
                  f'    simp only [List.map_cons, List.map_nil]\n'
                  f'    rw [ea, ega, ez, ez1, esq, ec, eq]\n'
                  f'    exact sh_call hμ hμ33 hτμ (tbReadsAt_drop hz τ)\n'
                  f'      (tbReadsAt_drop hz1 τ) (tbReadsAt_take (tbReadsAt_drop hsq τ) _) hrun')
        head = (f'set_option maxRecDepth 100000 in\n'
                f'/-- **Table `{t}`\'s shared selector tables** (`{p} ..< {q + 3}`). -/\n'
                f'theorem vtc_sh{t} (hl : args.length = 20) (hlow : LowDefB 14 rd) {{μ τ : ℕ}} {{point : List E}}\n'
                f'    (hkb : σv (.n {27 + t}) = gen ^ τ) (h9 : σv (.n 9) = gen ^ μ) (hμ : point.length = μ)\n'
                f'    (hμ33 : μ < 33) (hτμ : τ ≤ μ) (hz : TbReadsAt rd (σv (.n 8)) point)\n'
                f'    (hz1 : TbReadsAt rd (σv (.n 699)) (point.map (1 + ·)))\n'
                f'    (hsq : TbReadsAt rd (σv (.n 12)) gSquaresList) (hq : w {qv} = gen ^ ((μ - τ) / 4))\n'
                f'    (hrun : RunTables rd (w {ea}) (w {ga}) (μ - τ)\n'
                f'      (point.drop τ) ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take (μ - τ))) :\n'
                f'    (∀ s ∈ (vtPre.drop {p}).take {q + 3 - p}, VSH (coreProgram.Rel rd) rd σv s) ∧\n'
                f'      σv (.n (vtShLen {t})) = gen ^ (μ - τ) ∧\n'
                f'      σv (.n {qv + 7}) = gen ^ (32 * ((μ - τ) / 4 + 1)) ∧\n'
                f'      σv (.n {qv + 6}) = gen ^ (16 * ((μ - τ) / 4 + 1)) := by')
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
# The shared selector tables, honestly

`vtc_shptr`: table `t`'s nibble tables' pointers, the copies of its two allocations, the oracle's
answers. `vtc_sh{t}`: with `kappa_base[2 + t] = g^τ`, `g_bus_mu = g^μ`, the bus point at `zeta`,
`1 + ζ` at `zeta1`, the squares at `g_squares`, the oracle's `g^q` for `selector_run_nibbles`
(`q = (μ - τ) / 4`) and its two pointers holding the table's nibble tables (`RunTables`), its
statements hold, `shared_len[t] = g^(μ - τ)` and the tables' sizes are `g^(32(q + 1))`, `g^(16(q + 1))`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
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
