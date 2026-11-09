/-
  LeanVM.Guest.B1.Tables.VtC.AHon

  `verify_tables`' honest data: the specification's accepting run of what it mirrors, and the
  values the run fixes.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.Tables.VtC.ZBase
public import LeanVM.Guest.B1.Tables.Vt.SpecPhase
public import LeanVM.Guest.B1.Tables.Vt.SpecBus
public import LeanVM.Guest.B1.Tables.RunF
public import LeanVM.Protocol.WithHash

/-!
# The honest run

`VtHonest`: the bytecode, the memory's log-size, the public input, the bus challenges, point,
GKR values and `β`, the tables' row counts, the carried capacity `f`, the evaluator's bytecode
value `bv`, the stream words (the five framework words `xs5`, the rounds' `xsR`, the tables'
evaluations `evsT`) and the result of the run. `VtHonest.Ok`: the specification's `tablesSeg`
accepts them (`hrun`, from a sponge the guest carries as `f`).

The values the run fixes, explicitly: `busH`, the sponges `s1` (after the framework words), the
batching challenge `ξ`, the sumcheck's target, challenges `pts` and final claim `claimN`
(`zcRec`), the sponge `s3` after the evaluations, the public input's challenge `rm`.
`vt_spec`: an accepting run is this one: its result and final sponge, and the table sumcheck's
final check `terms.1 = claimN`. By determinism of the deployed reading (`runsTo_det`): the
soundness proof's run lemmas give runs of each step on the same words.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure)

@[expose] public section

/-! ## Determinism -/

/-- **Runs of one program from one sponge on one stream agree.** -/
theorem runsTo_det {α : Type} {p : VerifierProgram α} {s t1 t2 : Fs} {xs1 xs2 r1 r2 : List E}
    {a b : α}
    (h1 : RunsTo p s xs1 a t1) (h2 : RunsTo p s xs2 b t2) (hc : ∃ sp, s.Carries sp)
    (he : xs1 ++ r1 = xs2 ++ r2) : a = b ∧ t1 = t2 ∧ r1 = r2 := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp1, c1, e1⟩ := h1 sp hsp r1 [] []
  obtain ⟨sp2, c2, e2⟩ := h2 sp hsp r2 [] []
  rw [he, e2] at e1
  simp only [Option.some.injEq, Prod.mk.injEq, VerifierProgramState.mk.injEq] at e1
  obtain ⟨rfl, rfl, rfl, -⟩ := e1
  refine ⟨rfl, ?_, rfl⟩
  obtain ⟨c1a, c1b⟩ := c1
  obtain ⟨c2a, c2b⟩ := c2
  cases t1; cases t2
  simp only [Fs.mk.injEq]
  exact ⟨c1a.symm.trans c2a, c1b.symm.trans c2b⟩

/-- **An accepting run checked its requirement.** -/
theorem runsTo_require_inv {c : Prop} [Decidable c] {s t : Fs} {xs : List E} {u : Unit}
    (h : RunsTo (VerifierProgram.require c) s xs u t) (hc : ∃ sp, s.Carries sp) : c := by
  by_contra hn
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp1, -, e⟩ := h sp hsp [] [] []
  simp only [VerifierProgram.require, hn, ↓reduceIte] at e
  exact absurd e (by simp [runId, Compile.runWithHash])

/-- A run of a return returns its word, reading nothing. -/
theorem runsTo_ret_inv {α : Type} {x a : α} {s t : Fs} {xs : List E}
    (h : RunsTo (VerifierProgram.ret x) s xs a t) (hc : ∃ sp, s.Carries sp) : a = x ∧ t = s ∧ xs =
        [] := by
  obtain ⟨e1, e2, e3⟩ := runsTo_det h (runsTo_ret x s) hc (r1 := []) (r2 := xs) (by simp)
  refine ⟨e1, e2, ?_⟩
  simpa using e3.symm

/-! ## The honest data -/

/-- **`verify_tables`' honest data.** -/
structure VtHonest where
  /-- The guest's bytecode. -/
  bc : List K
  /-- The memory's log-size. -/
  lm : ℕ
  /-- The public input. -/
  pi : Digest
  /-- The bus challenges. -/
  alphas : List E
  /-- The bus point. -/
  point : List E
  /-- The GKR leaf values. -/
  values : List E
  /-- The bus's `β`. -/
  beta : E
  /-- The tables' row counts. -/
  rows : List ℕ
  /-- The carried capacity. -/
  f : List E
  /-- The evaluator. -/
  ev : (List K → List E → VerifierProgram E)
  /-- Its bytecode value. -/
  bv : E
  /-- The five framework words. -/
  xs5 : List E
  /-- The table sumcheck's round words. -/
  xsR : List E
  /-- The tables' evaluations, table by table. -/
  evsT : List (List E)
  /-- The run's bus result. -/
  bus : BusResult
  /-- The run's claims. -/
  claims : List ColumnClaim
  /-- The capacity after the run. -/
  cap' : List E

namespace VtHonest

variable (H : VtHonest)

/-- The layout. -/
noncomputable def L : Layout := layoutOf H.bc H.lm H.rows

/-- The table sumcheck's rounds: the largest height. -/
def n : ℕ := (tableHeightsOf H.rows).foldl max 0

/-- The sponge at the start. -/
def s0 : Fs := ⟨H.f, []⟩

/-- The sponge after the framework words. -/
def s1 : Fs := H.s0.absorbAll H.xs5 dsObserve

/-- The bus result. -/
noncomputable def busH : BusResult :=
  vtBus H.L H.alphas H.beta H.point H.values (H.xs5.take 3) (H.xs5.getD 3 0) (H.xs5.getD 4 0) H.bv

/-- The constraints' count. -/
abbrev nC : ℕ := (tables.map Table.nConstraints).sum

/-- The batching challenge. -/
def ξ : E := H.s1.squeeze.1

/-- The table sumcheck's target. -/
noncomputable def target : E := dot ((powers H.ξ (nC + 3)).drop nC) H.busH.totals

/-- The capacity the rounds start from. -/
def cap0 : List E := H.s1.squeeze.2.cap

/-- The rounds' challenges. -/
noncomputable def pts : List E := (List.range H.n).map (zcCh H.cap0 H.target H.xsR)

/-- The final claim. -/
noncomputable def claimN : E := (zcRec H.cap0 H.target H.xsR H.n).2

/-- The sponge after the rounds. -/
noncomputable def s2 : Fs := ⟨(zcRec H.cap0 H.target H.xsR H.n).1, []⟩

/-- The sponge after the evaluations. -/
noncomputable def s3 : Fs := H.s2.absorbAll H.evsT.flatten dsObserve

/-- The public input's challenge. -/
noncomputable def rm : E := H.s3.squeeze.1

/-- The table loop's rows. -/
noncomputable def rowsT : List (Table × ℕ × List Form × E) :=
  vtRows H.L.tableLogHeights H.busH.forms H.busH.point H.pts

/-- The table loop's result. -/
noncomputable def terms : E × List ColumnClaim :=
  termsPure ((powers H.ξ (nC + 3)).take nC) ((powers H.ξ (nC + 3)).drop nC) H.pts.reverse
    (List.zip H.rowsT H.evsT) 0 0 []

/-- The public input's claims. -/
noncomputable def pclaims : List ColumnClaim :=
  List.zipWith (fun column value ↦ ⟨column, H.rm ::
    List.replicate ((H.L.placement memory0).variableCount - 1) 0, value⟩)
    [memory0, memory1, memory2] (([0, 1, 2] : List (Fin 3)).map fun limb ↦
      multilinearEval [ofK ((digestHalves H.pi).1.limb limb),
        ofK ((digestHalves H.pi).2.limb limb)] [H.rm])

/-- **The specification accepts the honest data.** -/
structure Ok : Prop where
  hrun : RunsTo (tablesSeg H.ev H.L H.pi H.alphas H.beta H.point H.values) H.s0
    (H.xs5 ++ H.xsR ++ H.evsT.flatten) (H.bus, H.claims) ⟨H.cap', []⟩
  hcar : ∃ sp, H.s0.Carries sp
  hx5 : H.xs5.length = 5
  hxR : H.xsR.length = 3 * H.n
  hevl : H.evsT.length = H.rowsT.length
  hevw : ∀ p ∈ List.zip H.rowsT H.evsT, p.2.length = p.1.1.width
  hbv : BytecodeAt H.ev H.L.bytecode (H.point.take H.L.logBytecode ++ H.alphas) H.bv

end VtHonest

/-! ## The run is the honest one -/

theorem vt_xs5_split {xs5 : List E} (h : xs5.length = 5) :
    xs5 = xs5.take 3 ++ [xs5.getD 3 0, xs5.getD 4 0] := by
  match xs5, h with
  | [a, b, c, d, e], _ => rfl

/-- **An accepting run is the honest one**: the bus result, the claims, the final capacity, and
the table sumcheck's final check. -/
theorem vt_spec {H : VtHonest} (h : H.Ok) :
    H.terms.1 = H.claimN ∧ H.bus = H.busH ∧
      H.claims = H.busH.claims ++ H.terms.2 ++ H.pclaims ∧ H.cap' = H.s3.squeeze.2.cap := by
  obtain ⟨hrun, hcar, hx5, hxR, hevl, hevw, hbv⟩ := h
  -- the bus
  unfold tablesSeg at hrun
  obtain ⟨a1, xs1, xs2, t1, he1, r1, k1⟩ := RunsTo.unbind hrun hcar
  have hb := vt_busRest_run H.ev H.L H.alphas H.beta H.point H.values (H.xs5.take 3)
    (by simp [hx5]) (H.xs5.getD 3 0) (H.xs5.getD 4 0) H.bv hbv H.s0
  rw [← vt_xs5_split hx5] at hb
  obtain ⟨ea1, et1, ex2⟩ := runsTo_det r1 hb hcar (r1 := xs2) (r2 := H.xsR ++ H.evsT.flatten)
    (by rw [← he1, List.append_assoc])
  subst ea1 et1 ex2
  have c1 := RunsTo.carries r1 hcar
  -- the table phase and the public input
  obtain ⟨a2, xs3, xs4, t2, he2, r2, k2⟩ := RunsTo.unbind k1 c1
  have c2' := RunsTo.carries r2 c1
  obtain ⟨pc, p1s, p2s, u6, hp, o1, o2⟩ := RunsTo.unbind k2 c2'
  obtain ⟨epc, eu6, ep⟩ := runsTo_det o1 (vt_publicInputPhase_run H.L H.pi t2) c2'
    (r1 := p2s) (r2 := p1s ++ p2s) (by simp)
  have ep' : p1s = [] := by simpa using ep
  subst epc eu6 ep'
  obtain ⟨eres, eu7, ep2⟩ := runsTo_ret_inv o2 (RunsTo.carries o1 c2')
  subst ep2
  simp only [List.append_nil] at hp
  subst hp
  simp only [List.append_nil] at he2
  subst he2
  unfold tablePhaseClaims at r2
  obtain ⟨xi, ys1, ys2, u1, hy, q1, q2⟩ := RunsTo.unbind r2 c1
  obtain ⟨exi, eu1, ey1⟩ := runsTo_det q1 (runsTo_sampleE _) c1 (r1 := ys2) (r2 := ys1 ++ ys2)
    (by simp)
  have ey1' : ys1 = [] := by simpa using ey1
  subst exi eu1 ey1'
  simp only [List.nil_append] at hy
  subst hy
  have c2 := RunsTo.carries q1 c1
  obtain ⟨tc, zs1, zs2, u2, hz, w1, w2⟩ := RunsTo.unbind q2 c2
  obtain ⟨ea2, eu2, ez2⟩ := runsTo_ret_inv w2 (RunsTo.carries w1 c2)
  subst eu2 ez2
  simp only [List.append_nil] at hz
  subst hz
  -- the sumcheck
  unfold tableSumcheckClaims at w1
  obtain ⟨⟨ch, cl⟩, v1s, v2s, u3, hv, g1, g2⟩ := RunsTo.unbind w1 c2
  have hzc := zc_run H.cap0 H.target hxR
  obtain ⟨ech, eu3, ev2⟩ := runsTo_det g1 hzc c2 (r1 := v2s) (r2 := H.evsT.flatten) hv.symm
  simp only [Prod.mk.injEq] at ech
  obtain ⟨rfl, rfl⟩ := ech
  subst eu3 ev2
  have c3 := RunsTo.carries g1 c2
  -- the table loop
  obtain ⟨⟨fin, cls⟩, x1, x2, u4, hx, m1, m2⟩ := RunsTo.unbind g2 c3
  have hfst : (List.zip H.rowsT H.evsT).map (·.1) = H.rowsT := List.map_fst_zip (by omega)
  have hflat : (List.zip H.rowsT H.evsT).flatMap (·.2) = H.evsT.flatten := by
    rw [vt_flatMap_snd, List.map_snd_zip (by omega)]
  have ht := vt_runsTo_tableTerms ((powers H.ξ (VtHonest.nC + 3)).take VtHonest.nC)
    ((powers H.ξ (VtHonest.nC + 3)).drop VtHonest.nC) H.pts.reverse (List.zip H.rowsT H.evsT) 0 0 []
    H.s2 hevw
  rw [hfst, hflat] at ht
  obtain ⟨efin, eu4, ex2⟩ := runsTo_det m1 ht c3 (r1 := x2) (r2 := []) (by rw [hx]; simp)
  subst eu4 ex2
  have c4 := RunsTo.carries m1 c3
  obtain ⟨u, y1, y2, u5, hy', n1, n2⟩ := RunsTo.unbind m2 c4
  have hreq := runsTo_require_inv n1 c4
  obtain ⟨erc, eu5, -⟩ := runsTo_ret_inv n2 (RunsTo.carries n1 c4)
  obtain ⟨-, eu5', -⟩ := runsTo_det n1 (tb_runsTo_require hreq _) c4 (r1 := y2) (r2 := y1 ++ y2)
    (by simp)
  subst eu5'
  subst eu5
  simp only [Prod.mk.injEq] at eres
  have ef1 : fin = H.terms.1 := congrArg Prod.fst efin
  have ef2 : cls = H.terms.2 := congrArg Prod.snd efin
  subst erc
  refine ⟨ef1 ▸ hreq, eres.1, ?_, ?_⟩
  · rw [eres.2, ea2, ef2]; rfl
  · have := congrArg Fs.cap eu7
    exact this

end
end LeanVM.Guest.B1.Tables
