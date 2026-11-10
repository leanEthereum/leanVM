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

`VtHonest`: the bytecode, the memory's log-size, the public input, the slot weights, the bus
point, GKR values and `β`, the tables' row counts, the carried capacity `f`, the evaluator `ev`,
the stream words (the four framework words `xs4`, the bytecode share's ten `bcW`: the share, the
slot sumcheck's eight, the value; the table sumcheck's `xsR`, the tables' evaluations `evsT`) and
the result of the run. `VtHonest.Ok`: the specification's `tablesSeg` accepts them (`hrun`, from a
sponge the guest carries as `f`).

The values the run fixes, explicitly: the slot sumcheck's rounds (`bcRec`, `bcCh`: the sponge and
claim before each round of a plain degree-3 sumcheck, its challenges), the slot point `slots`,
`busH`, the sponge `sB` after the share's value, the batching challenge `ξ` (a `0`-bit grind, then a
squeeze), the table sumcheck's target, challenges `pts` and final claim `claimN` (`zcRec`), the
sponge `s3` after the evaluations, the public input's challenge `rm`.

`vt_spec`: an accepting run is this one: the slot sumcheck's final check (`bcClaim`), the table
sumcheck's (`terms.1 = claimN`), its result and final sponge. The run is read as an equation of
the carried run (`RunsTo.runT_eq`) down to the share's check; the rest splits at known runs
(`RunsTo.unbind_at`).
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
  obtain ⟨ea, et, -, er⟩ := runsToX_det (g := none) h1 h2 hc he
  exact ⟨ea, et, er⟩

/-- An accepting run checked its requirement. -/
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

/-! ## Runs as equations of the carried run -/

/-- A run is an equation of the carried run, on any rest of the stream. -/
theorem RunsTo.runT_eq {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s') (hc : ∃ sp, s.Carries sp) (rest : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) :
    runT p ⟨s, none, xs ++ rest, os, R⟩ = some (a, ⟨s', none, rest, os, R⟩) := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp', hc', he⟩ := h sp hsp rest os R
  rw [runT_of_runId p ⟨s, none, xs ++ rest, os, R⟩ sp hsp a _ he]
  obtain ⟨e1, e2⟩ := eq_fsOfT (g := none) hc'
  rw [← e1, ← e2]

/-- `RunsTo.runT_eq` for a run reading nothing. -/
theorem RunsTo.runT_eq0 {α : Type} {p : VerifierProgram α} {s s' : Fs} {a : α}
    (h : RunsTo p s [] a s') (hc : ∃ sp, s.Carries sp) (rest : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) :
    runT p ⟨s, none, rest, os, R⟩ = some (a, ⟨s', none, rest, os, R⟩) :=
  RunsTo.runT_eq h hc rest os R

theorem runT_bind' {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β) (st : TSt) :
    runT (p >>= f) st = (runT p st).bind (fun r ↦ runT (f r.1) r.2) := runT_bind p f st

theorem runT_require {c : Prop} [Decidable c] (st : TSt) :
    runT (VerifierProgram.require c) st = if c then some ((), st) else none := by
  unfold VerifierProgram.require
  split <;> rfl

/-! ## The slot sumcheck, honestly -/

/-- The sponge and the claim before round `j` of the plain degree-3 sumcheck from the sponge `s`
and the claim `cl`, round `j` reading `ws[2j], ws[2j+1]` (`c0, c2`). -/
def bcRec (s : Fs) (cl : E) (ws : List E) : ℕ → Fs × E
  | 0 => (s, cl)
  | j + 1 =>
    let r := bcRec s cl ws j
    let c0 := ws.getD (2 * j) 0
    let c2 := ws.getD (2 * j + 1) 0
    let t := (r.1.absorbAll [c0, c2] dsObserve).squeeze
    (t.2, polyEval [c0, r.2 + sumE [c2], c2] t.1)

/-- Round `j`'s challenge. -/
def bcCh (s : Fs) (cl : E) (ws : List E) (j : ℕ) : E :=
  ((bcRec s cl ws j).1.absorbAll [ws.getD (2 * j) 0, ws.getD (2 * j + 1) 0] dsObserve).squeeze.1

theorem bc_slice {ws : List E} {j k : ℕ} (h : 2 * (j + k + 1) ≤ ws.length) :
    (ws.drop (2 * j)).take (2 * (k + 1)) =
      [ws.getD (2 * j) 0, ws.getD (2 * j + 1) 0] ++ (ws.drop (2 * (j + 1))).take (2 * k) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop]
    rcases Nat.lt_or_ge i 2 with hi | hi
    · rw [List.getElem_append_left (by simpa using hi)]
      interval_cases i <;> simp <;> rw [List.getElem?_eq_getElem (by omega)] <;> rfl
    · rw [List.getElem_append_right (by simpa using hi)]
      simp only [List.length_cons, List.length_nil, List.getElem_take, List.getElem_drop]
      congr 1; omega

/-- **The honest rounds are the specification's degree-3 sumcheck.** -/
theorem bc_run (s : Fs) (cl : E) {ws : List E} {n : ℕ} (hl : ws.length = 2 * n) :
    RunsTo (sumcheck cl 3 (List.replicate n none)) s ws
      ((List.range n).map (bcCh s cl ws), (bcRec s cl ws n).2) (bcRec s cl ws n).1 := by
  have key : ∀ k j, j + k = n → RunsTo (sumcheck (bcRec s cl ws j).2 3 (List.replicate k none))
      (bcRec s cl ws j).1 ((ws.drop (2 * j)).take (2 * k))
      ((List.range k).map (fun i ↦ bcCh s cl ws (j + i)), (bcRec s cl ws n).2)
      (bcRec s cl ws n).1 := by
    intro k
    induction k with
    | zero =>
      intro j hj
      obtain rfl : j = n := by omega
      exact runsTo_sumcheck_nil _ _ _
    | succ k ih =>
      intro j hj
      have h1 := runsTo_roundPolyNone (bcRec s cl ws j).1 (bcRec s cl ws j).2
        (ws.getD (2 * j) 0) [ws.getD (2 * j + 1) 0] 3 rfl (by decide)
      have h2 := ih (j + 1) (by omega)
      have e : ((bcRec s cl ws j).1.absorb (ws.getD (2 * j) 0) dsObserve).absorbAll
          [ws.getD (2 * j + 1) 0] dsObserve =
          (bcRec s cl ws j).1.absorbAll [ws.getD (2 * j) 0, ws.getD (2 * j + 1) 0] dsObserve := rfl
      rw [e] at h1
      have h := runsTo_sumcheck_cons h1 h2
      rw [List.replicate_succ, bc_slice (by omega), List.range_succ_eq_map, List.map_cons,
        List.map_map]
      refine h.of_eq rfl rfl ?_ rfl
      rw [Nat.add_zero]
      refine Prod.ext (congrArg₂ List.cons rfl (List.map_congr_left fun i _ => ?_)) rfl
      simp only [Function.comp_apply]
      rw [show j + 1 + i = j + (i + 1) by omega]
  have := key n 0 (by omega)
  simp only [Nat.mul_zero, List.drop_zero, Nat.zero_add] at this
  rw [← hl, List.take_length] at this
  exact this

/-- The bytecode share's words `[S] ++ ws ++ [v]`. -/
theorem bcW_split {bcW : List E} (h : bcW.length = 10) :
    bcW = [bcW.getD 0 0] ++ ((bcW.drop 1).take 8 ++ [bcW.getD 9 0]) := by
  match bcW, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9], _ => rfl

theorem bcW_eq {bcW : List E} (h : bcW.length = 10) :
    [bcW.getD 0 0] ++ ((bcW.drop 1).take 8 ++ ([bcW.getD 9 0] ++ ([] ++ []))) = bcW := by
  match bcW, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9], _ => rfl

/-- The slot sumcheck's sponge before its rounds: the share absorbed. -/
def bcS0 (s : Fs) (bcW : List E) : Fs := s.absorb (bcW.getD 0 0) dsObserve

/-- The slot sumcheck's rounds' words. -/
def bcWs (bcW : List E) : List E := (bcW.drop 1).take 8

/-- The slot point. -/
def bcSlots (s : Fs) (bcW : List E) : List E :=
  (List.range busBits).map (bcCh (bcS0 s bcW) (bcW.getD 0 0) (bcWs bcW))

/-- The slot sumcheck's final claim. -/
def bcClaim (s : Fs) (bcW : List E) : E := (bcRec (bcS0 s bcW) (bcW.getD 0 0) (bcWs bcW) busBits).2

/-- The sponge after the share's value. -/
def bcEnd (s : Fs) (bcW : List E) : Fs :=
  (bcRec (bcS0 s bcW) (bcW.getD 0 0) (bcWs bcW) busBits).1.absorb (bcW.getD 9 0) dsObserve

theorem bcWs_length {bcW : List E} (h : bcW.length = 10) : (bcWs bcW).length = 2 * busBits := by
  simp [bcWs, h, busBits]

/-- **The bytecode share, honestly**: when its final check holds. -/
theorem bcShare_run (weights low : List E) (s : Fs) {bcW : List E} (hl : bcW.length = 10)
    (hreq : bcClaim s bcW = dot (eqKernel (bcSlots s bcW)) weights * bcW.getD 9 0) :
    RunsTo (bytecodeShare weights low) s bcW (bcW.getD 0 0, low ++ bcSlots s bcW, bcW.getD 9 0)
      (bcEnd s bcW) := by
  have h1 := runsTo_readE s (bcW.getD 0 0)
  have h2 := bc_run (bcS0 s bcW) (bcW.getD 0 0) (bcWs_length hl)
  have h3 := runsTo_readE (bcRec (bcS0 s bcW) (bcW.getD 0 0) (bcWs bcW) busBits).1 (bcW.getD 9 0)
  have h4 := tb_runsTo_require hreq (bcEnd s bcW)
  have h5 := runsTo_ret (bcW.getD 0 0, low ++ bcSlots s bcW, bcW.getD 9 0) (bcEnd s bcW)
  unfold bytecodeShare
  exact RunsTo.of_eq (h1.bind (h2.bind (h3.bind (h4.bind h5)))) rfl (bcW_eq hl) rfl rfl

/-- **The bytecode share's final check**, from an accepting carried run. -/
theorem bcShare_inv (weights low : List E) {s : Fs} (hc : ∃ sp, s.Carries sp) {bcW : List E}
    (hl : bcW.length = 10) {rest : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)}
    {r : E × List E × E} {st : TSt}
    (h : runT (bytecodeShare weights low) ⟨s, none, bcW ++ rest, os, R⟩ = some (r, st)) :
    bcClaim s bcW = dot (eqKernel (bcSlots s bcW)) weights * bcW.getD 9 0 := by
  have h1 := runsTo_readE s (bcW.getD 0 0)
  have c1 := RunsTo.carries h1 hc
  have h2 : RunsTo (sumcheck (bcW.getD 0 0) 3 (List.replicate busBits none))
      (s.absorb (bcW.getD 0 0) dsObserve) (bcWs bcW) _ _ :=
    bc_run (bcS0 s bcW) (bcW.getD 0 0) (bcWs_length hl)
  have c2 := RunsTo.carries h2 c1
  have h3 := runsTo_readE (bcRec (bcS0 s bcW) (bcW.getD 0 0) (bcWs bcW) busBits).1 (bcW.getD 9 0)
  have e : bcW ++ rest = [bcW.getD 0 0] ++ (bcWs bcW ++ ([bcW.getD 9 0] ++ rest)) := by
    conv_lhs => rw [bcW_split hl]
    simp [bcWs]
  rw [e] at h
  unfold bytecodeShare at h
  rw [runT_bind', RunsTo.runT_eq h1 hc, Option.bind_some] at h
  dsimp only at h
  rw [runT_bind', RunsTo.runT_eq h2 c1, Option.bind_some] at h
  dsimp only at h
  rw [runT_bind', RunsTo.runT_eq h3 c2, Option.bind_some] at h
  dsimp only at h
  rw [runT_bind', runT_require] at h
  split at h
  · assumption
  · simp at h

/-! ## The honest data -/

/-- **`verify_tables`' honest data.** -/
structure VtHonest where
  /-- The guest's bytecode. -/
  bc : List K
  /-- The memory's log-size. -/
  lm : ℕ
  /-- The public input. -/
  pi : Digest
  /-- The slot weights. -/
  weights : List E
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
  ev : List K → List E → E → VerifierProgram Unit
  /-- The four framework words. -/
  xs4 : List E
  /-- The bytecode share's ten words. -/
  bcW : List E
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
def s1 : Fs := H.s0.absorbAll H.xs4 dsObserve

/-- The share. -/
def share : E := H.bcW.getD 0 0

/-- The bytecode's value. -/
def bv : E := H.bcW.getD 9 0

/-- The slot point. -/
def slots : List E := bcSlots H.s1 H.bcW

/-- The sponge after the share's value. -/
def sB : Fs := bcEnd H.s1 H.bcW

/-- The bus result. -/
noncomputable def busH : BusResult :=
  vtBus H.L H.weights H.beta H.point H.values (H.xs4.take 2) (H.xs4.getD 2 0) (H.xs4.getD 3 0)
    H.share H.slots

/-- The constraints' count. -/
abbrev nC : ℕ := (tables.map Table.nConstraints).sum

/-- The batching challenge. -/
def ξ : E := H.sB.squeeze.1

/-- The table sumcheck's target. -/
noncomputable def target : E := dot ((powers H.ξ (nC + nTrees)).drop nC) H.busH.totals

/-- The capacity the rounds start from. -/
def cap0 : List E := H.sB.squeeze.2.cap

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
  termsPure ((powers H.ξ (nC + nTrees)).take nC) ((powers H.ξ (nC + nTrees)).drop nC)
    H.pts.reverse (List.zip H.rowsT H.evsT) 0 0 []

/-- The public input's claims. -/
noncomputable def pclaims : List ColumnClaim :=
  List.zipWith (fun column value ↦ ⟨column, H.rm ::
    List.replicate ((H.L.placement memory0).variableCount - 1) 0, value⟩)
    [memory0, memory1] (([0, 1] : List (Fin 2)).map fun limb ↦
      multilinearEval [ofK ((digestHalves H.pi).1.limb limb),
        ofK ((digestHalves H.pi).2.limb limb)] [H.rm])

/-- **The specification accepts the honest data.** -/
structure Ok : Prop where
  hrun : RunsTo (tablesSeg H.ev H.L H.pi H.weights H.beta H.point H.values) H.s0
    (H.xs4 ++ H.bcW ++ H.xsR ++ H.evsT.flatten) (H.bus, H.claims) ⟨H.cap', []⟩
  hcar : ∃ sp, H.s0.Carries sp
  hx4 : H.xs4.length = 4
  hbcW : H.bcW.length = 10
  hxR : H.xsR.length = 3 * H.n
  hevl : H.evsT.length = H.rowsT.length
  hevw : ∀ p ∈ List.zip H.rowsT H.evsT, p.2.length = p.1.1.width
  hbv : BytecodeAt H.ev H.L.bytecode (H.point.take H.L.logBytecode ++ H.slots) H.bv

end VtHonest

/-! ## The run is the honest one -/

theorem vt_xs4_split {xs4 : List E} (h : xs4.length = 4) :
    xs4 = xs4.take 2 ++ [xs4.getD 2 0, xs4.getD 3 0] := by
  match xs4, h with
  | [a, b, c, d], _ => rfl

/-- **The share's final check holds** on an accepting run. -/
theorem vt_bcReq {H : VtHonest} (h : H.Ok) :
    bcClaim H.s1 H.bcW = dot (eqKernel H.slots) H.weights * H.bv := by
  obtain ⟨hrun, hcar, hx4, hbcW, -, -, -, -⟩ := h
  have hT := RunsTo.runT_eq hrun hcar [] [] []
  have e : H.xs4 ++ H.bcW ++ H.xsR ++ H.evsT.flatten ++ [] = H.xs4.take 2 ++
      ([H.xs4.getD 2 0] ++ ([H.xs4.getD 3 0] ++ (H.bcW ++ (H.xsR ++ H.evsT.flatten)))) := by
    conv_lhs => rw [vt_xs4_split hx4]
    simp
  rw [e] at hT
  have r1 := runsTo_readN H.s0 (H.xs4.take 2)
  rw [show (H.xs4.take 2).length = 2 by simp [hx4]] at r1
  have c1 := RunsTo.carries r1 hcar
  have r2 := runsTo_readE (H.s0.absorbAll (H.xs4.take 2) dsObserve) (H.xs4.getD 2 0)
  have c2 := RunsTo.carries r2 c1
  have r3 := runsTo_readE ((H.s0.absorbAll (H.xs4.take 2) dsObserve).absorb (H.xs4.getD 2 0)
    dsObserve) (H.xs4.getD 3 0)
  have c3 := RunsTo.carries r3 c2
  unfold tablesSeg busRest at hT
  rw [runT_bind', runT_bind', RunsTo.runT_eq r1 hcar, Option.bind_some] at hT
  dsimp only at hT
  rw [runT_bind', RunsTo.runT_eq r2 c1, Option.bind_some] at hT
  dsimp only at hT
  rw [runT_bind', RunsTo.runT_eq r3 c2, Option.bind_some] at hT
  dsimp only at hT
  rw [runT_bind'] at hT
  have es : ((H.s0.absorbAll (H.xs4.take 2) dsObserve).absorb (H.xs4.getD 2 0) dsObserve).absorb
      (H.xs4.getD 3 0) dsObserve = H.s1 := by
    unfold VtHonest.s1
    conv_rhs => rw [vt_xs4_split hx4]
    simp [Fs.absorbAll, List.foldl_append]
  rw [es] at hT c3
  cases hb : runT (bytecodeShare H.weights (H.point.take H.L.logBytecode))
      ⟨H.s1, none, H.bcW ++ (H.xsR ++ H.evsT.flatten), [], []⟩ with
  | none => rw [hb] at hT; simp at hT
  | some r => exact bcShare_inv H.weights _ c3 hbcW hb

/-- **An accepting run is the honest one**: the slot sumcheck's and the table sumcheck's final
checks, the bus result, the claims and the final capacity. -/
theorem vt_spec {H : VtHonest} (h : H.Ok) :
    bcClaim H.s1 H.bcW = dot (eqKernel H.slots) H.weights * H.bv ∧
    H.terms.1 = H.claimN ∧ H.bus = H.busH ∧
      H.claims = H.busH.claims ++ H.terms.2 ++ H.pclaims ∧ H.cap' = H.s3.squeeze.2.cap := by
  have hreq := vt_bcReq h
  obtain ⟨hrun, hcar, hx4, hbcW, hxR, hevl, hevw, hbv⟩ := h
  -- the bus
  have hsh := RunsTo.of_eq (bcShare_run H.weights (H.point.take H.L.logBytecode) H.s1 hbcW hreq)
    (show H.s1 = H.s0.absorbAll (H.xs4.take 2 ++ [H.xs4.getD 2 0, H.xs4.getD 3 0]) dsObserve by
      unfold VtHonest.s1; rw [← vt_xs4_split hx4]) rfl rfl rfl
  have hb := vt_busRest_run H.ev H.L H.weights H.beta H.point H.values (H.xs4.take 2)
    (by simp [hx4]) (H.xs4.getD 2 0) (H.xs4.getD 3 0) H.share H.bv H.slots H.bcW H.s0 H.sB hsh hbv
  obtain ⟨xs2, he, k1⟩ := RunsTo.unbind_at hrun hcar hb
    ⟨H.xsR ++ H.evsT.flatten, by rw [← vt_xs4_split hx4]; simp⟩
  have ex2 : xs2 = H.xsR ++ H.evsT.flatten := by
    rw [← vt_xs4_split hx4] at he; simpa using he.symm
  subst ex2
  have c1 : ∃ sp, TCar H.sB none sp := RunsTo.carries hb hcar
  have k1g := RunsTo.toG k1
  -- the table phase
  obtain ⟨a2, xs3, xs4', t2, g2, he2, r2, k2⟩ := RunsG.unbind k1g c1
  unfold tablePhaseClaims at r2
  dsimp only at r2
  obtain ⟨u0, ys0, ys1, t0, g0, hy0, q0, q1⟩ := RunsG.unbind r2 c1
  obtain ⟨-, et0, eg0, ey0⟩ := RunsG.det q0 (RunsTo.toG (runsTo_grind0
    (bits := grindingBits ((tables.map Table.nConstraints).sum + nTrees - 1)) (by decide) H.sB))
    c1 (r1 := ys1) (r2 := ys0 ++ ys1) (by simp)
  have ey0' : ys0 = [] := by simpa using ey0
  subst et0 eg0 ey0'
  simp only [List.nil_append] at hy0
  subst hy0
  obtain ⟨xi, ys2, ys3, t1, g1, hy1, q2, q3⟩ := RunsG.unbind q1 c1
  obtain ⟨exi, et1, eg1, ey2⟩ := RunsG.det q2 (RunsTo.toG (runsTo_sampleE H.sB)) c1 (r1 := ys3)
    (r2 := ys2 ++ ys3) (by simp)
  have ey2' : ys2 = [] := by simpa using ey2
  subst exi et1 eg1 ey2'
  simp only [List.nil_append] at hy1
  subst hy1
  have c2 : ∃ sp, TCar H.sB.squeeze.2 none sp := RunsTo.carries (runsTo_sampleE H.sB) c1
  obtain ⟨tc, zs1, zs2, t3, g3, hz, w1, w2⟩ := RunsG.unbind q3 c2
  obtain ⟨ea2, et3, eg3, ez2⟩ := RunsG.ret_inv w2 (RunsG.carries w1 c2)
  subst et3 eg3 ez2
  simp only [List.append_nil] at hz
  subst hz
  -- the sumcheck
  unfold tableSumcheckClaims at w1
  dsimp only at w1
  obtain ⟨⟨ch, cl⟩, v1s, v2s, t4, g4, hv, m1, m2⟩ := RunsG.unbind w1 c2
  have hzc := zc_run H.cap0 H.target hxR
  obtain ⟨ech, et4, eg4, ev2⟩ := RunsG.det m1 (RunsTo.toG hzc) c2 (r1 := v2s ++ xs4')
    (r2 := H.evsT.flatten) (by rw [← List.append_assoc, ← hv]; exact he2.symm)
  simp only [Prod.mk.injEq] at ech
  obtain ⟨rfl, rfl⟩ := ech
  subst et4 eg4
  have c3 : ∃ sp, TCar H.s2 none sp := RunsTo.carries hzc c2
  -- the table loop
  obtain ⟨⟨fin, cls⟩, x1, x2, t5, g5, hx, n1, n2⟩ := RunsG.unbind m2 c3
  have hfst : (List.zip H.rowsT H.evsT).map (·.1) = H.rowsT := List.map_fst_zip (by omega)
  have hflat : (List.zip H.rowsT H.evsT).flatMap (·.2) = H.evsT.flatten := by
    rw [vt_flatMap_snd, List.map_snd_zip (by omega)]
  have ht := vt_runsTo_tableTerms ((powers H.ξ (VtHonest.nC + nTrees)).take VtHonest.nC)
    ((powers H.ξ (VtHonest.nC + nTrees)).drop VtHonest.nC) H.pts.reverse (List.zip H.rowsT H.evsT)
    0 0 [] H.s2 hevw
  rw [hfst, hflat] at ht
  obtain ⟨efin, et5, eg5, ex2⟩ := RunsG.det n1 (RunsTo.toG ht) c3 (r1 := x2 ++ xs4') (r2 := [])
    (by rw [← List.append_assoc, ← hx, ev2, List.append_nil])
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp ex2
  subst et5 eg5
  have c4 : ∃ sp, TCar H.s3 none sp := RunsTo.carries ht c3
  obtain ⟨u, y1, y2, t6, g6, hy', o1, o2⟩ := RunsG.unbind n2 c4
  have hreq2 := RunsG.require_inv o1 c4
  obtain ⟨-, et6, eg6, ey1⟩ := RunsG.det o1 (RunsTo.toG (tb_runsTo_require hreq2 H.s3)) c4
    (r1 := y2) (r2 := y1 ++ y2) (by simp)
  have ey1' : y1 = [] := by simpa using ey1
  subst et6 eg6 ey1'
  simp only [List.nil_append] at hy'
  subst hy'
  obtain ⟨erc, et7, eg7, ey7⟩ := RunsG.ret_inv o2 c4
  cases et7; cases eg7; cases ey7
  -- the public input
  obtain ⟨pc, p1s, p2s, t8, g8, hp, o3, o4⟩ := RunsG.unbind k2 c4
  obtain ⟨epc, et8, eg8, ep⟩ := RunsG.det o3 (RunsTo.toG (vt_publicInputPhase_run H.L H.pi H.s3))
    c4 (r1 := p2s) (r2 := p1s ++ p2s) (by simp)
  have ep' : p1s = [] := by simpa using ep
  subst epc et8 eg8 ep'
  obtain ⟨eres, et9, eg9, ep2⟩ := RunsG.ret_inv o4
    (RunsTo.carries (vt_publicInputPhase_run H.L H.pi H.s3) c4)
  simp only [Prod.mk.injEq] at eres
  have ef1 : fin = H.terms.1 := congrArg Prod.fst efin
  have ef2 : cls = H.terms.2 := congrArg Prod.snd efin
  refine ⟨hreq, ef1 ▸ hreq2, eres.1, ?_, ?_⟩
  · rw [eres.2, ea2, erc, ef2]; rfl
  · have := congrArg Fs.cap et9
    exact this

end
end LeanVM.Guest.B1.Tables
