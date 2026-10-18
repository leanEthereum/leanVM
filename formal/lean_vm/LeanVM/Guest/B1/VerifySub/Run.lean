/-
  LeanVM.Guest.B1.VerifySub.Run

  The deferring verifier's run, phase by phase, on the deployed hash: what `verify_sub`'s
  soundness assembles.
-/

module

public import LeanVM.Guest.B1.VerifySub.Spec
public import LeanVM.Guest.B1.Basic

/-!
# The deferring verifier, phase by phase

`Runs p s a s'`: `p` runs from the state `s` to `a` and `s'` (`runId`). The phases of
`verifyExecution`, as `verify_sub` runs them:

* `runs_readSizes`: the eight announced words `announce logMem rows rate` pass `readSizes`'s
  checks and give `layoutOf`;
* `runs_commitStack`: the stack's root, at the shape `stackShape`;
* `verifyExecution_split`: `verifyExecution` cut where `verify_sub` hands a phase to a callee;
* `runs_ringSwitch`, `runs_verifyStackedOpening`: the ring switch's challenges and the opening.

`verifyDeferred_true` assembles them: from the phases' runs, the deferring verifier accepts.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Runs -/

/-- `p` runs from `s` to `a` and `s'`. -/
def Runs {α : Type} (p : Prog α) (s : St) (a : α) (s' : St) : Prop := runId p s = some (a, s')

theorem Runs.bind {α β : Type} {p : Prog α} {f : α → Prog β} {s s1 s2 : St} {a : α} {b : β}
    (h1 : Runs p s a s1) (h2 : Runs (f a) s1 b s2) : Runs (p >>= f) s b s2 := by
  unfold Runs at *
  rw [prog_bind_eq, run_bind, h1]
  exact h2

theorem Runs.bind' {α β : Type} {p : Prog α} {f : α → Prog β} {s s1 s2 : St} {a : α} {b : β}
    (h1 : Runs p s a s1) (h2 : Runs (f a) s1 b s2) : Runs (p.bind f) s b s2 := Runs.bind h1 h2

theorem Runs.ret {α : Type} (a : α) (s : St) : Runs (Prog.ret a) s a s := rfl

theorem RunsTo.runs {α : Type} {p : Prog α} {cv cv' : Digest} {xs : List E} {a : α}
    (h : RunsTo p cv xs a cv') (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    Runs p ⟨cv, xs ++ rest, os, roots⟩ a ⟨cv', rest, os, roots⟩ := h rest os roots

theorem RunsWith.runs {α : Type} {p : Prog α} {cv cv' : Digest} {xs : List E} {os : List Opening}
    {roots roots' : List (Digest × ℕ × ℕ)} {a : α} (h : RunsWith p cv xs os roots a cv' roots')
    (rest : List E) (orest : List Opening) :
    Runs p ⟨cv, xs ++ rest, os ++ orest, roots⟩ a ⟨cv', rest, orest, roots'⟩ := h rest orest

theorem require_pos {c : Prop} [Decidable c] (h : c) : Prog.require c = Prog.ret () := by
  simp [Prog.require, h]

/-! ## The announced sizes -/

/-- The eight announced words: the memory's log-size, the six row counts, the rate. -/
def announce (logMem : ℕ) (rows : List ℕ) (rate : ℕ) : List E :=
  eOfNat logMem :: rows.map eOfNat ++ [eOfNat rate]

theorem log2Strict_two_pow_22 : log2Strict (2 ^ 22) = some 22 := by decide

theorem tables_length : tables.length = 6 := rfl

theorem buildLayout_eq {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem : ℕ}
    {rows : List ℕ} (h1 : 16 ≤ logMem) (h2 : logMem ≤ 32) (hl : rows.length = 6)
    (hr : ∀ n ∈ rows, n ≤ 2 ^ 32) :
    buildLayout bytecode logMem rows = some (layoutOf bytecode logMem rows) := by
  have hlog : Nat.log2 bytecode.length = 22 := by rw [hb, Nat.log2_two_pow]
  unfold buildLayout layoutOf
  rw [hlog, hb, log2Strict_two_pow_22]
  simp only
  split
  · rfl
  · rename_i h
    exact absurd ⟨by decide, h1, h2, List.all_eq_true.mpr fun n hn => decide_eq_true (hr n hn),
      by decide, by rw [hl, tables_length]⟩ h

theorem eOfNat_limb1 (n : ℕ) : (eOfNat n).limb 1 = 0 := (eOfNat_isInK n).1

theorem eOfNat_limb2 (n : ℕ) : (eOfNat n).limb 2 = 0 := (eOfNat_isInK n).2

theorem kToNat_eOfNat_limb0 {n : ℕ} (h : n < 2 ^ 64) : kToNat ((eOfNat n).limb 0) = n := by
  simpa [eOfNat, kToNat_ofBits] using h

theorem runs_readSizes {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem rate : ℕ}
    {rows : List ℕ} (hm1 : 16 ≤ logMem) (hm2 : logMem ≤ 32) (hr1 : 1 ≤ rate) (hr2 : rate ≤ 4)
    (hl : rows.length = 6) (hrows : ∀ n ∈ rows, n ≤ 2 ^ 32)
    (hs1 : minStackedLog ≤ (layoutOf bytecode logMem rows).stackLog)
    (hs2 : (layoutOf bytecode logMem rows).stackLog ≤ maxStackedLog) (cv : Digest) (rest : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    Runs (readSizes bytecode) ⟨cv, announce logMem rows rate ++ rest, os, roots⟩
      (layoutOf bytecode logMem rows, rate) ⟨obsAll cv (announce logMem rows rate), rest, os, roots⟩ := by
  have e : 2 + tables.length = (announce logMem rows rate).length := by
    simp [announce, hl, tables_length]
  have hall : ((announce logMem rows rate).all fun value ↦
      decide (value.limb 1 = 0 ∧ value.limb 2 = 0)) = true := by
    simp [announce, eOfNat_limb1, eOfNat_limb2]
  have hlt : ∀ n ∈ rows, n < 2 ^ 64 := fun n hn => lt_of_le_of_lt (hrows n hn) (by decide)
  have hm : kToNat (((announce logMem rows rate).headD 0).limb 0) = logMem := by
    simp only [announce, List.cons_append, List.headD_cons]
    exact kToNat_eOfNat_limb0 (by omega)
  have hrw : (((announce logMem rows rate).drop 1).take tables.length).map
      (fun value ↦ kToNat (value.limb 0)) = rows := by
    simp only [announce, List.cons_append, List.drop_succ_cons, List.drop_zero, tables_length,
      ← hl, List.take_left', List.length_map, List.map_map]
    conv_rhs => rw [← List.map_id rows]
    exact List.map_congr_left fun n hn => kToNat_eOfNat_limb0 (hlt n hn)
  have hrt : kToNat (((announce logMem rows rate).getLastD 0).limb 0) = rate := by
    simp only [announce, List.cons_append, List.getLastD_eq_getLast?, List.getLast?_cons,
      List.getLast?_append, Option.some_or, Option.getD_some]
    exact kToNat_eOfNat_limb0 (by omega)
  unfold readSizes
  rw [e]
  refine Runs.bind (RunsTo.runs (runsTo_readN cv _) rest os roots) ?_
  simp only [Prog.bind_eq, Prog.pure_eq, hall, hm, hrw, hrt, require_pos trivial,
    require_pos (show 1 ≤ rate ∧ rate ≤ 4 from ⟨hr1, hr2⟩), Prog.ret_bind,
    buildLayout_eq hb hm1 hm2 hl hrows, Verifier.liftOption, require_pos (show _ ∧ _ from ⟨hs1, hs2⟩)]
  exact Runs.ret _ _

/-! ## The stack's root -/

/-- The configuration has a first level. -/
def configOk (μ r : ℕ) : Bool :=
  match deriveConfig μ r with
  | some (_ :: _) => true
  | _ => false

theorem configOk_window : ∀ μ < 29, 22 ≤ μ → ∀ r < 5, 1 ≤ r → configOk μ r = true := by
  decide +kernel

theorem runs_commitStack {μ r : ℕ} (hc : configOk μ r = true) {x0 x1 : E} {root : Digest}
    (hroot : (x0, x1) = digestScalars root) (cv : Digest) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    Runs (commitStack μ r) ⟨cv, x0 :: x1 :: rest, os, roots⟩ ()
      ⟨obsAll cv [x0, x1], rest, os, roots ++ [(root, stackShape μ r)]⟩ := by
  unfold configOk at hc
  unfold commitStack stackShape
  split at hc
  · rename_i level levels hcfg
    rw [hcfg]
    simp only [Verifier.liftOption, Prog.bind_eq, Prog.ret_bind]
    show runId (Prog.commit _ _ (Prog.ret ())) _ = _
    simp only [runId, Compile.run, hroot, digestOfScalars_digestScalars]
    rfl
  · exact absurd hc (by simp)

/-! ## The phases -/

theorem verifyExecution_split (ev : Evaluations) (bytecode : List K) (publicInput : Digest) :
    verifyExecution ev bytecode publicInput = (do
      let lr ← readSizes bytecode
      commitStack lr.1.stackLog lr.2
      let alphas ← Prog.sampleN busBits
      let beta ← Prog.sampleE
      let r ← gkrPhase (pushDepth lr.1)
      let bc ← tablesSeg ev lr.1 publicInput alphas beta r.2.1 r.2.2
      let fl ← verifyFlock ev (blake2sR1csLogSize + lr.1.tableLogHeights.getD opBlake2s 0)
      let rs ← ringSwitch fl.1 fl.2
      verifyStackedOpening lr.1.stackLog lr.2
        (ringSwitchClaim lr.1 rs.1 rs.2 :: bc.2.map (·.onStack lr.1))) := by
  simp only [verifyExecution, verifyBusBalance_split, tablesSeg, Prog.bind_eq, Prog.pure_eq,
    Prog.bind_assoc, Prog.ret_bind]

/-- The ring switch's target: `Σ_i g^i Φ(s_i)` (V:2031). -/
def ringTarget (s challenges : List E) : E := polyEval (s.map (phiMap · challenges)) gen

theorem runs_ringSwitch (point s : List E) (cv : Digest) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    Runs (ringSwitch point s) ⟨cv, rest, os, roots⟩
      (ringTarget s (sqAll 6 cv).1,
        fun rPrime ↦ ringWeight point rPrime (ringCoefficients (sqAll 6 cv).1))
      ⟨(sqAll 6 cv).2, rest, os, roots⟩ := by
  unfold ringSwitch
  exact Runs.bind (RunsTo.runs (runsTo_sampleN 6 cv) rest os roots) (Runs.ret _ _)

theorem runs_verifyStackedOpening {μ r : ℕ} {claims : List StackClaim} {cv cv' : Digest}
    {xs : List E} {os : List Opening} {roots roots' : List (Digest × ℕ × ℕ)} {w : WhirEnd}
    (hw : RunsWith (whirOpen μ r (dot (powers (challengeOf (sqCv cv)) claims.length)
      (claims.map (·.2)))) (sqCv cv) xs os roots w cv' roots')
    (hacc : w.Accepts fun point ↦
      dot (powers (challengeOf (sqCv cv)) claims.length) (claims.map fun c ↦ c.1 point))
    (rest : List E) (orest : List Opening) :
    Runs (verifyStackedOpening μ r claims) ⟨cv, xs ++ rest, os ++ orest, roots⟩ ()
      ⟨cv', rest, orest, roots'⟩ := by
  unfold verifyStackedOpening
  simp only [verifyWhir_split, Prog.bind_eq]
  refine Runs.bind (RunsTo.runs (runsTo_sampleE cv) _ _ _) ?_
  refine Runs.bind (RunsWith.runs hw rest orest) ?_
  rw [require_pos hacc]
  exact Runs.ret _ _

theorem bytecodeAt_claimed (c : FixedClaims) (words : List K) :
    BytecodeAt (.claimed c) words c.bytecodePoint c.bytecodeValue := fun _ => by
  simp only [Evaluations.claimed, Prog.bind_eq, Prog.pure_eq]
  rfl

theorem matricesAt_claimed (c : FixedClaims) :
    MatricesAt (.claimed c) c.alpha c.zSkip c.rowPoint c.columnPoint c.slices c.matrixValue :=
  fun _ => by
    simp only [Evaluations.claimed, Prog.bind_eq, Prog.pure_eq]
    rfl

/-! ## The deferring verifier accepts -/

/-- **The deferring verifier accepts** the proof made of the phases' words and openings, when
every phase runs, from the seed's chain state, as `verify_sub` runs them. -/
theorem verifyDeferred_true {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    (seed pi : Digest) (c : FixedClaims) {logMem rate : ℕ} {rows : List ℕ}
    (hm1 : 16 ≤ logMem) (hm2 : logMem ≤ 32) (hr1 : 1 ≤ rate) (hr2 : rate ≤ 4)
    (hl : rows.length = 6) (hrows : ∀ n ∈ rows, n ≤ 2 ^ 32)
    (hs1 : 22 ≤ (layoutOf bytecode logMem rows).stackLog)
    (hs2 : (layoutOf bytecode logMem rows).stackLog ≤ 28)
    {x0 x1 : E} {root : Digest} (hroot : (x0, x1) = digestScalars root)
    {cv10 cvG cvT cvF cvW : Digest} {xsG xsT xsF xsW : List E} {os : List Opening}
    {roots' : List (Digest × ℕ × ℕ)}
    (h10 : cv10 = obsAll (obsAll (blake2sBytes (digestBytes seed ++ digestBytes pi))
      (announce logMem rows rate)) [x0, x1])
    {gr : E × List E × List E}
    (hG : RunsTo (gkrPhase (pushDepth (layoutOf bytecode logMem rows)))
      (sqCv (sqAll 4 cv10).2) xsG gr cvG)
    {bus : BusResult} {claims : List ColumnClaim}
    (hT : RunsTo (tablesSeg (.claimed c) (layoutOf bytecode logMem rows) pi (sqAll 4 cv10).1
      (challengeOf (sqCv (sqAll 4 cv10).2)) gr.2.1 gr.2.2) cvG xsT (bus, claims) cvT)
    {fp s : List E}
    (hF : RunsTo (verifyFlock (.claimed c) (blake2sR1csLogSize +
      (layoutOf bytecode logMem rows).tableLogHeights.getD opBlake2s 0)) cvT xsF (fp, s) cvF)
    {w : WhirEnd}
    (hW : RunsWith (whirOpen (layoutOf bytecode logMem rows).stackLog rate
        (dot (powers (challengeOf (sqCv (sqAll 6 cvF).2)) (claims.length + 1))
          (ringTarget s (sqAll 6 cvF).1 :: claims.map (·.value))))
      (sqCv (sqAll 6 cvF).2) xsW os
      [(root, stackShape (layoutOf bytecode logMem rows).stackLog rate)] w cvW roots')
    (hacc : w.Accepts (stackWeight (layoutOf bytecode logMem rows) claims fp
      (ringCoefficients (sqAll 6 cvF).1) (challengeOf (sqCv (sqAll 6 cvF).2)))) :
    verifyDeferred bytecode seed pi c
      ⟨announce logMem rows rate ++ x0 :: x1 :: (xsG ++ (xsT ++ (xsF ++ xsW))), os⟩ = true := by
  have hcfg : configOk (layoutOf bytecode logMem rows).stackLog rate = true :=
    configOk_window _ (by omega) hs1 _ (by omega) hr1
  have hrun : Runs (deferredProgram c bytecode pi)
      ⟨blake2sBytes (digestBytes seed ++ digestBytes pi),
        announce logMem rows rate ++ x0 :: x1 :: (xsG ++ (xsT ++ (xsF ++ xsW))), os, []⟩
      true ⟨cvW, [], [], roots'⟩ := by
    unfold deferredProgram
    rw [verifyExecution_split]
    refine Runs.bind (a := ()) (Runs.bind (runs_readSizes hb hm1 hm2 hr1 hr2 hl hrows
      (by unfold minStackedLog Whir.minLogStack; omega) (by exact hs2) _ _ _ _) ?_) (Runs.ret _ _)
    generalize layoutOf bytecode logMem rows = L at hG hT hF hW hacc hcfg ⊢
    simp only
    refine Runs.bind (runs_commitStack hcfg hroot _ _ _ _) ?_
    rw [← h10]
    refine Runs.bind (RunsTo.runs (runsTo_sampleN 4 cv10) _ _ _) ?_
    refine Runs.bind (RunsTo.runs (runsTo_sampleE _) _ _ _) ?_
    refine Runs.bind (RunsTo.runs hG _ _ _) ?_
    refine Runs.bind (RunsTo.runs hT _ _ _) ?_
    refine Runs.bind (RunsTo.runs hF _ _ _) ?_
    refine Runs.bind (runs_ringSwitch _ _ _ _ _ _) ?_
    have hlen : (ringSwitchClaim L (ringTarget s (sqAll 6 cvF).1)
        (fun rPrime ↦ ringWeight fp rPrime (ringCoefficients (sqAll 6 cvF).1)) ::
          claims.map (·.onStack L)).length = claims.length + 1 := by
      simp
    have hvals : (ringSwitchClaim L (ringTarget s (sqAll 6 cvF).1)
        (fun rPrime ↦ ringWeight fp rPrime (ringCoefficients (sqAll 6 cvF).1)) ::
          claims.map (·.onStack L)).map (·.2) =
        ringTarget s (sqAll 6 cvF).1 :: claims.map (·.value) := by
      simp [ringSwitchClaim, ColumnClaim.onStack, Function.comp_def]
    have key := runs_verifyStackedOpening
      (claims := ringSwitchClaim L (ringTarget s (sqAll 6 cvF).1)
        (fun rPrime ↦ ringWeight fp rPrime (ringCoefficients (sqAll 6 cvF).1)) ::
          claims.map (·.onStack L))
      (by rw [hlen, hvals]; exact hW) (by
        convert hacc using 1
        funext x
        simp only [stackWeight, ringSwitchClaim, List.length_cons, List.map_cons]) [] []
    rw [List.append_nil, List.append_nil] at key
    dsimp only [List.nil_append]
    exact key
  unfold verifyDeferred verifyDeferredWith runProof
  unfold Runs at hrun
  simp only [Id.run, bind, hrun]
  rfl

end
end LeanVM.Guest.B1.VerifySub
