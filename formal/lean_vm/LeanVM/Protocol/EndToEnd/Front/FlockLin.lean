/-
  LeanVM.Protocol.EndToEnd.Front.FlockLin

  The verifier program's Flock lincheck specified from the knowledge soundness of the Flock
  argument's components over the leanISA instance: the batching challenge, the plain rounds and
  the slices checked against the terminal.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.FlockZc

/-!
# The Flock lincheck as a specification

`verifyFlockLincheck zc` (`verifier.py:1152-1176` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) against the Flock argument's lincheck components
(`ToArkLib/Flock/Lincheck.lean`):

| program | component | doom after it | escape per challenge |
| --- | --- | --- | --- |
| `sampleE` (`α`) | `alphaDraw` | `rel linFamily 0` at `v_a + α v_b + α² v_c + α³` | `3/|E|` |
| `sumcheck claim 3 [none × 8]` | `linRounds` | `rel linFamily j` | `2/|E|` |
| `readN 64`, `require (terminal = R)` | `linEnd` | `outRel` at the program's point and slices | |

**The fidelity checks.** The batched claim is `alphaNext`'s exactly; the rounds are ArkLib's plain
rounds (`FlockSumcheck`); the program's point `χ'_in ‖ χ_out` is ArkLib's `linPoint`
(`toVec_linPoint`). The terminal check is ArkLib's `linCheck` provided the program's terminal value
equals `linTerminal` (`TerminalFaithful`), which `FlockTerminal` reduces to the forward walk of the
BLAKE2s circuit.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile CompPoly CMlPolynomialEval
open scoped ENNReal NNReal

@[expose] public section

/-- The program's terminal value of the lincheck (`verifier.py:1169-1174`). -/
def progTerminal (zc : LeanVM.Protocol.Verifier.ZerocheckResult) (alpha : E)
    (roundChallenges s : List E) : E :=
  let skipWeights := LeanVM.Protocol.Verifier.lagrangeWeights LeanVM.Protocol.Verifier.kBits
    zc.zSkip
  let chiIn := zc.chi.take LeanVM.Protocol.Verifier.flockNumLincheckRounds
  let eRow := (LeanVM.Protocol.Verifier.eqKernel chiIn).flatMap fun weight ↦
    skipWeights.map (weight * ·)
  let chiInPrime := roundChallenges.reverse
  let wCol := (LeanVM.Protocol.Verifier.eqKernel chiInPrime).flatMap fun weight ↦
    s.map (· * weight)
  LeanVM.Protocol.Verifier.blake2sBilinear alpha eRow wCol +
    alpha ^ 2 * LeanVM.Protocol.Verifier.eqEval chiIn chiInPrime *
      LeanVM.Protocol.Verifier.dot skipWeights s +
    alpha ^ 3 * wCol.getD LeanVM.Protocol.Verifier.blake2sConstantColumn 0

/-- The lincheck after its rounds: the slices, the terminal check, the point. -/
def linTail (zc : LeanVM.Protocol.Verifier.ZerocheckResult) (alpha : E) :
    List E × E → Prog (List E × List E)
  | (roundChallenges, rLc) => do
    let s ← Prog.readN LeanVM.Protocol.Verifier.kBits
    Prog.require (progTerminal zc alpha roundChallenges s = rLc)
    return (roundChallenges.reverse ++
      zc.chi.drop LeanVM.Protocol.Verifier.flockNumLincheckRounds, s)

/-- The lincheck is `α`, the rounds, then the tail. -/
theorem verifyFlockLincheck_eq (zc : LeanVM.Protocol.Verifier.ZerocheckResult) :
    LeanVM.Protocol.Verifier.verifyFlockLincheck .computed zc = Prog.sampleE >>= fun alpha ↦
      LeanVM.Protocol.Verifier.sumcheck (zc.vA + alpha * zc.vB + alpha ^ 2 * zc.vC + alpha ^ 3) 3
        (List.replicate LeanVM.Protocol.Verifier.flockNumLincheckRounds none) >>=
          linTail zc alpha := rfl

section Lin

variable (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes)
  (layout : LeanVM.Protocol.Verifier.Layout) (C : List Ev → Set (Column layout.stackLog))
  (toI : Column layout.stackLog → Column (fI F prog s).μ)
  (claims : List LeanVM.Protocol.Verifier.ColumnClaim) (input : LeanVM.Semantics.PublicInput)

/-- **The terminal's fidelity**: the program's terminal value is ArkLib's `linTerminal` at the
program's skip challenge, `χ_in`, `α`, `χ'_in` and slices. -/
def TerminalFaithful : Prop :=
  ∀ (zc : LeanVM.Protocol.Verifier.ZerocheckResult) (alpha : E) (rc sv : List E),
    zc.chi.length = (fP F prog s).m + (fP F prog s).κ → rc.length = (fP F prog s).m →
      sv.length = 64 →
      progTerminal zc alpha rc sv =
        Flock.linTerminal (fP F prog s).nodes (fC F prog s) (fP F prog s).cpos zc.zSkip
          (lowVec (toVec ((fP F prog s).m + (fP F prog s).κ) zc.chi)) alpha
          (toVec (fP F prog s).m rc).reverse (toVec (2 ^ (fP F prog s).s) sv)

/-- The lincheck's statement of a candidate: the zerocheck's terminal statement at the result. -/
def linStmt (zc : LeanVM.Protocol.Verifier.ZerocheckResult) (q : Column layout.stackLog) :
    Flock.TermStmt ((fI F prog s).Stmt × PubOut (fI F prog s)) E
      ((fP F prog s).m + (fP F prog s).κ) :=
  ((fS F prog s layout toI input q, zcDummy F prog s, zc.zSkip),
    toVec ((fP F prog s).m + (fP F prog s).κ) zc.chi, zc.vA, zc.vB, zc.vC)

/-- Alive during the lincheck's rounds. -/
def LinAlive (zc : LeanVM.Protocol.Verifier.ZerocheckResult) (alpha : E) (j : ℕ)
    (chis : List E) (v : E) (q : Column layout.stackLog) : Prop :=
  SumAlive (Flock.linFamily (fP F prog s) (fC F prog s) (fz F prog s) (fside F prog s))
    (fG layout claims) (fun q ↦ (linStmt F prog s layout toI input zc q, alpha))
    (fO F prog s layout toI) j chis v q

/-- Alive after the lincheck: the slices are the witness tables' extensions at the point. -/
def OutAlive (pt sv : List E) (q : Column layout.stackLog) : Prop :=
  fG layout claims q ∧ (((fS F prog s layout toI input q,
    toVec ((fP F prog s).m + (fP F prog s).κ) pt, toVec (2 ^ (fP F prog s).s) sv),
      fO F prog s layout toI q), ()) ∈
    Flock.outRel (fP F prog s) (fz F prog s) (fside F prog s)

/-- **`α`'s escape** (`alphaDrawSecurity`): a wrong value or constant position makes the batched
claim and the lincheck sum distinct cubics in `α`, which agree at three values at most. -/
theorem alpha_escape (zc : LeanVM.Protocol.Verifier.ZerocheckResult) (q : Column layout.stackLog)
    (hq : ¬ TermAlive F prog s layout toI claims input zc q) :
    avgE (fun α ↦ indE (LinAlive F prog s layout toI claims input zc α 0 []
      (zc.vA + α * zc.vB + α ^ 2 * zc.vC + α ^ 3) q)) ≤ ((overE 3 : ℝ≥0) : ℝ≥0∞) := by
  by_cases hG : fG layout claims q
  · have hin := fun h ↦ hq ⟨hG, h⟩
    have h := sample_escape (Flock.alphaDrawSecurity (fP F prog s) (fC F prog s) (fz F prog s)
      (fside F prog s)) (linStmt F prog s layout toI input zc q) _ hin rfl
    rw [← overF_eq_overE]
    refine (avgE_mono fun α ↦ indE_mono fun hα ↦ ?_).trans h
    have hα' := hα.2
    rw [toVec_zero] at hα'
    exact hα'
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hG h.1).trans ?_
    refine (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans ?_
    exact zero_le

/-- **The program's point is ArkLib's `linPoint`**: the reversed round challenges, then the
zerocheck's batch coordinates. -/
theorem toVec_linPoint {rc chi : List E} {m κ : ℕ} (hrc : rc.length = m)
    (hchi : chi.length = m + κ) :
    toVec (m + κ) (rc.reverse ++ chi.drop m) =
      (toVec m rc).reverse ++ highVec (toVec (m + κ) chi) := by
  apply Vector.ext
  intro i hi
  simp only [toVec, Vector.getElem_ofFn, Vector.getElem_append, Vector.getElem_reverse, highVec]
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa [hrc] using h),
      List.getElem?_reverse (by omega)]
    simp [List.getD_eq_getElem?_getD, hrc]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hrc]; omega)]
    simp [List.getD_eq_getElem?_getD, hrc]

/-- The lincheck's rounds are the within-block coordinates, `8`. -/
theorem numLin_eq : LeanVM.Protocol.Verifier.flockNumLincheckRounds = (fP F prog s).m := by
  rw [show (fP F prog s).m = 8 from rfl]
  decide

/-- **The lincheck's postcondition**: the point has a coordinate per variable, `64` slices, and
no candidate is alive at them. -/
def LinPost (r : List E × List E) (h : List Ev) : Prop :=
  r.1.length = (fP F prog s).m + (fP F prog s).κ ∧ r.2.length = 64 ∧
    Doomed C (OutAlive F prog s layout toI claims input r.1 r.2) h

/-- **The terminal check keeps doom** (`linEndSecurity`): a candidate alive at the program's point
and slices, when the program's terminal value is the running claim, was alive at the end of the
rounds. -/
theorem out_reflect (hterm : TerminalFaithful F prog s)
    (zc : LeanVM.Protocol.Verifier.ZerocheckResult)
    (hz : zc.chi.length = (fP F prog s).m + (fP F prog s).κ) (alpha : E) (rc : List E) (rLc : E)
    (hrc : rc.length = (fP F prog s).m) (sv : List E) (hsv : sv.length = 64)
    (hc : progTerminal zc alpha rc sv = rLc) (q : Column layout.stackLog)
    (hq : ¬ LinAlive F prog s layout toI claims input zc alpha (fP F prog s).m rc rLc q) :
    ¬ OutAlive F prog s layout toI claims input
      (rc.reverse ++ zc.chi.drop LeanVM.Protocol.Verifier.flockNumLincheckRounds) sv q := by
  rintro ⟨hG, hout⟩
  refine hq ⟨hG, sendChecked_reflect (Flock.linEndSecurity (fP F prog s) (fC F prog s)
    (fz F prog s) (fside F prog s)) _ _ (toVec (2 ^ (fP F prog s).s) sv) ?_ ?_⟩
  · unfold Flock.linCheck
    rw [decide_eq_true_eq, ← hc, hterm zc alpha rc sv hz hrc hsv]
    rfl
  · rw [numLin_eq F prog s, toVec_linPoint hrc hz] at hout
    exact hout

open Classical in
/-- The lincheck's tail: the slices, the terminal check, the point. -/
noncomputable def linTailSpec (hst : Stable C) (hterm : TerminalFaithful F prog s)
    {εmax T : ℝ≥0∞} (hT : T ≤ εmax) (zc : LeanVM.Protocol.Verifier.ZerocheckResult)
    (hz : zc.chi.length = (fP F prog s).m + (fP F prog s).κ) (alpha : E) (x : List E × E) :
    Spec (linTail zc alpha x)
      (fun h ↦ x.1.length = (fP F prog s).m ∧
        Doomed C (LinAlive F prog s layout toI claims input zc alpha (fP F prog s).m x.1 x.2) h)
      (LinPost F prog s layout C toI claims input) εmax 0 T :=
  match x with
  | (rc, rLc) =>
    if hrc : rc.length = (fP F prog s).m then
      ((doomReadN hst _ hT 63).mono (fun _ (h : rc.length = _ ∧ _) ↦ h.2) (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl).bind' fun sv ↦
        if hsv : sv.length = 64 then
          (Spec.require (Post := fun _ h ↦ Doomed C (OutAlive F prog s layout toI claims input
              (rc.reverse ++ zc.chi.drop LeanVM.Protocol.Verifier.flockNumLincheckRounds) sv) h)
            fun h₀ hpre hc q hq ho ↦ out_reflect F prog s layout toI claims input hterm zc hz alpha
              rc rLc hrc sv hsv hc q (hpre.2 q hq) ho).bind' fun _ ↦
          (Spec.ret (rc.reverse ++ zc.chi.drop LeanVM.Protocol.Verifier.flockNumLincheckRounds,
            sv)).mono (fun _ hd ↦ ⟨by
              simp only [List.length_append, List.length_reverse, List.length_drop, hrc, hz,
                numLin_eq F prog s]
              omega, hsv, hd⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ h ↦ hsv h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ h ↦ hrc h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

open Classical in
/-- **The lincheck's specification**, from the zerocheck's postcondition to `LinPost`: lead
`L₀·3/|E|` (`α`), each round's group `L₀·2/|E|`, the follower's allowance `T` after the slices. -/
noncomputable def linSpec (hst : Stable C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀)
    (hterm : TerminalFaithful F prog s) {εmax T : ℝ≥0∞} (hT : T ≤ εmax)
    (h2 : (L₀ : ℝ≥0∞) * ((overE 2 : ℝ≥0) : ℝ≥0∞) + 0 ≤ εmax)
    (zc : LeanVM.Protocol.Verifier.ZerocheckResult) :
    Spec (LeanVM.Protocol.Verifier.verifyFlockLincheck .computed zc)
      (ZcPost F prog s layout C toI claims input zc) (LinPost F prog s layout C toI claims input)
      εmax ((L₀ : ℝ≥0∞) * ((overE 3 : ℝ≥0) : ℝ≥0∞) + 0) T :=
  if hz : zc.chi.length = (fP F prog s).m + (fP F prog s).κ then
    Spec.congr (verifyFlockLincheck_eq zc).symm <|
      ((doomSample (εmax := εmax) (T := 0) hst hcard
        (TermAlive F prog s layout toI claims input zc)
        (fun α q ↦ LinAlive F prog s layout toI claims input zc α 0 []
          (zc.vA + α * zc.vB + α ^ 2 * zc.vC + α ^ 3) q)
        ((overE 3 : ℝ≥0) : ℝ≥0∞)
        fun q hq ↦ alpha_escape F prog s layout toI claims input zc q hq).mono
          (fun _ h ↦ h.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun alpha ↦
        (sumcheckSpecL (T := 0) hst hcard _
          (Flock.linFamily_honest (fP F prog s) (fC F prog s) (fz F prog s)
            (fside F prog s)).toConsistent
          (Flock.linFamily_sound (fP F prog s) (fC F prog s) (fz F prog s) (fside F prog s))
          (fG layout claims) (fun q ↦ (linStmt F prog s layout toI input zc q, alpha))
          (fO F prog s layout toI) h2 0 [] _ rfl _ (by
            rw [numLin_eq F prog s]
            exact List.ne_nil_of_length_pos (by
              rw [List.length_replicate, show (fP F prog s).m = 8 from rfl]
              norm_num)) (by
            simp [numLin_eq F prog s])
          (fun q k hk ↦ by
            simp only [List.getElem_replicate]
            rfl)).bind' fun x ↦
          (linTailSpec F prog s layout C toI claims input hst hterm hT zc hz alpha x).mono
            (fun _ h ↦ ⟨by simpa [numLin_eq F prog s] using h.1, by
              have e : 0 + (List.replicate LeanVM.Protocol.Verifier.flockNumLincheckRounds
                  (none : Option E)).length = (fP F prog s).m := by simp [numLin_eq F prog s]
              have h2 := h.2
              rw [e, List.nil_append] at h2
              exact h2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ h ↦ hz h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lin

end
end LeanVM.Protocol.EndToEnd.Front
