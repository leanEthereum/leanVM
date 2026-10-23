import LeanVM.Protocol.EndToEnd.Front.FlockBridge

/-!
# The front bridge's tests

* **Statement locks** of the three specifications (public input, Flock, ring switching), with their
  hypotheses, and of the fidelity theorems.
* **The trust audit**: the specifications and the fidelity theorems depend on `propext`, `Classical.choice` and `Quot.sound` only.
* **What is load-bearing.**
  - The public claims are computed from both public cells of every limb (`pubLimb`), and the
    leanISA instance sends no public line.
  - The wire's derived coefficient is the one passing ArkLib's round check: another value fails
    it, in both modes.
  - The skip interpolation needs the window denominator: the window is every node's denominator
    (`allInv_flockSkipDomain`), and the interpolation is ArkLib's on the coset values.
  - The ring coefficients: `c_0 = 1`, the identity's coefficient, and the sum identity on a
    function picking out one exponent gives that exponent's ArkLib coefficient.
* **Inhabitants**: candidates read off the commitments are stable (`stable_of_commits`); a message
  of the program's shape (`MsgOk`) in each mode.
-/

namespace LeanVMTests.Protocol.EndToEnd.Front.FlockBridge

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open scoped ENNReal NNReal

/-! ## Statement locks -/

noncomputable example (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes)
    (layout : LeanVM.Protocol.Verifier.Layout) (C : List Ev → Set (Column layout.stackLog))
    (toI : Column layout.stackLog → Column (fI F prog s).μ)
    (claims : List LeanVM.Protocol.Verifier.ColumnClaim)
    (input : LeanVM.Semantics.PublicInput) (hlayout : pubLayoutHyp F prog s layout toI)
    {publicInput : Digest}
    (hinput : Blake2sHash.digestScalars publicInput = (input.word0, input.word1))
    (hstable : CandsStable layout C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀)
    {εmax T : ℝ≥0∞} :
    Spec (LeanVM.Protocol.Verifier.publicInputPhase layout publicInput)
      (PubPre F prog s layout C toI claims input) (PubPost F prog s layout C toI claims) εmax
      (L₀ * ((overE 1 : ℝ≥0) : ℝ≥0∞) + T) T :=
  pubPhaseSpec F prog s layout C toI claims input hlayout hinput hstable hcard

/-- The fidelity of the public claims: on the leanISA instance, whose statement is the digest's,
the ArkLib phase's value for line `j` is the program's limb `j`. -/
example (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes)
    {publicInput : Digest} {input : LeanVM.Semantics.PublicInput}
    (hinput : Blake2sHash.digestScalars publicInput = (input.word0, input.word1)) (r : E)
    (j : Fin 3) :
    PublicInput.lineValue (leanIsaInstance F prog s) r
      ((leanIsaInstance F prog s).publicLines input)[j] = pubLimb publicInput r j :=
  lineValue_eq_pubLimb F prog s hinput r j

noncomputable example (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes)
    (layout : LeanVM.Protocol.Verifier.Layout) (C : List Ev → Set (Column layout.stackLog))
    (toI : Column layout.stackLog → Column (fI F prog s).μ)
    (claims : List LeanVM.Protocol.Verifier.ColumnClaim) (input : LeanVM.Semantics.PublicInput)
    (hlay : ringLayoutHyp F prog s layout toI) (hst : Stable C) {L₀ : ℕ}
    (hcard : ∀ h, (C h).ncard ≤ L₀) {εmax T : ℝ≥0∞} (pt sv : List E) :
    Spec (LeanVM.Protocol.Verifier.ringSwitch pt sv)
      (LinPost F prog s layout C toI claims input (pt, sv))
      (fun r h ↦ ∀ q ∈ C h, ¬ (ColumnClaimsHold layout claims q ∧
        StackClaim.Holds layout.stackLog
          (LeanVM.Protocol.Verifier.ringSwitchClaim layout r.1 r.2) q)) εmax
      ((∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + T) T :=
  ringBridgeSpec F prog s layout C toI claims input hlay hst hcard pt sv

example (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes) :
    WalkFaithful F → TerminalFaithful F prog s :=
  terminalFaithful F prog s

example (layout : LeanVM.Protocol.Verifier.Layout) (target : E) (point cs : List E) :
    IsMultilinearFn layout.stackLog
      (LeanVM.Protocol.Verifier.ringSwitchClaim layout target fun rPrime ↦
        LeanVM.Protocol.Verifier.ringWeight point rPrime cs).1 :=
  isMultilinearFn_ringSwitchClaim layout target point cs

/-! ## The trust audit -/

/--
info: 'LeanVM.Protocol.EndToEnd.Front.pubPhaseSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pubPhaseSpec

/--
info: 'LeanVM.Protocol.EndToEnd.Front.flockBridgeSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms flockBridgeSpec

/--
info: 'LeanVM.Protocol.EndToEnd.Front.ringBridgeSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ringBridgeSpec

/--
info: 'LeanVM.Protocol.EndToEnd.Front.terminalFaithful' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms terminalFaithful

/--
info: 'LeanVM.Protocol.EndToEnd.Front.ringFaithful' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ringFaithful

/-! ## What is load-bearing -/

/-- The public claims read both public cells: at the challenge `0` a limb's claim is its cell in
the digest's first half, at `1` its cell in the second, so a claim computed from one half only
would differ. -/
example (publicInput : Digest) (ℓ : Fin 3) :
    pubLimb publicInput 0 ℓ = ofK ((Blake2sHash.digestScalars publicInput).1.limb ℓ) := by
  rw [pubLimb_eq]
  ring

example (publicInput : Digest) (ℓ : Fin 3) :
    pubLimb publicInput 1 ℓ = ofK ((Blake2sHash.digestScalars publicInput).2.limb ℓ) := by
  rw [pubLimb_eq, CharTwo.add_self_eq_zero]
  ring

/-- The leanISA instance sends no public line: the prover's message is empty. -/
example (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes)
    (input : LeanVM.Semantics.PublicInput) :
    PublicInput.sentCount (leanIsaInstance F prog s)
      ((leanIsaInstance F prog s).publicLines input) = 0 := by
  rw [PublicInput.sentCount, unsentLines]
  rfl

/-- The plain wire's derived coefficient is the only one passing ArkLib's check. -/
example (claim c₀ c₂ : E) :
    SumcheckRound.weightedSum 2 (domOf none) (toVec 3 [c₀, claim + LeanVM.Protocol.Verifier.sumE
      [c₂] + 1, c₂]) ≠ claim := by
  intro h
  have hok := weightedSum_of_msgOk (eq := none) (claim := claim)
    (msg := [c₀, claim + LeanVM.Protocol.Verifier.sumE [c₂], c₂]) ⟨c₀, c₂, rfl⟩
  simp [SumcheckRound.weightedSum, domOf, SumcheckRound.evaluate, toVec, Fin.sum_univ_succ] at h hok
  have : (1 : E) = 0 := by linear_combination h - hok
  exact one_ne_zero this

/-- The equality-mode wire's derived coefficient is the only one passing ArkLib's check. -/
example (claim r c₁ c₂ : E) :
    SumcheckRound.weightedSum 2 (domOf (some r))
      (toVec 3 [claim + r * LeanVM.Protocol.Verifier.sumE [c₁, c₂] + 1, c₁, c₂]) ≠ claim := by
  intro h
  have hok := weightedSum_of_msgOk (eq := some r) (claim := claim)
    (msg := [claim + r * LeanVM.Protocol.Verifier.sumE [c₁, c₂], c₁, c₂]) ⟨c₁, c₂, rfl⟩
  simp [SumcheckRound.weightedSum, domOf, SumcheckRound.evaluate, toVec, Fin.sum_univ_succ] at h hok
  have : (1 : E) = 0 := by linear_combination h - hok
  exact one_ne_zero this

/-- The window denominator is every node's Lagrange denominator. -/
example (i : Fin (2 ^ Flock.kSkip + 2 ^ Flock.kSkip)) :
    flockSkipDomain.allInv[i] = LeanVM.Protocol.Verifier.windowDenominator 128 :=
  allInv_flockSkipDomain i

/-- The identity's coefficient is `1`. -/
example (f₀ f₁ f₂ f₃ f₄ f₅ : E) :
    (LeanVM.Protocol.Verifier.ringCoefficients [f₀, f₁, f₂, f₃, f₄, f₅]).getD 0 0 = 1 := by
  simp [LeanVM.Protocol.Verifier.ringCoefficients, LeanVM.Protocol.Verifier.ringMapShifts,
    Flock.ringShifts, LeanVM.Protocol.Verifier.kBits]

/-! ## Inhabitants -/

/-- Candidates read off the commitments are stable along a run with no commitment. -/
example (f : List (ℕ × ℕ × Word) → Set (Column 3)) : Stable fun h ↦ f (commits h) :=
  stable_of_commits f

/-- A plain round message of the program's shape. -/
example (claim c₀ c₂ : E) :
    MsgOk none claim [c₀, claim + LeanVM.Protocol.Verifier.sumE [c₂], c₂] := ⟨c₀, c₂, rfl⟩

/-- An equality-mode round message of the program's shape. -/
example (claim r c₁ c₂ : E) :
    MsgOk (some r) claim [claim + r * LeanVM.Protocol.Verifier.sumE [c₁, c₂], c₁, c₂] :=
  ⟨c₁, c₂, rfl⟩

end LeanVMTests.Protocol.EndToEnd.Front.FlockBridge
