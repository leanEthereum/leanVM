/-
  LeanVM.Protocol.EndToEnd.Front.FlockBridge

  The front bridge from the public input to ring switching, assembled: the public-input phase,
  Flock and ring switching of the deployed verifier program as specifications, from the ArkLib
  securities of the leanISA instance, with the fidelity of every computation proved but the
  forward walk of the BLAKE2s circuit, and with what they need of the layout named.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.FlockTerminal

/-!
# The front bridge: public input, Flock, ring switching

Steps 5-7 of `verify_execution` (`verifier.py:1390-1406` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`), as specifications of the calculus of verifier
programs (`LeanVM.Protocol.Compile.Spec`):

* `pubPhaseSpec` (`PubPhase`): `publicInputPhase`, `PubPre → PubPost`, lead `L₀/|E|` plus
  Flock's, since the phase makes no prover move;
* `flockBridgeSpec`: `verifyFlock (14 + τ_BLAKE2S)`, `FlockPre → LinPost`, lead
  `(τ_BLAKE2S + 1)·L₀/|E|`; `PubPost` is `FlockPre` at the claims with the public claims appended
  (`pubPost_iff_flockPre`);
* `ringBridgeSpec`: `ringSwitch point s`, `LinPost (point, s) → RingPost`, lead
  `6·L₀/|E| + T`, the follower's (the opening's) allowance;
* `isMultilinearFn_ringSwitchClaim` (`RingMultilinear`): the ring claim's weight is multilinear.

`RingPost` is the opening bridge's starting point: no candidate satisfies the column claims and
the ring claim `ringSwitchClaim layout ringTarget ringWeight`.

**Per-group escape bounds** (each `L₀ ×` the ArkLib component's proved per-challenge error, for at
most `L₀` candidates), which feed `εmax`:

| group (starts after) | challenges | bound |
| --- | --- | --- |
| the table phase's last move | `r`, then the point's `k + 1` coordinates | `(k + 2) · L₀/|E|` |
| the skip message | `z_skip` | `L₀ · 127/|E|` |
| a zerocheck round's message | its challenge | `L₀ · 2/|E|` |
| `v_b` | `α` | `L₀ · 3/|E|` |
| a lincheck round's message | its challenge | `L₀ · 2/|E|` |
| the slices | ring switching's 6 coefficients, then the opening's | `6 · L₀/|E| + T` |

**Hypotheses.** On the layout (bridge A): `pubLayoutHyp` (the memory claims at the public point
read the instance's memory columns), `ringLayoutHyp` (the `QFLOCK` placement's weight reads the
region at the instance's lift), `tableLogHeights[BLAKE2S] = τ_BLAKE2S`, and the candidates' reading
`toI` and stability `Stable C`. On the program: `WalkFaithful` (the forward walk of the BLAKE2s
circuit computes the R1CS's products), the one computation whose fidelity is not proved here; the
repository's digest test of the circuit's rows against the Python
(`tests/LeanVMTests/Protocol/Blake2sCircuit.lean`) is its test evidence.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile
open scoped ENNReal NNReal

@[expose] public section

section Bridge

variable (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes)
  (layout : LeanVM.Protocol.Verifier.Layout) (C : List Ev → Set (Column layout.stackLog))
  (toI : Column layout.stackLog → Column (fI F prog s).μ)
  (claims : List LeanVM.Protocol.Verifier.ColumnClaim) (input : LeanVM.Semantics.PublicInput)

/-- The public-input phase's postcondition is the Flock phase's precondition at the claims with
the public claims appended. -/
theorem pubPost_iff_flockPre (publicClaims : List LeanVM.Protocol.Verifier.ColumnClaim)
    (h : List Ev) :
    PubPost F prog s layout C toI claims publicClaims h ↔
      FlockPre F prog s layout C toI (claims ++ publicClaims) h := Iff.rfl

/-- **The Flock phase's specification** at the program's size `14 + τ_BLAKE2S`, from the walk's
fidelity. -/
noncomputable def flockBridgeSpec (hwalk : WalkFaithful F)
    (hk : layout.tableLogHeights.getD LeanVM.Protocol.Verifier.opBlake2s 0 = s.τ 5)
    (hst : Stable C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀) {εmax T : ℝ≥0∞} (hT : T ≤ εmax)
    (h127 : (L₀ : ℝ≥0∞) * ((overE 127 : ℝ≥0) : ℝ≥0∞) + 0 ≤ εmax)
    (h2 : (L₀ : ℝ≥0∞) * ((overE 2 : ℝ≥0) : ℝ≥0∞) + 0 ≤ εmax)
    (h3 : (L₀ : ℝ≥0∞) * ((overE 3 : ℝ≥0) : ℝ≥0∞) + 0 ≤ εmax) :
    Spec (LeanVM.Protocol.Verifier.verifyFlock .computed (LeanVM.Protocol.Verifier.blake2sR1csLogSize +
        layout.tableLogHeights.getD LeanVM.Protocol.Verifier.opBlake2s 0))
      (FlockPre F prog s layout C toI claims) (LinPost F prog s layout C toI claims input) εmax
      ((∑ _i ∈ Finset.range (LeanVM.Protocol.Verifier.blake2sR1csLogSize +
          layout.tableLogHeights.getD LeanVM.Protocol.Verifier.opBlake2s 0 -
          LeanVM.Protocol.Verifier.flockKSkip -
          LeanVM.Protocol.Verifier.fixedChallenges.length),
        (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + 0) T :=
  verifyFlockSpec F prog s layout C toI claims input hst hcard (terminalFaithful F prog s hwalk) hT
    h127 h2 h3 _ (flock_logN F prog s layout hk)

/-- **Ring switching's specification**, from the layout's reading of the Flock region. -/
noncomputable def ringBridgeSpec (hlay : ringLayoutHyp F prog s layout toI) (hst : Stable C)
    {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀) {εmax T : ℝ≥0∞} (pt sv : List E) :
    Spec (LeanVM.Protocol.Verifier.ringSwitch pt sv)
      (LinPost F prog s layout C toI claims input (pt, sv)) (RingPost layout C claims) εmax
      ((∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + T) T :=
  ringSpec F prog s layout C toI claims input hst hcard
    (ringFaithful F prog s layout toI hlay) pt sv

end Bridge

end
end LeanVM.Protocol.EndToEnd.Front
