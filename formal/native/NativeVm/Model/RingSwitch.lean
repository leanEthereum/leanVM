module

public import NativeVm.Model.KeccakGkr
public import Statement.Verifier.RingSwitch

/-!
# Phase 7a: ring switching

Models `ringSwitch` and `ringSwitchClaim` (`Statement/Verifier/RingSwitch.lean`, `Statement/Verifier/Lib.lean`, `ring_switch.rs`),
with `frobenius8`, `ringPsi`, `ringTarget` and `ringCoefficients`.

**Takes** `q_keccak`'s point and its 64 slices from phase 6. **Reads** a grind and the map's 16
challenges, `f` then `g`. **Returns** the target `T` and the ring-switched claim's weight as data,
the point and the 64 Frobenius coefficients `c_k` (`ringSwitch`'s `fun rPrime ↦ ringWeight point
rPrime coefficients`); `ringSwitchClaim` makes the stack claim `⟨.ring p point coefficients, T⟩`,
`p` the placement of `q_keccak`.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- `frobenius_8(value, p)`: `value^(2^(8p))`, by `8p` squarings. -/
def frobenius8 (value : EW) (p : Nat) : EW := EW.sqIter (ringMapWidth * p) value

/-- `ring_psi(value, g)`: `Σ_b g_b v^(2^b)`. -/
def ringPsi (value : EW) (g : Array EW) : EW :=
  (g.foldl (fun (acc : EW × EW) gB ↦ (acc.1 + gB * acc.2, acc.2 * acc.2)) (0, value)).1

/-- `ring_target(s, f, g)`: `Σ_p f_p (Σ_i z_p^i Ψ(s_i))^(2^(8p))`, `p` from `7` down. -/
def ringTarget (s f g : Array EW) : EW :=
  let images := s.map (ringPsi · g)
  ((Array.range ringMapWidth).reverse.foldl (fun (acc : EW × EW) p ↦
    let z := frobenius8 acc.2 1
    (acc.1 + f.getD p 0 * frobenius8 (polyEval images z) p, z)) (0, gen)).1

/-- `ring_coefficients(f, g)`: `c_(8p+b) = f_p · g_b^(2^(8p))`. -/
def ringCoefficients (f g : Array EW) : Array EW :=
  (f.foldl (fun (acc : Array EW × Array EW) fP ↦
    (acc.1 ++ acc.2.map (fP * ·), acc.2.map (frobenius8 · 1))) (#[], g)).1

/-- **Phase 7a** (`ringSwitch`): the target, and the weight's point and coefficients. -/
def ringSwitch (point s : Array EW) : VM (EW × Array EW × Array EW) := do
  grind Whir.batchGrindingBits
  let challenges ← sampleChallenges (2 * ringMapWidth)
  let f := challenges.extract 0 ringMapWidth
  let g := challenges.extract ringMapWidth challenges.size
  let coefficients := ringCoefficients f g
  let target := ringTarget s f g
  pure (target, point, coefficients)

/-- `ringSwitchClaim`: the claim on `q_keccak`'s region of the stack. -/
def ringSwitchClaim (layout : LayoutW) (target : EW) (point coefficients : Array EW) :
    StackClaimW :=
  ⟨.ring (layout.placement qkeccak) point coefficients, target⟩

end NativeVm.Model
