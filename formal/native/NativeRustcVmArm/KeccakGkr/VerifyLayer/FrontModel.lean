module

public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Model

/-!
# `verifyKeccakLayer` after each of the front's steps

The layer's run (`run_eq`) as the read of the product followed by `rest1`; `rest1` to `rest6`
what is left after the product, the first grind, the challenge `s`, the equality-mode sumcheck,
the plain one and the three values.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- After the second check: the grind, `β`, the new claim. -/
def rest6 (ch : EW) (pt lp t : Array EW) (s : TState) : Option (KeccakClaimW × TState) :=
  ((grind (grindingBits 2)).run s).bind fun w ↦
    some (newClaim ch pt lp t (sqS w.2).1, (sqS w.2).2)

/-- After the plain sumcheck: the three values and the second check. -/
def rest5 (c : KeccakClaimW) (ch : EW) (pt lp : Array EW) (val : EW) (s : TState) :
    Option (KeccakClaimW × TState) :=
  ((readScalars 3).run s).bind fun v ↦
    if checkB c (sumE (keccakInstanceWeights ch)) lp v.1 val then rest6 ch pt lp v.1 v.2 else none

/-- After the equality-mode sumcheck: the plain one. -/
def rest4 (c : KeccakClaimW) (ch : EW) (pt : Array EW) (val : EW) (s : TState) :
    Option (KeccakClaimW × TState) :=
  ((sumcheckPlain val 4 keccakLocalBits).run s).bind fun u ↦ rest5 c ch pt u.1.1 u.1.2 u.2

/-- After `s`: the equality-mode sumcheck. -/
def rest3 (c : KeccakClaimW) (p : Array EW) (ch : EW) (s : TState) :
    Option (KeccakClaimW × TState) :=
  ((sumcheck (polyEval p ch) 3 (c.point.map some)).run s).bind fun r ↦ rest4 c ch r.1.1 r.1.2 r.2

/-- After the first grind: `s`. -/
def rest2 (c : KeccakClaimW) (p : Array EW) (s : TState) : Option (KeccakClaimW × TState) :=
  rest3 c p (sqS s).1 (sqS s).2

/-- After the product: the first check and the grind. -/
def rest1 (logSteps step : Nat) (c : KeccakClaimW) (p : Array EW) (s : TState) :
    Option (KeccakClaimW × TState) :=
  if checkA logSteps step c p then
    ((grind (grindingBits (productBits - 1))).run s).bind fun q ↦ rest2 c p q.2
  else none

/-- **The layer**: the product, then `rest1`. -/
theorem run_rest (logSteps step : Nat) (c : KeccakClaimW) (s : TState) :
    (verifyKeccakLayer logSteps step c).run s =
      ((readScalars productBits).run s).bind fun p ↦ rest1 logSteps step c p.1 p.2 := by
  rw [run_eq]
  rfl

theorem grindingBits_46 : grindingBits (productBits - 1) = 3 := by decide

theorem grindingBits_2 : grindingBits 2 = 0 := by decide

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
