/-
  LeanVM.Guest.B1.KeccakGkr.VkCCK.Steps

  `verify_keccak`'s steps: their cores, and what the kernel checks of them.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCB
public import LeanVM.Guest.B1.KeccakGkr.VkChain

/-!
# The steps' cores

`stepCore s b`: step `s` but its call (`stepT = stepCore ++ stepTailT`). `stepKer`: what the
kernel checks of it (the loads that are not stores, the residual loads' pointers), checked for the
twelve steps two at a time in `VkCCK/K0.lean` … `VkCCK/K5.lean`, so that the checks build in
parallel (a module checks its proofs one after another), and gathered in `VkCCK.lean`
(`step_ker`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val}

/-- Where step `s` starts. -/
def stepB (s : ℕ) : ℕ :=
  [490, 531, 566, 600, 643, 684, 727, 760, 801, 839, 882, 923].getD s 0

/-- The capacity step `s` passes. -/
def stepCap (s : ℕ) : List ℕ :=
  if s = 0 then [181, 182, 183, 184, 185] else (List.range 5).map fun j ↦ stepB s - 6 + j

/-- The cursor step `s ≥ 1` passes. -/
def stepCur (s : ℕ) : ℕ := if s = 0 then 0 else stepB s - 1

/-- The value step `s ≥ 1` reads its claim's pointer from (`cb`: `claims·g^(22 (s - 1))`). -/
def stepCb (s : ℕ) : ℕ := if s ≤ 1 then 203 else stepB (s - 1) - 7

/-- The value step `s ≥ 1` reads the next claim's pointer from (`pn`: `claims·g^(22 s)`). -/
def stepPn (s : ℕ) : ℕ := if s = 0 then 0 else stepB s - 7

/-- Step `s` but its call. -/
def stepCore (s b : ℕ) : List Stmt :=
  [.atom (.load (.n b) (.n 203) (22 * s + 2)), .atom (.mul (.n (b + 1)) (.n b) (.n 17))] ++
  eqfLevel0T (.n (b + 1)) 0 (b + 2) ++ flipsT s (b + 6) ++
  iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 4) (b + 5)

/-- Where step `s`'s call starts. -/
def stepT0 (s b : ℕ) : ℕ := iotaSegEnd s (b + 6 + flipSz s * (iotaUsed s).length)

theorem stepT_split (s b : ℕ) (cap : List ℕ) (cur cb pn : ℕ) :
    stepT s b cap cur cb pn =
      stepCore s b ++ stepTailT s (stepT0 s b) cap cur cb pn (stepT0 s b - 1) := rfl

/-- The pointers the flips load through, and their ranges. -/
def flipPs (s b : ℕ) : List (V × ℕ × ℕ) :=
  if s = 0 then [(.n 276, 30, 31)]
  else (.n 203, 22 * s + 5, 22 * s + 6) :: (List.range (iotaUsed s).length).map fun j ↦
    (.n (b + 6 + 2 * j), 0, 7)

/-- What the kernel checks of step `s`'s core. -/
def stepKer (s b : ℕ) : Prop :=
  noneIn [.load (.n b) (.n 203) (22 * s + 2), .load (.n (b + 2)) (.n (b + 1)) 0] vkSt = true ∧
  (flipsT s (b + 6)).all isAtom = true ∧ canonChk [] (atomsL ([] ++ flipsT s (b + 6))) = true ∧
  (resid (atomsL (flipsT s (b + 6)))).all (ldR (flipPs s b)) = true ∧
  noneIn (resid (atomsL (flipsT s (b + 6)))) vkSt = true ∧
  (iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 4) (b + 5)).all isAtom = true ∧
  canonChk [] (atomsL ([] ++
    iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 4) (b + 5))) = true ∧
  resid (atomsL (iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 4) (b + 5)))
    = []

instance (s b : ℕ) : Decidable (stepKer s b) := by unfold stepKer; infer_instance

end
end LeanVM.Guest.B1.VerifySub
