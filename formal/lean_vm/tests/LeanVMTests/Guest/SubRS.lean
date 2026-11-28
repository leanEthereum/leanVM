import LeanVM.Guest.EndExecCoreResA

/-!
# The `subRS` family, pinned

A run of symbolic bounds inside a run of constant bounds, its exponent bounds the certificate's own facts
(`CoreMode.subRS`, `subRS_sound`), and a certificate's residuals of families sound with it (`resOk_sound`,
`resOk_instA`), on Lean's three axioms. The sample is `keccak_layer`'s tail run at `verify_keccak`'s first step in
small: `[c·v^32·w^2]·g^49·g^(2·[0, e(w)))` inside the stream `[c]·[0, 8192)`, from `e(v) < 2`, `e(w) < 16`.
-/

namespace LeanVMTests.Guest.SubRS

open LeanVM.Guest.CoreMode

/-- The sample's facts and run: `e(29) < 2`, `e(48) < 16`. -/
def L : List CRes := [.lt (.val 29) (.num 2), .lt (.val 48) (.num 16)]

def q : CRun := ⟨⟨[(5, 1), (29, 32), (48, 2)], 49⟩, 2, .num 0, .val 48⟩

def r : CRun := ⟨⟨[(5, 1)], 0⟩, 1, .num 0, .num 8192⟩

/-- `49 + 32·1 + 2·15 + 2·(15 - 1) = 139 < 8192`. -/
example : subRS L (.subR q r) = true := by decide +kernel

/-- Under conditions, its unconditional facts. -/
example : subRS L (.under [.nonzero 3] (.subR q r)) = true := by decide +kernel

/-- Not inside a stream of `139` words. -/
example : subRS L (.subR q ⟨⟨[(5, 1)], 0⟩, 1, .num 0, .num 139⟩) = false := by decide +kernel

/-- Not without the fact on `48`. -/
example : subRS [.lt (.val 29) (.num 2)] (.subR q r) = false := by decide +kernel

/-- Where the facts hold, the run is inside the stream. -/
example (σ : LeanVM.Guest.Core.Val) (h : ∀ y ∈ L, subRS L y = false → y.Holds σ) : (CRes.subR q r).Holds σ :=
  subRS_sound h _ (by decide +kernel)

end LeanVMTests.Guest.SubRS

/-- info: 'LeanVM.Guest.CoreMode.subRS_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.subRS_sound

/-- info: 'LeanVM.Guest.CoreMode.resOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.resOk_sound

/-- info: 'LeanVM.Guest.EndExec.resOk_instA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.resOk_instA

/-- info: 'LeanVM.Guest.EndExec.resOk_instGA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.resOk_instGA
