module

public import NativeRustcVm.Transcript.Update

/-!
# The model's sponge, lane by lane

`SpongeW.duplexInput`'s lanes (`duplexInput_lt`, `duplexInput_ge`) as `duplex_input` writes them:
lane `4 k + c` of the rate the waiting scalar `k`'s limb `c`, a zero lane or its tag, zero past the
queue; the capacity kept.
-/

namespace NativeRustcVm.Transcript

open NativeVm.Model LeanVM.Semantics

public section

/-- A rate lane of `duplexInput`. -/
theorem duplexInput_lt (sp : SpongeW) {i : Nat} (hi : i < 16) :
    sp.duplexInput[i]'(by omega) =
      if h : i / 4 < sp.pending.size then
        if i % 4 = 0 then sp.pending[i / 4].1.c0 else if i % 4 = 1 then sp.pending[i / 4].1.c1
        else if i % 4 = 2 then 0 else sp.pending[i / 4].2
      else 0 := by
  simp only [SpongeW.duplexInput, Vector.getElem_ofFn, hi, ite_true]
  by_cases h : i / 4 < sp.pending.size
  · simp only [h, dite_true]; rw [Array.getElem?_eq_getElem h]
  · simp only [h, dite_false]; rw [Array.getElem?_eq_none (by omega)]

/-- A capacity lane of `duplexInput`. -/
theorem duplexInput_ge (sp : SpongeW) {i : Nat} (hi : 16 ≤ i) (h25 : i < 25) :
    sp.duplexInput[i]'h25 = sp.state[i]'h25 := by
  simp only [SpongeW.duplexInput, Vector.getElem_ofFn, show ¬ i < 16 by omega, ite_false]
  rfl

end

end NativeRustcVm.Transcript
