/-
  LeanVM.Guest.B1.Sig.WotsCongr

  The codeword template's walks and layout depend on a chain step only through the chains, steps
  and powers it uses.
-/

module

public import LeanVM.Guest.B1.Sig.CodewordComplete

/-!
# The codeword's walks, by the steps they use

`WEq W W' I`: the steps agree on the chains `i < I`, the steps `s < 3` and the powers `j < 10`.
Then the walks of both are the same (`walkT_weq`, `walksT_weq`), and so are their slots, products,
encodings and arm starts (`slotsT_weq`, `prodT_weq`, `encT_weq`, `armStart_weq`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- Two chain steps agreeing on the chains `i < I`, the steps `s < 3` and the powers `j < 10`. -/
structure WEq (W W' : WotsT) (I : Nat) : Prop where
  size : W.size = W'.size
  step : ∀ i < I, ∀ s < 3, W.step i s = W'.step i s
  power : ∀ j < 10, W.power j = W'.power j

variable {W W' : WotsT} {I : Nat}

theorem walkT_weq (h : WEq W W' I) {i : Nat} (hi : i < I) (slot : Nat → Nat) (stride d b : Nat) :
    walkT W i slot stride d b = walkT W' i slot stride d b := by
  unfold walkT
  split
  · rfl
  · congr 1
    exact List.flatMap_congr fun j hj => by
      rw [List.mem_range] at hj
      rw [h.step i hi (d + j) (by omega)]

theorem walksT_weq (h : WEq W W' I) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    ∀ m r b, first + r + m ≤ I →
      walksT W slots first k stride m r b = walksT W' slots first k stride m r b
  | 0, _, _, _ => rfl
  | m + 1, r, b, hm => by
      simp only [walksT]
      rw [walkT_weq h (i := first + r) (by omega), walksT_weq h slots first k stride m (r + 1) _ (by omega)]

theorem slotsT_weq (h : WEq W W' I) : slotsT W = slotsT W' := by
  funext fold b r s
  simp only [slotsT, chainStride, h.size]

theorem prodT_weq (h : WEq W W' I) : prodT W = prodT W' := by
  funext fold n b
  simp only [prodT, chainStride, h.size]

theorem encT_weq (h : WEq W W' I) : encT W = encT W' := by
  funext fold n b
  simp only [encT, chainStride, h.size]

theorem armStart_weq (h : WEq W W' I) : armStart W = armStart W' := by
  funext slots fold k b r
  simp only [armStart, h.size]

end
end LeanVM.Guest.B1.Sig
