/-
  LeanVM.Guest.Located.Places

  The decoder's place codes read the guest world's valuation on every value of a function.
-/

module

public import LeanVM.Guest.Located.Replay
public import LeanVM.Guest.Compiled.Cpl.Tables

/-!
# The places agree

`PlacesAgree` (`Located.Replay`) asks that reading a value of a guest function through its row of
the decoder's place codes (`placeWith`, `Cost.Decoder.guestPlaces`) be the guest world's
valuation. The back end's per-function test (`LeanVM.Guest.Compiled.Cpl`) gives it: every value the core function
names is `⟨[], 0, k⟩` with `k` below its row (`Cpl.core_vals`), so `placeVal` reads its code, which
is the valuation by the back end's places (`Cpl.places_val`), the world's (`LeanVM.Guest.Compiled.vf_eq`).

* `placesAgree_of`: from those two statements;
* **`placesAgree`**.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Cost.Decoder

@[expose] public section

/-- `PlacesAgree` from the place codes' valuation (`hval`) and the core values' shape (`hcore`). -/
theorem placesAgree_of
    (hval : ∀ j, 1 ≤ j → j < nFns → ∀ {κ : ℕ} (L : MemoryImage κ) (fp : K) (v : V),
      v.idx < (guestPlaces.getD j #[]).size →
      placeVal L.read fp (guestPlaces.getD j #[]) v = LeanVM.Compiler.valP L fp (LeanVM.Guest.Compiled.gLocs (coreOf j).name) v)
    (hcore : ∀ j, 1 ≤ j → j < nFns → ∀ v ∈ (coreOf j).params ++ Stmt.valsList (coreOf j).body,
      v = ⟨[], 0, v.idx⟩ ∧ v.idx < (guestPlaces.getD j #[]).size) :
    PlacesAgree := by
  intro j h1 h2 κ L fp v hv
  obtain ⟨hvq, hlt⟩ := hcore j h1 h2 v hv
  have h := hval j h1 h2 L fp v hlt
  have hpath : v.path = [] := congrArg V.path hvq
  have htag : v.tag = 0 := congrArg V.tag hvq
  have he : (v.path.isEmpty && v.tag == 0) = true := by simp [hpath, htag]
  simp only [placeVal, he, ↓reduceIte] at h
  rw [h, LeanVM.Guest.Compiled.vf_eq (fns := LeanVM.Guest.Compiled.guestFns) (slots := LeanVM.Guest.Compiled.guestSlots) (L := L)
    (U := LeanVM.Guest.Compiled.Obl.guestU L.read) (coreOf j).name fp]

/-- **The decoder's place codes read the guest world's valuation**, on every value of every
function `1 ≤ j < nFns`. -/
theorem placesAgree : PlacesAgree :=
  placesAgree_of LeanVM.Guest.Compiled.Cpl.places_val LeanVM.Guest.Compiled.Cpl.core_vals

end
end LeanVM.Guest.Located
