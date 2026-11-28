/-
  LeanVM.Guest.B1.VsC.VsHonAlW

  `verify_sub`'s windows at `alW` from the honest contexts' parts.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonParts
public import LeanVM.Guest.B1.VsC.VsOrcAlW

/-!
# `verify_sub`'s windows at `alW`, from `HonParts`

**`vsHonEx_of_parts`**: `VsHonEx al` from honest choices whose context has `HonParts` (`hon_of_parts`);
**`vsWindows_alW_of_parts`**: `VsWindowsFromCallees alW 17` from them at `alW`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.Memory (alW)

@[expose] public section

/-- **The honest choices' parts at every placement.** -/
def VsHonPartsEx (al : String → Bool) : Prop :=
  ∀ x : VsCtx, x.al = al → x.Ok → ∃ (ec : ℕ → ℕ) (bw : List (List E)) (ex : List (ℕ × E)) (ret : ℕ → (ℕ → E) → E),
    ({ x with ec := ec, bw := bw, ex := ex, ret := ret } : VsCtx).HonParts

/-- **The honest contexts exist** once their parts do. -/
theorem vsHonEx_of_parts {al : String → Bool} (h : VsHonPartsEx al) : VsHonEx al := fun x hal hok => by
  obtain ⟨ec, bw, ex, ret, hp⟩ := h x hal hok
  exact ⟨ec, bw, ex, ret, VsCtx.hon_of_parts _ hp⟩

/-- **`verify_sub`'s windows at `alW`** from the honest contexts' parts. -/
theorem vsWindows_alW_of_parts (h : VsHonPartsEx alW) : VsWindowsFromCallees alW 17 :=
  vsWindows_of_honex (vsHonEx_of_parts h)

end
end LeanVM.Guest.B1.VsC
