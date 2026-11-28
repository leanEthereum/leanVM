module

public import LeanVM.Guest.CoreNames

/-!
# Names are told apart by their encodings

`encS_injective`: two names with one encoding (`encS`) are equal.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Guest

@[expose] public section

theorem encL_injective : ∀ {a b : List UInt8}, encL a = encL b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp only [encL] at h; omega
  | _ :: _, [], h => by simp only [encL] at h; omega
  | c :: cs, d :: ds, h => by
      simp only [encL] at h
      have := c.toNat_lt; have := d.toNat_lt
      rw [UInt8.toNat_inj.mp (by omega : c.toNat = d.toNat), encL_injective (by omega : encL cs = encL ds)]

/-- **Names are told apart by their encodings.** -/
theorem encS_injective {s t : String} (h : encS s = encS t) : s = t :=
  String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp (encL_injective h)))

end
end LeanVM.Guest.Complete
