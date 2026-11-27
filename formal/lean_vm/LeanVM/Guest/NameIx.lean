/-
  LeanVM.Guest.NameIx

  Names compared by their codes: the kernel compares two strings byte by byte, two numbers in one
  step.
-/

module

public import LeanVM.Guest.CoreNames

/-!
# Names compared by their codes

A check the kernel evaluates compares names by their codes (`nameEq`): each name encoded as a number
(`encS`, `CoreNames.lean`), the codes compared by `Nat.beq`. The kernel converts a string literal to its
bytes whichever way it is compared, but compares two strings byte by byte at every comparison, and the
guest's names share long prefixes (`column_selector__L0`, …). `encS` is injective, so `nameEq` is
string equality (`nameEq_iff`).
-/

namespace LeanVM.Guest

@[expose] public section

/-- **Two names are equal**, by their codes. -/
def nameEq (a b : String) : Bool := Nat.beq (encS a) (encS b)

end

public section

private theorem encL_inj_aux : ∀ {a b : List UInt8}, encL a = encL b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp only [encL] at h; omega
  | _ :: _, [], h => by simp only [encL] at h; omega
  | c :: cs, d :: ds, h => by
      simp only [encL] at h
      have := c.toNat_lt; have := d.toNat_lt
      rw [UInt8.toNat_inj.mp (by omega : c.toNat = d.toNat), encL_inj_aux (by omega : encL cs = encL ds)]

theorem nameEq_iff {a b : String} : nameEq a b = true ↔ a = b :=
  ⟨fun h ↦ String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp (encL_inj_aux (Nat.eq_of_beq_eq_true h)))),
    fun h ↦ h ▸ Nat.beq_refl _⟩

end

end LeanVM.Guest
