/-
  LeanVM.Guest.NameIx

  Names compared as numbers: the kernel evaluates a string comparison slowly, a comparison of
  numbers in one step.
-/

module

/-!
# Names as numbers

A check the kernel evaluates compares names by their codes (`nameEq`): each name is encoded once
as a number (`encS`, its bytes as digits in base `2^9`), and the codes are compared as numbers.
The kernel converts a string literal to its bytes once per check whichever way it is compared, but
compares two strings byte by byte at every comparison, and the guest's names share long prefixes
(`column_selector__L0`, …). `encS` is injective (`encS_inj`), so `nameEq` is string equality
(`nameEq_iff`).
-/

namespace LeanVM.Guest

@[expose] public section

/-- The bytes of a name as digits in base `2^9`, each shifted by one. -/
def encL : List UInt8 → Nat
  | [] => 0
  | c :: cs => (c.toNat + 1) + 2 ^ 9 * encL cs

/-- The encoding of a name. -/
def encS (s : String) : Nat := encL s.toByteArray.data.toList

/-- **Two names are equal**, by their codes. -/
def nameEq (a b : String) : Bool := Nat.beq (encS a) (encS b)

end

public section

theorem encL_inj : ∀ {a b : List UInt8}, encL a = encL b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp only [encL, Nat.reducePow] at h; omega
  | c :: cs, d :: ds, h => by
    simp only [encL, Nat.reducePow] at h
    have := c.toNat_lt; have := d.toNat_lt
    rw [UInt8.toNat_inj.mp (by omega : c.toNat = d.toNat), encL_inj (by omega : encL cs = encL ds)]

theorem encS_inj {a b : String} (h : encS a = encS b) : a = b := by
  obtain ⟨⟨⟨la⟩⟩, _⟩ := a
  obtain ⟨⟨⟨lb⟩⟩, _⟩ := b
  cases (encL_inj h : la = lb)
  rfl

theorem nameEq_iff {a b : String} : nameEq a b = true ↔ a = b :=
  ⟨fun h ↦ encS_inj (Nat.eq_of_beq_eq_true h), fun h ↦ h ▸ Nat.beq_refl _⟩

end

end LeanVM.Guest
