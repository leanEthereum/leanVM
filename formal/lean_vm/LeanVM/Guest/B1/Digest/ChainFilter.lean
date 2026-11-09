/-
  LeanVM.Guest.B1.Digest.ChainFilter

  A `KECCAK` chain's check does not see loads: it holds of a block exactly when it holds of the
  block without (some of) its loads.
-/

module

public import LeanVM.Guest.B1.Digest.Lists

/-!
# Chains without loads

`check_filter`: for a filter `q` keeping every atom but loads, `s.check (atoms.filter q) =
s.check atoms`, and `keccakBlocks` is unchanged (`keccakBlocks_filter`). A completeness proof
thus runs `chain_final` on a block without its stores, whose relations it knows first.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Guest.Core

@[expose] public section

/-- A load (or store). -/
def isLoadB : Atom → Bool
  | .load .. => true
  | _ => false

variable {q : Atom → Bool}

theorem any_filter_of (hq : ∀ a, isLoadB a = false → q a = true) {P : Atom → Bool}
    (hP : ∀ a, P a = true → isLoadB a = false) :
    ∀ l : List Atom, (l.filter q).any P = l.any P
  | [] => rfl
  | a :: l => by
    by_cases ha : q a = true
    · simp [ha, any_filter_of hq hP l]
    · have hPa : P a = false := by
        cases h : P a
        · rfl
        · exact absurd (hq a (hP a h)) ha
      simp [ha, hPa, any_filter_of hq hP l]

theorem addOf_filter (hq : ∀ a, isLoadB a = false → q a = true) :
    ∀ (l : List Atom) (x : V), addOf (l.filter q) x = addOf l x
  | [], _ => rfl
  | a :: l, x => by
    by_cases ha : q a = true
    · simp only [List.filter_cons, ha, ite_true, addOf, List.findSome?_cons]
      have := addOf_filter hq l x
      unfold addOf at this
      rw [this]
    · have hl : isLoadB a = true := by
        cases h : isLoadB a
        · exact absurd (hq a h) ha
        · rfl
      cases a <;> simp only [isLoadB, Bool.false_eq_true] at hl
      simp only [List.filter_cons, ha, Bool.false_eq_true, ite_false, addOf, List.findSome?_cons]
      have := addOf_filter hq l x
      unfold addOf at this
      exact this

theorem const_notLoad (x : V) (lo hi : ℕ) : ∀ a, isConstAt x lo hi a = true → isLoadB a = false := by
  intro a h; cases a <;> simp_all [isConstAt, isLoadB]

theorem copy_notLoad (x y : V) : ∀ a, isCopyAt x y a = true → isLoadB a = false := by
  intro a h; cases a <;> simp_all [isCopyAt, isLoadB]

theorem keccak_notLoad (ins outs : List V) (i o : Bool) :
    ∀ a, isKeccakAt ins outs i o a = true → isLoadB a = false := by
  intro a h; cases a <;> simp_all [isKeccakAt, isLoadB]

/-- **A chain's check does not see loads.** -/
theorem check_filter (hq : ∀ a, isLoadB a = false → q a = true) (s : ChainSpec) (l : List Atom) :
    s.check (l.filter q) = s.check l := by
  unfold ChainSpec.check ChainSpec.blockOk ChainSpec.rateAt ChainSpec.capAt rateOk evalP
  simp only [any_filter_of hq (const_notLoad _ _ _), any_filter_of hq (copy_notLoad _ _),
    any_filter_of hq (keccak_notLoad _ _ _ _), addOf_filter hq]

end
end LeanVM.Guest.B1.Digest
