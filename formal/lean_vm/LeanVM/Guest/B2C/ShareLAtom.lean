/-
  LeanVM.Guest.B2C.ShareLAtom

  What an atom's operand says of its word, by position: its constant, the value it equals, the
  key it is the output of; and the sorted list of a shared cell's values.
-/

module

public import LeanVM.Guest.B2C.ShareLHome
public import LeanVM.Guest.B2C.ShareBase
public import LeanVM.Guest.CheckSound

/-!
# Atoms by operand, and a cell's list

`constAt_sound`, `eqAt_sound`, `keyAt_sound`: an atom that holds gives its operand `i` the word
its constant, its equal value or its key names. `chain_order`: values each pointing to an
earlier one (by `key`) that points back, every value without one being the head `h`, are in one
list in `key` order; so a value's predecessor bounds every value of smaller key.
-/

namespace LeanVM.Guest.B2C.ShareL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Local
open LeanVM.Guest.Check LeanVM.Guest.Exec

@[expose] public section

/-! ## Constants' words -/

/-- The word of a constant's limbs. -/
def tw (x : ℕ × ℕ) : E := OffsetInstruction.immediateWord x.1 x.2

theorem tw_limbs (x : E) : tw (limbNat x 0, limbNat x 1) = x :=
  (eq_imm_of_limbs rfl rfl).symm

theorem tw_one : tw (1, 0) = 1 := by
  rw [tw, imm_of_ofBits K.ofBits_one, ofK_one]


section Atoms

variable {rd : Reader} {σ : Val}

theorem constAt_sound {a : Core.Atom} {i : ℕ} {y : ℕ × ℕ} {v : V} (h : constAt a i = some y)
    (hv : (atomVals a)[i]? = some v) (ha : a.Holds rd σ) : σ v = tw y := by
  rw [atomVals_eq] at hv
  cases a with
  | const d x =>
    simp only [constAt, Bool.cond_eq_ite, nbeq_iff'] at h
    split_ifs at h with hi
    obtain rfl := Option.some.inj h
    subst hi
    simp only [Core.Atom.vals, List.getElem?_cons_zero, Option.some.injEq] at hv
    subst hv
    rw [tw_limbs]; exact ha
  | assertNe x inv p =>
    simp only [constAt, Bool.cond_eq_ite, nbeq_iff'] at h
    split_ifs at h with hi
    obtain rfl := Option.some.inj h
    subst hi
    simp only [Core.Atom.vals] at hv
    simp at hv
    subst hv
    rw [tw_one]; exact ha.2
  | _ => simp [constAt] at h

theorem eqAt_sound {a : Core.Atom} {i : ℕ} {u v : V} (h : eqAt a i = some u)
    (hv : (atomVals a)[i]? = some v) (ha : a.Holds rd σ) : σ v = σ u := by
  rw [atomVals_eq] at hv
  cases a with
  | copy d s =>
    have ha' : σ d = σ s := ha
    simp only [eqAt, Bool.cond_eq_ite, nbeq_iff'] at h
    split_ifs at h with h0 h1
    · subst h0; obtain rfl := Option.some.inj h
      simp only [Core.Atom.vals, List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv; exact ha'
    · subst h1; obtain rfl := Option.some.inj h
      simp [Core.Atom.vals] at hv; subst hv; exact ha'.symm
  | assertEq x y =>
    have ha' : σ x = σ y := eq_of_add_eq_zero ha
    simp only [eqAt, Bool.cond_eq_ite, nbeq_iff'] at h
    split_ifs at h with h0 h1
    · subst h0; obtain rfl := Option.some.inj h
      simp only [Core.Atom.vals, List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv; exact ha'
    · subst h1; obtain rfl := Option.some.inj h
      simp [Core.Atom.vals] at hv; subst hv; exact ha'.symm
  | _ => simp [eqAt] at h

theorem keyAt_sound {a : Core.Atom} {i op : ℕ} {ins : List V} {v : V} (h : keyAt a i = some (op, ins))
    (hv : (atomVals a)[i]? = some v) (ha : a.Holds rd σ) : KeyHolds rd (σ v) op (ins.map σ) := by
  rw [atomVals_eq] at hv
  cases a with
  | add d x y =>
    have ha' : σ d = σ x + σ y := ha
    simp only [keyAt, Bool.cond_eq_ite, nbeq_iff'] at h
    split_ifs at h with h0 h1 h2 <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    · subst h0; simp only [Core.Atom.vals, List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv
      simp only [keyHolds_add, List.map_cons, List.map_nil]; exact ha'
    · subst h1; simp [Core.Atom.vals] at hv; subst hv
      simp only [keyHolds_add, List.map_cons, List.map_nil]
      rw [ha', add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · subst h2; simp [Core.Atom.vals] at hv; subst hv
      simp only [keyHolds_add, List.map_cons, List.map_nil]
      rw [ha', add_comm (σ x) (σ y), add_assoc, CharTwo.add_self_eq_zero, add_zero]
  | mul d x y =>
    simp only [keyAt, Bool.cond_eq_ite, nbeq_iff'] at h
    split_ifs at h with h0
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    subst h0; simp only [Core.Atom.vals, List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv
    simp only [keyHolds_mul, List.map_cons, List.map_nil]; exact ha
  | load d p off =>
    simp only [keyAt, Bool.cond_eq_ite, nbeq_iff'] at h
    split_ifs at h with h0
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    subst h0; simp only [Core.Atom.vals, List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv
    simp only [keyHolds_load, List.map_cons, List.map_nil]; exact ha
  | keccak ins' outs inOdd outOdd =>
    obtain ⟨-, ⟨oc, hlo⟩, O, hk, hw⟩ := keccak_holds_full ha
    simp only [keyAt, Bool.cond_eq_ite, band, Nat.ble_eq, Nat.blt_eq] at h
    split_ifs at h with h0
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp only [Core.Atom.vals] at hv
    rw [List.getElem?_append_right h0.1] at hv
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    have hj13 : i - ins'.length < 13 := by
      have := hlo ▸ hj; cases oc <;> simp [KeccakOutputCells.cellCount] at this <;> omega
    rw [hw ⟨_, hj13⟩ hj]
    exact keyHolds_keccak (k := ⟨_, hj13⟩) _ hk rfl
  | _ => simp [keyAt] at h

end Atoms

/-! ## A cell's list -/

section Chain

variable {S : ℕ → Prop} {key prev next : ℕ → ℕ} {h : ℕ}

theorem iter_strict {g : ℕ → ℕ} {d : ℕ} (hg : ∀ k < d, key (g k) < key (g (k + 1))) :
    ∀ a b, a < b → b ≤ d → key (g a) < key (g b)
  | a, 0, hab, _ => by omega
  | a, b + 1, hab, hb => by
      have := hg b (by omega)
      by_cases hab' : a = b
      · subst hab'; exact this
      · exact (iter_strict hg a b (by omega) (by omega)).trans this

/-- Every value is a step of the list from the head. -/
theorem chain_pos (hp : ∀ u, S u → prev u = 0 → u = h)
    (hq : ∀ u, S u → prev u ≠ 0 → S (prev u - 1) ∧ key (prev u - 1) < key u ∧ next (prev u - 1) = u) :
    ∀ (n u : ℕ), key u < n → S u → ∃ d, u = next^[d] h ∧ (∀ k ≤ d, S (next^[k] h)) ∧
      (∀ k < d, key (next^[k] h) < key (next^[k + 1] h)) ∧ (d ≠ 0 → prev u ≠ 0 ∧ prev u - 1 = next^[d - 1] h)
  | 0, u, hn, _ => by omega
  | n + 1, u, hn, hu => by
      by_cases h0 : prev u = 0
      · obtain rfl := hp u hu h0
        refine ⟨0, rfl, fun k hk ↦ ?_, fun k hk ↦ by omega, fun h' ↦ absurd rfl h'⟩
        obtain rfl : k = 0 := by omega
        exact hu
      · obtain ⟨hw, hk, hn'⟩ := hq u hu h0
        obtain ⟨d, hd, hS, hkey, -⟩ := chain_pos hp hq n (prev u - 1) (by omega) hw
        refine ⟨d + 1, ?_, fun k hk' ↦ ?_, fun k hk' ↦ ?_, fun _ ↦ ⟨h0, by simpa using hd⟩⟩
        · rw [Function.iterate_succ_apply', ← hd, hn']
        · by_cases hkd : k ≤ d
          · exact hS k hkd
          · obtain rfl : k = d + 1 := by omega
            rw [Function.iterate_succ_apply', ← hd, hn']; exact hu
        · by_cases hkd : k < d
          · exact hkey k hkd
          · obtain rfl : k = d := by omega
            rw [Function.iterate_succ_apply', ← hd, hn']; exact hk

/-- **A cell's list in order**: a value of smaller key than `u` is at most `u`'s predecessor;
values of equal key are equal. -/
theorem chain_order (hp : ∀ u, S u → prev u = 0 → u = h)
    (hq : ∀ u, S u → prev u ≠ 0 → S (prev u - 1) ∧ key (prev u - 1) < key u ∧ next (prev u - 1) = u)
    {u u' : ℕ} (hu : S u) (hu' : S u') :
    (key u' < key u → prev u ≠ 0 ∧ key u' ≤ key (prev u - 1)) ∧ (key u = key u' → u = u') := by
  obtain ⟨d, rfl, hS, hk, hpv⟩ := chain_pos hp hq (key u + 1) u (by omega) hu
  obtain ⟨d', rfl, hS', hk', -⟩ := chain_pos hp hq (key u' + 1) u' (by omega) hu'
  have hcmp : ∀ a b, a < b → (b ≤ d ∨ b ≤ d') → key (next^[a] h) < key (next^[b] h) := by
    intro a b hab hb
    rcases hb with hb | hb
    · exact iter_strict hk a b hab hb
    · exact iter_strict hk' a b hab hb
  refine ⟨fun hlt ↦ ?_, fun heq ↦ ?_⟩
  · have hdd : d' < d := by
      by_contra hc
      rcases Nat.lt_or_eq_of_le (Nat.not_lt.mp hc) with hc | hc
      · exact absurd (hcmp d d' hc (.inr le_rfl)) (by omega)
      · subst hc; omega
    obtain ⟨h1, h2⟩ := hpv (by omega)
    refine ⟨h1, ?_⟩
    rw [h2]
    rcases Nat.lt_or_eq_of_le (Nat.le_sub_one_of_lt hdd) with h3 | h3
    · exact (hcmp d' (d - 1) h3 (.inl (by omega))).le
    · rw [h3]
  · rcases Nat.lt_trichotomy d d' with h1 | rfl | h1
    · exact absurd (hcmp d d' h1 (.inr le_rfl)) (by omega)
    · rfl
    · exact absurd (hcmp d' d h1 (.inl le_rfl)) (by omega)

end Chain

end
end LeanVM.Guest.B2C.ShareL
