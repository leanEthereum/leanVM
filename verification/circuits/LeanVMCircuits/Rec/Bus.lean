module

public import LeanVMCircuits.Rec.Tables

@[expose] public section

/-!
The bus's copy argument.

Every slot pulls its key and its limbs and pushes its `next` slot's key and the same limbs. Its keys are distinct,
and `next` cycles through each wire class's slots in order. When the pulls and pushes balance in characteristic two
(each pair pulled as often as pushed, modulo two, which is what the log-derivative sum over `K` gives) every slot of
a class carries the same limbs. That the sums balance is the bus's GKR claim, not proved here.
-/

namespace LeanVMCircuits.Rec

variable {n : ℕ} {V : Type} [DecidableEq V]

/-- The pulls and pushes balance modulo two: each pair of a key and limbs is pulled and pushed equally often, mod 2. -/
def Balanced (key : Fin n → ℕ) (next : Fin n → Fin n) (v : Fin n → V) : Prop :=
  ∀ x : ℕ × V, ((Finset.univ.filter fun s => (key s, v s) = x).card : ZMod 2) =
    ((Finset.univ.filter fun s => (key (next s), v s) = x).card : ZMod 2)

/-- Balanced with distinct keys and a permutation `next`, every slot carries its next slot's limbs. -/
theorem bus_next (key : Fin n → ℕ) (hkey : Function.Injective key) (next : Fin n → Fin n)
    (hnext : Function.Injective next) (v : Fin n → V) (hbal : Balanced key next v) (s : Fin n) :
    v (next s) = v s := by
  have hpush : (Finset.univ.filter fun t => (key (next t), v t) = (key (next s), v s)) = {s} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨h, _⟩
      exact hnext (hkey h)
    · rintro rfl
      exact ⟨rfl, rfl⟩
  have h := hbal (key (next s), v s)
  rw [hpush, Finset.card_singleton] at h
  obtain ⟨t, ht⟩ : (Finset.univ.filter fun t => (key t, v t) = (key (next s), v s)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at h
    exact zero_ne_one h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ht
  rw [← hkey ht.1, ht.2]

/-- `FixedColumns::of`'s link from slot `i`: the next slot of its class in slot order, the class's first after its
last. -/
def classNext (cls : Fin n → ℕ) (i : Fin n) : Fin n :=
  match (Finset.univ.filter fun j => i < j ∧ cls j = cls i).min with
  | some j => j
  | none => (Finset.univ.filter fun j => cls j = cls i).min' ⟨i, by simp⟩

theorem classNext_forward (cls : Fin n → ℕ) (i j : Fin n) (hij : i < j) (hc : cls j = cls i) :
    i < classNext cls i ∧ classNext cls i ≤ j ∧ cls (classNext cls i) = cls i := by
  have hne : (Finset.univ.filter fun j => i < j ∧ cls j = cls i).Nonempty := ⟨j, by simp [hij, hc]⟩
  obtain ⟨k, hk⟩ := Finset.min_of_nonempty hne
  have hmem := Finset.mem_of_min hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  simp only [classNext, hk]
  exact ⟨hmem.1, Finset.min_le_of_eq (by simp [hij, hc]) hk, hmem.2⟩

theorem classNext_cls (cls : Fin n → ℕ) (i : Fin n) : cls (classNext cls i) = cls i := by
  unfold classNext
  split
  · rename_i k hk
    have := Finset.mem_of_min hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.2
  · have := Finset.min'_mem (Finset.univ.filter fun j => cls j = cls i) ⟨i, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this

/-- No slot of `i`'s class comes after it when its link wraps to the class's first slot. -/
theorem classNext_wrap (cls : Fin n → ℕ) (i : Fin n) (h : ¬ i < classNext cls i) :
    ∀ j, cls j = cls i → j ≤ i ∧ classNext cls i ≤ j := by
  intro j hj
  have hlast : ∀ j, cls j = cls i → j ≤ i := by
    intro j hj
    by_contra hlt
    exact h (classNext_forward cls i j (lt_of_not_ge hlt) hj).1
  refine ⟨hlast j hj, ?_⟩
  have hnone : (Finset.univ.filter fun j => i < j ∧ cls j = cls i).min = ⊤ := by
    rw [Finset.min_eq_top, Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact absurd (hlast k hk.2) (not_le_of_gt hk.1)
  unfold classNext
  rw [hnone]
  exact Finset.min'_le _ _ (by simp [hj])

theorem classNext_injective (cls : Fin n → ℕ) : Function.Injective (classNext cls) := by
  intro a b hab
  have hc : cls a = cls b := by
    have h1 := classNext_cls cls a
    rw [hab, classNext_cls cls b] at h1
    exact h1.symm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- `a < b` in one class: `a`'s link is at most `b`, `b`'s is after `b` or wraps to the first, at most `a`.
    have ha := classNext_forward cls a b hlt hc.symm
    by_cases hb : b < classNext cls b
    · exact absurd (hab ▸ ha.2.1) (not_le_of_gt hb)
    · have := (classNext_wrap cls b hb a hc).2
      exact absurd (lt_of_le_of_lt (hab ▸ this) ha.1) (lt_irrefl _)
  · have hb := classNext_forward cls b a hlt hc
    by_cases ha : a < classNext cls a
    · exact absurd (hab ▸ hb.2.1) (not_le_of_gt (hab ▸ ha))
    · have := (classNext_wrap cls a ha b hc.symm).2
      exact absurd (lt_of_le_of_lt this (hab ▸ hb.1)) (lt_irrefl _)

omit [DecidableEq V] in
/-- Limbs carried unchanged to each slot's link are equal across a class. -/
theorem class_eq (cls : Fin n → ℕ) (v : Fin n → V) (h : ∀ s, v (classNext cls s) = v s) (i j : Fin n)
    (hc : cls i = cls j) : v i = v j := by
  suffices ∀ d (i j : Fin n), j.val - i.val = d → i ≤ j → cls j = cls i → v j = v i by
    rcases le_total i j with hij | hji
    · exact (this _ i j rfl hij hc.symm).symm
    · exact this _ j i rfl hji hc
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i j hd hij hcj
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rfl
    · obtain ⟨hk, hkj, hck⟩ := classNext_forward cls i j hlt hcj
      rw [← h i]
      rcases eq_or_lt_of_le hkj with heq | hkj'
      · rw [heq]
      · have h1 : i.val < (classNext cls i).val := hk
        exact ih (j.val - (classNext cls i).val) (by omega) _ j rfl hkj (hcj.trans hck.symm)

/-- `SlotKey`: a slot's index among all tables' slots, then its row below `2^32`. -/
def slotKey (slot row : ℕ) : ℕ := slot * 2 ^ 32 + row

theorem slotKey_injective (a b : ℕ × ℕ) (ha : a.2 < 2 ^ 32) (hb : b.2 < 2 ^ 32)
    (h : slotKey a.1 a.2 = slotKey b.1 b.2) : a = b := by
  unfold slotKey at h
  rw [show (2 : ℕ) ^ 32 = 4294967296 by norm_num] at h ha hb
  exact Prod.ext (by omega) (by omega)

/-- The copy argument: a balanced bus whose links are `FixedColumns::of`'s cycles, its keys distinct, carries equal
limbs in every slot of a class. -/
theorem copy_argument (key : Fin n → ℕ) (hkey : Function.Injective key) (cls : Fin n → ℕ) (v : Fin n → V)
    (hbal : Balanced key (classNext cls) v) (i j : Fin n) (hc : cls i = cls j) : v i = v j :=
  class_eq cls v (bus_next key hkey _ (classNext_injective cls) v hbal) i j hc

end LeanVMCircuits.Rec
