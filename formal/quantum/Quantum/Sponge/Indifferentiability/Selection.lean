module

public import Quantum.Sponge.Indifferentiability.Paths

@[expose] public section

/-!
# The simulator's frozen tail selection

Section 7 of Alagic, Carolan, Majenz and Tokat (ePrint 2025/731), with the selection made total
and frozen on bad databases. On a query `h(z)` the simulator looks for a tail of `z` of length `1`
to `l` in its databases `D.k`, `D.k'`; if there is one (unique when `D` is good) it answers from
the random oracle at that tail, shifted by its head.

* `sel π l D z`: `some (m, hd m)` if `D` is good and `m` is a tail of `z` with `1 ≤ |m| ≤ l`, else
  `none` (`sel_eq_some_iff`). It ignores `D.h` (`sel_congr`).
* `sel_extends`: a selection survives every good extension; so when `z` has a selected tail the
  selection can only change on extensions that are bad (`not_good_of_sel_ne`).
* Change sets of one cell (`selChangeK`, `selChangeK'`: the values of an unset `k` or `k'` cell
  that change the selection at `z`): empty on bad databases; inside the bad values when a tail is
  selected; at most `(t + 1) t G` (`k`) and `1 + t² G` (`k'`) when none is
  (`card_selChangeK_le_of_sel_eq_none`, `card_selChangeK'_le_of_sel_eq_none`).
-/

namespace Quantum.Sponge

open Finset

variable {X Z : Type} [Zero X] [AddCommGroup Z] (π : Equiv.Perm (X × Z)) (l : ℕ)

/-- **The frozen selection**: the tail of `z` of length `1` to `l` and its head, when `D` is good
and has one; `none` otherwise. -/
noncomputable def sel (D : Dbs X Z) (z : Z) : Option (List X × X) :=
  @dite _ (Good π D ∧ ∃ t, IsTail π D t z ∧ t ≠ [] ∧ t.length ≤ l) (Classical.propDecidable _)
    (fun h ↦ some (h.2.choose, hd π (tab D.k) (tab D.k') h.2.choose)) fun _ ↦ none

variable {π l}

theorem sel_eq_some_iff {D : Dbs X Z} {z : Z} {m : List X} {x : X} :
    sel π l D z = some (m, x) ↔ Good π D ∧ IsTail π D m z ∧ m ≠ [] ∧ m.length ≤ l ∧
      x = hd π (tab D.k) (tab D.k') m := by
  rw [sel]
  split
  · next h =>
    have hc := h.2.choose_spec
    constructor
    · intro he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
      exact ⟨h.1, hc.1, hc.2.1, hc.2.2, rfl⟩
    · rintro ⟨-, hm, -, -, rfl⟩
      rw [h.1.1 z _ _ hc.1 hm]
  · next h =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨hD, hm, hne, hl, -⟩
    exact h ⟨hD, m, hm, hne, hl⟩

theorem sel_eq_none_of_not_good {D : Dbs X Z} (hD : ¬ Good π D) (z : Z) : sel π l D z = none :=
  dite_eq_right (fun h ↦ (hD h.1).elim)

theorem sel_eq_none_iff_of_good {D : Dbs X Z} (hD : Good π D) {z : Z} :
    sel π l D z = none ↔ ∀ t, IsTail π D t z → t ≠ [] → l < t.length := by
  rw [Option.eq_none_iff_forall_ne_some]
  constructor
  · intro h t ht hne
    by_contra hl
    exact h (t, _) (sel_eq_some_iff.2 ⟨hD, ht, hne, Nat.le_of_not_lt hl, rfl⟩)
  · rintro h ⟨m, x⟩ hs
    obtain ⟨-, hm, hne, hl, -⟩ := sel_eq_some_iff.1 hs
    exact absurd (h m hm hne) (Nat.not_lt.2 hl)

/-- The selection only reads `D.k` and `D.k'`. -/
theorem sel_congr {D D' : Dbs X Z} (hk : D.k = D'.k) (hk' : D.k' = D'.k') (z : Z) :
    sel π l D z = sel π l D' z := by
  have hE : Extends D D' := ⟨fun x a h ↦ hk ▸ h, fun x b h ↦ hk' ▸ h⟩
  have hE' : Extends D' D := ⟨fun x a h ↦ hk ▸ h, fun x b h ↦ hk' ▸ h⟩
  refine Option.ext fun ⟨m, x⟩ ↦ ?_
  rw [sel_eq_some_iff, sel_eq_some_iff, hk, hk']
  exact ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1.mono hE, h2.mono hE', h3⟩,
    fun ⟨h1, h2, h3⟩ ↦ ⟨h1.mono hE', h2.mono hE, h3⟩⟩

theorem sel_update_h (D : Dbs X Z) (hdb : Database Z X) (z : Z) :
    sel π l { D with h := hdb } z = sel π l D z :=
  sel_congr (D := { D with h := hdb }) (D' := D) rfl rfl z

/-- **A selection survives every good extension.** -/
theorem sel_extends {D D' : Dbs X Z} (hDD : Extends D' D) (hD' : Good π D') {z : Z}
    {s : List X × X} (hs : sel π l D z = some s) : sel π l D' z = some s := by
  obtain ⟨m, x⟩ := s
  obtain ⟨-, hm, hne, hl, rfl⟩ := sel_eq_some_iff.1 hs
  exact sel_eq_some_iff.2 ⟨hD', hm.mono hDD, hne, hl, (hm.hd_extends π hDD).symm⟩

/-- **Bad-only change when a tail is selected**: an extension that changes a selection is bad. -/
theorem not_good_of_sel_ne {D D' : Dbs X Z} (hDD : Extends D' D) {z : Z} {s : List X × X}
    (hs : sel π l D z = some s) (hne : sel π l D' z ≠ some s) : ¬ Good π D' :=
  fun hD' ↦ hne (sel_extends hDD hD' hs)

theorem sel_extends_eq_none {D D' : Dbs X Z} (hDD : Extends D' D) (hD : ¬ Good π D) (z : Z) :
    sel π l D' z = none :=
  sel_eq_none_of_not_good (fun hD' ↦ hD (hD'.mono hDD)) z

/-- If `D'` has the tails of `D` and `D` selects nothing at `z`, neither does `D'`. -/
theorem sel_eq_none_of_isTail_imp {D D' : Dbs X Z} (hD : Good π D) {z : Z}
    (hz : sel π l D z = none) (htail : ∀ t, IsTail π D' t z → IsTail π D t z) :
    sel π l D' z = none := by
  rw [Option.eq_none_iff_forall_ne_some]
  rintro ⟨m, x⟩ hs
  obtain ⟨-, hm, hne, hl, -⟩ := sel_eq_some_iff.1 hs
  exact absurd ((sel_eq_none_iff_of_good hD).1 hz m (htail m hm) hne) (Nat.not_lt.2 hl)

/-! ## Change sets of one cell -/

section change

variable [DecidableEq X] [Fintype Z]

open Classical in
/-- The values of the `k` cell at `x` that change the selection at `z`. -/
noncomputable def selChangeK (π : Equiv.Perm (X × Z)) (l : ℕ) (D : Dbs X Z) (x : X) (z : Z) :
    Finset Z :=
  univ.filter fun a ↦ sel π l { D with k := Function.update D.k x (some a) } z ≠ sel π l D z

open Classical in
/-- The values of the `k'` cell at `x'` that change the selection at `z`. -/
noncomputable def selChangeK' (π : Equiv.Perm (X × Z)) (l : ℕ) (D : Dbs X Z) (x' : X) (z : Z) :
    Finset Z :=
  univ.filter fun b ↦ sel π l { D with k' := Function.update D.k' x' (some b) } z ≠ sel π l D z

theorem mem_selChangeK {D : Dbs X Z} {x : X} {z a : Z} :
    a ∈ selChangeK π l D x z ↔
      sel π l { D with k := Function.update D.k x (some a) } z ≠ sel π l D z := by
  simp [selChangeK]

theorem mem_selChangeK' {D : Dbs X Z} {x' : X} {z b : Z} :
    b ∈ selChangeK' π l D x' z ↔
      sel π l { D with k' := Function.update D.k' x' (some b) } z ≠ sel π l D z := by
  simp [selChangeK']

theorem selChangeK_eq_empty_of_not_good {D : Dbs X Z} {x : X} (hx : D.k x = none)
    (hD : ¬ Good π D) (z : Z) : selChangeK π l D x z = ∅ :=
  eq_empty_of_forall_notMem fun _ ha ↦ mem_selChangeK.1 ha (by
    rw [sel_extends_eq_none (extends_update_k hx) hD, sel_eq_none_of_not_good hD])

theorem selChangeK'_eq_empty_of_not_good {D : Dbs X Z} {x' : X} (hx' : D.k' x' = none)
    (hD : ¬ Good π D) (z : Z) : selChangeK' π l D x' z = ∅ :=
  eq_empty_of_forall_notMem fun _ hb ↦ mem_selChangeK'.1 hb (by
    rw [sel_extends_eq_none (extends_update_k' hx') hD, sel_eq_none_of_not_good hD])

/-- With a selected tail, the values of a `k` cell that change the selection make `D` bad. -/
theorem not_good_of_mem_selChangeK {D : Dbs X Z} {x : X} {z a : Z} (hx : D.k x = none)
    (hz : sel π l D z ≠ none) (ha : a ∈ selChangeK π l D x z) :
    ¬ Good π { D with k := Function.update D.k x (some a) } := by
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hz
  exact not_good_of_sel_ne (extends_update_k hx) hs (hs ▸ mem_selChangeK.1 ha)

/-- With a selected tail, the values of a `k'` cell that change the selection make `D` bad. -/
theorem not_good_of_mem_selChangeK' {D : Dbs X Z} {x' : X} {z b : Z} (hx' : D.k' x' = none)
    (hz : sel π l D z ≠ none) (hb : b ∈ selChangeK' π l D x' z) :
    ¬ Good π { D with k' := Function.update D.k' x' (some b) } := by
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hz
  exact not_good_of_sel_ne (extends_update_k' hx') hs (hs ▸ mem_selChangeK'.1 hb)

variable [Fintype X] [DecidableEq Z]

theorem card_selChangeK_le_of_sel_ne_none {D : Dbs X Z} {x : X} {z : Z} {t G : ℕ}
    (hD : Good π D) (hG : PermGood π G) (hx : D.k x = none) (hk : D.k.size ≤ t)
    (hk' : D.k'.size ≤ t) (hz : sel π l D z ≠ none) :
    #(selChangeK π l D x z) ≤ (t + 1) * ((t + 1) * t + 2 * t) * G := by
  classical
  refine (card_le_card fun a ha ↦ ?_).trans (card_bad_k_le (x := x) hD hG hx hk hk')
  exact mem_filter.2 ⟨mem_univ _, not_good_of_mem_selChangeK hx hz ha⟩

theorem card_selChangeK'_le_of_sel_ne_none {D : Dbs X Z} {x' : X} {z : Z} {t G : ℕ}
    (hD : Good π D) (hG : PermGood π G) (hx' : D.k' x' = none) (hk : D.k.size ≤ t)
    (hk' : D.k'.size ≤ t) (hz : sel π l D z ≠ none) :
    #(selChangeK' π l D x' z) ≤ (t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G := by
  classical
  refine (card_le_card fun b hb ↦ ?_).trans (card_bad_k'_le (x' := x') hD hG hx' hk hk')
  exact mem_filter.2 ⟨mem_univ _, not_good_of_mem_selChangeK' hx' hz hb⟩

/-- **No selected tail, `k` cell**: a new tail needs a new intermediate pair `π (x, z0 + a)` from
a tailed capacity `z0` with its rate in `D.k'`; at most `(t + 1) t G` values. -/
theorem card_selChangeK_le_of_sel_eq_none {D : Dbs X Z} {x : X} {z : Z} {t G : ℕ}
    (hD : Good π D) (hG : PermGood π G) (hx : D.k x = none) (hk' : D.k'.size ≤ t)
    (hz : sel π l D z = none) :
    #(selChangeK π l D x z) ≤ (t + 1) * t * G := by
  have hT : #(tailFinset π D) ≤ t + 1 := (card_hasTail_le hD).trans (by omega)
  have hK' : #(univ.filter fun xi ↦ (D.k' xi).isSome) ≤ t := hk'
  calc #(selChangeK π l D x z)
      ≤ #((tailFinset π D).biUnion fun z0 ↦ (univ.filter fun xi ↦ (D.k' xi).isSome).biUnion
          fun xi ↦ univ.filter fun a ↦ (π (x, z0 + a)).1 = xi) := by
        refine card_le_card fun a ha ↦ ?_
        by_contra hno
        refine mem_selChangeK.1 ha ((sel_eq_none_of_isTail_imp hD hz fun t ht ↦
          (update_k_tail hx (fun z0 hz0 ↦ ?_) t z).1 ht).trans hz.symm)
        by_contra hne
        exact hno (mem_biUnion.2 ⟨z0, mem_tailFinset.2 hz0, mem_biUnion.2 ⟨_,
          mem_filter.2 ⟨mem_univ _, Option.isSome_iff_ne_none.2 hne⟩,
          mem_filter.2 ⟨mem_univ _, rfl⟩⟩⟩)
    _ ≤ #(tailFinset π D) * (t * G) := by
        refine card_biUnion_le_card_mul _ _ _ fun z0 _ ↦ ?_
        exact (card_biUnion_le_card_mul _ _ G fun xi _ ↦
          (card_rate_shift π x xi z0).trans_le (hG.rate x xi)).trans
            (Nat.mul_le_mul_right _ hK')
    _ ≤ (t + 1) * t * G := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ hT

/-- **No selected tail, `k'` cell**: a new tail needs the intermediate pair `(x', zi)`; it reaches
`z` directly for one value, or through a new intermediate pair `π (xp, zi + D.k xp + b)` with its
rate in `D.k'` or at `x'`; at most `1 + t² G` values when the updated `D.k'` has at most `t`
points. -/
theorem card_selChangeK'_le_of_sel_eq_none {D : Dbs X Z} {x' : X} {z : Z} {t G : ℕ}
    (hD : Good π D) (hG : PermGood π G) (hx' : D.k' x' = none) (hk : D.k.size ≤ t)
    (hk' : D.k'.size + 1 ≤ t) (hz : sel π l D z = none) :
    #(selChangeK' π l D x' z) ≤ 1 + t * t * G := by
  by_cases hip : ∃ zi, (x', zi) ∈ IP π D
  · obtain ⟨zi, xp0, zp0, a0, ⟨t0, ht0⟩, hk0, hπ0⟩ := hip
    have hK : #(univ.filter fun xp ↦ (D.k xp).isSome) ≤ t := hk
    have hK' : #(insert x' (univ.filter fun xi ↦ (D.k' xi).isSome)) ≤ t :=
      (card_insert_le _ _).trans hk'
    calc #(selChangeK' π l D x' z)
        ≤ #((univ.filter fun b ↦ zi + b = z) ∪
            (univ.filter fun xp ↦ (D.k xp).isSome).biUnion fun xp ↦
              (insert x' (univ.filter fun xi ↦ (D.k' xi).isSome)).biUnion fun xi ↦
                univ.filter fun b ↦ (π (xp, zi + (D.k xp).getD 0 + b)).1 = xi) := by
          refine card_le_card fun b hb ↦ ?_
          by_contra hno
          have hmem : ∀ xp a, D.k xp = some a → ∀ xi ∈ insert x' (univ.filter fun xi ↦
              (D.k' xi).isSome), (π (xp, zi + a + b)).1 ≠ xi := fun xp a hka xi hxi h ↦
            hno (mem_union_right _ (mem_biUnion.2 ⟨xp, mem_filter.2 ⟨mem_univ _, by simp [hka]⟩,
              mem_biUnion.2 ⟨xi, hxi, mem_filter.2 ⟨mem_univ _, by simpa [hka] using h⟩⟩⟩))
          have hk'0 : ∀ xp a, D.k xp = some a → D.k' (π (xp, zi + a + b)).1 = none :=
            fun xp a hka ↦ by
              by_contra hne
              exact hmem xp a hka _ (mem_insert_of_mem (mem_filter.2 ⟨mem_univ _,
                Option.isSome_iff_ne_none.2 hne⟩)) rfl
          have hzb : zi + b ≠ z := fun h ↦ hno (mem_union_left _ (mem_filter.2 ⟨mem_univ _, h⟩))
          have htails := update_k'_tail hD hx' ht0 hk0 hπ0 hk'0
            fun xp a hka ↦ hmem xp a hka x' (mem_insert_self _ _)
          refine mem_selChangeK'.1 hb ((sel_eq_none_of_isTail_imp hD hz fun t ht ↦ ?_).trans
            hz.symm)
          rcases (htails t z).1 ht with ht | ⟨-, rfl⟩
          · exact ht
          · exact (hzb rfl).elim
      _ ≤ 1 + t * (t * G) := by
          refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
          · rw [card_filter_add_left zi (· = z), filter_eq' univ z]
            simp
          · refine (card_biUnion_le_card_mul _ _ (t * G) fun xp _ ↦ ?_).trans
              (Nat.mul_le_mul_right _ hK)
            exact (card_biUnion_le_card_mul _ _ G fun xi _ ↦
              (card_rate_shift π xp xi _).trans_le (hG.rate xp xi)).trans
                (Nat.mul_le_mul_right _ hK')
      _ = 1 + t * t * G := by rw [Nat.mul_assoc]
  · have h' : ∀ zi, (x', zi) ∉ IP π D := fun zi hzi ↦ hip ⟨zi, hzi⟩
    rw [eq_empty_of_forall_notMem (s := selChangeK' π l D x' z) fun b hb ↦ ?_, card_empty]
    · exact Nat.zero_le _
    exact absurd ((sel_eq_none_of_isTail_imp hD hz fun t ht ↦
      (update_k'_tail_of_forall hx' h' t z).1 ht).trans hz.symm) (mem_selChangeK'.1 hb)

end change

end Quantum.Sponge

end
