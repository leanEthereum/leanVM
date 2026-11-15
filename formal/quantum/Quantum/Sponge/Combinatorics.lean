module

public import Quantum.Sponge.Database

@[expose] public section

/-!
# Counting tails, intermediate pairs and bad single updates

Section 5.3 of Alagic, Carolan, Majenz and Tokat (ePrint 2025/731): Lemma 5.12 (a good database
has at most `|D.k'| + 1` capacities with a tail and at most `|D.k| (|D.k'| + 1)` intermediate
pairs), monotonicity of goodness, and the single-update bad events of Lemmas 5.14, 5.16, 5.18.

* `badAttachK π D x`: the values `y` for which setting `D.k x := y` may break goodness, because a
  new intermediate pair `π (x, z + y)` has its rate in `badRates π D` (rates of intermediate pairs
  and points of `D.k'`) or two of them share a rate. Outside it the tails do not change.
* `badCompleteK' π D x'`: the values `y` for which setting `D.k' x' := y` may break goodness.
  If an intermediate pair `(x', zi)` exists, the capacity `zi + y` gets a tail; bad are the `y`
  for which `zi + y` already had one, or a new intermediate pair `π (xp, zi + y + D.k xp)` has its
  rate in `badRates π D` or at `x'`, or two of them share a rate. Outside it exactly one tail is
  added.

The paper's bad events omit collisions among the new intermediate pairs; they are covered here
through the `pair` field of `PermGood`.
-/

namespace Quantum.Sponge

open Quantum Finset

variable {X Z : Type} {π : Equiv.Perm (X × Z)}

/-! ## Monotonicity -/

theorem IsTail.mono [AddCommGroup Z] {D D' : Dbs X Z} (hDD : Extends D D') {t : List X} {z : Z}
    (h : IsTail π D' t z) : IsTail π D t z := by
  induction h with
  | nil => exact .nil
  | snoc _ hk hπ hk' ih => exact .snoc ih (hDD.1 _ _ hk) hπ (hDD.2 _ _ hk')

theorem HasTail.mono [AddCommGroup Z] {D D' : Dbs X Z} (hDD : Extends D D') {z : Z}
    (h : HasTail π D' z) : HasTail π D z :=
  let ⟨t, ht⟩ := h
  ⟨t, ht.mono hDD⟩

theorem IP_mono [AddCommGroup Z] {D D' : Dbs X Z} (hDD : Extends D D') : IP π D' ⊆ IP π D := by
  rintro s ⟨xp, zp, a, hz, hk, rfl⟩
  exact ⟨xp, zp, a, hz.mono hDD, hDD.1 _ _ hk, rfl⟩

/-- A database contained in a good database is good. -/
theorem Good.mono [AddCommGroup Z] {D D' : Dbs X Z} (hDD : Extends D D') (hD : Good π D) :
    Good π D' :=
  ⟨fun z t t' ht ht' ↦ hD.1 z t t' (ht.mono hDD) (ht'.mono hDD),
    fun _ hs _ hs' h ↦ hD.2 _ (IP_mono hDD hs) _ (IP_mono hDD hs') h⟩

/-- Updates of `D.h` never matter for goodness. -/
theorem good_update_h_iff [AddCommGroup Z] {D : Dbs X Z} (hdb : Database Z X) :
    Good π { D with h := hdb } ↔ Good π D :=
  ⟨Good.mono ⟨fun _ _ h ↦ h, fun _ _ h ↦ h⟩, Good.mono ⟨fun _ _ h ↦ h, fun _ _ h ↦ h⟩⟩

/-- A tail is empty, reaching `0`, or ends at `zi + D.k' xi` for an intermediate pair `(xi, zi)`. -/
theorem IsTail.eq_nil_or [AddCommGroup Z] {D : Dbs X Z} {t : List X} {z : Z}
    (h : IsTail π D t z) :
    (t = [] ∧ z = 0) ∨ ∃ xi zi b, (xi, zi) ∈ IP π D ∧ D.k' xi = some b ∧ z = zi + b := by
  cases h with
  | nil => exact .inl ⟨rfl, rfl⟩
  | snoc ht hk hπ hk' => exact .inr ⟨_, _, _, ⟨_, _, _, ⟨_, ht⟩, hk, hπ⟩, hk', rfl⟩

theorem extends_update_k [AddCommGroup Z] [DecidableEq X] {D : Dbs X Z} {x : X} {y : Z}
    (hx : D.k x = none) : Extends { D with k := Function.update D.k x (some y) } D :=
  ⟨fun x' a h ↦ by
    dsimp only
    rwa [Function.update_of_ne (by rintro rfl; simp [hx] at h)], fun _ _ h ↦ h⟩

theorem extends_update_k' [AddCommGroup Z] [DecidableEq X] {D : Dbs X Z} {x' : X} {y : Z}
    (hx' : D.k' x' = none) : Extends { D with k' := Function.update D.k' x' (some y) } D :=
  ⟨fun _ _ h ↦ h, fun x b h ↦ by
    dsimp only
    rwa [Function.update_of_ne (by rintro rfl; simp [hx'] at h)]⟩

/-! ## Single updates of `D.k` -/

/-- If no new intermediate pair `π (x, z + y)` has its rate in `D.k'`, setting `D.k x := y` adds
no tail. -/
theorem update_k_tail [AddCommGroup Z] [DecidableEq X] {D : Dbs X Z} {x : X} {y : Z}
    (hx : D.k x = none) (hk' : ∀ z, HasTail π D z → D.k' (π (x, z + y)).1 = none) (t : List X)
    (z : Z) : IsTail π { D with k := Function.update D.k x (some y) } t z ↔ IsTail π D t z := by
  refine ⟨fun h ↦ ?_, IsTail.mono (extends_update_k hx)⟩
  induction h with
  | nil => exact .nil
  | @snoc t zp xp xi a zi b _ hka hπ hb ih =>
    by_cases hxp : xp = x
    · subst hxp
      obtain rfl : y = a := by simpa using hka
      have := hk' zp ⟨t, ih⟩
      rw [hπ] at this
      exact absurd hb (by simp [this])
    · exact .snoc ih (by simpa [hxp] using hka) hπ hb

theorem update_k_good [AddCommGroup Z] [DecidableEq X] {D : Dbs X Z} {x : X} {y : Z}
    (hD : Good π D) (hx : D.k x = none)
    (hip : ∀ z, HasTail π D z → ∀ s ∈ IP π D, (π (x, z + y)).1 ≠ s.1)
    (hk' : ∀ z, HasTail π D z → D.k' (π (x, z + y)).1 = none)
    (hpair : ∀ z z', HasTail π D z → HasTail π D z' →
      (π (x, z + y)).1 = (π (x, z' + y)).1 → z = z') :
    Good π { D with k := Function.update D.k x (some y) } := by
  have htail := update_k_tail hx hk'
  have hip' : ∀ s ∈ IP π { D with k := Function.update D.k x (some y) },
      s ∈ IP π D ∨ ∃ z, HasTail π D z ∧ π (x, z + y) = s := by
    rintro s ⟨xp, zp, a, ⟨t, ht0⟩, hka, rfl⟩
    have ht := (htail t zp).1 ht0
    clear ht0
    by_cases hxp : xp = x
    · subst hxp
      obtain rfl : y = a := by simpa using hka
      exact .inr ⟨zp, ⟨t, ht⟩, rfl⟩
    · exact .inl ⟨xp, zp, a, ⟨t, ht⟩, by simpa [hxp] using hka, rfl⟩
  refine ⟨fun z t t' h h' ↦ hD.1 z t t' ((htail t z).1 h) ((htail t' z).1 h'),
    fun s hs s' hs' h ↦ ?_⟩
  rcases hip' s hs with hs | ⟨z, hz, rfl⟩ <;> rcases hip' s' hs' with hs' | ⟨z', hz', rfl⟩
  · exact hD.2 s hs s' hs' h
  · exact absurd h.symm (hip z' hz' s hs)
  · exact absurd h (hip z hz s' hs')
  · rw [hpair z z' hz hz' h]

/-! ## Single updates of `D.k'` -/

/-- If no intermediate pair has rate `x'`, setting `D.k' x' := y` adds no tail. -/
theorem update_k'_tail_of_forall [AddCommGroup Z] [DecidableEq X] {D : Dbs X Z} {x' : X} {y : Z}
    (hx' : D.k' x' = none) (h : ∀ zi, (x', zi) ∉ IP π D) (t : List X) (z : Z) :
    IsTail π { D with k' := Function.update D.k' x' (some y) } t z ↔ IsTail π D t z := by
  refine ⟨fun ht ↦ ?_, IsTail.mono (extends_update_k' hx')⟩
  induction ht with
  | nil => exact .nil
  | @snoc t zp xp xi a zi b _ hka hπ hb ih =>
    by_cases hxi : xi = x'
    · subst hxi
      exact absurd ⟨xp, zp, a, ⟨t, ih⟩, hka, hπ⟩ (h zi)
    · exact .snoc ih hka hπ (by simpa [hxi] using hb)

theorem update_k'_good_of_forall [AddCommGroup Z] [DecidableEq X] {D : Dbs X Z} {x' : X} {y : Z}
    (hD : Good π D) (hx' : D.k' x' = none) (h : ∀ zi, (x', zi) ∉ IP π D) :
    Good π { D with k' := Function.update D.k' x' (some y) } := by
  have htail := update_k'_tail_of_forall (y := y) hx' h
  have hip : IP π { D with k' := Function.update D.k' x' (some y) } ⊆ IP π D := by
    rintro s ⟨xp, zp, a, ⟨t, ht⟩, hka, rfl⟩
    exact ⟨xp, zp, a, ⟨t, (htail t zp).1 ht⟩, hka, rfl⟩
  exact ⟨fun z t t' h h' ↦ hD.1 z t t' ((htail t z).1 h) ((htail t' z).1 h'),
    fun s hs s' hs' ↦ hD.2 s (hip hs) s' (hip hs')⟩

/-- If the intermediate pair `(x', zi) = π (xp0, zp0 + a0)` exists and no new intermediate pair
`π (xp, zi + a + y)` has its rate in `D.k'` or at `x'`, setting `D.k' x' := y` adds exactly the tail
of `zi + y` through `(x', zi)`. -/
theorem update_k'_tail [AddCommGroup Z] [DecidableEq X] {D : Dbs X Z} {x' : X}
    (hD : Good π D) (hx' : D.k' x' = none) {t0 : List X} {zp0 : Z} {xp0 : X} {a0 zi y : Z}
    (ht0 : IsTail π D t0 zp0) (hk0 : D.k xp0 = some a0) (hπ0 : π (xp0, zp0 + a0) = (x', zi))
    (hk' : ∀ xp a, D.k xp = some a → D.k' (π (xp, zi + a + y)).1 = none)
    (hx'ne : ∀ xp a, D.k xp = some a → (π (xp, zi + a + y)).1 ≠ x') (t : List X) (z : Z) :
    IsTail π { D with k' := Function.update D.k' x' (some y) } t z ↔
      IsTail π D t z ∨ (t = t0 ++ [xp0] ∧ z = zi + y) := by
  refine ⟨fun ht ↦ ?_, ?_⟩
  · induction ht with
    | nil => exact .inl .nil
    | @snoc t zp xp xi a zi' b _ hka hπ hb ih =>
      rcases ih with ih | ⟨rfl, rfl⟩
      · by_cases hxi : xi = x'
        · subst hxi
          obtain rfl : y = b := by simpa using hb
          have hzz : zi' = zi := congrArg Prod.snd
            (hD.2 _ ⟨xp, zp, a, ⟨t, ih⟩, hka, hπ⟩ _ ⟨xp0, zp0, a0, ⟨t0, ht0⟩, hk0, hπ0⟩ rfl)
          subst hzz
          obtain ⟨rfl, he⟩ := Prod.mk.inj (π.injective (hπ.trans hπ0.symm))
          obtain rfl : a = a0 := Option.some.inj (hka.symm.trans hk0)
          obtain rfl := add_right_cancel he
          exact .inr ⟨by rw [hD.1 _ _ _ ih ht0], rfl⟩
        · exact .inl (.snoc ih hka hπ (by simpa [hxi] using hb))
      · rw [add_right_comm] at hπ
        by_cases hxi : xi = x'
        · exact (hx'ne xp a hka (by rw [hπ]; exact hxi)).elim
        · have := hk' xp a hka
          rw [hπ] at this
          exact absurd hb (by simp [hxi, this])
  · rintro (ht | ⟨rfl, rfl⟩)
    · exact ht.mono (extends_update_k' hx')
    · exact .snoc (ht0.mono (extends_update_k' hx')) hk0 hπ0 (by simp)

theorem update_k'_good [AddCommGroup Z] [DecidableEq X] {D : Dbs X Z} {x' : X}
    (hD : Good π D) (hx' : D.k' x' = none) {t0 : List X} {zp0 : Z} {xp0 : X} {a0 zi y : Z}
    (ht0 : IsTail π D t0 zp0) (hk0 : D.k xp0 = some a0) (hπ0 : π (xp0, zp0 + a0) = (x', zi))
    (htail : ¬ HasTail π D (zi + y))
    (hip : ∀ xp a, D.k xp = some a → ∀ s ∈ IP π D, (π (xp, zi + a + y)).1 ≠ s.1)
    (hk' : ∀ xp a, D.k xp = some a → D.k' (π (xp, zi + a + y)).1 = none)
    (hx'ne : ∀ xp a, D.k xp = some a → (π (xp, zi + a + y)).1 ≠ x')
    (hpair : ∀ xp1 a1 xp2 a2, D.k xp1 = some a1 → D.k xp2 = some a2 →
      (π (xp1, zi + a1 + y)).1 = (π (xp2, zi + a2 + y)).1 → xp1 = xp2) :
    Good π { D with k' := Function.update D.k' x' (some y) } := by
  have htails := update_k'_tail hD hx' ht0 hk0 hπ0 hk' hx'ne
  have hip' : ∀ s ∈ IP π { D with k' := Function.update D.k' x' (some y) },
      s ∈ IP π D ∨ ∃ xp a, D.k xp = some a ∧ π (xp, zi + a + y) = s := by
    rintro s ⟨xp, zp, a, ⟨t, ht⟩, hka, rfl⟩
    rcases (htails t zp).1 ht with ht | ⟨-, rfl⟩
    · exact .inl ⟨xp, zp, a, ⟨t, ht⟩, hka, rfl⟩
    · exact .inr ⟨xp, a, hka, by rw [add_right_comm]⟩
  refine ⟨fun z t t' h h' ↦ ?_, fun s hs s' hs' h ↦ ?_⟩
  · rcases (htails t z).1 h with h | ⟨rfl, hz⟩ <;>
      rcases (htails t' z).1 h' with h' | ⟨rfl, hz'⟩
    · exact hD.1 z t t' h h'
    · exact (htail ⟨t, hz' ▸ h⟩).elim
    · exact (htail ⟨t', hz ▸ h'⟩).elim
    · rfl
  · rcases hip' s hs with hs | ⟨xp, a, hka, rfl⟩ <;>
      rcases hip' s' hs' with hs' | ⟨xp', a', hka', rfl⟩
    · exact hD.2 s hs s' hs' h
    · exact absurd h.symm (hip xp' a' hka' s hs)
    · exact absurd h (hip xp a hka s' hs')
    · obtain rfl := hpair xp a xp' a' hka hka' h
      obtain rfl : a = a' := Option.some.inj (hka.symm.trans hka')
      rfl

/-! ## Counting -/

theorem card_filter_add_left [AddCommGroup Z] [Fintype Z] (c : Z) (P : Z → Prop)
    [DecidablePred P] : #(univ.filter fun y ↦ P (c + y)) = #(univ.filter P) :=
  card_equiv (Equiv.addLeft c) fun y ↦ by simp

theorem card_rate_shift [AddCommGroup Z] [Fintype Z] [DecidableEq X]
    (π : Equiv.Perm (X × Z)) (x1 xi : X) (c : Z) :
    #(univ.filter fun y ↦ (π (x1, c + y)).1 = xi) = rateCount π x1 xi :=
  card_filter_add_left c fun w ↦ (π (x1, w)).1 = xi

theorem card_pair_shift [AddCommGroup Z] [Fintype Z] [DecidableEq X]
    (π : Equiv.Perm (X × Z)) (x1 x2 : X) (c1 c2 : Z) :
    #(univ.filter fun y ↦ (π (x1, c1 + y)).1 = (π (x2, c2 + y)).1) =
      pairCount π x1 x2 (c2 - c1) := by
  rw [pairCount, ← card_filter_add_left c1 fun w ↦ (π (x1, w)).1 = (π (x2, w + (c2 - c1))).1]
  congr 1
  refine filter_congr fun y _ ↦ ?_
  simp only [show c1 + y + (c2 - c1) = c2 + y by abel]

open Classical in
/-- The capacities with a tail. -/
noncomputable def tailFinset [AddCommGroup Z] [Fintype Z] (π : Equiv.Perm (X × Z))
    (D : Dbs X Z) : Finset Z :=
  univ.filter (HasTail π D)

@[simp] theorem mem_tailFinset [AddCommGroup Z] [Fintype Z] {D : Dbs X Z} {z : Z} :
    z ∈ tailFinset π D ↔ HasTail π D z := by
  simp [tailFinset]

open Classical in
/-- The intermediate pairs. -/
noncomputable def ipFinset [AddCommGroup Z] [Fintype X] [Fintype Z] (π : Equiv.Perm (X × Z))
    (D : Dbs X Z) : Finset (X × Z) :=
  univ.filter (· ∈ IP π D)

@[simp] theorem mem_ipFinset [AddCommGroup Z] [Fintype X] [Fintype Z] {D : Dbs X Z}
    {s : X × Z} : s ∈ ipFinset π D ↔ s ∈ IP π D := by
  simp [ipFinset]

/-- Lemma 5.12, tails: a good database has at most `|D.k'| + 1` capacities with a tail. -/
theorem card_hasTail_le [AddCommGroup Z] [Fintype X] [Fintype Z] {D : Dbs X Z}
    (hD : Good π D) : #(tailFinset π D) ≤ D.k'.size + 1 := by
  classical
  let g : X → Z := fun xi ↦
    if h : ∃ p : Z × Z, (xi, p.1) ∈ IP π D ∧ D.k' xi = some p.2 then h.choose.1 + h.choose.2
    else 0
  have hsub : tailFinset π D ⊆ insert 0 ((univ.filter fun xi ↦ (D.k' xi).isSome).image g) := by
    intro z hz
    obtain ⟨t, ht⟩ := mem_tailFinset.1 hz
    rcases ht.eq_nil_or with ⟨-, rfl⟩ | ⟨xi, zi, b, hip, hb, rfl⟩
    · exact mem_insert_self _ _
    · refine mem_insert_of_mem (mem_image.2 ⟨xi, mem_filter.2 ⟨mem_univ _, by simp [hb]⟩, ?_⟩)
      have h : ∃ p : Z × Z, (xi, p.1) ∈ IP π D ∧ D.k' xi = some p.2 := ⟨(zi, b), hip, hb⟩
      have hp : h.choose = (zi, b) :=
        Prod.ext (congrArg Prod.snd (hD.2 _ h.choose_spec.1 _ hip rfl))
          (Option.some.inj (h.choose_spec.2.symm.trans hb))
      simp only [g, dite_eq_left h, hp]
  calc #(tailFinset π D) ≤ #(insert 0 ((univ.filter fun xi ↦ (D.k' xi).isSome).image g)) :=
        card_le_card hsub
    _ ≤ #((univ.filter fun xi ↦ (D.k' xi).isSome).image g) + 1 := card_insert_le _ _
    _ ≤ D.k'.size + 1 := Nat.add_le_add_right card_image_le _

/-- Lemma 5.12, intermediate pairs: a good database has at most `|D.k| (|D.k'| + 1)`. -/
theorem card_IP_le [AddCommGroup Z] [Fintype X] [Fintype Z] {D : Dbs X Z} (hD : Good π D) :
    #(ipFinset π D) ≤ D.k.size * (D.k'.size + 1) := by
  classical
  have hsub : ipFinset π D ⊆ ((univ.filter fun x ↦ (D.k x).isSome) ×ˢ tailFinset π D).image
      fun p ↦ π (p.1, p.2 + (D.k p.1).getD 0) := by
    intro s hs
    obtain ⟨xp, zp, a, hz, hk, rfl⟩ := mem_ipFinset.1 hs
    exact mem_image.2 ⟨(xp, zp), mem_product.2 ⟨mem_filter.2 ⟨mem_univ _, by simp [hk]⟩,
      mem_tailFinset.2 hz⟩, by simp [hk]⟩
  calc #(ipFinset π D) ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ = D.k.size * #(tailFinset π D) := card_product _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (card_hasTail_le hD)

/-- The rates a new intermediate pair must avoid: the rates of the intermediate pairs and the
points of `D.k'`. -/
noncomputable def badRates [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    (π : Equiv.Perm (X × Z)) (D : Dbs X Z) : Finset X :=
  (ipFinset π D).image Prod.fst ∪ univ.filter fun xi ↦ (D.k' xi).isSome

theorem card_badRates_le [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    {D : Dbs X Z} {t : ℕ} (hD : Good π D) (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) :
    #(badRates π D) ≤ (t + 1) * t + t :=
  (card_union_le _ _).trans (Nat.add_le_add (card_image_le.trans ((card_IP_le hD).trans
    ((Nat.mul_le_mul hk (Nat.succ_le_succ hk')).trans_eq (Nat.mul_comm _ _)))) hk')

/-- The values `y` for which setting `D.k x := y` may break goodness: a new intermediate pair
`π (x, z + y)` has its rate in `badRates π D`, or two of them share a rate. -/
noncomputable def badAttachK [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] (π : Equiv.Perm (X × Z)) (D : Dbs X Z) (x : X) : Finset Z :=
  (tailFinset π D).biUnion fun z ↦
    ((badRates π D).biUnion fun xi ↦ univ.filter fun y ↦ (π (x, z + y)).1 = xi) ∪
      ((tailFinset π D).erase z).biUnion fun z' ↦
        univ.filter fun y ↦ (π (x, z + y)).1 = (π (x, z' + y)).1

theorem card_badAttachK_le [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] {D : Dbs X Z} {x : X} {t G : ℕ} (hD : Good π D) (hG : PermGood π G)
    (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) :
    #(badAttachK π D x) ≤ (t + 1) * ((t + 1) * t + 2 * t) * G := by
  have hT : #(tailFinset π D) ≤ t + 1 := (card_hasTail_le hD).trans (by omega)
  refine (card_biUnion_le_card_mul _ _ (((t + 1) * t + t) * G + t * G) fun z hz ↦ ?_).trans ?_
  · refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · exact (card_biUnion_le_card_mul _ _ G fun xi _ ↦
        (card_rate_shift π x xi z).trans_le (hG.rate x xi)).trans
          (Nat.mul_le_mul_right _ (card_badRates_le hD hk hk'))
    · refine (card_biUnion_le_card_mul _ _ G fun z' hz' ↦ ?_).trans (Nat.mul_le_mul_right _ ?_)
      · rw [card_pair_shift]
        exact hG.pair _ _ _ fun h ↦ (mem_erase.1 hz').1 (sub_eq_zero.1 (Prod.mk.inj h).2)
      · rw [card_erase_of_mem hz]
        omega
  · calc #(tailFinset π D) * (((t + 1) * t + t) * G + t * G)
        ≤ (t + 1) * (((t + 1) * t + t) * G + t * G) := Nat.mul_le_mul_right _ hT
      _ = _ := by ring

/-- Outside `badAttachK π D x`, setting `D.k x := y` keeps the tails and goodness. -/
theorem update_k_of_not_mem [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] {D : Dbs X Z} {x : X} {y : Z} (hD : Good π D) (hx : D.k x = none)
    (hy : y ∉ badAttachK π D x) :
    (∀ t z, IsTail π { D with k := Function.update D.k x (some y) } t z ↔ IsTail π D t z) ∧
      Good π { D with k := Function.update D.k x (some y) } := by
  have hk' : ∀ z, HasTail π D z → D.k' (π (x, z + y)).1 = none := fun z hz ↦ by
    by_contra hne
    exact hy (mem_biUnion.2 ⟨z, mem_tailFinset.2 hz, mem_union_left _ (mem_biUnion.2
      ⟨_, mem_union_right _ (mem_filter.2 ⟨mem_univ _, Option.isSome_iff_ne_none.2 hne⟩),
        mem_filter.2 ⟨mem_univ _, rfl⟩⟩)⟩)
  refine ⟨update_k_tail hx hk', update_k_good hD hx (fun z hz s hs h ↦ hy ?_) hk'
    (fun z z' hz hz' h ↦ ?_)⟩
  · exact mem_biUnion.2 ⟨z, mem_tailFinset.2 hz, mem_union_left _ (mem_biUnion.2
      ⟨s.1, mem_union_left _ (mem_image.2 ⟨s, mem_ipFinset.2 hs, rfl⟩),
        mem_filter.2 ⟨mem_univ _, h⟩⟩)⟩
  · by_contra hne
    exact hy (mem_biUnion.2 ⟨z, mem_tailFinset.2 hz, mem_union_right _ (mem_biUnion.2
      ⟨z', mem_erase.2 ⟨Ne.symm hne, mem_tailFinset.2 hz'⟩, mem_filter.2 ⟨mem_univ _, h⟩⟩)⟩)

theorem isTail_update_k_iff [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] {D : Dbs X Z} {x : X} {y : Z} (hD : Good π D) (hx : D.k x = none)
    (hy : y ∉ badAttachK π D x) (t : List X) (z : Z) :
    IsTail π { D with k := Function.update D.k x (some y) } t z ↔ IsTail π D t z :=
  (update_k_of_not_mem hD hx hy).1 t z

theorem good_update_k [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] {D : Dbs X Z} {x : X} {y : Z} (hD : Good π D) (hx : D.k x = none)
    (hy : y ∉ badAttachK π D x) : Good π { D with k := Function.update D.k x (some y) } :=
  (update_k_of_not_mem hD hx hy).2

open Classical in
/-- Lemmas 5.14 and 5.16 with the pair condition: few `y` make `D[k := x ↦ y]` bad. -/
theorem card_bad_k_le [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] {D : Dbs X Z} {x : X} {t G : ℕ} (hD : Good π D) (hG : PermGood π G)
    (hx : D.k x = none) (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) :
    #(univ.filter fun y : Z ↦ ¬ Good π { D with k := Function.update D.k x (some y) }) ≤
      (t + 1) * ((t + 1) * t + 2 * t) * G := by
  refine (card_le_card fun y hy ↦ ?_).trans (card_badAttachK_le (x := x) hD hG hk hk')
  by_contra hm
  exact (mem_filter.1 hy).2 (good_update_k hD hx hm)

/-- The values `y` for which setting `D.k' x' := y` may break goodness, given the intermediate pair
`(x', zi)`: `zi + y` already has a tail, a new intermediate pair `π (xp, zi + D.k xp + y)` has its
rate in `badRates π D` or at `x'`, or two of them share a rate. -/
noncomputable def badCompleteAt [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] (π : Equiv.Perm (X × Z)) (D : Dbs X Z) (x' : X) (zi : Z) : Finset Z :=
  (univ.filter fun y ↦ zi + y ∈ tailFinset π D) ∪
    (univ.filter fun xp ↦ (D.k xp).isSome).biUnion (fun xp ↦
      (insert x' (badRates π D)).biUnion fun xi ↦
        univ.filter fun y ↦ (π (xp, zi + (D.k xp).getD 0 + y)).1 = xi) ∪
    (univ.filter fun xp ↦ (D.k xp).isSome).biUnion fun xp1 ↦
      ((univ.filter fun xp ↦ (D.k xp).isSome).erase xp1).biUnion fun xp2 ↦
        univ.filter fun y ↦
          (π (xp1, zi + (D.k xp1).getD 0 + y)).1 = (π (xp2, zi + (D.k xp2).getD 0 + y)).1

open Classical in
/-- The values `y` for which setting `D.k' x' := y` may break goodness: empty if no intermediate
pair has rate `x'`, else `badCompleteAt` of the (unique) one. -/
noncomputable def badCompleteK' [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] (π : Equiv.Perm (X × Z)) (D : Dbs X Z) (x' : X) : Finset Z :=
  if h : ∃ zi, (x', zi) ∈ IP π D then badCompleteAt π D x' h.choose else ∅

theorem card_badCompleteAt_le [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] {D : Dbs X Z} {x' : X} {t G : ℕ} (hD : Good π D) (hG : PermGood π G)
    (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) (zi : Z) :
    #(badCompleteAt π D x' zi) ≤ (t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G := by
  have hK : #(univ.filter fun xp ↦ (D.k xp).isSome) ≤ t := hk
  refine (card_union_le _ _).trans
    (Nat.add_le_add ((card_union_le _ _).trans (Nat.add_le_add ?_ ?_)) ?_)
  · refine (card_filter_add_left zi (· ∈ tailFinset π D)).trans_le
      ((card_le_card fun y hy ↦ (mem_filter.1 hy).2).trans ?_)
    exact (card_hasTail_le hD).trans (by omega)
  · refine (card_biUnion_le_card_mul _ _ (((t + 1) * t + t + 1) * G) fun xp _ ↦ ?_).trans
      ((Nat.mul_le_mul_right _ hK).trans_eq (Nat.mul_assoc _ _ _).symm)
    refine (card_biUnion_le_card_mul _ _ G fun xi _ ↦
      (card_rate_shift π xp xi _).trans_le (hG.rate xp xi)).trans (Nat.mul_le_mul_right _ ?_)
    have := card_badRates_le hD hk hk'
    exact (card_insert_le _ _).trans (by omega)
  · refine (card_biUnion_le_card_mul _ _ (t * G) fun xp1 _ ↦ ?_).trans
      ((Nat.mul_le_mul_right _ hK).trans_eq (Nat.mul_assoc _ _ _).symm)
    refine (card_biUnion_le_card_mul _ _ G fun xp2 hxp2 ↦ ?_).trans
      (Nat.mul_le_mul_right _ (card_erase_le.trans hK))
    rw [card_pair_shift]
    exact hG.pair _ _ _ fun h ↦ (mem_erase.1 hxp2).1 (Prod.mk.inj h).1.symm

theorem card_badCompleteK'_le [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] {D : Dbs X Z} {x' : X} {t G : ℕ} (hD : Good π D) (hG : PermGood π G)
    (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) :
    #(badCompleteK' π D x') ≤ (t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G := by
  rw [badCompleteK']
  split_ifs
  · exact card_badCompleteAt_le hD hG hk hk' _
  · simp

/-- Outside `badCompleteK' π D x'`, setting `D.k' x' := y` keeps goodness and adds at most one
tail: none if no intermediate pair has rate `x'`, else the tail of `zi + y` through the unique
intermediate pair `(x', zi)`, a capacity that had no tail. -/
theorem update_k'_of_not_mem [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] {D : Dbs X Z} {x' : X} {y : Z} (hD : Good π D) (hx' : D.k' x' = none)
    (hy : y ∉ badCompleteK' π D x') :
    (((∀ zi, (x', zi) ∉ IP π D) ∧
        ∀ t z, IsTail π { D with k' := Function.update D.k' x' (some y) } t z ↔ IsTail π D t z) ∨
      ∃ t0 zp xp a zi, IsTail π D t0 zp ∧ D.k xp = some a ∧ π (xp, zp + a) = (x', zi) ∧
        (∀ t z, IsTail π { D with k' := Function.update D.k' x' (some y) } t z ↔
          IsTail π D t z ∨ (t = t0 ++ [xp] ∧ z = zi + y)) ∧
        ¬ HasTail π D (zi + y)) ∧
      Good π { D with k' := Function.update D.k' x' (some y) } := by
  by_cases h : ∃ zi, (x', zi) ∈ IP π D
  · obtain ⟨zi, hzi, hy⟩ : ∃ zi, (x', zi) ∈ IP π D ∧ y ∉ badCompleteAt π D x' zi := by
      refine ⟨h.choose, h.choose_spec, ?_⟩
      rw [badCompleteK', dite_eq_left h] at hy
      exact hy
    obtain ⟨xp0, zp0, a0, ⟨t0, ht0⟩, hk0, hπ0⟩ := hzi
    have memK : ∀ xp a, D.k xp = some a → xp ∈ univ.filter fun xp ↦ (D.k xp).isSome :=
      fun xp a h ↦ mem_filter.2 ⟨mem_univ _, by simp [h]⟩
    have htail : ¬ HasTail π D (zi + y) := fun hz ↦
      hy (mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨mem_univ _, mem_tailFinset.2 hz⟩)))
    have hrate : ∀ xp a, D.k xp = some a → ∀ xi ∈ insert x' (badRates π D),
        (π (xp, zi + a + y)).1 ≠ xi := fun xp a hka xi hxi h ↦
      hy (mem_union_left _ (mem_union_right _ (mem_biUnion.2 ⟨xp, memK xp a hka,
        mem_biUnion.2 ⟨xi, hxi, mem_filter.2 ⟨mem_univ _, by rwa [hka, Option.getD_some]⟩⟩⟩)))
    have hk' : ∀ xp a, D.k xp = some a → D.k' (π (xp, zi + a + y)).1 = none := fun xp a hka ↦ by
      by_contra hne
      exact hrate xp a hka _ (mem_insert_of_mem (mem_union_right _
        (mem_filter.2 ⟨mem_univ _, Option.isSome_iff_ne_none.2 hne⟩))) rfl
    have hx'ne : ∀ xp a, D.k xp = some a → (π (xp, zi + a + y)).1 ≠ x' :=
      fun xp a hka ↦ hrate xp a hka x' (mem_insert_self _ _)
    refine ⟨.inr ⟨t0, zp0, xp0, a0, zi, ht0, hk0, hπ0,
      update_k'_tail hD hx' ht0 hk0 hπ0 hk' hx'ne, htail⟩,
      update_k'_good hD hx' ht0 hk0 hπ0 htail (fun xp a hka s hs ↦ hrate xp a hka _
        (mem_insert_of_mem (mem_union_left _ (mem_image.2 ⟨s, mem_ipFinset.2 hs, rfl⟩))))
        hk' hx'ne fun xp1 a1 xp2 a2 h1 h2 h ↦ ?_⟩
    by_contra hne
    refine hy (mem_union_right _ (mem_biUnion.2 ⟨xp1, memK _ _ h1, mem_biUnion.2
      ⟨xp2, mem_erase.2 ⟨Ne.symm hne, memK _ _ h2⟩, mem_filter.2 ⟨mem_univ _, ?_⟩⟩⟩))
    simp only [h1, h2, Option.getD_some]
    exact h
  · have h' : ∀ zi, (x', zi) ∉ IP π D := fun zi hzi ↦ h ⟨zi, hzi⟩
    exact ⟨.inl ⟨h', update_k'_tail_of_forall hx' h'⟩, update_k'_good_of_forall hD hx' h'⟩

theorem good_update_k' [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] {D : Dbs X Z} {x' : X} {y : Z} (hD : Good π D) (hx' : D.k' x' = none)
    (hy : y ∉ badCompleteK' π D x') :
    Good π { D with k' := Function.update D.k' x' (some y) } :=
  (update_k'_of_not_mem hD hx' hy).2

open Classical in
/-- Lemma 5.18 with the pair condition: few `y` make `D[k' := x' ↦ y]` bad. -/
theorem card_bad_k'_le [AddCommGroup Z] [Fintype X] [Fintype Z] [DecidableEq X]
    [DecidableEq Z] {D : Dbs X Z} {x' : X} {t G : ℕ} (hD : Good π D) (hG : PermGood π G)
    (hx' : D.k' x' = none) (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) :
    #(univ.filter fun y : Z ↦ ¬ Good π { D with k' := Function.update D.k' x' (some y) }) ≤
      (t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G := by
  refine (card_le_card fun y hy ↦ ?_).trans (card_badCompleteK'_le (x' := x') hD hG hk hk')
  by_contra hm
  exact (mem_filter.1 hy).2 (good_update_k' hD hx' hm)

end Quantum.Sponge

end
