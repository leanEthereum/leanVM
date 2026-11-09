/-
  LeanVM.Guest.B1.Sig.WotsGroup

  The layout of a WOTS+C group's arms: arm `0` lays the slots out after the group's base, every
  later arm starts above the product and the encoding.
-/

module

public import LeanVM.Guest.B1.Sig.WotsArm

/-!
# A group's layout

* `walksT_snd`, `armT_snd`, `armBase_succ`, `armsT_snd`: the bases;
* `slot_lt`, `slot_ge`: a group's slots lie between its first walk and its product;
* `armZeroLay`, `armPosLay`: the hypotheses of `armT_ssa`/`armT_canon` for arm `0` and for a later
  arm.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

theorem walksT_snd (W : WotsT) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    ∀ (m r b : Nat), (walksT W slots first k stride m r b).2 = walkBase stride k r m b
  | 0, _, _ => rfl
  | m + 1, r, _ => walksT_snd W slots first k stride m (r + 1) _

theorem armT_snd (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : Nat) :
    (armT W slots first n fold prodIn encIn prodOut encOut k b).2 =
      if k = 0 then walkBase (W.size + 1) k 0 n (if fold then b + 1 else b)
      else walkBase W.size k 0 n (if fold then b + 1 else b) + 1 := by
  unfold armT
  split <;> simp_all [walksT_snd]

/-- The base after arm `k` from `a`. -/
def armNext (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k a : Nat) : Nat :=
  if k = 0 then (armT W slots first n fold prodIn encIn prodOut encOut k a).2 + 2
  else (armT W slots first n fold prodIn encIn prodOut encOut k a).2

theorem armBase_succ (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : ∀ (k0 j b : Nat),
    armBase W slots first n fold prodIn encIn prodOut encOut k0 (j + 1) b =
      armNext W slots first n fold prodIn encIn prodOut encOut (k0 + j)
        (armBase W slots first n fold prodIn encIn prodOut encOut k0 j b)
  | k0, 0, b => by simp [armBase, armNext]
  | k0, j + 1, b => by
      rw [armBase, armBase_succ W slots first n fold prodIn encIn prodOut encOut (k0 + 1) j,
        show k0 + 1 + j = k0 + (j + 1) by omega]
      rfl

theorem armsT_snd (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : ∀ (m k b : Nat),
    (armsT W slots first n fold prodIn encIn prodOut encOut m k b).2 =
      armBase W slots first n fold prodIn encIn prodOut encOut k m b
  | 0, _, _ => rfl
  | m + 1, k, _ => armsT_snd W slots first n fold prodIn encIn prodOut encOut m (k + 1) _

/-- The group's start, as a number. -/
theorem groupStart_eq (fold : Bool) (b : Nat) : groupStart fold b = b + 6 + (if fold then 1 else 0) := rfl

theorem chainStride_eq (W : WotsT) : chainStride W = 1 + 3 * (W.size + 1) := rfl

theorem slot_bounds (W : WotsT) (fold : Bool) (b t s : Nat) (hs : s < 3) :
    groupStart fold b + chainStride W * t + 1 ≤ slotsT W fold b t s ∧
      slotsT W fold b t s + 1 ≤ groupStart fold b + chainStride W * (t + 1) := by
  unfold slotsT
  rw [mul_add, mul_one, chainStride_eq]
  interval_cases s <;> omega

theorem slot_mono (W : WotsT) (fold : Bool) (b t : Nat) {s s' : Nat} (h : s < s') (hs : s' < 3) :
    slotsT W fold b t s + 1 ≤ slotsT W fold b t s' := by
  unfold slotsT
  have : s < 3 := by omega
  interval_cases s <;> interval_cases s' <;> omega

theorem chain_le (W : WotsT) (fold : Bool) (b : Nat) {t t' : Nat} (h : t < t') :
    groupStart fold b + chainStride W * (t + 1) ≤ groupStart fold b + chainStride W * t' :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _

theorem walkSum_le (stride k r : Nat) {t t' : Nat} (h : t ≤ t') : walkSum stride k r t ≤ walkSum stride k r t' := by
  induction t' with
  | zero => have : t = 0 := by omega
            subst this; exact le_rfl
  | succ t' ih =>
      rcases Nat.lt_or_ge t (t' + 1) with h1 | h1
      · rw [walkSum_succ]; have := ih (by omega); omega
      · have : t = t' + 1 := by omega
        subst this; exact le_rfl

theorem walkBase_zero (S t b : Nat) : walkBase S 0 0 t b = b + t * (1 + 3 * S) := by
  rw [walkBase_eq, walkSum_zero_digits]

theorem walkSize_zero (S t : Nat) : walkSize S (dig 0 t) = 1 + 3 * S := by
  simp [walkSize, dig]

/-- **Arm `0`'s walks are laid out.** -/
theorem arm0_lay (W : WotsT) {B : Nat} (fold : Bool) {b n : Nat} (hB : B ≤ b + 6) :
    (∀ t < n, WalkLay W B (slotsT W fold b t) (W.size + 1) (dig 0 t)
      (walkBase (W.size + 1) 0 0 t (if fold then b + 6 + 1 else b + 6))) ∧
    (∀ t < n, ∀ t' < n, t ≠ t' → ∀ x,
      WalkR (slotsT W fold b t) (W.size + 1) (dig 0 t)
        (walkBase (W.size + 1) 0 0 t (if fold then b + 6 + 1 else b + 6)) x →
      ¬ WalkR (slotsT W fold b t') (W.size + 1) (dig 0 t')
        (walkBase (W.size + 1) 0 0 t' (if fold then b + 6 + 1 else b + 6)) x) ∧
    (∀ x, WalksR (slotsT W fold b) (W.size + 1) 0 n (if fold then b + 6 + 1 else b + 6) x →
      ∃ j, x = .n j ∧ groupStart fold b ≤ j ∧ j < groupStart fold b + chainStride W * n) := by
  have hgs : (if fold then b + 6 + 1 else b + 6) = groupStart fold b := by cases fold <;> rfl
  have hwb : ∀ t, walkBase (W.size + 1) 0 0 t (if fold then b + 6 + 1 else b + 6) =
      groupStart fold b + chainStride W * t := by
    intro t; rw [walkBase_zero, hgs, chainStride_eq, mul_comm]
  -- region of chain t
  have hreg : ∀ t x, WalkR (slotsT W fold b t) (W.size + 1) (dig 0 t)
      (walkBase (W.size + 1) 0 0 t (if fold then b + 6 + 1 else b + 6)) x →
      ∃ j, x = .n j ∧ groupStart fold b + chainStride W * t ≤ j ∧
        j < groupStart fold b + chainStride W * (t + 1) := by
    rintro t x (⟨u, hu, rfl⟩ | ⟨s, hs, u, hu, rfl⟩)
    · rw [walkSize_zero, ← chainStride_eq] at hu
      rw [hwb, mul_add, mul_one]
      exact ⟨_, rfl, by omega, by omega⟩
    · have := slot_bounds W fold b t s hs
      exact ⟨_, rfl, by omega, by omega⟩
  refine ⟨fun t ht => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun t ht t' ht' hne x hx hx' => ?_, fun x hx => ?_⟩
  · rw [hwb, groupStart_eq]; omega
  · intro s hs; have := slot_bounds W fold b t s hs; rw [groupStart_eq] at this; omega
  · intro s s' h hs'; exact slot_mono W fold b t h hs'
  · omega
  · intro s hs j hj
    have hj' : j < 3 := by simp [dig] at hj; omega
    rw [hwb]
    unfold slotsT
    rw [chainStride_eq]
    interval_cases s <;> interval_cases j <;> omega
  · intro s hs
    rw [hwb]
    have := slot_bounds W fold b t s hs
    omega
  · obtain ⟨j, rfl, h1, h2⟩ := hreg t x hx
    obtain ⟨j', e, h1', h2'⟩ := hreg t' _ hx'
    simp only [V.mk.injEq, true_and] at e
    subst e
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := chain_le W fold b h; omega
    · have := chain_le W fold b h; omega
  · obtain ⟨t, ht, hx⟩ := hx
    obtain ⟨j, rfl, h1, h2⟩ := hreg t x hx
    have : groupStart fold b + chainStride W * (t + 1) ≤ groupStart fold b + chainStride W * n :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _
    exact ⟨j, rfl, by omega, by omega⟩

theorem walkBase_succ (S k t b : Nat) :
    walkBase S k 0 (t + 1) b = walkBase S k 0 t b + walkSize S (dig k t) := by
  rw [walkBase_eq, walkBase_eq, walkSum_succ]
  simp only [Nat.zero_add]
  omega

theorem walkBase_le (S k b : Nat) {t t' : Nat} (h : t ≤ t') : walkBase S k 0 t b ≤ walkBase S k 0 t' b := by
  rw [walkBase_eq, walkBase_eq]
  have := walkSum_le S k 0 h
  omega

/-- **A later arm's walks are laid out**, above the product and the encoding. -/
theorem armPos_lay (W : WotsT) {B : Nat} (fold : Bool) {b n k a : Nat} (hB : B ≤ b + 6)
    (ha : groupStart fold b + chainStride W * n + 2 ≤ a) :
    (∀ t < n, WalkLay W B (slotsT W fold b t) W.size (dig k t)
      (walkBase W.size k 0 t (if fold then a + 1 else a))) ∧
    (∀ t < n, ∀ t' < n, t ≠ t' → ∀ x,
      WalkR (slotsT W fold b t) W.size (dig k t) (walkBase W.size k 0 t (if fold then a + 1 else a)) x →
      ¬ WalkR (slotsT W fold b t') W.size (dig k t') (walkBase W.size k 0 t' (if fold then a + 1 else a)) x) ∧
    (∀ x, WalksR (slotsT W fold b) W.size k n (if fold then a + 1 else a) x →
      ∃ j, x = .n j ∧ ((groupStart fold b ≤ j ∧ j < groupStart fold b + chainStride W * n) ∨
        ((if fold then a + 1 else a) ≤ j ∧ j < walkBase W.size k 0 n (if fold then a + 1 else a)))) := by
  set b0 := if fold then a + 1 else a with hb0
  have hab : a ≤ b0 := by rw [hb0]; split <;> omega
  have hslot : ∀ t < n, ∀ s < 3, slotsT W fold b t s + 1 ≤ groupStart fold b + chainStride W * n := by
    intro t ht s hs
    have h1 := slot_bounds W fold b t s hs
    have h2 : groupStart fold b + chainStride W * (t + 1) ≤ groupStart fold b + chainStride W * n :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _
    omega
  have hb0B : b0 ≤ walkBase W.size k 0 0 b0 := le_rfl
  have hreg : ∀ t < n, ∀ x, WalkR (slotsT W fold b t) W.size (dig k t) (walkBase W.size k 0 t b0) x →
      ∃ j, x = .n j ∧ ((groupStart fold b + chainStride W * t ≤ j ∧
        j < groupStart fold b + chainStride W * (t + 1)) ∨
        (walkBase W.size k 0 t b0 ≤ j ∧ j < walkBase W.size k 0 (t + 1) b0)) := by
    rintro t ht x (⟨u, hu, rfl⟩ | ⟨s, hs, u, hu, rfl⟩)
    · rw [walkBase_succ]
      exact ⟨_, rfl, Or.inr ⟨by omega, by omega⟩⟩
    · have := slot_bounds W fold b t s hs
      exact ⟨_, rfl, Or.inl ⟨by omega, by omega⟩⟩
  have hwbge : ∀ t, b0 ≤ walkBase W.size k 0 t b0 := fun t => by
    have := walkBase_le W.size k b0 (Nat.zero_le t); simpa [walkBase] using this
  refine ⟨fun t ht => ⟨?_, ?_, ?_, le_rfl, ?_, ?_⟩, fun t ht t' ht' hne x hx hx' => ?_, fun x hx => ?_⟩
  · have := hwbge t; rw [groupStart_eq] at ha; omega
  · intro s hs; have := slot_bounds W fold b t s hs; rw [groupStart_eq] at this; omega
  · intro s s' h hs'; exact slot_mono W fold b t h hs'
  · intro s hs j hj
    left
    have := hslot t ht s hs
    have := hwbge t
    omega
  · intro s hs
    left
    have := hslot t ht s hs
    have := hwbge t
    omega
  · obtain ⟨j, rfl, h1⟩ := hreg t ht x hx
    obtain ⟨j', e, h1'⟩ := hreg t' ht' _ hx'
    simp only [V.mk.injEq, true_and] at e
    subst e
    have d1 : groupStart fold b + chainStride W * (t + 1) ≤ groupStart fold b + chainStride W * n :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _
    have d2 : groupStart fold b + chainStride W * (t' + 1) ≤ groupStart fold b + chainStride W * n :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ ht') _
    have d3 := hwbge t
    have d4 := hwbge t'
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have c1 := chain_le W fold b h
      have c2 := walkBase_le W.size k b0 (show t + 1 ≤ t' by omega)
      have c3 := hwbge t
      have c4 : groupStart fold b + chainStride W * (t' + 1) ≤ groupStart fold b + chainStride W * n :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ ht') _
      rcases h1 with h1 | h1 <;> rcases h1' with h1' | h1' <;> omega
    · have c1 := chain_le W fold b h
      have c2 := walkBase_le W.size k b0 (show t' + 1 ≤ t by omega)
      have c3 := hwbge t'
      have c4 : groupStart fold b + chainStride W * (t + 1) ≤ groupStart fold b + chainStride W * n :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _
      rcases h1 with h1 | h1 <;> rcases h1' with h1' | h1' <;> omega
  · obtain ⟨t, ht, hx⟩ := hx
    obtain ⟨j, rfl, h1⟩ := hreg t ht x hx
    have c4 : groupStart fold b + chainStride W * (t + 1) ≤ groupStart fold b + chainStride W * n :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _
    have c2 := walkBase_le W.size k b0 (show t + 1 ≤ n by omega)
    have c3 := hwbge t
    rcases h1 with h1 | h1
    · exact ⟨j, rfl, Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨j, rfl, Or.inr ⟨by omega, by omega⟩⟩

/-- The base of arm `k` of a group from base `b`. -/
def armB (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b k : Nat) : Nat :=
  armBase W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) 0 k (b + 6)

theorem armB_zero (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) :
    armB W first n fold prodIn encIn b 0 = b + 6 := rfl

theorem armB_succ (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b k : Nat) :
    armB W first n fold prodIn encIn b (k + 1) =
      armNext W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) k
        (armB W first n fold prodIn encIn b k) := by
  unfold armB
  rw [armBase_succ, Nat.zero_add]

theorem armB_one (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) :
    armB W first n fold prodIn encIn b 1 = groupStart fold b + chainStride W * n + 2 := by
  rw [armB_succ, armB_zero, armNext, armT_snd]
  simp only [↓reduceIte, walkBase_zero, chainStride_eq]
  cases fold <;> simp [groupStart] <;> ring

theorem armB_next_pos (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b k : Nat)
    (hk : k ≠ 0) :
    armB W first n fold prodIn encIn b (k + 1) =
      walkBase W.size k 0 n (if fold then armB W first n fold prodIn encIn b k + 1
        else armB W first n fold prodIn encIn b k) + 1 := by
  rw [armB_succ, armNext, armT_snd]
  simp only [hk, ↓reduceIte]

theorem armB_lt (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) :
    ∀ k, armB W first n fold prodIn encIn b k < armB W first n fold prodIn encIn b (k + 1)
  | 0 => by
      rw [armB_one, armB_zero, groupStart_eq]
      split <;> omega
  | k + 1 => by
      rw [armB_next_pos W first n fold prodIn encIn b (k + 1) (by omega)]
      have := walkBase_le W.size (k + 1) (if fold = true then armB W first n fold prodIn encIn b (k + 1) + 1
        else armB W first n fold prodIn encIn b (k + 1)) (Nat.zero_le n)
      simp only [walkBase] at this
      cases fold <;> simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢ <;> omega

theorem armB_mono (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) {k k' : Nat}
    (h : k ≤ k') : armB W first n fold prodIn encIn b k ≤ armB W first n fold prodIn encIn b k' := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact le_rfl
  | succ k' ih =>
      rcases Nat.lt_or_ge k (k' + 1) with h1 | h1
      · have := armB_lt W first n fold prodIn encIn b k'; have := ih (by omega); omega
      · have : k = k' + 1 := by omega
        subst this; exact le_rfl

theorem armB_pos (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) {k : Nat}
    (hk : k ≠ 0) : groupStart fold b + chainStride W * n + 2 ≤ armB W first n fold prodIn encIn b k := by
  rw [← armB_one W first n fold prodIn encIn b]
  exact armB_mono W first n fold prodIn encIn b (by omega)

end
end LeanVM.Guest.B1.Sig
