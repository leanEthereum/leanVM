module

public import Quantum.Xmss.Hybrid.SchemeSplit

@[expose] public section

/-!
# The coin stage: the randomizer bases' paths in public slots

`schemeSplit` hides the scheme seed `S` but leaves the challenger's randomizer-base paths in the
table: for each requested label `a : J` (a finite set of labels, CoinPath's `J`), `k` at the
`S`-keyed cell `cell a P S` (the first block of the randomizer base's derivation), `k'` at its
rate, and `h` at its capacity. Three more exchanges, composed after `schemeSplit`, move these path
values into public slots, so that the randomizer bases `R0` of the requested messages are functions
of the public part with only `S` hidden. The `S`-keyed cells along the paths stay hidden cells.

* `stageK`: `k` at the cells `cell a P S` with the `k`-slots, when the cells are distinct
  (labels sharing a first block share the cell);
* `stageK'`: `k'` at the rates `(π (cell a P S, κ a)).1` (`κ` the `k`-slots) with the `k'`-slots,
  when distinct;
* `stageH`: `h` at the capacities `(π (cell a P S, κ a)).2 + κ' a` (`κ'` the `k'`-slots) with the
  `h`-slots, shifted by the rate, when distinct: the `h`-slots take the blocks' outputs.

Each stage's cells and shifts depend only on data it keeps (`π`, the parameter's slot, `S`, the
earlier slots), so `stageN` (through `fiberEquiv`) makes it a bijection. `coinSplit` composes them
after `schemeSplit`.

* `coinSplit_coins`: on the good set, the slots hold the table's `k` and `k'` at the paths' cells
  and the paths' outputs (`coinCellK`, `coinCellK'`, `coinCellH`). `digest_eq_pubR0`: the digest
  of a requested one-block input is `pubR0` of the public part; `randomizerBase_eq_pubR0`: the
  randomizer base `R0(l, e, M)` of a requested label, for messages under `72` bytes.
* `coinGood`: `schemeGood`, distinct path rates and distinct capacities of the hidden and the path
  cells (`CollGood`), and no computation `Q i` from the public part reading a path cell
  (`ReadGood`). On it the challenger's data is a function of the public part
  (`schemeData_eq_pubData_coinSplit`) and so is the parameter (`pubParam_coinSplit`).
* `coinGood_frac_le`: the bad fraction is at most that of `schemeGood`, the bad permutations, the
  collisions `(|J|² G + |A ⊕ J|² (G + 1)) / |Z|`, and per computation
  `qs₂ᵢ / 2^256 + |J| (G + 1) qᵢ / |Z|`; `coinGood_frac_le_of_schemeGood` adds
  `schemeGood_frac_le`.
-/

open scoped ENNReal

namespace Quantum.Xmss.Hybrid

open Quantum Quantum.Sponge

/-! ## Guarded exchanges and counts, over abstract types -/

section generic

/-- A guarded exchange keeps the data `w`; when the cells are distinct, the slots take the cell
values shifted and the other cells keep theirs. -/
theorem stageN_spec {X Z J W : Type*} [AddCommGroup X] (pos : W → J → Z) (sh : W → J → X)
    (p : (Z → X) × (J → X)) (w : W) :
    ∃ p' : (Z → X) × (J → X), stageN pos sh (p, w) = (p', w) ∧
      (Function.Injective (pos w) → (∀ a, p'.2 a = sh w a + p.1 (pos w a)) ∧
        ∀ z, (∀ a, pos w a ≠ z) → p'.1 z = p.1 z) :=
  ⟨(stageN pos sh (p, w)).1, stageN_eq_mk pos sh p w, fun hw ↦ by
    rw [stageN_apply_of_injective pos sh p w hw]
    exact ⟨fun a ↦ xch_snd _ hw _ p a, fun z hz ↦ xch_fst_of_notMem _ hw _ p hz⟩⟩

/-- The points outside a set, counted. -/
theorem sum_ite_mem_zero_one_eq {α : Type*} [Fintype α] [DecidableEq α] (G : Finset α) :
    ∑ a, (if a ∈ G then 0 else 1) = Fintype.card α - G.card := by
  have h1 : ∑ a, (if a ∈ G then 1 else 0) = G.card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.card_eq_sum_ones]
  have h2 : ∑ a, ((if a ∈ G then 0 else 1) + (if a ∈ G then 1 else 0)) = Fintype.card α := by
    calc ∑ a, ((if a ∈ G then 0 else 1) + (if a ∈ G then 1 else 0)) = ∑ _a : α, 1 :=
          Finset.sum_congr rfl fun a _ ↦ by split_ifs <;> rfl
      _ = Fintype.card α := by simp
  rw [Finset.sum_add_distrib, h1] at h2
  omega

/-- A count over four coordinates whose sum over the second is at most `c`. -/
theorem card_mul_sum4_le_snd {Ω S K : Type*} [Fintype Ω] [Fintype S] [Fintype K]
    (f : Ω → S → K → K → ℕ) (c : ℕ) (h : ∀ ω k k', ∑ s, f ω s k k' ≤ c) :
    Fintype.card S * ∑ ω, ∑ s, ∑ k, ∑ k', f ω s k k' ≤
      Fintype.card Ω * Fintype.card S * (Fintype.card K * Fintype.card K) * c := by
  calc Fintype.card S * ∑ ω, ∑ s, ∑ k, ∑ k', f ω s k k'
      = Fintype.card S * ∑ ω, ∑ k, ∑ k', ∑ s, f ω s k k' := by
        rw [Finset.sum_congr rfl fun ω _ ↦ sum_comm_three fun s k k' ↦ f ω s k k']
    _ ≤ Fintype.card S * ∑ _ω : Ω, ∑ _k : K, ∑ _k' : K, c := by
        gcongr with ω _ k _ k' _
        exact h ω k k'
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-- **Counts resampling a coordinate of the last two.** Terms `u` bounded on resampling the
coordinate `a` of the third argument and `v` on resampling that of the fourth, summed over `a`. -/
theorem card_mul_sum4_le_upd {Ω S J B : Type*} [Fintype Ω] [Fintype S] [Fintype J] [DecidableEq J]
    [Fintype B] (u v : Ω → S → (J → B) → (J → B) → J → ℕ) (c d : ℕ)
    (hu : ∀ ω s k' a k, ∑ w, u ω s (Function.update k a w) k' a ≤ c)
    (hv : ∀ ω s k a k', ∑ w, v ω s k (Function.update k' a w) a ≤ d) :
    Fintype.card B * ∑ ω, ∑ s, ∑ k, ∑ k', ∑ a, (u ω s k k' a + v ω s k k' a) ≤
      Fintype.card Ω * Fintype.card S * (Fintype.card (J → B) * Fintype.card (J → B)) *
        (Fintype.card J * (c + d)) := by
  have h1 : ∀ ω s, Fintype.card B * ∑ k, ∑ k', ∑ a, u ω s k k' a ≤
      Fintype.card (J → B) * Fintype.card (J → B) * (Fintype.card J * c) := fun ω s ↦ by
    calc Fintype.card B * ∑ k, ∑ k', ∑ a, u ω s k k' a
        = ∑ k', ∑ a, Fintype.card B * ∑ k, u ω s k k' a := by
          rw [sum_comm_three fun k k' a ↦ u ω s k k' a]
          simp only [Finset.mul_sum]
      _ ≤ ∑ _k' : J → B, ∑ _a : J, Fintype.card (J → B) * c :=
          Finset.sum_le_sum fun k' _ ↦ Finset.sum_le_sum fun a _ ↦
            card_mul_sum_le_of_update (fun k ↦ u ω s k k' a) a c fun k ↦ hu ω s k' a k
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  have h2 : ∀ ω s, Fintype.card B * ∑ k, ∑ k', ∑ a, v ω s k k' a ≤
      Fintype.card (J → B) * Fintype.card (J → B) * (Fintype.card J * d) := fun ω s ↦ by
    calc Fintype.card B * ∑ k, ∑ k', ∑ a, v ω s k k' a
        = ∑ k, ∑ a, Fintype.card B * ∑ k', v ω s k k' a := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ ∑ _k : J → B, ∑ _a : J, Fintype.card (J → B) * d :=
          Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun a _ ↦
            card_mul_sum_le_of_update (fun k' ↦ v ω s k k' a) a d fun k' ↦ hv ω s k a k'
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  calc Fintype.card B * ∑ ω, ∑ s, ∑ k, ∑ k', ∑ a, (u ω s k k' a + v ω s k k' a)
      = ∑ ω, ∑ s, (Fintype.card B * ∑ k, ∑ k', ∑ a, u ω s k k' a +
          Fintype.card B * ∑ k, ∑ k', ∑ a, v ω s k k' a) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    _ ≤ ∑ _ω : Ω, ∑ _s : S,
          (Fintype.card (J → B) * Fintype.card (J → B) * (Fintype.card J * c) +
            Fintype.card (J → B) * Fintype.card (J → B) * (Fintype.card J * d)) :=
        Finset.sum_le_sum fun ω _ ↦ Finset.sum_le_sum fun s _ ↦ add_le_add (h1 ω s) (h2 ω s)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-- A count of a function of an equivalence of the first coordinate. -/
theorem card_mul_sum_fst_equiv_le {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (e : α ≃ β) (g : β → ℕ) (P N : ℕ) (h : P * ∑ x, g x ≤ Fintype.card α * N) :
    P * ∑ θ : α × γ, g (e θ.1) ≤ Fintype.card (α × γ) * N := by
  have h1 : ∑ θ : α × γ, g (e θ.1) = Fintype.card γ • ∑ a, g (e a) :=
    sum_fst_eq (fun a ↦ g (e a))
  have h2 : ∑ a, g (e a) = ∑ x, g x := Fintype.sum_equiv e _ _ fun _ ↦ rfl
  rw [h1, h2, smul_eq_mul, Fintype.card_prod]
  calc P * (Fintype.card γ * ∑ x, g x) = Fintype.card γ * (P * ∑ x, g x) := by ring
    _ ≤ Fintype.card γ * (Fintype.card α * N) := Nat.mul_le_mul_left _ h
    _ = Fintype.card α * Fintype.card γ * N := by ring

/-- A count of a function of an equivalence. -/
theorem card_mul_sum_equiv_le {Θ T : Type*} [Fintype Θ] [Fintype T] (e : Θ ≃ T) (g : T → ℕ)
    (P N : ℕ) (h : P * ∑ y, g y ≤ Fintype.card T * N) :
    P * ∑ θ, g (e θ) ≤ Fintype.card Θ * N := by
  have h1 : ∑ θ, g (e θ) = ∑ y, g y := Fintype.sum_equiv e _ _ fun _ ↦ rfl
  rw [h1, Fintype.card_congr e]
  exact h

/-- A count over the second coordinate of a product as a fraction of the first. -/
theorem natCast_smul_eq_card_mul {α γ : Type*} [Fintype α] [Fintype γ] [Nonempty α] (m : ℕ) :
    ((Fintype.card γ • m : ℕ) : ℝ≥0∞) =
      Fintype.card (α × γ) * ((Fintype.card α : ℝ≥0∞)⁻¹ * m) := by
  have hα : (Fintype.card α : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [smul_eq_mul, Nat.cast_mul, Fintype.card_prod, Nat.cast_mul, ← mul_assoc,
    mul_comm (Fintype.card α : ℝ≥0∞) (Fintype.card γ : ℝ≥0∞), mul_assoc _ (Fintype.card α : ℝ≥0∞),
    ENNReal.mul_inv_cancel hα (ENNReal.natCast_ne_top _), mul_one]

/-- Splitting a sum of parts. -/
theorem sum_add_sum_eq {Θ ι : Type*} [Fintype Θ] [Fintype ι] (p c : Θ → ℕ) (d e : ι → Θ → ℕ) :
    ∑ θ, (p θ + (c θ + ∑ i, (d i θ + e i θ))) =
      ∑ θ, p θ + (∑ θ, c θ + ∑ i, (∑ θ, d i θ + ∑ θ, e i θ)) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.sum_add_distrib]

end generic

/-! ## Collisions of rates, over abstract types -/

section collide

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

open scoped Classical

omit [DecidableEq Z] in
/-- **Two distinct cells rarely share their rate**: for a permutation with rate counts at most `G`,
at most `G / |Z|` of the keys `k`. -/
theorem card_mul_sum_rateOf_eq_le (π : Equiv.Perm (X × Z)) (G : ℕ) (hG : PermGood π G)
    {b b' : X} (hb : b ≠ b') :
    Fintype.card Z * ∑ k : X → Z, ∑ _k' : X → Z,
        (if rateOf k π b = rateOf k π b' then 1 else 0) ≤
      Fintype.card (X → Z) * Fintype.card (X → Z) * G := by
  have h1 : Fintype.card Z * ∑ k : X → Z, (if rateOf k π b = rateOf k π b' then 1 else 0) ≤
      Fintype.card (X → Z) * G :=
    card_mul_sum_le_of_update _ b G fun k ↦ by
      simp only [rateOf, Function.update_self, Function.update_of_ne hb.symm]
      rw [← Finset.card_filter]
      exact hG.rate b _
  calc Fintype.card Z * ∑ k : X → Z, ∑ _k' : X → Z,
        (if rateOf k π b = rateOf k π b' then 1 else 0)
      = Fintype.card (X → Z) *
          (Fintype.card Z * ∑ k : X → Z, (if rateOf k π b = rateOf k π b' then 1 else 0)) := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.mul_sum]
        ring
    _ ≤ Fintype.card (X → Z) * (Fintype.card (X → Z) * G) := Nat.mul_le_mul_left _ h1
    _ = _ := by ring

/-- **Distinct cells rarely collide in rate**: for a permutation with rate counts at most `G`, the
rates of the cells `cell a` (distinct) collide for at most `|A|² G / |Z|` of the keys. -/
theorem card_mul_sum_not_injective_rateOf_le {A : Type*} [Fintype A] [DecidableEq A]
    (π : Equiv.Perm (X × Z)) (G : ℕ) (cell : A → X) (hcell : Function.Injective cell) :
    Fintype.card Z * ∑ k : X → Z, ∑ _k' : X → Z,
        (if PermGood π G ∧ ¬Function.Injective (fun a ↦ rateOf k π (cell a)) then 1 else 0) ≤
      Fintype.card (X → Z) * Fintype.card (X → Z) * (Fintype.card A * Fintype.card A * G) := by
  by_cases hG : PermGood π G
  · have hle : ∀ k : X → Z,
        (if PermGood π G ∧ ¬Function.Injective (fun a ↦ rateOf k π (cell a)) then 1 else 0) ≤
          ∑ a : A, ∑ b : A,
            (if a ≠ b ∧ rateOf k π (cell a) = rateOf k π (cell b) then 1 else 0) := by
      intro k
      split_ifs with h
      · obtain ⟨-, hn⟩ := h
        simp only [Function.Injective, not_forall] at hn
        obtain ⟨a, b, hab, hne⟩ := hn
        calc 1 = (if a ≠ b ∧ rateOf k π (cell a) = rateOf k π (cell b) then 1 else 0) :=
              (ite_eq_left ⟨hne, hab⟩).symm
          _ ≤ ∑ b' : A,
              (if a ≠ b' ∧ rateOf k π (cell a) = rateOf k π (cell b') then 1 else 0) :=
              Finset.single_le_sum (f := fun b' ↦
                (if a ≠ b' ∧ rateOf k π (cell a) = rateOf k π (cell b') then 1 else 0))
                (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ b)
          _ ≤ _ := Finset.single_le_sum (f := fun a' ↦ ∑ b' : A,
              (if a' ≠ b' ∧ rateOf k π (cell a') = rateOf k π (cell b') then 1 else 0))
              (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
      · exact Nat.zero_le _
    have hab : ∀ a b : A, Fintype.card Z * ∑ k : X → Z, ∑ _k' : X → Z,
        (if a ≠ b ∧ rateOf k π (cell a) = rateOf k π (cell b) then 1 else 0) ≤
          Fintype.card (X → Z) * Fintype.card (X → Z) * G := by
      intro a b
      by_cases h : a = b
      · simp [h]
      · have hc := card_mul_sum_rateOf_eq_le π G hG (hcell.ne h)
        simpa only [ne_eq, h, not_false_eq_true, true_and] using hc
    calc Fintype.card Z * ∑ k : X → Z, ∑ _k' : X → Z,
          (if PermGood π G ∧ ¬Function.Injective (fun a ↦ rateOf k π (cell a)) then 1 else 0)
        ≤ Fintype.card Z * ∑ k : X → Z, ∑ _k' : X → Z, ∑ a : A, ∑ b : A,
            (if a ≠ b ∧ rateOf k π (cell a) = rateOf k π (cell b) then 1 else 0) := by
          gcongr with k _ k' _
          exact hle k
      _ = ∑ a : A, ∑ b : A, Fintype.card Z * ∑ k : X → Z, ∑ _k' : X → Z,
            (if a ≠ b ∧ rateOf k π (cell a) = rateOf k π (cell b) then 1 else 0) := by
          rw [sum_comm_four]
          simp only [Finset.mul_sum]
      _ ≤ ∑ _a : A, ∑ _b : A, Fintype.card (X → Z) * Fintype.card (X → Z) * G :=
          Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ hab a b
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  · simp [hG]

end collide

/-! ## The coin stages on leanXMSS tables -/

section coin

open HashSig LeanXmss

/-- The coin slots of the labels `J`: their `k`-coins, `k'`-coins and `h`-coins. -/
abbrev CoinSlots (J : Type) : Type := (J → Z) × (J → Z) × (J → X)

/-- The tables with the scheme seed's slots and the coin slots. -/
abbrev CTab (J : Type) : Type := Tab × CoinSlots J

/-- The public part with the coin slots. -/
abbrev CPub (J : Type) : Type := Pub × CoinSlots J

/-- The public slots of `Pub`. -/
abbrev PubSlots : Type := (Fin 832 → ZMod 2) × X × (CsIdx → X)

/-- The data the `k`- and `k'`-stages keep: `h`, the other key, `π`, `S₀`, the public slots, the
other two coin slots, and the scheme seed. -/
abbrev RestCK (J : Type) : Type :=
  (Z → X) × (X → Z) × Equiv.Perm (X × Z) × MasterSeed × PubSlots × (J → Z) × (J → X) × MasterSeed

/-- The data the `h`-stage keeps: `k`, `k'`, `π`, `S₀`, the public slots, the `k`- and
`k'`-coins, and the scheme seed. -/
abbrev RestCH (J : Type) : Type :=
  (X → Z) × (X → Z) × Equiv.Perm (X × Z) × MasterSeed × PubSlots × (J → Z) × (J → Z) × MasterSeed

variable {J : Type}

/-- The `k`-stage's view: `k` with the `k`-coins, and the rest. -/
def shufK : CPub J × MasterSeed ≃ ((X → Z) × (J → Z)) × RestCK J where
  toFun x := ((x.1.1.1.keys.2.1, x.1.2.1), (x.1.1.1.keys.1, x.1.1.1.keys.2.2, x.1.1.1.perm,
    x.1.1.1.masterSeed, x.1.1.2, x.1.2.2.1, x.1.2.2.2, x.2))
  invFun y := (((⟨(y.2.1, y.1.1, y.2.2.1), y.2.2.2.1, y.2.2.2.2.1⟩, y.2.2.2.2.2.1),
    (y.1.2, y.2.2.2.2.2.2.1, y.2.2.2.2.2.2.2.1)), y.2.2.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `k'`-stage's view: `k'` with the `k'`-coins, and the rest. -/
def shufK' : CPub J × MasterSeed ≃ ((X → Z) × (J → Z)) × RestCK J where
  toFun x := ((x.1.1.1.keys.2.2, x.1.2.2.1), (x.1.1.1.keys.1, x.1.1.1.keys.2.1, x.1.1.1.perm,
    x.1.1.1.masterSeed, x.1.1.2, x.1.2.1, x.1.2.2.2, x.2))
  invFun y := (((⟨(y.2.1, y.2.2.1, y.1.1), y.2.2.2.1, y.2.2.2.2.1⟩, y.2.2.2.2.2.1),
    (y.2.2.2.2.2.2.1, y.1.2, y.2.2.2.2.2.2.2.1)), y.2.2.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `h`-stage's view: `h` with the `h`-coins, and the rest. -/
def shufH : CPub J × MasterSeed ≃ ((Z → X) × (J → X)) × RestCH J where
  toFun x := ((x.1.1.1.keys.1, x.1.2.2.2), (x.1.1.1.keys.2.1, x.1.1.1.keys.2.2, x.1.1.1.perm,
    x.1.1.1.masterSeed, x.1.1.2, x.1.2.1, x.1.2.2.1, x.2))
  invFun y := (((⟨(y.1.1, y.2.1, y.2.2.1), y.2.2.2.1, y.2.2.2.2.1⟩, y.2.2.2.2.2.1),
    (y.2.2.2.2.2.2.1, y.2.2.2.2.2.2.2.1, y.1.2)), y.2.2.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem shufK_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (ps : PubSlots) (kc k'c : J → Z) (hc : J → X) (S : MasterSeed) :
    shufK (((⟨(h, k, k'), π, S₀⟩, ps), (kc, k'c, hc)), S) =
      ((k, kc), (h, k', π, S₀, ps, k'c, hc, S)) :=
  rfl

theorem shufK_symm_apply (p : (X → Z) × (J → Z)) (h : Z → X) (k' : X → Z)
    (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) (ps : PubSlots) (k'c : J → Z) (hc : J → X)
    (S : MasterSeed) :
    shufK.symm (p, (h, k', π, S₀, ps, k'c, hc, S)) =
      (((⟨(h, p.1, k'), π, S₀⟩, ps), (p.2, k'c, hc)), S) :=
  rfl

theorem shufK'_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (ps : PubSlots) (kc k'c : J → Z) (hc : J → X) (S : MasterSeed) :
    shufK' (((⟨(h, k, k'), π, S₀⟩, ps), (kc, k'c, hc)), S) =
      ((k', k'c), (h, k, π, S₀, ps, kc, hc, S)) :=
  rfl

theorem shufK'_symm_apply (p : (X → Z) × (J → Z)) (h : Z → X) (k : X → Z)
    (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) (ps : PubSlots) (kc : J → Z) (hc : J → X)
    (S : MasterSeed) :
    shufK'.symm (p, (h, k, π, S₀, ps, kc, hc, S)) =
      (((⟨(h, k, p.1), π, S₀⟩, ps), (kc, p.2, hc)), S) :=
  rfl

theorem shufH_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (ps : PubSlots) (kc k'c : J → Z) (hc : J → X) (S : MasterSeed) :
    shufH (((⟨(h, k, k'), π, S₀⟩, ps), (kc, k'c, hc)), S) =
      ((h, hc), (k, k', π, S₀, ps, kc, k'c, S)) :=
  rfl

theorem shufH_symm_apply (p : (Z → X) × (J → X)) (k k' : X → Z) (π : Equiv.Perm (X × Z))
    (S₀ : MasterSeed) (ps : PubSlots) (kc k'c : J → Z) (S : MasterSeed) :
    shufH.symm (p, (k, k', π, S₀, ps, kc, k'c, S)) =
      (((⟨(p.1, k, k'), π, S₀⟩, ps), (kc, k'c, p.2)), S) :=
  rfl

variable (cell : J → PublicParameter → MasterSeed → X)

/-- The `k`-stage's cells: the labels' first blocks, for the parameter in slot `1` and the scheme
seed. -/
def posK (w : RestCK J) (a : J) : X :=
  cell a (trunc128 w.2.2.2.2.1.2.1) w.2.2.2.2.2.2.2

/-- The `k'`-stage's cells: the rates of the labels' first blocks with the `k`-coins. -/
def posK' (w : RestCK J) (a : J) : X :=
  (w.2.2.1 (cell a (trunc128 w.2.2.2.2.1.2.1) w.2.2.2.2.2.2.2, w.2.2.2.2.2.1 a)).1

/-- The `h`-stage's cells: the capacities of the labels' first blocks with the `k`- and
`k'`-slots. -/
def posH (w : RestCH J) (a : J) : Z :=
  (w.2.2.1 (cell a (trunc128 w.2.2.2.2.1.2.1) w.2.2.2.2.2.2.2, w.2.2.2.2.2.1 a)).2 +
    w.2.2.2.2.2.2.1 a

/-- The `h`-stage's shifts: the rates of the labels' first blocks with the `k`-slots. -/
def shH (w : RestCH J) (a : J) : X :=
  (w.2.2.1 (cell a (trunc128 w.2.2.2.2.1.2.1) w.2.2.2.2.2.2.2, w.2.2.2.2.2.1 a)).1

/-- **The `k`-stage**: `k` at the labels' first blocks takes the `k`-coin slots, which take its
values, when the blocks are distinct. -/
noncomputable def stageK : CPub J × MasterSeed ≃ CPub J × MasterSeed :=
  (shufK.trans (stageN (posK cell) fun _ _ ↦ 0)).trans shufK.symm

/-- **The `k'`-stage**: `k'` at the coin rates takes the `k'`-coin slots, which take its values,
when the rates are distinct. -/
noncomputable def stageK' : CPub J × MasterSeed ≃ CPub J × MasterSeed :=
  (shufK'.trans (stageN (posK' cell) fun _ _ ↦ 0)).trans shufK'.symm

/-- **The `h`-stage**: `h` at the path capacities takes the `h`-slots, which take the blocks'
outputs (rate plus `h`), when the capacities are distinct. -/
noncomputable def stageH : CPub J × MasterSeed ≃ CPub J × MasterSeed :=
  (shufH.trans (stageN (posH cell) (shH cell))).trans shufH.symm

theorem stageK_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (ps : PubSlots) (kc k'c : J → Z) (hc : J → X) (S : MasterSeed) :
    ∃ (k₂ : X → Z) (kc₂ : J → Z),
      stageK cell (((⟨(h, k, k'), π, S₀⟩, ps), (kc, k'c, hc)), S) =
        (((⟨(h, k₂, k'), π, S₀⟩, ps), (kc₂, k'c, hc)), S) ∧
      (Function.Injective (fun a ↦ cell a (trunc128 ps.2.1) S) →
        (∀ a, kc₂ a = k (cell a (trunc128 ps.2.1) S)) ∧
          ∀ x, (∀ a, cell a (trunc128 ps.2.1) S ≠ x) → k₂ x = k x) := by
  obtain ⟨p', hp', hsp⟩ := stageN_spec (posK cell) (fun _ _ ↦ (0 : Z)) (k, kc)
    (h, k', π, S₀, ps, k'c, hc, S)
  refine ⟨p'.1, p'.2, ?_, fun hinj ↦ ?_⟩
  · rw [stageK, Equiv.trans_apply, Equiv.trans_apply, shufK_apply, hp', shufK_symm_apply]
  · obtain ⟨h1, h2⟩ := hsp hinj
    exact ⟨fun a ↦ (h1 a).trans (zero_add _), h2⟩

theorem stageK'_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (ps : PubSlots) (kc k'c : J → Z) (hc : J → X) (S : MasterSeed) :
    ∃ (k'₂ : X → Z) (k'c₂ : J → Z),
      stageK' cell (((⟨(h, k, k'), π, S₀⟩, ps), (kc, k'c, hc)), S) =
        (((⟨(h, k, k'₂), π, S₀⟩, ps), (kc, k'c₂, hc)), S) ∧
      (Function.Injective (fun a ↦ (π (cell a (trunc128 ps.2.1) S, kc a)).1) →
        (∀ a, k'c₂ a = k' (π (cell a (trunc128 ps.2.1) S, kc a)).1) ∧
          ∀ x, (∀ a, (π (cell a (trunc128 ps.2.1) S, kc a)).1 ≠ x) → k'₂ x = k' x) := by
  obtain ⟨p', hp', hsp⟩ := stageN_spec (posK' cell) (fun _ _ ↦ (0 : Z)) (k', k'c)
    (h, k, π, S₀, ps, kc, hc, S)
  refine ⟨p'.1, p'.2, ?_, fun hinj ↦ ?_⟩
  · rw [stageK', Equiv.trans_apply, Equiv.trans_apply, shufK'_apply, hp', shufK'_symm_apply]
  · obtain ⟨h1, h2⟩ := hsp hinj
    exact ⟨fun a ↦ (h1 a).trans (zero_add _), h2⟩

theorem stageH_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (ps : PubSlots) (kc k'c : J → Z) (hc : J → X) (S : MasterSeed) :
    ∃ (h₂ : Z → X) (hc₂ : J → X),
      stageH cell (((⟨(h, k, k'), π, S₀⟩, ps), (kc, k'c, hc)), S) =
        (((⟨(h₂, k, k'), π, S₀⟩, ps), (kc, k'c, hc₂)), S) ∧
      (Function.Injective (fun a ↦ (π (cell a (trunc128 ps.2.1) S, kc a)).2 + k'c a) →
        (∀ a, hc₂ a = (π (cell a (trunc128 ps.2.1) S, kc a)).1 +
          h ((π (cell a (trunc128 ps.2.1) S, kc a)).2 + k'c a)) ∧
          ∀ z, (∀ a, (π (cell a (trunc128 ps.2.1) S, kc a)).2 + k'c a ≠ z) → h₂ z = h z) := by
  obtain ⟨p', hp', hsp⟩ := stageN_spec (posH cell) (shH cell) (h, hc)
    (k, k', π, S₀, ps, kc, k'c, S)
  refine ⟨p'.1, p'.2, ?_, fun hinj ↦ ?_⟩
  · rw [stageH, Equiv.trans_apply, Equiv.trans_apply, shufH_apply, hp', shufH_symm_apply]
  · obtain ⟨h1, h2⟩ := hsp hinj
    exact ⟨fun a ↦ h1 a, h2⟩

/-- The three coin stages. -/
noncomputable def coinStages : CPub J × MasterSeed ≃ CPub J × MasterSeed :=
  (stageK cell).trans ((stageK' cell).trans (stageH cell))

/-- **The coin stages**: they keep `π`, `S₀`, the public slots and the scheme seed; when the
labels' first blocks, their rates and their capacities are each distinct, the slots take `k`, `k'`
at the paths' cells and the blocks' outputs, and the keys keep their values off the paths' cells. -/
theorem coinStages_spec (L : HonestTable) (ps : PubSlots) (cs : CoinSlots J) (S : MasterSeed) :
    ∃ (h₂ : Z → X) (k₂ k'₂ : X → Z) (cs₂ : CoinSlots J),
      coinStages cell (((L, ps), cs), S) =
        (((⟨(h₂, k₂, k'₂), L.perm, L.masterSeed⟩, ps), cs₂), S) ∧
      ∀ P, trunc128 ps.2.1 = P →
        Function.Injective (fun a ↦ cell a P S) →
        Function.Injective (fun a ↦ rateOf L.keys.2.1 L.perm (cell a P S)) →
        Function.Injective (fun a ↦ capOf L.keys.2.1 L.keys.2.2 L.perm (cell a P S)) →
        (∀ a, cs₂.1 a = L.keys.2.1 (cell a P S)) ∧
        (∀ a, cs₂.2.1 a = L.keys.2.2 (rateOf L.keys.2.1 L.perm (cell a P S))) ∧
        (∀ a, cs₂.2.2 a = rateOf L.keys.2.1 L.perm (cell a P S) +
          L.keys.1 (capOf L.keys.2.1 L.keys.2.2 L.perm (cell a P S))) ∧
        (∀ x, (∀ a, cell a P S ≠ x) → k₂ x = L.keys.2.1 x) ∧
        (∀ x, (∀ a, (L.perm (cell a P S, cs₂.1 a)).1 ≠ x) → k'₂ x = L.keys.2.2 x) ∧
        ∀ z, (∀ a, (L.perm (cell a P S, cs₂.1 a)).2 + cs₂.2.1 a ≠ z) → h₂ z = L.keys.1 z := by
  obtain ⟨⟨h, k, k'⟩, π, S₀⟩ := L
  obtain ⟨kc, k'c, hc⟩ := cs
  obtain ⟨k₂, kc₂, eK, fK⟩ := stageK_spec cell h k k' π S₀ ps kc k'c hc S
  obtain ⟨k'₂, k'c₂, eK', fK'⟩ := stageK'_spec cell h k₂ k' π S₀ ps kc₂ k'c hc S
  obtain ⟨h₂, hc₂, eH, fH⟩ := stageH_spec cell h k₂ k'₂ π S₀ ps kc₂ k'c₂ hc S
  refine ⟨h₂, k₂, k'₂, (kc₂, k'c₂, hc₂), ?_, fun P hP hx hr hcap ↦ ?_⟩
  · rw [coinStages, Equiv.trans_apply, Equiv.trans_apply, eK, eK', eH]
  · subst hP
    obtain ⟨fK1, fK2⟩ := fK hx
    have hpr : ∀ a, (π (cell a (trunc128 ps.2.1) S, kc₂ a)).1 =
        rateOf k π (cell a (trunc128 ps.2.1) S) := fun a ↦ by rw [fK1 a, rateOf]
    obtain ⟨fK'1, fK'2⟩ := fK' fun a b hab ↦ hr ((hpr a).symm.trans (hab.trans (hpr b)))
    have hpc : ∀ a, (π (cell a (trunc128 ps.2.1) S, kc₂ a)).2 + k'c₂ a =
        capOf k k' π (cell a (trunc128 ps.2.1) S) := fun a ↦ by rw [fK'1 a, fK1 a, capOf]
    obtain ⟨fH1, fH2⟩ := fH fun a b hab ↦ hcap ((hpc a).symm.trans (hab.trans (hpc b)))
    exact ⟨fK1, fun a ↦ (fK'1 a).trans (congrArg k' (hpr a)),
      fun a ↦ (fH1 a).trans (congrArg₂ (· + ·) (hpr a) (congrArg h (hpc a))), fK2, fK'2, fH2⟩

/-- The public part and the scheme seed reordered with the coin slots. -/
def reorderC : (Pub × MasterSeed) × CoinSlots J ≃ CPub J × MasterSeed where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun y := ((y.1.1, y.2), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The staged swap with the coin stages**: the table with the scheme seed's and the coin slots
as the public part with the coin slots, and the scheme seed. -/
noncomputable def coinSplit : CTab J ≃ CPub J × MasterSeed :=
  ((schemeSplit.prodCongr (Equiv.refl (CoinSlots J))).trans reorderC).trans (coinStages cell)

theorem coinSplit_apply (θ : CTab J) :
    coinSplit cell θ = coinStages cell
      ((((schemeSplit θ.1).1.1, (schemeSplit θ.1).1.2), θ.2), (schemeSplit θ.1).2) :=
  rfl

/-- The `k`-cells of the coin paths in a table: the labels' first blocks. -/
def coinCellK (L : HonestTable) (a : J) : X :=
  cell a L.param L.seed

/-- The `k'`-cells of the coin paths in a table: the rates of the labels' first blocks. -/
def coinCellK' (L : HonestTable) (a : J) : X :=
  rateOf L.keys.2.1 L.perm (coinCellK cell L a)

/-- The `h`-cells of the coin paths in a table: the capacities of the labels' first blocks. -/
def coinCellH (L : HonestTable) (a : J) : Z :=
  capOf L.keys.2.1 L.keys.2.2 L.perm (coinCellK cell L a)

/-- The `k`-cells of the coin paths read off the public part and the scheme seed. -/
def pubCellK (y : CPub J × MasterSeed) (a : J) : X :=
  cell a (pubParam y.1.1) y.2

/-- The `k'`-cells of the coin paths read off the public part (with the `k`-coins) and the
scheme seed. -/
def pubCellK' (y : CPub J × MasterSeed) (a : J) : X :=
  (y.1.1.1.perm (pubCellK cell y a, y.1.2.1 a)).1

/-- The `h`-cells of the coin paths read off the public part (with the `k`- and `k'`-coins) and
the scheme seed. -/
def pubCellH (y : CPub J × MasterSeed) (a : J) : Z :=
  (y.1.1.1.perm (pubCellK cell y a, y.1.2.1 a)).2 + y.1.2.2.1 a

/-- The coin rates of the staged swap's coordinates are distinct. -/
abbrev RateInj (x : Pub × MasterSeed) : Prop :=
  Function.Injective fun a ↦ rateOf x.1.1.keys.2.1 x.1.1.perm (cell a (pubParam x.1) x.2)

/-- The capacities of the hidden cells and the coin cells of the staged swap's coordinates are
distinct. -/
abbrev CapInj (x : Pub × MasterSeed) : Prop :=
  Function.Injective fun c ↦ capOf x.1.1.keys.2.1 x.1.1.keys.2.2 x.1.1.perm
    (Sum.elim (hidCell (pubParam x.1) x.2 x.1.1.masterSeed) (fun a ↦ cell a (pubParam x.1) x.2) c)

/-- **No collisions** of the coin cells in the staged swap's coordinates. -/
def CollGood (x : Pub × MasterSeed) : Prop :=
  RateInj cell x ∧ CapInj cell x

variable {cell}

theorem CollGood.injective_cap {x : Pub × MasterSeed} (hx : CollGood cell x) :
    Function.Injective fun a ↦
      capOf x.1.1.keys.2.1 x.1.1.keys.2.2 x.1.1.perm (cell a (pubParam x.1) x.2) :=
  fun a b hab ↦ Sum.inr_injective (hx.2 (a₁ := Sum.inr a) (a₂ := Sum.inr b) hab)

theorem CollGood.injective_cell {x : Pub × MasterSeed} (hx : CollGood cell x) :
    Function.Injective fun a ↦ cell a (pubParam x.1) x.2 :=
  fun _ _ hab ↦ hx.injective_cap (congrArg (capOf x.1.1.keys.2.1 x.1.1.keys.2.2 x.1.1.perm) hab)

theorem CollGood.ne_posOf {x : Pub × MasterSeed} (hx : CollGood cell x) (a : J)
    (b : Option (Option CsIdx)) :
    capOf x.1.1.keys.2.1 x.1.1.keys.2.2 x.1.1.perm (cell a (pubParam x.1) x.2) ≠
      posOf x.1 x.2 b :=
  fun hab ↦ Sum.inr_ne_inl (hx.2 (a₁ := Sum.inr a) (a₂ := Sum.inl b) hab)

variable (cell)

theorem coinSplit_exists (θ : CTab J) : ∃ (h₂ : Z → X) (k₂ k'₂ : X → Z) (cs₂ : CoinSlots J),
    coinSplit cell θ = (((⟨(h₂, k₂, k'₂), (schemeSplit θ.1).1.1.perm,
      (schemeSplit θ.1).1.1.masterSeed⟩, (schemeSplit θ.1).1.2), cs₂), (schemeSplit θ.1).2) := by
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, -⟩ := coinStages_spec cell (schemeSplit θ.1).1.1
    (schemeSplit θ.1).1.2 θ.2 (schemeSplit θ.1).2
  exact ⟨h₂, k₂, k'₂, cs₂, (coinSplit_apply cell θ).trans hE⟩

/-- **The hidden coordinate is the scheme seed.** -/
theorem coinSplit_snd (θ : CTab J) : (coinSplit cell θ).2 = θ.1.1.seed := by
  obtain ⟨_, _, _, _, hE⟩ := coinSplit_exists cell θ
  rw [hE]
  exact schemeSplit_snd θ.1

theorem coinSplit_perm (θ : CTab J) : (coinSplit cell θ).1.1.1.perm = θ.1.1.perm := by
  obtain ⟨_, _, _, _, hE⟩ := coinSplit_exists cell θ
  rw [hE]
  exact schemeSplit_perm θ.1

theorem coinSplit_masterSeed (θ : CTab J) :
    (coinSplit cell θ).1.1.1.masterSeed = θ.1.1.masterSeed := by
  obtain ⟨_, _, _, _, hE⟩ := coinSplit_exists cell θ
  rw [hE]
  exact schemeSplit_masterSeed θ.1

/-- The coin stages keep the public slots. -/
theorem coinSplit_slots (θ : CTab J) : (coinSplit cell θ).1.1.2 = (schemeSplit θ.1).1.2 := by
  obtain ⟨_, _, _, _, hE⟩ := coinSplit_exists cell θ
  rw [hE]

/-- **The slots hold the table's path values**: when the hidden capacities are distinct and the
path cells do not collide, the `k`- and `k'`-slots hold `k` and `k'` of the table at the paths'
cells, and the `h`-slots the blocks' outputs. -/
theorem coinSplit_transfer (θ : CTab J)
    (hinj : Function.Injective (posOf (schemeSplit θ.1).1 (schemeSplit θ.1).2))
    (hcoll : CollGood cell (schemeSplit θ.1)) :
    (∀ a, (coinSplit cell θ).1.2.1 a = θ.1.1.keys.2.1 (coinCellK cell θ.1.1 a)) ∧
      (∀ a, (coinSplit cell θ).1.2.2.1 a = θ.1.1.keys.2.2 (coinCellK' cell θ.1.1 a)) ∧
      ∀ a, (coinSplit cell θ).1.2.2.2 a =
        rateOf θ.1.1.keys.2.1 θ.1.1.perm (coinCellK cell θ.1.1 a) +
          θ.1.1.keys.1 (coinCellH cell θ.1.1 a) := by
  obtain ⟨hP, -, hh⟩ := schemeSplit_transfer θ.1 hinj
  have hS := schemeSplit_snd θ.1
  have hk := schemeSplit_keys_snd θ.1
  have hπ := schemeSplit_perm θ.1
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, f⟩ := coinStages_spec cell (schemeSplit θ.1).1.1
    (schemeSplit θ.1).1.2 θ.2 (schemeSplit θ.1).2
  obtain ⟨f1, f2, f3, -, -, -⟩ := f (pubParam (schemeSplit θ.1).1) rfl hcoll.injective_cell
    hcoll.1 hcoll.injective_cap
  rw [coinSplit_apply, hE]
  refine ⟨fun a ↦ (f1 a).trans ?_, fun a ↦ (f2 a).trans ?_, fun a ↦ (f3 a).trans ?_⟩
  · rw [hk, hP, hS]
    rfl
  · rw [hk, hπ, hP, hS]
    rfl
  · rw [hh _ fun b hb ↦ hcoll.ne_posOf a b hb.symm, hk, hπ, hP, hS]
    rfl

/-- The keys of the public part agree with those after `schemeSplit` off the coin cells read off
the public part. -/
theorem coinSplit_keys_eq (θ : CTab J) (hcoll : CollGood cell (schemeSplit θ.1)) :
    (∀ x, (∀ a, pubCellK cell (coinSplit cell θ) a ≠ x) →
        (coinSplit cell θ).1.1.1.keys.2.1 x = (schemeSplit θ.1).1.1.keys.2.1 x) ∧
      (∀ x, (∀ a, pubCellK' cell (coinSplit cell θ) a ≠ x) →
        (coinSplit cell θ).1.1.1.keys.2.2 x = (schemeSplit θ.1).1.1.keys.2.2 x) ∧
      ∀ z, (∀ a, pubCellH cell (coinSplit cell θ) a ≠ z) →
        (coinSplit cell θ).1.1.1.keys.1 z = (schemeSplit θ.1).1.1.keys.1 z := by
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, f⟩ := coinStages_spec cell (schemeSplit θ.1).1.1
    (schemeSplit θ.1).1.2 θ.2 (schemeSplit θ.1).2
  obtain ⟨-, -, -, f4, f5, f6⟩ := f (pubParam (schemeSplit θ.1).1) rfl hcoll.injective_cell
    hcoll.1 hcoll.injective_cap
  rw [coinSplit_apply, hE]
  exact ⟨f4, f5, f6⟩

/-! ### The good set -/

variable {ι : Type} {β : ι → Type}

/-- No computation `Q i` from the public part reads a coin cell read off the public part. -/
def ReadGood (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (y : CPub J × MasterSeed) : Prop :=
  ∀ i a, pubCellK cell y a ∉ kCells (pubData Q y.1.1 i).2 ∧
    pubCellK' cell y a ∉ k'Cells (pubData Q y.1.1 i).2 ∧
    pubCellH cell y a ∉ hCells (pubData Q y.1.1 i).2

variable [Fintype J] [DecidableEq J]

open scoped Classical in
/-- **The good set** of the coin stage: `schemeGood`, no collisions of the coin cells, and no
computation reading a coin cell. Irreducible: its membership does not unfold to the enumeration
of all tables. -/
@[irreducible]
noncomputable def coinGood
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    Finset (CTab J) :=
  Finset.univ.filter fun θ ↦
    GoodPS Q (schemeSplit θ.1) ∧ CollGood cell (schemeSplit θ.1) ∧ ReadGood cell Q (coinSplit cell θ)

variable {cell}

theorem mem_coinGood
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    {θ : CTab J} :
    θ ∈ coinGood cell Q ↔ GoodPS Q (schemeSplit θ.1) ∧ CollGood cell (schemeSplit θ.1) ∧
      ReadGood cell Q (coinSplit cell θ) := by
  unfold coinGood
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The coordinate fact**: on the good set, the slots of the public part hold the table's `k` and
`k'` at the paths' cells and the paths' outputs. -/
theorem coinSplit_coins
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    {θ : CTab J} (hθ : θ ∈ coinGood cell Q) :
    (∀ a, (coinSplit cell θ).1.2.1 a = θ.1.1.keys.2.1 (coinCellK cell θ.1.1 a)) ∧
      (∀ a, (coinSplit cell θ).1.2.2.1 a = θ.1.1.keys.2.2 (coinCellK' cell θ.1.1 a)) ∧
      ∀ a, (coinSplit cell θ).1.2.2.2 a =
        rateOf θ.1.1.keys.2.1 θ.1.1.perm (coinCellK cell θ.1.1 a) +
          θ.1.1.keys.1 (coinCellH cell θ.1.1 a) := by
  obtain ⟨⟨hinj, -⟩, hcoll, -⟩ := mem_coinGood.mp hθ
  exact coinSplit_transfer cell θ hinj hcoll

/-- On the good set, the parameter is read off the public part. -/
theorem pubParam_coinSplit
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    {θ : CTab J} (hθ : θ ∈ coinGood cell Q) : pubParam (coinSplit cell θ).1.1 = θ.1.1.param := by
  obtain ⟨⟨hinj, -⟩, -, -⟩ := mem_coinGood.mp hθ
  exact (congrArg (fun s : PubSlots ↦ trunc128 s.2.1) (coinSplit_slots cell θ)).trans
    (schemeSplit_transfer θ.1 hinj).1

/-- The randomizer base of label `a` read off the public part: its truncated `h`-slot. -/
def pubR0 (y : CPub J) (a : J) : Digest :=
  trunc128 (y.2.2.2 a)

/-- **The paths' hashes are public**: on the good set, the hash of a requested one-block input
(with first block `cell a P S`) is read off the `h`-slot of the public part. -/
theorem coinSplit_hash (inp : J → PublicParameter → MasterSeed → HashInput)
    (hinp : ∀ a P S, firstCell (inp a P S) = cell a P S) (hlen : ∀ a P S, (inp a P S).length < 136)
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    {θ : CTab J} (hθ : θ ∈ coinGood cell Q) (a : J) :
    θ.1.1.hash (inp a θ.1.1.param θ.1.1.seed) = out256 ((coinSplit cell θ).1.2.2.2 a) := by
  rw [hash_of_lt θ.1.1 _ (hlen _ _ _), hinp, (coinSplit_coins hθ).2.2 a]
  rfl

/-- **The paths' digests are public**: on the good set, the digest of a requested one-block input
is `pubR0` of the public part. -/
theorem digest_eq_pubR0 (inp : J → PublicParameter → MasterSeed → HashInput)
    (hinp : ∀ a P S, firstCell (inp a P S) = cell a P S) (hlen : ∀ a P S, (inp a P S).length < 136)
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    {θ : CTab J} (hθ : θ ∈ coinGood cell Q) (a : J) :
    θ.1.1.digest (inp a θ.1.1.param θ.1.1.seed) = pubR0 (coinSplit cell θ).1 a :=
  congrArg truncateHash (coinSplit_hash inp hinp hlen hθ a)

open HashSig.OverPermutation Common in
/-- The randomizer base's derivation `P ‖ A ‖ S ‖ M` of a label `(l, e, M)`. -/
def rbInput (lab : J → Layer × KeyIndex × HashInput) (a : J) (P : PublicParameter)
    (S : MasterSeed) : HashInput :=
  thInput P (tweakFields 7 0 (layerHi (lab a).1 0) (lab a).2.1)
    (littleEndianBytes 32 S ++ (lab a).2.2)

/-- The first block of a label's randomizer-base derivation: the `S`-keyed cell of its path. -/
def rbCell (lab : J → Layer × KeyIndex × HashInput) (a : J) (P : PublicParameter)
    (S : MasterSeed) : X :=
  firstCell (rbInput lab a P S)

/-- **The randomizer bases of the requested messages are public**: on the good set of the labels'
randomizer-base cells, `R0(l, e, M)` of a requested label (message under `72` bytes, so its
derivation is one block) is `pubR0` of the public part. -/
theorem randomizerBase_eq_pubR0 (lab : J → Layer × KeyIndex × HashInput)
    (hlen : ∀ a, ((lab a).2.2).length < 72)
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    {θ : CTab J} (hθ : θ ∈ coinGood (rbCell lab) Q) (a : J) :
    θ.1.1.randomizerBase (lab a).1 (lab a).2.1 (lab a).2.2 = pubR0 (coinSplit (rbCell lab) θ).1 a :=
  digest_eq_pubR0 (rbInput lab) (fun _ _ _ ↦ rfl) (fun a P S ↦ by
    have h := hlen a
    rw [rbInput, length_thInput, List.length_append, length_littleEndianBytes]
    omega) hθ a

/-- **On the good set, the challenger's data is a function of the public part with the coin
slots.** -/
theorem schemeData_eq_pubData_coinSplit
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    {θ : CTab J} (hθ : θ ∈ coinGood cell Q) :
    schemeData Q θ.1.1 = pubData Q (coinSplit cell θ).1.1 := by
  obtain ⟨hgood, hcoll, hread⟩ := mem_coinGood.mp hθ
  rw [schemeData_eq_of_mem (mem_schemeGood.mpr hgood)]
  obtain ⟨g4, g5, g6⟩ := coinSplit_keys_eq cell θ hcoll
  have hsl := coinSplit_slots cell θ
  have hπ : (coinSplit cell θ).1.1.1.perm = (schemeSplit θ.1).1.1.perm :=
    (coinSplit_perm cell θ).trans (schemeSplit_perm θ.1).symm
  have hP : pubParam (coinSplit cell θ).1.1 = pubParam (schemeSplit θ.1).1 :=
    congrArg (fun s : PubSlots ↦ trunc128 s.2.1) hsl
  have hC : pubCs (coinSplit cell θ).1.1 = pubCs (schemeSplit θ.1).1 :=
    congrArg (fun (s : PubSlots) (j : CsIdx) ↦ out256 (s.2.2 j)) hsl
  funext i
  change honestEval (schemeSplit θ.1).1.1.keys (schemeSplit θ.1).1.1.perm
      (Q i (pubParam (schemeSplit θ.1).1) (pubCs (schemeSplit θ.1).1)) =
    honestEval (coinSplit cell θ).1.1.1.keys (coinSplit cell θ).1.1.1.perm
      (Q i (pubParam (coinSplit cell θ).1.1) (pubCs (coinSplit cell θ).1.1))
  rw [← hP, ← hC, ← hπ]
  refine honestEval_congr (t := (coinSplit cell θ).1.1.1.keys) (t' := (schemeSplit θ.1).1.1.keys)
    (coinSplit cell θ).1.1.1.perm _ fun e he ↦ ?_
  have ha := honestEval_answeredBy (coinSplit cell θ).1.1.1.perm (coinSplit cell θ).1.1.1.keys _ e he
  cases e with
  | h z v =>
    have hz : ∀ a, pubCellH cell (coinSplit cell θ) a ≠ z := fun a hza ↦
      (hread i a).2.2 (by rw [hza]; exact mem_hCells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← g6 z hz]
    exact ha
  | k x v =>
    have hx : ∀ a, pubCellK cell (coinSplit cell θ) a ≠ x := fun a hxa ↦
      (hread i a).1 (by rw [hxa]; exact mem_kCells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← g4 x hx]
    exact ha
  | k' x v =>
    have hx : ∀ a, pubCellK' cell (coinSplit cell θ) a ≠ x := fun a hxa ↦
      (hread i a).2.1 (by rw [hxa]; exact mem_k'Cells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← g5 x hx]
    exact ha

/-! ### The bad fraction -/

open scoped Classical

variable (cell) (G : ℕ)

/-- A good permutation and colliding coin rates. -/
noncomputable def rateBad (x : Pub × MasterSeed) : ℕ :=
  if PermGood x.1.1.perm G ∧ ¬RateInj cell x then 1 else 0

/-- A good permutation and colliding capacities of the hidden and the coin cells. -/
noncomputable def capBad (x : Pub × MasterSeed) : ℕ :=
  if PermGood x.1.1.perm G ∧ ¬CapInj cell x then 1 else 0

/-- A good permutation and a collision of the coin cells. -/
noncomputable def collBad (x : Pub × MasterSeed) : ℕ :=
  rateBad cell G x + capBad cell G x

/-- The computation `Q i` reads `k` at the coin path `a`'s first block. -/
noncomputable def kHit
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (i : ι) (a : J)
    (y : CPub J × MasterSeed) : ℕ :=
  if pubCellK cell y a ∈ kCells (pubData Q y.1.1 i).2 then 1 else 0

/-- A good permutation and the computation `Q i` reading `k'` at the coin path `a`'s rate. -/
noncomputable def k'Hit
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (i : ι) (a : J)
    (y : CPub J × MasterSeed) : ℕ :=
  if PermGood y.1.1.1.perm G ∧ pubCellK' cell y a ∈ k'Cells (pubData Q y.1.1 i).2 then 1 else 0

/-- The computation `Q i` reads `h` at the coin path `a`'s capacity. -/
noncomputable def hHit
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (i : ι) (a : J)
    (y : CPub J × MasterSeed) : ℕ :=
  if pubCellH cell y a ∈ hCells (pubData Q y.1.1 i).2 then 1 else 0

/-- The coin paths' first blocks read by `Q i`. -/
noncomputable def readK
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (i : ι)
    (y : CPub J × MasterSeed) : ℕ :=
  ∑ a, kHit cell Q i a y

/-- The coin paths' rates and capacities read by `Q i`. -/
noncomputable def readKH
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (i : ι)
    (y : CPub J × MasterSeed) : ℕ :=
  ∑ a, (k'Hit cell G Q i a y + hHit cell Q i a y)

/-- A table outside `schemeGood Q`. -/
noncomputable def schemeBad
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (t : Tab) : ℕ :=
  if t ∈ schemeGood Q then 0 else 1

/-- A table with a bad permutation. -/
noncomputable def permBad (t : Tab) : ℕ :=
  if ¬PermGood t.1.perm G then 1 else 0

omit [DecidableEq J] in
theorem rateBad_coordS (ω : Coord) (S : MasterSeed) (k k' : X → Z) :
    rateBad cell G (coordS (((ω, S), k), k')) =
      (if PermGood ω.1 G ∧ ¬Function.Injective (fun a ↦ rateOf k ω.1
        (cell a (trunc128 ω.2.2.1.2.1) S)) then 1 else 0) :=
  rfl

omit [DecidableEq J] in
theorem capBad_coordS (ω : Coord) (S : MasterSeed) (k k' : X → Z) :
    capBad cell G (coordS (((ω, S), k), k')) =
      (if PermGood ω.1 G ∧ ¬Function.Injective (fun c ↦ capOf k k' ω.1
        (Sum.elim (hidCell (trunc128 ω.2.2.1.2.1) S ω.2.2.2)
          (fun a ↦ cell a (trunc128 ω.2.2.1.2.1) S) c)) then 1 else 0) :=
  rfl

/-- **Coin-rate collisions**: at most `|J|² G / |Z|` of the coordinates. -/
theorem card_mul_sum_rateBad_le
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1) :
    Fintype.card Z * ∑ x, rateBad cell G x ≤
      Fintype.card Tab * (Fintype.card J * Fintype.card J * G) := by
  rw [sum_eq_sum_coords coordS (rateBad cell G), card_tab_eq]
  have h : Fintype.card Z * ∑ ω : Coord, ∑ S : MasterSeed, ∑ k : X → Z, ∑ k' : X → Z,
      rateBad cell G (coordS (((ω, S), k), k')) =
        ∑ ω : Coord, ∑ S : MasterSeed, Fintype.card Z * ∑ k : X → Z, ∑ _k' : X → Z,
          (if PermGood ω.1 G ∧ ¬Function.Injective (fun a ↦ rateOf k ω.1
            (cell a (trunc128 ω.2.2.1.2.1) S)) then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    simp only [rateBad_coordS]
  rw [h]
  exact sum_sum_le_mul _ _ _ fun ω S ↦ card_mul_sum_not_injective_rateOf_le ω.1 G _
    fun a a' haa ↦ congrArg Prod.snd (hcell _ (a₁ := (S, a)) (a₂ := (S, a')) haa)

/-- **Capacity collisions of the hidden and the coin cells**: at most `|A ⊕ J|² (G + 1) / |Z|` of
the coordinates, `A = Option (Option CsIdx)`. -/
theorem card_mul_sum_capBad_le
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
    (hsep : ∀ P S S₀ a b, hidCell P S S₀ b ≠ cell a P S) :
    Fintype.card Z * ∑ x, capBad cell G x ≤
      Fintype.card Tab * (Fintype.card (Option (Option CsIdx) ⊕ J) *
        Fintype.card (Option (Option CsIdx) ⊕ J) * (G + 1)) := by
  rw [sum_eq_sum_coords coordS (capBad cell G), card_tab_eq]
  have h : Fintype.card Z * ∑ ω : Coord, ∑ S : MasterSeed, ∑ k : X → Z, ∑ k' : X → Z,
      capBad cell G (coordS (((ω, S), k), k')) =
        ∑ ω : Coord, ∑ S : MasterSeed, Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
          (if PermGood ω.1 G ∧ ¬Function.Injective (fun c ↦ capOf k k' ω.1
            (Sum.elim (hidCell (trunc128 ω.2.2.1.2.1) S ω.2.2.2)
              (fun a ↦ cell a (trunc128 ω.2.2.1.2.1) S) c)) then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    simp only [capBad_coordS]
  rw [h]
  exact sum_sum_le_mul _ _ _ fun ω S ↦ card_mul_sum_not_injective_capOf_le ω.1 G _
    (Function.Injective.sumElim (hidCell_injective _ S ω.2.2.2)
      (fun a a' haa ↦ congrArg Prod.snd (hcell _ (a₁ := (S, a)) (a₂ := (S, a')) haa))
      fun b a ↦ hsep _ S ω.2.2.2 a b)

theorem card_mul_sum_collBad_le
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
    (hsep : ∀ P S S₀ a b, hidCell P S S₀ b ≠ cell a P S) :
    Fintype.card Z * ∑ x, collBad cell G x ≤
      Fintype.card Tab * (Fintype.card J * Fintype.card J * G +
        Fintype.card (Option (Option CsIdx) ⊕ J) * Fintype.card (Option (Option CsIdx) ⊕ J) *
          (G + 1)) := by
  calc Fintype.card Z * ∑ x, collBad cell G x =
        Fintype.card Z * ∑ x, rateBad cell G x + Fintype.card Z * ∑ x, capBad cell G x := by
        rw [← mul_add, ← Finset.sum_add_distrib]
        rfl
    _ ≤ Fintype.card Tab * (Fintype.card J * Fintype.card J * G) +
        Fintype.card Tab * (Fintype.card (Option (Option CsIdx) ⊕ J) *
          Fintype.card (Option (Option CsIdx) ⊕ J) * (G + 1)) :=
        add_le_add (card_mul_sum_rateBad_le cell G hcell) (card_mul_sum_capBad_le cell G hcell hsep)
    _ = _ := (mul_add _ _ _).symm

/-- The public part with the coin slots and the scheme seed in coordinates: the public part with
the `h`-coins, the scheme seed, the `k`-coins and the `k'`-coins. -/
def coordC : (((Pub × (J → X)) × MasterSeed) × (J → Z)) × (J → Z) ≃ CPub J × MasterSeed where
  toFun c := ((c.1.1.1.1, (c.1.2, c.2, c.1.1.1.2)), c.1.1.2)
  invFun y := ((((y.1.1, y.1.2.2.2), y.2), y.1.2.1), y.1.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The coin paths' first blocks are rarely read**: at most `qs₂ / 2^256` of the coordinates,
where `qs₂` bounds the reads of `Q i` at `k`-cells of the form `cell a P S`. -/
theorem card_mul_sum_readK_le
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (qs₂ : ι → ℕ)
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
    (hqs₂ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ a S, cell a P S = x).card ≤ qs₂ i)
    (i : ι) :
    Fintype.card MasterSeed * ∑ y, readK cell Q i y ≤
      Fintype.card (CPub J × MasterSeed) * qs₂ i := by
  rw [sum_eq_sum_coords coordC (readK cell Q i), card_eq_coords coordC]
  refine card_mul_sum4_le_snd _ (qs₂ i) fun ω _ _ ↦ ?_
  change ∑ S, ∑ a, (if cell a (pubParam ω.1) S ∈ kCells (pubData Q ω.1 i).2 then 1 else 0) ≤ qs₂ i
  rw [← Fintype.sum_prod_type']
  exact (sum_ite_mem_le_card_filter (fun s : MasterSeed × J ↦ cell s.2 (pubParam ω.1) s.1)
    (hcell _) _ (fun x ↦ ∃ a S, cell a (pubParam ω.1) S = x) fun s ↦ ⟨s.2, s.1, rfl⟩).trans
    (hqs₂ i _ _ _ _)

/-- **The coin paths' rates and capacities are rarely read**: at most `|J| (G + 1) q / |Z|` of the
coordinates, the `k'`-coins resampled for the capacities and the `k`-coins for the rates. -/
theorem card_mul_sum_readKH_le
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (q : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i) (i : ι) :
    Fintype.card Z * ∑ y, readKH cell G Q i y ≤
      Fintype.card (CPub J × MasterSeed) * (Fintype.card J * (G + 1) * q i) := by
  rw [sum_eq_sum_coords coordC (readKH cell G Q i), card_eq_coords coordC]
  have h := card_mul_sum4_le_upd (Ω := Pub × (J → X)) (S := MasterSeed) (B := Z)
    (fun ω S kc k'c a ↦ k'Hit cell G Q i a (coordC (((ω, S), kc), k'c)))
    (fun ω S kc k'c a ↦ hHit cell Q i a (coordC (((ω, S), kc), k'c))) (q i * G) (q i)
    (fun ω S _ a kc ↦ by
      change ∑ w, (if PermGood ω.1.1.perm G ∧ (ω.1.1.perm (cell a (pubParam ω.1) S,
        Function.update kc a w a)).1 ∈ k'Cells (pubData Q ω.1 i).2 then 1 else 0) ≤ q i * G
      simp only [Function.update_self]
      by_cases hG : PermGood ω.1.1.perm G
      · simp only [hG, true_and]
        exact (sum_ite_comp_mem_le (fun w ↦ (ω.1.1.perm (cell a (pubParam ω.1) S, w)).1) _ G
          fun x₂ ↦ hG.rate _ x₂).trans
            (Nat.mul_le_mul_right _ ((card_k'Cells_le _).trans (hq i _ _ _ _)))
      · simp only [hG, false_and, ↓reduceIte, Finset.sum_const_zero]
        exact Nat.zero_le _)
    (fun ω S kc a k'c ↦ by
      change ∑ w, (if (ω.1.1.perm (cell a (pubParam ω.1) S, kc a)).2 +
        Function.update k'c a w a ∈ hCells (pubData Q ω.1 i).2 then 1 else 0) ≤ q i
      simp only [Function.update_self]
      rw [sum_ite_add_mem_eq_card]
      exact (card_hCells_le _).trans (hq i _ _ _ _))
  rw [show Fintype.card J * (q i * G + q i) = Fintype.card J * (G + 1) * q i by ring] at h
  exact h

/-- The tables outside the good set: outside `schemeGood`, a bad permutation, a collision of the
coin cells, or a computation reading a coin cell. -/
theorem card_sub_card_coinGood_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    Fintype.card (CTab J) - (coinGood cell Q).card ≤
      ∑ θ : CTab J, ((schemeBad Q θ.1 + permBad G θ.1) + (collBad cell G (schemeSplit θ.1) +
        ∑ i, (readK cell Q i (coinSplit cell θ) + readKH cell G Q i (coinSplit cell θ)))) := by
  refine card_sub_card_le_sum (coinGood cell Q) _ fun θ hθ ↦ ?_
  rw [mem_coinGood] at hθ
  by_cases hs : θ.1 ∈ schemeGood Q
  · by_cases hG : PermGood θ.1.1.perm G
    · by_cases hcoll : CollGood cell (schemeSplit θ.1)
      · have hread : ¬ReadGood cell Q (coinSplit cell θ) :=
          fun h ↦ hθ ⟨mem_schemeGood.mp hs, hcoll, h⟩
        obtain ⟨i, a, hia⟩ : ∃ i a,
            ¬(pubCellK cell (coinSplit cell θ) a ∉ kCells (pubData Q (coinSplit cell θ).1.1 i).2 ∧
              pubCellK' cell (coinSplit cell θ) a ∉
                k'Cells (pubData Q (coinSplit cell θ).1.1 i).2 ∧
              pubCellH cell (coinSplit cell θ) a ∉
                hCells (pubData Q (coinSplit cell θ).1.1 i).2) := by
          by_contra hne
          exact hread fun i a ↦ by_contra fun h ↦ hne ⟨i, a, h⟩
        have hG' : PermGood (coinSplit cell θ).1.1.1.perm G := by
          rw [coinSplit_perm]
          exact hG
        have hk : kHit cell Q i a (coinSplit cell θ) ≤ readK cell Q i (coinSplit cell θ) :=
          Finset.single_le_sum (f := fun a' ↦ kHit cell Q i a' (coinSplit cell θ))
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
        have hkh : k'Hit cell G Q i a (coinSplit cell θ) + hHit cell Q i a (coinSplit cell θ) ≤
            readKH cell G Q i (coinSplit cell θ) :=
          Finset.single_le_sum (f := fun a' ↦ k'Hit cell G Q i a' (coinSplit cell θ) +
            hHit cell Q i a' (coinSplit cell θ)) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
        have h1 : 1 ≤ readK cell Q i (coinSplit cell θ) + readKH cell G Q i (coinSplit cell θ) := by
          by_cases m1 : pubCellK cell (coinSplit cell θ) a ∈
              kCells (pubData Q (coinSplit cell θ).1.1 i).2
          · have : kHit cell Q i a (coinSplit cell θ) = 1 := ite_eq_left m1
            omega
          · by_cases m2 : pubCellK' cell (coinSplit cell θ) a ∈
                k'Cells (pubData Q (coinSplit cell θ).1.1 i).2
            · have : k'Hit cell G Q i a (coinSplit cell θ) = 1 := ite_eq_left ⟨hG', m2⟩
              omega
            · have m3 : pubCellH cell (coinSplit cell θ) a ∈
                  hCells (pubData Q (coinSplit cell θ).1.1 i).2 :=
                by_contra fun m3 ↦ hia ⟨m1, m2, m3⟩
              have : hHit cell Q i a (coinSplit cell θ) = 1 := ite_eq_left m3
              omega
        have h2 : readK cell Q i (coinSplit cell θ) + readKH cell G Q i (coinSplit cell θ) ≤
            ∑ i', (readK cell Q i' (coinSplit cell θ) + readKH cell G Q i' (coinSplit cell θ)) :=
          Finset.single_le_sum (f := fun i' ↦ readK cell Q i' (coinSplit cell θ) +
            readKH cell G Q i' (coinSplit cell θ)) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        omega
      · have hG' : PermGood (schemeSplit θ.1).1.1.perm G := by
          rw [schemeSplit_perm]
          exact hG
        have h1 : 1 ≤ collBad cell G (schemeSplit θ.1) := by
          by_cases hr : RateInj cell (schemeSplit θ.1)
          · have : capBad cell G (schemeSplit θ.1) = 1 :=
              ite_eq_left ⟨hG', fun hc ↦ hcoll ⟨hr, hc⟩⟩
            unfold collBad
            omega
          · have : rateBad cell G (schemeSplit θ.1) = 1 := ite_eq_left ⟨hG', hr⟩
            unfold collBad
            omega
        omega
    · have : permBad G θ.1 = 1 := ite_eq_left hG
      omega
  · have : schemeBad Q θ.1 = 1 := ite_eq_right hs
    omega

/-- **The bad fraction of the coin stage**: the fraction of tables outside `coinGood cell Q` is at
most the fraction outside `schemeGood Q`, plus the fraction of permutations with a rate count above
`G`, plus the collisions `(|J|² G + |A ⊕ J|² (G + 1)) / |Z|` (`A = Option (Option CsIdx)`), plus per
computation `qs₂ᵢ / 2^256 + |J| (G + 1) qᵢ / |Z|`, where `qᵢ` bounds the reads of `Q i` and `qs₂ᵢ`
its reads at `k`-cells of the form `cell a P S`. The labels' first blocks are distinct for distinct
labels or seeds (`hcell`) and differ from the hidden cells (`hsep`). -/
theorem coinGood_frac_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₂ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₂ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ a S, cell a P S = x).card ≤ qs₂ i)
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
    (hsep : ∀ P S S₀ a b, hidCell P S S₀ b ≠ cell a P S) :
    (Fintype.card (CTab J) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (CTab J) - (coinGood cell Q).card : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) +
          ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z))) +
        ((Fintype.card J * Fintype.card J * G +
          Fintype.card (Option (Option CsIdx) ⊕ J) * Fintype.card (Option (Option CsIdx) ⊕ J) *
            (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        ∑ i, ((qs₂ i : ℝ≥0∞) / 2 ^ 256 + Fintype.card J * (G + 1) * q i / Fintype.card Z) := by
  refine inv_mul_le_of_parts Fintype.card_ne_zero
    ((card_sub_card_coinGood_le cell G Q).trans_eq (sum_add_sum_eq _ _ _ _)) ?_ ?_ ?_ ?_
  · rw [Finset.sum_add_distrib, Nat.cast_add, mul_add]
    refine add_le_add (le_of_eq ?_) ?_
    · have hs : ∑ t, schemeBad Q t = Fintype.card Tab - (schemeGood Q).card :=
        sum_ite_mem_zero_one_eq (schemeGood Q)
      rw [sum_fst_eq (schemeBad Q), hs]
      exact natCast_smul_eq_card_mul _
    · exact natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
        (card_mul_sum_fst_eq (γ := CoinSlots J) (permBad G) _ _
          (card_mul_sum_tab_not_permGood G)).le
  · exact natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_fst_equiv_le schemeSplit (collBad cell G) _ _
        (card_mul_sum_collBad_le cell G hcell hsep))
  · intro i
    have h := natCast_le_mul_div_of_mul_le (Fintype.card_ne_zero (α := MasterSeed))
      (card_mul_sum_equiv_le (coinSplit cell) (readK cell Q i) _ _
        (card_mul_sum_readK_le cell Q qs₂ hcell hqs₂ i))
    rwa [card_masterSeed, Nat.cast_pow, Nat.cast_ofNat] at h
  · intro i
    have h := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_equiv_le (coinSplit cell) (readKH cell G Q i) _ _
        (card_mul_sum_readKH_le cell G Q q hq i))
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    exact h

/-- **The bad fraction of the staged swap with the coin stages**, with `schemeGood_frac_le`. -/
theorem coinGood_frac_le_of_schemeGood [Fintype ι]
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₀ qs₁ qs₂ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₀ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter SeedShaped).card ≤ qs₀ i)
    (hqs₁ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs₁ i)
    (hqs₂ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ a S, cell a P S = x).card ≤ qs₂ i)
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
    (hsep : ∀ P S S₀ a b, hidCell P S S₀ b ≠ cell a P S) :
    (Fintype.card (CTab J) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (CTab J) - (coinGood cell Q).card : ℕ) : ℝ≥0∞) ≤
      ((((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z)) +
          ((Fintype.card (Option (Option CsIdx)) * Fintype.card (Option (Option CsIdx)) *
            (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
          ∑ i, ((qs₀ i : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q i / Fintype.card Z +
            ((qs₁ i : ℝ≥0∞) / 2 ^ 256 +
              Fintype.card (Option CsIdx) * (G + 1) * q i / Fintype.card Z))) +
          ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z))) +
        ((Fintype.card J * Fintype.card J * G +
          Fintype.card (Option (Option CsIdx) ⊕ J) * Fintype.card (Option (Option CsIdx) ⊕ J) *
            (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        ∑ i, ((qs₂ i : ℝ≥0∞) / 2 ^ 256 + Fintype.card J * (G + 1) * q i / Fintype.card Z) :=
  (coinGood_frac_le cell G Q q qs₂ hq hqs₂ hcell hsep).trans
    (add_le_add (add_le_add (add_le_add (schemeGood_frac_le G Q q qs₀ qs₁ hq hqs₀ hqs₁) le_rfl)
      le_rfl) le_rfl)

end coin

end Quantum.Xmss.Hybrid

end
