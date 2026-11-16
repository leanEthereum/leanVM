module

public import Quantum.Xmss.Hybrid.Seed

@[expose] public section

/-!
# Hiding the scheme seed: the seed-keyed cells and their capacities

* `fiberEquiv`, `xch`, `xch1`: bijections of tables that exchange cells of `h` with extra uniform
  slots, the cells chosen by data the exchange preserves.
* `capOf`, `rateOf`: the capacity and rate of a one-block input's round; `hash_of_lt`.
* `card_mul_sum_capOf_eq_le`: two distinct cells share their capacity for at most `(G + 1) / |Z|`
  of the keys. `sum_capOf_mem_le`: a computation that depends on `k`, `k'` only through its reads
  reads `h` at the capacity of a hidden cell on at most `qs / |S| + |A| (G + 1) q / |Z|` of the
  tables.
* The seed-keyed cells of leanXMSS: `skCell P S` (the parameter's and the chain starts'
  derivations), `hidCell` (with the seed derivation's cell); distinct (`skCell_injective`,
  `hidCell_injective`) and never seed-shaped.
-/

open Matrix
open scoped ENNReal ComplexOrder

universe u v w

namespace Quantum.Xmss.Hybrid

open Quantum Quantum.Sponge

/-! ## Gluing fiberwise equivalences, and exchanging cells with slots -/

section exchange

/-- A family of equivalences indexed by data that each of them preserves glues to one
equivalence. -/
def fiberEquiv {T C : Type*} (q : T → C) (Φ : C → T ≃ T) (hq : ∀ c t, q (Φ c t) = q t) :
    T ≃ T where
  toFun t := Φ (q t) t
  invFun t := (Φ (q t)).symm t
  left_inv t := by simp only [hq, Equiv.symm_apply_apply]
  right_inv t := by
    have h : q ((Φ (q t)).symm t) = q t := by
      have := hq (q t) ((Φ (q t)).symm t)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    simp only [h, Equiv.apply_symm_apply]

theorem fiberEquiv_apply {T C : Type*} (q : T → C) (Φ : C → T ≃ T)
    (hq : ∀ c t, q (Φ c t) = q t) (t : T) : fiberEquiv q Φ hq t = Φ (q t) t :=
  rfl

variable {X Z J : Type*} [AddCommGroup X]

/-- **Exchange cells with slots**: the cells `pos a` (distinct) take the slot values `u a`, and the
slots take the cell values shifted by `sh a`. -/
noncomputable def xch (pos : J → Z) (hpos : Function.Injective pos) (sh : J → X) :
    (Z → X) × (J → X) ≃ (Z → X) × (J → X) where
  toFun p := (fun z ↦ match Function.partialInv pos z with
      | some a => p.2 a
      | none => p.1 z,
    fun a ↦ sh a + p.1 (pos a))
  invFun p := (fun z ↦ match Function.partialInv pos z with
      | some a => p.2 a - sh a
      | none => p.1 z,
    fun a ↦ p.1 (pos a))
  left_inv p := by
    refine Prod.ext (funext fun z ↦ ?_) (funext fun a ↦ ?_)
    · cases hz : Function.partialInv pos z with
      | none => simp only [hz]
      | some a =>
        have hza : pos a = z := (hpos.isPartialInv a z).1 hz
        subst hza
        simp only [Function.partialInv_left hpos, add_sub_cancel_left]
    · simp only [Function.partialInv_left hpos]
  right_inv p := by
    refine Prod.ext (funext fun z ↦ ?_) (funext fun a ↦ ?_)
    · cases hz : Function.partialInv pos z with
      | none => simp only [hz]
      | some a =>
        have hza : pos a = z := (hpos.isPartialInv a z).1 hz
        subst hza
        simp only [Function.partialInv_left hpos]
    · simp only [Function.partialInv_left hpos, add_sub_cancel]

theorem xch_fst_of_notMem (pos : J → Z) (hpos : Function.Injective pos) (sh : J → X)
    (p : (Z → X) × (J → X)) {z : Z} (hz : ∀ a, pos a ≠ z) : (xch pos hpos sh p).1 z = p.1 z := by
  have hn : Function.partialInv pos z = none := by
    cases h : Function.partialInv pos z with
    | none => rfl
    | some a => exact absurd ((hpos.isPartialInv a z).1 h) (hz a)
  change (match Function.partialInv pos z with
    | some a => p.2 a
    | none => p.1 z) = p.1 z
  rw [hn]

theorem xch_snd (pos : J → Z) (hpos : Function.Injective pos) (sh : J → X)
    (p : (Z → X) × (J → X)) (a : J) : (xch pos hpos sh p).2 a = sh a + p.1 (pos a) :=
  rfl

/-- **Exchange one cell with a slot**: the cell `z` takes the slot value, and the slot takes the
cell value shifted by `r`. -/
def xch1 [DecidableEq Z] (z : Z) (r : X) : (Z → X) × X ≃ (Z → X) × X where
  toFun p := (Function.update p.1 z p.2, r + p.1 z)
  invFun p := (Function.update p.1 z (p.2 - r), p.1 z)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · simp only [Function.update_idem, add_sub_cancel_left, Function.update_eq_self]
    · simp only [Function.update_self]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp only [Function.update_idem, Function.update_eq_self]
    · simp only [Function.update_self, add_sub_cancel]

end exchange

/-! ## Capacities of honest cells, and their collisions -/

section count

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- The capacity at which a one-block input with first block `b` reads `h`. -/
def capOf (k k' : X → Z) (π : Equiv.Perm (X × Z)) (b : X) : Z :=
  (π (b, k b)).2 + k' (π (b, k b)).1

/-- The rate after the round of a one-block input with first block `b`. -/
def rateOf (k : X → Z) (π : Equiv.Perm (X × Z)) (b : X) : X :=
  (π (b, k b)).1

/-- A translate hits a point once. -/
theorem sum_ite_add_eq_one {A : Type*} [Fintype A] [DecidableEq A] [AddGroup A] (s c : A) :
    ∑ a, (if s + a = c then 1 else 0) = 1 := by
  have h := sum_ite_add_mem_eq_card ({c} : Finset A) s
  simpa only [Finset.mem_singleton, Finset.card_singleton] using h

open scoped Classical

/-- **Two distinct cells rarely share their capacity**: for a permutation with rate counts at most
`G`, at most `(G + 1) / |Z|` of the keys `k, k'`. -/
theorem card_mul_sum_capOf_eq_le (π : Equiv.Perm (X × Z)) (G : ℕ) (hG : PermGood π G)
    {b b' : X} (hb : b ≠ b') :
    Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
        (if capOf k k' π b = capOf k k' π b' then 1 else 0) ≤
      Fintype.card (X → Z) * Fintype.card (X → Z) * (G + 1) := by
  have hsplit : ∀ k k' : X → Z, (if capOf k k' π b = capOf k k' π b' then 1 else 0) ≤
      (if (π (b, k b)).1 = (π (b', k b')).1 then 1 else 0) +
        (if (π (b, k b)).1 ≠ (π (b', k b')).1 ∧ capOf k k' π b = capOf k k' π b' then 1 else 0) :=
    fun k k' ↦ by split_ifs <;> simp_all
  have h1 : ∀ k' : X → Z, Fintype.card Z * ∑ k : X → Z,
      (if (π (b, k b)).1 = (π (b', k b')).1 then 1 else 0) ≤ Fintype.card (X → Z) * G :=
    fun k' ↦ card_mul_sum_le_of_update _ b G fun k ↦ by
      simp only [Function.update_self, Function.update_of_ne hb.symm]
      rw [← Finset.card_filter]
      exact hG.rate b _
  have h2 : ∀ k : X → Z, Fintype.card Z * ∑ k' : X → Z,
      (if (π (b, k b)).1 ≠ (π (b', k b')).1 ∧ capOf k k' π b = capOf k k' π b' then 1 else 0) ≤
        Fintype.card (X → Z) * 1 :=
    fun k ↦ card_mul_sum_le_of_update _ (π (b, k b)).1 1 fun k' ↦ by
      by_cases hne : (π (b, k b)).1 = (π (b', k b')).1
      · simp [hne]
      · simp only [capOf, Function.update_self, Function.update_of_ne (Ne.symm hne), ne_eq, hne,
          not_false_eq_true, true_and]
        exact (sum_ite_add_eq_one _ _).le
  calc Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
        (if capOf k k' π b = capOf k k' π b' then 1 else 0)
      ≤ Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
          ((if (π (b, k b)).1 = (π (b', k b')).1 then 1 else 0) +
            (if (π (b, k b)).1 ≠ (π (b', k b')).1 ∧ capOf k k' π b = capOf k k' π b' then 1
              else 0)) := by
        gcongr with k _ k' _
        exact hsplit k k'
    _ = ∑ k' : X → Z, Fintype.card Z * ∑ k : X → Z,
          (if (π (b, k b)).1 = (π (b', k b')).1 then 1 else 0) +
        ∑ k : X → Z, Fintype.card Z * ∑ k' : X → Z,
          (if (π (b, k b)).1 ≠ (π (b', k b')).1 ∧ capOf k k' π b = capOf k k' π b' then 1
            else 0) := by
        simp only [Finset.sum_add_distrib, mul_add, Finset.mul_sum]
        exact congrArg (· + _) Finset.sum_comm
    _ ≤ ∑ _k' : X → Z, Fintype.card (X → Z) * G + ∑ _k : X → Z, Fintype.card (X → Z) * 1 :=
        add_le_add (Finset.sum_le_sum fun k' _ ↦ h1 k') (Finset.sum_le_sum fun k _ ↦ h2 k)
    _ = Fintype.card (X → Z) * Fintype.card (X → Z) * (G + 1) := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-- Moving two inner sums out. -/
theorem sum_comm_four {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ ↦ by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_comm

/-- **The capacity of a hidden cell is rarely read.** A computation `R k k' ω` (with `k`-, `k'`-
and `h`-cells `kc`, `k'c`, `hc`, at most `q` of the last two) that depends on `k` and `k'` only
through the cells it reads, and hidden cells `c a ω s` for uniform `s` that it reads at most `qs`
times in total: the computation reads `h` at the capacity of some hidden cell, for a permutation
with rate counts at most `G`, on at most `qs / |S| + |A| (G + 1) q / |Z|` of the tuples. -/
theorem sum_capOf_mem_le {Ω Sd A ρ : Type*} [Fintype Ω] [Fintype Sd] [Nonempty Sd] [Fintype A]
    (πf : Ω → Equiv.Perm (X × Z)) (c : A → Ω → Sd → X) (R : (X → Z) → (X → Z) → Ω → ρ)
    (kc k'c : ρ → Finset X) (hc : ρ → Finset Z)
    (hk : ∀ k k' ω x w, x ∉ kc (R (Function.update k x w) k' ω) →
      R (Function.update k x w) k' ω = R k k' ω)
    (hk' : ∀ k k' ω x a, x ∉ k'c (R k (Function.update k' x a) ω) →
      R k (Function.update k' x a) ω = R k k' ω)
    (G q qs : ℕ) (hq' : ∀ r, (k'c r).card ≤ q) (hqh : ∀ r, (hc r).card ≤ q)
    (hqs : ∀ k k' ω, ∑ s, ∑ a, (if c a ω s ∈ kc (R k k' ω) then 1 else 0) ≤ qs) :
    ((∑ ω, ∑ s, ∑ a, ∑ k : X → Z, ∑ k' : X → Z,
        (if PermGood (πf ω) G ∧ capOf k k' (πf ω) (c a ω s) ∈ hc (R k k' ω) then 1 else 0) : ℕ) :
        ℝ≥0∞) ≤
      ((Fintype.card Ω * Fintype.card Sd * (Fintype.card (X → Z) * Fintype.card (X → Z)) : ℕ) :
        ℝ≥0∞) * ((qs : ℝ≥0∞) / Fintype.card Sd + Fintype.card A * (G + 1) * q / Fintype.card Z) := by
  set N := Fintype.card Ω * Fintype.card Sd * (Fintype.card (X → Z) * Fintype.card (X → Z))
  set T₁ := ∑ ω, ∑ s, ∑ a, ∑ k : X → Z, ∑ k' : X → Z,
    (if c a ω s ∈ kc (R k k' ω) then 1 else 0)
  set T₂ := ∑ ω, ∑ s, ∑ a, ∑ k : X → Z, ∑ k' : X → Z,
    (if PermGood (πf ω) G ∧ c a ω s ∉ kc (R k k' ω) ∧
      (πf ω (c a ω s, k (c a ω s))).1 ∈ k'c (R k k' ω) then 1 else 0)
  set T₃ := ∑ ω, ∑ s, ∑ a, ∑ k : X → Z, ∑ k' : X → Z,
    (if (πf ω (c a ω s, k (c a ω s))).1 ∉ k'c (R k k' ω) ∧
      capOf k k' (πf ω) (c a ω s) ∈ hc (R k k' ω) then 1 else 0)
  have hsplit : ∑ ω, ∑ s, ∑ a, ∑ k : X → Z, ∑ k' : X → Z,
      (if PermGood (πf ω) G ∧ capOf k k' (πf ω) (c a ω s) ∈ hc (R k k' ω) then 1 else 0) ≤
        T₁ + T₂ + T₃ := by
    simp only [T₁, T₂, T₃, ← Finset.sum_add_distrib]
    gcongr with ω _ s _ a _ k _ k' _
    split_ifs <;> simp_all
  have h₁ : Fintype.card Sd * T₁ ≤ N * qs := by
    have : T₁ ≤ Fintype.card Ω * (Fintype.card (X → Z) * Fintype.card (X → Z)) * qs := by
      calc T₁ = ∑ ω, ∑ k : X → Z, ∑ k' : X → Z, ∑ s, ∑ a,
            (if c a ω s ∈ kc (R k k' ω) then 1 else 0) :=
            Finset.sum_congr rfl fun ω _ ↦ sum_comm_four _
        _ ≤ ∑ _ω : Ω, ∑ _k : X → Z, ∑ _k' : X → Z, qs :=
            Finset.sum_le_sum fun ω _ ↦ Finset.sum_le_sum fun k _ ↦
              Finset.sum_le_sum fun k' _ ↦ hqs k k' ω
        _ = _ := by
            simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
            ring
    calc Fintype.card Sd * T₁
        ≤ Fintype.card Sd * (Fintype.card Ω * (Fintype.card (X → Z) * Fintype.card (X → Z)) *
          qs) := Nat.mul_le_mul_left _ this
      _ = N * qs := by simp only [N]; ring
  have h₂ : Fintype.card Z * T₂ ≤ N * (Fintype.card A * G * q) := by
    have hin : ∀ ω s a (k' : X → Z), Fintype.card Z * ∑ k : X → Z,
        (if PermGood (πf ω) G ∧ c a ω s ∉ kc (R k k' ω) ∧
          (πf ω (c a ω s, k (c a ω s))).1 ∈ k'c (R k k' ω) then 1 else 0) ≤
        Fintype.card (X → Z) * (q * G) := fun ω s a k' ↦
      card_mul_sum_le_of_update _ (c a ω s) _ fun k ↦ by
        simp only [Function.update_self]
        calc ∑ w, (if PermGood (πf ω) G ∧
              c a ω s ∉ kc (R (Function.update k (c a ω s) w) k' ω) ∧
              (πf ω (c a ω s, w)).1 ∈ k'c (R (Function.update k (c a ω s) w) k' ω) then 1 else 0)
            ≤ ∑ w, (if PermGood (πf ω) G ∧ (πf ω (c a ω s, w)).1 ∈ k'c (R k k' ω)
              then 1 else 0) := by
              refine Finset.sum_le_sum fun w _ ↦ ?_
              split_ifs with h1 h2 <;> try omega
              obtain ⟨hG, hc', hm⟩ := h1
              rw [hk k k' ω _ w hc'] at hm
              exact absurd ⟨hG, hm⟩ h2
          _ ≤ q * G := by
              by_cases hG : PermGood (πf ω) G
              · simp only [hG, true_and]
                exact (sum_ite_comp_mem_le (fun w ↦ (πf ω (c a ω s, w)).1) _ G
                  fun x₂ ↦ hG.rate _ x₂).trans (Nat.mul_le_mul_right _ (hq' _))
              · simp only [hG, false_and, ↓reduceIte, Finset.sum_const_zero]
                exact Nat.zero_le _
    calc Fintype.card Z * T₂
        = ∑ ω, ∑ s, ∑ a, ∑ k' : X → Z, Fintype.card Z * ∑ k : X → Z,
          (if PermGood (πf ω) G ∧ c a ω s ∉ kc (R k k' ω) ∧
            (πf ω (c a ω s, k (c a ω s))).1 ∈ k'c (R k k' ω) then 1 else 0) := by
          simp only [T₂, Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ ↦ Finset.sum_congr rfl fun s _ ↦
            Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
      _ ≤ ∑ _ω : Ω, ∑ _s : Sd, ∑ _a : A, ∑ _k' : X → Z, Fintype.card (X → Z) * (q * G) :=
          Finset.sum_le_sum fun ω _ ↦ Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum fun a _ ↦
            Finset.sum_le_sum fun k' _ ↦ hin ω s a k'
      _ = N * (Fintype.card A * G * q) := by
          simp only [N, Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  have h₃ : Fintype.card Z * T₃ ≤ N * (Fintype.card A * q) := by
    have hin : ∀ ω s a (k : X → Z), Fintype.card Z * ∑ k' : X → Z,
        (if (πf ω (c a ω s, k (c a ω s))).1 ∉ k'c (R k k' ω) ∧
          capOf k k' (πf ω) (c a ω s) ∈ hc (R k k' ω) then 1 else 0) ≤
        Fintype.card (X → Z) * q := fun ω s a k ↦
      card_mul_sum_le_of_update _ (πf ω (c a ω s, k (c a ω s))).1 _ fun k' ↦ by
        simp only [capOf, Function.update_self]
        calc ∑ a', (if (πf ω (c a ω s, k (c a ω s))).1 ∉
              k'c (R k (Function.update k' (πf ω (c a ω s, k (c a ω s))).1 a') ω) ∧
              (πf ω (c a ω s, k (c a ω s))).2 + a' ∈
                hc (R k (Function.update k' (πf ω (c a ω s, k (c a ω s))).1 a') ω) then 1 else 0)
            ≤ ∑ a', (if (πf ω (c a ω s, k (c a ω s))).2 + a' ∈ hc (R k k' ω) then 1 else 0) := by
              refine Finset.sum_le_sum fun a' _ ↦ ?_
              split_ifs with h1 h2 <;> try omega
              obtain ⟨hc', hm⟩ := h1
              rw [hk' k k' ω _ a' hc'] at hm
              exact absurd hm h2
          _ ≤ q := by
              rw [sum_ite_add_mem_eq_card]
              exact hqh _
    calc Fintype.card Z * T₃
        = ∑ ω, ∑ s, ∑ a, ∑ k : X → Z, Fintype.card Z * ∑ k' : X → Z,
          (if (πf ω (c a ω s, k (c a ω s))).1 ∉ k'c (R k k' ω) ∧
            capOf k k' (πf ω) (c a ω s) ∈ hc (R k k' ω) then 1 else 0) := by
          simp only [T₃, Finset.mul_sum]
      _ ≤ ∑ _ω : Ω, ∑ _s : Sd, ∑ _a : A, ∑ _k : X → Z, Fintype.card (X → Z) * q :=
          Finset.sum_le_sum fun ω _ ↦ Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum fun a _ ↦
            Finset.sum_le_sum fun k _ ↦ hin ω s a k
      _ = N * (Fintype.card A * q) := by
          simp only [N, Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  have h₂₃ : Fintype.card Z * (T₂ + T₃) ≤ N * (Fintype.card A * (G + 1) * q) := by
    calc Fintype.card Z * (T₂ + T₃) = Fintype.card Z * T₂ + Fintype.card Z * T₃ := mul_add _ _ _
      _ ≤ N * (Fintype.card A * G * q) + N * (Fintype.card A * q) := add_le_add h₂ h₃
      _ = N * (Fintype.card A * (G + 1) * q) := by ring
  calc ((∑ ω, ∑ s, ∑ a, ∑ k : X → Z, ∑ k' : X → Z,
        (if PermGood (πf ω) G ∧ capOf k k' (πf ω) (c a ω s) ∈ hc (R k k' ω) then 1 else 0) : ℕ) :
        ℝ≥0∞)
      ≤ (T₁ : ℝ≥0∞) + ((T₂ + T₃ : ℕ) : ℝ≥0∞) := by
        rw [← Nat.cast_add, ← add_assoc]
        exact_mod_cast hsplit
    _ ≤ N * ((qs : ℝ≥0∞) / Fintype.card Sd) +
          N * (((Fintype.card A * (G + 1) * q : ℕ) : ℝ≥0∞) / Fintype.card Z) :=
        add_le_add (natCast_le_mul_div_of_mul_le Fintype.card_ne_zero h₁)
          (natCast_le_mul_div_of_mul_le Fintype.card_ne_zero h₂₃)
    _ = _ := by
        rw [← mul_add]
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]

end count

/-! ## The seed-keyed cells of leanXMSS -/

section cells

open HashSig LeanXmss
open LeanVM.Protocol.KeccakHash (padBlock)

/-- The chain-start derivations: layer, key and pair of chains. -/
abbrev CsIdx := Layer × KeyIndex × ChainPairIndex

/-- The parameter's derivation `0 ‖ A ‖ S`. -/
def paramInput (S : MasterSeed) : HashInput :=
  thInput 0 (keygenDomainFields .parameter) (littleEndianBytes 32 S)

/-- A chain start's derivation `P ‖ A ‖ S`. -/
def csInput (P : PublicParameter) (S : MasterSeed) (j : CsIdx) : HashInput :=
  thInput P (keygenDomainFields (.oneTimeChainPair j.1 j.2.1 j.2.2)) (littleEndianBytes 32 S)

/-- The first block of an input: the `k`-cell its hashing reads first. -/
def firstCell (input : HashInput) : X :=
  blockOf (firstBlock input)

/-- The seed-keyed cells: the parameter's derivation (`none`) and the chain starts'. -/
def skCell (P : PublicParameter) (S : MasterSeed) : Option CsIdx → X
  | none => firstCell (paramInput S)
  | some j => firstCell (csInput P S j)

/-- The cells whose capacities the decomposition hides: the seed derivation's (`none`) and the
seed-keyed cells. -/
def hidCell (P : PublicParameter) (S S₀ : MasterSeed) : Option (Option CsIdx) → X
  | none => seedCell S₀
  | some b => skCell P S b

theorem length_paramInput (S : MasterSeed) : (paramInput S).length = 64 := by
  rw [paramInput, length_thInput, length_littleEndianBytes]

theorem length_csInput (P : PublicParameter) (S : MasterSeed) (j : CsIdx) :
    (csInput P S j).length = 64 := by
  rw [csInput, length_thInput, length_littleEndianBytes]

/-- A short input is one block. -/
theorem blocks_of_lt (inp : HashInput) (h : inp.length < 136) : blocks inp = [firstCell inp] := by
  have hl := length_blocks inp
  have hh := head?_blocks inp
  cases hbl : blocks inp with
  | nil => rw [hbl] at hh; simp at hh
  | cons b m =>
    rw [hbl, List.length_cons] at hl
    rw [hbl, List.head?_cons, Option.some.injEq] at hh
    rw [List.eq_nil_of_length_eq_zero (l := m) (by omega), hh]
    rfl

/-- **The hash of a one-block input**: the rate after its round plus `h` at its capacity. -/
theorem hash_of_lt (L : HonestTable) (inp : HashInput) (h : inp.length < 136) :
    L.hash inp = out256 (rateOf L.keys.2.1 L.perm (firstCell inp) +
      L.keys.1 (capOf L.keys.2.1 L.keys.2.2 L.perm (firstCell inp))) := by
  show out256 (spongeHash (spongePerm L.keys L.perm) (blocks inp)) = _
  rw [blocks_of_lt inp h]
  simp only [spongeHash, absorb, List.foldl_cons, List.foldl_nil, absorbStep, spongePerm,
    Equiv.Perm.mul_apply, rateRound_apply, capacityRound_apply, zero_add, rateOf, capOf]

/-- The address fields a first block carries. -/
def fieldsOfCell (x : X) : TweakFields :=
  ⟨rateSlice x 184 5 (by norm_num), rateSlice x 189 3 (by norm_num),
    rateSlice x 160 24 (by norm_num), rateSlice x 128 32 (by norm_num)⟩

theorem fieldsOfCell_thInput (Q : PublicParameter) (fields : TweakFields) (payload : HashInput)
    (hp : 32 ≤ payload.length) : fieldsOfCell (firstCell (thInput Q fields payload)) = fields := by
  set x := firstCell (thInput Q fields payload)
  have hx : ∀ j (hj : j < 512), x ⟨j, by omega⟩ = inputBit (thInput Q fields payload) j :=
    fun j hj ↦ blockOf_firstBlock _ _ (by rw [length_thInput]; simp only; omega)
  have hlo : rateSlice x 128 32 (by norm_num) = fields.lo := rateSlice_eq fun j hj ↦ by
    rw [hx (128 + j) (by omega), inputBit_thInput_address _ _ _ _ (by omega),
      inputBit_addressBytes_lo _ _ hj]
  have hhi : rateSlice x 160 24 (by norm_num) = fields.hi := rateSlice_eq fun j hj ↦ by
    rw [hx (160 + j) (by omega), show 160 + j = 128 + (32 + j) by omega,
      inputBit_thInput_address _ _ _ _ (by omega), inputBit_addressBytes_hi _ _ hj]
  have htag : rateSlice x 184 5 (by norm_num) = fields.tag := rateSlice_eq fun j hj ↦ by
    rw [hx (184 + j) (by omega), show 184 + j = 128 + (56 + j) by omega,
      inputBit_thInput_address _ _ _ _ (by omega), inputBit_addressBytes_stepTag _ _ (by omega),
      BitVec.getLsbD_append, ite_eq_left hj]
  have hstep : rateSlice x 189 3 (by norm_num) = fields.step := rateSlice_eq fun j hj ↦ by
    rw [hx (189 + j) (by omega), show 189 + j = 128 + (56 + (5 + j)) by omega,
      inputBit_thInput_address _ _ _ _ (by omega), inputBit_addressBytes_stepTag _ _ (by omega),
      BitVec.getLsbD_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  rw [fieldsOfCell, hlo, hhi, htag, hstep]

theorem skCell_mem_seedKeyCells (P : PublicParameter) (S : MasterSeed) (b : Option CsIdx) :
    skCell P S b ∈ seedKeyCells S := by
  cases b with
  | none => exact firstBlock_thInput_seed_mem_seedKeyCells _ _ _
  | some j => exact firstBlock_thInput_seed_mem_seedKeyCells _ _ _

theorem fieldsOfCell_skCell (P : PublicParameter) (S : MasterSeed) :
    ∀ b : Option CsIdx, fieldsOfCell (skCell P S b) =
      keygenDomainFields (b.elim .parameter fun j ↦ .oneTimeChainPair j.1 j.2.1 j.2.2)
  | none => fieldsOfCell_thInput _ _ _ (by rw [length_littleEndianBytes])
  | some _ => fieldsOfCell_thInput _ _ _ (by rw [length_littleEndianBytes])

/-- The chain-start fields determine the layer, key and pair. -/
theorem keygenDomainFields_cs_injective {l l' : Layer} {e e' : KeyIndex}
    {c c' : ChainPairIndex}
    (h : keygenDomainFields (.oneTimeChainPair l e c) = keygenDomainFields (.oneTimeChainPair l' e' c')) :
    (l, e, c) = (l', e', c') := by
  have hhi := congrArg TweakFields.hi h
  have hlo := congrArg TweakFields.lo h
  simp only [keygenDomainFields, tweakFields] at hhi hlo
  have hc : c.val < 2 ^ 23 := by have := c.isLt; simp only [chainCount] at this; omega
  have hc' : c'.val < 2 ^ 23 := by have := c'.isLt; simp only [chainCount] at this; omega
  have hl : l = l' := by
    rw [← layerOf_layerHi l c.val hc, ← layerOf_layerHi l' c'.val hc', hhi]
  have hcc : c = c' := Fin.ext (by
    rw [← lowOf_layerHi l c.val hc, ← lowOf_layerHi l' c'.val hc', hhi])
  have he : e = e' := by rw [← keyOf_ofNat e, ← keyOf_ofNat e', hlo]
  rw [hl, hcc, he]

/-- **The seed-keyed cells are distinct**: a seed-keyed cell names its seed and its derivation. -/
theorem skCell_injective (P : PublicParameter) :
    Function.Injective fun q : MasterSeed × Option CsIdx ↦ skCell P q.1 q.2 := by
  rintro ⟨S, b⟩ ⟨S', b'⟩ h
  simp only at h
  have hS : S = S' := by
    have h₁ := skCell_mem_seedKeyCells P S b
    have h₂ := skCell_mem_seedKeyCells P S' b'
    simp only [seedKeyCells, Set.mem_ofPred_eq] at h₁ h₂
    rw [← h₁, ← h₂, h]
  subst hS
  have hf := congrArg fieldsOfCell h
  rw [fieldsOfCell_skCell, fieldsOfCell_skCell] at hf
  cases b with
  | none =>
    cases b' with
    | none => rfl
    | some j =>
      have ht := congrArg TweakFields.tag hf
      simp [keygenDomainFields, tweakFields] at ht
  | some j =>
    cases b' with
    | none =>
      have ht := congrArg TweakFields.tag hf
      simp [keygenDomainFields, tweakFields] at ht
    | some j' =>
      have := keygenDomainFields_cs_injective hf
      simp only [Prod.mk.eta] at this
      rw [this]

theorem not_seedShaped_skCell (P : PublicParameter) (S : MasterSeed) (b : Option CsIdx) :
    ¬SeedShaped (skCell P S b) := by
  cases b with
  | none =>
    rw [skCell, firstCell, firstBlock_of_lt _ (by rw [length_paramInput]; norm_num)]
    exact not_seedShaped_padBlock _ (by rw [length_paramInput]; norm_num)
      (by rw [length_paramInput]; norm_num)
  | some j =>
    rw [skCell, firstCell, firstBlock_of_lt _ (by rw [length_csInput]; norm_num)]
    exact not_seedShaped_padBlock _ (by rw [length_csInput]; norm_num)
      (by rw [length_csInput]; norm_num)

/-- The hidden cells are distinct. -/
theorem hidCell_injective (P : PublicParameter) (S S₀ : MasterSeed) :
    Function.Injective (hidCell P S S₀) := by
  intro a a' h
  cases a with
  | none =>
    cases a' with
    | none => rfl
    | some b =>
      have h' : seedCell S₀ = skCell P S b := h
      exact absurd (h' ▸ seedShaped_seedCell S₀) (not_seedShaped_skCell P S b)
  | some b =>
    cases a' with
    | none =>
      have h' : skCell P S b = seedCell S₀ := h
      exact absurd (h' ▸ seedShaped_seedCell S₀) (not_seedShaped_skCell P S b)
    | some b' =>
      have := @skCell_injective P (S, b) (S, b') h
      rw [Prod.mk.injEq] at this
      rw [this.2]

end cells

end Quantum.Xmss.Hybrid

end
