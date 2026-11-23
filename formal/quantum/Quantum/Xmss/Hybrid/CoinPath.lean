module

public import Quantum.Xmss.Hybrid.CoinsHiding
public import Quantum.Sponge.PermTail
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-!
# Coin paths spread the scheme seed

Once the coins are public, a coin path of the challenger (a one-block input whose first block
`x₀ a S` carries the scheme seed `S` at a public label `a`, with public `k`- and `k'`-values `c₀`,
`c₁`) has its `k'`-cell at `(π (x₀ a S, c₀)).1` and its `h`-cell at `(π (x₀ a S, c₀)).2 + c₁`,
hidden only through `S`. `PermGood` bounds rate counts between rows, not how many seeds share such
a cell; this file adds that condition on `π`.

* `CoinPathGood π x₀ κ`: for every label `a`, coin `c₀`, rate `x` and capacity `z`, at most `κ`
  seeds send `(x₀ a S, c₀)` to rate `x`, and at most `κ` to capacity `z`.
* `sum_indicator_coinK'Cells_le`, `sum_indicator_coinHCells_le`: the multiplicity hypotheses of
  `uavg_coinMass_le` for the `k'`- and `h`-cells of the coin paths `i : ι`, with `|ι| κ`.
* `uavg_coinMass_le_of_good`: `uavg_coinMass_le` with the multiplicities assumed only on good
  public data (a bad `π` puts its tables outside `G`).
* `prob_not_coinPathGood_le`: a uniform permutation fails `CoinPathGood` with probability at most
  `|J| |Z| (|X| C(|S|, κ+1) (|Z| / N)^(κ+1) + |Z| C(|S|, κ+1) (|X| / N)^(κ+1))`, `N = |X × Z|`,
  for labels `J` and seed lines `x₀ a` injective, by PermTail's union bounds.
* `prob_not_coinPathGood_keccak`: at Keccak sizes (`|X| = 2^1088`, `|Z| = 2^512`) with a 256-bit
  seed and `κ = 9`, at most `|J| / 2^1536`; `prob_not_coinPathGood_keccak_of_card_le`: `2^-704`
  for `|J| ≤ 2^832` (as many labels as contexts of a seed-keyed cell).
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

universe u v w

namespace Quantum.Xmss.Hybrid

open Finset Quantum QuantumRuntime Quantum.Sponge

/-! ## The condition and the multiplicities -/

section good

/-- The `k'`-cells of the coin paths `i` (labels `a i`, `k`-coins `c₀ i`) for the seed `S`. -/
def coinK'Cells {X Z J Sd ι : Type} (π : Equiv.Perm (X × Z)) (x₀ : J → Sd → X) (a : ι → J)
    (c₀ : ι → Z) (S : Sd) : Set X :=
  {x | ∃ i, (π (x₀ (a i) S, c₀ i)).1 = x}

/-- The `h`-cells of the coin paths `i` (labels `a i`, `k`-coins `c₀ i`, `k'`-coins `c₁ i`) for
the seed `S`. -/
def coinHCells {X Z J Sd ι : Type} [Add Z] (π : Equiv.Perm (X × Z)) (x₀ : J → Sd → X)
    (a : ι → J) (c₀ c₁ : ι → Z) (S : Sd) : Set Z :=
  {z | ∃ i, (π (x₀ (a i) S, c₀ i)).2 + c₁ i = z}

variable {X Z J Sd : Type} [DecidableEq X] [DecidableEq Z] [Fintype Sd]

/-- **Coin paths spread the seeds**: for every label `a`, coin `c₀`, rate `x` and capacity `z`,
at most `κ` seeds `S` send `(x₀ a S, c₀)` to rate `x`, and at most `κ` to capacity `z`. -/
def CoinPathGood (π : Equiv.Perm (X × Z)) (x₀ : J → Sd → X) (κ : ℕ) : Prop :=
  ∀ a c₀, (∀ x, #(univ.filter fun S ↦ (π (x₀ a S, c₀)).1 = x) ≤ κ) ∧
    ∀ z, #(univ.filter fun S ↦ (π (x₀ a S, c₀)).2 = z) ≤ κ

/-- A point lies in a union of cells at most as often as in the cells. -/
theorem indicator_setOf_exists_le {α ι : Type} [DecidableEq α] [Fintype ι] (f : ι → α) (t : α) :
    ({t' | ∃ i, f i = t'} : Set α).indicator (fun _ ↦ (1 : ℝ≥0∞)) t ≤
      ∑ i, if f i = t then 1 else 0 := by
  classical
  rw [Set.indicator_apply]
  split_ifs with ht
  · obtain ⟨i, hi⟩ := ht
    refine (show (1 : ℝ≥0∞) ≤ if f i = t then 1 else 0 by simp [hi]).trans ?_
    exact single_le_sum (f := fun i ↦ if f i = t then (1 : ℝ≥0∞) else 0)
      (fun _ _ ↦ zero_le) (mem_univ i)
  · exact zero_le

/-- **The `k'`-cell multiplicity.** For a good `π`, a rate lies in the `k'`-cells of the coin
paths `i : ι` for at most `|ι| κ` seeds: the hypothesis `hk'` of `uavg_coinMass_le`. -/
theorem sum_indicator_coinK'Cells_le {π : Equiv.Perm (X × Z)} {x₀ : J → Sd → X} {κ : ℕ}
    (hπ : CoinPathGood π x₀ κ) {ι : Type} [Fintype ι] (a : ι → J) (c₀ : ι → Z) (x : X) :
    ∑ S, (coinK'Cells π x₀ a c₀ S).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ Fintype.card ι * κ := by
  calc ∑ S, (coinK'Cells π x₀ a c₀ S).indicator (fun _ ↦ (1 : ℝ≥0∞)) x
      ≤ ∑ S, ∑ i, (if (π (x₀ (a i) S, c₀ i)).1 = x then (1 : ℝ≥0∞) else 0) :=
        sum_le_sum fun S _ ↦ indicator_setOf_exists_le (fun i ↦ (π (x₀ (a i) S, c₀ i)).1) x
    _ = ∑ i, ((#(univ.filter fun S ↦ (π (x₀ (a i) S, c₀ i)).1 = x) : ℕ) : ℝ≥0∞) := by
        rw [sum_comm]
        simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ ≤ ∑ _i : ι, (κ : ℝ≥0∞) := sum_le_sum fun i _ ↦ by exact_mod_cast (hπ (a i) (c₀ i)).1 x
    _ = Fintype.card ι * κ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- **The `h`-cell multiplicity.** For a good `π`, a capacity lies in the `h`-cells of the coin
paths `i : ι` for at most `|ι| κ` seeds: the hypothesis `hh` of `uavg_coinMass_le`. -/
theorem sum_indicator_coinHCells_le [AddCommGroup Z] {π : Equiv.Perm (X × Z)} {x₀ : J → Sd → X}
    {κ : ℕ} (hπ : CoinPathGood π x₀ κ) {ι : Type} [Fintype ι] (a : ι → J) (c₀ c₁ : ι → Z)
    (z : Z) :
    ∑ S, (coinHCells π x₀ a c₀ c₁ S).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ Fintype.card ι * κ := by
  calc ∑ S, (coinHCells π x₀ a c₀ c₁ S).indicator (fun _ ↦ (1 : ℝ≥0∞)) z
      ≤ ∑ S, ∑ i, (if (π (x₀ (a i) S, c₀ i)).2 + c₁ i = z then (1 : ℝ≥0∞) else 0) :=
        sum_le_sum fun S _ ↦
          indicator_setOf_exists_le (fun i ↦ (π (x₀ (a i) S, c₀ i)).2 + c₁ i) z
    _ = ∑ i, ((#(univ.filter fun S ↦ (π (x₀ (a i) S, c₀ i)).2 + c₁ i = z) : ℕ) : ℝ≥0∞) := by
        rw [sum_comm]
        simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ ≤ ∑ _i : ι, (κ : ℝ≥0∞) := sum_le_sum fun i _ ↦ by
        have h := (hπ (a i) (c₀ i)).2 (z - c₁ i)
        simp only [eq_sub_iff_add_eq] at h
        exact_mod_cast h
    _ = Fintype.card ι * κ := by rw [sum_const, card_univ, nsmul_eq_mul]

end good

/-! ## The coin-cell mass with multiplicities on good public data -/

section coinMass

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] {U M : Type} [Fintype M]
  [DecidableEq M] {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- Truncating hidden sets to the public data satisfying `good` keeps a multiplicity bound that
holds there. -/
theorem sum_indicator_ite_le {α P V : Type} [Fintype V] (good : P → Prop) [DecidablePred good]
    (C : P → V → Set α) (κ : ℝ≥0∞)
    (hC : ∀ p, good p → ∀ t, ∑ v, (C p v).indicator (fun _ ↦ (1 : ℝ≥0∞)) t ≤ κ) (p : P) (t : α) :
    ∑ v, (if good p then C p v else ∅).indicator (fun _ ↦ (1 : ℝ≥0∞)) t ≤ κ := by
  by_cases hp : good p
  · simpa only [hp, ↓reduceIte] using hC p hp t
  · simp only [hp, ↓reduceIte, Set.indicator_empty, sum_const_zero, zero_le]

/-- **The coin-cell mass, with multiplicities on good public data.** `uavg_coinMass_le` with the
multiplicity hypotheses only for the public data satisfying `good` (for coin paths:
`CoinPathGood` of its permutation), and `G` inside the tables of good public data. -/
theorem uavg_coinMass_le_of_good {Θ P V : Type} [Fintype Θ] [Fintype P] [Fintype V]
    (e : Θ ≃ P × V) (m₀ : M) (Lc : Θ → Hw X Z) (pos : Θ → CoinPlacement X Z U)
    (Lp : P → Hw X Z) (ref : P → CoinPlacement X Z U) (Ch : P → V → Set Z)
    (Ck Ck' : P → V → Set X) (κ : ℝ≥0∞) (good : P → Prop)
    (hh : ∀ p, good p → ∀ z, ∑ v, (Ch p v).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ κ)
    (hk : ∀ p, good p → ∀ x, ∑ v, (Ck p v).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ κ)
    (hk' : ∀ p, good p → ∀ x, ∑ v, (Ck' p v).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ κ)
    (xθ : Θ → QuantumComp L (hwSpec X Z M) Ω A) (ρθ : Θ → SubState A)
    (y : P → QuantumComp L (coinSpec X Z U M) Ω A) (ρ : P → SubState A) (G : Finset Θ)
    (hG : ∀ θ ∈ G, good (e θ).1 ∧ xθ θ = placeCoins (pos θ) (y (e θ).1) ∧ ρθ θ = ρ (e θ).1 ∧
      CoinsMatch (Lc θ) (pos θ) (Lp (e θ).1) (ref (e θ).1) ∧
      (coinsRuntime (Lc θ) (pos θ) m₀).ForallQueries I
        (fun i _ _ ↦ CoinsPortOK (Lc θ) (Lp (e θ).1) (pos θ) (ref (e θ).1) i) (y (e θ).1)
        ((ρ (e θ).1).matrix ⊗ₖ (initHw X Z m₀).matrix))
    (j : ℕ) :
    uavg (fun θ ↦ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
        (coinMass (Ch (e θ).1 (e θ).2) (Ck (e θ).1 (e θ).2) (Ck' (e θ).1 (e θ).2) (Lc θ)) (xθ θ)
        ((ρθ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j) ≤
      κ * (Fintype.card V : ℝ≥0∞)⁻¹ +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((Fintype.card Θ - G.card : ℕ) : ℝ≥0∞) := by
  classical
  have hw : ∀ (p : P) (i : (hwSpec X Z M).Port)
      (σ : Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
        ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ), σ.PosSemidef →
      ∑ v, coinMass (if good p then Ch p v else ∅) (if good p then Ck p v else ∅)
        (if good p then Ck' p v else ∅) (Lp p) i σ ≤ κ * ENNReal.ofReal σ.trace.re :=
    fun p i σ hσ ↦ (Finset.sum_le_sum fun v _ ↦ coinMass_le_hiddenMass _ _ _ _ i σ).trans
      (sum_hiddenMass_le (fun v ↦ if good p then Ch p v else ∅)
        (fun v ↦ if good p then Ck p v else ∅) (fun v ↦ if good p then Ck' p v else ∅) κ
        (sum_indicator_ite_le good Ch κ hh p) (sum_indicator_ite_le good Ck κ hk p)
        (sum_indicator_ite_le good Ck' κ hk' p) i hσ)
  exact avg_queryWeight_le_fam I e
    (fun θ ↦ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
      (coinMass (Ch (e θ).1 (e θ).2) (Ck (e θ).1 (e θ).2) (Ck' (e θ).1 (e θ).2) (Lc θ)) (xθ θ)
      ((ρθ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j)
    (fun p ↦ runtime2Coins X Z (Lp p) m₀) (fun p ↦ placeCoins (ref p) (y p))
    (fun p ↦ (ρ p).matrix ⊗ₖ (initHw X Z m₀).matrix)
    (fun p ↦ ((ρ p).prod (initHw X Z m₀)).posSemidef)
    (fun p ↦ ENNReal.ofReal_le_one.mpr ((ρ p).prod (initHw X Z m₀)).trace_re_le_one)
    (fun p v ↦ coinMass (if good p then Ch p v else ∅) (if good p then Ck p v else ∅)
      (if good p then Ck' p v else ∅) (Lp p)) κ hw j G
    (fun θ hθ ↦ by
      obtain ⟨hg, hx, hρ, hm, hq⟩ := hG θ hθ
      rw [hx, hρ]
      simp only [hg, ↓reduceIte]
      exact (queryWeight_coinMass_placeCoins_eq I _ _ _ m₀ hm (y (e θ).1) _
        (forallQueries_coinsOK I m₀ _ _ hq) j).le)
    fun θ _ ↦ ((runtime2Coins X Z (Lc θ) m₀).queryWeight_le_ofReal_trace I
      (fun i σ hσ ↦ (coinMass_le_hiddenMass _ _ _ _ i σ).trans (hiddenMass_le _ _ _ i hσ)) _
      ((ρθ θ).prod (initHw X Z m₀)).posSemidef j).trans
      (ENNReal.ofReal_le_one.mpr ((ρθ θ).prod (initHw X Z m₀)).trace_re_le_one)

end coinMass

/-! ## A uniform permutation spreads the coin paths -/

section prob

variable {X Z J Sd : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype J]
  [Fintype Sd]

instance (π : Equiv.Perm (X × Z)) (x₀ : J → Sd → X) (κ : ℕ) :
    Decidable (CoinPathGood π x₀ κ) := by
  unfold CoinPathGood
  infer_instance

omit [DecidableEq X] in
/-- A capacity's column `X × {z}` has `|X|` points. -/
theorem card_filter_snd_eq (z : Z) : #(univ.filter fun p : X × Z ↦ p.2 = z) = Fintype.card X := by
  rw [show (univ.filter fun p : X × Z ↦ p.2 = z) = univ.map (Function.Embedding.sectL X z) by
    ext ⟨a, b⟩
    simp [eq_comm], card_map, card_univ]

/-- The fraction of permutations sending at least `s` points of the seed line `(x₀ S, c₀)` to the
rate `x`. -/
theorem coinPath_fst_tail (x₀ : Sd → X) (hx₀ : Function.Injective x₀) (c₀ : Z) (x : X) (s : ℕ) :
    (#(univ.filter fun π : Equiv.Perm (X × Z) ↦
        s ≤ #(univ.filter fun S ↦ (π (x₀ S, c₀)).1 = x)) : ℝ) /
        Fintype.card (Equiv.Perm (X × Z)) ≤
      (Fintype.card Sd).choose s *
        ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z)) ^ s := by
  set em : Sd ↪ X × Z := ⟨fun S ↦ (x₀ S, c₀), fun _ _ h ↦ hx₀ (congrArg Prod.fst h)⟩
  have hcount : ∀ π : Equiv.Perm (X × Z), #(univ.filter fun S ↦ (π (x₀ S, c₀)).1 = x) =
      #((univ.map em).filter (π · ∈ univ.filter fun p : X × Z ↦ p.1 = x)) := by
    intro π
    rw [filter_map, card_map]
    simp [em]
    rfl
  have := card_filter_le_card_div_le (univ.map em) (univ.filter fun p : X × Z ↦ p.1 = x) s
  simp only [card_map, card_univ, card_filter_fst_eq, Fintype.card_prod, ← hcount] at this
  exact_mod_cast this

/-- The fraction of permutations sending at least `s` points of the seed line `(x₀ S, c₀)` to the
capacity `z`. -/
theorem coinPath_snd_tail (x₀ : Sd → X) (hx₀ : Function.Injective x₀) (c₀ : Z) (z : Z) (s : ℕ) :
    (#(univ.filter fun π : Equiv.Perm (X × Z) ↦
        s ≤ #(univ.filter fun S ↦ (π (x₀ S, c₀)).2 = z)) : ℝ) /
        Fintype.card (Equiv.Perm (X × Z)) ≤
      (Fintype.card Sd).choose s *
        ((Fintype.card X : ℝ) / (Fintype.card X * Fintype.card Z)) ^ s := by
  set em : Sd ↪ X × Z := ⟨fun S ↦ (x₀ S, c₀), fun _ _ h ↦ hx₀ (congrArg Prod.fst h)⟩
  have hcount : ∀ π : Equiv.Perm (X × Z), #(univ.filter fun S ↦ (π (x₀ S, c₀)).2 = z) =
      #((univ.map em).filter (π · ∈ univ.filter fun p : X × Z ↦ p.2 = z)) := by
    intro π
    rw [filter_map, card_map]
    simp [em]
    rfl
  have := card_filter_le_card_div_le (univ.map em) (univ.filter fun p : X × Z ↦ p.2 = z) s
  simp only [card_map, card_univ, card_filter_snd_eq, Fintype.card_prod, ← hcount] at this
  exact_mod_cast this

/-- **A uniform permutation spreads the coin paths.** For seed lines `x₀ a` injective, the
fraction of permutations that are not `CoinPathGood π x₀ κ` is at most
`|J| |Z| (|X| C(|S|, κ+1) (|Z| / N)^(κ+1) + |Z| C(|S|, κ+1) (|X| / N)^(κ+1))`, `N = |X| |Z|`:
the union over labels, coins and target rates (capacities) of `κ + 1` seeds hitting the target. -/
theorem prob_not_coinPathGood_le (x₀ : J → Sd → X) (hx₀ : ∀ a, Function.Injective (x₀ a))
    (κ : ℕ) :
    (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬CoinPathGood π x₀ κ) : ℝ) /
        Fintype.card (Equiv.Perm (X × Z)) ≤
      Fintype.card J * Fintype.card Z *
        (Fintype.card X * ((Fintype.card Sd).choose (κ + 1) *
            ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z)) ^ (κ + 1)) +
          Fintype.card Z * ((Fintype.card Sd).choose (κ + 1) *
            ((Fintype.card X : ℝ) / (Fintype.card X * Fintype.card Z)) ^ (κ + 1))) := by
  classical
  set F₁ : J → Z → X → Finset (Equiv.Perm (X × Z)) := fun a c₀ x ↦
    univ.filter fun π ↦ κ + 1 ≤ #(univ.filter fun S ↦ (π (x₀ a S, c₀)).1 = x) with hF₁
  set F₂ : J → Z → Z → Finset (Equiv.Perm (X × Z)) := fun a c₀ z ↦
    univ.filter fun π ↦ κ + 1 ≤ #(univ.filter fun S ↦ (π (x₀ a S, c₀)).2 = z) with hF₂
  have hsub : (univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬CoinPathGood π x₀ κ) ⊆
      univ.biUnion fun a ↦ univ.biUnion fun c₀ ↦
        (univ.biUnion fun x ↦ F₁ a c₀ x) ∪ univ.biUnion fun z ↦ F₂ a c₀ z := by
    intro π hπ
    simp only [mem_filter, mem_univ, true_and, CoinPathGood, not_forall, not_and_or, not_le]
      at hπ
    obtain ⟨a, c₀, ⟨x, hx⟩ | ⟨z, hz⟩⟩ := hπ
    · simp only [mem_biUnion, mem_union, mem_univ, true_and, hF₁, hF₂, mem_filter]
      exact ⟨a, c₀, Or.inl ⟨x, hx⟩⟩
    · simp only [mem_biUnion, mem_union, mem_univ, true_and, hF₁, hF₂, mem_filter]
      exact ⟨a, c₀, Or.inr ⟨z, hz⟩⟩
  have hcard : #(univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬CoinPathGood π x₀ κ) ≤
      ∑ a, ∑ c₀, (∑ x, #(F₁ a c₀ x) + ∑ z, #(F₂ a c₀ z)) :=
    (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun a _ ↦
      card_biUnion_le.trans (sum_le_sum fun c₀ _ ↦
        (card_union_le _ _).trans (add_le_add card_biUnion_le card_biUnion_le))))
  calc (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬CoinPathGood π x₀ κ) : ℝ) /
        Fintype.card (Equiv.Perm (X × Z))
      ≤ ((∑ a, ∑ c₀, (∑ x, #(F₁ a c₀ x) + ∑ z, #(F₂ a c₀ z)) : ℕ) : ℝ) /
          Fintype.card (Equiv.Perm (X × Z)) := by
        gcongr
    _ = ∑ a, ∑ c₀, (∑ x, (#(F₁ a c₀ x) : ℝ) / Fintype.card (Equiv.Perm (X × Z)) +
          ∑ z, (#(F₂ a c₀ z) : ℝ) / Fintype.card (Equiv.Perm (X × Z))) := by
        push_cast
        simp only [sum_div, add_div]
    _ ≤ ∑ _a : J, ∑ _c₀ : Z, (∑ _x : X, (Fintype.card Sd).choose (κ + 1) *
            ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z)) ^ (κ + 1) +
          ∑ _z : Z, (Fintype.card Sd).choose (κ + 1) *
            ((Fintype.card X : ℝ) / (Fintype.card X * Fintype.card Z)) ^ (κ + 1)) :=
        sum_le_sum fun a _ ↦ sum_le_sum fun c₀ _ ↦ add_le_add
          (sum_le_sum fun x _ ↦ coinPath_fst_tail (x₀ a) (hx₀ a) c₀ x (κ + 1))
          (sum_le_sum fun z _ ↦ coinPath_snd_tail (x₀ a) (hx₀ a) c₀ z (κ + 1))
    _ = _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        ring

set_option exponentiation.threshold 4096 in
/-- **Coin paths at Keccak sizes.** For `|X| = 2^1088`, `|Z| = 2^512` and a 256-bit seed, a uniform
permutation fails `CoinPathGood π x₀ 9` with probability at most `|J| / 2^1536`. -/
theorem prob_not_coinPathGood_keccak (hX : Fintype.card X = 2 ^ 1088)
    (hZ : Fintype.card Z = 2 ^ 512) (hS : Fintype.card Sd = 2 ^ 256) (x₀ : J → Sd → X)
    (hx₀ : ∀ a, Function.Injective (x₀ a)) :
    (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬CoinPathGood π x₀ 9) : ℝ) /
        Fintype.card (Equiv.Perm (X × Z)) ≤ Fintype.card J / 2 ^ 1536 := by
  have h := prob_not_coinPathGood_le (Z := Z) x₀ hx₀ 9
  rw [hX, hZ, hS, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at h
  have hc : (((2 ^ 256 : ℕ).choose (9 + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ 2560 / 3628800 :=
    (Nat.choose_le_pow_div (α := ℝ) (9 + 1) (2 ^ 256)).trans_eq
      (by rw [show Nat.factorial (9 + 1) = 3628800 from rfl]; push_cast; ring)
  generalize (((2 ^ 256 : ℕ).choose (9 + 1) : ℕ) : ℝ) = c at h hc
  have hin : (2 : ℝ) ^ 512 * (2 ^ 1088 * (c * (2 ^ 512 / (2 ^ 1088 * 2 ^ 512)) ^ 10) +
      2 ^ 512 * (c * (2 ^ 1088 / (2 ^ 1088 * 2 ^ 512)) ^ 10)) ≤ 1 / 2 ^ 1536 := by
    calc (2 : ℝ) ^ 512 * (2 ^ 1088 * (c * (2 ^ 512 / (2 ^ 1088 * 2 ^ 512)) ^ 10) +
          2 ^ 512 * (c * (2 ^ 1088 / (2 ^ 1088 * 2 ^ 512)) ^ 10))
        ≤ (2 : ℝ) ^ 512 * (2 ^ 1088 * (2 ^ 2560 / 3628800 * (2 ^ 512 / (2 ^ 1088 * 2 ^ 512)) ^ 10) +
          2 ^ 512 * (2 ^ 2560 / 3628800 * (2 ^ 1088 / (2 ^ 1088 * 2 ^ 512)) ^ 10)) := by
          gcongr
      _ ≤ 1 / 2 ^ 1536 := by norm_num
  refine h.trans ?_
  calc _ = (Fintype.card J : ℝ) * ((2 : ℝ) ^ 512 *
          (2 ^ 1088 * (c * (2 ^ 512 / (2 ^ 1088 * 2 ^ 512)) ^ 10) +
            2 ^ 512 * (c * (2 ^ 1088 / (2 ^ 1088 * 2 ^ 512)) ^ 10))) := by ring
    _ ≤ (Fintype.card J : ℝ) * (1 / 2 ^ 1536) :=
        mul_le_mul_of_nonneg_left hin (Nat.cast_nonneg _)
    _ = Fintype.card J / 2 ^ 1536 := by ring

set_option exponentiation.threshold 2048 in
/-- **Coin paths at Keccak sizes, over every context.** With at most `2^832` labels (as many as
the contexts of a seed-keyed cell: its bits outside the seed), a uniform permutation fails
`CoinPathGood π x₀ 9` with probability at most `2^-704`. -/
theorem prob_not_coinPathGood_keccak_of_card_le (hX : Fintype.card X = 2 ^ 1088)
    (hZ : Fintype.card Z = 2 ^ 512) (hS : Fintype.card Sd = 2 ^ 256)
    (hJ : Fintype.card J ≤ 2 ^ 832) (x₀ : J → Sd → X) (hx₀ : ∀ a, Function.Injective (x₀ a)) :
    (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬CoinPathGood π x₀ 9) : ℝ) /
        Fintype.card (Equiv.Perm (X × Z)) ≤ 1 / 2 ^ 704 := by
  refine (prob_not_coinPathGood_keccak hX hZ hS x₀ hx₀).trans ?_
  calc (Fintype.card J : ℝ) / 2 ^ 1536 ≤ 2 ^ 832 / 2 ^ 1536 := by
        gcongr
        exact_mod_cast hJ
    _ = 1 / 2 ^ 704 := by norm_num

end prob

end Quantum.Xmss.Hybrid

end
