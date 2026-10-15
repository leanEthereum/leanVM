import SphincsFors.BridgeVirtual
import SphincsFors.H0Charlier

/-! Poisson domination of the joint factorial moments of the virtual future by a product of
Charlier polynomials (`chProd`), which satisfies the slot and creation recursions with `≤`. Generic
in the view type `V` and the index map `idx`. -/

open ENNReal

namespace SphincsFors.Security.H0

open Domination

set_option linter.unusedSectionVars false

variable {V ι : Type} [DecidableEq ι] [Fintype ι] (idx : V → ι)

/-- Number of disclosed views at index `l`. -/
def cnt (d : Multiset V) (l : ι) : ℕ := (d.filter fun v => idx v = l).card

/-- Number of items at index `l`. -/
def nItems (items : List V) (l : ι) : ℕ := items.countP fun v => idx v = l

theorem cnt_add_single (d : Multiset V) (u : V) (l : ι) :
    cnt idx (d + {u}) l = cnt idx d l + if idx u = l then 1 else 0 := by
  unfold cnt
  rw [Multiset.filter_add, Multiset.card_add, Multiset.filter_singleton]
  split_ifs <;> simp

theorem cnt_zero (l : ι) : cnt idx (0 : Multiset V) l = 0 := by simp [cnt]

theorem nItems_cons (u : V) (items : List V) (l : ι) :
    nItems idx (u :: items) l = nItems idx items l + if idx u = l then 1 else 0 := by
  unfold nItems
  rw [List.countP_cons]
  simp

/-- Joint falling-factorial monomial of the counts. -/
noncomputable def fallMono (k : ι → ℕ) (d : Multiset V) : ℝ≥0∞ :=
  ∏ l, ((cnt idx d l).descFactorial (k l) : ℝ≥0∞)

/-- Product of Charlier polynomials at per-index rates. -/
noncomputable def chProd (k : ι → ℕ) (ρ : ι → ℝ≥0∞) (d : Multiset V) : ℝ≥0∞ :=
  ∏ l, charlier (k l) (cnt idx d l) (ρ l)

/-- One coin on one index. -/
theorem coin_factor (p : ℝ≥0∞) (hp : p ≤ 1) (n c : ℕ) (r : ℝ≥0∞) :
    p * charlier n (c + 1) r + (1 - p) * charlier n c r ≤ charlier n c (r + p) := by
  cases n with
  | zero =>
      simp only [charlier_zero_order, mul_one]
      rw [add_tsub_cancel_of_le hp]
  | succ n =>
      rw [charlier_succ]
      calc p * (charlier (n + 1) c r + ((n + 1 : ℕ) : ℝ≥0∞) * charlier n c r) + (1 - p) * charlier (n + 1) c r
          = (p + (1 - p)) * charlier (n + 1) c r + p * ((n + 1 : ℕ) : ℝ≥0∞) * charlier n c r := by ring
        _ = charlier (n + 1) c r + p * ((n + 1 : ℕ) : ℝ≥0∞) * charlier n c r := by
            rw [add_tsub_cancel_of_le hp, one_mul]
        _ ≤ _ := charlier_lower p n c r

theorem prod_split {f : ι → ℝ≥0∞} (j : ι) : ∏ l, f l = f j * ∏ l ∈ Finset.univ.erase j, f l :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

theorem coin_step (k : ι → ℕ) (ρ : ι → ℝ≥0∞) (p : ℝ≥0∞) (hp : p ≤ 1) (v : V) (d : Multiset V) :
    p * chProd idx k ρ (d + {v}) + (1 - p) * chProd idx k ρ d ≤
      chProd idx k (fun l => ρ l + if idx v = l then p else 0) d := by
  unfold chProd
  set j := idx v
  rw [prod_split j, prod_split (f := fun l => charlier (k l) (cnt idx d l) (ρ l)) j,
    prod_split (f := fun l => charlier (k l) (cnt idx d l) (ρ l + if idx v = l then p else 0)) j]
  have hrest1 : ∏ l ∈ Finset.univ.erase j, charlier (k l) (cnt idx (d + {v}) l) (ρ l) =
      ∏ l ∈ Finset.univ.erase j, charlier (k l) (cnt idx d l) (ρ l) := by
    refine Finset.prod_congr rfl fun l hl => ?_
    have hne : j ≠ l := (Finset.ne_of_mem_erase hl).symm
    rw [cnt_add_single, if_neg hne, add_zero]
  have hrest2 : ∏ l ∈ Finset.univ.erase j, charlier (k l) (cnt idx d l) (ρ l + if idx v = l then p else 0) =
      ∏ l ∈ Finset.univ.erase j, charlier (k l) (cnt idx d l) (ρ l) := by
    refine Finset.prod_congr rfl fun l hl => ?_
    have hne : j ≠ l := (Finset.ne_of_mem_erase hl).symm
    simp only [j] at hne
    rw [if_neg hne, add_zero]
  rw [hrest1, hrest2, cnt_add_single, if_pos rfl, if_pos rfl]
  set R := ∏ l ∈ Finset.univ.erase j, charlier (k l) (cnt idx d l) (ρ l)
  calc p * (charlier (k j) (cnt idx d j + 1) (ρ j) * R) + (1 - p) * (charlier (k j) (cnt idx d j) (ρ j) * R)
      = (p * charlier (k j) (cnt idx d j + 1) (ρ j) + (1 - p) * charlier (k j) (cnt idx d j) (ρ j)) * R := by
        ring
    _ ≤ charlier (k j) (cnt idx d j) (ρ j + p) * R := by
        gcongr
        exact coin_factor p hp _ _ _

/-- **Coins.** Independent coins on items are absorbed into the rates. -/
theorem coins_absorb (k : ι → ℕ) (w : ℝ≥0∞) (hw : w ≤ 1) :
    ∀ (items : List V) (ρ : ι → ℝ≥0∞) (d : Multiset V),
      slotValue (chProd idx k ρ) d (itemCoins w items) ≤
        chProd idx k (fun l => ρ l + w * nItems idx items l) d
  | [], ρ, d => by simp [itemCoins, slotValue, nItems]
  | v :: rest, ρ, d => by
      rw [itemCoins_cons]
      simp only [slotValue]
      have ih1 := coins_absorb k w hw rest ρ (d + {v})
      have ih2 := coins_absorb k w hw rest ρ d
      calc w * slotValue (chProd idx k ρ) (d + {v}) (itemCoins w rest) +
            (1 - w) * slotValue (chProd idx k ρ) d (itemCoins w rest)
          ≤ w * chProd idx k (fun l => ρ l + w * nItems idx rest l) (d + {v}) +
            (1 - w) * chProd idx k (fun l => ρ l + w * nItems idx rest l) d := by gcongr
        _ ≤ chProd idx k (fun l => (ρ l + w * nItems idx rest l) + if idx v = l then w else 0) d :=
            coin_step idx k _ w hw v d
        _ = chProd idx k (fun l => ρ l + w * nItems idx (v :: rest) l) d := by
            unfold chProd
            refine Finset.prod_congr rfl fun l _ => ?_
            congr 1
            dsimp only
            rw [nItems_cons]
            split_ifs <;> push_cast <;> ring

/-- The fresh view has a uniform index. -/
def UniformIndex (U : Finset V) : Prop :=
  ∀ g : ι → ℝ≥0∞, freshAvg U (fun u => g (idx u)) = (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ l, g l

/-- Product with one perturbed index `v`. -/
noncomputable def perturbed (k : ι → ℕ) (c : ι → ℕ) (y : ι → ℝ≥0∞) (mw : ℝ≥0∞) (v : ι) : ℝ≥0∞ :=
  ∏ l, charlier (k l) (c l + if v = l then 1 else 0) (y l + if v = l then mw else 0)

theorem perturbed_split (k : ι → ℕ) (c : ι → ℕ) (y : ι → ℝ≥0∞) (mw : ℝ≥0∞) (v : ι) :
    perturbed k c y mw v =
      charlier (k v) (c v + 1) (y v + mw) * ∏ l ∈ Finset.univ.erase v, charlier (k l) (c l) (y l) := by
  unfold perturbed
  rw [prod_split v, if_pos rfl, if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  have hne : v ≠ l := (Finset.ne_of_mem_erase hl).symm
  rw [if_neg hne, if_neg hne, add_zero, add_zero]

/-- **Fresh step.** One fresh uniform disclosure, which becomes an item with future coin rate
`m w`, is dominated by raising every rate by `α`. -/
theorem fresh_step (U : Finset V) (hU : UniformIndex idx U) (k : ι → ℕ) (K : ℕ) (hk : ∀ l, k l ≤ K + 1)
    (m : ℕ) (α w : ℝ≥0∞) (items : List V) (d : Multiset V)
    (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (hslack : (1 + m * w) * (1 + w * Fintype.card ι) ^ K ≤ Fintype.card ι * α)
    (hLα : 1 ≤ (Fintype.card ι : ℝ≥0∞) * α) :
    freshAvg U (fun u => chProd idx k
        (fun l => ((m : ℝ≥0∞) * α + m * w * nItems idx (u :: items) l) + w * nItems idx items l) (d + {u})) ≤
      chProd idx k (fun l => ((m + 1 : ℕ) : ℝ≥0∞) * α + ((m + 1 : ℕ) : ℝ≥0∞) * w * nItems idx items l) d := by
  have hg : ∀ u, chProd idx k
      (fun l => ((m : ℝ≥0∞) * α + m * w * nItems idx (u :: items) l) + w * nItems idx items l) (d + {u}) =
      perturbed k (fun l => cnt idx d l)
        (fun l => (m : ℝ≥0∞) * α + ((m + 1 : ℕ) : ℝ≥0∞) * w * nItems idx items l) ((m : ℝ≥0∞) * w) (idx u) := by
    intro u
    unfold chProd perturbed
    refine Finset.prod_congr rfl fun l _ => ?_
    dsimp only
    rw [cnt_add_single, nItems_cons]
    congr 1
    split_ifs <;> push_cast <;> ring
  have he : ∀ v, charlier (k v) (cnt idx d v + 1) ((m : ℝ≥0∞) * α + ((m + 1 : ℕ) : ℝ≥0∞) * w * nItems idx items v + m * w) ≤
      charlier (k v) (cnt idx d v) ((m : ℝ≥0∞) * α + ((m + 1 : ℕ) : ℝ≥0∞) * w * nItems idx items v) +
      (Fintype.card ι : ℝ≥0∞) * (α * (k v : ℝ≥0∞) *
        charlier (k v - 1) (cnt idx d v) ((m : ℝ≥0∞) * α + ((m + 1 : ℕ) : ℝ≥0∞) * w * nItems idx items v)) := by
    intro v
    rcases hkv : k v with _ | n
    · simp
    · have hmw : (m : ℝ≥0∞) * w ≤ (w * Fintype.card ι) *
          ((m : ℝ≥0∞) * α + ((m + 1 : ℕ) : ℝ≥0∞) * w * nItems idx items v) := by
        calc (m : ℝ≥0∞) * w = (m : ℝ≥0∞) * w * 1 := by rw [mul_one]
          _ ≤ (m : ℝ≥0∞) * w * ((Fintype.card ι : ℝ≥0∞) * α) := by gcongr
          _ = (w * Fintype.card ι) * ((m : ℝ≥0∞) * α) := by ring
          _ ≤ _ := by gcongr; exact le_self_add
      have hn : n ≤ K := by have := hk v; omega
      have hsl : (1 + (m : ℝ≥0∞) * w) * (1 + w * Fintype.card ι) ^ n ≤ Fintype.card ι * α :=
        le_trans (by gcongr; exact le_self_add) hslack
      have := fresh_index n (cnt idx d v) _ _ α _ _ hmw hsl
      simpa using this
  calc freshAvg U (fun u => chProd idx k
        (fun l => ((m : ℝ≥0∞) * α + m * w * nItems idx (u :: items) l) + w * nItems idx items l) (d + {u}))
      = freshAvg U (fun u => perturbed k (fun l => cnt idx d l)
        (fun l => (m : ℝ≥0∞) * α + ((m + 1 : ℕ) : ℝ≥0∞) * w * nItems idx items l) ((m : ℝ≥0∞) * w) (idx u)) := by
        congr 1; funext u; exact hg u
    _ = (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ v, perturbed k (fun l => cnt idx d l)
        (fun l => (m : ℝ≥0∞) * α + ((m + 1 : ℕ) : ℝ≥0∞) * w * nItems idx items l) ((m : ℝ≥0∞) * w) v := hU _
    _ ≤ ∏ l, (charlier (k l) (cnt idx d l) ((m : ℝ≥0∞) * α + ((m + 1 : ℕ) : ℝ≥0∞) * w * nItems idx items l) +
          α * (k l : ℝ≥0∞) *
            charlier (k l - 1) (cnt idx d l) ((m : ℝ≥0∞) * α + ((m + 1 : ℕ) : ℝ≥0∞) * w * nItems idx items l)) := by
        simp only [perturbed_split]
        exact avg_perturbed_le _ _ _ hL he
    _ ≤ ∏ l, charlier (k l) (cnt idx d l)
          (((m : ℝ≥0∞) * α + ((m + 1 : ℕ) : ℝ≥0∞) * w * nItems idx items l) + α) := by
        refine Finset.prod_le_prod' fun l _ => ?_
        rcases hkl : k l with _ | n
        · simp
        · simpa using charlier_lower α n (cnt idx d l) _
    _ = _ := by
        unfold chProd
        refine Finset.prod_congr rfl fun l _ => ?_
        congr 1
        push_cast
        ring

/-- **Factorial moments of the virtual future** are dominated by the Charlier product. -/
theorem virtual_le_chProd (U : Finset V) (hU : UniformIndex idx U) (k : ι → ℕ) (K : ℕ)
    (hk : ∀ l, k l ≤ K + 1) (N : ℕ) (α w : ℝ≥0∞) (hw : w ≤ 1)
    (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (hslack : (1 + N * w) * (1 + w * Fintype.card ι) ^ K ≤ Fintype.card ι * α)
    (hLα : 1 ≤ (Fintype.card ι : ℝ≥0∞) * α) :
    ∀ m, m ≤ N → ∀ items d, virtual U w (fallMono idx k) m items d ≤
      chProd idx k (fun l => (m : ℝ≥0∞) * α + m * w * nItems idx items l) d
  | 0, _, items, d => by
      simp only [virtual, fallMono, chProd, Nat.cast_zero, zero_mul, add_zero]
      exact le_of_eq (Finset.prod_congr rfl fun l _ => (charlier_rate_zero _ _).symm)
  | m + 1, hm, items, d => by
      simp only [virtual]
      have ih := virtual_le_chProd U hU k K hk N α w hw hL hslack hLα m (by omega)
      have hsl : (1 + m * w) * (1 + w * Fintype.card ι) ^ K ≤ Fintype.card ι * α :=
        le_trans (by gcongr; exact_mod_cast (by omega : m ≤ N)) hslack
      calc freshAvg U (fun u => slotValue (virtual U w (fallMono idx k) m (u :: items)) (d + {u})
              (itemCoins w items))
          ≤ freshAvg U (fun u => slotValue (chProd idx k
              (fun l => (m : ℝ≥0∞) * α + m * w * nItems idx (u :: items) l)) (d + {u}) (itemCoins w items)) :=
            freshAvg_mono U fun u _ => slotValue_le_of_le (fun e => ih (u :: items) e) _ _
        _ ≤ freshAvg U (fun u => chProd idx k
              (fun l => ((m : ℝ≥0∞) * α + m * w * nItems idx (u :: items) l) + w * nItems idx items l) (d + {u})) :=
            freshAvg_mono U fun u _ => coins_absorb idx k w hw items _ _
        _ ≤ _ := fresh_step idx U hU k K hk m α w items d hL hsl hLα

/-- Product with one shifted rate. -/
theorem shifted_split (k : ι → ℕ) (ρ : ι → ℝ≥0∞) (s : ℝ≥0∞) (v : ι) :
    ∏ l, (ρ l + if v = l then s else 0) ^ k l = (ρ v + s) ^ k v * ∏ l ∈ Finset.univ.erase v, ρ l ^ k l := by
  rw [prod_split v, if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [if_neg (Finset.ne_of_mem_erase hl).symm, add_zero]

/-- **Creation step.** A potential future pair (landed with probability `lam`, uniform index, coin
rate `Nw` over the remaining slots) is dominated by raising every rate by `γ`. -/
theorem creation_step (U : Finset V) (hU : UniformIndex idx U) (k : ι → ℕ) (K : ℕ) (hk : ∀ l, k l ≤ K + 1)
    (ρ : ι → ℝ≥0∞) (Nw θ lam γ : ℝ≥0∞) (hlam : lam ≤ 1) (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (hρ : ∀ l, Nw ≤ θ * ρ l) (hγ : lam * Nw * (1 + θ) ^ K ≤ Fintype.card ι * γ) :
    (1 - lam) * ∏ l, ρ l ^ k l + lam * freshAvg U (fun v => ∏ l, (ρ l + if idx v = l then Nw else 0) ^ k l) ≤
      ∏ l, (ρ l + γ) ^ k l := by
  set L := (Fintype.card ι : ℝ≥0∞)
  have hLtop : L ≠ ⊤ := ENNReal.natCast_ne_top _
  set b : ι → ℝ≥0∞ := fun l => L⁻¹ * (Nw * (1 + θ) ^ K) * (k l : ℝ≥0∞) * ρ l ^ (k l - 1)
  have he : ∀ v, (ρ v + Nw) ^ k v ≤ ρ v ^ k v + L * b v := by
    intro v
    rcases hkv : k v with _ | n
    · simp
    · have hn : n ≤ K := by have := hk v; omega
      have h1 := pow_add_le (ρ v) Nw n
      have h2 : (ρ v + Nw) ^ n ≤ (1 + θ) ^ n * ρ v ^ n := by
        rw [← mul_pow]; gcongr
        calc ρ v + Nw ≤ ρ v + θ * ρ v := by gcongr; exact hρ v
          _ = (1 + θ) * ρ v := by ring
      have h3 : (1 + θ) ^ n ≤ (1 + θ) ^ K := pow_le_pow_right₀ le_self_add hn
      calc (ρ v + Nw) ^ (n + 1) ≤ ρ v ^ (n + 1) + Nw * ((n + 1 : ℕ) : ℝ≥0∞) * (ρ v + Nw) ^ n := h1
        _ ≤ ρ v ^ (n + 1) + Nw * ((n + 1 : ℕ) : ℝ≥0∞) * ((1 + θ) ^ K * ρ v ^ n) := by
            gcongr; exact le_trans h2 (by gcongr)
        _ = ρ v ^ (n + 1) + (L * L⁻¹) * (Nw * (1 + θ) ^ K) * ((n + 1 : ℕ) : ℝ≥0∞) * ρ v ^ n := by
            rw [ENNReal.mul_inv_cancel hL hLtop]; ring
        _ = ρ v ^ (n + 1) + L * b v := by simp only [b, hkv]; push_cast; ring_nf
  have havg : freshAvg U (fun v => ∏ l, (ρ l + if idx v = l then Nw else 0) ^ k l) ≤
      ∏ l, ρ l ^ k l + ∑ v, b v * ∏ l ∈ Finset.univ.erase v, ρ l ^ k l := by
    rw [hU (fun v => ∏ l, (ρ l + if v = l then Nw else 0) ^ k l)]
    simp only [shifted_split]
    exact avg_perturbed_lin _ _ _ hL he
  calc (1 - lam) * ∏ l, ρ l ^ k l + lam * freshAvg U (fun v => ∏ l, (ρ l + if idx v = l then Nw else 0) ^ k l)
      ≤ (1 - lam) * ∏ l, ρ l ^ k l + lam * (∏ l, ρ l ^ k l + ∑ v, b v * ∏ l ∈ Finset.univ.erase v, ρ l ^ k l) := by
        gcongr
    _ = ∏ l, ρ l ^ k l + ∑ v, (lam * b v) * ∏ l ∈ Finset.univ.erase v, ρ l ^ k l := by
        rw [mul_add, ← add_assoc, ← add_mul, tsub_add_cancel_of_le hlam, one_mul, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun v _ => by ring
    _ ≤ ∏ l, (ρ l ^ k l + lam * b l) := prod_add_ge _ _ _
    _ ≤ ∏ l, (ρ l + γ) ^ k l := by
        refine Finset.prod_le_prod' fun l _ => ?_
        rcases hkl : k l with _ | n
        · simp [b, hkl]
        · have hγ' : lam * (L⁻¹ * (Nw * (1 + θ) ^ K)) ≤ γ := by
            calc lam * (L⁻¹ * (Nw * (1 + θ) ^ K)) = L⁻¹ * (lam * Nw * (1 + θ) ^ K) := by ring
              _ ≤ L⁻¹ * (L * γ) := by gcongr
              _ = γ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hL hLtop, one_mul]
          calc ρ l ^ (n + 1) + lam * b l
              = ρ l ^ (n + 1) + (lam * (L⁻¹ * (Nw * (1 + θ) ^ K))) * ((n + 1 : ℕ) : ℝ≥0∞) * ρ l ^ n := by
                simp only [b, hkl]; push_cast; ring_nf
            _ ≤ ρ l ^ (n + 1) + γ * ((n + 1 : ℕ) : ℝ≥0∞) * ρ l ^ n := by gcongr
            _ ≤ (ρ l + γ) ^ (n + 1) := pow_add_ge _ _ n

end SphincsFors.Security.H0
