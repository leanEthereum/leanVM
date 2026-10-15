import SphincsFors.H0Assembly
import SphincsFors.BridgeVirtualOnce

/-! The H-term of the one-coin virtual future (`virtualOnce`): fresh slots at the uniform rate
`α = 1/L` per index, and one coin per future pair. Its joint factorial moments are dominated by
the Poisson product at rate `N α + q γ`, with `γ` the coin rate of the future pairs alone. -/

open ENNReal

namespace SphincsFors.Security.H0

open Domination

set_option linter.unusedSectionVars false

variable {V ι : Type} [DecidableEq ι] [Fintype ι] (idx : V → ι)

/-- The H-term operator of the one-coin future. -/
noncomputable def hTermO (U : Finset V) (w lam : ℝ≥0∞) (N q : ℕ) (f : Multiset V → ℝ≥0∞) : ℝ≥0∞ :=
  creations U lam (fun I => virtualOnce U w f N I 0) q []

theorem hTermO_zero (U : Finset V) (hU : U.Nonempty) (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ) :
    hTermO U w lam N q (fun _ => 0) = 0 := by
  unfold hTermO
  simp only [virtualOnce_const hU hw 0]
  exact creations_const hU hlam 0 q []

theorem hTermO_add (U : Finset V) (hU : U.Nonempty) (w lam : ℝ≥0∞) (N q : ℕ) (f g : Multiset V → ℝ≥0∞) :
    hTermO U w lam N q (fun d => f d + g d) = hTermO U w lam N q f + hTermO U w lam N q g := by
  unfold hTermO
  simp only [virtualOnce_add hU f g]
  exact creations_add _ _ q []

theorem hTermO_const_mul (U : Finset V) (w lam : ℝ≥0∞) (N q : ℕ) (c : ℝ≥0∞) (f : Multiset V → ℝ≥0∞) :
    hTermO U w lam N q (fun d => c * f d) = c * hTermO U w lam N q f := by
  unfold hTermO
  simp only [virtualOnce_const_mul c f]
  exact creations_const_mul c _ q []

theorem hTermO_sum {τ : Type} [DecidableEq τ] (U : Finset V) (hU : U.Nonempty) (w lam : ℝ≥0∞) (hw : w ≤ 1)
    (hlam : lam ≤ 1) (N q : ℕ) (s : Finset τ) (c : τ → ℝ≥0∞) (g : τ → Multiset V → ℝ≥0∞) :
    hTermO U w lam N q (fun d => ∑ x ∈ s, c x * g x d) = ∑ x ∈ s, c x * hTermO U w lam N q (g x) := by
  induction s using Finset.induction_on with
  | empty => simpa using hTermO_zero U hU w lam hw hlam N q
  | insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      rw [hTermO_add U hU w lam N q (fun d => c j * g j d) (fun d => ∑ x ∈ s, c x * g x d), ih,
        hTermO_const_mul]

/-- **Fresh slots and coins.** The one-coin future of a falling-factorial monomial is dominated by
the Charlier product at the fresh rate plus `w` per item. -/
theorem virtualOnce_le_chProd (U : Finset V) (hU : UniformIndex idx U) (k : ι → ℕ) (K : ℕ)
    (hk : ∀ l, k l ≤ K + 1) (N : ℕ) (α w : ℝ≥0∞) (hw : w ≤ 1) (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (hLα : 1 ≤ (Fintype.card ι : ℝ≥0∞) * α) (items : List V) (d : Multiset V) :
    virtualOnce U w (fallMono idx k) N items d ≤
      chProd idx k (fun l => (N : ℝ≥0∞) * α + w * nItems idx items l) d := by
  have hslack : (1 + N * (0 : ℝ≥0∞)) * (1 + 0 * Fintype.card ι) ^ K ≤ Fintype.card ι * α := by simpa using hLα
  have hfresh : ∀ e, fresh U (fallMono idx k) N e ≤ chProd idx k (fun _ => (N : ℝ≥0∞) * α) e := by
    intro e
    rw [fresh_eq_virtual N [] e]
    have h := virtual_le_chProd idx U hU k K hk N α 0 zero_le_one hL hslack hLα N le_rfl [] e
    simpa using h
  unfold virtualOnce
  exact le_trans (slotValue_le_of_le hfresh _ _) (coins_absorb idx k w hw items _ d)

/-- **Creations** with one coin per future pair. -/
theorem creations_leO (U : Finset V) (hU : UniformIndex idx U) (k : ι → ℕ) (K : ℕ) (hk : ∀ l, k l ≤ K + 1)
    (N : ℕ) (hN : 1 ≤ N) (α w lam γ : ℝ≥0∞) (hlam : lam ≤ 1) (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (hLα : 1 ≤ (Fintype.card ι : ℝ≥0∞) * α)
    (hγ : lam * w * (1 + w * Fintype.card ι) ^ K ≤ Fintype.card ι * γ) :
    ∀ (j : ℕ) (items : List V),
      creations U lam (fun I => chProd idx k (fun l => (N : ℝ≥0∞) * α + w * nItems idx I l) 0) j items ≤
        ∏ l, ((N : ℝ≥0∞) * α + w * nItems idx items l + j * γ) ^ k l
  | 0, items => by
      simp only [creations, chProd, cnt_zero, charlier_zero_shift, Nat.cast_zero, zero_mul, add_zero, le_refl]
  | j + 1, items => by
      simp only [creations]
      have ih := creations_leO U hU k K hk N hN α w lam γ hlam hL hLα hγ j
      have hcons : ∀ v, ∏ l, ((N : ℝ≥0∞) * α + w * nItems idx (v :: items) l + j * γ) ^ k l =
          ∏ l, (((N : ℝ≥0∞) * α + w * nItems idx items l + j * γ) + if idx v = l then w else 0) ^ k l := by
        intro v
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [nItems_cons]
        congr 1
        split_ifs <;> push_cast <;> ring
      have hρ : ∀ l, w ≤ (w * Fintype.card ι) * ((N : ℝ≥0∞) * α + w * nItems idx items l + j * γ) := by
        intro l
        have hN' : (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hN
        calc w = w * 1 := by rw [mul_one]
          _ ≤ w * ((Fintype.card ι : ℝ≥0∞) * α) := by gcongr
          _ ≤ w * ((Fintype.card ι : ℝ≥0∞) * ((N : ℝ≥0∞) * α)) := by
              gcongr
              calc α = 1 * α := by rw [one_mul]
                _ ≤ (N : ℝ≥0∞) * α := by gcongr
          _ = (w * Fintype.card ι) * ((N : ℝ≥0∞) * α) := by ring
          _ ≤ _ := by gcongr; exact le_trans le_self_add le_self_add
      calc (1 - lam) * creations U lam (fun I => chProd idx k (fun l => (N : ℝ≥0∞) * α + w * nItems idx I l) 0) j items +
            lam * freshAvg U (fun v => creations U lam
              (fun I => chProd idx k (fun l => (N : ℝ≥0∞) * α + w * nItems idx I l) 0) j (v :: items))
          ≤ (1 - lam) * ∏ l, ((N : ℝ≥0∞) * α + w * nItems idx items l + j * γ) ^ k l +
            lam * freshAvg U (fun v => ∏ l, (((N : ℝ≥0∞) * α + w * nItems idx items l + j * γ) +
              if idx v = l then w else 0) ^ k l) := by
            gcongr
            · exact ih items
            · exact freshAvg_mono U fun v _ => le_trans (ih (v :: items)) (le_of_eq (hcons v))
        _ ≤ ∏ l, (((N : ℝ≥0∞) * α + w * nItems idx items l + j * γ) + γ) ^ k l :=
            creation_step idx U hU k K hk _ _ _ lam γ hlam hL hρ hγ
        _ = _ := by
            refine Finset.prod_congr rfl fun l _ => ?_
            push_cast; ring_nf

/-- **Joint factorial moments of the one-coin H-term are Poisson-dominated.** -/
theorem H0_fallMono_leO (U : Finset V) (hU : UniformIndex idx U) (k : ι → ℕ) (K : ℕ) (hk : ∀ l, k l ≤ K + 1)
    (N q : ℕ) (hN : 1 ≤ N) (α w lam γ : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (hLα : 1 ≤ (Fintype.card ι : ℝ≥0∞) * α)
    (hγ : lam * w * (1 + w * Fintype.card ι) ^ K ≤ Fintype.card ι * γ) :
    creations U lam (fun I => virtualOnce U w (fallMono idx k) N I 0) q [] ≤ ((N : ℝ≥0∞) * α + q * γ) ^ ∑ l, k l := by
  calc creations U lam (fun I => virtualOnce U w (fallMono idx k) N I 0) q []
      ≤ creations U lam (fun I => chProd idx k (fun l => (N : ℝ≥0∞) * α + w * nItems idx I l) 0) q [] :=
        creations_mono (fun I => virtualOnce_le_chProd idx U hU k K hk N α w hw hL hLα I 0) q []
    _ ≤ ∏ l, ((N : ℝ≥0∞) * α + w * nItems idx [] l + q * γ) ^ k l :=
        creations_leO idx U hU k K hk N hN α w lam γ hlam hL hLα hγ q []
    _ = _ := by simp [nItems, Finset.prod_pow_eq_pow_sum]

end SphincsFors.Security.H0
