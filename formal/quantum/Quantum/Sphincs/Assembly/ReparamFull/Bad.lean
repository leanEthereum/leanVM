module

public import Quantum.Sphincs.Assembly.ReparamFull.Game
public import Quantum.Sphincs.Assembly.PathsDisjoint

@[expose] public section

/-!
# The composed reparametrization of leanSPHINCS's tables: the good set and its bad fraction

* **The good set** `FullG S`: the core good set (`FullGCore`: the stage good sets for the
  computations `compQ`, a good permutation, `HRateSep`, Reparam's `XGood`), PathsDisjoint's
  `PathsDisjoint` at the template data, and a static condition `S` on the template data (the slot
  for SP-PF1's good-data conditions; `fun _ _ ↦ True` for none).
* **Static conditions move to the coordinates** (`frac_fwd_le`): `fullE` is injective where
  Reparam's table is good and the coordinates before the final bijection are as many as the padded
  tables, so the tables whose template data fail `S` are at most the coordinates failing it.
* `fullG_frac_le_keccak`: at most `2^-77` of the padded tables are outside the good set with no
  static condition, plus the static condition's fraction of the coordinates. The dominant term is
  DigestStage's read term over its `2^385` labels: `Σᵢ qᵢ / 2^122` with `Σᵢ qᵢ ≤ 2^44`
  (`sum_compReads_le`).
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer MasterSeed)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (CoinSlots)
open Quantum.SufCma (honestEval)
open Quantum.Xmss.Assembly (fwd injOn_fwd XW inv_card_mul_card_filter_comp_fst card_filter_notMem_eq
  card_filter_le_of_injOn permTerm_le_keccak)
open Quantum.Sphincs.Hybrid (Tab DTab DLab Secret SeedKS SkIdx rCell rOrd dLabCell dLabMsg dLabOrd
  schemeSplit schemeGood seedKGood dGood permSplit skCell card_skIdx_eq rCell_injective_msg
  skCell_ne_rCell
  card_message seedKGood_frac_le_keccak dGood_frac_le_keccak schemeGood_frac_le)

namespace Quantum.Sphincs.Assembly

/-! ## Finiteness -/

section fin

noncomputable instance instFintypeFT : Fintype FT :=
  instFintypeProd _ _

noncomputable instance instFintypeRestF : Fintype RestF :=
  instFintypeProd _ _

noncomputable instance instFintypeRTabS : Fintype RTabS :=
  instFintypeProd _ _

/-- Reparam's coordinates with the rest. -/
abbrev YS : Type := (((Z → X) × XW) × (ValPos → Digest)) × RestF

noncomputable instance instFintypeYS : Fintype YS :=
  instFintypeProd _ _

instance instNonemptyRestF : Nonempty RestF :=
  ⟨Classical.arbitrary _⟩

/-- The coordinates before the final bijection are as many as the padded tables. -/
theorem card_YS : Fintype.card YS = Fintype.card FT :=
  Fintype.card_congr ((rtabS.prodCongr (Equiv.refl RestF)).trans phiE.symm)

end fin

/-! ## Static conditions on the coordinates -/

section static

/-- The coordinates before the final bijection of a padded table. -/
noncomputable def yOf (t : FT) : YS :=
  (fwd sphFix sO (phiE t).1, (phiE t).2)

theorem fullE_eq_psiE (t : FT) : fullE t = psiE (yOf t) :=
  rfl

open scoped Classical in
/-- **A static condition moves to the coordinates**: the padded tables with Reparam's table good
whose coordinates fail `S` are at most the coordinates failing `S`. -/
theorem frac_fwd_le (S : YS → Prop) :
    (Fintype.card FT : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ XGood (phiE t).1 ∧ ¬S (yOf t)).card ≤
      (Fintype.card YS : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : YS ↦ ¬S y).card := by
  rw [← card_YS]
  gcongr
  refine card_filter_le_of_injOn yOf _ _ (fun _ h ↦ h.2) fun t₁ t₂ h₁ h₂ e ↦ ?_
  have hθ := injOn_fwd sO_consistent (good_of_xGood h₁.1) (good_of_xGood h₂.1) (Prod.mk.inj e).1
  exact phiE.injective (Prod.ext hθ (Prod.mk.inj e).2)

end static

/-! ## The good set -/

/-- **The good set**: the core good set, `PathsDisjoint` at the template data, and the static
condition `S` on the template data. -/
def FullG (S : PP → ((s : HPos) → XD s) → Prop) (t : FT) : Prop :=
  FullGCore t ∧ PathsDisjoint (pubP (fullE t).1).xw (pubP (fullE t).1).keys.1
    (valsOf (fullE t).2.1) ∧ S (fullE t).1 (fullE t).2.1

/-- **On the good set the template data avoid the output cells** (`PathsAvoid`). -/
theorem pathsAvoid_fullE {t : FT} (ht : FullGCore t) :
    PathsAvoid (pubP (fullE t).1).xw (pubP (fullE t).1).keys.1 (valsOf (fullE t).2.1) := by
  have h : PathsAvoid (fwd sphFix sO (phiE t).1).1.2 (fwd sphFix sO (phiE t).1).1.1
      (fwd sphFix sO (phiE t).1).2 := (xGoodPV_fwd ht.2.2.2).2
  rw [pubP, sPub_xw, sPub_keys_fst]
  exact h

/-! ## The bad fraction -/

section bad

/-- A union bound for a complement covered by five events. -/
theorem card_filter_not_le_five {Y : Type*} [Fintype Y] (GP P₁ P₂ P₃ P₄ P₅ : Y → Prop)
    [DecidablePred GP] [DecidablePred P₁] [DecidablePred P₂] [DecidablePred P₃]
    [DecidablePred P₄] [DecidablePred P₅] (h : ∀ y, ¬GP y → P₁ y ∨ P₂ y ∨ P₃ y ∨ P₄ y ∨ P₅ y) :
    (Finset.univ.filter fun y ↦ ¬GP y).card ≤
      (Finset.univ.filter P₁).card + (Finset.univ.filter P₂).card +
        (Finset.univ.filter P₃).card + (Finset.univ.filter P₄).card +
          (Finset.univ.filter P₅).card := by
  classical
  refine (Finset.card_le_card fun y hy ↦ ?_).trans
    ((Finset.card_union_le _ _).trans (add_le_add ((Finset.card_union_le _ _).trans
      (add_le_add ((Finset.card_union_le _ _).trans (add_le_add (Finset.card_union_le _ _)
        le_rfl)) le_rfl)) le_rfl))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
  rcases h y hy with h1 | h2 | h3 | h4 | h5
  · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h2)))
  · exact Or.inl (Or.inl (Or.inr h3))
  · exact Or.inl (Or.inr h4)
  · exact Or.inr h5

/-- A union bound for a complement covered by three events. -/
theorem card_filter_not_le_three {Y : Type*} [Fintype Y] (GP P₁ P₂ P₃ : Y → Prop)
    [DecidablePred GP] [DecidablePred P₁] [DecidablePred P₂] [DecidablePred P₃]
    (h : ∀ y, ¬GP y → P₁ y ∨ P₂ y ∨ P₃ y) :
    (Finset.univ.filter fun y ↦ ¬GP y).card ≤
      (Finset.univ.filter P₁).card + (Finset.univ.filter P₂).card +
        (Finset.univ.filter P₃).card := by
  classical
  refine (Finset.card_le_card fun y hy ↦ ?_).trans
    ((Finset.card_union_le _ _).trans (add_le_add (Finset.card_union_le _ _) le_rfl))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
  rcases h y hy with h1 | h2 | h3
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr h2)
  · exact Or.inr h3

/-- A count bound by five parts, as fractions. -/
theorem inv_mul_le_five {N g a b c d e : ℕ} (h : g ≤ a + b + c + d + e) :
    (N : ℝ≥0∞)⁻¹ * g ≤ (N : ℝ≥0∞)⁻¹ * a + (N : ℝ≥0∞)⁻¹ * b + (N : ℝ≥0∞)⁻¹ * c +
      (N : ℝ≥0∞)⁻¹ * d + (N : ℝ≥0∞)⁻¹ * e := by
  rw [← mul_add, ← mul_add, ← mul_add, ← mul_add]
  gcongr
  exact_mod_cast h

/-- The padded tables as the digest stage's tables and the rest. -/
def eDT : FT ≃ DTab Message DLab × ((SeedKS × (ValPos → Digest)) × StrPad) where
  toFun t := (t.1.1.1, ((t.1.1.2, t.1.2), t.2))
  invFun x := (((x.1, x.2.1.1), x.2.1.2), x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The padded tables as SeedStage's tables and the rest. -/
def eST : FT ≃ (Tab × SeedKS) ×
    (((CoinSlots Message × CoinSlots DLab) × (ValPos → Digest)) × StrPad) where
  toFun t := ((t.1.1.1.1.1, t.1.1.2), (((t.1.1.1.1.2, t.1.1.1.2), t.1.2), t.2))
  invFun x := (((((x.1.1, x.2.1.1.1), x.2.1.1.2), x.1.2), x.2.1.2), x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The padded tables as SchemeSplit's tables and the rest. -/
def eTT : FT ≃ Tab × ((((CoinSlots Message × CoinSlots DLab) × SeedKS) × (ValPos → Digest)) ×
    StrPad) where
  toFun t := (t.1.1.1.1.1, ((((t.1.1.1.1.2, t.1.1.1.2), t.1.1.2), t.1.2), t.2))
  invFun x := (((((x.1, x.2.1.1.1.1), x.2.1.1.1.2), x.2.1.1.2), x.2.1.2), x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The padded tables as the permutation and the rest. -/
noncomputable def ePT : FT ≃ Equiv.Perm (X × Z) ×
    (((SpongeKeys X Z × MasterSeed) × Quantum.Sphincs.Hybrid.SeedSlots) ×
      ((((CoinSlots Message × CoinSlots DLab) × SeedKS) × (ValPos → Digest)) × StrPad)) :=
  eTT.trans ((permSplit.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))

theorem ePT_fst (t : FT) : (ePT t).1 = (tabOf t).perm :=
  rfl

/-- `ofReal` sums. -/
theorem add_le_ofReal_add {x y : ℝ≥0∞} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hx : x ≤ ENNReal.ofReal r) (hy : y ≤ ENNReal.ofReal s) : x + y ≤ ENNReal.ofReal (r + s) :=
  (add_le_add hx hy).trans_eq (ENNReal.ofReal_add hr hs).symm

set_option exponentiation.threshold 4096 in
/-- SchemeSplit's per-computation read term at Keccak's sizes. -/
theorem schemeReadTerm_le_sph (q : ℕ) :
    (Fintype.card SkIdx : ℝ≥0∞) * ((18 : ℕ) + 1) * q / Fintype.card Z ≤
      ENNReal.ofReal (q / 2 ^ 463) := by
  have h : (Fintype.card SkIdx : ℝ≥0∞) * ((18 : ℕ) + 1) * q =
      (((27 * 2 ^ 39 + 2) * 19 * q : ℕ) : ℝ≥0∞) := by
    rw [card_skIdx_eq]
    push_cast
    ring
  have hn : (27 * 2 ^ 39 + 2) * 19 * q * 2 ^ 463 ≤ q * 2 ^ 512 := by
    calc (27 * 2 ^ 39 + 2) * 19 * q * 2 ^ 463 = q * ((27 * 2 ^ 39 + 2) * 19 * 2 ^ 463) := by ring
      _ ≤ q * 2 ^ 512 := Nat.mul_le_mul_left q (by norm_num)
  rw [h, Quantum.Xmss.Hybrid.R0.card_cap,
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hn

set_option exponentiation.threshold 4096 in
/-- SchemeSplit's static collision term at Keccak's sizes. -/
theorem schemeCollTerm_le_sph :
    ((Fintype.card SkIdx * Fintype.card SkIdx * (18 + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z ≤
      ENNReal.ofReal (1 / 2 ^ 419) := by
  rw [card_skIdx_eq, Quantum.Xmss.Hybrid.R0.card_cap,
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

/-- The per-computation terms summed over the computations. -/
theorem sum_compTerms_le (a b : ℕ) :
    ∑ i : CIdx, ((compReads i : ℝ≥0∞) / 2 ^ a + ENNReal.ofReal (compReads i / 2 ^ b)) ≤
      ENNReal.ofReal (2 ^ 44 / 2 ^ a + 2 ^ 44 / 2 ^ b) := by
  have hN : ((∑ i, compReads i : ℕ) : ℝ) ≤ 2 ^ 44 := by exact_mod_cast sum_compReads_le
  rw [Finset.sum_add_distrib]
  refine add_le_ofReal_add (by positivity) (by positivity) ?_ ?_
  · rw [← ENNReal.sum_div, ← Nat.cast_sum, ← ENNReal.ofReal_natCast,
      show (2 : ℝ≥0∞) ^ a = ENNReal.ofReal (2 ^ a) by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hN (by positivity))
  · rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity, ← Finset.sum_div]
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by positivity))
    exact_mod_cast hN

/-- SchemeSplit's per-computation terms summed over the computations. -/
theorem sum_schemeTerms_le :
    ∑ i : CIdx, ((compReads i : ℝ≥0∞) / 2 ^ 256 +
        Fintype.card SkIdx * ((18 : ℕ) + 1) * compReads i / Fintype.card Z) ≤
      ENNReal.ofReal (2 ^ 44 / 2 ^ 256 + 2 ^ 44 / 2 ^ 463) :=
  (Finset.sum_le_sum fun i _ ↦ add_le_add le_rfl (schemeReadTerm_le_sph (compReads i))).trans
    (sum_compTerms_le 256 463)

theorem compReads_hq (i : CIdx) (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z))
    (P : PublicParameter) (Cs : KeygenDomain → HashOutput) :
    (honestEval t π (compQ i P Cs)).2.length ≤ compReads i :=
  length_honestEval_compQ i t π P Cs

open scoped Classical in
/-- **SchemeSplit's bad fraction at Keccak's sizes** for the computations `compQ`. -/
theorem schemeGood_frac_le_sph :
    (Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood compQ).card : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / 2 ^ 777 + 1 / 2 ^ 419 + (2 ^ 44 / 2 ^ 256 + 2 ^ 44 / 2 ^ 463)) := by
  have h := schemeGood_frac_le 18 compQ compReads compReads compReads_hq fun i t π P Cs ↦
    (Finset.card_filter_le _ _).trans
      ((Quantum.Xmss.Hybrid.card_kCells_le _).trans (compReads_hq i t π P Cs))
  exact h.trans (add_le_ofReal_add (by positivity) (by positivity)
    (add_le_ofReal_add (by positivity) (by positivity) permTerm_le_keccak schemeCollTerm_le_sph)
    sum_schemeTerms_le)

theorem compReads_hqk {P' : PublicParameter → X → Prop} [∀ P, DecidablePred (P' P)] (i : CIdx)
    (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
    (Cs : KeygenDomain → HashOutput) :
    ((Quantum.Xmss.Hybrid.kCells (honestEval t π (compQ i P Cs)).2).filter (P' P)).card ≤
      compReads i :=
  (Finset.card_filter_le _ _).trans
    ((Quantum.Xmss.Hybrid.card_kCells_le _).trans (compReads_hq i t π P Cs))

/-- The `ofReal` bound of SchemeSplit's fraction. -/
noncomputable abbrev sfR : ℝ := 1 / 2 ^ 777 + 1 / 2 ^ 419 + (2 ^ 44 / 2 ^ 256 + 2 ^ 44 / 2 ^ 463)

open scoped Classical in
/-- **DigestStage's bad fraction at Keccak's sizes** for the computations `compQ`. -/
theorem dGood_frac_le_sph :
    (Fintype.card (DTab Message DLab) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (DTab Message DLab) -
          (dGood rCell rOrd dLabCell dLabMsg dLabOrd compQ).card : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (((sfR + 1 / 2 ^ 777) + 1 / 2 ^ 207 + (2 ^ 44 / 2 ^ 256 + 2 ^ 44 / 2 ^ 251)) +
        (1 / 2 ^ 777 + 1 / 2 ^ 316) + (2 ^ 44 / 2 ^ 128 + 2 ^ 44 / 2 ^ 122)) := by
  refine (dGood_frac_le_keccak compQ compReads compReads compReads compReads_hq
    compReads_hqk compReads_hqk).trans ?_
  refine add_le_ofReal_add (by positivity) (by positivity) (add_le_ofReal_add (by positivity)
    (by positivity) (add_le_ofReal_add (by positivity) (by positivity) (add_le_ofReal_add
      (by positivity) (by positivity) (add_le_ofReal_add (by positivity) (by positivity)
        schemeGood_frac_le_sph permTerm_le_keccak) le_rfl) (sum_compTerms_le 256 251))
    (add_le_ofReal_add (by positivity) (by positivity) permTerm_le_keccak le_rfl))
    (sum_compTerms_le 128 122)

theorem rCellS_injective (P : PublicParameter) (s : Secret) :
    Function.Injective fun M ↦ rCellS M P s :=
  rCell_injective_msg P s.2

theorem skCell_ne_rCellS (P : PublicParameter) (s : Secret) (M : Message) (b : SkIdx) :
    skCell P s.1 b ≠ rCellS M P s :=
  skCell_ne_rCell P s.1 b M s.2

open scoped Classical in
/-- **SeedStage's bad fraction at Keccak's sizes** for the computations `compQ`. -/
theorem seedKGood_frac_le_sph :
    (Fintype.card (Tab × SeedKS) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (Tab × SeedKS) - (seedKGood rCellS compQ).card : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal ((sfR + 1 / 2 ^ 777) + 1 / 2 ^ 574 + (2 ^ 44 / 2 ^ 256 + 2 ^ 44 / 2 ^ 464)) :=
  (seedKGood_frac_le_keccak compQ compReads compReads compReads_hq compReads_hqk
    rCellS_injective skCell_ne_rCellS card_message.le).trans
    (add_le_ofReal_add (by positivity) (by positivity) (add_le_ofReal_add (by positivity)
      (by positivity) (add_le_ofReal_add (by positivity) (by positivity) schemeGood_frac_le_sph
        permTerm_le_keccak) le_rfl) (sum_compTerms_le 256 464))

open scoped Classical in
theorem card_filter_notMem_eq' {α : Type*} [Fintype α] (G : Finset α) :
    (Finset.univ.filter fun x ↦ x ∉ G).card = Fintype.card α - G.card := by
  convert card_filter_notMem_eq G

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The core bad fraction at Keccak's sizes**: at most `2^-77` of the padded tables are outside
the core good set. DigestStage's read term `Σᵢ qᵢ / 2^122 ≤ 2^-78` dominates. -/
theorem fullGCore_frac_le_keccak :
    (Fintype.card FT : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬FullGCore t).card ≤
      ENNReal.ofReal (1 / 2 ^ 77) := by
  have h5 := card_filter_not_le_five FullGCore
    (fun t ↦ (eDT t).1 ∉ dGood rCell rOrd dLabCell dLabMsg dLabOrd compQ)
    (fun t ↦ (eST t).1 ∉ seedKGood rCellS compQ)
    (fun t ↦ ¬PermGood (ePT t).1 18)
    (fun t ↦ ¬HRateSep (schemeSplit (eTT t).1))
    (fun t ↦ ¬XGood (phiE t).1) fun t ht ↦ by
      by_cases h1 : t.1.1.1 ∈ dGood rCell rOrd dLabCell dLabMsg dLabOrd compQ
      · by_cases h2 : (t.1.1.1.1.1, t.1.1.2) ∈ seedKGood rCellS compQ
        · by_cases h3 : PermGood (tabOf t).perm 18
          · by_cases h4 : HRateSep (schemeSplit t.1.1.1.1.1)
            · exact Or.inr (Or.inr (Or.inr (Or.inr fun h5 ↦ ht ⟨⟨h1, h2⟩, h3, h4, h5⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
          · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inl h2)
      · exact Or.inl h1
  have e1 := inv_card_mul_card_filter_comp_fst eDT
    (fun x ↦ x ∉ dGood rCell rOrd dLabCell dLabMsg dLabOrd compQ)
  rw [card_filter_notMem_eq', ENNReal.div_eq_inv_mul] at e1
  have e2 := inv_card_mul_card_filter_comp_fst eST (fun x ↦ x ∉ seedKGood rCellS compQ)
  rw [card_filter_notMem_eq', ENNReal.div_eq_inv_mul] at e2
  have e3 := inv_card_mul_card_filter_comp_fst ePT (fun π ↦ ¬PermGood π 18)
  have e4 := inv_card_mul_card_filter_comp_fst eTT (fun t ↦ ¬HRateSep (schemeSplit t))
  rw [ENNReal.div_eq_inv_mul] at e4
  have e5 := inv_card_mul_card_filter_comp_fst phiE (fun θ ↦ ¬XGood θ)
  rw [ENNReal.div_eq_inv_mul] at e5
  refine (inv_mul_le_five h5).trans ?_
  rw [e1, e2, e3, e4, e5]
  refine (add_le_ofReal_add (by positivity) (by positivity) (add_le_ofReal_add (by positivity)
    (by positivity) (add_le_ofReal_add (by positivity) (by positivity) (add_le_ofReal_add
      (by positivity) (by positivity) dGood_frac_le_sph seedKGood_frac_le_sph)
        permTerm_le_keccak) hRateSep_frac_le_keccak) xGood_bad_frac_le).trans
    (ENNReal.ofReal_le_ofReal ?_)
  norm_num

/-- Fractions are kept by a bijection. -/
theorem frac_comp_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (p : B → Prop)
    [DecidablePred p] :
    (Fintype.card A : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun a ↦ p (e a)).card =
      (Fintype.card B : ℝ≥0∞)⁻¹ * (Finset.univ.filter p).card := by
  rw [Fintype.card_congr e, Finset.card_equiv e (t := Finset.univ.filter p) fun a ↦ by simp]

/-- Reparam's coordinates with the rest, as PathsDisjoint's coordinates. -/
def eYP : YS ≃ (((Z → X) × XW) × RestF) × (ValPos → Digest) where
  toFun y := ((y.1.1, y.2), y.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem pathsDisjoint_psiE_iff (y : YS) :
    PathsDisjoint (pubP (psiE y).1).xw (pubP (psiE y).1).keys.1 (valsOf (psiE y).2.1) ↔
      ¬PathMeet (eYP y).1.1.2 (eYP y).1.1.1 (eYP y).2 := by
  rw [pubP, sPub_xw, sPub_keys_fst]
  exact Iff.rfl

open scoped Classical in
/-- **PathsDisjoint's fraction on the coordinates**: at most `2^-400`. -/
theorem frac_pathsDisjoint_le :
    (Fintype.card YS : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : YS ↦
        ¬PathsDisjoint (pubP (psiE y).1).xw (pubP (psiE y).1).keys.1
          (valsOf (psiE y).2.1)).card ≤ ENNReal.ofReal (1 / 2 ^ 400) := by
  have hf : (Finset.univ.filter fun y : YS ↦
      ¬PathsDisjoint (pubP (psiE y).1).xw (pubP (psiE y).1).keys.1 (valsOf (psiE y).2.1)) =
      Finset.univ.filter fun y : YS ↦ PathMeet (eYP y).1.1.2 (eYP y).1.1.1 (eYP y).2 :=
    Finset.filter_congr fun y _ ↦ by rw [pathsDisjoint_psiE_iff, not_not]
  rw [hf, frac_comp_equiv eYP (fun x ↦ PathMeet x.1.1.2 x.1.1.1 x.2)]
  exact pathMeet_frac_le_keccak RestF

open scoped Classical in
/-- **The bad fraction of the good set at Keccak's sizes**: at most `2^-77 + 2^-400` of the padded
tables are outside it, plus the static condition's fraction of the coordinates. -/
theorem fullG_frac_le_keccak (S : PP → ((s : HPos) → XD s) → Prop) :
    (Fintype.card FT : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬FullG S t).card ≤
      ENNReal.ofReal (1 / 2 ^ 77) + ENNReal.ofReal (1 / 2 ^ 400) +
        (Fintype.card YS : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun y : YS ↦ ¬S (psiE y).1 (psiE y).2.1).card := by
  have hc := card_filter_not_le_three (FullG S) (fun t ↦ ¬FullGCore t)
    (fun t ↦ XGood (phiE t).1 ∧
      ¬PathsDisjoint (pubP (psiE (yOf t)).1).xw (pubP (psiE (yOf t)).1).keys.1
        (valsOf (psiE (yOf t)).2.1))
    (fun t ↦ XGood (phiE t).1 ∧ ¬S (psiE (yOf t)).1 (psiE (yOf t)).2.1) fun t ht ↦ by
      by_cases h1 : FullGCore t
      · by_cases h2 : PathsDisjoint (pubP (fullE t).1).xw (pubP (fullE t).1).keys.1
            (valsOf (fullE t).2.1)
        · exact Or.inr (Or.inr ⟨h1.2.2.2, fun h3 ↦ ht ⟨h1, h2, h3⟩⟩)
        · exact Or.inr (Or.inl ⟨h1.2.2.2, h2⟩)
      · exact Or.inl h1
  have h2 := frac_fwd_le (fun y ↦ PathsDisjoint (pubP (psiE y).1).xw (pubP (psiE y).1).keys.1
    (valsOf (psiE y).2.1))
  have h3 := frac_fwd_le (fun y ↦ S (psiE y).1 (psiE y).2.1)
  calc (Fintype.card FT : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬FullG S t).card
      ≤ (Fintype.card FT : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬FullGCore t).card +
          (Fintype.card FT : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ XGood (phiE t).1 ∧
            ¬PathsDisjoint (pubP (psiE (yOf t)).1).xw (pubP (psiE (yOf t)).1).keys.1
              (valsOf (psiE (yOf t)).2.1)).card +
          (Fintype.card FT : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ XGood (phiE t).1 ∧
            ¬S (psiE (yOf t)).1 (psiE (yOf t)).2.1).card := by
        rw [← mul_add, ← mul_add]
        gcongr
        exact_mod_cast hc
    _ ≤ _ := add_le_add (add_le_add fullGCore_frac_le_keccak (h2.trans frac_pathsDisjoint_le)) h3

end bad

end Quantum.Sphincs.Assembly

end
