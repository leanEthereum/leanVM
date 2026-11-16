module

public import Quantum.Sphincs.Assembly.ChgRev
public import Quantum.Sphincs.Assembly.CandCharge
public import Quantum.Xmss.Assembly.CwRev

@[expose] public section

/-!
# The first-meeting record mass of the charged coordinates, averaged over the coordinates

MassSources' mismatch term is the first-meeting record mass (`revFirst`) of the charged coordinates
`chgBK x` in the canonical game at the coordinates `x = (p, (v, k))`. Its average over the
coordinates is at most `R (|Message| / |Z| + 3 / |Digest|) + R` times the fraction of atypical
coordinates (`R = 3 signatureLimit`: CandCharge's `isChargeBound_gameR_rndDig`).

* **Pointwise** (`diagMass_revSet_chgBK_le`, `diagMass_revSet_dPartK_le`): a first meeting of the
  charged coordinates is a record meeting the randomizer part `rPartK` (paid by its trace), or a
  first meeting of the digest part `dPartK`; on atypical coordinates that is paid by the
  candidates recorded (`candCharge`).
* **The randomizer part** (`sum_revW_rPartK_le`): `rPartK p k` depends on the never-revealed part
  `k` only, through the randomizer stage's `k'`-coin of `M` at `M`'s capacity, so each candidate is
  in it for at most `|Message| / |Z|` of the `k` (`card_filter_rChg_le`); Mismatch's `sum_revW_le`.
* **The digest part** (`sum_totalWeight_cd_le`): at a first meeting of the digest part the hidden
  randomizer of the charged message is undisclosed (its coordinate is in the digest part), and the
  charge forces it into `badR` (`hit_of_dChg`), which does not read it (`badR_update`) and has at
  most three elements on typical coordinates: CwRev's view lemma gives `3 / |Digest|` per recorded
  candidate.
* `uavg_revFirst_chgBK_le`: the average over the coordinates.
-/

open Matrix IPFunctor
open scoped ENNReal ComplexOrder Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message Randomizer)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (diagMass revSet revWt revW recMeets candCharge Agree)
open Quantum.Xmss.Assembly (recHwSpec runtimeR realizeT kWt)
open Quantum.Sphincs.Hybrid (DLab)

namespace Quantum.Sphincs.Assembly

/-! ## Pointwise weights -/

section pointwise

theorem rPartK_subset_rndDigJ (p : PP) (k : KK) : rPartK p k ⊆ rndDigJ := by
  intro s hs
  refine mem_rndDigJ.mpr ?_
  have h := mem_rPartK.mp hs
  cases s with
  | rnd M => trivial
  | dig M i => trivial
  | val q => exact h
  | str j i => exact h
  | asg M j => exact h

theorem dPartK_subset_rndDigJ (x : CX) : dPartK x ⊆ rndDigJ := by
  intro s hs
  refine mem_rndDigJ.mpr ?_
  have h := mem_dPartK.mp hs
  cases s with
  | rnd M => trivial
  | dig M i => trivial
  | val q => exact h
  | str j i => exact h
  | asg M j => exact h

theorem revSet_inl (B : Finset HPos) (i : (hwSpec X Z (Finset HPos × Selections)).Port) :
    revSet X Z Selections B (.inl i) = ∅ :=
  rfl

theorem revSet_inr_of_disjoint {B T : Finset HPos} (h : Disjoint T B) :
    revSet X Z Selections B (.inr T) = ∅ := by
  simp [revSet, recMeets, h]

theorem revSet_inr_of_not {B T : Finset HPos} (h : ¬ Disjoint T B) :
    revSet X Z Selections B (.inr T) = {p | Disjoint p.2.2.2.1 B} := by
  simp [revSet, recMeets, h]

/-- **A first meeting of the charged coordinates** is a record meeting the randomizer part or a
first meeting of the digest part. -/
theorem diagMass_revSet_chgBK_le (x : CX) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i ×
      QReg.of (HwReg X Z (Finset HPos × Selections)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ)
    (hσ : σ.PosSemidef) :
    diagMass (revSet X Z Selections (chgBK x) i) σ ≤
      revWt X Z Selections (rPartK x.1 x.2.2) i σ +
        diagMass (revSet X Z Selections (dPartK x) i) σ := by
  rcases i with i | T
  · rw [revSet_inl, Quantum.Xmss.Hybrid.diagMass_empty]
    exact zero_le
  · by_cases hR : Disjoint T (rPartK x.1 x.2.2)
    · by_cases hD : Disjoint T (dPartK x)
      · have hC : Disjoint T (chgBK x) :=
          Finset.disjoint_of_subset_right (chgBK_subset_parts x)
            (Finset.disjoint_union_right.mpr ⟨hR, hD⟩)
        rw [revSet_inr_of_disjoint hC, Quantum.Xmss.Hybrid.diagMass_empty]
        exact zero_le
      · have hC : ¬ Disjoint T (chgBK x) := fun h ↦
          hD (Finset.disjoint_of_subset_right (dPartK_subset_chgBK x) h)
        rw [revSet_inr_of_not hC, revSet_inr_of_not hD]
        exact le_add_left (Quantum.Xmss.Hybrid.diagMass_mono (fun q hq ↦
          Finset.disjoint_of_subset_right (dPartK_subset_chgBK x) hq) σ)
    · refine le_add_right ?_
      simp only [revWt, recMeets, hR, decide_false, Bool.not_false, ↓reduceIte]
      exact Quantum.Xmss.Hybrid.diagMass_le _ hσ

/-- **A first meeting of the digest part** is paid by the recorded candidates. -/
theorem diagMass_revSet_dPartK_le (x : CX) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i ×
      QReg.of (HwReg X Z (Finset HPos × Selections)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ)
    (hσ : σ.PosSemidef) :
    diagMass (revSet X Z Selections (dPartK x) i) σ ≤
      (candCharge X Z Selections rndDigJ i : ℝ≥0∞) * ENNReal.ofReal σ.trace.re := by
  rcases i with i | T
  · rw [revSet_inl, Quantum.Xmss.Hybrid.diagMass_empty]
    exact zero_le
  · by_cases hD : Disjoint T (dPartK x)
    · rw [revSet_inr_of_disjoint hD, Quantum.Xmss.Hybrid.diagMass_empty]
      exact zero_le
    · obtain ⟨s, hsT, hsD⟩ := Finset.not_disjoint_iff.mp hD
      have h1 : (1 : ℝ≥0∞) ≤ (candCharge X Z Selections rndDigJ (.inr T) : ℝ≥0∞) := by
        show (1 : ℝ≥0∞) ≤ ((T ∩ rndDigJ).card : ℝ≥0∞)
        exact_mod_cast Finset.card_pos.mpr
          ⟨s, Finset.mem_inter.mpr ⟨hsT, dPartK_subset_rndDigJ x hsD⟩⟩
      exact (Quantum.Xmss.Hybrid.diagMass_le _ hσ).trans (le_mul_of_one_le_left zero_le h1)

end pointwise

/-! ## The randomizer part -/

section rpart

/-- Resampling one value of a function coordinate: at most `m` values meet a condition for every
rest gives at most `m / |Z|` of the coordinates. -/
theorem card_mul_card_filter_le_upd {A W : Type*} [Fintype A] [DecidableEq A] [Fintype W]
    (P : (A → Z) × W → Prop) [DecidablePred P] (a : A) (m : ℕ)
    (h : ∀ f r, (Finset.univ.filter fun w : Z ↦ P (Function.update f a w, r)).card ≤ m) :
    Fintype.card Z * (Finset.univ.filter P).card ≤ Fintype.card ((A → Z) × W) * m := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  calc ∑ r : W, Fintype.card Z * ∑ f : A → Z, (if P (f, r) then 1 else 0)
      ≤ ∑ _r : W, Fintype.card (A → Z) * m := Finset.sum_le_sum fun r _ ↦
        Quantum.Xmss.Hybrid.card_mul_sum_le_of_update
          (fun f : A → Z ↦ if P (f, r) then 1 else 0) a m fun f ↦ by
            rw [← Finset.card_filter]
            exact h f r
    _ = Fintype.card ((A → Z) × W) * m := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod]
        ring

/-- `d a ≤ N b` gives `a ≤ (b / d) N` in `ℝ≥0∞`. -/
theorem natCast_le_div_mul_of_mul_le {a b d N : ℕ} (hd : d ≠ 0) (h : d * a ≤ N * b) :
    (a : ℝ≥0∞) ≤ ((b : ℝ≥0∞) / d) * N :=
  (Quantum.Xmss.Hybrid.natCast_le_mul_div_of_mul_le hd h).trans_eq (mul_comm _ _)

/-- The never-revealed part with the randomizer stage's `k'`-coins first. -/
def eKK : KK ≃ (Message → Z) × (Hybrid.Secret × Hybrid.SeedKS × (Message → Z) ×
    (Message → Fin 960 → ZMod 2) × (DLab → Z) × (DLab → Z) × (DLab → Fin 832 → ZMod 2)) where
  toFun k := (k.2.2.2.1, (k.1, k.2.1, k.2.2.1, k.2.2.2.2))
  invFun r := (r.2.1, r.2.2.1, r.2.2.2.1, r.1, r.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
noncomputable instance instFintypeKKRest : Fintype (Hybrid.Secret × Hybrid.SeedKS ×
    (Message → Z) × (Message → Fin 960 → ZMod 2) × (DLab → Z) × (DLab → Z) ×
    (DLab → Fin 832 → ZMod 2)) :=
  inferInstanceAs (Fintype (Hybrid.Secret × Hybrid.SeedKS × (Message → Z) ×
    (Message → Fin 960 → ZMod 2) × (DLab → Z) × (DLab → Z) × (DLab → Fin 832 → ZMod 2)))

open scoped Classical in
/-- A non-first randomizer label after resampling its `k'`-coin: at most `|Message|` values. -/
theorem card_filter_rChg_upd_le (p : PP) (M : Message) (f : Message → Z)
    (r : Hybrid.Secret × Hybrid.SeedKS × (Message → Z) × (Message → Fin 960 → ZMod 2) ×
      (DLab → Z) × (DLab → Z) × (DLab → Fin 832 → ZMod 2)) :
    (Finset.univ.filter fun w : Z ↦
      RChg p (eKK.symm (Function.update f M w, r)) M).card ≤ Fintype.card Message := by
  have hsub : (Finset.univ.filter fun w : Z ↦ RChg p (eKK.symm (Function.update f M w, r)) M) ⊆
      imgCells fun M' : Message ↦
        rCapK p (eKK.symm (f, r)) M' - (p.1.2.2.1 (Hybrid.rCell M p.1.2.1 r.1.2, r.2.2.1 M)).2 := by
    intro w
    rw [Finset.mem_filter]
    rintro ⟨-, M', hlt, he⟩
    have hne : M' ≠ M := fun e ↦ by
      subst e
      exact lt_irrefl _ hlt
    have e1 : rCapK p (eKK.symm (Function.update f M w, r)) M' = rCapK p (eKK.symm (f, r)) M' := by
      show (p.1.2.2.1 (Hybrid.rCell M' p.1.2.1 r.1.2, r.2.2.1 M')).2 +
          Function.update f M w M' =
        (p.1.2.2.1 (Hybrid.rCell M' p.1.2.1 r.1.2, r.2.2.1 M')).2 + f M'
      rw [Function.update_of_ne hne]
    have e2 : rCapK p (eKK.symm (Function.update f M w, r)) M =
        (p.1.2.2.1 (Hybrid.rCell M p.1.2.1 r.1.2, r.2.2.1 M)).2 + w := by
      show (p.1.2.2.1 (Hybrid.rCell M p.1.2.1 r.1.2, r.2.2.1 M)).2 + Function.update f M w M = _
      rw [Function.update_self]
    have hw : w = rCapK p (eKK.symm (f, r)) M' -
        (p.1.2.2.1 (Hybrid.rCell M p.1.2.1 r.1.2, r.2.2.1 M)).2 := by
      rw [← e1, he, e2, add_sub_cancel_left]
    rw [hw]
    exact mem_imgCells _ M'
  exact (Finset.card_le_card hsub).trans (card_imgCells_le _)

open scoped Classical in
/-- **A randomizer label is non-first** for at most `|Message| / |Z|` of the never-revealed part. -/
theorem card_filter_rChg_le (p : PP) (M : Message) :
    ((Finset.univ.filter fun k : KK ↦ RChg p k M).card : ℝ≥0∞) ≤
      ((Fintype.card Message : ℝ≥0∞) / Fintype.card Z) * Fintype.card KK := by
  have h := card_mul_card_filter_le_upd (fun y ↦ RChg p (eKK.symm y) M) M (Fintype.card Message)
    fun f r ↦ card_filter_rChg_upd_le p M f r
  have hc : (Finset.univ.filter fun k : KK ↦ RChg p k M).card =
      (Finset.univ.filter fun y ↦ RChg p (eKK.symm y) M).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Fintype.sum_equiv eKK _ _ fun k ↦ by rw [Equiv.symm_apply_apply]
  rw [hc, Fintype.card_congr eKK]
  exact natCast_le_div_mul_of_mul_le Fintype.card_ne_zero h

/-- **The randomizer part's record mass**, summed over the never-revealed part. -/
theorem sum_revW_rPartK_le {A : SAdversary}
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ) (hρ : ρ.PosSemidef)
    (p : PP) (v : (s : HPos) → XD s) :
    ∑ k : KK, revW m0R LocalSig.Interp.instruments (rPartK p k) (gameR msgPol A (pubP p) v) ρ ≤
      Fintype.card KK * ((3 * signatureLimit : ℕ) *
        ((Fintype.card Message : ℝ≥0∞) / Fintype.card Z) * ENNReal.ofReal ρ.trace.re) := by
  classical
  refine Quantum.Xmss.Hybrid.sum_revW_le m0R LocalSig.Interp.instruments _ hρ (rPartK p) rndDigJ
    (rPartK_subset_rndDigJ p) _ (fun s hs ↦ ?_) (isChargeBound_gameR_rndDig A hsign (pubP p) v)
  have hs' := mem_rndDigJ.mp hs
  cases s with
  | rnd M =>
    refine le_of_eq_of_le (congrArg (fun n : ℕ ↦ (n : ℝ≥0∞)) (congrArg Finset.card
      (Finset.filter_congr fun k _ ↦ mem_rPartK))) (card_filter_rChg_le p M)
  | dig M i =>
    refine le_of_eq_of_le (congrArg (fun n : ℕ ↦ (n : ℝ≥0∞)) (congrArg Finset.card
      (Finset.filter_congr fun k _ ↦ mem_rPartK))) (card_filter_rChg_le p M)
  | val q => exact hs'.elim
  | str j i => exact hs'.elim
  | asg M j => exact hs'.elim

end rpart

end Quantum.Sphincs.Assembly

end
