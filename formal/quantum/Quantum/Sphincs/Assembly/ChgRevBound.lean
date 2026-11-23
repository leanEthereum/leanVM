module

public import Quantum.Sphincs.Assembly.ChgRev
public import Quantum.Sphincs.Assembly.ChgRevView
public import Quantum.Sphincs.Assembly.CandCharge

@[expose] public section

/-!
# The first-meeting record mass of the charged coordinates, over the coordinates

MassSources' and the win's mismatch term is the first-meeting record mass (`revFirst`) of the
charged coordinates `chgBK x` in the canonical game at the coordinates `x = (p, (v, k))`. On
coordinates whose template data satisfy ChgRevStatic's `ChgStatic`, its sum over the coordinates
is at most `R (εK + cD)` per coordinate times the trace (`R = 3 signatureLimit`: CandCharge's
`isChargeBound_gameR_rndDig`, a path records at most `R` candidates).

* **Pointwise** (`diagMass_revSet_chgBK_le`, `revFirst_chgBK_le`): a first meeting of the charged
  coordinates is a record meeting the never-revealed part's charges `kPartK` (paid by its trace),
  or a first meeting of the hidden randomizers' charges `dPartK` (`dCSet`).
* **The never-revealed part** (`sum_revW_kPartK_le`): each candidate is in `kPartK` for at most
  `εK = (3 |Message| + 2 |SkIdx|) / |Z|` of `k` (`card_filter_kChg_le`: the randomizer stage's
  `k'`-coins and SeedStage's slots are uniform translates); Mismatch's `sum_revW_le`.
* **The hidden randomizers** (`sum_totalWeight_dCSet_le`): at a first meeting of `dPartK` the
  charged message `M` and the message `M'` whose label shares its capacity are both charged, so both
  randomizers are undisclosed; the pair of blocks `(R(M), (M, i))`, `(R(M'), (M', j))` is one of
  at most `254` per recorded candidate (`ChgStatic`'s load), each of weight `|Randomizer|⁻²`
  (ChgRevView's pair-source view lemma), so `cD = 254 / |Randomizer|²` per recorded candidate.
* `avg_le_of_injOn_coords`: the average over the padded tables through an injection.
-/

open Matrix IPFunctor
open scoped ENNReal ComplexOrder Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message Randomizer)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (diagMass revSet revWt revW recMeets candCharge Agree)
open Quantum.Xmss.Assembly (recHwSpec runtimeR realizeT kWt)
open Quantum.Sphincs.Hybrid (DLab SkIdx)

namespace Quantum.Sphincs.Assembly

/-! ## Pointwise weights -/

section pointwise

theorem msgPos_subset_rndDigJ (Q : Message → Prop) : msgPos Q ⊆ rndDigJ := by
  intro s hs
  refine mem_rndDigJ.mpr ?_
  have h := mem_msgPos.mp hs
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

/-- **A first meeting of the charged coordinates** is a record meeting the never-revealed part's
charges or a first meeting of the hidden randomizers' charges. -/
theorem diagMass_revSet_chgBK_le (x : CX) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i ×
      QReg.of (HwReg X Z (Finset HPos × Selections)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ)
    (hσ : σ.PosSemidef) :
    diagMass (revSet X Z Selections (chgBK x) i) σ ≤
      revWt X Z Selections (kPartK x) i σ +
        diagMass (revSet X Z Selections (dPartK x.1 x.2.1) i) σ := by
  rcases i with i | T
  · rw [revSet_inl, Quantum.Xmss.Hybrid.diagMass_empty]
    exact zero_le
  · by_cases hR : Disjoint T (kPartK x)
    · by_cases hD : Disjoint T (dPartK x.1 x.2.1)
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

/-- **The first meetings of the hidden randomizers' charges** on a datum satisfying
`ChgStatic`. -/
def dCSet (p : PP) (v : (s : HPos) → XD s) (i : (recHwSpec X Z HPos Selections).Port) :
    Set ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Finset HPos × Selections))) :=
  {q | ChgStatic (pubP p) (rootV v) ∧ q ∈ revSet X Z Selections (dPartK p v) i}

/-- **The first-meeting record mass at a static datum**: at most the never-revealed part's record
mass and the hidden randomizers' first meetings. -/
theorem revFirst_chgBK_le (x : CX) (hS : ChgStatic (pubP x.1) (rootV x.2.1)) {Ω : QReg → Type}
    (y : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    {ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ} (hρ : ρ.PosSemidef) :
    revFirst m0R LocalSig.Interp.instruments (chgBK x) y ρ ≤
      revW m0R LocalSig.Interp.instruments (kPartK x) y ρ +
        (runtimeR m0R).totalWeight LocalSig.Interp.instruments
          (fun i ↦ diagMass (dCSet x.1 x.2.1 i)) y ρ := by
  have hC : ∀ i, dCSet x.1 x.2.1 i = revSet X Z Selections (dPartK x.1 x.2.1) i := fun i ↦
    Set.ext fun _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨hS, h⟩⟩
  calc revFirst m0R LocalSig.Interp.instruments (chgBK x) y ρ
      ≤ (runtimeR m0R).totalWeight LocalSig.Interp.instruments (fun i σ ↦
          revWt X Z Selections (kPartK x) i σ + diagMass (dCSet x.1 x.2.1 i) σ) y ρ :=
        Quantum.Xmss.Hybrid.totalWeight_le_totalWeight _ _ (fun i σ hσ ↦ by
          rw [hC i]
          exact diagMass_revSet_chgBK_le x i σ hσ) y hρ
    _ = _ := Quantum.Xmss.Hybrid.totalWeight_add_weight (runtimeR m0R)
        LocalSig.Interp.instruments (revWt X Z Selections (kPartK x))
        (fun i ↦ diagMass (dCSet x.1 x.2.1 i)) y ρ

end pointwise

/-! ## The never-revealed part -/

section kpart

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


/-- The never-revealed part with SeedStage's second slots first. -/
def eKS : KK ≃ (SkIdx → Z) × (Hybrid.Secret × (SkIdx → Z) × (Message → Z) × (Message → Z) ×
    (Message → Fin 960 → ZMod 2) × (DLab → Z) × (DLab → Z) × (DLab → Fin 832 → ZMod 2)) where
  toFun k := (k.2.1.2, (k.1, (k.2.1.1, k.2.2)))
  invFun r := (r.2.1, ((r.2.2.1, r.1), r.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
noncomputable instance instFintypeKKRestS : Fintype (Hybrid.Secret × (SkIdx → Z) ×
    (Message → Z) × (Message → Z) × (Message → Fin 960 → ZMod 2) × (DLab → Z) × (DLab → Z) ×
    (DLab → Fin 832 → ZMod 2)) :=
  inferInstanceAs (Fintype (Hybrid.Secret × (SkIdx → Z) × (Message → Z) × (Message → Z) ×
    (Message → Fin 960 → ZMod 2) × (DLab → Z) × (DLab → Z) × (DLab → Fin 832 → ZMod 2)))

/-- **Resampling one value through an equivalence**: at most `m` values meet a condition for every
rest gives at most `m / |Z|` of the space (over abstract types). -/
theorem card_filter_le_of_equiv_upd {K A W : Type*} [Fintype K] [Fintype A] [DecidableEq A]
    [Fintype W] (e : K ≃ (A → Z) × W) (P : K → Prop) [DecidablePred P] (a : A) (m : ℕ)
    (h : ∀ f r, (Finset.univ.filter fun w : Z ↦ P (e.symm (Function.update f a w, r))).card ≤ m) :
    ((Finset.univ.filter P).card : ℝ≥0∞) ≤ ((m : ℝ≥0∞) / Fintype.card Z) * Fintype.card K := by
  classical
  have h' := card_mul_card_filter_le_upd (fun y ↦ P (e.symm y)) a m h
  have hc : (Finset.univ.filter P).card = (Finset.univ.filter fun y ↦ P (e.symm y)).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Fintype.sum_equiv e _ _ fun k ↦ by rw [Equiv.symm_apply_apply]
  rw [hc, Fintype.card_congr e]
  exact natCast_le_div_mul_of_mul_le Fintype.card_ne_zero h'

/-- A sum of bounded terms (over an abstract type). -/
theorem sum_le_card_mul' {A : Type*} [Fintype A] (f : A → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ a, f a ≤ c) :
    ∑ a, f a ≤ Fintype.card A * c :=
  (Finset.sum_le_sum fun a _ ↦ h a).trans (le_of_eq (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]))

/-- A translate takes a value once (over an abstract group). -/
theorem card_filter_add_eq_le {G : Type*} [AddGroup G] [Fintype G] (P : G → Prop)
    [DecidablePred P] (a c : G) (h : ∀ w, P w → a + w = c) :
    (Finset.univ.filter P).card ≤ 1 :=
  Finset.card_le_one.mpr fun w hw w' hw' ↦ add_left_cancel
    ((h w (Finset.mem_filter.mp hw).2).trans (h w' (Finset.mem_filter.mp hw').2).symm)

/-- A count is monotone in the predicate (over an abstract type). -/
theorem card_filter_le_of_imp' {K : Type*} [Fintype K] (P Q : K → Prop) [DecidablePred P]
    [DecidablePred Q] (h : ∀ k, P k → Q k) :
    (Finset.univ.filter P).card ≤ (Finset.univ.filter Q).card :=
  Finset.card_le_card fun k hk ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    h k (Finset.mem_filter.mp hk).2⟩

/-- `(m / z) k = m (z⁻¹ k)` over abstract quantities. -/
theorem div_mul_eq_mul_inv_mul (m z k : ℝ≥0∞) : m / z * k = m * (z⁻¹ * k) := by
  rw [ENNReal.div_eq_inv_mul, mul_comm z⁻¹ m, mul_assoc]

open scoped Classical in
/-- **A randomizer-stage capacity takes a value** for at most `1 / |Z|` of the never-revealed
part. -/
theorem card_filter_rCapK_eq_le (p : PP) (M : Message) (c : Z) :
    ((Finset.univ.filter fun k : KK ↦ rCapK p k M = c).card : ℝ≥0∞) ≤
      (((1 : ℕ) : ℝ≥0∞) / Fintype.card Z) * Fintype.card KK := by
  exact card_filter_le_of_equiv_upd eKK (fun k ↦ rCapK p k M = c) M 1 fun f r ↦
    card_filter_add_eq_le _ (p.1.2.2.1 (Hybrid.rCell M p.1.2.1 r.1.2, r.2.2.1 M)).2 c fun w hw ↦ by
      have e : rCapK p (eKK.symm (Function.update f M w, r)) M =
          (p.1.2.2.1 (Hybrid.rCell M p.1.2.1 r.1.2, r.2.2.1 M)).2 + w := by
        show (p.1.2.2.1 (Hybrid.rCell M p.1.2.1 r.1.2, r.2.2.1 M)).2 + Function.update f M w M = _
        rw [Function.update_self]
      exact e.symm.trans hw

open scoped Classical in
/-- **An `SK.seed`-keyed capacity takes a value** for at most `1 / |Z|` of the never-revealed
part. -/
theorem card_filter_sCapK_eq_le (p : PP) (b : SkIdx) (c : Z) :
    ((Finset.univ.filter fun k : KK ↦ sCapK p k b = c).card : ℝ≥0∞) ≤
      (((1 : ℕ) : ℝ≥0∞) / Fintype.card Z) * Fintype.card KK := by
  exact card_filter_le_of_equiv_upd eKS (fun k ↦ sCapK p k b = c) b 1 fun f r ↦
    card_filter_add_eq_le _ (p.1.2.2.1 (Hybrid.skCell p.1.2.1 r.1.1 b, r.2.1 b)).2 c fun w hw ↦ by
      have e : sCapK p (eKS.symm (Function.update f b w, r)) b =
          (p.1.2.2.1 (Hybrid.skCell p.1.2.1 r.1.1 b, r.2.1 b)).2 + w := by
        show (p.1.2.2.1 (Hybrid.skCell p.1.2.1 r.1.1 b, r.2.1 b)).2 + Function.update f b w b = _
        rw [Function.update_self]
      exact e.symm.trans hw

/-- A count of a predicate implying an existential is at most the sum of the counts (over abstract
types). -/
theorem card_filter_le_sum_of_imp {K A : Type*} [Fintype K] [Fintype A] (P : K → Prop)
    [DecidablePred P] (Q : A → K → Prop) [∀ a, DecidablePred (Q a)] (h : ∀ k, P k → ∃ a, Q a k) :
    ((Finset.univ.filter P).card : ℝ≥0∞) ≤ ∑ a, ((Finset.univ.filter (Q a)).card : ℝ≥0∞) := by
  classical
  have hs : Finset.univ.filter P ⊆ Finset.univ.biUnion fun a ↦ Finset.univ.filter (Q a) := by
    intro k hk
    obtain ⟨a, ha⟩ := h k (Finset.mem_filter.mp hk).2
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ha⟩⟩
  exact_mod_cast (Finset.card_le_card hs).trans Finset.card_biUnion_le

/-- A count of a predicate implying a disjunction is at most the sum of the counts (over abstract
types). -/
theorem card_filter_le_add_of_imp' {K : Type*} [Fintype K] (P A B : K → Prop) [DecidablePred P]
    [DecidablePred A] [DecidablePred B] (h : ∀ k, P k → A k ∨ B k) :
    ((Finset.univ.filter P).card : ℝ≥0∞) ≤
      ((Finset.univ.filter A).card : ℝ≥0∞) + (Finset.univ.filter B).card := by
  exact_mod_cast Quantum.Xmss.Assembly.card_filter_le_add_of_imp P A B h

/-- A randomizer-stage capacity at `z`. -/
def RHit (p : PP) (k : KK) (z : Z) : Prop :=
  ∃ M, rCapK p k M = z

/-- An `SK.seed`-keyed capacity at `z`. -/
def SHit (p : PP) (k : KK) (z : Z) : Prop :=
  ∃ b, sCapK p k b = z

/-- The arithmetic of the never-revealed part's count, over abstract quantities. -/
theorem kChg_arith (m s a r e : ℝ≥0∞) (hr : r ≤ m * a) (he : e ≤ 2 * (m * a + s * a)) :
    r + e ≤ (3 * m + 2 * s) * a :=
  calc r + e ≤ m * a + 2 * (m * a + s * a) := add_le_add hr he
    _ = (3 * m + 2 * s) * a := by ring

/-- **The never-revealed part's charge rate**: `(3 |Message| + 2 |SkIdx|) / |Z|`. -/
noncomputable def epsK : ℝ≥0∞ :=
  (3 * (Fintype.card Message : ℝ≥0∞) + 2 * Fintype.card SkIdx) * (Fintype.card Z : ℝ≥0∞)⁻¹

theorem card_digestCall : Fintype.card DigestCall = 2 := by
  rw [Fintype.card_fin]
  rfl

open scoped Classical in
/-- **A message is charged over the never-revealed part** for at most `εK` of it: the randomizer
label non-first (`|Message| / |Z|`), or a label's capacity (fixed by `p` and the hidden values)
a randomizer-stage capacity or an `SK.seed`-keyed one (`2 (|Message| + |SkIdx|) / |Z|`). -/
theorem card_filter_kChg_le (p : PP) (v : (s : HPos) → XD s) (M : Message) :
    ((Finset.univ.filter fun k : KK ↦ KChg (p, (v, k)) M).card : ℝ≥0∞) ≤
      epsK * Fintype.card KK := by
  set a : ℝ≥0∞ := (Fintype.card Z : ℝ≥0∞)⁻¹ * Fintype.card KK with ha
  have h1 : (((1 : ℕ) : ℝ≥0∞) / Fintype.card Z) * Fintype.card KK = a := by
    rw [Nat.cast_one, one_div]
  set c : DigestCall → Z := fun i ↦ capD p (rootV v) (M, i) (v (.rnd M))
  have hR : ((Finset.univ.filter fun k : KK ↦ RChg p k M).card : ℝ≥0∞) ≤
      (Fintype.card Message : ℝ≥0∞) * a :=
    (card_filter_rChg_le p M).trans (le_of_eq (div_mul_eq_mul_inv_mul _ _ _))
  have hE : ∀ z, ((Finset.univ.filter fun k : KK ↦ ExtK p k z).card : ℝ≥0∞) ≤
      (Fintype.card Message : ℝ≥0∞) * a + (Fintype.card SkIdx : ℝ≥0∞) * a := fun z ↦ by
    refine (card_filter_le_add_of_imp' (fun k : KK ↦ ExtK p k z) (fun k ↦ RHit p k z)
      (fun k ↦ SHit p k z)
      fun _ h ↦ h).trans (add_le_add ?_ ?_)
    · exact (card_filter_le_sum_of_imp (fun k : KK ↦ RHit p k z) (fun M' k ↦ rCapK p k M' = z)
        fun _ h ↦ h).trans
        (sum_le_card_mul' _ _ fun M' ↦ (card_filter_rCapK_eq_le p M' z).trans h1.le)
    · exact (card_filter_le_sum_of_imp (fun k : KK ↦ SHit p k z) (fun b k ↦ sCapK p k b = z)
        fun _ h ↦ h).trans
        (sum_le_card_mul' _ _ fun b ↦ (card_filter_sCapK_eq_le p b z).trans h1.le)
  have hE2 : ((Finset.univ.filter fun k : KK ↦ ExtChg (p, (v, k)) M).card : ℝ≥0∞) ≤
      2 * ((Fintype.card Message : ℝ≥0∞) * a + (Fintype.card SkIdx : ℝ≥0∞) * a) := by
    refine (card_filter_le_sum_of_imp (fun k : KK ↦ ExtChg (p, (v, k)) M)
      (fun i k ↦ ExtK p k (c i)) fun _ h ↦ h).trans ?_
    refine (sum_le_card_mul' _ _ fun i ↦ hE (c i)).trans (le_of_eq ?_)
    rw [card_digestCall, Nat.cast_ofNat]
  refine (card_filter_le_add_of_imp' (fun k : KK ↦ KChg (p, (v, k)) M) (fun k ↦ RChg p k M)
    (fun k ↦ ExtChg (p, (v, k)) M)
    fun _ h ↦ h).trans ?_
  refine (kChg_arith _ _ _ _ _ hR hE2).trans (le_of_eq ?_)
  rw [epsK, ha, mul_assoc]

/-- **The never-revealed part's record mass**, summed over it. -/
theorem sum_revW_kPartK_le {A : SAdversary}
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ) (hρ : ρ.PosSemidef)
    (p : PP) (v : (s : HPos) → XD s) :
    ∑ k : KK, revW m0R LocalSig.Interp.instruments (kPartK (p, (v, k)))
        (gameR msgPol A (pubP p) v) ρ ≤
      Fintype.card KK * ((3 * signatureLimit : ℕ) * epsK * ENNReal.ofReal ρ.trace.re) := by
  classical
  refine Quantum.Xmss.Hybrid.sum_revW_le m0R LocalSig.Interp.instruments _ hρ
    (fun k ↦ kPartK (p, (v, k))) rndDigJ (fun _ ↦ msgPos_subset_rndDigJ _) _ (fun s hs ↦ ?_)
    (isChargeBound_gameR_rndDig A hsign (pubP p) v)
  have hs' := mem_rndDigJ.mp hs
  cases s with
  | rnd M =>
    exact le_of_eq_of_le (congrArg (fun n : ℕ ↦ (n : ℝ≥0∞)) (congrArg Finset.card
      (Finset.filter_congr fun k _ ↦ mem_msgPos))) (card_filter_kChg_le p v M)
  | dig M i =>
    exact le_of_eq_of_le (congrArg (fun n : ℕ ↦ (n : ℝ≥0∞)) (congrArg Finset.card
      (Finset.filter_congr fun k _ ↦ mem_msgPos))) (card_filter_kChg_le p v M)
  | val q => exact hs'.elim
  | str j i => exact hs'.elim
  | asg M j => exact hs'.elim

end kpart

/-! ## The hidden randomizers -/

section dpart

/-- A digest label's capacity is its block's (ChgRevStatic's `blkCap`). -/
theorem capD_eq_blkCap (p : PP) (root : Digest) (a : DLab) (R : Randomizer) :
    capD p root a R =
      blkCap (cRate (pubP p) root) (cBase (pubP p) root) (pubP p).xw.2.2.2 (R, a) :=
  rfl

theorem rootV_update_rnd (u : (s : HPos) → XD s) (M : Message) (d : XD (.rnd M)) :
    rootV (Function.update u (.rnd M) d) = rootV u :=
  Function.update_of_ne (by simp) _ _

/-- The messages of the candidates recorded by `T`. -/
noncomputable def msgsOf (T : Finset HPos) : Finset Message :=
  (T ∩ rndDigJ).image msgOfPos

open scoped Classical in
/-- **The colliding pairs of blocks** at a record of `T`: a block of a message of `T` and a block
of another message at one capacity, on a static datum; the source values are the two blocks'
randomizers. -/
noncomputable def pairF (p : PP) (T : Finset HPos) (j : DBlk × DBlk) (u : (s : HPos) → XD s) :
    Finset (XD (.rnd j.1.2.1) × XD (.rnd j.2.2.1)) :=
  if ChgStatic (pubP p) (rootV u) ∧ (dMsg j.1 ∈ msgsOf T ∧ dMsg j.1 ≠ dMsg j.2 ∧
      blkCap (cRate (pubP p) (rootV u)) (cBase (pubP p) (rootV u)) (pubP p).xw.2.2.2 j.1 =
        blkCap (cRate (pubP p) (rootV u)) (cBase (pubP p) (rootV u)) (pubP p).xw.2.2.2 j.2)
  then ({(j.1.1, j.2.1)} : Finset (Randomizer × Randomizer)) else ∅

/-- No pair off the condition. -/
theorem pairF_eq_empty (p : PP) (T : Finset HPos) (j : DBlk × DBlk) (u : (s : HPos) → XD s)
    (hn : ¬(ChgStatic (pubP p) (rootV u) ∧ (dMsg j.1 ∈ msgsOf T ∧ dMsg j.1 ≠ dMsg j.2 ∧
      blkCap (cRate (pubP p) (rootV u)) (cBase (pubP p) (rootV u)) (pubP p).xw.2.2.2 j.1 =
        blkCap (cRate (pubP p) (rootV u)) (cBase (pubP p) (rootV u)) (pubP p).xw.2.2.2 j.2))) :
    pairF p T j u = ∅ := by
  unfold pairF
  exact ite_eq_right hn

/-- A colliding pair of blocks names its randomizers. -/
theorem pairF_eq_of (p : PP) (T : Finset HPos) (j : DBlk × DBlk) (u : (s : HPos) → XD s)
    (hS : ChgStatic (pubP p) (rootV u)) (hm : dMsg j.1 ∈ msgsOf T) (hne : dMsg j.1 ≠ dMsg j.2)
    (hcap : blkCap (cRate (pubP p) (rootV u)) (cBase (pubP p) (rootV u)) (pubP p).xw.2.2.2 j.1 =
      blkCap (cRate (pubP p) (rootV u)) (cBase (pubP p) (rootV u)) (pubP p).xw.2.2.2 j.2) :
    pairF p T j u = ({(j.1.1, j.2.1)} : Finset (Randomizer × Randomizer)) := by
  unfold pairF
  exact ite_eq_left ⟨hS, hm, hne, hcap⟩

/-- **The hidden randomizers' charge rate** per recorded candidate: `254 / |Randomizer|²`. -/
noncomputable def cD : ℝ≥0∞ :=
  ((2 * 127 : ℕ) : ℝ≥0∞) * ((Fintype.card Randomizer : ℝ≥0∞) * Fintype.card Randomizer)⁻¹

theorem card_xd_rnd (M : Message) : Fintype.card (XD (.rnd M)) = Fintype.card Randomizer :=
  rfl

open scoped Classical in
/-- **The colliding pairs** weigh at most `|T ∩ J| cD`. -/
theorem sum_card_pairF_le (p : PP) (T : Finset HPos) (u : (s : HPos) → XD s) :
    ∑ j : DBlk × DBlk, ((pairF p T j u).card : ℝ≥0∞) *
        ((Fintype.card (XD (.rnd j.1.2.1)) : ℝ≥0∞) * Fintype.card (XD (.rnd j.2.2.1)))⁻¹ ≤
      ((T ∩ rndDigJ).card : ℝ≥0∞) * cD := by
  simp only [card_xd_rnd]
  rw [← Finset.sum_mul]
  have hN : ∑ j : DBlk × DBlk, (pairF p T j u).card ≤ (T ∩ rndDigJ).card * (2 * 127) := by
    by_cases hS : ChgStatic (pubP p) (rootV u)
    · have hc : ∀ j : DBlk × DBlk, (pairF p T j u).card = if dMsg j.1 ∈ msgsOf T ∧
          dMsg j.1 ≠ dMsg j.2 ∧ blkCap (cRate (pubP p) (rootV u)) (cBase (pubP p) (rootV u))
            (pubP p).xw.2.2.2 j.1 = blkCap (cRate (pubP p) (rootV u))
              (cBase (pubP p) (rootV u)) (pubP p).xw.2.2.2 j.2 then 1 else 0 := fun j ↦ by
        by_cases hc : dMsg j.1 ∈ msgsOf T ∧ dMsg j.1 ≠ dMsg j.2 ∧
            blkCap (cRate (pubP p) (rootV u)) (cBase (pubP p) (rootV u)) (pubP p).xw.2.2.2 j.1 =
              blkCap (cRate (pubP p) (rootV u)) (cBase (pubP p) (rootV u)) (pubP p).xw.2.2.2 j.2
        · rw [pairF_eq_of p T j u hS hc.1 hc.2.1 hc.2.2, ite_eq_left hc]
          exact Finset.card_singleton _
        · rw [pairF_eq_empty p T j u fun h ↦ hc h.2, ite_eq_right hc]
          exact Finset.card_empty
      rw [Finset.sum_congr rfl fun j _ ↦ hc j, ← Finset.card_filter]
      exact (card_filter_pairs_le (cRate (pubP p) (rootV u)) (cBase (pubP p) (rootV u)) dMsg
        (pubP p).xw.2.2.2 (msgsOf T) (2 * 127) hS.2.2).trans
        (Nat.mul_le_mul_right _ Finset.card_image_le)
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun j _ ↦ ?_) (Nat.zero_le _)
      rw [pairF_eq_empty p T j u fun h ↦ hS h.1, Finset.card_empty]
  calc (∑ j : DBlk × DBlk, ((pairF p T j u).card : ℝ≥0∞)) *
        ((Fintype.card Randomizer : ℝ≥0∞) * Fintype.card Randomizer)⁻¹
      ≤ (((T ∩ rndDigJ).card * (2 * 127) : ℕ) : ℝ≥0∞) *
          ((Fintype.card Randomizer : ℝ≥0∞) * Fintype.card Randomizer)⁻¹ := by
        gcongr
        exact_mod_cast hN
    _ = ((T ∩ rndDigJ).card : ℝ≥0∞) * cD := by
        rw [cD, Nat.cast_mul, mul_assoc]

open scoped Classical in
/-- **The count at a record**: the hidden values agreeing on the record's label with a first
meeting of the hidden randomizers' charges are at most `|T ∩ J| cD` of them. -/
theorem sum_agree_dCSet_le (p : PP) (v : (s : HPos) → XD s) (T : Finset HPos)
    (q : (recHwSpec X Z HPos Selections).In (.inr T) ×
      QReg.of (HwReg X Z (Finset HPos × Selections))) :
    ∑ u, (if Agree q.2.2.2.1 v u ∧ q ∈ dCSet p u (.inr T) then (1 : ℝ≥0∞) else 0) ≤
      ((T ∩ rndDigJ).card * cD) * ∑ u, if Agree q.2.2.2.1 v u then 1 else 0 := by
  refine sum_agree_and_le₂ q.2.2.2.1 v (fun u ↦ q ∈ dCSet p u (.inr T))
    (fun j : DBlk × DBlk ↦ HPos.rnd j.1.2.1) (fun j ↦ HPos.rnd j.2.2.1) (pairF p T)
    (fun j h u ↦ ?_) (fun j u d ↦ ?_) (fun j u d ↦ ?_) (fun u hu ↦ ?_) _
    (fun u ↦ sum_card_pairF_le p T u)
  · exact pairF_eq_empty p T j u fun hc ↦ hc.2.2.1 (HPos.rnd.inj h)
  · unfold pairF
    simp only [rootV_update_rnd]
  · unfold pairF
    simp only [rootV_update_rnd]
  · obtain ⟨hS, hq⟩ := hu
    have hD : ¬ Disjoint T (dPartK p u) := fun h ↦ by
      rw [revSet_inr_of_disjoint h] at hq
      exact hq
    rw [revSet_inr_of_not hD] at hq
    obtain ⟨s, hsT, hsD⟩ := Finset.not_disjoint_iff.mp hD
    obtain ⟨M, hMs⟩ : ∃ M, msgOfPos s = M := ⟨_, rfl⟩
    have hV : VChg p u M := hMs ▸ isOfMsg_msgOfPos (mem_msgPos.mp hsD)
    have hsJ : s ∈ rndDigJ := msgPos_subset_rndDigJ _ hsD
    rcases hV with ⟨i, b, hbM, he⟩ | hself
    · have hlab : ∀ M', VChg p u M' → HPos.rnd M' ∉ q.2.2.2.1 := fun M' hM' hm ↦
        Finset.disjoint_left.mp hq hm (mem_msgPos.mpr hM')
      refine ⟨((u (.rnd M), (M, i)), (u (.rnd b.1), b)), hlab M (Or.inl ⟨i, b, hbM, he⟩),
        hlab b.1 (Or.inl ⟨b.2, (M, i), fun h ↦ hbM h.symm, he.symm⟩), ?_⟩
      rw [pairF_eq_of p T ((u (.rnd M), (M, i)), (u (.rnd b.1), b)) u hS
        (Finset.mem_image.mpr ⟨s, Finset.mem_inter.mpr ⟨hsT, hsJ⟩, hMs⟩) (fun h ↦ hbM h.symm)
        ((capD_eq_blkCap p (rootV u) (M, i) (u (.rnd M))).symm.trans
          (he.symm.trans (capD_eq_blkCap p (rootV u) b (u (.rnd b.1)))))]
      exact Finset.mem_singleton_self _
    · exact absurd ((capD_eq_blkCap p (rootV u) (M, 0) (u (.rnd M))).symm.trans
        (hself.trans (capD_eq_blkCap p (rootV u) (M, 1) (u (.rnd M))))) (hS.2.1 (M, u (.rnd M)))

/-- A constant weight's diagonal is at most the weight times the trace. -/
theorem kWt_const_le {α : Type} [Fintype α] (c : ℝ≥0∞) {σ : Matrix α α ℂ} (hσ : σ.PosSemidef) :
    kWt (fun _ ↦ c) σ ≤ c * ENNReal.ofReal σ.trace.re := by
  have h : kWt (fun _ ↦ c) σ = c * diagMass Set.univ σ := by
    simp only [kWt, diagMass, Set.indicator_univ, Finset.mul_sum]
  rw [h]
  exact mul_le_mul' le_rfl (Quantum.Xmss.Hybrid.diagMass_le _ hσ)

/-- **The hidden randomizers' first meetings**, summed over the hidden values: at most
`R cD` per hidden value times the trace. -/
theorem sum_totalWeight_dCSet_le {A : SAdversary}
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ) (hρ : ρ.PosSemidef)
    (p : PP) :
    ∑ v, (runtimeR m0R).totalWeight LocalSig.Interp.instruments
        (fun i ↦ diagMass (dCSet p v i)) (gameR msgPol A (pubP p) v) ρ ≤
      Fintype.card ((s : HPos) → XD s) *
        ((3 * signatureLimit : ℕ) * cD * ENNReal.ofReal ρ.trace.re) := by
  classical
  refine (sum_totalWeight_le_cnt (runtimeR m0R) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
    (fun v ↦ gameR msgPol A (pubP p) v) (fun _ ↦ ρ) (fun _ ↦ hρ) (fun _ ↦ True)
    (fun j ↦ (viewBy_gameT Selections cwUpd msgPol (pubP p) A m0R ρ j).viewByOn _)
    (dCSet p) (fun _ _ h ↦ absurd trivial h)
    (fun i _ ↦ (candCharge X Z Selections rndDigJ i : ℝ≥0∞) * cD) (fun v i q ↦ ?_)).trans ?_
  · rcases i with i | T
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun u _ ↦ ite_eq_right_iff.mpr fun h ↦ ?_) zero_le
      have h2 := h.2.2
      rw [revSet_inl] at h2
      exact h2.elim
    · exact sum_agree_dCSet_le p v T q
  · have hv : ∀ v, (runtimeR m0R).totalWeight LocalSig.Interp.instruments
        (fun i ↦ kWt fun _ ↦ (candCharge X Z Selections rndDigJ i : ℝ≥0∞) * cD)
        (gameR msgPol A (pubP p) v) ρ ≤
          (3 * signatureLimit : ℕ) * cD * ENNReal.ofReal ρ.trace.re := fun v ↦ by
      refine (Quantum.Xmss.Hybrid.totalWeight_le_totalWeight _ _ (w' := fun i σ ↦ cD *
        ((candCharge X Z Selections rndDigJ i : ℝ≥0∞) * ENNReal.ofReal σ.trace.re))
        (fun i σ hσ ↦ (kWt_const_le _ hσ).trans (le_of_eq (by ring))) _ hρ).trans ?_
      refine (le_of_eq (Quantum.Xmss.Hybrid.totalWeight_const_mul_weight (runtimeR m0R)
        LocalSig.Interp.instruments cD (fun i σ ↦ (candCharge X Z Selections rndDigJ i : ℝ≥0∞) *
          ENNReal.ofReal σ.trace.re) (gameR msgPol A (pubP p) v) ρ)).trans ?_
      calc cD * (runtimeR m0R).totalWeight LocalSig.Interp.instruments
            (fun i σ ↦ (candCharge X Z Selections rndDigJ i : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)
            (gameR msgPol A (pubP p) v) ρ
          ≤ cD * ((3 * signatureLimit : ℕ) * ENNReal.ofReal ρ.trace.re) :=
            mul_le_mul' le_rfl (Quantum.Xmss.Hybrid.totalWeight_chargeTrace_le (runtimeR m0R)
              LocalSig.Interp.instruments (candCharge X Z Selections rndDigJ) _
              (isChargeBound_gameR_rndDig A hsign (pubP p) v) hρ)
        _ = (3 * signatureLimit : ℕ) * cD * ENNReal.ofReal ρ.trace.re := by ring
    refine (Finset.sum_le_sum fun v _ ↦ hv v).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end dpart

/-! ## The average over the coordinates -/

section avg

/-- **An average through an injection on a good set**: `e` maps `Θ` into `P × (V × K)`, injectively
on `G`, with `|P| |V × K| ≤ |Θ|`; if `r ≤ g ∘ e` on `G` and `g` sums over `V × K` to at most
`μ |V| |K|` for every `p`, the average of `r` over `G` (`0` elsewhere) is at most `μ`. -/
theorem avg_le_of_injOn_coords {Θ P V K : Type*} [Fintype Θ] [Fintype P] [Fintype V]
    [Fintype K] (e : Θ → P × (V × K)) (G : Θ → Prop) [DecidablePred G]
    (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card (V × K) ≤ Fintype.card Θ)
    (r : Θ → ℝ≥0∞) (g : P → V → K → ℝ≥0∞) (hr : ∀ t, G t → r t ≤ g (e t).1 (e t).2.1 (e t).2.2)
    (μ : ℝ≥0∞) (hg : ∀ p, ∑ v, ∑ k, g p v k ≤ μ * (Fintype.card V * Fintype.card K)) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ t, (if G t then r t else 0) ≤ μ := by
  classical
  have hsum : ∑ t, (if G t then r t else 0) ≤ μ * Fintype.card Θ := by
    rw [← Finset.sum_filter]
    have himg : ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2.1 (e t).2.2 =
        ∑ y ∈ (Finset.univ.filter G).image e, g y.1 y.2.1 y.2.2 :=
      (Finset.sum_image (f := fun y : P × (V × K) ↦ g y.1 y.2.1 y.2.2) fun a ha b hb h ↦
        hinj (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
          (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2 h).symm
    calc ∑ t ∈ Finset.univ.filter G, r t
        ≤ ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2.1 (e t).2.2 :=
          Finset.sum_le_sum fun t ht ↦ hr t (Finset.mem_filter.mp ht).2
      _ ≤ ∑ y : P × (V × K), g y.1 y.2.1 y.2.2 := by
          rw [himg]
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ p, ∑ v, ∑ k, g p v k := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun p _ ↦ Fintype.sum_prod_type _
      _ ≤ ∑ _p : P, μ * (Fintype.card V * Fintype.card K) := Finset.sum_le_sum fun p _ ↦ hg p
      _ = μ * ((Fintype.card P : ℝ≥0∞) * Fintype.card (V × K)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
          ring
      _ ≤ μ * Fintype.card Θ := mul_le_mul' le_rfl (by exact_mod_cast hcard)
  by_cases h0 : (Fintype.card Θ : ℝ≥0∞) = 0
  · have hΘ : IsEmpty Θ := Fintype.card_eq_zero_iff.mp (by exact_mod_cast h0)
    simp [Finset.univ_eq_empty]
  · calc (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ t, (if G t then r t else 0)
        ≤ (Fintype.card Θ : ℝ≥0∞)⁻¹ * (μ * Fintype.card Θ) := mul_le_mul' le_rfl hsum
      _ = μ := by
          rw [mul_comm μ, ← mul_assoc, ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _),
            one_mul]

/-- The arithmetic of the per-coordinate sum, over abstract quantities. -/
theorem coords_arith (cV cK a b R εK cD t : ℝ≥0∞) (ha : a ≤ cV * (cK * (R * εK * t)))
    (hb : b ≤ cV * (R * cD * t)) :
    a + cK * b ≤ R * (εK + cD) * t * (cV * cK) :=
  calc a + cK * b ≤ cV * (cK * (R * εK * t)) + cK * (cV * (R * cD * t)) :=
        add_le_add ha (mul_le_mul' le_rfl hb)
    _ = R * (εK + cD) * t * (cV * cK) := by ring

/-- **The first-meeting record mass, summed over the coordinates** at a public datum:
the never-revealed part's and the hidden randomizers' parts. -/
theorem sum_sum_revFirst_parts_le {A : SAdversary}
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ) (hρ : ρ.PosSemidef)
    (p : PP) :
    ∑ v : (s : HPos) → XD s, ∑ k : KK,
        (revW m0R LocalSig.Interp.instruments (kPartK (p, (v, k)))
          (gameR msgPol A (pubP p) v) ρ +
        (runtimeR m0R).totalWeight LocalSig.Interp.instruments
          (fun i ↦ diagMass (dCSet p v i)) (gameR msgPol A (pubP p) v) ρ) ≤
      (3 * signatureLimit : ℕ) * (epsK + cD) * ENNReal.ofReal ρ.trace.re *
        (Fintype.card ((s : HPos) → XD s) * Fintype.card KK) := by
  have hk : ∑ v : (s : HPos) → XD s, ∑ k : KK, revW m0R LocalSig.Interp.instruments
      (kPartK (p, (v, k))) (gameR msgPol A (pubP p) v) ρ ≤
      Fintype.card ((s : HPos) → XD s) * (Fintype.card KK *
        ((3 * signatureLimit : ℕ) * epsK * ENNReal.ofReal ρ.trace.re)) :=
    (Finset.sum_le_sum fun v _ ↦ sum_revW_kPartK_le hsign ρ hρ p v).trans (le_of_eq (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]))
  have hd := sum_totalWeight_dCSet_le hsign ρ hρ p
  rw [Finset.sum_congr rfl fun v _ ↦ Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  exact coords_arith _ _ _ _ _ _ _ _ hk hd

end avg

end Quantum.Sphincs.Assembly

end
