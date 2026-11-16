module

public import Quantum.Sphincs.Assembly.HmsgCoversInv
public import Quantum.Sphincs.Assembly.Masses

@[expose] public section

/-!
# The template's `H_msg` cells weigh `5 · 2^-128` per call

Masses' hypothesis `hX` (the further hidden cells of the public data and the hidden values) for the
template's `H_msg` cells at the hidden randomizers (HmsgCovers' `tmCellsH`, `tmCellsK`,
`tmCellsK'`, on the static condition `HStatic`): their sources are the randomizers `.rnd M`
(`hmSources`, Masses' `Sources` on HmsgCoversInv's invariant `HmInv`). A cell names at most five
pairs (randomizer, call): a block names its input (`dLabCell` is injective), a rate on
`HmsgRateInj`, a capacity on `HmsgCapLoad`; so it weighs at most `5 / |Randomizer|`
(`kappaH`).

* `sum_tmMass_le`: summed over the hidden values, at most `N · kappaH` per hidden value for the
  ports `Q` other than the program and record ports.
* `hX_sponge`, `hX_read`: Masses' `hS_sph` and `hRd_sph` hypotheses with `κX = kappaH` (the read
  mass is the mass at the read ports alone: a record port has no hidden cells, `readMass_eq_readQ`).
* `hS_sph'`, `hRd_sph'`: the masked hybrid's hypotheses with `hX` discharged.
-/

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message Randomizer)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (uavg portMass spongeMass readMass capOf rateOf)
open Quantum.Xmss.Assembly (Sources recHwSpec recSpec runtimeR realizeT invSupp extCls
  sum_totalWeight_portMass_runtimeR_le_inv)
open Quantum.Sphincs.Hybrid (DLab dLabCell dLabCell_injective)

namespace Quantum.Sphincs.Assembly

/-! ## The sources -/

section sources

/-- The randomizer coordinates. -/
def rndSet : Finset HPos :=
  Finset.univ.map ⟨HPos.rnd, fun _ _ h ↦ HPos.rnd.inj h⟩

theorem rnd_mem_rndSet (M : Message) : HPos.rnd M ∈ rndSet :=
  Finset.mem_map_of_mem _ (Finset.mem_univ M)

/-- The randomizers of `M` among the inputs `T`. -/
def srcOfT (T : Finset (Randomizer × DLab)) (M : Message) : Finset Randomizer :=
  (T.filter fun c ↦ c.2.1 = M).image Prod.fst

theorem mem_srcOfT {T : Finset (Randomizer × DLab)} {R : Randomizer} {a : DLab} (h : (R, a) ∈ T) :
    R ∈ srcOfT T a.1 :=
  Finset.mem_image.mpr ⟨(R, a), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

theorem sum_card_srcOfT_le (T : Finset (Randomizer × DLab)) :
    ∑ M, (srcOfT T M).card ≤ T.card :=
  (Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le).trans
    (Finset.card_eq_sum_card_fiberwise fun c _ ↦ Finset.mem_univ c.2.1).symm.le

open scoped Classical in
/-- The input whose cell `x` is, if any. -/
noncomputable def oneOf {α : Type} (c : Randomizer × DLab → α) (x : α) :
    Finset (Randomizer × DLab) :=
  @dite _ (∃ q, c q = x) (Classical.propDecidable _) (fun h ↦ {h.choose}) fun _ ↦ ∅

theorem card_oneOf_le {α : Type} (c : Randomizer × DLab → α) (x : α) : (oneOf c x).card ≤ 1 := by
  unfold oneOf
  split
  · exact (Finset.card_singleton _).le
  · exact Finset.card_empty.le.trans zero_le_one

theorem mem_oneOf {α : Type} {c : Randomizer × DLab → α} (hc : Function.Injective c) {x : α}
    {q : Randomizer × DLab} (hq : c q = x) : q ∈ oneOf c x := by
  have h : ∃ q, c q = x := ⟨q, hq⟩
  unfold oneOf
  rw [dite_eq_left_of_eq_true (eq_true h), Finset.mem_singleton]
  exact hc (hq.trans h.choose_spec.symm)

open scoped Classical in
/-- The inputs whose capacity is `z`, on the static condition. -/
noncomputable def inZ (pub : Pub) (root : Digest) (z : Z) : Finset (Randomizer × DLab) :=
  @dite _ (HStatic pub root) (Classical.propDecidable _) (fun h ↦ (h.2 z).choose) fun _ ↦ ∅

theorem card_inZ_le (pub : Pub) (root : Digest) (z : Z) : (inZ pub root z).card ≤ 5 := by
  unfold inZ
  split
  · rename_i h
    exact (h.2 z).choose_spec.1
  · exact Finset.card_empty.le.trans (by norm_num)

theorem mem_inZ {pub : Pub} {root : Digest} (h : HStatic pub root) {z : Z} {R : Randomizer}
    {a : DLab} (hz : hmCellZ pub root R a = z) : (R, a) ∈ inZ pub root z := by
  unfold inZ
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact (h.2 z).choose_spec.2 R a hz

theorem rootV_update_rnd (v : (s : HPos) → XD s) (M : Message) (d : XD (.rnd M)) :
    rootV (Function.update v (.rnd M) d) = rootV v :=
  Function.update_of_ne (fun h ↦ HPos.noConfusion h) _ _

/-- The source values of an `h`-cell. -/
noncomputable def srcH (p : PP) (z : Z) : (s : HPos) → ((s : HPos) → XD s) → Finset (XD s)
  | .rnd M, v => srcOfT (inZ (pubP p) (rootV v) z) M
  | .val _, _ => ∅
  | .dig _ _, _ => ∅
  | .str _ _, _ => ∅
  | .asg _ _, _ => ∅

/-- The source values of a `k`-cell. -/
noncomputable def srcK (p : PP) (x : X) : (s : HPos) → ((s : HPos) → XD s) → Finset (XD s)
  | .rnd M, v => srcOfT (oneOf (fun c ↦ hmCellK (pubP p) (rootV v) c.1 c.2) x) M
  | .val _, _ => ∅
  | .dig _ _, _ => ∅
  | .str _ _, _ => ∅
  | .asg _ _, _ => ∅

/-- The source values of a `k'`-cell. -/
noncomputable def srcK' (p : PP) (x : X) : (s : HPos) → ((s : HPos) → XD s) → Finset (XD s)
  | .rnd M, v => srcOfT (oneOf (fun c ↦ hmCellR (pubP p) (rootV v) c.1 c.2) x) M
  | .val _, _ => ∅
  | .dig _ _, _ => ∅
  | .str _ _, _ => ∅
  | .asg _ _, _ => ∅

/-- **The per-call weight of the template's `H_msg` cells**: `5 / |Randomizer|`. -/
noncomputable def kappaH : ℝ≥0∞ :=
  5 * (Fintype.card Randomizer : ℝ≥0∞)⁻¹

/-- A sum over the randomizer coordinates of counts of randomizers. -/
theorem sum_rndSet_le (g : (s : HPos) → Finset (XD s)) (T : Finset (Randomizer × DLab))
    (hg : ∀ M, g (.rnd M) = srcOfT T M) (hT : T.card ≤ 5) :
    ∑ s ∈ rndSet, ((g s).card : ℝ≥0∞) * (Fintype.card (XD s) : ℝ≥0∞)⁻¹ ≤ kappaH := by
  have e : ∑ s ∈ rndSet, ((g s).card : ℝ≥0∞) * (Fintype.card (XD s) : ℝ≥0∞)⁻¹ =
      ∑ M : Message, ((g (.rnd M)).card : ℝ≥0∞) * (Fintype.card (XD (.rnd M)) : ℝ≥0∞)⁻¹ :=
    Finset.sum_map _ _ _
  have h : ∀ M ∈ (Finset.univ : Finset Message),
      ((g (.rnd M)).card : ℝ≥0∞) * (Fintype.card (XD (.rnd M)) : ℝ≥0∞)⁻¹ =
        ((srcOfT T M).card : ℝ≥0∞) * (Fintype.card Randomizer : ℝ≥0∞)⁻¹ := fun M _ ↦ by
    rw [hg M]
    rfl
  rw [e, Finset.sum_congr rfl h, ← Finset.sum_mul, kappaH]
  gcongr
  exact_mod_cast (sum_card_srcOfT_le T).trans hT

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **The sources of the template's `H_msg` cells** on HmsgCoversInv's invariant: the randomizers;
`kappaH` per cell. -/
noncomputable def hmSources (p : PP) :
    Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) (HmInv (pubP p)) (tmCellsH p) (tmCellsK p)
      (tmCellsK' p) kappaH where
  sh _ _ := rndSet
  sk _ _ := rndSet
  sk' _ _ := rndSet
  Fh z _ s v := srcH p z s v
  Fk x _ s v := srcK p x s v
  Fk' x _ s v := srcK' p x s v
  hFh z _ s v d := by
    cases s with
    | rnd M => exact congrArg (fun r ↦ srcOfT (inZ (pubP p) r z) M) (rootV_update_rnd v M d)
    | _ => rfl
  hFk x _ s v d := by
    cases s with
    | rnd M =>
      exact congrArg (fun r ↦ srcOfT (oneOf (fun c ↦ hmCellK (pubP p) r c.1 c.2) x) M)
        (rootV_update_rnd v M d)
    | _ => rfl
  hFk' x _ s v d := by
    cases s with
    | rnd M =>
      exact congrArg (fun r ↦ srcOfT (oneOf (fun c ↦ hmCellR (pubP p) r c.1 c.2) x) M)
        (rootV_update_rnd v M d)
    | _ => rfl
  hh v z r hI hz hn := by
    obtain ⟨hS, M, i, rfl⟩ := hz
    exact ⟨.rnd M, rnd_mem_rndSet M, fun hm ↦ (hmCells_hardwired (pubP p) v hI hm i).2.2 hn,
      mem_srcOfT (a := (M, i)) (mem_inZ hS rfl)⟩
  hk v x r hI hx hn := by
    obtain ⟨-, M, i, rfl⟩ := hx
    exact ⟨.rnd M, rnd_mem_rndSet M, fun hm ↦ (hmCells_hardwired (pubP p) v hI hm i).1 hn,
      mem_srcOfT (a := (M, i)) (mem_oneOf (c := fun c ↦ hmCellK (pubP p) (rootV v) c.1 c.2)
        (dLabCell_injective (pubP p).seed (rootV v)) rfl)⟩
  hk' v x r hI hx hn := by
    obtain ⟨hS, M, i, rfl⟩ := hx
    exact ⟨.rnd M, rnd_mem_rndSet M, fun hm ↦ (hmCells_hardwired (pubP p) v hI hm i).2.1 hn,
      mem_srcOfT (a := (M, i))
        (mem_oneOf (c := fun c ↦ hmCellR (pubP p) (rootV v) c.1 c.2) hS.1 rfl)⟩
  hκh z _ v := sum_rndSet_le _ _ (fun _ ↦ rfl) (card_inZ_le _ _ z)
  hκk x _ v := sum_rndSet_le _ _ (fun _ ↦ rfl) ((card_oneOf_le _ x).trans (by norm_num))
  hκk' x _ v := sum_rndSet_le _ _ (fun _ ↦ rfl) ((card_oneOf_le _ x).trans (by norm_num))

end sources

/-! ## The masses -/

section mass

variable (Q : (recHwSpec X Z HPos Selections).Port → Prop) [DecidablePred Q] (A : SAdversary)
  (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)))
    (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos))) ℂ)

/-- **The template's `H_msg` cells' mass**, summed over the hidden values: at most `kappaH` per call
of the ports `Q` (no program or record port). -/
theorem sum_tmMass_le (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQr : ∀ T, ¬Q (.inr T))
    (hρ : ρ.PosSemidef) (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)) ↦ p.2.2.2.1)
      {∅} ρ)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge fun i ↦ if Q i then 1 else 0) N)
    (p : PP) :
    ∑ v, (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (portMass Q (tmCellsH p v) (tmCellsK p v) (tmCellsK' p v)) (gameR msgPol A (pubP p) v) ρ ≤
        N * kappaH * Fintype.card ((s : HPos) → XD s) := by
  refine (sum_totalWeight_portMass_runtimeR_le_inv LocalSig.Interp.instruments Q m0R
    (fun r ↦ r.2.2.1) (fun v ↦ gameR msgPol A (pubP p) v) (fun _ ↦ ρ) (fun _ ↦ hρ)
    (fun j ↦ viewByOn_gameT Selections cwUpd msgPol (pubP p) A m0R ρ j) (HmInv (pubP p))
    (fun v ↦ forallQueries_hmInv_gameT cwUpd hQ hQr m0R (pubP p) A v ρ hs)
    (tmCellsH p) (tmCellsK p) (tmCellsK' p) _ (hmSources Selections p)
    (fun v ↦ hN (pubP p) v)).trans ?_
  calc kappaH * (N * ∑ _v : (s : HPos) → XD s, ENNReal.ofReal ρ.trace.re)
      ≤ kappaH * (N * ∑ _v : (s : HPos) → XD s, (1 : ℝ≥0∞)) := by gcongr
    _ = N * kappaH * Fintype.card ((s : HPos) → XD s) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        ring

/-- The read ports alone. -/
def ReadQ : (recHwSpec X Z HPos Selections).Port → Prop
  | .inl (.inl (.inr _)) => True
  | _ => False

instance instDecidablePredReadQ : DecidablePred ReadQ := fun i ↦ by
  rcases i with ((i | c) | c) | T <;> unfold ReadQ <;> infer_instance

/-- **The read mass is the mass at the read ports alone**: a record port has no hidden cells. -/
theorem readMass_eq_readQ (Hh : Set Z) (Hk Hk' : Set X) :
    readMass (S := HPos) (M' := Selections) Hh Hk Hk' = portMass ReadQ Hh Hk Hk' := by
  funext i σ
  rcases i with ((i | c) | c) | T
  · rfl
  · rfl
  · rfl
  · rfl

variable {q : ℕ}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **`hX` at the sponge ports**: `κX = kappaH`. -/
theorem hX_sponge (p : PP) :
    ∑ v, (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (spongeMass (tmCellsH p v) (tmCellsK p v) (tmCellsK' p v)) (gameR msgPol A (pubP p) v)
        initR ≤ ((6 * q : ℕ) : ℝ≥0∞) * kappaH * Fintype.card ((s : HPos) → XD s) :=
  sum_tmMass_le (fun i ↦ extCls X Z (Mem HPos) (recSpec HPos Selections) i = false) A initR
    (fun _ h ↦ Bool.noConfusion h) (fun _ h ↦ Bool.noConfusion h) initR_posSemidef
    ofReal_trace_initR_le_one (Quantum.Xmss.Hybrid.querySupportedOn_initR m0R _)
    (advCalls_gameR_Q A hperm hsign) p

/-- The read ports' charge, from the read and record ports'. -/
theorem clsCalls_gameR_readQ (pub : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge fun i ↦ if ReadQ i then 1 else 0)
      clsCap := by
  refine Quantum.Xmss.Assembly.isChargeBound_mono_charge (fun s c ↦ ?_)
    (hN_readRec cwUpd msgPol A hperm hsign pub v)
  rcases c with o | ⟨((i | c) | c) | T, E, ℓ⟩ <;> simp [portCharge, ReadQ, readRecPort]

/-- **`hX` at the read ports**: `κX = kappaH`. -/
theorem hX_read (p : PP) :
    ∑ v, (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (readMass (tmCellsH p v) (tmCellsK p v) (tmCellsK' p v)) (gameR msgPol A (pubP p) v)
        initR ≤ clsCap * kappaH * Fintype.card ((s : HPos) → XD s) := by
  simp only [readMass_eq_readQ]
  exact sum_tmMass_le ReadQ A initR (fun _ h ↦ h) (fun _ h ↦ h) initR_posSemidef
    ofReal_trace_initR_le_one (Quantum.Xmss.Hybrid.querySupportedOn_initR m0R _)
    (clsCalls_gameR_readQ A hperm hsign) p

end mass

/-! ## The masked hybrid's hypotheses with `hX` discharged -/

section hybrid

variable (A : SAdversary) {q : ℕ}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

open scoped Classical in
/-- **`hS`** of the masked hybrid at the good set `FullG (SrcS S)`, `κ = 2^-128 + kkEps + kappaH +
chgRevAvg`. -/
theorem hS_sph' (S : PP → ((s : HPos) → XD s) → Prop)
    (hSt : ∀ p v, S p v → HStatic (pubP p) (rootV v)) :
    uavg (fun t : FT ↦ if FullG (SrcS S) t then (runtimeR m0R).totalWeight
      LocalSig.Interp.instruments
      (spongeMass (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t)))
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) initR else 0) ≤
      ((6 * q : ℕ) : ℝ≥0∞) * ((2 ^ 128 : ℝ≥0∞)⁻¹ + kkEps + kappaH + chgRevAvg A initR S) :=
  hS_sph A hperm hsign S hSt kappaH (hX_sponge A hperm hsign)

open scoped Classical in
/-- **`hRd`** of the masked hybrid at the good set `FullG (SrcS S)`,
`ν = trialTau (2 clsCap) + 2^-128 · 3 verifyBlocks + clsCap (kkEps + kappaH) + clsCap chgRevAvg`. -/
theorem hRd_sph' (S : PP → ((s : HPos) → XD s) → Prop)
    (hSt : ∀ p v, S p v → HStatic (pubP p) (rootV v))
    (hOff : ∀ p v, S p v → TrialsOff (pubP p).xw (pubP p).keys.1 (valsOf v)) :
    uavg (fun t : FT ↦ if FullG (SrcS S) t then (runtimeR m0R).totalWeight
      LocalSig.Interp.instruments
      (readMass (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t)))
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) initR else 0) ≤
      trialTau (2 * clsCap) + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) +
        clsCap * kkEps + clsCap * kappaH + clsCap * chgRevAvg A initR S :=
  hRd_sph A hperm hsign S hSt hOff kappaH (hX_read A hperm hsign)

end hybrid

end Quantum.Sphincs.Assembly

end
