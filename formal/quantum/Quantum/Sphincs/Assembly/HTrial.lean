module

public import Quantum.Sphincs.Assembly.TrialSource

@[expose] public section

/-!
# The counter trials' hidden read mass (`htrial`)

leanSPHINCS's counterpart of leanXMSS's `Quantum.Xmss.Assembly.HTrial`. TrialSource moves the hidden
mass of the challenge prefix's reads onto the counter trials' `k`-reads
(`totalWeight_prefixT_le_trialW_sph`, leanXMSS's trial charge `trialW`). Here the trial charge is
bounded and summed over the hidden values, which gives TrialSource's `htrial` on the good hidden
values (`TrialHidGood`) in the shape of `uavg_mask_readMass_le_split_good_sph`.

The hidden cells are abstract (`Hhv`, `Hkv`, `Hk'v`, functions of the hidden values) with Masses'
`Sources` of weight `κ ≤ 2^-128` on GameTCalls' `SlotInv`; their `k'`- and `h`-cells lie in sets of
at most `2^258` cells (`trialCellCap`, enough for the in-table paths' `2^50` cells and the `2^257`
`H_msg` cells, TrialHit's `card_k'CellsP_le`). The trial blocks are TrialsOff's static
`TrialBlock` (every `PK.seed`, key, value and counter), so the hidden value `v (msgPos K)` a key
signs enters only through the trial's `k`-cell being one of them.

* **One trial on the diagonal** (leanXMSS's `sum_potential_trial_le`, `ofReal_trialDiag_eq`, over
  abstract types): on a state with no decompressed `⊥` the charge of a `k`-read at `x` is at most
  the fresh part `(2 cK + 4 cH) / |Z|` plus four times the sources `srcK'`, `srcH` of a filled
  `k`-cell and `4 / |Z|` times those of an empty one per outcome (`srcHE`).
* **The view lemma with a base set** at the `k`-read ports (`sum_totalWeight_trialReadSet_h_le`,
  `sum_totalWeight_trialReadSet_k'_le`): the sources weigh `κ` of the recorded trial cells `baseK`,
  `baseK'`.
* **The charge along the prefix** (`totalWeight_trialW_le_sph`): `NoBot` (EventSqrt's
  `forallQueries_noBot`) and `SlotInv` (GameTCalls' `forallQueries_of_hp`) at every call.
* **`htrial`** (`sum_trialMass_le_sph`): summed over the hidden values, at most `trialTau R` per
  hidden value, `trialTau R = clsCap · 2^-248 + 8 · 2^-128 · R`, given the recorded trial cells
  (`trialRecWS`) of at most `R` per hidden value; `sum_trialRecWS_le`: `R = 2 clsCap`.
* **The good hidden values** (`trialHidGood_of_trialsOff`): a `PermGood π 18` permutation and the
  hidden `k`-cells among the in-table paths' `k`-cells, off TrialsOff's event (`2^-400` of the raw
  data, `trialsOff_frac_le_keccak`).
-/

open IPFunctor Matrix MeasureTheory
open scoped ENNReal ComplexOrder Kronecker

universe u v w

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (lazy_const suppAt_empty portMass sum_totalWeight_le_of_forall diagMass)
open Quantum.Xmss.Assembly (recHwSpec realizeT realizeT_bind₂ runtimeR trialW kpot invSupp Sources
  viewBy_runtimeR_of_disc isChargeBound_of_bind₂ kValG k'ValG hSetG k'SetG srcK' srcH srcHE baseK
  baseK' sum_potential_trial_le ofReal_trialDiag_eq sum_queryWeight_view_le_base
  nonneg_of_sum_ind_le sum_ind_rate_le sum_ind_add_le totalWeight_four_eq totalWeight_two_eq
  ofReal_four_div htrial_sum_arith NoBot forallQueries_noBot diagMass_eq_inter
  traceRight_diag_eq_zero rnCard_Z)

namespace Quantum.Sphincs.Assembly

/-! ## The trial charge along the challenge prefix -/

section program

variable {M : Type} [Fintype M] [DecidableEq M]

/-- The input states of a `k`-read port at the cell `x` in `G x` satisfying `Inv`; none at the
other ports. -/
def trialReadSet (G : X → Set (HwReg X Z (Finset HPos × M)))
    (Inv : HwReg X Z (Finset HPos × M) → Prop) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      Set ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
  | .inl (.inl (.inr (.readK x _))) => {p | p.2 ∈ G x ∧ Inv p.2}
  | _ => ∅

section srcs

variable {Inv : ((s : HPos) → XD s) → HwReg X Z (Finset HPos × M) → Prop}
  {Hhv : ((s : HPos) → XD s) → Set Z} {Hkv Hk'v : ((s : HPos) → XD s) → Set X} {κ : ℝ≥0∞}

/-- The sources of the hidden `h`-cells `zc x d` at the `k`-read ports. -/
noncomputable def trialSrcsH
    (src : Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) Inv Hhv Hkv Hk'v κ)
    (zc : X → HwReg X Z (Finset HPos × M) → Z) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      (recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)) → Finset HPos
  | .inl (.inl (.inr (.readK x _))), p => src.sh (zc x p.2) p.2
  | _, _ => ∅

/-- The source values of the hidden `h`-cells `zc x d` at the `k`-read ports. -/
noncomputable def trialValsH
    (src : Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) Inv Hhv Hkv Hk'v κ)
    (zc : X → HwReg X Z (Finset HPos × M) → Z) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      (recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)) →
        (s : HPos) → ((s : HPos) → XD s) → Finset (XD s)
  | .inl (.inl (.inr (.readK x _))), p => src.Fh (zc x p.2) p.2
  | _, _ => fun _ _ ↦ ∅

/-- The sources of the hidden `k'`-cells `yc x d` at the `k`-read ports. -/
noncomputable def trialSrcsK'
    (src : Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) Inv Hhv Hkv Hk'v κ)
    (yc : X → HwReg X Z (Finset HPos × M) → X) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      (recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)) → Finset HPos
  | .inl (.inl (.inr (.readK x _))), p => src.sk' (yc x p.2) p.2
  | _, _ => ∅

/-- The source values of the hidden `k'`-cells `yc x d` at the `k`-read ports. -/
noncomputable def trialValsK'
    (src : Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) Inv Hhv Hkv Hk'v κ)
    (yc : X → HwReg X Z (Finset HPos × M) → X) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      (recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)) →
        (s : HPos) → ((s : HPos) → XD s) → Finset (XD s)
  | .inl (.inl (.inr (.readK x _))), p => src.Fk' (yc x p.2) p.2
  | _, _ => fun _ _ ↦ ∅

end srcs

theorem trialReadSet_eq_empty (G : X → Set (HwReg X Z (Finset HPos × M)))
    (Inv : HwReg X Z (Finset HPos × M) → Prop) (i : (recHwSpec X Z HPos M).Port)
    (hi : ¬ i.isLeft = true) : trialReadSet G Inv i = ∅ := by
  rcases i with ((i | c) | c) | T
  · exact absurd rfl hi
  · exact absurd rfl hi
  · exact absurd rfl hi
  · rfl

theorem trialReadSet_mono {G G' : X → Set (HwReg X Z (Finset HPos × M))}
    {Inv Inv' : HwReg X Z (Finset HPos × M) → Prop} (hG : ∀ x d, d ∈ G x → Inv d → d ∈ G' x)
    (hI : ∀ d, Inv d → Inv' d) (i : (recHwSpec X Z HPos M).Port) :
    trialReadSet G Inv i ⊆ trialReadSet G' Inv' i := by
  rcases i with ((i | c) | c) | T
  · exact Set.empty_subset _
  · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
    · exact Set.empty_subset _
    · exact fun p hp ↦ ⟨hG x p.2 hp.1 hp.2, hI p.2 hp.2⟩
    · exact Set.empty_subset _
  · exact Set.empty_subset _
  · exact Set.empty_subset _

variable (upd : TrialUpd M) (pol : DigestPolicy)

/-- **The view lemma at the `k`-read ports, through hidden `h`-cells**: when every state of
`G v x` on the invariant has the hidden, not hardwired `h`-cell `zc x d`, the masses of `G v`
along the challenge prefix add up over the hidden values to `κ` times those of a base
`Bs ⊇ G v`. -/
theorem sum_totalWeight_trialReadSet_h_le (m₀ : Finset HPos × M) (pub : Pub) (A : SAdversary)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    {Hhv : ((s : HPos) → XD s) → Set Z} {Hkv Hk'v : ((s : HPos) → XD s) → Set X} {κ : ℝ≥0∞}
    (src : Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) (SlotInv M pub) Hhv Hkv Hk'v κ)
    (G : ((s : HPos) → XD s) → X → Set (HwReg X Z (Finset HPos × M)))
    (Bs : X → Set (HwReg X Z (Finset HPos × M))) (hGB : ∀ v x, G v x ⊆ Bs x)
    (zc : X → HwReg X Z (Finset HPos × M) → Z)
    (hz : ∀ v x d, d ∈ G v x → d ∈ hSetG (Hhv v) (zc x d)) :
    ∑ v : (s : HPos) → XD s, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (fun i ↦ diagMass (trialReadSet (G v) (SlotInv M pub v) i))
        (realizeT v (prefixT M upd pol pub A)) ρ ≤
      κ * ∑ v : (s : HPos) → XD s, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (fun i ↦ diagMass (trialReadSet Bs (fun _ ↦ True) i))
        (realizeT v (prefixT M upd pol pub A)) ρ :=
  sum_totalWeight_le_of_forall (runtimeR m₀) LocalSig.Interp.instruments _ _ _ _ _ fun j ↦
    sum_queryWeight_view_le_base (runtimeR m₀) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
      (fun v ↦ realizeT v (prefixT M upd pol pub A)) (fun _ ↦ ρ) (fun _ ↦ hρ) j _
      ((viewBy_runtimeR_of_disc LocalSig.Interp.instruments m₀ (prefixT M upd pol pub A) ∅
        (disc_prefixT M upd pol pub A ∅) (fun _ ↦ ρ) (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ)
          j).viewByOn fun i ↦ i.isLeft = true)
      (fun v ↦ trialReadSet (G v) (SlotInv M pub v)) (trialReadSet Bs fun _ ↦ True)
      (fun v i hi ↦ trialReadSet_eq_empty _ _ i hi)
      (fun v i ↦ trialReadSet_mono (fun x d hd _ ↦ hGB v x hd) (fun _ _ ↦ trivial) i)
      (trialSrcsH src zc) (trialValsH src zc) (fun i p s v d ↦ by
        rcases i with ((i | c) | c) | T
        · rfl
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · rfl
          · exact src.hFh _ _ s v d
          · rfl
        · rfl
        · rfl)
      (fun v i p hp ↦ by
        rcases i with ((i | c) | c) | T
        · exact hp.elim
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · exact hp.elim
          · obtain ⟨hG, hI⟩ := hp
            obtain ⟨hm, hn⟩ := hz v x p.2 hG
            exact src.hh v (zc x p.2) p.2 hI hm hn
          · exact hp.elim
        · exact hp.elim
        · exact hp.elim)
      _ (fun i p v ↦ by
        rcases i with ((i | c) | c) | T
        · simp [trialSrcsH]
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · simp [trialSrcsH]
          · exact src.hκh _ _ v
          · simp [trialSrcsH]
        · simp [trialSrcsH]
        · simp [trialSrcsH])

/-- **The view lemma at the `k`-read ports, through hidden `k'`-cells** (as
`sum_totalWeight_trialReadSet_h_le`). -/
theorem sum_totalWeight_trialReadSet_k'_le (m₀ : Finset HPos × M) (pub : Pub) (A : SAdversary)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    {Hhv : ((s : HPos) → XD s) → Set Z} {Hkv Hk'v : ((s : HPos) → XD s) → Set X} {κ : ℝ≥0∞}
    (src : Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) (SlotInv M pub) Hhv Hkv Hk'v κ)
    (G : ((s : HPos) → XD s) → X → Set (HwReg X Z (Finset HPos × M)))
    (Bs : X → Set (HwReg X Z (Finset HPos × M))) (hGB : ∀ v x, G v x ⊆ Bs x)
    (yc : X → HwReg X Z (Finset HPos × M) → X)
    (hy : ∀ v x d, d ∈ G v x → d ∈ k'SetG (Hk'v v) (yc x d)) :
    ∑ v : (s : HPos) → XD s, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (fun i ↦ diagMass (trialReadSet (G v) (SlotInv M pub v) i))
        (realizeT v (prefixT M upd pol pub A)) ρ ≤
      κ * ∑ v : (s : HPos) → XD s, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (fun i ↦ diagMass (trialReadSet Bs (fun _ ↦ True) i))
        (realizeT v (prefixT M upd pol pub A)) ρ :=
  sum_totalWeight_le_of_forall (runtimeR m₀) LocalSig.Interp.instruments _ _ _ _ _ fun j ↦
    sum_queryWeight_view_le_base (runtimeR m₀) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
      (fun v ↦ realizeT v (prefixT M upd pol pub A)) (fun _ ↦ ρ) (fun _ ↦ hρ) j _
      ((viewBy_runtimeR_of_disc LocalSig.Interp.instruments m₀ (prefixT M upd pol pub A) ∅
        (disc_prefixT M upd pol pub A ∅) (fun _ ↦ ρ) (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ)
          j).viewByOn fun i ↦ i.isLeft = true)
      (fun v ↦ trialReadSet (G v) (SlotInv M pub v)) (trialReadSet Bs fun _ ↦ True)
      (fun v i hi ↦ trialReadSet_eq_empty _ _ i hi)
      (fun v i ↦ trialReadSet_mono (fun x d hd _ ↦ hGB v x hd) (fun _ _ ↦ trivial) i)
      (trialSrcsK' src yc) (trialValsK' src yc) (fun i p s v d ↦ by
        rcases i with ((i | c) | c) | T
        · rfl
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · rfl
          · exact src.hFk' _ _ s v d
          · rfl
        · rfl
        · rfl)
      (fun v i p hp ↦ by
        rcases i with ((i | c) | c) | T
        · exact hp.elim
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · exact hp.elim
          · obtain ⟨hG, hI⟩ := hp
            obtain ⟨hm, hn⟩ := hy v x p.2 hG
            exact src.hk' v (yc x p.2) p.2 hI hm hn
          · exact hp.elim
        · exact hp.elim
        · exact hp.elim)
      _ (fun i p v ↦ by
        rcases i with ((i | c) | c) | T
        · simp [trialSrcsK']
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · simp [trialSrcsK']
          · exact src.hκk' _ _ v
          · simp [trialSrcsK']
        · simp [trialSrcsK']
        · simp [trialSrcsK'])

/-- **The weight bounding the trial charge** at the `k`-reads (leanXMSS's `sum_potential_trial_le`,
`ofReal_trialDiag_eq`): the fresh part `F` per read call, four times the sources of a filled
`k`-cell, `4 / |Z|` times those of an empty one per outcome, on the invariant `SlotInv`. -/
noncomputable def trialBndS (pub : Pub) (v : (s : HPos) → XD s) (Hh : Set Z) (Hk' : Set X)
    (F : ℝ≥0∞) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      Matrix ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
        ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M))) ℂ → ℝ≥0∞ :=
  fun i σ ↦ F * (if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0) +
    4 * diagMass (trialReadSet (srcK' pub.perm Hk') (SlotInv M pub v) i) σ +
    4 * diagMass (trialReadSet (srcH pub.perm Hh) (SlotInv M pub v) i) σ +
    ∑ a, ENNReal.ofReal (4 / Fintype.card Z) * diagMass
      (trialReadSet (fun x ↦ srcHE pub.perm Hh x a) (SlotInv M pub v) i) σ

/-- **The trial charge on the invariant**: along the challenge prefix, leanXMSS's `trialW` is at
most `trialBndS` with the fresh part `(2 cK + 4 cH) / |Z|`, when `cK` bounds the outcomes leading a
trial block to a hidden `k'`-cell and `cH` the values leading a capacity to a hidden `h`-cell. -/
theorem totalWeight_trialW_le_sph (hpol : pol.ValFree) (m₀ : Finset HPos × M) (pub : Pub)
    (A : SAdversary) (v : (s : HPos) → XD s)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    (hnb : QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z (Finset HPos × M) ↦ m.2)
      {s | NoBot s} (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z (Finset HPos × M)) ρ))
    (Hh : Set Z) (Hk' : Set X) (cK cH : ℝ)
    (hcK : ∀ x, ∑ a : Z, Hk'.indicator (1 : X → ℝ) (pub.perm (x, a)).1 ≤ cK)
    (hcH : ∀ z : Z, ∑ w : Z, Hh.indicator (1 : Z → ℝ) (z + w) ≤ cH) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments (trialW pub.perm Hh Hk')
        (realizeT v (prefixT M upd pol pub A)) ρ ≤
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (trialBndS pub v Hh Hk' (ENNReal.ofReal ((2 * cK + 4 * cH) / Fintype.card Z)))
        (realizeT v (prefixT M upd pol pub A)) ρ := by
  have hcK0 : 0 ≤ cK := nonneg_of_sum_ind_le _ (hcK 0)
  have hcH0 : 0 ≤ cH := nonneg_of_sum_ind_le _ (hcH 0)
  refine Quantum.Xmss.Assembly.totalWeight_le_of_forallQueries (runtimeR m₀)
    LocalSig.Interp.instruments
    (fun i σ ↦ QuerySupportedOn
      (fun m : (recHwSpec X Z HPos M).In i × HwReg X Z (Finset HPos × M) ↦ m.2) {s | NoBot s}
        (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos M).In i)
          ((recHwSpec X Z HPos M).In i) ℂ) ⊗ₖ compressReg X Z (Finset HPos × M)) σ) ∧
      (readRecPort M i = true → ∀ a, ¬ SlotInv M pub v a.2 → σ a a = 0))
    (fun i E τ hτ ↦ ⟨hτ.1, fun hQ a ha ↦ traceRight_diag_eq_zero fun e ↦ hτ.2 hQ (a, e) ha⟩)
    (fun i σ hσ hok ↦ ?_) _ hρ
    (Quantum.Xmss.Assembly.forallQueries_and
      (forallQueries_noBot m₀ LocalSig.Interp.instruments _ hnb)
      (forallQueries_of_hp (fun c ↦ readRecPort_prog c) m₀ _ pub v _ ∅ ∅
        (hp_prefixT_sph upd hpol pub v A) ρ
        (hs.imp fun _ ha ↦ invP_of_label_empty (Set.mem_singleton_iff.1 ha))))
  rcases i with ((i | c) | c) | T
  · exact zero_le
  · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
    · exact zero_le
    · have hinv : ∀ a, a ∉ {p : Unit × HwReg X Z (Finset HPos × M) | SlotInv M pub v p.2} →
          σ a a = 0 := fun a ha ↦ hok.2 rfl a ha
      show ∑ r, ∑ j, potential (kpot pub.perm Hh Hk' (.afK x (r.1.getD 0)) j)
          (MatrixMap.conj (hwReadKraus (.readK x (fun m _ ↦ m)) r) σ) ≤ _
      simp only [Fintype.sum_option, kpot]
      refine (sum_potential_trial_le pub.perm _ _ x cK cH (hcK x) hcH hσ hok.1).trans ?_
      rw [ofReal_trialDiag_eq pub.perm _ _ x cK cH hcK0 hcH0 hσ]
      refine add_le_add (add_le_add (add_le_add (le_of_eq rfl) ?_) ?_)
        (Finset.sum_le_sum fun a _ ↦ ?_)
      · exact mul_le_mul_of_nonneg_left (diagMass_eq_inter _ _ hinv).le zero_le
      · exact mul_le_mul_of_nonneg_left (diagMass_eq_inter _ _ hinv).le zero_le
      · exact mul_le_mul_of_nonneg_left (diagMass_eq_inter _ _ hinv).le zero_le
    · exact zero_le
  · exact zero_le
  · exact zero_le

end program

/-! ## `htrial` -/

section htrial

/-- **The good hidden values of the trials** at the hidden `k`-cells `Hk`: a `PermGood π 18`
permutation and no trial block a hidden `k`-cell. -/
def TrialHidGood (pub : Pub) (Hk : Set X) : Prop :=
  PermGood pub.perm 18 ∧ ∀ x, TrialBlock x → x ∉ Hk

/-- `TrialHidGood`, decided classically. -/
noncomputable instance instDecidableTrialHidGood (pub : Pub) (Hk : Set X) :
    Decidable (TrialHidGood pub Hk) :=
  Classical.dec _

/-- **The good hidden values from TrialsOff**: a `PermGood π 18` permutation, the hidden `k`-cells
among the `k`-cells of the in-table paths, and no such cell a trial block. -/
theorem trialHidGood_of_trialsOff {pub : Pub} {Hk : Set X} {w : ValPos → Digest}
    (hπ : PermGood pub.perm 18) (hoff : TrialsOff pub.xw pub.keys.1 w)
    (hHk : ∀ x ∈ Hk, ∃ s, InTable s ∧ ∃ j < nBlk pub.seed s, sCellK pub.xw pub.keys.1 s w j = x) :
    TrialHidGood pub Hk := by
  refine ⟨hπ, fun x hx hk ↦ ?_⟩
  obtain ⟨s, hs, j, hj, rfl⟩ := hHk x hk
  exact hoff s hs j hj hx

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **The recorded trial cells**: at a `k`-read at `x`, the mass of the states whose `k`-cell `x`
holds a value (recorded or hardwired) plus, averaged over the outcomes `a`, the mass of those whose
trial `k'`-cell `π (x, a)` holds a value. -/
noncomputable def trialRecWS (π : Equiv.Perm (X × Z)) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      Matrix ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
        ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M))) ℂ → ℝ≥0∞ :=
  fun i σ ↦ diagMass (trialReadSet baseK (fun _ ↦ True) i) σ +
    ∑ a, (Fintype.card Z : ℝ≥0∞)⁻¹ *
      diagMass (trialReadSet (fun x ↦ baseK' π x a) (fun _ ↦ True) i) σ

/-- The bound on the hidden `k'`- and `h`-cells of the trials: `2^258` (the in-table paths' `2^50`
cells and the `2^257` `H_msg` cells fit). -/
def trialCellCap : ℕ := 2 ^ 258

/-- **The trials' hidden read mass per hidden value**: `clsCap · 2^-248` for the fresh trial cells
(`40 · 2^258 / 2^512` per read call) plus `8 · 2^-128` per unit `R` of recorded trial cells. -/
noncomputable def trialTau (R : ℝ≥0∞) : ℝ≥0∞ :=
  (clsCap : ℝ≥0∞) * (2 ^ 248 : ℝ≥0∞)⁻¹ + 8 * (2 ^ 128 : ℝ≥0∞)⁻¹ * R

set_option exponentiation.threshold 1024 in
/-- The fresh trial cells at Keccak's sizes: `40 · 2^258 / 2^512 ≤ 2^-248`. -/
theorem freshTerm_le_sph {cZ : ℕ} (hZ : cZ = 2 ^ 512) :
    ENNReal.ofReal ((2 * ((18 * trialCellCap : ℕ) : ℝ) + 4 * ((trialCellCap : ℕ) : ℝ)) /
      (cZ : ℝ)) ≤ (2 ^ 248 : ℝ≥0∞)⁻¹ := by
  subst hZ
  rw [Quantum.Xmss.Assembly.inv_two_pow_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [trialCellCap]
  push_cast
  norm_num

/-- The final constants, over abstract quantities. -/
theorem trialTau_arith (F N κ R V c : ℝ≥0∞) (hF : F * N ≤ c) (hκ : κ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹) :
    (F * N + 8 * κ * R) * V ≤ (c + 8 * (2 ^ 128 : ℝ≥0∞)⁻¹ * R) * V := by
  gcongr

variable (upd : TrialUpd M) (pol : DigestPolicy)

theorem totalWeight_trialBndS_eq (m₀ : Finset HPos × M) (pub : Pub) (v : (s : HPos) → XD s)
    (Hh : Set Z) (Hk' : Set X) (F : ℝ≥0∞) {Ω : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments (recHwSpec X Z HPos M) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset HPos × M)))
      (A × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments (trialBndS pub v Hh Hk' F) x ρ =
      F * (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (fun i σ ↦ if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0) x ρ +
        4 * (runtimeR m₀).totalWeight LocalSig.Interp.instruments (fun i ↦ diagMass
          (trialReadSet (srcK' pub.perm Hk') (SlotInv M pub v) i)) x ρ +
        4 * (runtimeR m₀).totalWeight LocalSig.Interp.instruments (fun i ↦ diagMass
          (trialReadSet (srcH pub.perm Hh) (SlotInv M pub v) i)) x ρ +
        ∑ a, ENNReal.ofReal (4 / Fintype.card Z) *
          (runtimeR m₀).totalWeight LocalSig.Interp.instruments (fun i ↦ diagMass
            (trialReadSet (fun x ↦ srcHE pub.perm Hh x a) (SlotInv M pub v) i)) x ρ :=
  totalWeight_four_eq (runtimeR m₀) LocalSig.Interp.instruments F
    (ENNReal.ofReal (4 / Fintype.card Z))
    (fun i σ ↦ if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0)
    (fun i ↦ diagMass (trialReadSet (srcK' pub.perm Hk') (SlotInv M pub v) i))
    (fun i ↦ diagMass (trialReadSet (srcH pub.perm Hh) (SlotInv M pub v) i))
    (fun a i ↦ diagMass (trialReadSet (fun x ↦ srcHE pub.perm Hh x a) (SlotInv M pub v) i)) x ρ

theorem totalWeight_trialRecWS_eq (m₀ : Finset HPos × M) (π : Equiv.Perm (X × Z))
    {Ω : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments (recHwSpec X Z HPos M) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset HPos × M)))
      (A × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments (trialRecWS π) x ρ =
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (fun i ↦ diagMass (trialReadSet baseK (fun _ ↦ True) i)) x ρ +
        ∑ a, (Fintype.card Z : ℝ≥0∞)⁻¹ * (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (fun i ↦ diagMass (trialReadSet (fun x ↦ baseK' π x a) (fun _ ↦ True) i)) x ρ :=
  totalWeight_two_eq (runtimeR m₀) LocalSig.Interp.instruments
    (Fintype.card Z : ℝ≥0∞)⁻¹ (fun i ↦ diagMass (trialReadSet baseK (fun _ ↦ True) i))
    (fun a i ↦ diagMass (trialReadSet (fun x ↦ baseK' π x a) (fun _ ↦ True) i)) x ρ

variable (A : SAdversary) {q : ℕ}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix's read and record calls: at most `clsCap`. -/
theorem hN_readRec_prefixT (pub : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (realizeT v (prefixT M upd pol pub A))
      (portCharge fun i ↦ if readRecPort M i = true then 1 else 0) clsCap := by
  have h := hN_readRec upd pol A hperm hsign pub v
  rw [gameT_eq_prefixT_bind, realizeT_bind₂] at h
  exact isChargeBound_of_bind₂ h

/-- **The counter trials' hidden read mass** (TrialSource's `htrial` at one public datum, on the
good hidden values `TrialHidGood`): summed over the hidden values, at most `trialTau R` per hidden
value, given the recorded trial cells `R` per hidden value. -/
theorem sum_trialMass_le_sph (hpol : pol.ValFree) (m₀ : Finset HPos × M) (pub : Pub)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    (hnb : QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z (Finset HPos × M) ↦ m.2)
      {s | NoBot s} (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z (Finset HPos × M)) ρ))
    (Hhv : ((s : HPos) → XD s) → Set Z) (Hkv Hk'v : ((s : HPos) → XD s) → Set X) (κ : ℝ≥0∞)
    (hκ : κ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹)
    (src : Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) (SlotInv M pub) Hhv Hkv Hk'v κ)
    (hcellK' : ∀ v, ∃ C : Finset X, (∀ y ∈ Hk'v v, y ∈ C) ∧ C.card ≤ trialCellCap)
    (hcellH : ∀ v, ∃ C : Finset Z, (∀ z ∈ Hhv v, z ∈ C) ∧ C.card ≤ trialCellCap)
    (R : ℝ≥0∞)
    (hrec : ∑ v : (s : HPos) → XD s, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (trialRecWS pub.perm) (realizeT v (prefixT M upd pol pub A)) ρ ≤
        R * Fintype.card ((s : HPos) → XD s)) :
    ∑ v : (s : HPos) → XD s, (if TrialHidGood pub (Hkv v) then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (Hhv v) (Hkv v) (Hk'v v))
      (realizeT v (prefixT M upd pol pub A)) ρ else 0) ≤
      trialTau R * Fintype.card ((s : HPos) → XD s) := by
  set cK : ℝ := ((18 * trialCellCap : ℕ) : ℝ) with hcKdef
  set cH : ℝ := ((trialCellCap : ℕ) : ℝ) with hcHdef
  set F : ℝ≥0∞ := ENNReal.ofReal ((2 * cK + 4 * cH) / Fintype.card Z) with hF
  have hper : ∀ v, (if TrialHidGood pub (Hkv v) then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (Hhv v) (Hkv v) (Hk'v v))
          (realizeT v (prefixT M upd pol pub A)) ρ else 0) ≤
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments (trialBndS pub v (Hhv v) (Hk'v v) F)
        (realizeT v (prefixT M upd pol pub A)) ρ := by
    intro v
    by_cases hT : TrialHidGood pub (Hkv v)
    · rw [ite_eq_left hT]
      obtain ⟨CK, hCK, hCKc⟩ := hcellK' v
      obtain ⟨CH, hCH, hCHc⟩ := hcellH v
      have hcK : ∀ x, ∑ a : Z, (Hk'v v).indicator (1 : X → ℝ) (pub.perm (x, a)).1 ≤ cK :=
        fun x ↦ sum_ind_rate_le hT.1 x _ CK hCK hCKc
      have hcH : ∀ z : Z, ∑ w : Z, (Hhv v).indicator (1 : Z → ℝ) (z + w) ≤ cH :=
        fun z ↦ sum_ind_add_le z _ CH hCH hCHc
      exact (totalWeight_prefixT_le_trialW_sph (Hhv v) (Hk'v v) upd pol m₀ pub A v _ hT.2
        hρ).trans (totalWeight_trialW_le_sph upd pol hpol m₀ pub A v ρ hρ hs hnb (Hhv v)
          (Hk'v v) cK cH hcK hcH)
    · rw [ite_eq_right hT]
      exact zero_le
  refine (Finset.sum_le_sum fun v _ ↦ hper v).trans ?_
  refine (Finset.sum_congr rfl fun v _ ↦ totalWeight_trialBndS_eq m₀ pub v (Hhv v)
    (Hk'v v) F (realizeT v (prefixT M upd pol pub A)) ρ).trans_le ?_
  rw [ofReal_four_div (Fintype.card Z) Fintype.card_pos]
  refine (htrial_sum_arith F clsCap κ (Fintype.card ((s : HPos) → XD s))
    (Fintype.card Z : ℝ≥0∞)⁻¹ R _ _ _
    (fun v ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (fun i ↦ diagMass (trialReadSet baseK (fun _ ↦ True) i))
      (realizeT v (prefixT M upd pol pub A)) ρ)
    _ (fun v a ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (fun i ↦ diagMass (trialReadSet (fun x ↦ baseK' pub.perm x a) (fun _ ↦ True) i))
      (realizeT v (prefixT M upd pol pub A)) ρ) ?_ ?_ ?_ ?_ ?_).trans ?_
  · calc ∑ v, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (fun i σ ↦ if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0)
          (realizeT v (prefixT M upd pol pub A)) ρ
        ≤ ∑ _v : (s : HPos) → XD s, (clsCap : ℝ≥0∞) :=
          Finset.sum_le_sum fun v _ ↦ (Quantum.Xmss.Hybrid.totalWeight_trace_le_of_isChargeBound'
            (runtimeR m₀) LocalSig.Interp.instruments (fun i ↦ readRecPort M i = true)
            (realizeT v (prefixT M upd pol pub A))
            (hN_readRec_prefixT upd pol A hperm hsign pub v) hρ).trans
            ((mul_le_mul_of_nonneg_left hρ1 zero_le).trans_eq (mul_one _))
      _ = (clsCap : ℝ≥0∞) * Fintype.card ((s : HPos) → XD s) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  · exact sum_totalWeight_trialReadSet_k'_le upd pol m₀ pub A ρ hρ src
      (fun v ↦ srcK' pub.perm (Hk'v v)) baseK
      (fun _ _ _ ⟨_, ha, _⟩ h0 ↦ by rw [ha] at h0; cases h0)
      (fun x d ↦ (pub.perm (x, (kValG x d).getD 0)).1)
      (fun _ _ _ ⟨_, ha, h⟩ ↦ by rw [ha, Option.getD_some]; exact h)
  · exact sum_totalWeight_trialReadSet_h_le upd pol m₀ pub A ρ hρ src
      (fun v ↦ srcH pub.perm (Hhv v)) baseK
      (fun _ _ _ ⟨_, ha, _⟩ h0 ↦ by rw [ha] at h0; cases h0)
      (fun x d ↦ (pub.perm (x, (kValG x d).getD 0)).2 +
        (k'ValG (pub.perm (x, (kValG x d).getD 0)).1 d).getD 0)
      (fun _ _ _ ⟨_, ha, _, hw, h⟩ ↦ by rw [ha, Option.getD_some, hw, Option.getD_some]; exact h)
  · intro a
    exact sum_totalWeight_trialReadSet_h_le upd pol m₀ pub A ρ hρ src
      (fun v x ↦ srcHE pub.perm (Hhv v) x a) (fun x ↦ baseK' pub.perm x a)
      (fun _ _ _ ⟨_, _, hw, _⟩ h0 ↦ by rw [hw] at h0; cases h0)
      (fun x d ↦ (pub.perm (x, a)).2 + (k'ValG (pub.perm (x, a)).1 d).getD 0)
      (fun _ _ _ ⟨_, _, hw, h⟩ ↦ by rw [hw, Option.getD_some]; exact h)
  · simpa only [totalWeight_trialRecWS_eq] using hrec
  · refine trialTau_arith F clsCap κ R _ _ ?_ hκ
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (freshTerm_le_sph rnCard_Z) zero_le

omit hperm hsign in
/-- The diagonal mass of a `k`-read port's input set is at most the trace at the read and record
ports, and `0` elsewhere. -/
theorem diagMass_trialReadSet_le (G : X → Set (HwReg X Z (Finset HPos × M)))
    (Inv : HwReg X Z (Finset HPos × M) → Prop) (i : (recHwSpec X Z HPos M).Port)
    {σ : Matrix ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
      ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M))) ℂ}
    (hσ : σ.PosSemidef) :
    diagMass (trialReadSet G Inv i) σ ≤
      if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0 := by
  have hre : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : diagMass (trialReadSet G Inv i) σ ≤ ENNReal.ofReal σ.trace.re := by
    rw [diagMass, Matrix.trace, Complex.re_sum]
    simp only [Matrix.diag_apply]
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ ↦ hre a]
    refine Finset.sum_le_sum fun a _ ↦ ?_
    by_cases hS : a ∈ trialReadSet G Inv i
    · rw [Set.indicator_of_mem hS]
    · rw [Set.indicator_of_notMem hS]
      exact zero_le
  rcases i with ((p | c) | c) | T
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun a _ ↦
      Set.indicator_of_notMem (Set.notMem_empty a) _) zero_le
  · exact htr.trans_eq (ite_eq_left rfl).symm
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun a _ ↦
      Set.indicator_of_notMem (Set.notMem_empty a) _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun a _ ↦
      Set.indicator_of_notMem (Set.notMem_empty a) _) zero_le

omit hperm hsign in
/-- **The recorded trial cells per call**: a diagonal mass plus an average of diagonal masses, at
most `2` times the trace at the read and record ports. -/
theorem trialRecWS_le (π : Equiv.Perm (X × Z)) (i : (recHwSpec X Z HPos M).Port)
    (σ : Matrix ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
      ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M))) ℂ)
    (hσ : σ.PosSemidef) :
    trialRecWS π i σ ≤ 2 * if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0 := by
  set D : ℝ≥0∞ := if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0
  calc trialRecWS π i σ
      ≤ D + ∑ _a : Z, (Fintype.card Z : ℝ≥0∞)⁻¹ * D :=
        add_le_add (diagMass_trialReadSet_le _ _ i hσ) (Finset.sum_le_sum fun a _ ↦
          mul_le_mul_of_nonneg_left (diagMass_trialReadSet_le _ _ i hσ) zero_le)
    _ = 2 * D := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _), one_mul, two_mul]

/-- **`hrec` with `R = 2 clsCap`**: the recorded trial cells along the challenge prefix weigh at
most `2` per read call (`trialRecWS_le`), at most `clsCap` read calls. -/
theorem sum_trialRecWS_le (m₀ : Finset HPos × M) (pub : Pub)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1) :
    ∑ v : (s : HPos) → XD s, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (trialRecWS pub.perm) (realizeT v (prefixT M upd pol pub A)) ρ ≤
        2 * (clsCap : ℝ≥0∞) * Fintype.card ((s : HPos) → XD s) := by
  have hv : ∀ v : (s : HPos) → XD s, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (trialRecWS pub.perm) (realizeT v (prefixT M upd pol pub A)) ρ ≤
        2 * (clsCap : ℝ≥0∞) := fun v ↦ by
    refine ((Quantum.Xmss.Hybrid.totalWeight_le_totalWeight (runtimeR m₀)
      LocalSig.Interp.instruments
      (w' := fun i σ ↦ 2 * if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0)
      (fun i σ hσ ↦ trialRecWS_le _ i σ hσ) _ hρ).trans_eq
      (Quantum.Xmss.Hybrid.totalWeight_const_mul_weight (runtimeR m₀)
        LocalSig.Interp.instruments 2
        (fun i σ ↦ if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0) _ ρ)).trans
      (mul_le_mul_of_nonneg_left ?_ zero_le)
    exact (Quantum.Xmss.Hybrid.totalWeight_trace_le_of_isChargeBound' (runtimeR m₀)
      LocalSig.Interp.instruments (fun i ↦ readRecPort M i = true) _
      (hN_readRec_prefixT upd pol A hperm hsign pub v) hρ).trans
      ((mul_le_mul_of_nonneg_left hρ1 zero_le).trans_eq (mul_one _))
  calc ∑ v : (s : HPos) → XD s, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (trialRecWS pub.perm) (realizeT v (prefixT M upd pol pub A)) ρ
      ≤ ∑ _v : (s : HPos) → XD s, 2 * (clsCap : ℝ≥0∞) := Finset.sum_le_sum fun v _ ↦ hv v
    _ = 2 * (clsCap : ℝ≥0∞) * Fintype.card ((s : HPos) → XD s) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **`htrial` with the recorded trial cells bounded** (`sum_trialMass_le_sph` with
`sum_trialRecWS_le`): at most `trialTau (2 clsCap)` per hidden value. -/
theorem sum_trialMass_le_clsCap (hpol : pol.ValFree) (m₀ : Finset HPos × M) (pub : Pub)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    (hnb : QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z (Finset HPos × M) ↦ m.2)
      {s | NoBot s} (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z (Finset HPos × M)) ρ))
    (Hhv : ((s : HPos) → XD s) → Set Z) (Hkv Hk'v : ((s : HPos) → XD s) → Set X) (κ : ℝ≥0∞)
    (hκ : κ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹)
    (src : Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) (SlotInv M pub) Hhv Hkv Hk'v κ)
    (hcellK' : ∀ v, ∃ C : Finset X, (∀ y ∈ Hk'v v, y ∈ C) ∧ C.card ≤ trialCellCap)
    (hcellH : ∀ v, ∃ C : Finset Z, (∀ z ∈ Hhv v, z ∈ C) ∧ C.card ≤ trialCellCap) :
    ∑ v : (s : HPos) → XD s, (if TrialHidGood pub (Hkv v) then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (Hhv v) (Hkv v) (Hk'v v))
      (realizeT v (prefixT M upd pol pub A)) ρ else 0) ≤
      trialTau (2 * clsCap) * Fintype.card ((s : HPos) → XD s) :=
  sum_trialMass_le_sph upd pol A hperm hsign hpol m₀ pub ρ hρ hρ1 hs hnb Hhv Hkv Hk'v κ hκ src
    hcellK' hcellH _ (sum_trialRecWS_le upd pol A hperm hsign m₀ pub ρ hρ hρ1)

end htrial

end Quantum.Sphincs.Assembly

end
