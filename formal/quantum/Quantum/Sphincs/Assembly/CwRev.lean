module

public import Quantum.Sphincs.Assembly.CwRec
public import Quantum.Xmss.Assembly.CwRev

@[expose] public section

/-!
# The reveal charges of leanSPHINCS's counter searches

CwRec reduces the codeword-recorded mass of the challenge prefix (`cwRecPre`) to the fresh parts,
the programs of trial blocks (`cwProgW`) and the reveal charges (`cwRevW`): at each reveal
disclosing the value `v (msgPos K)` the key `K` signs (a FORS opening for `K_0(idx)`, a layer
signature for the key above), four times each trial of `K`'s search whose block is recorded or
hardwired while `K` is unselected. Here those charges are bounded, as leanXMSS's
`Quantum.Xmss.Assembly.CwRev`, keyed by keys.

* **The programs of trial blocks vanish** (`totalWeight_cwProgW_eq_zero`): the prefix programs only
  cells of `ProgCell` (GameTCalls' batch invariant), no trial block under `TrialsOff`
  (`not_progCell_k`).
* **Support invariants from port conditions** (`forallQueries_supp_of_port`): the hardwired cells
  stay in `ProgCell` along the prefix (`forallQueries_goodW_prefixR`).
* **The potential `Ψ`** (`revPot`): the recorded `k`-cells that are trial blocks of keys whose value
  is undisclosed. It is one-cell Lipschitz (a block names its key: `isBlk_unique`), the searches'
  reads (whose key's value is disclosed, `labInv`), programs and records do not raise it, and a
  reveal disclosing `K`'s value lowers it by `K`'s recorded trial blocks (`revDropO_add_le`). Along
  the prefix the drops add up to at most `6q` (`totalWeight_revDropW_le`).
* **First disclosures, recorded blocks** (`firstW`, `sum_totalWeight_firstW_le`): `K`'s value is
  the undisclosed source (Disclose's view lemma with a weight per state); a block determines the
  value and the counter (the counter is public, the hidden part is the signed value), so all the
  values whose trial blocks are recorded inject into the drop of `Ψ`:
  `4 · 6q / 2^128 = 24q · 2^-128` per hidden value (`revFirstC_eq`), without leanXMSS's `2^32`.
* **First disclosures, hardwired blocks** (`hwRevW`): no trial block is hardwired under
  `TrialsOff` (`totalWeight_hwRevW_eq_zero`).
* **Repeated disclosures** (`reRevW`, `CwReView`): a disclosure of a value already disclosed with
  its key unselected (the earlier search failed), charged `4 · 2^32` times its mass; the hypothesis
  is discharged by CwReFail.
* **The average** (`sum_cwRecPre_good_le`, `uavg_cwRecPre_le_rev`): over the hidden values with
  `TrialsOff`, at most `cwRevTau q ε`.
-/

universe u v w

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest PublicParameter HashInput HashOutput Message)
open Quantum.Xmss (X Z blocks)
open Quantum.Xmss.Hybrid (LazyProg restrictTo totalWeight_le_totalWeight totalWeight_add_weight
  totalWeight_const_mul_weight setProj diagMass diagMass_mono diagMass_empty progUpdate
  hwProgKraus_ne_zero_snd uavg totalWeight_chargeTrace_le sum_totalWeight_le_of_forall lazy_const
  suppAt_empty totalWeight_fintype_sum querySupportedOn_queryStep)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT RevealVals extWeight extCls
  ModedP recKraus sum_recKraus eq_of_recKraus_ne_zero cw_readKrausK_ne_zero cw_readKrausK'_ne_zero
  cw_readKrausH_ne_zero potential_diagPot_sqrt tsum_potential_sponge_le
  totalWeight_le_potential_of_forallQueries potential_basis_init viewBy_runtimeR_of_disc kWt
  sum_queryWeight_view_le_wt tsum_potential_le_of_keep card_filter_le_of_injective
  mem_filter_univ_of diagMass_le_three diagMass_eq_zero_of card_digest_inv
  querySupportedOn_traceRight totalWeight_le_of_forallQueries forallQueries_of_modedP cwFreshEps)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default
size. -/
set_option synthInstance.maxSize 2000

/-! ## Support invariants from port conditions -/

section suppPort

variable {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}} {Ω : QReg → Type w}
  (R : QuantumRuntime spec) (I : L.Interp)

/-- **A support invariant from a port condition**: if every call satisfying `Q` keeps the support
in `Inv`, a program calling only ports satisfying `Q`, run from an operator supported on `Inv`,
presents every call an operator supported on `Inv`. -/
theorem forallQueries_supp_of_port (Q : spec.Port → Prop) (Inv : Set R.D)
    (hstep : ∀ i r (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ), Q i →
      QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) Inv σ →
      QuerySupportedOn (fun m : spec.Out i × R.D ↦ m.2) Inv ((R.step i).branch r σ))
    {A : QReg} (x : QuantumComp L spec Ω A) :
    ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ}, R.ForallQueries I (fun i _ _ ↦ Q i) x ρ →
      QuerySupportedOn (fun m : A × R.D ↦ m.2) Inv ρ →
      R.ForallQueries I (fun i E σ ↦ Q i ∧
        QuerySupportedOn (fun m : (spec.In i × R.D) × E ↦ m.1.2) Inv σ) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _; trivial
  | primBind _ o k ih =>
    intro ρ hq hρ
    rw [QuantumRuntime.forallQueries_primBind_iff] at hq ⊢
    exact fun b ↦ ih b (hq b) (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro ρ hq hρ
    rw [QuantumRuntime.forallQueries_queryBind_iff] at hq ⊢
    refine ⟨⟨hq.1, ?_⟩, fun r ↦ ih r (hq.2 r)
      (querySupportedOn_queryStep R (fun s ↦ s) i r (fun σ h ↦ hstep i r σ hq.1 h) E ℓ hρ)⟩
    exact (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
      (q' := fun m : (spec.In i × R.D) × E ↦ m.1.2) (S' := Inv) fun m hm ↦ by
        obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
        rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

end suppPort

/-! ## The program cells of the prefix -/

section progCells

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **The prefix's program ports satisfy `cellOk (ProgCell pub v)` in batch order.** -/
theorem cwHb_prefixT (pol : DigestPolicy) (A : SAdversary) :
    HB (cellOk (M := Selections) (ProgCell pub v)) v (prefixT Selections cwUpd pol pub A) ∅ ∅ :=
  hb_revealThen _ v _ _ fun _ ↦
    hb₂_bind _ v _ _ (hb_substitute _ v _ (hb_challengeT _ v pub
      (fun _ hs ↦ batchOk_slotCell pub v hs) (fun msg i y ↦ batchOk_hmsgCall pub v msg i y)
      cwUpd pol) _) fun _ ↦ subset_rfl

/-- **The realized prefix calls only program ports of `ProgCell` cells.** -/
theorem cwCellPortIn_prefixR (pol : DigestPolicy) (A : SAdversary)
    (ρ : Matrix (QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D)
      (QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D) ℂ) :
    (runtimeR m0R).ForallQueries LocalSig.Interp.instruments
      (fun j _ _ ↦ CellPortIn (ProgCell pub v) j) (prefixR pol A pub v) ρ :=
  forallQueries_cellPortIn_of_hb m0R _ _ v _ ∅ ∅ (cwHb_prefixT pub v pol A) heldCompat_empty ρ

/-- **The hardwired cells stay in `ProgCell` along the realized prefix.** -/
theorem forallQueries_goodW_prefixR (pol : DigestPolicy) (A : SAdversary) :
    (runtimeR m0R).ForallQueries LocalSig.Interp.instruments (fun i E σ ↦
      CellPortIn (ProgCell pub v) i ∧ QuerySupportedOn
        (fun m : ((recHwSpec X Z HPos Selections).In i ×
          (runtimeR (X := X) (Z := Z) m0R).D) × E ↦ m.1.2)
        {s : HwReg X Z (Mem HPos) | GoodW (ProgCell pub v) s.2.1} σ)
      (prefixR pol A pub v) initR :=
  forallQueries_supp_of_port (runtimeR m0R) .instruments (CellPortIn (ProgCell pub v))
    {s : HwReg X Z (Mem HPos) | GoodW (ProgCell pub v) s.2.1}
    (fun i r σ hi hσ ↦ by
      classical
      have h := cutStepP_good (Pc := ProgCell pub v) m0R i r σ hσ
      unfold cutStepP at h
      rwa [ite_eq_left hi] at h)
    _ (cwCellPortIn_prefixR pub v pol A initR) (supp_init_good m0R)

/-- **A trial block is no programmable `k`-cell** under `TrialsOff`. -/
theorem not_progCell_cwBlk (hoff : TrialsOff pub.xw pub.keys.1 (valsOf v)) (K : Key) (m : Digest)
    (j : ℕ) : ¬ProgCell pub v (.k (cwBlk pub.seed K m j)) :=
  not_progCell_k (pub := pub) (v := v) hoff (blocks_encTrialIn_eq pub.seed K m j)

/-- **The programs of trial blocks vanish along the prefix** under `TrialsOff`. -/
theorem totalWeight_cwProgW_eq_zero (pol : DigestPolicy) (A : SAdversary)
    (hoff : TrialsOff pub.xw pub.keys.1 (valsOf v)) :
    (runtimeR m0R).totalWeight .instruments (cwProgW pub.seed) (prefixR pol A pub v) initR = 0 := by
  refine le_antisymm ?_ zero_le
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i _ ↦ CellPortIn (ProgCell pub v) i) (fun _ _ _ h ↦ h)
    (w' := fun i σ ↦ 0 * cwProgW pub.seed i σ) (fun i σ _ hi ↦ ?_) _ initR_posSemidef
    (cwCellPortIn_prefixR pub v pol A initR)).trans
    (le_of_eq ((totalWeight_const_mul_weight (runtimeR m0R) .instruments 0 (cwProgW pub.seed) _
      initR).trans (zero_mul _)))
  rw [zero_mul]
  rcases i with ((i | c) | c) | T
  · exact le_rfl
  · exact le_rfl
  · show cwProgCharge pub.seed c σ ≤ 0
    rcases c with ⟨z, w⟩ | ⟨x, w⟩ | ⟨x, w⟩
    · exact le_rfl
    · classical
      show (if IsCwBlk pub.seed x then _ else 0) ≤ 0
      rw [ite_eq_right]
      rintro ⟨K, m, j, -, rfl⟩
      exact not_progCell_cwBlk pub v hoff K m j hi
    · exact le_rfl
  · exact le_rfl

end progCells

/-! ## The trial blocks of a key -/

section blk

/-- `y` is the block of a trial of the search of key `K`. -/
def IsBlk (P : PublicParameter) (K : Key) (y : X) : Prop :=
  ∃ m : Digest, ∃ j < encodingAttemptLimit, y = cwBlk P K m j

/-- `IsBlk`, decided classically. -/
noncomputable instance instDecidableIsBlkK (P : PublicParameter) (K : Key) (y : X) :
    Decidable (IsBlk P K y) :=
  Classical.propDecidable _

theorem isBlk_unique {P : PublicParameter} {K K' : Key} {y : X} (h : IsBlk P K y)
    (h' : IsBlk P K' y) : K = K' := by
  obtain ⟨m, j, hj, rfl⟩ := h
  obtain ⟨m', j', hj', he⟩ := h'
  exact (cwBlk_inj P hj hj' he).1

/-- **The key whose value a reveal discloses among others**, the drop key of `Ψ`. -/
noncomputable def dropKey (T : Finset HPos) : Option Key :=
  match cwSingKey T with
  | some _ => none
  | none => cwDiscKey T

theorem dropKey_spec {T : Finset HPos} {K : Key} (h : dropKey T = some K) :
    HPos.val (msgPos K) ∈ T := by
  unfold dropKey at h
  rcases hs : cwSingKey T with _ | K'
  · rw [hs] at h
    exact (cwDiscKey_spec h).2
  · rw [hs] at h
    cases h

/-- The charge of a reveal is the one at its drop key. -/
theorem cwDiscCharge_eq (P : PublicParameter) (v : (s : HPos) → XD s) (T : Finset HPos)
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) :
    cwDiscCharge P v T σ = match dropKey T with
      | some K => ∑ i : Fin encodingAttemptLimit × Fin 4,
          diagMass {q : Unit × HwReg X Z (Mem HPos) | q.2 ∈ cwTD P K (valsOf v (msgPos K)) i.1} σ
      | none => 0 := by
  unfold cwDiscCharge dropKey
  rcases cwSingKey T with _ | K <;> rfl

end blk

/-! ## The potential: recorded trial blocks of keys with undisclosed values -/

section pot

variable {X₁ Z₁ M₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [Fintype M₁] [DecidableEq M₁] (B : Key → X₁ → Prop) [∀ K y, Decidable (B K y)]

/-- The keys with undisclosed values (under the memory label `T`) of which `y` is a trial block. -/
noncomputable def blkCnt (T : Finset HPos) (y : X₁) : ℝ :=
  ∑ K : Key, if HPos.val (msgPos K) ∉ T ∧ B K y then 1 else 0

/-- **The potential `Ψ`**: the recorded `k`-cells that are trial blocks of keys with undisclosed
values. -/
noncomputable def revPot (s : HwReg X₁ Z₁ (Finset HPos × M₁)) : ℝ :=
  ∑ y : X₁, if s.1.2.1 y ≠ none then blkCnt B s.2.2.1 y else 0

/-- `Ψ` with the cell `x` counted as recorded. -/
noncomputable def revPotAt (x : X₁) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) : ℝ :=
  ∑ y : X₁, if y = x then blkCnt B s.2.2.1 x else
    if s.1.2.1 y ≠ none then blkCnt B s.2.2.1 y else 0

/-- **The drop of `Ψ` at a disclosure of `K`'s value**: its recorded trial blocks. -/
noncomputable def revDrop (K : Key) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) : ℝ :=
  if HPos.val (msgPos K) ∈ s.2.2.1 then 0 else
    ((Finset.univ.filter fun y : X₁ ↦ s.1.2.1 y ≠ none ∧ B K y).card : ℝ)

/-- The drop at a reveal with drop key `o`. -/
noncomputable def revDropO (o : Option Key) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) : ℝ :=
  match o with
  | some K => revDrop B K s
  | none => 0

omit [Fintype X₁] [DecidableEq X₁] in
theorem blkCnt_nonneg (T : Finset HPos) (y : X₁) : 0 ≤ blkCnt B T y :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

omit [Fintype X₁] [DecidableEq X₁] in
theorem blkCnt_le_one (hB : ∀ {K K' y}, B K y → B K' y → K = K') (T : Finset HPos) (y : X₁) :
    blkCnt B T y ≤ 1 := by
  unfold blkCnt
  by_cases h : ∃ K, B K y
  · obtain ⟨K₀, hK₀⟩ := h
    rw [Finset.sum_eq_single K₀ (fun K _ hK ↦ ite_eq_right fun hc ↦
      hK (hB hc.2 hK₀)) (fun h ↦ absurd (Finset.mem_univ _) h)]
    split_ifs <;> norm_num
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun K _ ↦ ite_eq_right fun hc ↦ h ⟨K, hc.2⟩)
      zero_le_one

omit [Fintype X₁] [DecidableEq X₁] in
theorem blkCnt_eq_zero (hB : ∀ {K K' y}, B K y → B K' y → K = K') {T : Finset HPos}
    {K : Key} {y : X₁} (hy : B K y) (hT : HPos.val (msgPos K) ∈ T) : blkCnt B T y = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ ite_eq_right fun hc ↦ hc.1 (hB hy hc.2 ▸ hT)

omit [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem revPot_nonneg (s : HwReg X₁ Z₁ (Finset HPos × M₁)) : 0 ≤ revPot B s :=
  Finset.sum_nonneg fun y _ ↦ by
    split_ifs
    · exact blkCnt_nonneg B _ y
    · exact le_rfl

omit [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem revPot_congr {s s' : HwReg X₁ Z₁ (Finset HPos × M₁)} (hk : s'.1.2.1 = s.1.2.1)
    (hl : s'.2.2.1 = s.2.2.1) : revPot B s' = revPot B s := by
  unfold revPot
  rw [hk, hl]

omit [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem revPot_le_revPotAt (x : X₁) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) :
    revPot B s ≤ revPotAt B x s :=
  Finset.sum_le_sum fun y _ ↦ by
    by_cases hy : y = x
    · subst hy
      rw [ite_eq_left rfl]
      split_ifs
      · exact le_rfl
      · exact blkCnt_nonneg B _ y
    · rw [ite_eq_right hy]

omit [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem revPotAt_eq (hB : ∀ {K K' y}, B K y → B K' y → K = K') {x : X₁} {K : Key}
    (hx : B K x) {s : HwReg X₁ Z₁ (Finset HPos × M₁)} (hs : HPos.val (msgPos K) ∈ s.2.2.1) :
    revPotAt B x s = revPot B s :=
  Finset.sum_congr rfl fun y _ ↦ by
    by_cases hy : y = x
    · subst hy
      rw [ite_eq_left rfl, blkCnt_eq_zero B hB hx hs]
      split_ifs <;> rfl
    · rw [ite_eq_right hy]

omit [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem revPotAt_congr (x : X₁) {s s' : HwReg X₁ Z₁ (Finset HPos × M₁)}
    (hk : ∀ y, y ≠ x → s'.1.2.1 y = s.1.2.1 y) (hl : s'.2.2.1 = s.2.2.1) :
    revPotAt B x s' = revPotAt B x s :=
  Finset.sum_congr rfl fun y _ ↦ by
    rw [hl]
    by_cases hy : y = x
    · rw [ite_eq_left hy, ite_eq_left hy]
    · rw [ite_eq_right hy, ite_eq_right hy, hk y hy]

omit [Fintype Z₁] [Fintype M₁] [DecidableEq M₁] in
/-- **`Ψ` is one-cell Lipschitz** when a `k`-cell is a trial block of at most one key. -/
theorem oneCellLipschitz_revPot (hB : ∀ {K K' y}, B K y → B K' y → K = K') :
    OneCellLipschitz (revPot (Z₁ := Z₁) (M₁ := M₁) B) where
  h _ _ _ _ := le_of_eq_of_le (revPot_congr B rfl rfl) (le_add_of_nonneg_right zero_le_one)
  k' _ _ _ _ := le_of_eq_of_le (revPot_congr B rfl rfl) (le_add_of_nonneg_right zero_le_one)
  k D b x v := by
    set f : X₁ → ℝ := fun y ↦ if D.2.1 y ≠ none then blkCnt B b.2.1 y else 0
    set f' : X₁ → ℝ := fun y ↦
      if Function.update D.2.1 x v y ≠ none then blkCnt B b.2.1 y else 0
    have hd : ∑ y, (f' y - f y) = f' x - f x :=
      Finset.sum_eq_single x (fun y _ hy ↦ by simp [f, f', Function.update_of_ne hy])
        (fun h ↦ absurd (Finset.mem_univ x) h)
    have hf' : f' x ≤ 1 := by
      simp only [f']
      split_ifs
      · exact blkCnt_le_one B hB _ x
      · exact zero_le_one
    have hf : 0 ≤ f x := by
      simp only [f]
      split_ifs
      · exact blkCnt_nonneg B _ x
      · exact le_rfl
    show ∑ y, f' y ≤ ∑ y, f y + 1
    rw [Finset.sum_sub_distrib] at hd
    linarith

omit [Fintype Z₁] [Fintype M₁] [DecidableEq M₁] in
/-- **A program does not raise `Ψ`**: it discards its cell from the databases. -/
theorem revPot_progMap_le (c : HwProg X₁ Z₁) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) :
    revPot B (progMap c s) ≤ revPot B s := by
  obtain ⟨⟨dh, dk, dk'⟩, ⟨w1, w2, w3⟩, m⟩ := s
  rcases c with ⟨z, w⟩ | ⟨x, w⟩ | ⟨x, w⟩
  · exact le_of_eq (revPot_congr B rfl rfl)
  · refine Finset.sum_le_sum fun y _ ↦ ?_
    show (if Function.update dk x none y ≠ none then blkCnt B m.1 y else 0) ≤
      if dk y ≠ none then blkCnt B m.1 y else 0
    by_cases hy : y = x
    · subst hy
      rw [Function.update_self, ite_eq_right (fun h ↦ h rfl)]
      split_ifs
      · exact blkCnt_nonneg B _ y
      · exact le_rfl
    · rw [Function.update_of_ne hy]
  · exact le_of_eq (revPot_congr B rfl rfl)

/-- The register after a record of `T`. -/
def recMapS (T : Finset HPos) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) :
    HwReg X₁ Z₁ (Finset HPos × M₁) :=
  (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2))

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem blkCnt_union_le (T T' : Finset HPos) (y : X₁) : blkCnt B (T ∪ T') y ≤ blkCnt B T y :=
  Finset.sum_le_sum fun K _ ↦ by
    by_cases h : HPos.val (msgPos K) ∉ T ∪ T' ∧ B K y
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl ↦ h.1 (Finset.mem_union_left _ hl), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
/-- At one cell: the drop of `K` and the count after recording a set disclosing `K`'s value. -/
theorem ind_add_blkCnt_le {T T' : Finset HPos} {K : Key} (hK : HPos.val (msgPos K) ∉ T)
    (hK' : HPos.val (msgPos K) ∈ T') (y : X₁) :
    (if B K y then (1 : ℝ) else 0) + blkCnt B (T ∪ T') y ≤ blkCnt B T y := by
  unfold blkCnt
  have h1 : (if B K y then (1 : ℝ) else 0) =
      ∑ K' : Key, if K' = K then (if HPos.val (msgPos K') ∉ T ∧ B K' y then 1 else 0) else 0 := by
    rw [Finset.sum_ite_eq' Finset.univ K, ite_eq_left (Finset.mem_univ _)]
    by_cases hb : B K y
    · rw [ite_eq_left hb, ite_eq_left ⟨hK, hb⟩]
    · rw [ite_eq_right hb, ite_eq_right fun h ↦ hb h.2]
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun K' _ ↦ ?_
  by_cases hl : K' = K
  · subst hl
    have h0 : ¬(HPos.val (msgPos K') ∉ T ∪ T' ∧ B K' y) :=
      fun h ↦ h.1 (Finset.mem_union_right _ hK')
    rw [ite_eq_left rfl, ite_eq_right h0, add_zero]
  · rw [ite_eq_right hl, zero_add]
    by_cases h : HPos.val (msgPos K') ∉ T ∪ T' ∧ B K' y
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl' ↦ h.1 (Finset.mem_union_left _ hl'), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

omit [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
/-- **A record drops `Ψ` by at least the drop of its drop key.** -/
theorem revDropO_add_le (T : Finset HPos) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) :
    revDropO B (dropKey T) s + revPot B (recMapS T s) ≤ revPot B s := by
  obtain ⟨⟨dh, dk, dk'⟩, W, ⟨L, m⟩⟩ := s
  have hle : revPot B (recMapS T ((dh, dk, dk'), W, (L, m))) ≤
      revPot B ((dh, dk, dk'), W, (L, m)) :=
    Finset.sum_le_sum fun y _ ↦ by
      show (if dk y ≠ none then blkCnt B (L ∪ T) y else 0) ≤
        if dk y ≠ none then blkCnt B L y else 0
      split_ifs
      · exact blkCnt_union_le B L T y
      · exact le_rfl
  cases ho : dropKey T with
  | none =>
    show 0 + _ ≤ _
    rw [zero_add]
    exact hle
  | some K =>
    show revDrop B K ((dh, dk, dk'), W, (L, m)) + _ ≤ _
    unfold revDrop
    split_ifs with hK
    · rw [zero_add]
      exact hle
    · have hT := dropKey_spec ho
      show ((Finset.univ.filter fun y : X₁ ↦ dk y ≠ none ∧ B K y).card : ℝ) +
        ∑ y : X₁, (if dk y ≠ none then blkCnt B (L ∪ T) y else 0) ≤
          ∑ y : X₁, if dk y ≠ none then blkCnt B L y else 0
      rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun y _ ↦ ?_
      by_cases hD : dk y ≠ none
      · rw [ite_eq_left hD, ite_eq_left hD]
        have h := ind_add_blkCnt_le B hK hT y
        by_cases hb : B K y
        · rw [ite_eq_left hb] at h
          rw [ite_eq_left ⟨hD, hb⟩, Nat.cast_one]
          exact h
        · rw [ite_eq_right hb] at h
          rw [ite_eq_right fun h' ↦ hb h'.2, Nat.cast_zero]
          exact h
      · rw [ite_eq_right hD, ite_eq_right hD, ite_eq_right fun h ↦ hD h.1, Nat.cast_zero,
          zero_add]

end pot

/-! ## Diagonal potentials at the record ports -/

section steps

variable {X₁ Z₁ M₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [Fintype M₁] [DecidableEq M₁]

omit [Fintype M₁] in
theorem recKraus_apply_eqS (T : Finset HPos) (m : Finset HPos × M₁)
    (t s : Unit × HwReg X₁ Z₁ (Finset HPos × M₁)) :
    recKraus (X := X₁) (Z := Z₁) T m t s =
      if m = s.2.2.2 ∧ t = ((), recMapS T s.2) then 1 else 0 := by
  obtain ⟨⟨⟩, D', W', m'⟩ := t
  obtain ⟨⟨⟩, D, W, mm⟩ := s
  simp only [recKraus, kroneckerMap_apply, Matrix.one_apply_eq, one_mul, clsKraus_apply,
    Matrix.one_apply, recMapS, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- **A record port on a diagonal potential**: the weights after it are those of the recorded
states. -/
theorem tsum_potential_rec_eqS {φ : HwReg X₁ Z₁ (Finset HPos × M₁) → ℝ} (hφ0 : ∀ s, 0 ≤ φ s)
    (T : Finset HPos)
    {σ : Matrix (Unit × HwReg X₁ Z₁ (Finset HPos × M₁)) (Unit × HwReg X₁ Z₁ (Finset HPos × M₁)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' m, potential (diagPot fun s ↦ √(φ s))
        (MatrixMap.conj (recKraus (X := X₁) (Z := Z₁) T m) σ) =
      ENNReal.ofReal (∑ q, φ (recMapS T q.2) * (σ q q).re) := by
  have hpost : ∀ m, 0 ≤ dW (fun q : Unit × HwReg X₁ Z₁ (Finset HPos × M₁) ↦ φ q.2)
      (MatrixMap.conj (recKraus (X := X₁) (Z := Z₁) T m) σ) := fun m ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  have hpot : ∀ τ : Matrix (Unit × HwReg X₁ Z₁ (Finset HPos × M₁))
      (Unit × HwReg X₁ Z₁ (Finset HPos × M₁)) ℂ,
      potential (diagPot fun s ↦ √(φ s)) τ = ENNReal.ofReal (dW (fun q ↦ φ q.2) τ) :=
    fun τ ↦ potential_diagPot_sqrt hφ0 τ
  have hinj : ∀ q q' : Unit × HwReg X₁ Z₁ (Finset HPos × M₁), q.2.2.2 = q'.2.2.2 →
      ((), recMapS T q.2) = ((), recMapS T q'.2) → q = q' := fun q q' hi hf ↦
    Prod.ext (Subsingleton.elim _ _) (Prod.ext (congrArg (fun t ↦ t.2.1) hf)
      (Prod.ext (congrArg (fun t ↦ t.2.2.1) hf) hi))
  simp only [hpot]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun m _ ↦ hpost m, sum_dW_conj,
    gram_classical_diag (recKraus (X := X₁) (Z := Z₁) T) (fun q ↦ q.2.2.2)
      (fun q ↦ ((), recMapS T q.2)) (recKraus_apply_eqS T) hinj, re_trace_diagonal_mul]

end steps

/-! ## The label invariant of the searches and `Ψ` along the prefix -/

section labRun

/-- **The label invariant of the search modes**: in the search of `K`, its value is disclosed. -/
def labInv : CwMode → Set (HwReg X Z (Mem HPos))
  | .grd K _ _ => {s | HPos.val (msgPos K) ∈ s.2.2.1}
  | .afK K _ _ _ => {s | HPos.val (msgPos K) ∈ s.2.2.1}
  | .afK' K _ _ _ _ => {s | HPos.val (msgPos K) ∈ s.2.2.1}
  | _ => Set.univ

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter)

/-- **The allowed calls keep the label invariant**: the reveal starting a search records its key's
value, the searches' reads keep the memory label. -/
theorem labInv_step (v : (s : HPos) → XD s) (μ : CwMode)
    (i : (recHwSpec X Z HPos Selections).Port) (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ)
    (hok : cwOkZ π P (cwLiftHu cwUpd) μ i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2) (labInv μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2) (labInv (cwNxZ π P v μ i r))
        (((runtimeR m0R).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · exact querySupportedOn_univ _ _
  · have hb : ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    rw [hb]
    rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;>
      rcases μ with _ | ⟨K, m⟩ | ⟨K, m, j⟩ | ⟨K, m, j, a⟩ | ⟨K, m, j, xi, z'⟩
    all_goals try exact hok.elim
    · obtain ⟨rfl, rfl⟩ := hok
      refine hσ.conj fun q' q hK hq ↦ ?_
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := q.1) (a' := q'.1) (b := q.2) (b' := q'.2) hK
      obtain ⟨-, -, h3, h4⟩ := cw_readKrausH_ne_zero _ _ r hK'
      have hl : q'.2.2.2.1 = q.2.2.2.1 := by rw [h4, h3]; rfl
      show HPos.val (msgPos K) ∈ q'.2.2.2.1
      rw [hl]
      exact hq
    · obtain ⟨-, rfl, rfl⟩ := hok
      refine hσ.conj fun q' q hK hq ↦ ?_
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := q.1) (a' := q'.1) (b := q.2) (b' := q'.2) hK
      obtain ⟨-, -, -, -, h5, h6⟩ := cw_readKrausK_ne_zero _ _ r hK'
      have hl : q'.2.2.2.1 = q.2.2.2.1 := by rw [h6, h5]
      show HPos.val (msgPos K) ∈ q'.2.2.2.1
      rw [hl]
      exact hq
    · obtain ⟨rfl, rfl⟩ := hok
      refine hσ.conj fun q' q hK hq ↦ ?_
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := q.1) (a' := q'.1) (b := q.2) (b' := q'.2) hK
      obtain ⟨-, -, -, h4, h5⟩ := cw_readKrausK'_ne_zero _ _ r hK'
      have hl : q'.2.2.2.1 = q.2.2.2.1 := by rw [h5, h4]
      show HPos.val (msgPos K) ∈ q'.2.2.2.1
      rw [hl]
      exact hq
  · show QuerySupportedOn _ (labInv (cwProgNx μ)) _
    rcases μ with _ | ⟨K, m⟩ | _ | _ | _ <;> exact querySupportedOn_univ _ _
  · show QuerySupportedOn _ (labInv (cwRevNx μ T (valsOf v))) _
    unfold cwRevNx
    rcases hs : cwSingKey T with _ | K
    · dsimp only
      rcases cwDiscKey T with _ | K <;> exact querySupportedOn_univ _ _
    · dsimp only
      rcases μ with _ | ⟨K', m'⟩ | _ | _ | _
      all_goals try exact querySupportedOn_univ _ _
      dsimp only
      split_ifs with hK
      · have hT : T = {HPos.val (msgPos K)} := (cwSingKey_spec hs).2
        refine QuerySupportedOn.conj (K := recKraus (X := X) (Z := Z) T r) hσ fun q' q hK _ ↦ ?_
        rw [eq_of_recKraus_ne_zero (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK]
        show HPos.val (msgPos K) ∈ q.2.2.2.1 ∪ T
        rw [hT]
        exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      · exact querySupportedOn_univ _ _

/-- The drops of `Ψ` at the record ports. -/
noncomputable def revDropW :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ → ℝ≥0∞
  | .inr T, σ => ENNReal.ofReal (∑ q, revDropO (IsBlk P) (dropKey T) q.2 * (σ q q).re)
  | _, _ => 0

/-- The traces at the sponge ports. -/
noncomputable def spongeTrW (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ) : ℝ≥0∞ :=
  ((if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1 : ℕ) : ℝ≥0∞) *
    ENNReal.ofReal σ.trace.re

theorem revDropO_nonneg (o : Option Key) (s : HwReg X Z (Mem HPos)) :
    0 ≤ revDropO (IsBlk P) o s := by
  cases o with
  | none => exact le_rfl
  | some K =>
    show 0 ≤ revDrop (IsBlk P) K s
    unfold revDrop
    split_ifs
    · exact le_rfl
    · exact Nat.cast_nonneg _

/-- **The step of `Ψ`**: a sponge call raises it by at most its trace; a search's read, a program
and a record do not raise it, a record lowering it by the drop of its drop key. -/
theorem revPot_step (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ)
    (hσ : σ.PosSemidef)
    (hI : ∃ μ, cwOkZ π P (cwLiftHu cwUpd) μ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
        (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2) (labInv μ) σ) :
    revDropW P i σ + ∑' r, potential (diagPot fun s ↦ √(revPot (IsBlk P) s))
        (((runtimeR m0R).step i).branch r σ) ≤
      potential (diagPot fun s ↦ √(revPot (IsBlk P) s)) σ + spongeTrW i σ := by
  have hφ0 := revPot_nonneg (Z₁ := Z) (M₁ := Selections) (IsBlk P)
  rcases i with ((p | c) | c) | T
  · have hb : ∀ r : Unit, ((runtimeR m0R).step (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m0R).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m0R p r) σ
    have hc : spongeTrW (.inl (.inl (.inl p))) σ = ENNReal.ofReal σ.trace.re := by
      simp [spongeTrW, extCls, hwCls]
      rfl
    rw [hc]
    show 0 + _ ≤ _
    rw [zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans
      (tsum_potential_sponge_le hφ0 (oneCellLipschitz_revPot (IsBlk P) isBlk_unique)
        (hwEmpty X Z) m0R p hσ)
  · obtain ⟨μ, hok, hs⟩ := hI
    have hb : ∀ r, ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    have hc : spongeTrW (.inl (.inl (.inr c))) σ = 0 := by
      simp [spongeTrW, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    show ∑' r : c.Result, potential (diagPot fun s ↦ √(revPot (IsBlk P) s))
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ _
    rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;>
      rcases μ with _ | ⟨K, m⟩ | ⟨K, m, j⟩ | ⟨K, m, j, a⟩ | ⟨K, m, j, xi, z'⟩
    all_goals try exact hok.elim
    · obtain ⟨rfl, rfl⟩ := hok
      refine tsum_potential_le_of_keep _ (sum_hwReadKraus _) hφ0 (fun _ ↦ le_rfl)
        (fun r a a' h ↦ ?_) hσ (fun _ _ ↦ rfl)
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
      obtain ⟨h1, -, h3, h4⟩ := cw_readKrausH_ne_zero _ _ r hK'
      exact revPot_congr (IsBlk P) (congrArg Prod.fst h1) (by rw [h4, h3]; rfl)
    · obtain ⟨hj, rfl, rfl⟩ := hok
      have hx : IsBlk P K (cwBlk P K m j) := ⟨m, j, hj, rfl⟩
      refine tsum_potential_le_of_keep _ (sum_hwReadKraus _) hφ0
        (revPot_le_revPotAt (IsBlk P) (cwBlk P K m j)) (fun r a a' h ↦ ?_) hσ
        (fun q hq ↦ (revPotAt_eq (IsBlk P) isBlk_unique hx (hs q q hq).1).symm)
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
      obtain ⟨-, -, h3, -, h5, h6⟩ := cw_readKrausK_ne_zero _ _ r hK'
      exact revPotAt_congr (IsBlk P) _ h3 (by rw [h6, h5])
    · obtain ⟨rfl, rfl⟩ := hok
      refine tsum_potential_le_of_keep _ (sum_hwReadKraus _) hφ0 (fun _ ↦ le_rfl)
        (fun r a a' h ↦ ?_) hσ (fun _ _ ↦ rfl)
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
      obtain ⟨-, h2, -, h4, h5⟩ := cw_readKrausK'_ne_zero _ _ r hK'
      exact revPot_congr (IsBlk P) h2 (by rw [h5, h4])
  · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m0R c r) σ
    have hc : spongeTrW (.inl (.inr c)) σ = 0 := by
      simp [spongeTrW, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    refine (le_of_eq (tsum_potential_prog_eq hφ0 c hσ)).trans ?_
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ ?_)
    exact mul_le_mul_of_nonneg_right (revPot_progMap_le (IsBlk P) c q.2)
      (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  · have hc : spongeTrW (.inr T) σ = 0 := by
      simp [spongeTrW, extCls]
    rw [hc, add_zero]
    show ENNReal.ofReal (∑ q, revDropO (IsBlk P) (dropKey T) q.2 * (σ q q).re) +
      ∑' m, potential (diagPot fun s ↦ √(revPot (IsBlk P) s))
        (MatrixMap.conj (recKraus (X := X) (Z := Z) T m) σ) ≤ _
    rw [tsum_potential_rec_eqS hφ0 T hσ]
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    have h1 : 0 ≤ ∑ q, revDropO (IsBlk P) (dropKey T) q.2 * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (revDropO_nonneg P _ _) (hre q)
    have h2 : 0 ≤ ∑ q, revPot (IsBlk P) (recMapS T q.2) * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 _) (hre q)
    refine (ENNReal.ofReal_add h1 h2).symm.trans_le (ENNReal.ofReal_le_ofReal ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (revDropO_add_le (IsBlk P) T q.2) (hre q)

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The drops of `Ψ` along the challenge prefix**: at most `6q`, the sponge calls (the potential
starts at `0`). -/
theorem totalWeight_revDropW_le (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    (runtimeR m0R).totalWeight .instruments (revDropW p.seed) (prefixR pol A p v) initR ≤
      6 * q := by
  set x := prefixR pol A p v
  have hφ0 := revPot_nonneg (Z₁ := Z) (M₁ := Selections) (IsBlk p.seed)
  have hx := forallQueries_of_modedP (runtimeR m0R) .instruments labInv
    (fun μ i r σ hok h ↦ labInv_step p.perm p.seed v μ i r σ hok h) x .free
    (modedP_prefixR' cwUpd pol p A v) (ρ := initR) (querySupportedOn_univ _ _)
  have h := totalWeight_le_potential_of_forallQueries (runtimeR m0R) .instruments
    (diagPot fun s ↦ √(revPot (IsBlk p.seed) s)) _
    (fun i σ ↦ ∃ μ, cwOkZ p.perm p.seed (cwLiftHu cwUpd) μ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
        (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2) (labInv μ) σ)
    (fun i E σ hP ↦ by
      obtain ⟨μ, hok, hs⟩ := hP
      exact ⟨μ, hok, querySupportedOn_traceRight hs⟩)
    (revDropW p.seed) spongeTrW
    (fun i σ hσ hI ↦ revPot_step p.perm p.seed i σ hσ hI) x initR_posSemidef hx
  have h0 : potential (diagPot fun s ↦ √(revPot (IsBlk p.seed) s)) initR = 0 := by
    unfold initR
    rw [potential_basis_init m0R hφ0 ()]
    refine (congrArg ENNReal.ofReal (Finset.sum_eq_zero fun y _ ↦ ite_eq_right fun h ↦
      h rfl)).trans ENNReal.ofReal_zero
  refine h.trans ((add_le_add (le_of_eq h0) le_rfl).trans ?_)
  rw [zero_add]
  refine (totalWeight_chargeTrace_le (runtimeR m0R) .instruments _ x
    (advCalls_prefixR hperm hsign pol p v) initR_posSemidef).trans ?_
  calc ((6 * q : ℕ) : ℝ≥0∞) * ENNReal.ofReal initR.trace.re ≤ (6 * q : ℕ) * 1 := by
        gcongr
        exact ofReal_trace_initR_le_one
    _ = 6 * q := by rw [mul_one]; push_cast; ring

end labRun

/-! ## The first disclosures: Disclose's view lemma against `Ψ` -/

section first

variable (P : PublicParameter)

/-- At a disclosure of `K`'s value `m`: the value undisclosed, the block of trial `j` recorded. -/
def FirstRec (K : Key) (m : Digest) (j : ℕ) (s : HwReg X Z (Mem HPos)) : Prop :=
  HPos.val (msgPos K) ∉ s.2.2.1 ∧ s.1.2.1 (cwBlk P K m j) ≠ none

/-- At a disclosure of `K`'s value `m`: the value undisclosed, the block of trial `j` hardwired,
the key unselected. -/
def FirstHw (K : Key) (m : Digest) (j : ℕ) (s : HwReg X Z (Mem HPos)) : Prop :=
  HPos.val (msgPos K) ∉ s.2.2.1 ∧ s.2.1.2.1 (cwBlk P K m j) ≠ none ∧ cwU K s.2.2

/-- At a disclosure of `K`'s value: the value already disclosed (its search ran before) and the
key unselected. -/
def ReRev (K : Key) (s : HwReg X Z (Mem HPos)) : Prop :=
  HPos.val (msgPos K) ∈ s.2.2.1 ∧ cwU K s.2.2

/-- The first-disclosure states of trial `j` at a reveal with drop key `o`. -/
def firstSetO (v : (s : HPos) → XD s) (j : ℕ) (o : Option Key) :
    Set (Unit × HwReg X Z (Mem HPos)) :=
  match o with
  | some K => {q | FirstRec P K (valsOf v (msgPos K)) j q.2}
  | none => ∅

/-- The first-disclosure states of trial `j` at the reveals. -/
def firstSet (v : (s : HPos) → XD s) (j : ℕ) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Set ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
  | .inr T => firstSetO P v j (dropKey T)
  | _ => ∅

/-- The values whose trial-`j` block of `K` is recorded at `s`. -/
noncomputable def firstF (j : ℕ) (K : Key) (s : HwReg X Z (Mem HPos)) : Finset Digest :=
  Finset.univ.filter fun m : Digest ↦ s.1.2.1 (cwBlk P K m j) ≠ none

/-- The source of a reveal with drop key `o`: `K`'s value, if undisclosed. -/
def firstSrcO (o : Option Key) (q : Unit × HwReg X Z (Mem HPos)) : Finset HPos :=
  match o with
  | some K => if HPos.val (msgPos K) ∈ q.2.2.2.1 then ∅ else {HPos.val (msgPos K)}
  | none => ∅

/-- The sources at the reveals. -/
noncomputable def firstSrc : ∀ i : (recHwSpec X Z HPos Selections).Port,
    (recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)) → Finset HPos
  | .inr T, q => firstSrcO (dropKey T) q
  | _, _ => ∅

/-- A set of digests as values of a value coordinate (empty at the other coordinates). -/
def valFin : (s : HPos) → Finset Digest → Finset (XD s)
  | .val _, F => F
  | _, _ => ∅

/-- The source values of a reveal with drop key `o`. -/
noncomputable def firstFO (j : ℕ) (o : Option Key) (q : Unit × HwReg X Z (Mem HPos)) :
    Finset Digest :=
  match o with
  | some K => firstF P j K q.2
  | none => ∅

/-- The source values at the reveals. -/
noncomputable def firstFv (j : ℕ) : ∀ i : (recHwSpec X Z HPos Selections).Port,
    (recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)) → (s : HPos) →
      ((s : HPos) → XD s) → Finset (XD s)
  | .inr T, q => fun s _ ↦ valFin s (firstFO P j (dropKey T) q)
  | _, _ => fun _ _ ↦ ∅

/-- The weight per state of a reveal with drop key `o`. -/
noncomputable def firstKO (j : ℕ) (o : Option Key) (q : Unit × HwReg X Z (Mem HPos)) : ℝ≥0∞ :=
  ∑ s ∈ firstSrcO o q, ((valFin s (firstFO P j o q)).card : ℝ≥0∞) *
    (Fintype.card (XD s) : ℝ≥0∞)⁻¹

/-- The weights per state at the reveals. -/
noncomputable def firstK (j : ℕ) : ∀ i : (recHwSpec X Z HPos Selections).Port,
    (recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)) → ℝ≥0∞
  | .inr T, q => firstKO P j (dropKey T) q
  | _, _ => 0

/-- **The view lemma at the first disclosures, trial by trial**: the first-disclosure masses of
trial `j`, summed over the hidden values, are at most the weights `firstK` (`K`'s undisclosed
value is the source). -/
theorem sum_totalWeight_firstSet_le (pol : DigestPolicy) (pub : Pub) (A : SAdversary) (j : ℕ) :
    ∑ v : (s : HPos) → XD s, (runtimeR m0R).totalWeight .instruments
        (fun i ↦ diagMass (firstSet pub.seed v j i)) (prefixR pol A pub v) initR ≤
      ∑ v : (s : HPos) → XD s, (runtimeR m0R).totalWeight .instruments
        (fun i ↦ kWt (firstK pub.seed j i)) (prefixR pol A pub v) initR := by
  have h := sum_totalWeight_le_of_forall (runtimeR m0R) LocalSig.Interp.instruments
    (fun v i ↦ diagMass (firstSet pub.seed v j i)) (fun i ↦ kWt (firstK pub.seed j i))
    (fun v ↦ prefixR pol A pub v) (fun _ ↦ initR) 1 fun n ↦ by
      rw [one_mul]
      refine sum_queryWeight_view_le_wt (runtimeR m0R) LocalSig.Interp.instruments
        (fun r ↦ r.2.2.1) (fun v ↦ prefixR pol A pub v) (fun _ ↦ initR)
        (fun _ ↦ initR_posSemidef) n (fun _ ↦ True)
        ((viewBy_runtimeR_of_disc LocalSig.Interp.instruments m0R
          (prefixT Selections cwUpd pol pub A) ∅ (disc_prefixT Selections cwUpd pol pub A ∅)
          (fun _ ↦ initR) (lazy_const _ initR) (fun _ ↦ suppAt_empty _ initR) n).viewByOn
          fun _ ↦ True)
        (fun v ↦ firstSet pub.seed v j) (fun _ _ h ↦ absurd trivial h) firstSrc
        (firstFv pub.seed j) (fun i p s v d ↦ ?_) (fun v i p hp ↦ ?_) (firstK pub.seed j)
        (fun i p v ↦ ?_)
      · rcases i with ((i | c) | c) | T <;> rfl
      · rcases i with ((i | c) | c) | T
        · exact hp.elim
        · exact hp.elim
        · exact hp.elim
        · have hp' : p ∈ firstSetO pub.seed v j (dropKey T) := hp
          show ∃ s ∈ firstSrcO (dropKey T) p, s ∉ p.2.2.2.1 ∧
            v s ∈ valFin s (firstFO pub.seed j (dropKey T) p)
          revert hp'
          cases dropKey T with
          | none => exact fun hp' ↦ hp'.elim
          | some K =>
            intro hp'
            refine ⟨HPos.val (msgPos K), ?_, hp'.1, mem_filter_univ_of hp'.2⟩
            show HPos.val (msgPos K) ∈
              (if HPos.val (msgPos K) ∈ p.2.2.2.1 then ∅ else {HPos.val (msgPos K)})
            rw [ite_eq_right hp'.1]
            exact Finset.mem_singleton_self _
      · rcases i with ((i | c) | c) | T
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · exact le_rfl
  rwa [one_mul] at h

/-- The constant of the first disclosures: four copies per recorded trial block, over
`|Digest|`. -/
noncomputable def revFirstC : ℝ≥0∞ :=
  4 * (Fintype.card Digest : ℝ≥0∞)⁻¹

/-- **The first-disclosure constant at Keccak's sizes**: `4 / 2^128 = 2^-126`, so the first
disclosures cost `6q · 2^-126 = 24q · 2^-128`. -/
theorem revFirstC_eq : revFirstC = ((2 : ℝ≥0∞) ^ 126)⁻¹ := by
  have h128 : (2 : ℝ≥0∞) ^ 128 = 4 * 2 ^ 126 := by norm_num
  rw [revFirstC, card_digest_inv, h128,
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- **All the values and counters whose trial blocks of `K` are recorded inject into the recorded
trial blocks** (the counter is public). -/
theorem sum_card_firstF_le (K : Key) (s : HwReg X Z (Mem HPos)) :
    ∑ j : Fin encodingAttemptLimit, (firstF P j K s).card ≤
      (Finset.univ.filter fun y : X ↦ s.1.2.1 y ≠ none ∧ IsBlk P K y).card := by
  classical
  have he : ∑ j : Fin encodingAttemptLimit, (firstF P j K s).card =
      (Finset.univ.filter fun jm : Fin encodingAttemptLimit × Digest ↦
        s.1.2.1 (cwBlk P K jm.2 jm.1) ≠ none).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [firstF, Finset.card_filter]
  rw [he]
  refine card_filter_le_of_injective (f := fun jm : Fin encodingAttemptLimit × Digest ↦
    cwBlk P K jm.2 jm.1) (fun jm jm' h ↦ ?_) _ _ fun jm h ↦ ⟨h, jm.2, jm.1, jm.1.isLt, rfl⟩
  obtain ⟨-, hm, hj⟩ := cwBlk_inj P jm.1.isLt jm'.1.isLt h
  exact Prod.ext (Fin.ext hj) hm

theorem card_XD_val (p : ValPos) : Fintype.card (XD (.val p)) = Fintype.card Digest :=
  rfl

omit P in
/-- Four copies of a sum of naturals with a common factor. -/
theorem sum_prod_four_le {ι : Type} [Fintype ι] (f : ι → ℕ) (c : ℝ≥0∞) {n : ℕ}
    (h : ∑ j, f j ≤ n) : ∑ J : ι × Fin 4, (f J.1 : ℝ≥0∞) * c ≤ 4 * c * n := by
  calc ∑ J : ι × Fin 4, (f J.1 : ℝ≥0∞) * c = ∑ j, ∑ _b : Fin 4, (f j : ℝ≥0∞) * c :=
        Fintype.sum_prod_type' (f := fun j (_ : Fin 4) ↦ (f j : ℝ≥0∞) * c)
    _ = ∑ j, 4 * ((f j : ℝ≥0∞) * c) := Finset.sum_congr rfl fun j _ ↦ by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
    _ = 4 * c * ((∑ j, f j : ℕ) : ℝ≥0∞) := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, Nat.cast_sum]
        ring
    _ ≤ 4 * c * n := by gcongr

/-- **The weights of the trials at a reveal against the drop of `Ψ`.** -/
theorem sum_firstK_le (T : Finset HPos) (q : Unit × HwReg X Z (Mem HPos)) :
    ∑ J : Fin encodingAttemptLimit × Fin 4, firstKO P J.1 (dropKey T) q ≤
      revFirstC * ENNReal.ofReal (revDropO (IsBlk P) (dropKey T) q.2) := by
  cases dropKey T with
  | none => exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_empty) zero_le
  | some K =>
    by_cases hl : HPos.val (msgPos K) ∈ q.2.2.2.1
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun J _ ↦ ?_) zero_le
      show ∑ s ∈ (if HPos.val (msgPos K) ∈ q.2.2.2.1 then ∅ else {HPos.val (msgPos K)}), _ = 0
      rw [ite_eq_left hl, Finset.sum_empty]
    · have hd : revDropO (IsBlk P) (some K) q.2 =
          ((Finset.univ.filter fun y : X ↦ q.2.1.2.1 y ≠ none ∧ IsBlk P K y).card : ℝ) := by
        show revDrop (IsBlk P) K q.2 = _
        unfold revDrop
        rw [ite_eq_right hl]
      have hK : ∀ J : Fin encodingAttemptLimit × Fin 4, firstKO P J.1 (some K) q =
          ((firstF P J.1 K q.2).card : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := fun J ↦ by
        show ∑ s ∈ (if HPos.val (msgPos K) ∈ q.2.2.2.1 then ∅ else {HPos.val (msgPos K)}), _ = _
        rw [ite_eq_right hl, Finset.sum_singleton, card_XD_val]
        rfl
      rw [hd, ENNReal.ofReal_natCast]
      simp only [hK]
      have h4 := sum_prod_four_le (fun j : Fin encodingAttemptLimit ↦ (firstF P j K q.2).card)
        (Fintype.card Digest : ℝ≥0∞)⁻¹ (sum_card_firstF_le P K q.2)
      unfold revFirstC
      exact h4

/-- The first-disclosure charges: four times each trial whose block is recorded at a first
disclosure. -/
noncomputable def firstW (v : (s : HPos) → XD s) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ) : ℝ≥0∞ :=
  ∑ J : Fin encodingAttemptLimit × Fin 4, diagMass (firstSet P v J.1 i) σ

theorem sum_kWt_firstK_le (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ)
    (hσ : σ.PosSemidef) :
    ∑ J : Fin encodingAttemptLimit × Fin 4, kWt (firstK P J.1 i) σ ≤
      revFirstC * revDropW P i σ := by
  rcases i with ((i | c) | c) | T
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦
      zero_mul _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦
      zero_mul _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦
      zero_mul _) zero_le
  · have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    show ∑ J : Fin encodingAttemptLimit × Fin 4, ∑ q, firstKO P J.1 (dropKey T) q *
        ENNReal.ofReal (σ q q).re ≤
      revFirstC * ENNReal.ofReal (∑ q, revDropO (IsBlk P) (dropKey T) q.2 * (σ q q).re)
    rw [Finset.sum_comm, ENNReal.ofReal_sum_of_nonneg fun q _ ↦
      mul_nonneg (revDropO_nonneg P _ _) (hre q), Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← Finset.sum_mul, ENNReal.ofReal_mul (revDropO_nonneg P _ _), ← mul_assoc]
    exact mul_le_mul' (sum_firstK_le P T q) le_rfl

theorem totalWeight_firstW_eq {Ω : QReg → Type} (v : (s : HPos) → XD s)
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)))
      (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos))) ℂ) :
    (runtimeR m0R).totalWeight .instruments (firstW P v) x ρ =
      ∑ J : Fin encodingAttemptLimit × Fin 4,
        (runtimeR m0R).totalWeight .instruments (fun i ↦ diagMass (firstSet P v J.1 i)) x ρ :=
  totalWeight_fintype_sum (runtimeR m0R) .instruments
    (fun (J : Fin encodingAttemptLimit × Fin 4) i ↦ diagMass (firstSet P v J.1 i)) x ρ

theorem sum_totalWeight_kWt_le {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    {ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)))
      (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos))) ℂ} (hρ : ρ.PosSemidef) :
    ∑ J : Fin encodingAttemptLimit × Fin 4,
        (runtimeR m0R).totalWeight .instruments (fun i ↦ kWt (firstK P J.1 i)) x ρ ≤
      revFirstC * (runtimeR m0R).totalWeight .instruments (revDropW P) x ρ := by
  rw [← totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun (J : Fin encodingAttemptLimit × Fin 4) i ↦ kWt (firstK P J.1 i)) x ρ,
    ← totalWeight_const_mul_weight (runtimeR m0R) .instruments revFirstC (revDropW P) x ρ]
  exact totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (fun i σ hσ ↦ sum_kWt_firstK_le P i σ hσ) x hρ

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The first-disclosure charges**: summed over the hidden values, at most `revFirstC · 6q` per
hidden value (`4 · 6q / 2^128 = 24q · 2^-128`). -/
theorem sum_totalWeight_firstW_le (pol : DigestPolicy) (pub : Pub) :
    ∑ v : (s : HPos) → XD s, (runtimeR m0R).totalWeight .instruments (firstW pub.seed v)
        (prefixR pol A pub v) initR ≤
      revFirstC * (6 * q) * Fintype.card ((s : HPos) → XD s) := by
  calc ∑ v : (s : HPos) → XD s, (runtimeR m0R).totalWeight .instruments (firstW pub.seed v)
        (prefixR pol A pub v) initR
      = ∑ v : (s : HPos) → XD s, ∑ J : Fin encodingAttemptLimit × Fin 4,
          (runtimeR m0R).totalWeight .instruments
            (fun i ↦ diagMass (firstSet pub.seed v J.1 i)) (prefixR pol A pub v) initR :=
        Finset.sum_congr rfl fun v _ ↦ totalWeight_firstW_eq pub.seed v _ initR
    _ = ∑ J : Fin encodingAttemptLimit × Fin 4, ∑ v : (s : HPos) → XD s,
          (runtimeR m0R).totalWeight .instruments
            (fun i ↦ diagMass (firstSet pub.seed v J.1 i)) (prefixR pol A pub v) initR :=
        Finset.sum_comm
    _ ≤ ∑ J : Fin encodingAttemptLimit × Fin 4, ∑ v : (s : HPos) → XD s,
          (runtimeR m0R).totalWeight .instruments (fun i ↦ kWt (firstK pub.seed J.1 i))
            (prefixR pol A pub v) initR :=
        Finset.sum_le_sum fun J _ ↦ sum_totalWeight_firstSet_le pol pub A J.1
    _ = ∑ v : (s : HPos) → XD s, ∑ J : Fin encodingAttemptLimit × Fin 4,
          (runtimeR m0R).totalWeight .instruments (fun i ↦ kWt (firstK pub.seed J.1 i))
            (prefixR pol A pub v) initR := Finset.sum_comm
    _ ≤ ∑ v : (s : HPos) → XD s, revFirstC * (runtimeR m0R).totalWeight .instruments
          (revDropW pub.seed) (prefixR pol A pub v) initR :=
        Finset.sum_le_sum fun v _ ↦ sum_totalWeight_kWt_le pub.seed _ initR_posSemidef
    _ ≤ ∑ _v : (s : HPos) → XD s, revFirstC * (6 * q) :=
        Finset.sum_le_sum fun v _ ↦
          mul_le_mul' le_rfl (totalWeight_revDropW_le hperm hsign pol pub v)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end first

/-! ## The reveal charges: first disclosures, hardwired blocks, repeated disclosures -/

section assemble

variable (P : PublicParameter)

/-- The hardwired first-disclosure charge of a reveal with drop key `o`. -/
noncomputable def hwRevO (v : (s : HPos) → XD s) (o : Option Key)
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  match o with
  | some K => ∑ J : Fin encodingAttemptLimit × Fin 4,
      diagMass {q : Unit × HwReg X Z (Mem HPos) | FirstHw P K (valsOf v (msgPos K)) J.1 q.2} σ
  | none => 0

/-- **The hardwired first-disclosure charges.** -/
noncomputable def hwRevW (v : (s : HPos) → XD s) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ → ℝ≥0∞
  | .inr T, σ => hwRevO P v (dropKey T) σ
  | _, _ => 0

/-- The repeated-disclosure mass of a reveal with drop key `o`. -/
noncomputable def reRevO (o : Option Key)
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  match o with
  | some K => diagMass {q : Unit × HwReg X Z (Mem HPos) | ReRev K q.2} σ
  | none => 0

/-- **The repeated-disclosure masses**: at a reveal disclosing a value already disclosed, the mass
with its key unselected (the earlier search failed). -/
noncomputable def reRevW :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ → ℝ≥0∞
  | .inr T, σ => reRevO (dropKey T) σ
  | _, _ => 0

/-- **The split of a reveal charge** by the label at the reveal: first disclosures (block recorded
or hardwired) and repeated disclosures, the latter `4 · 2^32` times their mass. -/
theorem cwRevW_le (v : (s : HPos) → XD s) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ) :
    cwRevW P v i σ ≤ firstW P v i σ + hwRevW P v i σ +
      ((encodingAttemptLimit * 4 : ℕ) : ℝ≥0∞) * reRevW i σ := by
  rcases i with ((i | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · show cwDiscCharge P v T σ ≤
      ∑ J : Fin encodingAttemptLimit × Fin 4, diagMass (firstSetO P v J.1 (dropKey T)) σ +
        hwRevO P v (dropKey T) σ +
          ((encodingAttemptLimit * 4 : ℕ) : ℝ≥0∞) * reRevO (dropKey T) σ
    refine (le_of_eq (cwDiscCharge_eq P v T σ)).trans ?_
    cases dropKey T with
    | none => exact zero_le
    | some K =>
      show ∑ J : Fin encodingAttemptLimit × Fin 4,
          diagMass {q : Unit × HwReg X Z (Mem HPos) |
            q.2 ∈ cwTD P K (valsOf v (msgPos K)) J.1} σ ≤
        ∑ J : Fin encodingAttemptLimit × Fin 4, diagMass {q : Unit × HwReg X Z (Mem HPos) |
            FirstRec P K (valsOf v (msgPos K)) J.1 q.2} σ +
          ∑ J : Fin encodingAttemptLimit × Fin 4, diagMass {q : Unit × HwReg X Z (Mem HPos) |
            FirstHw P K (valsOf v (msgPos K)) J.1 q.2} σ +
          ((encodingAttemptLimit * 4 : ℕ) : ℝ≥0∞) *
            diagMass {q : Unit × HwReg X Z (Mem HPos) | ReRev K q.2} σ
      calc ∑ J : Fin encodingAttemptLimit × Fin 4,
            diagMass {q : Unit × HwReg X Z (Mem HPos) |
              q.2 ∈ cwTD P K (valsOf v (msgPos K)) J.1} σ
          ≤ ∑ J : Fin encodingAttemptLimit × Fin 4,
              (diagMass {q : Unit × HwReg X Z (Mem HPos) |
                FirstRec P K (valsOf v (msgPos K)) J.1 q.2} σ +
                diagMass {q : Unit × HwReg X Z (Mem HPos) |
                  FirstHw P K (valsOf v (msgPos K)) J.1 q.2} σ +
                diagMass {q : Unit × HwReg X Z (Mem HPos) | ReRev K q.2} σ) :=
            Finset.sum_le_sum fun J _ ↦ diagMass_le_three (fun a ha ↦ by
              by_cases hl : HPos.val (msgPos K) ∈ a.2.2.2.1
              · exact Or.inr (Or.inr ⟨hl, ha.2⟩)
              · rcases ha.1 with hd | hw
                · exact Or.inl ⟨hl, hd⟩
                · exact Or.inr (Or.inl ⟨hl, hw, ha.2⟩)) σ
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]

/-- **The hardwired first-disclosure charges vanish** under `TrialsOff`: the hardwired cells are
cells of `ProgCell`, no trial block. -/
theorem totalWeight_hwRevW_eq_zero (pol : DigestPolicy) (pub : Pub) (v : (s : HPos) → XD s)
    (A : SAdversary) (hoff : TrialsOff pub.xw pub.keys.1 (valsOf v)) :
    (runtimeR m0R).totalWeight .instruments (hwRevW pub.seed v) (prefixR pol A pub v) initR =
      0 := by
  refine le_antisymm ?_ zero_le
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i σ ↦ QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2)
      {s : HwReg X Z (Mem HPos) | GoodW (ProgCell pub v) s.2.1} σ)
    (fun i E σ hP ↦ querySupportedOn_traceRight hP.2)
    (w' := fun i σ ↦ 0 * hwRevW pub.seed v i σ) (fun i σ _ hok ↦ ?_) _ initR_posSemidef
    (forallQueries_goodW_prefixR pub v pol A)).trans (le_of_eq ((totalWeight_const_mul_weight
      (runtimeR m0R) .instruments 0 (hwRevW pub.seed v) _ initR).trans (zero_mul _)))
  rw [zero_mul]
  rcases i with ((i | c) | c) | T
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · show hwRevO pub.seed v (dropKey T) σ ≤ 0
    cases dropKey T with
    | none => exact le_rfl
    | some K =>
      refine le_of_eq (Finset.sum_eq_zero fun J _ ↦ diagMass_eq_zero_of fun q hq ↦ ?_)
      by_contra h0
      exact not_progCell_cwBlk pub v hoff K _ _ ((hok q q h0).1 (.k _) hq.2.1)

/-- **The constant of the codeword-recorded mass**: the first disclosures `revFirstC · 6q`, the
repeated disclosures `4 · 2^32 ε`, the fresh parts `cwFreshEps (6q + clsCap) · clsCap`. -/
noncomputable def cwRevTau (q : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  revFirstC * (6 * q) + ((encodingAttemptLimit * 4 : ℕ) : ℝ≥0∞) * ε +
    ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap

open scoped Classical in
/-- **The failed searches**: the mass at the repeated disclosures with the key unselected, summed
over the hidden values with `TrialsOff`, at most `ε` per hidden value. -/
def CwReView (pol : DigestPolicy) (A : SAdversary) (p : Pub) (ε : ℝ≥0∞) : Prop :=
  ∑ v : (s : HPos) → XD s,
    (if TrialsOff p.xw p.keys.1 (valsOf v) then (runtimeR m0R).totalWeight .instruments
      reRevW (prefixR pol A p v) initR else 0) ≤ ε * Fintype.card ((s : HPos) → XD s)

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

omit P in
/-- **The codeword-recorded mass at one datum off trial blocks**: the fresh parts, the first
disclosures and the repeated ones. -/
theorem cwRecPre_le_split (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hoff : TrialsOff p.xw p.keys.1 (valsOf v)) :
    cwRecPre pol A p v ≤ ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap +
      ((runtimeR m0R).totalWeight .instruments (firstW p.seed v) (prefixR pol A p v) initR +
        ((encodingAttemptLimit * 4 : ℕ) : ℝ≥0∞) *
          (runtimeR m0R).totalWeight .instruments reRevW (prefixR pol A p v) initR) := by
  set c : ℝ≥0∞ := ((encodingAttemptLimit * 4 : ℕ) : ℝ≥0∞)
  refine (cwRecPre_le_rev hperm hsign pol p v).trans ?_
  rw [totalWeight_cwProgW_eq_zero p v pol A hoff, add_zero]
  refine add_le_add le_rfl ?_
  refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := fun i σ ↦ (firstW p.seed v i σ + hwRevW p.seed v i σ) + c * reRevW i σ)
    (fun i σ _ ↦ cwRevW_le p.seed v i σ) _ initR_posSemidef).trans (le_of_eq
      ((totalWeight_add_weight (runtimeR m0R) .instruments
        (fun i σ ↦ firstW p.seed v i σ + hwRevW p.seed v i σ) (fun i σ ↦ c * reRevW i σ) _
          initR).trans ?_))
  have h1 : (runtimeR m0R).totalWeight .instruments
      (fun i σ ↦ firstW p.seed v i σ + hwRevW p.seed v i σ) (prefixR pol A p v) initR =
      (runtimeR m0R).totalWeight .instruments (firstW p.seed v) (prefixR pol A p v) initR :=
    (totalWeight_add_weight (runtimeR m0R) .instruments (firstW p.seed v) (hwRevW p.seed v) _
      initR).trans (by rw [totalWeight_hwRevW_eq_zero pol p v A hoff, add_zero])
  exact congrArg₂ (· + ·) h1 (totalWeight_const_mul_weight (runtimeR m0R) .instruments c reRevW _
    initR)

omit P in
open scoped Classical in
/-- **The codeword-recorded mass on the hidden values off trial blocks**, summed over the hidden
values: at most `cwRevTau q ε` per hidden value, given the failed searches `CwReView`. -/
theorem sum_cwRecPre_good_le (pol : DigestPolicy) (p : Pub) {ε : ℝ≥0∞}
    (hre : CwReView pol A p ε) :
    ∑ v : (s : HPos) → XD s, (if TrialsOff p.xw p.keys.1 (valsOf v) then
      cwRecPre pol A p v else 0) ≤ cwRevTau q ε * Fintype.card ((s : HPos) → XD s) := by
  set c : ℝ≥0∞ := ((encodingAttemptLimit * 4 : ℕ) : ℝ≥0∞)
  set F : ℝ≥0∞ := ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap
  have hv : ∀ v : (s : HPos) → XD s, (if TrialsOff p.xw p.keys.1 (valsOf v) then
      cwRecPre pol A p v else 0) ≤
      F + ((runtimeR m0R).totalWeight .instruments (firstW p.seed v) (prefixR pol A p v) initR +
        c * (if TrialsOff p.xw p.keys.1 (valsOf v) then (runtimeR m0R).totalWeight
          .instruments reRevW (prefixR pol A p v) initR else 0)) := fun v ↦ by
    split_ifs with hoff
    · exact cwRecPre_le_split hperm hsign pol p v hoff
    · exact zero_le
  calc ∑ v : (s : HPos) → XD s, (if TrialsOff p.xw p.keys.1 (valsOf v) then
        cwRecPre pol A p v else 0)
      ≤ ∑ v : (s : HPos) → XD s, (F + ((runtimeR m0R).totalWeight .instruments
          (firstW p.seed v) (prefixR pol A p v) initR +
        c * (if TrialsOff p.xw p.keys.1 (valsOf v) then (runtimeR m0R).totalWeight
          .instruments reRevW (prefixR pol A p v) initR else 0))) :=
        Finset.sum_le_sum fun v _ ↦ hv v
    _ = F * Fintype.card ((s : HPos) → XD s) +
        (∑ v : (s : HPos) → XD s, (runtimeR m0R).totalWeight .instruments (firstW p.seed v)
          (prefixR pol A p v) initR +
        c * ∑ v : (s : HPos) → XD s, (if TrialsOff p.xw p.keys.1 (valsOf v) then
          (runtimeR m0R).totalWeight .instruments reRevW (prefixR pol A p v) initR else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_comm]
    _ ≤ F * Fintype.card ((s : HPos) → XD s) +
        (revFirstC * (6 * q) * Fintype.card ((s : HPos) → XD s) +
          c * (ε * Fintype.card ((s : HPos) → XD s))) :=
        add_le_add le_rfl (add_le_add (sum_totalWeight_firstW_le hperm hsign pol p)
          (mul_le_mul' le_rfl hre))
    _ = _ := by
        unfold cwRevTau
        ring

omit P in
open scoped Classical in
/-- **The averaged codeword-recorded mass** over the hidden values off trial blocks: at most
`cwRevTau q ε`, given the failed searches `CwReView`. -/
theorem uavg_cwRecPre_le_rev (pol : DigestPolicy) (p : Pub) {ε : ℝ≥0∞}
    (hre : CwReView pol A p ε) :
    uavg (fun v : (s : HPos) → XD s ↦ if TrialsOff p.xw p.keys.1 (valsOf v) then
      cwRecPre pol A p v else 0) ≤ cwRevTau q ε := by
  unfold uavg
  have hc : (Fintype.card ((s : HPos) → XD s) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc (Fintype.card ((s : HPos) → XD s) : ℝ≥0∞)⁻¹ * ∑ v : (s : HPos) → XD s,
        (if TrialsOff p.xw p.keys.1 (valsOf v) then cwRecPre pol A p v else 0)
      ≤ (Fintype.card ((s : HPos) → XD s) : ℝ≥0∞)⁻¹ *
          (cwRevTau q ε * Fintype.card ((s : HPos) → XD s)) :=
        mul_le_mul' le_rfl (sum_cwRecPre_good_le hperm hsign pol p hre)
    _ = cwRevTau q ε := by
        rw [mul_comm (cwRevTau q ε), ← mul_assoc, ENNReal.inv_mul_cancel hc
          (ENNReal.natCast_ne_top _), one_mul]

end assemble

end Quantum.Sphincs.Assembly

end
