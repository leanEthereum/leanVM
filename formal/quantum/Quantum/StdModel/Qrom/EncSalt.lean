module

public import Quantum.StdModel.Qrom.Moded
public import Quantum.StdModel.Qrom.ReadGrade
public import Quantum.StdModel.Qrom.Tcr

@[expose] public section

/-!
# EncTCR$ in the QROM: the graded bound with additive classical costs

The targets of EncTCR$ (`Props.encTcrSalt`) are answered while the adversary runs, so a trial
read of the challenger may hit a cell the adversary recorded. Such reads cannot be priced like
sponge calls; they are priced additively, by their exact flip (a classical read is a
measurement, so the event weight grows by the flip, summed over the run as a total weight).

* **The graded bound along modes with additive costs**
  (`rpow_inv_two_tsum_potential_runtime2_moded_add`): as Moded's
  `rpow_inv_two_tsum_potential_runtime2_moded`, a call may also add `d i σ` to the event weight of
  its input, and the bound gains the total weight of `d` under the square root:
  `√w ≤ nA √(ηA tr ρ) + bud μ √(ηB tr ρ) + √(w ρ + ∑ d)`.
* **The refined read cost, linearized** (`readLin`, `readCost_readH_le`): the refined cost of a
  read of `h` is at most a diagonal sum: the values changing the event over `|X|` on an empty
  cell, `2/|X|`, the classical move and the flip-recorded indicator on a recorded one.
* **A read of a logged cell is free** (`tsum_potential_readH_logged`): decompressed, the read is
  the identity on the support plus a memory move.
* **The property game, graded with a live budget and additive costs**
  (`probAvg_game_slRed_le_moded_budget`): from OffTweak's bridge, Moded's mixed-game modes on the
  policies' ports (`modedP_toReads_policy`) and the win in the event, the success of a
  straight-line reduction is at most `((n + nB) √η + √(∑ d))²`, `nB` a budget of live charges
  read off the final memories.
* **EncTCR$** (namespace `EncSalt`): the event is Tcr's `BadR` with every tweak a class; the
  answers record the first codeword value of a class (`uSel`); sponge calls are charged
  statically (`κA`), the first reads of encoding cells by the reduction and the decision and the
  decision's slot live (`κB`, measure `βS`), re-reads of logged cells and reads off the encoding
  cells are free, the trial reads add their linearized cost (`dS`, `tsum_potential_step_salt`).
  The live invariant (`RecInv`) puts every win in the event (`won_of_judge`); a live step raises
  `βS` by its live charge (`κB_add_βS_le`), the decision by at most `2` (`βS_judge_le`).
* **The bound** (`probAvg_encTcrSalt_le`): `((q + k₁ + k₂ + 2) √(gradeEta F) + √TW)²`, `q` the
  adversary's calls, `k₁`, `k₂` the live budgets of the reduction's setup and output, `TW` the
  total weight of the challenger's trial reads.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

universe u v

namespace Quantum.StdModel.Qrom

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Xmss.Assembly (ModedP)
open Quantum.Xmss.Hybrid (runtime2)

/-! ## The graded bound along modes with additive costs -/

section sqrtModedAdd

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] [Nonempty X] [Nonempty Z] {M : Type} [Fintype M] [DecidableEq M]
  {Mode : Type} {rl : M → Z → Option X} {proj : Mode → Option M}
  {ok : Mode → (hwSpec X Z M).Port → Prop}
  {nx : Mode → (i : (hwSpec X Z M).Port) → (hwSpec X Z M).Result i → Mode}

/-- `a ≤ (√b + x)² + δ` gives `√(a + C) ≤ x + √(b + (δ + C))`. -/
theorem rpow_inv_two_add_le_of_le_sq_add {a b x δ C : ℝ≥0∞}
    (h : a ≤ (b ^ (2⁻¹ : ℝ) + x) ^ 2 + δ) :
    (a + C) ^ (2⁻¹ : ℝ) ≤ x + (b + (δ + C)) ^ (2⁻¹ : ℝ) := by
  have e : x = (x ^ 2) ^ (2⁻¹ : ℝ) := (Quantum.Xmss.Assembly.pow_two_rpow_inv_two x).symm
  rw [e] at h ⊢
  exact Quantum.Xmss.Assembly.rpow_inv_two_add_le_of_le_sq h

open scoped Classical in
/-- **The graded event bound along a moded program of runtime 2, with additive costs.** As
`rpow_inv_two_tsum_potential_runtime2_moded`, but a call may also add `d i σ` to the event weight
of its input `σ`; the total weight of `d` along the run enters under the square root:
`√w ≤ nA √(ηA tr ρ) + bud μ √(ηB tr ρ) + √(w ρ + ∑ d)`. -/
theorem rpow_inv_two_tsum_potential_runtime2_moded_add (m₀ : M)
    (hok : ∀ μ i, ok μ i → OkD rl (proj μ) i)
    (hnx : ∀ μ i r, ok μ i → proj (nx μ i r) = nxD rl (proj μ) i r)
    (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (doom : Mode → Prop)
    (hdoom : ∀ μ i r, ok μ i → doom μ → doom (nx μ i r))
    (κA : (hwSpec X Z M).Port → ℕ) (κB : Mode → (hwSpec X Z M).Port → ℕ) (bud : Mode → ℕ)
    (hbud : ∀ μ i r, ok μ i → ¬doom (nx μ i r) → κB μ i + bud (nx μ i r) ≤ bud μ)
    (ηA ηB : ℝ≥0∞) (CInv : Mode → Set (HwReg X Z M))
    (hC : ∀ μ i r (σ : Matrix ((hwSpec X Z M).In i × HwReg X Z M)
        ((hwSpec X Z M).In i × HwReg X Z M) ℂ), ok μ i →
      QuerySupportedOn (fun m : (hwSpec X Z M).In i × HwReg X Z M ↦ m.2) (CInv μ) σ →
      QuerySupportedOn (fun m : (hwSpec X Z M).Out i × HwReg X Z M ↦ m.2) (CInv (nx μ i r))
        (((runtime2 X Z m₀).step i).branch r σ))
    (d : ∀ i, Matrix ((hwSpec X Z M).In i × HwReg X Z M) ((hwSpec X Z M).In i × HwReg X Z M) ℂ →
      ℝ≥0∞)
    (hη : ∀ μ i (σ : Matrix ((hwSpec X Z M).In i × HwReg X Z M)
        ((hwSpec X Z M).In i × HwReg X Z M) ℂ), ok μ i → ¬doom μ → σ.PosSemidef →
      DSupp rl proj μ σ →
      QuerySupportedOn (fun m : (hwSpec X Z M).In i × HwReg X Z M ↦ m.2) (CInv μ) σ →
      ∑' r, (if doom (nx μ i r) then 0 else
          potential (hwProjector S) (((runtime2 X Z m₀).step i).branch r σ)) ≤
        (potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
          (κA i * (ηA * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) +
          κB μ i * (ηB * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ))) ^ 2 + d i σ)
    {Ω : QReg → Type} {fin : (Σ u, Ω u) → Mode → Prop}
    (hfin : ∀ p μ, fin p μ → doom μ → proj μ = none) {L : LocalSig.{u, v}} (I : L.Interp)
    {A : QReg} (x : QuantumComp L (hwSpec X Z M) Ω A) :
    ∀ (nA : ℕ), IFreeM.IsChargeBound x (portCharge κA) nA → ∀ μ, ModedP ok nx fin μ x →
      ∀ {ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ}, ρ.PosSemidef →
        DSupp rl proj μ ρ → QuerySupportedOn (fun m : A × HwReg X Z M ↦ m.2) (CInv μ) ρ →
        (∑' p, potential (hwProjector S) (((runtime2 X Z m₀).run I x).branch p ρ)) ^ (2⁻¹ : ℝ) ≤
          nA * (ηA * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
            bud μ * (ηB * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
            (potential (hwProjector S) ρ +
              (runtime2 X Z m₀).totalWeight I d x ρ) ^ (2⁻¹ : ℝ) := by
  classical
  have hzero : ∀ {B : QReg} (y : QuantumComp L (hwSpec X Z M) Ω B) (μ : Mode), doom μ →
      ModedP ok nx fin μ y → ∀ {ρ : Matrix (B × HwReg X Z M) (B × HwReg X Z M) ℂ},
        DSupp rl proj μ ρ →
        ∑' p, potential (hwProjector S) (((runtime2 X Z m₀).run I y).branch p ρ) = 0 := by
    intro B y μ hd hy ρ hρ
    refine ENNReal.tsum_eq_zero.mpr fun p ↦ ?_
    rw [branch_eq_zero_of_doom m₀ hok hnx doom hdoom hfin I y μ hd hy hρ p]
    simp [potential]
  induction x using QuantumComp.inductionOn with
  | pure B y =>
    intro nA _ μ _ ρ _ _ _
    rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ u, Ω u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply]
        simp [potential],
      DSubInstrument.branch_ret_self, LinearMap.id_apply, totalWeight_pure, add_zero]
    exact le_add_left le_rfl
  | primBind B o k ih =>
    intro nA hxA μ hx ρ hρ hs hcs
    by_cases hd : doom μ
    · rw [hzero _ μ hd hx hs, ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
    have hρb := fun b ↦ ((I o).frame (QReg.of (HwReg X Z M))).posSemidef_branch_apply b hρ
    have hL : ∀ p, potential (hwProjector S) (((runtime2 X Z m₀).run I
        (QuantumComp.primBind o k)).branch p ρ) = ∑' b, potential (hwProjector S)
          (((runtime2 X Z m₀).run I (k b)).branch p
            (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ)) := fun p ↦ by
      rw [run_primBind, DSubInstrument.branch_bind_apply]
      exact Quantum.Sponge.potential_tsum _ ((((I o).frame _).isCPTNIFamily.comp_eval
        (fun b ↦ ((runtime2 X Z m₀).run I (k b)).isCPTNIFamily) p).summable_apply ρ)
        fun b ↦ ((runtime2 X Z m₀).run I (k b)).posSemidef_branch_apply p (hρb b)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_primBind_iff] at hxA
    have hch : ∀ b, (∑' p, potential (hwProjector S) (((runtime2 X Z m₀).run I (k b)).branch p
        (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ))) ^ (2⁻¹ : ℝ) ≤
        nA * (ηA * ENNReal.ofReal
          (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ).trace.re) ^ (2⁻¹ : ℝ) +
        bud μ * (ηB * ENNReal.ofReal
          (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ).trace.re) ^ (2⁻¹ : ℝ) +
        (potential (hwProjector S) (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ) +
          (runtime2 X Z m₀).totalWeight I d (k b)
            (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ)) ^ (2⁻¹ : ℝ) := fun b ↦ by
      have hxb : ModedP ok nx fin μ (k b) := hx.2 (ULift.up b)
      exact ih b nA (hxA b) μ hxb (hρb b) (dSupp_frame o I b hs)
        (QuerySupportedOn.amplify_snd (q := id) hcs _)
    refine rpow_inv_two_tsum_le_two nA (bud μ) ηA ηB _ _ hch
      (((I o).frame _).isCPTNIFamily.tsum_ofReal_trace_re_le hρ) ?_
    rw [ENNReal.tsum_add, totalWeight_primBind]
    exact add_le_add (tsum_potential_frame_le _ (I o) hρ) le_rfl
  | queryBind B i E ℓ k ih =>
    intro nA hxA μ hx ρ hρ hs hcs
    by_cases hd : doom μ
    · rw [hzero _ μ hd hx hs, ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
    have hρr := fun r ↦ ((runtime2 X Z m₀).queryStep i E ℓ).posSemidef_branch_apply r hρ
    have hL : ∀ p, potential (hwProjector S) (((runtime2 X Z m₀).run I
        (QuantumComp.queryBind i E ℓ k)).branch p ρ) = ∑' r, potential (hwProjector S)
          (((runtime2 X Z m₀).run I (k r)).branch p
            (((runtime2 X Z m₀).queryStep i E ℓ).branch r ρ)) := fun p ↦ by
      rw [run_queryBind, DSubInstrument.branch_bind_apply]
      exact Quantum.Sponge.potential_tsum _
        ((((runtime2 X Z m₀).queryStep i E ℓ).isCPTNIFamily.comp_eval
          (fun r ↦ ((runtime2 X Z m₀).run I (k r)).isCPTNIFamily) p).summable_apply ρ)
        fun r ↦ ((runtime2 X Z m₀).run I (k r)).posSemidef_branch_apply p (hρr r)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_queryBind_iff] at hxA
    have hi : ok μ i := hx.1
    have hxr : ∀ r, ModedP ok nx fin (nx μ i r) (k r) := fun r ↦ hx.2 (ULift.up r)
    by_cases hall : ∀ r, doom (nx μ i r)
    · rw [ENNReal.tsum_eq_zero.mpr fun r ↦ hzero (k r) _ (hall r) (hxr r)
        (dSupp_queryStep m₀ hok hnx hi E ℓ r hs), ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
    obtain ⟨r₀, hr₀⟩ := not_forall.mp hall
    have hB : κB μ i ≤ bud μ := (Nat.le_add_right _ _).trans (hbud μ i r₀ hi hr₀)
    set a := nA - κA i
    set b := bud μ - κB μ i
    set tr : (hwSpec X Z M).Result i → ℝ≥0∞ := fun r ↦
      ENNReal.ofReal (((runtime2 X Z m₀).queryStep i E ℓ).branch r ρ).trace.re
    set P : (hwSpec X Z M).Result i → ℝ≥0∞ := fun r ↦
      (if doom (nx μ i r) then 0 else potential (hwProjector S)
        (((runtime2 X Z m₀).step i).branch r (callInput ℓ _ ρ))) +
      (runtime2 X Z m₀).totalWeight I d (k r) (((runtime2 X Z m₀).queryStep i E ℓ).branch r ρ)
    have hchild : ∀ r, (∑' p, potential (hwProjector S) (((runtime2 X Z m₀).run I (k r)).branch p
        (((runtime2 X Z m₀).queryStep i E ℓ).branch r ρ))) ^ (2⁻¹ : ℝ) ≤
        a * (ηA * tr r) ^ (2⁻¹ : ℝ) + b * (ηB * tr r) ^ (2⁻¹ : ℝ) + P r ^ (2⁻¹ : ℝ) := by
      intro r
      have hsr := dSupp_queryStep m₀ hok hnx hi E ℓ r hs
      by_cases hdr : doom (nx μ i r)
      · rw [hzero (k r) _ hdr (hxr r) hsr, ENNReal.zero_rpow_of_pos (by norm_num)]
        exact zero_le
      simp only [P, hdr, ↓reduceIte]
      rw [← potential_queryStep (runtime2 X Z m₀) (hwProjector S) i E ℓ r ρ]
      refine (ih r a (hxA.2 r) _ (hxr r) (hρr r) hsr
        (querySupportedOn_queryStep_moded (runtime2 X Z m₀) CInv hC hi E ℓ r hcs)).trans ?_
      have hb : bud (nx μ i r) ≤ b := by
        have := hbud μ i r hi hdr
        omega
      gcongr
    have hη' := hη μ i _ hi hd (posSemidef_callInput ℓ hρ) (dSupp_callInput ℓ hs)
      (QuerySupportedOn.callInput (g := id) hcs ℓ)
    rw [potential_callInput, trace_callInput] at hη'
    set T := ENNReal.ofReal ρ.trace.re
    set c : ℝ≥0∞ := κA i * (ηA * T) ^ (2⁻¹ : ℝ) + κB μ i * (ηB * T) ^ (2⁻¹ : ℝ)
    set D : ℝ≥0∞ := d i (callInput ℓ _ ρ) + ∑' r, (runtime2 X Z m₀).totalWeight I d (k r)
      (((runtime2 X Z m₀).queryStep i E ℓ).branch r ρ)
    have hP : ∑' r, P r ≤ (potential (hwProjector S) ρ ^ (2⁻¹ : ℝ) + c) ^ 2 + D := by
      simp only [P, D]
      rw [ENNReal.tsum_add, ← add_assoc]
      exact add_le_add hη' le_rfl
    refine (rpow_inv_two_tsum_le_two a b ηA ηB T _ hchild
      (((runtime2 X Z m₀).queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ) hP).trans ?_
    have hsq := rpow_inv_two_add_le_of_le_sq_add (C := D)
      (le_of_eq (add_zero ((potential (hwProjector S) ρ ^ (2⁻¹ : ℝ) + c) ^ 2)).symm)
    rw [zero_add] at hsq
    rw [totalWeight_queryBind]
    have hnA : (nA : ℝ≥0∞) = κA i + a := by
      rw [← Nat.cast_add]
      exact congrArg _ (by omega)
    have hbud' : (bud μ : ℝ≥0∞) = κB μ i + b := by
      rw [← Nat.cast_add]
      exact congrArg _ (by omega)
    calc (a : ℝ≥0∞) * (ηA * T) ^ (2⁻¹ : ℝ) + b * (ηB * T) ^ (2⁻¹ : ℝ) +
          ((potential (hwProjector S) ρ ^ (2⁻¹ : ℝ) + c) ^ 2 + D) ^ (2⁻¹ : ℝ)
        ≤ (a : ℝ≥0∞) * (ηA * T) ^ (2⁻¹ : ℝ) + b * (ηB * T) ^ (2⁻¹ : ℝ) +
          (c + (potential (hwProjector S) ρ + D) ^ (2⁻¹ : ℝ)) := by gcongr
      _ = _ := by
        rw [hnA, hbud']
        simp only [c, D]
        ring

end sqrtModedAdd

/-! ## The refined cost of a read, linearized -/

section linCost

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Nonempty X]
  [Nonempty Z] {M : Type} [Fintype M] [DecidableEq M]

/-- **The diagonal cost of a read of cell `z` of `h`** with the policy `u`, at the state `q`: on
an empty cell, the values whose recording changes the event (`rdCnt`, plus `2`, and `hFlip`)
over `|X|`; on a recorded cell, `2/|X|`, the classical move and the flip-recorded indicator (`pd`
of `Flip`: the recorded value flips the event, or its move changes it); on a hardwired cell, the
classical move. -/
noncomputable def readLin (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (u : M → Option X → M) (q : Unit × HwReg X Z M) : ℝ :=
  (if q.2.2.1.1 z = none then
      (if q.2.1.1 z = none then ((rdCnt S z u q : ℝ) + 2) / Fintype.card X else
        2 / Fintype.card X + if hCls S u (q.2.1.1 z) q then 1 else 0) else
      if hCls S u (q.2.2.1.1 z) q then 1 else 0) +
    (if q.2.2.1.1 z = none ∧ q.2.1.1 z = none then
      ((Finset.univ.filter (hFlip S z u q)).card : ℝ) / Fintype.card X else 0) +
    pd (splitH' z) (actH z) (Flip (splitH' z) (tauH z u) (liftSet S)) q

omit [Fintype X] [DecidableEq X] [Fintype Z] [Fintype M] [DecidableEq M] [Nonempty X]
  [Nonempty Z] in
/-- The flip-recorded indicator is at most the recorded mass at the read cell. -/
theorem pd_flip_le_readH (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (u : M → Option X → M) (q : Unit × HwReg X Z M) :
    pd (splitH' z) (actH z) (Flip (splitH' z) (tauH z u) (liftSet S)) q ≤
      if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none then (1 : ℝ) else 0 := by
  unfold pd
  rw [show (splitH' z q).1 = q.2.1.1 z from rfl]
  change (if q.2.2.1.1 z = none then _ else _) ≤ _
  cases q.2.1.1 z <;> simp only [Option.elim_none, Option.elim_some] <;> split_ifs <;> simp_all

/-- `2 √(a b) ≤ a + b`. -/
theorem two_mul_rpow_inv_two_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (ENNReal.ofReal a * ENNReal.ofReal b) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal a + ENNReal.ofReal b := by
  rw [← ENNReal.ofReal_mul ha, ENNReal.ofReal_rpow_inv_two, ← ENNReal.ofReal_add ha hb,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.sqrt_mul ha]
  nlinarith [sq_nonneg (√a - √b), Real.sq_sqrt ha, Real.sq_sqrt hb]

omit [DecidableEq M] [Nonempty Z] in
/-- **The refined cost of a read of `h`, linearized**: at most the diagonal sum of `readLin`. -/
theorem readCost_readH_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (u : M → Option X → M) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) :
    readCost S (.readH z u) σ ≤ ENNReal.ofReal (∑ q, readLin S z u q * (σ q q).re) := by
  obtain ⟨hE, -, -⟩ := read_readH_le S z u hσ
  have hA := readA_readH_le S z u hσ
  have hE0 := costE_nonneg (e := splitH' z) (act := actH z) (τ := tauH z u) (liftSet S) hσ
  have hP0 := costP_nonneg (e := splitH' z) (act := actH z) (τ := tauH z u) (liftSet S) hσ
  change ENNReal.ofReal (readA S (.readH z u) σ) + 2 * (ENNReal.ofReal (readE S (.readH z u) σ) *
    ENNReal.ofReal (costP (splitH' z) (actH z) (tauH z u) (liftSet S) σ)) ^ (2⁻¹ : ℝ) ≤ _
  refine (add_le_add le_rfl (two_mul_rpow_inv_two_le hE0 hP0)).trans ?_
  rw [← add_assoc]
  have hre : ∀ q : Unit × HwReg X Z M, 0 ≤ (σ q q).re :=
    fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hnn : ∀ f : Unit × HwReg X Z M → ℝ, (∀ q, 0 ≤ f q) → 0 ≤ ∑ q, f q * (σ q q).re :=
    fun f hf ↦ Finset.sum_nonneg fun q _ ↦ mul_nonneg (hf q) (hre q)
  have hA' : 0 ≤ ∑ q, (if q.2.2.1.1 z = none then
      (if q.2.1.1 z = none then
        ((rdCnt S z u q : ℝ) + 2) / Fintype.card X else
        2 / Fintype.card X + if hCls S u (q.2.1.1 z) q then 1 else 0) else
      if hCls S u (q.2.2.1.1 z) q then 1 else 0) * (σ q q).re :=
    hnn _ fun q ↦ by split_ifs <;> positivity
  have hE' : 0 ≤ ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z = none then
      ((Finset.univ.filter (hFlip S z u q)).card : ℝ) / Fintype.card X else 0) * (σ q q).re :=
    hnn _ fun q ↦ by split_ifs <;> positivity
  refine (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hA) (ENNReal.ofReal_le_ofReal hE))
    le_rfl).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add hA' hE', ← ENNReal.ofReal_add (add_nonneg hA' hE') hP0]
  congr 1
  simp only [readLin, costP, add_mul, Finset.sum_add_distrib]

end linCost

/-! ## A read of a logged cell is free -/

section reread

open Quantum.Xmss.Assembly (kron_one_mul_clsKraus_mul_kron_one
  compressAll_mul_cellRead_mul_compressAll)

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] [Nonempty X] [Nonempty Z] {M : Type} [Fintype M] [DecidableEq M]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **A read of `h` in the decompressed basis** is classical: it keeps the databases and the
hardwired cells, checks the memory and the cell's value, and moves the memory. -/
theorem compressReg_mul_readKrausH (z : Z) (u : M → Option X → M) (r : Option X × M) :
    compressReg X Z M * readKrausH z u r * compressReg X Z M =
      clsKraus (fun b : Hw X Z × M ↦ b.2 = r.2) (fun b ↦ (b.1, u r.2 r.1)) fun b ↦
        diagonal fun D : DbReg X Z ↦ if (b.1.1 z).or (D.1 z) = r.1 then (1 : ℂ) else 0 := by
  rw [compressReg, readKrausH, kron_one_mul_clsKraus_mul_kron_one]
  congr 1
  funext b
  rw [compressDbs, ← mul_kronecker_mul, ← mul_kronecker_mul,
    compressAll_mul_cellRead_mul_compressAll, Matrix.mul_one, ← mul_kronecker_mul,
    compressAll_mul_self, one_kronecker_one, ← Matrix.diagonal_one,
    Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext D
  rw [mul_one]

/-- The memory move from the memory `m` with the outcome `some v`, on the hardwired cells and
the memory. -/
noncomputable def mvMemOp (u : M → Option X → M) (m : M) (v : X) :
    Matrix (Hw X Z × M) (Hw X Z × M) ℂ :=
  Matrix.of fun a c ↦ if c.2 = m ∧ a = (c.1, u m (some v)) then 1 else 0

/-- **The memory move** on the register beside the trivial one. -/
noncomputable def mvOp (u : M → Option X → M) (m : M) (v : X) :
    Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ :=
  (1 : Matrix Unit Unit ℂ) ⊗ₖ ((1 : Matrix (DbReg X Z) (DbReg X Z) ℂ) ⊗ₖ mvMemOp u m v)

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- The compression commutes with the memory move. -/
theorem compress_mul_mvOp (u : M → Option X → M) (m : M) (v : X) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) * mvOp u m v =
      mvOp u m v * ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) := by
  simp only [mvOp, compressReg, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

omit [Fintype M] [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem mvOp_apply (u : M → Option X → M) (m : M) (v : X) (a c : Unit × HwReg X Z M) :
    mvOp u m v a c = if c.2.2.2 = m ∧ a.2 = (c.2.1, c.2.2.1, u m (some v)) then 1 else 0 := by
  simp only [mvOp, mvMemOp, kroneckerMap_apply, Matrix.of_apply, Matrix.one_apply,
    Subsingleton.elim a.1 c.1, ↓reduceIte, one_mul]
  by_cases h1 : a.2.1 = c.2.1 <;> by_cases h2 : c.2.2.2 = m <;>
    by_cases h3 : a.2.2 = (c.2.2.1, u m (some v)) <;> simp [h1, h2, h3, Prod.ext_iff]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **The read of a logged cell, decompressed**: on an operator decompressed-supported at a
memory `m` whose cell `z` holds `v` with no hardwired cell, the decompressed read with outcome
`(some v, m)` is the memory move, every other outcome is zero. -/
theorem dec_readKrausH_mul (z : Z) (u : M → Option X → M) (m : M) (v : X) (r : Option X × M)
    {τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hd : QuerySupportedOn (fun q : Unit × HwReg X Z M ↦ q.2)
      {s | s.1.1 z = some v ∧ s.2.1 = hwEmpty X Z ∧ s.2.2 = m} τ) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ (compressReg X Z M * readKrausH z u r * compressReg X Z M)) *
        τ = if r = (some v, m) then mvOp u m v * τ else 0 := by
  rw [compressReg_mul_readKrausH]
  ext a b
  rw [Matrix.mul_apply]
  split_ifs with hr
  · rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    by_cases hcb : τ c b = 0
    · rw [hcb, mul_zero, mul_zero]
    obtain ⟨⟨hz, hW, hm⟩, -⟩ := hd c b hcb
    dsimp only at hz hW hm
    subst hr
    rw [mvOp_apply, kroneckerMap_apply, clsKraus_apply, Matrix.one_apply_eq, one_mul, hm]
    congr 1
    by_cases h3 : a.2.2 = (c.2.2.1, u m (some v))
    · by_cases h1 : a.2.1 = c.2.1
      · rw [ite_eq_left ⟨rfl, h3⟩, ite_eq_left ⟨rfl, Prod.ext h1 h3⟩, h1,
          Matrix.diagonal_apply_eq, hW, hwEmpty_fst_apply, Option.none_or, ite_eq_left hz]
      · rw [ite_eq_left ⟨rfl, h3⟩, ite_eq_right (fun h : _ ∧ _ ↦ h1 (by rw [h.2])),
          Matrix.diagonal_apply_ne _ h1]
    · rw [ite_eq_right (fun h ↦ h3 h.2), ite_eq_right (fun h ↦ h3 (congrArg Prod.snd h.2))]
  · rw [Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    by_cases hcb : τ c b = 0
    · rw [hcb, mul_zero]
    obtain ⟨⟨hz, hW, hm⟩, -⟩ := hd c b hcb
    dsimp only at hz hW hm
    rw [kroneckerMap_apply, clsKraus_apply]
    refine mul_eq_zero_of_left (mul_eq_zero_of_right _ ?_) _
    split_ifs with hc
    · have : some v ≠ r.1 := fun h ↦ hr (Prod.ext h.symm (by rw [← hc.1, hm]))
      by_cases h1 : a.2.1 = c.2.1
      · rw [h1, Matrix.diagonal_apply_eq, hW, hwEmpty_fst_apply, Option.none_or, hz,
          ite_eq_right this]
      · exact Matrix.diagonal_apply_ne _ h1
    · rfl

omit [Nonempty X] [Nonempty Z] [AddCommGroup X] [AddCommGroup Z] in
/-- The diagonal of a memory move: the moved state's weight. -/
theorem mvOp_mul_mul_conjTranspose_diag (u : M → Option X → M) (m : M) (v : X)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) (q : Unit × HwReg X Z M) :
    (mvOp u m v * σ * (mvOp u m v)ᴴ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) q q =
      ∑ c, (if c.2.2.2 = m ∧
      q.2 = (c.2.1, c.2.2.1, u m (some v)) then σ c c else 0) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, mvOp_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.sum_eq_single c (fun d _ hdc ↦ ?_) (by simp)]
  · split_ifs <;> simp
  · by_cases hc : c.2.2.2 = m ∧ q.2 = (c.2.1, c.2.2.1, u m (some v))
    · by_cases hd : d.2.2.2 = m ∧ q.2 = (d.2.1, d.2.2.1, u m (some v))
      · exfalso
        refine hdc (Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ (Prod.ext ?_ ?_)))
        · have := congrArg Prod.fst (hc.2.symm.trans hd.2)
          exact this.symm
        · have := congrArg (fun p ↦ p.2.1) (hc.2.symm.trans hd.2)
          exact this.symm
        · rw [hc.1, hd.1]
      · simp [hd]
    · simp [hc]

/-- **A read of a logged cell is free.** On an operator whose decompressed support has the
memory `m`, the value `v` at the read cell `z` and no hardwired cell, the read of `z` with the
policy `u` only moves the memory to `u m (some v)`; if the event ignores that move, the event
weight does not grow. -/
theorem tsum_potential_readH_logged (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (u : M → Option X → M) (m : M) (v : X)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hd : QuerySupportedOn (fun q : Unit × HwReg X Z M ↦ q.2)
      {s | s.1.1 z = some v ∧ s.2.1 = hwEmpty X Z ∧ s.2.2 = m}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) σ))
    (hS : ∀ s : HwReg X Z M, s.2.2 = m → ((((s.1, s.2.1, u m (some v)) : HwReg X Z M) ∈ S) ↔
      s ∈ S)) :
    ∑' r, potential (hwProjector S) (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) ≤
      potential (hwProjector S) σ := by
  set U : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ :=
    (1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M with hUdef
  have hUU : U * U = 1 := by
    rw [hUdef, ← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self, one_kronecker_one]
  have hUh : Uᴴ = U := by
    rw [hUdef, conjTranspose_kronecker, conjTranspose_one, conjTranspose_compressReg]
  have hUU' : ∀ A : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ, U * (U * A) = A :=
    fun A ↦ by rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  set σd := U * σ * U with hσd
  have hd' : QuerySupportedOn (fun q : Unit × HwReg X Z M ↦ q.2)
      {s | s.1.1 z = some v ∧ s.2.1 = hwEmpty X Z ∧ s.2.2 = m} σd := by
    rw [MatrixMap.conj_apply, hUh] at hd
    exact hd
  set L : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ := mvOp u m v
  have hσσ : U * σd * U = σ := by simp only [hσd, Matrix.mul_assoc, hUU', hUU, Matrix.mul_one]
  have hσdh : σdᴴ = σd := by
    rw [hσd, conjTranspose_mul, conjTranspose_mul, hUh, hσ.1.eq, Matrix.mul_assoc]
  have hKd : ∀ r : Option X × M, U * hwReadKraus (.readH z u) r * U * σd =
      if r = (some v, m) then L * σd else 0 := fun r ↦ by
    have e : U * hwReadKraus (.readH z u) r * U = (1 : Matrix Unit Unit ℂ) ⊗ₖ
        (compressReg X Z M * readKrausH z u r * compressReg X Z M) := by
      change ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z u r) *
          ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) = _
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
    rw [e]
    exact dec_readKrausH_mul z u m v r hd'
  have hconj : ∀ r : Option X × M, MatrixMap.conj (hwReadKraus (.readH z u) r) σ =
      if r = (some v, m) then L * σ * Lᴴ else 0 := fun r ↦ by
    set K := hwReadKraus (.readH z u) r
    set Kd := U * K * U
    have hKK : U * Kd * U = K := by simp only [Kd, Matrix.mul_assoc, hUU', hUU, Matrix.mul_one]
    have h1 : MatrixMap.conj K σ = U * (Kd * σd * Kdᴴ) * U := by
      rw [MatrixMap.conj_apply, ← hKK, ← hσσ, conjTranspose_mul, conjTranspose_mul, hUh]
      simp only [Matrix.mul_assoc, hUU']
    have hc : U * L = L * U := compress_mul_mvOp u m v
    have hc' : Lᴴ * U = U * Lᴴ := by
      rw [← hUh, ← conjTranspose_mul, ← conjTranspose_mul, hc]
    have hfin : U * (L * σd * Lᴴ) * U = L * σ * Lᴴ := by
      rw [← hσσ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U L, hc]
      simp only [Matrix.mul_assoc]
      rw [hc']
    have hK' : Kd * σd = if r = (some v, m) then L * σd else 0 := hKd r
    have h2 : σd * Kdᴴ = (Kd * σd)ᴴ := by rw [Matrix.conjTranspose_mul Kd σd, hσdh]
    rw [h1, Matrix.mul_assoc Kd, h2, hK']
    split_ifs with hr
    · rw [Matrix.conjTranspose_mul L σd, hσdh, ← Matrix.mul_assoc Kd σd, hK', ite_eq_left hr,
        hfin]
    · simp
  simp only [hconj]
  rw [tsum_eq_single ((some v, m) : Option X × M) fun r hr ↦ by
    rw [ite_eq_right hr, QuantumRuntime.potential, map_zero]
    simp, ite_eq_left rfl]
  rw [potential_hwProjector_eq, potential_hwProjector_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hre : ∀ c, 0 ≤ (σ c c).re := fun c ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  calc ∑ q : Unit × HwReg X Z M, (if q.2 ∈ S then (1 : ℝ) else 0) * ((L * σ * Lᴴ) q q).re
      = ∑ c : Unit × HwReg X Z M, ∑ q : Unit × HwReg X Z M,
          (if q.2 ∈ S then (1 : ℝ) else 0) * (if c.2.2.2 = m ∧
          q.2 = (c.2.1, c.2.2.1, u m (some v)) then σ c c else 0).re := by
        simp only [L, mvOp_mul_mul_conjTranspose_diag, Complex.re_sum, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ c : Unit × HwReg X Z M, (if c.2 ∈ S then (1 : ℝ) else 0) * (σ c c).re := by
        refine Finset.sum_le_sum fun c _ ↦ ?_
        by_cases hc : c.2.2.2 = m
        · rw [Finset.sum_eq_single (c.1, c.2.1, c.2.2.1, u m (some v)) (fun q _ hq ↦ by
              have : ¬ (c.2.2.2 = m ∧ q.2 = (c.2.1, c.2.2.1, u m (some v))) :=
                fun h ↦ hq (Prod.ext (Subsingleton.elim _ _) h.2)
              simp [this]) (by simp)]
          by_cases hcs : c.2 ∈ S
          · simp [hc, hcs, (hS c.2 hc).2 hcs]
          · have hn : ((c.2.1, c.2.2.1, u m (some v)) : HwReg X Z M) ∉ S :=
              fun h ↦ hcs ((hS c.2 hc).1 h)
            simp [hc, hcs, hn]
        · rw [Finset.sum_eq_zero fun q _ ↦ by simp [hc]]
          exact mul_nonneg (by split_ifs <;> norm_num) (hre c)
end reread

/-! ## The property game of a straight-line reduction, graded with additive costs -/

section assembly

open Quantum.Qrom HashSig Props OracleComp OracleSpec

variable {Sx M' : Type} [Fintype Sx] [DecidableEq Sx] [Fintype M'] [DecidableEq M']

/-- The start of runtime 2 from the memory `m₀`, beside the trivial register. -/
noncomputable abbrev rhoMem0 (m₀ : Finset Sx × M') :
    Matrix (QReg.of Unit × RomReg HashDomain HashOutput (Finset Sx × M'))
      (QReg.of Unit × RomReg HashDomain HashOutput (Finset Sx × M')) ℂ :=
  (SubState.basis ()).matrix ⊗ₖ (runtime2 HashOutput HashDomain m₀).init.matrix

/-- The read program of a mixed program with the policies `upd`. -/
noncomputable abbrev readProgOf (upd : Caller → HashDomain → Finset Sx × M' →
    Option HashOutput → Finset Sx × M') {Ω : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A) :
    QuantumComp LocalSig.instruments.{0} (hwSpec HashOutput HashDomain (Finset Sx × M')) Ω A :=
  IFreeM.mapLens Quantum.Xmss.Assembly.liftReadLens (IFreeM.substitute (readSub upd) x)

/-- `(√a)² = a`. -/
theorem sq_rpow_inv_two (a : ℝ≥0∞) : (a ^ (2⁻¹ : ℝ)) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- One step of a moded command tree: normalize the head, then split the command. -/
local macro "moded_step" : tactic => `(tactic| (
  (conv => arg 5; whnf);
  refine ⟨?_, fun _ ↦ ?_⟩))

omit [Fintype Sx] [DecidableEq Sx] [Fintype M'] [DecidableEq M'] in
/-- **The read program of a moded mixed program is moded, on the policies' ports**: as
Moded's `modedP_toReads`, every call is moreover a sponge call or a read with a tag's policy. -/
theorem modedP_toReads_policy
    (upd : Caller → HashDomain → Finset Sx × M' → Option HashOutput → Finset Sx × M')
    (rl : Finset Sx × M' → HashDomain → Option HashOutput) (hrec : ∀ c z, RecordsAt rl z (upd c z))
    {Ω : QReg → Type} {fin : (Σ u, Ω u) → Option (Finset Sx × M') → Prop}
    (hfin : ∀ p, fin p none) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A)
    (μ : Option (Finset Sx × M')) (hx : ModedP okM (nxM upd rl) fin μ x) :
    ModedP (fun μ i ↦ OkD rl μ i ∧ (μ ≠ none → PolicyPort upd i)) (nxD rl) fin μ
      (readProgOf upd x) := by
  rw [readProgOf, ← IFreeM.substitute_toSubstitution, Quantum.Xmss.Assembly.substitute_substitute]
  refine modedP_substitute _ none (fun i ↦ ⟨trivial, fun h ↦ absurd rfl h⟩) (nxD_none rl)
    (fun A c μ _ ↦ ?_) hfin x μ hx
  rcases c with o | ⟨p | ⟨tag, n | z⟩, E, ℓ⟩
  · moded_step
    · trivial
    · exact Or.inl rfl
  · moded_step
    · exact ⟨okD_sponge rl μ _, fun _ ↦ trivial⟩
    · exact Or.inl (nxD_sponge rl μ _ _)
  · moded_step
    · trivial
    moded_step
    · trivial
    exact Or.inl rfl
  · moded_step
    · trivial
    moded_step
    · exact ⟨okD_readH rl μ z _ (hrec tag z), fun _ ↦ ⟨tag, rfl⟩⟩
    moded_step
    · trivial
    exact nxD_readH rl μ z _ _

open scoped Classical in
/-- **The property game of a straight-line reduction in the QROM, graded with a live budget and
additive costs.** Let the read policies `upd` log every outcome (`rl`), let the live runs of the
mixed game carry the invariants of `modedP_mixGame`, every run ending in a memory of budget
measure `β ≤ nB` and every winning run in a memory of `Won`, and let the event `S` contain the
registers with memory in `Won` and miss the start. The live memories keep `Inv`, and a call on a
live memory `m` raises `β` by at least its live charge `κB m i`. If every allowed call on a live
memory raises the square root of the event weight by `(κ i + κB m i) √(η tr σ)` and the weight by
`d i σ`, and the read program is within the charge `n` of `κ`, then the success is at most
`((n + nB) √η + √(∑ d))²`. -/
theorem probAvg_game_slRed_le_moded_budget {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type}
    {R' : OracleSpec.{0, 0} Q'} {St Pub Out : Type} (E : Experiment romWorld R' Pub Out)
    {S0 F : Type} (pre : Pub → OracleComp (romWorld.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler romWorld R R' St)
    (post : Pub → S0 → F → St → OracleComp (romWorld.Oracles + R') Out)
    (upd : Caller → HashDomain → Finset Sx × M' → Option HashOutput → Finset Sx × M')
    (rl : Finset Sx × M' → HashDomain → Option HashOutput)
    (hrec : ∀ c z, RecordsAt rl z (upd c z)) (m₀ : Finset Sx × M') (hrl : ∀ z, rl m₀ z = none)
    (I0 : E.State → Option (Finset Sx × M') → Prop)
    (h0 : ∀ s μ, LiveRun rl (upd .setup) E.setup (some m₀) s μ → I0 s μ)
    (J : E.State → S0 → St × QueryLog R' → Option (Finset Sx × M') → Prop)
    (hpre : ∀ s μ, I0 s μ → ∀ a μ', LiveRedRun rl upd (E.answer s) (pre (E.pub s)) [] μ a μ' →
      J s a.1 (st0 (E.pub s) a.1, a.2) μ')
    (hσ : ∀ s a st log μ q, J s a (st, log) μ → ∀ r μ',
      LiveRedRun rl upd (E.answer s) (σ (E.pub s) st q) log μ r μ' → J s a (r.1.2, r.2) μ')
    (Ipost : E.State → Out × QueryLog R' → Option (Finset Sx × M') → Prop)
    (hpost : ∀ s a f st log μ, J s a (st, log) μ → ∀ r μ',
      LiveRedRun rl upd (E.answer s) (post (E.pub s) a f st) log μ r μ' → Ipost s r μ')
    (Won : Set (Finset Sx × M')) (β : Finset Sx × M' → ℕ) (nB : ℕ)
    (hjudge : ∀ s r μ, Ipost s r μ → ∀ b μ', LiveRun rl (upd .judge) (E.judge s r.2 r.1) μ b μ' →
      ∀ m, μ' = some m → β m ≤ nB ∧ (b = true → m ∈ Won))
    (S : Set (RomReg HashDomain HashOutput (Finset Sx × M'))) [DecidablePred (· ∈ S)]
    (hE : ∀ s : RomReg HashDomain HashOutput (Finset Sx × M'), s.2.2 ∈ Won → s ∈ S)
    (hS0 : potential (hwProjector S) (rhoMem0 m₀) = 0)
    (Inv : Finset Sx × M' → Prop) (hInv0 : Inv m₀)
    (hInv : ∀ m i r m', OkD rl (some m) i → PolicyPort upd i → Inv m →
      nxD rl (some m) i r = some m' → Inv m')
    (κ : (hwSpec HashOutput HashDomain (Finset Sx × M')).Port → ℕ)
    (κB : Finset Sx × M' → (hwSpec HashOutput HashDomain (Finset Sx × M')).Port → ℕ)
    (hβ : ∀ m i r m', OkD rl (some m) i → PolicyPort upd i →
      nxD rl (some m) i r = some m' → κB m i + β m ≤ β m')
    (η : ℝ≥0∞)
    (d : ∀ i, Matrix ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
      RomReg HashDomain HashOutput (Finset Sx × M'))
      ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
        RomReg HashDomain HashOutput (Finset Sx × M')) ℂ → ℝ≥0∞)
    (hη : ∀ m i (τ : Matrix ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
        RomReg HashDomain HashOutput (Finset Sx × M'))
        ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
          RomReg HashDomain HashOutput (Finset Sx × M')) ℂ),
      OkD rl (some m) i → PolicyPort upd i → Inv m → τ.PosSemidef → DSupp rl id (some m) τ →
      ∑' r, (if nxD rl (some m) i r = none ∨ ∃ m', nxD rl (some m) i r = some m' ∧ nB < β m'
          then 0 else
          potential (hwProjector S) (((runtime2 HashOutput HashDomain m₀).step i).branch r τ)) ≤
        (potential (hwProjector S) τ ^ (2⁻¹ : ℝ) +
          (κ i * (η * ENNReal.ofReal τ.trace.re) ^ (2⁻¹ : ℝ) +
            κB m i * (η * ENNReal.ofReal τ.trace.re) ^ (2⁻¹ : ℝ))) ^ 2 + d i τ)
    {n : ℕ} (hn : IFreeM.IsChargeBound (readProgOf upd (mixGame E pre adv st0 σ post))
      (portCharge κ) n) :
    romWorld.probAvg (E.game fun p ↦ slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (((n : ℝ≥0∞) + nB) * η ^ (2⁻¹ : ℝ) + ((runtime2 HashOutput HashDomain m₀).totalWeight
        .instruments d (readProgOf upd (mixGame E pre adv st0 σ post)) (rhoMem0 m₀)) ^
          (2⁻¹ : ℝ)) ^ 2 := by
  set x := readProgOf upd (mixGame E pre adv st0 σ post)
  set fin : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → Option (Finset Sx × M') → Prop :=
    fun p μ ↦ μ = none ∨ ∀ m, μ = some m → β m ≤ nB ∧ (p.2.2 = true → m ∈ Won)
  have hmix := modedP_mixGame upd rl E pre adv st0 σ post m₀ I0 h0 J hpre hσ Ipost hpost
    (fun b μ ↦ μ = none ∨ ∀ m, μ = some m → β m ≤ nB ∧ (b = true → m ∈ Won))
    (fun s r μ hI b μ' hr ↦ Or.inr (hjudge s r μ hI b μ' hr))
  have hx : ModedP (fun μ i ↦ OkD rl μ i ∧ (μ ≠ none → PolicyPort upd i)) (nxD rl) fin
      (some m₀) x :=
    modedP_toReads_policy upd rl hrec (fun _ ↦ Or.inl rfl) _ _ hmix
  have hρ : (rhoMem0 m₀).PosSemidef :=
    ((SubState.basis ()).prod (runtime2 HashOutput HashDomain m₀).init).posSemidef
  have htr : ENNReal.ofReal (rhoMem0 m₀).trace.re ≤ 1 := by
    change ENNReal.ofReal ((SubState.basis ()).matrix ⊗ₖ
      (runtime2 HashOutput HashDomain m₀).init.matrix).trace.re ≤ 1
    rw [← SubState.matrix_prod]
    exact ENNReal.ofReal_le_one.mpr
      ((SubState.basis ()).prod (runtime2 HashOutput HashDomain m₀).init).trace_re_le_one
  have hwin := evalDistMap_le_eventWeight_moded (X := HashOutput) (Z := HashDomain) rl id m₀ hrl
    (fun _ _ h ↦ h.1) (fun _ _ _ _ ↦ rfl) S Won hE x (some m₀) rfl hx
    (fun p μ h hp m hm ↦ by
      rcases h with h | h
      · rw [h] at hm
        cases hm
      · exact (h m hm).2 hp)
  set doom : Option (Finset Sx × M') → Prop :=
    fun μ ↦ μ = none ∨ ∃ m', μ = some m' ∧ nB < β m' with hdoom
  set bud : Option (Finset Sx × M') → ℕ := fun μ ↦ μ.elim 0 fun m ↦ nB - β m
  set κB' : Option (Finset Sx × M') → (hwSpec HashOutput HashDomain (Finset Sx × M')).Port →
    ℕ := fun μ i ↦ μ.elim 0 fun m ↦ κB m i
  set CInv : Option (Finset Sx × M') → Set (RomReg HashDomain HashOutput (Finset Sx × M')) :=
    fun μ ↦ {_s | ∀ m, μ = some m → Inv m}
  have hsq := rpow_inv_two_tsum_potential_runtime2_moded_add (rl := rl) (proj := id) m₀
    (ok := fun μ i ↦ OkD rl μ i ∧ (μ ≠ none → PolicyPort upd i)) (nx := nxD rl)
    (fun _ _ h ↦ h.1) (fun _ _ _ _ ↦ rfl) S doom
    (fun μ i r hi h ↦ by
      rcases h with h | ⟨m', rfl, hm'⟩
      · rw [h]
        exact Or.inl rfl
      · rcases hnx : nxD rl (some m') i r with _ | m''
        · exact Or.inl rfl
        · exact Or.inr ⟨m'', rfl, lt_of_lt_of_le hm'
            ((Nat.le_add_left _ _).trans (hβ m' i r m'' hi.1 (hi.2 (by simp)) hnx))⟩)
    κ κB' bud
    (fun μ i r hi hnd ↦ by
      rcases μ with _ | m
      · exact absurd (Or.inl rfl) hnd
      rcases hnx : nxD rl (some m) i r with _ | m'
      · exact absurd (Or.inl hnx) hnd
      have hb := hβ m i r m' hi.1 (hi.2 (by simp)) hnx
      have hm' : β m' ≤ nB := not_lt.mp fun h ↦ hnd (Or.inr ⟨m', hnx, h⟩)
      change κB m i + (nB - β m') ≤ nB - β m
      omega)
    η η CInv
    (fun μ i r τ hi hτ ↦ by
      by_cases hI : ∀ m, μ = some m → Inv m
      · have hI' : ∀ m', nxD rl μ i r = some m' → Inv m' := by
          intro m' hm'
          rcases μ with _ | m
          · cases hm'
          · exact hInv m i r m' hi.1 (hi.2 (by simp)) (hI m rfl) hm'
        exact fun _ _ _ ↦ ⟨hI', hI'⟩
      · have h0 : τ = 0 := by
          ext a b
          by_contra hab
          exact hI (hτ a b hab).1
        subst h0
        rw [map_zero]
        exact fun a b hab ↦ absurd (Matrix.zero_apply a b) hab)
    d
    (fun μ i τ hi hd hτ hs hc ↦ by
      rcases μ with _ | m
      · exact absurd (Or.inl rfl) hd
      · by_cases hIm : Inv m
        · refine le_trans (le_of_eq (tsum_congr fun r ↦ ?_))
            (hη m i τ hi.1 (hi.2 (by simp)) hIm hτ hs)
          split_ifs <;> rfl
        · have h0 : τ = 0 := by
            ext a b
            by_contra hab
            exact hIm ((hc a b hab).1 m rfl)
          subst h0
          refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun r ↦ ?_)) zero_le
          split_ifs
          · rfl
          · rw [map_zero]
            simp [potential])
    (fun p μ h hd ↦ by
      rcases hd with hd | ⟨m', rfl, hm'⟩
      · exact hd
      · rcases h with h | h
        · exact absurd h (by simp)
        · exact absurd (h m' rfl).1 (not_le.mpr hm'))
    .instruments x n hn (some m₀) hx hρ (dInv_init rl m₀ hrl _) (fun _ _ _ ↦ ⟨fun m hm ↦ by
      cases hm
      exact hInv0, fun m hm ↦ by cases hm; exact hInv0⟩)
  simp only [hS0, zero_add] at hsq
  refine (probAvg_game_slRed_le_hw E pre adv st0 σ post upd m₀).trans (hwin.trans ?_)
  refine (le_of_eq (eventWeight_eq_tsum_potential (runtime2 HashOutput HashDomain m₀)
    .instruments (hwProjector S) x (rhoMem0 m₀))).trans ?_
  refine (le_of_eq (sq_rpow_inv_two _).symm).trans ?_
  refine pow_le_pow_left₀ zero_le (hsq.trans ?_) 2
  have hη1 : (η * ENNReal.ofReal (rhoMem0 m₀).trace.re) ^ (2⁻¹ : ℝ) ≤ η ^ (2⁻¹ : ℝ) := by
    gcongr
    calc η * ENNReal.ofReal (rhoMem0 m₀).trace.re ≤ η * 1 := by gcongr
      _ = η := mul_one η
  have hb : (bud (some m₀) : ℝ≥0∞) ≤ nB := by
    exact_mod_cast Nat.sub_le nB (β m₀)
  rw [add_mul]
  gcongr

end assembly

end Quantum.StdModel.Qrom

/-! ## EncTCR$: the event, the policies and the cost of every call -/

namespace Quantum.StdModel.Qrom.EncSalt

open Quantum QuantumRuntime Quantum.Sponge Quantum.Qrom HashSig Props
open Quantum.Xmss.Hybrid (runtime2 runtime2_branch kraus2)
open Tcr (Mem IsG Recordless BadR uRed uJudge KeepsRecs keepsRecs_uRed keepsRecs_uJudge)

section policy

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- **Every tweak is a challenge tweak**: the classes of the event are the encoding cells of a
parameter and a tweak. -/
def G : Unit → Tw → Prop := fun _ _ ↦ True

open scoped Classical in
/-- **The challenger's answers**: log the outcome; a codeword outcome at an encoding cell of a
class without a record becomes its record (the selected digest). -/
noncomputable def uSel (z : HashDomain) (m : Mem) (o : Option HashOutput) : Mem :=
  (m.1, Function.update m.log z o, m.seen,
    if IsG e.hash G z ∧ Recordless e.hash G m z ∧
        ∃ v, o = some v ∧ e.isCode (e.hash.trunc v) = true then
      Function.update m.recs z (some (o.getD 0))
    else m.recs, m.slot)

/-- **The policy of each caller**: the answers select, the reduction and the setup log and mark,
the decision also fills the slot. -/
noncomputable def upd : Caller → HashDomain → Mem → Option HashOutput → Mem
  | .setup => uRed
  | .answer => uSel e
  | .judge => uJudge
  | .red => uRed

theorem recordsAt_upd (c : Caller) (z : HashDomain) : RecordsAt Tcr.rl z (upd e c z) := by
  intro m o
  cases c <;> rfl

/-- **The static charges**: a sponge call. -/
def κA (i : (hwSpec HashOutput HashDomain Mem).Port) : ℕ :=
  if hwCls i then 0 else 1

open scoped Classical in
/-- **The live charges**: a read of an encoding cell by the reduction or the setup not read by
them before, and a read of an encoding cell by the decision not read before or filling the
slot. -/
noncomputable def κB (m : Mem) : (hwSpec HashOutput HashDomain Mem).Port → ℕ
  | .inl (.inr (.readH z u)) => if IsG e.hash G z ∧ ((u = uRed z ∧ m.seen z = false) ∨
      (u = uJudge z ∧ (m.seen z = false ∨ m.slot = none))) then 1 else 0
  | _ => 0

open scoped Classical in
/-- **The budget measure**: the encoding cells read by the reduction, the setup or the decision,
and the filled slot. -/
noncomputable def βS (m : Mem) : ℕ :=
  (Finset.univ.filter fun z ↦ IsG e.hash G z ∧ m.seen z = true).card +
    if m.slot = none then 0 else 1

/-- **The live memories' invariant**: every cell read by the reduction, the setup or the decision
is in the log. -/
def InvS (m : Mem) : Prop :=
  ∀ z, m.seen z = true → m.log z ≠ none

open scoped Classical in
/-- **The additive costs**: the refined cost of every read other than the reduction's, the
setup's and the decision's (the challenger's trial reads). -/
noncomputable def dS : ∀ i : (hwSpec HashOutput HashDomain Mem).Port,
    Matrix ((hwSpec HashOutput HashDomain Mem).In i × RomReg HashDomain HashOutput Mem)
      ((hwSpec HashOutput HashDomain Mem).In i × RomReg HashDomain HashOutput Mem) ℂ → ℝ≥0∞
  | .inl (.inr (.readH z u)), σ =>
      if u = uRed z ∨ u = uJudge z then 0 else
        ENNReal.ofReal (∑ q, readLin (BadR e.hash G) z u q * (σ q q).re)
  | _, _ => 0

variable {e}

theorem keepsRecs_of_red {z : HashDomain} {u : Mem → Option HashOutput → Mem}
    (h : u = uRed z ∨ u = uJudge z) : KeepsRecs z u := by
  rcases h with rfl | rfl
  · exact keepsRecs_uRed z
  · exact keepsRecs_uJudge z

/-- A memory move keeping the records and the slot keeps the event. -/
theorem badR_congr_mem {s : RomReg HashDomain HashOutput Mem} {m' : Mem}
    (hr : m'.recs = s.2.2.recs) (hsl : m'.slot = s.2.2.slot) :
    ((s.1, s.2.1, m') : RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔
      s ∈ BadR e.hash G := by
  have ht : Tcr.tgt e.hash G s.2.1 m' = Tcr.tgt e.hash G s.2.1 s.2.2 := Tcr.tgt_congr hr _ _
  constructor
  · rintro (⟨x, y, hxy, hy⟩ | ⟨z', y, hs', hy⟩)
    · exact Or.inl ⟨x, y, hxy, by rw [← ht]; exact hy⟩
    · refine Or.inr ⟨z', y, hsl ▸ hs', ?_⟩
      change y ∈ Tcr.tgt e.hash G s.2.1 m' z' at hy
      rw [ht] at hy
      exact hy
  · rintro (⟨x, y, hxy, hy⟩ | ⟨z', y, hs', hy⟩)
    · exact Or.inl ⟨x, y, hxy, by change y ∈ Tcr.tgt e.hash G s.2.1 m' x; rw [ht]; exact hy⟩
    · refine Or.inr ⟨z', y, hsl.trans hs', ?_⟩
      change y ∈ Tcr.tgt e.hash G s.2.1 m' z'
      rw [ht]
      exact hy

open scoped Classical in
/-- **The cost of every call allowed on a live memory**: a sponge call and a read charged live
cost `√(gradeEta F · tr)`; any other read of the reduction, the setup or the decision costs
nothing (off the encoding cells, or a re-read of a logged cell keeping the slot); every other
read adds its refined cost. -/
theorem tsum_potential_step_salt {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F) (m₀ m : Mem)
    (i : (hwSpec HashOutput HashDomain Mem).Port)
    (τ : Matrix ((hwSpec HashOutput HashDomain Mem).In i × RomReg HashDomain HashOutput Mem)
      ((hwSpec HashOutput HashDomain Mem).In i × RomReg HashDomain HashOutput Mem) ℂ)
    (hi : OkD Tcr.rl (some m) i) (hI : InvS m) (hτ : τ.PosSemidef)
    (hs : DSupp Tcr.rl id (some m) τ) :
    ∑' r, potential (hwProjector (BadR e.hash G))
          (((runtime2 HashOutput HashDomain m₀).step i).branch r τ) ≤
      (potential (hwProjector (BadR e.hash G)) τ ^ (2⁻¹ : ℝ) +
        (κA i * (ENNReal.ofReal (gradeEta HashOutput F) * ENNReal.ofReal τ.trace.re) ^
          (2⁻¹ : ℝ) + κB e m i * (ENNReal.ofReal (gradeEta HashOutput F) *
            ENNReal.ofReal τ.trace.re) ^ (2⁻¹ : ℝ))) ^ 2 + dS e i τ := by
  have hbr : ∀ r, ((runtime2 HashOutput HashDomain m₀).step i).branch r τ =
      MatrixMap.conj (kraus2 HashOutput HashDomain m₀ i r) τ := fun r ↦
    LinearMap.congr_fun (runtime2_branch m₀ i r) τ
  simp only [hbr]
  rcases i with (p | c) | c
  · change ∑' r : Unit, _ ≤ _
    rw [tsum_eq_single () fun r hr ↦ absurd (Subsingleton.elim r ()) hr]
    have h := Tcr.potential_sponge_badR_le (C := e.hash) (G := G) hF m₀ p hτ
    have h2 := pow_le_pow_left₀ (by positivity) h 2
    rw [sq_rpow_inv_two] at h2
    refine h2.trans ?_
    change _ ≤ (_ + (((1 : ℕ) : ℝ≥0∞) * _ + ((0 : ℕ) : ℝ≥0∞) * _)) ^ 2 + 0
    simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero]
    exact le_rfl
  · have hκA : κA (.inl (.inr c) : (hwSpec HashOutput HashDomain Mem).Port) = 0 := rfl
    rw [hκA, Nat.cast_zero, zero_mul, zero_add]
    cases c with
    | readH z u =>
      have hbr' : ∀ r, MatrixMap.conj (kraus2 HashOutput HashDomain m₀ (.inl (.inr (.readH z u))) r)
          τ = MatrixMap.conj (hwReadKraus (.readH z u) r) τ := fun _ ↦ rfl
      simp only [hbr']
      by_cases hu : u = uRed z ∨ u = uJudge z
      · have hd : dS e (.inl (.inr (.readH z u))) τ = 0 := by simp [dS, hu]
        rw [hd, add_zero]
        have hk := keepsRecs_of_red hu
        by_cases hz : IsG e.hash G z
        · by_cases hch : (u = uRed z ∧ m.seen z = false) ∨
              (u = uJudge z ∧ (m.seen z = false ∨ m.slot = none))
          · have hκ : κB e m (.inl (.inr (.readH z u))) = 1 := by simp [κB, hz, hch]
            rw [hκ, Nat.cast_one, one_mul, ← ENNReal.ofReal_mul (gradeEta_nonneg _ _)]
            exact Tcr.tsum_potential_read_badR hF hτ (readNoBot_of_dSupp rfl hs _)
              fun q _ ↦ Or.inl (hk q.2.2.2)
          · have hκ : κB e m (.inl (.inr (.readH z u))) = 0 := by simp [κB, hch]
            rw [hκ, Nat.cast_zero, zero_mul, add_zero, sq_rpow_inv_two]
            have hseen : m.seen z = true := by
              rcases hu with rfl | rfl
              · simpa using fun h ↦ hch (Or.inl ⟨rfl, h⟩)
              · simpa using fun h ↦ hch (Or.inr ⟨rfl, Or.inl h⟩)
            obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hI z hseen)
            refine tsum_potential_readH_logged (BadR e.hash G) z u m v hτ ?_ fun s hsm ↦ ?_
            · unfold DSupp at hs
              exact hs.imp fun s hs' ↦ ⟨hs'.2.2.2 z v hv, hs'.2.1, hs'.1⟩
            · refine badR_congr_mem (s := s) ?_ ?_
              · rw [hsm]
                exact (hk m (some v)).1
              · rw [hsm]
                rcases hu with rfl | rfl
                · rfl
                · have hsl : m.slot ≠ none := fun h ↦ hch (Or.inr ⟨rfl, Or.inr h⟩)
                  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hsl
                  change m.slot.or _ = m.slot
                  rw [hp]
                  rfl
        · have hκ : κB e m (.inl (.inr (.readH z u))) = 0 := by simp [κB, hz]
          have h0 := readFlip_eq_zero (BadR e.hash G) (Tcr.readInvisible_badR hz hk) τ hτ
          unfold readFlip at h0
          rw [tsub_eq_zero_iff_le] at h0
          rw [hκ, Nat.cast_zero, zero_mul, add_zero, sq_rpow_inv_two]
          exact h0
      · have hd : dS e (.inl (.inr (.readH z u))) τ =
            ENNReal.ofReal (∑ q, readLin (BadR e.hash G) z u q * (τ q q).re) := by
          simp [dS, hu]
        have hκ : κB e m (.inl (.inr (.readH z u))) = 0 := by
          simp only [κB]
          rw [ite_eq_right]
          rintro ⟨-, h | h⟩
          · exact hu (Or.inl h.1)
          · exact hu (Or.inr h.1)
        rw [hd, hκ, Nat.cast_zero, zero_mul, add_zero, sq_rpow_inv_two]
        exact (potential_hwReadKraus_le_refined (BadR e.hash G) (.readH z u) hτ
          (readNoBot_of_dSupp rfl hs _)).trans
            (add_le_add le_rfl (readCost_readH_le (BadR e.hash G) z u hτ))
    | readK _ _ => exact absurd hi id
    | readK' _ _ => exact absurd hi id
  · exact absurd hi id

end policy

/-! ## The live runs: a win is in the event -/

section live

open OracleComp OracleSpec
open Tcr (SameCls GCell GSep gCell_unique rl liveRun_pure liveRun_bind liveRun_hashQ
  liveRun_noHash liveRun_query hashW)

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- The cell of the encoding input `(P, t, d)`. -/
noncomputable def cell (P : Par) (t : Tw) (d : Msg × Salt) : HashDomain :=
  (encodeInput (e.hash.layout () P t d)).getD 0

/-- The transcripts of EncTCR$. -/
abbrev SLog (Tw Msg Salt Dig : Type) := QueryLog (Tw × Msg →ₒ Option (Salt × Dig))

/-- **The invariant of a live memory** against the transcript `log` at the parameter `P`: an
empty slot; at most one record per class; every record at a cell of a logged tweak; and on a
transcript with distinct tweaks, every answered target's record at its selected cell, with the
answered digest. -/
def RecInv (P : Par) (log : SLog Tw Msg Salt Dig) (m : Mem) : Prop :=
  m.slot = none ∧
  (∀ y y', (m.recs y).isSome → (m.recs y').isSome → SameCls e.hash G y y' → y = y') ∧
  (∀ y v, m.recs y = some v → ∃ x ∈ log, ∃ d, y = cell e P x.1.1 d) ∧
  ((log.map fun x ↦ x.1.1).Nodup → ∀ x ∈ log, ∀ ρ D, x.2 = some (ρ, D) →
    ∃ v, m.recs (cell e P x.1.1 (x.1.2, ρ)) = some v ∧ e.hash.trunc v = D)

/-- The invariant of a live mode. -/
def LiveInv (P : Par) (log : SLog Tw Msg Salt Dig) (μ : Option Mem) : Prop :=
  ∀ m, μ = some m → RecInv e P log m

variable {e}

theorem encodeInput_cell (hlen : e.hash.LengthLe maxLen) (P : Par) (t : Tw) (d : Msg × Salt) :
    encodeInput (e.hash.layout () P t d) = some (cell e P t d) := by
  rw [cell, encodeInput_of_length_le (hlen _ _ _ _)]
  rfl

theorem gCell_cell (hlen : e.hash.LengthLe maxLen) (P : Par) (t : Tw) (d : Msg × Salt) :
    GCell e.hash G (cell e P t d) P t :=
  ⟨(), d, trivial, encodeInput_cell hlen P t d⟩

theorem isG_cell (hlen : e.hash.LengthLe maxLen) (P : Par) (t : Tw) (d : Msg × Salt) :
    IsG e.hash G (cell e P t d) :=
  ⟨P, t, gCell_cell hlen P t d⟩

theorem sameCls_cell (hlen : e.hash.LengthLe maxLen) (P : Par) (t : Tw) (d d' : Msg × Salt) :
    SameCls e.hash G (cell e P t d) (cell e P t d') :=
  ⟨P, t, gCell_cell hlen P t d, gCell_cell hlen P t d'⟩

/-- Two cells of the same class at the parameter `P` have the same tweak. -/
theorem tweak_eq_of_sameCls (hs : GSep e.hash G) (hlen : e.hash.LengthLe maxLen) {P : Par}
    {t t' : Tw} {d d' : Msg × Salt} (h : SameCls e.hash G (cell e P t d) (cell e P t' d')) :
    t = t' := by
  obtain ⟨P'', t'', h₁, h₂⟩ := h
  obtain ⟨-, e₁⟩ := gCell_unique hs (gCell_cell hlen P t d) h₁
  obtain ⟨-, e₂⟩ := gCell_unique hs (gCell_cell hlen P t' d') h₂
  exact e₁.symm.trans e₂

/-- The class of a tweak not in the transcript has no record. -/
theorem recordless_of_notMem (hs : GSep e.hash G) (hlen : e.hash.LengthLe maxLen) {P : Par}
    {log : SLog Tw Msg Salt Dig} {m : Mem} (hI : RecInv e P log m) {t : Tw}
    (ht : t ∉ log.map fun x ↦ x.1.1) (d : Msg × Salt) : Recordless e.hash G m (cell e P t d) := by
  intro x hx
  rcases hv : m.recs x with _ | v
  · rfl
  · obtain ⟨x', hx', d', rfl⟩ := hI.2.2.1 x v hv
    exact absurd (List.mem_map.2 ⟨x', hx', tweak_eq_of_sameCls hs hlen hx⟩) ht

open scoped Classical in
theorem uSel_recs (z : HashDomain) (m : Mem) (o : Option HashOutput) :
    (uSel e z m o).recs = if IsG e.hash G z ∧ Recordless e.hash G m z ∧
        ∃ v, o = some v ∧ e.isCode (e.hash.trunc v) = true then
      Function.update m.recs z (some (o.getD 0)) else m.recs :=
  rfl

/-- **The answers keep one record per class.** -/
theorem uSel_unique {z : HashDomain} {m : Mem} {o : Option HashOutput}
    (h : ∀ y y', (m.recs y).isSome → (m.recs y').isSome → SameCls e.hash G y y' → y = y') :
    ∀ y y', ((uSel e z m o).recs y).isSome → ((uSel e z m o).recs y').isSome →
      SameCls e.hash G y y' → y = y' := by
  rw [uSel_recs]
  split_ifs with hc
  · obtain ⟨-, hrl, -⟩ := hc
    intro y y' hy hy' hyy'
    by_cases hyz : y = z
    · by_cases hy'z : y' = z
      · rw [hyz, hy'z]
      · rw [Function.update_of_ne hy'z] at hy'
        rw [hyz] at hyy'
        rw [hrl y' hyy'.symm] at hy'
        cases hy'
    · rw [Function.update_of_ne hyz] at hy
      by_cases hy'z : y' = z
      · rw [hy'z] at hyy'
        rw [hrl y hyy'] at hy
        cases hy
      · rw [Function.update_of_ne hy'z] at hy'
        exact h y y' hy hy' hyy'
  · exact h

/-- A live run from the dead mode stays dead. -/
theorem liveRun_none {u : HashDomain → Mem → Option HashOutput → Mem} {α : Type}
    (oa : OracleComp romWorld.Oracles α) {a : α} {μ' : Option Mem}
    (h : LiveRun rl u oa none a μ') : μ' = none := by
  induction oa using OracleComp.inductionOn with
  | pure a' => exact (liveRun_pure h).2
  | query_bind t k ih =>
    unfold LiveRun at h
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at h
    obtain ⟨⟨w, μ1⟩, h1, h2⟩ := h
    have hμ1 : μ1 = none := by
      rcases t with n | z
      · change (w, μ1) ∈ support ((fun b ↦ (b, (none : Option Mem))) <$>
          (liftM (romWorld.Oracles.query (.inl n)) : OracleComp romWorld.Oracles _)) at h1
        simp only [support_map, Set.mem_image, Prod.mk.injEq] at h1
        obtain ⟨w', -, -, hμ⟩ := h1
        exact hμ.symm
      · change (w, μ1) ∈ support ((fun v ↦ (v, stepRd rl (u z) z none v)) <$>
          (liftM (romWorld.Oracles.query (.inr z)) : OracleComp romWorld.Oracles _)) at h1
        rw [liveRun_query (u := u) (x := z) (w := w) (μ := none) (μ' := μ1) h1]
        rfl
    rw [hμ1] at h2
    exact ih w h2

/-- **A live grind at a class without a record**: it records nothing and fails, or records the
selected cell with its value and answers the salt and the value's digest. -/
theorem liveRun_grind (hlen : e.hash.LengthLe maxLen) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) :
    ∀ (n c : ℕ) (μ : Option Mem) (a : Option (Salt × Dig)) (μ' : Option Mem),
      LiveRun rl (upd e .answer) (e.grind romWorld P t M r0 c n) μ a μ' →
      ∀ m, μ = some m → (∀ d, Recordless e.hash G m (cell e P t d)) → ∀ m', μ' = some m' →
        m'.slot = m.slot ∧ ((a = none ∧ m'.recs = m.recs) ∨
          ∃ ρ v, a = some (ρ, e.hash.trunc v) ∧
            m'.recs = Function.update m.recs (cell e P t (M, ρ)) (some v)) := by
  intro n
  induction n with
  | zero =>
    intro c μ a μ' h m hm _ m' hm'
    obtain ⟨rfl, rfl⟩ := liveRun_pure h
    rw [hm] at hm'
    cases hm'
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | succ n ih =>
    intro c μ a μ' h m hm hrl m' hm'
    obtain ⟨dg, μ1, h1, h2⟩ := liveRun_bind h
    obtain ⟨v, rfl, rfl⟩ := liveRun_hashQ e.hash.trunc
      (encodeInput_cell hlen P t (M, e.shift r0 c)) h1
    subst hm
    by_cases hbad : (rl m (cell e P t (M, e.shift r0 c))).isSome ∧
        rl m (cell e P t (M, e.shift r0 c)) ≠ some v
    · have h0 : stepRd rl (upd e .answer (cell e P t (M, e.shift r0 c)))
          (cell e P t (M, e.shift r0 c)) (some m) v = none := by
        simp only [stepRd]
        rw [ite_eq_left hbad]
      rw [h0] at h2
      rw [liveRun_none _ h2] at hm'
      cases hm'
    have h0 : stepRd rl (upd e .answer (cell e P t (M, e.shift r0 c)))
        (cell e P t (M, e.shift r0 c)) (some m) v =
          some (uSel e (cell e P t (M, e.shift r0 c)) m (some v)) := by
      simp only [stepRd]
      rw [ite_eq_right hbad]
      rfl
    rw [h0] at h2
    have hz := isG_cell hlen P t (M, e.shift r0 c)
    by_cases hcode : e.isCode (e.hash.trunc v) = true
    · simp only [hcode, ↓reduceIte] at h2
      obtain ⟨rfl, rfl⟩ := liveRun_pure h2
      cases hm'
      refine ⟨rfl, Or.inr ⟨e.shift r0 c, v, rfl, ?_⟩⟩
      rw [uSel_recs, ite_eq_left ⟨hz, hrl _, v, rfl, hcode⟩]
      rfl
    · simp only [hcode, ↓reduceIte, Bool.false_eq_true] at h2
      have hrec : (uSel e (cell e P t (M, e.shift r0 c)) m (some v)).recs = m.recs := by
        rw [uSel_recs, ite_eq_right fun hc ↦ ?_]
        obtain ⟨-, -, v', hv', hc'⟩ := hc
        cases hv'
        exact hcode hc'
      have hrl' : ∀ d, Recordless e.hash G (uSel e (cell e P t (M, e.shift r0 c)) m (some v))
          (cell e P t d) := fun d x hx ↦ by
        rw [hrec]
        exact hrl d x hx
      obtain ⟨hsl, h⟩ := ih (c + 1) _ a μ' h2 _ rfl hrl' m' hm'
      refine ⟨hsl, ?_⟩
      rw [hrec] at h
      exact h

/-- **Any live grind** keeps the slot and the old records, keeps one record per class, and adds
records only at cells of its tweak. -/
theorem liveRun_grind_any (hlen : e.hash.LengthLe maxLen) (P : Par) (t : Tw)
    (M : Msg) (r0 : Salt) :
    ∀ (n c : ℕ) (μ : Option Mem) (a : Option (Salt × Dig)) (μ' : Option Mem),
      LiveRun rl (upd e .answer) (e.grind romWorld P t M r0 c n) μ a μ' →
      ∀ m, μ = some m → ∀ m', μ' = some m' →
        m'.slot = m.slot ∧ (∀ y v, m.recs y = some v → m'.recs y = some v) ∧
        (∀ y v, m'.recs y = some v → m.recs y = some v ∨ ∃ d, y = cell e P t d) ∧
        ((∀ y y', (m.recs y).isSome → (m.recs y').isSome → SameCls e.hash G y y' → y = y') →
          ∀ y y', (m'.recs y).isSome → (m'.recs y').isSome → SameCls e.hash G y y' → y = y') := by
  intro n
  induction n with
  | zero =>
    intro c μ a μ' h m hm m' hm'
    obtain ⟨rfl, rfl⟩ := liveRun_pure h
    rw [hm] at hm'
    cases hm'
    exact ⟨rfl, fun _ _ h ↦ h, fun _ _ h ↦ Or.inl h, id⟩
  | succ n ih =>
    intro c μ a μ' h m hm m' hm'
    obtain ⟨dg, μ1, h1, h2⟩ := liveRun_bind h
    set x := cell e P t (M, e.shift r0 c)
    obtain ⟨v, rfl, rfl⟩ := liveRun_hashQ e.hash.trunc (encodeInput_cell hlen P t (M, e.shift r0 c))
      h1
    subst hm
    by_cases hbad : (rl m x).isSome ∧ rl m x ≠ some v
    · have h0 : stepRd rl (upd e .answer x) x (some m) v = none := by
        simp only [stepRd]
        rw [ite_eq_left hbad]
      rw [h0] at h2
      rw [liveRun_none _ h2] at hm'
      cases hm'
    have h0 : stepRd rl (upd e .answer x) x (some m) v = some (uSel e x m (some v)) := by
      simp only [stepRd]
      rw [ite_eq_right hbad]
      rfl
    rw [h0] at h2
    set m1 := uSel e x m (some v)
    have hstep : m1.slot = m.slot ∧ (∀ y w, m.recs y = some w → m1.recs y = some w) ∧
        (∀ y w, m1.recs y = some w → m.recs y = some w ∨ ∃ d, y = cell e P t d) ∧
        ((∀ y y', (m.recs y).isSome → (m.recs y').isSome → SameCls e.hash G y y' → y = y') →
          ∀ y y', (m1.recs y).isSome → (m1.recs y').isSome → SameCls e.hash G y y' →
            y = y') := by
      have hxc : x = cell e P t (M, e.shift r0 c) := rfl
      refine ⟨rfl, fun y w hy ↦ ?_, fun y w hy ↦ ?_, uSel_unique⟩
      · change (uSel e x m (some v)).recs y = some w
        rw [uSel_recs]
        split_ifs with hc
        · by_cases hyx : y = x
          · rw [hyx, hc.2.1 x hc.1.sameCls_self] at hy
            cases hy
          · rw [Function.update_of_ne hyx]
            exact hy
        · exact hy
      · change (uSel e x m (some v)).recs y = some w at hy
        rw [uSel_recs] at hy
        split_ifs at hy with hc
        · by_cases hyx : y = x
          · exact Or.inr ⟨_, hyx.trans hxc⟩
          · rw [Function.update_of_ne hyx] at hy
            exact Or.inl hy
        · exact Or.inl hy
    by_cases hcode : e.isCode (e.hash.trunc v) = true
    · simp only [hcode, ↓reduceIte] at h2
      obtain ⟨rfl, rfl⟩ := liveRun_pure h2
      rw [(Option.some.inj hm').symm]
      exact hstep
    · simp only [hcode, ↓reduceIte, Bool.false_eq_true] at h2
      obtain ⟨s1, o1, n1, u1⟩ := ih (c + 1) _ a μ' h2 m1 rfl m' hm'
      obtain ⟨s0, o0, n0, u0⟩ := hstep
      refine ⟨s1.trans s0, fun y w hy ↦ o1 y w (o0 y w hy), fun y w hy ↦ ?_,
        fun h ↦ u1 (u0 h)⟩
      rcases n1 y w hy with h | h
      · exact n0 y w h
      · exact Or.inr h

/-- **The challenger's answers keep the invariant.** -/
theorem liveInv_answer [SampleableType Par] [SampleableType Salt] (hs : GSep e.hash G)
    (hlen : e.hash.LengthLe maxLen) {P : Par} {log : SLog Tw Msg Salt Dig} {μ μ' : Option Mem}
    (q : Tw × Msg) {a : Option (Salt × Dig)} (hI : LiveInv e P log μ)
    (h : LiveRun rl (upd e .answer) ((encTcrSalt romWorld e).answer P q) μ a μ') :
    LiveInv e P (log ++ [⟨q, a⟩]) μ' := by
  intro m' hm'
  obtain ⟨r0, μ1, h1, h2⟩ := liveRun_bind h
  have hμ1 : μ1 = μ := liveRun_noHash _
    (Common.isWeightBound_liftM_probComp hashW (fun _ ↦ rfl) _) h1
  subst hμ1
  rcases μ1 with _ | m
  · rw [liveRun_none _ h2] at hm'
    cases hm'
  obtain ⟨h0, hu, h2r, h3⟩ := hI m rfl
  obtain ⟨s', o', n', u'⟩ := liveRun_grind_any hlen P q.1 q.2 r0 e.limit 0 _ a _ h2 m rfl m'
    hm'
  refine ⟨s'.trans h0, u' hu, fun y v hy ↦ ?_, fun hnd x hx ρ D hxa ↦ ?_⟩
  · rcases n' y v hy with h | ⟨d, rfl⟩
    · obtain ⟨x, hx, d, rfl⟩ := h2r y v h
      exact ⟨x, List.mem_append_left _ hx, d, rfl⟩
    · exact ⟨⟨q, a⟩, List.mem_append_right _ (List.mem_singleton_self _), d, rfl⟩
  · rw [List.map_append, List.nodup_append] at hnd
    obtain ⟨hnd₁, -, hnd₃⟩ := hnd
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨v, hv, hdv⟩ := h3 hnd₁ x hx ρ D hxa
      exact ⟨v, o' _ v hv, hdv⟩
    · rw [List.mem_singleton] at hx
      subst hx
      have hq : q.1 ∉ log.map fun x ↦ x.1.1 := fun hq ↦
        hnd₃ q.1 hq q.1 (List.mem_singleton_self _) rfl
      obtain ⟨-, h⟩ := liveRun_grind hlen P q.1 q.2 r0 e.limit 0 _ _ _ h2 m rfl
        (recordless_of_notMem hs hlen ⟨h0, hu, h2r, h3⟩ hq) m' hm'
      rcases h with ⟨ha, -⟩ | ⟨ρ', v, ha, hv⟩
      · rw [ha] at hxa
        cases hxa
      · rw [ha] at hxa
        simp only [Option.some.injEq, Prod.mk.injEq] at hxa
        obtain ⟨rfl, rfl⟩ := hxa
        exact ⟨v, by rw [hv, Function.update_self], rfl⟩

/-- The reduction's own reads keep the invariant. -/
theorem liveInv_red {P : Par} {log : SLog Tw Msg Salt Dig} {μ μ' : Option Mem}
    {i : romWorld.Oracles.Domain} {y : romWorld.Oracles.Range i} (hI : LiveInv e P log μ)
    (h : (y, μ') ∈ support ((liveImpl rl (upd e .red) i).run μ)) : LiveInv e P log μ' := by
  rcases i with n | z
  · change (y, μ') ∈ support ((fun b ↦ (b, μ)) <$>
      (liftM (romWorld.Oracles.query (.inl n)) : OracleComp romWorld.Oracles _)) at h
    rw [support_map] at h
    obtain ⟨w, -, hw⟩ := h
    simp only [Prod.mk.injEq] at hw
    rw [← hw.2]
    exact hI
  · have hμ := liveRun_query (u := upd e .red) (x := z) (w := y) (μ := μ) (μ' := μ') h
    rw [hμ]
    intro m' hm'
    rcases μ with _ | m
    · cases hm'
    simp only [stepRd] at hm'
    split_ifs at hm'
    injection hm' with hm'
    subst hm'
    exact hI m rfl

/-- **The reduction's live runs keep an invariant** kept by its own reads and by the challenger's
answers. -/
theorem liveRedRun_inv {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (Inv : QueryLog R' → Option Mem → Prop)
    (hred : ∀ log μ i y μ', Inv log μ →
      (y, μ') ∈ support ((liveImpl rl (upd e .red) i).run μ) → Inv log μ')
    (hans : ∀ log μ q' a μ', Inv log μ → LiveRun rl (upd e .answer) (ans q') μ a μ' →
      Inv (log ++ [⟨q', a⟩]) μ') {α : Type} (oa : OracleComp (romWorld.Oracles + R') α) :
    ∀ log μ r μ', Inv log μ → LiveRedRun rl (upd e) ans oa log μ r μ' → Inv r.2 μ' := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro log μ r μ' hI h
    unfold LiveRedRun at h
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    obtain ⟨-, h1, h2⟩ := h
    rw [h1, h2]
    exact hI
  | query_bind t k ih =>
    intro log μ r μ' hI h
    unfold LiveRedRun at h
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at h
    obtain ⟨⟨a, log₁, μ₁⟩, h1, h2⟩ := h
    refine ih a log₁ μ₁ r μ' ?_ h2
    rcases t with i | q'
    · change (a, (log₁, μ₁)) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rl (upd e .red) i).run μ) at h1
      rw [support_map] at h1
      obtain ⟨⟨y, μ₂⟩, h3, h4⟩ := h1
      simp only [Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl, rfl⟩ := h4
      exact hred log μ i y μ₂ hI h3
    · change (a, (log₁, μ₁)) ∈ support ((fun p ↦ (p.1, (log ++ [⟨q', p.1⟩], p.2))) <$>
        (simulateQ (liveImpl rl (upd e .answer)) (ans q')).run μ) at h1
      rw [support_map] at h1
      obtain ⟨⟨y, μ₂⟩, h3, h4⟩ := h1
      simp only [Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl, rfl⟩ := h4
      exact hans log μ q' y μ₂ hI h3

/-- **The decision accepts only in a winning memory**: the judge's read at the forgery's cell has
the digest of the unique record of its class, at another cell. -/
theorem won_of_judge [SampleableType Par] [SampleableType Salt] (hs : GSep e.hash G)
    (hinj : ∀ P t, (e.hash.layout () P t).Injective) (hlen : e.hash.LengthLe maxLen) {P : Par}
    {log : SLog Tw Msg Salt Dig} (out : Tw × Msg × Salt) {μ μ' : Option Mem}
    (hI : LiveInv e P log μ)
    (h : LiveRun rl (upd e .judge) ((encTcrSalt romWorld e).judge P log out) μ true μ') :
    ∀ m, μ' = some m → m ∈ Tcr.Won e.hash G := by
  obtain ⟨dg, μ₁, h1, h2⟩ := liveRun_bind h
  obtain ⟨hb, hμ₁⟩ := liveRun_pure h2
  obtain ⟨v, rfl, hμv⟩ := liveRun_hashQ e.hash.trunc
    (encodeInput_cell hlen P out.1 (out.2.1, out.2.2)) h1
  rw [hμ₁, hμv]
  have hb' := hb.symm
  rw [holds_eq_true] at hb'
  obtain ⟨hval, x, hx, ρ, hxa, hxt, hne⟩ := hb'
  intro m' hm'
  rcases μ with _ | m
  · cases hm'
  simp only [stepRd] at hm'
  split_ifs at hm'
  injection hm' with hm'
  subst hm'
  obtain ⟨h0, hu, -, h3⟩ := hI m rfl
  obtain ⟨w, hw, hdw⟩ := h3 hval x hx ρ _ hxa
  have hcls : SameCls e.hash G (cell e P x.1.1 (x.1.2, ρ))
      (cell e P out.1 (out.2.1, out.2.2)) := by
    rw [hxt]
    exact sameCls_cell hlen P out.1 _ _
  refine ⟨cell e P out.1 (out.2.1, out.2.2), v, ?_, cell e P x.1.1 (x.1.2, ρ), w, hw, ?_, hcls,
    fun x' hx' hc ↦ hu x' _ hx' (by rw [hw]; rfl) (hc.trans hs hcls.symm), hdw.symm⟩
  · change m.slot.or _ = _
    rw [h0]
    rfl
  · intro heq
    rw [hxt] at heq
    have := hinj P out.1 (encodeInput_injective (encodeInput_cell hlen P out.1 (x.1.2, ρ))
      (heq ▸ encodeInput_cell hlen P out.1 (out.2.1, out.2.2)))
    exact hne (by rw [this])

end live

/-! ## The bound -/

section main

open OracleComp OracleSpec
open Tcr (GSep rl liveRun_bind liveRun_pure liveRun_hashQ liveRun_noHash hashW)

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- The start memory: no log, no cell read, no record, no judge's read. -/
def mem0 : Mem :=
  (∅, fun _ ↦ none, fun _ ↦ false, fun _ ↦ none, none)

/-- The read program of the EncTCR$ game played by a straight-line reduction. -/
noncomputable abbrev saltProg [SampleableType Par] [SampleableType Salt] {Q : Type}
    {R : OracleSpec.{0, 0} Q} {St S0 Fo : Type}
    (pre : Par → OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) S0)
    (adv : Par → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : Par → S0 → St) (σ : Par → HHandler romWorld R (Tw × Msg →ₒ Option (Salt × Dig)) St)
    (post : Par → S0 → Fo → St →
      OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) (Tw × Msg × Salt)) :=
  readProgOf (upd e) (mixGame (encTcrSalt romWorld e) pre adv st0 σ post)

/-- **Marking a cell read** adds it once to the count of marked cells of `P`. -/
theorem card_filter_update_true {α : Type} [Fintype α] [DecidableEq α] (P : α → Prop)
    [DecidablePred P] (s : α → Bool) (z : α) :
    (Finset.univ.filter fun y ↦ P y ∧ s y = true).card + (if P z ∧ s z = false then 1 else 0) ≤
      (Finset.univ.filter fun y ↦ P y ∧ Function.update s z true y = true).card ∧
    (Finset.univ.filter fun y ↦ P y ∧ Function.update s z true y = true).card ≤
      (Finset.univ.filter fun y ↦ P y ∧ s y = true).card + 1 := by
  have hsub : (Finset.univ.filter fun y ↦ P y ∧ s y = true) ⊆
      Finset.univ.filter fun y ↦ P y ∧ Function.update s z true y = true := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    refine ⟨hy.1, ?_⟩
    by_cases hyz : y = z
    · rw [hyz, Function.update_self]
    · rw [Function.update_of_ne hyz]
      exact hy.2
  refine ⟨?_, ?_⟩
  · split_ifs with h
    · have hz : z ∉ Finset.univ.filter fun y ↦ P y ∧ s y = true := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro _ hz
        rw [h.2] at hz
        exact Bool.false_ne_true hz
      rw [← Finset.card_insert_of_notMem hz]
      refine Finset.card_le_card (Finset.insert_subset ?_ hsub)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h.1, by rw [Function.update_self]⟩
    · rw [add_zero]
      exact Finset.card_le_card hsub
  · refine (Finset.card_le_card fun y hy ↦ ?_).trans (Finset.card_insert_le z _)
    rw [Finset.mem_insert]
    by_cases hyz : y = z
    · exact Or.inl hyz
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [Function.update_of_ne hyz] at hy
      exact Or.inr hy

variable {e}

open scoped Classical in
/-- **A read of the reduction or the setup** adds its cell once to the budget measure. -/
theorem βS_uRed (z : HashDomain) (m : Mem) (o : Option HashOutput) :
    (if IsG e.hash G z ∧ m.seen z = false then 1 else 0) + βS e m ≤ βS e (uRed z m o) ∧
      βS e (uRed z m o) ≤ βS e m + 1 := by
  obtain ⟨h1, h2⟩ := card_filter_update_true (IsG e.hash G) m.seen z
  unfold βS
  rw [show (uRed z m o).seen = Function.update m.seen z true from rfl]
  change _ ≤ _ + (if m.slot = none then 0 else 1) ∧
    _ + (if m.slot = none then 0 else 1) ≤ _
  constructor <;> omega

open scoped Classical in
/-- **A read off the encoding cells, or a re-read, keeps the budget measure.** -/
theorem βS_uRed_eq {z : HashDomain} {m : Mem} (h : ¬ IsG e.hash G z ∨ m.seen z = true)
    (o : Option HashOutput) : βS e (uRed z m o) = βS e m := by
  unfold βS
  rw [show (uRed z m o).seen = Function.update m.seen z true from rfl]
  have hc : (Finset.univ.filter fun y ↦ IsG e.hash G y ∧ Function.update m.seen z true y = true) =
      Finset.univ.filter fun y ↦ IsG e.hash G y ∧ m.seen y = true := by
    refine Finset.filter_congr fun y _ ↦ ?_
    by_cases hyz : y = z
    · subst hyz
      rw [Function.update_self]
      rcases h with h | h
      · exact ⟨fun h' ↦ absurd h'.1 h, fun h' ↦ absurd h'.1 h⟩
      · rw [h]
    · rw [Function.update_of_ne hyz]
  rw [hc]
  rfl

open scoped Classical in
/-- **A read of the decision** adds its cell once and fills the slot. -/
theorem βS_uJudge (z : HashDomain) (m : Mem) (v : HashOutput) :
    (if IsG e.hash G z ∧ m.seen z = false then 1 else 0) + (if m.slot = none then 1 else 0) +
        βS e m ≤ βS e (uJudge z m (some v)) ∧
      βS e (uJudge z m (some v)) ≤ βS e m + 2 := by
  obtain ⟨h1, h2⟩ := card_filter_update_true (IsG e.hash G) m.seen z
  have hsl : (uJudge z m (some v)).slot ≠ none := by
    change m.slot.or (some (z, v)) ≠ none
    cases m.slot <;> simp
  unfold βS
  rw [ite_eq_right hsl, show (uJudge z m (some v)).seen = Function.update m.seen z true from rfl]
  change _ + (if m.slot = none then 1 else 0) + (_ + if m.slot = none then 0 else 1) ≤ _ + 1 ∧
    _ + 1 ≤ _ + (if m.slot = none then 0 else 1) + 2
  split_ifs at h1 ⊢ <;> constructor <;> omega

theorem uRed_ne_uJudge (z : HashDomain) : uRed z ≠ uJudge z := fun h ↦ by
  have h' := congrArg Mem.slot (congrFun (congrFun h mem0) (some 0))
  change (none : Option (HashDomain × HashOutput)) = some (z, 0) at h'
  cases h'

theorem uSel_ne_uRed (z : HashDomain) : uSel e z ≠ uRed z := fun h ↦ by
  have h' := congrArg (fun m ↦ Mem.seen m z) (congrFun (congrFun h mem0) none)
  change false = Function.update (fun _ ↦ false) z true z at h'
  rw [Function.update_self] at h'
  cases h'

theorem uSel_ne_uJudge (z : HashDomain) : uSel e z ≠ uJudge z := fun h ↦ by
  have h' := congrArg (fun m ↦ Mem.seen m z) (congrFun (congrFun h mem0) none)
  change false = Function.update (fun _ ↦ false) z true z at h'
  rw [Function.update_self] at h'
  cases h'

open scoped Classical in
/-- **A live policy step raises the budget measure by its live charge.** -/
theorem κB_add_βS_le {m m' : Mem} {i : (hwSpec HashOutput HashDomain Mem).Port}
    {r : (hwSpec HashOutput HashDomain Mem).Result i} (hp : PolicyPort (upd e) i)
    (h : nxD rl (some m) i r = some m') : κB e m i + βS e m ≤ βS e m' := by
  rcases i with (p | c) | c
  · cases h
    exact le_of_eq (zero_add _)
  · cases c with
    | readH z u =>
      obtain ⟨c, rfl⟩ := hp
      rcases r with ⟨_ | v, w⟩
      · cases h
      obtain ⟨rfl, -⟩ := stepRd_some (rl := rl) h
      cases c with
      | answer =>
        show κB e m (.inl (.inr (.readH z (uSel e z)))) + βS e m ≤ βS e (uSel e z m (some v))
        have hκ : κB e m (.inl (.inr (.readH z (uSel e z)))) = 0 := by
          simp [κB, uSel_ne_uRed, uSel_ne_uJudge]
        rw [hκ, zero_add]
        exact le_rfl
      | judge =>
        show κB e m (.inl (.inr (.readH z (uJudge z)))) + βS e m ≤ βS e (uJudge z m (some v))
        refine le_trans ?_ (βS_uJudge z m v).1
        have hκ : κB e m (.inl (.inr (.readH z (uJudge z)))) =
            if IsG e.hash G z ∧ (m.seen z = false ∨ m.slot = none) then 1 else 0 := by
          simp [κB, (uRed_ne_uJudge z).symm]
        rw [hκ]
        gcongr
        split_ifs <;> simp_all
      | setup | red =>
        show κB e m (.inl (.inr (.readH z (uRed z)))) + βS e m ≤ βS e (uRed z m (some v))
        refine le_trans ?_ (βS_uRed z m (some v)).1
        have hκ : κB e m (.inl (.inr (.readH z (uRed z)))) =
            if IsG e.hash G z ∧ m.seen z = false then 1 else 0 := by
          simp [κB, uRed_ne_uJudge z]
        rw [hκ]
    | readK _ _ => exact absurd hp id
    | readK' _ _ => exact absurd hp id
  · exact absurd hp id

/-- **Live policy steps keep `InvS`**: every policy logs its outcome and marks only its cell. -/
theorem invS_step {m m' : Mem} {i : (hwSpec HashOutput HashDomain Mem).Port}
    {r : (hwSpec HashOutput HashDomain Mem).Result i} (hp : PolicyPort (upd e) i) (hI : InvS m)
    (h : nxD rl (some m) i r = some m') : InvS m' := by
  rcases i with (p | c) | c
  · cases h
    exact hI
  · cases c with
    | readH z u =>
      obtain ⟨c, rfl⟩ := hp
      rcases r with ⟨_ | v, w⟩
      · cases h
      obtain ⟨rfl, -⟩ := stepRd_some (rl := rl) h
      intro y hy
      have hlog : (upd e c z m (some v)).log = Function.update m.log z (some v) := by
        cases c <;> rfl
      rw [hlog]
      by_cases hyz : y = z
      · rw [hyz, Function.update_self]
        exact Option.some_ne_none v
      · rw [Function.update_of_ne hyz]
        refine hI y ?_
        have hseen : (upd e c z m (some v)).seen y = m.seen y := by
          cases c
          · exact Function.update_of_ne hyz _ _
          · rfl
          · exact Function.update_of_ne hyz _ _
          · exact Function.update_of_ne hyz _ _
        rw [← hseen]
        exact hy
    | readK _ _ => exact absurd hp id
    | readK' _ _ => exact absurd hp id
  · exact absurd hp id

/-- A live run of a reduction's algorithm from the dead mode stays dead. -/
theorem liveRedRun_none {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) {log : QueryLog R'} {r : α × QueryLog R'}
    {μ' : Option Mem} (h : LiveRedRun rl (upd e) ans oa log none r μ') : μ' = none :=
  liveRedRun_inv ans (fun _ μ ↦ μ = none)
    (fun _ μ i y μ'' hμ h' ↦ by
      subst hμ
      rcases i with n | z
      · change (y, μ'') ∈ support ((fun b ↦ (b, (none : Option Mem))) <$>
          (liftM (romWorld.Oracles.query (.inl n)) : OracleComp romWorld.Oracles _)) at h'
        rw [support_map] at h'
        obtain ⟨_, _, hw⟩ := h'
        exact (Prod.mk.inj hw).2.symm
      · rw [eq_stepRd_of_mem_support h']
        rfl)
    (fun _ μ _ _ _ hμ h' ↦ by
      subst hμ
      exact liveRun_none _ h')
    oa log none r μ' rfl h

/-- **The decision raises the budget measure by at most `2`**: its one read. -/
theorem βS_judge_le [SampleableType Par] [SampleableType Salt] (hlen : e.hash.LengthLe maxLen)
    {P : Par} {log : SLog Tw Msg Salt Dig} (out : Tw × Msg × Salt) {μ μ' : Option Mem}
    {b : Bool} (h : LiveRun rl (upd e .judge) ((encTcrSalt romWorld e).judge P log out) μ b μ')
    {m m' : Mem} (hm : μ = some m) (hm' : μ' = some m') : βS e m' ≤ βS e m + 2 := by
  obtain ⟨dg, μ₁, h1, h2⟩ := liveRun_bind h
  obtain ⟨-, hμ₁⟩ := liveRun_pure h2
  obtain ⟨v, -, hμv⟩ := liveRun_hashQ e.hash.trunc
    (encodeInput_cell hlen P out.1 (out.2.1, out.2.2)) h1
  rw [hμ₁, hμv, hm] at hm'
  obtain ⟨rfl, -⟩ := stepRd_some (rl := rl) hm'
  exact (βS_uJudge _ m v).2

/-- The start memory satisfies the live invariant on the empty transcript. -/
theorem liveInv_mem0 (P : Par) : LiveInv e P ([] : SLog Tw Msg Salt Dig) (some mem0) := by
  rintro m hm
  cases hm
  refine ⟨rfl, fun y _ hy ↦ absurd hy (by simp [mem0, Mem.recs]), fun y v hv ↦ ?_,
    fun _ x hx ↦ absurd hx (List.not_mem_nil)⟩
  cases hv

variable (e)

open scoped Classical in
/-- **EncTCR$ in the QROM against a straight-line reduction, with a live budget.** Let the
encoding inputs be cells of at most `maxLen` bytes, determine their parameter and tweak (`hs`)
and be injective in the message and salt (`hinj`), and let the truncation's fibers have at most
`F` values. Let the adversary make at most `q` calls of the oracle. On the live runs (every read
answered consistently with the log, the memory moved by the policies `upd`), let the reduction's
setup mark at most `k₁` encoding cells (`βS`), its handler mark none it did not mark before, and
its output at most `k₂` more, under an invariant `Ju` of its choice. Then
`probAvg ≤ ((q + k₁ + k₂ + 2) √(gradeEta F) + √TW)²`, `TW` the total weight of the challenger's
trial reads (`dS`). -/
theorem probAvg_encTcrSalt_le [SampleableType Par] [SampleableType Salt] (hs : GSep e.hash G)
    (hinj : ∀ P t, (e.hash.layout () P t).Injective) (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 Fo : Type}
    (pre : Par → OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) S0)
    (adv : Par → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : Par → S0 → St) (σ : Par → HHandler romWorld R (Tw × Msg →ₒ Option (Salt × Dig)) St)
    (post : Par → S0 → Fo → St →
      OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) (Tw × Msg × Salt))
    {q : ℕ} (hadv : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge hashCharge) q)
    (k₁ k₂ : ℕ) (Ju : Par → S0 → St × SLog Tw Msg Salt Dig → Option Mem → Prop)
    (hpreU : ∀ P a μ', LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (pre P) []
      (some mem0) a μ' → Ju P a.1 (st0 P a.1, a.2) μ' ∧ ∀ m', μ' = some m' → βS e m' ≤ k₁)
    (hσU : ∀ P a st log μ qq, LiveInv e P log μ → Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (σ P st qq) log μ r μ' →
        Ju P a (r.1.2, r.2) μ' ∧ ∀ m m', μ = some m → μ' = some m' → βS e m' ≤ βS e m)
    (hpostU : ∀ P a f st log μ, LiveInv e P log μ → Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (post P a f st) log μ r μ' →
        ∀ m m', μ = some m → μ' = some m' → βS e m' ≤ βS e m + k₂) :
    romWorld.probAvg ((encTcrSalt romWorld e).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (((q : ℝ≥0∞) + (k₁ + k₂ + 2 : ℕ)) * ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ) +
        (runtime2 HashOutput HashDomain mem0).totalWeight .instruments (dS e)
          (saltProg e pre adv st0 σ post) (rhoMem0 mem0) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hinv : ∀ (P : Par) {α : Type} (oa : OracleComp (romWorld.Oracles +
      (Tw × Msg →ₒ Option (Salt × Dig))) α) log μ r μ', LiveInv e P log μ →
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) oa log μ r μ' →
        LiveInv e P r.2 μ' := fun P _ oa ↦
    liveRedRun_inv _ (LiveInv e P) (fun _ _ _ _ _ hI h ↦ liveInv_red hI h)
      (fun _ _ q' _ _ hI h ↦ liveInv_answer hs hlen q' hI h) oa
  refine probAvg_game_slRed_le_moded_budget (encTcrSalt romWorld e) pre adv st0 σ post (upd e) rl
    (recordsAt_upd e) mem0 (fun _ ↦ rfl) (fun _ μ ↦ μ = some mem0) (fun _ μ h ↦ ?_)
    (fun P a s μ ↦ LiveInv e P s.2 μ ∧ Ju P a s μ ∧ ∀ m, μ = some m → βS e m ≤ k₁)
    (fun P μ hμ a μ' h ↦ ?_) (fun P a st log μ qq hJ r μ' h ↦ ?_)
    (fun P r μ ↦ LiveInv e P r.2 μ ∧ ∀ m, μ = some m → βS e m ≤ k₁ + k₂)
    (fun P a f st log μ hJ r μ' h ↦ ?_) (Tcr.Won e.hash G) (βS e) (k₁ + k₂ + 2)
    (fun P r μ hI b μ' h m hm ↦ ?_) (BadR e.hash G)
    (fun s hs' ↦ by
      obtain ⟨z, y, h1, h2⟩ := hs'
      exact Or.inr ⟨z, y, h1, h2⟩)
    (Tcr.potential_init_badR (C := e.hash) (G := G) mem0 fun _ ↦ rfl) InvS
    (fun _ h ↦ absurd h Bool.false_ne_true) (fun _ _ _ _ _ hp hI h ↦ invS_step hp hI h) κA (κB e)
    (fun _ _ _ _ _ hp h ↦ κB_add_βS_le hp h) (ENNReal.ofReal (gradeEta HashOutput F)) (dS e)
    (fun m i τ hi _ hI hτ hsupp ↦ (ENNReal.tsum_le_tsum fun r ↦ by
      split_ifs
      · exact zero_le
      · exact le_rfl).trans (tsum_potential_step_salt hF mem0 m i τ hi hI hτ hsupp))
    (isChargeBound_toReads (upd e)
      (isChargeBound_mixGame (encTcrSalt romWorld e) pre adv st0 σ post hadv))
  · exact liveRun_noHash _ (Common.isWeightBound_liftM_probComp hashW (fun _ ↦ rfl) _) h
  · subst hμ
    obtain ⟨hJu, hβ⟩ := hpreU P a μ' h
    exact ⟨hinv P _ [] _ a μ' (liveInv_mem0 P) h, hJu, hβ⟩
  · obtain ⟨hI, hJu, hβ⟩ := hJ
    obtain ⟨hJu', hβ'⟩ := hσU P a st log μ qq hI hJu r μ' h
    refine ⟨hinv P _ log μ r μ' hI h, hJu', fun m' hm' ↦ ?_⟩
    rcases μ with _ | m
    · rw [liveRedRun_none _ _ h] at hm'
      cases hm'
    · exact (hβ' m m' rfl hm').trans (hβ m rfl)
  · obtain ⟨hI, hJu, hβ⟩ := hJ
    refine ⟨hinv P _ log μ r μ' hI h, fun m' hm' ↦ ?_⟩
    rcases μ with _ | m
    · rw [liveRedRun_none _ _ h] at hm'
      cases hm'
    · have := hpostU P a f st log _ hI hJu r μ' h m m' rfl hm'
      have := hβ m rfl
      omega
  · obtain ⟨hI, hβ⟩ := hI
    rcases μ with _ | m₁
    · rw [liveRun_none _ h] at hm
      cases hm
    refine ⟨?_, fun hb ↦ ?_⟩
    · have := βS_judge_le hlen r.1 h rfl hm
      have := hβ m₁ rfl
      omega
    · subst hb
      exact won_of_judge hs hinj hlen r.1 hI h m hm

open scoped Classical in
/-- **EncTCR$ with a setup marking no encoding cell and an output marking at most two** (B2's
shape: the honest top root reads no encoding cell, the output its forged digests):
`probAvg ≤ ((q + 4) √(gradeEta F) + √TW)²`. -/
theorem probAvg_encTcrSalt_le_four [SampleableType Par] [SampleableType Salt] (hs : GSep e.hash G)
    (hinj : ∀ P t, (e.hash.layout () P t).Injective) (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 Fo : Type}
    (pre : Par → OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) S0)
    (adv : Par → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : Par → S0 → St) (σ : Par → HHandler romWorld R (Tw × Msg →ₒ Option (Salt × Dig)) St)
    (post : Par → S0 → Fo → St →
      OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) (Tw × Msg × Salt))
    {q : ℕ} (hadv : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge hashCharge) q)
    (Ju : Par → S0 → St × SLog Tw Msg Salt Dig → Option Mem → Prop)
    (hpreU : ∀ P a μ', LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (pre P) []
      (some mem0) a μ' → Ju P a.1 (st0 P a.1, a.2) μ' ∧ ∀ m', μ' = some m' → βS e m' = 0)
    (hσU : ∀ P a st log μ qq, LiveInv e P log μ → Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (σ P st qq) log μ r μ' →
        Ju P a (r.1.2, r.2) μ' ∧ ∀ m m', μ = some m → μ' = some m' → βS e m' ≤ βS e m)
    (hpostU : ∀ P a f st log μ, LiveInv e P log μ → Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (post P a f st) log μ r μ' →
        ∀ m m', μ = some m → μ' = some m' → βS e m' ≤ βS e m + 2) :
    romWorld.probAvg ((encTcrSalt romWorld e).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (((q : ℝ≥0∞) + 4) * ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ) +
        (runtime2 HashOutput HashDomain mem0).totalWeight .instruments (dS e)
          (saltProg e pre adv st0 σ post) (rhoMem0 mem0) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := probAvg_encTcrSalt_le e hs hinj hlen hF pre adv st0 σ post hadv 0 2 Ju
    (fun P a μ' hr ↦ ⟨(hpreU P a μ' hr).1, fun m' hm' ↦ ((hpreU P a μ' hr).2 m' hm').le⟩)
    hσU hpostU
  have h4 : ((0 + 2 + 2 : ℕ) : ℝ≥0∞) = 4 := by norm_num
  rw [h4] at h
  exact h

end main

end Quantum.StdModel.Qrom.EncSalt

end
