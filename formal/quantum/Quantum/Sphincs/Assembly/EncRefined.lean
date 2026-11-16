module

public import Quantum.Sphincs.Assembly.HwHeads
public import Quantum.Sphincs.Assembly.RecJ
public import Quantum.Sphincs.Assembly.RecBadMass
public import Quantum.Xmss.Assembly.EncRefined

@[expose] public section

/-!
# leanSPHINCS: the refined joint count of the selecting reads

leanXMSS's `Quantum.Xmss.Assembly.EncRefined` on CostRun's canonical prefix `prefixR pol A p v` at
the template data `(p, v)`, for every digest policy, with the codeword rate `ρ_c ≥ 2^-14`. Its
generic parts are reused (diagonal weights off the read cell, `trace_flipOp_split`, a cell read
with post-state weights `re_trace_gramW_le`, the leaks `readK_leak_le`, `readK'_leak_le`, the
refined trial modes `HMode`). CostRefined's `twPR_le` prices the prefix's reads with the linear
charge `E = 2 encRPre + hwMovePre + kapRR clsCap`; here `E` is bounded linearly in the flip-value
recorded mass `cwRecPre + recBadPre`.

* **The unselected key, count-weighted** (`unselFlip_le`, `unselRead_drop`): ReadCost's
  `re_trace_flipOp_le` on `N σ N` for the event "the trial's key is unselected": diagonal cost
  `-ρ_c` on the empty cells with the key unselected (`EmptyUnsel`), empty-to-recorded weight `ρ_c`,
  the cross term on the codeword-recorded cells (`CwRecG`). Hence `2^-15 e + post ≤ pre + 3 p`.
* **The read cell** (`TrialHead`, `cellFlip_le`): on the trial head re-compression costs `6/|X|`
  (`goodBlock_le`), off it `3` per unit of mass (`offBlock_le`). The trial head asks the rate only
  up to its digest, since `trialOf` names a trial up to it (`trialUpd_trunc`).
* **The refined joint count** (`trialRead_drop_ref`, `totalWeight_cntEW_le`, `cntEP_le`): along the
  prefix, `cntEP ≤ 2^15 (6q + progCap) + 2^15 (3C cwRecPre + 3 offHeadPre + kapS 6q +
  kapR6 clsCap + potCap (kfPre + recJPre))` with `C = nW progCap + 6q + clsCap` (EncPorts' port
  charges, RecJ's `kfPre`, `recJPre` through `totalWeight_kJumpW_le`).
* **The empty-cell flips** (`card_hFlip_div_le`, `encRW_le`, `encRPre_le_cntEP`, `encRPre_le_lin`):
  `encRPre ≤ encE0 q + encBeta q (cwRecPre + recBadPre) + encGamma q (kfPre + recJPre) +
  encDelta offHeadPre`. A selected key's head flips hit its tail's target (RecBadMass'
  `recBad_cases`).
* **The off-head mass** (`HRd`, `hFree_prefixT`, `offHead_step`, `offHeadPre_le`): the trial reads'
  refined modes keep the block and the `k`, `k'` outcomes; a trial's `h` read is off its head only
  where the union misses an outcome of its own `k`, `k'` reads (`offHeadW_le_miss`), which a read
  leaves with weight at most `2/|Z|`. Hence `offHeadPre ≤ 2^-511 clsCap`.
* **The hardwired moves** (`hwMoveW_le_offHeadW`, `hwMovePre_le_offHeadPre`): on HwHeads'
  honest-heads invariant (`forallQueries_hwHeads_prefixR`) a hardwired trial head cannot occur
  (the analogue of `hwHeadPre = 0`), so `hwMovePre ≤ offHeadPre`.
* **The prefix's linear charge** (`encE_le`): at data with `PermGood π 18`, for `q ≤ 2^64`, with the
  prefix's calls inside a hardwired table,
  `E ≤ encEC q + 2 encBeta q (cwRecPre + recBadPre) + 2 encGamma q (kfPre + recJPre)`.
-/

universe u v w

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Assembly Quantum.Xmss.Hybrid Sphincs
open HashSig (Digest HashOutput Message)
open Quantum.Xmss (X Z blocks trunc128 out256 card_X extProgCharge two_pow_div_card_X)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default
size. -/
set_option synthInstance.maxSize 2000

/-! ## The unselected-key event at a trial read -/

section unsel

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)
  (updOf : TrialPt → M → Option X → M)

/-- **A selected key stays selected** under every trial read. -/
def TrialKeep : Prop :=
  ∀ t m o, get m t.K ≠ none → get (updOf t m o) t.K ≠ none

/-- The states whose trial key is unselected. -/
def unselQ (t : TrialPt) : Set (Unit × HwReg X Z M) := {q | get q.2.2.2 t.K = none}

/-- `unselQ`, decided. -/
instance unselQDec (t : TrialPt) : DecidablePred (· ∈ unselQ get t) :=
  fun q ↦ inferInstanceAs (Decidable (get q.2.2.2 t.K = none))

/-- **The flip values of the unselected-key event** at a rest: the key unselected and the digest a
codeword. -/
def CwFlip (t : TrialPt) (z : Z) (y : X) (r : RestH X M z) : Prop :=
  get (memH z r) t.K = none ∧ Codeword.Valid (trunc128 (t.xi + y))

/-- `CwFlip`, decided classically. -/
noncomputable instance cwFlipDec (t : TrialPt) (z : Z) (y : X) (r : RestH X M z) :
    Decidable (CwFlip get t z y r) :=
  Classical.propDecidable _

/-- The states a trial read selects from: the cell neither hardwired nor recorded, the trial's
key unselected. -/
def EmptyUnsel (z : Z) (t : TrialPt) (s : HwReg X Z M) : Prop :=
  s.2.1.1 z = none ∧ s.1.1 z = none ∧ get s.2.2 t.K = none

/-- `EmptyUnsel`, decided classically. -/
noncomputable instance emptyUnselDec (z : Z) (t : TrialPt) :
    DecidablePred (EmptyUnsel get (M := M) z t) :=
  Classical.decPred _

/-- The states whose read cell is codeword-recorded for the trial's unselected key (EncPotential's
`cwRecW` integrand through `get`). -/
def CwRecG (z : Z) (t : TrialPt) (s : HwReg X Z M) : Prop :=
  s.2.1.1 z = none ∧ get s.2.2 t.K = none ∧
    ∃ v, s.1.1 z = some v ∧ Codeword.Valid (trunc128 (t.xi + v))

/-- `CwRecG`, decided classically. -/
noncomputable instance cwRecGDec (z : Z) (t : TrialPt) : DecidablePred (CwRecG get (M := M) z t) :=
  Classical.decPred _

omit [Fintype M] [DecidableEq M] in
theorem ind_unselQ_symm (t : TrialPt) (z : Z) (a : Option X) (r : RestH X M z) :
    ind (unselQ get t) ((splitH' z).symm (a, r)) =
      if get (memH z r) t.K = none then 1 else 0 :=
  rfl

omit [Fintype M] [DecidableEq M] in
theorem ind_unselQ (t : TrialPt) (q : Unit × HwReg X Z M) :
    ind (unselQ get t) q = if get q.2.2.2 t.K = none then 1 else 0 :=
  rfl

omit [Fintype M] [DecidableEq M] in
/-- The weight of a recorded outcome against the unselected-key event: whether the memory update
leaves the key unselected. -/
theorem gw_unselQ [Nonempty X] (t : TrialPt) (z : Z) (upd : M → Option X → M) (y : X)
    (r : RestH X M z) :
    gw (splitH' z) (tauH z upd) (unselQ get t) (some y) r =
      if get (upd (memH z r) (some y)) t.K = none then 1 else 0 := by
  unfold gw
  have h : ∀ a : Option X, ind (unselQ get t) ((splitH' z).symm (a, tauH z upd (some y) r)) =
      if get (upd (memH z r) (some y)) t.K = none then 1 else 0 := fun a ↦ rfl
  simp only [h]
  rw [← Finset.sum_mul, sum_cr_sq, one_mul]

variable {get updOf}

omit [Fintype M] [DecidableEq M] in
theorem upd_unsel_iff (hu : CwTrialUpd get updOf) {t : TrialPt} {m : M}
    (hm : get m t.K = none) (v : X) :
    get (updOf t m (some v)) t.K = none ↔ ¬ Codeword.Valid (trunc128 (t.xi + v)) := by
  rw [hu.sel t m v hm]
  exact cwSel_eq_none_iff hm t.x t.xi v

omit [Fintype M] [DecidableEq M] in
/-- **The diagonal cost of the unselected-key event**: `-ρ_c` on an empty, not hardwired cell of a
state with the key unselected, at most `0` elsewhere. -/
theorem fd_unselQ_le (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf) (t : TrialPt) (z : Z)
    (q : Unit × HwReg X Z M) :
    fd (splitH' z) (actH z) (tauH z (updOf t)) (unselQ get t) (phiH z (updOf t)) q ≤
      -(rhoCw * if EmptyUnsel get z t q.2 then 1 else 0) := by
  have hmem : memH z (splitH' z q).2 = q.2.2.2 := rfl
  unfold fd
  by_cases ha : actH z (splitH' z q).2
  · have ha' : q.2.2.1.1 z = none := ha
    rw [ite_eq_left ha, ind_unselQ]
    rcases hc : (splitH' z q).1 with _ | y
    · have hc' : q.2.1.1 z = none := hc
      show (∑ y, gw (splitH' z) (tauH z (updOf t)) (unselQ get t) (some y) (splitH' z q).2) /
          Fintype.card X - _ ≤ _
      simp only [gw_unselQ, hmem]
      by_cases hm : get q.2.2.2 t.K = none
      · have hsum : (∑ y : X, if get (updOf t q.2.2.2 (some y)) t.K = none then (1 : ℝ)
            else 0) = Fintype.card X -
              ((Finset.univ.filter fun v : X ↦ Codeword.Valid (trunc128 (t.xi + v))).card : ℝ) := by
          rw [Finset.sum_congr rfl fun y _ ↦ if_congr (upd_unsel_iff hu hm y) rfl rfl,
            Finset.sum_boole, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _),
            Finset.card_univ, Nat.cast_sub (Finset.card_le_univ _)]
        have hN : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
        have hE : EmptyUnsel get z t q.2 := And.intro ha' (And.intro hc' hm)
        rw [hsum, sub_div, div_self hN.ne', card_codeword_div_card_X, ite_eq_left hm,
          ite_eq_left hE]
        linarith
      · have h0 : ∀ y : X, get (updOf t q.2.2.2 (some y)) t.K ≠ none := fun y ↦ hk t _ _ hm
        have hR : (if EmptyUnsel get z t q.2 then (1 : ℝ) else 0) = 0 :=
          ite_eq_right fun h ↦ hm h.2.2
        rw [hR, mul_zero, neg_zero, ite_eq_right hm]
        simp only [h0, ↓reduceIte, Finset.sum_const_zero, zero_div, sub_zero, le_refl]
    · have hc' : q.2.1.1 z ≠ none := by rw [← splitH'_apply_fst, hc]; exact Option.some_ne_none y
      show gw (splitH' z) (tauH z (updOf t)) (unselQ get t) (some y) (splitH' z q).2 - _ ≤ _
      have hR : (if EmptyUnsel get z t q.2 then (1 : ℝ) else 0) = 0 :=
        ite_eq_right fun h ↦ hc' h.2.1
      rw [hR, mul_zero, neg_zero, gw_unselQ, hmem]
      by_cases hm : get q.2.2.2 t.K = none
      · rw [ite_eq_left hm]
        split_ifs <;> norm_num
      · rw [ite_eq_right hm, ite_eq_right (hk t _ _ hm), sub_zero]
  · have ha' : q.2.2.1.1 z ≠ none := ha
    have hR : (if EmptyUnsel get z t q.2 then (1 : ℝ) else 0) = 0 :=
      ite_eq_right fun h ↦ ha' h.1
    rw [ite_eq_right ha, ind_unselQ, ind_unselQ, hR, mul_zero, neg_zero]
    show (if get (updOf t q.2.2.2 (q.2.2.1.1 z)) t.K = none then (1 : ℝ) else 0) - _ ≤ 0
    by_cases hm : get q.2.2.2 t.K = none
    · rw [ite_eq_left hm]
      split_ifs <;> norm_num
    · rw [ite_eq_right hm, ite_eq_right (hk t _ _ hm), sub_zero]

omit [Fintype M] [DecidableEq M] in
/-- **The empty-to-recorded weight of the unselected-key event**, with the reference weight `q0`:
`ρ_c` on an empty, not hardwired cell with the key unselected, `0` elsewhere. -/
theorem ew_unselQ_le (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf) (t : TrialPt) (z : Z)
    (q : Unit × HwReg X Z M) :
    ew (splitH' z) (actH z) (tauH z (updOf t)) (unselQ get t)
        (q0 (splitH' z) (unselQ get t)) q ≤
      rhoCw * if EmptyUnsel get z t q.2 then 1 else 0 := by
  have hmem : memH z (splitH' z q).2 = q.2.2.2 := rfl
  have hρ : 0 ≤ rhoCw := rhoCw_pos.le
  unfold ew
  split_ifs with h1 h2 h2
  · have hN : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
    have hq0 : q0 (splitH' z) (unselQ get t) (splitH' z q).2 = 1 := by
      unfold q0
      rw [ind_unselQ_symm, hmem, ite_eq_left h2.2.2]
    have hterm : ∀ y : X, xv (splitH' z) (tauH z (updOf t)) (unselQ get t)
        (q0 (splitH' z) (unselQ get t)) (some y) (splitH' z q).2 ^ 2 =
        (if Codeword.Valid (trunc128 (t.xi + y)) then 1 else 0) / Fintype.card X := fun y ↦ by
      have hsq : ((if ¬ Codeword.Valid (trunc128 (t.xi + y)) then (1 : ℝ) else 0) - 1) ^ 2 =
          if Codeword.Valid (trunc128 (t.xi + y)) then 1 else 0 := by
        split_ifs <;> norm_num
      show ((gw (splitH' z) (tauH z (updOf t)) (unselQ get t) (some y) (splitH' z q).2 -
        q0 (splitH' z) (unselQ get t) (splitH' z q).2) / Real.sqrt (Fintype.card X)) ^ 2 = _
      rw [hq0, gw_unselQ, hmem, if_congr (upd_unsel_iff hu h2.2.2 y) rfl rfl, div_pow,
        Real.sq_sqrt hN.le, hsq]
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, ← Finset.sum_div, Finset.sum_boole,
      card_codeword_div_card_X, mul_one]
  · have hm : get q.2.2.2 t.K ≠ none := fun hm ↦
      h2 (And.intro h1.1 (And.intro h1.2 hm) : EmptyUnsel get z t q.2)
    have hq0 : q0 (splitH' z) (unselQ get t) (splitH' z q).2 = 0 := by
      unfold q0
      rw [ind_unselQ_symm, hmem, ite_eq_right hm]
    have hterm : ∀ y : X, xv (splitH' z) (tauH z (updOf t)) (unselQ get t)
        (q0 (splitH' z) (unselQ get t)) (some y) (splitH' z q).2 ^ 2 = 0 := fun y ↦ by
      show ((gw (splitH' z) (tauH z (updOf t)) (unselQ get t) (some y) (splitH' z q).2 -
        q0 (splitH' z) (unselQ get t) (splitH' z q).2) / Real.sqrt (Fintype.card X)) ^ 2 = _
      rw [hq0, gw_unselQ, hmem, ite_eq_right (hk t _ (some y) hm), sub_self, zero_div]
      exact zero_pow two_ne_zero
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, Finset.sum_const_zero, mul_zero]
  · exact absurd ⟨h2.1, h2.2.1⟩ h1
  · rw [mul_zero]

omit [Fintype M] [DecidableEq M] in
/-- **The cross term's support**: the recorded cells of the flip values are codeword-recorded
for the unselected key. -/
theorem pd_cwFlip_le (t : TrialPt) (z : Z) (q : Unit × HwReg X Z M) :
    pd (splitH' z) (actH z) (CwFlip get t z) q ≤
      if CwRecG get z t q.2 then 1 else 0 := by
  classical
  unfold pd
  split_ifs with h1 h2
  · rcases hc : (splitH' z q).1 with _ | y
    · simp
    · simp only [Option.elim_some]
      split_ifs <;> norm_num
  · rcases hc : (splitH' z q).1 with _ | y
    · simp
    · simp only [Option.elim_some]
      split_ifs with h3
      · exfalso
        have hc' : q.2.1.1 z = some y := hc
        exact h2 (And.intro h1 (And.intro h3.1 ⟨y, hc', h3.2⟩) : CwRecG get z t q.2)
      · exact le_rfl
  · norm_num
  · exact le_rfl

omit [Fintype M] [DecidableEq M] in
/-- Off the flip values a recorded outcome weighs the reference weight `q0`. -/
theorem gw_eq_q0_of_not_cwFlip (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf)
    (t : TrialPt) (z : Z) (r : RestH X M z) (y : X) (hy : ¬ CwFlip get t z y r) :
    gw (splitH' z) (tauH z (updOf t)) (unselQ get t) (some y) r =
      q0 (splitH' z) (unselQ get t) r := by
  unfold q0
  rw [gw_unselQ, ind_unselQ_symm]
  by_cases hm : get (memH z r) t.K = none
  · rw [ite_eq_left hm, ite_eq_left ((upd_unsel_iff hu hm y).2 fun hv ↦ hy ⟨hm, hv⟩)]
  · rw [ite_eq_right hm, ite_eq_right (hk t _ _ hm)]

variable (get updOf)

/-- The unselected `n`-weighted mass is the event weight of `N σ N`. -/
theorem re_trace_indProj_sqrtDiag (t : TrialPt) {n : HwReg X Z M → ℝ} (hn0 : ∀ s, 0 ≤ n s)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    (indProj (unselQ get t) * (sqrtDiag n * σ * sqrtDiag n)).trace.re =
      dW (fun q ↦ ind (unselQ get t) q * n q.2) σ := by
  rw [indProj, re_trace_diagonal_mul]
  unfold dW
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [re_sqrtDiag_conj_apply hn0]
  exact (mul_assoc _ _ _).symm

/-- **The unselected `n`-weighted mass after a trial read**: the mass before plus the flip of the
unselected-key event on `N σ N`. -/
theorem unsel_post_eq (z : Z) (t : TrialPt) {n : HwReg X Z M → ℝ} (hn0 : ∀ s, 0 ≤ n s)
    (hn : OffCell z n) (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    ∑ r : Option X × M, dW (fun q ↦ ind (unselQ get t) q * n q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
      dW (fun q ↦ ind (unselQ get t) q * n q.2) σ +
        (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r) (unselQ get t) *
          (sqrtDiag n * σ * sqrtDiag n)).trace.re := by
  have h1 : ∀ r, dW (fun q ↦ ind (unselQ get t) q * n q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
      dW (fun q ↦ ind (unselQ get t) q)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) (sqrtDiag n * σ * sqrtDiag n)) :=
    fun r ↦ (dW_conj_sqrtDiag z (updOf t) hn0 hn (fun q ↦ ind (unselQ get t) q) r σ).symm
  have hsumeq : (∑ r : Option X × M, (hwReadKraus (.readH z (updOf t)) r)ᴴ *
      diagonal (fun q ↦ ((ind (unselQ get t) q : ℝ) : ℂ)) *
        hwReadKraus (.readH z (updOf t)) r) =
      flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r) (unselQ get t) +
        indProj (unselQ get t) := by
    rw [flipOp, sub_add_cancel]
    rfl
  rw [Finset.sum_congr rfl fun r _ ↦ h1 r, sum_dW_conj, hsumeq, Matrix.add_mul,
    Matrix.trace_add, Complex.add_re, add_comm, re_trace_indProj_sqrtDiag get t hn0 σ]

variable {get updOf}

/-- **The flip of the unselected-key event at a trial read, `n`-weighted** (ReadCost's
`re_trace_flipOp_le` on `N σ N`): at most `-ρ_c e + 2 √(ρ_c e p)`, `e` the `n`-weighted
`EmptyUnsel` mass and `p` the `n`-weighted `CwRecG` mass. -/
theorem unselFlip_le (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf) (z : Z)
    (t : TrialPt) {n : HwReg X Z M → ℝ} (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r) (unselQ get t) *
        (sqrtDiag n * σ * sqrtDiag n)).trace.re ≤
      -(rhoCw * ∑ q, (if EmptyUnsel get z t q.2 then 1 else 0) * (n q.2 * (σ q q).re)) +
        2 * √(rhoCw * (∑ q, (if EmptyUnsel get z t q.2 then 1 else 0) * (n q.2 * (σ q q).re)) *
          ∑ q, (if CwRecG get z t q.2 then 1 else 0) * (n q.2 * (σ q q).re)) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hτ : (sqrtDiag n * σ * sqrtDiag n).PosSemidef := posSemidef_sqrtDiag_conj n hσ
  have hdiag : ∀ q, ((sqrtDiag n * σ * sqrtDiag n) q q).re = n q.2 * (σ q q).re :=
    re_sqrtDiag_conj_apply hn0 σ
  have hnσ : ∀ q, 0 ≤ n q.2 * (σ q q).re := fun q ↦ mul_nonneg (hn0 _) (hre q)
  have hF := re_trace_flipOp_le (unselQ get t) (cellRead_readH z (updOf t))
    (clsOff_readH z (updOf t)) (q0 (splitH' z) (unselQ get t)) (CwFlip get t z)
    (fun r _ y hy ↦ gw_eq_q0_of_not_cwFlip hu hk t z r y hy) hτ (cellNoBot_sqrtDiag hn hnb)
  have he : 0 ≤ ∑ q, (if EmptyUnsel get z t q.2 then (1 : ℝ) else 0) * (n q.2 * (σ q q).re) :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hnσ q)
  have hρ : 0 ≤ rhoCw := rhoCw_pos.le
  have hfd : ∑ s, fd (splitH' z) (actH z) (tauH z (updOf t)) (unselQ get t) (phiH z (updOf t)) s *
      ((sqrtDiag n * σ * sqrtDiag n) s s).re ≤
      -(rhoCw * ∑ q, (if EmptyUnsel get z t q.2 then 1 else 0) * (n q.2 * (σ q q).re)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [hdiag]
    exact (mul_le_mul_of_nonneg_right (fd_unselQ_le hu hk t z q) (hnσ q)).trans_eq (by ring)
  have hew : ∑ s, ew (splitH' z) (actH z) (tauH z (updOf t)) (unselQ get t)
      (q0 (splitH' z) (unselQ get t)) s * ((sqrtDiag n * σ * sqrtDiag n) s s).re ≤
      rhoCw * ∑ q, (if EmptyUnsel get z t q.2 then 1 else 0) * (n q.2 * (σ q q).re) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [hdiag]
    exact (mul_le_mul_of_nonneg_right (ew_unselQ_le hu hk t z q) (hnσ q)).trans_eq (by ring)
  have hpd : ∑ s, pd (splitH' z) (actH z) (CwFlip get t z) s *
      ((sqrtDiag n * σ * sqrtDiag n) s s).re ≤
      ∑ q, (if CwRecG get z t q.2 then 1 else 0) * (n q.2 * (σ q q).re) :=
    Finset.sum_le_sum fun q _ ↦ by
      rw [hdiag]
      exact mul_le_mul_of_nonneg_right (pd_cwFlip_le t z q) (hnσ q)
  have hP0 : 0 ≤ ∑ s, pd (splitH' z) (actH z) (CwFlip get t z) s *
      ((sqrtDiag n * σ * sqrtDiag n) s s).re :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      rcases pd_mem (e := splitH' z) (act := actH z) (CwFlip get t z) q with h | h <;>
        simp only [h, le_refl, zero_le_one]) (by rw [hdiag]; exact hnσ q)
  refine hF.trans (add_le_add hfd (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
  rw [← Real.sqrt_mul' _ hP0]
  exact Real.sqrt_le_sqrt (mul_le_mul hew hpd hP0 (mul_nonneg hρ he))

/-- **The unselected-key part of the potential at a trial read** (`unsel_post_eq`,
`unselFlip_le`, EncPotential's `drop_of_survive_rho`): `2^-15 e` plus the `n`-weighted unselected
mass after the read is at most the one before plus `3 p`. -/
theorem unselRead_drop (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf) (z : Z)
    (t : TrialPt) {n : HwReg X Z M → ℝ} (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (2 ^ 15 : ℝ)⁻¹ * (∑ q, (if EmptyUnsel get z t q.2 then 1 else 0) * (n q.2 * (σ q q).re)) +
      ∑ r : Option X × M, dW (fun q ↦ ind (unselQ get t) q * n q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) ≤
    dW (fun q ↦ ind (unselQ get t) q * n q.2) σ +
      3 * ∑ q, (if CwRecG get z t q.2 then 1 else 0) * (n q.2 * (σ q q).re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hnσ : ∀ q, 0 ≤ n q.2 * (σ q q).re := fun q ↦ mul_nonneg (hn0 _) (hre q)
  refine drop_of_survive_rho (Finset.sum_nonneg fun q _ ↦ mul_nonneg
    (by split_ifs <;> norm_num) (hnσ q)) (Finset.sum_nonneg fun q _ ↦ mul_nonneg
      (by split_ifs <;> norm_num) (hnσ q)) inv_two_pow_14_le_rhoCw ?_
  rw [unsel_post_eq get updOf z t hn0 hn σ]
  have h := unselFlip_le hu hk z t hn0 hn hσ hnb
  have hp : 0 ≤ ∑ q, (if CwRecG get z t q.2 then (1 : ℝ) else 0) * (n q.2 * (σ q q).re) :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hnσ q)
  linarith

end unsel

/-! ## The read cell after a trial read -/

section cell

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)
  (updOf : TrialPt → M → Option X → M)

/-- **The trial-head states** of a trial read at the cell `z`: a bad union, or the trial's block
at its key's encoding slot with head-tail `z` at a rate with the trial's digest (the support
invariant of the trial reads). Unlike EncPotential's `TrialGood`, the key may be selected and the
rate is asked only up to its digest. -/
def TrialHead (d : EvData) (z : Z) (t : TrialPt) (s : HwReg X Z M) : Prop :=
  ¬ Good d.perm (union s.2.1 s.1) ∨ (EncAt d t.K [t.x] ∧
    ∃ xi, trunc128 xi = trunc128 t.xi ∧ IsHeadTail d.perm (union s.2.1 s.1) [t.x] z xi)

/-- `TrialHead`, decided classically. -/
noncomputable instance trialHeadDec (d : EvData) (z : Z) (t : TrialPt) :
    DecidablePred (TrialHead (M := M) d z t) :=
  Classical.decPred _

omit [Fintype M] [DecidableEq M] in
theorem trialHead_congr {d : EvData} {z : Z} {t : TrialPt} {s s' : HwReg X Z M}
    (hk : (union s'.2.1 s'.1).k = (union s.2.1 s.1).k)
    (hk' : (union s'.2.1 s'.1).k' = (union s.2.1 s.1).k') :
    TrialHead d z t s' ↔ TrialHead d z t s := by
  unfold TrialHead
  simp only [good_congr hk hk', isHeadTail_congr hk hk']

omit [Fintype M] [DecidableEq M] in
theorem trialHead_offCell (d : EvData) (z : Z) (t : TrialPt) :
    OffCell z (fun s : HwReg X Z M ↦ if TrialHead d z t s then (1 : ℝ) else 0) := by
  intro s s' h1 h2 h3
  obtain ⟨hk, hk', -⟩ := union_congr_off h1 h2 h3
  exact if_congr (trialHead_congr hk hk') rfl rfl

omit [Fintype M] [DecidableEq M] in
theorem trialHead_offCell' (d : EvData) (z : Z) (t : TrialPt) :
    OffCell z (fun s : HwReg X Z M ↦ if TrialHead d z t s then (0 : ℝ) else 1) := by
  intro s s' h1 h2 h3
  obtain ⟨hk, hk', -⟩ := union_congr_off h1 h2 h3
  exact if_congr (trialHead_congr hk hk') rfl rfl

variable {get updOf}

omit [Fintype M] [DecidableEq M] in
/-- **After a trial read the read cell does not count**: on `TrialHead` states, recording any value
`y` at `z` with the trial's update leaves `encCSet` (an unselected key selects the codeword digest,
a selected key stays selected). -/
theorem not_mem_encCSet_of_trialHead (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf)
    {d : EvData} {z : Z} {t : TrialPt} {s s' : HwReg X Z M} {y : X}
    (hg : TrialHead d z t s) (hk1 : (union s'.2.1 s'.1).k = (union s.2.1 s.1).k)
    (hk2 : (union s'.2.1 s'.1).k' = (union s.2.1 s.1).k') (hz : (union s'.2.1 s'.1).h z = some y)
    (hm : s'.2.2 = updOf t s.2.2 (some y)) : s' ∉ encCSet get d z := by
  rintro ⟨hG', K, hun, t', xi', w, hP, hi, hw, hcw⟩
  have hG : Good d.perm (union s.2.1 s.1) := (good_congr hk1 hk2).1 hG'
  rcases hg with hg | ⟨hslot, xi, hxi, hhead⟩
  · exact hg hG
  have hhead' := (isHeadTail_congr hk1.symm hk2.symm).1 hhead
  obtain ⟨rfl, rfl⟩ := hG'.isHeadTail_unique hi hhead'
  obtain rfl := encAt_unique d _ _ _ hP hslot
  rw [hz] at hw
  obtain rfl := Option.some.inj hw
  rw [hm] at hun
  rw [trunc128_add_congr hxi] at hcw
  by_cases hm0 : get s.2.2 t.K = none
  · rw [hu.sel t _ y hm0] at hun
    exact ((cwSel_eq_none_iff hm0 t.x t.xi y).1 hun) hcw
  · exact hk t _ _ hm0 hun

/-- **The good block of the read cell**: on `TrialHead` states, the flip of `encCSet` is at most
`2/|X|` on the diagonal and `4/|X|²` from the empty-to-recorded amplitudes with reference weight
`0`, so ReadCost's `re_trace_flipOp_le` (cross term over all recorded cells, here at most the
trace) gives `6/|X|` per unit of trace. -/
theorem goodBlock_le (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf) (d : EvData)
    (z : Z) (t : TrialPt) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
        (liftSet (encCSet get d z)) *
        (sqrtDiag (fun s ↦ if TrialHead d z t s then (1 : ℝ) else 0) * σ *
          sqrtDiag (fun s ↦ if TrialHead d z t s then (1 : ℝ) else 0))).trace.re ≤
      6 / (Fintype.card X : ℝ) *
        ∑ q, (if TrialHead d z t q.2 then (1 : ℝ) else 0) * (σ q q).re := by
  set S := liftSet (encCSet get d z)
  set g : HwReg X Z M → ℝ := fun s ↦ if TrialHead d z t s then (1 : ℝ) else 0
  have hg0 : ∀ s, 0 ≤ g s := fun s ↦ by simp only [g]; split_ifs <;> norm_num
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hgσ : ∀ q, 0 ≤ g q.2 * (σ q q).re := fun q ↦ mul_nonneg (hg0 _) (hre q)
  have hτ := posSemidef_sqrtDiag_conj g hσ
  have hdiag : ∀ q, ((sqrtDiag g * σ * sqrtDiag g) q q).re = g q.2 * (σ q q).re :=
    re_sqrtDiag_conj_apply hg0 σ
  have hF := re_trace_flipOp_le S (cellRead_readH z (updOf t)) (clsOff_readH z (updOf t))
    (fun _ ↦ 0) (fun _ _ ↦ True) (fun _ _ _ hy ↦ absurd trivial hy) hτ
    (cellNoBot_sqrtDiag (trialHead_offCell d z t) hnb)
  have hA : ∀ q : Unit × HwReg X Z M, TrialHead d z t q.2 → actH z (splitH' z q).2 →
      ∀ y, ind S ((splitH' z).symm (some y, tauH z (updOf t) (some y) (splitH' z q).2)) = 0 := by
    intro q hg ha y
    have ha' : q.2.2.1.1 z = none := ha
    rw [splitH'_symm_tau]
    exact ind_eq_zero_of_not_mem S (not_mem_encCSet_of_trialHead hu hk hg (union_k_h _ _ _ _)
      (union_k'_h _ _ _ _) (union_h_upd q.2.2.1 q.2.1.1 q.2.1.2 z y ha') rfl)
  have hH : ∀ q : Unit × HwReg X Z M, TrialHead d z t q.2 → ¬ actH z (splitH' z q).2 →
      ind S (phiH z (updOf t) q) = 0 := by
    intro q hg ha
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 (show q.2.2.1.1 z ≠ none from ha)
    refine ind_eq_zero_of_not_mem _ fun h ↦ not_mem_encCSet_of_trialHead hu hk (y := w)
      (s' := (q.2.1, q.2.2.1, updOf t q.2.2.2 (q.2.2.1.1 z))) hg rfl rfl ?_ ?_
      ((mem_liftSet _ _).1 h)
    · show (q.2.2.1.1 z).or (q.2.1.1 z) = some w
      rw [hw]
      rfl
    · show updOf t q.2.2.2 (q.2.2.1.1 z) = updOf t q.2.2.2 (some w)
      rw [hw]
  have hgw : ∀ q : Unit × HwReg X Z M, TrialHead d z t q.2 → actH z (splitH' z q).2 → ∀ y,
      gw (splitH' z) (tauH z (updOf t)) S (some y) (splitH' z q).2 ≤ 2 / Fintype.card X :=
    fun q hg ha y ↦ gw_some_le_two_div S (hA q hg ha y)
  have hN : (0 : ℝ) ≤ 2 / Fintype.card X := by positivity
  have hfd : ∀ q, fd (splitH' z) (actH z) (tauH z (updOf t)) S (phiH z (updOf t)) q *
      (g q.2 * (σ q q).re) ≤ 2 / Fintype.card X * (g q.2 * (σ q q).re) := fun q ↦ by
    by_cases hg : TrialHead d z t q.2
    · refine mul_le_mul_of_nonneg_right ?_ (hgσ q)
      unfold fd
      split_ifs with ha
      · exact (sub_le_self _ (ind_nonneg S q)).trans (gdiag_le_of S (hgw q hg ha) _)
      · rw [hH q hg ha, zero_sub]
        exact (neg_nonpos.2 (ind_nonneg S q)).trans hN
    · have h0 : g q.2 = 0 := ite_eq_right hg
      rw [h0, zero_mul, mul_zero, mul_zero]
  have hew : ∀ q, ew (splitH' z) (actH z) (tauH z (updOf t)) S (fun _ ↦ 0) q *
      (g q.2 * (σ q q).re) ≤ (2 / Fintype.card X) ^ 2 * (g q.2 * (σ q q).re) := fun q ↦ by
    by_cases hg : TrialHead d z t q.2
    · refine mul_le_mul_of_nonneg_right ?_ (hgσ q)
      by_cases ha : actH z (splitH' z q).2
      · exact ew_zero_le_of S (hgw q hg ha)
      · unfold ew
        rw [ite_eq_right fun h ↦ ha h.1]
        positivity
    · have h0 : g q.2 = 0 := ite_eq_right hg
      rw [h0, zero_mul, mul_zero, mul_zero]
  have hpd : ∀ q, pd (splitH' z) (actH z) (fun _ _ ↦ True) q * (g q.2 * (σ q q).re) ≤
      g q.2 * (σ q q).re := fun q ↦ by
    rcases pd_mem (e := splitH' z) (act := actH z) (fun _ _ ↦ True) q with h | h <;>
      (rw [h]; linarith [hgσ q])
  set m := ∑ q, g q.2 * (σ q q).re
  have hm : 0 ≤ m := Finset.sum_nonneg fun q _ ↦ hgσ q
  have hA' : ∑ s, fd (splitH' z) (actH z) (tauH z (updOf t)) S (phiH z (updOf t)) s *
      ((sqrtDiag g * σ * sqrtDiag g) s s).re ≤ 2 / Fintype.card X * m := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun q _ ↦ by rw [hdiag]; exact hfd q
  have hE : ∑ s, ew (splitH' z) (actH z) (tauH z (updOf t)) S (fun _ ↦ 0) s *
      ((sqrtDiag g * σ * sqrtDiag g) s s).re ≤ (2 / Fintype.card X) ^ 2 * m := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun q _ ↦ by rw [hdiag]; exact hew q
  have hP : ∑ s, pd (splitH' z) (actH z) (fun _ _ ↦ True) s *
      ((sqrtDiag g * σ * sqrtDiag g) s s).re ≤ m :=
    Finset.sum_le_sum fun q _ ↦ by rw [hdiag]; exact hpd q
  have hsE : √(∑ s, ew (splitH' z) (actH z) (tauH z (updOf t)) S (fun _ ↦ 0) s *
      ((sqrtDiag g * σ * sqrtDiag g) s s).re) ≤ 2 / Fintype.card X * √m := by
    refine (Real.sqrt_le_sqrt hE).trans_eq ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hN]
  have hsP := Real.sqrt_le_sqrt hP
  have hmm : √m * √m = m := Real.mul_self_sqrt hm
  have hprod : √(∑ s, ew (splitH' z) (actH z) (tauH z (updOf t)) S (fun _ ↦ 0) s *
      ((sqrtDiag g * σ * sqrtDiag g) s s).re) * √(∑ s, pd (splitH' z) (actH z) (fun _ _ ↦ True) s *
        ((sqrtDiag g * σ * sqrtDiag g) s s).re) ≤ 2 / Fintype.card X * m := by
    calc _ ≤ (2 / Fintype.card X * √m) * √m :=
          mul_le_mul hsE hsP (Real.sqrt_nonneg _) (mul_nonneg hN (Real.sqrt_nonneg _))
      _ = 2 / Fintype.card X * m := by rw [mul_assoc, hmm]
  show _ ≤ 6 / (Fintype.card X : ℝ) * m
  have h6 : 6 / (Fintype.card X : ℝ) * m = 2 / Fintype.card X * m + 2 * (2 / Fintype.card X * m) :=
    by ring
  rw [h6]
  linarith [hF, hA', hprod]

/-- **The off block of the read cell**: off `TrialHead`, the flip of `encCSet` is at most `3`
per unit of trace (`re_trace_flipOp_le_good` with no good state). -/
theorem offBlock_le (d : EvData) (z : Z) (t : TrialPt)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
        (liftSet (encCSet get d z)) *
        (sqrtDiag (fun s ↦ if TrialHead d z t s then (0 : ℝ) else 1) * σ *
          sqrtDiag (fun s ↦ if TrialHead d z t s then (0 : ℝ) else 1))).trace.re ≤
      3 * ∑ q, (if TrialHead d z t q.2 then (0 : ℝ) else 1) * (σ q q).re := by
  set g : HwReg X Z M → ℝ := fun s ↦ if TrialHead d z t s then (0 : ℝ) else 1
  have hg0 : ∀ s, 0 ≤ g s := fun s ↦ by simp only [g]; split_ifs <;> norm_num
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hτ := posSemidef_sqrtDiag_conj g hσ
  have hdiag : ∀ q, ((sqrtDiag g * σ * sqrtDiag g) q q).re = g q.2 * (σ q q).re :=
    re_sqrtDiag_conj_apply hg0 σ
  have hF := re_trace_flipOp_le_good (liftSet (encCSet get d z)) (cellRead_readH z (updOf t))
    (clsOff_readH z (updOf t)) (fun _ ↦ False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) hτ
    (cellNoBot_sqrtDiag (trialHead_offCell' d z t) hnb)
  refine hF.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  rw [hdiag]
  have hpd : pd (splitH' z) (actH z) (fun _ _ ↦ True) q ≤ 1 := by
    rcases pd_mem (e := splitH' z) (act := actH z) (fun _ _ ↦ True) q with h | h <;>
      simp only [h, zero_le_one, le_refl]
  have h2 : ((if (fun _ : Unit × HwReg X Z M ↦ False) q then 2 / (Fintype.card X : ℝ) +
      (2 / (Fintype.card X : ℝ)) ^ 2 else 2) + pd (splitH' z) (actH z) (fun _ _ ↦ True) q) ≤ 3 := by
    rw [ite_eq_right not_false]
    linarith
  exact mul_le_mul_of_nonneg_right h2 (mul_nonneg (hg0 q.2) (hre q))

/-- **The read cell's part of the potential at a trial read**: at most `6/|X|` per unit of trace
and `3` per unit of the off-head mass (`trace_flipOp_split`, `goodBlock_le`, `offBlock_le`). -/
theorem cellFlip_le (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf) (d : EvData)
    (z : Z) (t : TrialPt) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
        (liftSet (encCSet get d z)) * σ).trace.re ≤
      6 / (Fintype.card X : ℝ) * ∑ q, (σ q q).re +
        3 * ∑ q, (if TrialHead d z t q.2 then (0 : ℝ) else 1) * (σ q q).re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hs := congrArg Complex.re (trace_flipOp_split z (updOf t) (TrialHead d z t)
    (trialHead_offCell d z t) (trialHead_offCell' d z t) (liftSet (encCSet get d z)) σ)
  rw [Complex.add_re] at hs
  rw [hs]
  have hG := goodBlock_le hu hk d z t hσ hnb
  have hO := offBlock_le (get := get) (updOf := updOf) d z t hσ hnb
  have hle : ∑ q, (if TrialHead d z t q.2 then (1 : ℝ) else 0) * (σ q q).re ≤ ∑ q, (σ q q).re :=
    Finset.sum_le_sum fun q _ ↦ by
      split_ifs
      · rw [one_mul]
      · rw [zero_mul]
        exact hre q
  have hN : (0 : ℝ) ≤ 6 / Fintype.card X := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hle hN]

end cell

/-! ## A trial read against the cross-key potential, refined -/

section trialRef

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)
  (updOf : TrialPt → M → Option X → M)

/-- The count of a trial's key off the read cell on the states the read selects from (the cell
empty, the key unselected): the `e` of `unselRead_drop`. -/
noncomputable def trialCntE (d : EvData) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, (if EmptyUnsel get z t q.2 then 1 else 0) * (encOff d z t.K q.2 * (σ q q).re)

/-- **The refined charge of a trial read**: three times the count-weighted codeword-recorded
mass, `6/|X|` per unit of trace and three times the off-head mass. -/
noncomputable def trialChgRe (d : EvData) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  3 * (∑ q, (if CwRecG get z t q.2 then 1 else 0) * (encOff d z t.K q.2 * (σ q q).re)) +
    (6 / (Fintype.card X : ℝ) * ∑ q, (σ q q).re +
      3 * ∑ q, (if TrialHead d z t q.2 then (0 : ℝ) else 1) * (σ q q).re)

open scoped Classical in
/-- **The joint count of the selecting reads, refined**, per port: `trialCntE` at a trial read
port. -/
noncomputable def cntEW (d : EvData) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then
    ENNReal.ofReal (trialCntE get d (trialOf updOf c).1 (trialOf updOf c).2 σ) else 0

open scoped Classical in
/-- **The refined charge of a trial read port** (`trialChgRe`; `0` elsewhere). -/
noncomputable def trialChgR (d : EvData) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then
    ENNReal.ofReal (trialChgRe get d (trialOf updOf c).1 (trialOf updOf c).2 σ) else 0

omit [DecidableEq M] in
theorem trialCntE_nonneg (d : EvData) (z : Z) (t : TrialPt)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ trialCntE get d z t σ :=
  Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num)
    (mul_nonneg (encOff_nonneg d z _ _) (Complex.nonneg_iff.1 hσ.diag_nonneg).1)

variable {get updOf}

/-- **A trial read against the potential, refined** (real form): `2^-15 trialCntE` plus the
potential after the read is at most the potential before plus `trialChgRe`. The other keys keep
their part (`encA_keep`); the trial's key off the read cell drops (`unselRead_drop`); the read
cell counts after the read by `cellFlip_le`. -/
theorem trialRead_drop_ref (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf)
    (d : EvData) (z : Z) (t : TrialPt)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (2 ^ 15 : ℝ)⁻¹ * trialCntE get d z t σ +
      ∑ r : Option X × M, dW (fun q ↦ encPot get d q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) ≤
    dW (fun q ↦ encPot get d q.2) σ + trialChgRe get d z t σ := by
  have hsplit : ∀ τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ,
      dW (fun q ↦ encPot get d q.2) τ = dW (fun q ↦ encA get d z t.K q.2) τ +
        dW (fun q ↦ ind (unselQ get t) q * encOff d z t.K q.2) τ +
        dW (fun q ↦ ind (liftSet (encCSet get d z)) q) τ := fun τ ↦ by
    simp only [dW, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have hB : encB get d z t.K q.2 = ind (unselQ get t) q * encOff d z t.K q.2 := by
      rw [ind_unselQ]
      unfold encB
      split_ifs <;> ring
    rw [encPot_eq get d z t.K q, hB]
    ring
  have hA : ∑ r : Option X × M, dW (fun q ↦ encA get d z t.K q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
        dW (fun q ↦ encA get d z t.K q.2) σ :=
    sum_dW_conj_of_keep (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r) _
      (fun r a a' h ↦ encA_keep get updOf hu d z t r a a' h) (sum_readKrausH z (updOf t)) σ
  have hB := unselRead_drop hu hk z t (encOff_nonneg d z t.K) (encOff_offCell d z t.K) hσ hnb
  have hsumeq : (∑ r : Option X × M, (hwReadKraus (.readH z (updOf t)) r)ᴴ *
      diagonal (fun q ↦ ((ind (liftSet (encCSet get d z)) q : ℝ) : ℂ)) *
        hwReadKraus (.readH z (updOf t)) r) =
      flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
        (liftSet (encCSet get d z)) + indProj (liftSet (encCSet get d z)) := by
    rw [flipOp, sub_add_cancel]
    rfl
  have hCpost : ∑ r : Option X × M, dW (fun q ↦ ind (liftSet (encCSet get d z)) q)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
      dW (fun q ↦ ind (liftSet (encCSet get d z)) q) σ +
        (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
          (liftSet (encCSet get d z)) * σ).trace.re := by
    rw [sum_dW_conj, hsumeq, Matrix.add_mul, Matrix.trace_add, Complex.add_re, add_comm,
      dW_eq_trace]
    rfl
  have hC := cellFlip_le hu hk d z t hσ hnb
  have hpost : ∑ r : Option X × M, dW (fun q ↦ encPot get d q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
      ∑ r : Option X × M, dW (fun q ↦ encA get d z t.K q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) +
      ∑ r : Option X × M, dW (fun q ↦ ind (unselQ get t) q * encOff d z t.K q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) +
      ∑ r : Option X × M, dW (fun q ↦ ind (liftSet (encCSet get d z)) q)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) := by
    simp only [hsplit, Finset.sum_add_distrib]
  rw [hpost, hsplit σ, hA, hCpost]
  unfold trialCntE trialChgRe
  linarith [hB, hC]

/-- **A trial read port against the potential, refined**: on a state with no decompressed `⊥` at
the read cell, `2^-15 cntEW` plus the potential after the read is at most the potential before
plus `trialChgR`. -/
theorem trialRead_potential_le_ref (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf)
    (d : EvData) {c : HwRead X Z M} (ht : IsTrial updOf c)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : ReadNoBot c σ) :
    (2 ^ 15 : ℝ≥0∞)⁻¹ * cntEW get updOf d c σ +
        ∑' r, potential (diagPot fun s ↦ √(encPot get d s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
      potential (diagPot fun s ↦ √(encPot get d s)) σ + trialChgR get updOf d c σ := by
  have hc := eq_readH_trialOf updOf ht
  simp only [cntEW, trialChgR, ht, ↓reduceIte]
  generalize trialOf updOf c = zt at hc ⊢
  subst hc
  obtain ⟨z, t⟩ := zt
  have hreal := trialRead_drop_ref hu hk d z t hσ hnb
  have h15 : (2 ^ 15 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 ^ 15 : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  have hpost : ∀ r : Option X × M, 0 ≤ dW (fun q ↦ encPot get d q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) := fun r ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (encPot_nonneg get d q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  rw [tsum_fintype]
  simp only [potential_encPot]
  rw [← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hpost r, h15,
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) (trialCntE_nonneg get d z t hσ))
      (Finset.sum_nonneg fun r _ ↦ hpost r)]
  exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le

end trialRef

/-! ## The refined joint count along a run of `runtimeR` -/

section joint

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  {get : Finset S × M' → Selections} {updOf : TrialPt → Finset S × M' → Option X → Finset S × M'}
  {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- **The refined joint count of the selecting reads along a run of `runtimeR`**
(EncPotential's `totalWeight_cntGW_le` with the refined trial port `trialRead_potential_le_ref`):
the count `cntEW` along the run is at most `2^15 (q + P')` plus `2^15` times the charges, the trial
reads charging `trialChgR`. -/
theorem totalWeight_cntEW_le (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf)
    (hlab : ∀ (T T' : Finset S) (m : M'), get (T, m) = get (T', m)) (d : EvData)
    (m₀ : Finset S × M')
    (P : ∀ (i : (recHwSpec X Z S M').Port) (E : QReg),
      Matrix (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E)
        (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E) ℂ → Prop)
    (Inv : ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → Prop)
    (hP : ∀ i E σ, P i E σ → Inv i (MatrixMap.traceRight _ E σ))
    (cS : ∀ p : SpongePort, Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cR : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cP : HwProg X Z → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (hS : ∀ p (σ : Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
        (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef →
      Inv (.inl (.inl (.inl p))) σ →
      ∑' _r : Unit, potential (diagPot fun s ↦ √(encPot get d s))
          (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ) ≤
        potential (diagPot fun s ↦ √(encPot get d s)) σ + (ENNReal.ofReal σ.trace.re + cS p σ))
    (hR : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ),
      ¬ IsTrial updOf c → σ.PosSemidef → Inv (.inl (.inl (.inr c))) σ →
      ∑' r, potential (diagPot fun s ↦ √(encPot get d s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(encPot get d s)) σ + cR c σ)
    (hnb : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M'))
        (Unit × HwReg X Z (Finset S × M')) ℂ), IsTrial updOf c → Inv (.inl (.inl (.inr c))) σ →
      ReadNoBot c σ)
    (hPr : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M'))
        (Unit × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef → Inv (.inl (.inr c)) σ →
      ∑' r, potential (diagPot fun s ↦ √(encPot get d s)) (MatrixMap.conj (hwProgKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(encPot get d s)) σ + (ENNReal.ofReal σ.trace.re + cP c σ))
    (I : Λ.Interp) {B : Type} [Fintype B] [DecidableEq B] (u : B)
    (x : QuantumComp Λ (recHwSpec X Z S M') Ω (QReg.of B)) {q P' : ℕ}
    (hq : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) q)
    (hp : IFreeM.IsChargeBound x (portCharge (extProgCharge X Z (Finset S × M') (recSpec S M')))
      P')
    (hx : (runtimeR m₀).ForallQueries I P x
      ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) :
    (runtimeR m₀).totalWeight I (extWeight (hwCost (cntEW get updOf d) fun _ _ ↦ 0)) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤
      2 ^ 15 * (q + P' : ℕ) + 2 ^ 15 * (runtimeR m₀).totalWeight I
        (portCh X Z S M' cS (fun c σ ↦ trialChgR get updOf d c σ + cR c σ) cP) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  set ρ := (SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix
  have hρ : ρ.PosSemidef :=
    ((SubState.basis u).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef
  have hφ0 := encPot_nonneg get d
  have hp0 : potential (diagPot fun s ↦ √(encPot get d s)) ρ = 0 :=
    (potential_basis_init m₀ hφ0 u).trans
      ((congrArg ENNReal.ofReal (encPot_init get d m₀)).trans ENNReal.ofReal_zero)
  have htr : ENNReal.ofReal ρ.trace.re ≤ 1 := (ofReal_trace_basis_init m₀ u).le
  have hR' : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef → Inv (.inl (.inl (.inr c))) σ →
      (2 ^ 15 : ℝ≥0∞)⁻¹ * cntEW get updOf d c σ + ∑' r, potential
        (diagPot fun s ↦ √(encPot get d s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(encPot get d s)) σ +
          (0 + (trialChgR get updOf d c σ + cR c σ)) := by
    intro c σ hσ hI
    rw [zero_add]
    by_cases ht : IsTrial updOf c
    · exact (trialRead_potential_le_ref hu hk d ht hσ (hnb c σ ht hI)).trans
        (add_le_add le_rfl le_self_add)
    · have h0 : cntEW get updOf d c σ = 0 := by simp only [cntEW, ht, ↓reduceIte]
      have h1 : trialChgR get updOf d c σ = 0 := by simp only [trialChgR, ht, ↓reduceIte]
      rw [h0, h1, mul_zero, zero_add, zero_add]
      exact hR c σ ht hσ hI
  have h := totalWeight_le_potential_runtimeR_inv m₀ hφ0 (encPot_labelFree get hlab d) P Inv hP
    (fun c σ ↦ (2 ^ 15 : ℝ≥0∞)⁻¹ * cntEW get updOf d c σ)
    (fun p σ ↦ ENNReal.ofReal σ.trace.re + cS p σ)
    (fun c σ ↦ 0 + (trialChgR get updOf d c σ + cR c σ))
    (fun c σ ↦ ENNReal.ofReal σ.trace.re + cP c σ) hS hR' hPr I x hρ hx
  have hlow : (2 ^ 15 : ℝ≥0∞)⁻¹ *
      (runtimeR m₀).totalWeight I (extWeight (hwCost (cntEW get updOf d) fun _ _ ↦ 0)) x ρ ≤
      (runtimeR m₀).totalWeight I (extWeight (hwCost
        (fun c σ ↦ (2 ^ 15 : ℝ≥0∞)⁻¹ * cntEW get updOf d c σ) fun _ _ ↦ 0)) x ρ := by
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m₀) I _
      (extWeight (hwCost (cntEW get updOf d) fun _ _ ↦ 0)) x ρ).symm).trans
      (totalWeight_le_totalWeight (runtimeR m₀) I (fun i σ _ ↦ ?_) x hρ)
    rcases i with ((_ | _) | _) | _
    · exact le_of_eq (mul_zero _)
    · exact le_rfl
    · exact le_of_eq (mul_zero _)
    · exact le_of_eq (mul_zero _)
  have hsplit := (totalWeight_le_totalWeight (runtimeR m₀) I
    (w := portCh X Z S M' (fun p σ ↦ ENNReal.ofReal σ.trace.re + cS p σ)
      (fun c σ ↦ 0 + (trialChgR get updOf d c σ + cR c σ))
      (fun c σ ↦ ENNReal.ofReal σ.trace.re + cP c σ))
    (w' := fun i σ ↦ portCh X Z S M' (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (fun _ _ ↦ 0)
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ +
      portCh X Z S M' cS (fun c σ ↦ trialChgR get updOf d c σ + cR c σ) cP i σ)
    (fun i σ _ ↦ le_of_eq (congrFun (congrFun (portCh_add _ _ _ _ _ _) i) σ)) x hρ).trans
    (le_of_eq (totalWeight_add_weight (runtimeR m₀) I _ _ x ρ))
  have ht := (totalWeight_portCh_trace_le m₀ I x hq hp hρ).trans
    ((mul_le_mul_of_nonneg_left htr zero_le).trans_eq (mul_one _))
  have hmain := hlow.trans (h.trans ((add_le_add (le_of_eq hp0) le_rfl).trans_eq (zero_add _)
    |>.trans (hsplit.trans (add_le_add ht le_rfl))))
  have h2 : (2 ^ 15 : ℝ≥0∞) ≠ 0 := by positivity
  have h2' : (2 ^ 15 : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have e : ∀ w : ℝ≥0∞, w = 2 ^ 15 * ((2 ^ 15 : ℝ≥0∞)⁻¹ * w) := fun w ↦ by
    rw [← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
  exact (e _).trans_le ((mul_le_mul_of_nonneg_left hmain zero_le).trans_eq (mul_add _ _ _))

end joint

/-! ## The refined charges at the calls -/

section ports

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  (get : Finset S × M' → Selections)
  (updOf : TrialPt → Finset S × M' → Option X → Finset S × M')

open scoped Classical in
/-- **The off-head mass of a trial read port**: the weight off `TrialHead` (`0` at the other read
ports). -/
noncomputable def offHeadW (d : EvData) (c : HwRead X Z (Finset S × M'))
    (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ) :
    ℝ≥0∞ :=
  if IsTrial updOf c then ENNReal.ofReal (∑ q, (if TrialHead d (trialOf updOf c).1
    (trialOf updOf c).2 q.2 then (0 : ℝ) else 1) * (σ q q).re) else 0

omit [DecidableEq S] [DecidableEq M'] in
open scoped Classical in
/-- EncPotential's `cwRecW` through `CwRecG`. -/
theorem cwRecW_eq (c : HwRead X Z (Finset S × M'))
    (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ) :
    cwRecW get updOf c σ = if IsTrial updOf c then ENNReal.ofReal (∑ a, if CwRecG get
      (trialOf updOf c).1 (trialOf updOf c).2 a.2 then (σ a a).re else 0) else 0 := by
  unfold cwRecW
  split_ifs
  · exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun a _ ↦ if_congr Iff.rfl rfl rfl)
  · rfl

/-- **The charge of a read call per unit of trace, refined**: the `k`, `k'` reads'
`potCap (ε + 2/|X| + 2/|Z| + 2 √ε)` and the trial reads' `6/|X|`. -/
noncomputable def kapR6 (nD P : ℕ) : ℝ :=
  potCap nD P * (epsQ nD P + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ nD P)) +
    6 / (Fintype.card X : ℝ)

theorem kapR6_nonneg (nD P : ℕ) : 0 ≤ kapR6 nD P := by
  have := epsQ_nonneg nD P
  unfold kapR6
  positivity

omit [DecidableEq S] [DecidableEq M'] in
/-- **The refined trial charge against the codeword-recorded and off-head masses** (real form):
where the count off the read cell is at most `C`, `trialChgRe ≤ 3 C cw + 3 off + 6/|X| tr σ`. -/
theorem trialChgRe_le (d : EvData) (z : Z) (t : TrialPt) {C : ℝ}
    {σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ}
    (hσ : σ.PosSemidef) (hC : ∀ a, encOff d z t.K a.2 ≤ C ∨ σ a a = 0) :
    trialChgRe get d z t σ ≤ 3 * C * (∑ a, if CwRecG get z t a.2 then (σ a a).re else 0) +
      3 * (∑ a, (if TrialHead d z t a.2 then (0 : ℝ) else 1) * (σ a a).re) +
        6 / (Fintype.card X : ℝ) * σ.trace.re := by
  have hre : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ a, (σ a a).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  have h1 : ∑ a, (if CwRecG get z t a.2 then (1 : ℝ) else 0) * (encOff d z t.K a.2 *
      (σ a a).re) ≤ C * ∑ a, if CwRecG get z t a.2 then (σ a a).re else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ ↦ ?_
    split_ifs
    · rw [one_mul]
      rcases hC a with h | h
      · exact mul_le_mul_of_nonneg_right h (hre a)
      · rw [h, Complex.zero_re, mul_zero, mul_zero]
    · rw [zero_mul, mul_zero]
  unfold trialChgRe
  rw [htr]
  nlinarith [h1]

/-- **The refined trial charge at the calls**: `3 C cwRecW + 3 offHeadW + 6/|X| tr σ` with
`C = nW P + nD` (`trialChgRe_le`, the count bounded by the grades). -/
theorem trialChgR_le_port (Ok : HwRead X Z (Finset S × M') → Prop) (d : EvData) {nD P : ℕ}
    (m₀ : Finset S × M') (c : HwRead X Z (Finset S × M'))
    {σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ}
    (hσ : σ.PosSemidef) (hI : PortInv Ok nD P m₀ (.inl (.inl (.inr c))) σ) :
    trialChgR get updOf d c σ ≤
      ENNReal.ofReal (3 * ((nW P + nD : ℕ) : ℝ)) * cwRecW get updOf c σ +
        3 * offHeadW updOf d c σ + ENNReal.ofReal (6 / (Fintype.card X : ℝ) * σ.trace.re) := by
  have hC : ∀ (z : Z) (K : Key) a, encOff d z K a.2 ≤ ((nW P + nD : ℕ) : ℝ) ∨
      σ a a = 0 := fun z K a ↦ by
    by_cases h0 : σ a a = 0
    · exact .inr h0
    · have hs := (hI.2.1 a a h0).1
      refine .inl ((encOff_le_grade d _ _ a.2).trans ?_)
      have : dbGrade a.2.2.1 + dbGrade a.2.1 ≤ nW P + nD := by
        have h1 : dbGrade a.2.1 ≤ nD := hs.1
        have h2 : dbGrade a.2.2.1 ≤ P := hs.2
        unfold nW
        omega
      exact_mod_cast this
  rw [cwRecW_eq]
  by_cases ht : IsTrial updOf c
  · simp only [trialChgR, offHeadW, ht, ↓reduceIte]
    generalize trialOf updOf c = zt
    obtain ⟨z, t⟩ := zt
    dsimp only
    have h3 : (0 : ℝ) ≤ 3 * ((nW P + nD : ℕ) : ℝ) := by positivity
    have hre : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    have hR0 : 0 ≤ ∑ a, if CwRecG get z t a.2 then (σ a a).re else 0 :=
      Finset.sum_nonneg fun a _ ↦ by split_ifs; exacts [hre a, le_rfl]
    have hW0 : 0 ≤ ∑ a, (if TrialHead d z t a.2 then (0 : ℝ) else 1) * (σ a a).re :=
      Finset.sum_nonneg fun a _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hre a)
    calc ENNReal.ofReal (trialChgRe get d z t σ)
        ≤ ENNReal.ofReal (3 * ((nW P + nD : ℕ) : ℝ) *
            (∑ a, if CwRecG get z t a.2 then (σ a a).re else 0) +
          3 * (∑ a, (if TrialHead d z t a.2 then (0 : ℝ) else 1) * (σ a a).re) +
            6 / (Fintype.card X : ℝ) * σ.trace.re) :=
          ENNReal.ofReal_le_ofReal (trialChgRe_le get d z t hσ (hC z t.K))
      _ ≤ ENNReal.ofReal (3 * ((nW P + nD : ℕ) : ℝ) *
            (∑ a, if CwRecG get z t a.2 then (σ a a).re else 0)) +
          ENNReal.ofReal (3 * (∑ a, (if TrialHead d z t a.2 then (0 : ℝ) else 1) * (σ a a).re)) +
            ENNReal.ofReal (6 / (Fintype.card X : ℝ) * σ.trace.re) :=
          ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
      _ = _ := by
          have e1 : ENNReal.ofReal (3 * ((nW P + nD : ℕ) : ℝ) *
              (∑ a, if CwRecG get z t a.2 then (σ a a).re else 0)) =
              ENNReal.ofReal (3 * ((nW P + nD : ℕ) : ℝ)) *
                ENNReal.ofReal (∑ a, if CwRecG get z t a.2 then (σ a a).re else 0) :=
            ENNReal.ofReal_mul h3
          have e2 : ENNReal.ofReal (3 * (∑ a, (if TrialHead d z t a.2 then (0 : ℝ) else 1) *
              (σ a a).re)) = 3 * ENNReal.ofReal (∑ a, (if TrialHead d z t a.2 then (0 : ℝ) else 1) *
                (σ a a).re) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]
          rw [e1, e2]
  · simp only [trialChgR, ht, ↓reduceIte, zero_le]

/-- **The charge of a read call at the calls, refined**: the trial charge and `cRq` together are
at most `3 C cwRecW + 3 offHeadW + kapR6 tr σ`. -/
theorem readChargeR_le (Ok : HwRead X Z (Finset S × M') → Prop) (d : EvData) {nD P : ℕ}
    (m₀ : Finset S × M') (c : HwRead X Z (Finset S × M'))
    {σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ}
    (hσ : σ.PosSemidef) (hI : PortInv Ok nD P m₀ (.inl (.inl (.inr c))) σ) :
    trialChgR get updOf d c σ + cRq nD P c σ ≤
      ENNReal.ofReal (3 * ((nW P + nD : ℕ) : ℝ)) * cwRecW get updOf c σ +
        3 * offHeadW updOf d c σ + ENNReal.ofReal (kapR6 nD P) * ENNReal.ofReal σ.trace.re := by
  have htr : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have he := epsQ_nonneg nD P
  refine (add_le_add (trialChgR_le_port get updOf Ok d m₀ c hσ hI) le_rfl).trans ?_
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  unfold cRq
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) htr)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) htr)),
    ← ENNReal.ofReal_mul (kapR6_nonneg nD P)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold kapR6
  ring

end ports

/-! ## The empty-cell flips of a trial read -/

section flips

/-- A trial read never removes a selection. -/
theorem sel_le_trialUpd (t : TrialPt) (m : Mem HPos) (o : Option X) :
    m.2.Le (trialUpd t m o).2 := by
  rw [show trialUpd t m o = (m.1, cwUpd t.K t.x t.xi m.2 o) from rfl, snd_pair]
  exact le_cwUpd t.K t.x t.xi m.2 o

/-- **A selected key stays selected** under `trialUpd`. -/
theorem trialKeep_trialUpd : TrialKeep (Prod.snd : Mem HPos → Selections) trialUpd := by
  intro t m o hm
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hm
  rw [sel_le_trialUpd t m o t.K c hc]
  exact Option.some_ne_none c

/-- **The template's trial updates record codeword selections.** -/
theorem cwTrialUpd_trialUpd : CwTrialUpd (Prod.snd : Mem HPos → Selections) trialUpd :=
  cwTrialUpd_cwUpd HPos

/-- **More selections keep every Struct and Enc target.** -/
theorem sphTgt_le_mono {d : EvData} {Ex : Set Slot} {sel sel' : Selections} (hle : sel.Le sel')
    {t : List X} {y : Digest} (h : d.sphTgt Ex sel t = some y) : d.sphTgt Ex sel' t = some y := by
  obtain ⟨s, hs, hst | hst⟩ := sphTgt_eq_some_iff.1 h
  · exact sphTgt_eq_some_iff.2 ⟨s, hs, .inl hst⟩
  obtain ⟨l, τ, e, x', rfl, hc, hne⟩ := encTgt_eq_some_iff.1 hst
  exact sphTgt_enc hs (hle _ _ hc) hne

/-- Rates with the same digest select the same digests. -/
theorem cwSel_congr {m : Selections} {K : Key} {x xi xi' : X} (h : trunc128 xi = trunc128 xi')
    (w : X) : cwSel m K x xi w = cwSel m K x xi' w := by
  unfold cwSel
  rw [trunc128_add_congr h]

variable {p : Pub} {v : (s : HPos) → XD s}

/-- **A state in `BadR` with the cell empty has no flip value** (the slices are up-closed and a
trial read only adds targets). -/
theorem not_hFlip_of_badR {z : Z} {t : TrialPt} {q : Unit × HwReg X Z (Mem HPos)}
    (hb : q.2 ∈ BadR p v progCap) (hD : q.2.1.1 z = none) (w : X) :
    ¬ hFlip (BadR p v progCap) z (trialUpd t) q w := by
  have hfill : ∀ (u : Option X) (m : Mem HPos), (∀ l y, (evData p v).sphTgt
      ((evData p v).exS q.2.2.1) q.2.2.2.2 l = some y →
        (evData p v).sphTgt ((evData p v).exS q.2.2.1) m.2 l = some y) →
      ((Function.update q.2.1.1 z u, q.2.1.2), q.2.2.1, m) ∈ BadR p v progCap :=
    fun u m hm ↦ mem_bad_fill (S := HPos) (d := evData p v) (N := progCap) (D := q.2.1)
      (W := q.2.2.1) (m := q.2.2.2) hb hD u m.1 m.2 hm
  rintro (h | ⟨u, h⟩)
  · exact h (iff_of_true (hfill (some w) q.2.2.2 fun _ _ h ↦ h) hb)
  · exact h (iff_of_true (hfill u _ fun _ _ h ↦
      sphTgt_le_mono (sel_le_trialUpd t q.2.2.2 (some w)) h) (hfill u q.2.2.2 fun _ _ h ↦ h))

/-- **A flip value of a state outside `BadR` whose key is selected** records a value that puts the
state into `BadR` (the memory does not move). -/
theorem hFlip_sel {z : Z} {t : TrialPt} {q : Unit × HwReg X Z (Mem HPos)}
    (hb : q.2 ∉ BadR p v progCap) (hm : q.2.2.2.2 t.K ≠ none) {w : X}
    (h : hFlip (BadR p v progCap) z (trialUpd t) q w) :
    ((Function.update q.2.1.1 z (some w), q.2.1.2), q.2.2) ∈ BadR p v progCap := by
  have hkeep : trialUpd t q.2.2.2 (some w) = q.2.2.2 := by
    show (q.2.2.2.1, cwUpd t.K t.x t.xi q.2.2.2.2 (some w)) = q.2.2.2
    have h0 : cwUpd t.K t.x t.xi q.2.2.2.2 (some w) = q.2.2.2.2 := by
      show (if q.2.2.2.2 t.K = none then cwSel q.2.2.2.2 t.K t.x t.xi w else q.2.2.2.2) = _
      rw [ite_eq_right hm]
    rw [h0]
  rcases h with h | ⟨u, h⟩
  · by_contra hc
    exact h (iff_of_false hc hb)
  · rw [hkeep] at h
    exact absurd Iff.rfl h

/-- Recording a value at an empty cell and emptying it again gives the cell back. -/
theorem update_update_none {α β : Type*} [DecidableEq α] (f : α → Option β) (a : α) (b : β)
    (h : f a = none) : Function.update (Function.update f a (some b)) a none = f := by
  rw [Function.update_idem, Function.update_eq_self_iff.2 h.symm]

/-- **A flip value of a selected key's head**: recording it makes the trial's tail reach its
target (RecBadMass' `recBad_cases`; the coverage part needs an `H_msg` tail). -/
theorem flip_sel_tgt {z : Z} {t : TrialPt} {q : Unit × HwReg X Z (Mem HPos)}
    (hb : q.2 ∉ BadR p v progCap) (hW : q.2.2.1.1 z = none) (hD : q.2.1.1 z = none)
    (hm : q.2.2.2.2 t.K ≠ none) (hslot : EncAt (evData p v) t.K [t.x]) {xi : X}
    (hxi : trunc128 xi = trunc128 t.xi) (hhead : IsHeadTail p.perm (union q.2.2.1 q.2.1) [t.x] z xi)
    {w : X} (h : hFlip (BadR p v progCap) z (trialUpd t) q w) :
    (evData p v).sphTgtHw q.2.2.1 q.2.2.2 [t.x] = some (trunc128 (t.xi + w)) := by
  have hF := hFlip_sel hb hm h
  have hRB : RecBad p v z ((Function.update q.2.1.1 z (some w), q.2.1.2), q.2.2) := by
    refine ⟨hW, ?_, hF, ?_⟩
    · dsimp only
      rw [Function.update_self]
      exact Option.some_ne_none w
    · dsimp only
      rw [update_update_none q.2.1.1 z w hD]
      exact hb
  rcases recBad_cases p v hslot hRB with ⟨-, y, hy, ht⟩ | ⟨-, -, hoff⟩
  · dsimp only at hy
    rw [Function.update_self] at hy
    obtain rfl := Option.some.inj hy
    exact ht
  · exact absurd ⟨xi, hxi, (isHeadTail_congr
      (union_k_h q.2.2.1 q.2.1.1 (Function.update q.2.1.1 z (some w)) q.2.1.2)
      (union_k'_h q.2.2.1 q.2.1.1 (Function.update q.2.1.1 z (some w)) q.2.1.2)).1 hhead⟩ hoff

/-- **A flip value of a state outside `BadR` with a selection read** (at a rate with the trial's
digest) records a codeword selection that puts the state into `Bad`. -/
theorem hFlip_unsel {z : Z} {t : TrialPt} {xi : X}
    {q : Unit × HwReg X Z (Mem HPos)} (hb : q.2 ∉ BadR p v progCap)
    (hsr : SelectRead (evData p v) q.2.1 q.2.2.1 q.2.2.2.2 z t.K t.x xi)
    (hxi : trunc128 xi = trunc128 t.xi) {w : X} (h : hFlip (BadR p v progCap) z (trialUpd t) q w) :
    ∃ u : Option X, ((Function.update q.2.1.1 z u, q.2.1.2), q.2.2.1,
      ((q.2.2.2.1, cwSel q.2.2.2.2 t.K t.x xi w) : Mem HPos)) ∈ Bad (evData p v) progCap := by
  have hb' : (q.2.1, q.2.2.1, ((q.2.2.2.1, q.2.2.2.2) : Mem HPos)) ∉ Bad (evData p v) progCap := hb
  have hkeep : ∀ u, ((Function.update q.2.1.1 z u, q.2.1.2), q.2.2) ∉ BadR p v progCap :=
    fun u ↦ not_mem_bad_read_keep hb' hsr u
  rcases h with h | ⟨u, h⟩
  · exact absurd (iff_of_false (hkeep (some w)) hb) h
  · refine ⟨u, ?_⟩
    have h1 : ((Function.update q.2.1.1 z u, q.2.1.2), q.2.2.1, trialUpd t q.2.2.2 (some w)) ∈
        BadR p v progCap := by
      by_contra hc
      exact h (iff_of_false hc (hkeep u))
    have hm : trialUpd t q.2.2.2 (some w) = (q.2.2.2.1, cwSel q.2.2.2.2 t.K t.x xi w) := by
      rw [show trialUpd t q.2.2.2 (some w) =
          (q.2.2.2.1, cwUpd t.K t.x t.xi q.2.2.2.2 (some w)) from rfl,
        cwUpd_some_of_none _ _ _ hsr.hm, cwSel_congr hxi.symm]
    rw [hm] at h1
    exact h1

variable (p v)

open scoped Classical in
/-- **The flip values of an empty, not hardwired cell at a trial read**, over `|X|`: at most
`2^-128` times the count off the cell on the selecting states, `2^-128` on the others, and `1` off
the trial head. In `BadR` there is none; outside `BadR` the union is good; a selected key's head
flips hit its tail's target (`flip_sel_tgt`); an unselected key at its trial head selects only a
codeword the other tails of the encoding slot reach (`card_flip_readCw_le`). -/
theorem card_hFlip_div_le (z : Z) (t : TrialPt) (q : Unit × HwReg X Z (Mem HPos))
    (hW : q.2.2.1.1 z = none) (hD : q.2.1.1 z = none) (hN : dbGrade q.2.2.1 ≤ progCap) :
    ((Finset.univ.filter (hFlip (BadR p v progCap) z (trialUpd t) q)).card : ℝ) /
        Fintype.card X ≤
      (2 ^ 128 : ℝ)⁻¹ * ((if EmptyUnsel Prod.snd z t q.2 then 1 else 0) *
        encOff (evData p v) z t.K q.2) + (2 ^ 128 : ℝ)⁻¹ +
        (if TrialHead (evData p v) z t q.2 then (0 : ℝ) else 1) := by
  have hN0 : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  have hE0 : 0 ≤ (2 ^ 128 : ℝ)⁻¹ * ((if EmptyUnsel Prod.snd z t q.2 then 1 else 0) *
      encOff (evData p v) z t.K q.2) :=
    mul_nonneg (by positivity) (mul_nonneg (by split_ifs <;> norm_num) (encOff_nonneg _ _ _ _))
  have hT0 : 0 ≤ (if TrialHead (evData p v) z t q.2 then (0 : ℝ) else 1) := by
    split_ifs <;> norm_num
  have h2 : (0 : ℝ) ≤ (2 ^ 128 : ℝ)⁻¹ := by positivity
  set c := (Finset.univ.filter (hFlip (BadR p v progCap) z (trialUpd t) q)).card with hc
  by_cases hb : q.2 ∈ BadR p v progCap
  · have h0 : c = 0 := by
      rw [hc, Finset.filter_false_of_mem fun w _ ↦ not_hFlip_of_badR hb hD w, Finset.card_empty]
    rw [h0, Nat.cast_zero, zero_div]
    linarith
  have hG : Good (evData p v).perm (union q.2.2.1 q.2.1) :=
    good_of_not_mem_bad (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hb hN
  by_cases hh : TrialHead (evData p v) z t q.2
  swap
  · rw [ite_eq_right hh]
    have hle : (c : ℝ) / Fintype.card X ≤ 1 :=
      (div_le_one hN0).2 (Nat.cast_le.2 ((Finset.card_filter_le _ _).trans_eq Finset.card_univ))
    linarith
  obtain ⟨hslot, xi, hxi, hhead⟩ := hh.resolve_left (not_not.2 hG)
  rw [ite_eq_left hh, add_zero]
  by_cases hm : q.2.2.2.2 t.K = none
  · have hsr : SelectRead (evData p v) q.2.1 q.2.2.1 q.2.2.2.2 z t.K t.x xi :=
      ⟨hW, hD, hm, hslot, hhead⟩
    have hb' : (q.2.1, q.2.2.1, ((q.2.2.2.1, q.2.2.2.2) : Mem HPos)) ∉
        Bad (evData p v) progCap := hb
    have hcard : c ≤ encCwCount (evData p v) (union q.2.2.1 q.2.1) t.K * 2 ^ 960 :=
      card_filter_le_of_imp (card_flip_readCw_le hb' hsr) fun w hw ↦ hFlip_unsel hb hsr hxi hw
    have hE : EmptyUnsel Prod.snd z t q.2 := And.intro hW (And.intro hD hm)
    have henc : encOff (evData p v) z t.K q.2 =
        encCwCount (evData p v) (union q.2.2.1 q.2.1) t.K :=
      encOff_of_selectRead Prod.snd (t := ⟨t.K, t.x, xi⟩) (evData p v) hsr hG
    rw [ite_eq_left hE, one_mul, henc]
    have hd : (c : ℝ) / Fintype.card X ≤
        ((encCwCount (evData p v) (union q.2.2.1 q.2.1) t.K * 2 ^ 960 : ℕ) : ℝ) /
          Fintype.card X :=
      div_le_div_of_nonneg_right (Nat.cast_le.2 hcard) hN0.le
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, two_pow_div_card_X,
      mul_comm] at hd
    linarith
  · have hcard : c ≤ 2 ^ 960 := by
      rcases hT : (evData p v).sphTgtHw q.2.2.1 q.2.2.2 [t.x] with _ | dg
      · have h0 : c = 0 := by
          rw [hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro w _ hw
          have h' := flip_sel_tgt hb hW hD hm hslot hxi hhead hw
          rw [hT] at h'
          exact Option.some_ne_none _ h'.symm
        rw [h0]
        exact Nat.zero_le _
      · exact card_filter_le_of_imp (card_fiber_trunc128_add t.xi dg) fun w hw ↦ by
          have h' := flip_sel_tgt hb hW hD hm hslot hxi hhead hw
          rw [hT] at h'
          exact (Option.some.inj h').symm
    have hd : (c : ℝ) / Fintype.card X ≤ ((2 ^ 960 : ℕ) : ℝ) / Fintype.card X :=
      div_le_div_of_nonneg_right (Nat.cast_le.2 hcard) hN0.le
    rw [Nat.cast_pow, Nat.cast_ofNat, two_pow_div_card_X] at hd
    linarith

/-- **The empty-cell flips of a read port against the refined count**: on states whose hardwired
grade is at most `progCap`, `encRW ≤ 2^-128 cntEW + 2^-128 tr σ + offHeadW`. -/
theorem encRW_le (c : HwRead X Z (Mem HPos))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hgr : ∀ a, dbGrade a.2.2.1 ≤ progCap ∨ σ a a = 0) :
    encRW p v c σ ≤ ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * cntEW Prod.snd trialUpd (evData p v) c σ +
      ENNReal.ofReal ((2 ^ 128 : ℝ)⁻¹ * σ.trace.re) + offHeadW trialUpd (evData p v) c σ := by
  by_cases ht : IsTrial trialUpd c
  · simp only [encRW, cntEW, offHeadW, ht, ↓reduceIte]
    generalize trialOf trialUpd c = zt
    obtain ⟨z, t⟩ := zt
    have hre : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    have htr : σ.trace.re = ∑ a, (σ a a).re := by rw [Matrix.trace, Complex.re_sum]; rfl
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine (ENNReal.ofReal_le_ofReal ?_).trans
      (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl))
    unfold encRSum trialCntE
    rw [htr, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ ↦ ?_
    by_cases h0 : σ a a = 0
    · rw [h0, Complex.zero_re]
      simp only [mul_zero, add_zero, le_refl]
    have hN := (hgr a).resolve_right h0
    by_cases hcell : a.2.2.1.1 z = none ∧ a.2.1.1 z = none
    · rw [ite_eq_left hcell]
      have h := mul_le_mul_of_nonneg_right (card_hFlip_div_le p v z t a hcell.1 hcell.2 hN) (hre a)
      refine h.trans_eq ?_
      ring
    · rw [ite_eq_right hcell, zero_mul]
      have h1 : 0 ≤ (2 ^ 128 : ℝ)⁻¹ * ((if EmptyUnsel Prod.snd z t a.2 then 1 else 0) *
          (encOff (evData p v) z t.K a.2 * (σ a a).re)) :=
        mul_nonneg (by positivity) (mul_nonneg (by split_ifs <;> norm_num)
          (mul_nonneg (encOff_nonneg _ _ _ _) (hre a)))
      have h2 : 0 ≤ (if TrialHead (evData p v) z t a.2 then (0 : ℝ) else 1) * (σ a a).re :=
        mul_nonneg (by split_ifs <;> norm_num) (hre a)
      have h3 : 0 ≤ (2 ^ 128 : ℝ)⁻¹ * (σ a a).re := mul_nonneg (by positivity) (hre a)
      linarith
  · simp only [encRW, ht, ↓reduceIte, zero_le]

end flips

/-! ## The challenge prefix -/

section prefixDefs

/-- **The port invariant of the prefix**: EncPorts' `PortInv` for the `EncReadOk` reads of the
trial update, at database grade `6q + clsCap` and hardwired grade `progCap`. -/
def EncInv (q : ℕ) (i : (recHwSpec X Z HPos Selections).Port)
    (τ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ) : Prop :=
  PortInv (EncReadOk trialUpd) (6 * q + clsCap) progCap m0R i τ

/-- **The refined joint count along the challenge prefix** (`cntEW`). -/
noncomputable def cntEP (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments
    (extWeight (hwCost (cntEW Prod.snd trialUpd (evData p v)) fun _ _ ↦ 0)) (prefixR pol A p v)
    initR

/-- **The off-head mass of the trial reads along the challenge prefix**. -/
noncomputable def offHeadPre (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments
    (extWeight (hwCost (offHeadW trialUpd (evData p v)) fun _ _ ↦ 0)) (prefixR pol A p v) initR

/-- **The constant of the refined Enc term**: `2^-128 (2^15 (6q + progCap) + 2^15 (6q kapS +
clsCap kapR6) + clsCap)`. -/
noncomputable def encE0 (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * (2 ^ 15 * ((6 * q + progCap : ℕ) : ℝ≥0∞) +
    2 ^ 15 * (ENNReal.ofReal (kapS (6 * q + clsCap) progCap) * ((6 * q : ℕ) : ℝ≥0∞) +
      ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * (clsCap : ℝ≥0∞)) + (clsCap : ℝ≥0∞))

/-- **The recorded-mass factor of the refined Enc term**: `2^-128 2^15 3 (nW progCap + 6q +
clsCap)`. -/
noncomputable def encBeta (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ *
    (2 ^ 15 * ENNReal.ofReal (3 * ((nW progCap + (6 * q + clsCap) : ℕ) : ℝ)))

/-- **The program-jump factor of the refined Enc term**: `2^-128 2^15 potCap`. -/
noncomputable def encGamma (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * (2 ^ 15 * (potCap (6 * q + clsCap) progCap : ℝ≥0∞))

/-- **The off-head factor of the refined Enc term**: `1 + 2^-128 2^15 3`. -/
noncomputable def encDelta : ℝ≥0∞ :=
  1 + ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * (2 ^ 15 * 3)

/-- **The constant of the prefix's linear charge** `2 encRPre + hwMovePre + kapRR clsCap`:
`2 E₀ q + (2 δ + 1) 2^-511 clsCap + kapRR clsCap`. -/
noncomputable def encEC (q : ℕ) : ℝ≥0∞ :=
  2 * encE0 q + (2 * encDelta + 1) * (ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞)) +
    ENNReal.ofReal kapRR * (clsCap : ℝ≥0∞)

end prefixDefs

section prefixRef

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)

/-- The prefix calls only `EncReadOk` reads. -/
theorem okChg_prefixR (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (prefixR pol A p v) (portCharge (okChg (EncReadOk trialUpd))) 0 :=
  isChargeBound_mono_charge (fun _ a ↦ by
    rcases a with o | ⟨i, E, ℓ⟩
    · exact le_rfl
    · exact okChg_encReadOk_le_bR i) (chgB_prefixR pol A p v)

include hperm hsign

/-- **The invariant holds at every call of the prefix** (EncPorts' `forallQueries_portInv`). -/
theorem forallQueries_encInv (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    ∃ P : ∀ (i : (recHwSpec X Z HPos Selections).Port) (E : QReg),
      Matrix (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E)
        (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E) ℂ →
          Prop, (∀ i E σ, P i E σ → EncInv q i (MatrixMap.traceRight _ E σ)) ∧
      (runtimeR m0R).ForallQueries .instruments P (prefixR pol A p v) initR :=
  forallQueries_portInv (EncReadOk trialUpd) m0R .instruments () (prefixR pol A p v)
    (advCalls_prefixR hperm hsign pol p v) (clsCalls_prefixR hperm hsign pol p v)
    (okChg_prefixR pol p v) (progCalls_prefixR hperm hsign pol p v)

/-- **The empty-cell flips along the prefix against the refined joint count**:
`encRPre ≤ 2^-128 cntEP + 2^-128 clsCap + offHeadPre`. -/
theorem encRPre_le_cntEP (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    encRPre pol A p v ≤ ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * cntEP pol A p v +
      ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * (clsCap : ℝ≥0∞) + offHeadPre pol A p v := by
  obtain ⟨P, hP, hx⟩ := forallQueries_encInv (q := q) hperm hsign pol p v
  set wC : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (cntEW Prod.snd trialUpd (evData p v)) fun _ _ ↦ 0)
  set wT : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re)
  set wO : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (offHeadW trialUpd (evData p v)) fun _ _ ↦ 0)
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (EncInv q) hP
    (w' := fun i σ ↦ ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * wC i σ +
      ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * wT i σ + wO i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR pol A p v) initR_posSemidef hx).trans ?_
  · rcases i with ((sp | c) | c) | T
    · exact zero_le
    · show encRW p v c σ ≤
          ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * cntEW Prod.snd trialUpd (evData p v) c σ +
          ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * ENNReal.ofReal σ.trace.re +
            offHeadW trialUpd (evData p v) c σ
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact encRW_le p v c hσ fun a ↦ by
        by_cases h0 : σ a a = 0
        · exact .inr h0
        · exact .inl (hI.2.1 a a h0).1.2
    · exact zero_le
    · exact zero_le
  · refine (totalWeight_le_lin (runtimeR m0R) .instruments _ wC wT wO _ _ (fun _ _ _ ↦ le_rfl)
      (prefixR pol A p v) initR_posSemidef).trans (add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left ?_ zero_le)) le_rfl)
    exact totalWeight_calls_le (prefixR pol A p v) (clsCalls_prefixR hperm hsign pol p v)

/-- **The refined joint count on the challenge prefix**: at data with `PermGood π 18`, for
`q ≤ 2^64`, with the prefix's calls inside a hardwired table, at most `2^15 (6q + progCap)` plus
`2^15` times the charges: `3C` per unit of the codeword-recorded mass (`cwRecPre`,
`C = nW progCap + 6q + clsCap`), `3` per unit of the off-head mass (`offHeadPre`), `kapS` per `k`,
`k'` sponge call, `kapR6` per read call and `potCap` per unit of the program jump weight, at most
`kfPre + recJPre` (EncPorts' `totalWeight_kJumpW_le`). -/
theorem cntEP_le (hq : q ≤ 2 ^ 64) (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) {Wt : Hw X Z} (hW : StaysInR pol A p v Wt) :
    cntEP pol A p v ≤ 2 ^ 15 * ((6 * q + progCap : ℕ) : ℝ≥0∞) + 2 ^ 15 *
      (ENNReal.ofReal (3 * ((nW progCap + (6 * q + clsCap) : ℕ) : ℝ)) * cwRecPre pol A p v +
        3 * offHeadPre pol A p v +
        (ENNReal.ofReal (kapS (6 * q + clsCap) progCap) * ((6 * q : ℕ) : ℝ≥0∞) +
          ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * (clsCap : ℝ≥0∞) +
          (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * (kfPre pol A p v + recJPre pol A p v))) := by
  obtain ⟨P, hP, hx⟩ := forallQueries_encInv (q := q) hperm hsign pol p v
  have h := totalWeight_cntEW_le cwTrialUpd_trialUpd trialKeep_trialUpd (fun _ _ _ ↦ rfl)
    (evData p v) m0R P (EncInv q) hP (cSq (6 * q + clsCap) progCap)
    (cRq (6 * q + clsCap) progCap) (progJump (encPot Prod.snd (evData p v)))
    (fun sp _ hσ hI ↦ hS_port Prod.snd (EncReadOk trialUpd) (evData p v) hπ m0R sp hσ hI)
    (fun c _ ht hσ hI ↦ hR_port Prod.snd trialUpd (evData p v) hπ m0R c ht hσ hI)
    (fun c _ _ hI ↦ readNoBot_of_noBot c hI.2.2)
    (fun c _ hσ _ ↦ tsum_potential_prog_le (encPot_nonneg Prod.snd (evData p v)) c hσ)
    .instruments () (prefixR pol A p v) (advCalls_prefixR hperm hsign pol p v)
    (progCalls_prefixR hperm hsign pol p v) hx
  refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le))
  set C : ℝ := ((nW progCap + (6 * q + clsCap) : ℕ) : ℝ)
  set wM : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (cwRecW Prod.snd trialUpd) fun _ _ ↦ 0)
  set wO : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (offHeadW trialUpd (evData p v)) fun _ _ ↦ 0)
  set wR : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ _ ↦ 0)
  set wJ : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ _ ↦ 0) (kJumpW (evData p v)))
  set wS : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ := fun i σ ↦
    ((if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal σ.trace.re
  set wX : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ := fun i σ ↦
    ENNReal.ofReal (kapS (6 * q + clsCap) progCap) * wS i σ +
      ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * wR i σ +
      (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * wJ i σ
  have hle := totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (EncInv q) hP
    (w := portCh X Z HPos Selections (cSq (6 * q + clsCap) progCap)
      (fun c σ ↦ trialChgR Prod.snd trialUpd (evData p v) c σ + cRq (6 * q + clsCap) progCap c σ)
      (progJump (encPot Prod.snd (evData p v))))
    (w' := fun i σ ↦ ENNReal.ofReal (3 * C) * wM i σ + 3 * wO i σ + wX i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR pol A p v) initR_posSemidef hx
  · have hS : (runtimeR m0R).totalWeight .instruments wS (prefixR pol A p v) initR ≤
        ((6 * q : ℕ) : ℝ≥0∞) :=
      (totalWeight_chargeTrace_le (runtimeR m0R) .instruments
        (fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1)
        (prefixR pol A p v) (advCalls_prefixR hperm hsign pol p v) initR_posSemidef).trans_eq
          ((congrArg (((6 * q : ℕ) : ℝ≥0∞) * ·) (ofReal_trace_basis_init m0R ())).trans
            (mul_one _))
    have hR : (runtimeR m0R).totalWeight .instruments wR (prefixR pol A p v) initR ≤ clsCap :=
      (totalWeight_le_totalWeight (runtimeR m0R) .instruments
        (w' := extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
          fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (fun i σ _ ↦ by
            rcases i with ((sp | c) | c) | T
            · exact le_rfl
            · exact le_rfl
            · exact zero_le
            · exact le_rfl) (prefixR pol A p v) initR_posSemidef).trans
        (totalWeight_calls_le (prefixR pol A p v) (clsCalls_prefixR hperm hsign pol p v))
    obtain ⟨W, hWW, hxW⟩ := hW
    have hJ : (runtimeR m0R).totalWeight .instruments wJ (prefixR pol A p v) initR ≤
        kfPre pol A p v + recJPre pol A p v :=
      totalWeight_kJumpW_le trialUpd (evData p v) m0R .instruments () (prefixR pol A p v)
        (progCap_add_le hq) Wt (advCalls_prefixR hperm hsign pol p v)
        (clsCalls_prefixR hperm hsign pol p v) (okChg_prefixR pol p v)
        (progCalls_prefixR hperm hsign pol p v) W hWW hxW
    have hX : (runtimeR m0R).totalWeight .instruments wX (prefixR pol A p v) initR ≤
        ENNReal.ofReal (kapS (6 * q + clsCap) progCap) * ((6 * q : ℕ) : ℝ≥0∞) +
          ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * (clsCap : ℝ≥0∞) +
          (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * (kfPre pol A p v + recJPre pol A p v) :=
      (totalWeight_le_lin (runtimeR m0R) .instruments wX wS wR
        (fun i σ ↦ (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * wJ i σ) _ _ (fun _ _ _ ↦ le_rfl)
        (prefixR pol A p v) initR_posSemidef).trans
        (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hS zero_le)
          (mul_le_mul_of_nonneg_left hR zero_le))
          ((le_of_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wJ
            (prefixR pol A p v) initR)).trans (mul_le_mul_of_nonneg_left hJ zero_le)))
    exact hle.trans ((totalWeight_le_lin (runtimeR m0R) .instruments _ wM wO wX _ _
      (fun _ _ _ ↦ le_rfl) (prefixR pol A p v) initR_posSemidef).trans (add_le_add le_rfl hX))
  · rcases i with ((sp | c) | c) | T
    · show cSq (6 * q + clsCap) progCap sp σ ≤ ENNReal.ofReal (3 * C) * 0 + 3 * 0 +
          (ENNReal.ofReal (kapS (6 * q + clsCap) progCap) *
            (((1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
            ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * 0 +
              (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * 0)
      simp only [Nat.cast_one, one_mul, mul_zero, zero_add, add_zero]
      rw [← ENNReal.ofReal_mul (kapS_nonneg _ _)]
      cases sp with
      | h => exact zero_le
      | k => exact le_rfl
      | k' => exact le_rfl
    · show trialChgR Prod.snd trialUpd (evData p v) c σ + cRq (6 * q + clsCap) progCap c σ ≤
        ENNReal.ofReal (3 * C) * cwRecW Prod.snd trialUpd c σ +
          3 * offHeadW trialUpd (evData p v) c σ +
          (ENNReal.ofReal (kapS (6 * q + clsCap) progCap) *
            (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
            ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * ENNReal.ofReal σ.trace.re +
              (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * 0)
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
      exact readChargeR_le Prod.snd trialUpd (EncReadOk trialUpd) (evData p v) m0R c hσ hI
    · show progJump (encPot Prod.snd (evData p v)) c σ ≤ ENNReal.ofReal (3 * C) * 0 + 3 * 0 +
        (ENNReal.ofReal (kapS (6 * q + clsCap) progCap) *
          (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * 0 +
            (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * kJumpW (evData p v) c σ)
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
      exact progJump_le_port Prod.snd (EncReadOk trialUpd) (evData p v) m0R c hσ hI
    · exact zero_le

/-- **The refined Enc term, linear in the flip-value recorded mass** (`encRPre_le_cntEP`,
`cntEP_le`): at data with `PermGood π 18`, for `q ≤ 2^64`, with the prefix's calls inside a
hardwired table,
`encRPre ≤ E₀ q + β q (cwRecPre + recBadPre) + γ q (kfPre + recJPre) + δ offHeadPre`. -/
theorem encRPre_le_lin (hq : q ≤ 2 ^ 64) (pol : DigestPolicy) (p : Pub)
    (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) {Wt : Hw X Z}
    (hW : StaysInR pol A p v Wt) :
    encRPre pol A p v ≤ encE0 q + encBeta q * (cwRecPre pol A p v + recBadPre pol A p v) +
      encGamma q * (kfPre pol A p v + recJPre pol A p v) + encDelta * offHeadPre pol A p v := by
  have h1 := encRPre_le_cntEP hperm hsign pol p v
  have h3 : cntEP pol A p v ≤ 2 ^ 15 * ((6 * q + progCap : ℕ) : ℝ≥0∞) + 2 ^ 15 *
      (ENNReal.ofReal (3 * ((nW progCap + (6 * q + clsCap) : ℕ) : ℝ)) *
          (cwRecPre pol A p v + recBadPre pol A p v) +
        3 * offHeadPre pol A p v +
        (ENNReal.ofReal (kapS (6 * q + clsCap) progCap) * ((6 * q : ℕ) : ℝ≥0∞) +
          ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * (clsCap : ℝ≥0∞) +
          (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * (kfPre pol A p v + recJPre pol A p v))) :=
    (cntEP_le hperm hsign hq pol p v hπ hW).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left le_self_add zero_le) le_rfl) le_rfl) zero_le))
  refine h1.trans ((add_le_add (add_le_add (mul_le_mul_of_nonneg_left h3 zero_le) le_rfl)
    le_rfl).trans_eq ?_)
  unfold encE0 encBeta encGamma encDelta
  ring

end prefixRef

/-! ## The refined modes of the counter trials

leanXMSS's refined trial modes `HMode` (the block `x`, the `k` outcome `a`, the `k'` outcome `c`)
on leanSPHINCS's template: a counter trial of key `K` on the value `m` reads `k` at its block
`encBlk pub K m n`, then `k'`, then `h` with the trial's update. -/

section hmodes

variable (pub : Pub)

/-- **The reads a refined mode allows on runtime 1's ports**: a free read is a `k`-read; after the
`k`-read at `x` with outcome `a` the `k'`-read at `π (x, a)`; then the `h`-read at `π (x, a) + c`
of a counter trial's block, updating the memory by `cwUpd K x (π (x, a)).1`. -/
def HRd1 : HMode → HwRead X Z Selections → Prop
  | .free, .readK _ _ => True
  | .afK x a, .readK' y _ => y = (pub.perm (x, a)).1
  | .afK' x a c, .readH z u => z = (pub.perm (x, a)).2 + c ∧
      ∃ (K : Key) (m : Digest) (n : EncodingCounter), x = encBlk pub K m n ∧
        u = cwUpd K x (pub.perm (x, a)).1
  | _, _ => False

/-- **The reads a refined mode allows on the labelled memory**, as `HRd1` with the trial update
`trialUpd`. -/
def HRd : HMode → HwRead X Z (Mem HPos) → Prop
  | .free, .readK _ _ => True
  | .afK x a, .readK' y _ => y = (pub.perm (x, a)).1
  | .afK' x a c, .readH z u => z = (pub.perm (x, a)).2 + c ∧
      ∃ (K : Key) (m : Digest) (n : EncodingCounter), x = encBlk pub K m n ∧
        u = trialUpd ⟨K, x, (pub.perm (x, a)).1⟩
  | _, _ => False

/-- The calls the refined modes allow, on runtime 1's ports. -/
def okRS : HMode → (hwReadSpec X Z Selections).Port → Prop
  | μ, .inl _ => μ = .free
  | μ, .inr c => HRd1 pub μ c

/-- The calls the refined modes allow, on the template's ports. -/
def okTS : HMode → (SSpec Selections).Port → Prop
  | μ, .inl (.inl (.inr c)) => HRd pub μ c.1
  | μ, _ => μ = .free

/-- The calls the refined modes allow, on runtime 2's ports with record ports. -/
def okZS : HMode → (recHwSpec X Z HPos Selections).Port → Prop
  | μ, .inl (.inl (.inr c)) => HRd pub μ c
  | μ, _ => μ = .free

/-- The refined mode after a call of the template. -/
def nxTS : HMode → (i : (SSpec Selections).Port) → (SSpec Selections).Result i → HMode
  | μ, .inl (.inl (.inr c)), r => rdNxH μ c.1 r
  | _, _, _ => .free

/-- The refined mode after a call of runtime 2 with record ports. -/
def nxZS : HMode → (i : (recHwSpec X Z HPos Selections).Port) →
    (recHwSpec X Z HPos Selections).Result i → HMode
  | μ, .inl (.inl (.inr c)), r => rdNxH μ c r
  | _, _, _ => .free

theorem hModedR_readCall {μ : HMode} {c : HwRead X Z Selections} (h : HRd1 pub μ c) (B : QReg) :
    ModedE (L := LocalSig.instruments) (okRS pub) nxRH (fun p ↦ rdNxH μ c p.2.2) μ
      (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

/-- A stateful program of runtime 1 moded from every state. -/
def SModS {B : QReg} {σ α : Type} (μ : HMode) (fin : α → HMode)
    (x : StateT σ (QComp (hwReadSpec X Z Selections) B B) α) : Prop :=
  ∀ s, ModedE (L := LocalSig.instruments) (okRS pub) nxRH (fun p ↦ fin p.2.2.1) μ (x.run s)

section smod

variable {B : QReg} {σ α β : Type}

theorem sModS_bind {x : StateT σ (QComp (hwReadSpec X Z Selections) B B) α}
    {k : α → StateT σ (QComp (hwReadSpec X Z Selections) B B) β} {μ : HMode} {f : α → HMode}
    {g : β → HMode} (hx : SModS pub μ f x) (hk : ∀ a, SModS pub (f a) g (k a)) :
    SModS pub μ g (x >>= k) := by
  intro s
  rw [StateT.run_bind]
  exact modedE₂_bind (fin := fun q : α × σ ↦ f q.1) (fin' := fun q : β × σ ↦ g q.1) _ _ (hx s)
    fun p ↦ hk p.1 p.2

theorem sModS_pure (a : α) (f : α → HMode) :
    SModS pub (f a) f (pure a : StateT σ (QComp (hwReadSpec X Z Selections) B B) α) := by
  intro s
  rw [StateT.run_pure]
  rfl

theorem sModS_map {x : StateT σ (QComp (hwReadSpec X Z Selections) B B) α} (g : α → β)
    {μ : HMode} {f : β → HMode} (hx : SModS pub μ (fun a ↦ f (g a)) x) :
    SModS pub μ f (g <$> x) := by
  intro s
  rw [StateT.run_map]
  exact modedEH_map (f := fun q : β × σ ↦ f q.1) (fun p : α × σ ↦ (g p.1, p.2)) (hx s)

theorem sModS_rdK (x : X) :
    SModS pub .free (fun a ↦ .afK x a) (rdK (M := Selections) B x) :=
  fun s ↦ modedE₂_bind (fin := fun r : Option Z × Selections ↦ HMode.afK x (r.1.getD 0))
    (fin' := fun q : Z × List (SpongeRead X Z) ↦ HMode.afK x q.1) (readCall (.readK x keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k x (r.1.getD 0)]))
    (hModedR_readCall pub (μ := .free) (c := .readK x keepMem) trivial B) fun _ ↦ rfl

theorem sModS_rdK' {x : X} {a : Z} {y : X} (hy : y = (pub.perm (x, a)).1) :
    SModS pub (.afK x a) (fun c ↦ .afK' x a c) (rdK' (M := Selections) B y) :=
  fun s ↦ modedE₂_bind (fin := fun r : Option Z × Selections ↦ HMode.afK' x a (r.1.getD 0))
    (fin' := fun q : Z × List (SpongeRead X Z) ↦ HMode.afK' x a q.1)
    (readCall (.readK' y keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k' y (r.1.getD 0)]))
    (hModedR_readCall pub (μ := .afK x a) (c := .readK' y keepMem) hy B) fun _ ↦ rfl

theorem sModS_rdHU {x : X} {a c : Z} {z : Z} (hz : z = (pub.perm (x, a)).2 + c) {K : Key}
    {m : Digest} {n : EncodingCounter} (hx : x = encBlk pub K m n)
    {u : Selections → Option X → Selections} (hu : u = cwUpd K x (pub.perm (x, a)).1) :
    SModS pub (.afK' x a c) (fun _ ↦ .free) (rdHU Selections B z u) :=
  fun s ↦ modedE₂_bind (fin := fun _ : Option X × Selections ↦ HMode.free)
    (fin' := fun _ : X × List (SpongeRead X Z) ↦ HMode.free) (readCall (.readH z u) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.h z (r.1.getD 0)]))
    (hModedR_readCall pub (μ := .afK' x a c) (c := .readH z u)
      ⟨hz, K, m, n, hx, hu⟩ B) fun _ ↦ rfl

/-- **A trial's round of reads**, from the zero state, at a trial block of key `K`. -/
theorem sModS_rdRoundU (K : Key) (m : Digest) (n : EncodingCounter) :
    SModS pub .free (fun _ ↦ .free)
      (rdRoundU Selections (cwUpd K) pub.perm B (0, 0) (encBlk pub K m n)) := by
  unfold rdRoundU
  refine sModS_bind pub (sModS_rdK pub ((0 : X × Z).1 + encBlk pub K m n)) fun a ↦ ?_
  refine sModS_bind pub (sModS_rdK' (a := a) pub (by simp only [Prod.fst_zero, zero_add]))
    fun c ↦ ?_
  refine sModS_bind pub (sModS_rdHU pub (a := a) (c := c)
    (by simp only [Prod.fst_zero, zero_add]) (K := K) (m := m) (n := n)
    (by simp only [Prod.fst_zero, zero_add]) (by simp only [Prod.fst_zero, zero_add]))
    fun w ↦ ?_
  exact sModS_pure pub (f := fun _ ↦ HMode.free) _

/-- **A counter trial's hash** of key `K` on the value `m`. -/
theorem hModedR_hashTrial (K : Key) (m : Digest) (cnt : ℕ) :
    ModedE (L := LocalSig.instruments) (okRS pub) nxRH (fun _ ↦ .free) .free
      (hashTrial Selections (cwUpd K) pub.perm B (trialInput pub K m cnt)) := by
  have hb : blocks (trialInput pub K m cnt) =
      [encBlk pub K m (BitVec.ofNat counterBits cnt)] :=
    blocks_encIn pub K m _
  have hfold : SModS pub (B := B) .free (fun _ ↦ .free)
      ((blocks (trialInput pub K m cnt)).foldlM (rdRoundU Selections (cwUpd K) pub.perm B)
        (0, 0)) := by
    rw [hb]
    exact sModS_bind pub (sModS_rdRoundU pub K m _)
      fun s' ↦ sModS_pure pub (f := fun _ ↦ HMode.free) s'
  exact modedEH_map (f := fun _ ↦ HMode.free) Prod.fst
    (sModS_map pub (f := fun _ ↦ HMode.free) (out256 : X → HashOutput)
      (sModS_map pub (f := fun _ ↦ HMode.free) (fun s : X × Z ↦ s.1) hfold) [])

/-- **The counter search** of key `K` on the value `m` is moded. -/
theorem hModedR_grindK (K : Key) (m : Digest) :
    ∀ n cnt, ModedE (L := LocalSig.instruments) (okRS pub) nxRH (fun _ ↦ .free) .free
      (grindK Selections cwUpd pub B K m n cnt)
  | 0, _ => rfl
  | n + 1, cnt => by
    rw [grindK]
    refine modedE₂_bind (fin := fun _ ↦ HMode.free) (fin' := fun _ ↦ HMode.free) _ _
      (hModedR_hashTrial pub K m cnt) fun out ↦ ?_
    split
    · rfl
    · exact hModedR_grindK K m n (cnt + 1)

end smod

theorem hRd_liftRead {μ : HMode} {c : HwRead X Z Selections} (h : HRd1 pub μ c) :
    HRd pub μ (liftRead (S := HPos) c) := by
  rcases μ with _ | ⟨x, a⟩ | ⟨x, a, c'⟩ <;> rcases c with ⟨z', u⟩ | ⟨x', u⟩ | ⟨y, u⟩
  all_goals try exact h
  obtain ⟨hz, K, m, n, hx, hu⟩ := h
  subst hu
  exact ⟨hz, K, m, n, hx, rfl⟩

/-- **Lifting runtime 1's refined moded programs to templates.** -/
theorem hModed_readLift {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → HMode}
    (y : QuantumComp LocalSig.instruments (hwReadSpec X Z Selections) Ω A) {μ : HMode}
    (hy : ModedE (okRS pub) nxRH fin μ y) :
    ModedE (okTS pub) nxTS fin μ (readLift goodAll y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedE _ _ _ μ (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hRd_liftRead pub hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with _ | ⟨x', a⟩ | ⟨x', a, c'⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

/-- A sponge program of runtime 1 is moded, free throughout. -/
theorem hModedR_liftOrdinary {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (spongeSpec X Z) Ω A) :
    ModedE (okRS pub) nxRH (fun _ ↦ .free) .free
      (y.liftOrdinary (t := hwReadCmdSpec X Z Selections)) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => rfl
  | liftBind _ c next ih =>
    show ModedE _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _⟩
    · exact ⟨rfl, fun b ↦ ih _⟩

/-- **Realizing keeps the refined modes.** -/
theorem hModed_realizeT (v : (s : HPos) → XD s) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → HMode} (y : QuantumComp L (SSpec Selections) Ω A)
    {μ : HMode} (hy : ModedE (okTS pub) nxTS fin μ y) :
    ModedE (okZS pub) nxZS fin μ (realizeT v y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedE _ _ _ μ (IFreeM.mapLens (tmplLens v) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · cases p <;> exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩

section trialPrefix

/-- A template moded from the free refined mode back to it. -/
abbrev HFree {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (SSpec Selections) Ω A) : Prop :=
  ModedE (okTS pub) nxTS (fun _ ↦ .free) .free y

theorem hFree_bind {A B B' : QReg} {α β : Type} (x : QComp (SSpec Selections) A B α)
    (g : α → QComp (SSpec Selections) B B' β) (hx : HFree pub x) (hg : ∀ a, HFree pub (g a)) :
    HFree pub (x.bind g) :=
  modedE₂_bind (fin := fun _ ↦ HMode.free) (fin' := fun _ ↦ HMode.free) x g hx hg

theorem hFree_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    HFree pub (QComp.act (spec := SSpec Selections) p) :=
  ⟨trivial, fun _ ↦ rfl⟩

theorem hFree_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × Selections) → QComp (SSpec Selections) B B' α)
    (hk : ∀ r, HFree pub (k r)) : HFree pub (revealThen goodAll T k) :=
  ⟨rfl, fun b ↦ hFree_bind pub _ _ (hFree_act pub _) fun _ ↦ hk b.down⟩

theorem hFree_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec Selections) B B' α) (hk : HFree pub k) : HFree pub (progThen p hp k) :=
  ⟨rfl, fun _ ↦ hFree_bind pub _ _ (hFree_act pub _) fun _ ↦ hk⟩

theorem hFree_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    HFree pub (progPorts Selections B ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact hFree_progThen pub p trivial _ ih

theorem hFree_progSlots (B : QReg) (ss : List Slot) :
    HFree pub (progSlots Selections pub B ss) := by
  induction ss with
  | nil => rfl
  | cons s ss ih => exact hFree_bind pub _ _ (hFree_progPorts pub B _) fun _ ↦ ih

theorem hFree_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    HFree pub (forsOpenT Selections pub B idx lv) := by
  unfold forsOpenT
  exact hFree_revealThen pub _ _ fun _ ↦ hFree_bind pub _ _ (hFree_progSlots pub B _) fun _ ↦ rfl

/-- **A layer signature**: its counter search is moded. -/
theorem hFree_signLayerT (B : QReg) (K : Key) :
    HFree pub (signLayerT Selections cwUpd pub B K) := by
  unfold signLayerT
  refine hFree_revealThen pub _ _ fun r₀ ↦ hFree_bind pub _ _
    (hModed_readLift pub _ (hModedR_grindK pub K _ _ _)) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · rfl
  · exact hFree_revealThen pub _ _ fun r ↦ hFree_bind pub _ _ (hFree_progSlots pub B _)
      fun _ ↦ rfl

/-- **A signature** is moded, for every digest policy. -/
theorem hFree_signT (pol : DigestPolicy) (B : QReg) (msg : Message) :
    HFree pub (signT Selections cwUpd pol pub B msg) := by
  unfold signT
  refine hFree_revealThen pub _ _ fun _ ↦ hFree_revealThen pub _ _ fun _ ↦ ?_
  refine hFree_bind pub _ _ (hFree_progPorts pub B _) fun _ ↦ ?_
  refine hFree_bind pub _ _ (hFree_forsOpenT pub B _ _) fun _ ↦ ?_
  refine hFree_bind pub _ _ (hFree_signLayerT pub B _) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · rfl
  · refine hFree_bind pub _ _ (hFree_signLayerT pub B _) fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · rfl
    · refine hFree_bind pub _ _ (hFree_signLayerT pub B _) fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> rfl

/-- **The challenger** is moded, for every digest policy. -/
theorem hFree_challengeT (pol : DigestPolicy) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    ModedE (okTS pub) nxTS (fun _ ↦ .free) .free (challengeT Selections cwUpd pol pub A cmd) := by
  rcases cmd with o | ⟨q | msg, E, ℓ⟩
  · exact hModed_readLift pub _ (hModedR_liftOrdinary pub _)
  · exact hModed_readLift pub _ (hModedR_liftOrdinary pub _)
  · exact modedE_bind _ _ (hFree_bind pub _ _ (hFree_act pub _)
      fun _ ↦ hFree_signT pub pol _ msg) fun _ _ ↦ rfl

/-- Substituting refined moded trees that start and end free. -/
theorem hModed_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (SSpec Selections)))
    (hσ : ∀ A c, ModedE (okTS pub) nxTS (fun _ ↦ .free) .free (σ A c))
    {Ω : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ModedE (okTS pub) nxTS (fun _ ↦ .free) .free (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact modedE_bind _ _ (hσ s c) fun u ans ↦ (modedEH_cast ans.2 _ _).mpr (ih ans.1)

/-- **The challenge prefix is moded by the refined trial modes**, for every digest policy. -/
theorem hFree_prefixT (pol : DigestPolicy) (A : SAdversary) :
    HFree pub (prefixT Selections cwUpd pol pub A) := by
  unfold prefixT challengedT
  exact hFree_revealThen pub _ _ fun _ ↦ hFree_bind pub _ _
    (hModed_substitute pub _ (hFree_challengeT pub pol) _) fun _ ↦ rfl

end trialPrefix

end hmodes

/-! ## The off-head mass of the trial reads -/

section offHead

set_option exponentiation.threshold 1024 in
/-- **A trial's update determines its rate's digest** (beside its key and block, KeyMsg's
`trialUpd_inj`): a codeword value of the read cell records the digest. -/
theorem trialUpd_trunc {t t' : TrialPt} (h : trialUpd t' = trialUpd t) :
    trunc128 t'.xi = trunc128 t.xi := by
  have hc : 0 < cwCount := Nat.pos_of_ne_zero fun h0 ↦ by
    have := rhoCw_pos
    simp [rhoCw, h0] at this
  obtain ⟨w, hw⟩ := exists_of_card_filter_eq_mul (card_codeword_trunc128 t.xi) hc
    (Nat.two_pow_pos _)
  set m₀ : Mem HPos := (∅, fun _ ↦ none) with hm₀
  have h1 : (trialUpd t' m₀ (some w)).2 t.K = (trialUpd t m₀ (some w)).2 t.K :=
    congrArg (fun m' : Mem HPos ↦ m'.2 t.K) (congrFun (congrFun h m₀) (some w))
  have hR : (trialUpd t m₀ (some w)).2 t.K = some (t.x, trunc128 (t.xi + w)) := by
    rw [show trialUpd t m₀ (some w) = (m₀.1, cwUpd t.K t.x t.xi m₀.2 (some w)) from rfl,
      snd_pair, cwUpd_some_of_none t.K t.x t.xi (show m₀.2 t.K = none from rfl), cwSel,
      ite_eq_left hw, Selections.select_self]
  have hL : (trialUpd t' m₀ (some w)).2 t.K = cwSel m₀.2 t'.K t'.x t'.xi w t.K := by
    rw [show trialUpd t' m₀ (some w) = (m₀.1, cwUpd t'.K t'.x t'.xi m₀.2 (some w)) from rfl,
      snd_pair, cwUpd_some_of_none t'.K t'.x t'.xi (show m₀.2 t'.K = none from rfl)]
  rw [hR, hL] at h1
  rcases cwSel_eq m₀.2 t'.K t'.x t'.xi w with he | he
  · rw [he] at h1
    exact absurd h1 (by simp [hm₀])
  · rw [he] at h1
    by_cases hK : t.K = t'.K
    · rw [hK, Selections.select_self] at h1
      have h2 := trunc128_add_congr (Prod.mk.inj (Option.some.inj h1)).2 (-w)
      rwa [add_neg_cancel_right, add_neg_cancel_right] at h2
    · rw [Selections.select_of_ne _ _ _ hK] at h1
      exact absurd h1 (by simp [hm₀])

/-- The potentials of the refined trial modes: after the `k`-read, the union misses its outcome;
after the `k'`-read, it misses the `k` or the `k'` outcome. -/
noncomputable def hpot (π : Equiv.Perm (X × Z)) :
    HMode → Unit → Matrix (HwReg X Z (Mem HPos)) (HwReg X Z (Mem HPos)) ℂ
  | .free, _ => 0
  | .afK x a, _ => setProj {s | KMiss x a s}
  | .afK' x a c, _ => setProj {s | KMiss x a s ∨ K'Miss (π (x, a)).1 c s}

/-- **The leak charge of a read port**: after a `k` or `k'` read, the weight of the states whose
union misses the read's outcome (`0` at the `h` reads). -/
noncomputable def leakW : (c : HwRead X Z (Mem HPos)) →
    Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ → ℝ≥0∞
  | .readK x u, σ => ENNReal.ofReal (∑ r : Option Z × Mem HPos,
      dW (fun q ↦ if KMiss x (r.1.getD 0) q.2 then (1 : ℝ) else 0)
        (MatrixMap.conj (hwReadKraus (.readK x u) r) σ))
  | .readK' y u, σ => ENNReal.ofReal (∑ r : Option Z × Mem HPos,
      dW (fun q ↦ if K'Miss y (r.1.getD 0) q.2 then (1 : ℝ) else 0)
        (MatrixMap.conj (hwReadKraus (.readK' y u) r) σ))
  | .readH _ _, _ => 0

theorem sum_potential_hpot_free (π : Equiv.Perm (X × Z)) {A : Type} [Fintype A] [DecidableEq A]
    (σ : Matrix (A × HwReg X Z (Mem HPos)) (A × HwReg X Z (Mem HPos)) ℂ) :
    ∑ j, potential (hpot π .free j) σ = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ potential_zero σ

/-- A diagonal mass as a weighted diagonal. -/
theorem diagMass_eq_dW (S : Set (HwReg X Z (Mem HPos))) [DecidablePred (· ∈ S)]
    {τ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hτ : τ.PosSemidef) :
    diagMass {q : Unit × HwReg X Z (Mem HPos) | q.2 ∈ S} τ =
      ENNReal.ofReal (dW (fun q ↦ if q.2 ∈ S then (1 : ℝ) else 0) τ) := by
  have hre : ∀ q, 0 ≤ (τ q q).re := fun q ↦ (Complex.nonneg_iff.1 hτ.diag_nonneg).1
  unfold diagMass dW
  rw [ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hre q)]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases h : q.2 ∈ S
  · rw [Set.indicator_of_mem (show q ∈ {q : Unit × HwReg X Z (Mem HPos) | q.2 ∈ S} from h),
      ite_eq_left h, one_mul]
  · rw [Set.indicator_of_notMem (show q ∉ {q : Unit × HwReg X Z (Mem HPos) | q.2 ∈ S} from h),
      ite_eq_right h, zero_mul, ENNReal.ofReal_zero]

theorem offHeadW_not_trial (d : EvData) {c : HwRead X Z (Mem HPos)}
    (hc : ∀ z u, c ≠ .readH z u)
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) :
    offHeadW trialUpd d c σ = 0 := by
  unfold offHeadW
  exact ite_eq_right fun ⟨_, h⟩ ↦ hc _ _ h

variable (p : Pub) (v : (s : HPos) → XD s)

/-- **A trial `h` read in the refined mode `afK' x a c` is off its head only where the union
misses the `k` or the `k'` outcome.** -/
theorem offHeadW_le_miss {x : X} {a c z : Z} {u : Mem HPos → Option X → Mem HPos}
    (hz : z = (p.perm (x, a)).2 + c) {K : Key} {m : Digest} {n : EncodingCounter}
    (hx : x = encBlk p K m n) (hu : u = trialUpd ⟨K, x, (p.perm (x, a)).1⟩)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    offHeadW trialUpd (evData p v) (.readH z u) σ ≤
      diagMass {q : Unit × HwReg X Z (Mem HPos) | q.2 ∈
        {s | KMiss x a s ∨ K'Miss (p.perm (x, a)).1 c s}} σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set xi := (p.perm (x, a)).1
  have htr : IsTrial trialUpd (.readH z u : HwRead X Z (Mem HPos)) :=
    ⟨(z, ⟨K, x, xi⟩), by rw [hu]⟩
  have hc := eq_readH_trialOf trialUpd htr
  obtain ⟨hz', hu'⟩ := HwRead.readH.inj hc
  have hinj : trialUpd (trialOf trialUpd (.readH z u : HwRead X Z (Mem HPos))).2 =
      trialUpd ⟨K, x, xi⟩ := by rw [← hu', hu]
  obtain ⟨hK, hxe⟩ := trialUpd_inj hinj
  have hxi := trialUpd_trunc hinj
  have hs : EncAt (evData p v) K [x] := by
    rw [hx]
    exact slotOf_encBlk p v K m n
  rw [diagMass_eq_dW _ hσ]
  unfold offHeadW
  rw [ite_eq_left htr]
  refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ ?_)
  refine mul_le_mul_of_nonneg_right ?_ (hre q)
  dsimp only
  by_cases hm : q.2 ∈ {s : HwReg X Z (Mem HPos) | KMiss x a s ∨ K'Miss xi c s}
  · rw [ite_eq_left hm]
    split_ifs <;> norm_num
  · rw [ite_eq_right hm]
    have hka : (union q.2.2.1 q.2.1).k x = some a := not_not.1 fun h ↦ hm (.inl h)
    have hkc : (union q.2.2.1 q.2.1).k' xi = some c := not_not.1 fun h ↦ hm (.inr h)
    have hslot : EncAt (evData p v) (trialOf trialUpd (.readH z u : HwRead X Z (Mem HPos))).2.K
        [(trialOf trialUpd (.readH z u : HwRead X Z (Mem HPos))).2.x] := by
      rw [hK, hxe]
      exact hs
    refine (ite_eq_left (Or.inr ⟨hslot, xi, hxi.symm, ?_⟩)).le
    rw [hxe, ← hz']
    exact ⟨[], 0, x, a, (p.perm (x, a)).2, c, rfl, IsTail.nil, hka, by rw [zero_add]; rfl, hkc,
      hz⟩

/-- **The step condition of the refined trial modes at a read port.** -/
theorem offHead_step_read (μ : HMode) (c : HwRead X Z (Mem HPos))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hok : HRd p μ c) :
    offHeadW trialUpd (evData p v) c σ + ∑' r, ∑ j, potential (hpot p.perm (rdNxH μ c r) j)
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      ∑ j, potential (hpot p.perm μ j) σ + leakW c σ := by
  have hpos : ∀ r, (MatrixMap.conj (hwReadKraus c r) σ).PosSemidef :=
    fun r ↦ posSemidef_conj _ hσ
  rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with _ | ⟨x₀, a⟩ | ⟨x₀, a, c₀⟩
  all_goals try exact False.elim hok
  · -- the `h`-read of a trial
    obtain ⟨hz, K, m, n, hx, hu⟩ := hok
    have h0 : ∀ r, ∑ j, potential (hpot p.perm (rdNxH (HMode.afK' x₀ a c₀)
        (.readH z u : HwRead X Z (Mem HPos)) r) j)
          (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) = 0 :=
      fun r ↦ sum_potential_hpot_free p.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero, Fintype.sum_unique]
    show offHeadW trialUpd (evData p v) (.readH z u) σ ≤ potential (setProj {s | KMiss x₀ a s ∨
      K'Miss (p.perm (x₀, a)).1 c₀ s}) σ + 0
    rw [add_zero, potential_setProj _ hσ]
    exact offHeadW_le_miss p v hz hx hu hσ
  · -- the `k`-read of a trial
    have hL : ∀ r : Option Z × Mem HPos, ∑ j, potential (hpot p.perm (rdNxH HMode.free
        (.readK x u : HwRead X Z (Mem HPos)) r) j)
          (MatrixMap.conj (hwReadKraus (.readK x u) r) σ) =
        ENNReal.ofReal (dW (fun q ↦ if KMiss x (r.1.getD 0) q.2 then (1 : ℝ) else 0)
          (MatrixMap.conj (hwReadKraus (.readK x u) r) σ)) := fun r ↦ by
      rw [Fintype.sum_unique]
      exact (potential_setProj _ (hpos r)).trans (diagMass_eq_dW _ (hpos r))
    rw [offHeadW_not_trial (evData p v) (fun _ _ h ↦ by cases h), zero_add, tsum_fintype,
      Finset.sum_congr rfl fun r _ ↦ hL r, sum_potential_hpot_free, zero_add]
    show _ ≤ ENNReal.ofReal _
    rw [ENNReal.ofReal_sum_of_nonneg fun r _ ↦ dW_nonneg (fun q ↦ by split_ifs <;> norm_num)
      (hpos r)]
  · -- the `k'`-read of a trial
    obtain rfl := hok
    have hnn : ∀ (f : Unit × HwReg X Z (Mem HPos) → ℝ), (∀ q, 0 ≤ f q) →
        ∀ r : Option Z × Mem HPos,
          0 ≤ dW f (MatrixMap.conj (hwReadKraus (.readK' (p.perm (x₀, a)).1 u) r) σ) :=
      fun f hf r ↦ dW_nonneg hf (hpos r)
    have hi : ∀ q : Unit × HwReg X Z (Mem HPos), (0 : ℝ) ≤ if KMiss x₀ a q.2 then 1 else 0 :=
      fun q ↦ by split_ifs <;> norm_num
    have hi' : ∀ (r : Option Z × Mem HPos) (q : Unit × HwReg X Z (Mem HPos)),
        (0 : ℝ) ≤ if K'Miss (p.perm (x₀, a)).1 (r.1.getD 0) q.2 then 1 else 0 := fun r q ↦ by
      split_ifs <;> norm_num
    have hL : ∀ r : Option Z × Mem HPos, ∑ j, potential (hpot p.perm (rdNxH (HMode.afK x₀ a)
        (.readK' (p.perm (x₀, a)).1 u : HwRead X Z (Mem HPos)) r) j)
          (MatrixMap.conj (hwReadKraus (.readK' (p.perm (x₀, a)).1 u) r) σ) =
        ENNReal.ofReal (dW (fun q ↦ if q.2 ∈ {s | KMiss x₀ a s ∨
          K'Miss (p.perm (x₀, a)).1 (r.1.getD 0) s} then (1 : ℝ) else 0)
          (MatrixMap.conj (hwReadKraus (.readK' (p.perm (x₀, a)).1 u) r) σ)) := fun r ↦ by
      rw [Fintype.sum_unique]
      exact (potential_setProj _ (hpos r)).trans (diagMass_eq_dW _ (hpos r))
    have hR : ∑ j, potential (hpot p.perm (HMode.afK x₀ a) j) σ =
        ENNReal.ofReal (dW (fun q ↦ if KMiss x₀ a q.2 then (1 : ℝ) else 0) σ) := by
      rw [Fintype.sum_unique]
      exact (potential_setProj _ hσ).trans (diagMass_eq_dW _ hσ)
    rw [offHeadW_not_trial (evData p v) (fun _ _ h ↦ by cases h), zero_add, tsum_fintype,
      Finset.sum_congr rfl fun r _ ↦ hL r, hR,
      ← readK'_keep_kMiss (p.perm (x₀, a)).1 u x₀ a σ]
    show _ ≤ _ + ENNReal.ofReal _
    rw [← ENNReal.ofReal_add (Finset.sum_nonneg fun r _ ↦ hnn _ hi r)
        (Finset.sum_nonneg fun r _ ↦ hnn _ (hi' r) r), ← Finset.sum_add_distrib,
      ENNReal.ofReal_sum_of_nonneg fun r _ ↦ add_nonneg (hnn _ hi r) (hnn _ (hi' r) r)]
    refine Finset.sum_le_sum fun r _ ↦ ENNReal.ofReal_le_ofReal ?_
    rw [← dW_add]
    unfold dW
    refine Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right ?_
      ((Complex.nonneg_iff.1 (hpos r).diag_nonneg).1)
    dsimp only
    by_cases h1 : KMiss x₀ a q.2
    · have : q.2 ∈ {s | KMiss x₀ a s ∨ K'Miss (p.perm (x₀, a)).1 (r.1.getD 0) s} := .inl h1
      rw [ite_eq_left this, ite_eq_left h1]
      linarith [hi' r q]
    · by_cases h2 : K'Miss (p.perm (x₀, a)).1 (r.1.getD 0) q.2
      · have : q.2 ∈ {s | KMiss x₀ a s ∨ K'Miss (p.perm (x₀, a)).1 (r.1.getD 0) s} := .inr h2
        rw [ite_eq_left this, ite_eq_right h1, ite_eq_left h2, zero_add]
      · have : q.2 ∉ {s | KMiss x₀ a s ∨ K'Miss (p.perm (x₀, a)).1 (r.1.getD 0) s} :=
          fun h ↦ h.elim h1 h2
        rw [ite_eq_right this, ite_eq_right h1, ite_eq_right h2, add_zero]

/-- **The step condition of the refined trial modes**: the off-head mass of every allowed call
plus the potentials after it is at most the potentials before plus the leak charge. -/
theorem offHead_step (μ : HMode) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ)
    (hσ : σ.PosSemidef) (hok : okZS p μ i) :
    extWeight (hwCost (offHeadW trialUpd (evData p v)) fun _ _ ↦ 0) i σ +
        ∑' r, ∑ j, potential (hpot p.perm (nxZS μ i r) j) (((runtimeR m0R).step i).branch r σ) ≤
      ∑ j, potential (hpot p.perm μ j) σ + extWeight (hwCost leakW fun _ _ ↦ 0) i σ := by
  rcases i with ((sp | c) | c) | T
  · obtain rfl : μ = .free := hok
    have h0 : ∀ r, ∑ j, potential (hpot p.perm (nxZS HMode.free (.inl (.inl (.inl sp))) r) j)
        (((runtimeR m0R).step (.inl (.inl (.inl sp)))).branch r σ) = 0 :=
      fun r ↦ sum_potential_hpot_free p.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le
  · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    simp only [hb]
    exact offHead_step_read p v μ c hσ hok
  · obtain rfl : μ = .free := hok
    have h0 : ∀ r, ∑ j, potential (hpot p.perm (nxZS HMode.free (.inl (.inr c)) r) j)
        (((runtimeR m0R).step (.inl (.inr c))).branch r σ) = 0 :=
      fun r ↦ sum_potential_hpot_free p.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le
  · obtain rfl : μ = .free := hok
    have h0 : ∀ r, ∑ j, potential (hpot p.perm (nxZS HMode.free (.inr T) r) j)
        (((runtimeR m0R).step (.inr T)).branch r σ) = 0 :=
      fun r ↦ sum_potential_hpot_free p.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le

/-- **The off-head mass moves onto the leaks of the trials' `k`, `k'` reads** (TrialSource's
`totalWeight_le_moded_of_zero` with the refined modes). -/
theorem offHeadPre_le_leak (pol : DigestPolicy) (A : SAdversary) :
    offHeadPre pol A p v ≤ (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost leakW fun _ _ ↦ 0)) (prefixR pol A p v) initR :=
  totalWeight_le_moded_of_zero (runtimeR m0R) .instruments (hpot p.perm) _ _
    (fun μ i σ hσ hok ↦ offHead_step p v μ i σ hσ hok) (prefixR pol A p v) .free (fun _ ↦ rfl)
    (hModed_realizeT p v _ (hFree_prefixT p pol A)) initR_posSemidef

/-- **A hardwired classical move into `BadR` at a trial read is off the trial's head** on states
whose hardwired `h` cells head honest (non-encoding) tails, with at most `progCap` hardwired
cells: outside `BadR` the union is good, so the head-tail of the read cell is unique and cannot be
both the trial's (at an encoding slot) and an honest one. -/
theorem hwMoveW_le_offHeadW (c : HwRead X Z (Mem HPos))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef)
    (hH : ∀ a, σ a a ≠ 0 → HwHeadsHonest (evData p v) a.2 ∧ dbGrade a.2.2.1 ≤ progCap) :
    hwMoveW p v c σ ≤ offHeadW trialUpd (evData p v) c σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  by_cases ht : IsTrial trialUpd c
  · simp only [hwMoveW, offHeadW, ht, ↓reduceIte]
    generalize trialOf trialUpd c = zt
    obtain ⟨z, t⟩ := zt
    refine ENNReal.ofReal_le_ofReal ?_
    unfold hwMoveSum
    refine Finset.sum_le_sum fun a _ ↦ ?_
    by_cases h0 : σ a a = 0
    · rw [h0, Complex.zero_re, mul_zero, mul_zero]
    refine mul_le_mul_of_nonneg_right ?_ (hre a)
    by_cases h1 : a.2.2.1.1 z ≠ none ∧ hCls (BadR p v progCap) (trialUpd t) (a.2.2.1.1 z) a
    · have hnh : ¬ TrialHead (evData p v) z t a.2 := by
        intro hh
        obtain ⟨hhon, hN⟩ := hH a h0
        have hG : Good (evData p v).perm (union a.2.2.1 a.2.1) :=
          good_of_not_mem_bad (D := a.2.1) (W := a.2.2.1) (m := a.2.2.2) h1.2.1 hN
        obtain ⟨hslot, xi, -, hi'⟩ := hh.resolve_left (not_not.2 hG)
        obtain ⟨t', xi', hi, hhs⟩ := hhon z h1.1
        obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hi'
        exact hhs _ hslot
      exact le_of_eq (by rw [ite_eq_left h1, ite_eq_right hnh])
    · rw [ite_eq_right h1]
      split_ifs <;> norm_num
  · simp only [hwMoveW, ht, ↓reduceIte, zero_le]

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The leaks along the prefix**: at most `2/|Z|` per read call (`readK_leak_le`,
`readK'_leak_le` on the prefix's states, which have no decompressed `⊥`). -/
theorem totalWeight_leakW_le (pol : DigestPolicy) :
    (runtimeR m0R).totalWeight .instruments (extWeight (hwCost leakW fun _ _ ↦ 0))
      (prefixR pol A p v) initR ≤ ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞) := by
  obtain ⟨P, hP, hx⟩ := forallQueries_encInv (q := q) hperm hsign pol p v
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (EncInv q) hP
    (w' := fun i σ ↦ ENNReal.ofReal (2 / Fintype.card Z) * extWeight (hwCost
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR pol A p v) initR_posSemidef hx).trans ?_
  · rcases i with ((sp | c) | c) | T
    · exact zero_le
    · show leakW c σ ≤ ENNReal.ofReal (2 / Fintype.card Z) * ENNReal.ofReal σ.trace.re
      have hnb : ReadNoBot c σ := readNoBot_of_noBot c hI.2.2
      have htr : σ.trace.re = ∑ a, (σ a a).re := by rw [Matrix.trace, Complex.re_sum]; rfl
      rw [← ENNReal.ofReal_mul (by positivity), htr]
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
      · exact zero_le
      · exact ENNReal.ofReal_le_ofReal (readK_leak_le x u hσ hnb)
      · exact ENNReal.ofReal_le_ofReal (readK'_leak_le y u hσ hnb)
    · exact zero_le
    · exact zero_le
  · refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments _
      (extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
        fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (prefixR pol A p v) initR)).trans ?_
    exact mul_le_mul_of_nonneg_left (totalWeight_calls_le (prefixR pol A p v)
      (clsCalls_prefixR hperm hsign pol p v)) zero_le

/-- **The off-head mass of the trial reads along the prefix**: at most `2/|Z|` per read call,
`offHeadPre ≤ 2^-511 clsCap`. -/
theorem offHeadPre_le (pol : DigestPolicy) :
    offHeadPre pol A p v ≤ ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞) :=
  (offHeadPre_le_leak p v pol A).trans (totalWeight_leakW_le p v hperm hsign pol)

/-- **The hardwired classical moves along the prefix are off the trials' heads** (HwHeads'
honest-heads invariant `forallQueries_hwHeads_prefixR`): `hwMovePre ≤ offHeadPre`. -/
theorem hwMovePre_le_offHeadPre (pol : DigestPolicy) :
    hwMovePre pol A p v ≤ offHeadPre pol A p v := by
  obtain ⟨P, hP, hx⟩ := forallQueries_encInv (q := q) hperm hsign pol p v
  show (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (hwMoveW p v) fun _ _ ↦ 0))
      (prefixR pol A p v) initR ≤ (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (offHeadW trialUpd (evData p v)) fun _ _ ↦ 0)) (prefixR pol A p v) initR
  refine totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i σ ↦ EncInv q i σ ∧ (ReadPortQ i → DiagOn (HwHeadsHonest (evData p v)) σ))
    (P := fun i E σ ↦ P i E σ ∧
      invSupp (runtimeR m0R) ReadPortQ (HwHeadsHonest (evData p v)) i E σ)
    (fun i E σ h ↦ ⟨hP i E σ h.1, fun hq a ha ↦
      traceRight_diag_eq_zero fun e ↦ h.2 hq (a, e) ha⟩)
    (fun i σ hσ hI ↦ ?_) (prefixR pol A p v) initR_posSemidef
    (Quantum.Xmss.Assembly.forallQueries_and hx (forallQueries_hwHeads_prefixR p v pol A))
  rcases i with ((sp | c) | c) | T
  · exact zero_le
  · refine hwMoveW_le_offHeadW p v c hσ fun a ha ↦ ⟨?_, (hI.1.2.1 a a ha).1.2⟩
    by_contra hn
    exact ha (hI.2 trivial a hn)
  · exact zero_le
  · exact zero_le

/-- **The prefix's linear charge** (CostRefined's `twPR_le` Enc term
`E = 2 encRPre + hwMovePre + kapRR clsCap`): at data with `PermGood π 18`, for `q ≤ 2^64`, with
the prefix's calls inside a hardwired table (RecJ's `StaysInR`), for every digest policy,
`E ≤ encEC q + 2 β q (cwRecPre + recBadPre) + 2 γ q (kfPre + recJPre)` (`β = encBeta`,
`γ = encGamma`; no hardwired-head term: `hwMovePre_le_offHeadPre`). -/
theorem encE_le (hq : q ≤ 2 ^ 64) (pol : DigestPolicy) (hπ : PermGood p.perm 18) {Wt : Hw X Z}
    (hW : StaysInR pol A p v Wt) :
    2 * encRPre pol A p v + hwMovePre pol A p v + ENNReal.ofReal kapRR * (clsCap : ℝ≥0∞) ≤
      encEC q + 2 * encBeta q * (cwRecPre pol A p v + recBadPre pol A p v) +
        2 * encGamma q * (kfPre pol A p v + recJPre pol A p v) := by
  have h1 := encRPre_le_lin hperm hsign hq pol p v hπ hW
  have h2 := offHeadPre_le p v hperm hsign pol
  have h3 : hwMovePre pol A p v ≤ ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞) :=
    (hwMovePre_le_offHeadPre p v hperm hsign pol).trans h2
  have h4 : encRPre pol A p v ≤ encE0 q + encBeta q * (cwRecPre pol A p v + recBadPre pol A p v) +
      encGamma q * (kfPre pol A p v + recJPre pol A p v) +
        encDelta * (ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞)) :=
    h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 zero_le))
  refine (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h4 zero_le) h3) le_rfl).trans_eq ?_
  unfold encEC
  ring

end offHead

end Quantum.Sphincs.Assembly

end
