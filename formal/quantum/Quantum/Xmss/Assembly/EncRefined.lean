module

public import Quantum.Xmss.Assembly.CostRefined
public import Quantum.Xmss.Assembly.TrialSource

@[expose] public section

/-!
# The refined joint count of the selecting reads

CostRefined's `twPR_le` prices the challenge prefix's reads with the refined read cost; its linear
charge is `E = 2 encRPre + hwMovePre + kapRR clsCap` (the empty-cell flips and the hardwired
classical moves of the trial reads). Here `E` is bounded linearly in the flip-value recorded mass
`cwRecPre + recBadPre`, through a joint count whose charges no longer contain the whole recorded
mass `massPre`.

* **The unselected key, count-weighted** (`unselFlip_le`, `unselRead_drop`): ReadCost's
  `re_trace_flipOp_le` on `N σ N` (`N` the square roots of a count off the read cell,
  `cellNoBot_sqrtDiag`) for the event "the trial's key is unselected", with reference weight `q0`
  and flip values `CwFlip`: diagonal cost `-ρ_c` on the empty cells with the key unselected
  (`EmptyUnsel`), at most `0` elsewhere (`fd_unselQ_le`); empty-to-recorded weight `ρ_c`
  (`ew_unselQ_le`); the cross term on the codeword-recorded cells (`CwRecG`, `pd_cwFlip_le`).
  Hence `2^-22 e + post ≤ pre + 3 p`.
* **The read cell** (`TrialHead`, `cellFlip_le`): the flip operator splits along `TrialHead` (a
  property of the `k`, `k'` cells, `trace_flipOp_split`); on the trial head re-compression costs
  `6/|X|` (`goodBlock_le`), off it `3` per unit of mass (`offBlock_le`). The trial head asks the
  rate only up to its digest, since `trialOf` names a trial up to it (`trialUpd_inj`).
* **The refined joint count** (`trialRead_drop_ref`, `trialRead_potential_le_ref`,
  `totalWeight_cntEW_le`, `cntEP_le`): `cntEP ≤ 2^22 (6q + progCap) + 2^22 (3C cwRecPre +
  3 offHeadPre + kapS 6q + kapR6 clsCap + potCap kJumpPre)` with `C = nW + nD q`.
* **The empty-cell flips** (`card_hFlip_div_le`, `encRW_le`, `encRPre_le_cntEP`):
  `encRPre ≤ 2^-128 cntEP + 2^-128 clsCap + offHeadPre`; together (`encRPre_le_lin`):
  `encRPre ≤ encE0 q + encBeta q (cwRecPre + recBadPre) + encGamma q (kfPre + recJPre) +
  encDelta offHeadPre`.
* **The off-head mass** (`HMode`, `tFreeH_prefixT`, `offHead_step`, `readK_leak_le`,
  `readK'_leak_le`, `offHeadPre_le`): TrialSource's trial modes refined to keep the block and the
  `k`, `k'` outcomes; a trial's `h` read is off its head only where the union misses an outcome of
  its own `k`, `k'` reads (`offHeadW_le_miss`), which a read leaves with weight at most `2/|Z|`
  (`re_trace_gramW_le`). Hence `offHeadPre ≤ 2^-511 clsCap`.
* **The hardwired moves** (`hwMoveW_le`, `hwMovePre_le`, `hwHeadPre_eq_zero`):
  `hwMovePre ≤ 2^-511 clsCap + hwHeadPre`, and `hwHeadPre = 0` when the prefix's calls see their
  hardwired `h` cells at the end of honest (non-message) head-tails (`HwHeadsHonest`).
* **The prefix's linear charge** (`encE_le`): `E ≤ encEC q + 2 encBeta q (cwRecPre + recBadPre) +
  2 encGamma q (kfPre + recJPre) + hwHeadPre`.
-/

universe u v w

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## Diagonal weights off the read cell -/

section offCell

variable {M : Type} [Fintype M] [DecidableEq M]

omit [Fintype M] [DecidableEq M] in
/-- A state rebuilt from a rest agrees with the rest off the read cell, whatever the cell. -/
theorem splitH'_symm_off (z : Z) (o o' : Option X) (r : RestH X M z) :
    (∀ b, b ≠ z → ((splitH' z).symm (o, r)).2.1.1 b = ((splitH' z).symm (o', r)).2.1.1 b) ∧
      ((splitH' z).symm (o, r)).2.1.2 = ((splitH' z).symm (o', r)).2.1.2 ∧
      ((splitH' z).symm (o, r)).2.2.1 = ((splitH' z).symm (o', r)).2.2.1 := by
  refine ⟨fun b hb ↦ ?_, rfl, rfl⟩
  simp [splitH', hb]

/-- **No decompressed `⊥` survives a diagonal weight off the read cell**: `N σ N` has no
decompressed `⊥` at the cell if `σ` has none and `N = sqrtDiag n` with `n` off the cell. -/
theorem cellNoBot_sqrtDiag {z : Z} {n : HwReg X Z M → ℝ} (hn : OffCell z n)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    CellNoBot (splitH' z) (actH z) (sqrtDiag n * σ * sqrtDiag n) := by
  intro r hr t
  have hc : ∀ y : X, n ((splitH' z).symm (some y, r)).2 = n ((splitH' z).symm (none, r)).2 :=
    fun y ↦ by
      obtain ⟨h1, h2, h3⟩ := splitH'_symm_off z (some y) none r
      exact hn _ _ h1 h2 h3
  simp only [sqrtDiag, mul_diagonal, diagonal_mul]
  rw [Finset.sum_congr rfl fun y _ ↦ by rw [hc y], ← Finset.sum_mul, ← Finset.mul_sum,
    hnb r hr t, mul_zero, zero_mul]

/-- A diagonal weight off the read cell commutes with the flip operator of a read of the cell. -/
theorem sqrtDiag_mul_flipOp (z : Z) (upd : M → Option X → M) {n : HwReg X Z M → ℝ}
    (hn : OffCell z n) (S : Set (Unit × HwReg X Z M)) [DecidablePred (· ∈ S)] :
    sqrtDiag n * flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r) S =
      flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r) S * sqrtDiag n := by
  have hK := sqrtDiag_mul_readH z upd hn
  have hKh : ∀ r, sqrtDiag n * (hwReadKraus (.readH z upd) r)ᴴ =
      (hwReadKraus (.readH z upd) r)ᴴ * sqrtDiag n := fun r ↦ by
    have := congrArg conjTranspose (hK r)
    simp only [conjTranspose_mul, sqrtDiag_conjTranspose] at this
    exact this.symm
  have hP : sqrtDiag n * indProj S = indProj S * sqrtDiag n := by
    simp only [sqrtDiag, indProj, diagonal_mul_diagonal, mul_comm]
  unfold flipOp
  rw [Matrix.mul_sub, Matrix.sub_mul, Finset.mul_sum, Finset.sum_mul, hP]
  refine congrArg (· - indProj S * sqrtDiag n) (Finset.sum_congr rfl fun r _ ↦ ?_)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hKh, Matrix.mul_assoc _ (sqrtDiag n), hP,
    ← Matrix.mul_assoc, Matrix.mul_assoc _ (sqrtDiag n), hK, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc]

/-- A weight `n` read after `N = sqrtDiag n'` (both off the read cell) and a read: the read of
`N σ N` against `f` is the read of `σ` against `f · n'`. -/
theorem dW_conj_sqrtDiag (z : Z) (upd : M → Option X → M) {n : HwReg X Z M → ℝ}
    (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n) (f : Unit × HwReg X Z M → ℝ) (r : Option X × M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    dW f (MatrixMap.conj (hwReadKraus (.readH z upd) r) (sqrtDiag n * σ * sqrtDiag n)) =
      dW (fun q ↦ f q * n q.2) (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ) := by
  set N := sqrtDiag n
  set K := hwReadKraus (.readH z upd) r
  have hc : N * K = K * N := sqrtDiag_mul_readH z upd hn r
  have hc' : N * Kᴴ = Kᴴ * N := by
    have := congrArg conjTranspose hc
    simp only [conjTranspose_mul, N, sqrtDiag_conjTranspose] at this
    exact this.symm
  have heq : K * (N * σ * N) * Kᴴ = N * (K * σ * Kᴴ) * N := by
    calc K * (N * σ * N) * Kᴴ = (K * N) * σ * (N * Kᴴ) := by simp only [Matrix.mul_assoc]
      _ = (N * K) * σ * (Kᴴ * N) := by rw [hc, hc']
      _ = N * (K * σ * Kᴴ) * N := by simp only [Matrix.mul_assoc]
  rw [MatrixMap.conj_apply, MatrixMap.conj_apply, heq]
  unfold dW
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [re_sqrtDiag_conj_apply hn0]
  exact (mul_assoc _ _ _).symm

theorem posSemidef_sqrtDiag_conj (n : HwReg X Z M → ℝ)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    (sqrtDiag n * σ * sqrtDiag n).PosSemidef := by
  have := hσ.mul_mul_conjTranspose_same (sqrtDiag n)
  rwa [sqrtDiag_conjTranspose] at this

end offCell

/-! ## The unselected-key event at a trial read -/

section unsel

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)
  (updOf : TrialPt → M → Option X → M)

/-- **A selected key stays selected** under every trial read. -/
def TrialKeep : Prop :=
  ∀ t m o, get m t.l t.e ≠ none → get (updOf t m o) t.l t.e ≠ none

/-- The states whose trial key is unselected. -/
def unselQ (t : TrialPt) : Set (Unit × HwReg X Z M) := {q | get q.2.2.2 t.l t.e = none}

/-- `unselQ`, decided. -/
instance unselQDec (t : TrialPt) : DecidablePred (· ∈ unselQ get t) :=
  fun q ↦ inferInstanceAs (Decidable (get q.2.2.2 t.l t.e = none))

/-- **The flip values of the unselected-key event** at a rest: the key unselected and the digest a
codeword. -/
def CwFlip (t : TrialPt) (z : Z) (y : X) (r : RestH X M z) : Prop :=
  get (memH z r) t.l t.e = none ∧ Codeword.Valid (trunc128 (t.xi + y))

/-- `CwFlip`, decided classically. -/
noncomputable instance cwFlipDec (t : TrialPt) (z : Z) (y : X) (r : RestH X M z) :
    Decidable (CwFlip get t z y r) :=
  Classical.propDecidable _

/-- The states a trial read selects from: the cell neither hardwired nor recorded, the trial's
key unselected. -/
def EmptyUnsel (z : Z) (t : TrialPt) (s : HwReg X Z M) : Prop :=
  s.2.1.1 z = none ∧ s.1.1 z = none ∧ get s.2.2 t.l t.e = none

/-- `EmptyUnsel`, decided classically. -/
noncomputable instance emptyUnselDec (z : Z) (t : TrialPt) :
    DecidablePred (EmptyUnsel get (M := M) z t) :=
  Classical.decPred _

/-- The states whose read cell is codeword-recorded for the trial's unselected key (RestMass's
`CwRec` through `get`). -/
def CwRecG (z : Z) (t : TrialPt) (s : HwReg X Z M) : Prop :=
  s.2.1.1 z = none ∧ get s.2.2 t.l t.e = none ∧
    ∃ v, s.1.1 z = some v ∧ Codeword.Valid (trunc128 (t.xi + v))

/-- `CwRecG`, decided classically. -/
noncomputable instance cwRecGDec (z : Z) (t : TrialPt) : DecidablePred (CwRecG get (M := M) z t) :=
  Classical.decPred _

omit [Fintype M] [DecidableEq M] in
theorem ind_unselQ_symm (t : TrialPt) (z : Z) (a : Option X) (r : RestH X M z) :
    ind (unselQ get t) ((splitH' z).symm (a, r)) =
      if get (memH z r) t.l t.e = none then 1 else 0 :=
  rfl

omit [Fintype M] [DecidableEq M] in
theorem ind_unselQ (t : TrialPt) (q : Unit × HwReg X Z M) :
    ind (unselQ get t) q = if get q.2.2.2 t.l t.e = none then 1 else 0 :=
  rfl

omit [Fintype M] [DecidableEq M] in
/-- The weight of a recorded outcome against the unselected-key event: whether the memory update
leaves the key unselected. -/
theorem gw_unselQ [Nonempty X] (t : TrialPt) (z : Z) (upd : M → Option X → M) (y : X)
    (r : RestH X M z) :
    gw (splitH' z) (tauH z upd) (unselQ get t) (some y) r =
      if get (upd (memH z r) (some y)) t.l t.e = none then 1 else 0 := by
  unfold gw
  have h : ∀ a : Option X, ind (unselQ get t) ((splitH' z).symm (a, tauH z upd (some y) r)) =
      if get (upd (memH z r) (some y)) t.l t.e = none then 1 else 0 := fun a ↦ rfl
  simp only [h]
  rw [← Finset.sum_mul, sum_cr_sq, one_mul]

variable {get updOf}

omit [Fintype M] [DecidableEq M] in
theorem upd_unsel_iff (hu : CwTrialUpd get updOf) {t : TrialPt} {m : M}
    (hm : get m t.l t.e = none) (v : X) :
    get (updOf t m (some v)) t.l t.e = none ↔ ¬ Codeword.Valid (trunc128 (t.xi + v)) := by
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
      by_cases hm : get q.2.2.2 t.l t.e = none
      · have hsum : (∑ y : X, if get (updOf t q.2.2.2 (some y)) t.l t.e = none then (1 : ℝ)
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
      · have h0 : ∀ y : X, get (updOf t q.2.2.2 (some y)) t.l t.e ≠ none := fun y ↦ hk t _ _ hm
        have hR : (if EmptyUnsel get z t q.2 then (1 : ℝ) else 0) = 0 :=
          ite_eq_right fun h ↦ hm h.2.2
        rw [hR, mul_zero, neg_zero, ite_eq_right hm]
        simp only [h0, ↓reduceIte, Finset.sum_const_zero, zero_div, sub_zero, le_refl]
    · have hc' : q.2.1.1 z ≠ none := by rw [← splitH'_apply_fst, hc]; exact Option.some_ne_none y
      show gw (splitH' z) (tauH z (updOf t)) (unselQ get t) (some y) (splitH' z q).2 - _ ≤ _
      have hR : (if EmptyUnsel get z t q.2 then (1 : ℝ) else 0) = 0 :=
        ite_eq_right fun h ↦ hc' h.2.1
      rw [hR, mul_zero, neg_zero, gw_unselQ, hmem]
      by_cases hm : get q.2.2.2 t.l t.e = none
      · rw [ite_eq_left hm]
        split_ifs <;> norm_num
      · rw [ite_eq_right hm, ite_eq_right (hk t _ _ hm), sub_zero]
  · have ha' : q.2.2.1.1 z ≠ none := ha
    have hR : (if EmptyUnsel get z t q.2 then (1 : ℝ) else 0) = 0 :=
      ite_eq_right fun h ↦ ha' h.1
    rw [ite_eq_right ha, ind_unselQ, ind_unselQ, hR, mul_zero, neg_zero]
    show (if get (updOf t q.2.2.2 (q.2.2.1.1 z)) t.l t.e = none then (1 : ℝ) else 0) - _ ≤ 0
    by_cases hm : get q.2.2.2 t.l t.e = none
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
  have hρ : 0 ≤ rhoCw := le_trans (by positivity) inv_two_pow_21_le_rhoCw
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
  · have hm : get q.2.2.2 t.l t.e ≠ none := fun hm ↦
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
  by_cases hm : get (memH z r) t.l t.e = none
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
  have hρ : 0 ≤ rhoCw := le_trans (by positivity) inv_two_pow_21_le_rhoCw
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
`unselFlip_le`, CostJoint's `drop_of_survive`): `2^-22 e` plus the `n`-weighted unselected mass
after the read is at most the one before plus `3 p`. -/
theorem unselRead_drop (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf) (z : Z)
    (t : TrialPt) {n : HwReg X Z M → ℝ} (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (2 ^ 22 : ℝ)⁻¹ * (∑ q, (if EmptyUnsel get z t q.2 then 1 else 0) * (n q.2 * (σ q q).re)) +
      ∑ r : Option X × M, dW (fun q ↦ ind (unselQ get t) q * n q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) ≤
    dW (fun q ↦ ind (unselQ get t) q * n q.2) σ +
      3 * ∑ q, (if CwRecG get z t q.2 then 1 else 0) * (n q.2 * (σ q q).re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hnσ : ∀ q, 0 ≤ n q.2 * (σ q q).re := fun q ↦ mul_nonneg (hn0 _) (hre q)
  refine drop_of_survive (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num)
    (hnσ q)) (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hnσ q))
    inv_two_pow_21_le_rhoCw ?_
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

/-- Rates with the same digest give the same digests after adding a value. -/
theorem trunc128_add_congr {a b : X} (h : trunc128 a = trunc128 b) (v : X) :
    trunc128 (a + v) = trunc128 (b + v) := by
  rw [trunc128_eq, trunc128_eq] at h
  rw [trunc128_eq, trunc128_eq]
  have h' := (bitsEquiv 128).symm.injective h
  refine congrArg (bitsEquiv 128).symm (funext fun j ↦ ?_)
  rw [Pi.add_apply, Pi.add_apply, congrFun h' j]

/-- **The trial-head states** of a trial read at the cell `z`: a bad union, or the trial's block
at its key's message slot with head-tail `z` at a rate with the trial's digest (the support
invariant of the trial reads). Unlike EncPotential's `TrialGood`, the key may be selected. -/
def TrialHead (L : HonestTable) (z : Z) (t : TrialPt) (s : HwReg X Z M) : Prop :=
  ¬ Good L.perm (union s.2.1 s.1) ∨ (MsgAt L (t.l, t.e) (blocks (blockInput t.x)) ∧
    ∃ xi, trunc128 xi = trunc128 t.xi ∧
      IsHeadTail L.perm (union s.2.1 s.1) (blocks (blockInput t.x)) z xi)

/-- `TrialHead`, decided classically. -/
noncomputable instance trialHeadDec (L : HonestTable) (z : Z) (t : TrialPt) :
    DecidablePred (TrialHead (M := M) L z t) :=
  Classical.decPred _

omit [Fintype M] [DecidableEq M] in
theorem trialHead_congr {L : HonestTable} {z : Z} {t : TrialPt} {s s' : HwReg X Z M}
    (hk : (union s'.2.1 s'.1).k = (union s.2.1 s.1).k)
    (hk' : (union s'.2.1 s'.1).k' = (union s.2.1 s.1).k') :
    TrialHead L z t s' ↔ TrialHead L z t s := by
  unfold TrialHead
  simp only [good_congr hk hk', isHeadTail_congr hk hk']

omit [Fintype M] [DecidableEq M] in
theorem trialHead_offCell (L : HonestTable) (z : Z) (t : TrialPt) :
    OffCell z (fun s : HwReg X Z M ↦ if TrialHead L z t s then (1 : ℝ) else 0) := by
  intro s s' h1 h2 h3
  obtain ⟨hk, hk', -⟩ := union_congr_off h1 h2 h3
  exact if_congr (trialHead_congr hk hk') rfl rfl

omit [Fintype M] [DecidableEq M] in
theorem trialHead_offCell' (L : HonestTable) (z : Z) (t : TrialPt) :
    OffCell z (fun s : HwReg X Z M ↦ if TrialHead L z t s then (0 : ℝ) else 1) := by
  intro s s' h1 h2 h3
  obtain ⟨hk, hk', -⟩ := union_congr_off h1 h2 h3
  exact if_congr (trialHead_congr hk hk') rfl rfl

variable {get updOf}

omit [Fintype M] [DecidableEq M] in
/-- **After a trial read the read cell does not count**: on `TrialHead` states, recording any value
`y` at `z` with the trial's update leaves `encCSet` (an unselected key selects the codeword digest,
a selected key stays selected). -/
theorem not_mem_encCSet_of_trialHead (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf)
    {L : HonestTable} {z : Z} {t : TrialPt} {s s' : HwReg X Z M} {y : X}
    (hg : TrialHead L z t s) (hk1 : (union s'.2.1 s'.1).k = (union s.2.1 s.1).k)
    (hk2 : (union s'.2.1 s'.1).k' = (union s.2.1 s.1).k') (hz : (union s'.2.1 s'.1).h z = some y)
    (hm : s'.2.2 = updOf t s.2.2 (some y)) : s' ∉ encCSet get L z := by
  rintro ⟨hG', k, hun, t', xi', w, hP, hi, hw, hcw⟩
  have hG : Good L.perm (union s.2.1 s.1) := (good_congr hk1 hk2).1 hG'
  rcases hg with hg | ⟨hslot, xi, hxi, hhead⟩
  · exact hg hG
  have hhead' := (isHeadTail_congr hk1.symm hk2.symm).1 hhead
  obtain ⟨rfl, rfl⟩ := hG'.isHeadTail_unique hi hhead'
  obtain rfl := msgAt_unique L _ _ _ hP hslot
  rw [hz] at hw
  obtain rfl := Option.some.inj hw
  rw [hm] at hun
  rw [trunc128_add_congr hxi] at hcw
  by_cases hm0 : get s.2.2 t.l t.e = none
  · rw [hu.sel t _ y hm0] at hun
    exact ((cwSel_eq_none_iff hm0 t.x t.xi y).1 hun) hcw
  · exact hk t _ _ hm0 hun

/-- **A flip operator of a read of `h` splits along a predicate off the read cell**: with
`G = sqrtDiag 1_P`, `G' = sqrtDiag 1_{¬P}`, `tr (F σ) = tr (F (G σ G)) + tr (F (G' σ G'))`. -/
theorem trace_flipOp_split (z : Z) (upd : M → Option X → M) (P : HwReg X Z M → Prop)
    [DecidablePred P] (hP : OffCell z (fun s ↦ if P s then (1 : ℝ) else 0))
    (hP' : OffCell z (fun s ↦ if P s then (0 : ℝ) else 1)) (S : Set (Unit × HwReg X Z M))
    [DecidablePred (· ∈ S)] (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r) S * σ).trace =
      (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r) S *
          (sqrtDiag (fun s ↦ if P s then (1 : ℝ) else 0) * σ *
            sqrtDiag (fun s ↦ if P s then (1 : ℝ) else 0))).trace +
        (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r) S *
          (sqrtDiag (fun s ↦ if P s then (0 : ℝ) else 1) * σ *
            sqrtDiag (fun s ↦ if P s then (0 : ℝ) else 1))).trace := by
  set F := flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r) S
  set G := sqrtDiag (fun s : HwReg X Z M ↦ if P s then (1 : ℝ) else 0)
  set G' := sqrtDiag (fun s : HwReg X Z M ↦ if P s then (0 : ℝ) else 1)
  have hsum : G + G' = 1 := by
    simp only [G, G', sqrtDiag]
    rw [diagonal_add, ← diagonal_one]
    refine congrArg diagonal (funext fun q ↦ ?_)
    by_cases h : P q.2 <;> simp [h]
  have h0 : G * G' = 0 := by
    simp only [G, G', sqrtDiag]
    rw [diagonal_mul_diagonal, ← diagonal_zero]
    refine congrArg diagonal (funext fun q ↦ ?_)
    by_cases h : P q.2 <;> simp [h]
  have h0' : G' * G = 0 := by
    simp only [G, G', sqrtDiag]
    rw [diagonal_mul_diagonal, ← diagonal_zero]
    refine congrArg diagonal (funext fun q ↦ ?_)
    by_cases h : P q.2 <;> simp [h]
  have hFG : G * F = F * G := sqrtDiag_mul_flipOp z upd hP S
  have hFG' : G' * F = F * G' := sqrtDiag_mul_flipOp z upd hP' S
  have hcross : ∀ A B : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ, B * F = F * B →
      B * A = 0 → (F * (A * σ * B)).trace = 0 := fun A B hB hBA ↦ by
    calc (F * (A * σ * B)).trace = (B * (F * A * σ)).trace := by
          rw [Matrix.trace_mul_comm B]
          simp only [Matrix.mul_assoc]
      _ = (B * F * A * σ).trace := by simp only [Matrix.mul_assoc]
      _ = (F * (B * A) * σ).trace := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hBA, Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero]
  have hσ : (F * σ).trace = (F * ((G + G') * σ * (G + G'))).trace := by
    rw [hsum, Matrix.one_mul, Matrix.mul_one]
  rw [hσ]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
  rw [hcross G G' hFG' h0', hcross G' G hFG h0, add_zero, zero_add]

/-- **The good block of the read cell**: on `TrialHead` states, the flip of `encCSet` is at most
`2/|X|` on the diagonal and `4/|X|²` from the empty-to-recorded amplitudes with reference weight
`0`, so ReadCost's `re_trace_flipOp_le` (cross term over all recorded cells, here at most the
trace) gives `6/|X|` per unit of trace. -/
theorem goodBlock_le (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf) (L : HonestTable)
    (z : Z) (t : TrialPt) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
        (liftSet (encCSet get L z)) *
        (sqrtDiag (fun s ↦ if TrialHead L z t s then (1 : ℝ) else 0) * σ *
          sqrtDiag (fun s ↦ if TrialHead L z t s then (1 : ℝ) else 0))).trace.re ≤
      6 / (Fintype.card X : ℝ) *
        ∑ q, (if TrialHead L z t q.2 then (1 : ℝ) else 0) * (σ q q).re := by
  set S := liftSet (encCSet get L z)
  set g : HwReg X Z M → ℝ := fun s ↦ if TrialHead L z t s then (1 : ℝ) else 0
  have hg0 : ∀ s, 0 ≤ g s := fun s ↦ by simp only [g]; split_ifs <;> norm_num
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hgσ : ∀ q, 0 ≤ g q.2 * (σ q q).re := fun q ↦ mul_nonneg (hg0 _) (hre q)
  have hτ := posSemidef_sqrtDiag_conj g hσ
  have hdiag : ∀ q, ((sqrtDiag g * σ * sqrtDiag g) q q).re = g q.2 * (σ q q).re :=
    re_sqrtDiag_conj_apply hg0 σ
  have hF := re_trace_flipOp_le S (cellRead_readH z (updOf t)) (clsOff_readH z (updOf t))
    (fun _ ↦ 0) (fun _ _ ↦ True) (fun _ _ _ hy ↦ absurd trivial hy) hτ
    (cellNoBot_sqrtDiag (trialHead_offCell L z t) hnb)
  have hA : ∀ q : Unit × HwReg X Z M, TrialHead L z t q.2 → actH z (splitH' z q).2 →
      ∀ y, ind S ((splitH' z).symm (some y, tauH z (updOf t) (some y) (splitH' z q).2)) = 0 := by
    intro q hg ha y
    have ha' : q.2.2.1.1 z = none := ha
    rw [splitH'_symm_tau]
    exact ind_eq_zero_of_not_mem S (not_mem_encCSet_of_trialHead hu hk hg (union_k_h _ _ _ _)
      (union_k'_h _ _ _ _) (union_h_upd q.2.2.1 q.2.1.1 q.2.1.2 z y ha') rfl)
  have hH : ∀ q : Unit × HwReg X Z M, TrialHead L z t q.2 → ¬ actH z (splitH' z q).2 →
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
  have hgw : ∀ q : Unit × HwReg X Z M, TrialHead L z t q.2 → actH z (splitH' z q).2 → ∀ y,
      gw (splitH' z) (tauH z (updOf t)) S (some y) (splitH' z q).2 ≤ 2 / Fintype.card X :=
    fun q hg ha y ↦ gw_some_le_two_div S (hA q hg ha y)
  have hN : (0 : ℝ) ≤ 2 / Fintype.card X := by positivity
  have hfd : ∀ q, fd (splitH' z) (actH z) (tauH z (updOf t)) S (phiH z (updOf t)) q *
      (g q.2 * (σ q q).re) ≤ 2 / Fintype.card X * (g q.2 * (σ q q).re) := fun q ↦ by
    by_cases hg : TrialHead L z t q.2
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
    by_cases hg : TrialHead L z t q.2
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
theorem offBlock_le (L : HonestTable) (z : Z) (t : TrialPt)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
        (liftSet (encCSet get L z)) *
        (sqrtDiag (fun s ↦ if TrialHead L z t s then (0 : ℝ) else 1) * σ *
          sqrtDiag (fun s ↦ if TrialHead L z t s then (0 : ℝ) else 1))).trace.re ≤
      3 * ∑ q, (if TrialHead L z t q.2 then (0 : ℝ) else 1) * (σ q q).re := by
  set g : HwReg X Z M → ℝ := fun s ↦ if TrialHead L z t s then (0 : ℝ) else 1
  have hg0 : ∀ s, 0 ≤ g s := fun s ↦ by simp only [g]; split_ifs <;> norm_num
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hτ := posSemidef_sqrtDiag_conj g hσ
  have hdiag : ∀ q, ((sqrtDiag g * σ * sqrtDiag g) q q).re = g q.2 * (σ q q).re :=
    re_sqrtDiag_conj_apply hg0 σ
  have hF := re_trace_flipOp_le_good (liftSet (encCSet get L z)) (cellRead_readH z (updOf t))
    (clsOff_readH z (updOf t)) (fun _ ↦ False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) hτ
    (cellNoBot_sqrtDiag (trialHead_offCell' L z t) hnb)
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
theorem cellFlip_le (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf) (L : HonestTable)
    (z : Z) (t : TrialPt) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
        (liftSet (encCSet get L z)) * σ).trace.re ≤
      6 / (Fintype.card X : ℝ) * ∑ q, (σ q q).re +
        3 * ∑ q, (if TrialHead L z t q.2 then (0 : ℝ) else 1) * (σ q q).re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hs := congrArg Complex.re (trace_flipOp_split z (updOf t) (TrialHead L z t)
    (trialHead_offCell L z t) (trialHead_offCell' L z t) (liftSet (encCSet get L z)) σ)
  rw [Complex.add_re] at hs
  rw [hs]
  have hG := goodBlock_le hu hk L z t hσ hnb
  have hO := offBlock_le (get := get) (updOf := updOf) L z t hσ hnb
  have hle : ∑ q, (if TrialHead L z t q.2 then (1 : ℝ) else 0) * (σ q q).re ≤ ∑ q, (σ q q).re :=
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
noncomputable def trialCntE (L : HonestTable) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, (if EmptyUnsel get z t q.2 then 1 else 0) * (encOff L z (t.l, t.e) q.2 * (σ q q).re)

/-- **The refined charge of a trial read**: three times the count-weighted codeword-recorded
mass, `6/|X|` per unit of trace and three times the off-head mass. -/
noncomputable def trialChgRe (L : HonestTable) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  3 * (∑ q, (if CwRecG get z t q.2 then 1 else 0) * (encOff L z (t.l, t.e) q.2 * (σ q q).re)) +
    (6 / (Fintype.card X : ℝ) * ∑ q, (σ q q).re +
      3 * ∑ q, (if TrialHead L z t q.2 then (0 : ℝ) else 1) * (σ q q).re)

open scoped Classical in
/-- **The joint count of the selecting reads, refined**, per port: `trialCntE` at a trial read
port. -/
noncomputable def cntEW (L : HonestTable) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then
    ENNReal.ofReal (trialCntE get L (trialOf updOf c).1 (trialOf updOf c).2 σ) else 0

open scoped Classical in
/-- **The refined charge of a trial read port** (`trialChgRe`; `0` elsewhere). -/
noncomputable def trialChgR (L : HonestTable) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then
    ENNReal.ofReal (trialChgRe get L (trialOf updOf c).1 (trialOf updOf c).2 σ) else 0

omit [DecidableEq M] in
theorem trialCntE_nonneg (L : HonestTable) (z : Z) (t : TrialPt)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ trialCntE get L z t σ :=
  Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num)
    (mul_nonneg (encOff_nonneg L z _ _) (Complex.nonneg_iff.1 hσ.diag_nonneg).1)

variable {get updOf}

/-- **A trial read against the potential, refined** (real form): `2^-22 trialCntE` plus the
potential after the read is at most the potential before plus `trialChgRe`. The other keys keep
their part (`encA_keep`); the trial's key off the read cell drops (`unselRead_drop`); the read
cell counts after the read by `cellFlip_le`. -/
theorem trialRead_drop_ref (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf)
    (L : HonestTable) (z : Z) (t : TrialPt)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (2 ^ 22 : ℝ)⁻¹ * trialCntE get L z t σ +
      ∑ r : Option X × M, dW (fun q ↦ encPot get L q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) ≤
    dW (fun q ↦ encPot get L q.2) σ + trialChgRe get L z t σ := by
  have hsplit : ∀ τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ,
      dW (fun q ↦ encPot get L q.2) τ = dW (fun q ↦ encA get L z (t.l, t.e) q.2) τ +
        dW (fun q ↦ ind (unselQ get t) q * encOff L z (t.l, t.e) q.2) τ +
        dW (fun q ↦ ind (liftSet (encCSet get L z)) q) τ := fun τ ↦ by
    simp only [dW, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have hB : encB get L z (t.l, t.e) q.2 = ind (unselQ get t) q * encOff L z (t.l, t.e) q.2 := by
      rw [ind_unselQ]
      unfold encB
      dsimp only
      split_ifs <;> ring
    rw [encPot_eq get L z (t.l, t.e) q, hB]
    ring
  have hA : ∑ r : Option X × M, dW (fun q ↦ encA get L z (t.l, t.e) q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
        dW (fun q ↦ encA get L z (t.l, t.e) q.2) σ :=
    sum_dW_conj_of_keep (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r) _
      (fun r a a' h ↦ encA_keep get updOf hu L z t r a a' h) (sum_readKrausH z (updOf t)) σ
  have hB := unselRead_drop hu hk z t (encOff_nonneg L z (t.l, t.e))
    (encOff_offCell L z (t.l, t.e)) hσ hnb
  have hsumeq : (∑ r : Option X × M, (hwReadKraus (.readH z (updOf t)) r)ᴴ *
      diagonal (fun q ↦ ((ind (liftSet (encCSet get L z)) q : ℝ) : ℂ)) *
        hwReadKraus (.readH z (updOf t)) r) =
      flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
        (liftSet (encCSet get L z)) + indProj (liftSet (encCSet get L z)) := by
    rw [flipOp, sub_add_cancel]
    rfl
  have hCpost : ∑ r : Option X × M, dW (fun q ↦ ind (liftSet (encCSet get L z)) q)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
      dW (fun q ↦ ind (liftSet (encCSet get L z)) q) σ +
        (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
          (liftSet (encCSet get L z)) * σ).trace.re := by
    rw [sum_dW_conj, hsumeq, Matrix.add_mul, Matrix.trace_add, Complex.add_re, add_comm,
      dW_eq_trace]
    rfl
  have hC := cellFlip_le hu hk L z t hσ hnb
  have hpost : ∑ r : Option X × M, dW (fun q ↦ encPot get L q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
      ∑ r : Option X × M, dW (fun q ↦ encA get L z (t.l, t.e) q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) +
      ∑ r : Option X × M, dW (fun q ↦ ind (unselQ get t) q * encOff L z (t.l, t.e) q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) +
      ∑ r : Option X × M, dW (fun q ↦ ind (liftSet (encCSet get L z)) q)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) := by
    simp only [hsplit, Finset.sum_add_distrib]
  rw [hpost, hsplit σ, hA, hCpost]
  unfold trialCntE trialChgRe
  linarith [hB, hC]

/-- **A trial read port against the potential, refined**: on a state with no decompressed `⊥` at
the read cell, `2^-22 cntEW` plus the potential after the read is at most the potential before
plus `trialChgR`. -/
theorem trialRead_potential_le_ref (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf)
    (L : HonestTable) {c : HwRead X Z M} (ht : IsTrial updOf c)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : ReadNoBot c σ) :
    (2 ^ 22 : ℝ≥0∞)⁻¹ * cntEW get updOf L c σ +
        ∑' r, potential (diagPot fun s ↦ √(encPot get L s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
      potential (diagPot fun s ↦ √(encPot get L s)) σ + trialChgR get updOf L c σ := by
  have hc := eq_readH_trialOf updOf ht
  simp only [cntEW, trialChgR, ht, ↓reduceIte]
  generalize trialOf updOf c = zt at hc ⊢
  subst hc
  obtain ⟨z, t⟩ := zt
  have hreal := trialRead_drop_ref hu hk L z t hσ hnb
  have h22 : (2 ^ 22 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 ^ 22 : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  have hpost : ∀ r : Option X × M, 0 ≤ dW (fun q ↦ encPot get L q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) := fun r ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (encPot_nonneg get L q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  rw [tsum_fintype]
  simp only [potential_encPot]
  rw [← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hpost r, h22,
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) (trialCntE_nonneg get L z t hσ))
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
the count `cntEW` along the run is at most `2^22 (q + P')` plus `2^22` times the charges, the trial
reads charging `trialChgR`. -/
theorem totalWeight_cntEW_le (hu : CwTrialUpd get updOf) (hk : TrialKeep get updOf)
    (hlab : ∀ (T T' : Finset S) (m : M'), get (T, m) = get (T', m)) (L : HonestTable)
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
      ∑' _r : Unit, potential (diagPot fun s ↦ √(encPot get L s))
          (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ) ≤
        potential (diagPot fun s ↦ √(encPot get L s)) σ + (ENNReal.ofReal σ.trace.re + cS p σ))
    (hR : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ),
      ¬ IsTrial updOf c → σ.PosSemidef → Inv (.inl (.inl (.inr c))) σ →
      ∑' r, potential (diagPot fun s ↦ √(encPot get L s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(encPot get L s)) σ + cR c σ)
    (hnb : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M'))
        (Unit × HwReg X Z (Finset S × M')) ℂ), IsTrial updOf c → Inv (.inl (.inl (.inr c))) σ →
      ReadNoBot c σ)
    (hPr : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M'))
        (Unit × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef → Inv (.inl (.inr c)) σ →
      ∑' r, potential (diagPot fun s ↦ √(encPot get L s)) (MatrixMap.conj (hwProgKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(encPot get L s)) σ + (ENNReal.ofReal σ.trace.re + cP c σ))
    (I : Λ.Interp) {B : Type} [Fintype B] [DecidableEq B] (u : B)
    (x : QuantumComp Λ (recHwSpec X Z S M') Ω (QReg.of B)) {q P' : ℕ}
    (hq : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) q)
    (hp : IFreeM.IsChargeBound x (portCharge (extProgCharge X Z (Finset S × M') (recSpec S M')))
      P')
    (hx : (runtimeR m₀).ForallQueries I P x
      ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) :
    (runtimeR m₀).totalWeight I (extWeight (hwCost (cntEW get updOf L) fun _ _ ↦ 0)) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤
      2 ^ 22 * (q + P' : ℕ) + 2 ^ 22 * (runtimeR m₀).totalWeight I
        (portCh X Z S M' cS (fun c σ ↦ trialChgR get updOf L c σ + cR c σ) cP) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  set ρ := (SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix
  have hρ : ρ.PosSemidef :=
    ((SubState.basis u).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef
  have hφ0 := encPot_nonneg get L
  have hp0 : potential (diagPot fun s ↦ √(encPot get L s)) ρ = 0 :=
    (potential_basis_init m₀ hφ0 u).trans
      ((congrArg ENNReal.ofReal (encPot_init get L m₀)).trans ENNReal.ofReal_zero)
  have htr : ENNReal.ofReal ρ.trace.re ≤ 1 := (ofReal_trace_basis_init m₀ u).le
  have hR' : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef → Inv (.inl (.inl (.inr c))) σ →
      (2 ^ 22 : ℝ≥0∞)⁻¹ * cntEW get updOf L c σ + ∑' r, potential
        (diagPot fun s ↦ √(encPot get L s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(encPot get L s)) σ +
          (0 + (trialChgR get updOf L c σ + cR c σ)) := by
    intro c σ hσ hI
    rw [zero_add]
    by_cases ht : IsTrial updOf c
    · exact (trialRead_potential_le_ref hu hk L ht hσ (hnb c σ ht hI)).trans
        (add_le_add le_rfl le_self_add)
    · have h0 : cntEW get updOf L c σ = 0 := by simp only [cntEW, ht, ↓reduceIte]
      have h1 : trialChgR get updOf L c σ = 0 := by simp only [trialChgR, ht, ↓reduceIte]
      rw [h0, h1, mul_zero, zero_add, zero_add]
      exact hR c σ ht hσ hI
  have h := totalWeight_le_potential_runtimeR_inv m₀ hφ0 (encPot_labelFree get hlab L) P Inv hP
    (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * cntEW get updOf L c σ)
    (fun p σ ↦ ENNReal.ofReal σ.trace.re + cS p σ)
    (fun c σ ↦ 0 + (trialChgR get updOf L c σ + cR c σ))
    (fun c σ ↦ ENNReal.ofReal σ.trace.re + cP c σ) hS hR' hPr I x hρ hx
  have hlow : (2 ^ 22 : ℝ≥0∞)⁻¹ *
      (runtimeR m₀).totalWeight I (extWeight (hwCost (cntEW get updOf L) fun _ _ ↦ 0)) x ρ ≤
      (runtimeR m₀).totalWeight I (extWeight (hwCost
        (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * cntEW get updOf L c σ) fun _ _ ↦ 0)) x ρ := by
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m₀) I _
      (extWeight (hwCost (cntEW get updOf L) fun _ _ ↦ 0)) x ρ).symm).trans
      (totalWeight_le_totalWeight (runtimeR m₀) I (fun i σ _ ↦ ?_) x hρ)
    rcases i with ((_ | _) | _) | _
    · exact le_of_eq (mul_zero _)
    · exact le_rfl
    · exact le_of_eq (mul_zero _)
    · exact le_of_eq (mul_zero _)
  have hsplit := (totalWeight_le_totalWeight (runtimeR m₀) I
    (w := portCh X Z S M' (fun p σ ↦ ENNReal.ofReal σ.trace.re + cS p σ)
      (fun c σ ↦ 0 + (trialChgR get updOf L c σ + cR c σ))
      (fun c σ ↦ ENNReal.ofReal σ.trace.re + cP c σ))
    (w' := fun i σ ↦ portCh X Z S M' (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (fun _ _ ↦ 0)
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ +
      portCh X Z S M' cS (fun c σ ↦ trialChgR get updOf L c σ + cR c σ) cP i σ)
    (fun i σ _ ↦ le_of_eq (congrFun (congrFun (portCh_add _ _ _ _ _ _) i) σ)) x hρ).trans
    (le_of_eq (totalWeight_add_weight (runtimeR m₀) I _ _ x ρ))
  have ht := (totalWeight_portCh_trace_le m₀ I x hq hp hρ).trans
    ((mul_le_mul_of_nonneg_left htr zero_le).trans_eq (mul_one _))
  have hmain := hlow.trans (h.trans ((add_le_add (le_of_eq hp0) le_rfl).trans_eq (zero_add _)
    |>.trans (hsplit.trans (add_le_add ht le_rfl))))
  have h2 : (2 ^ 22 : ℝ≥0∞) ≠ 0 := by positivity
  have h2' : (2 ^ 22 : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have e : ∀ w : ℝ≥0∞, w = 2 ^ 22 * ((2 ^ 22 : ℝ≥0∞)⁻¹ * w) := fun w ↦ by
    rw [← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
  exact (e _).trans_le ((mul_le_mul_of_nonneg_left hmain zero_le).trans_eq (mul_add _ _ _))

end joint

/-! ## The challenge prefix -/

section prefixRef

attribute [local instance] badRDec

/-- **A selected key stays selected** under `trialUpd`. -/
theorem trialKeep_trialUpd : TrialKeep (Prod.snd : Mem → Selections) trialUpd := by
  intro t m o hm
  show cwUpd t.l t.e t.x t.xi m.2 o t.l t.e ≠ none
  rcases o with _ | v
  · exact hm
  · show (if m.2 t.l t.e = none then cwSel m.2 t.l t.e t.x t.xi v else m.2) t.l t.e ≠ none
    rw [ite_eq_right hm]
    exact hm

open scoped Classical in
/-- **The off-head mass of a trial read port**: the weight off `TrialHead` (`0` at the other read
ports). -/
noncomputable def offHeadW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal (∑ q, (if TrialHead L (trialOf trialUpd c).1
    (trialOf trialUpd c).2 q.2 then (0 : ℝ) else 1) * (σ q q).re) else 0

open scoped Classical in
/-- The codeword-recorded mass of a trial read port through `CwRecG` (`cwRecGW_eq`: RestMass's
integrand `cwRecW`). -/
noncomputable def cwRecGW (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal (∑ q, if CwRecG Prod.snd (trialOf trialUpd c).1
    (trialOf trialUpd c).2 q.2 then (σ q q).re else 0) else 0

theorem cwRecGW_eq (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    cwRecGW c σ = cwRecW Prod.snd trialUpd c σ := by
  unfold cwRecGW cwRecW
  split_ifs
  · exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun a _ ↦ if_congr Iff.rfl rfl rfl)
  · rfl

/-- **The refined joint count along the challenge prefix** (`cntEW`). -/
noncomputable def cntEP (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments
    (extWeight (hwCost (cntEW Prod.snd trialUpd L) fun _ _ ↦ 0)) (prefixR A L) initR

/-- **The off-head mass of the trial reads along the challenge prefix**. -/
noncomputable def offHeadPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (offHeadW L) fun _ _ ↦ 0))
    (prefixR A L) initR

/-- **The charge of a read call per unit of trace, refined**: the `k`, `k'` reads'
`potCap (ε + 2/|X| + 2/|Z| + 2 √ε)` and the trial reads' `6/|X|`. -/
noncomputable def kapR6 (q : ℕ) : ℝ :=
  potCap q * (epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q)) +
    6 / (Fintype.card X : ℝ)

theorem kapR6_nonneg (q : ℕ) : 0 ≤ kapR6 q := by
  have := epsQ_nonneg q
  unfold kapR6
  positivity

/-- **The refined trial charge against the codeword-recorded and off-head masses** (real form):
where the count off the read cell is at most `C`, `trialChgRe ≤ 3 C cw + 3 off + 6/|X| tr σ`. -/
theorem trialChgRe_le {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)
    (L : HonestTable) (z : Z) (t : TrialPt) {C : ℝ}
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ a, encOff L z (t.l, t.e) a.2 ≤ C ∨ σ a a = 0) :
    trialChgRe get L z t σ ≤ 3 * C * (∑ a, if CwRecG get z t a.2 then (σ a a).re else 0) +
      3 * (∑ a, (if TrialHead L z t a.2 then (0 : ℝ) else 1) * (σ a a).re) +
        6 / (Fintype.card X : ℝ) * σ.trace.re := by
  have hre : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ a, (σ a a).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  have h1 : ∑ a, (if CwRecG get z t a.2 then (1 : ℝ) else 0) * (encOff L z (t.l, t.e) a.2 *
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

variable {q : ℕ}

/-- **The refined trial charge on the prefix**: `3 C cwRecW + 3 offHeadW + 6/|X| tr σ` with
`C = nW + nD q` (`trialChgRe_le`, the count bounded by the grades). -/
theorem trialChgR_le_prefix (L : HonestTable) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hI : PreInv q (.inl (.inl (.inr c))) σ) :
    trialChgR Prod.snd trialUpd L c σ ≤
      ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ)) * cwRecW Prod.snd trialUpd c σ +
        3 * offHeadW L c σ + ENNReal.ofReal (6 / (Fintype.card X : ℝ) * σ.trace.re) := by
  have hC : ∀ (z : Z) (k : Layer × KeyIndex) a, encOff L z k a.2 ≤ ((nW + nD q : ℕ) : ℝ) ∨
      σ a a = 0 := fun z k a ↦ by
    by_cases h0 : σ a a = 0
    · exact .inr h0
    · have hs := (hI.2.1 a a h0).1
      refine .inl ((encOff_le_grade L _ _ a.2).trans ?_)
      have : dbGrade a.2.2.1 + dbGrade a.2.1 ≤ nW + nD q := by
        have h1 : dbGrade a.2.1 ≤ nD q := hs.1
        have h2 : dbGrade a.2.2.1 ≤ progCap := hs.2
        unfold nW
        omega
      exact_mod_cast this
  rw [← cwRecGW_eq]
  by_cases ht : IsTrial trialUpd c
  · simp only [trialChgR, cwRecGW, offHeadW, ht, ↓reduceIte]
    generalize trialOf trialUpd c = zt
    obtain ⟨z, t⟩ := zt
    dsimp only
    have h3 : (0 : ℝ) ≤ 3 * ((nW + nD q : ℕ) : ℝ) := by positivity
    have hre : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    have hR0 : 0 ≤ ∑ a, if CwRecG Prod.snd z t a.2 then (σ a a).re else 0 :=
      Finset.sum_nonneg fun a _ ↦ by split_ifs; exacts [hre a, le_rfl]
    have hW0 : 0 ≤ ∑ a, (if TrialHead L z t a.2 then (0 : ℝ) else 1) * (σ a a).re :=
      Finset.sum_nonneg fun a _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hre a)
    calc ENNReal.ofReal (trialChgRe Prod.snd L z t σ)
        ≤ ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ) *
            (∑ a, if CwRecG Prod.snd z t a.2 then (σ a a).re else 0) +
          3 * (∑ a, (if TrialHead L z t a.2 then (0 : ℝ) else 1) * (σ a a).re) +
            6 / (Fintype.card X : ℝ) * σ.trace.re) :=
          ENNReal.ofReal_le_ofReal (trialChgRe_le Prod.snd L z t hσ (hC z (t.l, t.e)))
      _ ≤ ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ) *
            (∑ a, if CwRecG Prod.snd z t a.2 then (σ a a).re else 0)) +
          ENNReal.ofReal (3 * (∑ a, (if TrialHead L z t a.2 then (0 : ℝ) else 1) * (σ a a).re)) +
            ENNReal.ofReal (6 / (Fintype.card X : ℝ) * σ.trace.re) :=
          ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
      _ = _ := by
          have e1 : ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ) *
              (∑ a, if CwRecG Prod.snd z t a.2 then (σ a a).re else 0)) =
              ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ)) *
                ENNReal.ofReal (∑ a, if CwRecG Prod.snd z t a.2 then (σ a a).re else 0) :=
            ENNReal.ofReal_mul h3
          have e2 : ENNReal.ofReal (3 * (∑ a, (if TrialHead L z t a.2 then (0 : ℝ) else 1) *
              (σ a a).re)) = 3 * ENNReal.ofReal (∑ a, (if TrialHead L z t a.2 then (0 : ℝ) else 1) *
                (σ a a).re) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]
          rw [e1, e2]
  · simp only [trialChgR, ht, ↓reduceIte, zero_le]

/-- **The charge of a read call on the prefix, refined**: the trial charge and `cRq` together are
at most `3 C cwRecW + 3 offHeadW + kapR6 q tr σ`. -/
theorem readChargeR_le (L : HonestTable) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hI : PreInv q (.inl (.inl (.inr c))) σ) :
    trialChgR Prod.snd trialUpd L c σ + cRq q c σ ≤
      ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ)) * cwRecW Prod.snd trialUpd c σ +
        3 * offHeadW L c σ + ENNReal.ofReal (kapR6 q) * ENNReal.ofReal σ.trace.re := by
  have htr : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have he := epsQ_nonneg q
  refine (add_le_add (trialChgR_le_prefix L c hσ hI) le_rfl).trans ?_
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  unfold cRq
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) htr)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) htr)),
    ← ENNReal.ofReal_mul (kapR6_nonneg q)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold kapR6
  ring

/-! ### The empty-cell flips of a trial read against the refined count -/

theorem cwSel_congr {m : Selections} {l : Layer} {e : KeyIndex} {x xi xi' : X}
    (h : trunc128 xi = trunc128 xi') (v : X) : cwSel m l e x xi v = cwSel m l e x xi' v := by
  unfold cwSel
  rw [trunc128_add_congr h]

/-- A trial read only adds targets. -/
theorem tgt_trialUpd (L : HonestTable) (W : Hw X Z) (t : TrialPt) (m : Mem) (o : Option X)
    {l : List X} {y : Digest} (h : xmssTgtHw L W m.2 l = some y) :
    xmssTgtHw L W (trialUpd t m o).2 l = some y := by
  rcases o with _ | v
  · exact h
  · by_cases hm : m.2 t.l t.e = none
    · show xmssTgtHw L W (cwUpd t.l t.e t.x t.xi m.2 (some v)) l = some y
      rw [cwUpd_some_of_none _ _ _ _ hm]
      unfold cwSel
      split_ifs
      · exact xmssTgt_select_mono hm h
      · exact h
    · show xmssTgtHw L W (if m.2 t.l t.e = none then cwSel m.2 t.l t.e t.x t.xi v else m.2) l =
        some y
      rw [ite_eq_right hm]
      exact h

/-- Filling the empty cell `z` of `h` and moving the memory to one with at least the targets keeps
`BadR`. -/
theorem mem_badR_fill {L : HonestTable} {s : HwReg X Z Mem} (hs : s ∈ BadR L progCap) {z : Z}
    (hz : s.1.1 z = none) (u : Option X) (m : Mem)
    (hm : ∀ l y, xmssTgtHw L s.2.1 s.2.2.2 l = some y → xmssTgtHw L s.2.1 m.2 l = some y) :
    ((Function.update s.1.1 z u, s.1.2), s.2.1, m) ∈ BadR L progCap :=
  mem_hwTargetBad_fill (s := (s.1, s.2.1, s.2.2.2)) hs hz u m.2 hm

/-- **A state in `BadR` with the cell empty has no flip value** (the slices are up-closed and a
trial read only adds targets). -/
theorem not_hFlip_of_badR {L : HonestTable} {z : Z} {t : TrialPt} {q : Unit × HwReg X Z Mem}
    (hb : q.2 ∈ BadR L progCap) (hD : q.2.1.1 z = none) (v : X) :
    ¬ hFlip (BadR L progCap) z (trialUpd t) q v := by
  rintro (h | ⟨u, h⟩)
  · exact h (iff_of_true (mem_badR_fill hb hD (some v) q.2.2.2 fun _ _ h ↦ h) hb)
  · exact h (iff_of_true (mem_badR_fill hb hD u (trialUpd t q.2.2.2 (some v))
      fun _ _ h ↦ tgt_trialUpd L _ t _ _ h) (mem_badR_fill hb hD u q.2.2.2 fun _ _ h ↦ h))

/-- **A flip value of a state outside `BadR` whose key is selected** records a value that puts the
state into `BadR` (the memory does not move). -/
theorem hFlip_sel {L : HonestTable} {z : Z} {t : TrialPt} {q : Unit × HwReg X Z Mem}
    (hb : q.2 ∉ BadR L progCap) (hm : q.2.2.2.2 t.l t.e ≠ none) {v : X}
    (h : hFlip (BadR L progCap) z (trialUpd t) q v) :
    ((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2) ∈ BadR L progCap := by
  have hkeep : trialUpd t q.2.2.2 (some v) = q.2.2.2 := by
    show (q.2.2.2.1, if q.2.2.2.2 t.l t.e = none then cwSel q.2.2.2.2 t.l t.e t.x t.xi v
      else q.2.2.2.2) = q.2.2.2
    rw [ite_eq_right hm]
  rcases h with h | ⟨u, h⟩
  · by_contra hc
    exact h (iff_of_false hc hb)
  · rw [hkeep] at h
    exact absurd Iff.rfl h

/-- **A flip value of a state outside `BadR` with a selection read** (at a rate with the trial's
digest) records a codeword selection that puts the state into `Bad`. -/
theorem hFlip_unsel {L : HonestTable} {z : Z} {t : TrialPt} {xi : X}
    {q : Unit × HwReg X Z Mem} (hb : q.2 ∉ BadR L progCap)
    (hsr : SelectRead L q.2.1 q.2.2.1 q.2.2.2.2 z t.l t.e t.x xi)
    (hxi : trunc128 xi = trunc128 t.xi) {v : X} (h : hFlip (BadR L progCap) z (trialUpd t) q v) :
    ∃ u : Option X, ((Function.update q.2.1.1 z u, q.2.1.2), q.2.2.1,
      cwSel q.2.2.2.2 t.l t.e t.x xi v) ∈ Bad L progCap := by
  have hb' : (q.2.1, q.2.2.1, q.2.2.2.2) ∉ Bad L progCap := hb
  have hkeep : ∀ u, ((Function.update q.2.1.1 z u, q.2.1.2), q.2.2) ∉ BadR L progCap :=
    fun u ↦ not_mem_bad_read_keep hb' hsr u
  rcases h with h | ⟨u, h⟩
  · exact absurd (iff_of_false (hkeep (some v)) hb) h
  · refine ⟨u, ?_⟩
    have h1 : ((Function.update q.2.1.1 z u, q.2.1.2), q.2.2.1, trialUpd t q.2.2.2 (some v)) ∈
        BadR L progCap := by
      by_contra hc
      exact h (iff_of_false hc (hkeep u))
    have hm : (trialUpd t q.2.2.2 (some v)).2 = cwSel q.2.2.2.2 t.l t.e t.x xi v := by
      show cwUpd t.l t.e t.x t.xi q.2.2.2.2 (some v) = _
      rw [cwUpd_some_of_none _ _ _ _ hsr.hm, cwSel_congr hxi.symm]
    have h2 : ((Function.update q.2.1.1 z u, q.2.1.2), q.2.2.1,
        (trialUpd t q.2.2.2 (some v)).2) ∈ Bad L progCap := h1
    rwa [hm] at h2

open scoped Classical in
/-- **Recording a value at an empty `h` cell** of a state outside `Bad` (hardwired grade at most
`progCap`): at most `2^960` values put it into `Bad` (one target per head-tail). -/
theorem card_recordH_le {L : HonestTable} {D : DbReg X Z} {W : Hw X Z} {m : Selections}
    (hs : (D, W, m) ∉ Bad L progCap) (hN : dbGrade W ≤ progCap) {z : Z} (hW : W.1 z = none)
    (hD : D.1 z = none) :
    (Finset.univ.filter fun v : X ↦
      ((Function.update D.1 z (some v), D.2), W, m) ∈ Bad L progCap).card ≤ 2 ^ 960 := by
  have hU : union W D ∉ TargetBad L.perm trunc128 (xmssTgtHw L W m) :=
    union_not_mem_of_not_mem_hwTargetBad hs hN
  have hz : (union W D).h z = none := by
    rw [union_h, hW, hD]
    rfl
  refine card_filter_le_of_imp (card_targetBad_updateH_le card_fiber_trunc128_le hU hz)
    fun v hv ↦ ?_
  have h2 : union W (Function.update D.1 z (some v), D.2.1, D.2.2) ∈
      TargetBad L.perm trunc128 (xmssTgtHw L W m) := hv.2
  rwa [union_updateH W hW] at h2

/-- **The flip values of an empty, not hardwired cell at a trial read**, over `|X|`: at most
`2^-128` times the count off the cell on the selecting states, `2^-128` on the others, and `1` off
the trial head. In `BadR` there is none; outside `BadR` the union is good; a selected key records
one target per head-tail (`card_recordH_le`); an unselected key at its trial head selects only a
codeword the other tails of the message slot reach (`card_flip_readCw_le`). -/
theorem card_hFlip_div_le (L : HonestTable) (z : Z) (t : TrialPt) (q : Unit × HwReg X Z Mem)
    (hW : q.2.2.1.1 z = none) (hD : q.2.1.1 z = none) (hN : dbGrade q.2.2.1 ≤ progCap) :
    ((Finset.univ.filter (hFlip (BadR L progCap) z (trialUpd t) q)).card : ℝ) /
        Fintype.card X ≤
      (2 ^ 128 : ℝ)⁻¹ * ((if EmptyUnsel Prod.snd z t q.2 then 1 else 0) *
        encOff L z (t.l, t.e) q.2) + (2 ^ 128 : ℝ)⁻¹ +
        (if TrialHead L z t q.2 then (0 : ℝ) else 1) := by
  have hN0 : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  have hE0 : 0 ≤ (2 ^ 128 : ℝ)⁻¹ * ((if EmptyUnsel Prod.snd z t q.2 then 1 else 0) *
      encOff L z (t.l, t.e) q.2) :=
    mul_nonneg (by positivity) (mul_nonneg (by split_ifs <;> norm_num) (encOff_nonneg _ _ _ _))
  have hT0 : 0 ≤ (if TrialHead L z t q.2 then (0 : ℝ) else 1) := by split_ifs <;> norm_num
  have h2 : (0 : ℝ) ≤ (2 ^ 128 : ℝ)⁻¹ := by positivity
  set c := (Finset.univ.filter (hFlip (BadR L progCap) z (trialUpd t) q)).card with hc
  by_cases hb : q.2 ∈ BadR L progCap
  · have h0 : c = 0 := by
      rw [hc, Finset.filter_false_of_mem fun v _ ↦ not_hFlip_of_badR hb hD v, Finset.card_empty]
    rw [h0, Nat.cast_zero, zero_div]
    linarith
  have hb' : (q.2.1, q.2.2.1, q.2.2.2.2) ∉ Bad L progCap := hb
  have hG : Good L.perm (union q.2.2.1 q.2.1) :=
    (not_mem_targetBad_iff.1 (union_not_mem_of_not_mem_hwTargetBad hb' hN)).1
  by_cases hm : q.2.2.2.2 t.l t.e = none
  · by_cases hh : TrialHead L z t q.2
    · obtain ⟨hslot, xi, hxi, hhead⟩ := hh.resolve_left (not_not.2 hG)
      have hsr : SelectRead L q.2.1 q.2.2.1 q.2.2.2.2 z t.l t.e t.x xi := ⟨hW, hD, hm, hslot, hhead⟩
      have hcard : c ≤ msgCwCount L (union q.2.2.1 q.2.1) t.l t.e * 2 ^ 960 :=
        card_filter_le_of_imp (card_flip_readCw_le hb' hsr) fun v hv ↦ hFlip_unsel hb hsr hxi hv
      have hE : EmptyUnsel Prod.snd z t q.2 := And.intro hW (And.intro hD hm)
      have henc : encOff L z (t.l, t.e) q.2 = msgCwCount L (union q.2.2.1 q.2.1) t.l t.e :=
        encOff_of_selectRead Prod.snd (t := ⟨t.l, t.e, t.x, xi⟩) L hsr hG
      rw [ite_eq_left hE, one_mul, henc]
      have hd : (c : ℝ) / Fintype.card X ≤
          ((msgCwCount L (union q.2.2.1 q.2.1) t.l t.e * 2 ^ 960 : ℕ) : ℝ) / Fintype.card X :=
        div_le_div_of_nonneg_right (Nat.cast_le.2 hcard) hN0.le
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, two_pow_div_card_X,
        mul_comm] at hd
      linarith
    · rw [ite_eq_right hh]
      have hle : (c : ℝ) / Fintype.card X ≤ 1 :=
        (div_le_one hN0).2 (Nat.cast_le.2 ((Finset.card_filter_le _ _).trans_eq Finset.card_univ))
      linarith
  · have hcard : c ≤ 2 ^ 960 :=
      card_filter_le_of_imp (card_recordH_le hb' hN hW hD) fun v hv ↦ hFlip_sel hb hm hv
    have hd : (c : ℝ) / Fintype.card X ≤ ((2 ^ 960 : ℕ) : ℝ) / Fintype.card X :=
      div_le_div_of_nonneg_right (Nat.cast_le.2 hcard) hN0.le
    rw [Nat.cast_pow, Nat.cast_ofNat, two_pow_div_card_X] at hd
    linarith

/-- **The empty-cell flips of a read port against the refined count**: on states whose hardwired
grade is at most `progCap`, `encRW ≤ 2^-128 cntEW + 2^-128 tr σ + offHeadW`. -/
theorem encRW_le (L : HonestTable) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hgr : ∀ a, dbGrade a.2.2.1 ≤ progCap ∨ σ a a = 0) :
    encRW L c σ ≤ ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * cntEW Prod.snd trialUpd L c σ +
      ENNReal.ofReal ((2 ^ 128 : ℝ)⁻¹ * σ.trace.re) + offHeadW L c σ := by
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
      have h := mul_le_mul_of_nonneg_right (card_hFlip_div_le L z t a hcell.1 hcell.2 hN) (hre a)
      refine h.trans_eq ?_
      ring
    · rw [ite_eq_right hcell, zero_mul]
      have h1 : 0 ≤ (2 ^ 128 : ℝ)⁻¹ * ((if EmptyUnsel Prod.snd z t a.2 then 1 else 0) *
          (encOff L z (t.l, t.e) a.2 * (σ a a).re)) :=
        mul_nonneg (by positivity) (mul_nonneg (by split_ifs <;> norm_num)
          (mul_nonneg (encOff_nonneg _ _ _ _) (hre a)))
      have h2 : 0 ≤ (if TrialHead L z t a.2 then (0 : ℝ) else 1) * (σ a a).re :=
        mul_nonneg (by split_ifs <;> norm_num) (hre a)
      have h3 : 0 ≤ (2 ^ 128 : ℝ)⁻¹ * (σ a a).re := mul_nonneg (by positivity) (hre a)
      linarith
  · simp only [encRW, ht, ↓reduceIte, zero_le]

variable {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The empty-cell flips along the prefix against the refined joint count**:
`encRPre ≤ 2^-128 cntEP + 2^-128 clsCap + offHeadPre`. -/
theorem encRPre_le_cntEP (L : HonestTable) :
    encRPre A L ≤ ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * cntEP A L +
      ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * (clsCap : ℝ≥0∞) + offHeadPre A L := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  set wC : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (cntEW Prod.snd trialUpd L) fun _ _ ↦ 0)
  set wT : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re)
  set wO : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (offHeadW L) fun _ _ ↦ 0)
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w' := fun i σ ↦ ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * wC i σ +
      ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * wT i σ + wO i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef hx).trans ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · show encRW L c σ ≤ ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * cntEW Prod.snd trialUpd L c σ +
          ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * ENNReal.ofReal σ.trace.re + offHeadW L c σ
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact encRW_le L c hσ fun a ↦ by
        by_cases h0 : σ a a = 0
        · exact .inr h0
        · exact .inl (hI.2.1 a a h0).1.2
    · exact zero_le
    · exact zero_le
  · refine (totalWeight_le_lin (runtimeR m0R) .instruments _ wC wT wO _ _ (fun _ _ _ ↦ le_rfl)
      (prefixR A L) initR_posSemidef).trans (add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left ?_ zero_le)) le_rfl)
    exact totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L)

/-- **The refined joint count on the challenge prefix**: for a table with `PermGood π 18`, at most
`2^22 (6q + progCap)` plus `2^22` times the charges: `3C` per unit of the codeword-recorded mass
(`cwRecPre`, `C = nW + nD q`), `3` per unit of the off-head mass (`offHeadPre`), `kapS q` per `k`,
`k'` sponge call, `kapR6 q` per read call and `potCap q` per unit of the program jump weight. -/
theorem cntEP_le (L : HonestTable) (hπ : PermGood L.perm 18) :
    cntEP A L ≤ 2 ^ 22 * ((6 * q + progCap : ℕ) : ℝ≥0∞) + 2 ^ 22 *
      (ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ)) * cwRecPre A L + 3 * offHeadPre A L +
        (ENNReal.ofReal (kapS q) * ((6 * q : ℕ) : ℝ≥0∞) +
          ENNReal.ofReal (kapR6 q) * (clsCap : ℝ≥0∞) + (potCap q : ℝ≥0∞) * kJumpPre A L)) := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  have h := totalWeight_cntEW_le cwTrialUpd_trialUpd trialKeep_trialUpd (fun _ _ _ ↦ rfl) L m0R P
    (PreInv q) hP (cSq q) (cRq q) (progJump (encPot Prod.snd L))
    (fun p _ hσ hI ↦ hS_prefix L hπ p hσ hI) (fun c _ ht hσ hI ↦ hR_prefix L hπ c ht hσ hI)
    (fun c _ _ hI ↦ readNoBot_of_noBot c hI.2.2)
    (fun c _ hσ _ ↦ tsum_potential_prog_le (encPot_nonneg Prod.snd L) c hσ)
    .instruments () (prefixR A L) (advCalls_prefixR hperm hsign L)
    (progCalls_prefixR hperm hsign L) hx
  refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le))
  set C : ℝ := ((nW + nD q : ℕ) : ℝ)
  set wM : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (cwRecW Prod.snd trialUpd) fun _ _ ↦ 0)
  set wO : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (offHeadW L) fun _ _ ↦ 0)
  set wR : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ _ ↦ 0)
  set wJ : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ _ ↦ 0) (kJumpW L))
  set wS : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ := fun i σ ↦
    ((if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal σ.trace.re
  set wX : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ := fun i σ ↦
    ENNReal.ofReal (kapS q) * wS i σ + ENNReal.ofReal (kapR6 q) * wR i σ +
      (potCap q : ℝ≥0∞) * wJ i σ
  have hle := totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w := portCh X Z HPos Selections (cSq q)
      (fun c σ ↦ trialChgR Prod.snd trialUpd L c σ + cRq q c σ) (progJump (encPot Prod.snd L)))
    (w' := fun i σ ↦ ENNReal.ofReal (3 * C) * wM i σ + 3 * wO i σ + wX i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef hx
  · have hS : (runtimeR m0R).totalWeight .instruments wS (prefixR A L) initR ≤
        ((6 * q : ℕ) : ℝ≥0∞) :=
      (totalWeight_chargeTrace_le (runtimeR m0R) .instruments
        (fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1) (prefixR A L)
        (advCalls_prefixR hperm hsign L) initR_posSemidef).trans_eq
          ((congrArg (((6 * q : ℕ) : ℝ≥0∞) * ·) (ofReal_trace_basis_init m0R ())).trans
            (mul_one _))
    have hR : (runtimeR m0R).totalWeight .instruments wR (prefixR A L) initR ≤ clsCap :=
      (totalWeight_le_totalWeight (runtimeR m0R) .instruments
        (w' := extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
          fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (fun i σ _ ↦ by
            rcases i with ((p | c) | c) | T
            · exact le_rfl
            · exact le_rfl
            · exact zero_le
            · exact le_rfl) (prefixR A L) initR_posSemidef).trans
        (totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L))
    have hX : (runtimeR m0R).totalWeight .instruments wX (prefixR A L) initR ≤
        ENNReal.ofReal (kapS q) * ((6 * q : ℕ) : ℝ≥0∞) +
          ENNReal.ofReal (kapR6 q) * (clsCap : ℝ≥0∞) + (potCap q : ℝ≥0∞) * kJumpPre A L :=
      (totalWeight_le_lin (runtimeR m0R) .instruments wX wS wR
        (fun i σ ↦ (potCap q : ℝ≥0∞) * wJ i σ) _ _ (fun _ _ _ ↦ le_rfl) (prefixR A L)
        initR_posSemidef).trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hS zero_le)
          (mul_le_mul_of_nonneg_left hR zero_le))
          (le_of_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wJ (prefixR A L)
            initR)))
    exact hle.trans ((totalWeight_le_lin (runtimeR m0R) .instruments _ wM wO wX _ _
      (fun _ _ _ ↦ le_rfl) (prefixR A L) initR_posSemidef).trans (add_le_add le_rfl hX))
  · rcases i with ((p | c) | c) | T
    · show cSq q p σ ≤ ENNReal.ofReal (3 * C) * 0 + 3 * 0 +
          (ENNReal.ofReal (kapS q) * (((1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
            ENNReal.ofReal (kapR6 q) * 0 + (potCap q : ℝ≥0∞) * 0)
      simp only [Nat.cast_one, one_mul, mul_zero, zero_add, add_zero]
      rw [← ENNReal.ofReal_mul (kapS_nonneg q)]
      cases p with
      | h => exact zero_le
      | k => exact le_rfl
      | k' => exact le_rfl
    · show trialChgR Prod.snd trialUpd L c σ + cRq q c σ ≤
        ENNReal.ofReal (3 * C) * cwRecW Prod.snd trialUpd c σ + 3 * offHeadW L c σ +
          (ENNReal.ofReal (kapS q) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
            ENNReal.ofReal (kapR6 q) * ENNReal.ofReal σ.trace.re + (potCap q : ℝ≥0∞) * 0)
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
      exact readChargeR_le L c hσ hI
    · show progJump (encPot Prod.snd L) c σ ≤ ENNReal.ofReal (3 * C) * 0 + 3 * 0 +
        (ENNReal.ofReal (kapS q) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          ENNReal.ofReal (kapR6 q) * 0 + (potCap q : ℝ≥0∞) * kJumpW L c σ)
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
      exact progJump_le_prefix L c hσ hI
    · exact zero_le

/-- **The constant of the refined Enc term**: `2^-128 (2^22 (6q + progCap) + 2^22 (6q kapS +
clsCap kapR6) + clsCap)`. -/
noncomputable def encE0 (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * (2 ^ 22 * ((6 * q + progCap : ℕ) : ℝ≥0∞) +
    2 ^ 22 * (ENNReal.ofReal (kapS q) * ((6 * q : ℕ) : ℝ≥0∞) +
      ENNReal.ofReal (kapR6 q) * (clsCap : ℝ≥0∞)) + (clsCap : ℝ≥0∞))

/-- **The recorded-mass factor of the refined Enc term**: `2^-128 2^22 3 (nW + nD q)`. -/
noncomputable def encBeta (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * (2 ^ 22 * ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ)))

/-- **The program-jump factor of the refined Enc term**: `2^-128 2^22 potCap q`. -/
noncomputable def encGamma (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * (2 ^ 22 * (potCap q : ℝ≥0∞))

/-- **The off-head factor of the refined Enc term**: `1 + 2^-128 2^22 3`. -/
noncomputable def encDelta : ℝ≥0∞ :=
  1 + ENNReal.ofReal (2 ^ 128 : ℝ)⁻¹ * (2 ^ 22 * 3)

/-- **The refined Enc term, linear in the flip-value recorded mass** (`encRPre_le_cntEP`,
`cntEP_le`, EncPorts' `kJumpPre_le`): on a `PermGood` table, for `q ≤ 2^64`,
`encRPre ≤ E₀ q + β q (cwRecPre + recBadPre) + γ q (kfPre + recJPre) + δ offHeadPre`. -/
theorem encRPre_le_lin (hq : q ≤ 2 ^ 64) (L : HonestTable) (hπ : PermGood L.perm 18) :
    encRPre A L ≤ encE0 q + encBeta q * (cwRecPre A L + recBadPre A L) +
      encGamma q * (kfPre A L + recJPre A L) + encDelta * offHeadPre A L := by
  have h1 := encRPre_le_cntEP hperm hsign L
  have hj := kJumpPre_le hperm hsign hq L
  have h3 : cntEP A L ≤ 2 ^ 22 * ((6 * q + progCap : ℕ) : ℝ≥0∞) + 2 ^ 22 *
      (ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ)) * (cwRecPre A L + recBadPre A L) +
        3 * offHeadPre A L + (ENNReal.ofReal (kapS q) * ((6 * q : ℕ) : ℝ≥0∞) +
          ENNReal.ofReal (kapR6 q) * (clsCap : ℝ≥0∞) +
            (potCap q : ℝ≥0∞) * (kfPre A L + recJPre A L))) :=
    (cntEP_le hperm hsign L hπ).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left le_self_add zero_le) le_rfl)
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hj zero_le))) zero_le))
  refine h1.trans ((add_le_add (add_le_add (mul_le_mul_of_nonneg_left h3 zero_le) le_rfl)
    le_rfl).trans_eq ?_)
  unfold encE0 encBeta encGamma encDelta
  ring

end prefixRef

/-! ## A cell read with post-state weights -/

section gramW

variable {n Y R M0 : Type} [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y]
  [Fintype R] [DecidableEq R] [Fintype M0] [DecidableEq M0]
  {e : n ≃ Option Y × R} {act : R → Prop} [DecidablePred act] {μ : R → M0}
  {τ : Option Y → R → R} {K : Option Y × M0 → Matrix n n ℂ} {idx : n → Option Y × M0}
  {φ : n → n}

/-- The weights after a Kraus family with outcome-dependent weights, as the trace of its weighted
Gram operator. -/
theorem sum_dW_conj_dep {ι : Type*} [Fintype ι] (K : ι → Matrix n n ℂ) (f : ι → n → ℝ)
    (σ : Matrix n n ℂ) :
    ∑ r, dW (f r) (MatrixMap.conj (K r) σ) =
      ((∑ r, (K r)ᴴ * diagonal (fun q ↦ ((f r q : ℝ) : ℂ)) * K r) * σ).trace.re := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [dW_eq_trace, MatrixMap.conj_apply]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

omit [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] [Fintype M0] [DecidableEq M0]
  [DecidablePred act] in
theorem gramW_term (w : Option Y → n → ℝ) (i : Option Y × M0) (t s : n) :
    ((K i)ᴴ * diagonal (fun u ↦ ((w i.1 u : ℝ) : ℂ)) * K i) t s =
      ∑ u, star (K i u t) * ((w i.1 u : ℝ) : ℂ) * K i u s := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [mul_diagonal, conjTranspose_apply]

omit [DecidablePred act] in
/-- **The Gram operator of a cell read with post-state weights**, on an active column. -/
theorem gramW_apply (h : CellRead e act μ τ K) (w : Option Y → n → ℝ) {s : n}
    (hs : act (e s).2) (t : n) :
    (∑ i, (K i)ᴴ * diagonal (fun u ↦ ((w i.1 u : ℝ) : ℂ)) * K i) t s =
      if (e t).2 = (e s).2 then
        ((∑ o, cr (e t).1 o * (∑ a, cr a o ^ 2 * w o (e.symm (a, τ o (e s).2))) *
          cr o (e s).1 : ℝ) : ℂ)
      else 0 := by
  simp only [Matrix.sum_apply, gramW_term]
  split_ifs with hts
  · have ht : act (e t).2 := hts ▸ hs
    rw [Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    rw [Finset.sum_eq_single (μ (e s).2)]
    · rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm,
        Finset.sum_eq_single (τ o (e s).2)]
      · rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [h.entry _ _ _ _ ht, h.entry _ _ _ _ hs]
        simp only [Equiv.apply_symm_apply, hts, and_self, ↓reduceIte, Complex.star_def,
          Complex.conj_ofReal]
        push_cast
        rw [cr_comm o (e t).1]
        ring
      · intro r _ hr
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        rw [h.entry _ _ _ _ hs]
        simp [hr]
      · simp
    · intro m0 _ hm
      refine Finset.sum_eq_zero fun u _ ↦ ?_
      rw [h.entry _ _ _ _ hs]
      simp [Ne.symm hm]
    · simp
  · refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun u _ ↦ ?_
    by_cases hKs : K i u s = 0
    · simp [hKs]
    obtain ⟨hμ, hτ⟩ := Quantum.Sponge.cellRead_ne_zero h hs hKs
    have hKt : K i u t = 0 := by
      by_contra hKt
      by_cases ht : act (e t).2
      · obtain ⟨hμ', hτ'⟩ := Quantum.Sponge.cellRead_ne_zero h ht hKt
        exact hts (h.inj i.1 _ _ (hμ'.trans hμ.symm) (hτ'.symm.trans hτ))
      · exact h.off i u t ht hKt (hτ ▸ h.act_τ _ _ hs)
    simp [hKt]

omit [Fintype R] [DecidablePred act] in
/-- The Gram operator of a cell read with post-state weights, on a hardwired column. -/
theorem gramW_off (h : CellRead e act μ τ K) (hc : ClsOff e act K idx φ)
    (w : Option Y → n → ℝ) {s : n} (hs : ¬ act (e s).2) (t : n) :
    (∑ i, (K i)ᴴ * diagonal (fun u ↦ ((w i.1 u : ℝ) : ℂ)) * K i) t s =
      if t = s then ((w (idx s).1 (φ s) : ℝ) : ℂ) else 0 := by
  simp only [Matrix.sum_apply, gramW_term]
  rw [Finset.sum_eq_single (idx s)]
  · rw [Finset.sum_eq_single (φ s)]
    · have hφ : ¬ act (e (φ s)).2 := h.off (idx s) (φ s) s hs (by rw [hc.entry _ _ _ hs]; simp)
      rw [hc.entry _ _ _ hs, ite_eq_left ⟨rfl, rfl⟩, mul_one]
      by_cases ht : act (e t).2
      · have h0 : K (idx s) (φ s) t = 0 := by
          by_contra h0
          exact hφ ((Quantum.Sponge.cellRead_ne_zero h ht h0).2 ▸ h.act_τ _ _ ht)
        rw [h0, star_zero, zero_mul, ite_eq_right]
        rintro rfl
        exact hs ht
      · rw [hc.entry _ _ _ ht]
        by_cases hts : t = s
        · subst hts
          simp
        · rw [ite_eq_right, ite_eq_right hts]
          · simp
          · rintro ⟨h1, h2⟩
            exact hts (hc.inj t s ht hs h1.symm h2.symm)
    · intro u _ hu
      rw [hc.entry _ _ _ hs, ite_eq_right fun h' ↦ hu h'.2, mul_zero]
    · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    rw [hc.entry _ _ _ hs, ite_eq_right fun h' ↦ hi h'.1, mul_zero]
  · simp

omit [Fintype n] [DecidableEq n] in
/-- The compression is an involution, entrywise. -/
theorem sum_cr_mul_cr [Nonempty Y] (a a' : Option Y) :
    ∑ o, ((cr o a' * cr a o : ℝ) : ℂ) = if a = a' then 1 else 0 := by
  have h := congrFun (congrFun (Quantum.cellCompress_mul_self (Y := Y)) a) a'
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [cellCompress_eq_cr] at h
  rw [← h]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  push_cast
  ring

/-- **A cell read with post-state weights**: for a state with no decompressed `⊥` at the cell, if
every recorded outcome's post-state weight, through the compression's column, is at most `ε` and
the hardwired columns' classical moves weigh nothing, the weights after the read are at most `ε`
times the trace. -/
theorem re_trace_gramW_le [Nonempty Y] (h : CellRead e act μ τ K) (hc : ClsOff e act K idx φ)
    (w : Option Y → n → ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ r, act r → ∀ y, ∑ a, cr a (some y) ^ 2 * w (some y) (e.symm (a, τ (some y) r)) ≤ ε)
    (hoff : ∀ s, ¬ act (e s).2 → w (idx s).1 (φ s) = 0)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (hnb : CellNoBot e act σ) :
    ((∑ i, (K i)ᴴ * diagonal (fun u ↦ ((w i.1 u : ℝ) : ℂ)) * K i) * σ).trace.re ≤
      ε * ∑ s, (σ s s).re := by
  obtain ⟨G, hG⟩ : ∃ G : Matrix n n ℂ,
      G = ∑ i, (K i)ᴴ * diagonal (fun u ↦ ((w i.1 u : ℝ) : ℂ)) * K i := ⟨_, rfl⟩
  rw [← hG]
  have hGa : ∀ s, act (e s).2 → ∀ t, G t s = if (e t).2 = (e s).2 then
      ((∑ o, cr (e t).1 o * (∑ a, cr a o ^ 2 * w o (e.symm (a, τ o (e s).2))) *
        cr o (e s).1 : ℝ) : ℂ) else 0 :=
    fun s hs t ↦ by rw [hG]; exact gramW_apply h w hs t
  have hGo : ∀ s, ¬ act (e s).2 → ∀ t,
      G t s = if t = s then ((w (idx s).1 (φ s) : ℝ) : ℂ) else 0 :=
    fun s hs t ↦ by rw [hG]; exact gramW_off h hc w hs t
  have htr : (G * σ).trace = ∑ s, ∑ t, G t s * σ s t := by
    rw [Matrix.trace]
    simp only [diag_apply, Matrix.mul_apply]
    exact Finset.sum_comm
  have hsplit : ∀ f : n → ℝ, ∑ s, f s = ∑ r, ∑ a, f (e.symm (a, r)) := fun f ↦ by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rw [htr, Complex.re_sum, hsplit, hsplit, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  by_cases hr : act r
  · -- an active rest
    obtain ⟨S, hS⟩ : ∃ S : Matrix (Option Y) (Option Y) ℂ,
        ∀ a' a, σ (e.symm (a', r)) (e.symm (a, r)) = S a' a := ⟨fun a' a ↦ _, fun _ _ ↦ rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : Option Y → ℝ,
        ∀ o, ∑ b, cr b o ^ 2 * w o (e.symm (b, τ o r)) = g o := ⟨_, fun _ ↦ rfl⟩
    have hrow : ∀ a, ∑ y, S (some y) a = 0 := fun a ↦ by
      simp only [← hS]
      exact hnb r hr _
    have hF : ∀ a', ∑ t, G t (e.symm (a', r)) * σ (e.symm (a', r)) t =
        ∑ a, ((∑ o, cr a o * g o * cr o a' : ℝ) : ℂ) * S a' a := fun a' ↦ by
      have hs : act (e (e.symm (a', r))).2 := by rw [Equiv.apply_symm_apply]; exact hr
      rw [sum_rest_eq (e := e) r fun t ht ↦ by
        rw [hGa _ hs, Equiv.apply_symm_apply, ite_eq_right ht, zero_mul]]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [hGa _ hs]
      simp only [Equiv.apply_symm_apply, ↓reduceIte, hg, hS]
    have hVc : ∑ a', ∑ a, ((∑ o, cr a o * g o * cr o a' : ℝ) : ℂ) * S a' a =
        ∑ o, (g o : ℂ) * ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a := by
      simp only [Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a' _ ↦ ?_
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun o _ ↦ ?_
      push_cast
      ring
    have hVsum : ∑ o, ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a = ∑ a, S a a := by
      calc ∑ o, ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a
          = ∑ a', ∑ a, ∑ o, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun a' _ ↦ Finset.sum_comm
        _ = ∑ a', ∑ a, (if a = a' then 1 else 0) * S a' a := by
            refine Finset.sum_congr rfl fun a' _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
            rw [← Finset.sum_mul, sum_cr_mul_cr]
        _ = ∑ a', S a' a' := by
            refine Finset.sum_congr rfl fun a' _ ↦ ?_
            simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
              ↓reduceIte]
    have hVnn : ∀ o, 0 ≤ (∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a).re := fun o ↦ by
      have hSm := (hσ.submatrix fun a : Option Y ↦ e.symm (a, r)).dotProduct_mulVec_nonneg
        (fun a ↦ ((cr a o : ℝ) : ℂ))
      have key : star (fun a ↦ ((cr a o : ℝ) : ℂ)) ⬝ᵥ
          ((σ.submatrix (fun a : Option Y ↦ e.symm (a, r)) fun a ↦ e.symm (a, r)) *ᵥ
            fun a ↦ ((cr a o : ℝ) : ℂ)) =
          ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a := by
        simp only [dotProduct, mulVec, submatrix_apply, Pi.star_apply, Complex.star_def,
          Complex.conj_ofReal, hS, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
        rw [cr_comm o a']
        push_cast
        ring
      rw [key] at hSm
      exact (Complex.nonneg_iff.1 hSm).1
    simp only [hF]
    rw [← Complex.re_sum, hVc, Complex.re_sum]
    simp only [Complex.re_ofReal_mul]
    rw [Fintype.sum_option, cellV_none hrow, Complex.zero_re, mul_zero, zero_add]
    have hRHS : ∑ a, (σ (e.symm (a, r)) (e.symm (a, r))).re =
        ∑ y : Y, (∑ a', ∑ a, ((cr (some y) a' * cr a (some y) : ℝ) : ℂ) * S a' a).re := by
      have h1 := congrArg Complex.re hVsum
      rw [Complex.re_sum, Complex.re_sum, Fintype.sum_option, cellV_none hrow, Complex.zero_re,
        zero_add] at h1
      rw [h1]
      exact Finset.sum_congr rfl fun a _ ↦ by rw [hS]
    rw [hRHS, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_right ?_ (hVnn _)
    rw [← hg]
    exact hε r hr y
  · -- a hardwired rest
    have h0 : ∀ a, (∑ t, G t (e.symm (a, r)) * σ (e.symm (a, r)) t).re = 0 := fun a ↦ by
      have hs : ¬ act (e (e.symm (a, r))).2 := by rw [Equiv.apply_symm_apply]; exact hr
      rw [Finset.sum_eq_single (e.symm (a, r))]
      · rw [hGo _ hs, ite_eq_left rfl, hoff _ hs, Complex.ofReal_zero, zero_mul, Complex.zero_re]
      · intro t _ ht
        rw [hGo _ hs, ite_eq_right ht, zero_mul]
      · simp
    rw [Finset.sum_congr rfl fun a _ ↦ h0 a, Finset.sum_const_zero]
    exact mul_nonneg hε0 (Finset.sum_nonneg fun a _ ↦
      (Complex.nonneg_iff.1 hσ.diag_nonneg).1)

end gramW

/-! ## The leaks of a trial's `k` and `k'` reads -/

section leak

variable {M : Type} [Fintype M] [DecidableEq M]

/-- The union's cell `x` of `k` does not hold `a`. -/
def KMiss (x : X) (a : Z) (s : HwReg X Z M) : Prop := (union s.2.1 s.1).k x ≠ some a

/-- The union's cell `y` of `k'` does not hold `c`. -/
def K'Miss (y : X) (c : Z) (s : HwReg X Z M) : Prop := (union s.2.1 s.1).k' y ≠ some c

/-- `KMiss`, decided classically. -/
noncomputable instance kMissDec (x : X) (a : Z) : DecidablePred (KMiss (M := M) x a) :=
  Classical.decPred _

/-- `K'Miss`, decided classically. -/
noncomputable instance k'MissDec (y : X) (c : Z) : DecidablePred (K'Miss (M := M) y c) :=
  Classical.decPred _

/-- The recorded outcomes leave the cell elsewhere with weight `1 - (1 - 1/N)² ≤ 2/N`. -/
theorem sum_cr_sq_ne_le {Y : Type} [Fintype Y] [DecidableEq Y] [Nonempty Y] (y : Y) :
    ∑ a, cr a (some y) ^ 2 * (if a = some y then (0 : ℝ) else 1) ≤ 2 / Fintype.card Y := by
  have hN : (1 : ℝ) ≤ Fintype.card Y := Nat.one_le_cast.mpr Fintype.card_pos
  have h : ∀ a : Option Y, cr a (some y) ^ 2 * (if a = some y then (0 : ℝ) else 1) =
      cr a (some y) ^ 2 - if a = some y then cr a (some y) ^ 2 else 0 := fun a ↦ by
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun a _ ↦ h a, Finset.sum_sub_distrib, sum_cr_sq,
    Finset.sum_ite_eq' Finset.univ (some y), ite_eq_left (Finset.mem_univ _)]
  simp only [cr, ↓reduceIte]
  have hinv : (0 : ℝ) ≤ (Fintype.card Y : ℝ)⁻¹ := inv_nonneg.2 (by linarith)
  have h2 : 2 / (Fintype.card Y : ℝ) = 2 * (Fintype.card Y : ℝ)⁻¹ := div_eq_mul_inv _ _
  nlinarith

/-- **The leak of a `k` read**: after the read of the cell `x` of `k` with outcome `a`, the union
misses `a` at `x` with weight at most `2/|Z|` per unit of trace, on a state with no decompressed
`⊥` at the cell (the hardwired cells read their value classically). -/
theorem readK_leak_le (x : X) (u : M → Option Z → M)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : ReadNoBot (.readK x u) σ) :
    ∑ r : Option Z × M, dW (fun q ↦ if KMiss x (r.1.getD 0) q.2 then (1 : ℝ) else 0)
        (MatrixMap.conj (hwReadKraus (.readK x u) r) σ) ≤
      2 / Fintype.card Z * ∑ q, (σ q q).re := by
  rw [sum_dW_conj_dep]
  refine re_trace_gramW_le (cellRead_readK x u) (clsOff_readK x u)
    (fun o q ↦ if KMiss x (o.getD 0) q.2 then (1 : ℝ) else 0) (by positivity) ?_ ?_ hσ hnb
  · intro r hr y
    have hr' : r.2.2.2.1.2.1 x = none := hr
    have hk : ∀ a : Option Z, (if KMiss x ((some y).getD 0)
        ((splitK x).symm (a, tauK x u (some y) r)).2 then (1 : ℝ) else 0) =
        if a = some y then 0 else 1 := fun a ↦ by
      have hu : (union ((splitK x).symm (a, tauK x u (some y) r)).2.2.1
          ((splitK x).symm (a, tauK x u (some y) r)).2.1).k x = a := by
        simp [union_k, splitK, tauK, hr']
      have hiff : KMiss x ((some y).getD 0) ((splitK x).symm (a, tauK x u (some y) r)).2 ↔
          ¬ a = some y := by
        simp only [KMiss, hu, Option.getD_some, ne_eq]
      rw [if_congr hiff rfl rfl, ite_not]
    rw [Finset.sum_congr rfl fun a _ ↦ by rw [hk a]]
    exact sum_cr_sq_ne_le y
  · intro s hs
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (show s.2.2.1.2.1 x ≠ none from hs)
    refine ite_eq_right fun h ↦ h ?_
    show (s.2.2.1.2.1 x).or (s.2.1.2.1 x) = some ((s.2.2.1.2.1 x).getD 0)
    rw [hv]
    rfl

/-- **The leak of a `k'` read**, as `readK_leak_le`. -/
theorem readK'_leak_le (y : X) (u : M → Option Z → M)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : ReadNoBot (.readK' y u) σ) :
    ∑ r : Option Z × M, dW (fun q ↦ if K'Miss y (r.1.getD 0) q.2 then (1 : ℝ) else 0)
        (MatrixMap.conj (hwReadKraus (.readK' y u) r) σ) ≤
      2 / Fintype.card Z * ∑ q, (σ q q).re := by
  rw [sum_dW_conj_dep]
  refine re_trace_gramW_le (cellRead_readK' y u) (clsOff_readK' y u)
    (fun o q ↦ if K'Miss y (o.getD 0) q.2 then (1 : ℝ) else 0) (by positivity) ?_ ?_ hσ hnb
  · intro r hr c
    have hr' : r.2.2.2.1.2.2 y = none := hr
    have hk : ∀ a : Option Z, (if K'Miss y ((some c).getD 0)
        ((splitK' y).symm (a, tauK y u (some c) r)).2 then (1 : ℝ) else 0) =
        if a = some c then 0 else 1 := fun a ↦ by
      have hu : (union ((splitK' y).symm (a, tauK y u (some c) r)).2.2.1
          ((splitK' y).symm (a, tauK y u (some c) r)).2.1).k' y = a := by
        simp [union_k', splitK', tauK, hr']
      have hiff : K'Miss y ((some c).getD 0) ((splitK' y).symm (a, tauK y u (some c) r)).2 ↔
          ¬ a = some c := by
        simp only [K'Miss, hu, Option.getD_some, ne_eq]
      rw [if_congr hiff rfl rfl, ite_not]
    rw [Finset.sum_congr rfl fun a _ ↦ by rw [hk a]]
    exact sum_cr_sq_ne_le c
  · intro s hs
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (show s.2.2.1.2.2 y ≠ none from hs)
    refine ite_eq_right fun h ↦ h ?_
    show (s.2.2.1.2.2 y).or (s.2.1.2.2 y) = some ((s.2.2.1.2.2 y).getD 0)
    rw [hv]
    rfl

omit [Fintype M] in
/-- A nonzero entry of a read of `k'` keeps the databases of `h` and `k` and the hardwired
cells. -/
theorem readKrausK'_ne_zero_k (y : X) (u : M → Option Z → M) (r : Option Z × M)
    {s' s : HwReg X Z M} (h : readKrausK' y u r s' s ≠ 0) :
    s'.1.2.1 = s.1.2.1 ∧ s'.2.1 = s.2.1 := by
  rw [readKrausK', clsKraus_apply] at h
  split_ifs at h with hc
  · rw [kroneckerMap_apply, kroneckerMap_apply] at h
    have h2 := left_ne_zero_of_mul (right_ne_zero_of_mul h)
    refine ⟨?_, by rw [hc.2]⟩
    by_contra hne
    exact h2 (Matrix.one_apply_ne hne)
  · exact absurd rfl h

/-- **A `k'` read keeps the `k` misses**: the weight of `KMiss x a` after the read is the weight
before. -/
theorem readK'_keep_kMiss (y : X) (u : M → Option Z → M) (x : X) (a : Z)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    ∑ r : Option Z × M, dW (fun q ↦ if KMiss x a q.2 then (1 : ℝ) else 0)
        (MatrixMap.conj (hwReadKraus (.readK' y u) r) σ) =
      dW (fun q ↦ if KMiss x a q.2 then (1 : ℝ) else 0) σ := by
  refine sum_dW_conj_of_keep (fun r : Option Z × M ↦ hwReadKraus (.readK' y u) r) _
    (fun r q q' h ↦ ?_) (sum_readKrausK' y u) σ
  obtain ⟨-, h'⟩ := one_kronecker_ne_zero (a := q.1) (a' := q'.1) (b := q.2) (b' := q'.2) h
  obtain ⟨h1, h2⟩ := readKrausK'_ne_zero_k y u r h'
  have hk : (union q'.2.2.1 q'.2.1).k = (union q.2.2.1 q.2.1).k := by
    rw [union_k, union_k, h1, h2]
  exact if_congr (by simp only [KMiss, hk]) rfl rfl

end leak

/-! ## The refined modes of the randomizer trials

TrialSource's trial modes, keeping the block `x`, the `k` outcome `a` and the `k'` outcome `c`,
with the `h` read's memory update named: `w l e x (π (x, a)).1` for the key `(l, e)` of the
block's message slot. -/

section hmodes

open HashSig LeanXmss Common Common.SufCma LeanXmss.RandomPermutationModel

/-- The refined modes of a randomizer trial's reads: free; after the `k`-read at the block `x`
with outcome `a`; after the `k'`-read, with outcome `c`. -/
inductive HMode
  | free
  | afK (x : X) (a : Z)
  | afK' (x : X) (a c : Z)

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter)

/-- The reads a refined mode allows: a free read is a `k`-read at a trial block keeping the
memory; after the `k`-read at `x` with outcome `a` the `k'`-read at `π (x, a)` keeping the memory;
then the `h`-read at `π (x, a) + c` updating the memory by `w l e x (π (x, a)).1` for the key of
the block's message slot. -/
def rdOkH {M' : Type} (w : Layer → KeyIndex → X → X → M' → Option X → M') :
    HMode → HwRead X Z M' → Prop
  | .free, .readK x u => TrialBlock P x ∧ u = fun m _ ↦ m
  | .afK x a, .readK' y u => y = (π (x, a)).1 ∧ u = fun m _ ↦ m
  | .afK' x a c, .readH z u => z = (π (x, a)).2 + c ∧ TrialBlock P x ∧
      ∃ l e, slotOf P (blocks (blockInput x)) = some (.msg l e) ∧ u = w l e x (π (x, a)).1
  | _, _ => False

/-- The refined mode after a read. -/
def rdNxH {M' : Type} : HMode → (c : HwRead X Z M') → c.Result → HMode
  | .free, .readK x _, r => .afK x (r.1.getD 0)
  | .afK x a, .readK' _ _, r => .afK' x a (r.1.getD 0)
  | _, _, _ => .free

/-- The calls the refined modes allow, on runtime 1's ports. -/
def okRH {M : Type} (w : Layer → KeyIndex → X → X → M → Option X → M) :
    HMode → (hwReadSpec X Z M).Port → Prop
  | μ, .inl _ => μ = .free
  | μ, .inr c => rdOkH π P w μ c

/-- The refined mode after a call of runtime 1. -/
def nxRH {M : Type} : HMode → (i : (hwReadSpec X Z M).Port) → (hwReadSpec X Z M).Result i →
    HMode
  | _, .inl _, _ => .free
  | μ, .inr c, r => rdNxH μ c r

/-- The calls the refined modes allow, on the template's ports. -/
def okTH {M : Type}
    (w : Layer → KeyIndex → X → X → Finset HPos × M → Option X → Finset HPos × M) :
    HMode → (XSpec M).Port → Prop
  | μ, .inl (.inl (.inr c)) => rdOkH π P w μ c.1
  | μ, _ => μ = .free

/-- The refined mode after a call of the template. -/
def nxTH {M : Type} : HMode → (i : (XSpec M).Port) → (XSpec M).Result i → HMode
  | μ, .inl (.inl (.inr c)), r => rdNxH μ c.1 r
  | _, _, _ => .free

/-- The calls the refined modes allow, on runtime 2's ports with record ports. -/
def okZH {M : Type}
    (w : Layer → KeyIndex → X → X → Finset HPos × M → Option X → Finset HPos × M) :
    HMode → (recHwSpec X Z HPos M).Port → Prop
  | μ, .inl (.inl (.inr c)) => rdOkH π P w μ c
  | μ, _ => μ = .free

/-- The refined mode after a call of runtime 2 with record ports. -/
def nxZH {M : Type} : HMode → (i : (recHwSpec X Z HPos M).Port) →
    (recHwSpec X Z HPos M).Result i → HMode
  | μ, .inl (.inl (.inr c)), r => rdNxH μ c r
  | _, _, _ => .free

/-- The memory update of a trial read on the memory with the label. -/
def liftW {M : Type} (upd : TrialUpd M) :
    Layer → KeyIndex → X → X → Finset HPos × M → Option X → Finset HPos × M :=
  fun l e x xi m o ↦ (m.1, upd l e x xi m.2 o)

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

variable {π P}

omit [Fintype M] [DecidableEq M] in
theorem modedEH_readCall {μ : HMode} {c : HwRead X Z M} (h : rdOkH π P upd μ c) (B : QReg) :
    ModedE (L := LocalSig.instruments) (okRH π P upd) nxRH (fun p ↦ rdNxH μ c p.2.2) μ
      (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

variable (π P) in
/-- A stateful program of runtime 1 moded from every state. -/
def SModH {B : QReg} {σ α : Type} (μ : HMode) (fin : α → HMode)
    (x : StateT σ (QComp (hwReadSpec X Z M) B B) α) : Prop :=
  ∀ s, ModedE (L := LocalSig.instruments) (okRH π P upd) nxRH (fun p ↦ fin p.2.2.1) μ
    (x.run s)

section smod

variable {B : QReg} {σ α β : Type}

omit [Fintype M] [DecidableEq M] in
theorem sModH_bind {x : StateT σ (QComp (hwReadSpec X Z M) B B) α}
    {k : α → StateT σ (QComp (hwReadSpec X Z M) B B) β} {μ : HMode} {f : α → HMode}
    {g : β → HMode} (hx : SModH π P upd μ f x) (hk : ∀ a, SModH π P upd (f a) g (k a)) :
    SModH π P upd μ g (x >>= k) := by
  intro s
  rw [StateT.run_bind]
  exact modedE₂_bind (fin := fun q : α × σ ↦ f q.1) (fin' := fun q : β × σ ↦ g q.1) _ _ (hx s)
    fun p ↦ hk p.1 p.2

omit [Fintype M] [DecidableEq M] in
theorem sModH_pure (a : α) (f : α → HMode) :
    SModH π P upd (f a) f (pure a : StateT σ (QComp (hwReadSpec X Z M) B B) α) := by
  intro s
  rw [StateT.run_pure]
  rfl

omit [Fintype M] [DecidableEq M] in
theorem modedEH_map {spec : QuantumOracleSpec.{0, 0}} {ok : HMode → spec.Port → Prop}
    {nx : HMode → (i : spec.Port) → spec.Result i → HMode} {A B' : QReg} {γ δ : Type}
    {x : QComp spec A B' γ} (g : γ → δ) {f : δ → HMode} {μ : HMode}
    (hx : ModedE (L := LocalSig.instruments) ok nx (fun p ↦ f (g p.2.2)) μ x) :
    ModedE (L := LocalSig.instruments) ok nx (fun p ↦ f p.2.2) μ (x.map g) := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact modedE₂_bind (fin := fun a ↦ f (g a)) _ _ hx fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem sModH_map {x : StateT σ (QComp (hwReadSpec X Z M) B B) α} (g : α → β) {μ : HMode}
    {f : β → HMode} (hx : SModH π P upd μ (fun a ↦ f (g a)) x) :
    SModH π P upd μ f (g <$> x) := by
  intro s
  rw [StateT.run_map]
  exact modedEH_map (f := fun q : β × σ ↦ f q.1) (fun p : α × σ ↦ (g p.1, p.2)) (hx s)

omit [Fintype M] [DecidableEq M] in
theorem sModH_rdK {x : X} (hx : TrialBlock P x) :
    SModH π P upd .free (fun a ↦ .afK x a) (rdK (M := M) B x) :=
  fun s ↦ modedE₂_bind (fin := fun r : Option Z × M ↦ HMode.afK x (r.1.getD 0))
    (fin' := fun q : Z × List (SpongeRead X Z) ↦ HMode.afK x q.1) (readCall (.readK x keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k x (r.1.getD 0)]))
    (modedEH_readCall (π := π) upd (μ := .free) (c := .readK x keepMem) ⟨hx, rfl⟩ B) fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem sModH_rdK' {x : X} {a : Z} {y : X} (hy : y = (π (x, a)).1) :
    SModH π P upd (.afK x a) (fun c ↦ .afK' x a c) (rdK' (M := M) B y) :=
  fun s ↦ modedE₂_bind (fin := fun r : Option Z × M ↦ HMode.afK' x a (r.1.getD 0))
    (fin' := fun q : Z × List (SpongeRead X Z) ↦ HMode.afK' x a q.1)
    (readCall (.readK' y keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k' y (r.1.getD 0)]))
    (modedEH_readCall (π := π) upd (μ := .afK x a) (c := .readK' y keepMem) ⟨hy, rfl⟩ B)
    fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem sModH_rdHU {x : X} {a c : Z} {z : Z} (hz : z = (π (x, a)).2 + c) (hT : TrialBlock P x)
    {l : Layer} {e : KeyIndex} (hslot : slotOf P (blocks (blockInput x)) = some (.msg l e))
    {u : M → Option X → M} (hu : u = upd l e x (π (x, a)).1) :
    SModH π P upd (.afK' x a c) (fun _ ↦ .free) (rdHU M B z u) :=
  fun s ↦ modedE₂_bind (fin := fun _ : Option X × M ↦ HMode.free)
    (fin' := fun _ : X × List (SpongeRead X Z) ↦ HMode.free) (readCall (.readH z u) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.h z (r.1.getD 0)]))
    (modedEH_readCall (π := π) upd (μ := .afK' x a c) (c := .readH z u)
      ⟨hz, hT, l, e, hslot, hu⟩ B) fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
/-- **A trial's round of reads**, from the zero state, at a trial block of the message slot of
key `(l, e)`. -/
theorem sModH_rdRoundU (l : Layer) (e : KeyIndex) (b : X) (hb : TrialBlock P b)
    (hslot : slotOf P (blocks (blockInput b)) = some (.msg l e)) :
    SModH π P upd .free (fun _ ↦ .free) (rdRoundU M (upd l e) π B (0, 0) b) := by
  have hb' : TrialBlock P ((0 : X × Z).1 + b) := by
    rw [show (0 : X × Z).1 = 0 from rfl, zero_add]
    exact hb
  unfold rdRoundU
  refine sModH_bind upd (sModH_rdK upd hb') fun a ↦ ?_
  refine sModH_bind upd (sModH_rdK' (a := a) upd (by simp only [zero_add]))
    fun c ↦ ?_
  refine sModH_bind upd (sModH_rdHU upd (a := a) (c := c)
    (by simp only [Prod.fst_zero, zero_add]) hb' (l := l) (e := e)
    (by simp only [Prod.fst_zero, zero_add]; exact hslot)
    (by simp only [Prod.fst_zero, zero_add])) fun w ↦ ?_
  exact sModH_pure upd (f := fun _ ↦ HMode.free) _

omit [Fintype M] [DecidableEq M] in
/-- **A randomizer trial's hash** of a one-block input at the message slot of key `(l, e)`. -/
theorem modedEH_hashTrial (l : Layer) (e : KeyIndex) (input : HashInput) (b : X)
    (hb : blocks input = [b]) (hT : TrialBlock P b)
    (hslot : slotOf P (blocks (blockInput b)) = some (.msg l e)) :
    ModedE (L := LocalSig.instruments) (okRH π P upd) nxRH (fun _ ↦ .free) .free
      (hashTrial M (upd l e) π B input) := by
  have hfold : SModH π P upd (B := B) .free (fun _ ↦ .free)
      ((blocks input).foldlM (rdRoundU M (upd l e) π B) (0, 0)) := by
    rw [hb]
    exact sModH_bind upd (sModH_rdRoundU upd l e b hT hslot)
      fun s' ↦ sModH_pure upd (f := fun _ ↦ HMode.free) s'
  exact modedEH_map (f := fun _ ↦ HMode.free) Prod.fst
    (sModH_map upd (f := fun _ ↦ HMode.free) (out256 : X → HashOutput)
      (sModH_map upd (f := fun _ ↦ HMode.free) (fun s : X × Z ↦ s.1) hfold) [])

omit [Fintype M] [DecidableEq M] in
/-- **The randomizer search** of a label's message (of `16` to `32` bytes) is moded. -/
theorem modedEH_grindR (pub : Pub) (l : Layer) (e : KeyIndex) {message : HashInput}
    (hm : message.length ≤ 32) (hm16 : 16 ≤ message.length) (base : Randomizer) :
    ∀ n trial, ModedE (L := LocalSig.instruments) (okRH pub.perm pub.param upd) nxRH
      (fun _ ↦ .free) .free (grindR M upd pub B l e message base n trial)
  | 0, _ => rfl
  | n + 1, trial => by
    rw [grindR]
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (length_blocks_trial pub.param
      (hashDomainFields (.message l e)) hm base trial)
    have hlen : (thInput pub.param (hashDomainFields (.message l e))
        (message ++ littleEndianBytes 16 (base + BitVec.ofNat digestBits trial))).length < 136 := by
      have h1 := length_blocks (thInput pub.param (hashDomainFields (.message l e))
        (message ++ littleEndianBytes 16 (base + BitVec.ofNat digestBits trial)))
      rw [hb, List.length_singleton] at h1
      omega
    have hslot : slotOf pub.param (blocks (blockInput b)) = some (.msg l e) := by
      rw [blocks_blockInput hb, ← hb, ← absorbTail_blocks_of_lt pub.perm hlen]
      exact slotOf_msg pub.perm pub.param l e message hm16 _
    refine modedE₂_bind (fin := fun _ ↦ HMode.free) (fin' := fun _ ↦ HMode.free) _ _
      (modedEH_hashTrial upd l e _ b hb ⟨l, e, message, _, hm, hb⟩ hslot) fun out ↦ ?_
    show ModedE _ _ _ _ (match Codeword.decode (truncateHash out) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindR M upd pub B l e message base n (trial + 1))
    split
    · rfl
    · exact modedEH_grindR pub l e hm hm16 base n (trial + 1)

end smod

omit [Fintype M] [DecidableEq M] in
theorem rdOkH_liftRead {μ : HMode} {c : HwRead X Z M} (h : rdOkH π P upd μ c) :
    rdOkH π P (liftW upd) μ (liftRead (S := HPos) c) := by
  rcases μ with _ | ⟨x, a⟩ | ⟨x, a, c'⟩ <;> rcases c with ⟨z', u⟩ | ⟨x', u⟩ | ⟨y, u⟩
  all_goals try exact h
  · exact ⟨h.1, by rw [h.2]⟩
  · exact ⟨h.1, by rw [h.2]⟩
  · obtain ⟨hz, hT, l, e, hslot, hu⟩ := h
    exact ⟨hz, hT, l, e, hslot, by rw [hu]; rfl⟩

omit [Fintype M] [DecidableEq M] in
/-- **Lifting runtime 1's refined moded programs to templates.** -/
theorem modedEH_readLift {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → HMode}
    (y : QuantumComp LocalSig.instruments (hwReadSpec X Z M) Ω A) {μ : HMode}
    (hy : ModedE (okRH π P upd) nxRH fin μ y) :
    ModedE (okTH π P (liftW upd)) nxTH fin μ (readLift goodAll y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedE _ _ _ μ (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨rdOkH_liftRead upd hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with _ | ⟨x', a⟩ | ⟨x', a, c'⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

omit [Fintype M] [DecidableEq M] in
/-- A sponge program of runtime 1 is moded, free throughout. -/
theorem modedEH_liftOrdinary {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (spongeSpec X Z) Ω A) :
    ModedE (okRH π P upd) nxRH (fun _ ↦ .free) .free
      (y.liftOrdinary (t := hwReadCmdSpec X Z M)) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => rfl
  | liftBind _ c next ih =>
    show ModedE _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _⟩
    · exact ⟨rfl, fun b ↦ ih _⟩

omit [Fintype M] [DecidableEq M] in
/-- **Realizing keeps the refined modes.** -/
theorem modedEH_realizeT (v : HPos → Digest) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → HMode} (y : QuantumComp L (XSpec M) Ω A) {μ : HMode}
    (hy : ModedE (okTH π P (liftW upd)) nxTH fin μ y) :
    ModedE (okZH π P (liftW upd)) nxZH fin μ (realizeT v y) := by
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

variable (π P) in
/-- A template moded from the free refined mode back to it. -/
abbrev TFreeH {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments (XSpec M) Ω A) :
    Prop :=
  ModedE (okTH π P (liftW upd)) nxTH (fun _ ↦ .free) .free y

omit [Fintype M] [DecidableEq M] in
theorem tFreeH_bind {A B B' : QReg} {α β : Type} (x : QComp (XSpec M) A B α)
    (g : α → QComp (XSpec M) B B' β) (hx : TFreeH π P upd x) (hg : ∀ a, TFreeH π P upd (g a)) :
    TFreeH π P upd (x.bind g) :=
  modedE₂_bind (fin := fun _ ↦ HMode.free) (fin' := fun _ ↦ HMode.free) x g hx hg

omit [Fintype M] [DecidableEq M] in
theorem tFreeH_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    TFreeH π P upd (QComp.act (spec := XSpec M) p) :=
  ⟨trivial, fun _ ↦ rfl⟩

omit [Fintype M] [DecidableEq M] in
theorem tFreeH_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B B' α)
    (hk : ∀ r, TFreeH π P upd (k r)) : TFreeH π P upd (revealThen goodAll T k) :=
  ⟨rfl, fun b ↦ tFreeH_bind upd _ _ (tFreeH_act upd _) fun _ ↦ hk b.down⟩

omit [Fintype M] [DecidableEq M] in
theorem tFreeH_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec M) B B' α) (hk : TFreeH π P upd k) : TFreeH π P upd (progThen p hp k) :=
  ⟨rfl, fun _ ↦ tFreeH_bind upd _ _ (tFreeH_act upd _) fun _ ↦ hk⟩

omit [Fintype M] [DecidableEq M] in
theorem tFreeH_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    TFreeH π P upd (progPorts M B ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact tFreeH_progThen upd p trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem tFreeH_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    TFreeH π P upd (progSlots M pub B ss) := by
  induction ss with
  | nil => rfl
  | cons s ss ih => exact tFreeH_bind upd _ _ (tFreeH_progPorts upd B _) fun _ ↦ ih

theorem RLabel.length_msg_ge (lab : RLabel) : 16 ≤ lab.msg.length := by
  rcases lab with ⟨_, m⟩ | ⟨_, d⟩
  · exact (XmssCost.littleEndianBytes_length _ _).ge.trans' (by norm_num)
  · exact (XmssCost.littleEndianBytes_length _ _).ge

omit [Fintype M] [DecidableEq M] in
theorem tFreeH_signLayerT (pub : Pub) (B : QReg) (lab : RLabel) :
    TFreeH pub.perm pub.param upd (signLayerT M upd pub B lab) := by
  refine tFreeH_revealThen upd _ _ fun r₀ ↦ tFreeH_bind upd _ _
    (modedEH_readLift upd _ (modedEH_grindR upd pub lab.layer lab.key (RLabel.length_msg_le lab)
      (RLabel.length_msg_ge lab) _ _ _)) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · rfl
  · exact tFreeH_revealThen upd _ _ fun r ↦ tFreeH_bind upd _ _ (tFreeH_progSlots upd pub B _)
      fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem tFreeH_signT (pub : Pub) (B : QReg) (r : SigningRequest) :
    TFreeH pub.perm pub.param upd (signT M upd pub B r) := by
  refine tFreeH_bind upd _ _ (tFreeH_signLayerT upd pub B _) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · rfl
  · refine tFreeH_bind upd _ _ (tFreeH_signLayerT upd pub B _) fun t ↦ ?_
    rcases t with _ | ⟨top, _⟩ <;> rfl

omit [Fintype M] [DecidableEq M] in
theorem tFreeH_challengeT (pub : Pub) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    ModedE (okTH pub.perm pub.param (liftW upd)) nxTH (fun _ ↦ .free) .free
      (challengeT M upd pub A c) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact modedEH_readLift upd _ (modedEH_liftOrdinary upd _)
  · exact modedEH_readLift upd _ (modedEH_liftOrdinary upd _)
  · exact modedE_bind _ _ (tFreeH_bind upd _ _ (tFreeH_act upd _) fun _ ↦ tFreeH_signT upd pub _ r)
      fun _ _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem modedEH_cast {spec : QuantumOracleSpec.{0, 0}} {ok : HMode → spec.Port → Prop}
    {nx : HMode → (i : spec.Port) → spec.Result i → HMode} {Ω : QReg → Type w}
    {fin : (Σ u, Ω u) → HMode} {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) (μ : HMode) :
    ModedE ok nx fin μ (e ▸ y) ↔ ModedE ok nx fin μ y := by
  subst e
  rfl

omit [Fintype M] [DecidableEq M] in
/-- Substituting refined moded trees that start and end free. -/
theorem modedEH_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (XSpec M)))
    (hσ : ∀ A c, ModedE (okTH π P (liftW upd)) nxTH (fun _ ↦ .free) .free (σ A c))
    {Ω : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ModedE (okTH π P (liftW upd)) nxTH (fun _ ↦ .free) .free (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact modedE_bind _ _ (hσ s c) fun u ans ↦ (modedEH_cast ans.2 _ _).mpr (ih ans.1)

omit [Fintype M] [DecidableEq M] in
/-- **The challenge prefix is moded by the refined trial modes.** -/
theorem tFreeH_prefixT (pub : Pub) (A : Adversary (X × Z)) :
    TFreeH pub.perm pub.param upd (prefixT M upd pub A) :=
  tFreeH_revealThen upd _ _ fun _ ↦ tFreeH_bind upd _ _
    (modedEH_substitute upd _ (tFreeH_challengeT upd pub) _) fun _ ↦ rfl

end trialPrefix

end hmodes

/-! ## The off-head mass of the trial reads -/

section offHead

open HashSig LeanXmss Common Common.SufCma LeanXmss.RandomPermutationModel

/-- `Selections.select`, pointwise. -/
theorem select_apply (m : Selections) (l : Layer) (e : KeyIndex) (x : X) (y : Digest)
    (l' : Layer) (e' : KeyIndex) :
    m.select l e x y l' e' = if l' = l ∧ e' = e then some (x, y) else m l' e' := by
  unfold Selections.select
  by_cases hl : l' = l
  · subst hl
    by_cases he : e' = e
    · subst he
      simp
    · simp [he]
  · simp [hl]

/-- A filter with a nonzero count has a member (over abstract types). -/
theorem exists_of_card_filter_ne_zero {α : Type*} [Fintype α] {p : α → Prop}
    {_ : DecidablePred p} (h : (Finset.univ.filter p).card ≠ 0) : ∃ a, p a := by
  obtain ⟨a, ha⟩ := Finset.card_ne_zero.1 h
  exact ⟨a, (Finset.mem_filter.1 ha).2⟩

/-- **A trial's update determines its key, its block and its rate's digest**, so `trialOf` picks
the program's trial up to the rate's untruncated bits. -/
theorem trialUpd_inj {t t' : TrialPt} (h : trialUpd t' = trialUpd t) :
    t'.l = t.l ∧ t'.e = t.e ∧ t'.x = t.x ∧ trunc128 t'.xi = trunc128 t.xi := by
  obtain ⟨v, hv⟩ : ∃ v : X, Codeword.Valid (trunc128 (t.xi + v)) := by
    have hρ : (0 : ℝ) < rhoCw := lt_of_lt_of_le (by positivity) inv_two_pow_21_le_rhoCw
    have h2 : (0 : ℝ) < ((Finset.univ.filter fun v : X ↦
        Codeword.Valid (trunc128 (t.xi + v))).card : ℝ) / Fintype.card X := by
      rw [card_codeword_div_card_X]
      exact hρ
    have h3 : ((Finset.univ.filter fun v : X ↦
        Codeword.Valid (trunc128 (t.xi + v))).card : ℝ) ≠ 0 := fun h0 ↦ by
      rw [h0, zero_div] at h2
      exact lt_irrefl _ h2
    exact exists_of_card_filter_ne_zero (by exact_mod_cast h3)
  have h1 : (trialUpd t' ((∅, m0) : Mem) (some v)).2 t.l t.e =
      (trialUpd t ((∅, m0) : Mem) (some v)).2 t.l t.e :=
    congrArg (fun m' : Mem ↦ m'.2 t.l t.e) (congrFun (congrFun h ((∅, m0) : Mem)) (some v))
  have hR : (trialUpd t ((∅, m0) : Mem) (some v)).2 t.l t.e =
      some (t.x, trunc128 (t.xi + v)) := by
    show cwUpd t.l t.e t.x t.xi m0 (some v) t.l t.e = _
    rw [cwUpd_some_of_none _ _ _ _ rfl]
    unfold cwSel
    rw [ite_eq_left hv, select_apply, ite_eq_left ⟨rfl, rfl⟩]
  have hL : (trialUpd t' ((∅, m0) : Mem) (some v)).2 t.l t.e =
      cwSel m0 t'.l t'.e t'.x t'.xi v t.l t.e := by
    show cwUpd t'.l t'.e t'.x t'.xi m0 (some v) t.l t.e = _
    rw [cwUpd_some_of_none _ _ _ _ rfl]
  rw [hR, hL] at h1
  unfold cwSel at h1
  split_ifs at h1 with hv'
  · rw [select_apply] at h1
    split_ifs at h1 with hle
    · obtain ⟨hx, hd⟩ := Prod.mk.inj (Option.some.inj h1)
      refine ⟨hle.1.symm, hle.2.symm, hx, ?_⟩
      have h2 := trunc128_add_congr hd (-v)
      rwa [add_neg_cancel_right, add_neg_cancel_right] at h2
    · simp [m0] at h1
  · simp [m0] at h1

/-- The potentials of the refined trial modes: after the `k`-read, the union misses its outcome;
after the `k'`-read, it misses the `k` or the `k'` outcome. -/
noncomputable def hpot (π : Equiv.Perm (X × Z)) :
    HMode → Unit → Matrix (HwReg X Z Mem) (HwReg X Z Mem) ℂ
  | .free, _ => 0
  | .afK x a, _ => setProj {s | KMiss x a s}
  | .afK' x a c, _ => setProj {s | KMiss x a s ∨ K'Miss (π (x, a)).1 c s}

/-- **The leak charge of a read port**: after a `k` or `k'` read, the weight of the states whose
union misses the read's outcome (`0` at the `h` reads). -/
noncomputable def leakW : (c : HwRead X Z Mem) →
    Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ → ℝ≥0∞
  | .readK x u, σ => ENNReal.ofReal (∑ r : Option Z × Mem,
      dW (fun q ↦ if KMiss x (r.1.getD 0) q.2 then (1 : ℝ) else 0)
        (MatrixMap.conj (hwReadKraus (.readK x u) r) σ))
  | .readK' y u, σ => ENNReal.ofReal (∑ r : Option Z × Mem,
      dW (fun q ↦ if K'Miss y (r.1.getD 0) q.2 then (1 : ℝ) else 0)
        (MatrixMap.conj (hwReadKraus (.readK' y u) r) σ))
  | .readH _ _, _ => 0

theorem sum_potential_hpot_free (π : Equiv.Perm (X × Z)) {A : Type} [Fintype A] [DecidableEq A]
    (σ : Matrix (A × HwReg X Z Mem) (A × HwReg X Z Mem) ℂ) :
    ∑ j, potential (hpot π .free j) σ = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ potential_zero σ

/-- A diagonal mass as a weighted diagonal. -/
theorem diagMass_eq_dW (S : Set (HwReg X Z Mem)) [DecidablePred (· ∈ S)]
    {τ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hτ : τ.PosSemidef) :
    diagMass {q : Unit × HwReg X Z Mem | q.2 ∈ S} τ =
      ENNReal.ofReal (dW (fun q ↦ if q.2 ∈ S then (1 : ℝ) else 0) τ) := by
  have hre : ∀ q, 0 ≤ (τ q q).re := fun q ↦ (Complex.nonneg_iff.1 hτ.diag_nonneg).1
  unfold diagMass dW
  rw [ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hre q)]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases h : q.2 ∈ S
  · rw [Set.indicator_of_mem (show q ∈ {q : Unit × HwReg X Z Mem | q.2 ∈ S} from h), ite_eq_left h,
      one_mul]
  · rw [Set.indicator_of_notMem (show q ∉ {q : Unit × HwReg X Z Mem | q.2 ∈ S} from h),
      ite_eq_right h, zero_mul, ENNReal.ofReal_zero]

theorem offHeadW_not_trial (L : HonestTable) {c : HwRead X Z Mem} (hc : ∀ z u, c ≠ .readH z u)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : offHeadW L c σ = 0 := by
  unfold offHeadW
  exact ite_eq_right fun ⟨_, h⟩ ↦ hc _ _ h

/-- **A trial `h` read in the refined mode `afK' x a c` is off its head only where the union
misses the `k` or the `k'` outcome.** -/
theorem offHeadW_le_miss (L : HonestTable) {x : X} {a c z : Z} {u : Mem → Option X → Mem}
    (hz : z = (L.perm (x, a)).2 + c) (hT : TrialBlock L.param x) {l : Layer} {e : KeyIndex}
    (hslot : slotOf L.param (blocks (blockInput x)) = some (.msg l e))
    (hu : u = liftW cwUpd l e x (L.perm (x, a)).1)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    offHeadW L (.readH z u) σ ≤
      diagMass {q : Unit × HwReg X Z Mem | q.2 ∈
        {s | KMiss x a s ∨ K'Miss (L.perm (x, a)).1 c s}} σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set xi := (L.perm (x, a)).1
  have htr : IsTrial trialUpd (.readH z u : HwRead X Z Mem) := ⟨(z, ⟨l, e, x, xi⟩), by rw [hu]; rfl⟩
  have hc := eq_readH_trialOf trialUpd htr
  obtain ⟨hz', hu'⟩ := HwRead.readH.inj hc
  obtain ⟨hl, he, hx, hxi⟩ := trialUpd_inj (t := ⟨l, e, x, xi⟩) (t' := (trialOf trialUpd
    (.readH z u : HwRead X Z Mem)).2) (by rw [← hu', hu]; rfl)
  obtain ⟨l0, e0, msg, ρ, -, hb⟩ := hT
  have hbx : blocks (blockInput x) = [x] := blocks_blockInput hb
  rw [diagMass_eq_dW _ hσ]
  unfold offHeadW
  rw [ite_eq_left htr]
  refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ ?_)
  refine mul_le_mul_of_nonneg_right ?_ (hre q)
  dsimp only
  by_cases hm : q.2 ∈ {s : HwReg X Z Mem | KMiss x a s ∨ K'Miss xi c s}
  · rw [ite_eq_left hm]
    split_ifs <;> norm_num
  · rw [ite_eq_right hm]
    have hka : (union q.2.2.1 q.2.1).k x = some a := not_not.1 fun h ↦ hm (.inl h)
    have hkc : (union q.2.2.1 q.2.1).k' xi = some c := not_not.1 fun h ↦ hm (.inr h)
    refine (ite_eq_left (Or.inr ⟨?_, xi, hxi.symm, ?_⟩)).le
    · show slotOf L.param (blocks (blockInput (trialOf trialUpd
        (.readH z u : HwRead X Z Mem)).2.x)) = some (.msg (trialOf trialUpd
          (.readH z u : HwRead X Z Mem)).2.l (trialOf trialUpd (.readH z u : HwRead X Z Mem)).2.e)
      rw [hx, hl, he]
      exact hslot
    · rw [hx, hbx, ← hz']
      exact ⟨[], 0, x, a, (L.perm (x, a)).2, c, rfl, IsTail.nil, hka,
        by rw [zero_add], hkc, hz⟩

/-- **The step condition of the refined trial modes at a read port.** -/
theorem offHead_step_read (L : HonestTable) (μ : HMode) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hok : rdOkH L.perm L.param (liftW cwUpd) μ c) :
    offHeadW L c σ + ∑' r, ∑ j, potential (hpot L.perm (rdNxH μ c r) j)
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      ∑ j, potential (hpot L.perm μ j) σ + leakW c σ := by
  have hpos : ∀ r, (MatrixMap.conj (hwReadKraus c r) σ).PosSemidef :=
    fun r ↦ posSemidef_conj _ hσ
  rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with _ | ⟨x₀, a⟩ | ⟨x₀, a, c₀⟩
  all_goals try exact False.elim hok
  · -- the `h`-read of a trial
    obtain ⟨hz, hT, l, e, hslot, hu⟩ := hok
    have h0 : ∀ r, ∑ j, potential (hpot L.perm (rdNxH (HMode.afK' x₀ a c₀)
        (.readH z u : HwRead X Z Mem) r) j) (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) = 0 :=
      fun r ↦ sum_potential_hpot_free L.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero, Fintype.sum_unique]
    show offHeadW L (.readH z u) σ ≤ potential (setProj {s | KMiss x₀ a s ∨
      K'Miss (L.perm (x₀, a)).1 c₀ s}) σ + 0
    rw [add_zero, potential_setProj _ hσ]
    exact offHeadW_le_miss L hz hT hslot hu hσ
  · -- the `k`-read of a trial
    have hL : ∀ r : Option Z × Mem, ∑ j, potential (hpot L.perm (rdNxH HMode.free
        (.readK x u : HwRead X Z Mem) r) j) (MatrixMap.conj (hwReadKraus (.readK x u) r) σ) =
        ENNReal.ofReal (dW (fun q ↦ if KMiss x (r.1.getD 0) q.2 then (1 : ℝ) else 0)
          (MatrixMap.conj (hwReadKraus (.readK x u) r) σ)) := fun r ↦ by
      rw [Fintype.sum_unique]
      exact (potential_setProj _ (hpos r)).trans (diagMass_eq_dW _ (hpos r))
    rw [offHeadW_not_trial L (fun _ _ h ↦ by cases h), zero_add, tsum_fintype,
      Finset.sum_congr rfl fun r _ ↦ hL r, sum_potential_hpot_free, zero_add]
    show _ ≤ ENNReal.ofReal _
    rw [ENNReal.ofReal_sum_of_nonneg fun r _ ↦ dW_nonneg (fun q ↦ by split_ifs <;> norm_num)
      (hpos r)]
  · -- the `k'`-read of a trial
    obtain ⟨rfl, -⟩ := hok
    have hnn : ∀ (f : Unit × HwReg X Z Mem → ℝ), (∀ q, 0 ≤ f q) → ∀ r : Option Z × Mem,
        0 ≤ dW f (MatrixMap.conj (hwReadKraus (.readK' (L.perm (x₀, a)).1 u) r) σ) :=
      fun f hf r ↦ dW_nonneg hf (hpos r)
    have hi : ∀ q : Unit × HwReg X Z Mem, (0 : ℝ) ≤ if KMiss x₀ a q.2 then 1 else 0 := fun q ↦ by
      split_ifs <;> norm_num
    have hi' : ∀ (r : Option Z × Mem) (q : Unit × HwReg X Z Mem),
        (0 : ℝ) ≤ if K'Miss (L.perm (x₀, a)).1 (r.1.getD 0) q.2 then 1 else 0 := fun r q ↦ by
      split_ifs <;> norm_num
    have hL : ∀ r : Option Z × Mem, ∑ j, potential (hpot L.perm (rdNxH (HMode.afK x₀ a)
        (.readK' (L.perm (x₀, a)).1 u : HwRead X Z Mem) r) j)
          (MatrixMap.conj (hwReadKraus (.readK' (L.perm (x₀, a)).1 u) r) σ) =
        ENNReal.ofReal (dW (fun q ↦ if q.2 ∈ {s | KMiss x₀ a s ∨
          K'Miss (L.perm (x₀, a)).1 (r.1.getD 0) s} then (1 : ℝ) else 0)
          (MatrixMap.conj (hwReadKraus (.readK' (L.perm (x₀, a)).1 u) r) σ)) := fun r ↦ by
      rw [Fintype.sum_unique]
      exact (potential_setProj _ (hpos r)).trans (diagMass_eq_dW _ (hpos r))
    have hR : ∑ j, potential (hpot L.perm (HMode.afK x₀ a) j) σ =
        ENNReal.ofReal (dW (fun q ↦ if KMiss x₀ a q.2 then (1 : ℝ) else 0) σ) := by
      rw [Fintype.sum_unique]
      exact (potential_setProj _ hσ).trans (diagMass_eq_dW _ hσ)
    rw [offHeadW_not_trial L (fun _ _ h ↦ by cases h), zero_add, tsum_fintype,
      Finset.sum_congr rfl fun r _ ↦ hL r, hR,
      ← readK'_keep_kMiss (L.perm (x₀, a)).1 u x₀ a σ]
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
    · have : q.2 ∈ {s | KMiss x₀ a s ∨ K'Miss (L.perm (x₀, a)).1 (r.1.getD 0) s} := .inl h1
      rw [ite_eq_left this, ite_eq_left h1]
      linarith [hi' r q]
    · by_cases h2 : K'Miss (L.perm (x₀, a)).1 (r.1.getD 0) q.2
      · have : q.2 ∈ {s | KMiss x₀ a s ∨ K'Miss (L.perm (x₀, a)).1 (r.1.getD 0) s} := .inr h2
        rw [ite_eq_left this, ite_eq_right h1, ite_eq_left h2, zero_add]
      · have : q.2 ∉ {s | KMiss x₀ a s ∨ K'Miss (L.perm (x₀, a)).1 (r.1.getD 0) s} :=
          fun h ↦ h.elim h1 h2
        rw [ite_eq_right this, ite_eq_right h1, ite_eq_right h2, add_zero]

/-- **The step condition of the refined trial modes**: the off-head mass of every allowed call
plus the potentials after it is at most the potentials before plus the leak charge. -/
theorem offHead_step (L : HonestTable) (μ : HMode) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ)
    (hσ : σ.PosSemidef) (hok : okZH L.perm L.param (liftW cwUpd) μ i) :
    extWeight (hwCost (offHeadW L) fun _ _ ↦ 0) i σ +
        ∑' r, ∑ j, potential (hpot L.perm (nxZH μ i r) j) (((runtimeR m0R).step i).branch r σ) ≤
      ∑ j, potential (hpot L.perm μ j) σ + extWeight (hwCost leakW fun _ _ ↦ 0) i σ := by
  rcases i with ((p | c) | c) | T
  · obtain rfl : μ = .free := hok
    have h0 : ∀ r, ∑ j, potential (hpot L.perm (nxZH HMode.free (.inl (.inl (.inl p))) r) j)
        (((runtimeR m0R).step (.inl (.inl (.inl p)))).branch r σ) = 0 :=
      fun r ↦ sum_potential_hpot_free L.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le
  · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    simp only [hb]
    exact offHead_step_read L μ c hσ hok
  · obtain rfl : μ = .free := hok
    have h0 : ∀ r, ∑ j, potential (hpot L.perm (nxZH HMode.free (.inl (.inr c)) r) j)
        (((runtimeR m0R).step (.inl (.inr c))).branch r σ) = 0 :=
      fun r ↦ sum_potential_hpot_free L.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le
  · obtain rfl : μ = .free := hok
    have h0 : ∀ r, ∑ j, potential (hpot L.perm (nxZH HMode.free (.inr T) r) j)
        (((runtimeR m0R).step (.inr T)).branch r σ) = 0 :=
      fun r ↦ sum_potential_hpot_free L.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le

variable {q : ℕ} {A : Adversary (X × Z)}

/-- **The off-head mass moves onto the leaks of the trials' `k`, `k'` reads** (TrialSource's
`totalWeight_le_moded_of_zero` with the refined modes). -/
theorem offHeadPre_le_leak (A : Adversary (X × Z)) (L : HonestTable) :
    offHeadPre A L ≤ (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost leakW fun _ _ ↦ 0)) (prefixR A L) initR :=
  totalWeight_le_moded_of_zero (runtimeR m0R) .instruments (hpot L.perm) _ _
    (fun μ i σ hσ hok ↦ offHead_step L μ i σ hσ hok) (prefixR A L) .free (fun _ ↦ rfl)
    (modedEH_realizeT cwUpd (valueAt L) _ (tFreeH_prefixT cwUpd (pubOf L) A)) initR_posSemidef

variable (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The leaks along the prefix**: at most `2/|Z|` per read call (`readK_leak_le`,
`readK'_leak_le` on the prefix's states, which have no decompressed `⊥`). -/
theorem totalWeight_leakW_le (L : HonestTable) :
    (runtimeR m0R).totalWeight .instruments (extWeight (hwCost leakW fun _ _ ↦ 0)) (prefixR A L)
      initR ≤ ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞) := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w' := fun i σ ↦ ENNReal.ofReal (2 / Fintype.card Z) * extWeight (hwCost
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef hx).trans ?_
  · rcases i with ((p | c) | c) | T
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
        fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (prefixR A L) initR)).trans ?_
    exact mul_le_mul_of_nonneg_left (totalWeight_calls_le (prefixR A L)
      (clsCalls_prefixR hperm hsign L)) zero_le

/-- **The off-head mass of the trial reads along the prefix**: at most `2/|Z|` per read call,
`offHeadPre ≤ 2^-511 clsCap`. -/
theorem offHeadPre_le (L : HonestTable) :
    offHeadPre A L ≤ ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞) :=
  (offHeadPre_le_leak A L).trans (totalWeight_leakW_le hperm hsign L)

omit hperm hsign in
open scoped Classical in
/-- **The hardwired trial heads of a trial read port**: the states whose read cell is hardwired,
outside `BadR`, with the trial's head path in the union (`0` at the other read ports). -/
noncomputable def hwHeadW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal (∑ q, (if q.2.2.1.1 (trialOf trialUpd c).1 ≠ none ∧
    q.2 ∉ BadR L progCap ∧ TrialHead L (trialOf trialUpd c).1 (trialOf trialUpd c).2 q.2 then
      (1 : ℝ) else 0) * (σ q q).re) else 0

omit hperm hsign in
/-- **The hardwired trial heads along the prefix.** -/
noncomputable def hwHeadPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (hwHeadW L) fun _ _ ↦ 0))
    (prefixR A L) initR

omit hperm hsign in
/-- **A hardwired classical move into `BadR` at a trial read** is off the trial's head or a
hardwired trial head. -/
theorem hwMoveW_le (L : HonestTable) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    hwMoveW L c σ ≤ offHeadW L c σ + hwHeadW L c σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  by_cases ht : IsTrial trialUpd c
  · simp only [hwMoveW, offHeadW, hwHeadW, ht, ↓reduceIte]
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    unfold hwMoveSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hre q)
    split_ifs with h1 h2 h3 h3 h2 h3 h3 <;> norm_num
    · exact h3 ⟨h1.1, h1.2.1, h2⟩
  · simp only [hwMoveW, ht, ↓reduceIte, zero_le]

omit hperm hsign in
/-- **The hardwired classical moves along the prefix**: at most the off-head mass and the
hardwired trial heads. -/
theorem hwMovePre_le_add (A : Adversary (X × Z)) (L : HonestTable) :
    hwMovePre A L ≤ offHeadPre A L + hwHeadPre A L := by
  refine (totalWeight_le_add (runtimeR m0R) .instruments _
    (extWeight (hwCost (offHeadW L) fun _ _ ↦ 0)) (extWeight (hwCost (hwHeadW L) fun _ _ ↦ 0))
    1 1 (fun i σ hσ ↦ ?_) (prefixR A L) initR_posSemidef).trans_eq (by rw [one_mul, one_mul]; rfl)
  rcases i with ((p | c) | c) | T
  · exact zero_le
  · show hwMoveW L c σ ≤ 1 * offHeadW L c σ + 1 * hwHeadW L c σ
    rw [one_mul, one_mul]
    exact hwMoveW_le L c hσ
  · exact zero_le
  · exact zero_le

/-- **The hardwired classical moves along the prefix**: `hwMovePre ≤ 2^-511 clsCap + hwHeadPre`. -/
theorem hwMovePre_le (L : HonestTable) :
    hwMovePre A L ≤ ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞) + hwHeadPre A L :=
  (hwMovePre_le_add A L).trans (add_le_add (offHeadPre_le hperm hsign L) le_rfl)

/-- **The constant of the prefix's linear charge** `2 encRPre + hwMovePre + kapRR clsCap`:
`2 E₀ q + (2 δ + 1) 2^-511 clsCap + kapRR clsCap`. -/
noncomputable def encEC (q : ℕ) : ℝ≥0∞ :=
  2 * encE0 q + (2 * encDelta + 1) * (ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞)) +
    ENNReal.ofReal kapRR * (clsCap : ℝ≥0∞)

/-- **The prefix's linear charge, per good table** (CostRefined's `twPR_le` Enc term
`E = 2 encRPre + hwMovePre + kapRR clsCap`): on a `PermGood` table, for `q ≤ 2^64`,
`E ≤ encEC q + 2 β q (cwRecPre + recBadPre) + 2 γ q (kfPre + recJPre) + hwHeadPre`, the shape of
Security's `uavg_ite_cost_le_add` with `m = cwRecPre + recBadPre`. -/
theorem encE_le (hq : q ≤ 2 ^ 64) (L : HonestTable) (hπ : PermGood L.perm 18) :
    2 * encRPre A L + hwMovePre A L + ENNReal.ofReal kapRR * (clsCap : ℝ≥0∞) ≤
      encEC q + 2 * encBeta q * (cwRecPre A L + recBadPre A L) +
        2 * encGamma q * (kfPre A L + recJPre A L) + hwHeadPre A L := by
  have h1 := encRPre_le_lin hperm hsign hq L hπ
  have h2 := offHeadPre_le hperm hsign L
  have h3 := hwMovePre_le hperm hsign L
  have h4 : encRPre A L ≤ encE0 q + encBeta q * (cwRecPre A L + recBadPre A L) +
      encGamma q * (kfPre A L + recJPre A L) +
        encDelta * (ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞)) :=
    h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 zero_le))
  refine (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h4 zero_le) h3) le_rfl).trans_eq ?_
  unfold encEC
  ring

omit hperm hsign in
/-- **The register states whose hardwired `h` cells head honest tails**: every hardwired `h` cell
is the end of a head-tail of the union at a slot other than a message slot (the honest path of the
slot that programmed it). -/
def HwHeadsHonest (L : HonestTable) (s : HwReg X Z Mem) : Prop :=
  ∀ z, s.2.1.1 z ≠ none → ∃ t xi, IsHeadTail L.perm (union s.2.1 s.1) t z xi ∧
    ∀ l e, slotOf L.param t ≠ some (.msg l e)

omit hperm hsign in
/-- **No hardwired trial head on states with honest hardwired heads**: outside `BadR` (a good union
at hardwired grade at most `progCap`) the head-tail of the read cell is unique, so it cannot be
both the trial's (at a message slot) and an honest one. -/
theorem hwHeadW_eq_zero (L : HonestTable) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hH : ∀ a, σ a a ≠ 0 → HwHeadsHonest L a.2 ∧ dbGrade a.2.2.1 ≤ progCap) :
    hwHeadW L c σ = 0 := by
  classical
  by_cases ht : IsTrial trialUpd c
  · simp only [hwHeadW, ht, ↓reduceIte]
    rw [Finset.sum_eq_zero fun a _ ↦ ?_, ENNReal.ofReal_zero]
    by_cases h0 : σ a a = 0
    · rw [h0, Complex.zero_re, mul_zero]
    rw [ite_eq_right, zero_mul]
    rintro ⟨hw, hb, hg⟩
    obtain ⟨hhon, hN⟩ := hH a h0
    obtain ⟨t, xi, hi, hslot⟩ := hhon _ hw
    have hb' : (a.2.1, a.2.2.1, a.2.2.2.2) ∉ Bad L progCap := hb
    have hG : Good L.perm (union a.2.2.1 a.2.1) :=
      (not_mem_targetBad_iff.1 (union_not_mem_of_not_mem_hwTargetBad hb' hN)).1
    rcases hg with hg | ⟨hmsg, xi', -, hi'⟩
    · exact hg hG
    · obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hi'
      exact hslot _ _ hmsg
  · simp only [hwHeadW, ht, ↓reduceIte]

/-- **The hardwired trial heads vanish under the honest-heads invariant**: if every call of the
prefix is presented states whose hardwired `h` cells head honest tails (`HwHeadsHonest`), then
`hwHeadPre = 0`. -/
theorem hwHeadPre_eq_zero (L : HonestTable)
    (h : (runtimeR m0R).ForallQueries .instruments
      (invSupp (runtimeR m0R) (fun _ ↦ True) (HwHeadsHonest L)) (prefixR A L) initR) :
    hwHeadPre A L = 0 := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  refine le_antisymm ((totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i σ ↦ PreInv q i σ ∧ DiagOn (HwHeadsHonest L) σ)
    (P := fun i E σ ↦ P i E σ ∧ invSupp (runtimeR m0R) (fun _ ↦ True) (HwHeadsHonest L) i E σ)
    (fun i E σ h ↦ ⟨hP i E σ h.1, fun a ha ↦ traceRight_diag_eq_zero fun e ↦ h.2 trivial (a, e) ha⟩)
    (w' := fun i σ ↦ 0 * extWeight (hwCost (hwHeadW L) fun _ _ ↦ 0) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef (forallQueries_and hx h)).trans_eq ?_)
    zero_le
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · refine le_of_eq ((hwHeadW_eq_zero L c fun a ha ↦ ⟨?_, (hI.1.2.1 a a ha).1.2⟩).trans
        (zero_mul _).symm)
      by_contra hn
      exact ha (hI.2 a hn)
    · exact zero_le
    · exact zero_le
  · exact (totalWeight_const_mul_weight (runtimeR m0R) .instruments _
      (extWeight (hwCost (hwHeadW L) fun _ _ ↦ 0)) (prefixR A L) initR).trans (zero_mul _)

end offHead

end Quantum.Xmss.Assembly

end
