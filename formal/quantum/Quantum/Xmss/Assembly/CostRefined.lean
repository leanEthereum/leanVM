module

public import Quantum.Xmss.Assembly.RestMass
public import Quantum.Xmss.Assembly.EncPorts

@[expose] public section

/-!
# The challenge prefix's classical costs with the refined read cost

Security's chain prices a read port with CostLift's `flipCost` relative to `PRof`, whose `p` term is
`massW`: the whole weight off the selection reads (recorded or hardwired cells with any value, the
re-grinds of selected keys). Here the read ports are priced with ReadCost's refined cost
`readCostT` (`dRref`): the event bound at the end of the prefix holds with it (`ewPrefix_le_ref`,
`ewR_le_sqrt_ref`), and its total `twPR` splits with the cross term on the flip-value recorded mass
only.

* **An `h` read, linearized** (`dw_le_diag`, `readA_readH_le_fine`, `costP_readH_le`,
  `readCost_readH_le_lin`): for every `s > 0` the refined cost is at most
  `(1 + s) readHA + (1 + 1/s) readHP`. `readHA`: on an empty cell `(2 f + 2) / |X|` with `f` the
  values that flip the event when read (`hFlip`), on a recorded cell `2 / |X|`, on a hardwired cell
  its classical move (`hCls`). `readHP`: the recorded cells whose value flips the event against the
  emptied cell or moves the memory across it (`RecFlip`).
* **The trials' recorded flips** (`recFlip_trial`): at a trial read a recorded flip is
  codeword-recorded for the trial's unselected key (RestMass's `CwRec`: the memory moves only by a
  codeword selection) or a recorded value that puts the state into `BadR` (`RecBad`; e.g. a key
  already selected with digest `d` and a recorded value reaching `d`). The second part is not in
  `cwRecW`: its cross term pairs it with the `2^-128`-scale empty-cell flips of the same port.
* **The `k`, `k'` reads** (`keepE_readK_le`, `keepE_readK'_le`, `readCost_readKPort_le`,
  `readCost_readK'Port_le`): they keep the memory; the capacity-scale counts of CostLift give
  `keepE ≤ 2^-301 tr σ`, so the refined cost is at most `kapRR tr σ`,
  `kapRR = 2^-301 + 2/|X| + 2/|Z| + 2 √(2^-301)`.
* **The prefix** (`twPR_le`): on `PermGood` tables, for `q ≤ 2^64`,
  `twPR ≤ (√(2 encRPre + hwMovePre + kapRR clsCap) + √(cwRecPre + recBadPre))² + progPreR`
  (EncPorts' `forallQueries_preInv`: only `ReadOk` reads, low grade, no decompressed `⊥`).
* **The remaining averaged bound for the new mass** (`RecBadAvg`): the average over a good set of
  `recBadPre`, the analogue of RestMass's `uavg_cwRecPre_le_add` for `RecBad`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Sponge

open Quantum

/-! ## The change weight of a recorded outcome, by its own state -/

theorem dw_le_diag {n Y R : Type} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {e : n ≃ Option Y × R} {τ : Option Y → R → R} (S : Set n) [DecidablePred (· ∈ S)]
    (y : Y) (r : R) :
    dw e τ S y r ≤ (if ind S (e.symm (some y, τ (some y) r)) = q0 e S r then 0 else 1) +
      2 / Fintype.card Y := by
  have hN : (1 : ℝ) ≤ Fintype.card Y := Nat.one_le_cast.mpr Fintype.card_pos
  have hc : ∑ a, cr a (some y) ^ 2 - cr (some y) (some y) ^ 2 ≤ 2 / Fintype.card Y := by
    rw [sum_cr_sq]
    simp only [cr, ↓reduceIte]
    have : 0 < (Fintype.card Y : ℝ)⁻¹ := inv_pos.mpr (by linarith)
    rw [div_eq_mul_inv]
    nlinarith
  have hyy : cr (some y) (some y) ^ 2 ≤ 1 := by
    simp only [cr, ↓reduceIte]
    have h0 : 0 ≤ (Fintype.card Y : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : (Fintype.card Y : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
    nlinarith
  have hc01 : ∀ a : Option Y,
      0 ≤ (if ind S (e.symm (a, τ (some y) r)) = q0 e S r then (0 : ℝ) else 1) ∧
        (if ind S (e.symm (a, τ (some y) r)) = q0 e S r then (0 : ℝ) else 1) ≤ 1 :=
    fun a ↦ by split_ifs <;> norm_num
  have hrest : ∑ a ∈ Finset.univ.erase (some y), cr a (some y) ^ 2 *
      (if ind S (e.symm (a, τ (some y) r)) = q0 e S r then (0 : ℝ) else 1) ≤
      ∑ a, cr a (some y) ^ 2 - cr (some y) (some y) ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (some y)), add_sub_cancel_right]
    exact Finset.sum_le_sum fun a _ ↦ mul_le_of_le_one_right (sq_nonneg _) (hc01 a).2
  have hlast : cr (some y) (some y) ^ 2 *
      (if ind S (e.symm (some y, τ (some y) r)) = q0 e S r then (0 : ℝ) else 1) ≤
      (if ind S (e.symm (some y, τ (some y) r)) = q0 e S r then (0 : ℝ) else 1) :=
    mul_le_of_le_one_left (hc01 _).1 hyy
  rw [dw, ← Finset.sum_erase_add _ _ (Finset.mem_univ (some y))]
  linarith

/-! ## A read of `h`, linearized -/

section readH

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

omit [Fintype X] [DecidableEq X] [Fintype Z] [Fintype M] [DecidableEq M] in
/-- **The recorded flip states of a read of `h` at `z`**: the cell is recorded with a value `y`
that flips the event against the emptied cell, or whose read moves the memory across the event
for some content of the cell. -/
def RecFlip (S : Set (HwReg X Z M)) (z : Z) (upd : M → Option X → M)
    (q : Unit × HwReg X Z M) : Prop :=
  ∃ y, q.2.1.1 z = some y ∧
    (¬ (q.2 ∈ S ↔ ((Function.update q.2.1.1 z none, q.2.1.2), q.2.2) ∈ S) ∨
      ∃ u : Option X, ¬ ((((Function.update q.2.1.1 z u, q.2.1.2), q.2.2.1,
        upd q.2.2.2 (some y)) ∈ S) ↔ (((Function.update q.2.1.1 z u, q.2.1.2), q.2.2) ∈ S)))

/-- **The linear part of a read of `h`**: `(2 f + 2) / |X|` on an empty cell (`f` the flipping
values `hFlip`), `2 / |X|` on a recorded cell, the classical move on a hardwired cell. -/
noncomputable def readHA (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (upd : M → Option X → M) (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, (if q.2.2.1.1 z = none then
      (if q.2.1.1 z = none then
        (2 * ((Finset.univ.filter (hFlip S z upd q)).card : ℝ) + 2) / Fintype.card X else
        2 / Fintype.card X) else
      if hCls S upd (q.2.2.1.1 z) q then 1 else 0) * (σ q q).re

open scoped Classical in
/-- **The flip-value recorded mass of a read of `h`**: the recorded, not hardwired, flip states. -/
noncomputable def readHP (S : Set (HwReg X Z M)) (z : Z) (upd : M → Option X → M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, (if q.2.2.1.1 z = none ∧ RecFlip S z upd q then 1 else 0) * (σ q q).re

omit [DecidableEq M] in
/-- **The diagonal term of a read of `h`, with the empty cells by their own flips**: an empty cell
costs its flipping values over `|X|` plus `2 / |X|` (`dw_le_diag`); recorded and hardwired cells as
in `read_readH_le`. -/
theorem readA_readH_le_fine [Nonempty X] (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (upd : M → Option X → M) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) :
    readA S (.readH z upd) σ ≤ ∑ q, (if q.2.2.1.1 z = none then
      (if q.2.1.1 z = none then
        (((Finset.univ.filter (hFlip S z upd q)).card : ℝ) + 2) / Fintype.card X else
        2 / Fintype.card X + if hCls S upd (q.2.1.1 z) q then 1 else 0) else
      if hCls S upd (q.2.2.1.1 z) q then 1 else 0) * (σ q q).re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hsym := splitH'_symm_tau (M := M) z upd
  have hN0 : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold readA costA
  refine Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right ?_ (hre q)
  by_cases ha : q.2.2.1.1 z = none
  · rw [ite_eq_left ha]
    have ha' : actH z (splitH' z q).2 := ha
    rcases h1 : q.2.1.1 z with _ | y
    · rw [ite_eq_left rfl]
      refine (fd_none_le (liftSet S) ha' h1).trans
        (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
      have hq0 : q0 (splitH' z) (liftSet S) (splitH' z q).2 = ind (liftSet S) q := by
        rw [q0, splitH'_symm_none z q h1]
      calc chw (splitH' z) (tauH z upd) (liftSet S) (splitH' z q).2
          ≤ ∑ y : X, ((if ind (liftSet S) ((splitH' z).symm (some y,
              tauH z upd (some y) (splitH' z q).2)) = q0 (splitH' z) (liftSet S)
                (splitH' z q).2 then (0 : ℝ) else 1) + (2 : ℝ) / Fintype.card X) :=
            Finset.sum_le_sum fun y _ ↦ dw_le_diag (liftSet S) y _
        _ = ((Finset.univ.filter fun y : X ↦ ¬ ind (liftSet S) ((splitH' z).symm (some y,
              tauH z upd (some y) (splitH' z q).2)) = q0 (splitH' z) (liftSet S)
                (splitH' z q).2).card : ℝ) + 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              Finset.card_filter, Nat.cast_sum]
            congr 1
            · exact Finset.sum_congr rfl fun y _ ↦ by split_ifs <;> simp
            · field_simp
        _ ≤ ((Finset.univ.filter (hFlip S z upd q)).card : ℝ) + 2 := by
            refine add_le_add (Nat.cast_le.mpr (Finset.card_le_card fun v hv ↦ ?_)) le_rfl
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
            rw [hsym, hq0] at hv
            replace hv := (ind_ne_iff _ _).1 hv
            unfold hFlip
            by_cases h2 : (((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2) ∈ S ↔ q.2 ∈ S)
            · exact .inr ⟨some v, fun h3 ↦ hv (h3.trans h2)⟩
            · exact .inl h2
    · rw [ite_eq_right (Option.some_ne_none y)]
      refine (fd_some_le (liftSet S) (τ := tauH z upd) (φ := phiH z upd) ha' h1).trans ?_
      rw [hsym]
      have hup : Function.update q.2.1.1 z (some y) = q.2.1.1 := by
        rw [← h1, Function.update_eq_self]
      rw [hup, add_comm]
      exact add_le_add le_rfl (ind_sub_ind_le _ q)
  · rw [ite_eq_right ha, fd_off (liftSet S) (show ¬ actH z (splitH' z q).2 from ha)]
    exact ind_sub_ind_le _ q

omit [DecidableEq M] in
/-- **The flip-value recorded mass of a read of `h`** is at most `readHP`. -/
theorem costP_readH_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (upd : M → Option X → M) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) :
    Quantum.Xmss.Assembly.readP S (.readH z upd) σ ≤ readHP S z upd σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hsym := splitH'_symm_tau (M := M) z upd
  have hsym0 : ∀ (q : Unit × HwReg X Z M) (a : Option X), (splitH' z).symm (a, (splitH' z q).2) =
      ((), ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, q.2.2.2)) := fun q a ↦
    splitH'_symm_tau z (fun m _ ↦ m) q a a
  show costP (splitH' z) (actH z) (tauH z upd) (liftSet S) σ ≤ _
  unfold costP readHP
  refine Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right ?_ (hre q)
  unfold pd
  by_cases ha : q.2.2.1.1 z = none
  · rw [ite_eq_left (show actH z (splitH' z q).2 from ha)]
    rcases h1 : (splitH' z q).1 with _ | y
    · simp only [Option.elim_none]
      split_ifs <;> norm_num
    · simp only [Option.elim_some]
      by_cases hf : Flip (splitH' z) (tauH z upd) (liftSet S) y (splitH' z q).2
      · rw [ite_eq_left hf]
        have hq : (splitH' z).symm (some y, (splitH' z q).2) = q := by
          rw [← h1, Prod.mk.eta, Equiv.symm_apply_apply]
        have hrf : RecFlip S z upd q := by
          refine ⟨y, h1, ?_⟩
          rcases hf with hf | ⟨a, hm⟩
          · rw [q0, hq, hsym0, ind_ne_iff] at hf
            exact .inl hf
          · rw [hsym, hsym0, ind_ne_iff] at hm
            exact .inr ⟨a, hm⟩
        rw [ite_eq_left ⟨ha, hrf⟩]
      · rw [ite_eq_right hf]
        split_ifs <;> norm_num
  · rw [ite_eq_right (show ¬ actH z (splitH' z q).2 from ha), ite_eq_right fun h' ↦ ha h'.1]

omit [Fintype X] [DecidableEq X] [Fintype Z] [Fintype M] [DecidableEq M] in
/-- A classical move with the recorded value is a recorded flip. -/
theorem recFlip_of_hCls {S : Set (HwReg X Z M)} {z : Z} {upd : M → Option X → M}
    {q : Unit × HwReg X Z M} (hD : q.2.1.1 z ≠ none) (h : hCls S upd (q.2.1.1 z) q) :
    RecFlip S z upd q := by
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hD
  refine ⟨y, hy, .inr ⟨some y, fun hiff ↦ h.1 ?_⟩⟩
  have hup : Function.update q.2.1.1 z (some y) = q.2.1.1 := by
    rw [← hy, Function.update_eq_self]
  rw [hup] at hiff
  have h2 := h.2
  rw [hy] at h2
  exact hiff.1 h2

omit [DecidableEq M] in
/-- **The refined cost of a read of `h`, linearized**: for every `s > 0`, at most
`(1 + s) readHA + (1 + 1/s) readHP` (`re_trace_flipOp_le`'s `A + 2 √(E p)` with `A ≤ readHA - E`
plus the recorded classical moves, `E ≤` the empty cells' flipping values over `|X|`, `p ≤ readHP`;
`2 √(E p) ≤ s E + p / s`). -/
theorem readCost_readH_le_lin [Nonempty X] (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (z : Z) (upd : M → Option X → M)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) {s : ℝ}
    (hs : 0 < s) :
    readCost S (.readH z upd) σ ≤ ENNReal.ofReal (1 + s) * ENNReal.ofReal (readHA S z upd σ) +
      ENNReal.ofReal (1 + s⁻¹) * ENNReal.ofReal (readHP S z upd σ) := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  obtain ⟨hE, -, -⟩ := read_readH_le S z upd hσ
  have hA := readA_readH_le_fine S z upd hσ
  have hP := costP_readH_le S z upd hσ
  have hN : (0 : ℝ) ≤ Fintype.card X := Nat.cast_nonneg _
  set A0 : ℝ := ∑ q, (if q.2.2.1.1 z = none then
      (if q.2.1.1 z = none then
        (((Finset.univ.filter (hFlip S z upd q)).card : ℝ) + 2) / Fintype.card X else
        2 / Fintype.card X) else
      if hCls S upd (q.2.2.1.1 z) q then 1 else 0) * (σ q q).re with hA0
  set E0 : ℝ := ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z = none then
      ((Finset.univ.filter (hFlip S z upd q)).card : ℝ) / Fintype.card X else 0) *
      (σ q q).re with hE0
  have hA' : readA S (.readH z upd) σ ≤ A0 + readHP S z upd σ := by
    refine hA.trans ?_
    rw [hA0, readHP, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hre q)
    by_cases hW : q.2.2.1.1 z = none
    · by_cases hD : q.2.1.1 z = none
      · simp only [ite_eq_left hW, ite_eq_left hD]
        split_ifs <;> norm_num
      · simp only [ite_eq_left hW, ite_eq_right hD]
        by_cases hc : hCls S upd (q.2.1.1 z) q
        · rw [ite_eq_left hc, ite_eq_left ⟨hW, recFlip_of_hCls hD hc⟩]
        · rw [ite_eq_right hc]
          split_ifs <;> norm_num
    · simp only [ite_eq_right hW]
      split_ifs <;> norm_num
  have hsum : A0 + E0 = readHA S z upd σ := by
    rw [hA0, hE0, readHA, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    by_cases hW : q.2.2.1.1 z = none
    · by_cases hD : q.2.1.1 z = none
      · simp only [ite_eq_left hW, ite_eq_left hD, ite_eq_left (And.intro hW hD)]
        ring
      · simp only [ite_eq_left hW, ite_eq_right hD, ite_eq_right fun h : _ ∧ _ ↦ hD h.2]
        ring
    · simp only [ite_eq_right hW, ite_eq_right fun h : _ ∧ _ ↦ hW h.1]
      ring
  have hE00 : 0 ≤ E0 := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by positivity) (hre q)
  have hA00 : 0 ≤ A0 := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
    split_ifs <;> positivity) (hre q)
  have hP0 : 0 ≤ readHP S z upd σ := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
    split_ifs <;> norm_num) (hre q)
  rw [Quantum.Xmss.Assembly.readCost_eq]
  calc ENNReal.ofReal (readA S (.readH z upd) σ) +
        2 * (ENNReal.ofReal (readE S (.readH z upd) σ) *
          ENNReal.ofReal (Quantum.Xmss.Assembly.readP S (.readH z upd) σ)) ^ (2⁻¹ : ℝ)
      ≤ ENNReal.ofReal A0 + ENNReal.ofReal (readHP S z upd σ) +
          2 * (ENNReal.ofReal E0 * ENNReal.ofReal (readHP S z upd σ)) ^ (2⁻¹ : ℝ) :=
        add_le_add ((ENNReal.ofReal_le_ofReal hA').trans ENNReal.ofReal_add_le)
          (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow (mul_le_mul'
            (ENNReal.ofReal_le_ofReal hE) (ENNReal.ofReal_le_ofReal hP)) (by norm_num)) zero_le)
    _ ≤ ENNReal.ofReal (1 + s) * (ENNReal.ofReal A0 + ENNReal.ofReal E0) +
          ENNReal.ofReal (1 + s⁻¹) * ENNReal.ofReal (readHP S z upd σ) :=
        Quantum.Xmss.Assembly.cost_le_lin' hs hP0
    _ = _ := by rw [← ENNReal.ofReal_add hA00 hE00, hsum]

end readH

end Quantum.Sponge

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## The ports of the prefix -/

section ports

attribute [local instance] badRDec

/-- **A recorded value that puts the state into the event**: the cell `z` recorded, not hardwired,
the state in `BadR`, the state with the cell emptied not. -/
def RecBad (L : HonestTable) (z : Z) (s : HwReg X Z Mem) : Prop :=
  s.2.1.1 z = none ∧ s.1.1 z ≠ none ∧ s ∈ BadR L progCap ∧
    ((Function.update s.1.1 z none, s.1.2), s.2) ∉ BadR L progCap

open scoped Classical in
/-- **The `RecBad` mass of a trial read port** (`0` at the other read ports). -/
noncomputable def recBadW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal (∑ q, if RecBad L (trialOf trialUpd c).1 q.2 then
    (σ q q).re else 0) else 0

/-- The empty-cell flips of a trial read: the values that flip `BadR` when read, over `|X|`. -/
noncomputable def encRSum (L : HonestTable) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ :=
  ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z = none then
    ((Finset.univ.filter (hFlip (BadR L progCap) z (trialUpd t) q)).card : ℝ) /
      Fintype.card X else 0) * (σ q q).re

/-- The hardwired classical moves of a trial read into `BadR`. -/
noncomputable def hwMoveSum (L : HonestTable) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ :=
  ∑ q, (if q.2.2.1.1 z ≠ none ∧ hCls (BadR L progCap) (trialUpd t) (q.2.2.1.1 z) q then 1 else 0) *
    (σ q q).re

open scoped Classical in
/-- **The empty-cell flips of a trial read port** (`encRSum`; `0` at the other read ports). -/
noncomputable def encRW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then
    ENNReal.ofReal (encRSum L (trialOf trialUpd c).1 (trialOf trialUpd c).2 σ) else 0

open scoped Classical in
/-- **The hardwired classical moves of a trial read port** (`hwMoveSum`; `0` elsewhere). -/
noncomputable def hwMoveW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then
    ENNReal.ofReal (hwMoveSum L (trialOf trialUpd c).1 (trialOf trialUpd c).2 σ) else 0

/-- **The charge of a `k`, `k'` read per unit of trace**: `2^-301 + 2/|X| + 2/|Z| + 2 √(2^-301)`
(it also covers the trial reads' `2/|X|`). -/
noncomputable def kapRR : ℝ :=
  (2 ^ 301 : ℝ)⁻¹ + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √((2 ^ 301 : ℝ)⁻¹)

theorem kapRR_nonneg : 0 ≤ kapRR := by
  unfold kapRR
  positivity

theorem two_div_card_X_le_kapRR : 2 / (Fintype.card X : ℝ) ≤ kapRR := by
  have key : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ c → 0 ≤ d → b ≤ a + (b + c) + d :=
    fun a b c d ha hc hd ↦ by linarith
  exact key _ _ _ _ (inv_nonneg.mpr (pow_nonneg zero_le_two _))
    (div_nonneg zero_le_two (Nat.cast_nonneg _)) (mul_nonneg zero_le_two (Real.sqrt_nonneg _))

/-- **The linear charge of a read port**: `2 encRW + hwMoveW + kapRR tr σ`. -/
noncomputable def aRW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  2 * encRW L c σ + hwMoveW L c σ + ENNReal.ofReal (kapRR * σ.trace.re)

/-- **The flip-value recorded mass of a read port**: RestMass's `cwRecW` plus `recBadW`. -/
noncomputable def pRW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  cwRecW Prod.snd trialUpd c σ + recBadW L c σ

/-- **A recorded flip at a trial read is codeword-recorded or `RecBad`.** The memory moves only by
a codeword selection of the unselected key (`cwUpd`); a recorded value that flips the event against
the emptied cell puts the state into `BadR` (the slices are up-closed). -/
theorem recFlip_trial (L : HonestTable) (t : TrialPt) (z : Z) (q : Unit × HwReg X Z Mem)
    (hW : q.2.2.1.1 z = none) (h : RecFlip (BadR L progCap) z (trialUpd t) q) :
    CwRec z t q.2 ∨ RecBad L z q.2 := by
  obtain ⟨y, hy, h | ⟨u, hu⟩⟩ := h
  · have hfill : ((Function.update q.2.1.1 z none, q.2.1.2), q.2.2) ∈ BadR L progCap →
        q.2 ∈ BadR L progCap := by
      intro hb
      have hb' : ((Function.update q.2.1.1 z none, q.2.1.2), q.2.2.1, q.2.2.2.2) ∈
          Bad L progCap := hb
      have h2 := mem_hwTargetBad_fill (z := z) hb' (by simp) (some y) q.2.2.2.2 fun _ _ h ↦ h
      have h3 : Function.update (Function.update q.2.1.1 z none) z (some y) = q.2.1.1 := by
        rw [Function.update_idem, ← hy, Function.update_eq_self]
      simp only [h3] at h2
      exact h2
    by_cases hq : q.2 ∈ BadR L progCap
    · exact .inr ⟨hW, by rw [hy]; exact Option.some_ne_none y, hq,
        fun hb ↦ h (iff_of_true hq hb)⟩
    · exact absurd (iff_of_false hq fun hb ↦ hq (hfill hb)) h
  · have key : ¬ (q.2.2.2.2 t.l t.e = none ∧ Codeword.Valid (trunc128 (t.xi + y))) →
        trialUpd t q.2.2.2 (some y) = q.2.2.2 := by
      intro hc
      show (q.2.2.2.1, cwUpd t.l t.e t.x t.xi q.2.2.2.2 (some y)) = q.2.2.2
      have h0 : cwUpd t.l t.e t.x t.xi q.2.2.2.2 (some y) = q.2.2.2.2 := by
        show (if q.2.2.2.2 t.l t.e = none then cwSel q.2.2.2.2 t.l t.e t.x t.xi y else
          q.2.2.2.2) = _
        split_ifs with hn
        · unfold cwSel
          exact ite_eq_right fun hv ↦ hc ⟨hn, hv⟩
        · rfl
      rw [h0]
    have hk : q.2.2.2.2 t.l t.e = none ∧ Codeword.Valid (trunc128 (t.xi + y)) := by
      by_contra hc
      apply hu
      rw [key hc]
    exact .inl ⟨hW, hk.1, y, hy, hk.2⟩

/-- **A trial read port, linearized**: for every `s > 0` its refined cost is at most
`(1 + s) aRW + (1 + 1/s) pRW` (`readCost_readH_le_lin`, `recFlip_trial`). -/
theorem readCost_trial_le (L : HonestTable) {c : HwRead X Z Mem} (ht : IsTrial trialUpd c)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) {s : ℝ}
    (hs : 0 < s) :
    readCost (BadR L progCap) c σ ≤
      ENNReal.ofReal (1 + s) * aRW L c σ + ENNReal.ofReal (1 + s⁻¹) * pRW L c σ := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  have hc := eq_readH_trialOf trialUpd ht
  simp only [aRW, pRW, encRW, hwMoveW, cwRecW, recBadW, ht, ↓reduceIte]
  generalize trialOf trialUpd c = zt at hc ⊢
  subst hc
  obtain ⟨z, t⟩ := zt
  refine (readCost_readH_le_lin (BadR L progCap) z (trialUpd t) hσ hs).trans
    (add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) (mul_le_mul_of_nonneg_left ?_ zero_le))
  · have hkey : readHA (BadR L progCap) z (trialUpd t) σ ≤
        2 * encRSum L z t σ + hwMoveSum L z t σ + kapRR * σ.trace.re := by
      rw [htr]
      unfold readHA encRSum hwMoveSum
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun q _ ↦ ?_
      have h2 := mul_le_mul_of_nonneg_right two_div_card_X_le_kapRR (hre q)
      have hk := mul_nonneg kapRR_nonneg (hre q)
      by_cases hW : q.2.2.1.1 z = none
      · have hn : ¬ (q.2.2.1.1 z ≠ none ∧ hCls (BadR L progCap) (trialUpd t) (q.2.2.1.1 z) q) :=
          fun h ↦ h.1 hW
        rw [ite_eq_right hn, zero_mul, add_zero]
        by_cases hD : q.2.1.1 z = none
        · simp only [ite_eq_left hW, ite_eq_left hD, ite_eq_left (And.intro hW hD)]
          have e : (2 * ((Finset.univ.filter
              (hFlip (BadR L progCap) z (trialUpd t) q)).card : ℝ) + 2) / Fintype.card X *
                (σ q q).re = 2 * (((Finset.univ.filter
                  (hFlip (BadR L progCap) z (trialUpd t) q)).card : ℝ) / Fintype.card X *
                    (σ q q).re) + 2 / Fintype.card X * (σ q q).re := by ring
          rw [e]
          linarith
        · simp only [ite_eq_left hW, ite_eq_right hD, ite_eq_right fun h : _ ∧ _ ↦ hD h.2, zero_mul,
            mul_zero,
            zero_add]
          exact h2
      · simp only [ite_eq_right hW, ite_eq_right fun h : _ ∧ _ ↦ hW h.1, zero_mul, mul_zero,
          zero_add]
        have he : (if hCls (BadR L progCap) (trialUpd t) (q.2.2.1.1 z) q then (1 : ℝ) else 0) =
            if q.2.2.1.1 z ≠ none ∧ hCls (BadR L progCap) (trialUpd t) (q.2.2.1.1 z) q then 1
              else 0 := by
          by_cases hcl : hCls (BadR L progCap) (trialUpd t) (q.2.2.1.1 z) q
          · rw [ite_eq_left hcl, ite_eq_left ⟨hW, hcl⟩]
          · rw [ite_eq_right hcl, ite_eq_right fun h ↦ hcl h.2]
        rw [he]
        linarith
    have he0 : 0 ≤ encRSum L z t σ := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      split_ifs
      exacts [div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), le_rfl]) (hre q)
    have hm0 : 0 ≤ hwMoveSum L z t σ := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      split_ifs <;> norm_num) (hre q)
    have ht0 : 0 ≤ kapRR * σ.trace.re :=
      mul_nonneg kapRR_nonneg (Complex.nonneg_iff.1 hσ.trace_nonneg).1
    refine (ENNReal.ofReal_le_ofReal hkey).trans ?_
    rw [ENNReal.ofReal_add (by positivity) ht0, ENNReal.ofReal_add (by positivity) hm0,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  · refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    unfold readHP
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases hp : q.2.2.1.1 z = none ∧ RecFlip (BadR L progCap) z (trialUpd t) q
    · rw [ite_eq_left hp, one_mul]
      have h := recFlip_trial L t z q hp.1 hp.2
      split_ifs with h1 h2 h2
      · linarith [hre q]
      · linarith [hre q]
      · linarith [hre q]
      · exfalso
        rcases h with h | h
        · exact h1 h
        · exact h2 h
    · rw [ite_eq_right hp, zero_mul]
      exact add_nonneg (by split_ifs <;> linarith [hre q]) (by split_ifs <;> linarith [hre q])

/-- `C / |Z| ≤ 2^-301` for `C ≤ 2^211`. -/
theorem cap_div_card_Z_le {C : ℕ} (hC : C ≤ 2 ^ 211) :
    (C : ℝ) / Fintype.card Z ≤ (2 ^ 301 : ℝ)⁻¹ := by
  rw [card_Z, Nat.cast_pow, Nat.cast_ofNat,
    show (2 : ℝ) ^ 512 = 2 ^ 211 * 2 ^ 301 by rw [← pow_add], div_le_iff₀ (by positivity),
    mul_comm ((2 : ℝ) ^ 211), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  exact_mod_cast hC

/-- **The empty-cell term of a `k` read for `BadR`**: on states with at most `2^68 - progCap`
database entries per function, `keepE ≤ 2^-301 tr σ` (`card_flip_readK_bad_le`; inside `BadR` a
filled cell stays inside). -/
theorem keepE_readK_le (L : HonestTable) (hπ : PermGood L.perm 18) (x : X)
    (upd : Mem → Option Z → Mem) {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    keepE (BadR L progCap) (.readK x upd) σ ≤ (2 ^ 301 : ℝ)⁻¹ * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  rw [htr, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases h0 : σ q q = 0
  · exact le_of_eq (by rw [h0, Complex.zero_re, mul_zero, mul_zero])
  refine mul_le_mul_of_nonneg_right ?_ (hre q)
  split_ifs with hx
  · refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) (Nat.cast_nonneg _))
      (cap_div_card_Z_le capK_le)
    unfold flipCnt
    by_cases hB : q.2 ∈ BadR L progCap
    · refine (Nat.le_zero.mpr ?_).trans (Nat.zero_le _)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (iff_of_true (mem_hwTargetBad_fillK (s := (q.2.1, q.2.2.1, q.2.2.2.2)) hB hx.2 b)
        hB)
    · exact card_filter_le_of_imp (card_flip_readK_bad_le (L := L) (N := progCap) (T := 2 ^ 68)
        (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2.2) hπ hB (hsupp q h0) hx.2 hx.1)
        fun b hb ↦ by
          by_contra hn
          exact hb (iff_of_false hn hB)
  · positivity

/-- **The empty-cell term of a `k'` read for `BadR`** (as `keepE_readK_le`). -/
theorem keepE_readK'_le (L : HonestTable) (hπ : PermGood L.perm 18) (x : X)
    (upd : Mem → Option Z → Mem) {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    keepE (BadR L progCap) (.readK' x upd) σ ≤ (2 ^ 301 : ℝ)⁻¹ * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  rw [htr, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases h0 : σ q q = 0
  · exact le_of_eq (by rw [h0, Complex.zero_re, mul_zero, mul_zero])
  refine mul_le_mul_of_nonneg_right ?_ (hre q)
  split_ifs with hx
  · refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) (Nat.cast_nonneg _))
      (cap_div_card_Z_le capK'_le)
    unfold flipCnt
    by_cases hB : q.2 ∈ BadR L progCap
    · refine (Nat.le_zero.mpr ?_).trans (Nat.zero_le _)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (iff_of_true (mem_hwTargetBad_fillK' (s := (q.2.1, q.2.2.1, q.2.2.2.2)) hB hx.2 b)
        hB)
    · exact card_filter_le_of_imp (card_flip_readK'_bad_le (L := L) (N := progCap) (T := 2 ^ 68)
        (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2.2) hπ hB (hsupp q h0) hx.2 hx.1)
        fun b hb ↦ by
          by_contra hn
          exact hb (iff_of_false hn hB)
  · positivity

/-- **The refined cost of a template `k` read**: at most `kapRR tr σ` (`readCost_le_of_keep`). -/
theorem readCost_readKPort_le (L : HonestTable) (hπ : PermGood L.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    readCost (BadR L progCap) (readKPort x) σ ≤ ENNReal.ofReal (kapRR * σ.trace.re) :=
  readCost_le_of_keep (BadR L progCap) (readKPort x) (fun _ _ ↦ rfl) hσ (by positivity)
    (keepE_readK_le L hπ x _ hσ hsupp)

/-- **The refined cost of a template `k'` read**: at most `kapRR tr σ`. -/
theorem readCost_readK'Port_le (L : HonestTable) (hπ : PermGood L.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    readCost (BadR L progCap) (readK'Port x) σ ≤ ENNReal.ofReal (kapRR * σ.trace.re) :=
  readCost_le_of_keep (BadR L progCap) (readK'Port x) (fun _ _ ↦ rfl) hσ (by positivity)
    (keepE_readK'_le L hπ x _ hσ hsupp)

end ports

/-! ## The event bound with the refined read cost -/

section event

attribute [local instance] badRDec

/-- **The refined read cost** for `BadR L progCap` (ReadCost's `readCostT`: `⊤` off `ReadNoBot`). -/
noncomputable def dRref (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  readCostT (BadR L progCap) c σ

/-- **The prefix's classical costs with the refined read cost** (record ports free). -/
noncomputable def twPR (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (dRref L) (dPof L))) (prefixR A L)
    initR

/-- The empty-cell flips of the trial reads, summed along the prefix. -/
noncomputable def encRPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (encRW L) fun _ _ ↦ 0)) (prefixR A L)
    initR

/-- The hardwired classical moves of the trial reads, summed along the prefix. -/
noncomputable def hwMovePre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (hwMoveW L) fun _ _ ↦ 0))
    (prefixR A L) initR

/-- **The `RecBad` mass of the trial reads, summed along the prefix** (beside RestMass's
`cwRecPre`). -/
noncomputable def recBadPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (recBadW L) fun _ _ ↦ 0))
    (prefixR A L) initR

/-- The flip costs of the prefix's program ports (Security's `progPre`). -/
noncomputable def progPreR (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (dPof L)))
    (prefixR A L) initR

/-- **The remaining averaged bound** for the new recorded mass (the `RecBad` analogue of RestMass's
`uavg_cwRecPre_le`): over the tables of a good set, the average of `recBadPre` is at most `τ`. -/
def RecBadAvg (A : Adversary (X × Z)) (good : HonestTable → Prop) [DecidablePred good]
    (τ : ℝ≥0∞) : Prop :=
  uavg (fun L ↦ if good L then recBadPre A L else 0) ≤ τ

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The event bound at the end of the challenge prefix, with the refined read cost**
(`eventWeight_runtimeR_le` with ReadCost's `potential_hwReadKraus_le_refinedT`). -/
theorem ewPrefix_le_ref (L : HonestTable) (hπ : PermGood L.perm 18) :
    (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (prefixR A L) initR ≤
      (advTerm q + twPR A L ^ (2⁻¹ : ℝ)) ^ 2 :=
  eventWeight_runtimeR_le (q := 6 * q) (K := clsCap) (BadR L progCap) (labelFree_badR L progCap)
    (fun W m ↦ upClosed_slice_bad W m.2) m0R (empty_not_mem_bad m0) advEps
    (fun n _ ↦ advEps_ne_top n)
    (fun n _ W m ↦ freshBound_slice_badR L hπ (n + clsCap + 1) W m)
    (dRref L) (dPof L)
    (fun c σ hσ ↦ potential_hwReadKraus_le_refinedT (BadR L progCap) c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadR L progCap) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    .instruments (prefixR A L) (advCalls_prefixR hperm hsign L) (clsCalls_prefixR hperm hsign L)
    (SubState.basis ())

/-- **The event bound over the whole game from a bound at the end of the prefix** (EventSqrt's
`ewR_le_sqrt` for any prefix cost `T`): if the prefix's event weight is at most
`(advTerm q + √T)²`, then `ewR (gameR A) L ≤ (advTerm q + verTerm q + √(T + verLin q))²`. -/
theorem ewR_le_sqrt_of_prefix (L : HonestTable) (hπ : PermGood L.perm 18) {T : ℝ≥0∞}
    (hpreT : (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (prefixR A L)
      initR ≤ (advTerm q + T ^ (2⁻¹ : ℝ)) ^ 2) :
    ewR (gameR A) L ≤ (advTerm q + verTerm q + (T + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hρa := fun a ↦ ((runtimeR m0R).run₂ .instruments (prefixR A L)).posSemidef_branch_apply a
    initR_posSemidef
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1)
    (fun _ ↦ 1) (querySupportedOn_runtimeR_step m0R) .instruments (calls_prefixR hperm hsign L)
    querySupportedOn_initR ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR m0R .instruments (prefixR A L) (SubState.basis ()).matrix
    ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le (BadR L progCap)
    (fun W m ↦ upClosed_slice_bad W m.2) m0R (N := 6 * q + clsCap + 3 * verifyBlocks)
    (verEps_ne_top q) (fun W m ↦ freshBound_slice_badR L hπ _ W m) .instruments
    (realizeT (valueAt L) (verifyT Selections (pubOf L) a))
    (chg_verifyT_one (pubOf L) (valueAt L) a) (chg_verifyT_nonKeep (pubOf L) (valueAt L) a)
    (t := 0 + (6 * q + clsCap)) (by omega) (hρa a) (hga a) (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a
      initR).trace.re ≤ 1 :=
    (((runtimeR m0R).run₂ .instruments (prefixR A L)).isCPTNIFamily.tsum_ofReal_trace_re_le
      initR_posSemidef).trans ofReal_trace_initR_le_one
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0R) .instruments
    (hwProjector (BadR L progCap)) (prefixR A L) initR
  have hm : ∑' j, (∑' a, (if j < 3 * verifyBlocks then verEps q else 0) *
      ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a
        initR).trace.re) ^ (2⁻¹ : ℝ) ≤ verTerm q := by
    calc _ ≤ ∑' j, ((if j < 3 * verifyBlocks then verEps q else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTerm q := by
          unfold verTerm
          rw [tsum_rpow_inv_two_ite, mul_one]
  have ht : ∑' a, (potential (hwProjector (BadR L progCap))
      (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a initR) +
      ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps q) *
        ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a
          initR).trace.re) ≤
      (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (prefixR A L) initR +
        verLin q := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps q) * _
        ≤ ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps q) * 1 := by
          gcongr
      _ = verLin q := mul_one _
  have hpre' : ((runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap))
      (prefixR A L) initR + verLin q) ^ (2⁻¹ : ℝ) ≤
      advTerm q + (T + verLin q) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := advTerm q ^ 2) (δ := 0) (C := verLin q)
      (b := T) (a := (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap))
        (prefixR A L) initR) (by
          rw [pow_two_rpow_inv_two, add_zero, add_comm]
          exact hpreT)
    rwa [pow_two_rpow_inv_two, zero_add] at h
  have hew : ewR (gameR A) L = ∑' a, (runtimeR m0R).eventWeight .instruments
      (hwProjector (BadR L progCap)) (realizeT (valueAt L) (verifyT Selections (pubOf L) a))
      (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a initR) := by
    unfold ewR
    rw [gameR_eq]
    exact eventWeight_bind₂ (runtimeR m0R) .instruments (hwProjector (BadR L progCap))
      (prefixR A L) _ initR_posSemidef
  have hfin : ewR (gameR A) L ^ (2⁻¹ : ℝ) ≤
      advTerm q + verTerm q + (T + verLin q) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap))
          (prefixR A L) initR + verLin q) ^ (2⁻¹ : ℝ) + verTerm q :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ advTerm q + (T + verLin q) ^ (2⁻¹ : ℝ) + verTerm q := add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

/-- **The event bound over the whole game with the refined read cost**: on a `PermGood` table,
`ewR (gameR A) L ≤ (advTerm q + verTerm q + √(twPR A L + verLin q))²`. -/
theorem ewR_le_sqrt_ref (L : HonestTable) (hπ : PermGood L.perm 18) :
    ewR (gameR A) L ≤ (advTerm q + verTerm q + (twPR A L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 :=
  ewR_le_sqrt_of_prefix hperm hsign L hπ (ewPrefix_le_ref hperm hsign L hπ)

omit hperm hsign in
/-- **The refined cost of a read port at the prefix's calls, linearized**: for every `s > 0`, at
most `(1 + s) aRW + (1 + 1/s) pRW` (trial reads: `readCost_trial_le`; the other reads are `k`, `k'`
reads keeping the memory: `kapRR tr σ`). -/
theorem dRref_le_prefix (hq : q ≤ 2 ^ 64) (L : HonestTable) (hπ : PermGood L.perm 18)
    (c : HwRead X Z Mem) {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) (hI : PreInv q (.inl (.inl (.inr c))) σ) {s : ℝ} (hs : 0 < s) :
    dRref L c σ ≤ ENNReal.ofReal (1 + s) * aRW L c σ + ENNReal.ofReal (1 + s⁻¹) * pRW L c σ := by
  have hnb : ReadNoBot c σ := readNoBot_of_noBot c hI.2.2
  have hR : dRref L c σ = readCost (BadR L progCap) c σ := by
    unfold dRref readCostT
    rw [ite_eq_left hnb]
  rw [hR]
  by_cases ht : IsTrial trialUpd c
  · exact readCost_trial_le L ht hσ hs
  have hsupp : ∀ a, σ a a ≠ 0 → progCap + dbGrade a.2.1 ≤ 2 ^ 68 := fun a h0 ↦ by
    have h1 : dbGrade a.2.1 ≤ nD q := (hI.2.1 a a h0).1.1
    have h2 := progCap_add_le hq
    unfold nD at h1
    omega
  have hk : readCost (BadR L progCap) c σ ≤ ENNReal.ofReal (kapRR * σ.trace.re) := by
    rcases readOk_of_okCharge hI.1 with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ht'
    · exact readCost_readKPort_le L hπ x hσ hsupp
    · exact readCost_readK'Port_le L hπ x hσ hsupp
    · exact absurd ht' ht
  refine hk.trans (le_trans ?_ le_self_add)
  refine (le_add_self).trans (le_mul_of_one_le_left zero_le ?_)
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **The prefix's refined classical costs**: on a `PermGood` table, for `q ≤ 2^64`,
`twPR ≤ (√(2 encRPre + hwMovePre + kapRR clsCap) + √(cwRecPre + recBadPre))² + progPreR`. The
cross terms pair the empty-cell flips only with the flip-value recorded mass: RestMass's codeword
recorded mass `cwRecPre` and `recBadPre`. -/
theorem twPR_le (hq : q ≤ 2 ^ 64) (L : HonestTable) (hπ : PermGood L.perm 18) :
    twPR A L ≤ ((2 * encRPre A L + hwMovePre A L + ENNReal.ofReal kapRR * clsCap) ^ (2⁻¹ : ℝ) +
      (cwRecPre A L + recBadPre A L) ^ (2⁻¹ : ℝ)) ^ 2 + progPreR A L := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  set wa : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (aRW L) fun _ _ ↦ 0)
  set wp : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (pRW L) fun _ _ ↦ 0)
  set wg : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ _ ↦ 0) (dPof L))
  -- The linear charge along the prefix.
  have ha : (runtimeR m0R).totalWeight .instruments wa (prefixR A L) initR ≤
      2 * encRPre A L + hwMovePre A L + ENNReal.ofReal kapRR * clsCap := by
    refine (totalWeight_le_lin (runtimeR m0R) .instruments wa
      (extWeight (hwCost (encRW L) fun _ _ ↦ 0)) (extWeight (hwCost (hwMoveW L) fun _ _ ↦ 0))
      (fun i σ ↦ ENNReal.ofReal kapRR * extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
        fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ) 2 1 (fun i σ _ ↦ ?_) (prefixR A L)
      initR_posSemidef).trans ?_
    · rcases i with ((p | c) | c) | T
      · exact zero_le
      · show aRW L c σ ≤ 2 * encRW L c σ + 1 * hwMoveW L c σ +
          ENNReal.ofReal kapRR * ENNReal.ofReal σ.trace.re
        exact le_of_eq (by rw [one_mul, ← ENNReal.ofReal_mul kapRR_nonneg]; rfl)
      · exact zero_le
      · exact zero_le
    · rw [one_mul]
      refine add_le_add le_rfl ((le_of_eq (totalWeight_const_mul_weight (runtimeR m0R)
        .instruments (ENNReal.ofReal kapRR) _ (prefixR A L) initR)).trans
        (mul_le_mul_of_nonneg_left
          (totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L)) zero_le))
  -- The flip-value recorded mass along the prefix.
  have hp : (runtimeR m0R).totalWeight .instruments wp (prefixR A L) initR ≤
      cwRecPre A L + recBadPre A L := by
    refine (totalWeight_le_add (runtimeR m0R) .instruments wp
      (extWeight (hwCost (cwRecW Prod.snd trialUpd) fun _ _ ↦ 0))
      (extWeight (hwCost (recBadW L) fun _ _ ↦ 0)) 1 1 (fun i σ _ ↦ ?_) (prefixR A L)
      initR_posSemidef).trans_eq ?_
    · rcases i with ((p | c) | c) | T
      · exact zero_le
      · show pRW L c σ ≤ 1 * cwRecW Prod.snd trialUpd c σ + 1 * recBadW L c σ
        exact le_of_eq (by rw [one_mul, one_mul]; rfl)
      · exact zero_le
      · exact zero_le
    · rw [one_mul, one_mul]
      rfl
  refine le_sq_add_of_forall_lin fun s hs ↦ ?_
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w' := fun i σ ↦ ENNReal.ofReal (1 + s) * wa i σ + ENNReal.ofReal (1 + s⁻¹) * wp i σ + wg i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef hx).trans ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · show dRref L c σ ≤ ENNReal.ofReal (1 + s) * aRW L c σ +
        ENNReal.ofReal (1 + s⁻¹) * pRW L c σ + 0
      rw [add_zero]
      exact dRref_le_prefix hq L hπ c hσ hI hs
    · show dPof L c σ ≤ ENNReal.ofReal (1 + s) * 0 + ENNReal.ofReal (1 + s⁻¹) * 0 + dPof L c σ
      simp only [mul_zero, zero_add, le_refl]
    · exact zero_le
  · refine (totalWeight_le_lin (runtimeR m0R) .instruments _ wa wp wg (ENNReal.ofReal (1 + s))
      (ENNReal.ofReal (1 + s⁻¹)) (fun _ _ _ ↦ le_rfl) (prefixR A L) initR_posSemidef).trans ?_
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha zero_le)
      (mul_le_mul_of_nonneg_left hp zero_le)) le_rfl

end event

end Quantum.Xmss.Assembly

end
