module

public import Quantum.Xmss.Assembly.CostRefined
public import Quantum.Sphincs.Assembly.CostRun
public import Quantum.Sphincs.Assembly.EncPorts

@[expose] public section

/-!
# leanSPHINCS's challenge prefix: classical costs with the refined read cost

leanXMSS's `Quantum.Xmss.Assembly.CostRefined` on CostRun's canonical prefix `prefixR pol A p v`
at the template data `(p, v)` (contract C4), for every digest policy. Its generic part (namespace
`Quantum.Sponge`: an `h` read linearized, `RecFlip`, `readHA`, `readHP`,
`readCost_readH_le_lin`) and the constant `kapRR` are reused. The read ports are priced with
ReadCost's refined cost `readCostT` (`dRref`); the prefix's total `twPR` splits with the cross term
on the flip-value recorded mass only.

* **The trials' recorded flips** (`recFlip_trial`): at a trial read a recorded flip is
  codeword-recorded for the trial's unselected key (`CwRec`: the memory moves only by a codeword
  selection, Events' `cwSel`) or a recorded value that puts the state into `BadR` (`RecBad`). A
  trial read port, linearized (`readCost_trial_le`): `(1 + s) aRW + (1 + 1/s) pRW` with
  `aRW = 2 encRW + hwMoveW + kapRR tr σ` and `pRW = cwRecW + recBadW` (EncPotential's `cwRecW`).
* **The `k`, `k'` reads** (`keepE_readK_le`, `keepE_readK'_le`, `readCost_readKPort_le`,
  `readCost_readK'Port_le`): they keep the memory; CostRun's capacity-scale counts give
  `keepE ≤ 2^-301 tr σ`, so the refined cost is at most `kapRR tr σ`.
* **The invariant at the prefix's calls** (`PreInv`, `forallQueries_preInv`): EncPorts' `PortInv`
  for CostRun's `ReadOk` reads at database grade `6q + clsCap` and hardwired grade `progCap`
  (`chgB_prefixR`, GameR's call counts).
* **The prefix** (`twPR_le`): at data with `PermGood π 18`, for `q ≤ 2^64`,
  `twPR ≤ (√(2 encRPre + hwMovePre + kapRR clsCap) + √(cwRecPre + recBadPre))² + progPreR`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open Quantum.Xmss (X Z trunc128)
open Quantum.Xmss.Hybrid (totalWeight_const_mul_weight)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR extWeight extCls kapRR kapRR_nonneg
  two_div_card_X_le_kapRR cap_div_card_Z_le readCost_le_of_keep totalWeight_le_lin
  totalWeight_le_add le_sq_add_of_forall_lin totalWeight_le_of_forallQueries card_filter_le_of_imp
  isChargeBound_mono_charge)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default
size. -/
set_option synthInstance.maxSize 2000

/-! ## The ports of the prefix -/

section ports

/-- **A recorded value that puts the state into the event**: the cell `z` recorded, not hardwired,
the state in `BadR`, the state with the cell emptied not. -/
def RecBad (p : Pub) (v : (s : HPos) → XD s) (z : Z) (s : HwReg X Z (Mem HPos)) : Prop :=
  s.2.1.1 z = none ∧ s.1.1 z ≠ none ∧ s ∈ BadR p v progCap ∧
    ((Function.update s.1.1 z none, s.1.2), s.2) ∉ BadR p v progCap

open scoped Classical in
/-- **The `RecBad` mass of a trial read port** (`0` at the other read ports). -/
noncomputable def recBadW (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal (∑ q, if RecBad p v (trialOf trialUpd c).1 q.2 then
    (σ q q).re else 0) else 0

/-- **The codeword-recorded states of a trial read** at the cell `z` of the trial `t`: not
hardwired, the trial's key unselected, recorded with a value selecting it (EncPotential's `cwRecW`
integrand). -/
def CwRec (z : Z) (t : TrialPt) (s : HwReg X Z (Mem HPos)) : Prop :=
  s.2.1.1 z = none ∧ s.2.2.2 t.K = none ∧
    ∃ y, s.1.1 z = some y ∧ Codeword.Valid (trunc128 (t.xi + y))

/-- The empty-cell flips of a trial read: the values that flip `BadR` when read, over `|X|`. -/
noncomputable def encRSum (p : Pub) (v : (s : HPos) → XD s) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ :=
  ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z = none then
    ((Finset.univ.filter (hFlip (BadR p v progCap) z (trialUpd t) q)).card : ℝ) /
      Fintype.card X else 0) * (σ q q).re

/-- The hardwired classical moves of a trial read into `BadR`. -/
noncomputable def hwMoveSum (p : Pub) (v : (s : HPos) → XD s) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ :=
  ∑ q, (if q.2.2.1.1 z ≠ none ∧ hCls (BadR p v progCap) (trialUpd t) (q.2.2.1.1 z) q then 1
    else 0) * (σ q q).re

open scoped Classical in
/-- **The empty-cell flips of a trial read port** (`encRSum`; `0` at the other read ports). -/
noncomputable def encRW (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then
    ENNReal.ofReal (encRSum p v (trialOf trialUpd c).1 (trialOf trialUpd c).2 σ) else 0

open scoped Classical in
/-- **The hardwired classical moves of a trial read port** (`hwMoveSum`; `0` elsewhere). -/
noncomputable def hwMoveW (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then
    ENNReal.ofReal (hwMoveSum p v (trialOf trialUpd c).1 (trialOf trialUpd c).2 σ) else 0

/-- **The linear charge of a read port**: `2 encRW + hwMoveW + kapRR tr σ`. -/
noncomputable def aRW (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  2 * encRW p v c σ + hwMoveW p v c σ + ENNReal.ofReal (kapRR * σ.trace.re)

/-- **The flip-value recorded mass of a read port**: EncPotential's `cwRecW` plus `recBadW`. -/
noncomputable def pRW (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  cwRecW Prod.snd trialUpd c σ + recBadW p v c σ

/-- **A recorded flip at a trial read is codeword-recorded or `RecBad`.** The memory moves only by
a codeword selection of the unselected key (`cwUpd`); a recorded value that flips the event against
the emptied cell puts the state into `BadR` (filling an empty cell keeps the event: `mem_bad_fill`).
-/
theorem recFlip_trial (p : Pub) (v : (s : HPos) → XD s) (t : TrialPt) (z : Z)
    (q : Unit × HwReg X Z (Mem HPos)) (hW : q.2.2.1.1 z = none)
    (h : RecFlip (BadR p v progCap) z (trialUpd t) q) : CwRec z t q.2 ∨ RecBad p v z q.2 := by
  obtain ⟨y, hy, h | ⟨u, hu⟩⟩ := h
  · have hfill : ((Function.update q.2.1.1 z none, q.2.1.2), q.2.2) ∈ BadR p v progCap →
        q.2 ∈ BadR p v progCap := by
      intro hb
      have h2 := mem_bad_fill (S := HPos) (d := evData p v) (N := progCap)
        (D := (Function.update q.2.1.1 z none, q.2.1.2)) (W := q.2.2.1) (m := q.2.2.2)
        (z := z) hb (by simp) (some y) q.2.2.2.1 q.2.2.2.2 fun _ _ h ↦ h
      have h3 : Function.update (Function.update q.2.1.1 z none) z (some y) = q.2.1.1 := by
        rw [Function.update_idem, ← hy, Function.update_eq_self]
      dsimp only at h2
      rw [h3] at h2
      exact h2
    by_cases hq : q.2 ∈ BadR p v progCap
    · exact .inr ⟨hW, by rw [hy]; exact Option.some_ne_none y, hq,
        fun hb ↦ h (iff_of_true hq hb)⟩
    · exact absurd (iff_of_false hq fun hb ↦ hq (hfill hb)) h
  · have key : ¬ (q.2.2.2.2 t.K = none ∧ Codeword.Valid (trunc128 (t.xi + y))) →
        trialUpd t q.2.2.2 (some y) = q.2.2.2 := by
      intro hc
      show (q.2.2.2.1, cwUpd t.K t.x t.xi q.2.2.2.2 (some y)) = q.2.2.2
      have h0 : cwUpd t.K t.x t.xi q.2.2.2.2 (some y) = q.2.2.2.2 := by
        show (if q.2.2.2.2 t.K = none then cwSel q.2.2.2.2 t.K t.x t.xi y else q.2.2.2.2) = _
        split_ifs with hn
        · unfold cwSel
          exact ite_eq_right fun hv ↦ hc ⟨hn, hv⟩
        · rfl
      rw [h0]
    have hk : q.2.2.2.2 t.K = none ∧ Codeword.Valid (trunc128 (t.xi + y)) := by
      by_contra hc
      apply hu
      rw [key hc]
    exact .inl ⟨hW, hk.1, y, hy, hk.2⟩

/-- **A trial read port, linearized**: for every `s > 0` its refined cost is at most
`(1 + s) aRW + (1 + 1/s) pRW` (`readCost_readH_le_lin`, `recFlip_trial`). -/
theorem readCost_trial_le (p : Pub) (v : (s : HPos) → XD s) {c : HwRead X Z (Mem HPos)}
    (ht : IsTrial trialUpd c)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) {s : ℝ} (hs : 0 < s) :
    readCost (BadR p v progCap) c σ ≤
      ENNReal.ofReal (1 + s) * aRW p v c σ + ENNReal.ofReal (1 + s⁻¹) * pRW p v c σ := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  have hc := eq_readH_trialOf trialUpd ht
  simp only [aRW, pRW, encRW, hwMoveW, cwRecW, recBadW, ht, ↓reduceIte]
  generalize trialOf trialUpd c = zt at hc ⊢
  subst hc
  obtain ⟨z, t⟩ := zt
  refine (readCost_readH_le_lin (BadR p v progCap) z (trialUpd t) hσ hs).trans
    (add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) (mul_le_mul_of_nonneg_left ?_ zero_le))
  · have hkey : readHA (BadR p v progCap) z (trialUpd t) σ ≤
        2 * encRSum p v z t σ + hwMoveSum p v z t σ + kapRR * σ.trace.re := by
      rw [htr]
      unfold readHA encRSum hwMoveSum
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun q _ ↦ ?_
      have h2 := mul_le_mul_of_nonneg_right two_div_card_X_le_kapRR (hre q)
      have hk := mul_nonneg kapRR_nonneg (hre q)
      by_cases hW : q.2.2.1.1 z = none
      · have hn : ¬ (q.2.2.1.1 z ≠ none ∧
            hCls (BadR p v progCap) (trialUpd t) (q.2.2.1.1 z) q) := fun h ↦ h.1 hW
        rw [ite_eq_right hn, zero_mul, add_zero]
        by_cases hD : q.2.1.1 z = none
        · simp only [ite_eq_left hW, ite_eq_left hD, ite_eq_left (And.intro hW hD)]
          have e : (2 * ((Finset.univ.filter
              (hFlip (BadR p v progCap) z (trialUpd t) q)).card : ℝ) + 2) / Fintype.card X *
                (σ q q).re = 2 * (((Finset.univ.filter
                  (hFlip (BadR p v progCap) z (trialUpd t) q)).card : ℝ) / Fintype.card X *
                    (σ q q).re) + 2 / Fintype.card X * (σ q q).re := by ring
          rw [e]
          linarith
        · simp only [ite_eq_left hW, ite_eq_right hD, ite_eq_right fun h : _ ∧ _ ↦ hD h.2,
            zero_mul, mul_zero, zero_add]
          exact h2
      · simp only [ite_eq_right hW, ite_eq_right fun h : _ ∧ _ ↦ hW h.1, zero_mul, mul_zero,
          zero_add]
        have he : (if hCls (BadR p v progCap) (trialUpd t) (q.2.2.1.1 z) q then (1 : ℝ) else 0) =
            if q.2.2.1.1 z ≠ none ∧ hCls (BadR p v progCap) (trialUpd t) (q.2.2.1.1 z) q then 1
              else 0 := by
          by_cases hcl : hCls (BadR p v progCap) (trialUpd t) (q.2.2.1.1 z) q
          · rw [ite_eq_left hcl, ite_eq_left ⟨hW, hcl⟩]
          · rw [ite_eq_right hcl, ite_eq_right fun h ↦ hcl h.2]
        rw [he]
        linarith
    have he0 : 0 ≤ encRSum p v z t σ := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      split_ifs
      exacts [div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), le_rfl]) (hre q)
    have hm0 : 0 ≤ hwMoveSum p v z t σ := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
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
    by_cases hp : q.2.2.1.1 z = none ∧ RecFlip (BadR p v progCap) z (trialUpd t) q
    · rw [ite_eq_left hp, one_mul]
      have h := recFlip_trial p v t z q hp.1 hp.2
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

/-- **The empty-cell term of a `k` read for `BadR`**: on states with at most `2^68 - progCap`
database entries per function, `keepE ≤ 2^-301 tr σ` (`card_flip_readK_bad_le`; inside `BadR` a
filled cell stays inside). -/
theorem keepE_readK_le (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) (x : X)
    (upd : Mem HPos → Option Z → Mem HPos)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    keepE (BadR p v progCap) (.readK x upd) σ ≤ (2 ^ 301 : ℝ)⁻¹ * σ.trace.re := by
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
    by_cases hB : q.2 ∈ BadR p v progCap
    · refine (Nat.le_zero.mpr ?_).trans (Nat.zero_le _)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (iff_of_true (mem_bad_fillK (s := q.2) hB hx.2 b) hB)
    · exact card_filter_le_of_imp (card_flip_readK_bad_le (d := evData p v) (N := progCap)
        (T := 2 ^ 68) (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hπ hB (hsupp q h0) hx.2 hx.1)
        fun b hb ↦ by
          by_contra hn
          exact hb (iff_of_false hn hB)
  · positivity

/-- **The empty-cell term of a `k'` read for `BadR`** (as `keepE_readK_le`). -/
theorem keepE_readK'_le (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) (x : X)
    (upd : Mem HPos → Option Z → Mem HPos)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    keepE (BadR p v progCap) (.readK' x upd) σ ≤ (2 ^ 301 : ℝ)⁻¹ * σ.trace.re := by
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
    by_cases hB : q.2 ∈ BadR p v progCap
    · refine (Nat.le_zero.mpr ?_).trans (Nat.zero_le _)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (iff_of_true (mem_bad_fillK' (s := q.2) hB hx.2 b) hB)
    · exact card_filter_le_of_imp (card_flip_readK'_bad_le (d := evData p v) (N := progCap)
        (T := 2 ^ 68) (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hπ hB (hsupp q h0) hx.2 hx.1)
        fun b hb ↦ by
          by_contra hn
          exact hb (iff_of_false hn hB)
  · positivity

/-- **The refined cost of a template `k` read**: at most `kapRR tr σ` (`readCost_le_of_keep`). -/
theorem readCost_readKPort_le (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    readCost (BadR p v progCap) (readKPort x) σ ≤ ENNReal.ofReal (kapRR * σ.trace.re) :=
  readCost_le_of_keep (BadR p v progCap) (readKPort x) (fun _ _ ↦ rfl) hσ (by positivity)
    (keepE_readK_le p v hπ x _ hσ hsupp)

/-- **The refined cost of a template `k'` read**: at most `kapRR tr σ`. -/
theorem readCost_readK'Port_le (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18)
    (x : X) {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    readCost (BadR p v progCap) (readK'Port x) σ ≤ ENNReal.ofReal (kapRR * σ.trace.re) :=
  readCost_le_of_keep (BadR p v progCap) (readK'Port x) (fun _ _ ↦ rfl) hσ (by positivity)
    (keepE_readK'_le p v hπ x _ hσ hsupp)

end ports

/-! ## The costs along the prefix -/

section costs

/-- **The refined read cost** for `BadR p v progCap` (ReadCost's `readCostT`: `⊤` off
`ReadNoBot`). -/
noncomputable def dRref (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  readCostT (BadR p v progCap) c σ

/-- **The prefix's classical costs with the refined read cost** (record ports free). -/
noncomputable def twPR (pol : DigestPolicy) (A : SAdversary) (p : Pub) (v : (s : HPos) → XD s) :
    ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (dRref p v) (dPof p v)))
    (prefixR pol A p v) initR

/-- The empty-cell flips of the trial reads, summed along the prefix. -/
noncomputable def encRPre (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (encRW p v) fun _ _ ↦ 0))
    (prefixR pol A p v) initR

/-- The hardwired classical moves of the trial reads, summed along the prefix. -/
noncomputable def hwMovePre (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (hwMoveW p v) fun _ _ ↦ 0))
    (prefixR pol A p v) initR

/-- **The codeword-recorded mass of the trials' selecting reads, summed along the prefix**
(EncPotential's `cwRecW`). -/
noncomputable def cwRecPre (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments
    (extWeight (hwCost (cwRecW Prod.snd trialUpd) fun _ _ ↦ 0)) (prefixR pol A p v) initR

/-- **The `RecBad` mass of the trial reads, summed along the prefix** (beside `cwRecPre`). -/
noncomputable def recBadPre (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (recBadW p v) fun _ _ ↦ 0))
    (prefixR pol A p v) initR

/-- The flip costs of the prefix's program ports. -/
noncomputable def progPreR (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (dPof p v)))
    (prefixR pol A p v) initR

/-- **The invariant at the prefix's calls**: EncPorts' `PortInv` for CostRun's `ReadOk` reads, at
database grade `6q + clsCap` and hardwired grade `progCap` (no decompressed `⊥`). -/
def PreInv (q : ℕ) (i : (recHwSpec X Z HPos Selections).Port)
    (τ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ) : Prop :=
  PortInv ReadOk (6 * q + clsCap) progCap m0R i τ

/-- EncPorts' port charge of `ReadOk` is at most CostRun's `bR`. -/
theorem okChg_readOk_le_bR (i : (recHwSpec X Z HPos Selections).Port) :
    okChg ReadOk i ≤ bR i := by
  rcases i with ((i | c) | c) | T
  · unfold okChg
    split_ifs with h
    · exact Nat.zero_le _
    · exact absurd trivial h
  · show okChg ReadOk (.inl (.inl (.inr c))) ≤ okCharge c
    by_cases h : ReadOk c
    · rw [okCharge_eq_zero h]
      unfold okChg
      rw [ite_eq_left (show OkPort ReadOk (.inl (.inl (.inr c))) from h)]
    · unfold okChg okCharge
      rw [ite_eq_right h]
      split_ifs <;> omega
  · unfold okChg
    split_ifs with h
    · exact Nat.zero_le _
    · exact absurd trivial h
  · unfold okChg
    split_ifs with h
    · exact Nat.zero_le _
    · exact absurd trivial h

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The invariant holds at every call of the prefix** (EncPorts' `forallQueries_portInv` with
GameR's call counts and `chgB_prefixR`), for every digest policy and template data. -/
theorem forallQueries_preInv (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    ∃ P : ∀ (i : (recHwSpec X Z HPos Selections).Port) (E : QReg),
      Matrix (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E)
        (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E) ℂ →
          Prop, (∀ i E σ, P i E σ → PreInv q i (MatrixMap.traceRight _ E σ)) ∧
      (runtimeR m0R).ForallQueries .instruments P (prefixR pol A p v) initR :=
  forallQueries_portInv ReadOk m0R .instruments () (prefixR pol A p v)
    (advCalls_prefixR hperm hsign pol p v) (clsCalls_prefixR hperm hsign pol p v)
    (isChargeBound_mono_charge (fun _ a ↦ by
      rcases a with o | ⟨i, E, ℓ⟩
      · exact le_rfl
      · exact okChg_readOk_le_bR i) (chgB_prefixR pol A p v))
    (progCalls_prefixR hperm hsign pol p v)

omit hperm hsign in
/-- **The refined cost of a read port at the prefix's calls, linearized**: for every `s > 0`, at
most `(1 + s) aRW + (1 + 1/s) pRW` (trial reads: `readCost_trial_le`; the other reads are `k`, `k'`
reads keeping the memory: `kapRR tr σ`). -/
theorem dRref_le_prefix (hq : q ≤ 2 ^ 64) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) (c : HwRead X Z (Mem HPos))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hI : PreInv q (.inl (.inl (.inr c))) σ) {s : ℝ} (hs : 0 < s) :
    dRref p v c σ ≤
      ENNReal.ofReal (1 + s) * aRW p v c σ + ENNReal.ofReal (1 + s⁻¹) * pRW p v c σ := by
  have hnb : ReadNoBot c σ := readNoBot_of_noBot c hI.2.2
  have hR : dRref p v c σ = readCost (BadR p v progCap) c σ := by
    unfold dRref readCostT
    rw [ite_eq_left hnb]
  rw [hR]
  by_cases ht : IsTrial trialUpd c
  · exact readCost_trial_le p v ht hσ hs
  have hsupp : ∀ a, σ a a ≠ 0 → progCap + dbGrade a.2.1 ≤ 2 ^ 68 := fun a h0 ↦ by
    have h1 : dbGrade a.2.1 ≤ 6 * q + clsCap := (hI.2.1 a a h0).1.1
    have h2 := progCap_add_le hq
    omega
  have hok : ReadOk c := hI.1
  have hk : readCost (BadR p v progCap) c σ ≤ ENNReal.ofReal (kapRR * σ.trace.re) := by
    rcases hok with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ht'
    · exact readCost_readKPort_le p v hπ x hσ hsupp
    · exact readCost_readK'Port_le p v hπ x hσ hsupp
    · exact absurd ht' ht
  refine hk.trans (le_trans ?_ le_self_add)
  refine (le_add_self).trans (le_mul_of_one_le_left zero_le ?_)
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **The prefix's refined classical costs**: at data with `PermGood π 18`, for `q ≤ 2^64` and every
digest policy,
`twPR ≤ (√(2 encRPre + hwMovePre + kapRR clsCap) + √(cwRecPre + recBadPre))² + progPreR`. The cross
terms pair the empty-cell flips only with the flip-value recorded mass: the codeword-recorded mass
`cwRecPre` and `recBadPre`. -/
theorem twPR_le (hq : q ≤ 2 ^ 64) (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) :
    twPR pol A p v ≤ ((2 * encRPre pol A p v + hwMovePre pol A p v +
      ENNReal.ofReal kapRR * clsCap) ^ (2⁻¹ : ℝ) +
        (cwRecPre pol A p v + recBadPre pol A p v) ^ (2⁻¹ : ℝ)) ^ 2 + progPreR pol A p v := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign pol p v
  set wa : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (aRW p v) fun _ _ ↦ 0)
  set wp : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (pRW p v) fun _ _ ↦ 0)
  set wg : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ _ ↦ 0) (dPof p v))
  -- The linear charge along the prefix.
  have ha : (runtimeR m0R).totalWeight .instruments wa (prefixR pol A p v) initR ≤
      2 * encRPre pol A p v + hwMovePre pol A p v + ENNReal.ofReal kapRR * clsCap := by
    refine (totalWeight_le_lin (runtimeR m0R) .instruments wa
      (extWeight (hwCost (encRW p v) fun _ _ ↦ 0)) (extWeight (hwCost (hwMoveW p v) fun _ _ ↦ 0))
      (fun i σ ↦ ENNReal.ofReal kapRR * extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
        fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ) 2 1 (fun i σ _ ↦ ?_) (prefixR pol A p v)
      initR_posSemidef).trans ?_
    · rcases i with ((sp | c) | c) | T
      · exact zero_le
      · show aRW p v c σ ≤ 2 * encRW p v c σ + 1 * hwMoveW p v c σ +
          ENNReal.ofReal kapRR * ENNReal.ofReal σ.trace.re
        exact le_of_eq (by rw [one_mul, ← ENNReal.ofReal_mul kapRR_nonneg]; rfl)
      · exact zero_le
      · exact zero_le
    · rw [one_mul]
      refine add_le_add le_rfl ((le_of_eq (totalWeight_const_mul_weight (runtimeR m0R)
        .instruments (ENNReal.ofReal kapRR) _ (prefixR pol A p v) initR)).trans
        (mul_le_mul_of_nonneg_left
          (totalWeight_calls_le (prefixR pol A p v) (clsCalls_prefixR hperm hsign pol p v))
          zero_le))
  -- The flip-value recorded mass along the prefix.
  have hp : (runtimeR m0R).totalWeight .instruments wp (prefixR pol A p v) initR ≤
      cwRecPre pol A p v + recBadPre pol A p v := by
    refine (totalWeight_le_add (runtimeR m0R) .instruments wp
      (extWeight (hwCost (cwRecW Prod.snd trialUpd) fun _ _ ↦ 0))
      (extWeight (hwCost (recBadW p v) fun _ _ ↦ 0)) 1 1 (fun i σ _ ↦ ?_) (prefixR pol A p v)
      initR_posSemidef).trans_eq ?_
    · rcases i with ((sp | c) | c) | T
      · exact zero_le
      · show pRW p v c σ ≤ 1 * cwRecW Prod.snd trialUpd c σ + 1 * recBadW p v c σ
        exact le_of_eq (by rw [one_mul, one_mul]; rfl)
      · exact zero_le
      · exact zero_le
    · rw [one_mul, one_mul]
      rfl
  refine le_sq_add_of_forall_lin fun s hs ↦ ?_
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w' := fun i σ ↦ ENNReal.ofReal (1 + s) * wa i σ + ENNReal.ofReal (1 + s⁻¹) * wp i σ + wg i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR pol A p v) initR_posSemidef hx).trans ?_
  · rcases i with ((sp | c) | c) | T
    · exact zero_le
    · show dRref p v c σ ≤ ENNReal.ofReal (1 + s) * aRW p v c σ +
        ENNReal.ofReal (1 + s⁻¹) * pRW p v c σ + 0
      rw [add_zero]
      exact dRref_le_prefix hq p v hπ c hσ hI hs
    · show dPof p v c σ ≤
        ENNReal.ofReal (1 + s) * 0 + ENNReal.ofReal (1 + s⁻¹) * 0 + dPof p v c σ
      simp only [mul_zero, zero_add, le_refl]
    · exact zero_le
  · refine (totalWeight_le_lin (runtimeR m0R) .instruments _ wa wp wg (ENNReal.ofReal (1 + s))
      (ENNReal.ofReal (1 + s⁻¹)) (fun _ _ _ ↦ le_rfl) (prefixR pol A p v)
      initR_posSemidef).trans ?_
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha zero_le)
      (mul_le_mul_of_nonneg_left hp zero_le)) le_rfl

end costs

end Quantum.Sphincs.Assembly

end
