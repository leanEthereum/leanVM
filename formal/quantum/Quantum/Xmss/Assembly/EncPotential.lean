module

public import Quantum.Sponge.Oracle.Hardwired.ReadCost
public import Quantum.Xmss.Assembly.CostJoint

@[expose] public section

/-!
# The cross-key potential of the selecting reads

Security's `encJoint` bounds the joint count of the selecting reads of all trials of all keys by a
diagonal potential argument (CostJoint). This file supplies the potential and the trial-read port.

* **The potential** (`encPot`): on a good union, `∑_{k unselected} msgCwCount(·, k)`; `0` on a bad
  union. Label-free (`encPot_labelFree`), zero at the empty register (`encPot_init`). At a read
  cell `z` and a key `k₀` it splits (`encPot_eq`) into the other keys off `z` (`encA`), the key
  `k₀` off `z` (`encB`, `encOff`) and the indicator of the cell `z` counting for some unselected key
  (`encCSet`; at most one key in a good union, `outAt_unique`).
* **A trial read** (`trialRead_drop_real`, `trialRead_potential_le`): `2^-22 e` plus the potential
  after the read is at most the potential before plus `trialChg`. The other keys keep their part
  (`encA_keep`); the trial's key drops by `ρ_c e` up to `3 p` (CostJoint's
  `survive_readH_weighted_le`, `drop_of_survive`, with the count off the read cell, `OffCell`);
  after the read the cell counts only off `TrialGood` (the key unselected, the trial's block at
  its message slot and the head-tail of `z`: the support invariant of the trial reads), by
  re-compression (`2/|X| + 4/|X|²`) and on the cell's recorded mass (`re_trace_flipOp_le_good`,
  ReadCost's `re_trace_flipOp_le` with reference weight `0`; needs no decompressed `⊥` at the cell).
* **Along a run** (`totalWeight_le_potential_runtimeR_inv`, `totalWeight_cntGW_le`): the joint
  count `cntGW` along a run of `runtimeR` is at most `2^22 (q + P)` plus `2^22` times the charges,
  given the port conditions of the sponge, other read and program ports as hypotheses.
* **Links to CostLift** (`encW_le_cntGW`, `trialChg_le_massW`, `cwRecW_le_massW`): the codeword
  flips are at most `2^-128 cntGW` on grade-capped states; the trial charge is at most
  `(3C + 3) massW + (2/|X| + 4/|X|²) tr σ` where the count is at most `C`; the codeword-recorded mass
  `cwRecW` (the restated `restMass` integrand) is part of `massW`.
-/

universe u v w

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

/-! ## A cell read into an event that its outcome-consistent states avoid -/

namespace Quantum.Sponge

open Quantum

section core

variable {n Y R M0 : Type} [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y]
  [Fintype R] [DecidableEq R] [Fintype M0] [DecidableEq M0]
  {e : n ≃ Option Y × R} {act : R → Prop} [DecidablePred act] {μ : R → M0}
  {τ : Option Y → R → R} {K : Option Y × M0 → Matrix n n ℂ} {idx : n → Option Y × M0}
  {φ : n → n} (S : Set n) [DecidablePred (· ∈ S)]

omit [Fintype n] [DecidableEq n] in
theorem ind_eq_zero_of_not_mem {s : n} (h : s ∉ S) : ind S s = 0 := by
  exact ite_eq_right_of_eq_false _ _ (eq_false h)

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- **A recorded outcome whose own state avoids the event** weighs at most `2/|Y|`: only the
re-compression leaves the outcome's value, with weight `1 - (1 - 1/|Y|)²`. -/
theorem gw_some_le_two_div [Nonempty Y] {y : Y} {r : R}
    (h0 : ind S (e.symm (some y, τ (some y) r)) = 0) :
    gw e τ S (some y) r ≤ 2 / Fintype.card Y := by
  have hN : (1 : ℝ) ≤ Fintype.card Y := by exact_mod_cast Fintype.card_pos
  have hle : ∀ a, cr a (some y) ^ 2 * ind S (e.symm (a, τ (some y) r)) ≤
      cr a (some y) ^ 2 - if a = some y then cr a (some y) ^ 2 else 0 := fun a ↦ by
    by_cases ha : a = some y
    · subst ha
      rw [h0, ite_eq_left rfl]
      simp
    · rw [ite_eq_right ha, sub_zero]
      exact mul_le_of_le_one_right (sq_nonneg _) (ind_le_one S _)
  refine (Finset.sum_le_sum fun a _ ↦ hle a).trans ?_
  rw [Finset.sum_sub_distrib, sum_cr_sq, Finset.sum_ite_eq' Finset.univ (some y),
    ite_eq_left (Finset.mem_univ _)]
  simp only [cr, ↓reduceIte]
  have hinv : (0 : ℝ) ≤ (Fintype.card Y : ℝ)⁻¹ := inv_nonneg.2 (by linarith)
  have h2 : 2 / (Fintype.card Y : ℝ) = 2 * (Fintype.card Y : ℝ)⁻¹ := div_eq_mul_inv _ _
  nlinarith

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- The diagonal weight `gdiag` is at most a bound of the recorded outcomes' weights. -/
theorem gdiag_le_of [Nonempty Y] {r : R} {b : ℝ} (hb : ∀ y, gw e τ S (some y) r ≤ b)
    (o : Option Y) : gdiag e τ S o r ≤ b := by
  rcases o with _ | y
  · show (∑ y, gw e τ S (some y) r) / Fintype.card Y ≤ b
    have hN : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
    rw [div_le_iff₀ hN]
    calc ∑ y, gw e τ S (some y) r ≤ ∑ _y : Y, b := Finset.sum_le_sum fun y _ ↦ hb y
      _ = b * Fintype.card Y := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  · exact hb y

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- The empty-to-recorded weight with the reference `0` is at most the square of a bound of the
recorded outcomes' weights. -/
theorem ew_zero_le_of [Nonempty Y] {t : n} {b : ℝ}
    (hb : ∀ y, gw e τ S (some y) (e t).2 ≤ b) : ew e act τ S (fun _ ↦ 0) t ≤ b ^ 2 := by
  unfold ew
  split_ifs
  · have hN : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
    have hterm : ∀ y, xv e τ S (fun _ ↦ 0) (some y) (e t).2 ^ 2 ≤ b ^ 2 / Fintype.card Y :=
      fun y ↦ by
        simp only [xv, sub_zero, div_pow, Real.sq_sqrt hN.le]
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (gw_nonneg S _ _) (hb y) 2) hN.le
    calc ∑ y, xv e τ S (fun _ ↦ 0) (some y) (e t).2 ^ 2
        ≤ ∑ _y : Y, b ^ 2 / Fintype.card Y := Finset.sum_le_sum fun y _ ↦ hterm y
      _ = b ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  · exact sq_nonneg b

/-- **A read into an event avoided by the outcome-consistent states.** On the states `good`
(on an active rest every outcome `y`'s own state `(y, τ y r)` is outside `S`; on a hardwired one
the classical move is outside `S`), the flip into `S` is at most `2/|Y| + 4/|Y|²`; elsewhere at
most `2`; plus the recorded mass of the active rests. -/
theorem re_trace_flipOp_le_good [Nonempty Y] (h : CellRead e act μ τ K)
    (hc : ClsOff e act K idx φ) (good : n → Prop) [DecidablePred good]
    (hA : ∀ s, good s → act (e s).2 → ∀ y, ind S (e.symm (some y, τ (some y) (e s).2)) = 0)
    (hH : ∀ s, good s → ¬ act (e s).2 → ind S (φ s) = 0)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (hnb : CellNoBot e act σ) :
    (flipOp K S * σ).trace.re ≤ ∑ s, ((if good s then 2 / (Fintype.card Y : ℝ) +
      (2 / (Fintype.card Y : ℝ)) ^ 2 else 2) + pd e act (fun _ _ ↦ True) s) * (σ s s).re := by
  have hre : ∀ s, 0 ≤ (σ s s).re := fun s ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hF := re_trace_flipOp_le S h hc (fun _ ↦ 0) (fun _ _ ↦ True) (fun _ _ _ hy ↦ absurd trivial hy)
    hσ hnb
  set E := ∑ s, ew e act τ S (fun _ ↦ 0) s * (σ s s).re
  set p := ∑ s, pd e act (fun _ _ ↦ True) s * (σ s s).re
  have hE : 0 ≤ E := Finset.sum_nonneg fun s _ ↦ mul_nonneg (by
    unfold ew
    split_ifs
    · exact Finset.sum_nonneg fun y _ ↦ sq_nonneg _
    · exact le_rfl) (hre s)
  have hp : 0 ≤ p := Finset.sum_nonneg fun s _ ↦ mul_nonneg (by
    rcases pd_mem (e := e) (act := act) (fun _ _ ↦ True) s with h0 | h0 <;> rw [h0]; norm_num)
    (hre s)
  have hsq : 2 * (√E * √p) ≤ E + p := by
    nlinarith [sq_nonneg (√E - √p), Real.sq_sqrt hE, Real.sq_sqrt hp]
  have hpt : ∀ s, fd e act τ S φ s + ew e act τ S (fun _ ↦ 0) s ≤
      if good s then 2 / (Fintype.card Y : ℝ) + (2 / (Fintype.card Y : ℝ)) ^ 2 else 2 :=
      fun s ↦ by
    split_ifs with hg
    · have hgw : act (e s).2 → ∀ y, gw e τ S (some y) (e s).2 ≤ 2 / Fintype.card Y :=
        fun ha y ↦ gw_some_le_two_div S (hA s hg ha y)
      refine add_le_add ?_ ?_
      · unfold fd
        split_ifs with ha
        · exact (sub_le_self _ (ind_nonneg S s)).trans (gdiag_le_of S (hgw ha) _)
        · rw [hH s hg ha, zero_sub]
          exact (neg_nonpos.2 (ind_nonneg S s)).trans (by positivity)
      · by_cases ha : act (e s).2
        · exact ew_zero_le_of S (hgw ha)
        · unfold ew
          rw [ite_eq_right fun h' ↦ ha h'.1]
          positivity
    · refine (add_le_add ?_ ?_).trans_eq (one_add_one_eq_two)
      · unfold fd
        split_ifs
        · exact (sub_le_self _ (ind_nonneg S s)).trans
            (gdiag_le_of S (fun y ↦ gw_some_le_one S y _) _)
        · exact (sub_le_self _ (ind_nonneg S s)).trans (ind_le_one S _)
      · exact (ew_zero_le_of S (fun y ↦ gw_some_le_one S y _)).trans_eq (one_pow 2)
  calc (flipOp K S * σ).trace.re ≤ ∑ s, fd e act τ S φ s * (σ s s).re + (E + p) :=
        hF.trans (add_le_add le_rfl hsq)
    _ = ∑ s, (fd e act τ S φ s + ew e act τ S (fun _ ↦ 0) s +
          pd e act (fun _ _ ↦ True) s) * (σ s s).re := by
        simp only [E, p, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_right
        (add_le_add (hpt s) le_rfl) (hre s)

end core

/-! ## Diagonal weights after a Kraus family -/

section weights

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The `f`-weighted diagonal of an operator. -/
noncomputable def dW (f : n → ℝ) (τ : Matrix n n ℂ) : ℝ := ∑ q, f q * (τ q q).re

theorem dW_eq_trace (f : n → ℝ) (τ : Matrix n n ℂ) :
    dW f τ = ((diagonal fun q ↦ ((f q : ℝ) : ℂ)) * τ).trace.re :=
  (re_trace_diagonal_mul f τ).symm

omit [DecidableEq n] in
theorem dW_add (f g : n → ℝ) (τ : Matrix n n ℂ) : dW (fun q ↦ f q + g q) τ = dW f τ + dW g τ := by
  simp only [dW, add_mul, Finset.sum_add_distrib]

/-- The weights after a Kraus family, as the trace of its weighted Gram operator. -/
theorem sum_dW_conj {ι : Type*} [Fintype ι] (K : ι → Matrix n n ℂ) (f : n → ℝ)
    (σ : Matrix n n ℂ) :
    ∑ r, dW f (MatrixMap.conj (K r) σ) =
      ((∑ r, (K r)ᴴ * diagonal (fun q ↦ ((f q : ℝ) : ℂ)) * K r) * σ).trace.re := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [dW_eq_trace, MatrixMap.conj_apply]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

/-- **A weight kept by a complete Kraus family**: if every nonzero entry of every Kraus operator
keeps `f`, the weights after the family add up to the weight before. -/
theorem sum_dW_conj_of_keep {ι : Type*} [Fintype ι] (K : ι → Matrix n n ℂ) (f : n → ℝ)
    (hK : ∀ r a a', K r a' a ≠ 0 → f a' = f a) (hsum : ∑ r, (K r)ᴴ * K r = 1)
    (σ : Matrix n n ℂ) : ∑ r, dW f (MatrixMap.conj (K r) σ) = dW f σ := by
  rw [sum_dW_conj, dW_eq_trace]
  have hc : ∀ r, (K r)ᴴ * diagonal (fun q ↦ ((f q : ℝ) : ℂ)) * K r =
      (K r)ᴴ * K r * diagonal (fun q ↦ ((f q : ℝ) : ℂ)) := fun r ↦ by
    rw [Matrix.mul_assoc, Xmss.Assembly.diagonal_mul_comm_of _ _ fun a a' h ↦ by
      rw [hK r a a' h], ← Matrix.mul_assoc]
  simp only [hc, ← Finset.sum_mul, hsum, Matrix.one_mul]

omit [DecidableEq n] in
/-- A diagonal entry of `K σ Kᴴ` vanishes on a row where `K` vanishes. -/
theorem conj_apply_diag_eq_zero (K : Matrix n n ℂ) (σ : Matrix n n ℂ) {q : n}
    (h : ∀ a, K q a = 0) : MatrixMap.conj K σ q q = 0 := by
  rw [MatrixMap.conj_apply, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [Matrix.mul_apply, Finset.sum_eq_zero fun b _ ↦ by rw [h b, zero_mul], zero_mul]

omit [DecidableEq n] in
theorem posSemidef_conj (K : Matrix n n ℂ) {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    (MatrixMap.conj K σ).PosSemidef := by
  rw [MatrixMap.conj_apply]
  exact hσ.mul_mul_conjTranspose_same K

end weights

/-! ## Counting the cells of a tail predicate, off one cell -/

section counts

variable {X Z Y : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] {π : Equiv.Perm (X × Z)} {out : X → Y}

/-- The cell `z'` of `U` is counted by `tailOutCount`: a head-tail satisfying `P`, recorded, with
an output in `Qo`. -/
def OutAt (π : Equiv.Perm (X × Z)) (U : Dbs X Z) (out : X → Y) (P : List X → Prop)
    (Qo : Y → Prop) (z' : Z) : Prop :=
  ∃ t xi w, P t ∧ IsHeadTail π U t z' xi ∧ U.h z' = some w ∧ Qo (out (xi + w))

open scoped Classical in
/-- The cells other than `z` counted by `tailOutCount`. -/
noncomputable def tailOutOff (π : Equiv.Perm (X × Z)) (U : Dbs X Z) (out : X → Y)
    (P : List X → Prop) (Qo : Y → Prop) (z : Z) : ℕ :=
  (Finset.univ.filter fun z' ↦ z' ≠ z ∧ OutAt π U out P Qo z').card

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [AddCommGroup Z] in
theorem card_filter_eq_off_add {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop)
    [DecidablePred p] (a : α) :
    (Finset.univ.filter p).card =
      (Finset.univ.filter fun b ↦ b ≠ a ∧ p b).card + if p a then 1 else 0 := by
  have hu : Finset.univ.filter p =
      (Finset.univ.filter fun b ↦ b ≠ a ∧ p b) ∪ Finset.univ.filter fun b ↦ b = a ∧ p b := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases hb : b = a <;> simp [hb]
  have hd : Disjoint (Finset.univ.filter fun b ↦ b ≠ a ∧ p b)
      (Finset.univ.filter fun b ↦ b = a ∧ p b) := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    exact (Finset.mem_filter.1 hb).2.1 (Finset.mem_filter.1 hb').2.1
  rw [hu, Finset.card_union_of_disjoint hd]
  congr 1
  split_ifs with ha
  · rw [Finset.card_eq_one]
    refine ⟨a, ?_⟩
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h ▸ ha⟩⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro b - ⟨rfl, hb⟩
    exact ha hb

omit [Fintype X] [DecidableEq X] in
open scoped Classical in
/-- `tailOutCount` is the count off `z` plus the cell `z` itself. -/
theorem tailOutCount_eq_off_add (π : Equiv.Perm (X × Z)) (U : Dbs X Z) (out : X → Y)
    (P : List X → Prop) (Qo : Y → Prop) (z : Z) :
    tailOutCount π U out P Qo = tailOutOff π U out P Qo z + if OutAt π U out P Qo z then 1 else 0 :=
  card_filter_eq_off_add (OutAt π U out P Qo) z

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] in
theorem isHeadTail_congr {U U' : Dbs X Z} (hk : U.k = U'.k) (hk' : U.k' = U'.k') {t : List X}
    {z : Z} {xi : X} : IsHeadTail π U t z xi ↔ IsHeadTail π U' t z xi :=
  ⟨fun h ↦ h.mono (extends_refl_of_eq hk.symm hk'.symm), fun h ↦ h.mono (extends_refl_of_eq hk hk')⟩

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] in
theorem good_congr {U U' : Dbs X Z} (hk : U.k = U'.k) (hk' : U.k' = U'.k') :
    Good π U ↔ Good π U' :=
  ⟨fun h ↦ h.mono (extends_refl_of_eq hk hk'), fun h ↦ h.mono (extends_refl_of_eq hk.symm hk'.symm)⟩

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem outAt_congr {U U' : Dbs X Z} (hk : U.k = U'.k) (hk' : U.k' = U'.k') {z' : Z}
    (hh : U.h z' = U'.h z') (P : List X → Prop) (Qo : Y → Prop) :
    OutAt π U out P Qo z' ↔ OutAt π U' out P Qo z' := by
  unfold OutAt
  simp only [isHeadTail_congr hk hk', hh]

omit [Fintype X] [DecidableEq X] in
theorem tailOutOff_congr {U U' : Dbs X Z} (hk : U.k = U'.k) (hk' : U.k' = U'.k') {z : Z}
    (hh : ∀ z', z' ≠ z → U.h z' = U'.h z') (P : List X → Prop) (Qo : Y → Prop) :
    tailOutOff π U out P Qo z = tailOutOff π U' out P Qo z := by
  unfold tailOutOff
  congr 1
  ext z'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr_right fun hz ↦ outAt_congr hk hk' (hh z' hz) P Qo

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- In a good database a cell is counted for at most one of exclusive tail predicates. -/
theorem outAt_unique {κ : Type*} {U : Dbs X Z} (hG : Good π U) (P : κ → List X → Prop)
    (hP : ∀ k k' t, P k t → P k' t → k = k') (Qo : Y → Prop) {z : Z} {k k' : κ}
    (h : OutAt π U out (P k) Qo z) (h' : OutAt π U out (P k') Qo z) : k = k' := by
  obtain ⟨t, xi, -, hPt, hi, -⟩ := h
  obtain ⟨t', xi', -, hPt', hi', -⟩ := h'
  obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hi'
  exact hP k k' t hPt hPt'

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z] in
theorem union_empty_h (z : Z) :
    (union (hwEmpty X Z) (Database.empty, Database.empty, Database.empty)).h z = none :=
  rfl

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
theorem tailOutCount_eq_zero {U : Dbs X Z} (h : ∀ z, U.h z = none) (P : List X → Prop)
    (Qo : Y → Prop) : tailOutCount π U out P Qo = 0 := by
  classical
  unfold tailOutCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro z - ⟨t, xi, w, -, -, hw, -⟩
  rw [h z] at hw
  cases hw

omit [Fintype X] [DecidableEq X] [Fintype Z] [AddCommGroup X] [AddCommGroup Z] in
theorem union_h_upd (W : Hw X Z) (h : Database Z X) (kk : Database X Z × Database X Z) (z : Z)
    (y : X) (hW : W.1 z = none) : (union W (Function.update h z (some y), kk)).h z = some y := by
  show (W.1 z).or (Function.update h z (some y) z) = some y
  rw [hW, Function.update_self]
  rfl

end counts

/-! ## Sums over the keys -/

section keys

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Splitting off one key. -/
theorem sum_ite_split (p : κ → Prop) [DecidablePred p] (f : κ → ℝ) (k₀ : κ) :
    ∑ k, (if p k then f k else 0) =
      ∑ k, (if k ≠ k₀ ∧ p k then f k else 0) + if p k₀ then f k₀ else 0 := by
  have h : ∀ k, (if p k then f k else 0) =
      (if k ≠ k₀ ∧ p k then f k else 0) + if k = k₀ then (if p k then f k else 0) else 0 :=
    fun k ↦ by by_cases hk : k = k₀ <;> by_cases hp : p k <;> simp [hk, hp]
  rw [Finset.sum_congr rfl fun k _ ↦ h k, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ k₀, ite_eq_left (Finset.mem_univ _)]

omit [DecidableEq κ] in
/-- A sum of indicators of a predicate holding for at most one key. -/
theorem sum_ite_one_of_unique (p : κ → Prop) [DecidablePred p] [Decidable (∃ k, p k)]
    (hu : ∀ k k', p k → p k' → k = k') :
    ∑ k, (if p k then (1 : ℝ) else 0) = if ∃ k, p k then 1 else 0 := by
  split_ifs with h
  · obtain ⟨k, hk⟩ := h
    rw [Finset.sum_eq_single k (fun k' _ hk' ↦ ite_eq_right fun h' ↦ hk' (hu k' k h' hk))
      (fun h' ↦ absurd (Finset.mem_univ k) h'), ite_eq_left hk]
  · exact Finset.sum_eq_zero fun k _ ↦ ite_eq_right fun h' ↦ h ⟨k, h'⟩

end keys

end Quantum.Sponge

/-! ## The leanXMSS potential -/

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss

/-- The message slot of key `k`. -/
def MsgAt (L : HonestTable) (k : Layer × KeyIndex) (t : List X) : Prop :=
  slotOf L.param t = some (.msg k.1 k.2)

theorem msgAt_unique (L : HonestTable) (k k' : Layer × KeyIndex) (t : List X) (h : MsgAt L k t)
    (h' : MsgAt L k' t) : k = k' := by
  obtain ⟨h1, h2⟩ := Slot.msg.inj (Option.some.inj (h.symm.trans h'))
  exact Prod.ext h1 h2

theorem msgCwCount_eq_tailOutCount (L : HonestTable) (U : Dbs X Z) (k : Layer × KeyIndex) :
    msgCwCount L U k.1 k.2 = tailOutCount L.perm U trunc128 (MsgAt L k) Codeword.Valid :=
  rfl

theorem union_h (W : Hw X Z) (D : DbReg X Z) (z : Z) : (union W D).h z = (W.1 z).or (D.1 z) :=
  rfl

theorem union_k (W : Hw X Z) (D : DbReg X Z) : (union W D).k = fun x ↦ (W.2.1 x).or (D.2.1 x) :=
  rfl

theorem union_k' (W : Hw X Z) (D : DbReg X Z) :
    (union W D).k' = fun x ↦ (W.2.2 x).or (D.2.2 x) :=
  rfl

theorem union_k_h (W : Hw X Z) (h h' : Database Z X) (kk : Database X Z × Database X Z) :
    (union W (h, kk)).k = (union W (h', kk)).k :=
  rfl

theorem union_k'_h (W : Hw X Z) (h h' : Database Z X) (kk : Database X Z × Database X Z) :
    (union W (h, kk)).k' = (union W (h', kk)).k' :=
  rfl

section pot

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)

open scoped Classical in
/-- **The cross-key potential**: on a good union, the codeword counts `msgCwCount` of the
unselected keys; `0` on a bad union. -/
noncomputable def encPot (L : HonestTable) (s : HwReg X Z M) : ℝ :=
  if Good L.perm (union s.2.1 s.1) then
    ∑ k : Layer × KeyIndex, if get s.2.2 k.1 k.2 = none then
      (msgCwCount L (union s.2.1 s.1) k.1 k.2 : ℝ) else 0
  else 0

open scoped Classical in
/-- The count of key `k` off the cell `z`, on a good union. -/
noncomputable def encOff (L : HonestTable) (z : Z) (k : Layer × KeyIndex) (s : HwReg X Z M) : ℝ :=
  if Good L.perm (union s.2.1 s.1) then
    (tailOutOff L.perm (union s.2.1 s.1) trunc128 (MsgAt L k) Codeword.Valid z : ℝ) else 0

/-- The part of the potential of the keys other than `k₀`, off the cell `z`. -/
noncomputable def encA (L : HonestTable) (z : Z) (k₀ : Layer × KeyIndex) (s : HwReg X Z M) : ℝ :=
  ∑ k : Layer × KeyIndex, if k ≠ k₀ ∧ get s.2.2 k.1 k.2 = none then encOff L z k s else 0

/-- The part of the potential of key `k₀`, off the cell `z`. -/
noncomputable def encB (L : HonestTable) (z : Z) (k₀ : Layer × KeyIndex) (s : HwReg X Z M) : ℝ :=
  if get s.2.2 k₀.1 k₀.2 = none then encOff L z k₀ s else 0

/-- The states whose cell `z` counts for an unselected key, on a good union. -/
def encCSet (L : HonestTable) (z : Z) : Set (HwReg X Z M) :=
  {s | Good L.perm (union s.2.1 s.1) ∧ ∃ k : Layer × KeyIndex, get s.2.2 k.1 k.2 = none ∧
    OutAt L.perm (union s.2.1 s.1) trunc128 (MsgAt L k) Codeword.Valid z}

/-- Membership in `encCSet`, decided classically. -/
noncomputable instance encCSetDec (L : HonestTable) (z : Z) :
    DecidablePred (· ∈ encCSet get L z) :=
  Classical.decPred _

omit [Fintype M] [DecidableEq M] in
theorem encOff_nonneg (L : HonestTable) (z : Z) (k : Layer × KeyIndex) (s : HwReg X Z M) :
    0 ≤ encOff L z k s := by
  unfold encOff
  split_ifs <;> positivity

omit [Fintype M] [DecidableEq M] in
theorem encPot_nonneg (L : HonestTable) (s : HwReg X Z M) : 0 ≤ encPot get L s := by
  unfold encPot
  split_ifs
  · exact Finset.sum_nonneg fun k _ ↦ by split_ifs <;> positivity
  · exact le_rfl

omit [Fintype M] [DecidableEq M] in
/-- **The potential at a read cell `z` and a key `k₀`**: the other keys off `z`, the key `k₀` off
`z`, and the cell `z` itself (at most one key counts it in a good union). -/
theorem encPot_eq (L : HonestTable) (z : Z) (k₀ : Layer × KeyIndex) (q : Unit × HwReg X Z M) :
    encPot get L q.2 = encA get L z k₀ q.2 + encB get L z k₀ q.2 + ind (liftSet (encCSet get L z)) q := by
  classical
  have hind : ind (liftSet (encCSet get L z)) q = if q.2 ∈ encCSet get L z then 1 else 0 := by
    unfold ind
    exact if_congr (mem_liftSet _ q) rfl rfl
  rw [hind]
  unfold encPot encA encB encOff
  by_cases hG : Good L.perm (union q.2.2.1 q.2.1)
  · simp only [hG, ↓reduceIte]
    have hsplit : ∀ k : Layer × KeyIndex, (if get q.2.2.2 k.1 k.2 = none then
        (msgCwCount L (union q.2.2.1 q.2.1) k.1 k.2 : ℝ) else 0) =
        (if get q.2.2.2 k.1 k.2 = none then (tailOutOff L.perm (union q.2.2.1 q.2.1) trunc128
          (MsgAt L k) Codeword.Valid z : ℝ) else 0) +
        (if get q.2.2.2 k.1 k.2 = none ∧ OutAt L.perm (union q.2.2.1 q.2.1) trunc128 (MsgAt L k)
          Codeword.Valid z then 1 else 0) := fun k ↦ by
      rw [msgCwCount_eq_tailOutCount, tailOutCount_eq_off_add _ _ _ _ _ z]
      by_cases hu : get q.2.2.2 k.1 k.2 = none
      · by_cases ho : OutAt L.perm (union q.2.2.1 q.2.1) trunc128 (MsgAt L k) Codeword.Valid z
        · simp only [hu, ho, and_self, ↓reduceIte, Nat.cast_add, Nat.cast_one]
        · simp only [hu, ho, and_false, ↓reduceIte, add_zero]
      · simp only [hu, false_and, ↓reduceIte, add_zero]
    rw [Finset.sum_congr rfl fun k _ ↦ hsplit k, Finset.sum_add_distrib,
      sum_ite_split (fun k : Layer × KeyIndex ↦ get q.2.2.2 k.1 k.2 = none) _ k₀,
      sum_ite_one_of_unique _ fun k k' h h' ↦ outAt_unique hG (MsgAt L) (msgAt_unique L)
        Codeword.Valid h.2 h'.2]
    have hmem : q.2 ∈ encCSet get L z ↔ ∃ k : Layer × KeyIndex, get q.2.2.2 k.1 k.2 = none ∧
        OutAt L.perm (union q.2.2.1 q.2.1) trunc128 (MsgAt L k) Codeword.Valid z :=
      ⟨fun h ↦ h.2, fun h ↦ ⟨hG, h⟩⟩
    rw [if_congr hmem rfl rfl]
  · have hmem : q.2 ∉ encCSet get L z := fun h ↦ hG h.1
    simp only [hG, ↓reduceIte, hmem, ite_self, Finset.sum_const_zero, add_zero]

end pot

/-! ## A selecting read, against the potential -/

/-- **The trial updates**: a trial read of an unselected key records the codeword selection
(`cwSel`), and no read changes the other keys. -/
structure CwTrialUpd {M : Type} (get : M → Selections) (updOf : TrialPt → M → Option X → M) :
    Prop where
  sel : ∀ t m v, get m t.l t.e = none →
    get (updOf t m (some v)) = cwSel (get m) t.l t.e t.x t.xi v
  keep : ∀ t m o (k : Layer × KeyIndex), k ≠ (t.l, t.e) →
    get (updOf t m o) k.1 k.2 = get m k.1 k.2

section trial

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)
  (updOf : TrialPt → M → Option X → M)

/-- **The states where the read cell cannot count after a trial read**: a bad union, or the
trial's key unselected, the trial's block at its message slot and the head-tail of the cell `z`
(the support invariant of the trial reads). -/
def TrialGood (L : HonestTable) (z : Z) (t : TrialPt) (s : HwReg X Z M) : Prop :=
  ¬ Good L.perm (union s.2.1 s.1) ∨ (get s.2.2 t.l t.e = none ∧
    MsgAt L (t.l, t.e) (blocks (blockInput t.x)) ∧
    IsHeadTail L.perm (union s.2.1 s.1) (blocks (blockInput t.x)) z t.xi)

omit [Fintype M] [DecidableEq M] in
/-- **After a trial read the read cell does not count**: on `TrialGood` states, recording any value
`y` at `z` with the trial's update leaves `encCSet`. -/
theorem not_mem_encCSet_of_trialGood (hu : CwTrialUpd get updOf) {L : HonestTable} {z : Z}
    {t : TrialPt} {s s' : HwReg X Z M} {y : X} (hg : TrialGood get L z t s)
    (hk : (union s'.2.1 s'.1).k = (union s.2.1 s.1).k)
    (hk' : (union s'.2.1 s'.1).k' = (union s.2.1 s.1).k') (hz : (union s'.2.1 s'.1).h z = some y)
    (hm : s'.2.2 = updOf t s.2.2 (some y)) : s' ∉ encCSet get L z := by
  rintro ⟨hG', k, hun, t', xi', w, hP, hi, hw, hcw⟩
  have hG : Good L.perm (union s.2.1 s.1) := (good_congr hk hk').1 hG'
  rcases hg with hg | ⟨hm0, hslot, hhead⟩
  · exact hg hG
  have hhead' := (isHeadTail_congr hk.symm hk'.symm).1 hhead
  obtain ⟨rfl, rfl⟩ := hG'.isHeadTail_unique hi hhead'
  obtain rfl := msgAt_unique L _ _ _ hP hslot
  rw [hz] at hw
  obtain rfl := Option.some.inj hw
  rw [hm, hu.sel t _ y hm0] at hun
  exact ((cwSel_eq_none_iff hm0 t.x t.xi y).1 hun) hcw

omit [Fintype M] in
/-- A nonzero entry of a read of `h` accepts the memory `r.2` and moves it to `upd r.2 r.1`. -/
theorem readKrausH_mem (z : Z) (upd : M → Option X → M) (r : Option X × M) {s' s : HwReg X Z M}
    (h : readKrausH z upd r s' s ≠ 0) : s.2.2 = r.2 ∧ s'.2.2 = upd r.2 r.1 := by
  rw [readKrausH, clsKraus_apply] at h
  split_ifs at h with hc
  · exact ⟨hc.1, by rw [hc.2]⟩
  · exact absurd rfl h

omit [Fintype M] [DecidableEq M] in
theorem union_congr_off {s s' : HwReg X Z M} {z : Z} (h1 : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b)
    (h2 : s'.1.2 = s.1.2) (h3 : s'.2.1 = s.2.1) :
    (union s'.2.1 s'.1).k = (union s.2.1 s.1).k ∧ (union s'.2.1 s'.1).k' = (union s.2.1 s.1).k' ∧
      ∀ b, b ≠ z → (union s'.2.1 s'.1).h b = (union s.2.1 s.1).h b := by
  refine ⟨?_, ?_, fun b hb ↦ ?_⟩
  · rw [union_k, union_k, h3, h2]
  · rw [union_k', union_k', h3, h2]
  · rw [union_h, union_h, h3, h1 b hb]

omit [Fintype M] [DecidableEq M] in
open scoped Classical in
/-- The counts off `z` do not see the cell `z` nor the memory. -/
theorem encOff_offCell (L : HonestTable) (z : Z) (k : Layer × KeyIndex) :
    OffCell z (encOff (M := M) L z k) := by
  intro s s' h1 h2 h3
  obtain ⟨hk, hk', hh⟩ := union_congr_off h1 h2 h3
  unfold encOff
  rw [tailOutOff_congr hk hk' hh]
  exact if_congr (good_congr hk hk') rfl rfl

omit [Fintype M] [DecidableEq M] in
theorem encA_congr (L : HonestTable) (z : Z) (k₀ : Layer × KeyIndex) {s s' : HwReg X Z M}
    (h1 : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b) (h2 : s'.1.2 = s.1.2) (h3 : s'.2.1 = s.2.1)
    (hm : ∀ k : Layer × KeyIndex, k ≠ k₀ → get s'.2.2 k.1 k.2 = get s.2.2 k.1 k.2) :
    encA get L z k₀ s' = encA get L z k₀ s := by
  unfold encA
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : k = k₀
  · rw [ite_eq_right fun h ↦ absurd hk h.1, ite_eq_right fun h ↦ absurd hk h.1]
  · rw [hm k hk, encOff_offCell L z k s s' h1 h2 h3]

omit [Fintype M] in
/-- A nonzero entry of a trial read keeps the part of the potential of the other keys. -/
theorem encA_keep (hu : CwTrialUpd get updOf) (L : HonestTable) (z : Z) (t : TrialPt)
    (r : Option X × M) (a a' : Unit × HwReg X Z M)
    (h : hwReadKraus (.readH z (updOf t)) r a' a ≠ 0) :
    encA get L z (t.l, t.e) a'.2 = encA get L z (t.l, t.e) a.2 := by
  obtain ⟨-, h'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
  obtain ⟨h1, h2, h3⟩ := readKrausH_ne_zero_rest z (updOf t) r h'
  obtain ⟨hm1, hm2⟩ := readKrausH_mem z (updOf t) r h'
  refine encA_congr get L z _ h1 h2 h3 fun k hk ↦ ?_
  rw [hm2, hu.keep t _ _ k hk, hm1]

/-- The rows of a trial read's output carry the updated memory. -/
theorem conj_readH_diag_eq_zero (z : Z) (upd : M → Option X → M) (r : Option X × M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) {q : Unit × HwReg X Z M}
    (hq : q.2.2.2 ≠ upd r.2 r.1) : MatrixMap.conj (hwReadKraus (.readH z upd) r) σ q q = 0 := by
  refine conj_apply_diag_eq_zero _ σ fun a ↦ ?_
  by_contra hne
  obtain ⟨-, h'⟩ := one_kronecker_ne_zero (a := a.1) (a' := q.1) (b := a.2) (b' := q.2) hne
  exact hq (readKrausH_mem z upd r h').2

open scoped Classical in
/-- **A trial read against the potential** (real form). For a trial `t` read at the cell `z`, on
a state with no decompressed `⊥` there, `2^-22 e` plus the potential after the read is at most
the potential before plus `3 p` and the cell's own charge: `e` and `p` are the count of key
`(t.l, t.e)` off `z` on the selection reads and off them (`survive_readH_weighted_le`,
`drop_of_survive`), the other keys keep their part (`encA_keep`), and the cell `z` counts after
the read only off `TrialGood` (at most `2`), by re-compression (`2/|X| + 4/|X|²`) and on its
recorded mass (`re_trace_flipOp_le_good`). -/
theorem trialRead_drop_real (hu : CwTrialUpd get updOf) (L : HonestTable) (z : Z) (t : TrialPt)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (2 ^ 22 : ℝ)⁻¹ * (∑ q, if SelectRead L q.2.1 q.2.2.1 (get q.2.2.2) z t.l t.e t.x t.xi then
        encOff L z (t.l, t.e) q.2 * (σ q q).re else 0) +
      ∑ r : Option X × M, dW (fun q ↦ encPot get L q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) ≤
    dW (fun q ↦ encPot get L q.2) σ +
      3 * (∑ q, if SelectRead L q.2.1 q.2.2.1 (get q.2.2.2) z t.l t.e t.x t.xi then 0 else
        encOff L z (t.l, t.e) q.2 * (σ q q).re) +
      ∑ q, ((if TrialGood get L z t q.2 then 2 / (Fintype.card X : ℝ) +
        (2 / (Fintype.card X : ℝ)) ^ 2 else 2) + pd (splitH' z) (actH z) (fun _ _ ↦ True) q) *
        (σ q q).re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hsplit : ∀ τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ,
      dW (fun q ↦ encPot get L q.2) τ = dW (fun q ↦ encA get L z (t.l, t.e) q.2) τ +
        dW (fun q ↦ encB get L z (t.l, t.e) q.2) τ +
        dW (fun q ↦ ind (liftSet (encCSet get L z)) q) τ := fun τ ↦ by
    simp only [dW, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [encPot_eq get L z (t.l, t.e) q]
    ring
  -- The other keys.
  have hA : ∑ r : Option X × M, dW (fun q ↦ encA get L z (t.l, t.e) q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
        dW (fun q ↦ encA get L z (t.l, t.e) q.2) σ :=
    sum_dW_conj_of_keep (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r) _
      (fun r a a' h ↦ encA_keep get updOf hu L z t r a a' h) (sum_readKrausH z (updOf t)) σ
  -- The key of the trial, off the cell.
  have hn0 : ∀ s : HwReg X Z M, 0 ≤ encOff L z (t.l, t.e) s := encOff_nonneg L z (t.l, t.e)
  have hupdT : ∀ m ∈ {m : M | get m t.l t.e = none}, ∀ v,
      updOf t m (some v) ∈ {m : M | get m t.l t.e = none} ↔
        ¬ Codeword.Valid (trunc128 (t.xi + v)) := fun m hm v ↦ by
    show get (updOf t m (some v)) t.l t.e = none ↔ _
    rw [hu.sel t m v hm]
    exact cwSel_eq_none_iff hm t.x t.xi v
  have hsurv := survive_readH_weighted_le z (updOf t) {m : M | get m t.l t.e = none}
    (fun v ↦ Codeword.Valid (trunc128 (t.xi + v))) (card_codeword_div_card_X t.xi) hupdT
    (fun s ↦ SelectRead L s.1 s.2.1 (get s.2.2) z t.l t.e t.x t.xi)
    (fun s hs ↦ ⟨hs.hd, hs.hw, hs.hm⟩) hn0 (encOff_offCell L z (t.l, t.e)) hσ
  have he : 0 ≤ ∑ q, if SelectRead L q.2.1 q.2.2.1 (get q.2.2.2) z t.l t.e t.x t.xi then
      encOff L z (t.l, t.e) q.2 * (σ q q).re else 0 :=
    Finset.sum_nonneg fun q _ ↦ by
      split_ifs
      · exact mul_nonneg (hn0 _) (hre q)
      · exact le_rfl
  have hp : 0 ≤ ∑ q, if SelectRead L q.2.1 q.2.2.1 (get q.2.2.2) z t.l t.e t.x t.xi then 0 else
      encOff L z (t.l, t.e) q.2 * (σ q q).re :=
    Finset.sum_nonneg fun q _ ↦ by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hn0 _) (hre q)
  have hdrop := drop_of_survive he hp inv_two_pow_21_le_rhoCw hsurv
  have hBpost : ∀ r : Option X × M, dW (fun q ↦ encB get L z (t.l, t.e) q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
      if updOf t r.2 r.1 ∈ {m : M | get m t.l t.e = none} then
        ∑ q, encOff L z (t.l, t.e) q.2 *
          ((MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) q q).re else 0 := by
    intro r
    have hq : ∀ q, encB get L z (t.l, t.e) q.2 *
        ((MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) q q).re =
        if updOf t r.2 r.1 ∈ {m : M | get m t.l t.e = none} then encOff L z (t.l, t.e) q.2 *
          ((MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) q q).re else 0 := by
      intro q
      by_cases hqm : q.2.2.2 = updOf t r.2 r.1
      · have hB : encB get L z (t.l, t.e) q.2 =
            if updOf t r.2 r.1 ∈ {m : M | get m t.l t.e = none} then
              encOff L z (t.l, t.e) q.2 else 0 := by
          show (if get q.2.2.2 t.l t.e = none then encOff L z (t.l, t.e) q.2 else 0) = _
          rw [hqm]
          exact if_congr Iff.rfl rfl rfl
        rw [hB]
        split_ifs <;> ring
      · rw [conj_readH_diag_eq_zero z (updOf t) r σ hqm, Complex.zero_re, mul_zero, mul_zero,
          ite_self]
    unfold dW
    rw [Finset.sum_congr rfl fun q _ ↦ hq q]
    split_ifs
    · rfl
    · exact Finset.sum_const_zero
  have hBpre : dW (fun q ↦ encB get L z (t.l, t.e) q.2) σ =
      ∑ q, if q.2.2.2 ∈ {m : M | get m t.l t.e = none} then
        encOff L z (t.l, t.e) q.2 * (σ q q).re else 0 := by
    unfold dW
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    show (if get q.2.2.2 t.l t.e = none then encOff L z (t.l, t.e) q.2 else 0) * (σ q q).re = _
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · exact zero_mul _
  -- The cell itself.
  have hgood : ∀ q : Unit × HwReg X Z M, TrialGood get L z t q.2 → actH z (splitH' z q).2 →
      ∀ y, ind (liftSet (encCSet get L z))
        ((splitH' z).symm (some y, tauH z (updOf t) (some y) (splitH' z q).2)) = 0 := by
    intro q hg ha y
    have ha' : q.2.2.1.1 z = none := ha
    have hnot : ((Function.update q.2.1.1 z (some y), q.2.1.2), q.2.2.1,
        updOf t q.2.2.2 (some y)) ∉ encCSet get L z := by
      exact not_mem_encCSet_of_trialGood get updOf hu hg (union_k_h _ _ _ _)
        (union_k'_h _ _ _ _) (union_h_upd q.2.2.1 q.2.1.1 q.2.1.2 z y ha') rfl
    rw [splitH'_symm_tau]
    exact ind_eq_zero_of_not_mem (liftSet (encCSet get L z)) hnot
  have hgoodH : ∀ q : Unit × HwReg X Z M, TrialGood get L z t q.2 → ¬ actH z (splitH' z q).2 →
      ind (liftSet (encCSet get L z)) (phiH z (updOf t) q) = 0 := by
    intro q hg ha
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 (show q.2.2.1.1 z ≠ none from ha)
    refine ind_eq_zero_of_not_mem _ fun h ↦ not_mem_encCSet_of_trialGood get updOf hu (y := w)
      (s' := (q.2.1, q.2.2.1, updOf t q.2.2.2 (q.2.2.1.1 z))) hg rfl rfl ?_ ?_
      ((mem_liftSet _ _).1 h)
    · show (q.2.2.1.1 z).or (q.2.1.1 z) = some w
      rw [hw]
      rfl
    · show updOf t q.2.2.2 (q.2.2.1.1 z) = updOf t q.2.2.2 (some w)
      rw [hw]
  have hC := re_trace_flipOp_le_good (liftSet (encCSet get L z)) (cellRead_readH z (updOf t))
    (clsOff_readH z (updOf t)) (fun q ↦ TrialGood get L z t q.2) hgood hgoodH hσ hnb
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
  -- Together.
  have hpost : ∑ r : Option X × M, dW (fun q ↦ encPot get L q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
      ∑ r : Option X × M, dW (fun q ↦ encA get L z (t.l, t.e) q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) +
      ∑ r : Option X × M, dW (fun q ↦ encB get L z (t.l, t.e) q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) +
      ∑ r : Option X × M, dW (fun q ↦ ind (liftSet (encCSet get L z)) q)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) := by
    simp only [hsplit, Finset.sum_add_distrib]
  rw [hpost, hsplit σ, hA, hCpost, Finset.sum_congr rfl fun r _ ↦ hBpost r, hBpre]
  linarith [hdrop, hC]


open scoped Classical in
/-- The count of a trial's key off the read cell on the selection reads (the `e` of the survival
bound): on a selection read the cell is empty, so this is `msgCwCount` on a good union
(`encOff_eq_of_selectRead`). -/
noncomputable def trialCnt (L : HonestTable) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, if SelectRead L q.2.1 q.2.2.1 (get q.2.2.2) z t.l t.e t.x t.xi then
    encOff L z (t.l, t.e) q.2 * (σ q q).re else 0

open scoped Classical in
/-- The weighted mass off the selection reads (the `p` of the survival bound). -/
noncomputable def trialOffW (L : HonestTable) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, if SelectRead L q.2.1 q.2.2.1 (get q.2.2.2) z t.l t.e t.x t.xi then 0 else
    encOff L z (t.l, t.e) q.2 * (σ q q).re

open scoped Classical in
/-- The charge of the read cell itself: `2/|X| + 4/|X|²` on `TrialGood` states, `2` elsewhere,
plus the recorded mass of the cell (`pd`). -/
noncomputable def trialCellW (L : HonestTable) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, ((if TrialGood get L z t q.2 then 2 / (Fintype.card X : ℝ) +
    (2 / (Fintype.card X : ℝ)) ^ 2 else 2) + pd (splitH' z) (actH z) (fun _ _ ↦ True) q) *
    (σ q q).re

open scoped Classical in
/-- **The joint count of the selecting reads**, per port: `trialCnt` at a trial read port. -/
noncomputable def cntGW (L : HonestTable) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then
    ENNReal.ofReal (trialCnt get L (trialOf updOf c).1 (trialOf updOf c).2 σ) else 0

open scoped Classical in
/-- **The charge of a trial read port** against the potential: `3 p` plus the cell's charge. -/
noncomputable def trialChg (L : HonestTable) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then ENNReal.ofReal (3 * trialOffW get L (trialOf updOf c).1
    (trialOf updOf c).2 σ + trialCellW get L (trialOf updOf c).1 (trialOf updOf c).2 σ) else 0

omit [DecidableEq M] in
theorem dW_nonneg {n : Type} [Fintype n] {f : n → ℝ} (hf : ∀ q, 0 ≤ f q) {τ : Matrix n n ℂ}
    (hτ : τ.PosSemidef) : 0 ≤ dW f τ :=
  Finset.sum_nonneg fun q _ ↦ mul_nonneg (hf q) (Complex.nonneg_iff.1 hτ.diag_nonneg).1

omit [DecidableEq M] in
theorem trialCnt_nonneg (L : HonestTable) (z : Z) (t : TrialPt)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ trialCnt get L z t σ :=
  Finset.sum_nonneg fun q _ ↦ by
    split_ifs
    · exact mul_nonneg (encOff_nonneg L z _ _) (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    · exact le_rfl

/-- The potential of the hardwired register as a weighted diagonal. -/
theorem potential_encPot (L : HonestTable) (τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    potential (diagPot fun s ↦ √(encPot get L s)) τ =
      ENNReal.ofReal (dW (fun q ↦ encPot get L q.2) τ) :=
  potential_diagPot_sqrt (encPot_nonneg get L) τ

/-- **A trial read port against the potential**: on a state with no decompressed `⊥` at the read
cell, `2^-22 cntGW` plus the potential after the read is at most the potential before plus
`trialChg` (`trialRead_drop_real`). -/
theorem trialRead_potential_le (hu : CwTrialUpd get updOf) (L : HonestTable) {c : HwRead X Z M}
    (ht : IsTrial updOf c) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) (hnb : ReadNoBot c σ) :
    (2 ^ 22 : ℝ≥0∞)⁻¹ * cntGW get updOf L c σ +
        ∑' r, potential (diagPot fun s ↦ √(encPot get L s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
      potential (diagPot fun s ↦ √(encPot get L s)) σ + trialChg get updOf L c σ := by
  have hc := eq_readH_trialOf updOf ht
  simp only [cntGW, trialChg, ht, ↓reduceIte]
  generalize trialOf updOf c = zt at hc ⊢
  subst hc
  obtain ⟨z, t⟩ := zt
  have hreal := trialRead_drop_real get updOf hu L z t hσ hnb
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
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) (trialCnt_nonneg get L z t hσ))
      (Finset.sum_nonneg fun r _ ↦ hpost r)]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  have hr := hreal
  unfold trialCnt trialOffW trialCellW
  linarith [hr]

omit [Fintype M] [DecidableEq M] in
/-- **On a selection read the count off the read cell is the codeword count** (the cell is
empty), on a good union. -/
theorem encOff_of_selectRead (L : HonestTable) {s : HwReg X Z M} {z : Z} {t : TrialPt}
    (hs : SelectRead L s.1 s.2.1 (get s.2.2) z t.l t.e t.x t.xi)
    (hG : Good L.perm (union s.2.1 s.1)) :
    encOff L z (t.l, t.e) s = (msgCwCount L (union s.2.1 s.1) t.l t.e : ℝ) := by
  have hz : (union s.2.1 s.1).h z = none := by
    rw [union_h, hs.hw, hs.hd]
    rfl
  have hout : ¬ OutAt L.perm (union s.2.1 s.1) trunc128 (MsgAt L (t.l, t.e)) Codeword.Valid z :=
    fun ⟨_, _, _, _, _, hw, _⟩ ↦ by rw [hz] at hw; cases hw
  unfold encOff
  rw [ite_eq_left hG, msgCwCount_eq_tailOutCount L _ (t.l, t.e),
    tailOutCount_eq_off_add _ _ _ _ _ z, ite_eq_right hout, add_zero]

omit [DecidableEq M] in
/-- **The codeword flips of the selecting reads against the joint count** (`encW_le_cntW` with
the good unions only): on states whose hardwired grade is at most `N`, a state outside `Bad L N`
has a good union. -/
theorem encW_le_cntGW (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] {L : HonestTable} {N : ℕ}
    (hB : ∀ r, r ∈ B ↔ (r.1, r.2.1, get r.2.2) ∈ Bad L N) (c : HwRead X Z M)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hgr : ∀ q, dbGrade q.2.2.1 ≤ N ∨ σ q q = 0) :
    encW get updOf B L c σ ≤ ENNReal.ofReal (2 ^ 128)⁻¹ * cntGW get updOf L c σ := by
  by_cases ht : IsTrial updOf c
  · simp only [encW, cntGW, ht, ↓reduceIte]
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    rw [encWt, trialCnt, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases hq : trialSR get updOf L c q.2 ∧ q.2 ∉ B
    · rw [ite_eq_left hq]
      have hsr := trialSR_of_isTrial get updOf ht hq.1
      rw [ite_eq_left hsr]
      rcases hgr q with hN | h0
      · have hbad : (q.2.1, q.2.2.1, get q.2.2.2) ∉ Bad L N := fun h ↦ hq.2 ((hB q.2).2 h)
        have hG : Good L.perm (union q.2.2.1 q.2.1) :=
          (not_mem_targetBad_iff.1 (union_not_mem_of_not_mem_hwTargetBad hbad hN)).1
        rw [encOff_of_selectRead get L hsr hG, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          mul_div_assoc, two_pow_div_card_X]
        exact le_of_eq (by ring)
      · rw [h0, Complex.zero_re, mul_zero, mul_zero, mul_zero]
    · rw [ite_eq_right hq]
      refine mul_nonneg (by positivity) ?_
      split_ifs
      · exact mul_nonneg (encOff_nonneg L _ _ _) (hre q)
      · exact le_rfl
  · simp only [encW, cntGW, ht, ↓reduceIte, mul_zero, le_refl]

theorem re_trace_readPs (SR : HwReg X Z M → Prop) [DecidablePred SR]
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    (readPs SR * σ).trace.re = ∑ q, if SR q.2 then 0 else (σ q q).re := by
  rw [readPs, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Matrix.diag_apply, diagonal_mul]
  by_cases hq : SR q.2
  · simp [hq]
  · simp [hq]

open scoped Classical in
/-- **The trial charge against the recorded mass** (CostLift's `massW`, the weight off the
selection reads): if the count off the read cell is at most `C` on the support, the charge is at
most `(3C + 3) massW + (2/|X| + 4/|X|²) tr σ`. -/
theorem trialChg_le_massW (L : HonestTable) {c : HwRead X Z M} (ht : IsTrial updOf c) {C : ℝ}
    (hC0 : 0 ≤ C) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, encOff L (trialOf updOf c).1 ((trialOf updOf c).2.l, (trialOf updOf c).2.e) q.2 ≤
      C ∨ σ q q = 0) :
    trialChg get updOf L c σ ≤ ENNReal.ofReal (3 * C + 3) * massW get updOf L c σ +
      ENNReal.ofReal ((2 / (Fintype.card X : ℝ) + (2 / (Fintype.card X : ℝ)) ^ 2) *
        σ.trace.re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  simp only [trialChg, massW, PRof, ht, ↓reduceIte]
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  set z := (trialOf updOf c).1
  set t := (trialOf updOf c).2
  set a : ℝ := 2 / (Fintype.card X : ℝ) + (2 / (Fintype.card X : ℝ)) ^ 2
  have ha : a ≤ 1 := by
    have hN : (4 : ℝ) ≤ Fintype.card X := by
      rw [card_X, Nat.cast_pow, Nat.cast_ofNat]
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ 1088 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h2 : 2 / (Fintype.card X : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h0 : 0 ≤ 2 / (Fintype.card X : ℝ) := by positivity
    nlinarith
  have hsr : ∀ q : Unit × HwReg X Z M, trialSR get updOf L c q.2 ↔
      SelectRead L q.2.1 q.2.2.1 (get q.2.2.2) z t.l t.e t.x t.xi := fun q ↦
    ⟨trialSR_of_isTrial get updOf ht, fun h ↦ .inl ⟨ht, h⟩⟩
  rw [re_trace_readPs, Matrix.trace, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, trialOffW,
    trialCellW, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  rw [Matrix.diag_apply]
  have hpd := pd_mem (e := splitH' z) (act := actH z) (fun _ _ ↦ True) q
  by_cases hq : SelectRead L q.2.1 q.2.2.1 (get q.2.2.2) z t.l t.e t.x t.xi
  · have hg : TrialGood get L z t q.2 := by
      by_cases hG : Good L.perm (union q.2.2.1 q.2.1)
      · exact .inr ⟨hq.hm, hq.slot, hq.head⟩
      · exact .inl hG
    have hpd0 : pd (splitH' z) (actH z) (fun _ _ ↦ True) q = 0 := by
      unfold pd
      split_ifs
      · rw [show (splitH' z q).1 = q.2.1.1 z from rfl, hq.hd]
        rfl
      · rfl
    rw [ite_eq_left hq, ite_eq_left ((hsr q).2 hq), ite_eq_left hg, hpd0]
    simp only [mul_zero, add_zero, zero_add]
    exact le_rfl
  · rw [ite_eq_right hq, ite_eq_right fun h ↦ hq ((hsr q).1 h)]
    have hpd1 : pd (splitH' z) (actH z) (fun _ _ ↦ True) q ≤ 1 := by
      rcases hpd with h | h <;> rw [h]; norm_num
    have hcell : (if TrialGood get L z t q.2 then a else 2) ≤ 2 := by
      split_ifs
      · linarith
      · exact le_rfl
    have hoff : encOff L z (t.l, t.e) q.2 * (σ q q).re ≤ C * (σ q q).re := by
      rcases hC q with h | h
      · exact mul_le_mul_of_nonneg_right h (hre q)
      · rw [h, Complex.zero_re, mul_zero, mul_zero]
    have ha0 : 0 ≤ a := by positivity
    nlinarith [hre q, mul_le_mul_of_nonneg_right (add_le_add hcell hpd1) (hre q)]

open scoped Classical in
/-- **The codeword-recorded mass of a trial read port** (the restated `restMass` integrand): the
states whose read cell `z` is recorded by the adversary (in the database, not hardwired) with a
value `v` that selects the trial's unselected key (`trunc128 (xi + v)` a codeword). This contains
the flip-recorded mass of ReadCost's cross term for the trial's selecting update (a recorded
value moves the memory only by a selection). -/
noncomputable def cwRecW (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then ENNReal.ofReal (∑ q, if q.2.2.1.1 (trialOf updOf c).1 = none ∧
      get q.2.2.2 (trialOf updOf c).2.l (trialOf updOf c).2.e = none ∧
      ∃ v, q.2.1.1 (trialOf updOf c).1 = some v ∧
        Codeword.Valid (trunc128 ((trialOf updOf c).2.xi + v)) then (σ q q).re else 0)
  else 0

/-- The codeword-recorded mass is part of the mass off the selection reads (`massW`). -/
theorem cwRecW_le_massW (L : HonestTable) (c : HwRead X Z M)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    cwRecW get updOf c σ ≤ massW get updOf L c σ := by
  by_cases ht : IsTrial updOf c
  · simp only [cwRecW, massW, PRof, ht, ↓reduceIte]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [re_trace_readPs]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    have hre : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    split_ifs with h1 h2
    · obtain ⟨v, hv, -⟩ := h1.2.2
      have hd := (trialSR_of_isTrial get updOf ht h2).hd
      rw [hd] at hv
      cases hv
    · exact le_rfl
    · exact le_rfl
    · exact hre
  · simp only [cwRecW, ht, ↓reduceIte, zero_le]

end trial

/-! ## Along a run of `runtimeR` -/

section runtimeRInv

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  {Λ : LocalSig.{u, v}} {Ω : QReg → Type w} {A : QReg}

/-- **The drops of a diagonal potential along a run of `runtimeR`, on port invariants**:
CostJoint's `totalWeight_le_diagPotential_runtimeR` with an arbitrary property `Inv i` of the
inputs of port `i` (for example no decompressed `⊥` at a read cell), which the calls of `x`
satisfy through `P`. -/
theorem totalWeight_le_potential_runtimeR_inv (m₀ : Finset S × M')
    {φ : HwReg X Z (Finset S × M') → ℝ} (hφ0 : ∀ s, 0 ≤ φ s) (hlab : PotLabelFree φ)
    (P : ∀ (i : (recHwSpec X Z S M').Port) (E : QReg),
      Matrix (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E)
        (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E) ℂ → Prop)
    (Inv : ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → Prop)
    (hP : ∀ i E σ, P i E σ → Inv i (MatrixMap.traceRight _ E σ))
    (dR : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cS : ∀ p : SpongePort, Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cR : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cP : HwProg X Z → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (hS : ∀ p (σ : Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
        (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef →
      Inv (.inl (.inl (.inl p))) σ →
      ∑' _r : Unit, potential (diagPot fun s ↦ √(φ s))
          (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + cS p σ)
    (hR : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ),
      σ.PosSemidef → Inv (.inl (.inl (.inr c))) σ →
      dR c σ + ∑' r, potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + cR c σ)
    (hPr : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M'))
        (Unit × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef → Inv (.inl (.inr c)) σ →
      ∑' r, potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (hwProgKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + cP c σ)
    (I : Λ.Interp) (x : QuantumComp Λ (recHwSpec X Z S M') Ω A)
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M'))) (A × QReg.of (HwReg X Z (Finset S × M')))
      ℂ} (hρ : ρ.PosSemidef) (hx : (runtimeR m₀).ForallQueries I P x ρ) :
    (runtimeR m₀).totalWeight I (extWeight (hwCost dR fun _ _ ↦ 0)) x ρ ≤
      potential (diagPot fun s ↦ √(φ s)) ρ +
        (runtimeR m₀).totalWeight I (portCh X Z S M' cS cR cP) x ρ := by
  refine totalWeight_le_potential_of_forallQueries (runtimeR m₀) I
    (diagPot fun s ↦ √(φ s)) P Inv hP
    (extWeight (hwCost dR fun _ _ ↦ 0)) (portCh X Z S M' cS cR cP) (fun i σ hσ hI ↦ ?_) x hρ hx
  rcases i with ((p | c) | c) | T
  · have hb : ∀ r : Unit, ((runtimeR m₀).step (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ p r) σ
    simp only [portCh, extWeight, sumWeight, hwCost, zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans (hS p σ hσ hI)
  · have hb : ∀ r, ((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c r) σ
    simp only [portCh, extWeight, sumWeight, hwCost]
    exact (le_of_eq (congrArg (dR c σ + ·) (tsum_congr fun r ↦ congrArg _ (hb r)))).trans
      (hR c σ hσ hI)
  · have hb : ∀ r, ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) σ
    simp only [portCh, extWeight, sumWeight, hwCost, zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans (hPr c σ hσ hI)
  · simp only [portCh, extWeight, sumWeight, zero_add, add_zero]
    exact tsum_potential_recStep_diag hφ0 hlab T hσ

end runtimeRInv

/-! ## The joint count of the selecting reads -/

section joint

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  (get : Finset S × M' → Selections) (updOf : TrialPt → Finset S × M' → Option X → Finset S × M')
  {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem encPot_labelFree (hlab : ∀ (T T' : Finset S) (m : M'), get (T, m) = get (T', m))
    (L : HonestTable) : PotLabelFree (encPot get L) := by
  intro D W T T' m
  simp only [encPot, hlab T T' m]

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem encPot_init (L : HonestTable) (m₀ : Finset S × M') :
    encPot get L ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) = 0 := by
  unfold encPot
  split_ifs
  · refine Finset.sum_eq_zero fun k _ ↦ ?_
    split_ifs
    · rw [msgCwCount_eq_tailOutCount, tailOutCount_eq_zero (fun z ↦ union_empty_h z),
        Nat.cast_zero]
    · rfl
  · rfl

/-- **The joint count of the selecting reads along a run of `runtimeR`** (the restated
`encJoint`, before averaging). Let the trial updates record codeword selections
(`CwTrialUpd`) and not read the memory label; let the calls of `x` satisfy port invariants `Inv`
(through `P`) under which every trial read port has no decompressed `⊥` at its cell, every sponge
call raises the potential `encPot` by at most its trace plus `cS`, every other read by at most `cR`
and every program call by at most its trace plus `cP`. With at most `q` sponge calls and `P'`
program calls, the joint count `cntGW` (the codeword counts of the trials' keys on their selection
reads, on good unions) along the run is at most `2^22 (q + P')` plus `2^22` times the charges
along the run: `cS`, `cP`, `cR` and at the trial reads `trialChg` (three times the count-weighted
mass off the selection reads, `2` off `TrialGood`, the read cell's recorded mass and
`2/|X| + 4/|X|²`). -/
theorem totalWeight_cntGW_le (hu : CwTrialUpd get updOf)
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
    (runtimeR m₀).totalWeight I (extWeight (hwCost (cntGW get updOf L) fun _ _ ↦ 0)) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤
      2 ^ 22 * (q + P' : ℕ) + 2 ^ 22 * (runtimeR m₀).totalWeight I
        (portCh X Z S M' cS (fun c σ ↦ trialChg get updOf L c σ + cR c σ) cP) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  set ρ := (SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix
  have hρ : ρ.PosSemidef := ((SubState.basis u).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef
  have hφ0 := encPot_nonneg get L
  have hp0 : potential (diagPot fun s ↦ √(encPot get L s)) ρ = 0 :=
    (potential_basis_init m₀ hφ0 u).trans
      ((congrArg ENNReal.ofReal (encPot_init get L m₀)).trans ENNReal.ofReal_zero)
  have htr : ENNReal.ofReal ρ.trace.re ≤ 1 := (ofReal_trace_basis_init m₀ u).le
  have hR' : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef → Inv (.inl (.inl (.inr c))) σ →
      (2 ^ 22 : ℝ≥0∞)⁻¹ * cntGW get updOf L c σ + ∑' r, potential
        (diagPot fun s ↦ √(encPot get L s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(encPot get L s)) σ +
          (0 + (trialChg get updOf L c σ + cR c σ)) := by
    intro c σ hσ hI
    rw [zero_add]
    by_cases ht : IsTrial updOf c
    · exact (trialRead_potential_le get updOf hu L ht hσ (hnb c σ ht hI)).trans
        (add_le_add le_rfl le_self_add)
    · have h0 : cntGW get updOf L c σ = 0 := by simp only [cntGW, ht, ↓reduceIte]
      have h1 : trialChg get updOf L c σ = 0 := by simp only [trialChg, ht, ↓reduceIte]
      rw [h0, h1, mul_zero, zero_add, zero_add]
      exact hR c σ ht hσ hI
  have h := totalWeight_le_potential_runtimeR_inv m₀ hφ0 (encPot_labelFree get hlab L) P Inv hP
    (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * cntGW get updOf L c σ)
    (fun p σ ↦ ENNReal.ofReal σ.trace.re + cS p σ)
    (fun c σ ↦ 0 + (trialChg get updOf L c σ + cR c σ))
    (fun c σ ↦ ENNReal.ofReal σ.trace.re + cP c σ) hS hR' hPr I x hρ hx
  have hlow : (2 ^ 22 : ℝ≥0∞)⁻¹ *
      (runtimeR m₀).totalWeight I (extWeight (hwCost (cntGW get updOf L) fun _ _ ↦ 0)) x ρ ≤
      (runtimeR m₀).totalWeight I (extWeight (hwCost
        (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * cntGW get updOf L c σ) fun _ _ ↦ 0)) x ρ := by
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m₀) I _
      (extWeight (hwCost (cntGW get updOf L) fun _ _ ↦ 0)) x ρ).symm).trans
      (totalWeight_le_totalWeight (runtimeR m₀) I (fun i σ _ ↦ ?_) x hρ)
    rcases i with ((_ | _) | _) | _
    · exact le_of_eq (mul_zero _)
    · exact le_rfl
    · exact le_of_eq (mul_zero _)
    · exact le_of_eq (mul_zero _)
  have hsplit := (totalWeight_le_totalWeight (runtimeR m₀) I
    (w := portCh X Z S M' (fun p σ ↦ ENNReal.ofReal σ.trace.re + cS p σ)
      (fun c σ ↦ 0 + (trialChg get updOf L c σ + cR c σ))
      (fun c σ ↦ ENNReal.ofReal σ.trace.re + cP c σ))
    (w' := fun i σ ↦ portCh X Z S M' (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (fun _ _ ↦ 0)
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ +
      portCh X Z S M' cS (fun c σ ↦ trialChg get updOf L c σ + cR c σ) cP i σ)
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

end Quantum.Xmss.Assembly
