module

public import Quantum.Xmss.Assembly.EncPotential
public import Quantum.Xmss.Assembly.KeyLazy
public import Quantum.Xmss.Assembly.EventSqrt

@[expose] public section

/-!
# The ports of the cross-key potential on the challenge prefix

EncPotential's `totalWeight_cntGW_le` bounds the joint count `cntGW` of the selecting reads along a
run of `runtimeR`, given port conditions `hS`, `hR`, `hPr` and `hnb` on the potential `encPot`.
This file discharges them on the challenge prefix `prefixR A L` and states the joint count with
explicit charges (`cntGP_le`).

* **Two-sided fresh bounds** (`instability_le_of_count`, `PortInst`,
  `posSemidef_spongeHardwired_certificate_inst`, `levelRaise_spongeHardwired_le`): a set of
  register states, not up-closed, whose membership changes for at most a fraction `ε` of the
  values of a fresh cell of a port, has the commutator certificate `6 ε`; its weight then rises
  at the port by at most `(2 √(6ε) + 6ε) tr σ`.
* **Layer cake** (`levSet`, `potential_layer`, `tsum_potential_sponge_layer_le`,
  `tsum_potential_read_layer_le`): a count `F ≤ H` is the sum of the indicators of its level
  sets; a port raises it by at most `H` times the raise of one level set (the port acts
  block-diagonally in the cell's value in the decompressed basis, so a fresh `k`, `k'` value moves
  the count only through `badAttachK`, `badCompleteOutK'`: `encPotN_updK_ne`, `encPotN_updK'_ne`).
* **The `h` port** (`posSemidef_diagonalPotential_drop_h`, `tsum_potential_spongeH_le`): `encPot`
  changes by at most one with one database `h` cell (`encPot_update_h_le`), so the `h` port
  raises it by at most the trace, with no charge.
* **Reads** (`keepE_le_of_portInst`, `readCost_le_of_keep`): the `k`, `k'` reads keeping the
  memory cost `(ε + 2/|X| + 2/|Z| + 2 √ε) tr σ` per level set.
* **Programs** (`progJump`, `tsum_potential_prog_le`, `KJump`, `encPot_progMap_le`,
  `progJump_le`): a program raises the potential by its trace plus `potCap` on the jump states:
  a hardwired cell with another value (none on the prefix: `forallQueries_hwSupp_prefixR`), a
  target-free fresh flip (KeyLazy's `kfW`, averaged in `uavg_kfTot_le`) or `RecJ` (a bad union
  made bad by the database value at the programmed cell): `kJumpW_le`, `kJumpPre_le`.
* **The prefix** (`PreInv`, `forallQueries_preInv`): its calls have database grade at most
  `nD q = 6q + clsCap`, hardwired grade at most `progCap`, only `ReadOk` reads and no
  decompressed `⊥` (`hnb` via ReadCost's `readNoBot_of_noBot`). The ports: `hS_prefix`,
  `hR_prefix`, `progJump_le_prefix`, `trialChg_le_prefix` (EncPotential's `trialChg_le_massW`
  with the count bound `C = nW + nD q`).
* **The joint count** (`cntGP_le`): `cntGP ≤ 2^22 (6q + progCap) + 2^22 ((3C + 3) massP +
  6q kapS + clsCap kapR + potCap kJumpPre)`; the codeword flips are `2^-128 cntGP`
  (`encWPre_le_cntGP`).

**Open**: `recJPre` (the `RecJ` weight at the prefix's `k`, `k'` program calls) is not bounded
here.
-/

universe u v w

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Sponge

open Quantum OracleSpec

/-! ## Two-sided fresh bounds -/

section inst

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]

/-- **The instability by counts**: if on every database below `t` entries and every empty cell at
most a fraction `ε` of the answers changes the label, the instability is at most `ε`. -/
theorem instability_le_of_count [UniformAnswerMeasure (A →ₒ Y)] (lab : Database A Y → Bool)
    (t : ℕ) (ε : ℝ≥0∞)
    (h : ∀ d : Database A Y, d.size < t → ∀ a, d a = none →
      ((Finset.univ.filter fun u : Y ↦ lab (Function.update d a (some u)) ≠ lab d).card :
        ℝ≥0∞) / Fintype.card Y ≤ ε) :
    Database.instability lab t ≤ ε := by
  rw [Database.instability_eq_iSup]
  refine iSup_le fun i ↦ iSup_le fun d ↦ iSup_le fun hi ↦ iSup_le fun hd ↦ iSup_le fun a ↦
    iSup_le fun ha ↦ ?_
  subst hi
  exact h d hd a ha

end inst

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- **A two-sided fresh bound at one port**: for every triple whose databases have fewer than `t`
entries and every empty cell of the port's database, at most a fraction `ε` of the values change
membership in `S`. -/
def PortInst (S : Set (Dbs X Z)) [DecidablePred (· ∈ S)] : SpongePort → ℕ → ℝ≥0∞ → Prop
  | .h, t, ε => ∀ D : Dbs X Z, D.h.size < t → D.k.size < t → D.k'.size < t → ∀ z, D.h z = none →
      ((Finset.univ.filter fun u : X ↦
        ¬ ((({ D with h := Function.update D.h z (some u) } : Dbs X Z) ∈ S) ↔ D ∈ S)).card :
          ℝ≥0∞) / Fintype.card X ≤ ε
  | .k, t, ε => ∀ D : Dbs X Z, D.h.size < t → D.k.size < t → D.k'.size < t → ∀ x, D.k x = none →
      ((Finset.univ.filter fun u : Z ↦
        ¬ ((({ D with k := Function.update D.k x (some u) } : Dbs X Z) ∈ S) ↔ D ∈ S)).card :
          ℝ≥0∞) / Fintype.card Z ≤ ε
  | .k', t, ε => ∀ D : Dbs X Z, D.h.size < t → D.k.size < t → D.k'.size < t → ∀ x,
      D.k' x = none → ((Finset.univ.filter fun u : Z ↦
        ¬ ((({ D with k' := Function.update D.k' x (some u) } : Dbs X Z) ∈ S) ↔ D ∈ S)).card :
          ℝ≥0∞) / Fintype.card Z ≤ ε

omit [DecidableEq X] [DecidableEq Z] in
theorem card_div_le_of_imp {Y : Type} [Fintype Y] {p q : Y → Prop} [DecidablePred p]
    [DecidablePred q] (h : ∀ u, p u → q u) {ε : ℝ≥0∞}
    (hq : ((Finset.univ.filter q).card : ℝ≥0∞) / Fintype.card Y ≤ ε) :
    ((Finset.univ.filter p).card : ℝ≥0∞) / Fintype.card Y ≤ ε :=
  le_trans (ENNReal.div_le_div_right (Nat.cast_le.mpr (Finset.card_le_card fun u hu ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact h u hu)) _) hq

variable [AddCommGroup X] [AddCommGroup Z]

/-- **The per-port certificate from a two-sided fresh bound**, at the `n`-th call, with rate `6 ε`
(as `posSemidef_spongeCompressed_certificate`, without upward closure). -/
theorem posSemidef_spongeCompressed_certificate_inst (S : Set (Dbs X Z)) [DecidablePred (· ∈ S)]
    {n : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤) (i : SpongePort) (hε : PortInst S i (n + 1) ε) :
    let U := (spongeCompressed X Z).U i
    let Q := (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ dbsProjector S
    let P : Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ :=
      diagonal fun m ↦ if dbGrade m.2 ≤ n then (1 : ℂ) else 0
    ((6 * ε.toReal) • (1 : Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ) -
      ((Q * U - U * Q) * P)ᴴ * ((Q * U - U * Q) * P)).PosSemidef := by
  have hr0 : 0 ≤ 6 * ε.toReal := by positivity
  cases i
  · let _ : UniformAnswerMeasure (Z →ₒ X) := UniformAnswerMeasure.ofFiniteNonempty _
    refine posSemidef_port_certificate (splitH (Z × X)) (fun d b ↦ (d, b.1, b.2))
      (fun _ _ _ ↦ rfl) (fun D : DbReg X Z ↦ decide (D.toDbs ∈ S)) dbGrade
      (fun b ↦ b.1.size ≤ n ∧ b.2.size ≤ n) n
      (fun d b ↦ by simp only [dbGrade, max_le_iff]) hr0 fun b hb ↦ ?_
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hεtop
      (instability_le_of_count _ _ _ fun d hsize z hz ↦ ?_)) (by norm_num)
    refine card_div_le_of_imp (fun u hu ↦ ?_)
      (hε ⟨d, b.1, b.2⟩ hsize (Nat.lt_succ_of_le hb.1) (Nat.lt_succ_of_le hb.2) z hz)
    rwa [ne_eq, decide_eq_decide] at hu
  · let _ : UniformAnswerMeasure (X →ₒ Z) := UniformAnswerMeasure.ofFiniteNonempty _
    refine posSemidef_port_certificate (splitK (X × Z)) (fun d b ↦ (b.1, d, b.2))
      (fun _ _ _ ↦ rfl) (fun D : DbReg X Z ↦ decide (D.toDbs ∈ S)) dbGrade
      (fun b ↦ b.1.size ≤ n ∧ b.2.size ≤ n) n
      (fun d b ↦ by simp only [dbGrade, max_le_iff]; tauto) hr0 fun b hb ↦ ?_
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hεtop
      (instability_le_of_count _ _ _ fun d hsize x hx ↦ ?_)) (by norm_num)
    refine card_div_le_of_imp (fun u hu ↦ ?_)
      (hε ⟨b.1, d, b.2⟩ (Nat.lt_succ_of_le hb.1) hsize (Nat.lt_succ_of_le hb.2) x hx)
    rwa [ne_eq, decide_eq_decide] at hu
  · let _ : UniformAnswerMeasure (X →ₒ Z) := UniformAnswerMeasure.ofFiniteNonempty _
    refine posSemidef_port_certificate (splitK' (X × Z)) (fun d b ↦ (b.1, b.2, d))
      (fun _ _ _ ↦ rfl) (fun D : DbReg X Z ↦ decide (D.toDbs ∈ S)) dbGrade
      (fun b ↦ b.1.size ≤ n ∧ b.2.size ≤ n) n
      (fun d b ↦ by simp only [dbGrade, max_le_iff]; tauto) hr0 fun b hb ↦ ?_
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hεtop
      (instability_le_of_count _ _ _ fun d hsize x hx ↦ ?_)) (by norm_num)
    refine card_div_le_of_imp (fun u hu ↦ ?_)
      (hε ⟨b.1, b.2, d⟩ (Nat.lt_succ_of_le hb.1) (Nat.lt_succ_of_le hb.2) hsize x hx)
    rwa [ne_eq, decide_eq_decide] at hu

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **The per-port certificate of the hardwired runtime from two-sided fresh bounds** of every
slice (as `posSemidef_spongeHardwired_certificate`). -/
theorem posSemidef_spongeHardwired_certificate_inst (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] {n : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤) (W₀ : Hw X Z) (m₀ : M)
    (i : SpongePort) (hε : ∀ W m, PortInst (slice S W m) i (n + 1) ε) :
    let U := (spongeHardwired X Z W₀ m₀).U i
    let Q := (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ hwProjector S
    let P : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ :=
      diagonal fun q ↦ if dbGrade q.2.1 ≤ n then (1 : ℂ) else 0
    ((6 * ε.toReal) •
        (1 : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ) -
      ((Q * U - U * Q) * P)ᴴ * ((Q * U - U * Q) * P)).PosSemidef := by
  intro U Q P
  let e := hwSplit X Z M (spongeIn X Z i)
  let Ub : Hw X Z × M →
      Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ := fun b ↦
    labelProjector (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1) false *
        (spongeCompressed X Z).U i +
      hwShift b.1 i ⊗ₖ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)
  let Qb : Hw X Z × M →
      Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ := fun b ↦
    (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ dbsProjector (slice S b.1 b.2)
  let Pb : Hw X Z × M →
      Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ := fun _ ↦
    diagonal fun q : spongeIn X Z i × DbReg X Z ↦ if dbGrade q.2 ≤ n then (1 : ℂ) else 0
  have hu : U = liftBlocks e Ub := spongeHardwired_U W₀ m₀ i
  have hq : Q = liftBlocks e Qb := one_kronecker_hwProjector_eq_liftBlocks S _
  have hp : P = liftBlocks e Pb := (liftBlocks_diagonal e _).symm
  have hb (b : Hw X Z × M) :
      ((6 * ε.toReal) • (1 : Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ) -
        (((Qb * Ub - Ub * Qb) * Pb) b)ᴴ * (((Qb * Ub - Ub * Qb) * Pb) b)).PosSemidef := by
    have hQL : Qb b * labelProjector (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1)
        false = labelProjector (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1) false *
          Qb b := by
      simp only [Qb, dbsProjector, one_kronecker_labelProjector]
      exact labelProjector_mul_comm _ _ _ _
    have hQN : Qb b * (hwShift b.1 i ⊗ₖ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) =
        (hwShift b.1 i ⊗ₖ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) * Qb b := by
      simp only [Qb, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    exact posSemidef_masked_certificate (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1)
      ((spongeCompressed X Z).U i) _ (Qb b) (Pb b) hQL hQN
      (posSemidef_spongeCompressed_certificate_inst (slice S b.1 b.2) hεtop i (hε b.1 b.2))
  have hh := posSemidef_liftBlocks e hb
  change (liftBlocks e ((6 * ε.toReal) • 1 -
    (fun b ↦ (((Qb * Ub - Ub * Qb) * Pb) b)ᴴ) * ((Qb * Ub - Ub * Qb) * Pb))).PosSemidef at hh
  rw [liftBlocks_sub, liftBlocks_smul, liftBlocks_one] at hh
  change (_ - liftBlocks e ((fun b ↦ (((Qb * Ub - Ub * Qb) * Pb) b)ᴴ) *
    ((Qb * Ub - Ub * Qb) * Pb))).PosSemidef at hh
  rw [liftBlocks_mul, liftBlocks_adjoint, liftBlocks_mul, liftBlocks_sub, liftBlocks_mul,
    liftBlocks_mul, ← hq, ← hp, ← hu] at hh
  exact hh

omit [AddCommGroup X] [AddCommGroup Z] [Fintype M] in
/-- The event projector of the hardwired register is the diagonal potential of the indicator. -/
theorem hwProjector_eq_diagPot (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] :
    hwProjector S = diagPot fun s ↦ √(if s ∈ S then (1 : ℝ) else 0) := by
  unfold hwProjector labelProjector diagPot
  congr 1
  funext s
  by_cases hs : s ∈ S <;> simp [hs]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **The weight of an event of the hardwired register** as a diagonal sum. -/
theorem potential_hwProjector_eq {α : Type} [Fintype α] [DecidableEq α] (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (τ : Matrix (α × HwReg X Z M) (α × HwReg X Z M) ℂ) :
    QuantumRuntime.potential (hwProjector S) τ =
      ENNReal.ofReal (∑ q, (if q.2 ∈ S then (1 : ℝ) else 0) * (τ q q).re) := by
  rw [hwProjector_eq_diagPot]
  exact Xmss.Assembly.potential_diagPot_sqrt (fun s ↦ by split_ifs <;> norm_num) τ

/-- `a' ≤ a + (2 √r + r) t` from `√a' ≤ √a + √(r t)` and `a ≤ t`. -/
theorem le_add_of_sqrt_le {a a' t r : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (hr : 0 ≤ r) (ha' : 0 ≤ a')
    (h : √a' ≤ √a + √(r * t)) : a' ≤ a + (2 * √r + r) * t := by
  have ht : 0 ≤ t := ha.trans hat
  have hsq : a' ≤ (√a + √(r * t)) ^ 2 := by
    rw [← Real.sq_sqrt ha']
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  have h1 : √a ≤ √t := Real.sqrt_le_sqrt hat
  have h2 : √(r * t) = √r * √t := Real.sqrt_mul hr t
  have h3 : √t * √t = t := Real.mul_self_sqrt ht
  have h4 : √r * √r = r := Real.mul_self_sqrt hr
  rw [add_sq, Real.sq_sqrt ha, h2] at hsq
  have h5 : √a * (√r * √t) ≤ √t * (√r * √t) :=
    mul_le_mul_of_nonneg_right h1 (mul_nonneg (Real.sqrt_nonneg r) (Real.sqrt_nonneg t))
  have h6 : (√r * √t) ^ 2 = r * t := by
    rw [mul_pow, Real.sq_sqrt hr, Real.sq_sqrt ht]
  have h7 : √t * (√r * √t) = √r * t := by
    calc √t * (√r * √t) = √r * (√t * √t) := by ring
      _ = √r * t := by rw [h3]
  nlinarith

/-- **A sponge port raises the weight of an event with two-sided fresh bounds** by at most
`(2 √(6ε) + 6ε) tr σ`, on inputs of database grade at most `N` (no upward closure needed). -/
theorem levelRaise_spongeHardwired_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] {N : ℕ}
    {ε : ℝ} (hε0 : 0 ≤ ε) (W₀ : Hw X Z) (m₀ : M) (i : SpongePort)
    (hε : ∀ W m, PortInst (slice S W m) i (N + 1) (ENNReal.ofReal ε))
    {σ : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef)
    (hσg : QuerySupportedOn (fun q : spongeIn X Z i × HwReg X Z M ↦ dbGrade q.2.1) (Set.Iic N) σ) :
    ∑ q, (if q.2 ∈ S then (1 : ℝ) else 0) *
        ((MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U i) σ) q q).re ≤
      ∑ q, (if q.2 ∈ S then (1 : ℝ) else 0) * (σ q q).re +
        (2 * √(6 * ε) + 6 * ε) * σ.trace.re := by
  set U := (spongeHardwired X Z W₀ m₀).U i
  set Q := (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ hwProjector S
  set a' := ∑ q, (if q.2 ∈ S then (1 : ℝ) else 0) * ((MatrixMap.conj U σ) q q).re
  set a := ∑ q, (if q.2 ∈ S then (1 : ℝ) else 0) * (σ q q).re
  have hre : ∀ τ : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ,
      τ.PosSemidef → ∀ q, 0 ≤ (τ q q).re := fun τ hτ q ↦ (Complex.nonneg_iff.1 hτ.diag_nonneg).1
  have hσ' : (MatrixMap.conj U σ).PosSemidef := by
    rw [MatrixMap.conj_apply]
    exact hσ.mul_mul_conjTranspose_same U
  have ha : 0 ≤ a := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hre σ hσ q)
  have ha' : 0 ≤ a' :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hre _ hσ' q)
  have hat : a ≤ σ.trace.re := by
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [Matrix.diag_apply]
    split_ifs
    · rw [one_mul]
    · rw [zero_mul]
      exact hre σ hσ q
  have hpot : ∀ τ : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ,
      QuantumRuntime.potential (hwProjector S) τ = ENNReal.ofReal (MatrixMap.conj Q τ).trace.re :=
    fun τ ↦ by rw [QuantumRuntime.potential, MatrixMap.amplifyLeft_conj]
  have hεtop : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
  have hr0 : (0 : ℝ) ≤ 6 * (ENNReal.ofReal ε).toReal := by positivity
  have hmain : QuantumRuntime.potential (hwProjector S) (MatrixMap.conj U σ) ^ (2⁻¹ : ℝ) ≤
      QuantumRuntime.potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (6 * ε) * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) := by
    rw [hpot, hpot, ← LinearMap.comp_apply, ← MatrixMap.conj_mul,
      show Q * U = U * Q + (Q * U - U * Q) by abel]
    refine (MatrixMap.ofReal_trace_conj_add_rpow_le hσ _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [MatrixMap.conj_mul, LinearMap.comp_apply,
        trace_conj_of_mem_unitaryGroup ((spongeHardwired X Z W₀ m₀).unitary i)]
    · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      refine (ofReal_trace_conj_le_of_certificate _ _ hr0
        (posSemidef_spongeHardwired_certificate_inst S hεtop W₀ m₀ i hε) hσ
        (hσg.conj_diagonal_eq_self fun q hq ↦ by simp [Set.mem_Iic.mp hq])).trans_eq ?_
      rw [ENNReal.toReal_ofReal hε0]
  rw [potential_hwProjector_eq, potential_hwProjector_eq, ENNReal.ofReal_rpow_inv_two,
    ENNReal.ofReal_rpow_inv_two, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_inv_two, ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmain
  exact le_add_of_sqrt_le ha hat (by positivity) ha' hmain

/-! ## The `h` port of a potential that changes by at most one with an `h` cell -/

section hport

omit [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z] in
theorem le_add_one_of_eraseCell_eq_h {φ : HwReg X Z M → ℝ}
    (hφ : ∀ (D : DbReg X Z) b z v, φ ((Function.update D.1 z v, D.2.1, D.2.2), b) ≤ φ (D, b) + 1)
    (a : spongeIn X Z .h) {D D' : DbReg X Z} (b : Hw X Z × M)
    (h : eraseCell .h a D' = eraseCell .h a D) : φ (D, b) ≤ φ (D', b) + 1 := by
  have hD : D = (Function.update D'.1 (a : Z × X).1 (D.1 (a : Z × X).1), D'.2.1, D'.2.2) := by
    simp only [eraseCell, Prod.mk.injEq] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    refine Prod.ext (funext fun z ↦ ?_) (Prod.ext h₂.symm h₃.symm)
    by_cases hz : z = (a : Z × X).1
    · subst hz
      simp
    · simpa [Function.update_of_ne hz] using (congrFun h₁ z).symm
  rw [hD]
  exact hφ D' b _ _

omit [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z] in
theorem le_cellMin_add_one_h {φ : HwReg X Z M → ℝ}
    (hφ : ∀ (D : DbReg X Z) b z v, φ ((Function.update D.1 z v, D.2.1, D.2.2), b) ≤ φ (D, b) + 1)
    (a : spongeIn X Z .h) (s : HwReg X Z M) : φ s ≤ cellMin φ .h a s + 1 := by
  obtain ⟨D, hD, he⟩ := Finset.exists_mem_eq_inf'
    (s := Finset.univ.filter fun D : DbReg X Z ↦ eraseCell .h a D = eraseCell .h a s.1)
    ⟨s.1, by simp⟩ fun D ↦ φ (D, s.2)
  rw [cellMin, he]
  exact le_add_one_of_eraseCell_eq_h hφ a s.2 (Finset.mem_filter.mp hD).2

/-- **The `h` port raises a diagonal potential that changes by at most one with an `h` cell by at
most one**: `Uᴴ (1 ⊗ Φ) U ≤ 1 ⊗ Φ + 1` (`posSemidef_diagonalPotential_drop` at the `h` port). -/
theorem posSemidef_diagonalPotential_drop_h {φ : HwReg X Z M → ℝ}
    (hφ : ∀ (D : DbReg X Z) b z v, φ ((Function.update D.1 z v, D.2.1, D.2.2), b) ≤ φ (D, b) + 1)
    (W₀ : Hw X Z) (m₀ : M) :
    let U := (spongeHardwired X Z W₀ m₀).U .h
    ((1 : Matrix (spongeIn X Z .h) (spongeIn X Z .h) ℂ) ⊗ₖ diagPot φ + 1 -
      Uᴴ * ((1 : Matrix (spongeIn X Z .h) (spongeIn X Z .h) ℂ) ⊗ₖ diagPot φ) * U).PosSemidef := by
  intro U
  set Φ := (1 : Matrix (spongeIn X Z .h) (spongeIn X Z .h) ℂ) ⊗ₖ diagPot φ
  set Ψ := diagPot fun q : spongeIn X Z .h × HwReg X Z M ↦ cellMin φ .h q.1 q.2
  have hΦ : Φ = diagPot fun q : spongeIn X Z .h × HwReg X Z M ↦ φ q.2 := by
    simp only [Φ, diagPot, ← diagonal_one, diagonal_kronecker_diagonal, one_mul]
  have hUΨ : U * Ψ = Ψ * U := by
    ext ⟨a', s'⟩ ⟨a, s⟩
    simp only [Ψ, diagPot, mul_diagonal, diagonal_mul]
    by_cases hU : U (a', s') (a, s) = 0
    · simp [hU]
    · obtain ⟨hb, ha, hD⟩ := eraseCell_of_spongeHardwired_U_ne_zero W₀ m₀ .h a a' s s' hU
      rw [cellMin_congr φ .h ha hb hD, mul_comm]
  have hUU : Uᴴ * U = 1 := (spongeHardwired X Z W₀ m₀).conjTranspose_mul_self .h
  have hconj : Uᴴ * (Ψ + 1) * U = Ψ + 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, Matrix.mul_assoc, ← hUΨ,
      ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have h₁ : (Φ - Ψ).PosSemidef := by
    simp only [hΦ, Ψ, diagPot]
    rw [diagonal_sub]
    exact posSemidef_diagonal_iff.mpr fun q ↦ by
      rw [← Complex.ofReal_sub]
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr (cellMin_le φ .h q.1 q.2))
  have h₂ : (Ψ + 1 - Φ).PosSemidef := by
    simp only [hΦ, Ψ, diagPot]
    rw [← diagonal_one, diagonal_add, diagonal_sub]
    exact posSemidef_diagonal_iff.mpr fun q ↦ by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_sub]
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr (le_cellMin_add_one_h hφ q.1 q.2))
  have heq : Φ + 1 - Uᴴ * Φ * U = (Φ - Ψ) + Uᴴ * (Ψ + 1 - Φ) * U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hconj]
    abel
  rw [heq]
  exact h₁.add (h₂.conjTranspose_mul_mul_same U)

/-- **The `h` port raises such a potential by at most the trace.** -/
theorem tsum_potential_spongeH_le {φ : HwReg X Z M → ℝ} (hφ0 : ∀ s, 0 ≤ φ s)
    (hφ : ∀ (D : DbReg X Z) b z v, φ ((Function.update D.1 z v, D.2.1, D.2.2), b) ≤ φ (D, b) + 1)
    (W₀ : Hw X Z) (m₀ : M)
    {σ : Matrix (spongeIn X Z .h × HwReg X Z M) (spongeIn X Z .h × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' _r : Unit, QuantumRuntime.potential (diagPot fun s ↦ √(φ s))
        (MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U .h) σ) ≤
      QuantumRuntime.potential (diagPot fun s ↦ √(φ s)) σ + ENNReal.ofReal σ.trace.re := by
  have hd := QuantumRuntime.drop_of_posSemidef
    (fun _ : Unit ↦ (spongeHardwired X Z W₀ m₀).U .h)
    (diagPot fun s ↦ √(φ s)) (diagPot fun s ↦ √(φ s)) 1 hσ (by
      rw [Fintype.sum_unique, Xmss.Assembly.diagPot_sqrt_gram hφ0]
      exact posSemidef_diagonalPotential_drop_h hφ W₀ m₀)
  rw [Matrix.one_mul] at hd
  exact le_add_self.trans hd

end hport

/-! ## Level sets of a count -/

section layer

/-- **The level sets of a count**, inside the hardwired grade `Nw`. -/
def levSet (F : HwReg X Z M → ℕ) (Nw m : ℕ) : Set (HwReg X Z M) :=
  {s | dbGrade s.2.1 ≤ Nw ∧ m < F s}

/-- Membership in a level set, decided classically. -/
noncomputable instance levSetDec (F : HwReg X Z M → ℕ) (Nw m : ℕ) :
    DecidablePred (· ∈ levSet F Nw m) :=
  Classical.decPred _

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z]
  [Fintype M] [DecidableEq M] in
theorem sum_range_ite_lt {f H : ℕ} (h : f ≤ H) :
    ∑ m ∈ Finset.range H, (if m < f then (1 : ℝ) else 0) = f := by
  rw [← Finset.sum_range_add_sum_Ico _ h,
    Finset.sum_congr rfl fun m hm ↦ ite_eq_left (Finset.mem_range.mp hm),
    Finset.sum_eq_zero fun m hm ↦ ite_eq_right (not_lt.mpr (Finset.mem_Ico.mp hm).1)]
  simp

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **The layer cake of a count**: on an operator supported where the hardwired grade is at most
`Nw` and the count at most `H`, the potential of the count is the sum of the weights of its first
`H` level sets. -/
theorem potential_layer {α : Type} [Fintype α] [DecidableEq α] (F : HwReg X Z M → ℕ)
    (Nw H : ℕ) (G : Set (HwReg X Z M)) (hG : ∀ s ∈ G, dbGrade s.2.1 ≤ Nw ∧ F s ≤ H)
    {τ : Matrix (α × HwReg X Z M) (α × HwReg X Z M) ℂ} (hτ : τ.PosSemidef)
    (hsupp : QuerySupportedOn (fun q : α × HwReg X Z M ↦ q.2) G τ) :
    QuantumRuntime.potential (diagPot fun s ↦ √(F s : ℝ)) τ =
      ∑ m ∈ Finset.range H, QuantumRuntime.potential (hwProjector (levSet F Nw m)) τ := by
  have hre : ∀ q, 0 ≤ (τ q q).re := fun q ↦ (Complex.nonneg_iff.1 hτ.diag_nonneg).1
  rw [Xmss.Assembly.potential_diagPot_sqrt (fun s ↦ Nat.cast_nonneg _)]
  simp only [potential_hwProjector_eq]
  rw [← ENNReal.ofReal_sum_of_nonneg fun m _ ↦ Finset.sum_nonneg fun q _ ↦
    mul_nonneg (by split_ifs <;> norm_num) (hre q)]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← Finset.sum_mul]
  by_cases h0 : τ q q = 0
  · rw [h0, Complex.zero_re, mul_zero, mul_zero]
  · obtain ⟨hW, hF⟩ := hG q.2 (hsupp q q h0).1
    congr 1
    rw [← sum_range_ite_lt hF]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    by_cases hm : m < F q.2
    · rw [ite_eq_left (show q.2 ∈ levSet F Nw m from ⟨hW, hm⟩), ite_eq_left hm]
    · rw [ite_eq_right (show q.2 ∉ levSet F Nw m from fun h ↦ hm h.2), ite_eq_right hm]

/-- **A sponge port against a count with two-sided fresh bounds on its level sets**: on inputs of
database grade at most `N` and hardwired grade at most `Nw`, with the count at most `H` up to
database grade `N + 1`, the potential rises by at most `H (2 √(6ε) + 6ε) tr σ`. -/
theorem tsum_potential_sponge_layer_le (F : HwReg X Z M → ℕ) (Nw N H : ℕ)
    (hF : ∀ s : HwReg X Z M, dbGrade s.2.1 ≤ Nw → dbGrade s.1 ≤ N + 1 → F s ≤ H)
    {ε : ℝ} (hε0 : 0 ≤ ε) (W₀ : Hw X Z) (m₀ : M) (i : SpongePort)
    (hε : ∀ m W mm, PortInst (slice (levSet F Nw m) W mm) i (N + 1) (ENNReal.ofReal ε))
    {σ : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef)
    (hsupp : QuerySupportedOn (fun q : spongeIn X Z i × HwReg X Z M ↦ q.2)
      {s | dbGrade s.1 ≤ N ∧ dbGrade s.2.1 ≤ Nw} σ) :
    ∑' _r : Unit, QuantumRuntime.potential (diagPot fun s ↦ √(F s : ℝ))
        (MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U i) σ) ≤
      QuantumRuntime.potential (diagPot fun s ↦ √(F s : ℝ)) σ +
        ENNReal.ofReal (H * ((2 * √(6 * ε) + 6 * ε) * σ.trace.re)) := by
  set U := (spongeHardwired X Z W₀ m₀).U i
  have hσ' : (MatrixMap.conj U σ).PosSemidef := by
    rw [MatrixMap.conj_apply]
    exact hσ.mul_mul_conjTranspose_same U
  have hpost : QuerySupportedOn (fun q : spongeIn X Z i × HwReg X Z M ↦ q.2)
      {s | dbGrade s.1 ≤ N + 1 ∧ dbGrade s.2.1 ≤ Nw} (MatrixMap.conj U σ) :=
    hsupp.conj fun q' q hK hq ↦ by
      obtain ⟨hb, -, -⟩ := eraseCell_of_spongeHardwired_U_ne_zero W₀ m₀ i q.1 q'.1 q.2 q'.2 hK
      refine ⟨(dbGrade_le_of_spongeHardwired_U_ne_zero W₀ m₀ i q.1 q'.1 q.2 q'.2 hK).trans
        (Nat.add_le_add_right hq.1 1), ?_⟩
      rw [show q'.2.2.1 = q.2.2.1 from congrArg Prod.fst hb]
      exact hq.2
  have hg : QuerySupportedOn (fun q : spongeIn X Z i × HwReg X Z M ↦ dbGrade q.2.1)
      (Set.Iic N) σ := hsupp.imp fun q hq ↦ Set.mem_Iic.mpr hq.1
  rw [tsum_fintype, Fintype.sum_unique,
    potential_layer F Nw H _ (fun s hs ↦ ⟨hs.2, hF s hs.2 hs.1⟩) hσ' hpost,
    potential_layer F Nw H _ (fun s hs ↦ ⟨hs.2, hF s hs.2 (hs.1.trans (Nat.le_succ _))⟩) hσ
      hsupp]
  calc ∑ m ∈ Finset.range H, QuantumRuntime.potential (hwProjector (levSet F Nw m))
        (MatrixMap.conj U σ)
      ≤ ∑ m ∈ Finset.range H, (QuantumRuntime.potential (hwProjector (levSet F Nw m)) σ +
          ENNReal.ofReal ((2 * √(6 * ε) + 6 * ε) * σ.trace.re)) := by
        refine Finset.sum_le_sum fun m _ ↦ ?_
        rw [potential_hwProjector_eq, potential_hwProjector_eq]
        exact (ENNReal.ofReal_le_ofReal (levelRaise_spongeHardwired_le (levSet F Nw m) hε0 W₀ m₀
          i (hε m) hσ hg)).trans ENNReal.ofReal_add_le
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **A read port against a count**: on inputs of database grade at most `N` and hardwired grade
at most `Nw`, with the count at most `H` up to database grade `N + 1`, and no decompressed `⊥` at
the read cell, the potential rises by at most `H` times a bound of the refined read cost
(`readCost`) of every level set. -/
theorem tsum_potential_read_layer_le [Nonempty X] [Nonempty Z] (F : HwReg X Z M → ℕ)
    (Nw N H : ℕ) (hF : ∀ s : HwReg X Z M, dbGrade s.2.1 ≤ Nw → dbGrade s.1 ≤ N + 1 → F s ≤ H)
    (c : HwRead X Z M) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) (hnb : ReadNoBot c σ) {b : ℝ≥0∞}
    (hb : ∀ m, readCost (levSet F Nw m) c σ ≤ b)
    (hsupp : QuerySupportedOn (fun q : Unit × HwReg X Z M ↦ q.2)
      {s | dbGrade s.1 ≤ N ∧ dbGrade s.2.1 ≤ Nw} σ) :
    ∑' r, QuantumRuntime.potential (diagPot fun s ↦ √(F s : ℝ))
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      QuantumRuntime.potential (diagPot fun s ↦ √(F s : ℝ)) σ + H * b := by
  have hpost : ∀ r, QuerySupportedOn (fun q : Unit × HwReg X Z M ↦ q.2)
      {s | dbGrade s.1 ≤ N + 1 ∧ dbGrade s.2.1 ≤ Nw} (MatrixMap.conj (hwReadKraus c r) σ) :=
    fun r ↦ hsupp.conj fun q' q hK hq ↦ by
      refine ⟨(dbGrade_le_of_hwReadKraus_ne_zero c r q.1 q'.1 q.2 q'.2 hK).trans
        (Nat.add_le_add_right hq.1 1), ?_⟩
      rw [hw_eq_of_hwReadKraus_ne_zero c r q.1 q'.1 q.2 q'.2 hK]
      exact hq.2
  have hσ' : ∀ r, (MatrixMap.conj (hwReadKraus c r) σ).PosSemidef := fun r ↦ by
    rw [MatrixMap.conj_apply]
    exact hσ.mul_mul_conjTranspose_same _
  rw [tsum_congr fun r ↦ potential_layer F Nw H _ (fun s hs ↦ ⟨hs.2, hF s hs.2 hs.1⟩) (hσ' r)
      (hpost r),
    Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable),
    potential_layer F Nw H _ (fun s hs ↦ ⟨hs.2, hF s hs.2 (hs.1.trans (Nat.le_succ _))⟩) hσ
      hsupp]
  calc ∑ m ∈ Finset.range H, ∑' r, QuantumRuntime.potential (hwProjector (levSet F Nw m))
        (MatrixMap.conj (hwReadKraus c r) σ)
      ≤ ∑ m ∈ Finset.range H, (QuantumRuntime.potential (hwProjector (levSet F Nw m)) σ + b) :=
        Finset.sum_le_sum fun m _ ↦
          (potential_hwReadKraus_le_refined (levSet F Nw m) c hσ hnb).trans (add_le_add le_rfl (hb m))
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end layer

/-! ## Program ports against a diagonal potential -/

section prog

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **A classical step on a diagonal weight**: Kraus operators `|f s⟩⟨s|` on the states of index
`i`, with `(idx, f)` injective, give the weight at the image (`gram_classical` with weights). -/
theorem gram_classical_diag {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (K : ι → Matrix n n ℂ) (idx : n → ι) (f : n → n)
    (hK : ∀ i t s, K i t s = if i = idx s ∧ t = f s then 1 else 0)
    (hinj : ∀ s s', idx s = idx s' → f s = f s' → s = s') (g : n → ℝ) :
    ∑ i, (K i)ᴴ * diagonal (fun s ↦ ((g s : ℝ) : ℂ)) * K i =
      diagonal fun s ↦ ((g (f s) : ℝ) : ℂ) := by
  ext t s
  rw [Matrix.sum_apply, Finset.sum_eq_single (idx s)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (f s)]
    · rw [mul_diagonal, conjTranspose_apply, hK (idx s) (f s) s,
        ite_eq_left ⟨rfl, rfl⟩, mul_one, hK (idx s) (f s) t, diagonal_apply]
      by_cases hts : t = s
      · subst hts
        simp
      · rw [ite_eq_right fun h ↦ hts (hinj t s h.1.symm h.2.symm), ite_eq_right hts]
        simp
    · intro u _ hu
      rw [hK (idx s) u s, ite_eq_right fun h ↦ hu h.2]
      simp
    · simp
  · intro i _ hi
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    rw [hK i u s, ite_eq_right fun h ↦ hi h.1]
    simp
  · simp

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **A program port on a diagonal potential**: the weights after the port are those of the
programmed states. -/
theorem tsum_potential_prog_eq {φ : HwReg X Z M → ℝ} (hφ0 : ∀ s, 0 ≤ φ s) (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    ∑' r, QuantumRuntime.potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (hwProgKraus c r) σ) =
      ENNReal.ofReal (∑ q, φ (progMap c q.2) * (σ q q).re) := by
  have hpost : ∀ r, 0 ≤ dW (fun q : Unit × HwReg X Z M ↦ φ q.2)
      (MatrixMap.conj (hwProgKraus c r) σ) := fun r ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  have hpot : ∀ τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ,
      QuantumRuntime.potential (diagPot fun s ↦ √(φ s)) τ =
        ENNReal.ofReal (dW (fun q : Unit × HwReg X Z M ↦ φ q.2) τ) :=
    fun τ ↦ Xmss.Assembly.potential_diagPot_sqrt hφ0 τ
  simp only [hpot]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hpost r, sum_dW_conj,
    gram_classical_diag (hwProgKraus c) (fun q ↦ progIdx c q.2) (fun q ↦ ((), progMap c q.2))
      (hwProgKraus_apply c)
      (fun q q' hi hf ↦ Prod.ext rfl (progMap_inj c hi (congrArg Prod.snd hf))),
    re_trace_diagonal_mul]

end prog

end Quantum.Sponge


/-! ## Counts through fresh `k`, `k'` cells -/

namespace Quantum.Sponge

section outUpd

variable {X Z Y : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] {π : Equiv.Perm (X × Z)} {out : X → Y}

/-- **A `k` value outside `badAttachK` keeps the counted cells** of a good database. -/
theorem outAt_update_k_iff {U : Dbs X Z} (hG : Good π U) {x : X} (hx : U.k x = none) {y : Z}
    (hy : y ∉ badAttachK π U x) (P : List X → Prop) (Qo : Y → Prop) (z : Z) :
    OutAt π { U with k := Function.update U.k x (some y) } out P Qo z ↔ OutAt π U out P Qo z := by
  constructor
  · rintro ⟨t, xi, w, hP, hi, hw, hq⟩
    rcases (updateK_tails hG hx hy).2 t z hi.isTail with ht | hn
    · exact ⟨t, xi, w, hP, IsHeadTail.of_isTail (extends_update_k hx) ht hi, hw, hq⟩
    · change U.h z = some w at hw
      rw [hn] at hw
      cases hw
  · rintro ⟨t, xi, w, hP, hi, hw, hq⟩
    exact ⟨t, xi, w, hP, hi.mono (extends_update_k hx), hw, hq⟩

/-- **A `k'` value outside `badCompleteOutK'` keeps the counted cells** of a good database. -/
theorem outAt_update_k'_iff {U : Dbs X Z} (hG : Good π U) {x : X} (hx : U.k' x = none) {y : Z}
    (hy : y ∉ badCompleteOutK' π U x) (P : List X → Prop) (Qo : Y → Prop) (z : Z) :
    OutAt π { U with k' := Function.update U.k' x (some y) } out P Qo z ↔
      OutAt π U out P Qo z := by
  constructor
  · rintro ⟨t, xi, w, hP, hi, hw, hq⟩
    rcases (updateK'_tails hG hx hy).2 t z hi.isTail with ht | hn
    · exact ⟨t, xi, w, hP, IsHeadTail.of_isTail (extends_update_k' hx) ht hi, hw, hq⟩
    · change U.h z = some w at hw
      rw [hn] at hw
      cases hw
  · rintro ⟨t, xi, w, hP, hi, hw, hq⟩
    exact ⟨t, xi, w, hP, hi.mono (extends_update_k' hx), hw, hq⟩

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
open scoped Classical in
theorem tailOutCount_congr_of_iff {U U' : Dbs X Z} {P : List X → Prop} {Qo : Y → Prop}
    (h : ∀ z, OutAt π U' out P Qo z ↔ OutAt π U out P Qo z) :
    tailOutCount π U' out P Qo = tailOutCount π U out P Qo := by
  unfold tailOutCount
  exact congrArg Finset.card (Finset.filter_congr fun z _ ↦ h z)

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
open scoped Classical in
theorem tailOutCount_le_of_imp {U U' : Dbs X Z} {P : List X → Prop} {Qo : Y → Prop}
    (h : ∀ z, OutAt π U' out P Qo z → OutAt π U out P Qo z) :
    tailOutCount π U' out P Qo ≤ tailOutCount π U out P Qo := by
  unfold tailOutCount
  exact Finset.card_le_card fun z hz ↦ Finset.mem_filter.2 ⟨Finset.mem_univ z,
    h z (Finset.mem_filter.1 hz).2⟩

end outUpd

section unionUpd

variable {X Z : Type} [DecidableEq X] [DecidableEq Z]

omit [DecidableEq X] [DecidableEq Z] in
theorem union_h_apply' (W : Hw X Z) (D : DbReg X Z) (z : Z) :
    (union W D).h z = (W.1 z).or (D.1 z) :=
  rfl

omit [DecidableEq X] [DecidableEq Z] in
theorem union_k_apply' (W : Hw X Z) (D : DbReg X Z) (x : X) :
    (union W D).k x = (W.2.1 x).or (D.2.1 x) :=
  rfl

omit [DecidableEq X] [DecidableEq Z] in
theorem union_k'_apply' (W : Hw X Z) (D : DbReg X Z) (x : X) :
    (union W D).k' x = (W.2.2 x).or (D.2.2 x) :=
  rfl

omit [DecidableEq X] [DecidableEq Z] in
theorem union_k_of_h (W : Hw X Z) (D : DbReg X Z) (h : Database Z X) :
    (union W (h, D.2.1, D.2.2)).k = (union W D).k :=
  rfl

omit [DecidableEq X] [DecidableEq Z] in
theorem union_k'_of_h (W : Hw X Z) (D : DbReg X Z) (h : Database Z X) :
    (union W (h, D.2.1, D.2.2)).k' = (union W D).k' :=
  rfl

omit [DecidableEq X] [DecidableEq Z] in
theorem union_h_of_k (W : Hw X Z) (D : DbReg X Z) (k : Database X Z) (z : Z) :
    (union W (D.1, k, D.2.2)).h z = (union W D).h z :=
  rfl

omit [DecidableEq X] [DecidableEq Z] in
theorem union_k'_of_k (W : Hw X Z) (D : DbReg X Z) (k : Database X Z) :
    (union W (D.1, k, D.2.2)).k' = (union W D).k' :=
  rfl

omit [DecidableEq X] [DecidableEq Z] in
theorem union_h_of_k' (W : Hw X Z) (D : DbReg X Z) (k' : Database X Z) (z : Z) :
    (union W (D.1, D.2.1, k')).h z = (union W D).h z :=
  rfl

omit [DecidableEq X] [DecidableEq Z] in
theorem union_k_of_k' (W : Hw X Z) (D : DbReg X Z) (k' : Database X Z) :
    (union W (D.1, D.2.1, k')).k = (union W D).k :=
  rfl

omit [DecidableEq X] in
theorem union_updH_off (W : Hw X Z) (D : DbReg X Z) {z y : Z} (hy : y ≠ z) (v : Option X) :
    (union W (Function.update D.1 z v, D.2.1, D.2.2)).h y = (union W D).h y := by
  simp only [union_h_apply', Function.update_of_ne hy]

omit [DecidableEq Z] in
theorem union_updK_of_none (W : Hw X Z) (D : DbReg X Z) {x : X} (hW : W.2.1 x = none) (u : Z) :
    (union W (D.1, Function.update D.2.1 x (some u), D.2.2)).k =
      Function.update (union W D).k x (some u) := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp only [union_k_apply', Function.update_self, hW, Option.none_or]
  · simp only [union_k_apply', Function.update_of_ne hy]

omit [DecidableEq Z] in
theorem union_updK_of_some (W : Hw X Z) (D : DbReg X Z) {x : X} {b : Z} (hW : W.2.1 x = some b)
    (u : Z) : (union W (D.1, Function.update D.2.1 x (some u), D.2.2)).k = (union W D).k := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp only [union_k_apply', hW, Option.some_or]
  · simp only [union_k_apply', Function.update_of_ne hy]

omit [DecidableEq Z] in
theorem union_updK'_of_none (W : Hw X Z) (D : DbReg X Z) {x : X} (hW : W.2.2 x = none) (u : Z) :
    (union W (D.1, D.2.1, Function.update D.2.2 x (some u))).k' =
      Function.update (union W D).k' x (some u) := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp only [union_k'_apply', Function.update_self, hW, Option.none_or]
  · simp only [union_k'_apply', Function.update_of_ne hy]

omit [DecidableEq Z] in
theorem union_updK'_of_some (W : Hw X Z) (D : DbReg X Z) {x : X} {b : Z}
    (hW : W.2.2 x = some b) (u : Z) :
    (union W (D.1, D.2.1, Function.update D.2.2 x (some u))).k' = (union W D).k' := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp only [union_k'_apply', hW, Option.some_or]
  · simp only [union_k'_apply', Function.update_of_ne hy]

omit [DecidableEq Z] in
theorem union_updK_of_none_with (W : Hw X Z) (D : DbReg X Z) {x : X} (hW : W.2.1 x = none)
    (u : Z) : (union W (D.1, Function.update D.2.1 x (some u), D.2.2)).k =
      ({ union W D with k := Function.update (union W D).k x (some u) } : Dbs X Z).k :=
  union_updK_of_none W D hW u

omit [DecidableEq Z] in
theorem union_updK'_of_none_with (W : Hw X Z) (D : DbReg X Z) {x : X} (hW : W.2.2 x = none)
    (u : Z) : (union W (D.1, D.2.1, Function.update D.2.2 x (some u))).k' =
      ({ union W D with k' := Function.update (union W D).k' x (some u) } : Dbs X Z).k' :=
  union_updK'_of_none W D hW u

omit [DecidableEq X] [DecidableEq Z] in
theorem union_k_none {W : Hw X Z} {D : DbReg X Z} {x : X} (hW : W.2.1 x = none)
    (hD : D.2.1 x = none) : (union W D).k x = none := by
  simp only [union_k_apply', hW, hD, Option.none_or]

omit [DecidableEq X] [DecidableEq Z] in
theorem union_k'_none {W : Hw X Z} {D : DbReg X Z} {x : X} (hW : W.2.2 x = none)
    (hD : D.2.2 x = none) : (union W D).k' x = none := by
  simp only [union_k'_apply', hW, hD, Option.none_or]

end unionUpd

end Quantum.Sponge

/-! ## The potential as a count -/

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss

/-- The fresh-`k` count `(T + 1)((T + 1) T + 2T) G` of `card_badAttachK_le`. -/
def capKJ (T G : ℕ) : ℕ := (T + 1) * ((T + 1) * T + 2 * T) * G

/-- The fresh-`k'` count of `card_badCompleteOutK'_le` with `|D.h| ≤ T`. -/
def capKJ' (T G : ℕ) : ℕ := (T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T

section encN

open scoped Classical in
/-- **The cross-key potential of a union and a selection** as a count: on a good union, the
codeword counts of the unselected keys. -/
noncomputable def encPotU (L : HonestTable) (U : Dbs X Z) (g : Selections) : ℕ :=
  if Good L.perm U then
    ∑ k : Layer × KeyIndex, if g k.1 k.2 = none then msgCwCount L U k.1 k.2 else 0
  else 0

theorem encPotU_congr (L : HonestTable) {U U' : Dbs X Z} (hk : U'.k = U.k) (hk' : U'.k' = U.k')
    (hh : ∀ z, U'.h z = U.h z) (g : Selections) : encPotU L U' g = encPotU L U g := by
  unfold encPotU
  by_cases hG : Good L.perm U
  · rw [ite_eq_left ((good_congr hk hk').2 hG), ite_eq_left hG]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [msgCwCount_eq_tailOutCount, msgCwCount_eq_tailOutCount,
      tailOutCount_congr_of_iff fun z ↦ outAt_congr hk hk' (hh z) _ _]
  · rw [ite_eq_right fun h ↦ hG ((good_congr hk hk').1 h), ite_eq_right hG]

theorem encPotU_congr_k' (L : HonestTable) {U U' : Dbs X Z} (hk' : U'.k' = U.k')
    (hk : U'.k = U.k) (hh : ∀ z, U'.h z = U.h z) (g : Selections) :
    encPotU L U' g = encPotU L U g :=
  encPotU_congr L hk hk' hh g

theorem encPotU_le (L : HonestTable) (U : Dbs X Z) (g : Selections) :
    encPotU L U g ≤ U.h.size := by
  unfold encPotU
  split_ifs with hG
  · exact (Finset.sum_le_sum (g := fun k : Layer × KeyIndex ↦ msgCwCount L U k.1 k.2)
      fun k _ ↦ by split_ifs <;> simp).trans
        ((sum_msgCwCount_le hG).trans (msgSlotCount_le_size L U))
  · exact Nat.zero_le _

/-- **A `k` value outside `badAttachK` keeps the potential** of a good union. -/
theorem encPotU_updK_eq (L : HonestTable) {U : Dbs X Z} (hG : Good L.perm U) {x : X}
    (hx : U.k x = none) {u : Z} (hu : u ∉ badAttachK L.perm U x) (g : Selections) :
    encPotU L { U with k := Function.update U.k x (some u) } g = encPotU L U g := by
  unfold encPotU
  rw [ite_eq_left (updateK_tails hG hx hu).1, ite_eq_left hG]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [msgCwCount_eq_tailOutCount, msgCwCount_eq_tailOutCount,
    tailOutCount_congr_of_iff fun z ↦ outAt_update_k_iff hG hx hu _ _ z]

/-- **A `k'` value outside `badCompleteOutK'` keeps the potential** of a good union. -/
theorem encPotU_updK'_eq (L : HonestTable) {U : Dbs X Z} (hG : Good L.perm U) {x : X}
    (hx : U.k' x = none) {u : Z} (hu : u ∉ badCompleteOutK' L.perm U x) (g : Selections) :
    encPotU L { U with k' := Function.update U.k' x (some u) } g = encPotU L U g := by
  unfold encPotU
  rw [ite_eq_left (updateK'_tails hG hx hu).1, ite_eq_left hG]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [msgCwCount_eq_tailOutCount, msgCwCount_eq_tailOutCount,
    tailOutCount_congr_of_iff fun z ↦ outAt_update_k'_iff hG hx hu _ _ z]

theorem encPotU_of_not_good (L : HonestTable) {U : Dbs X Z} (hG : ¬ Good L.perm U)
    (g : Selections) : encPotU L U g = 0 := by
  unfold encPotU
  rw [ite_eq_right hG]

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)

/-- **The cross-key potential as a count** on the hardwired register. -/
noncomputable def encPotN (L : HonestTable) (s : HwReg X Z M) : ℕ :=
  encPotU L (union s.2.1 s.1) (get s.2.2)

omit [Fintype M] [DecidableEq M] in
theorem encPot_eq_encPotN (L : HonestTable) (s : HwReg X Z M) :
    encPot get L s = (encPotN get L s : ℝ) := by
  unfold encPot encPotN encPotU
  split_ifs
  · rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Nat.cast_ite, Nat.cast_zero]
  · rw [Nat.cast_zero]

omit [Fintype M] [DecidableEq M] in
theorem sqrt_encPot_eq (L : HonestTable) :
    (fun s : HwReg X Z M ↦ √(encPot get L s)) = fun s ↦ √(encPotN get L s : ℝ) :=
  funext fun s ↦ by rw [encPot_eq_encPotN]

omit [Fintype M] [DecidableEq M] in
/-- **The potential is at most the hardwired and database grades.** -/
theorem encPotN_le (L : HonestTable) (s : HwReg X Z M) :
    encPotN get L s ≤ dbGrade s.2.1 + dbGrade s.1 :=
  (encPotU_le L _ _).trans (size_unionH_le s.2.1 s.1)

omit [Fintype M] [DecidableEq M] in
open scoped Classical in
/-- **The potential changes by at most one with the union's `h` cell `z`**, the `k`, `k'` cells
and the selections kept. -/
theorem encPot_le_add_one_of_off (L : HonestTable) (z : Z) {s s' : HwReg X Z M}
    (hk : (union s'.2.1 s'.1).k = (union s.2.1 s.1).k)
    (hk' : (union s'.2.1 s'.1).k' = (union s.2.1 s.1).k')
    (hh : ∀ b, b ≠ z → (union s'.2.1 s'.1).h b = (union s.2.1 s.1).h b)
    (hm : get s'.2.2 = get s.2.2) : encPot get L s' ≤ encPot get L s + 1 := by
  have hoff : ∀ k, encOff L z k s' = encOff L z k s := fun k ↦ by
    unfold encOff
    rw [tailOutOff_congr hk hk' hh]
    exact if_congr (good_congr hk hk') rfl rfl
  set k₀ : Layer × KeyIndex := (bottomLayer, ⟨0, by unfold lifetime; positivity⟩)
  have hA : encA get L z k₀ s' = encA get L z k₀ s := by
    unfold encA
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hm, hoff k]
  have hB : encB get L z k₀ s' = encB get L z k₀ s := by
    unfold encB
    rw [hm, hoff k₀]
  have e' := encPot_eq get L z k₀ ((), s')
  have e := encPot_eq get L z k₀ ((), s)
  have h1 := ind_le_one (liftSet (encCSet get L z)) ((), s')
  have h0 := ind_nonneg (liftSet (encCSet get L z)) ((), s)
  simp only at e e'
  linarith

omit [Fintype M] [DecidableEq M] in
/-- **The potential is one-cell Lipschitz in the database's `h` cells.** -/
theorem encPot_update_h_le (L : HonestTable) (D : DbReg X Z) (b : Hw X Z × M) (z : Z)
    (v : Option X) :
    encPot get L ((Function.update D.1 z v, D.2.1, D.2.2), b) ≤ encPot get L (D, b) + 1 :=
  encPot_le_add_one_of_off get L z (union_k_of_h b.1 D _) (union_k'_of_h b.1 D _)
    (fun _ hy ↦ union_updH_off b.1 D hy v) rfl

omit [Fintype M] [DecidableEq M] in
/-- **The values of a fresh `k` cell changing the potential lie in `badAttachK`** of a good
union, the cell not hardwired. -/
theorem encPotN_updK_ne (L : HonestTable) {s : HwReg X Z M} {x : X} (hx : s.1.2.1 x = none)
    {u : Z} (hne : encPotN get L ((s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2), s.2) ≠
      encPotN get L s) :
    s.2.1.2.1 x = none ∧ Good L.perm (union s.2.1 s.1) ∧
      u ∈ badAttachK L.perm (union s.2.1 s.1) x := by
  unfold encPotN at hne
  by_cases hW : s.2.1.2.1 x = none
  · have hUx : (union s.2.1 s.1).k x = none := union_k_none hW hx
    have hV : encPotU L (union s.2.1 (s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2))
        (get s.2.2) = encPotU L { union s.2.1 s.1 with
          k := Function.update (union s.2.1 s.1).k x (some u) } (get s.2.2) :=
      encPotU_congr (U' := union s.2.1 (s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2))
        (U := { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k x (some u) }) L
        (union_updK_of_none_with s.2.1 s.1 hW u) (union_k'_of_k s.2.1 s.1 _)
        (union_h_of_k s.2.1 s.1 _) _
    by_cases hG : Good L.perm (union s.2.1 s.1)
    · refine ⟨hW, hG, ?_⟩
      by_contra hu
      exact hne (hV.trans (encPotU_updK_eq L hG hUx hu _))
    · refine absurd ?_ hne
      rw [hV, encPotU_of_not_good L (fun h ↦ hG (Good.mono (extends_update_k hUx) h)),
        encPotU_of_not_good L hG]
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hW
    exact absurd (encPotU_congr
      (U' := union s.2.1 (s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2))
      (U := union s.2.1 s.1) L (union_updK_of_some s.2.1 s.1 hb u)
      (union_k'_of_k s.2.1 s.1 _) (union_h_of_k s.2.1 s.1 _) (get s.2.2)) hne

omit [Fintype M] [DecidableEq M] in
/-- **The values of a fresh `k'` cell changing the potential lie in `badCompleteOutK'`** of a
good union, the cell not hardwired. -/
theorem encPotN_updK'_ne (L : HonestTable) {s : HwReg X Z M} {x : X} (hx : s.1.2.2 x = none)
    {u : Z} (hne : encPotN get L ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)), s.2) ≠
      encPotN get L s) :
    s.2.1.2.2 x = none ∧ Good L.perm (union s.2.1 s.1) ∧
      u ∈ badCompleteOutK' L.perm (union s.2.1 s.1) x := by
  unfold encPotN at hne
  by_cases hW : s.2.1.2.2 x = none
  · have hUx : (union s.2.1 s.1).k' x = none := union_k'_none hW hx
    have hV : encPotU L (union s.2.1 (s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)))
        (get s.2.2) = encPotU L { union s.2.1 s.1 with
          k' := Function.update (union s.2.1 s.1).k' x (some u) } (get s.2.2) :=
      encPotU_congr (U' := union s.2.1 (s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)))
        (U := { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' x (some u) }) L
        (union_k_of_k' s.2.1 s.1 _) (union_updK'_of_none_with s.2.1 s.1 hW u)
        (union_h_of_k' s.2.1 s.1 _) _
    by_cases hG : Good L.perm (union s.2.1 s.1)
    · refine ⟨hW, hG, ?_⟩
      by_contra hu
      exact hne (hV.trans (encPotU_updK'_eq L hG hUx hu _))
    · refine absurd ?_ hne
      rw [hV, encPotU_of_not_good L (fun h ↦ hG (Good.mono (extends_update_k' hUx) h)),
        encPotU_of_not_good L hG]
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hW
    exact absurd (encPotU_congr
      (U' := union s.2.1 (s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)))
      (U := union s.2.1 s.1) L (union_k_of_k' s.2.1 s.1 _)
      (union_updK'_of_some s.2.1 s.1 hb u) (union_h_of_k' s.2.1 s.1 _) (get s.2.2)) hne

end encN

end Quantum.Xmss.Assembly


/-! ## Read and program ports, generically -/

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge

section readGen

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

/-- The sponge port whose cell a read port reads. -/
def readPort : HwRead X Z M → SpongePort
  | .readH .. => .h
  | .readK .. => .k
  | .readK' .. => .k'

omit [DecidableEq M] in
/-- **The empty-cell term of a read from two-sided fresh bounds** (as `keepE_le_of_freshBound`,
without upward closure). -/
theorem keepE_le_of_portInst (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] {N : ℕ}
    {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤) (c : HwRead X Z M)
    (hε : ∀ W m, PortInst (slice S W m) (readPort c) (N + 1) ε)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hg : QuerySupportedOn (fun q : Unit × HwReg X Z M ↦ dbGrade q.2.1) (Set.Iic N) σ) :
    keepE S c σ ≤ ε.toReal * σ.trace.re := by
  cases c with
  | readH z upd =>
    unfold keepE
    refine sum_mul_re_le_trace hσ _ fun q hq0 ↦ ?_
    split_ifs with hq
    · obtain ⟨h1, h2, h3⟩ := size_lt_of_dbGrade_le (hg q q hq0).1
      have hf := hε q.2.2.1 q.2.2.2 q.2.1.toDbs h1 h2 h3 z hq.2
      refine le_trans ?_ (natCast_div_le_toReal hεtop hf)
      refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card fun b hb ↦ ?_))
        (Nat.cast_nonneg _)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ b, (Finset.mem_filter.1 hb).2⟩
    · exact ENNReal.toReal_nonneg
  | readK x upd =>
    unfold keepE
    refine sum_mul_re_le_trace hσ _ fun q hq0 ↦ ?_
    split_ifs with hq
    · obtain ⟨h1, h2, h3⟩ := size_lt_of_dbGrade_le (hg q q hq0).1
      have hf := hε q.2.2.1 q.2.2.2 q.2.1.toDbs h1 h2 h3 x hq.2
      refine le_trans ?_ (natCast_div_le_toReal hεtop hf)
      refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card fun b hb ↦ ?_))
        (Nat.cast_nonneg _)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ b, (Finset.mem_filter.1 hb).2⟩
    · exact ENNReal.toReal_nonneg
  | readK' x upd =>
    unfold keepE
    refine sum_mul_re_le_trace hσ _ fun q hq0 ↦ ?_
    split_ifs with hq
    · obtain ⟨h1, h2, h3⟩ := size_lt_of_dbGrade_le (hg q q hq0).1
      have hf := hε q.2.2.1 q.2.2.2 q.2.1.toDbs h1 h2 h3 x hq.2
      refine le_trans ?_ (natCast_div_le_toReal hεtop hf)
      refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card fun b hb ↦ ?_))
        (Nat.cast_nonneg _)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ b, (Finset.mem_filter.1 hb).2⟩
    · exact ENNReal.toReal_nonneg

/-- The flip-recorded mass `p` of a read port. -/
noncomputable def readP (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] :
    HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ
  | .readH z upd, σ => costP (splitH' z) (actH z) (tauH z upd) (liftSet S) σ
  | .readK x upd, σ => costP (splitK x) (actK x) (tauK x upd) (liftSet S) σ
  | .readK' x upd, σ => costP (splitK' x) (actK' x) (tauK x upd) (liftSet S) σ

omit [DecidableEq M] in
theorem readCost_eq (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    readCost S c σ = ENNReal.ofReal (readA S c σ) +
      2 * (ENNReal.ofReal (readE S c σ) * ENNReal.ofReal (readP S c σ)) ^ (2⁻¹ : ℝ) := by
  cases c <;> rfl

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M] in
theorem pd_le_one {n Y R : Type} {e : n ≃ Option Y × R} {act : R → Prop} [DecidablePred act]
    {D : Y → R → Prop} [∀ y r, Decidable (D y r)] (t : n) : pd e act D t ≤ 1 := by
  rcases pd_mem (e := e) (act := act) D t with h0 | h0
  · rw [h0]
    norm_num
  · rw [h0]

omit [DecidableEq M] in
theorem readP_le_trace (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (c : HwRead X Z M)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    readP S c σ ≤ σ.trace.re := by
  cases c with
  | readH z upd =>
    exact (sum_mul_re_le_trace hσ _ fun q _ ↦ pd_le_one q).trans_eq (one_mul _)
  | readK x upd =>
    exact (sum_mul_re_le_trace hσ _ fun q _ ↦ pd_le_one q).trans_eq (one_mul _)
  | readK' x upd =>
    exact (sum_mul_re_le_trace hσ _ fun q _ ↦ pd_le_one q).trans_eq (one_mul _)

/-- `ofReal A + 2 √(E p) ≤ ofReal ((e + r + 2 √e) t)` for `A ≤ (e + r) t`, `E ≤ e t`, `p ≤ t`. -/
theorem ofReal_add_two_sqrt_le_of {A E p t e r : ℝ} (hA : A ≤ (e + r) * t) (hE : E ≤ e * t)
    (hE0 : 0 ≤ E) (hp0 : 0 ≤ p) (hp : p ≤ t) (he0 : 0 ≤ e) (hr : 0 ≤ r) :
    ENNReal.ofReal A + 2 * (ENNReal.ofReal E * ENNReal.ofReal p) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal ((e + r + 2 * √e) * t) := by
  have ht : 0 ≤ t := hp0.trans hp
  have hsq : √(E * p) ≤ √e * t := by
    calc √(E * p) ≤ √(e * t * t) :=
          Real.sqrt_le_sqrt (mul_le_mul hE hp hp0 (mul_nonneg he0 ht))
      _ = √e * t := by rw [mul_assoc, Real.sqrt_mul he0, Real.sqrt_mul_self ht]
  rw [← ENNReal.ofReal_mul hE0, ENNReal.ofReal_rpow_inv_two,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
    show (e + r + 2 * √e) * t = (e + r) * t + 2 * √e * t by ring,
    ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (ENNReal.ofReal_le_ofReal hA)
    (ENNReal.ofReal_le_ofReal (by nlinarith [Real.sqrt_nonneg (E * p)]))

omit [DecidableEq M] in
/-- **The refined cost of a read that keeps the memory**: with the empty-cell term at most
`e tr σ`, at most `(e + 2/|X| + 2/|Z| + 2 √e) tr σ`. -/
theorem readCost_le_of_keep [Nonempty X] [Nonempty Z] (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (c : HwRead X Z M) (hk : KeepUpd c)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) {e : ℝ}
    (he0 : 0 ≤ e) (hE : keepE S c σ ≤ e * σ.trace.re) :
    readCost S c σ ≤ ENNReal.ofReal
      ((e + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √e) * σ.trace.re) := by
  obtain ⟨hE', hA, -⟩ := read_keep_le S c hk hσ
  have hR := recW_le c hσ
  have hE0 : 0 ≤ readE S c σ := by
    cases c with
    | readH z upd => exact costE_nonneg _ hσ
    | readK x upd => exact costE_nonneg _ hσ
    | readK' x upd => exact costE_nonneg _ hσ
  have hp0 : 0 ≤ readP S c σ := by
    cases c with
    | readH z upd => exact costP_nonneg _ hσ
    | readK x upd => exact costP_nonneg _ hσ
    | readK' x upd => exact costP_nonneg _ hσ
  rw [readCost_eq]
  exact ofReal_add_two_sqrt_le_of (by rw [add_mul]; linarith) (hE'.trans hE) hE0 hp0
    (readP_le_trace S c hσ) he0 (by positivity)

end readGen

section progGen

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

/-- **The jump of a diagonal potential at a program port** beyond one per unit of trace. -/
noncomputable def progJump (φ : HwReg X Z M → ℝ) (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ q, max (φ (progMap c q.2) - φ q.2 - 1) 0 * (σ q q).re)

/-- **A program port raises a diagonal potential by its trace and its jump.** -/
theorem tsum_potential_prog_le {φ : HwReg X Z M → ℝ} (hφ0 : ∀ s, 0 ≤ φ s) (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    ∑' r, QuantumRuntime.potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (hwProgKraus c r) σ) ≤
      QuantumRuntime.potential (diagPot fun s ↦ √(φ s)) σ +
        (ENNReal.ofReal σ.trace.re + progJump φ c σ) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have hj : 0 ≤ ∑ q, max (φ (progMap c q.2) - φ q.2 - 1) 0 * (σ q q).re :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (le_max_right _ _) (hre q)
  have hp : 0 ≤ ∑ q : Unit × HwReg X Z M, φ q.2 * (σ q q).re :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 q.2) (hre q)
  have hreal : ∑ q : Unit × HwReg X Z M, φ (progMap c q.2) * (σ q q).re ≤
      ∑ q : Unit × HwReg X Z M, φ q.2 * (σ q q).re +
        (σ.trace.re + ∑ q, max (φ (progMap c q.2) - φ q.2 - 1) 0 * (σ q q).re) := by
    rw [Matrix.trace, Complex.re_sum]
    simp only [Matrix.diag_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    have h := le_max_left (φ (progMap c q.2) - φ q.2 - 1) 0
    nlinarith [hre q]
  rw [tsum_potential_prog_eq hφ0 c hσ, potential_diagPot_sqrt hφ0, progJump]
  calc ENNReal.ofReal (∑ q : Unit × HwReg X Z M, φ (progMap c q.2) * (σ q q).re)
      ≤ ENNReal.ofReal (∑ q : Unit × HwReg X Z M, φ q.2 * (σ q q).re +
          (σ.trace.re + ∑ q, max (φ (progMap c q.2) - φ q.2 - 1) 0 * (σ q q).re)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = _ := by rw [ENNReal.ofReal_add hp (add_nonneg htr hj), ENNReal.ofReal_add htr hj]

omit [DecidableEq M] in
/-- **The jump at the states of a set**: if off `J` the program raises the potential by at most
one, and the potential after the program is at most `H` on the support, the jump is at most `H`
times the weight of `J`. -/
theorem progJump_le {φ : HwReg X Z M → ℝ} (hφ0 : ∀ s, 0 ≤ φ s) (c : HwProg X Z)
    (J : HwReg X Z M → Prop) [DecidablePred J] (hJ : ∀ s, ¬ J s → φ (progMap c s) ≤ φ s + 1)
    {H : ℝ} {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hH : ∀ q, σ q q ≠ 0 → φ (progMap c q.2) ≤ H) :
    progJump φ c σ ≤ ENNReal.ofReal (H * ∑ q, (if J q.2 then (1 : ℝ) else 0) * (σ q q).re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases h0 : σ q q = 0
  · rw [h0, Complex.zero_re, mul_zero, mul_zero, mul_zero]
  · by_cases hj : J q.2
    · rw [ite_eq_left hj, ← mul_assoc, mul_one]
      refine mul_le_mul_of_nonneg_right (max_le ?_ ((hφ0 _).trans (hH q h0))) (hre q)
      linarith [hφ0 q.2, hH q h0]
    · rw [ite_eq_right hj, max_eq_right (by linarith [hJ q.2 hj]), zero_mul, mul_zero]

end progGen

end Quantum.Xmss.Assembly

/-! ## Generic facts on level sets and programmed unions -/

namespace Quantum.Sponge

section levGen

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] [Fintype M] [DecidableEq M]

omit [DecidableEq X] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z] [Fintype M]
  [DecidableEq M] in
/-- A state that changes level-set membership changes the count, inside the hardwired grade. -/
theorem levFlip_ne {F : HwReg X Z M → ℕ} {Nw m : ℕ} {s s' : HwReg X Z M} (hw : s'.2.1 = s.2.1)
    (hu : ¬ (s' ∈ levSet F Nw m ↔ s ∈ levSet F Nw m)) : dbGrade s.2.1 ≤ Nw ∧ F s' ≠ F s := by
  by_cases hW : dbGrade s.2.1 ≤ Nw
  · refine ⟨hW, fun he ↦ hu ?_⟩
    show (dbGrade s'.2.1 ≤ Nw ∧ m < F s') ↔ (dbGrade s.2.1 ≤ Nw ∧ m < F s)
    rw [hw, he]
  · exact absurd ⟨fun h ↦ absurd (hw ▸ h.1) hW, fun h ↦ absurd h.1 hW⟩ hu

omit [AddCommGroup X] [Fintype M] [DecidableEq M] in
/-- **The values of a fresh `k` cell flipping a level set**, if only `badAttachK` values change
the count: at most `capKJ`. -/
theorem card_levFlip_k_le (F : HwReg X Z M → ℕ) (π : Equiv.Perm (X × Z)) {G : ℕ}
    (hπ : PermGood π G) (Nw m n : ℕ) (s : HwReg X Z M) {x : X} (hD : dbGrade s.1 ≤ n)
    (hF : ∀ u, F ((s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2), s.2) ≠ F s →
      s.2.1.2.1 x = none ∧ Good π (union s.2.1 s.1) ∧ u ∈ badAttachK π (union s.2.1 s.1) x) :
    (Finset.univ.filter fun u : Z ↦ ¬ ((((s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2),
      s.2) ∈ levSet F Nw m) ↔ s ∈ levSet F Nw m)).card ≤
        Xmss.Assembly.capKJ (Nw + n) G := by
  by_cases hc : dbGrade s.2.1 ≤ Nw ∧ s.2.1.2.1 x = none ∧ Good π (union s.2.1 s.1)
  · refine (Finset.card_le_card fun u hu ↦ ?_).trans (card_badAttachK_le (x := x) hc.2.2 hπ
      ((size_unionK_le s.2.1 s.1).trans (Nat.add_le_add hc.1 hD))
      ((size_unionK'_le s.2.1 s.1).trans (Nat.add_le_add hc.1 hD)))
    exact (hF u (levFlip_ne (F := F) (Nw := Nw) (m := m) (s := s)
      (s' := ((s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2), s.2)) rfl
      (Finset.mem_filter.1 hu).2).2).2.2
  · refine (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun u _ hu ↦ ?_)).trans_le
      (Nat.zero_le _)
    obtain ⟨hW, hne⟩ := levFlip_ne (F := F) (Nw := Nw) (m := m) (s := s)
      (s' := ((s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2), s.2)) rfl hu
    obtain ⟨h1, h2, -⟩ := hF u hne
    exact hc ⟨hW, h1, h2⟩

omit [AddCommGroup X] [Fintype M] [DecidableEq M] in
/-- **The values of a fresh `k'` cell flipping a level set**: at most `capKJ'`. -/
theorem card_levFlip_k'_le (F : HwReg X Z M → ℕ) (π : Equiv.Perm (X × Z)) {G : ℕ}
    (hπ : PermGood π G) (Nw m n : ℕ) (s : HwReg X Z M) {x : X} (hD : dbGrade s.1 ≤ n)
    (hF : ∀ u, F ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)), s.2) ≠ F s →
      s.2.1.2.2 x = none ∧ Good π (union s.2.1 s.1) ∧ u ∈ badCompleteOutK' π (union s.2.1 s.1) x) :
    (Finset.univ.filter fun u : Z ↦ ¬ ((((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)),
      s.2) ∈ levSet F Nw m) ↔ s ∈ levSet F Nw m)).card ≤
        Xmss.Assembly.capKJ' (Nw + n) G := by
  by_cases hc : dbGrade s.2.1 ≤ Nw ∧ s.2.1.2.2 x = none ∧ Good π (union s.2.1 s.1)
  · have hT : dbGrade s.2.1 + dbGrade s.1 ≤ Nw + n := Nat.add_le_add hc.1 hD
    refine (Finset.card_le_card fun u hu ↦ ?_).trans ((card_badCompleteOutK'_le hc.2.2 hπ x
      ((size_unionK_le s.2.1 s.1).trans hT) ((size_unionK'_le s.2.1 s.1).trans hT)).trans
        (Nat.add_le_add_left ((size_unionH_le s.2.1 s.1).trans hT) _))
    exact (hF u (levFlip_ne (F := F) (Nw := Nw) (m := m) (s := s)
      (s' := ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)), s.2)) rfl
      (Finset.mem_filter.1 hu).2).2).2.2
  · refine (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun u _ hu ↦ ?_)).trans_le
      (Nat.zero_le _)
    obtain ⟨hW, hne⟩ := levFlip_ne (F := F) (Nw := Nw) (m := m) (s := s)
      (s' := ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)), s.2)) rfl hu
    obtain ⟨h1, h2, -⟩ := hF u hne
    exact hc ⟨hW, h1, h2⟩

omit [AddCommGroup X] [AddCommGroup Z] [Fintype M] [DecidableEq M] in
/-- **A two-sided fresh bound at `k` from counts on the states** of every slice. -/
theorem portInst_k_of_card [Nonempty Z] (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (W : Hw X Z) (mm : M) {n J : ℕ}
    (h : ∀ s : HwReg X Z M, dbGrade s.1 ≤ n → ∀ x, s.1.2.1 x = none →
      (Finset.univ.filter fun u : Z ↦ ¬ ((((s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2),
        s.2) ∈ S) ↔ s ∈ S)).card ≤ J) :
    PortInst (slice S W mm) .k (n + 1) (ENNReal.ofReal ((J : ℝ) / Fintype.card Z)) := by
  intro D _ hk _ x hx
  have hD : dbGrade ((D.h, D.k, D.k') : DbReg X Z) ≤ n := by
    simp only [dbGrade, max_le_iff]
    omega
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (h ((D.h, D.k, D.k'), W, mm) hD x hx)) _

omit [AddCommGroup X] [AddCommGroup Z] [Fintype M] [DecidableEq M] in
/-- **A two-sided fresh bound at `k'` from counts on the states** of every slice. -/
theorem portInst_k'_of_card [Nonempty Z] (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (W : Hw X Z) (mm : M) {n J : ℕ}
    (h : ∀ s : HwReg X Z M, dbGrade s.1 ≤ n → ∀ x, s.1.2.2 x = none →
      (Finset.univ.filter fun u : Z ↦ ¬ ((((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)),
        s.2) ∈ S) ↔ s ∈ S)).card ≤ J) :
    PortInst (slice S W mm) .k' (n + 1) (ENNReal.ofReal ((J : ℝ) / Fintype.card Z)) := by
  intro D _ _ hk' x hx
  have hD : dbGrade ((D.h, D.k, D.k') : DbReg X Z) ≤ n := by
    simp only [dbGrade, max_le_iff]
    omega
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (h ((D.h, D.k, D.k'), W, mm) hD x hx)) _

omit [Fintype X] [Fintype Z] [AddCommGroup X] [AddCommGroup Z] [Fintype M] [DecidableEq M] in
theorem progMap_mem (c : HwProg X Z) (s : HwReg X Z M) : (progMap c s).2.2 = s.2.2 := by
  cases c <;> rfl

omit [Fintype X] [Fintype Z] [AddCommGroup X] [AddCommGroup Z] [Fintype M] [DecidableEq M] in
theorem union_progMapH_k (z : Z) (v : X) (s : HwReg X Z M) :
    (union (progMap (.programH z v) s).2.1 (progMap (.programH z v) s).1).k =
      (union s.2.1 s.1).k :=
  rfl

omit [Fintype X] [Fintype Z] [AddCommGroup X] [AddCommGroup Z] [Fintype M] [DecidableEq M] in
theorem union_progMapH_k' (z : Z) (v : X) (s : HwReg X Z M) :
    (union (progMap (.programH z v) s).2.1 (progMap (.programH z v) s).1).k' =
      (union s.2.1 s.1).k' :=
  rfl

omit [Fintype X] [Fintype Z] [AddCommGroup X] [AddCommGroup Z] [Fintype M] [DecidableEq M] in
theorem union_progMapH_h (z : Z) (v : X) (s : HwReg X Z M) {y : Z} (hy : y ≠ z) :
    (union (progMap (.programH z v) s).2.1 (progMap (.programH z v) s).1).h y =
      (union s.2.1 s.1).h y := by
  simp only [progMap, union_h_apply', Function.update_of_ne hy]

omit [Fintype X] [Fintype Z] [AddCommGroup X] [AddCommGroup Z] [Fintype M] [DecidableEq M] in
theorem union_progMapK (y : X) (a : Z) (s : HwReg X Z M) :
    union (progMap (.programK y a) s).2.1 (progMap (.programK y a) s).1 =
      { ({ union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k y none } : Dbs X Z) with
        k := Function.update (Function.update (union s.2.1 s.1).k y none) y (some a) } :=
  union_programK s.2.1 s.1 y a

omit [Fintype X] [Fintype Z] [AddCommGroup X] [AddCommGroup Z] [Fintype M] [DecidableEq M] in
theorem union_progMapK' (y : X) (a : Z) (s : HwReg X Z M) :
    union (progMap (.programK' y a) s).2.1 (progMap (.programK' y a) s).1 =
      { ({ union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' y none } : Dbs X Z) with
        k' := Function.update (Function.update (union s.2.1 s.1).k' y none) y (some a) } :=
  union_programK' s.2.1 s.1 y a

omit [Fintype X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z] in
theorem eraseK_k_self (U : Dbs X Z) (y : X) :
    ({ U with k := Function.update U.k y none } : Dbs X Z).k y = none :=
  Function.update_self _ _ _

omit [Fintype X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z] in
theorem eraseK'_k'_self (U : Dbs X Z) (y : X) :
    ({ U with k' := Function.update U.k' y none } : Dbs X Z).k' y = none :=
  Function.update_self _ _ _

omit [Fintype X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z] in
theorem reprogK_k {U : Dbs X Z} {y : X} {a : Z} (h : U.k y = some a) :
    ({ ({ U with k := Function.update U.k y none } : Dbs X Z) with
      k := Function.update (Function.update U.k y none) y (some a) } : Dbs X Z).k = U.k := by
  show Function.update (Function.update U.k y none) y (some a) = U.k
  rw [Function.update_idem, Function.update_eq_self_iff.mpr h.symm]

omit [Fintype X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z] in
theorem reprogK'_k' {U : Dbs X Z} {y : X} {a : Z} (h : U.k' y = some a) :
    ({ ({ U with k' := Function.update U.k' y none } : Dbs X Z) with
      k' := Function.update (Function.update U.k' y none) y (some a) } : Dbs X Z).k' = U.k' := by
  show Function.update (Function.update U.k' y none) y (some a) = U.k'
  rw [Function.update_idem, Function.update_eq_self_iff.mpr h.symm]

omit [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z] in
theorem union_k_some {W D : DbReg X Z} {y : X} {a : Z} (hW : W.2.1 y = some a) :
    (union W D).k y = some a := by
  simp only [union_k_apply', hW, Option.some_or]

omit [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z] in
theorem union_k'_some {W D : DbReg X Z} {y : X} {a : Z} (hW : W.2.2 y = some a) :
    (union W D).k' y = some a := by
  simp only [union_k'_apply', hW, Option.some_or]

end levGen

end Quantum.Sponge

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss

/-! ## The potential at the fresh `k`, `k'` cells and the programs -/

section levels

theorem encPotU_mono (L : HonestTable) {U U₀ : Dbs X Z} (hE : Extends U U₀)
    (hh : ∀ z, U₀.h z = U.h z) (hG : Good L.perm U) (g : Selections) :
    encPotU L U₀ g ≤ encPotU L U g := by
  unfold encPotU
  rw [ite_eq_left (Good.mono hE hG), ite_eq_left hG]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  split_ifs
  · rw [msgCwCount_eq_tailOutCount, msgCwCount_eq_tailOutCount]
    exact tailOutCount_le_of_imp fun z ⟨t, xi, w, hP, hi, hw, hq⟩ ↦
      ⟨t, xi, w, hP, hi.mono hE, (hh z) ▸ hw, hq⟩
  · exact le_rfl

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)

/-- The fresh-cell rate of the level sets: `(capK + capK') / |Z|` for `T = Nw + n`. -/
noncomputable def epsLev (T G : ℕ) : ℝ := ((capKJ T G + capKJ' T G : ℕ) : ℝ) / Fintype.card Z

theorem epsLev_nonneg (T G : ℕ) : 0 ≤ epsLev T G := by
  unfold epsLev
  positivity

omit [Fintype M] [DecidableEq M] in
/-- **Two-sided fresh bounds of the level sets of the potential at `k`.** -/
theorem portInst_levSet_k (L : HonestTable) {G : ℕ} (hπ : PermGood L.perm G) (Nw n m : ℕ)
    (W : Hw X Z) (mm : M) :
    PortInst (slice (levSet (encPotN get L) Nw m) W mm) .k (n + 1)
      (ENNReal.ofReal (epsLev (Nw + n) G)) := by
  have h := portInst_k_of_card (levSet (encPotN get L) Nw m) W mm (n := n)
    (J := capKJ (Nw + n) G + capKJ' (Nw + n) G) fun s hD x hx ↦
      (card_levFlip_k_le (encPotN get L) L.perm hπ Nw m n s hD fun u hne ↦
        encPotN_updK_ne get L hx hne).trans (Nat.le_add_right _ _)
  exact h

omit [Fintype M] [DecidableEq M] in
/-- **Two-sided fresh bounds of the level sets of the potential at `k'`.** -/
theorem portInst_levSet_k' (L : HonestTable) {G : ℕ} (hπ : PermGood L.perm G) (Nw n m : ℕ)
    (W : Hw X Z) (mm : M) :
    PortInst (slice (levSet (encPotN get L) Nw m) W mm) .k' (n + 1)
      (ENNReal.ofReal (epsLev (Nw + n) G)) := by
  have h := portInst_k'_of_card (levSet (encPotN get L) Nw m) W mm (n := n)
    (J := capKJ (Nw + n) G + capKJ' (Nw + n) G) fun s hD x hx ↦
      (card_levFlip_k'_le (encPotN get L) L.perm hπ Nw m n s hD fun u hne ↦
        encPotN_updK'_ne get L hx hne).trans (Nat.le_add_left _ _)
  exact h

/-- **A bad union made good by programming the cell**: the cell not hardwired, the union bad and
the union with the cell emptied good (the database records at the cell a value that breaks
goodness). -/
def RecJ (L : HonestTable) : HwProg X Z → HwReg X Z M → Prop
  | .programH _ _, _ => False
  | .programK y _, s => s.2.1.2.1 y = none ∧ ¬ Good L.perm (union s.2.1 s.1) ∧
      Good L.perm { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k y none }
  | .programK' y _, s => s.2.1.2.2 y = none ∧ ¬ Good L.perm (union s.2.1 s.1) ∧
      Good L.perm { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' y none }

/-- **The program states whose potential may jump**: none for `h`; for `k` (`k'`) a hardwired
cell with another value, a fresh flip (KeyLazy's `FlipK`, `FlipK'`) or `RecJ`. -/
def KJump (L : HonestTable) : HwProg X Z → HwReg X Z M → Prop
  | .programH _ _, _ => False
  | .programK y a, s => (s.2.1.2.1 y ≠ none ∧ s.2.1.2.1 y ≠ some a) ∨
      FlipK L.perm s.2.1 s.1 y a ∨ RecJ L (.programK y a) s
  | .programK' y a, s => (s.2.1.2.2 y ≠ none ∧ s.2.1.2.2 y ≠ some a) ∨
      FlipK' L.perm s.2.1 s.1 y a ∨ RecJ L (.programK' y a) s

/-- The jump states, decided classically. -/
noncomputable instance kJumpDec (L : HonestTable) (c : HwProg X Z) :
    DecidablePred (KJump (M := M) L c) :=
  Classical.decPred _

/-- The `RecJ` states, decided classically. -/
noncomputable instance recJDec (L : HonestTable) (c : HwProg X Z) :
    DecidablePred (RecJ (M := M) L c) :=
  Classical.decPred _

omit [Fintype M] [DecidableEq M] in
/-- **Off the jump states a program raises the potential by at most one.** -/
theorem encPot_progMap_le (L : HonestTable) (c : HwProg X Z) (s : HwReg X Z M)
    (h : ¬ KJump L c s) : encPot get L (progMap c s) ≤ encPot get L s + 1 := by
  cases c with
  | programH z v =>
    exact encPot_le_add_one_of_off get L z (s := s) (s' := progMap (.programH z v) s)
      (union_progMapH_k z v s) (union_progMapH_k' z v s) (fun _ hy ↦ union_progMapH_h z v s hy)
      (congrArg get (progMap_mem _ s))
  | programK y a =>
    have hle : encPotN get L (progMap (.programK y a) s) ≤ encPotN get L s := by
      have hW : s.2.1.2.1 y ≠ none → s.2.1.2.1 y = some a := fun h1 ↦ by
        by_contra h2
        exact h (.inl ⟨h1, h2⟩)
      have hF : ¬ FlipK L.perm s.2.1 s.1 y a := fun h' ↦ h (.inr (.inl h'))
      have hR : ¬ RecJ L (.programK y a) s := fun h' ↦ h (.inr (.inr h'))
      unfold encPotN
      rw [union_progMapK y a s, progMap_mem]
      by_cases hWn : s.2.1.2.1 y = none
      · by_cases hG : Good L.perm (union s.2.1 s.1)
        · have hG₀ : Good L.perm
              { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k y none } :=
            Good.mono (extendsAll_eraseK (union s.2.1 s.1) y).1 hG
          have ha : a ∉ badAttachK L.perm
              { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k y none } y :=
            not_and.mp (not_and.mp hF hWn) hG₀
          rw [encPotU_updK_eq L hG₀ (eraseK_k_self (union s.2.1 s.1) y) ha]
          exact encPotU_mono L (extendsAll_eraseK (union s.2.1 s.1) y).1 (fun _ ↦ rfl) hG _
        · have hG₀ : ¬ Good L.perm
              { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k y none } :=
            fun h₀ ↦ hR ⟨hWn, hG, h₀⟩
          rw [encPotU_of_not_good L fun h' ↦ hG₀ (Good.mono
            (extends_update_k (eraseK_k_self (union s.2.1 s.1) y)) h')]
          exact Nat.zero_le _
      · exact le_of_eq (encPotU_congr L (reprogK_k (union_k_some (D := s.1) (hW hWn))) rfl
          (fun _ ↦ rfl) _)
    rw [encPot_eq_encPotN, encPot_eq_encPotN]
    exact (Nat.cast_le.mpr hle).trans (le_add_of_nonneg_right zero_le_one)
  | programK' y a =>
    have hle : encPotN get L (progMap (.programK' y a) s) ≤ encPotN get L s := by
      have hW : s.2.1.2.2 y ≠ none → s.2.1.2.2 y = some a := fun h1 ↦ by
        by_contra h2
        exact h (.inl ⟨h1, h2⟩)
      have hF : ¬ FlipK' L.perm s.2.1 s.1 y a := fun h' ↦ h (.inr (.inl h'))
      have hR : ¬ RecJ L (.programK' y a) s := fun h' ↦ h (.inr (.inr h'))
      unfold encPotN
      rw [union_progMapK' y a s, progMap_mem]
      by_cases hWn : s.2.1.2.2 y = none
      · by_cases hG : Good L.perm (union s.2.1 s.1)
        · have hG₀ : Good L.perm
              { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' y none } :=
            Good.mono (extendsAll_eraseK' (union s.2.1 s.1) y).1 hG
          have ha : a ∉ badCompleteOutK' L.perm
              { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' y none } y :=
            not_and.mp (not_and.mp hF hWn) hG₀
          rw [encPotU_updK'_eq L hG₀ (eraseK'_k'_self (union s.2.1 s.1) y) ha]
          exact encPotU_mono L (extendsAll_eraseK' (union s.2.1 s.1) y).1 (fun _ ↦ rfl) hG _
        · have hG₀ : ¬ Good L.perm
              { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' y none } :=
            fun h₀ ↦ hR ⟨hWn, hG, h₀⟩
          rw [encPotU_of_not_good L fun h' ↦ hG₀ (Good.mono
            (extends_update_k' (eraseK'_k'_self (union s.2.1 s.1) y)) h')]
          exact Nat.zero_le _
      · exact le_of_eq (encPotU_congr_k' L (reprogK'_k' (union_k'_some (D := s.1) (hW hWn)))
          rfl (fun _ ↦ rfl) _)
    rw [encPot_eq_encPotN, encPot_eq_encPotN]
    exact (Nat.cast_le.mpr hle).trans (le_add_of_nonneg_right zero_le_one)

/-- **The weight of the jump states** of a program port. -/
noncomputable def kJumpW (L : HonestTable) (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ q, (if KJump L c q.2 then (1 : ℝ) else 0) * (σ q q).re)

end levels

end Quantum.Xmss.Assembly


/-! ## The challenge prefix -/

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

section prefixPorts

/-- **The trial updates record codeword selections** (`CwTrialUpd` for `trialUpd`). -/
theorem cwTrialUpd_trialUpd : CwTrialUpd (Prod.snd : Mem → Selections) trialUpd where
  sel t m v hm := by
    show cwUpd t.l t.e t.x t.xi m.2 (some v) = _
    show (if m.2 t.l t.e = none then cwSel m.2 t.l t.e t.x t.xi v else m.2) = _
    rw [ite_eq_left hm]
  keep t m o k hk := by
    show cwUpd t.l t.e t.x t.xi m.2 o k.1 k.2 = m.2 k.1 k.2
    rcases o with _ | v
    · rfl
    · rcases cwUpd_some t.l t.e t.x t.xi m.2 v with h | h <;> rw [h]
      unfold cwSel
      split_ifs
      · unfold Selections.select
        by_cases h1 : k.1 = t.l
        · have h2 : k.2 ≠ t.e := fun h2 ↦ hk (Prod.ext h1 h2)
          rw [h1, Function.update_self, Function.update_of_ne h2]
        · rw [Function.update_of_ne h1]
      · rfl

/-- The database grade cap at the prefix's calls: `6q + clsCap`. -/
def nD (q : ℕ) : ℕ := 6 * q + clsCap

/-- The hardwired grade of the level sets: `progCap + 1` (a program call adds one cell). -/
def nW : ℕ := progCap + 1

/-- **The potential cap** on the states around the prefix's calls: `progCap + 6q + clsCap + 2`. -/
def potCap (q : ℕ) : ℕ := nW + nD q + 1

/-- The fresh-cell rate of the level sets at the prefix: `epsLev (nW + nD q) 18`. -/
noncomputable def epsQ (q : ℕ) : ℝ := epsLev (nW + nD q) 18

/-- **The charge of a `k`, `k'` sponge call** per unit of trace: `potCap (2 √(6ε) + 6ε)`. -/
noncomputable def kapS (q : ℕ) : ℝ := potCap q * (2 * √(6 * epsQ q) + 6 * epsQ q)

/-- **The charge of a read call** per unit of trace: the `k`, `k'` reads'
`potCap (ε + 2/|X| + 2/|Z| + 2 √ε)`, plus the trial reads' cell charge `2/|X| + 4/|X|²`. -/
noncomputable def kapR (q : ℕ) : ℝ :=
  potCap q * (epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q)) +
    (2 / (Fintype.card X : ℝ) + (2 / (Fintype.card X : ℝ)) ^ 2)

theorem epsQ_nonneg (q : ℕ) : 0 ≤ epsQ q := epsLev_nonneg _ _

theorem kapS_nonneg (q : ℕ) : 0 ≤ kapS q := by
  have := epsQ_nonneg q
  unfold kapS
  positivity

theorem kapR_nonneg (q : ℕ) : 0 ≤ kapR q := by
  have := epsQ_nonneg q
  unfold kapR
  positivity

/-- **The invariant at the prefix's calls**: only `ReadOk` reads, database grade at most `nD q`,
hardwired grade at most `progCap`, no decompressed `⊥`. -/
def PreInv (q : ℕ) (i : (recHwSpec X Z HPos Selections).Port)
    (τ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ) : Prop :=
  bR i = 0 ∧
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × HwReg X Z Mem ↦ m.2)
      {s | dbGrade s.1 ≤ nD q ∧ dbGrade s.2.1 ≤ progCap} τ ∧
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × HwReg X Z Mem ↦ m.2)
      {s | NoBot s} (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
        ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem) τ)

/-- The initial state has no hardwired cell. -/
theorem querySupportedOn_initR_hwGrade :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦ dbGrade m.2.2.1)
      (Set.Iic 0) initR := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty X Z, m0R) : HwReg X Z Mem)).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, hwEmpty, dbGrade, Database.size_empty]
  · exact False.elim (h rfl)

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The prefix's program calls**: at most `progCap` (`progCalls_gameR`). -/
theorem progCalls_prefixR (L : HonestTable) :
    IFreeM.IsChargeBound (prefixR A L) (progChargeR HPos Selections) progCap := by
  have h := progCalls_gameR hperm hsign L
  rw [gameR_eq] at h
  exact isChargeBound_of_bind₂ h

/-- **The invariant holds at every call of the prefix** (CostRun's `forallQueries_of_charge_step`
for the database and hardwired grades with `chgB_prefixR`, EventSqrt's `forallQueries_noBot`). -/
theorem forallQueries_preInv (L : HonestTable) :
    ∃ P : ∀ (i : (recHwSpec X Z HPos Selections).Port) (E : QReg),
      Matrix (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E)
        (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E) ℂ →
          Prop, (∀ i E σ, P i E σ → PreInv q i (MatrixMap.traceRight _ E σ)) ∧
      (runtimeR m0R).ForallQueries .instruments P (prefixR A L) initR := by
  set κ : (recHwSpec X Z HPos Selections).Port → ℕ := fun i ↦
    (if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1) +
      (if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0) with hκ
  have hκ1 : ∀ i, κ i = 1 := fun i ↦ by
    rw [hκ]
    by_cases h : extCls X Z Mem (recSpec HPos Selections) i = true <;> simp [h]
  have hx : IFreeM.IsChargeBound (prefixR A L) (portCharge κ) (6 * q + clsCap) :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl)
      ((advCalls_prefixR hperm hsign L).add (clsCalls_prefixR hperm hsign L))
  have h1 := forallQueries_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1) κ bR
    (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_step m0R i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hκ1]))) .instruments (prefixR A L) hx (chgB_prefixR A L)
    querySupportedOn_initR
  have h2 := forallQueries_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.2.1)
    (extProgCharge X Z Mem (recSpec HPos Selections)) (fun _ ↦ 0)
    (fun i r t σ hσ ↦ by
      rcases i with i | j
      · exact querySupportedOn_hw_step (hwEmpty X Z) m0R i r t σ hσ
      · exact gradeSupp_recStep j r t σ hσ) .instruments (prefixR A L)
    (progCalls_prefixR hperm hsign L) (isChargeBound_portCharge_zero _)
    querySupportedOn_initR_hwGrade
  have h3 := forallQueries_noBot m0R .instruments (prefixR A L)
    (noBot_init m0R (SubState.basis ()).matrix)
  refine ⟨_, fun i E σ hP ↦ ?_, forallQueries_and (forallQueries_and h1 h2) h3⟩
  obtain ⟨⟨⟨hb, hg1⟩, ⟨-, hg2⟩⟩, hnb⟩ := hP
  refine ⟨hb, ?_, hnb⟩
  have g1 := (querySupportedOn_traceRight (q := fun a :
      (recHwSpec X Z HPos Selections).In i × HwReg X Z Mem ↦ dbGrade a.2.1) hg1).imp
    (q' := fun a : (recHwSpec X Z HPos Selections).In i × HwReg X Z Mem ↦ a.2)
    (S' := {s : HwReg X Z Mem | dbGrade s.1 ≤ nD q}) fun a ha ↦ by
      have := Set.mem_Iic.mp ha
      show dbGrade a.2.1 ≤ 6 * q + clsCap
      omega
  have g2 := (querySupportedOn_traceRight (q := fun a :
      (recHwSpec X Z HPos Selections).In i × HwReg X Z Mem ↦ dbGrade a.2.2.1) hg2).imp
    (q' := fun a : (recHwSpec X Z HPos Selections).In i × HwReg X Z Mem ↦ a.2)
    (S' := {s : HwReg X Z Mem | dbGrade s.2.1 ≤ progCap}) fun a ha ↦ by
      have := Set.mem_Iic.mp ha
      show dbGrade a.2.2.1 ≤ progCap
      omega
  exact (querySupportedOn_inter g1 g2).imp fun _ h ↦ h

end prefixPorts

section jumpSplit

/-- **The weight of the `RecJ` states** of a program port. -/
noncomputable def recJW (L : HonestTable) (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ q, (if RecJ L c q.2 then (1 : ℝ) else 0) * (σ q q).re)

/-- **The challenge prefix programs only cells of `tableHw L` with their values** (as
`progsIn_gameT`). -/
theorem progsIn_prefixT (L : HonestTable) (A : Adversary (X × Z)) :
    ProgsIn (tableHw L) (valueAt L) (prefixT Selections cwUpd (pubOf L) A) :=
  progsIn_revealThen (tableHw L) (valueAt L) _ _ fun _ ↦
    progsIn₂_bind (tableHw L) (valueAt L) _ _ (progsIn_substitute (tableHw L) (valueAt L) _
      (progsIn_challengeT (tableHw L) (valueAt L) cwUpd (progsOf_tableHw L)) _) fun _ ↦ trivial

/-- **The calls of the prefix stay inside `tableHw L`** (as `forallQueries_hwSupp_gameR`). -/
theorem forallQueries_hwSupp_prefixR (A : Adversary (X × Z)) (L : HonestTable) :
    (runtimeR m0R).ForallQueries .instruments (hwSupp Selections m0R (tableHw L)) (prefixR A L)
      initR :=
  forallQueries_of_progsIn (tableHw L) (valueAt L) m0R .instruments _
    (progsIn_prefixT L A) initR (querySupportedOn_initR_hw (tableHw L))

theorem ofReal_ind_mul_le {α : Type} (S : Set α) (g : α → ℝ≥0∞) (a : α) {r : ℝ}
    (hg : g a = ENNReal.ofReal r) {p p' : Prop} [Decidable p] [Decidable p']
    (h : p → a ∈ S ∨ p') :
    ENNReal.ofReal ((if p then (1 : ℝ) else 0) * r) ≤
      S.indicator g a + ENNReal.ofReal ((if p' then (1 : ℝ) else 0) * r) := by
  by_cases hp : p
  · rcases h hp with hS | hp'
    · rw [ite_eq_left hp, Set.indicator_of_mem hS, hg, one_mul]
      exact le_self_add
    · rw [ite_eq_left hp, ite_eq_left hp']
      exact le_add_self
  · rw [ite_eq_right hp, zero_mul, ENNReal.ofReal_zero]
    exact zero_le

/-- **The jump states split**: inside `tableHw L` with a port programming its value and at low
grade, a jump state is a target-free fresh flip (KeyLazy's `kfSet`, `kfSet'`) or a `RecJ` state. -/
theorem kJumpW_le (L : HonestTable) (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hc : ProgOf (tableHw L) c)
    (hsupp : ∀ q, σ q q ≠ 0 → Quantum.Sponge.HwLe q.2.2.1 (tableHw L) ∧
      dbGrade q.2.2.1 ≤ progCap ∧ progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    kJumpW L c σ ≤ kfW L.perm c σ + recJW L c σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hsum : ∀ (p : Unit × HwReg X Z Mem → Prop) [DecidablePred p],
      ENNReal.ofReal (∑ q, (if p q then (1 : ℝ) else 0) * (σ q q).re) =
        ∑ q, ENNReal.ofReal ((if p q then (1 : ℝ) else 0) * (σ q q).re) := fun p _ ↦
    ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hre q)
  have key : ∀ S : Set (Unit × HwReg X Z Mem),
      (∀ q, σ q q ≠ 0 → KJump L c q.2 → q ∈ S ∨ RecJ L c q.2) →
      kJumpW L c σ ≤ diagMass S σ + recJW L c σ := fun S hS ↦ by
    unfold kJumpW recJW diagMass
    rw [hsum (fun q ↦ KJump L c q.2), hsum (fun q ↦ RecJ L c q.2), ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · rw [h0, Complex.zero_re, mul_zero, ENNReal.ofReal_zero]
      exact zero_le
    · exact ofReal_ind_mul_le S (fun a ↦ ENNReal.ofReal (σ a a).re) q rfl (hS q h0)
  cases c with
  | programH z v =>
    refine (key ∅ fun _ _ h ↦ h.elim).trans_eq ?_
    show diagMass ∅ σ + _ = (0 : ℝ≥0∞) + _
    rw [diagMass_empty]
  | programK y a =>
    refine key (kfSet L.perm y a) fun q h0 h ↦ ?_
    obtain ⟨hW, hg1, hg2⟩ := hsupp q h0
    rcases h with ⟨h1, h2⟩ | hF | hR
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
      have h3 : (tableHw L).2.1 y = some b := hW.2.1 y b hb
      exact absurd (hb.trans (Option.some.inj (h3.symm.trans hc) ▸ rfl)) h2
    · exact .inl (mem_kfSet.mpr ⟨hF, hg1, hg2⟩)
    · exact .inr hR
  | programK' y a =>
    refine key (kfSet' L.perm y a) fun q h0 h ↦ ?_
    obtain ⟨hW, hg1, hg2⟩ := hsupp q h0
    rcases h with ⟨h1, h2⟩ | hF | hR
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
      have h3 : (tableHw L).2.2 y = some b := hW.2.2 y b hb
      exact absurd (hb.trans (Option.some.inj (h3.symm.trans hc) ▸ rfl)) h2
    · exact .inl (mem_kfSet'.mpr ⟨hF, hg1, hg2⟩)
    · exact .inr hR

end jumpSplit

section prefixCharges

variable {q : ℕ} (L : HonestTable)

/-- **The charge of a sponge call**: `0` at `h`, `kapS q tr σ` at `k`, `k'`. -/
noncomputable def cSq (q : ℕ) : ∀ p : SpongePort,
    Matrix (spongeIn X Z p × HwReg X Z Mem) (spongeIn X Z p × HwReg X Z Mem) ℂ → ℝ≥0∞
  | .h, _ => 0
  | .k, σ => ENNReal.ofReal (kapS q * σ.trace.re)
  | .k', σ => ENNReal.ofReal (kapS q * σ.trace.re)

/-- **The charge of a read call** other than a trial read: the `k`, `k'` reads'
`potCap (ε + 2/|X| + 2/|Z| + 2 √ε) tr σ`. -/
noncomputable def cRq (q : ℕ) (_c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  (potCap q : ℝ≥0∞) * ENNReal.ofReal
    ((epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q)) * σ.trace.re)

theorem encPotN_le_potCap {s : HwReg X Z Mem} (hW : dbGrade s.2.1 ≤ nW)
    (hD : dbGrade s.1 ≤ nD q + 1) : encPotN Prod.snd L s ≤ potCap q :=
  (encPotN_le Prod.snd L s).trans (by unfold potCap; omega)

/-- **`hS` on the prefix**: the `h` port raises the potential by its trace, the `k`, `k'` ports
by their trace plus `kapS q` per unit of trace (two-sided fresh bounds of the level sets). -/
theorem hS_prefix (hπ : PermGood L.perm 18) (p : SpongePort)
    {σ : Matrix (spongeIn X Z p × HwReg X Z Mem) (spongeIn X Z p × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) (hI : PreInv q (.inl (.inl (.inl p))) σ) :
    ∑' _r : Unit, potential (diagPot fun s ↦ √(encPot Prod.snd L s))
        (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m0R).U p) σ) ≤
      potential (diagPot fun s ↦ √(encPot Prod.snd L s)) σ +
        (ENNReal.ofReal σ.trace.re + cSq q p σ) := by
  have hsupp : QuerySupportedOn (fun m : spongeIn X Z p × HwReg X Z Mem ↦ m.2)
      {s | dbGrade s.1 ≤ nD q ∧ dbGrade s.2.1 ≤ nW} σ :=
    hI.2.1.imp fun _ h ↦ ⟨h.1, h.2.trans (Nat.le_succ _)⟩
  have hF : ∀ s : HwReg X Z Mem, dbGrade s.2.1 ≤ nW → dbGrade s.1 ≤ nD q + 1 →
      encPotN Prod.snd L s ≤ potCap q := fun s hW hD ↦ encPotN_le_potCap L hW hD
  have hk : ∀ (i : SpongePort), (∀ (m : ℕ) (W : Hw X Z) (mm : Mem),
      PortInst (slice (levSet (encPotN Prod.snd L) nW m) W mm) i (nD q + 1)
        (ENNReal.ofReal (epsQ q))) →
      ∀ {τ : Matrix (spongeIn X Z i × HwReg X Z Mem) (spongeIn X Z i × HwReg X Z Mem) ℂ},
      τ.PosSemidef → QuerySupportedOn (fun m : spongeIn X Z i × HwReg X Z Mem ↦ m.2)
        {s | dbGrade s.1 ≤ nD q ∧ dbGrade s.2.1 ≤ nW} τ →
      ∑' _r : Unit, potential (diagPot fun s ↦ √(encPot Prod.snd L s))
          (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m0R).U i) τ) ≤
        potential (diagPot fun s ↦ √(encPot Prod.snd L s)) τ +
          (ENNReal.ofReal τ.trace.re + ENNReal.ofReal (kapS q * τ.trace.re)) := by
    intro i hε τ hτ hs
    rw [sqrt_encPot_eq]
    refine (tsum_potential_sponge_layer_le (encPotN Prod.snd L) nW (nD q) (potCap q) hF
      (epsQ_nonneg q) (hwEmpty X Z) m0R i hε hτ hs).trans (add_le_add le_rfl (le_add_left
        (le_of_eq (congrArg ENNReal.ofReal ?_))))
    unfold kapS
    ring
  cases p with
  | h =>
    refine (tsum_potential_spongeH_le (encPot_nonneg Prod.snd L) (encPot_update_h_le Prod.snd L)
      (hwEmpty X Z) m0R hσ).trans (add_le_add le_rfl ?_)
    rw [cSq, add_zero]
  | k => exact hk .k (fun m W mm ↦ portInst_levSet_k Prod.snd L hπ nW (nD q) m W mm) hσ hsupp
  | k' => exact hk .k' (fun m W mm ↦ portInst_levSet_k' Prod.snd L hπ nW (nD q) m W mm) hσ hsupp

/-- **`hR` on the prefix**: the reads other than the trial reads are `k`, `k'` reads keeping the
memory (`ReadOk`); each raises the potential by at most `cRq q` (two-sided fresh bounds of the
level sets through `keepE`, the recorded cells `2/|Y|`, the flip-recorded mass at most `tr σ`). -/
theorem hR_prefix (hπ : PermGood L.perm 18) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (ht : ¬ IsTrial trialUpd c)
    (hσ : σ.PosSemidef) (hI : PreInv q (.inl (.inl (.inr c))) σ) :
    ∑' r, potential (diagPot fun s ↦ √(encPot Prod.snd L s))
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      potential (diagPot fun s ↦ √(encPot Prod.snd L s)) σ + cRq q c σ := by
  have hok : ReadOk c := readOk_of_okCharge hI.1
  have hnb : ReadNoBot c σ := readNoBot_of_noBot c hI.2.2
  have hsupp : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2)
      {s | dbGrade s.1 ≤ nD q ∧ dbGrade s.2.1 ≤ nW} σ :=
    hI.2.1.imp fun _ h ↦ ⟨h.1, h.2.trans (Nat.le_succ _)⟩
  have hg : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ dbGrade m.2.1) (Set.Iic (nD q)) σ :=
    hI.2.1.imp fun _ h ↦ Set.mem_Iic.mpr h.1
  have hcost : ∀ m, (∀ W mm, PortInst (slice (levSet (encPotN Prod.snd L) nW m) W mm)
      (readPort c) (nD q + 1) (ENNReal.ofReal (epsQ q))) → KeepUpd c →
      readCost (levSet (encPotN Prod.snd L) nW m) c σ ≤ ENNReal.ofReal
        ((epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q)) * σ.trace.re) :=
    fun m hε hk ↦ readCost_le_of_keep _ c hk hσ (epsQ_nonneg q)
      ((keepE_le_of_portInst _ ENNReal.ofReal_ne_top c hε hσ hg).trans_eq
        (by rw [ENNReal.toReal_ofReal (epsQ_nonneg q)]))
  rw [sqrt_encPot_eq]
  refine tsum_potential_read_layer_le (encPotN Prod.snd L) nW (nD q) (potCap q)
    (fun s hW hD ↦ encPotN_le_potCap L hW hD) c hσ hnb (fun m ↦ ?_) hsupp
  rcases hok with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ht'
  · exact hcost m (fun W mm ↦ portInst_levSet_k Prod.snd L hπ nW (nD q) m W mm)
      (fun _ _ ↦ rfl)
  · exact hcost m (fun W mm ↦ portInst_levSet_k' Prod.snd L hπ nW (nD q) m W mm)
      (fun _ _ ↦ rfl)
  · exact absurd ht' ht

theorem dbGrade_progMap_le (c : HwProg X Z) (s : HwReg X Z Mem) :
    dbGrade (progMap c s).1 ≤ dbGrade s.1 + 1 ∧ dbGrade (progMap c s).2.1 ≤ dbGrade s.2.1 + 1 := by
  have hK : hwProgKraus c (progIdx c s) ((), progMap c s) ((), s) ≠ 0 := by
    rw [hwProgKraus_apply c (progIdx c s) ((), progMap c s) ((), s), ite_eq_left ⟨rfl, rfl⟩]
    exact one_ne_zero
  exact ⟨dbGrade_le_of_hwProgKraus_ne_zero c _ () () s _ hK,
    dbGrade_hw_le_of_hwProgKraus_ne_zero c _ () () s _ hK⟩

/-- **The program jump on the prefix**: at most `potCap q` times the weight of the jump states
(`KJump`). -/
theorem progJump_le_prefix (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hI : PreInv q (.inl (.inr c)) σ) :
    progJump (encPot Prod.snd L) c σ ≤ (potCap q : ℝ≥0∞) * kJumpW L c σ := by
  refine (progJump_le (encPot_nonneg Prod.snd L) c (KJump L c)
    (fun s hs ↦ encPot_progMap_le Prod.snd L c s hs) hσ (H := potCap q) fun a ha ↦ ?_).trans_eq ?_
  · have hs := (hI.2.1 a a ha).1
    obtain ⟨h1, h2⟩ := dbGrade_progMap_le c a.2
    rw [encPot_eq_encPotN]
    exact_mod_cast encPotN_le_potCap L (h2.trans (Nat.add_le_add_right hs.2 1))
      (h1.trans (Nat.add_le_add_right hs.1 1))
  · rw [kJumpW, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem encOff_le_grade (z : Z) (k : Layer × KeyIndex) (s : HwReg X Z Mem) :
    encOff L z k s ≤ dbGrade s.2.1 + dbGrade s.1 := by
  unfold encOff
  split_ifs
  · have h1 := tailOutCount_eq_off_add L.perm (union s.2.1 s.1) trunc128 (MsgAt L k)
      Codeword.Valid z
    have h2 := (tailOutCount_le_tailCount L.perm (union s.2.1 s.1) trunc128 (MsgAt L k)
      Codeword.Valid).trans ((tailCount_le_size L.perm (union s.2.1 s.1) (MsgAt L k)).trans
        (size_unionH_le s.2.1 s.1))
    exact_mod_cast (Nat.le_add_right _ _).trans (h1 ▸ h2)
  · positivity

/-- **The trial charge on the prefix**: `(3 C + 3) massW + (2/|X| + 4/|X|²) tr σ` with
`C = nW + nD q` (`trialChg_le_massW`, the count bounded by the grades). -/
theorem trialChg_le_prefix (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hI : PreInv q (.inl (.inl (.inr c))) σ) :
    trialChg Prod.snd trialUpd L c σ ≤
      ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ) + 3) * massW Prod.snd trialUpd L c σ +
        ENNReal.ofReal ((2 / (Fintype.card X : ℝ) + (2 / (Fintype.card X : ℝ)) ^ 2) *
          σ.trace.re) := by
  by_cases ht : IsTrial trialUpd c
  · refine trialChg_le_massW Prod.snd trialUpd L ht (Nat.cast_nonneg _) hσ fun a ↦ ?_
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
  · simp only [trialChg, ht, ↓reduceIte, zero_le]

/-- **The charge of a read call on the prefix**: the trial charge and `cRq` together are at most
`(3C + 3) massW + kapR q tr σ`. -/
theorem readCharge_le (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hI : PreInv q (.inl (.inl (.inr c))) σ) :
    trialChg Prod.snd trialUpd L c σ + cRq q c σ ≤
      ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ) + 3) * massW Prod.snd trialUpd L c σ +
        ENNReal.ofReal (kapR q) * ENNReal.ofReal σ.trace.re := by
  have htr : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have he := epsQ_nonneg q
  refine (add_le_add (trialChg_le_prefix L c hσ hI) le_rfl).trans ?_
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  unfold cRq
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) htr)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) htr)),
    ← ENNReal.ofReal_mul (kapR_nonneg q)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold kapR
  ring

end prefixCharges

section joint

attribute [local instance] badRDec

/-- **The joint count of the selecting reads along the challenge prefix** (`cntGW`, on good
unions). -/
noncomputable def cntGP (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments
    (extWeight (hwCost (cntGW Prod.snd trialUpd L) fun _ _ ↦ 0)) (prefixR A L) initR

/-- **The weight of the program jump states along the prefix** (`KJump`: the `k`, `k'` program
calls on a fresh flip, a `RecJ` state or a hardwired cell of another value). -/
noncomputable def kJumpPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments
    (extWeight (hwCost (fun _ _ ↦ 0) (kJumpW L))) (prefixR A L) initR

/-- **The target-free fresh `k`, `k'` flips along the prefix** (KeyLazy's `kfW`). -/
noncomputable def kfPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments
    (extWeight (hwCost (fun _ _ ↦ 0) (kfW L.perm))) (prefixR A L) initR

/-- **The `RecJ` weight along the prefix**: the `k`, `k'` program calls on a bad union that the
database's value at the programmed cell makes bad. -/
noncomputable def recJPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments
    (extWeight (hwCost (fun _ _ ↦ 0) (recJW L))) (prefixR A L) initR

/-- The target-free flips of the prefix are at most those of the game. -/
theorem kfPre_le (A : Adversary (X × Z)) (L : HonestTable) :
    kfPre A L ≤ (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfW L.perm))) (gameR A L) initR := by
  rw [gameR_eq]
  exact totalWeight_le_bind₂ (runtimeR m0R) .instruments _ (prefixR A L) _ initR

/-- **The averaged target-free flips of the game** (KeyLazy's `uavg_kTot_le` before
`kTot_le_kfTot`): on the `PermGood` tables at most `progCap · 2^-301` plus `progCap` times the bad
fraction of a reparametrization exposing the keys. -/
theorem uavg_kfTot_le {q : ℕ} {A : Adversary (X × Z)}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    {E Q V : Type} [Fintype E] [Nonempty E] [Fintype Q] [Fintype V]
    (e : HonestTable × E → Q × (((X → Z) × (X → Z)) × V)) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card Q * Fintype.card (((X → Z) × (X → Z)) × V) ≤
      Fintype.card (HonestTable × E))
    (par : Q → PublicParameter) (perm : Q → Equiv.Perm (X × Z)) (hk : Q → Z → X)
    (val : V → HPos → Digest)
    (hgame : ∀ t, G t → gameR A t.1 = gameKK A (par (e t).1) (perm (e t).1) (hk (e t).1)
      (val (e t).2.2) (e t).2.1.1 (e t).2.1.2)
    (hπ : ∀ t, G t → perm (e t).1 = t.1.perm) :
    uavg (fun L ↦ if PermGood L.perm 18 then (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfW L.perm))) (gameR A L) initR else 0) ≤
      (2 ^ 301)⁻¹ * progCap + progCap * ((Fintype.card (HonestTable × E) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬G t).card) := by
  refine uavg_le_of_injOn e G hinj hcard _
    (fun p x ↦ if PermGood (perm p) 18 then (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfW (perm p))))
        (gameKK A (par p) (perm p) (hk p) (val x.2) x.1.1 x.1.2) initR else 0)
    (fun t ht ↦ ?_) progCap (fun t _ ↦ ?_) ((2 ^ 301)⁻¹ * progCap) (fun p ↦ ?_)
  · by_cases hL : PermGood t.1.perm 18
    · have hp : PermGood (perm (e t).1) 18 := (hπ t ht).symm ▸ hL
      rw [ite_eq_left hL, ite_eq_left hp, hgame t ht, hπ t ht]
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hL : PermGood t.1.perm 18
    · rw [ite_eq_left hL]
      refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
        (w' := extWeight (hwCost (fun _ _ ↦ 0) fun _ σ ↦ ENNReal.ofReal σ.trace.re))
        (fun i σ hσ ↦ ?_) (gameR A t.1) initR_posSemidef).trans
        (totalWeight_progs_le (gameR A t.1) (progCalls_gameR hperm hsign t.1))
      rcases i with ((p | c) | c) | T
      · exact le_rfl
      · exact le_rfl
      · dsimp only [extWeight, sumWeight, hwCost]
        cases c with
        | programH z u => exact zero_le
        | programK y a => exact diagMass_le_trace _ hσ
        | programK' y a => exact diagMass_le_trace _ hσ
      · exact le_rfl
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hp : PermGood (perm p) 18
    · refine (Finset.sum_congr rfl fun x _ ↦ ite_eq_left hp).trans_le ?_
      exact sum_pair_le (fun k k' w ↦ (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfW (perm p))))
          (gameKK A (par p) (perm p) (hk p) (val w) k k') initR) _ _
        fun w ↦ sum_kfTot_le A (par p) (perm p) (hk p) (val w) hperm hsign hp
    · rw [Finset.sum_eq_zero fun x _ ↦ ite_eq_right hp]
      exact zero_le

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The joint count of the selecting reads on the challenge prefix** (Security's `encJoint`,
restated on `cntGW`): for a table with `PermGood π 18`, at most `2^22 (6q + progCap)` plus `2^22`
times the charges along the prefix: `(3C + 3)` per unit of recorded mass (`massW`, with
`C = nW + nD q` the count bound on the support), `kapS q` per `k`, `k'` sponge call, `kapR q` per
read call and `potCap q` per unit of weight of the program jump states (`kJumpPre`). -/
theorem cntGP_le (L : HonestTable) (hπ : PermGood L.perm 18) :
    cntGP A L ≤ 2 ^ 22 * ((6 * q + progCap : ℕ) : ℝ≥0∞) + 2 ^ 22 *
      (ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ) + 3) *
          (runtimeR m0R).totalWeight .instruments
            (extWeight (hwCost (massW Prod.snd trialUpd L) fun _ _ ↦ 0)) (prefixR A L) initR +
        ((6 * q : ℕ) : ℝ≥0∞) * ENNReal.ofReal (kapS q) +
        (clsCap : ℝ≥0∞) * ENNReal.ofReal (kapR q) + (potCap q : ℝ≥0∞) * kJumpPre A L) := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  have h := totalWeight_cntGW_le Prod.snd trialUpd cwTrialUpd_trialUpd (fun _ _ _ ↦ rfl) L m0R P
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
    extWeight (hwCost (massW Prod.snd trialUpd L) fun _ _ ↦ 0)
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
  have hle := totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w := portCh X Z HPos Selections (cSq q)
      (fun c σ ↦ trialChg Prod.snd trialUpd L c σ + cRq q c σ) (progJump (encPot Prod.snd L)))
    (w' := fun i σ ↦ (ENNReal.ofReal (3 * C + 3) * wM i σ + ENNReal.ofReal (kapS q) * wS i σ) +
      (ENNReal.ofReal (kapR q) * wR i σ + (potCap q : ℝ≥0∞) * wJ i σ))
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef hx
  · have e := (totalWeight_add_weight (runtimeR m0R) .instruments
      (fun i σ ↦ ENNReal.ofReal (3 * C + 3) * wM i σ + ENNReal.ofReal (kapS q) * wS i σ)
      (fun i σ ↦ ENNReal.ofReal (kapR q) * wR i σ + (potCap q : ℝ≥0∞) * wJ i σ)
      (prefixR A L) initR).trans (congrArg₂ (· + ·)
        ((totalWeight_add_weight (runtimeR m0R) .instruments
          (fun i σ ↦ ENNReal.ofReal (3 * C + 3) * wM i σ)
          (fun i σ ↦ ENNReal.ofReal (kapS q) * wS i σ) (prefixR A L) initR).trans
          (congrArg₂ (· + ·)
            (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wM (prefixR A L) initR)
            (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wS (prefixR A L) initR)))
        ((totalWeight_add_weight (runtimeR m0R) .instruments
          (fun i σ ↦ ENNReal.ofReal (kapR q) * wR i σ)
          (fun i σ ↦ (potCap q : ℝ≥0∞) * wJ i σ) (prefixR A L) initR).trans
          (congrArg₂ (· + ·)
            (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wR (prefixR A L) initR)
            (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wJ (prefixR A L) initR))))
    have hS : (runtimeR m0R).totalWeight .instruments wS (prefixR A L) initR ≤
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
    have hJ : (potCap q : ℝ≥0∞) * (runtimeR m0R).totalWeight .instruments wJ (prefixR A L) initR ≤
        (potCap q : ℝ≥0∞) * kJumpPre A L :=
      le_refl _
    refine hle.trans (e.trans_le ((add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hS zero_le)) (add_le_add (mul_le_mul_of_nonneg_left hR zero_le)
        hJ)).trans_eq ?_))
    ring
  · rcases i with ((p | c) | c) | T
    · show cSq q p σ ≤ (ENNReal.ofReal (3 * C + 3) * 0 + ENNReal.ofReal (kapS q) *
          (((1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)) +
          (ENNReal.ofReal (kapR q) * 0 + (potCap q : ℝ≥0∞) * 0)
      rw [Nat.cast_one, one_mul]
      rw [mul_zero, mul_zero, mul_zero, zero_add, zero_add, add_zero,
        ← ENNReal.ofReal_mul (kapS_nonneg q)]
      cases p with
      | h => exact zero_le
      | k => exact le_rfl
      | k' => exact le_rfl
    · show trialChg Prod.snd trialUpd L c σ + cRq q c σ ≤
        (ENNReal.ofReal (3 * C + 3) * massW Prod.snd trialUpd L c σ +
          ENNReal.ofReal (kapS q) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)) +
        (ENNReal.ofReal (kapR q) * ENNReal.ofReal σ.trace.re + (potCap q : ℝ≥0∞) * 0)
      rw [Nat.cast_zero, zero_mul]
      rw [mul_zero, mul_zero, add_zero, add_zero]
      exact readCharge_le L c hσ hI
    · show progJump (encPot Prod.snd L) c σ ≤
        (ENNReal.ofReal (3 * C + 3) * 0 +
          ENNReal.ofReal (kapS q) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)) +
        (ENNReal.ofReal (kapR q) * 0 + (potCap q : ℝ≥0∞) * kJumpW L c σ)
      rw [Nat.cast_zero, zero_mul, mul_zero, mul_zero, mul_zero, add_zero, zero_add, zero_add]
      exact progJump_le_prefix L c hσ hI
    · exact zero_le

/-- **The codeword flips of the prefix against the joint count** (`encW_le_cntGW` at the prefix's
calls, whose hardwired grade is at most `progCap`): at most `2^-128 cntGP`. -/
theorem encWPre_le_cntGP (L : HonestTable) :
    (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (encW Prod.snd trialUpd (BadR L progCap) L) fun _ _ ↦ 0))
        (prefixR A L) initR ≤ ENNReal.ofReal (2 ^ 128)⁻¹ * cntGP A L := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w' := fun i σ ↦ ENNReal.ofReal (2 ^ 128)⁻¹ *
      extWeight (hwCost (cntGW Prod.snd trialUpd L) fun _ _ ↦ 0) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef hx).trans_eq
      (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ _ (prefixR A L) initR)
  rcases i with ((p | c) | c) | T
  · exact zero_le
  · exact encW_le_cntGW Prod.snd trialUpd (BadR L progCap) (fun _ ↦ Iff.rfl) c hσ fun a ↦ by
      by_cases h0 : σ a a = 0
      · exact .inr h0
      · exact .inl (hI.2.1 a a h0).1.2
  · exact zero_le
  · exact zero_le

/-- **The jump weight of the prefix splits** into the target-free fresh flips and the `RecJ`
weight (`kJumpW_le`: the prefix programs only `tableHw L` values, its calls stay inside
`tableHw L` and at low grade for `q ≤ 2^64`). -/
theorem kJumpPre_le (hq : q ≤ 2 ^ 64) (L : HonestTable) :
    kJumpPre A L ≤ kfPre A L + recJPre A L := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  have hT := progCap_add_le hq
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i τ ↦ PreInv q i τ ∧ PortIn Selections (tableHw L) i ∧
      ∀ a, ¬ Quantum.Sponge.HwLe a.2.2.1 (tableHw L) → τ a a = 0)
    (P := fun i E σ ↦ P i E σ ∧ hwSupp Selections m0R (tableHw L) i E σ)
    (fun i E σ h ↦ ⟨hP i E σ h.1, h.2.1, fun a ha ↦
      traceRight_diag_eq_zero fun e ↦ h.2.2 (a, e) ha⟩)
    (w' := fun i σ ↦ extWeight (hwCost (fun _ _ ↦ 0) (kfW L.perm)) i σ +
      extWeight (hwCost (fun _ _ ↦ 0) (recJW L)) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef
    (forallQueries_and hx (forallQueries_hwSupp_prefixR A L))).trans_eq
      (totalWeight_add_weight (runtimeR m0R) .instruments _ _ (prefixR A L) initR)
  rcases i with ((p | c) | c) | T
  · exact zero_le
  · exact zero_le
  · refine kJumpW_le L c hσ hI.2.1 fun a ha ↦ ⟨?_, (hI.1.2.1 a a ha).1.2, ?_⟩
    · by_contra h
      exact ha (hI.2.2 a h)
    · have h1 : dbGrade a.2.1 ≤ nD q := (hI.1.2.1 a a ha).1.1
      unfold nD at h1
      omega
  · exact zero_le

end joint

end Quantum.Xmss.Assembly

end
