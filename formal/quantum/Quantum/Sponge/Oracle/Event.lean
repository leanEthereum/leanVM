module

public import Quantum.Sponge.Oracle.Runtime
public import VCVio.Quantum.VC.Proof.Offline
public import VCVio.Quantum.Oracle.Compressed.BinaryPartition
public import VCVio.Quantum.Oracle.Compressed.ProjectorEvent
public import VCVio.Quantum.Comp.Potential
public import VCVio.Quantum.Comp.GradedRuntime

@[expose] public section

/-!
# An upward-closed database event against the three compressed oracles

The transition-capacity bound of Chung, Fehr, Huang and Liao for one event, on the three
compressed oracles of `spongeCompressedRuntime`. Let `S` be a set of database triples that is
upward closed (`UpClosed`: filling an empty cell never leaves `S`) and does not contain the empty
triple. If, for every call `n < T`, filling one empty cell of one database of a triple outside `S`
whose databases have at most `n` entries lands in `S` for at most a fraction `ε n` of the answers
(`FreshBound S (n + 1) (ε n)`), then a program making at most `T` calls in total ends with the
database register in `S` with weight at most `(∑_{n < T} √(6 ε n))²`
(`rpow_inv_two_eventWeight_spongeCompressedRuntime_le`); with one `ε` for all calls, at most
`6 T² ε` (`eventWeight_spongeCompressedRuntime_le`).

The proof: the square root of the final event weight is at most the sum, over the calls, of the
square roots of the weights of the commutators `[1 ⊗ Q_S, U_p]` at the actual call inputs
(`Quantum.QuantumRuntime.rpow_inv_two_eventWeight_le_commutators`). At the `n`-th call every
database has at most `n` entries. Port `p` acts block-diagonally on the other two databases; on
each block it is VCVio's compressed oracle, and `Q_S` restricted to the block is the projector of
a set of databases of port `p`, whose instability at `n + 1` is at most `ε n` by upward closure.
VCVio's commutator bound `‖[P, O^(t)]‖² ≤ 6 I(t)`
(`Quantum.l2_opNorm_labelProjector_commutator_truncatedOracle_sq_le_six_mul`) bounds each block.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

universe u v w

namespace Quantum.Sponge

open Quantum

/-! ## Local bounds on one compressed oracle -/

section oneOracle

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The commutator of the compressed oracle with a label projector, on databases with at most
`n` entries, has squared norm at most `6` times the instability at `n + 1`. -/
theorem commutator_compressedOracle_sizeProjector_sq_le [UniformAnswerMeasure (A →ₒ Y)]
    (π : Database A Y → Bool) (n : ℕ) :
    ‖(labelProjector (fun m : (A × Y) × Database A Y ↦ π m.2) true * compressedOracle A Y -
        compressedOracle A Y * labelProjector (fun m : (A × Y) × Database A Y ↦ π m.2) true) *
        sizeProjector A Y n‖ ^ 2 ≤ 6 * (Database.instability π (n + 1)).toReal := by
  let Q := labelProjector (fun m : (A × Y) × Database A Y ↦ π m.2) true (α := ℂ)
  have he : (Q * compressedOracle A Y - compressedOracle A Y * Q) * sizeProjector A Y n =
      (Q * truncatedOracle A Y (n + 1) - truncatedOracle A Y (n + 1) * Q) *
        sizeProjector A Y n := by
    ext a b
    simp only [Q, labelProjector, Matrix.sub_apply, diagonal_mul, mul_diagonal,
      sizeProjector, truncatedOracle]
    by_cases hb : b.2.size ≤ n
    · by_cases hz : compressedOracle A Y a b = 0
      · simp [hz]
      · have ha := (size_le_of_compressedOracle_apply_ne_zero hz).trans
          (Nat.add_le_add_right hb 1)
        simp [hb, ha, Nat.le_succ_of_le hb]
    · simp [hb]
  have hp := l2_opNorm_sizeProjector_le_one (X := A) (Y := Y) n
  rw [he]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    ((l2_opNorm_mul _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hp)) 2).trans
      (l2_opNorm_labelProjector_commutator_truncatedOracle_sq_le_six_mul π (n + 1) true)

omit [DecidableEq Y] [AddCommGroup Y] in
/-- For a labelling whose `true` class is closed under filling a cell, the instability counts only
the fillings that enter the `true` class. -/
theorem instability_le_of_fresh [UniformAnswerMeasure (A →ₒ Y)] (lab : Database A Y → Bool)
    (t : ℕ) (ε : ℝ≥0∞)
    (hup : ∀ d, lab d = true → ∀ a u, d a = none → lab (Function.update d a (some u)) = true)
    (hfresh : ∀ d, lab d = false → d.size < t → ∀ a, d a = none →
      ((Finset.univ.filter fun u : Y ↦ lab (Function.update d a (some u)) = true).card :
        ℝ≥0∞) / Fintype.card Y ≤ ε) :
    Database.instability lab t ≤ ε := by
  rw [Database.instability_eq_iSup]
  refine iSup_le fun i ↦ iSup_le fun d ↦ iSup_le fun hi ↦ iSup_le fun hd ↦ iSup_le fun a ↦
    iSup_le fun ha ↦ ?_
  cases i
  · refine le_trans (le_of_eq ?_) (hfresh d hi hd a ha)
    simp only [ne_eq, Bool.not_eq_false]
  · have h : (Finset.univ.filter fun u : Y ↦ lab (Function.update d a (some u)) ≠ true) = ∅ := by
      ext u
      simp [hup d hi a u ha]
    rw [h]
    simp

/-- **One port on a block-split register.** Let a port act as the compressed oracle on its
query register and the database `d` of the split `e`, and as the identity on the rest `b`. If the
event `lab`, restricted to each rest `b` whose grades are admissible (`ok b`), has instability at
`n + 1` at most `r / 6`, then the commutator of the port with the event, on grades at most `n`,
has squared norm at most `r`. -/
theorem posSemidef_port_certificate {B N : Type} [Fintype B] [DecidableEq B] [Fintype N]
    [DecidableEq N] [UniformAnswerMeasure (A →ₒ Y)]
    (e : (A × Y) × N ≃ ((A × Y) × Database A Y) × B) (asm : Database A Y → B → N)
    (he : ∀ m d b, e.symm ((m, d), b) = (m, asm d b)) (lab : N → Bool) (g : N → ℕ)
    (ok : B → Prop) [DecidablePred ok] (n : ℕ) (hg : ∀ d b, g (asm d b) ≤ n ↔ d.size ≤ n ∧ ok b)
    {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ∀ b, ok b → 6 * (Database.instability (fun d ↦ lab (asm d b)) (n + 1)).toReal ≤ r) :
    let U := onFactor e (compressedOracle A Y)
    let Q := (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ labelProjector lab true
    let P : Matrix ((A × Y) × N) ((A × Y) × N) ℂ :=
      diagonal fun m ↦ if g m.2 ≤ n then (1 : ℂ) else 0
    (r • (1 : Matrix ((A × Y) × N) ((A × Y) × N) ℂ) -
      ((Q * U - U * Q) * P)ᴴ * ((Q * U - U * Q) * P)).PosSemidef := by
  intro U Q P
  let Qb (b : B) := labelProjector (fun m : (A × Y) × Database A Y ↦ lab (asm m.2 b)) true
    (α := ℂ)
  let Pb (b : B) : Matrix ((A × Y) × Database A Y) ((A × Y) × Database A Y) ℂ :=
    if ok b then sizeProjector A Y n else 0
  let Ub (_ : B) := compressedOracle A Y
  have hq : Q = liftBlocks e Qb := by
    simp only [Q, labelProjector]
    rw [← diagonal_one, diagonal_kronecker_diagonal, ← liftBlocks_diagonal e]
    congr 1
    funext b
    simp only [Qb, labelProjector]
    congr 1
    funext ⟨m, d⟩
    rw [he]
    simp
  have hp : P = liftBlocks e Pb := by
    simp only [P]
    rw [← liftBlocks_diagonal e]
    congr 1
    funext b
    simp only [Pb]
    split_ifs with hb
    · rw [sizeProjector]
      congr 1
      funext ⟨m, d⟩
      rw [he]
      simp [hg, hb]
    · refine diagonal_eq_zero.mpr (funext fun m ↦ ?_)
      obtain ⟨m, d⟩ := m
      simp [he, hg, hb]
  have hu : U = liftBlocks e Ub := (liftBlocks_const e _).symm
  have hb (b : B) :
      (r • (1 : Matrix ((A × Y) × Database A Y) ((A × Y) × Database A Y) ℂ) -
        ((Qb b * Ub b - Ub b * Qb b) * Pb b)ᴴ * ((Qb b * Ub b - Ub b * Qb b) * Pb b)).PosSemidef := by
    apply MatrixMap.posSemidef_scalar_sub_gram_of_norm_sq_le
    by_cases hb : ok b
    · have hP : Pb b = sizeProjector A Y n := by simp only [Pb, hb, ↓reduceIte]
      have h := commutator_compressedOracle_sizeProjector_sq_le (A := A) (Y := Y)
        (fun d ↦ lab (asm d b)) n
      rw [hP]
      exact h.trans (hr b hb)
    · have hP : Pb b = 0 := by simp only [Pb, hb, ↓reduceIte]
      rw [hP, Matrix.mul_zero, norm_zero, zero_pow two_ne_zero]
      exact hr0
  have hh := posSemidef_liftBlocks e hb
  change (liftBlocks e (r • 1 -
    (fun b ↦ (((Qb * Ub - Ub * Qb) * Pb) b)ᴴ) * ((Qb * Ub - Ub * Qb) * Pb))).PosSemidef at hh
  rw [liftBlocks_sub, liftBlocks_smul, liftBlocks_one] at hh
  change (_ - liftBlocks e ((fun b ↦ (((Qb * Ub - Ub * Qb) * Pb) b)ᴴ) *
    ((Qb * Ub - Ub * Qb) * Pb))).PosSemidef at hh
  rw [liftBlocks_mul, liftBlocks_adjoint, liftBlocks_mul, liftBlocks_sub,
    liftBlocks_mul, liftBlocks_mul, ← hq, ← hp, ← hu] at hh
  exact hh

end oneOracle

/-- A Gram bound on the support of `σ` bounds the weight of `C σ Cᴴ` by `r tr σ`. -/
theorem ofReal_trace_conj_le_of_certificate {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (d : n → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hcert : (r • (1 : Matrix n n ℂ) - (C * diagonal d)ᴴ * (C * diagonal d)).PosSemidef)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (hsupp : MatrixMap.conj (diagonal d) σ = σ) :
    ENNReal.ofReal (MatrixMap.conj C σ).trace.re ≤
      ENNReal.ofReal r * ENNReal.ofReal σ.trace.re := by
  have hc : MatrixMap.conj C σ = MatrixMap.conj (C * diagonal d) σ := by
    rw [MatrixMap.conj_mul, LinearMap.comp_apply, hsupp]
  rw [hc, ← ENNReal.ofReal_mul hr]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := hcert.trace_mul_re_nonneg hσ
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at h
  rw [MatrixMap.trace_conj_apply]
  linarith

/-! ## Upward-closed events and fresh-cell bounds -/

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- `S` is upward closed: filling an empty cell of any of the three databases of a triple in `S`
gives a triple in `S`. -/
structure UpClosed (S : Set (Dbs X Z)) : Prop where
  /-- Filling a cell of `D.h`. -/
  h : ∀ D ∈ S, ∀ z u, D.h z = none → ({ D with h := Function.update D.h z (some u) } : Dbs X Z) ∈ S
  /-- Filling a cell of `D.k`. -/
  k : ∀ D ∈ S, ∀ x u, D.k x = none → ({ D with k := Function.update D.k x (some u) } : Dbs X Z) ∈ S
  /-- Filling a cell of `D.k'`. -/
  k' : ∀ D ∈ S, ∀ x u, D.k' x = none →
    ({ D with k' := Function.update D.k' x (some u) } : Dbs X Z) ∈ S

/-- `FreshBound S t ε`: for every triple `D ∉ S` whose three databases have fewer than `t`
entries, and every empty cell of one of them, at most a fraction `ε` of the answers put the filled
triple in `S`. -/
structure FreshBound (S : Set (Dbs X Z)) [DecidablePred (· ∈ S)] (t : ℕ) (ε : ℝ≥0∞) : Prop where
  /-- Filling a cell of `D.h` with a uniform `u : X`. -/
  h : ∀ D ∉ S, D.h.size < t → D.k.size < t → D.k'.size < t → ∀ z, D.h z = none →
    ((Finset.univ.filter fun u : X ↦
        ({ D with h := Function.update D.h z (some u) } : Dbs X Z) ∈ S).card : ℝ≥0∞) /
      Fintype.card X ≤ ε
  /-- Filling a cell of `D.k` with a uniform `u : Z`. -/
  k : ∀ D ∉ S, D.h.size < t → D.k.size < t → D.k'.size < t → ∀ x, D.k x = none →
    ((Finset.univ.filter fun u : Z ↦
        ({ D with k := Function.update D.k x (some u) } : Dbs X Z) ∈ S).card : ℝ≥0∞) /
      Fintype.card Z ≤ ε
  /-- Filling a cell of `D.k'` with a uniform `u : Z`. -/
  k' : ∀ D ∉ S, D.h.size < t → D.k.size < t → D.k'.size < t → ∀ x, D.k' x = none →
    ((Finset.univ.filter fun u : Z ↦
        ({ D with k' := Function.update D.k' x (some u) } : Dbs X Z) ∈ S).card : ℝ≥0∞) /
      Fintype.card Z ≤ ε

/-- A fresh-cell bound for databases below `t` holds below any `t' ≤ t`. -/
theorem FreshBound.mono {S : Set (Dbs X Z)} [DecidablePred (· ∈ S)] {t t' : ℕ} {ε : ℝ≥0∞}
    (h : FreshBound S t ε) (ht : t' ≤ t) : FreshBound S t' ε where
  h D hD h₁ h₂ h₃ := h.h D hD (h₁.trans_le ht) (h₂.trans_le ht) (h₃.trans_le ht)
  k D hD h₁ h₂ h₃ := h.k D hD (h₁.trans_le ht) (h₂.trans_le ht) (h₃.trans_le ht)
  k' D hD h₁ h₂ h₃ := h.k' D hD (h₁.trans_le ht) (h₂.trans_le ht) (h₃.trans_le ht)

/-- The projector of the database register onto the triples in `S`; its weight on the final state
of a run is the probability that measuring the three databases gives a triple in `S`. -/
noncomputable def dbsProjector (S : Set (Dbs X Z)) [DecidablePred (· ∈ S)] :
    Matrix (DbReg X Z) (DbReg X Z) ℂ :=
  labelProjector (fun D : DbReg X Z ↦ decide (D.toDbs ∈ S)) true

/-- The grade of a triple: the largest number of entries of its databases. -/
def dbGrade (D : DbReg X Z) : ℕ :=
  max D.1.size (max D.2.1.size D.2.2.size)

/-! ## The event bound -/

variable [AddCommGroup X] [AddCommGroup Z]

/-- Every port raises the grade by at most one. -/
theorem dbGrade_le_of_spongeCompressed_U_ne_zero (i : SpongePort) (a a' : spongeIn X Z i)
    (d d' : DbReg X Z) (h : (spongeCompressed X Z).U i (a', d') (a, d) ≠ 0) :
    dbGrade d' ≤ dbGrade d + 1 := by
  obtain ⟨dh, dk, dk'⟩ := d
  obtain ⟨dh₂, dk₂, dk₂'⟩ := d'
  cases i
  · change onFactor (splitH (Z × X)) (compressedOracle Z X) (a', (dh₂, dk₂, dk₂'))
      (a, (dh, dk, dk')) ≠ 0 at h
    rw [onFactor_apply] at h
    split_ifs at h with hr
    swap
    · exact absurd rfl h
    have hs := size_le_of_compressedOracle_apply_ne_zero h
    simp only [splitH, Equiv.prodAssoc_symm_apply, Prod.mk.injEq] at hr hs
    obtain ⟨rfl, rfl⟩ := hr
    simp only [dbGrade]
    omega
  · change onFactor (splitK (X × Z)) (compressedOracle X Z) (a', (dh₂, dk₂, dk₂'))
      (a, (dh, dk, dk')) ≠ 0 at h
    rw [onFactor_apply] at h
    split_ifs at h with hr
    swap
    · exact absurd rfl h
    have hs := size_le_of_compressedOracle_apply_ne_zero h
    simp only [splitK, Equiv.coe_fn_mk, Prod.mk.injEq] at hr hs
    obtain ⟨rfl, rfl⟩ := hr
    simp only [dbGrade]
    omega
  · change onFactor (splitK' (X × Z)) (compressedOracle X Z) (a', (dh₂, dk₂, dk₂'))
      (a, (dh, dk, dk')) ≠ 0 at h
    rw [onFactor_apply] at h
    split_ifs at h with hr
    swap
    · exact absurd rfl h
    have hs := size_le_of_compressedOracle_apply_ne_zero h
    simp only [splitK', Equiv.coe_fn_mk, Prod.mk.injEq] at hr hs
    obtain ⟨rfl, rfl⟩ := hr
    simp only [dbGrade]
    omega

/-- The per-port certificate at the `n`-th call, with rate `6 ε`. -/
theorem posSemidef_spongeCompressed_certificate (S : Set (Dbs X Z)) [DecidablePred (· ∈ S)]
    (hup : UpClosed S) {n : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤) (hε : FreshBound S (n + 1) ε)
    (i : SpongePort) :
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
      (instability_le_of_fresh _ _ _ (fun d hd z u hz ↦ ?_) fun d hd hsize z hz ↦ ?_))
      (by norm_num)
    · simp only [decide_eq_true_eq] at hd ⊢
      exact hup.h _ hd z u hz
    · simp only [decide_eq_true_eq]
      exact hε.h ⟨d, b.1, b.2⟩ (fun h ↦ by simp [DbReg.toDbs, h] at hd) hsize (Nat.lt_succ_of_le hb.1)
        (Nat.lt_succ_of_le hb.2) z hz
  · let _ : UniformAnswerMeasure (X →ₒ Z) := UniformAnswerMeasure.ofFiniteNonempty _
    refine posSemidef_port_certificate (splitK (X × Z)) (fun d b ↦ (b.1, d, b.2))
      (fun _ _ _ ↦ rfl) (fun D : DbReg X Z ↦ decide (D.toDbs ∈ S)) dbGrade
      (fun b ↦ b.1.size ≤ n ∧ b.2.size ≤ n) n
      (fun d b ↦ by simp only [dbGrade, max_le_iff]; tauto) hr0 fun b hb ↦ ?_
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hεtop
      (instability_le_of_fresh _ _ _ (fun d hd x u hx ↦ ?_) fun d hd hsize x hx ↦ ?_))
      (by norm_num)
    · simp only [decide_eq_true_eq] at hd ⊢
      exact hup.k _ hd x u hx
    · simp only [decide_eq_true_eq]
      exact hε.k ⟨b.1, d, b.2⟩ (fun h ↦ by simp [DbReg.toDbs, h] at hd) (Nat.lt_succ_of_le hb.1) hsize
        (Nat.lt_succ_of_le hb.2) x hx
  · let _ : UniformAnswerMeasure (X →ₒ Z) := UniformAnswerMeasure.ofFiniteNonempty _
    refine posSemidef_port_certificate (splitK' (X × Z)) (fun d b ↦ (b.1, b.2, d))
      (fun _ _ _ ↦ rfl) (fun D : DbReg X Z ↦ decide (D.toDbs ∈ S)) dbGrade
      (fun b ↦ b.1.size ≤ n ∧ b.2.size ≤ n) n
      (fun d b ↦ by simp only [dbGrade, max_le_iff]; tauto) hr0 fun b hb ↦ ?_
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hεtop
      (instability_le_of_fresh _ _ _ (fun d hd x u hx ↦ ?_) fun d hd hsize x hx ↦ ?_))
      (by norm_num)
    · simp only [decide_eq_true_eq] at hd ⊢
      exact hup.k' _ hd x u hx
    · simp only [decide_eq_true_eq]
      exact hε.k' ⟨b.1, b.2, d⟩ (fun h ↦ by simp [DbReg.toDbs, h] at hd) (Nat.lt_succ_of_le hb.1)
        (Nat.lt_succ_of_le hb.2) hsize x hx

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **The event bound, per call.** For an upward-closed set `S` of database triples without the
empty triple, and a program over `spongeSpec X Z` making at most `T` calls in total, if at the
`n`-th call (`n < T`) a fresh cell enters `S` with probability at most `ε n`
(`FreshBound S (n + 1) (ε n)`), the weight of the final database register on `S` satisfies
`√w ≤ ∑_{n < T} √(6 ε n)`. -/
theorem rpow_inv_two_eventWeight_spongeCompressedRuntime_le (S : Set (Dbs X Z))
    [DecidablePred (· ∈ S)] (hup : UpClosed S)
    (hempty : (⟨Database.empty, Database.empty, Database.empty⟩ : Dbs X Z) ∉ S) {T : ℕ}
    (ε : ℕ → ℝ≥0∞) (hε : ∀ n < T, FreshBound S (n + 1) (ε n)) (I : L.Interp)
    (x : QuantumComp L (spongeSpec X Z) W A) (hx : x.IsTotalQueryBound T) (ρ : SubState A) :
    (spongeCompressedRuntime X Z).eventWeight I (dbsProjector S) x
        (ρ.matrix ⊗ₖ (spongeCompressedRuntime X Z).init.matrix) ^ (2⁻¹ : ℝ) ≤
      ∑ n ∈ Finset.range T, (6 * ε n) ^ (2⁻¹ : ℝ) := by
  have hq := isStarProjection_labelProjector (α := ℂ)
    (fun D : DbReg X Z ↦ decide (D.toDbs ∈ S)) true
  have hρ0 : (ρ.matrix ⊗ₖ (spongeCompressed X Z).init.matrix).PosSemidef :=
    (ρ.prod (spongeCompressed X Z).init).posSemidef
  have hzero : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ dbsProjector S)
      (ρ.matrix ⊗ₖ (SubState.basis ((Database.empty : Database Z X),
        (Database.empty : Database X Z), (Database.empty : Database X Z))).matrix) = 0 := by
    have hz : dbsProjector S * (SubState.basis ((Database.empty : Database Z X),
        (Database.empty : Database X Z), (Database.empty : Database X Z))).matrix = 0 := by
      rw [dbsProjector, labelProjector, SubState.matrix_basis]
      ext a b
      rw [diagonal_mul, Matrix.single_apply]
      by_cases h : ((Database.empty : Database Z X), (Database.empty : Database X Z),
          (Database.empty : Database X Z)) = a ∧ ((Database.empty : Database Z X),
          (Database.empty : Database X Z), (Database.empty : Database X Z)) = b
      · rcases h with ⟨rfl, rfl⟩
        simp [DbReg.toDbs, hempty]
      · simp [h]
    rw [MatrixMap.conj_apply, ← mul_kronecker_mul, hz, kronecker_zero, Matrix.zero_mul]
  have hgrade : QuerySupportedOn (fun m : A × DbReg X Z ↦ dbGrade m.2) (Set.Iic 0)
      (ρ.matrix ⊗ₖ (SubState.basis ((Database.empty : Database Z X),
        (Database.empty : Database X Z), (Database.empty : Database X Z))).matrix) := by
    intro m m' hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
    · exact False.elim (h rfl)
  have hhyb := QuantumRuntime.rpow_inv_two_eventWeight_le_commutators I
    (spongeCompressed X Z).toRuntime_step_branch (Q := dbsProjector S) (by exact hq.isSelfAdjoint)
    (by exact hq.isIdempotentElem) (spongeCompressed X Z).init x hρ0 (by exact hzero)
  refine hhyb.trans ?_
  rw [tsum_eq_sum (s := Finset.range T) fun j hj ↦ by
    rw [QuantumRuntime.queryWeight_eq_zero_of_isTotalQueryBound _ I hx (by simpa using hj),
      ENNReal.zero_rpow_of_pos (by norm_num)]]
  refine Finset.sum_le_sum fun j hj ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hjT := Finset.mem_range.mp hj
  by_cases htop : ε j = ⊤
  · rw [htop, ENNReal.mul_top (by norm_num)]
    exact le_top
  have hr0 : (0 : ℝ) ≤ 6 * (ε j).toReal := by positivity
  refine (QuantumRuntime.queryWeight_mono_of_grade _ I dbGrade
    (w' := fun _ σ ↦ ENNReal.ofReal (6 * (ε j).toReal) * ENNReal.ofReal σ.trace.re)
    (by
      exact (spongeCompressed X Z).querySupportedOn_toRuntime_step dbGrade
        dbGrade_le_of_spongeCompressed_U_ne_zero)
    x hρ0 0 j (by exact hgrade) fun i σ hσ hsupp ↦ ?_).trans ?_
  · rw [QuantumRuntime.krausWeight, tsum_fintype, Fintype.sum_unique]
    refine ofReal_trace_conj_le_of_certificate _ _ hr0
      (by exact posSemidef_spongeCompressed_certificate S hup htop (hε j hjT) i) hσ ?_
    refine hsupp.conj_diagonal_eq_self fun m hm ↦ ?_
    rw [zero_add] at hm
    simp [Set.mem_Iic.mp hm]
  · rw [QuantumRuntime.queryWeight_const_mul]
    calc ENNReal.ofReal (6 * (ε j).toReal) * _
        ≤ ENNReal.ofReal (6 * (ε j).toReal) *
            ENNReal.ofReal (ρ.matrix ⊗ₖ (spongeCompressed X Z).init.matrix).trace.re := by
          gcongr
          exact QuantumRuntime.queryWeight_le_ofReal_trace _ I (fun _ _ _ ↦ le_rfl) x hρ0 j
      _ ≤ ENNReal.ofReal (6 * (ε j).toReal) * 1 := by
          gcongr
          rw [← SubState.matrix_prod]
          exact ENNReal.ofReal_le_one.mpr (ρ.prod (spongeCompressed X Z).init).trace_re_le_one
      _ = 6 * ε j := by
          rw [mul_one, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal htop]
          norm_num

/-- **The event bound.** For an upward-closed set `S` of database triples without the empty
triple, and a program over `spongeSpec X Z` making at most `T` calls in total, if filling a fresh
cell of a triple outside `S` with databases below `T` entries enters `S` with probability at most
`ε`, the final database register lies in `S` with weight at most `6 T² ε`. -/
theorem eventWeight_spongeCompressedRuntime_le (S : Set (Dbs X Z)) [DecidablePred (· ∈ S)]
    (hup : UpClosed S)
    (hempty : (⟨Database.empty, Database.empty, Database.empty⟩ : Dbs X Z) ∉ S) {T : ℕ}
    {ε : ℝ≥0∞} (hε : FreshBound S T ε) (I : L.Interp)
    (x : QuantumComp L (spongeSpec X Z) W A) (hx : x.IsTotalQueryBound T) (ρ : SubState A) :
    (spongeCompressedRuntime X Z).eventWeight I (dbsProjector S) x
        (ρ.matrix ⊗ₖ (spongeCompressedRuntime X Z).init.matrix) ≤ 6 * T ^ 2 * ε := by
  have h := rpow_inv_two_eventWeight_spongeCompressedRuntime_le S hup hempty (fun _ ↦ ε)
    (fun n hn ↦ hε.mono (Nat.succ_le_of_lt hn)) I x hx ρ
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  rw [rpow_inv_two_rpow_two, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    rpow_inv_two_rpow_two, ENNReal.rpow_two] at h2
  calc _ ≤ (T : ℝ≥0∞) ^ 2 * (6 * ε) := h2
    _ = 6 * T ^ 2 * ε := by ring

end Quantum.Sponge

end
