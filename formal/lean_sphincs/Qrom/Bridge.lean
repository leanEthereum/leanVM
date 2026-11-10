module

public import VCVio.Quantum.Oracle.Compressed.Equivalence

@[expose] public section

/-!
# Observations of the random function, read on the compressed database

In the quantum random-oracle model the challenger may check a relation between the program's
output and the hidden function `H`. For a weight `c : (X → Y) → ℂ` on the functions, the
`c`-weighted sum over `H` of the weights of a leaf `p` against the oracle unitaries of `H` is the
trace of the compressed joint post-state at `p` against the operator `1 ⊗ K diag(c) Kᴴ` on the
database register, where `K = S^{⊗X} E` compresses every cell after tabulating a function
(`Qrom.sum_mul_trace_jointPost_additive_eq`). The proof goes through the purified runtime, whose
private register holds the function: reading it at `H` gives the run against `H`
(`Qrom.smul_matrix_jointPost_additive`), and `K` carries the purified run to the compressed one.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The isometry from the function register to the database register: tabulate, then compress
every cell. -/
noncomputable abbrev tabCompress (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] : Matrix (Database X Y) (X → Y) ℂ :=
  compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y)

/-- Reading the purified joint post-state at `H` gives, up to the weight `|Y|^(-|X|)`, the joint
post-state against the oracle unitary of `H`. -/
theorem smul_matrix_jointPost_additive (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (p : Σ u, W u) (H : X → Y) :
    ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X) •
        ((additiveOracleRuntime H).jointPost I x ρ p).matrix =
      (MatrixMap.conj (evalRow H)).amplifyLeft p.1
        ((purifiedRuntime X Y).jointPost I x ρ p).matrix := by
  have hsim := QuantumRuntime.simulation (R₁ := purifiedRuntime X Y)
    (R₂ := additiveOracleRuntime H) (V := MatrixMap.conj (evalRow H)) I (fun i r ↦ by
      change (MatrixMap.conj (oracleUnitary H)).amplify Unit ∘ₗ
          (MatrixMap.conj (evalRow H)).amplifyLeft (X × Y) =
        (MatrixMap.conj (evalRow H)).amplifyLeft (X × Y) ∘ₗ
          MatrixMap.conj (tableOracle (id : (X → Y) → X → Y))
      rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
        ← MatrixMap.conj_mul, oracleUnitary_kronecker_one_mul_one_kronecker_evalRow]) x p
  have h' := LinearMap.congr_fun hsim (ρ.matrix ⊗ₖ (purifiedRuntime X Y).init.matrix)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, MatrixMap.amplifyLeft_kronecker] at h'
  rw [QuantumRuntime.matrix_jointPost, QuantumRuntime.matrix_jointPost]
  refine Eq.trans ?_ h'
  rw [← map_smul]
  refine congrArg (((additiveOracleRuntime H).run I x).branch p) ?_
  have hk : ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X) •
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix : Matrix (A × Unit) (A × Unit) ℂ) =
      ρ.matrix ⊗ₖ MatrixMap.conj (evalRow H) (uniformFunctionState X Y).matrix := by
    rw [conj_evalRow_uniformFunctionState, kronecker_smul]
  exact hk

/-- The compressed joint post-state is the purified one carried by `K`. -/
theorem matrix_jointPost_compressed_eq (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (p : Σ u, W u) :
    ((compressedRuntime X Y).jointPost I x ρ p).matrix =
      MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ tabCompress X Y)
        ((purifiedRuntime X Y).jointPost I x ρ p).matrix := by
  rw [← MatrixMap.amplifyLeft_conj]
  refine QuantumRuntime.matrix_jointPost_of_simulation (R₁ := purifiedRuntime X Y)
    (R₂ := compressedRuntime X Y) (V := MatrixMap.conj (tabCompress X Y)) I (fun i r ↦ ?_)
    conj_compressAll_mul_basisMatrix_uniformFunctionState x ρ p
  change MatrixMap.conj (compressedOracle X Y) ∘ₗ
      (MatrixMap.conj (compressAll X Y * basisMatrix Database.ofFun)).amplifyLeft (X × Y) =
    (MatrixMap.conj (compressAll X Y * basisMatrix Database.ofFun)).amplifyLeft (X × Y) ∘ₗ
      MatrixMap.conj (tableOracle (id : (X → Y) → X → Y))
  rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
    compressedOracle_mul_one_kronecker_compressAll_mul_basisMatrix]

/-- The diagonal blocks of the function register, weighted by `c`, give the trace against
`1 ⊗ diag(c)`. -/
theorem sum_mul_trace_amplifyLeft_conj_evalRow {B : Type*} [Fintype B] [DecidableEq B]
    (c : (X → Y) → ℂ) (M : Matrix (B × (X → Y)) (B × (X → Y)) ℂ) :
    ∑ H : X → Y, c H * ((MatrixMap.conj (evalRow H)).amplifyLeft B M).trace =
      (((1 : Matrix B B ℂ) ⊗ₖ diagonal c) * M).trace := by
  simp only [trace_amplifyLeft_conj_evalRow, Finset.mul_sum]
  rw [Finset.sum_comm, Matrix.trace, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun H _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single b (fun b' _ hb' ↦ by simp [Ne.symm hb'])
      (by simp), Finset.sum_eq_single H (fun H' _ hH' ↦ by simp [Ne.symm hH']) (by simp)]
  simp

/-- An isometry moves an observable of its input register to its output register. -/
theorem trace_one_kronecker_mul_conj {B S T : Type*} [Fintype B] [DecidableEq B] [Fintype S]
    [DecidableEq S] [Fintype T] (K : Matrix T S ℂ) (hK : Kᴴ * K = 1) (C : Matrix S S ℂ)
    (M : Matrix (B × S) (B × S) ℂ) :
    (((1 : Matrix B B ℂ) ⊗ₖ (K * C * Kᴴ)) *
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ K) M).trace =
      (((1 : Matrix B B ℂ) ⊗ₖ C) * M).trace := by
  have h : ((1 : Matrix B B ℂ) ⊗ₖ K)ᴴ * ((1 : Matrix B B ℂ) ⊗ₖ (K * C * Kᴴ)) *
      ((1 : Matrix B B ℂ) ⊗ₖ K) = (1 : Matrix B B ℂ) ⊗ₖ C := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
      Matrix.one_mul, Matrix.one_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hK, Matrix.one_mul, Matrix.mul_assoc, hK,
      Matrix.mul_one]
  rw [MatrixMap.conj_apply, ← h]
  calc _ = (((1 : Matrix B B ℂ) ⊗ₖ (K * C * Kᴴ)) * (((1 : Matrix B B ℂ) ⊗ₖ K) * M) *
        ((1 : Matrix B B ℂ) ⊗ₖ K)ᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = (((1 : Matrix B B ℂ) ⊗ₖ K)ᴴ * (((1 : Matrix B B ℂ) ⊗ₖ (K * C * Kᴴ)) *
        (((1 : Matrix B B ℂ) ⊗ₖ K) * M))).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **The bridge.** The `c`-weighted average over `H` of the weights of a leaf against the
oracle unitaries of `H` is the trace of the compressed joint post-state against
`1 ⊗ K diag(c) Kᴴ`. -/
theorem sum_mul_trace_jointPost_additive_eq (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (p : Σ u, W u) (c : (X → Y) → ℂ) :
    ∑ H : X → Y, c H * ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X *
        ((additiveOracleRuntime H).jointPost I x ρ p).matrix.trace) =
      (((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (tabCompress X Y * diagonal c * (tabCompress X Y)ᴴ)) *
        ((compressedRuntime X Y).jointPost I x ρ p).matrix).trace := by
  rw [matrix_jointPost_compressed_eq]
  refine Eq.trans ?_ (trace_one_kronecker_mul_conj (tabCompress X Y)
    conjTranspose_compressAll_mul_basisMatrix_mul_self _ _).symm
  refine Eq.trans ?_ (sum_mul_trace_amplifyLeft_conj_evalRow c _)
  refine Finset.sum_congr rfl fun H _ ↦ ?_
  rw [← smul_matrix_jointPost_additive]
  congr 1
  rw [← smul_eq_mul, ← Matrix.trace_smul]
  rfl

end Qrom
