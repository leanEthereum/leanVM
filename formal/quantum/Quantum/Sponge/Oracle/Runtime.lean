module

public import Quantum.Sponge.Spec
public import Quantum.Sponge.Database
public import VCVio.Quantum.VC.Compressed

@[expose] public section

/-!
# Three compressed oracles for the sponge's random functions

The private register `DbReg X Z` holds the databases of `h : Z → X`, `k : X → Z` and
`k' : X → Z`, all started empty; each port of `spongeSpec` applies VCVio's compressed oracle
(`Quantum.compressedOracle`) to its query register and its own database, and the identity to the
other two (`spongeCompressed`, `spongeCompressedRuntime`).

**Exactness** (`evalDistMap_spongeCompressedRuntime`): every program, observed through any
function of its leaf, has the same law against `spongeCompressedRuntime` as in the experiment
`spongeEvalDistMap` with uniform `(h, k, k')`. The proof follows VCVio's one-function proof
(`Quantum.outcomeLawWith_compressedRuntime`). Tabulating the three functions and compressing every
cell, `M = S^{⊗} E`, is an isometry from the register of function triples, started in the uniform
superposition (`spongePurified`), to the database register; it intertwines the ports, since every
port is the table oracle of its database conjugated by the compression of all three databases
(`onFactor_compressedOracle_eq_conj`). Reading the function register at a triple `t` intertwines
the purified oracle with the oracles of `t`, and these rows resolve the identity.
-/

open MeasureTheory Matrix
open scoped Kronecker ENNReal NNReal

universe u v w

namespace Quantum.Sponge

open Quantum

/-! ## The database register -/

/-- The register of the three databases: `D.h`, `D.k`, `D.k'`, in that order. -/
abbrev DbReg (X Z : Type) := Database Z X × Database X Z × Database X Z

/-- The databases held by a basis state of the register. -/
def DbReg.toDbs {X Z : Type} (D : DbReg X Z) : Dbs X Z :=
  ⟨D.1, D.2.1, D.2.2⟩

/-- The register split for port `h`: its query register with `D.h`, then `(D.k, D.k')`. -/
def splitH (M : Type) {X Z : Type} :
    M × DbReg X Z ≃ (M × Database Z X) × (Database X Z × Database X Z) :=
  (Equiv.prodAssoc M _ _).symm

/-- The register split for port `k`: its query register with `D.k`, then `(D.h, D.k')`. -/
def splitK (M : Type) {X Z : Type} :
    M × DbReg X Z ≃ (M × Database X Z) × (Database Z X × Database X Z) where
  toFun p := ((p.1, p.2.2.1), (p.2.1, p.2.2.2))
  invFun p := (p.1.1, (p.2.1, p.1.2, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The register split for port `k'`: its query register with `D.k'`, then `(D.h, D.k)`. -/
def splitK' (M : Type) {X Z : Type} :
    M × DbReg X Z ≃ (M × Database X Z) × (Database Z X × Database X Z) where
  toFun p := ((p.1, p.2.2.2), (p.2.1, p.2.2.1))
  invFun p := (p.1.1, (p.2.1, p.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Table oracles conjugated by compression -/

section conjForm

variable {A Y T T' : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype T] [DecidableEq T] [Fintype T'] [DecidableEq T']

/-- **A compressed oracle on one factor is a conjugated table oracle.** If the compression of the
factor's database is `Cp` on the register, the standard oracle on the factor is the table oracle
of `read`, and `R` is an involution commuting with that table oracle with `C = Cp R = R Cp`, then
the compressed oracle on the factor is the table oracle conjugated by `C`. -/
theorem onFactor_compressedOracle_eq_conj {B : Type} [Fintype B] [DecidableEq B]
    (e : (A × Y) × T ≃ ((A × Y) × Database A Y) × B) (read : T → A → Y) (Cp R C : Matrix T T ℂ)
    (hC : onFactor e ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressAll A Y) =
      (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ Cp)
    (hS : onFactor e (standardOracle A Y) = tableOracle read) (hRR : R * R = 1)
    (hRT : tableOracle read * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ R) =
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ R) * tableOracle read)
    (h₁ : C = Cp * R) (h₂ : C = R * Cp) :
    onFactor e (compressedOracle A Y) =
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) * tableOracle read *
        ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) := by
  have hk (M N : Matrix T T ℂ) : ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ M) *
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ N) = (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (M * N) := by
    rw [← mul_kronecker_mul, Matrix.one_mul]
  rw [compressedOracle, onFactor_mul, onFactor_mul, hC, hS]
  calc ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ Cp) * tableOracle read *
        ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ Cp)
      = ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ Cp) * tableOracle read *
          (((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ R) * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ R)) *
          ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ Cp) := by
        rw [hk, hRR, one_kronecker_one, Matrix.mul_one]
    _ = ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ Cp) * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ R) *
          tableOracle read *
          (((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ R) * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ Cp)) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (tableOracle read), hRT, Matrix.mul_assoc]
    _ = _ := by rw [hk, hk, ← h₁, ← h₂]

/-- A conjugated table oracle, intertwined with tabulating along `f` and compressing with `C`. -/
theorem conj_tableOracle_mul_one_kronecker (read : T → A → Y) (read' : T' → A → Y)
    (C : Matrix T T ℂ) (hCC : C * C = 1) (f : T' → T) (hf : ∀ t, read (f t) = read' t) :
    ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) * tableOracle read *
        ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) *
        ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (C * basisMatrix f)) =
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (C * basisMatrix f)) * tableOracle read' := by
  have hk (M : Matrix T T ℂ) (N : Matrix T T' ℂ) : ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ M) *
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ N) = (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (M * N) := by
    rw [← mul_kronecker_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc _ ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C), hk, ← Matrix.mul_assoc C, hCC,
    Matrix.one_mul, Matrix.mul_assoc, tableOracle_mul_one_kronecker_basisMatrix hf,
    ← Matrix.mul_assoc, hk]

end conjForm

/-! ## Rows of a register -/

section rows

variable {T : Type} [Fintype T] [DecidableEq T]

/-- Reading a register at `t`: the row `⟨t|`. -/
def rowAt (t : T) : Matrix Unit T ℂ :=
  Matrix.of fun _ t' ↦ if t' = t then 1 else 0

/-- The rows `⟨t|` resolve the identity. -/
theorem sum_conjTranspose_rowAt_mul_self : ∑ t : T, (rowAt t)ᴴ * rowAt t = 1 := by
  ext t' t''
  simp [Matrix.sum_apply, Matrix.mul_apply, rowAt, Matrix.one_apply, eq_comm]

/-- Reading an operator at `t` leaves its diagonal entry at `t`. -/
theorem conj_rowAt (t : T) (ρ : Matrix T T ℂ) :
    MatrixMap.conj (rowAt t) ρ = Matrix.of fun _ _ ↦ ρ t t := by
  ext ⟨⟩ ⟨⟩
  simp [MatrixMap.conj_apply, Matrix.mul_apply, rowAt, conjTranspose_apply]

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Reading the table register at `t` intertwines the table oracle of `read` with the oracle
unitary of `read t`. -/
theorem oracleUnitary_kronecker_one_mul_one_kronecker_rowAt (read : T → A → Y) (t : T) :
    (oracleUnitary (read t) ⊗ₖ (1 : Matrix Unit Unit ℂ)) *
        ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ rowAt t) =
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ rowAt t) * tableOracle read := by
  ext ⟨m, u⟩ ⟨m', t'⟩
  by_cases ht : t' = t
  · subst ht
    simp only [rowAt, Matrix.mul_apply, kroneckerMap_apply, oracleUnitary_apply,
      one_apply_eq, mul_one, Matrix.one_apply, of_apply, ↓reduceIte, mul_ite, mul_zero,
      Fintype.sum_prod_type, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, tableOracle_apply,
      tableOracleEquiv_apply, oracleEquiv_apply, ite_mul, one_mul, zero_mul, Prod.mk.injEq,
      and_true, Finset.sum_ite_eq]
    split_ifs <;> simp_all
  · simp [Matrix.mul_apply, Fintype.sum_prod_type, rowAt, oracleUnitary_apply,
      tableOracle_apply, Matrix.one_apply, ht, Ne.symm ht]

end rows

/-- `(A ⊗ B) (ρ ⊗ σ) (A ⊗ B)ᴴ = (A ρ Aᴴ) ⊗ (B σ Bᴴ)`. -/
theorem conj_kronecker_kronecker {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p]
    [Fintype q] (K : Matrix m n ℂ) (K' : Matrix p q ℂ) (ρ : Matrix n n ℂ) (σ : Matrix q q ℂ) :
    MatrixMap.conj (K ⊗ₖ K') (ρ ⊗ₖ σ) = MatrixMap.conj K ρ ⊗ₖ MatrixMap.conj K' σ := by
  simp only [MatrixMap.conj_apply, conjTranspose_kronecker, ← mul_kronecker_mul]

/-- The trace-weighted mixture form of a family of row intertwiners: if rows `M ω` resolve the
identity, intertwine the steps of `E` with those of `F ω`, and send the initial substate of `E`
to `c ω` times that of `F ω`, then every observed law against `E` is the `c`-mixture of the laws
against the `F ω`. -/
theorem evalDistMap_eq_sum_of_rows {spec : QuantumOracleSpec.{0, 0}}
    {Ω : Type*} [Fintype Ω] (E : QuantumRuntime spec)
    (F : Ω → QuantumRuntime spec) (M : ∀ ω, Matrix (F ω).D E.D ℂ) (c : Ω → ℝ≥0)
    (hM : ∑ ω, (M ω)ᴴ * M ω = 1)
    (hstep : ∀ ω i r, ((F ω).step i).branch r ∘ₗ
        (MatrixMap.conj (M ω)).amplifyLeft (spec.In i) =
      (MatrixMap.conj (M ω)).amplifyLeft (spec.Out i) ∘ₗ (E.step i).branch r)
    (hinit : ∀ ω, MatrixMap.conj (M ω) E.init.matrix =
      ((c ω : ℝ) : ℂ) • (F ω).init.matrix)
    {L : LocalSig.{u, v}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L spec W A) (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, W u) → γ) :
    E.evalDistMap I x ρ f = ∑ ω, (c ω : ℝ≥0∞) • (F ω).evalDistMap I x ρ f := by
  have htr (p : Σ u, W u) : (E.jointPost I x ρ p).matrix.trace =
      ∑ ω, ((c ω : ℝ) : ℂ) * ((F ω).jointPost I x ρ p).matrix.trace := by
    rw [← EmulatedOracle.sum_trace_amplifyLeft_conj M hM]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    have hsim := QuantumRuntime.simulation (R₁ := E) (R₂ := (F ω))
      (V := MatrixMap.conj (M ω)) I (hstep ω) x p
    have h' := LinearMap.congr_fun hsim (ρ.matrix ⊗ₖ E.init.matrix)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, MatrixMap.amplifyLeft_kronecker, hinit,
      kronecker_smul, map_smul] at h'
    rw [QuantumRuntime.matrix_jointPost, QuantumRuntime.matrix_jointPost, ← h', Matrix.trace_smul,
      smul_eq_mul]
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply, QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs]
  simp only [Measure.smul_apply, smul_eq_mul, QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs,
    htr, Complex.re_sum, Complex.re_ofReal_mul, ← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  refine tsum_congr fun p ↦ ?_
  rw [ENNReal.ofReal_sum_of_nonneg, Finset.sum_mul]
  · refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [ENNReal.ofReal_mul (c ω).coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_assoc]
  · exact fun ω _ ↦ mul_nonneg (c ω).coe_nonneg (SubState.trace_re_nonneg _)

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Decidable equality of the database register, named so that instance search on registers
built from it stays small. -/
instance (priority := high) DbReg.instDecidableEq : DecidableEq (DbReg X Z) :=
  inferInstanceAs (DecidableEq (Database Z X × Database X Z × Database X Z))

/-- The database register is finite. -/
instance (priority := high) DbReg.instFintype : Fintype (DbReg X Z) :=
  inferInstanceAs (Fintype (Database Z X × Database X Z × Database X Z))

/-! ## Compression and tabulation of three databases -/

variable (X Z) in
/-- Compressing every cell of the three databases. -/
noncomputable def compressDbs : Matrix (DbReg X Z) (DbReg X Z) ℂ :=
  compressAll Z X ⊗ₖ (compressAll X Z ⊗ₖ compressAll X Z)

/-- Tabulating three functions as three databases. -/
def ofFunDbs (t : (Z → X) × (X → Z) × (X → Z)) : DbReg X Z :=
  (Database.ofFun t.1, Database.ofFun t.2.1, Database.ofFun t.2.2)

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem ofFunDbs_injective : Function.Injective (ofFunDbs (X := X) (Z := Z)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [ofFunDbs, Prod.mk.injEq] at h
  rw [Database.ofFun_injective h.1, Database.ofFun_injective h.2.1,
    Database.ofFun_injective h.2.2]

theorem conjTranspose_compressDbs : (compressDbs X Z)ᴴ = compressDbs X Z := by
  simp only [compressDbs, conjTranspose_kronecker, conjTranspose_compressAll]

theorem basisMatrix_ofFunDbs :
    basisMatrix (ofFunDbs (X := X) (Z := Z)) = basisMatrix Database.ofFun ⊗ₖ
      (basisMatrix Database.ofFun ⊗ₖ basisMatrix Database.ofFun) := by
  ext ⟨a, b, c⟩ ⟨f, g, g'⟩
  simp only [basisMatrix_apply, kroneckerMap_apply, ofFunDbs, Prod.mk.injEq,
    ite_zero_mul_ite_zero, mul_one]

variable [AddCommGroup X] [AddCommGroup Z]

theorem compressDbs_mul_self : compressDbs X Z * compressDbs X Z = 1 := by
  simp only [compressDbs, ← mul_kronecker_mul, compressAll_mul_self, one_kronecker_one]

/-! ## The runtimes -/

variable (X Z) in
/-- **Three compressed oracles.** The private register holds the databases of `h`, `k`, `k'`,
started empty; port `h` applies the compressed oracle to `|z, x⟩` and `D.h`, ports `k` and `k'`
apply it to `|x, z⟩` and `D.k`, respectively `D.k'`, each with the identity on the other
databases. -/
@[reducible]
noncomputable def spongeCompressed : EmulatedOracle SpongePort (spongeIn X Z) where
  S := QReg.of (DbReg X Z)
  init := SubState.basis (Database.empty, Database.empty, Database.empty)
  U
    | .h => onFactor (splitH (Z × X)) (compressedOracle Z X)
    | .k => onFactor (splitK (X × Z)) (compressedOracle X Z)
    | .k' => onFactor (splitK' (X × Z)) (compressedOracle X Z)
  unitary
    | .h => onFactor_mem_unitaryGroup _ compressedOracle_mem_unitaryGroup
    | .k => onFactor_mem_unitaryGroup _ compressedOracle_mem_unitaryGroup
    | .k' => onFactor_mem_unitaryGroup _ compressedOracle_mem_unitaryGroup

variable (X Z) in
/-- The runtime of the three compressed oracles, for programs over `spongeSpec X Z`. -/
@[reducible]
noncomputable def spongeCompressedRuntime : QuantumRuntime (spongeSpec X Z) :=
  (spongeCompressed X Z).toRuntime

variable (X Z) in
/-- The purified oracle of three functions: the private register holds the triple `(h, k, k')`,
started in the uniform superposition, and each port applies the table oracle of its function. -/
@[reducible]
noncomputable def spongePurified : EmulatedOracle SpongePort (spongeIn X Z) where
  S := QReg.of ((Z → X) × (X → Z) × (X → Z))
  init := (uniformFunctionState Z X).prod
    ((uniformFunctionState X Z).prod (uniformFunctionState X Z))
  U
    | .h => tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.1
    | .k => tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.2.1
    | .k' => tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.2.2
  unitary
    | .h => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)
    | .k => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)
    | .k' => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)

/-! ## The ports as conjugated table oracles -/

theorem spongeCompressed_U_h :
    (spongeCompressed X Z).U .h =
      ((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ compressDbs X Z) *
        tableOracle (fun D : DbReg X Z ↦ D.1.lookup) *
        ((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ compressDbs X Z) := by
  refine onFactor_compressedOracle_eq_conj (splitH (Z × X)) _
    (compressAll Z X ⊗ₖ (1 : Matrix (Database X Z × Database X Z) _ ℂ))
    ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ (compressAll X Z ⊗ₖ compressAll X Z))
    (compressDbs X Z) ?_ ?_ ?_ ?_ ?_ ?_
  · ext ⟨m, dh, r⟩ ⟨m', dh', r'⟩
    by_cases hr : r = r' <;>
      simp [onFactor_apply, splitH, kroneckerMap_apply, Matrix.one_apply, hr]
  · rw [standardOracle, tableOracle, tableOracle, onFactor_basisMatrix]
    congr 1
  · simp only [← mul_kronecker_mul, Matrix.one_mul, compressAll_mul_self, one_kronecker_one]
  · refine tableOracle_mul_one_kronecker_comm _ ?_
    rintro ⟨dh, r⟩ ⟨dh', r'⟩ h
    by_cases hd : dh = dh'
    · subst hd
      rfl
    · exact absurd (by simp [kroneckerMap_apply, hd]) h
  · simp only [compressDbs, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  · simp only [compressDbs, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem spongeCompressed_U_k :
    (spongeCompressed X Z).U .k =
      ((1 : Matrix (X × Z) (X × Z) ℂ) ⊗ₖ compressDbs X Z) *
        tableOracle (fun D : DbReg X Z ↦ D.2.1.lookup) *
        ((1 : Matrix (X × Z) (X × Z) ℂ) ⊗ₖ compressDbs X Z) := by
  refine onFactor_compressedOracle_eq_conj (splitK (X × Z)) _
    ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      (compressAll X Z ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ)))
    (compressAll Z X ⊗ₖ ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ compressAll X Z))
    (compressDbs X Z) ?_ ?_ ?_ ?_ ?_ ?_
  · ext ⟨m, dh, dk, dk'⟩ ⟨m', dh', dk₂, dk₂'⟩
    by_cases h₁ : dh = dh' <;> by_cases h₂ : dk' = dk₂' <;>
      simp [onFactor_apply, splitK, kroneckerMap_apply, Matrix.one_apply, h₁, h₂]
  · rw [standardOracle, tableOracle, tableOracle, onFactor_basisMatrix]
    congr 1
  · simp only [← mul_kronecker_mul, Matrix.one_mul, compressAll_mul_self, one_kronecker_one]
  · refine tableOracle_mul_one_kronecker_comm _ ?_
    rintro ⟨dh, dk, dk'⟩ ⟨dh₂, dk₂, dk₂'⟩ h
    by_cases hd : dk = dk₂
    · subst hd
      rfl
    · exact absurd (by simp [kroneckerMap_apply, hd]) h
  · simp only [compressDbs, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  · simp only [compressDbs, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem spongeCompressed_U_k' :
    (spongeCompressed X Z).U .k' =
      ((1 : Matrix (X × Z) (X × Z) ℂ) ⊗ₖ compressDbs X Z) *
        tableOracle (fun D : DbReg X Z ↦ D.2.2.lookup) *
        ((1 : Matrix (X × Z) (X × Z) ℂ) ⊗ₖ compressDbs X Z) := by
  refine onFactor_compressedOracle_eq_conj (splitK' (X × Z)) _
    ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ compressAll X Z))
    (compressAll Z X ⊗ₖ (compressAll X Z ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ)))
    (compressDbs X Z) ?_ ?_ ?_ ?_ ?_ ?_
  · ext ⟨m, dh, dk, dk'⟩ ⟨m', dh', dk₂, dk₂'⟩
    by_cases h₁ : dh = dh' <;> by_cases h₂ : dk = dk₂ <;>
      simp [onFactor_apply, splitK', kroneckerMap_apply, Matrix.one_apply, h₁, h₂]
  · rw [standardOracle, tableOracle, tableOracle, onFactor_basisMatrix]
    congr 1
  · simp only [← mul_kronecker_mul, Matrix.one_mul, compressAll_mul_self, one_kronecker_one]
  · refine tableOracle_mul_one_kronecker_comm _ ?_
    rintro ⟨dh, dk, dk'⟩ ⟨dh₂, dk₂, dk₂'⟩ h
    by_cases hd : dk' = dk₂'
    · subst hd
      rfl
    · exact absurd (by simp [kroneckerMap_apply, hd]) h
  · simp only [compressDbs, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  · simp only [compressDbs, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-! ## The compressed oracles simulate the purified oracle -/

variable (X Z) in
/-- Tabulating the three functions and compressing every cell, `M = S^{⊗} E`, from the register
of the purified oracle to that of the compressed oracles. -/
noncomputable def tabulateDbs : Matrix (spongeCompressed X Z).S (spongePurified X Z).S ℂ :=
  compressDbs X Z * basisMatrix ofFunDbs

/-- Tabulating and compressing intertwines every port. -/
theorem spongeCompressed_U_mul_one_kronecker (i : SpongePort) :
    (spongeCompressed X Z).U i * (1 ⊗ₖ tabulateDbs X Z) =
      (1 ⊗ₖ tabulateDbs X Z) * (spongePurified X Z).U i := by
  cases i
  · rw [spongeCompressed_U_h]
    exact conj_tableOracle_mul_one_kronecker _ _ _ compressDbs_mul_self _
      fun t ↦ Database.lookup_ofFun t.1
  · rw [spongeCompressed_U_k]
    exact conj_tableOracle_mul_one_kronecker _ _ _ compressDbs_mul_self _
      fun t ↦ Database.lookup_ofFun t.2.1
  · rw [spongeCompressed_U_k']
    exact conj_tableOracle_mul_one_kronecker _ _ _ compressDbs_mul_self _
      fun t ↦ Database.lookup_ofFun t.2.2

/-- Tabulating and compressing is an isometry. -/
theorem conjTranspose_tabulateDbs_mul_self : (tabulateDbs X Z)ᴴ * tabulateDbs X Z = 1 := by
  change (compressDbs X Z * basisMatrix ofFunDbs)ᴴ * (compressDbs X Z * basisMatrix ofFunDbs) =
    (1 : Matrix ((Z → X) × (X → Z) × (X → Z)) ((Z → X) × (X → Z) × (X → Z)) ℂ)
  rw [conjTranspose_mul, conjTranspose_compressDbs, Matrix.mul_assoc,
    ← Matrix.mul_assoc (compressDbs X Z), compressDbs_mul_self, Matrix.one_mul,
    conjTranspose_basisMatrix_mul_self ofFunDbs_injective]

/-- Tabulating and compressing sends the uniform superposition to the empty databases. -/
theorem conj_tabulateDbs_init :
    MatrixMap.conj (tabulateDbs X Z) (spongePurified X Z).init.matrix =
      (spongeCompressed X Z).init.matrix := by
  change MatrixMap.conj (compressDbs X Z * basisMatrix ofFunDbs)
      ((uniformFunctionState Z X).matrix ⊗ₖ
        ((uniformFunctionState X Z).matrix ⊗ₖ (uniformFunctionState X Z).matrix)) =
    (SubState.basis ((Database.empty : Database Z X), (Database.empty : Database X Z),
      (Database.empty : Database X Z))).matrix
  rw [basisMatrix_ofFunDbs, compressDbs, ← mul_kronecker_mul, ← mul_kronecker_mul,
    conj_kronecker_kronecker, conj_kronecker_kronecker,
    conj_compressAll_mul_basisMatrix_uniformFunctionState,
    conj_compressAll_mul_basisMatrix_uniformFunctionState, ← SubState.matrix_prod,
    ← SubState.matrix_prod, SubState.basis_prod_basis, SubState.basis_prod_basis]

/-! ## The purified oracle is the experiment -/

variable (X Z) in
/-- The runtime of the purified oracle, for programs over `spongeSpec X Z`. -/
@[reducible]
noncomputable def spongePurifiedRuntime : QuantumRuntime (spongeSpec X Z) :=
  (spongePurified X Z).toRuntime

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The uniform superposition over functions has diagonal entries `|Y|^(-|X|)`. -/
theorem uniformFunctionState_apply_self {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [Nonempty Y] (H : A → Y) :
    (uniformFunctionState A Y).matrix H H = (Fintype.card Y : ℂ)⁻¹ ^ Fintype.card A := by
  have h := congrFun (congrFun (conj_evalRow_uniformFunctionState H) ()) ()
  rw [show evalRow H = rowAt H from rfl, conj_rowAt, SubState.matrix_basis] at h
  simpa using h

/-- Reading the uniform superposition over triples at `t` leaves the weight `1 / #triples`. -/
theorem conj_rowAt_uniform (t : (Z → X) × (X → Z) × (X → Z)) :
    MatrixMap.conj (rowAt t) ((uniformFunctionState Z X).matrix ⊗ₖ
        ((uniformFunctionState X Z).matrix ⊗ₖ (uniformFunctionState X Z).matrix)) =
      (((Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0)⁻¹ : ℝ) : ℂ) •
        (SubState.basis ()).matrix := by
  rw [conj_rowAt, SubState.matrix_basis]
  ext ⟨⟩ ⟨⟩
  rw [Matrix.smul_apply, single_apply_same, smul_eq_mul, mul_one]
  simp only [of_apply, kroneckerMap_apply, uniformFunctionState_apply_self, Fintype.card_prod,
    Fintype.card_fun]
  push_cast
  ring

/-- The rows of the triples intertwine the purified oracle with the oracles of the triples. -/
theorem spongeFnRuntime_step_intertwine (t : (Z → X) × (X → Z) × (X → Z)) (i : SpongePort)
    (r : Unit) :
    ((spongeFnRuntime t.1 t.2.1 t.2.2).step i).branch r ∘ₗ
        (MatrixMap.conj (rowAt t)).amplifyLeft ((spongeSpec X Z).In i) =
      (MatrixMap.conj (rowAt t)).amplifyLeft ((spongeSpec X Z).Out i) ∘ₗ
        ((spongePurifiedRuntime X Z).step i).branch r := by
  cases i
  · change (MatrixMap.conj (oracleUnitary t.1)).amplify Unit ∘ₗ
        (MatrixMap.conj (rowAt t)).amplifyLeft (Z × X) =
      (MatrixMap.conj (rowAt t)).amplifyLeft (Z × X) ∘ₗ
        MatrixMap.conj (tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.1)
    rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
      ← MatrixMap.conj_mul, oracleUnitary_kronecker_one_mul_one_kronecker_rowAt
        (fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.1)]
  · change (MatrixMap.conj (oracleUnitary t.2.1)).amplify Unit ∘ₗ
        (MatrixMap.conj (rowAt t)).amplifyLeft (X × Z) =
      (MatrixMap.conj (rowAt t)).amplifyLeft (X × Z) ∘ₗ
        MatrixMap.conj (tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.2.1)
    rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
      ← MatrixMap.conj_mul, oracleUnitary_kronecker_one_mul_one_kronecker_rowAt
        (fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.2.1)]
  · change (MatrixMap.conj (oracleUnitary t.2.2)).amplify Unit ∘ₗ
        (MatrixMap.conj (rowAt t)).amplifyLeft (X × Z) =
      (MatrixMap.conj (rowAt t)).amplifyLeft (X × Z) ∘ₗ
        MatrixMap.conj (tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.2.2)
    rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
      ← MatrixMap.conj_mul, oracleUnitary_kronecker_one_mul_one_kronecker_rowAt
        (fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.2.2)]

/-! ## The main theorem -/

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **The three compressed oracles are exactly the experiment.** Every program over
`spongeSpec X Z`, observed through any function of its leaf, has the same law against the three
compressed oracles started empty as against uniform `(h, k, k')`. -/
theorem evalDistMap_spongeCompressedRuntime {γ : Type*} [MeasurableSpace γ] (I : L.Interp)
    (x : QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (spongeCompressedRuntime X Z).evalDistMap I x ρ f = spongeEvalDistMap I x ρ fun _ ↦ f := by
  refine (EmulatedOracle.outcomeLawWith_eq_of_intertwine (spongePurified X Z)
    (spongeCompressed X Z) (tabulateDbs X Z) conjTranspose_tabulateDbs_mul_self
    spongeCompressed_U_mul_one_kronecker conj_tabulateDbs_init I x ρ f).trans ?_
  refine (evalDistMap_eq_sum_of_rows (spongePurifiedRuntime X Z)
    (fun t ↦ spongeFnRuntime t.1 t.2.1 t.2.2) (fun t ↦ rowAt t)
    (fun _ ↦ (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0)⁻¹)
    (by exact sum_conjTranspose_rowAt_mul_self) (fun t i r ↦ by exact spongeFnRuntime_step_intertwine t i r)
    (fun t ↦ by exact conj_rowAt_uniform t) I x ρ f).trans ?_
  rw [spongeEvalDistMap_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [ENNReal.coe_inv (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_natCast]

/-- The law of the leaf against the three compressed oracles is the law of the experiment. -/
theorem evalDist_spongeCompressedRuntime [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A) :
    (spongeCompressedRuntime X Z).evalDist I x ρ = spongeEvalDist I x ρ := by
  rw [← QuantumRuntime.evalDistMap_id, evalDistMap_spongeCompressedRuntime, spongeEvalDistMap_id]

end Quantum.Sponge

end
