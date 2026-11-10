module

public import Qrom.Override
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The bridge for games with overrides

For a game `g : Qrom.OvGame`, the `c`-weighted average over `G` of the weight of a leaf against
`g.sampled G` is the trace of the compressed joint post-state against
`1 ⊗ (1_S ⊗ K diag(c) Kᴴ)` (`Qrom.OvGame.sum_mul_trace_jointPost_sampled_eq`), as for the plain
random oracle (`Qrom.sum_mul_trace_jointPost_additive_eq`). The purified runtime goes between:
reading its function register at `G` gives the sampled run, and `1_S ⊗ K` carries it to the
compressed run. The side ports act on the side state only, so they commute with both maps.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

namespace OvGame

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]
variable (g : OvGame X Y S P Res)
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

omit [Fintype S] in
/-- A table oracle is unitary on both sides. -/
theorem tableOracle_mul_conjTranspose {T : Type} [Fintype T] [DecidableEq T] (read : T → X → Y) :
    tableOracle read * (tableOracle read)ᴴ = 1 :=
  mul_eq_one_comm.mp (conjTranspose_tableOracle_mul_self read)

/-- Reading the function register at `G` intertwines the purified table oracle with the sampled
one. -/
theorem tableOracle_mul_one_kronecker_evalRow (G : X → Y) :
    tableOracle (fun t : S × Unit ↦ g.answer t.1 G) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ evalRow G)) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ evalRow G)) *
        tableOracle (fun t : S × (X → Y) ↦ g.answer t.1 t.2) := by
  set f : S × Unit → S × (X → Y) := fun t ↦ (t.1, G)
  set Ts := tableOracle (fun t : S × Unit ↦ g.answer t.1 G)
  set Tp := tableOracle (fun t : S × (X → Y) ↦ g.answer t.1 t.2)
  set Bf := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ basisMatrix f
  have hE : (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ evalRow G) = Bfᴴ := by
    rw [conjTranspose_kronecker, conjTranspose_one]
    congr 1
    ext ⟨s, u⟩ ⟨s', H⟩
    simp only [kroneckerMap_apply, evalRow, Matrix.one_apply, f, basisMatrix_apply,
      conjTranspose_apply, Matrix.of_apply, Prod.mk.injEq]
    by_cases h1 : s = s' <;> by_cases h2 : H = G <;> simp [h1, h2, eq_comm]
  have hT : Tp * Bf = Bf * Ts := tableOracle_mul_one_kronecker_basisMatrix fun t ↦ rfl
  have hT' : Bfᴴ * Tpᴴ = Tsᴴ * Bfᴴ := by
    rw [← conjTranspose_mul, ← conjTranspose_mul, hT]
  rw [hE]
  calc Ts * Bfᴴ = Ts * (Bfᴴ * (Tpᴴ * Tp)) := by
        rw [conjTranspose_tableOracle_mul_self, Matrix.mul_one]
    _ = Ts * (Tsᴴ * Bfᴴ) * Tp := by
        rw [← Matrix.mul_assoc Bfᴴ, hT', Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = Bfᴴ * Tp := by
        rw [← Matrix.mul_assoc Ts, tableOracle_mul_conjTranspose, Matrix.one_mul]

variable [Nonempty Y]

/-- Tabulating and compressing intertwines the purified table oracle with the compressed oracle
with overrides. -/
theorem compOracle_mul_one_kronecker :
    g.compOracle * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)) *
        tableOracle (fun t : S × (X → Y) ↦ g.answer t.1 t.2) := by
  set A := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compS (S := S) (X := X) (Y := Y)
  set Bm := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ
    basisMatrix (Database.ofFun : (X → Y) → Database X Y))
  have hsplit : (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y) =
      A * Bm := by
    rw [← mul_kronecker_mul, Matrix.one_mul, compS, ← mul_kronecker_mul, Matrix.one_mul]
  have hB : Bm = (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
      basisMatrix (Prod.map id (Database.ofFun : (X → Y) → Database X Y)) :=
    by simp only [Bm]; rw [one_kronecker_basisMatrix (A := S) Database.ofFun]
  have hT : tableOracle g.readDb * Bm = Bm * tableOracle (fun t : S × (X → Y) ↦ g.answer t.1 t.2) := by
    rw [hB]
    exact tableOracle_mul_one_kronecker_basisMatrix fun t ↦ by
      funext x
      simp [readDb, answer]
  rw [hsplit, compOracle]
  calc A * tableOracle g.readDb * A * (A * Bm) = A * tableOracle g.readDb * (A * A) * Bm := by
        simp only [Matrix.mul_assoc]
    _ = A * (tableOracle g.readDb * Bm) := by
        rw [one_kronecker_compS_mul_self, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hT, ← Matrix.mul_assoc]

/-- Reading the purified joint post-state at `G` gives, up to the weight `|Y|^(-|X|)`, the joint
post-state of the sampled game. -/
theorem smul_matrix_jointPost_sampled (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (p : Σ u, W u) (G : X → Y) :
    ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X) • ((g.sampled G).jointPost I x ρ p).matrix =
      (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ evalRow G)).amplifyLeft p.1
        (g.purified.jointPost I x ρ p).matrix := by
  have hsim := QuantumRuntime.simulation (R₁ := g.purified) (R₂ := g.sampled G)
    (V := MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ evalRow G)) I (fun i r ↦ by
      rcases i with ⟨⟩ | j
      · change MatrixMap.conj (tableOracle (fun t : S × Unit ↦ g.answer t.1 G)) ∘ₗ
            (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ evalRow G)).amplifyLeft (X × Y) =
          (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ evalRow G)).amplifyLeft (X × Y) ∘ₗ
            MatrixMap.conj (tableOracle (fun t : S × (X → Y) ↦ g.answer t.1 t.2))
        rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
          tableOracle_mul_one_kronecker_evalRow]
      · change MatrixMap.conj (g.sideKraus Unit j r) ∘ₗ
            (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ evalRow G)).amplifyLeft Unit =
          (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ evalRow G)).amplifyLeft Unit ∘ₗ
            MatrixMap.conj (g.sideKraus (X → Y) j r)
        rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
        exact congrArg MatrixMap.conj (g.sideKraus_mul_one_kronecker (X → Y) (evalRow G) j r)) x p
  have h' := LinearMap.congr_fun hsim (ρ.matrix ⊗ₖ g.purified.init.matrix)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, MatrixMap.amplifyLeft_kronecker] at h'
  rw [QuantumRuntime.matrix_jointPost, QuantumRuntime.matrix_jointPost]
  refine Eq.trans ?_ h'
  rw [← map_smul]
  refine congrArg (((g.sampled G).run I x).branch p) ?_
  have hk : ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X) •
      (ρ.matrix ⊗ₖ ((SubState.basis g.init).prod (SubState.basis ())).matrix :
        Matrix (A × (S × Unit)) (A × (S × Unit)) ℂ) =
      ρ.matrix ⊗ₖ MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ evalRow G)
        ((SubState.basis g.init).prod (uniformFunctionState X Y)).matrix := by
    rw [SubState.matrix_prod, SubState.matrix_prod, MatrixMap.conj_apply, conjTranspose_kronecker,
      conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      ← MatrixMap.conj_apply, conj_evalRow_uniformFunctionState, kronecker_smul, kronecker_smul]
  exact hk

/-- The compressed joint post-state is the purified one carried by `1_S ⊗ K`. -/
theorem matrix_jointPost_compressed_eq (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (p : Σ u, W u) :
    (g.compressed.jointPost I x ρ p).matrix =
      MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y))
        (g.purified.jointPost I x ρ p).matrix := by
  rw [← MatrixMap.amplifyLeft_conj]
  refine QuantumRuntime.matrix_jointPost_of_simulation (R₁ := g.purified) (R₂ := g.compressed)
    (V := MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)) I (fun i r ↦ ?_) ?_ x ρ p
  · rcases i with ⟨⟩ | j
    · change MatrixMap.conj g.compOracle ∘ₗ
          (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)).amplifyLeft (X × Y) =
        (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)).amplifyLeft (X × Y) ∘ₗ
          MatrixMap.conj (tableOracle (fun t : S × (X → Y) ↦ g.answer t.1 t.2))
      rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
        compOracle_mul_one_kronecker]
    · change MatrixMap.conj (g.sideKraus (Database X Y) j r) ∘ₗ
          (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)).amplifyLeft Unit =
        (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)).amplifyLeft Unit ∘ₗ
          MatrixMap.conj (g.sideKraus (X → Y) j r)
      rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
      exact congrArg MatrixMap.conj
        (g.sideKraus_mul_one_kronecker (X → Y) (tabCompress X Y) j r)
  · change MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)
        ((SubState.basis g.init).prod (uniformFunctionState X Y)).matrix =
      (SubState.basis (g.init, Database.empty)).matrix
    rw [SubState.matrix_prod, MatrixMap.conj_apply, conjTranspose_kronecker, conjTranspose_one,
      ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      ← MatrixMap.conj_apply, conj_compressAll_mul_basisMatrix_uniformFunctionState,
      SubState.matrix_basis, SubState.matrix_basis, SubState.matrix_basis]
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [kroneckerMap_apply, Matrix.single_apply, Prod.mk.injEq]
    rcases eq_or_ne g.init a with rfl | ha
    · rcases eq_or_ne g.init c with rfl | hc
      · rcases eq_or_ne Database.empty b with rfl | hb
        · rcases eq_or_ne Database.empty d with rfl | hd
          · simp
          · simp [hd]
        · simp [hb]
      · simp [hc]
    · simp [ha]

omit [Fintype S] [DecidableEq S] in
theorem trace_amplifyLeft_conj_one_kronecker_evalRow {B : Type*} [Fintype B] [DecidableEq B]
    [Fintype S] [DecidableEq S] (G : X → Y) (M : Matrix (B × (S × (X → Y))) (B × (S × (X → Y))) ℂ) :
    ((MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ evalRow G)).amplifyLeft B M).trace =
      ∑ b, ∑ s, M (b, (s, G)) (b, (s, G)) := by
  rw [MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply, Matrix.trace, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [Fintype.univ_punit, Finset.sum_singleton, Matrix.diag, Matrix.mul_apply,
    conjTranspose_apply, kroneckerMap_apply, Matrix.one_apply, evalRow, Matrix.of_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_eq_single b (fun b' _ h ↦ by simp [Ne.symm h]) (by simp),
    Finset.sum_eq_single s (fun s' _ h ↦ by simp [Ne.symm h]) (by simp),
    Finset.sum_eq_single G (fun G' _ h ↦ by simp [h]) (by simp)]
  rw [Finset.sum_eq_single b (fun b' _ h ↦ by simp [Ne.symm h]) (by simp),
    Finset.sum_eq_single s (fun s' _ h ↦ by simp [Ne.symm h]) (by simp),
    Finset.sum_eq_single G (fun G' _ h ↦ by simp [h]) (by simp)]
  simp

omit [Fintype S] [DecidableEq S] in
theorem trace_one_kronecker_diagonal_mul {B : Type*} [Fintype B] [DecidableEq B] [Fintype S]
    [DecidableEq S] (c : (X → Y) → ℂ) (M : Matrix (B × (S × (X → Y))) (B × (S × (X → Y))) ℂ) :
    (((1 : Matrix B B ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ diagonal c)) * M).trace =
      ∑ b, ∑ s, ∑ G, c G * M (b, (s, G)) (b, (s, G)) := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun G _ ↦ ?_
  rw [Matrix.diag, Matrix.mul_apply, Finset.sum_eq_single (b, (s, G))]
  · simp [kroneckerMap_apply]
  · intro k _ hk
    obtain ⟨b', s', G'⟩ := k
    simp only [kroneckerMap_apply, Matrix.one_apply, diagonal_apply]
    by_cases h1 : b = b'
    · by_cases h2 : s = s'
      · by_cases h3 : G = G'
        · exact absurd (by rw [h1, h2, h3]) hk
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · simp

/-- The weighted diagonal blocks of the function register beside the side state. -/
theorem sum_mul_trace_amplifyLeft_conj_one_kronecker_evalRow {B : Type*} [Fintype B]
    [DecidableEq B] (c : (X → Y) → ℂ) (M : Matrix (B × (S × (X → Y))) (B × (S × (X → Y))) ℂ) :
    ∑ G : X → Y, c G * ((MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ evalRow G)).amplifyLeft B M).trace =
      (((1 : Matrix B B ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ diagonal c)) * M).trace := by
  rw [trace_one_kronecker_diagonal_mul]
  simp only [trace_amplifyLeft_conj_one_kronecker_evalRow, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_comm]

/-- **The bridge for games with overrides.** -/
theorem sum_mul_trace_jointPost_sampled_eq (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (p : Σ u, W u)
    (c : (X → Y) → ℂ) :
    ∑ G : X → Y, c G * ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X *
        ((g.sampled G).jointPost I x ρ p).matrix.trace) =
      (((1 : Matrix p.1 p.1 ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ
        (tabCompress X Y * diagonal c * (tabCompress X Y)ᴴ))) *
        (g.compressed.jointPost I x ρ p).matrix).trace := by
  rw [matrix_jointPost_compressed_eq]
  have hK : ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)ᴴ * ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y) =
      1 := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
      conjTranspose_compressAll_mul_basisMatrix_mul_self, one_kronecker_one]
  have hC : (1 : Matrix S S ℂ) ⊗ₖ (tabCompress X Y * diagonal c * (tabCompress X Y)ᴴ) =
      ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y) * ((1 : Matrix S S ℂ) ⊗ₖ diagonal c) *
        ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)ᴴ := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
      Matrix.one_mul, Matrix.one_mul]
  rw [hC]
  refine Eq.trans ?_ (trace_one_kronecker_mul_conj _ hK _ _).symm
  refine Eq.trans ?_ (sum_mul_trace_amplifyLeft_conj_one_kronecker_evalRow c _)
  refine Finset.sum_congr rfl fun G _ ↦ ?_
  rw [← smul_matrix_jointPost_sampled]
  congr 1
  rw [← smul_eq_mul, ← Matrix.trace_smul]

end OvGame

end Qrom
