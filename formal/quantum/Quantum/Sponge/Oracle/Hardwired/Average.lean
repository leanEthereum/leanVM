module

public import Quantum.Sponge.Oracle.Hardwired.Event

@[expose] public section

/-!
# The hardwired runtime is the average over consistent functions

For hardwired cells `W` and functions `t = (h, k, k')`, `overwrite W t` replaces the values of
`t` on the hardwired cells by those of `W`. A program over `spongeSpec X Z`, run against the
hardwired runtime started at `(∅, W, m)`, has the law of the experiment with the functions
`overwrite W t` for uniform `t` (`evalDistMap_hardwired_eq_avg`), that is, with uniform functions
consistent with `W` (`evalDistMap_hardwired_eq_avg_consistent`). For `W` empty this is
`evalDistMap_spongeCompressedRuntime`.

The proof: the sponge ports act block by block on the classical data `(W, m)`, which they never
change, so the run stays in the block of the start (`hwBlock`); on that block every port is the
table oracle of `(W a).getD (D.lookup a)` conjugated by the compression of every cell, and the
tabulation of the functions intertwines it with the purified oracle of `overwrite W t`, whose rows
are the runs against `overwrite W t`, as in `evalDistMap_spongeCompressedRuntime`.
-/

open MeasureTheory Matrix
open scoped Kronecker ENNReal NNReal

universe u v w

namespace Quantum.Sponge

open Quantum

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

/-! ## Overwriting functions with hardwired values -/

/-- The functions `t` with their values on the hardwired cells of `W` replaced by `W`'s. -/
def overwrite (W : Hw X Z) (t : (Z → X) × (X → Z) × (X → Z)) : (Z → X) × (X → Z) × (X → Z) :=
  (fun z ↦ (W.1 z).getD (t.1 z), fun x ↦ (W.2.1 x).getD (t.2.1 x),
    fun x ↦ (W.2.2 x).getD (t.2.2 x))

/-- The functions `t` agree with the hardwired cells of `W`. -/
def Consistent (W : Hw X Z) (t : (Z → X) × (X → Z) × (X → Z)) : Prop :=
  overwrite W t = t

instance (W : Hw X Z) : DecidablePred (Consistent W) :=
  fun t ↦ inferInstanceAs (Decidable (overwrite W t = t))

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem overwrite_overwrite (W : Hw X Z) (t : (Z → X) × (X → Z) × (X → Z)) :
    overwrite W (overwrite W t) = overwrite W t := by
  simp only [overwrite, Prod.mk.injEq]
  refine ⟨funext fun z ↦ ?_, funext fun x ↦ ?_, funext fun x ↦ ?_⟩
  · cases W.1 z <;> rfl
  · cases W.2.1 x <;> rfl
  · cases W.2.2 x <;> rfl

/-! ## Unitarity of conjugated table oracles -/

/-- A table oracle conjugated by a Hermitian involution is unitary. -/
theorem conj_tableOracle_mem_unitaryGroup {A Y T : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] [Fintype T] [DecidableEq T] (C : Matrix T T ℂ)
    (hCh : Cᴴ = C) (hCC : C * C = 1) (read : T → A → Y) :
    ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) * tableOracle read *
        ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) ∈ unitaryGroup ((A × Y) × T) ℂ := by
  have hCh' : ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C)ᴴ = (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C := by
    rw [conjTranspose_kronecker, conjTranspose_one, hCh]
  have hCC' : ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) =
      1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul, hCC, one_kronecker_one]
  have hC : ∀ N : Matrix ((A × Y) × T) ((A × Y) × T) ℂ,
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) * (((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) * N) = N :=
    fun N ↦ by rw [← Matrix.mul_assoc, hCC', Matrix.one_mul]
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
  simp only [conjTranspose_mul, hCh', Matrix.mul_assoc, hC]
  rw [← Matrix.mul_assoc (tableOracle read)ᴴ, conjTranspose_tableOracle_mul_self, Matrix.one_mul,
    hCC']

variable [AddCommGroup X] [AddCommGroup Z]

/-! ## The block of one classical datum -/

variable (X Z) in
/-- The hardwired oracle on one block: the database register only, with fixed hardwired cells
`W`, started empty. -/
@[reducible]
noncomputable def hwBlock (W : Hw X Z) : EmulatedOracle SpongePort (spongeIn X Z) where
  S := QReg.of (DbReg X Z)
  init := SubState.basis (Database.empty, Database.empty, Database.empty)
  U
    | .h => ((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ compressDbs X Z) *
        tableOracle (fun D : DbReg X Z ↦ fun z ↦ (W.1 z).getD (D.1.lookup z)) *
        ((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ compressDbs X Z)
    | .k => ((1 : Matrix (X × Z) (X × Z) ℂ) ⊗ₖ compressDbs X Z) *
        tableOracle (fun D : DbReg X Z ↦ fun x ↦ (W.2.1 x).getD (D.2.1.lookup x)) *
        ((1 : Matrix (X × Z) (X × Z) ℂ) ⊗ₖ compressDbs X Z)
    | .k' => ((1 : Matrix (X × Z) (X × Z) ℂ) ⊗ₖ compressDbs X Z) *
        tableOracle (fun D : DbReg X Z ↦ fun x ↦ (W.2.2 x).getD (D.2.2.lookup x)) *
        ((1 : Matrix (X × Z) (X × Z) ℂ) ⊗ₖ compressDbs X Z)
  unitary
    | .h => conj_tableOracle_mem_unitaryGroup _ conjTranspose_compressDbs compressDbs_mul_self _
    | .k => conj_tableOracle_mem_unitaryGroup _ conjTranspose_compressDbs compressDbs_mul_self _
    | .k' => conj_tableOracle_mem_unitaryGroup _ conjTranspose_compressDbs compressDbs_mul_self _

/-- The sponge ports of the hardwired oracle are block diagonal, with the ports of `hwBlock` on
the blocks. -/
theorem spongeHardwired_U_eq_liftBlocks (W₀ : Hw X Z) (m₀ : M) (i : SpongePort) :
    (spongeHardwired X Z W₀ m₀).U i =
      liftBlocks (hwSplit X Z M (spongeIn X Z i)) fun b ↦ (hwBlock X Z b.1).U i := by
  cases i <;> exact hwPort_eq_liftBlocks _

/-- Reading the classical data at `b`: the row `⟨b|` on the classical factor. -/
def blockRow (b : Hw X Z × M) : Matrix (DbReg X Z) (HwReg X Z M) ℂ :=
  Matrix.of fun D' s ↦ if s.1 = D' ∧ s.2 = b then 1 else 0

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The rows of the classical data resolve the identity. -/
theorem sum_conjTranspose_blockRow_mul_self :
    ∑ b : Hw X Z × M, (blockRow b)ᴴ * blockRow b = 1 := by
  ext ⟨D, b⟩ ⟨D', b'⟩
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, blockRow, of_apply]
  by_cases h : D = D' ∧ b = b'
  · obtain ⟨rfl, rfl⟩ := h
    rw [Finset.sum_eq_single b (fun c _ hc ↦ by simp [Ne.symm hc]) (by simp)]
    simp
  · rw [Matrix.one_apply_ne (by simpa [Prod.ext_iff] using h)]
    refine Finset.sum_eq_zero fun c _ ↦ Finset.sum_eq_zero fun D₁ _ ↦ ?_
    by_cases h₁ : D = D₁ ∧ b = c
    · obtain ⟨rfl, rfl⟩ := h₁
      have : ¬ (D' = D ∧ b' = b) := fun h' ↦ h ⟨h'.1.symm, h'.2.symm⟩
      simp [this]
    · simp [h₁]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- Reading the classical data at `b` intertwines a block diagonal operator with its block. -/
theorem one_kronecker_blockRow_mul_liftBlocks {P : Type} [Fintype P] [DecidableEq P]
    (U : Hw X Z × M → Matrix (P × DbReg X Z) (P × DbReg X Z) ℂ) (b : Hw X Z × M) :
    ((1 : Matrix P P ℂ) ⊗ₖ blockRow b) * liftBlocks (hwSplit X Z M P) U =
      U b * ((1 : Matrix P P ℂ) ⊗ₖ blockRow b) := by
  ext ⟨p', D'⟩ ⟨p, D, c⟩
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (p', (D', b)) ?_ (by simp),
    Finset.sum_eq_single (p, D) ?_ (by simp)]
  · by_cases hc : c = b
    · subst hc
      simp [kroneckerMap_apply, blockRow, liftBlocks, hwSplit, blockDiagonal_apply]
    · simp [kroneckerMap_apply, blockRow, liftBlocks, hwSplit, blockDiagonal_apply, hc, Ne.symm hc]
  · rintro ⟨p₁, D₁⟩ - hne
    rw [kroneckerMap_apply]
    by_cases hp : p₁ = p
    · subst hp
      have : ¬ (D = D₁ ∧ c = b) := fun h ↦ hne (by rw [h.1])
      simp [blockRow, this]
    · simp [Matrix.one_apply_ne hp]
  · rintro ⟨p₁, s₁⟩ - hne
    rw [kroneckerMap_apply]
    by_cases hp : p' = p₁
    · subst hp
      have : ¬ (s₁.1 = D' ∧ s₁.2 = b) := fun h ↦ hne (Prod.ext rfl (Prod.ext h.1 h.2))
      simp [blockRow, this]
    · simp [Matrix.one_apply_ne hp]

/-! ## The main theorem -/

variable (X Z) in
/-- The purified oracle of the functions `overwrite W t`. -/
@[reducible]
noncomputable def spongePurifiedHw (W : Hw X Z) : EmulatedOracle SpongePort (spongeIn X Z) where
  S := QReg.of ((Z → X) × (X → Z) × (X → Z))
  init := (spongePurified X Z).init
  U
    | .h => tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).1
    | .k => tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).2.1
    | .k' => tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).2.2
  unitary
    | .h => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)
    | .k => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)
    | .k' => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)

/-- Tabulating and compressing intertwines the block oracle with the purified oracle of the
overwritten functions. -/
theorem hwBlock_U_mul_one_kronecker (W : Hw X Z) (i : SpongePort) :
    (hwBlock X Z W).U i * (1 ⊗ₖ tabulateDbs X Z) =
      (1 ⊗ₖ tabulateDbs X Z) * (spongePurifiedHw X Z W).U i := by
  cases i
  · exact conj_tableOracle_mul_one_kronecker _ _ _ compressDbs_mul_self _
      fun t ↦ funext fun z ↦ by simp [ofFunDbs, overwrite]
  · exact conj_tableOracle_mul_one_kronecker _ _ _ compressDbs_mul_self _
      fun t ↦ funext fun x ↦ by simp [ofFunDbs, overwrite]
  · exact conj_tableOracle_mul_one_kronecker _ _ _ compressDbs_mul_self _
      fun t ↦ funext fun x ↦ by simp [ofFunDbs, overwrite]

/-- The rows of the triples intertwine the purified oracle of the overwritten functions with the
oracles of the overwritten functions. -/
theorem spongeFnRuntime_overwrite_step_intertwine (W : Hw X Z)
    (t : (Z → X) × (X → Z) × (X → Z)) (i : SpongePort) (r : Unit) :
    ((spongeFnRuntime (overwrite W t).1 (overwrite W t).2.1 (overwrite W t).2.2).step i).branch r ∘ₗ
        (MatrixMap.conj (rowAt t)).amplifyLeft ((spongeSpec X Z).In i) =
      (MatrixMap.conj (rowAt t)).amplifyLeft ((spongeSpec X Z).Out i) ∘ₗ
        ((spongePurifiedHw X Z W).toRuntime.step i).branch r := by
  cases i
  · change (MatrixMap.conj (oracleUnitary (overwrite W t).1)).amplify Unit ∘ₗ
        (MatrixMap.conj (rowAt t)).amplifyLeft (Z × X) =
      (MatrixMap.conj (rowAt t)).amplifyLeft (Z × X) ∘ₗ
        MatrixMap.conj (tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).1)
    rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
      ← MatrixMap.conj_mul, oracleUnitary_kronecker_one_mul_one_kronecker_rowAt
        (fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).1)]
  · change (MatrixMap.conj (oracleUnitary (overwrite W t).2.1)).amplify Unit ∘ₗ
        (MatrixMap.conj (rowAt t)).amplifyLeft (X × Z) =
      (MatrixMap.conj (rowAt t)).amplifyLeft (X × Z) ∘ₗ
        MatrixMap.conj (tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).2.1)
    rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
      ← MatrixMap.conj_mul, oracleUnitary_kronecker_one_mul_one_kronecker_rowAt
        (fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).2.1)]
  · change (MatrixMap.conj (oracleUnitary (overwrite W t).2.2)).amplify Unit ∘ₗ
        (MatrixMap.conj (rowAt t)).amplifyLeft (X × Z) =
      (MatrixMap.conj (rowAt t)).amplifyLeft (X × Z) ∘ₗ
        MatrixMap.conj (tableOracle fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).2.2)
    rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
      ← MatrixMap.conj_mul, oracleUnitary_kronecker_one_mul_one_kronecker_rowAt
        (fun t : (Z → X) × (X → Z) × (X → Z) ↦ (overwrite W t).2.2)]

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The block oracle is the experiment with the overwritten functions. -/
theorem evalDistMap_hwBlock {γ : Type*} [MeasurableSpace γ] (Wh : Hw X Z) (I : L.Interp)
    (x : QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (hwBlock X Z Wh).toRuntime.evalDistMap I x ρ f =
      ∑ t : (Z → X) × (X → Z) × (X → Z), (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ •
        (spongeFnRuntime (overwrite Wh t).1 (overwrite Wh t).2.1 (overwrite Wh t).2.2).evalDistMap
          I x ρ f := by
  refine (EmulatedOracle.outcomeLawWith_eq_of_intertwine (spongePurifiedHw X Z Wh)
    (hwBlock X Z Wh) (tabulateDbs X Z) conjTranspose_tabulateDbs_mul_self
    (hwBlock_U_mul_one_kronecker Wh) conj_tabulateDbs_init I x ρ f).trans ?_
  refine (evalDistMap_eq_sum_of_rows (spongePurifiedHw X Z Wh).toRuntime
    (fun t ↦ spongeFnRuntime (overwrite Wh t).1 (overwrite Wh t).2.1 (overwrite Wh t).2.2)
    (fun t ↦ rowAt t) (fun _ ↦ (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0)⁻¹)
    (by exact sum_conjTranspose_rowAt_mul_self)
    (fun t i r ↦ by exact spongeFnRuntime_overwrite_step_intertwine Wh t i r)
    (fun t ↦ by exact conj_rowAt_uniform t) I x ρ f).trans ?_
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [ENNReal.coe_inv (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_natCast]

/-- A program over the sponge ports, run against runtime 1, is run against its sponge oracles. -/
theorem evalDistMap_spongeHardwiredReadRuntime_liftOrdinary {γ : Type*} [MeasurableSpace γ]
    (W₀ : Hw X Z) (m₀ : M) (I : L.Interp) (x : QuantumComp L (spongeSpec X Z) W A)
    (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (spongeHardwiredReadRuntime X Z W₀ m₀).evalDistMap I x.liftOrdinary ρ f =
      (spongeHardwired X Z W₀ m₀).toRuntime.evalDistMap I x ρ f := by
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost,
    spongeHardwiredReadRuntime, QuantumRuntime.run_liftOrdinary]
  rfl

/-- A program over the sponge and read ports, run against the hardwired runtime, is run against
runtime 1. -/
theorem evalDistMap_spongeHardwiredRuntime_liftOrdinary {γ : Type*} [MeasurableSpace γ]
    (W₀ : Hw X Z) (m₀ : M) (I : L.Interp) (x : QuantumComp L (hwReadSpec X Z M) W A)
    (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (spongeHardwiredRuntime X Z W₀ m₀).evalDistMap I x.liftOrdinary ρ f =
      (spongeHardwiredReadRuntime X Z W₀ m₀).evalDistMap I x ρ f := by
  have h := QuantumRuntime.run_liftOrdinary (spongeHardwiredReadRuntime X Z W₀ m₀) I
    (t := hwProgSpec X Z) hwProgStep x
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.matrix_jointPost, spongeHardwiredRuntime]
  rw [h]
  rfl

/-- **The hardwired runtime is the average over overwritten functions.** A program over the
sponge ports, run against runtime 1 started at `(∅, W₀, m₀)`, has the law of the experiment with
the functions `overwrite W₀ t` for uniform `t`. -/
theorem evalDistMap_hardwired_eq_avg {γ : Type*} [MeasurableSpace γ] (W₀ : Hw X Z) (m₀ : M)
    (I : L.Interp) (x : QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (spongeHardwiredReadRuntime X Z W₀ m₀).evalDistMap I x.liftOrdinary ρ f =
      ∑ t : (Z → X) × (X → Z) × (X → Z), (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ •
        (spongeFnRuntime (overwrite W₀ t).1 (overwrite W₀ t).2.1 (overwrite W₀ t).2.2).evalDistMap
          I x ρ f := by
  rw [evalDistMap_spongeHardwiredReadRuntime_liftOrdinary, ← evalDistMap_hwBlock W₀ I x ρ f]
  refine (evalDistMap_eq_sum_of_rows (spongeHardwired X Z W₀ m₀).toRuntime
    (fun b : Hw X Z × M ↦ (hwBlock X Z b.1).toRuntime) (fun b ↦ blockRow b)
    (fun b ↦ if b = (W₀, m₀) then 1 else 0) (by exact sum_conjTranspose_blockRow_mul_self)
    (fun b i r ↦ ?_) (fun b ↦ ?_) I x ρ f).trans ?_
  · change MatrixMap.conj ((hwBlock X Z b.1).U i) ∘ₗ
        (MatrixMap.conj (blockRow b)).amplifyLeft (spongeIn X Z i) =
      (MatrixMap.conj (blockRow b)).amplifyLeft (spongeIn X Z i) ∘ₗ
        MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U i)
    rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
      spongeHardwired_U_eq_liftBlocks, one_kronecker_blockRow_mul_liftBlocks]
  · change MatrixMap.conj (blockRow b)
        (SubState.basis (((Database.empty, Database.empty, Database.empty), W₀, m₀) :
          HwReg X Z M)).matrix =
      (((if b = (W₀, m₀) then 1 else 0 : ℝ≥0) : ℝ) : ℂ) •
        (SubState.basis ((Database.empty, Database.empty, Database.empty) : DbReg X Z)).matrix
    rw [SubState.matrix_basis, SubState.matrix_basis]
    ext D D'
    simp only [MatrixMap.conj_apply, Matrix.mul_apply, conjTranspose_apply, blockRow, of_apply,
      Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (((Database.empty, Database.empty, Database.empty), W₀, m₀) :
      HwReg X Z M) (fun s _ hs ↦ by simp [Ne.symm hs]) (by simp)]
    rw [Finset.sum_eq_single (((Database.empty, Database.empty, Database.empty), W₀, m₀) :
      HwReg X Z M) (fun s _ hs ↦ by simp [Ne.symm hs]) (by simp)]
    by_cases hb : (W₀, m₀) = b
    · subst hb
      by_cases h₁ : (Database.empty, Database.empty, Database.empty) = D <;>
        by_cases h₂ : (Database.empty, Database.empty, Database.empty) = D' <;>
        simp [h₁, h₂]
    · simp [hb, Ne.symm hb]
  · rw [Finset.sum_eq_single (W₀, m₀) (fun b _ hb ↦ by simp [hb]) (by simp)]
    simp

/-! ## Averaging over consistent functions -/

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- Translating the functions `t` by a difference of consistent functions moves the fibers of
`overwrite W`. -/
theorem overwrite_translate (W : Hw X Z) (t t'' : (Z → X) × (X → Z) × (X → Z))
    (h'' : Consistent W t'') : overwrite W (t - overwrite W t + t'') = t'' := by
  refine Eq.trans ?_ h''
  simp only [overwrite, Prod.mk.injEq]
  refine ⟨funext fun z ↦ ?_, funext fun x ↦ ?_, funext fun x ↦ ?_⟩
  · cases hz : W.1 z <;> simp [hz]
  · cases hx : W.2.1 x <;> simp [hx]
  · cases hx : W.2.2 x <;> simp [hx]

/-- All fibers of `overwrite W` over consistent functions have the same size. -/
theorem card_fiber_overwrite (W : Hw X Z) {t' t'' : (Z → X) × (X → Z) × (X → Z)}
    (h' : Consistent W t') (h'' : Consistent W t'') :
    (Finset.univ.filter fun t ↦ overwrite W t = t').card =
      (Finset.univ.filter fun t ↦ overwrite W t = t'').card := by
  refine Finset.card_nbij' (fun t ↦ t - t' + t'') (fun t ↦ t - t'' + t') (fun t ht ↦ ?_)
    (fun t ht ↦ ?_) (fun t _ ↦ by simp only [add_sub_cancel_right, sub_add_cancel])
    (fun t _ ↦ by simp only [add_sub_cancel_right, sub_add_cancel])
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    have h := overwrite_translate W t t'' h''
    rwa [ht] at h
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    have h := overwrite_translate W t t' h'
    rwa [ht] at h

/-- **Averaging over overwritten functions is averaging over consistent functions.** -/
theorem sum_overwrite_eq_sum_consistent (W : Hw X Z) {β : Type*} [AddCommMonoid β]
    [Module ℝ≥0∞ β] (F : (Z → X) × (X → Z) × (X → Z) → β) :
    ∑ t, (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ • F (overwrite W t) =
      ∑ t ∈ Finset.univ.filter (Consistent W),
        ((Finset.univ.filter (Consistent W)).card : ℝ≥0∞)⁻¹ • F t := by
  set C := Finset.univ.filter (Consistent W)
  set t₀ := overwrite W 0
  have h₀ : Consistent W t₀ := overwrite_overwrite W 0
  set k := (Finset.univ.filter fun t ↦ overwrite W t = t₀).card
  have hmaps : ∀ t ∈ (Finset.univ : Finset ((Z → X) × (X → Z) × (X → Z))),
      overwrite W t ∈ C := fun t _ ↦ by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact overwrite_overwrite W t
  have hk : ∀ t' ∈ C, (Finset.univ.filter fun t ↦ overwrite W t = t').card = k := fun t' ht' ↦
    card_fiber_overwrite W (Finset.mem_filter.mp ht').2 h₀
  have hk0 : k ≠ 0 := Finset.card_ne_zero.mpr ⟨t₀, by simp [t₀, overwrite_overwrite]⟩
  have hcard : Fintype.card ((Z → X) × (X → Z) × (X → Z)) = C.card * k := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hk,
      Finset.sum_const, smul_eq_mul]
  rw [← Finset.smul_sum, ← Finset.smul_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]
  have hin : ∀ t' ∈ C, ∑ t ∈ Finset.univ.filter (fun t ↦ overwrite W t = t'), F (overwrite W t) =
      (k : ℝ≥0∞) • F t' := fun t' ht' ↦ by
    rw [Finset.sum_congr rfl fun t ht ↦ by rw [(Finset.mem_filter.mp ht).2], Finset.sum_const,
      hk t' ht', Nat.cast_smul_eq_nsmul]
  rw [Finset.sum_congr rfl hin, ← Finset.smul_sum, smul_smul, hcard, Nat.cast_mul]
  congr 1
  have hk' : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top k)) (Or.inr hk'), mul_assoc,
    ENNReal.inv_mul_cancel hk' (ENNReal.natCast_ne_top k), mul_one]

/-- **The hardwired runtime is the experiment with uniform functions consistent with `W₀`.** -/
theorem evalDistMap_hardwired_eq_avg_consistent {γ : Type*} [MeasurableSpace γ] (W₀ : Hw X Z)
    (m₀ : M) (I : L.Interp) (x : QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (spongeHardwiredReadRuntime X Z W₀ m₀).evalDistMap I x.liftOrdinary ρ f =
      ∑ t ∈ Finset.univ.filter (Consistent W₀),
        ((Finset.univ.filter (Consistent W₀)).card : ℝ≥0∞)⁻¹ •
          (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap I x ρ f := by
  rw [evalDistMap_hardwired_eq_avg]
  exact sum_overwrite_eq_sum_consistent W₀
    (fun t ↦ (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap I x ρ f)

end Quantum.Sponge

end
