module

public import Qrom.Override
public import Qrom.EventBound
public import QuantumFoundations.MatrixMap.BlockNorm
public import VCVio.Quantum.Comp.TotalQueryBound

@[expose] public section

/-!
# Database events against a game with overrides

In side state `s`, the compressed oracle with overrides answers an overridden input `x` with
`d = ov s x`, leaving the database alone, and every other input with the compressed oracle
(`Qrom.OvGame.tableOracle_readS_eq`). An event of the database therefore commutes with the
overridden part, and its commutator with the rest is the commutator with the compressed oracle,
cut to the inputs that are not overridden: `‖[1 ⊗ Q, O_s]‖² ≤ 6 I`
(`Qrom.OvGame.norm_comm_cOs_sq_le`). Truncating at `|X|` cells changes nothing, since no database
has more, so `I` is the instability at `|X|`. Over the side states the oracle is block diagonal,
with the supremum of the blocks' norms as norm.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- No database has more than `|X|` cells, so truncating there is the identity. -/
theorem sizeProjector_card : sizeProjector X Y (Fintype.card X) = 1 := by
  rw [sizeProjector, ← diagonal_one]
  congr 1
  funext m
  simp only [show m.2.size ≤ Fintype.card X from Finset.card_le_univ _, ↓reduceIte]

theorem truncatedOracle_card [Nonempty Y] :
    truncatedOracle X Y (Fintype.card X) = compressedOracle X Y := by
  rw [truncatedOracle, sizeProjector_card, Matrix.one_mul, Matrix.mul_one]

namespace OvGame

variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]
variable (g : OvGame X Y S P Res)

/-- The read of a database in side state `s`. -/
def readS (s : S) (D : Database X Y) (x : X) : Y :=
  g.answer s (Database.lookup D) x

/-- The overridden inputs of side state `s`, on the query register. -/
def ovProj (s : S) : Matrix (X × Y) (X × Y) ℂ :=
  diagonal fun m ↦ if (g.ov s m.1).isSome then 1 else 0

/-- The override values of side state `s`, `0` where none. -/
def ovVal (s : S) (x : X) : Y :=
  (g.ov s x).getD 0

/-- The overridden inputs, on the joint register. -/
def ovDiag (s : S) : (X × Y) × Database X Y → ℂ :=
  fun p ↦ if (g.ov s p.1.1).isSome then 1 else 0

theorem ovProj_kronecker_one (s : S) :
    g.ovProj s ⊗ₖ (1 : Matrix (Database X Y) (Database X Y) ℂ) = diagonal (g.ovDiag s) := by
  ext ⟨m, D⟩ ⟨m', D'⟩
  by_cases h : (m, D) = (m', D')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [ovProj, ovDiag, kroneckerMap_apply]
  · rw [diagonal_apply_ne _ h, kroneckerMap_apply]
    by_cases hm : m = m'
    · subst hm
      have hD : D ≠ D' := fun hD ↦ h (by rw [hD])
      simp [Matrix.one_apply_ne hD]
    · simp [ovProj, diagonal_apply_ne _ hm]

/-- On the overridden inputs the table oracle adds the override values. -/
theorem diagonal_mul_tableOracle_readS (s : S) :
    diagonal (g.ovDiag s) * tableOracle (g.readS s) =
      diagonal (g.ovDiag s) * tableOracle (fun (_ : Database X Y) ↦ g.ovVal s) := by
  ext ⟨m, D⟩ ⟨m', D'⟩
  simp only [Matrix.diagonal_mul, tableOracle_apply, tableOracleEquiv_apply, oracleEquiv_apply,
    ovDiag]
  rcases h : g.ov s m.1 with _ | d
  · simp
  · simp only [Option.isSome_some, ↓reduceIte, one_mul]
    by_cases hm : m.1 = m'.1
    · simp [readS, answer, ovVal, ← hm, h]
    · have : ∀ y, (m, D) ≠ ((m'.1, m'.2 + y), D') := fun y he ↦ hm (by rw [Prod.mk.inj he |>.1])
      simp [this]

/-- Off the overridden inputs the table oracle is the standard oracle. -/
theorem one_sub_diagonal_mul_tableOracle_readS (s : S) :
    (1 - diagonal (g.ovDiag s)) * tableOracle (g.readS s) =
      (1 - diagonal (g.ovDiag s)) * standardOracle X Y := by
  rw [← diagonal_one, diagonal_sub]
  ext ⟨m, D⟩ ⟨m', D'⟩
  simp only [Matrix.diagonal_mul, tableOracle_apply, tableOracleEquiv_apply, oracleEquiv_apply,
    standardOracle_apply, standardOracleEquiv_apply, ovDiag]
  rcases h : g.ov s m.1 with _ | d
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, sub_zero, one_mul]
    by_cases hm : m.1 = m'.1
    · simp [readS, answer, ← hm, h]
    · have : ∀ y, (m, D) ≠ ((m'.1, m'.2 + y), D') := fun y he ↦ hm (by rw [Prod.mk.inj he |>.1])
      simp [this]
  · simp

theorem tableOracle_const (s : S) :
    tableOracle (fun (_ : Database X Y) ↦ g.ovVal s) =
      oracleUnitary (g.ovVal s) ⊗ₖ (1 : Matrix (Database X Y) (Database X Y) ℂ) := by
  ext ⟨m, D⟩ ⟨m', D'⟩
  simp only [tableOracle_apply, tableOracleEquiv_apply, kroneckerMap_apply, oracleUnitary_apply,
    Matrix.one_apply, oracleEquiv_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

variable [Nonempty Y]

/-- The compressed oracle of side state `s`. -/
noncomputable def cOs (s : S) : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ :=
  ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) * tableOracle (g.readS s) *
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y)

/-- **The decomposition of one side state.** -/
theorem cOs_eq (s : S) :
    g.cOs s = diagonal (g.ovDiag s) * (oracleUnitary (g.ovVal s) ⊗ₖ
        (1 : Matrix (Database X Y) (Database X Y) ℂ)) +
      (1 - diagonal (g.ovDiag s)) * compressedOracle X Y := by
  set A := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y with hA
  set Pr := diagonal (g.ovDiag s) with hPr
  have hAA : A * A = 1 := one_kronecker_compressAll_mul_self
  have hPrA : Pr * A = A * Pr := by
    rw [hPr, hA, ← ovProj_kronecker_one, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have hUA : (oracleUnitary (g.ovVal s) ⊗ₖ (1 : Matrix (Database X Y) (Database X Y) ℂ)) * A =
      A * (oracleUnitary (g.ovVal s) ⊗ₖ (1 : Matrix (Database X Y) (Database X Y) ℂ)) := by
    rw [hA, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one]
  have hT : tableOracle (g.readS s) = Pr * (oracleUnitary (g.ovVal s) ⊗ₖ
      (1 : Matrix (Database X Y) (Database X Y) ℂ)) + (1 - Pr) * standardOracle X Y := by
    rw [← tableOracle_const, ← diagonal_mul_tableOracle_readS,
      ← one_sub_diagonal_mul_tableOracle_readS, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
  have hPrcA : (1 - Pr) * A = A * (1 - Pr) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hPrA, Matrix.one_mul, Matrix.mul_one]
  rw [cOs, hT, Matrix.mul_add, Matrix.add_mul, compressedOracle]
  congr 1
  · calc A * (Pr * (oracleUnitary (g.ovVal s) ⊗ₖ (1 : Matrix (Database X Y) (Database X Y) ℂ))) * A
        = Pr * (oracleUnitary (g.ovVal s) ⊗ₖ (1 : Matrix (Database X Y) (Database X Y) ℂ)) *
            (A * A) := by
          rw [← Matrix.mul_assoc, ← hPrA, Matrix.mul_assoc Pr, ← hUA]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hAA, Matrix.mul_one]
  · calc A * ((1 - Pr) * standardOracle X Y) * A = (1 - Pr) * (A * standardOracle X Y * A) := by
          rw [← Matrix.mul_assoc, ← hPrcA]
          simp only [Matrix.mul_assoc]
      _ = _ := rfl

/-- **The commutator of one side state.** `‖[1 ⊗ Q, O_s]‖² ≤ 6 I(π, |X|)`. -/
theorem norm_comm_cOs_sq_le [UniformAnswerMeasure (X →ₒ Y)] (π : Database X Y → Bool) (s : S) :
    ‖((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ eventProj π) * g.cOs s -
        g.cOs s * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ eventProj π)‖ ^ 2 ≤
      6 * (Database.instability π (Fintype.card X)).toReal := by
  set Qh := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ eventProj π with hQh
  set Pr := diagonal (g.ovDiag s) with hPr
  set U := oracleUnitary (g.ovVal s) ⊗ₖ (1 : Matrix (Database X Y) (Database X Y) ℂ) with hU
  have hQPr : Qh * Pr = Pr * Qh := by
    rw [hPr, hQh, ← ovProj_kronecker_one, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have hQU : Qh * U = U * Qh := by
    rw [hQh, hU, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one]
  have hQPrc : Qh * (1 - Pr) = (1 - Pr) * Qh := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hQPr, Matrix.mul_one, Matrix.one_mul]
  have heq : Qh * g.cOs s - g.cOs s * Qh =
      (1 - Pr) * (Qh * compressedOracle X Y - compressedOracle X Y * Qh) := by
    rw [cOs_eq, Matrix.mul_add, Matrix.add_mul]
    have h1 : Qh * (Pr * U) = Pr * U * Qh := by
      rw [← Matrix.mul_assoc, hQPr, Matrix.mul_assoc, hQU, ← Matrix.mul_assoc]
    have h2 : Qh * ((1 - Pr) * compressedOracle X Y) =
        (1 - Pr) * (Qh * compressedOracle X Y) := by
      rw [← Matrix.mul_assoc, hQPrc, Matrix.mul_assoc]
    rw [h1, h2, Matrix.mul_sub, Matrix.mul_assoc (1 - Pr)]
    abel
  rw [heq]
  have hPrc : ‖(1 - Pr : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ)‖ ≤ 1 := by
    rw [← diagonal_one, diagonal_sub, l2_opNorm_diagonal]
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun p ↦ ?_
    by_cases h : (g.ov s p.1.1).isSome <;> simp [ovDiag, h]
  have hc := l2_opNorm_labelProjector_commutator_truncatedOracle_sq_le_six_mul π (Fintype.card X)
    true
  rw [truncatedOracle_card, ← one_kronecker_eventProj] at hc
  calc _ ≤ (‖(1 - Pr : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ)‖ *
        ‖Qh * compressedOracle X Y - compressedOracle X Y * Qh‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_mul _ _) 2
    _ ≤ (1 * ‖Qh * compressedOracle X Y - compressedOracle X Y * Qh‖) ^ 2 := by gcongr
    _ ≤ _ := by rw [one_mul]; exact hc

/-! ## Block diagonal over the side states -/

/-- The block diagonal operator with block `M s` at side state `s`. -/
noncomputable def blk {M : Type*} [Fintype M] [DecidableEq M] (B : S → Matrix M M ℂ) :
    Matrix (S × M) (S × M) ℂ :=
  ∑ s, Matrix.single s s (1 : ℂ) ⊗ₖ B s

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
theorem blk_apply {M : Type*} [Fintype M] [DecidableEq M] (B : S → Matrix M M ℂ) (s s' : S)
    (i j : M) : blk B (s, i) (s', j) = if s = s' then B s i j else 0 :=
  Matrix.sum_single_kronecker_apply B s s' i j

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
theorem blk_mul {M : Type*} [Fintype M] [DecidableEq M] (B C : S → Matrix M M ℂ) :
    blk B * blk C = blk (fun s ↦ B s * C s) := by
  ext ⟨s, i⟩ ⟨s', j⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single s, blk_apply]
  · by_cases h : s = s'
    · subst h
      simp [blk_apply, Matrix.mul_apply]
    · simp [blk_apply, h]
  · intro t _ ht
    simp [blk_apply, Ne.symm ht]
  · simp

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
theorem blk_sub {M : Type*} [Fintype M] [DecidableEq M] (B C : S → Matrix M M ℂ) :
    blk B - blk C = blk (fun s ↦ B s - C s) := by
  ext ⟨s, i⟩ ⟨s', j⟩
  simp only [Matrix.sub_apply, blk_apply]
  split_ifs <;> simp

/-- Moving the side state to the front. -/
def swapE : (X × Y) × (S × Database X Y) ≃ S × ((X × Y) × Database X Y) where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun q := (q.2.1, (q.1, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem one_kronecker_one_kronecker_eq (M : Matrix (Database X Y) (Database X Y) ℂ) :
    (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ M) =
      (blk fun _ : S ↦ (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ M).submatrix swapE swapE := by
  ext ⟨m, s, D⟩ ⟨m', s', D'⟩
  simp only [submatrix_apply, swapE, Equiv.coe_fn_mk, blk_apply, kroneckerMap_apply,
    Matrix.one_apply]
  by_cases h1 : m = m' <;> by_cases h2 : s = s' <;> simp [h1, h2]

theorem tableOracle_readDb_eq :
    tableOracle g.readDb = (blk fun s ↦ tableOracle (g.readS s)).submatrix swapE swapE := by
  ext ⟨m, s, D⟩ ⟨m', s', D'⟩
  simp only [submatrix_apply, swapE, Equiv.coe_fn_mk, blk_apply, tableOracle_apply,
    tableOracleEquiv_apply, Prod.mk.injEq]
  by_cases h : s = s'
  · subst h
    have hr : g.readDb (s, D') = g.readS s D' := rfl
    simp only [hr, true_and, ↓reduceIte]
  · simp [h]

theorem compOracle_eq : g.compOracle = (blk g.cOs).submatrix swapE swapE := by
  rw [compOracle, compS, one_kronecker_one_kronecker_eq, tableOracle_readDb_eq,
    submatrix_mul_equiv, submatrix_mul_equiv, blk_mul, blk_mul]
  rfl

/-- **The commutator of the compressed oracle with overrides.** -/
theorem norm_comm_compOracle_sq_le [UniformAnswerMeasure (X →ₒ Y)] (π : Database X Y → Bool) :
    ‖((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ eventProj π)) * g.compOracle -
        g.compOracle * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ eventProj π))‖ ^ 2 ≤
      6 * (Database.instability π (Fintype.card X)).toReal := by
  have hsub : ∀ M N : Matrix (S × ((X × Y) × Database X Y)) (S × ((X × Y) × Database X Y)) ℂ,
      M.submatrix swapE swapE - N.submatrix swapE swapE = (M - N).submatrix swapE swapE :=
    fun M N ↦ by ext; simp
  rw [compOracle_eq, one_kronecker_one_kronecker_eq, submatrix_mul_equiv, submatrix_mul_equiv,
    hsub, l2_opNorm_submatrix_equiv, blk_mul, blk_mul, blk_sub, blk,
    l2_opNorm_sum_single_kronecker]
  have h0 : 0 ≤ 6 * (Database.instability π (Fintype.card X)).toReal := by positivity
  have hsup := Real.iSup_le (fun s ↦ Real.le_sqrt_of_sq_le (g.norm_comm_cOs_sq_le π s))
    (Real.sqrt_nonneg _)
  calc _ ≤ √(6 * (Database.instability π (Fintype.card X)).toReal) ^ 2 :=
        pow_le_pow_left₀ (Real.iSup_nonneg fun _ ↦ norm_nonneg _) hsup 2
    _ = _ := Real.sq_sqrt h0

/-! ## The event bound -/

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The Kraus operators of the compressed game. -/
noncomputable def compKraus : ∀ i : (ovSpec X Y S P Res).Port, (ovSpec X Y S P Res).Result i →
    Matrix ((ovSpec X Y S P Res).Out i × (S × Database X Y))
      ((ovSpec X Y S P Res).In i × (S × Database X Y)) ℂ
  | .inl _ => fun _ ↦ g.compOracle
  | .inr j => fun r ↦ g.sideKraus (Database X Y) j r

/-- **The event bound for a game with overrides.** From `ρ`, a program with at most `n` calls in
all, to the hash and to the side ports, leaves weight at most `6 I(π, |X|) n² tr ρ` on the event
`π` of the compressed database. -/
theorem tsum_eventWeight_compressed_le [UniformAnswerMeasure (X →ₒ Y)] (I : L.Interp)
    (π : Database X Y → Bool) (hπ : π Database.empty = false) (n : ℕ)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (hx : x.IsTotalQueryBound n) (ρ : SubState A) :
    ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ
        ((1 : Matrix S S ℂ) ⊗ₖ eventProj π)) (g.compressed.jointPost I x ρ p).matrix).trace.re ≤
      ENNReal.ofReal (6 * (Database.instability π (Fintype.card X)).toReal) * (n : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal ρ.matrix.trace.re := by
  set R := g.compressed
  set Q : Matrix (S × Database X Y) (S × Database X Y) ℂ := (1 : Matrix S S ℂ) ⊗ₖ eventProj π
    with hQdef
  set c : ℝ≥0∞ := ENNReal.ofReal (6 * (Database.instability π (Fintype.card X)).toReal)
  have hU : ∀ i r, (R.step i).branch r = MatrixMap.conj (g.compKraus i r) := by
    rintro (⟨⟩ | j) r
    · exact SubInstrument.branch_ofIsometry_apply g.compOracle g.conjTranspose_compOracle_mul_self r
    · exact g.sideStep_branch (Database X Y) j r
  have hQ : Qᴴ = Q := by
    rw [hQdef, conjTranspose_kronecker, conjTranspose_one, eventProj_conjTranspose]
  have hQQ : Q * Q = Q := by
    rw [hQdef, ← mul_kronecker_mul, Matrix.one_mul, eventProj_mul_self]
  have hρ : (ρ.matrix ⊗ₖ R.init.matrix).PosSemidef := (ρ.prod R.init).posSemidef
  have hρQ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) (ρ.matrix ⊗ₖ R.init.matrix) = 0 := by
    have h : Q * (SubState.basis (g.init, Database.empty)).matrix = 0 := by
      rw [SubState.matrix_basis]
      ext ⟨s, D⟩ ⟨s', D'⟩
      simp only [hQdef, Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
        Matrix.one_apply, Matrix.single_apply, eventProj, labelProjector, diagonal_apply,
        Matrix.zero_apply]
      refine Finset.sum_eq_zero fun s₁ _ ↦ Finset.sum_eq_zero fun D₁ _ ↦ ?_
      by_cases h1 : D = D₁
      · subst h1
        by_cases h2 : D = Database.empty
        · subst h2
          simp [hπ]
        · simp [Ne.symm h2]
      · simp [h1]
    rw [MatrixMap.conj_apply, ← mul_kronecker_mul, Matrix.one_mul]
    change ρ.matrix ⊗ₖ (Q * (SubState.basis (g.init, Database.empty)).matrix) * _ = 0
    rw [h, kronecker_zero, Matrix.zero_mul]
  have h := QuantumRuntime.rpow_inv_two_eventWeight_le_commutators (D := R.D) (σ₀ := R.init)
    (s := R.step) (U := g.compKraus) I hU hQ hQQ x hρ hρQ
  -- each call's commutator weight is at most `c` times the trace of its input
  have hcall : ∀ (i : (ovSpec X Y S P Res).Port) (σ : Matrix ((ovSpec X Y S P Res).In i ×
      (S × Database X Y)) ((ovSpec X Y S P Res).In i × (S × Database X Y)) ℂ), σ.PosSemidef →
      QuantumRuntime.krausWeight (spec := ovSpec X Y S P Res) (D := R.D)
          (fun i r ↦ (1 ⊗ₖ Q) * g.compKraus i r - g.compKraus i r * (1 ⊗ₖ Q)) i σ ≤
        c * ENNReal.ofReal σ.trace.re := by
    rintro (⟨⟨⟩⟩ | j) σ hσ
    · let _ : Unique ((ovSpec X Y S P Res).Result (.inl ())) := inferInstanceAs (Unique Unit)
      let _ : Fintype ((ovSpec X Y S P Res).Result (.inl ())) := inferInstanceAs (Fintype Unit)
      refine (QuantumRuntime.krausWeight_le (spec := ovSpec X Y S P Res) (D := R.D)
        (fun i r ↦ (1 ⊗ₖ Q) * g.compKraus i r - g.compKraus i r * (1 ⊗ₖ Q)) _ hσ).trans ?_
      gcongr
      rw [tsum_fintype, Fintype.sum_unique]
      exact ENNReal.ofReal_le_ofReal (g.norm_comm_compOracle_sq_le π)
    · rw [QuantumRuntime.krausWeight]
      refine (ENNReal.tsum_eq_zero.mpr fun r ↦ ?_).le.trans zero_le
      have hz : ((1 : Matrix ((ovSpec X Y S P Res).Out (.inr j)) ((ovSpec X Y S P Res).Out (.inr j))
          ℂ) ⊗ₖ Q) * g.compKraus (.inr j) r - g.compKraus (.inr j) r *
          ((1 : Matrix ((ovSpec X Y S P Res).In (.inr j)) ((ovSpec X Y S P Res).In (.inr j)) ℂ) ⊗ₖ
            Q) = 0 :=
        sub_eq_zero.mpr (g.sideKraus_mul_one_kronecker (Database X Y) (eventProj π) j r).symm
      rw [hz, MatrixMap.conj_apply, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero,
        Complex.zero_re, ENNReal.ofReal_zero]
  have hj : ∀ j, R.queryWeight I (QuantumRuntime.krausWeight
        (fun i r ↦ (1 ⊗ₖ Q) * g.compKraus i r - g.compKraus i r * (1 ⊗ₖ Q))) x
        (ρ.matrix ⊗ₖ R.init.matrix) j ≤ c * ENNReal.ofReal ρ.matrix.trace.re := by
    intro j
    refine (R.queryWeight_mono I (w' := fun _ σ ↦ c * ENNReal.ofReal σ.trace.re) hcall x hρ
      j).trans ?_
    rw [QuantumRuntime.queryWeight_const_mul]
    have htr : (ρ.matrix ⊗ₖ R.init.matrix).trace = ρ.matrix.trace := by
      simp [R, Matrix.trace_kronecker, SubState.matrix_basis]
    gcongr
    rw [← htr]
    exact R.queryWeight_le_ofReal_trace I (fun _ _ _ ↦ le_rfl) x hρ j
  have hzero : ∀ j ∉ Finset.range n, R.queryWeight I (QuantumRuntime.krausWeight
        (fun i r ↦ (1 ⊗ₖ Q) * g.compKraus i r - g.compKraus i r * (1 ⊗ₖ Q))) x
        (ρ.matrix ⊗ₖ R.init.matrix) j ^ (2⁻¹ : ℝ) = 0 := by
    intro j hj'
    rw [R.queryWeight_eq_zero_of_isTotalQueryBound I hx (by simpa using hj') _,
      ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hzero] at h
  have hsum : ∑ j ∈ Finset.range n, R.queryWeight I (QuantumRuntime.krausWeight
        (fun i r ↦ (1 ⊗ₖ Q) * g.compKraus i r - g.compKraus i r * (1 ⊗ₖ Q))) x
        (ρ.matrix ⊗ₖ R.init.matrix) j ^ (2⁻¹ : ℝ) ≤
      (n : ℝ≥0∞) * (c * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) := by
    calc _ ≤ ∑ _j ∈ Finset.range n, (c * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ ENNReal.rpow_le_rpow (hj j) (by norm_num)
      _ = _ := by simp
  have h2 := ENNReal.rpow_le_rpow (h.trans hsum) (z := 2) (by norm_num)
  rw [← ENNReal.rpow_mul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    show (2⁻¹ : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2
  calc _ ≤ _ := h2
    _ = _ := by
      rw [show ((n : ℝ≥0∞) ^ (2 : ℝ)) = (n : ℝ≥0∞) ^ 2 by norm_cast]
      ring

end OvGame

end Qrom
