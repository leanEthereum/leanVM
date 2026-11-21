module

public import Quantum.Sponge.Reads.Core
public import VCVio.Quantum.Oracle.Compressed.Consistency

@[expose] public section

/-!
# Classical reads of one compressed random oracle

The single-function case of the fundamental lemma for recorded reads (Lemma 4.14 and
Corollary 4.15 of ePrint 2025/731, in the form of Chiesa, Di, Hu and Zheng, ePrint 2025/2166,
eq. (26)). A program `x` over `Quantum.qromSpec X Y` is followed by classical reads at its leaf
(`withReads x (qromReadImpl X Y) oa`), each a basis call `|t, 0⟩ ↦ |t, H t⟩` read out in the
computational basis. If every read algorithm makes at most `l` queries, then any event of the
leaf, result and read log has probability, in the quantum random-oracle model, at most its
probability jointly with "the measured compressed database holds every logged answer", plus
`2 l / |Y|` (`qromEvalDistMap_withReads_le`).

The proof runs against the purified oracle, whose register holds the function: there the reads
project onto the functions consistent with the log. Compressing the tabulated function,
`M = S^{⊗X} E`, carries this projector `Pf` to the compressed consistency projector `P̂`
(`compressAll_mul_basisMatrix_mul_logProjector`), and `P̂ P P̂ = (1 - 1/|Y|)^{2d} P̂`
(`Quantum.compressedCheckProjector_mul_checkProjector_mul_compressedCheckProjector`) gives
`Pf Mᴴ P M Pf = (1 - 1/|Y|)^{2d} Pf` for the check projector `P` of the measured database.
-/

open Matrix MeasureTheory OracleSpec OracleComp
open scoped Kronecker ENNReal

universe u v w

namespace Quantum.Sponge

open Quantum

/-! ## Read lengths -/

/-- A transcript of an algorithm making at most `n` queries has at most `n` entries. -/
theorem IsTranscript.length_le {ι : Type} {ospec : OracleSpec.{0, 0} ι} {β : Type}
    {oa : OracleComp ospec β} {n : ℕ} (hb : IsTotalQueryBound oa n) {r : β × QueryLog ospec}
    (hr : IsTranscript oa r) : r.2.length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n r with
  | pure b =>
    rw [isTranscript_pure] at hr
    subst hr
    simp
  | query_bind t k ih =>
    obtain ⟨c, log, hlog, hk⟩ := (isTranscript_query_bind t k r).mp hr
    rw [isTotalQueryBound_query_bind_iff] at hb
    have h := ih c (hb.2 c) hk
    have hn := hb.1
    rw [hlog, List.length_cons]
    dsimp only at h
    omega

/-- Bernoulli's inequality for the consistency scalar: `1 - 2 d / N ≤ (1 - 1/N)^(2 d)`. -/
theorem one_sub_le_one_sub_inv_pow (N : ℕ) (hN : 0 < N) (d l : ℕ) (hd : d ≤ l) :
    1 - 2 * (l : ℝ) / N ≤ (1 - (N : ℝ)⁻¹) ^ (2 * d) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h := one_add_mul_le_pow (a := -(N : ℝ)⁻¹)
    (by linarith [inv_le_one_of_one_le₀ (show (1 : ℝ) ≤ N from Nat.one_le_cast.mpr hN)]) (2 * d)
  have hdl : (d : ℝ) ≤ l := Nat.cast_le.mpr hd
  rw [← sub_eq_add_neg] at h
  refine le_trans ?_ h
  push_cast
  rw [div_eq_mul_inv]
  nlinarith [inv_pos.mpr hN']

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ## Tabulating, checking and compressing one function -/

/-- Tabulating a function checks the log exactly when the function is consistent with it:
`E Pf = P E`. -/
theorem basisMatrix_ofFun_mul_logProjector (log : QueryLog (X →ₒ Y)) :
    basisMatrix (Database.ofFun : (X → Y) → Database X Y) *
        logProjector (fun (H : X → Y) (t : X) ↦ H t) log =
      checkProjector Y log * basisMatrix (Database.ofFun : (X → Y) → Database X Y) := by
  ext D H
  simp only [logProjector, checkProjector, mul_diagonal, diagonal_mul, basisMatrix_apply]
  by_cases hD : D = Database.ofFun H
  · subst hD
    simp [Database.ofFun]
  · simp [hD]

variable [Nonempty Y]

/-- Compressing carries the consistency projector of the functions to the compressed check
projector: `M Pf = P̂ M` for `M = S^{⊗X} E`. -/
theorem compressAll_mul_basisMatrix_mul_logProjector (log : QueryLog (X →ₒ Y)) :
    compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y) *
        logProjector (fun (H : X → Y) (t : X) ↦ H t) log =
      compressedCheckProjector log *
        (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y)) := by
  rw [Matrix.mul_assoc, basisMatrix_ofFun_mul_logProjector, compressedCheckProjector,
    Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (compressAll X Y)
      (compressAll X Y), compressAll_mul_self, Matrix.one_mul, ← Matrix.mul_assoc]

/-- **The sandwich identity for one function**: `Pf Mᴴ P M Pf = (1 - 1/N)^{2d} Pf`. -/
theorem logProjector_mul_compressAll_sandwich (log : QueryLog (X →ₒ Y)) :
    logProjector (fun (H : X → Y) (t : X) ↦ H t) log *
        (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y))ᴴ *
        checkProjector Y log * (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y)) *
        logProjector (fun (H : X → Y) (t : X) ↦ H t) log =
      (((1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * (loggedCells log).card) : ℝ) : ℂ) •
        logProjector (fun (H : X → Y) (t : X) ↦ H t) log := by
  set M := compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y)
  set Pf := logProjector (fun (H : X → Y) (t : X) ↦ H t) log
  have hMP : M * Pf = compressedCheckProjector log * M :=
    compressAll_mul_basisMatrix_mul_logProjector log
  have hPf : Pfᴴ = Pf := conjTranspose_logProjector _ _
  have hPM : Pf * Mᴴ = Mᴴ * compressedCheckProjector log := by
    calc Pf * Mᴴ = (M * Pf)ᴴ := by rw [Matrix.conjTranspose_mul M Pf, hPf]
      _ = _ := by rw [hMP, Matrix.conjTranspose_mul, conjTranspose_compressedCheckProjector]
  have hscal : (1 - (Fintype.card Y : ℂ)⁻¹) ^ (2 * (loggedCells log).card) =
      (((1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * (loggedCells log).card) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [Matrix.mul_assoc (Pf * Mᴴ * checkProjector Y log), hMP, hPM,
    ← Matrix.mul_assoc, Matrix.mul_assoc Mᴴ, Matrix.mul_assoc Mᴴ,
    compressedCheckProjector_mul_checkProjector_mul_compressedCheckProjector]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, ← hMP, ← Matrix.mul_assoc,
    conjTranspose_compressAll_mul_basisMatrix_mul_self, Matrix.one_mul, hscal]

/-! ## The reads and the runtimes -/

variable [AddCommGroup Y]

variable (X Y) in
/-- Classical reads of the random oracle on a held register `B`: the query `t` is the basis call
at `(t, 0)`, reporting the answer register. -/
noncomputable def qromReadImpl (B : QReg) : QueryImpl (X →ₒ Y) (QComp (qromSpec X Y) B B) :=
  fun t ↦ QComp.callBasis (spec := qromSpec X Y) () B (t, 0) fun o _ ↦ o.2

variable (X Y) in
/-- The purified random oracle as an emulated oracle: the register holds the function, started
in the uniform superposition, and the port applies its table oracle. Its runtime is
`Quantum.purifiedRuntime X Y`. -/
noncomputable def purifiedEmulated : EmulatedOracle Unit fun _ ↦ QReg.of (X × Y) where
  S := QReg.of (X → Y)
  init := uniformFunctionState X Y
  U _ := tableOracle (id : (X → Y) → X → Y)
  unitary _ := mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)

/-- Against the purified oracle, a classical read reporting `c` projects onto the functions
answering `c`. -/
theorem branch_run₂_qromReadImpl (B : QReg) (t : X) (c : Y) :
    ((purifiedRuntime X Y).run₂ .instruments (qromReadImpl X Y B t)).branch c =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        readProjector (fun (H : X → Y) (t : X) ↦ H t) t c) := by
  change ((purifiedEmulated X Y).toRuntime.run₂ .instruments
    (QComp.callBasis (spec := uSpec Unit fun _ ↦ QReg.of (X × Y)) () B (t, 0)
      fun o _ ↦ o.2)).branch c = _
  rw [EmulatedOracle.branch_run₂_callBasis]
  exact sum_conj_submatrix_tableOracle B id t c

omit [Nonempty Y] in
/-- Tabulating and compressing intertwines the purified runtime with the compressed runtime. -/
theorem compressedRuntime_step_intertwine (i : Unit) (r : Unit) :
    ((compressedRuntime X Y).step i).branch r ∘ₗ
        (MatrixMap.conj (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y))
          ).amplifyLeft ((qromSpec X Y).In i) =
      (MatrixMap.conj (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y))
          ).amplifyLeft ((qromSpec X Y).Out i) ∘ₗ ((purifiedRuntime X Y).step i).branch r := by
  change MatrixMap.conj (compressedOracle X Y) ∘ₗ
      (MatrixMap.conj (compressAll X Y * basisMatrix Database.ofFun)).amplifyLeft (X × Y) =
    (MatrixMap.conj (compressAll X Y * basisMatrix Database.ofFun)).amplifyLeft (X × Y) ∘ₗ
      MatrixMap.conj (tableOracle (id : (X → Y) → X → Y))
  rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
    compressedOracle_mul_one_kronecker_compressAll_mul_basisMatrix]

/-! ## The fundamental lemma for one function -/

/-- **Classical reads of a compressed random oracle are recorded, up to `2 l / |Y|`.** A program
`x` over the random oracle `X → Y`, followed at each leaf `p` by classical reads `oa p` making at
most `l` queries: every event `E` of the leaf, the result and the read log has probability, in the
quantum random-oracle model, at most its probability jointly with the measured compressed
database holding every logged answer at its point, plus `2 l / |Y|`. -/
theorem qromEvalDistMap_withReads_le {W : QReg → Type} {A : QReg} {β : Type}
    (x : QuantumComp LocalSig.instruments.{0} (qromSpec X Y) W A)
    (oa : (Σ u, W u) → OracleComp (X →ₒ Y) β) {l : ℕ} (hl : ∀ p, IsTotalQueryBound (oa p) l)
    (ρ : SubState A) (E : (Σ u, W u × β × QueryLog (X →ₒ Y)) → Prop) [DecidablePred E] :
    qromEvalDistMap .instruments (withReads x (qromReadImpl X Y) oa) ρ
        (fun _ q ↦ decide (E q)) {true} ≤
      jointLaw (compressedRuntime X Y) .instruments (withReads x (qromReadImpl X Y) oa) ρ
          (fun q D ↦ decide (E q ∧ ∀ e ∈ q.2.2.2, D e.1 = some e.2)) {true} +
        ENNReal.ofReal (2 * l / Fintype.card Y) := by
  rw [← outcomeLawWith_compressedRuntime]
  exact evalDistMap_withReads_le (purifiedRuntime X Y) (compressedRuntime X Y)
    (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y))
    conjTranspose_compressAll_mul_basisMatrix_mul_self compressedRuntime_step_intertwine
    conj_compressAll_mul_basisMatrix_uniformFunctionState (fun (H : X → Y) (t : X) ↦ H t)
    (qromReadImpl X Y) branch_run₂_qromReadImpl (fun log D ↦ ∀ e ∈ log, D e.1 = some e.2)
    (fun log ↦ (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * (loggedCells log).card))
    logProjector_mul_compressAll_sandwich x oa ρ _
    (fun p r hr ↦ one_sub_le_one_sub_inv_pow _ Fintype.card_pos _ _
      ((card_loggedCells_le_length _).trans (hr.length_le (hl p)))) E

end Quantum.Sponge

end
