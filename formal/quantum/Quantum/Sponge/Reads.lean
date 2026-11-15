module

public import Quantum.Sponge.Reads.Single
public import Quantum.Sponge.Oracle.Runtime

@[expose] public section

/-!
# Classical reads of the sponge's three compressed oracles

The fundamental-lemma step (Lemma 4.14 and Corollary 4.15 of Alagic, Carolan, Majenz and Tokat,
ePrint 2025/731) for the three random functions `h : Z → X` and `k, k' : X → Z`. A program `x`
over `spongeSpec X Z` is followed at each leaf `p` by a classical, possibly adaptive, algorithm
`oa p` over the classical oracles of `h`, `k` and `k'` (`spongeOSpec`), each query answered by a
basis call (`spongeReadImpl`); `withReads x spongeReadImpl oa` keeps the leaf, the result and the
log of the reads. If `oa p` makes at most `l_h`, `l_k`, `l_k'` queries to `h`, `k`, `k'` on every
path, then every event `E` of the leaf, result and log has probability, with uniform
`(h, k, k')`, at most its probability jointly with "the measured databases hold every logged
answer" (`DbReg.Agrees`), under the joint law of the three compressed oracles and their measured
databases (`spongeJointLaw`), plus `2 (l_h / |X| + (l_k + l_k') / |Z|)`
(`spongeEvalDistMap_withReads_le`).

The proof is that of `Quantum.Sponge.qromEvalDistMap_withReads_le`, factor by factor: the
consistency projectors and the compression of the three databases are tensor products, so the
sandwich scalar is the product `(1 - 1/|X|)^{2 d_h} (1 - 1/|Z|)^{2 d_k} (1 - 1/|Z|)^{2 d_k'}` of the
three one-function scalars (`sponge_sandwich`).
-/

open Matrix MeasureTheory OracleSpec OracleComp
open scoped Kronecker ENNReal

universe u v w

namespace Quantum.Sponge

open Quantum

/-! ## The classical oracles of `h`, `k` and `k'` -/

/-- A classical query of one of the three functions: `h` at `z : Z`, `k` or `k'` at `x : X`. -/
inductive SpongeQuery (X Z : Type) where
  /-- A query of `h : Z → X`. -/
  | h (z : Z)
  /-- A query of `k : X → Z`. -/
  | k (x : X)
  /-- A query of `k' : X → Z`. -/
  | k' (x : X)
  deriving DecidableEq

/-- The port that a classical query reads. -/
def SpongeQuery.port {X Z : Type} : SpongeQuery X Z → SpongePort
  | .h _ => .h
  | .k _ => .k
  | .k' _ => .k'

/-- The classical oracles of `h`, `k` and `k'`: a query of `h` is answered in `X`, a query of
`k` or `k'` in `Z`. -/
@[reducible] def spongeOSpec (X Z : Type) : OracleSpec (SpongeQuery X Z)
  | .h _ => X
  | .k _ => Z
  | .k' _ => Z

instance {X Z : Type} [DecidableEq X] [DecidableEq Z] (t : SpongeQuery X Z) :
    DecidableEq (spongeOSpec X Z t) :=
  match t with
  | .h _ => inferInstanceAs (DecidableEq X)
  | .k _ => inferInstanceAs (DecidableEq Z)
  | .k' _ => inferInstanceAs (DecidableEq Z)

variable {X Z : Type}

/-- The answer of the functions `t = (h, k, k')` to a classical query. -/
def spongeAns (t : (Z → X) × (X → Z) × (X → Z)) : (q : SpongeQuery X Z) → spongeOSpec X Z q
  | .h z => t.1 z
  | .k x => t.2.1 x
  | .k' x => t.2.2 x

/-- The cell of the databases `D` that a classical query reads. -/
def dbAns (D : DbReg X Z) : (q : SpongeQuery X Z) → Option (spongeOSpec X Z q)
  | .h z => D.1 z
  | .k x => D.2.1 x
  | .k' x => D.2.2 x

/-- The databases `D` hold every answer of the log `log` at its point. -/
def DbReg.Agrees (log : QueryLog (spongeOSpec X Z)) (D : DbReg X Z) : Prop :=
  ∀ e ∈ log, dbAns D e.1 = some e.2

instance [DecidableEq X] [DecidableEq Z] (log : QueryLog (spongeOSpec X Z)) :
    DecidablePred (DbReg.Agrees log) :=
  fun D ↦ inferInstanceAs (Decidable (∀ e ∈ log, dbAns D e.1 = some e.2))

/-! ## Splitting a log by function -/

/-- The entries of `h` in a log entry. -/
def toLogH : (e : (q : SpongeQuery X Z) × spongeOSpec X Z q) → Option ((_ : Z) × X)
  | ⟨.h z, a⟩ => some ⟨z, a⟩
  | ⟨.k _, _⟩ => none
  | ⟨.k' _, _⟩ => none

/-- The entries of `k` in a log entry. -/
def toLogK : (e : (q : SpongeQuery X Z) × spongeOSpec X Z q) → Option ((_ : X) × Z)
  | ⟨.h _, _⟩ => none
  | ⟨.k x, a⟩ => some ⟨x, a⟩
  | ⟨.k' _, _⟩ => none

/-- The entries of `k'` in a log entry. -/
def toLogK' : (e : (q : SpongeQuery X Z) × spongeOSpec X Z q) → Option ((_ : X) × Z)
  | ⟨.h _, _⟩ => none
  | ⟨.k _, _⟩ => none
  | ⟨.k' x, a⟩ => some ⟨x, a⟩

/-- A property of every entry of a log is the property of every entry of its three parts. -/
theorem forall_mem_iff_split (log : QueryLog (spongeOSpec X Z))
    (P : ((q : SpongeQuery X Z) × spongeOSpec X Z q) → Prop) (Ph : Z → X → Prop)
    (Pk Pk' : X → Z → Prop) (hh : ∀ z a, P ⟨.h z, a⟩ ↔ Ph z a)
    (hk : ∀ x a, P ⟨.k x, a⟩ ↔ Pk x a) (hk' : ∀ x a, P ⟨.k' x, a⟩ ↔ Pk' x a) :
    (∀ e ∈ log, P e) ↔
      (∀ e ∈ log.filterMap toLogH, Ph e.1 e.2) ∧ (∀ e ∈ log.filterMap toLogK, Pk e.1 e.2) ∧
        ∀ e ∈ log.filterMap toLogK', Pk' e.1 e.2 := by
  simp only [List.mem_filterMap]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, b⟩ ⟨⟨q, a⟩, he, hq⟩
      cases q <;> simp only [toLogH, reduceCtorEq, Option.some.injEq] at hq
      cases hq
      exact (hh _ _).mp (h _ he)
    · rintro ⟨y, b⟩ ⟨⟨q, a⟩, he, hq⟩
      cases q <;> simp only [toLogK, reduceCtorEq, Option.some.injEq] at hq
      cases hq
      exact (hk _ _).mp (h _ he)
    · rintro ⟨y, b⟩ ⟨⟨q, a⟩, he, hq⟩
      cases q <;> simp only [toLogK', reduceCtorEq, Option.some.injEq] at hq
      cases hq
      exact (hk' _ _).mp (h _ he)
  · rintro ⟨h₁, h₂, h₃⟩ ⟨q, a⟩ he
    cases q
    · exact (hh _ _).mpr (h₁ ⟨_, a⟩ ⟨_, he, rfl⟩)
    · exact (hk _ _).mpr (h₂ ⟨_, a⟩ ⟨_, he, rfl⟩)
    · exact (hk' _ _).mpr (h₃ ⟨_, a⟩ ⟨_, he, rfl⟩)

/-- The number of reads of one port in a log. -/
def readCount (port : SpongePort) (log : QueryLog (spongeOSpec X Z)) : ℕ :=
  log.countP fun e ↦ decide (e.1.port = port)

theorem length_filterMap_toLogH (log : QueryLog (spongeOSpec X Z)) :
    (log.filterMap toLogH).length = readCount .h log := by
  rw [List.length_filterMap_eq_countP, readCount]
  refine List.countP_congr fun ⟨q, a⟩ _ ↦ ?_
  cases q <;> simp [toLogH, SpongeQuery.port]

theorem length_filterMap_toLogK (log : QueryLog (spongeOSpec X Z)) :
    (log.filterMap toLogK).length = readCount .k log := by
  rw [List.length_filterMap_eq_countP, readCount]
  refine List.countP_congr fun ⟨q, a⟩ _ ↦ ?_
  cases q <;> simp [toLogK, SpongeQuery.port]

theorem length_filterMap_toLogK' (log : QueryLog (spongeOSpec X Z)) :
    (log.filterMap toLogK').length = readCount .k' log := by
  rw [List.length_filterMap_eq_countP, readCount]
  refine List.countP_congr fun ⟨q, a⟩ _ ↦ ?_
  cases q <;> simp [toLogK', SpongeQuery.port]

theorem ite_eq_ite_mul_ite_mul_ite {P a b c : Prop} {_ : Decidable P} {_ : Decidable a}
    {_ : Decidable b} {_ : Decidable c} (h : P ↔ a ∧ b ∧ c) :
    (if P then (1 : ℂ) else 0) =
      (if a then 1 else 0) * ((if b then 1 else 0) * (if c then 1 else 0)) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp_all

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-! ## The projectors factor over the three functions -/

/-- The functions consistent with a log are those whose three parts are consistent with its three
parts. -/
theorem logProjector_spongeAns (log : QueryLog (spongeOSpec X Z)) :
    logProjector spongeAns log =
      logProjector (fun (H : Z → X) (t : Z) ↦ H t) (log.filterMap toLogH : QueryLog (Z →ₒ X)) ⊗ₖ
        (logProjector (fun (H : X → Z) (t : X) ↦ H t)
            (log.filterMap toLogK : QueryLog (X →ₒ Z)) ⊗ₖ
          logProjector (fun (H : X → Z) (t : X) ↦ H t)
            (log.filterMap toLogK' : QueryLog (X →ₒ Z))) := by
  simp only [logProjector, diagonal_kronecker_diagonal]
  congr 1
  funext t
  exact ite_eq_ite_mul_ite_mul_ite (forall_mem_iff_split log (fun e ↦ spongeAns t e.1 = e.2)
    (fun z a ↦ t.1 z = a) (fun x a ↦ t.2.1 x = a) (fun x a ↦ t.2.2 x = a) (fun _ _ ↦ Iff.rfl)
    (fun _ _ ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl))

/-- The databases agreeing with a log are those whose three databases hold its three parts. -/
theorem diagonal_agrees (log : QueryLog (spongeOSpec X Z)) :
    diagonal (fun D : DbReg X Z ↦ if DbReg.Agrees log D then (1 : ℂ) else 0) =
      checkProjector X (log.filterMap toLogH : QueryLog (Z →ₒ X)) ⊗ₖ
        (checkProjector Z (log.filterMap toLogK : QueryLog (X →ₒ Z)) ⊗ₖ
          checkProjector Z (log.filterMap toLogK' : QueryLog (X →ₒ Z))) := by
  simp only [checkProjector, diagonal_kronecker_diagonal]
  congr 1
  funext D
  exact ite_eq_ite_mul_ite_mul_ite (forall_mem_iff_split log (fun e ↦ dbAns D e.1 = some e.2)
    (fun z a ↦ D.1 z = some a) (fun x a ↦ D.2.1 x = some a) (fun x a ↦ D.2.2 x = some a)
    (fun _ _ ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl))

/-- The consistency scalar of the three functions. -/
noncomputable def spongeScalar (X Z : Type) [Fintype X] [DecidableEq X] [Fintype Z]
    [DecidableEq Z] (log : QueryLog (spongeOSpec X Z)) : ℝ :=
  (1 - (Fintype.card X : ℝ)⁻¹) ^ (2 * (loggedCells (log.filterMap toLogH : QueryLog (Z →ₒ X))).card) *
    ((1 - (Fintype.card Z : ℝ)⁻¹) ^
        (2 * (loggedCells (log.filterMap toLogK : QueryLog (X →ₒ Z))).card) *
      (1 - (Fintype.card Z : ℝ)⁻¹) ^
        (2 * (loggedCells (log.filterMap toLogK' : QueryLog (X →ₒ Z))).card))

variable [Nonempty X] [Nonempty Z]

/-- **The sandwich identity for the three functions.** -/
theorem sponge_sandwich (log : QueryLog (spongeOSpec X Z)) :
    logProjector spongeAns log * (compressDbs X Z * basisMatrix (ofFunDbs (X := X) (Z := Z)))ᴴ *
        diagonal (fun D : DbReg X Z ↦ if DbReg.Agrees log D then (1 : ℂ) else 0) *
        (compressDbs X Z * basisMatrix (ofFunDbs (X := X) (Z := Z))) *
        logProjector spongeAns log =
      (spongeScalar X Z log : ℂ) • logProjector spongeAns log := by
  rw [logProjector_spongeAns, diagonal_agrees, basisMatrix_ofFunDbs, compressDbs,
    ← mul_kronecker_mul, ← mul_kronecker_mul]
  simp only [conjTranspose_kronecker, ← mul_kronecker_mul]
  rw [logProjector_mul_compressAll_sandwich, logProjector_mul_compressAll_sandwich,
    logProjector_mul_compressAll_sandwich]
  simp only [kronecker_smul, smul_kronecker, smul_smul, spongeScalar]
  congr 1
  push_cast
  ring

/-! ## The reads and the runtimes -/

variable [AddCommGroup X] [AddCommGroup Z]

variable (X Z) in
/-- Classical reads of `h`, `k` and `k'` on a held register `B`: a query is the basis call of its
port at `(point, 0)`, reporting the answer register. -/
noncomputable def spongeReadImpl (B : QReg) :
    QueryImpl (spongeOSpec X Z) (QComp (spongeSpec X Z) B B)
  | .h z => QComp.callBasis (spec := spongeSpec X Z) .h B (z, (0 : X)) fun o _ ↦ o.2
  | .k x => QComp.callBasis (spec := spongeSpec X Z) .k B (x, (0 : Z)) fun o _ ↦ o.2
  | .k' x => QComp.callBasis (spec := spongeSpec X Z) .k' B (x, (0 : Z)) fun o _ ↦ o.2

omit [Nonempty X] [Nonempty Z] in
/-- Against the purified oracle, a classical read reporting `c` projects onto the triples of
functions answering `c`. -/
theorem branch_run₂_spongeReadImpl (B : QReg) (q : SpongeQuery X Z) (c : spongeOSpec X Z q) :
    ((spongePurifiedRuntime X Z).run₂ .instruments (spongeReadImpl X Z B q)).branch c =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ readProjector spongeAns q c) := by
  cases q with
  | h z =>
    change ((spongePurified X Z).toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec SpongePort (spongeIn X Z)) .h B (z, (0 : X))
        fun o _ ↦ o.2)).branch c = _
    rw [EmulatedOracle.branch_run₂_callBasis]
    exact sum_conj_submatrix_tableOracle B (fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.1) z c
  | k x =>
    change ((spongePurified X Z).toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec SpongePort (spongeIn X Z)) .k B (x, (0 : Z))
        fun o _ ↦ o.2)).branch c = _
    rw [EmulatedOracle.branch_run₂_callBasis]
    exact sum_conj_submatrix_tableOracle B (fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.2.1) x c
  | k' x =>
    change ((spongePurified X Z).toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec SpongePort (spongeIn X Z)) .k' B (x, (0 : Z))
        fun o _ ↦ o.2)).branch c = _
    rw [EmulatedOracle.branch_run₂_callBasis]
    exact sum_conj_submatrix_tableOracle B (fun t : (Z → X) × (X → Z) × (X → Z) ↦ t.2.2) x c

omit [Nonempty X] [Nonempty Z] in
/-- Tabulating and compressing intertwines the purified runtime with the compressed runtime. -/
theorem spongeCompressedRuntime_step_intertwine (i : SpongePort) (r : Unit) :
    ((spongeCompressedRuntime X Z).step i).branch r ∘ₗ
        (MatrixMap.conj (tabulateDbs X Z)).amplifyLeft ((spongeSpec X Z).In i) =
      (MatrixMap.conj (tabulateDbs X Z)).amplifyLeft ((spongeSpec X Z).Out i) ∘ₗ
        ((spongePurifiedRuntime X Z).step i).branch r := by
  change MatrixMap.conj ((spongeCompressed X Z).U i) ∘ₗ
      (MatrixMap.conj (tabulateDbs X Z)).amplifyLeft (spongeIn X Z i) =
    (MatrixMap.conj (tabulateDbs X Z)).amplifyLeft (spongeIn X Z i) ∘ₗ
      MatrixMap.conj ((spongePurified X Z).U i)
  rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
    spongeCompressed_U_mul_one_kronecker]

omit [Nonempty X] [Nonempty Z] in
/-- **The budget of a program followed by reads**: the budget of the program plus, per port, the
number of reads of that port. -/
theorem isQueryBound_withReads_spongeReadImpl {W : QReg → Type} {A : QReg} {β : Type}
    {x : QuantumComp LocalSig.instruments.{0} (spongeSpec X Z) W A} {b : SpongePort → ℕ}
    (hx : x.IsQueryBound b) (oa : (Σ u, W u) → OracleComp (spongeOSpec X Z) β)
    (lb : SpongePort → ℕ) (hl : ∀ p i, IsQueryBoundP (oa p) (fun q ↦ q.port = i) (lb i)) :
    (withReads x (spongeReadImpl X Z) oa).IsQueryBound (b + lb) :=
  isQueryBound_withReads SpongeQuery.port (spongeReadImpl X Z)
    (fun B q ↦ by cases q <;> exact QComp.isQueryBound_callBasis_single _ _ _ _) hx oa lb hl

/-! ## The fundamental lemma for the sponge's three functions -/

/-- The error of the reads: `2 (l_h / |X| + (l_k + l_k') / |Z|)`. -/
noncomputable def readError (X Z : Type) [Fintype X] [Fintype Z] (lh lk lk' : ℕ) : ℝ :=
  2 * (lh / Fintype.card X + (lk + lk') / Fintype.card Z)

omit [AddCommGroup X] [AddCommGroup Z] in
/-- A log with at most `l_h`, `l_k`, `l_k'` reads of `h`, `k`, `k'` has consistency scalar at least
`1 - readError`. -/
theorem one_sub_readError_le_spongeScalar {lh lk lk' : ℕ} {log : QueryLog (spongeOSpec X Z)}
    (hh : readCount .h log ≤ lh) (hk : readCount .k log ≤ lk) (hk' : readCount .k' log ≤ lk') :
    1 - readError X Z lh lk lk' ≤ spongeScalar X Z log := by
  have h₁ := one_sub_le_one_sub_inv_pow (Fintype.card X) Fintype.card_pos _ lh
    ((card_loggedCells_le_length _).trans ((length_filterMap_toLogH log).trans_le hh))
  have h₂ := one_sub_le_one_sub_inv_pow (Fintype.card Z) Fintype.card_pos _ lk
    ((card_loggedCells_le_length _).trans ((length_filterMap_toLogK log).trans_le hk))
  have h₃ := one_sub_le_one_sub_inv_pow (Fintype.card Z) Fintype.card_pos _ lk'
    ((card_loggedCells_le_length _).trans ((length_filterMap_toLogK' log).trans_le hk'))
  have hX : (Fintype.card X : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr Fintype.card_pos)
  have hZ : (Fintype.card Z : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr Fintype.card_pos)
  set a := (1 - (Fintype.card X : ℝ)⁻¹) ^
    (2 * (loggedCells (log.filterMap toLogH : QueryLog (Z →ₒ X))).card)
  set b := (1 - (Fintype.card Z : ℝ)⁻¹) ^
    (2 * (loggedCells (log.filterMap toLogK : QueryLog (X →ₒ Z))).card)
  set c := (1 - (Fintype.card Z : ℝ)⁻¹) ^
    (2 * (loggedCells (log.filterMap toLogK' : QueryLog (X →ₒ Z))).card)
  have ha0 : 0 ≤ a := pow_nonneg (by linarith) _
  have hb0 : 0 ≤ b := pow_nonneg (by linarith) _
  have hc0 : 0 ≤ c := pow_nonneg (by linarith) _
  have hX0 : (0 : ℝ) ≤ (Fintype.card X : ℝ)⁻¹ := by positivity
  have hZ0 : (0 : ℝ) ≤ (Fintype.card Z : ℝ)⁻¹ := by positivity
  have ha1 : a ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hb1 : b ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hc1 : c ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hbc : 1 - (2 * lk / Fintype.card Z + 2 * lk' / Fintype.card Z) ≤ b * c := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1)]
  have habc : 1 - (2 * lh / Fintype.card X + (2 * lk / Fintype.card Z +
      2 * lk' / Fintype.card Z)) ≤ a * (b * c) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ((mul_le_mul hb1 hc1 hc0 zero_le_one).trans_eq (one_mul 1)))]
  rw [spongeScalar, readError]
  refine le_trans (le_of_eq ?_) habc
  ring

/-- **Classical reads of the sponge's compressed oracles are recorded.** A program `x` over the
three random functions of the sponge, followed at each leaf `p` by classical reads `oa p` making
at most `l_h`, `l_k`, `l_k'` queries of `h`, `k`, `k'` on every path: every event `E` of the leaf,
the result and the read log has probability, with uniform `(h, k, k')`, at most its probability
jointly with the measured databases of the three compressed oracles holding every logged answer
at its point, plus `2 (l_h / |X| + (l_k + l_k') / |Z|)`. -/
theorem spongeEvalDistMap_withReads_le {W : QReg → Type} {A : QReg} {β : Type}
    (x : QuantumComp LocalSig.instruments.{0} (spongeSpec X Z) W A)
    (oa : (Σ u, W u) → OracleComp (spongeOSpec X Z) β) {lh lk lk' : ℕ}
    (hh : ∀ p, IsQueryBoundP (oa p) (fun q ↦ q.port = .h) lh)
    (hk : ∀ p, IsQueryBoundP (oa p) (fun q ↦ q.port = .k) lk)
    (hk' : ∀ p, IsQueryBoundP (oa p) (fun q ↦ q.port = .k') lk')
    (ρ : SubState A) (E : (Σ u, W u × β × QueryLog (spongeOSpec X Z)) → Prop)
    [DecidablePred E] :
    spongeEvalDistMap .instruments (withReads x (spongeReadImpl X Z) oa) ρ
        (fun _ q ↦ decide (E q)) {true} ≤
      jointLaw (spongeCompressedRuntime X Z) .instruments (withReads x (spongeReadImpl X Z) oa) ρ
          (fun q D ↦ decide (E q ∧ DbReg.Agrees q.2.2.2 D)) {true} +
        ENNReal.ofReal (readError X Z lh lk lk') := by
  rw [← evalDistMap_spongeCompressedRuntime]
  exact evalDistMap_withReads_le (spongePurifiedRuntime X Z) (spongeCompressedRuntime X Z)
    (tabulateDbs X Z) conjTranspose_tabulateDbs_mul_self spongeCompressedRuntime_step_intertwine
    conj_tabulateDbs_init spongeAns (spongeReadImpl X Z)
    branch_run₂_spongeReadImpl DbReg.Agrees (spongeScalar X Z) sponge_sandwich x oa ρ _
    (fun p r hr ↦ one_sub_readError_le_spongeScalar (hr.countP_le (hh p))
      (hr.countP_le (hk p)) (hr.countP_le (hk' p))) E

end Quantum.Sponge

end
