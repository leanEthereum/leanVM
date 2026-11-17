module

public import Quantum.Par.LockstepRounds
public import Quantum.Qrom.Xmss.DepthPar

@[expose] public section

/-!
# Hidden masses of the lockstep round

The summed hidden masses of the calls of `lockRoundR` (a round counted as the sum over its slots)
are those of the serialized simulation `simulate π (seqCalls dir E ℓ post)`, against every runtime
that reads its functions in the basis of a unitary `U` (`IsReadRuntime`), for hidden sets that
depend only on a call's input and on the part of the runtime register that `U` keeps
(`totalWeight_lockRoundR_eq`, `totalWeight_diagMass_lockRoundR_eq`).

* **Counts** (`diagW`): a count `n` of the basis states weighs `∑ a, n a · ρ_aa`; a diagonal mass
  is the count of the set's indicator (`diagMass_eq_diagW`).
* **Programs weighing as a count** (`WeighsAs`): a program built of basis maps and calls of basis
  steps weighs, for counts `c` of the calls' inputs, as a count of its initial basis states
  (`WeighsAs.bind`, `WeighsAs.queryBind`).
* **Serialization** (`parCount`, `totalWeight_parCount_eq`): for steps keeping the counts
  (`KeepsCounts`), a round's count (the sum over its slots) is the summed count of its calls.
* **Read basis** (`keepsCounts_of_isReadRuntime`, `totalWeight_eq_read`): counts kept by `U` are
  the counts against the read runtime from the state conjugated by `U`.
* **The two programs against a read runtime** (`weighsAs_simulate_seqCalls`,
  `weighsAs_lockRoundR`): both weigh as the sum over the slots of the counts of their six calls
  (`simCount`).
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

universe u v w

namespace Quantum.Par

open Quantum Quantum.Sponge QuantumRuntime SubInstrument Quantum.Xmss.Hybrid

/-! ## Counts of basis states -/

section diag

variable {α β : Type} [Fintype α] [Fintype β]

/-- **The weight of a count** `n` of the basis states: `∑ a, n a · ρ_aa`. -/
noncomputable def diagW (n : α → ℕ) (σ : Matrix α α ℂ) : ℝ≥0∞ :=
  ∑ a, (n a : ℝ≥0∞) * ENNReal.ofReal (σ a a).re

theorem diagW_zero (σ : Matrix α α ℂ) : diagW (0 : α → ℕ) σ = 0 := by
  simp [diagW]

theorem diagW_add (n₁ n₂ : α → ℕ) (σ : Matrix α α ℂ) :
    diagW (n₁ + n₂) σ = diagW n₁ σ + diagW n₂ σ := by
  simp only [diagW, Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem diagW_congr {n₁ n₂ : α → ℕ} (h : ∀ a, n₁ a = n₂ a) (σ : Matrix α α ℂ) :
    diagW n₁ σ = diagW n₂ σ := by
  rw [funext h]

theorem sum_diagW {ι : Type} (s : Finset ι) (n : ι → α → ℕ) (σ : Matrix α α ℂ) :
    ∑ j ∈ s, diagW (n j) σ = diagW (fun a ↦ ∑ j ∈ s, n j a) σ := by
  simp only [diagW, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem diagMass_eq_diagW (C : Set α) (σ : Matrix α α ℂ) :
    diagMass C σ = diagW (C.indicator 1) σ := by
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases h : a ∈ C <;> simp [h]

variable [DecidableEq α] [DecidableEq β]

omit [Fintype β] in
theorem conj_basisMatrix_apply_self {f : α → β} (hf : Function.Injective f) (σ : Matrix α α ℂ)
    (a : α) : MatrixMap.conj (basisMatrix f) σ (f a) (f a) = σ a a := by
  simp [MatrixMap.conj_apply, Matrix.mul_apply, basisMatrix_apply, hf.eq_iff]

omit [Fintype β] [DecidableEq α] in
theorem conj_basisMatrix_apply_of_notMem (f : α → β) (σ : Matrix α α ℂ) {b : β}
    (hb : b ∉ Set.range f) : MatrixMap.conj (basisMatrix f) σ b b = 0 := by
  have h : ∀ a, b ≠ f a := fun a h ↦ hb ⟨a, h.symm⟩
  simp [MatrixMap.conj_apply, Matrix.mul_apply, basisMatrix_apply, h]

/-- The count after a basis injection is the count composed with it. -/
theorem diagW_conj_basisMatrix {f : α → β} (hf : Function.Injective f) (n : β → ℕ)
    (σ : Matrix α α ℂ) : diagW n (MatrixMap.conj (basisMatrix f) σ) = diagW (n ∘ f) σ := by
  refine (Fintype.sum_of_injective f hf _ _ (fun b hb ↦ ?_) fun a ↦ ?_).symm
  · rw [conj_basisMatrix_apply_of_notMem f σ hb, Complex.zero_re, ENNReal.ofReal_zero, mul_zero]
  · rw [conj_basisMatrix_apply_self hf, Function.comp_apply]

/-- **The count of a call's input**: the count of the states by their exposed part and runtime
register. -/
theorem diagW_callInput {A J E D : Type} [Fintype A] [DecidableEq A] [Fintype J]
    [DecidableEq J] [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D] (ℓ : A ≃ J × E)
    (n : J × D → ℕ) {ρ : Matrix (A × D) (A × D) ℂ} (hρ : ρ.PosSemidef) :
    diagW n (callInput ℓ D ρ) = diagW (fun p : A × D ↦ n ((ℓ p.1).1, p.2)) ρ := by
  have hd : ∀ p, 0 ≤ (ρ p p).re := fun _ ↦ (Complex.nonneg_iff.1 hρ.diag_nonneg).1
  have hent : ∀ q, callInput ℓ D ρ q q =
      ∑ e, ρ ((queryEquivIn ℓ D).symm (q, e)) ((queryEquivIn ℓ D).symm (q, e)) := fun q ↦ by
    simp only [callInput, LinearMap.comp_apply, MatrixMap.traceRight_apply,
      SubInstrument.relabel_branch_apply, Matrix.submatrix_apply]
  have h1 : ∀ q, (n q : ℝ≥0∞) * ENNReal.ofReal (callInput ℓ D ρ q q).re =
      ∑ e, (n q : ℝ≥0∞) * ENNReal.ofReal
        (ρ ((queryEquivIn ℓ D).symm (q, e)) ((queryEquivIn ℓ D).symm (q, e))).re := fun q ↦ by
    rw [hent, Complex.re_sum, ENNReal.ofReal_sum_of_nonneg fun e _ ↦ hd _, Finset.mul_sum]
  rw [diagW, diagW, Finset.sum_congr rfl fun q _ ↦ h1 q]
  refine (Fintype.sum_prod_type (fun x : (J × D) × E ↦ (n x.1 : ℝ≥0∞) * ENNReal.ofReal
    (ρ ((queryEquivIn ℓ D).symm x) ((queryEquivIn ℓ D).symm x)).re)).symm.trans ?_
  refine Fintype.sum_equiv (queryEquivIn ℓ D).symm _ _ fun x ↦ ?_
  obtain ⟨p, rfl⟩ := (queryEquivIn ℓ D).surjective x
  rw [Equiv.symm_apply_apply]
  rfl

/-- The square roots of a count, on the diagonal. -/
noncomputable def sqrtCount (n : α → ℕ) : Matrix α α ℂ :=
  diagonal fun a ↦ ((Real.sqrt (n a) : ℝ) : ℂ)

/-- The weight of a count is the trace weight of the square roots of the count, on positive
semidefinite operators. -/
theorem diagW_eq_ofReal_trace (n : α → ℕ) {σ : Matrix α α ℂ} (hσ : σ.PosSemidef) :
    diagW n σ = ENNReal.ofReal (MatrixMap.conj (sqrtCount n) σ).trace.re := by
  have hd : ∀ a, 0 ≤ (σ a a).re := fun _ ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hK : (sqrtCount n)ᴴ * sqrtCount n = diagonal fun a ↦ ((n a : ℝ) : ℂ) := by
    rw [sqrtCount, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext a
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have ht : (diagonal (fun a ↦ ((n a : ℝ) : ℂ)) * σ).trace.re = ∑ a, (n a : ℝ) * (σ a a).re := by
    simp only [Matrix.trace, Matrix.diag, diagonal_mul, Complex.re_sum, Complex.re_ofReal_mul]
  rw [MatrixMap.trace_conj_apply, hK, ht,
    ENNReal.ofReal_sum_of_nonneg fun a _ ↦ mul_nonneg (Nat.cast_nonneg _) (hd a), diagW]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end diag

/-! ## Summed counts of the calls -/

section weigh

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) (c : ∀ i, spec.In i × R.D → ℕ)

/-- Summed counts are summed trace weights of the square roots, from positive semidefinite
states. -/
theorem totalWeight_diagW_eq_conj {Ω : QReg → Type w} {A : QReg} (x : QuantumComp L spec Ω A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I (fun i ↦ diagW (c i)) x ρ =
      R.totalWeight I (fun i σ ↦ ENNReal.ofReal (MatrixMap.conj (sqrtCount (c i)) σ).trace.re) x
        ρ :=
  le_antisymm
    (totalWeight_le_totalWeight R I (fun i _ hσ ↦ (diagW_eq_ofReal_trace (c i) hσ).le) x hρ)
    (totalWeight_le_totalWeight R I (fun i _ hσ ↦ (diagW_eq_ofReal_trace (c i) hσ).ge) x hρ)

/-- **Summed counts add under sequencing.** -/
theorem totalWeight_diagW_bind {X Y : QReg → Type w} {A : QReg} (x : QuantumComp L spec X A)
    (k : ∀ u, X u → QuantumComp L spec Y u) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef) :
    R.totalWeight I (fun i ↦ diagW (c i)) (x.bind k) ρ =
      R.totalWeight I (fun i ↦ diagW (c i)) x ρ +
        ∑' p, R.totalWeight I (fun i ↦ diagW (c i)) (k p.1 p.2) ((R.run I x).branch p ρ) := by
  rw [totalWeight_diagW_eq_conj R I c _ hρ,
    R.totalWeight_bind I (Φ := fun i ↦ MatrixMap.conj (sqrtCount (c i)))
      (fun i ↦ MatrixMap.isCP_conj _) x k hρ, totalWeight_diagW_eq_conj R I c x hρ]
  exact congrArg (_ + ·) (tsum_congr fun p ↦ (totalWeight_diagW_eq_conj R I c _
    ((R.run I x).posSemidef_branch_apply _ hρ)).symm)

/-- **Summed counts add under sequencing of fixed-register programs.** -/
theorem totalWeight_diagW_bind₂ {A B B' : QReg} {α β : Type}
    (x : QuantumComp₂ L spec A B α) (k : α → QuantumComp₂ L spec B B' β)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I (fun i ↦ diagW (c i)) (x.bind k) ρ =
      R.totalWeight I (fun i ↦ diagW (c i)) x ρ +
        ∑' a, R.totalWeight I (fun i ↦ diagW (c i)) (k a) ((R.run₂ I x).branch a ρ) := by
  refine (totalWeight_diagW_bind R I c x
    (fun u (p : QuantumComp₂.Leaf B α u) ↦ p.casesOn fun h a ↦ h ▸ k a) hρ).trans
    (congrArg (_ + ·) ?_)
  rw [← (QuantumComp₂.leafEquiv B α).tsum_eq]
  rfl

/-- **A program weighs as a count** `n` of its initial basis states: against `R`, from every
positive semidefinite state, the summed counts `c` of the inputs of its calls are the weight of
`n`. -/
def WeighsAs {A B : QReg} {α : Type} (x : QuantumComp₂ LocalSig.instruments.{0} spec A B α)
    (n : A × R.D → ℕ) : Prop :=
  ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef →
    R.totalWeight .instruments (fun i ↦ diagW (c i)) x ρ = diagW n ρ

variable {R c}

theorem WeighsAs.congr {A B : QReg} {α : Type}
    {x : QuantumComp₂ LocalSig.instruments.{0} spec A B α} {n n' : A × R.D → ℕ}
    (hx : WeighsAs R c x n) (h : ∀ q, n q = n' q) : WeighsAs R c x n' := by
  rwa [← funext h]

variable (R c) in
theorem weighsAs_pure {A : QReg} {α : Type} (a : α) :
    WeighsAs R c (QuantumComp₂.pure a : QuantumComp₂ LocalSig.instruments.{0} spec A A α) 0 :=
  fun ρ _ ↦ (R.totalWeight_pure _ _ ρ).trans (diagW_zero ρ).symm

variable (R c) in
/-- A local operation with one outcome, then `pure ()`, counts nothing. -/
theorem weighsAs_primBind_pure {A B : QReg} (p : SubInstrument A B PUnit.{1}) :
    WeighsAs R c (QuantumComp₂.primBind (L := LocalSig.instruments.{0}) (spec := spec)
      ⟨PUnit, fun _ ↦ B, p⟩ fun _ ↦ QuantumComp₂.pure ()) 0 := fun ρ _ ↦ by
  refine (R.totalWeight_primBind _ _ _ ρ).trans (Eq.trans ?_ (diagW_zero ρ).symm)
  exact (tsum_congr fun _ ↦ R.totalWeight_pure _ _ _).trans tsum_zero

variable (R c) in
theorem weighsAs_isoGate {A B : QReg} (f : A → B) (hf : Function.Injective f) :
    WeighsAs R c (isoGate.{0} (spec := spec) f hf) 0 :=
  weighsAs_primBind_pure R c _

variable (R c) in
theorem weighsAs_coGate {A B : QReg} (f : B → A) (hf : Function.Injective f) :
    WeighsAs R c (coGate.{0} (spec := spec) f hf) 0 :=
  weighsAs_primBind_pure R c _

/-- **Sequencing**: the count of `x`, then the count of `y` after the basis map of `x`. -/
theorem WeighsAs.bind {A B C : QReg} {x : QuantumComp₂ LocalSig.instruments.{0} spec A B Unit}
    {y : Unit → QuantumComp₂ LocalSig.instruments.{0} spec B C Unit} {n₁ : A × R.D → ℕ}
    {n₂ : B × R.D → ℕ} {F : A × R.D → B × R.D} (hx : WeighsAs R c x n₁) (hF : RunsAs R x F)
    (hFi : Function.Injective F) (hy : WeighsAs R c (y ()) n₂) :
    WeighsAs R c (x.bind y) (n₁ + n₂ ∘ F) := fun ρ hρ ↦ by
  rw [totalWeight_diagW_bind₂ R .instruments c x y hρ, hx ρ hρ, tsum_fintype,
    Fintype.sum_unique, show (default : Unit) = () from rfl, hF,
    hy _ ((MatrixMap.isCP_conj _).posSemidef hρ), diagW_conj_basisMatrix hFi, diagW_add]

/-- **Sequencing with a continuation that counts nothing.** -/
theorem WeighsAs.bind_zero {A B C : QReg} {x : QuantumComp₂ LocalSig.instruments.{0} spec A B Unit}
    {y : Unit → QuantumComp₂ LocalSig.instruments.{0} spec B C Unit} {n : A × R.D → ℕ}
    (hx : WeighsAs R c x n) (hy : WeighsAs R c (y ()) 0) : WeighsAs R c (x.bind y) n :=
  fun ρ hρ ↦ by
  rw [totalWeight_diagW_bind₂ R .instruments c x y hρ, hx ρ hρ, tsum_fintype,
    Fintype.sum_unique, show (default : Unit) = () from rfl,
    hy _ ((R.run₂ .instruments x).posSemidef_branch_apply () hρ), diagW_zero, add_zero]

/-- `WeighsAs.bind` with the continuation's count stated for every unit. -/
theorem WeighsAs.bind' {A B C : QReg} {x : QuantumComp₂ LocalSig.instruments.{0} spec A B Unit}
    {y : Unit → QuantumComp₂ LocalSig.instruments.{0} spec B C Unit} {n₁ : A × R.D → ℕ}
    {n₂ : B × R.D → ℕ} {F : A × R.D → B × R.D} (hx : WeighsAs R c x n₁) (hF : RunsAs R x F)
    (hFi : Function.Injective F) (hy : ∀ u, WeighsAs R c (y u) n₂) :
    WeighsAs R c (x.bind y) (n₁ + n₂ ∘ F) :=
  hx.bind hF hFi (hy ())

/-- `WeighsAs.bind_zero` with the continuation's count stated for every unit. -/
theorem WeighsAs.bind_zero' {A B C : QReg}
    {x : QuantumComp₂ LocalSig.instruments.{0} spec A B Unit}
    {y : Unit → QuantumComp₂ LocalSig.instruments.{0} spec B C Unit} {n : A × R.D → ℕ}
    (hx : WeighsAs R c x n) (hy : ∀ u, WeighsAs R c (y u) 0) : WeighsAs R c (x.bind y) n :=
  hx.bind_zero (hy ())

/-- **A call of a basis step**, then a continuation: the count of the call's input, then the count
of the continuation after the call's basis map. -/
theorem WeighsAs.queryBind {i : spec.Port} [Unique (spec.Result i)]
    (g : spec.In i × R.D → spec.Out i × R.D) (hgi : Function.Injective g)
    (hg : ∀ r, (R.step i).branch r = MatrixMap.conj (basisMatrix g)) (E : QReg) {A C : QReg}
    (ℓ : A ≃ spec.In i × E)
    {y : spec.Result i → QuantumComp₂ LocalSig.instruments.{0} spec (QReg.of (spec.Out i × E))
      C Unit}
    {n : (spec.Out i × E) × R.D → ℕ} (hy : ∀ r, WeighsAs R c (y r) n) :
    WeighsAs R c (QuantumComp₂.queryBind i E ℓ y) (fun q ↦ c i ((ℓ q.1).1, q.2) +
      n ((QuantumRuntime.queryEquivOut (spec.Out i) R.D E ∘ Prod.map g id ∘
        QuantumRuntime.queryEquivIn ℓ R.D) q)) := fun ρ hρ ↦ by
  have hinj : Function.Injective (QuantumRuntime.queryEquivOut (spec.Out i) R.D E ∘
      Prod.map g id ∘ QuantumRuntime.queryEquivIn ℓ R.D) :=
    (Equiv.injective _).comp ((hgi.prodMap Function.injective_id).comp (Equiv.injective _))
  refine (R.totalWeight_queryBind _ i E ℓ y ρ).trans ?_
  rw [tsum_fintype, Fintype.sum_unique, branch_queryStep_of_basis R g (hg default) E ℓ,
    hy _ _ ((MatrixMap.isCP_conj _).posSemidef hρ), diagW_conj_basisMatrix hinj,
    diagW_callInput ℓ (c i) hρ, ← diagW_add]
  rfl

end weigh

/-! ## Counts kept by isometries -/

section keep

/-- The count after a relabelling is the count composed with it. -/
theorem diagW_relabel {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (n : β → ℕ) (σ : Matrix α α ℂ) :
    diagW n ((SubInstrument.relabel e).branch () σ) = diagW (n ∘ e) σ := by
  rw [SubInstrument.relabel_branch_apply, diagW, diagW]
  refine Fintype.sum_equiv e.symm _ _ fun b ↦ ?_
  obtain ⟨a, rfl⟩ := e.surjective b
  simp only [Equiv.symm_apply_apply, Matrix.submatrix_apply, Function.comp_apply]

/-- **An isometry moving basis states between equal counts** keeps the weight of the count. -/
theorem diagW_conj_of_keep {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (K : Matrix m n ℂ) (hK : Kᴴ * K = 1) (c : m → ℕ) (c' : n → ℕ)
    (hc : ∀ y x, K y x ≠ 0 → c y = c' x) {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    diagW c (MatrixMap.conj K σ) = diagW c' σ := by
  have hcomm : sqrtCount c * K = K * sqrtCount c' := by
    ext y x
    rw [sqrtCount, sqrtCount, diagonal_mul, mul_diagonal]
    by_cases h : K y x = 0
    · simp [h]
    · rw [hc y x h, mul_comm]
  rw [diagW_eq_ofReal_trace c ((MatrixMap.isCP_conj K).posSemidef hσ),
    diagW_eq_ofReal_trace c' hσ, ← LinearMap.comp_apply, ← MatrixMap.conj_mul, hcomm,
    MatrixMap.conj_mul, LinearMap.comp_apply, MatrixMap.trace_conj_apply, hK, Matrix.one_mul]

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)

/-- **A call of an isometric step keeping the counts**: the count after the call is the count of
the states it comes from. -/
theorem diagW_queryStep_of_keep (i : spec.Port) (E : QReg) {A : QReg} (ℓ : A ≃ spec.In i × E)
    (r : spec.Result i) (K : Matrix (spec.Out i × R.D) (spec.In i × R.D) ℂ)
    (hK : (R.step i).branch r = MatrixMap.conj K) (hKu : Kᴴ * K = 1)
    (n : (spec.Out i × E) × R.D → ℕ) (n' : A × R.D → ℕ)
    (hkeep : ∀ a d o d', K (o, d') ((ℓ a).1, d) ≠ 0 → n ((o, (ℓ a).2), d') = n' (a, d))
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    diagW n ((R.queryStep i E ℓ).branch r ρ) = diagW n' ρ := by
  rw [queryStep_branch_apply, DSubInstrument.branch_frame_apply, hK, MatrixMap.amplify_conj,
    diagW_relabel]
  have hK1 : (K ⊗ₖ (1 : Matrix E E ℂ))ᴴ * (K ⊗ₖ (1 : Matrix E E ℂ)) = 1 := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← Matrix.mul_kronecker_mul, hKu,
      Matrix.one_mul, Matrix.one_kronecker_one]
  rw [diagW_conj_of_keep _ hK1 _ (fun y ↦ n' ((queryEquivIn ℓ R.D).symm y)) ?_
    ((SubInstrument.relabel (queryEquivIn ℓ R.D)).posSemidef_branch_apply () hρ),
    diagW_relabel]
  · exact diagW_congr (fun a ↦ congrArg n' ((queryEquivIn ℓ R.D).symm_apply_apply a)) ρ
  · rintro ⟨⟨o, d'⟩, e'⟩ y h
    obtain ⟨⟨a, d⟩, rfl⟩ := (queryEquivIn ℓ R.D).surjective y
    rw [queryEquivIn_apply, kroneckerMap_apply, Matrix.one_apply] at h
    split_ifs at h with he
    · subst he
      rw [Equiv.symm_apply_apply]
      exact hkeep a d o d' (left_ne_zero_of_mul h)
    · exact absurd (mul_zero _) h

/-- **A port whose steps keep the counts**: one result, and its branch is an isometry that moves
the runtime register only between states at which every port's count is the same. -/
def KeepsCounts (c : ∀ i, spec.In i × R.D → ℕ) (i : spec.Port) : Prop :=
  Subsingleton (spec.Result i) ∧ Nonempty (spec.Result i) ∧
    ∀ r, ∃ K : Matrix (spec.Out i × R.D) (spec.In i × R.D) ℂ,
      (R.step i).branch r = MatrixMap.conj K ∧ Kᴴ * K = 1 ∧
        ∀ o d' x d, K (o, d') (x, d) ≠ 0 → ∀ p (y : spec.In p), c p (y, d') = c p (y, d)

end keep

/-! ## Counts of rounds, and their serialization -/

section par

variable {spec : QuantumOracleSpec.{0, 0}}

/-- The count of a round: the sum over its slots of the counts of their calls. -/
def roundCount {D : QReg} (c : ∀ i, spec.In i × D → ℕ) {w : ℕ} (f : Fin w → spec.Port) :
    roundIn spec f × D → ℕ :=
  fun x ↦ ∑ j, c (f j) (x.1 j, x.2)

/-- **The counts of a parallel signature**: those of the single calls, and on a round the sum over
its slots. -/
def parCount {Q : Type} (port : Q → spec.Port) {D : QReg} (c : ∀ i, spec.In i × D → ℕ) :
    ∀ i : (parSpec spec port).Port, (parSpec spec port).In i × D → ℕ
  | .inl i => c i
  | .inr (.round _ f) => roundCount c fun j ↦ port (f j)

variable (R : QuantumRuntime spec) (c : ∀ i, spec.In i × R.D → ℕ)

/-- **The count of a round, slot by slot**: its first slot's count at the first call's input, and
the other slots' count after the first call. -/
theorem roundCount_succ {w : ℕ} (f : Fin (w + 1) → spec.Port) (hf : KeepsCounts R c (f 0))
    (E : QReg) {A : QReg} (ℓ : A ≃ roundIn spec f × E) (r : spec.Result (f 0))
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    diagW (c (f 0)) (callInput (seqSplitIn f E ℓ) R.D ρ) +
      diagW (roundCount c fun i ↦ f i.succ) (callInput (seqShift f E) R.D
        ((R.queryStep (f 0) _ (seqSplitIn f E ℓ)).branch r ρ)) =
      diagW (roundCount c f) (callInput ℓ R.D ρ) := by
  obtain ⟨K, hK, hKu, hkeep⟩ := hf.2.2 r
  rw [diagW_callInput _ _ hρ, diagW_callInput _ _
    ((R.queryStep (f 0) _ (seqSplitIn f E ℓ)).posSemidef_branch_apply r hρ),
    diagW_callInput _ _ hρ,
    diagW_queryStep_of_keep R (f 0) _ (seqSplitIn f E ℓ) r K hK hKu _
      (fun p ↦ ∑ j : Fin w, c (f j.succ) ((ℓ p.1).1 j.succ, p.2))
      (fun a d o d' h ↦ Finset.sum_congr rfl fun j _ ↦ hkeep o d' _ d h _ _) hρ,
    ← diagW_add]
  refine diagW_congr (fun p ↦ ?_) ρ
  simp only [Pi.add_apply, roundCount, Fin.sum_univ_succ]
  rfl

/-- **The calls of a round, then a continuation**: the counts of the calls are the round's count
at the round's input. -/
theorem totalWeight_diagW_bind_seqCalls {Xf : QReg → Type} : ∀ {w : ℕ} (f : Fin w → spec.Port),
    (∀ i, KeepsCounts R c (f i)) → ∀ (E : QReg) {A B : QReg} (ℓ : A ≃ roundIn spec f × E)
    (post : roundOut spec f × E ≃ B)
    (g : ∀ u, QuantumComp₂.Leaf B (RoundResult spec f) u →
      QuantumComp LocalSig.instruments.{0} spec Xf u)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ}, ρ.PosSemidef →
    R.totalWeight .instruments (fun i ↦ diagW (c i)) (IFreeM.bind (seqCalls f E ℓ post) g) ρ =
      diagW (roundCount c f) (callInput ℓ R.D ρ) +
        ∑' rs, R.totalWeight .instruments (fun i ↦ diagW (c i)) (g B ⟨rfl, rs⟩)
          ((R.run₂ .instruments (seqCalls f E ℓ post)).branch rs ρ)
  | 0, f, _, E, A, B, ℓ, post, g, ρ, _ => by
    rw [show diagW (roundCount c f) (callInput ℓ R.D ρ) = 0 from
      Finset.sum_eq_zero fun x _ ↦ by simp [roundCount], zero_add]
    exact R.totalWeight_bind_seqCalls_of_eq_zero f (fun i ↦ i.elim0) E ℓ post g ρ
  | w + 1, f, hf, E, A, B, ℓ, post, g, ρ, hρ => by
    have hL : IFreeM.bind (seqCalls f E ℓ post) g =
        QuantumComp.queryBind (f 0) (QReg.of (roundIn spec (fun i ↦ f i.succ) × E))
          (seqSplitIn f E ℓ) fun r ↦ IFreeM.bind ((seqCalls (fun i ↦ f i.succ)
            (QReg.of (spec.Out (f 0) × E)) (seqShift f E) (seqPost f E post)).map
              (Fin.cons r)) g :=
      rfl
    have hk : ∀ r, IFreeM.bind ((seqCalls (fun i ↦ f i.succ) (QReg.of (spec.Out (f 0) × E))
        (seqShift f E) (seqPost f E post)).map (Fin.cons r)) g =
        IFreeM.bind (seqCalls (fun i ↦ f i.succ) (QReg.of (spec.Out (f 0) × E))
          (seqShift f E) (seqPost f E post)) fun u l ↦ g u ⟨l.1, Fin.cons r l.2⟩ :=
      fun _ ↦ IFreeM.bind_imap _ _ _
    have hb := fun r ↦ (R.queryStep (f 0) _ (seqSplitIn f E ℓ)).posSemidef_branch_apply r hρ
    refine (congrArg (fun y ↦ R.totalWeight .instruments (fun i ↦ diagW (c i)) y ρ) hL).trans
      ((R.totalWeight_queryBind .instruments _ _ _ _ ρ).trans ?_)
    refine (congrArg (_ + ·) (tsum_congr fun r ↦ (congrArg (fun y ↦
      R.totalWeight .instruments (fun i ↦ diagW (c i)) y _) (hk r)).trans
        (totalWeight_diagW_bind_seqCalls (fun i ↦ f i.succ) (fun i ↦ hf i.succ) _ _ _ _
          (hb r)))).trans ?_
    rw [ENNReal.tsum_add, ← add_assoc]
    congr 1
    · obtain ⟨_, ⟨r₀⟩, _⟩ := hf 0
      rw [tsum_eq_single r₀ fun r h ↦ absurd (Subsingleton.elim r r₀) h]
      exact roundCount_succ R c f (hf 0) E ℓ r₀ hρ
    · refine Eq.trans ?_ ((Fin.consEquiv fun i ↦ spec.Result (f i)).tsum_eq _)
      refine Eq.trans ?_ ENNReal.tsum_prod'.symm
      refine tsum_congr fun r ↦ tsum_congr fun rs ↦ ?_
      exact (congrArg (R.totalWeight .instruments (fun i ↦ diagW (c i))
        (g B ⟨rfl, Fin.cons r rs⟩)) (R.branch_run₂_seqCalls_cons f E ℓ post r rs ρ)).symm

/-- **The counts of a parallel program are those of its serialization**: a round's count (the sum
over its slots) is the summed count of its calls, for steps of the rounds' ports that keep the
counts. -/
theorem totalWeight_parCount_eq {Q : Type} (port : Q → spec.Port)
    (hport : ∀ q, KeepsCounts R c (port q)) {Xf : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (parSpec spec port) Xf A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    (R.par port).totalWeight .instruments (fun i ↦ diagW (parCount port c i)) x ρ =
      R.totalWeight .instruments (fun i ↦ diagW (c i)) (IFreeM.substitute (parToSeq port) x) ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    exact ((R.par port).totalWeight_pure _ y ρ).trans (R.totalWeight_pure _ y ρ).symm
  | primBind _ o k ih =>
    exact ((R.par port).totalWeight_primBind _ o k ρ).trans
      ((tsum_congr fun b ↦ ih b (((LocalSig.Interp.instruments o).frame _).posSemidef_branch_apply
        b hρ)).trans (R.totalWeight_primBind _ o
          (fun b ↦ IFreeM.substitute (parToSeq port) (k b)) ρ).symm)
  | queryBind _ i E ℓ k ih =>
    rcases i with p | ⟨w, f⟩
    · exact ((R.par port).totalWeight_queryBind _ (.inl p) E ℓ k ρ).trans
        ((congrArg (_ + ·) (tsum_congr fun r ↦ ih r ((R.queryStep p E ℓ).posSemidef_branch_apply
          r hρ))).trans (R.totalWeight_queryBind _ (w := fun i ↦ diagW (c i)) p E ℓ
            (fun r ↦ IFreeM.substitute (parToSeq port) (k r)) ρ).symm)
    · have hq := R.queryStep_par_round port f E ℓ
      have hb : ∀ r, ((R.par port).queryStep (.inr (.round w f)) E ℓ).branch r ρ =
          (R.run₂ .instruments (seqCalls (fun i ↦ port (f i)) E
            (B := QReg.of (roundOut spec (fun i ↦ port (f i)) × E)) ℓ (Equiv.refl _))).branch
              r ρ := fun r ↦ congrArg (fun T ↦ DSubInstrument.branch T r ρ) hq
      have hR : R.totalWeight .instruments (fun i ↦ diagW (c i))
          (IFreeM.substitute (parToSeq port) (QuantumComp.queryBind (.inr (.round w f)) E ℓ k))
            ρ = _ :=
        (congrArg (fun y ↦ R.totalWeight .instruments (fun i ↦ diagW (c i)) y ρ)
          (IFreeM.bind_assoc _ _ _)).trans
          (totalWeight_diagW_bind_seqCalls R c (fun i ↦ port (f i)) (fun i ↦ hport (f i)) E ℓ
            (B := QReg.of (roundOut spec (fun i ↦ port (f i)) × E)) (Equiv.refl _) _ hρ)
      refine ((R.par port).totalWeight_queryBind _ (.inr (.round w f)) E ℓ k ρ).trans
        (Eq.trans ?_ hR.symm)
      refine congrArg₂ (· + ·) rfl (tsum_congr fun r ↦ ?_)
      rw [hb r]
      exact ih r ((R.run₂ .instruments _).posSemidef_branch_apply r hρ)

end par

/-! ## Read runtimes: steps keeping the counts, and the transfer to the read basis -/

section transfer

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z]

/-- An entry of a product of three matrices is nonzero only along nonzero entries. -/
theorem exists_of_mul_mul_ne_zero {l m n o : Type} [Fintype m] [Fintype n] (A : Matrix l m ℂ)
    (B : Matrix m n ℂ) (C : Matrix n o ℂ) {y : l} {x : o} (h : (A * B * C) y x ≠ 0) :
    ∃ u v, A y u ≠ 0 ∧ B u v ≠ 0 ∧ C v x ≠ 0 := by
  rw [Matrix.mul_apply] at h
  obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hv
  rw [Matrix.mul_apply] at h1
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  obtain ⟨h3, h4⟩ := mul_ne_zero_iff.mp hu
  exact ⟨u, v, h3, h4, h2⟩

variable {D : QReg} (σ₀ : SubState D) (rd : D → SpongeKeys X Z)

theorem injective_stepMap_read (p : SpongePort) :
    Function.Injective (stepMap (readRuntime D σ₀ rd) (fun p s ↦ spongeKeyEquiv (rd s) p) p) :=
  fun a b h ↦ by
    have h2 := congrArg Prod.snd h
    have h1 := congrArg Prod.fst h
    simp only [stepMap] at h1 h2
    rw [h2] at h1
    exact Prod.ext ((spongeKeyEquiv (rd b.2) p).injective h1) h2

/-- The steps of a read runtime keep every count. -/
theorem keepsCounts_read (c : ∀ p, spongeIn X Z p × D → ℕ) (p : SpongePort) :
    KeepsCounts (readRuntime D σ₀ rd) c p := by
  refine ⟨inferInstanceAs (Subsingleton Unit), ⟨()⟩, fun r ↦ ⟨_, readRuntime_branch p r,
    conjTranspose_basisMatrix_mul_self (injective_stepMap_read σ₀ rd p), ?_⟩⟩
  intro o d' x d h q y
  rw [basisMatrix_apply] at h
  split_ifs at h with he
  · rw [show d' = d from congrArg Prod.snd he]
  · exact absurd rfl h

variable (R : QuantumRuntime (spongeSpec X Z)) (U : Matrix R.D R.D ℂ)
  (hU : U ∈ unitaryGroup R.D ℂ) (rd : R.D → SpongeKeys X Z) (hR : IsReadRuntime R U rd)
  (c : ∀ p, spongeIn X Z p × R.D → ℕ)
  (hcU : ∀ d' d, U d' d ≠ 0 → ∀ p y, c p (y, d') = c p (y, d))

include hU hR hcU in
/-- **The steps of a runtime reading its functions in the basis of `U` keep the counts** that `U`
keeps. -/
theorem keepsCounts_of_isReadRuntime (p : SpongePort) : KeepsCounts R c p := by
  have hUU : U * Uᴴ = 1 := by
    rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hU
  have hUU' : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have hB : (basisMatrix (readEquiv rd p))ᴴ * basisMatrix (readEquiv rd p) = 1 :=
    conjTranspose_basisMatrix_mul_self (readEquiv rd p).injective
  refine ⟨inferInstanceAs (Subsingleton Unit), ⟨()⟩, fun r ↦ ⟨_, hR p, ?_, ?_⟩⟩
  · simp only [Matrix.conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one,
      conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 ⊗ₖ U), ← mul_kronecker_mul, Matrix.one_mul, hUU, one_kronecker_one,
      Matrix.one_mul, ← Matrix.mul_assoc (basisMatrix (readEquiv rd p))ᴴ, hB, Matrix.one_mul,
      ← mul_kronecker_mul, Matrix.one_mul, hUU', one_kronecker_one]
  · intro o d' x d h q y
    obtain ⟨⟨o₁, d₁⟩, ⟨x₁, d₂⟩, h1, h2, h3⟩ := exists_of_mul_mul_ne_zero _ _ _ h
    rw [kroneckerMap_apply, conjTranspose_apply] at h1
    rw [kroneckerMap_apply] at h3
    rw [basisMatrix_apply] at h2
    have e12 : d₁ = d₂ := by
      split_ifs at h2 with he
      · exact congrArg Prod.snd he
      · exact absurd rfl h2
    have u1 : U d₁ d' ≠ 0 := fun h0 ↦ h1 (by rw [h0, star_zero, mul_zero])
    have u2 : U d₂ d ≠ 0 := fun h0 ↦ h3 (by rw [h0, mul_zero])
    rw [← hcU d₁ d' u1 q y, e12, hcU d₂ d u2 q y]

include hU hR hcU in
/-- **Counts in the read basis**: the summed counts against a runtime reading its functions in the
basis of `U` are those against the read runtime, from the state conjugated by `U`. -/
theorem totalWeight_eq_read {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w}
    {A : QReg} (x : QuantumComp L (spongeSpec X Z) Ω A) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef) :
    R.totalWeight I (fun i ↦ diagW (c i)) x ρ =
      (readRuntime R.D R.init rd).totalWeight I (fun i ↦ diagW (c i)) x
        (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ U) ρ) := by
  have hUU : U * Uᴴ = 1 := by
    rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hU
  have hUU' : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have hsim : ∀ i r, (R.step i).branch r ∘ₗ (MatrixMap.conj Uᴴ).amplifyLeft
      ((spongeSpec X Z).In i) = (MatrixMap.conj Uᴴ).amplifyLeft ((spongeSpec X Z).Out i) ∘ₗ
        ((readRuntime R.D R.init rd).step i).branch r := fun i r ↦ by
    rw [show r = () from rfl, hR i, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul]
    refine (congrArg MatrixMap.conj ?_).trans ((MatrixMap.conj_mul _ _).trans
      (congrArg (MatrixMap.conj _ ∘ₗ ·) (branch_relabel (readEquiv rd i) ()).symm))
    rw [Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.one_mul, hUU, one_kronecker_one,
      Matrix.mul_one]
  have hρ' : (MatrixMap.conj Uᴴ).amplifyLeft A
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ U) ρ) = ρ := by
    rw [MatrixMap.amplifyLeft_conj, ← LinearMap.comp_apply, ← MatrixMap.conj_mul,
      ← mul_kronecker_mul, Matrix.one_mul, hUU', one_kronecker_one, MatrixMap.conj_one,
      LinearMap.id_apply]
  have hw : ∀ i (σ : Matrix ((spongeSpec X Z).In i × R.D) ((spongeSpec X Z).In i × R.D) ℂ),
      σ.PosSemidef → diagW (c i) ((MatrixMap.conj Uᴴ).amplifyLeft _ σ) = diagW (c i) σ := by
    intro i σ hσ
    rw [MatrixMap.amplifyLeft_conj]
    refine diagW_conj_of_keep _ ?_ _ _ ?_ hσ
    · rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_conjTranspose,
        ← mul_kronecker_mul, Matrix.one_mul, hUU, one_kronecker_one]
    · rintro ⟨y, d'⟩ ⟨x, d⟩ h
      rw [kroneckerMap_apply, Matrix.one_apply] at h
      split_ifs at h with hyx
      · subst hyx
        rw [conjTranspose_apply] at h
        exact (hcU d d' (fun h0 ↦ h (by rw [h0, star_zero, mul_zero])) i y).symm
      · exact absurd (zero_mul _) h
  have hρ1 : (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ U) ρ).PosSemidef :=
    (MatrixMap.isCP_conj _).posSemidef hρ
  have hq := fun j ↦ QuantumRuntime.queryWeight_simulation I
    (R₁ := readRuntime R.D R.init rd) (R₂ := R) (V := MatrixMap.conj Uᴴ) hsim
    (fun i ↦ diagW (c i)) x (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ U) ρ) j
  refine (congrArg (R.totalWeight I (fun i ↦ diagW (c i)) x) hρ'.symm).trans
    ((tsum_congr hq).trans (le_antisymm ?_ ?_))
  · exact totalWeight_le_totalWeight (readRuntime R.D R.init rd) I
      (fun i σ hσ ↦ (hw i σ hσ).le) x hρ1
  · exact totalWeight_le_totalWeight (readRuntime R.D R.init rd) I
      (fun i σ hσ ↦ (hw i σ hσ).ge) x hρ1

end transfer

/-! ## The counts of the serialized simulation against a read runtime -/

section simCount

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z]

section defs

variable {D : QReg} (c : ∀ p, spongeIn X Z p × D → ℕ) (π : Equiv.Perm (X × Z))

/-- **The counts of an in-place evaluation**: of the three calls of `φ` (`forward`) or `φ⁻¹`
(`inverse`) from the state `a`, with the functions `t`, at the runtime state `s`. -/
def evalCount (t : SpongeKeys X Z) (s : D) : PermutationPort → X × Z → ℕ
  | .forward, a => c .k (a, s) + c .k' (π (capacityRound t.2.1 a), s) +
      c .h (Equiv.prodComm X Z (capacityRound t.2.2 (π (capacityRound t.2.1 a))), s)
  | .inverse, a => c .h (Equiv.prodComm X Z (negRate X Z a), s) +
      c .k' (negCap X Z ((rateRound t.1)⁻¹ a), s) +
      c .k (negCap X Z (π⁻¹ ((capacityRound t.2.2)⁻¹ ((rateRound t.1)⁻¹ a))), s)

/-- **The counts of a simulated call** of port `p` on the input `v`: its six calls. -/
def simCount (t : SpongeKeys X Z) (s : D) (p : PermutationPort) (v : (X × Z) × (X × Z)) : ℕ :=
  evalCount c π t s p v.1 + evalCount c π t s (flipPort p) (portPerm (spongePerm t π) p v.1)

end defs

variable {D : QReg} (σ₀ : SubState D) (rd : D → SpongeKeys X Z)
  (c : ∀ p, spongeIn X Z p × D → ℕ) (π : Equiv.Perm (X × Z))

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem injective_onStateD {F : Type*} (e : D → Equiv.Perm (X × Z)) :
    Function.Injective (onStateD (F := F) e) := fun a b h ↦ by
  have h2 := congrArg Prod.snd h
  have h1 := congrArg Prod.fst h
  simp only [onStateD] at h1 h2
  rw [h2] at h1
  obtain ⟨h11, h12⟩ := Prod.ext_iff.1 h1
  exact Prod.ext (Prod.ext ((e b.2).injective h11) h12) h2

variable (F : QReg)

theorem weighsAs_query_read (p : SpongePort) {A : QReg} (ℓ : A ≃ spongeIn X Z p × F) :
    WeighsAs (readRuntime D σ₀ rd) c
      (QuantumComp₂.query (L := LocalSig.instruments.{0}) (spec := spongeSpec X Z) p F ℓ)
      (fun q ↦ c p ((ℓ q.1).1, q.2)) := by
  have : Unique ((spongeSpec X Z).Result p) := inferInstanceAs (Unique Unit)
  exact (WeighsAs.queryBind (R := readRuntime D σ₀ rd) (c := c) (i := p) _
    (injective_stepMap_read σ₀ rd p) (fun r ↦ readRuntime_branch p r) F ℓ
    fun r ↦ weighsAs_pure (readRuntime D σ₀ rd) c r).congr fun _ ↦ rfl

theorem injective_query_read (p : SpongePort) {A : QReg} (ℓ : A ≃ spongeIn X Z p × F) :
    Function.Injective (QuantumRuntime.queryEquivOut (spongeIn X Z p) D F ∘
      Prod.map (stepMap (readRuntime D σ₀ rd) (fun p s ↦ spongeKeyEquiv (rd s) p) p) id ∘
        QuantumRuntime.queryEquivIn ℓ D) :=
  (Equiv.injective _).comp (((injective_stepMap_read σ₀ rd p).prodMap Function.injective_id).comp
    (Equiv.injective _))

theorem weighsAs_stateGate_read (e : Equiv.Perm (X × Z)) :
    WeighsAs (readRuntime D σ₀ rd) c (stateGate.{0} F e) 0 :=
  weighsAs_isoGate (readRuntime D σ₀ rd) c _ _

theorem weighsAs_sigmaK_read :
    WeighsAs (readRuntime D σ₀ rd) c (sigmaK.{0} F) (fun q ↦ c .k (q.1.1, q.2)) :=
  weighsAs_query_read σ₀ rd c F .k _

theorem weighsAs_sigmaK'_read :
    WeighsAs (readRuntime D σ₀ rd) c (sigmaK'.{0} F) (fun q ↦ c .k' (q.1.1, q.2)) :=
  weighsAs_query_read σ₀ rd c F .k' _

theorem weighsAs_omegaH_read :
    WeighsAs (readRuntime D σ₀ rd) c (omegaH.{0} F)
      (fun q ↦ c .h (Equiv.prodComm X Z q.1.1, q.2)) := by
  unfold omegaH
  exact ((weighsAs_query_read σ₀ rd c F .h _).bind
    (runsAs_query _ .h _ (readRuntime_branch .h ()) F _) (injective_query_read σ₀ rd F .h _)
    (weighsAs_isoGate (readRuntime D σ₀ rd) c _ _)).congr fun _ ↦ rfl

theorem weighsAs_sigmaKInv_read :
    WeighsAs (readRuntime D σ₀ rd) c (sigmaKInv.{0} F)
      (fun q ↦ c .k (negCap X Z q.1.1, q.2)) := by
  unfold sigmaKInv
  exact ((weighsAs_stateGate_read σ₀ rd c F _).bind (runsAs_stateGate_read σ₀ rd F _)
    (injective_onStateD _) ((weighsAs_sigmaK_read σ₀ rd c F).bind_zero
      (weighsAs_stateGate_read σ₀ rd c F _))).congr fun q ↦ by
    simp [onStateD]

theorem weighsAs_sigmaK'Inv_read :
    WeighsAs (readRuntime D σ₀ rd) c (sigmaK'Inv.{0} F)
      (fun q ↦ c .k' (negCap X Z q.1.1, q.2)) := by
  unfold sigmaK'Inv
  exact ((weighsAs_stateGate_read σ₀ rd c F _).bind (runsAs_stateGate_read σ₀ rd F _)
    (injective_onStateD _) ((weighsAs_sigmaK'_read σ₀ rd c F).bind_zero
      (weighsAs_stateGate_read σ₀ rd c F _))).congr fun q ↦ by
    simp [onStateD]

theorem weighsAs_omegaHInv_read :
    WeighsAs (readRuntime D σ₀ rd) c (omegaHInv.{0} F)
      (fun q ↦ c .h (Equiv.prodComm X Z (negRate X Z q.1.1), q.2)) := by
  unfold omegaHInv
  exact ((weighsAs_stateGate_read σ₀ rd c F _).bind (runsAs_stateGate_read σ₀ rd F _)
    (injective_onStateD _) ((weighsAs_omegaH_read σ₀ rd c F).bind_zero
      (weighsAs_stateGate_read σ₀ rd c F _))).congr fun q ↦ by
    simp [onStateD]

theorem weighsAs_evalPerm_read :
    WeighsAs (readRuntime D σ₀ rd) c (evalPerm.{0} F π)
      (fun q ↦ evalCount c π (rd q.2) q.2 .forward q.1.1) := by
  unfold evalPerm
  exact ((weighsAs_sigmaK_read σ₀ rd c F).bind (runsAs_sigmaK_read σ₀ rd F)
    (injective_onStateD _) ((weighsAs_stateGate_read σ₀ rd c F π).bind
      (runsAs_stateGate_read σ₀ rd F π) (injective_onStateD _)
      ((weighsAs_sigmaK'_read σ₀ rd c F).bind (runsAs_sigmaK'_read σ₀ rd F)
        (injective_onStateD _) (weighsAs_omegaH_read σ₀ rd c F)))).congr fun q ↦ by
    simp only [Pi.add_apply, Function.comp_apply, onStateD, zero_add, evalCount]
    omega

theorem weighsAs_evalPermInv_read :
    WeighsAs (readRuntime D σ₀ rd) c (evalPermInv.{0} F π)
      (fun q ↦ evalCount c π (rd q.2) q.2 .inverse q.1.1) := by
  unfold evalPermInv
  exact ((weighsAs_omegaHInv_read σ₀ rd c F).bind (runsAs_omegaHInv_read σ₀ rd F)
    (injective_onStateD _) ((weighsAs_sigmaK'Inv_read σ₀ rd c F).bind
      (runsAs_sigmaK'Inv_read σ₀ rd F) (injective_onStateD _)
      ((weighsAs_stateGate_read σ₀ rd c F π⁻¹).bind (runsAs_stateGate_read σ₀ rd F π⁻¹)
        (injective_onStateD _) (weighsAs_sigmaKInv_read σ₀ rd c F)))).congr fun q ↦ by
    simp only [Pi.add_apply, Function.comp_apply, onStateD, zero_add, evalCount]
    omega

theorem weighsAs_evalPort_read (p : PermutationPort) :
    WeighsAs (readRuntime D σ₀ rd) c (evalPort.{0} F π p)
      (fun q ↦ evalCount c π (rd q.2) q.2 p q.1.1) := by
  cases p
  exacts [weighsAs_evalPerm_read σ₀ rd c π F, weighsAs_evalPermInv_read σ₀ rd c π F]

variable {E : QReg}

/-- **The counts of a simulated call** against a read runtime. -/
theorem weighsAs_simCall_read (p : PermutationPort) {A : QReg}
    (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) :
    WeighsAs (readRuntime D σ₀ rd) c (simCall.{0} π p E ℓ)
      (fun q ↦ simCount c π (rd q.2) q.2 p (ℓ q.1).1) := by
  unfold simCall
  refine (((weighsAs_isoGate (readRuntime D σ₀ rd) c _ _).bind (runsAs_isoGate _ _)
    ((copyIn_injective ℓ).prodMap Function.injective_id)
    ((weighsAs_evalPort_read σ₀ rd c π _ p).bind (runsAs_evalPort_read σ₀ rd _ π p)
      (injective_onStateD _) ((weighsAs_isoGate (readRuntime D σ₀ rd) c _ _).bind
        (runsAs_isoGate _ _)
        ((addInto p E).injective.prodMap Function.injective_id)
        (weighsAs_evalPort_read σ₀ rd c π _ (flipPort p))))).bind_zero
    (weighsAs_coGate (readRuntime D σ₀ rd) c _ _)).congr fun q ↦ ?_
  simp only [Pi.add_apply, Function.comp_apply, onStateD, Pi.zero_apply, zero_add, Prod.map,
    id, simCount]
  rfl

section simulate

variable (R : QuantumRuntime (spongeSpec X Z)) (c : ∀ p, spongeIn X Z p × R.D → ℕ)
  (π : Equiv.Perm (X × Z))

/-- **A simulated call, then a continuation**: the counts of the call, then those of the
continuation from the call's branch. -/
theorem totalWeight_simTree_bind (p : PermutationPort) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) {W : QReg → Type}
    (g : ∀ t, (Subtype fun _ : ULift.{0} Unit ↦ callReg X Z p E = t) →
      QuantumComp LocalSig.instruments.{0} (spongeSpec X Z) W t)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight .instruments (fun i ↦ diagW (c i)) ((simTree π p E ℓ).bind g) ρ =
      R.totalWeight .instruments (fun i ↦ diagW (c i)) (simCall.{0} π p E ℓ) ρ +
        R.totalWeight .instruments (fun i ↦ diagW (c i)) (g _ ⟨ULift.up (), rfl⟩)
          ((R.run₂ .instruments (simCall.{0} π p E ℓ)).branch () ρ) := by
  refine (congrArg (fun y ↦ R.totalWeight .instruments (fun i ↦ diagW (c i)) y ρ)
    (QuantumComp.bind_assoc (simCall π p E ℓ) _ g)).trans ?_
  refine (totalWeight_diagW_bind R .instruments c _ _ hρ).trans (congrArg (_ + ·) ?_)
  rw [← (QuantumComp₂.leafEquiv _ Unit).tsum_eq, tsum_fintype, Fintype.sum_unique]
  rfl

omit [AddCommGroup X] [AddCommGroup Z] in
/-- A local subinstrument counts nothing. -/
theorem totalWeight_act {A B : QReg} {α : Type} (q : SubInstrument A B α)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight .instruments (fun i ↦ diagW (c i))
      (QComp.act.{0} (spec := spongeSpec X Z) q) ρ = 0 :=
  (R.totalWeight_primBind _ _ _ ρ).trans
    ((tsum_congr fun _ ↦ R.totalWeight_pure _ _ _).trans tsum_zero)

omit [AddCommGroup X] [AddCommGroup Z] in
/-- Relabelling the value keeps the counts. -/
theorem totalWeight_map₂ {A B : QReg} {α β : Type}
    (x : QuantumComp₂ LocalSig.instruments.{0} (spongeSpec X Z) A B α) (f : α → β)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight .instruments (fun i ↦ diagW (c i)) (x.map f) ρ =
      R.totalWeight .instruments (fun i ↦ diagW (c i)) x ρ := by
  rw [QuantumComp₂.map_eq_bind_pure, totalWeight_diagW_bind₂ R .instruments c _ _ hρ]
  exact (congrArg (_ + ·) ((tsum_congr fun _ ↦ R.totalWeight_pure _ _ _).trans tsum_zero)).trans
    (add_zero _)

theorem keepsPrims_simSubst :
    KeepsPrims (simSubst (L := LocalSig.instruments.{0}) LocalSig.Interp.instruments π) :=
  fun _ _ ↦ rfl

end simulate

theorem injective_callMap {E A : QReg} (p : PermutationPort) (φ : D → Equiv.Perm (X × Z))
    (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) :
    Function.Injective (fun q : A × D ↦ callMap (φ q.2) p ℓ q) := fun a b h ↦ by
  have h2 := congrArg Prod.snd h
  have h1 := congrArg (fun x ↦ x.1) h
  simp only [callMap] at h2
  simp only [callMap, h2, Prod.mk.injEq] at h1
  obtain ⟨⟨h111, h112⟩, h13⟩ := h1
  rw [h111] at h112
  exact Prod.ext (ℓ.injective (Prod.ext (Prod.ext h111 (add_right_cancel h112)) h13)) h2

/-- **The counts of the serialized simulation of a round** against a read runtime: the sum over
the slots of the counts of their simulated calls. -/
theorem weighsAs_simulate_seqCalls : ∀ {w : ℕ} (dir : Fin w → PermutationPort) (E : QReg)
    {A B : QReg} (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E)
    (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B),
    WeighsAs (readRuntime D σ₀ rd) c
      (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post))
      (fun q ↦ ∑ i, simCount c π (rd q.2) q.2 (dir i) ((ℓ q.1).1 i))
  | 0, dir, E, A, B, ℓ, post => fun ρ _ ↦ by
    rw [seqCalls_zero]
    show (readRuntime D σ₀ rd).totalWeight .instruments _
      (IFreeM.substitute (simSubst LocalSig.Interp.instruments π) _) ρ = _
    rw [substitute_act_of_keepsPrims (keepsPrims_simSubst π)]
    exact (totalWeight_act (readRuntime D σ₀ rd) c _ ρ).trans
      ((diagW_congr (fun _ ↦ Finset.sum_empty) ρ).trans (diagW_zero ρ)).symm
  | w + 1, dir, E, A, B, ℓ, post => fun ρ hρ ↦ by
    have hb := (runsAs_simCall_read σ₀ rd π (dir 0) (seqSplitIn (spec := qrpmSpec (X × Z)) dir E ℓ))
    rw [RunsAs] at hb
    refine (totalWeight_simTree_bind (readRuntime D σ₀ rd) c π (dir 0) _
      (seqSplitIn (spec := qrpmSpec (X × Z)) dir E ℓ) _
      hρ).trans ?_
    rw [weighsAs_simCall_read σ₀ rd c π (dir 0) (seqSplitIn (spec := qrpmSpec (X × Z)) dir E ℓ)
      ρ hρ, hb]
    have hpsd : (MatrixMap.conj (basisMatrix fun q ↦ callMap (spongePerm (rd q.2) π) (dir 0)
        (seqSplitIn (spec := qrpmSpec (X × Z)) dir E ℓ) q) ρ).PosSemidef :=
      (MatrixMap.isCP_conj _).posSemidef hρ
    have e := substitute_map (simSubst LocalSig.Interp.instruments π)
      (seqCalls (spec := qrpmSpec (X × Z)) (fun i ↦ dir i.succ)
        (QReg.of ((qrpmSpec (X × Z)).Out (dir 0) × E))
        (seqShift (spec := qrpmSpec (X × Z)) dir E)
        (seqPost (spec := qrpmSpec (X × Z)) dir E post))
      (Fin.cons (α := fun i ↦ (qrpmSpec (X × Z)).Result (dir i)) ())
    refine (congrArg (_ + ·) ((congrArg (fun y ↦ (readRuntime D σ₀ rd).totalWeight .instruments
      (fun i ↦ diagW (c i)) y _) e).trans ((totalWeight_map₂ (readRuntime D σ₀ rd) c _ _
        hpsd).trans (weighsAs_simulate_seqCalls (fun i ↦ dir i.succ) _
          (seqShift (spec := qrpmSpec (X × Z)) dir E)
          (seqPost (spec := qrpmSpec (X × Z)) dir E post) _ hpsd)))).trans ?_
    refine (congrArg (_ + ·) (diagW_conj_basisMatrix (injective_callMap (D := D) (dir 0)
      (fun s ↦ spongePerm (rd s) π) (seqSplitIn (spec := qrpmSpec (X × Z)) dir E ℓ)) _ ρ)).trans
      ((diagW_add _ _ ρ).symm.trans (diagW_congr (fun q ↦ ?_) ρ))
    have h0 : ((seqSplitIn (spec := qrpmSpec (X × Z)) dir E ℓ) q.1).1 = (ℓ q.1).1 0 := rfl
    have hs : ∀ i, ((seqShift (spec := qrpmSpec (X × Z)) dir E) (callMap (spongePerm (rd q.2) π)
        (dir 0) (seqSplitIn (spec := qrpmSpec (X × Z)) dir E ℓ) q).1).1 i = (ℓ q.1).1 i.succ :=
      fun _ ↦ rfl
    have h2 : (callMap (spongePerm (rd q.2) π) (dir 0)
        (seqSplitIn (spec := qrpmSpec (X × Z)) dir E ℓ) q).2 = q.2 := rfl
    refine (congrArg₂ (· + ·) (congrArg (simCount c π (rd q.2) q.2 (dir 0)) h0)
      (Finset.sum_congr rfl fun i _ ↦ ?_)).trans (Fin.sum_univ_succ (fun i ↦
        simCount c π (rd q.2) q.2 (dir i) ((ℓ q.1).1 i))).symm
    exact congrArg₂ (fun s v ↦ simCount c π (rd s) s (dir i.succ) v) h2 (hs i)

end simCount

/-! ## The counts of the lockstep round against a read runtime -/

section lockCount

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] {w : ℕ} {E D : QReg} (σ₀ : SubState D) (rd : D → SpongeKeys X Z)
  (c : ∀ p, spongeIn X Z p × D → ℕ)

theorem sum_subEnum {M : Type*} [AddCommMonoid M] (P : Fin w → Prop) [DecidablePred P]
    (F : Fin w → M) : ∑ j, F (subEnum P j) = ∑ i, if P i then F i else 0 :=
  (Equiv.sum_comp (subEnum P) (fun x : {i // P i} ↦ F x)).trans
    ((Finset.sum_subtype (Finset.univ.filter P) (fun i ↦ by simp) F).symm.trans
      (Finset.sum_filter _ _))

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem injective_allMap (g : Fin w → D → Equiv.Perm (SlotT X Z)) :
    Function.Injective (allMap (E := E) g) := fun a b h ↦ by
  have h2 := congrArg Prod.snd h
  have h1 := congrArg Prod.fst h
  simp only [allMap] at h1 h2
  rw [h2] at h1
  obtain ⟨h11, h12⟩ := Prod.ext_iff.1 h1
  exact Prod.ext (Prod.ext (funext fun i ↦ (g i b.2).injective (congrFun h11 i)) h12) h2

theorem injective_roundMap_read {m : ℕ} (f : Fin m → SpongePort) :
    Function.Injective (fun q : roundIn (spongeSpec X Z) f × D ↦
      ((fun i ↦ spongeKeyEquiv (rd q.2) (f i) (q.1 i) : ∀ i, (spongeSpec X Z).Out (f i)),
        q.2)) := fun a b h ↦ by
  have h2 := congrArg Prod.snd h
  have h1 := congrArg Prod.fst h
  simp only at h1 h2
  rw [h2] at h1
  exact Prod.ext (funext fun i ↦ (spongeKeyEquiv (rd b.2) (f i)).injective (congrFun h1 i)) h2

theorem weighsAs_gateAll (g : Fin w → Equiv.Perm (SlotT X Z)) :
    WeighsAs (readParR D σ₀ rd) (parCount id c) (gateAll (E := E) g) 0 :=
  weighsAs_isoGate (readParR D σ₀ rd) (parCount id c) _ _

/-- **The counts of a round of port `p` on the slots in `P`**: the sum over those slots of the
count of their state, read through `e`. -/
theorem weighsAs_subRound (p : SpongePort) (e : (X × Z) ≃ spongeIn X Z p) (P : Fin w → Prop)
    [DecidablePred P] :
    WeighsAs (readParR D σ₀ rd) (parCount id c) (subRound (E := E) p e P)
      (fun q ↦ ∑ i, if P i then c p (e (q.1.1 i).1, q.2) else 0) := by
  unfold subRound
  have : Unique ((lockSpecR X Z).Result (.inr (.round (Fintype.card {i // P i}) fun _ ↦ p))) :=
    inferInstanceAs (Unique (Fin _ → Unit))
  refine (WeighsAs.queryBind (R := readParR D σ₀ rd) (c := parCount id c)
    (i := .inr (.round (Fintype.card {i // P i}) fun _ ↦ p)) _ (injective_roundMap_read rd _)
    (fun r ↦ branch_roundStep_basis (R := readRuntime D σ₀ rd)
      (G := fun p s ↦ spongeKeyEquiv (rd s) p) (fun p r ↦ readRuntime_branch p r) _ r) _ _
    fun _ ↦ weighsAs_isoGate (readParR D σ₀ rd) (parCount id c) _ _).congr fun q ↦ ?_
  exact (add_zero _).trans (sum_subEnum P fun i ↦ c p (e (q.1.1 i).1, q.2))

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem spongePerm_apply' (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (u : X × Z) :
    spongePerm t π u = rateRound t.1 (capacityRound t.2.2 (π (capacityRound t.2.1 u))) :=
  rfl

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem spongePerm_symm_apply (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (u : X × Z) :
    (spongePerm t π).symm u =
      (capacityRound t.2.1)⁻¹ (π⁻¹ ((capacityRound t.2.2)⁻¹ ((rateRound t.1)⁻¹ u))) :=
  rfl

variable (π : Equiv.Perm (X × Z)) (dir : Fin w → PermutationPort)

/-- **The counts of the lockstep round** against a read runtime: the sum over the slots of the
counts of their simulated calls. -/
theorem weighsAs_lockRoundR {A B : QReg} (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E)
    (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B) :
    WeighsAs (readParR D σ₀ rd) (parCount id c) (lockRoundR π dir ℓ post)
      (fun q ↦ ∑ i, simCount c π (rd q.2) q.2 (dir i) ((ℓ q.1).1 i)) := by
  have h18 := weighsAs_gateAll σ₀ rd c (E := E) fun i ↦ byDir (dir i) (stateE (negCap X Z)) 1
  have h17 := (weighsAs_subRound σ₀ rd c (E := E) .k (Equiv.refl _)
    fun i ↦ dir i = .forward).bind' (runsAs_subRound_k σ₀ rd _) (injective_allMap _) fun _ ↦ h18
  have h16 := (weighsAs_gateAll σ₀ rd c (E := E) fun i ↦ byDir (dir i)
    (stateE (negCap X Z) * stateE π⁻¹ * stateE (negCap X Z)) 1).bind'
      (runsAs_gateAll σ₀ rd _) (injective_allMap _) fun _ ↦ h17
  have h15 := (weighsAs_subRound σ₀ rd c (E := E) .k' (Equiv.refl _)
    fun i ↦ dir i = .forward).bind' (runsAs_subRound_k' σ₀ rd _) (injective_allMap _) fun _ ↦ h16
  have h14 := (weighsAs_gateAll σ₀ rd c (E := E) fun i ↦ byDir (dir i)
    (stateE (negCap X Z) * stateE (negRate X Z)) 1).bind'
      (runsAs_gateAll σ₀ rd _) (injective_allMap _) fun _ ↦ h15
  have h13 := (weighsAs_subRound σ₀ rd c (E := E) .h (Equiv.prodComm X Z)
    fun _ ↦ True).bind' (runsAs_subRound_h σ₀ rd _) (injective_allMap _) fun _ ↦ h14
  have h12 := (weighsAs_subRound σ₀ rd c (E := E) .k' (Equiv.refl _)
    fun i ↦ dir i = .inverse).bind' (runsAs_subRound_k' σ₀ rd _) (injective_allMap _) fun _ ↦ h13
  have h11 := (weighsAs_gateAll σ₀ rd c (E := E) fun i ↦ byDir (dir i) 1 (stateE π)).bind'
    (runsAs_gateAll σ₀ rd _) (injective_allMap _) fun _ ↦ h12
  have h10 := (weighsAs_subRound σ₀ rd c (E := E) .k (Equiv.refl _)
    fun i ↦ dir i = .inverse).bind' (runsAs_subRound_k σ₀ rd _) (injective_allMap _) fun _ ↦ h11
  have h9 := (weighsAs_gateAll σ₀ rd c (E := E) fun i ↦ byDir (dir i) 1
    (addT * stateE (negCap X Z))).bind' (runsAs_gateAll σ₀ rd _) (injective_allMap _) fun _ ↦ h10
  have h8 := (weighsAs_subRound σ₀ rd c (E := E) .k (Equiv.refl _)
    fun i ↦ dir i = .inverse).bind' (runsAs_subRound_k σ₀ rd _) (injective_allMap _) fun _ ↦ h9
  have h7 := (weighsAs_gateAll σ₀ rd c (E := E) fun i ↦ byDir (dir i) 1
    (stateE (negCap X Z) * stateE π⁻¹ * stateE (negCap X Z))).bind'
      (runsAs_gateAll σ₀ rd _) (injective_allMap _) fun _ ↦ h8
  have h6 := (weighsAs_subRound σ₀ rd c (E := E) .k' (Equiv.refl _)
    fun i ↦ dir i = .inverse).bind' (runsAs_subRound_k' σ₀ rd _) (injective_allMap _) fun _ ↦ h7
  have h5 := (weighsAs_gateAll σ₀ rd c (E := E) fun i ↦ byDir (dir i)
    (stateE (negRate X Z) * addT) (stateE (negCap X Z) * stateE (negRate X Z))).bind'
      (runsAs_gateAll σ₀ rd _) (injective_allMap _) fun _ ↦ h6
  have h4 := (weighsAs_subRound σ₀ rd c (E := E) .h (Equiv.prodComm X Z)
    fun _ ↦ True).bind' (runsAs_subRound_h σ₀ rd _) (injective_allMap _) fun _ ↦ h5
  have h3 := (weighsAs_subRound σ₀ rd c (E := E) .k' (Equiv.refl _)
    fun i ↦ dir i = .forward).bind' (runsAs_subRound_k' σ₀ rd _) (injective_allMap _) fun _ ↦ h4
  have h2 := (weighsAs_gateAll σ₀ rd c (E := E) fun i ↦ byDir (dir i) (stateE π)
    (stateE (negRate X Z))).bind' (runsAs_gateAll σ₀ rd _) (injective_allMap _) fun _ ↦ h3
  have h1 := (weighsAs_subRound σ₀ rd c (E := E) .k (Equiv.refl _)
    fun i ↦ dir i = .forward).bind' (runsAs_subRound_k σ₀ rd _) (injective_allMap _) fun _ ↦ h2
  have h0 := ((weighsAs_isoGate (readParR D σ₀ rd) (parCount id c) (B := lockReg X Z w E)
    (copyAll dir ℓ)
    (copyAll_injective dir ℓ)).bind' (runsAs_isoGate _ _)
      ((copyAll_injective dir ℓ).prodMap Function.injective_id) fun _ ↦ h1).bind_zero'
    fun _ ↦ (weighsAs_coGate (readParR D σ₀ rd) (parCount id c) (A := lockReg X Z w E)
      (uncopyAll dir post)
      (uncopyAll_injective dir post))
  refine h0.congr fun q ↦ ?_
  simp only [Pi.add_apply, Function.comp_apply, Pi.zero_apply, add_zero, zero_add, Prod.map,
    allMap, copyAll, id]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases hd : dir i <;>
  simp only [byDir, reduceCtorEq, ↓reduceIte, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    stateE_apply, addT_apply, simCount, evalCount, flipPort, portPerm, add_zero, zero_add,
    negCap_cap_negCap_apply, negRate_rate_negRate_apply, Equiv.refl_apply, spongePerm_apply',
    spongePerm_symm_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, Equiv.apply_symm_apply] <;>
  omega

end lockCount

/-! ## Hidden masses of the lockstep round -/

section main

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] (R : QuantumRuntime (spongeSpec X Z)) (U : Matrix R.D R.D ℂ)
  (hU : U ∈ unitaryGroup R.D ℂ) (rd : R.D → SpongeKeys X Z) (hR : IsReadRuntime R U rd)
  (c : ∀ p, spongeIn X Z p × R.D → ℕ)
  (hcU : ∀ d' d, U d' d ≠ 0 → ∀ p y, c p (y, d') = c p (y, d))

include hU hR hcU in
/-- **Counts of the lockstep round = counts of the serialized simulation.** Against a runtime
reading its functions in the basis of a unitary `U`, for counts `c` of the calls' inputs that `U`
keeps (reading only a call's input and a coordinate of the register that `U` preserves), the
summed counts of the calls of `lockRoundR` (a round counted as the sum over its slots) are the
summed counts of the calls of the serialized simulation. -/
theorem totalWeight_lockRoundR_eq (π : Equiv.Perm (X × Z)) {w : ℕ}
    (dir : Fin w → PermutationPort) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E) (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    (R.par id).totalWeight .instruments (fun i ↦ diagW (parCount id c i))
        (lockRoundR π dir ℓ post) ρ =
      R.totalWeight .instruments (fun i ↦ diagW (c i))
        (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post)) ρ := by
  have hρ' : (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ U) ρ).PosSemidef :=
    (MatrixMap.isCP_conj _).posSemidef hρ
  refine (totalWeight_parCount_eq R c id (keepsCounts_of_isReadRuntime R U hU rd hR c hcU) _
    hρ).trans ((totalWeight_eq_read R U hU rd hR c hcU _ _ hρ).trans (Eq.trans ?_
      (totalWeight_eq_read R U hU rd hR c hcU _ _ hρ).symm))
  refine (totalWeight_parCount_eq (readRuntime R.D R.init rd) c id
    (keepsCounts_read R.init rd c) _ hρ').symm.trans ?_
  exact (weighsAs_lockRoundR R.init rd c π dir ℓ post _ hρ').trans
    (weighsAs_simulate_seqCalls R.init rd c π dir E ℓ post _ hρ').symm

include hU hR in
/-- **Hidden masses of the lockstep round** (`totalWeight_lockRoundR_eq` for the diagonal masses
of sets `C p` that `U` keeps): the summed hidden masses of `lockRoundR`, a round counted as the
summed masses of its slots, are those of the serialized simulation. -/
theorem totalWeight_diagMass_lockRoundR_eq (C : ∀ p, Set (spongeIn X Z p × R.D))
    (hCU : ∀ d' d, U d' d ≠ 0 → ∀ p y, ((y, d') ∈ C p ↔ (y, d) ∈ C p))
    (π : Equiv.Perm (X × Z)) {w : ℕ} (dir : Fin w → PermutationPort) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E) (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    (R.par id).totalWeight .instruments
        (fun i ↦ diagW (parCount id (fun p ↦ (C p).indicator 1) i)) (lockRoundR π dir ℓ post) ρ =
      R.totalWeight .instruments (fun p ↦ diagMass (C p))
        (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post)) ρ := by
  refine (totalWeight_lockRoundR_eq R U hU rd hR (fun p ↦ (C p).indicator 1) (fun d' d h p y ↦ ?_)
    π dir E ℓ post hρ).trans (congrArg (fun W ↦ R.totalWeight .instruments W _ ρ)
      (funext fun p ↦ funext fun σ ↦ (diagMass_eq_diagW (C p) σ).symm))
  by_cases hy : (y, d) ∈ C p
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((hCU d' d h p y).2 hy)]
    rfl
  · rw [Set.indicator_of_notMem hy,
      Set.indicator_of_notMem fun h' ↦ hy ((hCU d' d h p y).1 h')]

end main

end Quantum.Par

end
