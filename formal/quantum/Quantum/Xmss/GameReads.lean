module

public import Quantum.Xmss.TableLaw
public import Quantum.SufCma.Classical
public import Quantum.Sponge.Simulate

@[expose] public section

/-!
# The game's honest hashing as read ports: G1 to G2

The step G1 → G2 of the design for the whole SUF-CMA game. After `qrpmEvalDistMap_eq_simulate`,
the game runs against the oracles of `t = (h, k, k')` given `π`, every permutation call simulated
by `simulate`. The adversary's calls are quantum and stay simulated; the honest calls (key
generation, each signature, verification) are classical, and each is one evaluation of
`φ = spongePerm t π` on a basis state. Here the honest hash computations become programs of the
classical read ports `HwRead` of runtime 1, each sponge round three reads (`k`, `k'`, `h`).

* `readCall c B`: one read port beside a held register `B`. `readsProgram π B x`: a hash-query
  computation (`OracleComp SchemeHashSpec`) with every hash the sponge evaluation through read
  ports (`rdRound`, three reads per block), logging its reads.
* `ReadsTo t W m x a₀`: against `spongeFnReadRuntime X Z t W m`, from any state of its held
  register beside the block `(W, m)` of the classical register (`hwAt W m`), the program returns
  `a₀` with certainty and leaves the held register and the block untouched.
  `readsTo_readsProgram`: the read program returns the honest evaluation
  `honestEval (overwrite W t) π x`, result and read log.
* `classicalOn_simulate_permImpl_forward`, `permReads`, `readsTo_permReads`: the per-call
  identity. A classical forward call of the honest scheme, simulated, returns
  `statePerm (spongePerm t π) s` with certainty; its read program, the three reads of one round,
  returns the same state and logs the round's reads.
* `challengeReads`, `gameReads π sch Sch A b`: for a scheme `sch` of the statement's game and its
  hash-query form `Sch` (`sch = Sch.overPermutation`), the game after key generation (its honest
  result `b.1`),
  with the adversary's local operations and permutation calls simulated and lifted to the read
  signature, every signing request answered by the read program of the signer, and verification
  as a read program.
* `intertwines_game`, `evalDistMap_game_eq_reads`: against `φ = spongePerm (overwrite W t) π`, the
  game has the law of `gameReads π A (honestEval (overwrite W t) π (keygen S0))` against
  `spongeFnReadRuntime X Z t W m`; the runs intertwine through the embedding of the trivial
  register as the block `(W, m)`.
* `evalDistMap_simulate_game_eq_reads` (fixed `t`, `π`), `spongeEvalDistMap_simulate_game_eq_reads`
  (fixed `π`), `qrpm_game_eq_reads`: the game's law in the QRPM is the average over `π` and
  uniform `t` of the read runtime's law of `gameReads π A (honestEval t π (keygen S0))`, the
  left-hand side of `spongeEvalDistMap_eq_tableLaw` (key generation as `x`, `gameReads π A` as
  `y`), summand for summand.

Every read keeps the memory (`keepMem`); the memory `m₀` of the read runtime is arbitrary.

The sums over the functions `t` are huge at the Keccak sizes: a kernel definitional check that
unfolds a scalar multiple of such a sum evaluates it. The sum manipulations are therefore proved
for abstract `X`, `Z` (`spongeEvalDistMap_eq_sum_smul`, `qrpmEvalDistMap_eq_sum_smul`) and
instantiated with named summands (`gameReadsLaw`, `gameReadsAvg`), so that the concrete proofs
only compare terms that agree syntactically under every scalar.
-/

open IPFunctor OracleComp OracleSpec Matrix MeasureTheory
open scoped Kronecker ENNReal

universe u v w

namespace Quantum.Sponge

open Quantum

/-! ## Runs that intertwine -/

section intertwine

variable {spec₀ spec₁ spec₂ : QuantumOracleSpec.{0, 0}} {R₁ : QuantumRuntime spec₁}
  {R₂ : QuantumRuntime spec₂} {V : MatrixMap R₁.D R₂.D}

/-- A leaf intertwines with itself. -/
theorem intertwines_run_pure {Y : QReg → Type} {A : QReg} (y : Y A) :
    DSubInstrument.Intertwines (V.amplifyLeft A) (fun p : Σ u, Y u ↦ V.amplifyLeft p.1)
      (R₁.run .instruments (QuantumComp.pure (L := LocalSig.instruments.{0}) (spec := spec₁) y))
      (R₂.run .instruments (QuantumComp.pure (L := LocalSig.instruments.{0}) (spec := spec₂) y)) := by
  rw [QuantumRuntime.run_pure, QuantumRuntime.run_pure]
  exact DSubInstrument.Intertwines.ret (B := fun p : Σ u, Y u ↦ p.1 × R₁.D)
    (B' := fun p : Σ u, Y u ↦ p.1 × R₂.D) (fun p ↦ V.amplifyLeft p.1) ⟨A, y⟩

/-- A returned value intertwines with itself. -/
theorem intertwines_run₂_pure {B : QReg} {α : Type} (a : α) :
    DSubInstrument.Intertwines (V.amplifyLeft B) (fun _ ↦ V.amplifyLeft B)
      (R₁.run₂ .instruments (QuantumComp₂.pure a : QComp spec₁ B B α))
      (R₂.run₂ .instruments (QuantumComp₂.pure a : QComp spec₂ B B α)) := by
  rw [QuantumRuntime.run₂_pure, QuantumRuntime.run₂_pure]
  exact DSubInstrument.Intertwines.ret (B := fun _ : α ↦ B × R₁.D) (B' := fun _ : α ↦ B × R₂.D)
    (fun _ ↦ V.amplifyLeft B) a

/-- Sequences of fixed-register programs whose parts intertwine intertwine. -/
theorem intertwines_run₂_bind {A B C : QReg} {α β : Type} {x₁ : QComp spec₁ A B α}
    {x₂ : QComp spec₂ A B α} {k₁ : α → QComp spec₁ B C β} {k₂ : α → QComp spec₂ B C β}
    (hx : DSubInstrument.Intertwines (V.amplifyLeft A) (fun _ ↦ V.amplifyLeft B)
      (R₁.run₂ .instruments x₁) (R₂.run₂ .instruments x₂))
    (hk : ∀ a, DSubInstrument.Intertwines (V.amplifyLeft B) (fun _ ↦ V.amplifyLeft C)
      (R₁.run₂ .instruments (k₁ a)) (R₂.run₂ .instruments (k₂ a))) :
    DSubInstrument.Intertwines (V.amplifyLeft A) (fun _ ↦ V.amplifyLeft C)
      (R₁.run₂ .instruments (x₁.bind k₁)) (R₂.run₂ .instruments (x₂.bind k₂)) := by
  rw [QuantumRuntime.run₂_bind, QuantumRuntime.run₂_bind]
  exact hx.bind hk

/-- A local operation followed by programs that intertwine intertwines. -/
theorem intertwines_run₂_act_bind {A B C : QReg} {α β : Type} (p : SubInstrument A B α)
    {k₁ : α → QComp spec₁ B C β} {k₂ : α → QComp spec₂ B C β}
    (hk : ∀ a, DSubInstrument.Intertwines (V.amplifyLeft B) (fun _ ↦ V.amplifyLeft C)
      (R₁.run₂ .instruments (k₁ a)) (R₂.run₂ .instruments (k₂ a))) :
    DSubInstrument.Intertwines (V.amplifyLeft A) (fun _ ↦ V.amplifyLeft C)
      (R₁.run₂ .instruments ((QComp.act p).bind k₁))
      (R₂.run₂ .instruments ((QComp.act p).bind k₂)) := by
  rw [QuantumRuntime.run₂_act_bind, QuantumRuntime.run₂_act_bind]
  exact (DSubInstrument.Intertwines.frame_amplifyLeft p V).bind hk

/-- Relabellings that compose to the identity, around the identity, are the identity. -/
theorem relabel_comp_id_comp {P Q S : Type} [Fintype P] [DecidableEq P] [Fintype Q]
    [DecidableEq Q] [Fintype S] [DecidableEq S] (e₁ : P ≃ Q) (e₂ : Q ≃ S) (e₃ : S ≃ P)
    (h : ∀ p, e₃ (e₂ (e₁ p)) = p) :
    (SubInstrument.relabel e₃).branch () ∘ₗ ((SubInstrument.relabel e₂).branch () ∘ₗ
      LinearMap.id) ∘ₗ (SubInstrument.relabel e₁).branch () = LinearMap.id := by
  have h' : ∀ x, e₁.symm (e₂.symm (e₃.symm x)) = x := fun x ↦ by
    rw [← h (e₁.symm (e₂.symm (e₃.symm x)))]
    simp
  refine LinearMap.ext fun ρ ↦ ?_
  ext x y
  simp [SubInstrument.relabel_branch_apply, h']

/-- Relabellings around the zero map are the zero map. -/
theorem relabel_comp_zero_comp {P Q Q' S T : Type} [Fintype P] [DecidableEq P] [Fintype Q]
    [DecidableEq Q] [Fintype Q'] [DecidableEq Q'] [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] (e₁ : P ≃ Q) (e₂ : Q' ≃ S) (e₃ : S ≃ T) :
    (SubInstrument.relabel e₃).branch () ∘ₗ ((SubInstrument.relabel e₂).branch () ∘ₗ
      (0 : MatrixMap Q Q')) ∘ₗ (SubInstrument.relabel e₁).branch () = 0 := by
  simp

/-- The run of a read-style call: a call of port `i` beside `B`, a relabelling back to `B`, and
the call's result. -/
theorem run₂_query_relabel {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)
    (i : spec.Port) (B : QReg) (ℓ : B ≃ spec.In i × B) (e : spec.Out i × B ≃ B) :
    R.run₂ .instruments ((QuantumComp₂.query (L := LocalSig.instruments.{0}) i B ℓ).bind fun r ↦
      (QComp.act (A := QReg.of (spec.Out i × B)) (B := B) (SubInstrument.relabel e)).bind
        fun _ ↦ QuantumComp₂.pure r) =
      (R.queryStep i B ℓ).bind fun r ↦
        ((SubInstrument.relabel e).frame R.D).bind fun _ ↦ SubInstrument.pure r := by
  simp only [QuantumRuntime.run₂_query_bind, QuantumRuntime.run₂_act_bind,
    QuantumRuntime.run₂_pure]

/-- Runs on a fixed final register that intertwine intertwine as runs. -/
theorem intertwines_run_of_run₂ {A B : QReg} {α : Type} {x₁ : QComp spec₁ A B α}
    {x₂ : QComp spec₂ A B α}
    (h : DSubInstrument.Intertwines (V.amplifyLeft A) (fun _ ↦ V.amplifyLeft B)
      (R₁.run₂ .instruments x₁) (R₂.run₂ .instruments x₂)) :
    DSubInstrument.Intertwines (V.amplifyLeft A)
      (fun p : Σ u, QuantumComp₂.Leaf B α u ↦ V.amplifyLeft p.1)
      (R₁.run .instruments x₁) (R₂.run .instruments x₂) := by
  rintro ⟨u, hu, a⟩
  subst hu
  exact h a

/-- Runs that intertwine intertwine on a fixed final register. -/
theorem intertwines_run₂_of_run {A B : QReg} {α : Type} {x₁ : QComp spec₁ A B α}
    {x₂ : QComp spec₂ A B α}
    (h : DSubInstrument.Intertwines (V.amplifyLeft A)
      (fun p : Σ u, QuantumComp₂.Leaf B α u ↦ V.amplifyLeft p.1)
      (R₁.run .instruments x₁) (R₂.run .instruments x₂)) :
    DSubInstrument.Intertwines (V.amplifyLeft A) (fun _ ↦ V.amplifyLeft B)
      (R₁.run₂ .instruments x₁) (R₂.run₂ .instruments x₂) :=
  fun a ↦ h ⟨B, rfl, a⟩

/-- Sequences whose parts intertwine intertwine. -/
theorem intertwines_run_bind {X Y : QReg → Type} {A : QReg}
    {x₁ : QuantumComp LocalSig.instruments.{0} spec₁ X A}
    {x₂ : QuantumComp LocalSig.instruments.{0} spec₂ X A}
    {k₁ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} spec₁ Y u}
    {k₂ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} spec₂ Y u}
    (hx : DSubInstrument.Intertwines (V.amplifyLeft A) (fun p : Σ u, X u ↦ V.amplifyLeft p.1)
      (R₁.run .instruments x₁) (R₂.run .instruments x₂))
    (hk : ∀ p : Σ u, X u, DSubInstrument.Intertwines (V.amplifyLeft p.1)
      (fun q : Σ u, Y u ↦ V.amplifyLeft q.1) (R₁.run .instruments (k₁ p.1 p.2))
      (R₂.run .instruments (k₂ p.1 p.2))) :
    DSubInstrument.Intertwines (V.amplifyLeft A) (fun q : Σ u, Y u ↦ V.amplifyLeft q.1)
      (R₁.run .instruments (x₁.bind k₁)) (R₂.run .instruments (x₂.bind k₂)) := by
  rw [QuantumRuntime.run_bind, QuantumRuntime.run_bind]
  exact hx.bind hk

/-- **Substitutions whose commands intertwine** give programs that intertwine. -/
theorem intertwines_substitute
    {σ₁ : CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₁)}
    {σ₂ : CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₂)}
    (h : ∀ (A : QReg) c, DSubInstrument.Intertwines (V.amplifyLeft A)
      (fun p : Σ u, {b : (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀).B A c //
        (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀).src A c b = u} ↦
          V.amplifyLeft p.1)
      (R₁.run .instruments (σ₁ A c)) (R₂.run .instruments (σ₂ A c)))
    {Y : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀) Y A) :
    DSubInstrument.Intertwines (V.amplifyLeft A) (fun p : Σ u, Y u ↦ V.amplifyLeft p.1)
      (R₁.run .instruments (x.substitute σ₁)) (R₂.run .instruments (x.substitute σ₂)) := by
  induction x using IFreeM.inductionOn with
  | pure A y => exact intertwines_run_pure y
  | liftBind A c next ih =>
    refine intertwines_run_bind (h A c) fun p ↦ ?_
    obtain ⟨u, b, hb⟩ := p
    subst hb
    exact ih b

/-- A program that returns `v` with certainty, through the identity, collapses a sequence. -/
theorem run₂_bind_of_classicalOn_pure {A B : QReg} {α β : Type} {x : QComp spec₁ A A α} {v : α}
    (hx : ClassicalOn R₁ x (pure v) LinearMap.id) (k : α → QComp spec₁ A B β) :
    R₁.run₂ .instruments (x.bind k) = R₁.run₂ .instruments (k v) := by
  classical
  have hb : ∀ a, (R₁.run₂ .instruments x).branch a = if a = v then LinearMap.id else 0 := by
    intro a
    rw [hx a, prEvent_pure]
    by_cases ha : a = v
    · subst ha
      simp
    · simp [Ne.symm ha, ha]
  refine DSubInstrument.ext (funext fun c ↦ LinearMap.ext fun ρ ↦ ?_)
  rw [QuantumRuntime.run₂_bind, SubInstrument.bind, DSubInstrument.branch_bind_apply,
    tsum_eq_single v fun a ha ↦ by rw [hb a, ite_eq_right ha, LinearMap.zero_apply, map_zero],
    hb v, ite_eq_left rfl, LinearMap.id_apply]

/-- Runs that intertwine through an isometry `K` of the runtime registers, from initial states it
relates, have the same observed laws. -/
theorem evalDistMap_eq_of_intertwines {K : Matrix R₂.D R₁.D ℂ} (hK : Kᴴ * K = 1)
    (hinit : MatrixMap.conj K R₁.init.matrix = R₂.init.matrix)
    {Y : QReg → Type} {A : QReg} {x₁ : QuantumComp LocalSig.instruments.{0} spec₁ Y A}
    {x₂ : QuantumComp LocalSig.instruments.{0} spec₂ Y A}
    (h : DSubInstrument.Intertwines ((MatrixMap.conj K).amplifyLeft A)
      (fun p : Σ u, Y u ↦ (MatrixMap.conj K).amplifyLeft p.1) (R₁.run .instruments x₁)
      (R₂.run .instruments x₂))
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ] (f : (Σ u, Y u) → γ) :
    R₁.evalDistMap .instruments x₁ ρ f = R₂.evalDistMap .instruments x₂ ρ f := by
  have htr : ∀ p, (R₂.jointPost .instruments x₂ ρ p).matrix.trace =
      (R₁.jointPost .instruments x₁ ρ p).matrix.trace := fun p ↦ by
    rw [QuantumRuntime.matrix_jointPost, QuantumRuntime.matrix_jointPost, ← hinit,
      ← MatrixMap.amplifyLeft_kronecker, ← LinearMap.comp_apply, h p, LinearMap.comp_apply]
    dsimp only
    rw [MatrixMap.amplifyLeft_conj, MatrixMap.trace_conj_apply, conjTranspose_kronecker,
      conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, hK, one_kronecker_one,
      Matrix.one_mul]
  simp only [QuantumRuntime.evalDistMap, htr]

end intertwine

/-! ## Averages of laws, generically

Stated for abstract `X`, `Z` so that the kernel never unfolds a sum over the concrete functions;
the law of each summand is a named function `G`, so that no redex appears under a scalar. -/

section average

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg} {γ : Type*}
  [MeasurableSpace γ]

/-- The uniform-function experiment of `x` with a constant observation is the average of laws
`G t` that equal the runs against `t`. -/
theorem spongeEvalDistMap_eq_sum_smul (I : L.Interp) (x : QuantumComp L (spongeSpec X Z) W A)
    (ρ : SubState A) (f : (Σ u, W u) → γ) (G : (Z → X) × (X → Z) × (X → Z) → Measure γ)
    (h : ∀ t, (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap I x ρ f = G t) :
    spongeEvalDistMap I x ρ (fun _ ↦ f) =
      ∑ t, (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ • G t := by
  rw [spongeEvalDistMap_eq_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun t _ ↦ congrArg _ (h t)

/-- The QRPM with a constant observation is the average over `π` of laws `G π` that equal the
uniform-function experiments of the simulations. -/
theorem qrpmEvalDistMap_eq_sum_smul (I : L.Interp) (x : QuantumComp L (qrpmSpec (X × Z)) W A)
    (ρ : SubState A) (f : (Σ u, W u) → γ) (G : Equiv.Perm (X × Z) → Measure γ)
    (h : ∀ π, spongeEvalDistMap .instruments (simulate I π x) ρ (fun _ ↦ f) = G π) :
    qrpmEvalDistMap I x ρ (fun _ ↦ f) =
      (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ • ∑ π, G π := by
  rw [qrpmEvalDistMap_eq_simulate]
  exact congrArg _ (Finset.sum_congr rfl fun π _ ↦ h π)

end average

/-! ## The block of the classical register -/

section block

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

/-- The column `|((), W, m)⟩` of the classical register of the read runtime. -/
def hwCol (W : Hw X Z) (m : M) : Matrix (Unit × Hw X Z × M) Unit ℂ :=
  (rowAt (((), W, m) : Unit × Hw X Z × M))ᴴ

/-- The embedding of the trivial register as the block `((), W, m)`. -/
noncomputable def hwAt (W : Hw X Z) (m : M) : MatrixMap Unit (Unit × Hw X Z × M) :=
  MatrixMap.conj (hwCol W m)

theorem conjTranspose_hwCol_mul_self (W : Hw X Z) (m : M) : (hwCol W m)ᴴ * hwCol W m = 1 := by
  ext ⟨⟩ ⟨⟩
  simp [hwCol, rowAt, Matrix.mul_apply]

/-- The embedding sends the trivial state to the basis state of the block. -/
theorem hwAt_basis (W : Hw X Z) (m : M) :
    hwAt W m (SubState.basis ()).matrix =
      (SubState.basis (((), W, m) : Unit × Hw X Z × M)).matrix := by
  rw [SubState.matrix_basis, SubState.matrix_basis, hwAt, MatrixMap.conj_apply]
  ext u u'
  simp [hwCol, rowAt, Matrix.mul_apply, Matrix.single_apply]
  by_cases h₁ : u = ((), W, m)
  · by_cases h₂ : u' = ((), W, m)
    · simp [h₁, h₂]
    · simp [h₂, Ne.symm h₂]
  · simp [h₁, Ne.symm h₁]

/-- A table oracle beside the column `|t⟩` is the oracle unitary of `read t`. -/
theorem tableOracle_mul_one_kronecker_colAt {T A Y : Type} [Fintype T] [DecidableEq T] [Fintype A]
    [DecidableEq A] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] (read : T → A → Y) (t : T) :
    tableOracle read * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (rowAt t)ᴴ) =
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (rowAt t)ᴴ) *
        (oracleUnitary (read t) ⊗ₖ (1 : Matrix Unit Unit ℂ)) := by
  have h := congrArg conjTranspose (oracleUnitary_kronecker_one_mul_one_kronecker_rowAt read t)
  simp only [conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one] at h
  have hO : (oracleUnitary (read t))ᴴ * oracleUnitary (read t) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (oracleUnitary_mem_unitaryGroup _)
  have hT : tableOracle read * (tableOracle read)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp
      (Matrix.mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self read))
  have hO' : ((oracleUnitary (read t))ᴴ ⊗ₖ (1 : Matrix Unit Unit ℂ)) *
      (oracleUnitary (read t) ⊗ₖ (1 : Matrix Unit Unit ℂ)) = 1 := by
    rw [← mul_kronecker_mul, hO, Matrix.one_mul, one_kronecker_one]
  calc tableOracle read * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (rowAt t)ᴴ)
      = tableOracle read * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (rowAt t)ᴴ) *
          (((oracleUnitary (read t))ᴴ ⊗ₖ (1 : Matrix Unit Unit ℂ)) *
            (oracleUnitary (read t) ⊗ₖ (1 : Matrix Unit Unit ℂ))) := by rw [hO', Matrix.mul_one]
    _ = tableOracle read * (((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (rowAt t)ᴴ) *
          ((oracleUnitary (read t))ᴴ ⊗ₖ (1 : Matrix Unit Unit ℂ))) *
            (oracleUnitary (read t) ⊗ₖ (1 : Matrix Unit Unit ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h, ← Matrix.mul_assoc, hT, Matrix.one_mul]

/-- A partial classical map on a basis column. -/
theorem clsMap_mul_colAt {B : Type} [Fintype B] [DecidableEq B] (p : B → Prop) [DecidablePred p]
    (φ : B → B) (b : B) :
    clsMap p φ * (rowAt b)ᴴ = if p b then (rowAt (φ b))ᴴ else 0 := by
  ext b' ⟨⟩
  by_cases hb : p b
  · simp [clsMap, rowAt, Matrix.mul_apply, hb, conjTranspose_apply]
  · simp [clsMap, rowAt, Matrix.mul_apply, hb, conjTranspose_apply]

/-- The memory update of a read that keeps the memory. -/
def keepMem {V : Type} (m : M) (_ : Option V) : M :=
  m

/-- The read keeps the memory. -/
def HwRead.KeepsMem : HwRead X Z M → Prop
  | .readH _ upd => upd = keepMem
  | .readK _ upd => upd = keepMem
  | .readK' _ upd => upd = keepMem

/-- The result of a read on the block `(W, m)` against `t`: the value of `overwrite W t` at the
cell, and the memory. -/
def readAnswer (t : (Z → X) × (X → Z) × (X → Z)) (W : Hw X Z) (m : M) :
    (c : HwRead X Z M) → c.Result
  | .readH z _ => (some ((overwrite W t).1 z), m)
  | .readK x _ => (some ((overwrite W t).2.1 x), m)
  | .readK' x _ => (some ((overwrite W t).2.2 x), m)

/-- The results of a read have decidable equality. -/
instance instDecidableEqHwReadResult (c : HwRead X Z M) : DecidableEq c.Result := by
  cases c <;> exact inferInstanceAs (DecidableEq (Option _ × M))

omit [Fintype M] in
theorem branch_pure_eq_ite {A : Type*} [Fintype A] {α : Type} [DecidableEq α] (a₀ a : α) :
    (SubInstrument.pure a₀ : SubInstrument A A α).branch a =
      if a = a₀ then LinearMap.id else 0 := by
  by_cases h : a = a₀
  · subst h
    rw [SubInstrument.branch_pure_self, ite_eq_left rfl]
  · rw [SubInstrument.branch_pure_of_ne h, ite_eq_right h]

variable [AddCommGroup X] [AddCommGroup Z]

/-- **The sponge ports on the block `(W, m)`** are the oracles of `overwrite W t`. -/
theorem spongeFnHw_step_intertwine (t : (Z → X) × (X → Z) × (X → Z)) (W : Hw X Z) (m : M)
    (i : SpongePort) (r : Unit) :
    ((spongeFnHw X Z t W m).toRuntime.step i).branch r ∘ₗ
        (hwAt W m).amplifyLeft ((spongeSpec X Z).In i) =
      (hwAt W m).amplifyLeft ((spongeSpec X Z).Out i) ∘ₗ
        ((spongeFnRuntime (overwrite W t).1 (overwrite W t).2.1 (overwrite W t).2.2).step i).branch
          r := by
  cases i
  · change MatrixMap.conj (tableOracle fun u : Unit × Hw X Z × M ↦ (overwrite u.2.1 t).1) ∘ₗ
        (MatrixMap.conj (hwCol W m)).amplifyLeft (Z × X) =
      (MatrixMap.conj (hwCol W m)).amplifyLeft (Z × X) ∘ₗ
        (MatrixMap.conj (oracleUnitary (overwrite W t).1)).amplify Unit
    rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
      ← MatrixMap.conj_mul]
    exact congrArg MatrixMap.conj (tableOracle_mul_one_kronecker_colAt
      (fun u : Unit × Hw X Z × M ↦ (overwrite u.2.1 t).1) ((), W, m))
  · change MatrixMap.conj (tableOracle fun u : Unit × Hw X Z × M ↦ (overwrite u.2.1 t).2.1) ∘ₗ
        (MatrixMap.conj (hwCol W m)).amplifyLeft (X × Z) =
      (MatrixMap.conj (hwCol W m)).amplifyLeft (X × Z) ∘ₗ
        (MatrixMap.conj (oracleUnitary (overwrite W t).2.1)).amplify Unit
    rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
      ← MatrixMap.conj_mul]
    exact congrArg MatrixMap.conj (tableOracle_mul_one_kronecker_colAt
      (fun u : Unit × Hw X Z × M ↦ (overwrite u.2.1 t).2.1) ((), W, m))
  · change MatrixMap.conj (tableOracle fun u : Unit × Hw X Z × M ↦ (overwrite u.2.1 t).2.2) ∘ₗ
        (MatrixMap.conj (hwCol W m)).amplifyLeft (X × Z) =
      (MatrixMap.conj (hwCol W m)).amplifyLeft (X × Z) ∘ₗ
        (MatrixMap.conj (oracleUnitary (overwrite W t).2.2)).amplify Unit
    rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
      ← MatrixMap.conj_mul]
    exact congrArg MatrixMap.conj (tableOracle_mul_one_kronecker_colAt
      (fun u : Unit × Hw X Z × M ↦ (overwrite u.2.1 t).2.2) ((), W, m))

/-- A program over the sponge ports runs on the block `(W, m)` as against `overwrite W t`. -/
theorem intertwines_run_spongeFnHw (t : (Z → X) × (X → Z) × (X → Z)) (W : Hw X Z) (m : M)
    {L : LocalSig.{u, v}} (I : L.Interp) {Y : QReg → Type w} {A : QReg}
    (x : QuantumComp L (spongeSpec X Z) Y A) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A)
      (fun p : Σ u, Y u ↦ (hwAt W m).amplifyLeft p.1)
      ((spongeFnRuntime (overwrite W t).1 (overwrite W t).2.1 (overwrite W t).2.2).run I x)
      ((spongeFnHw X Z t W m).toRuntime.run I x) :=
  QuantumRuntime.intertwines_run
    (R₁ := spongeFnRuntime (overwrite W t).1 (overwrite W t).2.1 (overwrite W t).2.2)
    (R₂ := (spongeFnHw X Z t W m).toRuntime) (V := hwAt W m) I
    (fun i r ↦ spongeFnHw_step_intertwine t W m i r) x

/-- A program over the QRPM against `φ = spongePerm (overwrite W t) π` intertwines with its
simulation, lifted to the read signature, on the block `(W, m)`. -/
theorem intertwines_simulate (π : Equiv.Perm (X × Z)) (t : (Z → X) × (X → Z) × (X → Z))
    (W : Hw X Z) (m : M) {Y : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (qrpmSpec (X × Z)) Y A) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A)
      (fun p : Σ u, Y u ↦ (hwAt W m).amplifyLeft p.1)
      ((permutationRuntime (spongePerm (overwrite W t) π)).run .instruments x)
      ((spongeFnReadRuntime X Z t W m).run .instruments
        ((simulate LocalSig.Interp.instruments π x).liftOrdinary (t := hwReadCmdSpec X Z M))) := by
  have e := run_simulate LocalSig.Interp.instruments π (overwrite W t) x
  have hsim := intertwines_run_spongeFnHw t W m LocalSig.Interp.instruments.{0}
    (simulate LocalSig.Interp.instruments π x)
  rw [e] at hsim
  have h : (spongeFnReadRuntime X Z t W m).run .instruments
      ((simulate LocalSig.Interp.instruments π x).liftOrdinary (t := hwReadCmdSpec X Z M)) =
        (spongeFnHw X Z t W m).toRuntime.run .instruments
          (simulate LocalSig.Interp.instruments.{0} π x) :=
    QuantumRuntime.run_liftOrdinary _ _ _ _
  rw [h]
  exact hsim

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **A read that keeps the memory, on the block `(W, m)`**, returns `readAnswer` and keeps the
block. -/
theorem fnReadKraus_mul_hwCol (t : (Z → X) × (X → Z) × (X → Z)) (W : Hw X Z) (m : M)
    (c : HwRead X Z M) (hc : c.KeepsMem) (r : c.Result) :
    fnReadKraus t c r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwCol W m) =
      if r = readAnswer t W m c then (1 : Matrix Unit Unit ℂ) ⊗ₖ hwCol W m else 0 := by
  cases c with
  | readH z upd =>
    change upd = keepMem at hc
    subst hc
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsMap (fun u : Unit × Hw X Z × M ↦
        u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).1 z))
        (fun u ↦ (u.1, u.2.1, keepMem r.2 r.1))) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwCol W m) = _
    rw [← mul_kronecker_mul, Matrix.one_mul, hwCol, clsMap_mul_colAt]
    by_cases h : r = (some ((overwrite W t).1 z), m)
    · subst h
      simp [readAnswer, keepMem]
    · have h' : ¬ (m = r.2 ∧ r.1 = some ((overwrite W t).1 z)) := fun h' ↦
        h (Prod.ext h'.2 h'.1.symm)
      simp [readAnswer, h, h']
  | readK x upd =>
    change upd = keepMem at hc
    subst hc
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsMap (fun u : Unit × Hw X Z × M ↦
        u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).2.1 x))
        (fun u ↦ (u.1, u.2.1, keepMem r.2 r.1))) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwCol W m) = _
    rw [← mul_kronecker_mul, Matrix.one_mul, hwCol, clsMap_mul_colAt]
    by_cases h : r = (some ((overwrite W t).2.1 x), m)
    · subst h
      simp [readAnswer, keepMem]
    · have h' : ¬ (m = r.2 ∧ r.1 = some ((overwrite W t).2.1 x)) := fun h' ↦
        h (Prod.ext h'.2 h'.1.symm)
      simp [readAnswer, h, h']
  | readK' x upd =>
    change upd = keepMem at hc
    subst hc
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsMap (fun u : Unit × Hw X Z × M ↦
        u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).2.2 x))
        (fun u ↦ (u.1, u.2.1, keepMem r.2 r.1))) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwCol W m) = _
    rw [← mul_kronecker_mul, Matrix.one_mul, hwCol, clsMap_mul_colAt]
    by_cases h : r = (some ((overwrite W t).2.2 x), m)
    · subst h
      simp [readAnswer, keepMem]
    · have h' : ¬ (m = r.2 ∧ r.1 = some ((overwrite W t).2.2 x)) := fun h' ↦
        h (Prod.ext h'.2 h'.1.symm)
      simp [readAnswer, h, h']

/-! ## Read programs -/

/-- The held register `B` as the trivial register of a read port beside `B`. -/
def readSplit (c : HwRead X Z M) (B : QReg) : B ≃ (hwReadSpec X Z M).In (.inr c) × B :=
  (Equiv.uniqueProd B Unit).symm

/-- The trivial register of a read port beside `B` as `B`. -/
def readJoin (c : HwRead X Z M) (B : QReg) : (hwReadSpec X Z M).Out (.inr c) × B ≃ B :=
  Equiv.uniqueProd B Unit

/-- **One read port beside a held register `B`**: relabel `B` as the port's trivial register
beside `B`, call the port, relabel back, and return the read's result. -/
noncomputable def readCall (c : HwRead X Z M) (B : QReg) :
    QComp (hwReadSpec X Z M) B B c.Result :=
  (QuantumComp₂.query (L := LocalSig.instruments) (spec := hwReadSpec X Z M) (.inr c) B
      (readSplit c B)).bind fun r ↦
    (QComp.act (A := QReg.of ((hwReadSpec X Z M).Out (.inr c) × B)) (B := B)
      (SubInstrument.relabel (readJoin c B))).bind fun _ ↦ QuantumComp₂.pure r

/-- **A program that returns `a₀` with certainty on the block `(W, m)`**: against
`spongeFnReadRuntime X Z t W m`, from any state of its held register beside the block `(W, m)`
of the classical register, it returns `a₀`, leaves the held register and the block untouched,
and returns nothing else. -/
def ReadsTo (t : (Z → X) × (X → Z) × (X → Z)) (W : Hw X Z) (m : M) {B : QReg} {α : Type}
    (x : QComp (hwReadSpec X Z M) B B α) (a₀ : α) : Prop :=
  ((spongeFnReadRuntime X Z t W m).run₂ .instruments x).branch a₀ ∘ₗ (hwAt W m).amplifyLeft B =
      (hwAt W m).amplifyLeft B ∧
    ∀ a ≠ a₀, ((spongeFnReadRuntime X Z t W m).run₂ .instruments x).branch a ∘ₗ
      (hwAt W m).amplifyLeft B = 0

variable {t : (Z → X) × (X → Z) × (X → Z)} {W : Hw X Z} {m : M} {B : QReg}

theorem readsTo_pure {α : Type} (a : α) :
    ReadsTo t W m (QuantumComp₂.pure a : QComp (hwReadSpec X Z M) B B α) a := by
  refine ⟨?_, fun a' ha' ↦ ?_⟩
  · rw [QuantumRuntime.run₂_pure, SubInstrument.branch_pure_self]
    exact LinearMap.id_comp _
  · rw [QuantumRuntime.run₂_pure, SubInstrument.branch_pure_of_ne ha']
    exact LinearMap.zero_comp _

theorem ReadsTo.bind {α β : Type} {x : QComp (hwReadSpec X Z M) B B α} {a₀ : α}
    {k : α → QComp (hwReadSpec X Z M) B B β} {b₀ : β} (hx : ReadsTo t W m x a₀)
    (hk : ReadsTo t W m (k a₀) b₀) : ReadsTo t W m (x.bind k) b₀ := by
  have key : ∀ c, ((spongeFnReadRuntime X Z t W m).run₂ .instruments (x.bind k)).branch c ∘ₗ
      (hwAt W m).amplifyLeft B =
      ((spongeFnReadRuntime X Z t W m).run₂ .instruments (k a₀)).branch c ∘ₗ
        (hwAt W m).amplifyLeft B := by
    intro c
    refine LinearMap.ext fun ρ ↦ ?_
    have h₀ : ((spongeFnReadRuntime X Z t W m).run₂ .instruments x).branch a₀
        ((hwAt W m).amplifyLeft B ρ) = (hwAt W m).amplifyLeft B ρ :=
      LinearMap.congr_fun hx.1 ρ
    have h₁ : ∀ a ≠ a₀, ((spongeFnReadRuntime X Z t W m).run₂ .instruments x).branch a
        ((hwAt W m).amplifyLeft B ρ) = 0 := fun a ha ↦ LinearMap.congr_fun (hx.2 a ha) ρ
    change ((spongeFnReadRuntime X Z t W m).run₂ .instruments (x.bind k)).branch c
        ((hwAt W m).amplifyLeft B ρ) =
      ((spongeFnReadRuntime X Z t W m).run₂ .instruments (k a₀)).branch c
        ((hwAt W m).amplifyLeft B ρ)
    rw [QuantumRuntime.run₂_bind]
    erw [DSubInstrument.branch_bind_apply]
    rw [tsum_eq_single a₀ fun a ha ↦ by erw [h₁ a ha, map_zero]]
    erw [h₀]
  exact ⟨(key b₀).trans hk.1, fun c hc ↦ (key c).trans (hk.2 c hc)⟩

theorem ReadsTo.map {α β : Type} {x : QComp (hwReadSpec X Z M) B B α} {a₀ : α}
    (hx : ReadsTo t W m x a₀) (f : α → β) : ReadsTo t W m (x.map f) (f a₀) := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact hx.bind (readsTo_pure (f a₀))

/-- **A read that keeps the memory returns its answer with certainty on the block.** -/
theorem readsTo_readCall (c : HwRead X Z M) (hc : c.KeepsMem) (B : QReg) :
    ReadsTo t W m (readCall c B) (readAnswer t W m c) := by
  set V := hwAt (M := M) W m
  set R := spongeFnReadRuntime X Z t W m
  set a₀ := readAnswer t W m c
  have hstep : DSubInstrument.Intertwines (V.amplifyLeft Unit) (fun _ ↦ V.amplifyLeft Unit)
      (SubInstrument.pure a₀ : SubInstrument (Unit × Unit) (Unit × Unit) c.Result)
      (R.step (.inr c)) := fun a ↦ by
    change MatrixMap.conj (fnReadKraus t c a) ∘ₗ (MatrixMap.conj (hwCol W m)).amplifyLeft Unit =
      _ ∘ₗ _
    rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, fnReadKraus_mul_hwCol t W m c hc,
      branch_pure_eq_ite]
    by_cases ha : a = a₀
    · rw [ite_eq_left ha, ite_eq_left ha, LinearMap.comp_id, ← MatrixMap.amplifyLeft_conj]
      rfl
    · rw [ite_eq_right ha, ite_eq_right ha, MatrixMap.conj_zero, LinearMap.comp_zero]
  have hq : DSubInstrument.Intertwines (V.amplifyLeft B) (fun _ ↦ V.amplifyLeft (Unit × B))
      ((SubInstrument.relabel (QuantumRuntime.queryEquivIn (readSplit c B) Unit)).bind
        fun _ ↦ ((SubInstrument.pure a₀ : SubInstrument (Unit × Unit) (Unit × Unit) c.Result).frame
          B).bind fun r ↦ (SubInstrument.relabel (QuantumRuntime.queryEquivOut Unit Unit B)).bind
            fun _ ↦ SubInstrument.pure r)
      (R.queryStep (.inr c) B (readSplit c B)) :=
    (QuantumRuntime.intertwines_relabel_queryEquivIn V (readSplit c B)).bind
      fun _ ↦ (hstep.frame B).bind fun r ↦
        (QuantumRuntime.intertwines_relabel_queryEquivOut V Unit B).bind fun _ ↦
          DSubInstrument.Intertwines.ret (fun _ ↦ V.amplifyLeft (Unit × B)) r
  have hR : R.run₂ .instruments (readCall c B) =
      (R.queryStep (.inr c) B (readSplit c B)).bind fun r ↦
        ((SubInstrument.relabel (readJoin c B)).frame R.D).bind fun _ ↦
          SubInstrument.pure r := by
    exact run₂_query_relabel R (.inr c) B (readSplit c B) (readJoin c B)
  have hrun : DSubInstrument.Intertwines (V.amplifyLeft B) (fun _ ↦ V.amplifyLeft B)
      (((SubInstrument.relabel (QuantumRuntime.queryEquivIn (readSplit c B) Unit)).bind
        fun _ ↦ ((SubInstrument.pure a₀ : SubInstrument (Unit × Unit) (Unit × Unit)
          c.Result).frame B).bind fun r ↦
            (SubInstrument.relabel (QuantumRuntime.queryEquivOut Unit Unit B)).bind
              fun _ ↦ SubInstrument.pure r).bind fun r ↦
        ((SubInstrument.relabel (readJoin c B)).frame Unit).bind fun _ ↦
          SubInstrument.pure r)
      (R.run₂ .instruments (readCall c B)) := by
    rw [hR]
    exact hq.bind fun r ↦
      (DSubInstrument.Intertwines.frame_amplifyLeft
        (SubInstrument.relabel (readJoin c B)) V).bind fun _ ↦
          DSubInstrument.Intertwines.ret (fun _ ↦ V.amplifyLeft B) r
  have hbr : ∀ a, (R.run₂ .instruments (readCall c B)).branch a ∘ₗ V.amplifyLeft B =
      V.amplifyLeft B ∘ₗ (if a = a₀ then LinearMap.id else 0) := by
    intro a
    refine (hrun a).trans ?_
    congr 1
    have hJ : ((SubInstrument.relabel (readJoin c B)).frame Unit).branch () =
        (SubInstrument.relabel ((readJoin c B).prodCongr (Equiv.refl Unit))).branch () :=
      congrArg (fun p ↦ DSubInstrument.branch p ()) (SubInstrument.frame_relabel _ Unit)
    erw [DSubInstrument.branch_bind_bind_unit_ret, hJ, DSubInstrument.branch_bind_unit,
      DSubInstrument.branch_bind_bind_unit_ret, DSubInstrument.branch_frame_apply,
      branch_pure_eq_ite]
    by_cases ha : a = a₀
    · erw [ite_eq_left ha, ite_eq_left ha, MatrixMap.amplify_id]
      exact relabel_comp_id_comp _ _ _ fun _ ↦ rfl
    · erw [ite_eq_right ha, ite_eq_right ha, MatrixMap.amplify_zero]
      exact relabel_comp_zero_comp _ _ _
  refine ⟨(hbr a₀).trans ?_, fun a ha ↦ (hbr a).trans ?_⟩
  · rw [ite_eq_left rfl]
    exact LinearMap.comp_id _
  · rw [ite_eq_right ha]
    exact LinearMap.comp_zero _

/-- Read `h` at `z` through its read port beside `B`, logged. -/
noncomputable def rdH (B : QReg) (z : Z) :
    StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) X :=
  fun log ↦ (readCall (.readH z keepMem) B).bind fun r ↦
    QuantumComp₂.pure (r.1.getD 0, log ++ [.h z (r.1.getD 0)])

/-- Read `k` at `x` through its read port beside `B`, logged. -/
noncomputable def rdK (B : QReg) (x : X) :
    StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) Z :=
  fun log ↦ (readCall (.readK x keepMem) B).bind fun r ↦
    QuantumComp₂.pure (r.1.getD 0, log ++ [.k x (r.1.getD 0)])

/-- Read `k'` at `x` through its read port beside `B`, logged. -/
noncomputable def rdK' (B : QReg) (x : X) :
    StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) Z :=
  fun log ↦ (readCall (.readK' x keepMem) B).bind fun r ↦
    QuantumComp₂.pure (r.1.getD 0, log ++ [.k' x (r.1.getD 0)])

variable (M) in
/-- **One round of the sponge through read ports**, as `evalRoundM`: read `k` at the block
entering `π`, `k'` at the intermediate rate, and `h` at the new capacity. -/
noncomputable def rdRound (π : Equiv.Perm (X × Z)) (B : QReg) (s : X × Z) (b : X) :
    StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) (X × Z) := do
  let xp := s.1 + b
  let a ← rdK B xp
  let p := π (xp, s.2 + a)
  let c ← rdK' B p.1
  let w ← rdH B (p.2 + c)
  pure (p.1 + w, p.2 + c)

/-- A stateful read program that runs as the stateful computation `y` on the block `(W, m)`. -/
def ReadsToS (t : (Z → X) × (X → Z) × (X → Z)) (W : Hw X Z) (m : M) {B : QReg} {α : Type}
    (x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α)
    (y : StateM (List (SpongeRead X Z)) α) : Prop :=
  ∀ s, ReadsTo t W m (x.run s) (y.run s)

theorem readsToS_pure {α : Type} (a : α) :
    ReadsToS t W m (pure a : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α)
      (pure a) :=
  fun s ↦ readsTo_pure (a, s)

theorem ReadsToS.bind {α β : Type}
    {x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α}
    {y : StateM (List (SpongeRead X Z)) α}
    {f : α → StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) β}
    {g : α → StateM (List (SpongeRead X Z)) β} (hx : ReadsToS t W m x y)
    (hf : ∀ a, ReadsToS t W m (f a) (g a)) : ReadsToS t W m (x >>= f) (y >>= g) := by
  intro s
  have hy : (y >>= g).run s = (g (y.run s).1).run (y.run s).2 := rfl
  rw [StateT.run_bind, hy]
  exact (hx s).bind (hf _ _)

theorem ReadsToS.map {α β : Type}
    {x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α}
    {y : StateM (List (SpongeRead X Z)) α} (hx : ReadsToS t W m x y) (f : α → β) :
    ReadsToS t W m (f <$> x) (f <$> y) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact hx.bind fun a ↦ readsToS_pure (f a)

theorem readsToS_rdH (z : Z) :
    ReadsToS t W m (rdH (M := M) B z) (readH (overwrite W t).1 z) := fun s ↦
  show ReadsTo t W m ((readCall (.readH z keepMem) B).bind fun r ↦
      QuantumComp₂.pure (r.1.getD 0, s ++ [.h z (r.1.getD 0)]))
    ((overwrite W t).1 z, s ++ [.h z ((overwrite W t).1 z)]) from
  (readsTo_readCall (.readH z keepMem) rfl B).bind (readsTo_pure _)

theorem readsToS_rdK (x : X) :
    ReadsToS t W m (rdK (M := M) B x) (readK (overwrite W t).2.1 x) := fun s ↦
  show ReadsTo t W m ((readCall (.readK x keepMem) B).bind fun r ↦
      QuantumComp₂.pure (r.1.getD 0, s ++ [.k x (r.1.getD 0)]))
    ((overwrite W t).2.1 x, s ++ [.k x ((overwrite W t).2.1 x)]) from
  (readsTo_readCall (.readK x keepMem) rfl B).bind (readsTo_pure _)

theorem readsToS_rdK' (x : X) :
    ReadsToS t W m (rdK' (M := M) B x) (readK' (overwrite W t).2.2 x) := fun s ↦
  show ReadsTo t W m ((readCall (.readK' x keepMem) B).bind fun r ↦
      QuantumComp₂.pure (r.1.getD 0, s ++ [.k' x (r.1.getD 0)]))
    ((overwrite W t).2.2 x, s ++ [.k' x ((overwrite W t).2.2 x)]) from
  (readsTo_readCall (.readK' x keepMem) rfl B).bind (readsTo_pure _)

variable (π : Equiv.Perm (X × Z))

/-- A round of read ports runs as the logged round against `overwrite W t`. -/
theorem readsToS_rdRound (s : X × Z) (b : X) :
    ReadsToS t W m (rdRound M π B s b)
      (evalRoundM π (readH (overwrite W t).1) (readK (overwrite W t).2.1)
        (readK' (overwrite W t).2.2) s b) := by
  unfold rdRound evalRoundM
  exact (readsToS_rdK _).bind fun _ ↦ (readsToS_rdK' _).bind fun _ ↦ (readsToS_rdH _).bind
    fun _ ↦ readsToS_pure _

theorem readsToS_foldlM (msg : List X) (s : X × Z) :
    ReadsToS t W m (msg.foldlM (rdRound M π B) s)
      (msg.foldlM (evalRoundM π (readH (overwrite W t).1) (readK (overwrite W t).2.1)
        (readK' (overwrite W t).2.2)) s) := by
  induction msg generalizing s with
  | nil => exact readsToS_pure s
  | cons b msg ih =>
    rw [List.foldlM_cons, List.foldlM_cons]
    exact (readsToS_rdRound π s b).bind ih

end block

end Quantum.Sponge

namespace Quantum.SufCma

open Quantum Quantum.Sponge HashSig Common Common.SufCma
open Quantum.Xmss (X Z keccakStateEquiv blocks out256)
open LeanVM.Semantics (KeccakState)

variable {M : Type} [Fintype M] [DecidableEq M]

/-! ## The honest hash through read ports -/

variable (M) in
/-- **The honest hash through read ports**: hash an input by evaluating the sponge on its blocks
through logged read ports of `h`, `k`, `k'` (three per block), as `readHash` does with the
functions. -/
noncomputable def readsImpl (π : Equiv.Perm (X × Z)) (B : QReg) :
    QueryImpl SchemeHashSpec (StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B)) :=
  fun input ↦ out256 <$> (fun s : X × Z ↦ s.1) <$> (blocks input).foldlM (rdRound M π B) (0, 0)

variable (M) in
/-- **A hash-query computation as a program of read ports**: every hash the sponge evaluation
through read ports beside `B`; its result and its reads. -/
noncomputable def readsProgram (π : Equiv.Perm (X × Z)) (B : QReg) {α : Type}
    (x : OracleComp SchemeHashSpec α) :
    QComp (hwReadSpec X Z M) B B (α × List (SpongeRead X Z)) :=
  (simulateQ (readsImpl M π B) x).run []

variable {t : SpongeKeys X Z} {W : Hw X Z} {m : M} {B : QReg} (π : Equiv.Perm (X × Z))

theorem readsToS_readsImpl (input : HashInput) :
    ReadsToS t W m (readsImpl M π B input) (readHash (overwrite W t) π input) :=
  ((readsToS_foldlM π (blocks input) (0, 0)).map fun s ↦ s.1).map out256

theorem readsToS_simulateQ {α : Type} (x : OracleComp SchemeHashSpec α) :
    ReadsToS t W m (simulateQ (readsImpl M π B) x) (simulateQ (readHash (overwrite W t) π) x) := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    rw [simulateQ_pure, simulateQ_pure]
    exact readsToS_pure a
  | query_bind input k ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query]
    exact (readsToS_readsImpl π input).bind ih

/-- **The read program returns the honest evaluation with certainty**: against
`spongeFnReadRuntime X Z t W m` on the block `(W, m)`, the read program of `x` returns
`honestEval (overwrite W t) π x`, the result of `x` with the honest hash and its read log. -/
theorem readsTo_readsProgram {α : Type} (x : OracleComp SchemeHashSpec α) :
    ReadsTo t W m (readsProgram M π B x) (honestEval (overwrite W t) π x) :=
  readsToS_simulateQ π x []

/-- `readsTo_readsProgram` without hardwired cells: the read program returns `honestEval t π x`
on the block `(∅, m)`. -/
theorem readsTo_readsProgram_hwEmpty {α : Type} (x : OracleComp SchemeHashSpec α) :
    ReadsTo t (hwEmpty X Z) m (readsProgram M π B x) (honestEval t π x) :=
  readsTo_readsProgram π x

/-! ## One classical permutation call is one round of reads -/

/-- The run of a simulated program on a fixed final register is its run against `φ`. -/
theorem run₂_simulate (t : SpongeKeys X Z) {A B : QReg} {α : Type}
    (x : QComp (qrpmSpec (X × Z)) A B α) :
    (spongeFnRuntime t.1 t.2.1 t.2.2).run₂ .instruments (simulate .instruments π x) =
      (permutationRuntime (spongePerm t π)).run₂ .instruments x := by
  unfold QuantumRuntime.run₂
  exact congrArg (fun d ↦ DSubInstrument.comap (QuantumComp₂.leafEquiv B α)
    (QuantumComp₂.leafEquiv B α).injective d) (run_simulate .instruments π t x)

/-- **A classical forward call, simulated**, returns `statePerm (spongePerm t π) s` with
certainty and leaves the held register untouched. -/
theorem classicalOn_simulate_permImpl_forward (t : SpongeKeys X Z) (B : QReg) (s : KeccakState) :
    ClassicalOn (spongeFnRuntime t.1 t.2.1 t.2.2)
      (simulate .instruments π (permImpl keccakStateEquiv B (.inr (.forward s))))
      (pure (statePerm (spongePerm t π) s)) LinearMap.id := by
  intro a
  rw [run₂_simulate, permImpl_eq_qrpmImpl]
  exact classicalOn_qrpmImpl keccakStateEquiv B (spongePerm t π) (.inr (.forward s)) a

variable (M) in
/-- **One forward call as reads**: the `k`, `k'`, `h` reads of one round on the state
`keccakStateEquiv s` (the round with the zero block), read back through `keccakStateEquiv`; the
new state and the round's reads. -/
noncomputable def permReads (B : QReg) (s : KeccakState) :
    QComp (hwReadSpec X Z M) B B (KeccakState × List (SpongeRead X Z)) :=
  ((rdRound M π B (keccakStateEquiv s) 0).run []).map
    fun p : (X × Z) × List (SpongeRead X Z) ↦ (keccakStateEquiv.symm p.1, p.2)

/-- **The per-call identity**: the reads of one round return `statePerm (spongePerm t' π) s`
with `t' = overwrite W t`, the state the simulated classical call returns
(`classicalOn_simulate_permImpl_forward`), and the round's three reads. -/
theorem readsTo_permReads (s : KeccakState) :
    ReadsTo t W m (permReads M π B s)
      (statePerm (spongePerm (overwrite W t) π) s,
        roundReads π (overwrite W t).1 (overwrite W t).2.1 (overwrite W t).2.2
          (keccakStateEquiv s) 0) := by
  have h := (readsToS_rdRound (t := t) (W := W) (m := m) (B := B) π (keccakStateEquiv s) 0
    []).map fun p : (X × Z) × List (SpongeRead X Z) ↦ (keccakStateEquiv.symm p.1, p.2)
  have e : (fun p : (X × Z) × List (SpongeRead X Z) ↦ (keccakStateEquiv.symm p.1, p.2))
      ((evalRoundM π (readH (overwrite W t).1) (readK (overwrite W t).2.1)
        (readK' (overwrite W t).2.2) (keccakStateEquiv s) 0).run []) =
      (statePerm (spongePerm (overwrite W t) π) s,
        roundReads π (overwrite W t).1 (overwrite W t).2.1 (overwrite W t).2.2
          (keccakStateEquiv s) 0) := by
    rw [run_evalRoundM_log]
    simp [logStep, absorbStep, statePerm, Equiv.permCongr_apply]
  exact (congrArg (ReadsTo t W m (permReads M π B s)) e).mp h

/-! ## The challenger with honest reads -/

variable {Seed PK SK Req Resp F : Type} (sch : Scheme Seed PK SK Req Resp F)
  (Sch : SchemeWithHash Seed PK SK Req Resp F)

variable (M) in
/-- The signer's answer to the request `r` as reads: relabel the adversary's register, then run
the read program of the hash-query signer. -/
noncomputable def signReads (sk : SK) (r : Req) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec Req Resp (X × Z)).In (.sign r) × E) :
    QComp (hwReadSpec X Z M) A (QReg.of ((advSpec Req Resp (X × Z)).Out (.sign r) × E)) Resp :=
  (QComp.act (B := QReg.of ((advSpec Req Resp (X × Z)).Out (.sign r) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ (readsProgram M π _ (Sch.sign sk r)).map Prod.fst

variable (M) in
/-- **The challenger with honest reads**: a local operation and a permutation call are the
challenger's, simulated given `π` and lifted to the read signature; a signing request is
answered by the read program of the signer (`signReads`). -/
noncomputable def challengeReads (sk : SK) :
    CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec Req Resp (X × Z)))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec X Z M))
  | A, .prim o => (simulate LocalSig.Interp.instruments π
      (challenge sch keccakStateEquiv sk A (.prim o))).liftOrdinary
  | A, .query (.perm p) E ℓ => (simulate LocalSig.Interp.instruments π
      (challenge sch keccakStateEquiv sk A (.query (.perm p) E ℓ))).liftOrdinary
  | _, .query (.sign r) E ℓ =>
      QuantumComp.bind (signReads M π Sch sk r E ℓ) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

variable (M) in
/-- The adversary's program with the challenger with honest reads substituted. -/
noncomputable def challengedReads (sk : SK) {A B : QReg} {α : Type}
    (x : QComp (advSpec Req Resp (X × Z)) A B α) : QComp (hwReadSpec X Z M) A B α :=
  IFreeM.substitute (challengeReads M π sch Sch sk) x

variable (M) in
/-- **G2 with honest reads, after key generation**: from the keys `b.1` (the result of the honest
evaluation `b` of key generation), the adversary against `challengeReads` with its signing
transcript, the verification of its forgery as a read program, and the winning condition. -/
noncomputable def gameReads (A : Adversary PK Req Resp F (X × Z))
    (b : (PK × SK) × List (SpongeRead X Z)) :
    QComp (hwReadSpec X Z M) (QReg.of Unit) (QReg.of Unit) Bool :=
  (challengedReads M π sch Sch b.1.2 (withSignLog (A b.1.1))).bind fun run ↦
    ((readsProgram M π _ (Sch.verify b.1.1 run.1)).map Prod.fst).bind
      fun verified ↦ QuantumComp₂.pure (sch.winningCondition run.2 run.1 && verified)

/-! ## The game and its reads intertwine -/

variable (t W m)

/-- An honest computation that returns `v` with certainty against `φ` intertwines with a read
program that returns `v` with certainty on the block. -/
theorem intertwines_of_classicalOn_readsTo {B : QReg} {α : Type}
    {x₁ : QComp (qrpmSpec (X × Z)) B B α} {x₂ : QComp (hwReadSpec X Z M) B B α} {v : α}
    (h₁ : ClassicalOn (permutationRuntime (spongePerm (overwrite W t) π)) x₁ (pure v)
      LinearMap.id)
    (h₂ : ReadsTo t W m x₂ v) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft B)
      ((permutationRuntime (spongePerm (overwrite W t) π)).run₂ .instruments x₁)
      ((spongeFnReadRuntime X Z t W m).run₂ .instruments x₂) := by
  classical
  intro a
  rw [h₁ a, prEvent_pure]
  by_cases ha : a = v
  · subst ha
    refine h₂.1.trans ?_
    rw [ite_eq_left rfl, ENNReal.toReal_one, Complex.ofReal_one, one_smul]
    exact (LinearMap.comp_id _).symm
  · refine (h₂.2 a ha).trans ?_
    rw [ite_eq_right (Ne.symm ha), ENNReal.toReal_zero, Complex.ofReal_zero, zero_smul]
    exact (LinearMap.comp_zero _).symm

/-- The honest classical computations of the scheme against `φ = spongePerm t π`. -/
theorem classicalOn_toQuantumAt_permImpl (B : QReg) {α : Type}
    (oa : OracleComp RandomPermutationOracles α) :
    ClassicalOn (permutationRuntime (spongePerm t π))
      (oa.toQuantumAt (permImpl keccakStateEquiv B))
      (simulateQ (eagerPermOracles (statePerm (spongePerm t π))) oa) LinearMap.id := by
  rw [permImpl_eq_qrpmImpl]
  exact classicalOn_toQuantumAt_qrpmImpl keccakStateEquiv B (spongePerm t π) oa

/-- **The challenger and the challenger with honest reads intertwine on every command**, for a
scheme `sch` that is the hash-query scheme `Sch` over `π`. -/
theorem intertwines_challenge (hsch : sch = Sch.overPermutation) (sk : SK) (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec Req Resp (X × Z))).A A) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A)
      (fun p : Σ u, {b : (QuantumComp.toIPFunctor LocalSig.instruments.{0}
          (advSpec Req Resp (X × Z))).B A c //
        (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec Req Resp (X × Z))).src A c b =
          u} ↦ (hwAt W m).amplifyLeft p.1)
      ((permutationRuntime (spongePerm (overwrite W t) π)).run .instruments
        (challenge sch keccakStateEquiv sk A c))
      ((spongeFnReadRuntime X Z t W m).run .instruments (challengeReads M π sch Sch sk A c)) := by
  subst hsch
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact intertwines_simulate π t W m _
  · exact intertwines_simulate π t W m _
  · change DSubInstrument.Intertwines _ _
      ((permutationRuntime (spongePerm (overwrite W t) π)).run .instruments
        (QuantumComp.bind (signTree Sch.overPermutation keccakStateEquiv sk r E ℓ) _))
      ((spongeFnReadRuntime X Z t W m).run .instruments
        (QuantumComp.bind (signReads M π Sch sk r E ℓ) _))
    refine intertwines_run_bind (R₁ := permutationRuntime (spongePerm (overwrite W t) π))
      (R₂ := spongeFnReadRuntime X Z t W m) (V := hwAt W m)
      (intertwines_run_of_run₂ (R₁ := permutationRuntime (spongePerm (overwrite W t) π))
        (R₂ := spongeFnReadRuntime X Z t W m) (V := hwAt W m) ?_) fun p ↦ ?_
    · rw [signTree, signReads]
      refine intertwines_run₂_act_bind (R₁ := permutationRuntime (spongePerm (overwrite W t) π))
        (R₂ := spongeFnReadRuntime X Z t W m) (V := hwAt W m) (A := A)
        (B := QReg.of ((advSpec Req Resp (X × Z)).Out (.sign r) × E)) _
        fun _ ↦ ?_
      refine intertwines_of_classicalOn_readsTo t W m π ?_
        ((readsTo_readsProgram π (Sch.sign sk r)).map Prod.fst)
      exact (classicalOn_toQuantumAt_permImpl (overwrite W t) π _ _).congr
        (simulateQ_overPermutation_sign (overwrite W t) π _ Sch (fun _ ↦ rfl) sk r) rfl
    · exact intertwines_run_pure (R₁ := permutationRuntime (spongePerm (overwrite W t) π))
        (R₂ := spongeFnReadRuntime X Z t W m) (V := hwAt W m) _

/-- **The game and its reads intertwine** on the block `(W, m)`: against
`φ = spongePerm (overwrite W t) π`, the game runs as `gameReads` after the honest evaluation of
key generation runs against `spongeFnReadRuntime X Z t W m`. -/
theorem intertwines_game (hsch : sch = Sch.overPermutation) (S0 : Seed)
    (A : Adversary PK Req Resp F (X × Z)) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft (QReg.of Unit))
      (fun _ ↦ (hwAt W m).amplifyLeft (QReg.of Unit))
      ((permutationRuntime (spongePerm (overwrite W t) π)).run₂ .instruments
        (game sch keccakStateEquiv S0 A))
      ((spongeFnReadRuntime X Z t W m).run₂ .instruments
        (gameReads M π sch Sch A (honestEval (overwrite W t) π (Sch.keygen S0)))) := by
  subst hsch
  rw [game, run₂_bind_of_classicalOn_pure ((classicalOn_toQuantumAt_permImpl (overwrite W t) π _
    _).congr (simulateQ_overPermutation_generateKeys (overwrite W t) π _ Sch (fun _ ↦ rfl) S0)
    rfl)]
  dsimp only
  refine intertwines_run₂_bind (R₁ := permutationRuntime (spongePerm (overwrite W t) π))
    (R₂ := spongeFnReadRuntime X Z t W m) (V := hwAt W m)
    (intertwines_run₂_of_run (intertwines_substitute (spec₀ := advSpec Req Resp (X × Z))
      (R₁ := permutationRuntime (spongePerm (overwrite W t) π))
      (R₂ := spongeFnReadRuntime X Z t W m) (V := hwAt W m)
      (fun A c ↦ intertwines_challenge t W m π _ Sch rfl
        (honestEval (overwrite W t) π (Sch.keygen S0)).1.2 A c) _))
    fun run ↦ ?_
  refine intertwines_run₂_bind (R₁ := permutationRuntime (spongePerm (overwrite W t) π))
    (R₂ := spongeFnReadRuntime X Z t W m) (V := hwAt W m)
    (intertwines_of_classicalOn_readsTo t W m π ?_
      ((readsTo_readsProgram π (Sch.verify _ run.1)).map Prod.fst))
    fun _ ↦ intertwines_run₂_pure _
  exact (classicalOn_toQuantumAt_permImpl (overwrite W t) π _ _).congr
    (simulateQ_overPermutation_verify (overwrite W t) π _ Sch (fun _ ↦ rfl) _ run.1) rfl

/-- **G1 → G2 at fixed `t` and `π`**: against `φ = spongePerm (overwrite W t) π`, the game has the
law of its reads `gameReads` against `spongeFnReadRuntime X Z t W m`, after the honest evaluation
of key generation. -/
theorem evalDistMap_game_eq_reads (hsch : sch = Sch.overPermutation) (S0 : Seed)
    (A : Adversary PK Req Resp F (X × Z)) (ρ : SubState (QReg.of Unit)) {γ : Type*}
    [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (permutationRuntime (spongePerm (overwrite W t) π)).evalDistMap .instruments
        (game sch keccakStateEquiv S0 A) ρ f =
      (spongeFnReadRuntime X Z t W m).evalDistMap .instruments
        (gameReads M π sch Sch A (honestEval (overwrite W t) π (Sch.keygen S0))) ρ f :=
  evalDistMap_eq_of_intertwines (R₁ := permutationRuntime (spongePerm (overwrite W t) π))
    (R₂ := spongeFnReadRuntime X Z t W m) (K := hwCol W m) (conjTranspose_hwCol_mul_self W m)
    (hwAt_basis W m) (intertwines_run_of_run₂ (intertwines_game t W m π sch Sch hsch S0 A)) ρ f

/-- **G1 → G2 at fixed `t` and `π`, after the simulation**: against the oracles of `t`, the
simulated game has the law of its reads against the classical reads of `t` without hardwired
cells. -/
theorem evalDistMap_simulate_game_eq_reads (hsch : sch = Sch.overPermutation) (m₀ : M) (S0 : Seed)
    (A : Adversary PK Req Resp F (X × Z)) (ρ : SubState (QReg.of Unit)) {γ : Type*}
    [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap .instruments
        (simulate .instruments π (game sch keccakStateEquiv S0 A)) ρ f =
      (spongeFnReadRuntime X Z t (hwEmpty X Z) m₀).evalDistMap .instruments
        (gameReads M π sch Sch A (honestEval t π (Sch.keygen S0))) ρ f := by
  have h := evalDistMap_game_eq_reads t (hwEmpty X Z) m₀ π sch Sch hsch S0 A ρ f
  rw [overwrite_hwEmpty] at h
  exact (evalDistMap_simulate .instruments π t _ ρ f).trans h

variable (M) in
/-- The law of the game's reads after key generation, against the classical reads of `k`
without hardwired cells. -/
noncomputable def gameReadsLaw (m₀ : M) (S0 : Seed) (A : Adversary PK Req Resp F (X × Z))
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) (k : SpongeKeys X Z) : Measure γ :=
  (spongeFnReadRuntime X Z k (hwEmpty X Z) m₀).evalDistMap .instruments
    (gameReads M π sch Sch A (honestEval k π (Sch.keygen S0))) ρ f

/-- **G1 → G2 at fixed `π`**: the uniform-function experiment of the simulated game is the
average over uniform `t` of the laws of its reads. -/
theorem spongeEvalDistMap_simulate_game_eq_reads (hsch : sch = Sch.overPermutation) (m₀ : M)
    (S0 : Seed) (A : Adversary PK Req Resp F (X × Z)) (ρ : SubState (QReg.of Unit)) {γ : Type*}
    [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    spongeEvalDistMap .instruments (simulate .instruments π (game sch keccakStateEquiv S0 A)) ρ
        (fun _ ↦ f) =
      ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
        (spongeFnReadRuntime X Z t (hwEmpty X Z) m₀).evalDistMap .instruments
          (gameReads M π sch Sch A (honestEval t π (Sch.keygen S0))) ρ f := by
  refine (spongeEvalDistMap_eq_sum_smul LocalSig.Interp.instruments
    (simulate .instruments π (game sch keccakStateEquiv S0 A)) ρ f
    (gameReadsLaw M π sch Sch m₀ S0 A ρ f)
    fun k ↦ evalDistMap_simulate_game_eq_reads k π sch Sch hsch m₀ S0 A ρ f).trans ?_
  exact Finset.sum_congr rfl fun _ _ ↦
    congr_arg₂ HSMul.hSMul (congrArg (fun n : ℕ ↦ (n : ℝ≥0∞)⁻¹) rfl) rfl

variable (M) in
/-- The average over uniform `t` of the laws of the game's reads, at `p`. -/
noncomputable def gameReadsAvg (m₀ : M) (S0 : Seed) (A : Adversary PK Req Resp F (X × Z))
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) (p : Equiv.Perm (X × Z)) :
    Measure γ :=
  ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
    (spongeFnReadRuntime X Z t (hwEmpty X Z) m₀).evalDistMap .instruments
      (gameReads M p sch Sch A (honestEval t p (Sch.keygen S0))) ρ f

/-- **The game in the QRPM is the average of its reads (G1 → G2)**: the quantum SUF-CMA game's
observed law is the average over `π` and uniform `t` of the law, against the classical reads of
`t` (`spongeFnReadRuntime` without hardwired cells), of `gameReads π A b` after the honest
evaluation `b = honestEval t π (keygen S0)` of key generation: the left-hand side of
`spongeEvalDistMap_eq_tableLaw` with `x` the key generation and `y = gameReads π A`. -/
theorem qrpm_game_eq_reads (hsch : sch = Sch.overPermutation) (m₀ : M) (S0 : Seed)
    (A : Adversary PK Req Resp F (X × Z)) (ρ : SubState (QReg.of Unit)) {γ : Type*}
    [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    qrpmEvalDistMap .instruments (game sch keccakStateEquiv S0 A) ρ (fun _ ↦ f) =
      (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ • ∑ π : Equiv.Perm (X × Z),
        ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
          (spongeFnReadRuntime X Z t (hwEmpty X Z) m₀).evalDistMap .instruments
            (gameReads M π sch Sch A (honestEval t π (Sch.keygen S0))) ρ f := by
  refine (qrpmEvalDistMap_eq_sum_smul LocalSig.Interp.instruments
    (game sch keccakStateEquiv S0 A) ρ f (gameReadsAvg M sch Sch m₀ S0 A ρ f)
    fun p ↦ spongeEvalDistMap_simulate_game_eq_reads p sch Sch hsch m₀ S0 A ρ f).trans ?_
  exact congr_arg₂ HSMul.hSMul (congrArg (fun n : ℕ ↦ (n : ℝ≥0∞)⁻¹) rfl)
    (Finset.sum_congr rfl fun _ _ ↦ rfl)

end Quantum.SufCma

end
