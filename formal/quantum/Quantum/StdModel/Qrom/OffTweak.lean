module

public import Quantum.StdModel.Fixed
public import Quantum.Qrom.Xmss.GameReads
public import Quantum.Qrom.CellEvent
public import Quantum.Xmss.Assembly.RecordDrop
public import Quantum.Xmss.Assembly.CostJoint
public import Quantum.Sponge.Oracle.Hardwired.Read

@[expose] public section

/-!
# Off-tweak insensitivity of the QROM property games

A QROM property game played by a straight-line reduction makes two kinds of hash calls: the
adversary's quantum calls, and classical calls (the challenger's, and the reduction's honest work,
up to about `2^64` of them). Here the classical calls become read ports of runtime 1, so that
they are charged only through the event they flip.

* **Mixed programs** (`MixSpec T`): the random oracle's port, quantum, beside tagged classical
  calls of the model's oracles. In the QROM (`romRun`) a tagged call is made classically, by a basis
  call of the port. As a read program (`toReads M upd`), a coin is a coin and a hash of `x` the read
  port of cell `x`, updating the memory by the tag's policy `upd`.
* **The bridge** (`probAt_romRun_eq`, `readLaw_eq_avg`, `probAvg_romRun_eq`): against
  `(overwrite W t).1` the QROM run of a mixed program has the law of its read program against the
  classical reads of `t` (`intertwines_romRun`), so runtime 1 started with the hardwired cells `W₀`
  runs the read program as the average over `t` of the QROM runs against `(overwrite W₀ t).1`, and
  at `W₀ = ∅` with the law of the QROM.
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal Kronecker ComplexOrder

universe u v w

namespace Quantum.StdModel.Qrom

open Quantum Quantum.Qrom Props HashSig
open Quantum.Sponge (Hw HwRead hwReadSpec hwReadCmdSpec spongeFnReadRuntime overwrite ReadsTo
  ReadsTo.map readCall readsTo_readCall keepMem hwAt hwCol hwAt_basis conjTranspose_hwCol_mul_self
  intertwines_run_pure intertwines_run₂_act_bind intertwines_run_of_run₂ intertwines_run₂_of_run
  intertwines_run_bind intertwines_substitute evalDistMap_eq_of_intertwines
  spongeHardwiredReadRuntime read_port_eq_classical_read)
open Quantum.Sponge (hwEmpty overwrite_hwEmpty)

/-! ## Mixed programs -/

/-- **Tagged classical calls**: the query `t` of the model's oracles with a tag, answered as `t`. -/
@[reducible]
def tagSpec (T : Type) : OracleSpec.{0, 0} (T × RomOracles.Domain) :=
  fun p ↦ RomOracles.Range p.2

/-- **The signature of a mixed program**: the random oracle's port, quantum, and the tagged
classical calls. -/
noncomputable abbrev MixSpec (T : Type) : QuantumOracleSpec.{0, 0} :=
  advSpec romWorld.spec (tagSpec T)

/-- The answer to a tagged call: the query of the model's oracles. -/
noncomputable def romAns (T : Type) (p : T × RomOracles.Domain) :
    OracleComp romWorld.Oracles ((tagSpec T).Range p) :=
  (liftM (romWorld.Oracles.query p.2) : OracleComp romWorld.Oracles (romWorld.Oracles.Range p.2))

variable {T : Type}

/-- **A mixed program in the QROM**: each tagged call made classically, by a basis call of the
port (`answered` with the queries themselves). -/
noncomputable def romRun {A B : QReg} {α : Type} (x : QComp (MixSpec T) A B α) :
    QComp romWorld.spec A B α :=
  answered romWorld (romAns T) x

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **The model's oracles by read ports** beside `B`: a coin is a coin, a hash of `x` the read port
of cell `x` updating the memory with `u x`. -/
noncomputable def readImpl (u : HashDomain → M → Option HashOutput → M) (B : QReg) :
    QueryImpl RomOracles (QComp (hwReadSpec HashOutput HashDomain M) B B)
  | .inl n => QComp.coinImpl _ B n
  | .inr x => (readCall (.readH x (u x)) B).map fun r ↦ r.1.getD 0

variable {M}

/-- A tagged call by reads: relabel the register, then the read program of the query, the
memory updated by the tag's policy. -/
noncomputable def readTree (upd : T → HashDomain → M → Option HashOutput → M)
    (p : T × RomOracles.Domain) (E : QReg) {A : QReg} (ℓ : A ≃ (MixSpec T).In (.call p) × E) :
    QComp (hwReadSpec HashOutput HashDomain M) A (QReg.of ((MixSpec T).Out (.call p) × E))
      ((tagSpec T).Range p) :=
  (QComp.act (B := QReg.of ((MixSpec T).Out (.call p) × E)) (SubInstrument.relabel ℓ)).bind
    fun _ ↦ (romAns T p).toQuantumAt (readImpl M (upd p.1) _)

/-- **The read substitution**: a local operation and a hash call lifted to port `h` and the read
signature, a tagged call by reads (`readTree`). -/
noncomputable def readSub (upd : T → HashDomain → M → Option HashOutput → M) :
    CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec T))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec HashOutput HashDomain M))
  | A, .prim o => (liftH (answerSub romWorld (romAns T) A (.prim o))).liftOrdinary
  | A, .query (.hash p) E ℓ =>
      (liftH (answerSub romWorld (romAns T) A (.query (.hash p) E ℓ))).liftOrdinary
  | _, .query (.call p) E ℓ =>
      QuantumComp.bind (readTree upd p E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **A mixed program as a read program**, the memory updated by the policy `upd`. -/
noncomputable def toReads (upd : T → HashDomain → M → Option HashOutput → M) {A B : QReg}
    {α : Type} (x : QComp (MixSpec T) A B α) : QComp (hwReadSpec HashOutput HashDomain M) A B α :=
  IFreeM.substitute (readSub upd) x

/-- The policy that keeps the memory. -/
def keepAll (T M : Type) : T → HashDomain → M → Option HashOutput → M :=
  fun _ _ ↦ keepMem

/-! ## Read programs on a block -/

section block

variable {t : (HashDomain → HashOutput) × (HashOutput → HashDomain) × (HashOutput → HashDomain)}
  {W : Hw HashOutput HashDomain} {m : M} {B : QReg}

variable (t W m) in
/-- **A read program that runs as the sampler `pa` on the block `(W, m)`**: against the classical
reads of `t`, from the block `(W, m)`, its branch at `a` is the probability that `pa` returns `a`
times the embedding of the block. -/
def ClsTo {α : Type} (x : QComp (hwReadSpec HashOutput HashDomain M) B B α) (pa : ProbComp α) :
    Prop :=
  ∀ a ρ, ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments x).branch a
      ((hwAt W m).amplifyLeft B ρ) =
    ((Pr{let z ← pa}[z = a]).toReal : ℂ) • (hwAt W m).amplifyLeft B ρ

/-- A program that runs classically through the identity runs so on every block. -/
theorem clsTo_of_classicalOn {α : Type} {x : QComp (hwReadSpec HashOutput HashDomain M) B B α}
    {pa : ProbComp α}
    (h : ClassicalOn (spongeFnReadRuntime HashOutput HashDomain t W m) x pa LinearMap.id) :
    ClsTo t W m x pa := fun a ρ ↦ by
  rw [h a]
  rfl

/-- A program that returns `a₀` with certainty on the block runs as the sampler of `a₀`. -/
theorem clsTo_of_readsTo {α : Type} {x : QComp (hwReadSpec HashOutput HashDomain M) B B α}
    {a₀ : α} (h : ReadsTo t W m x a₀) : ClsTo t W m x (pure a₀) := fun a ρ ↦ by
  classical
  rw [prEvent_pure]
  by_cases ha : a = a₀
  · subst ha
    refine (LinearMap.congr_fun h.1 ρ).trans ?_
    simp
    rfl
  · refine (LinearMap.congr_fun (h.2 a ha) ρ).trans ?_
    simp [Ne.symm ha]
    rfl

/-- Sequencing programs that run as samplers on the block runs as the sequenced sampler. -/
theorem ClsTo.bind {α β : Type} {x : QComp (hwReadSpec HashOutput HashDomain M) B B α}
    {pa : ProbComp α} {k : α → QComp (hwReadSpec HashOutput HashDomain M) B B β}
    {pk : α → ProbComp β} (hx : ClsTo t W m x pa) (hk : ∀ a, ClsTo t W m (k a) (pk a)) :
    ClsTo t W m (x.bind k) (pa >>= pk) := by
  intro c ρ
  have hne (a : α) : Pr{let z ← pa}[z = a] * Pr{let z ← pk a}[z = c] ≠ ∞ :=
    ENNReal.mul_ne_top (prEvent_ne_top _) (prEvent_ne_top _)
  have hsum : ∑' a, Pr{let z ← pa}[z = a] * Pr{let z ← pk a}[z = c] ≠ ∞ := by
    rw [← prEvent_bind_eq_tsum]
    exact prEvent_ne_top _
  rw [QuantumRuntime.run₂_bind]
  erw [DSubInstrument.branch_bind_apply]
  rw [prEvent_bind_eq_tsum, ENNReal.tsum_toReal_eq hne, Complex.ofReal_tsum,
    ← (Complex.summable_ofReal.mpr (ENNReal.summable_toReal hsum)).tsum_smul_const]
  refine tsum_congr fun a ↦ ?_
  erw [hx a ρ, map_smul, hk a c ρ]
  refine (smul_smul _ _ _).trans ?_
  rw [ENNReal.toReal_mul, Complex.ofReal_mul]
  rfl

/-- **A classical algorithm by read programs** runs as the simulated algorithm. -/
theorem clsTo_toQuantumAt {ι : Type} {ospec : OracleSpec.{0, 0} ι}
    {q : QueryImpl ospec (QComp (hwReadSpec HashOutput HashDomain M) B B)}
    {impl : QueryImpl ospec ProbComp} (hq : ∀ i, ClsTo t W m (q i) (impl i)) {α : Type}
    (oa : OracleComp ospec α) : ClsTo t W m (oa.toQuantumAt q) (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    rw [toQuantumAt_pure, simulateQ_pure]
    exact clsTo_of_classicalOn (classicalOn_pure x)
  | query_bind i k ih =>
    rw [toQuantumAt_query_bind, simulateQ_bind, simulateQ_spec_query]
    exact (hq i).bind ih

/-- A coin runs as a uniform coin in every runtime. -/
theorem classicalOn_coinImpl {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) (n : ℕ) :
    ClassicalOn R (QComp.coinImpl spec B n) (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
      LinearMap.id := by
  classical
  intro y
  have hp : Pr{let z ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))}[z = y] =
      (Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹ := by
    simpa [Finset.filter_eq'] using
      (prEvent_liftM_query_eq_card_div (spec := unifSpec) n (fun x ↦ x = y))
  rw [hp, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.ofReal_inv, Complex.ofReal_natCast,
    QComp.coinImpl, QuantumRuntime.run₂_act, SubInstrument.bind_pure,
    DSubInstrument.branch_frame_apply]
  refine LinearMap.ext fun ρ ↦ ?_
  ext x x'
  simp [SubInstrument.branch_uniform_apply]

/-- **The read implementation keeping the memory runs as the model's oracles answered by
`(overwrite W t).1`** on every block. -/
theorem clsTo_readImpl (i : RomOracles.Domain) :
    ClsTo t W m (readImpl M (fun _ ↦ keepMem) B i) (eagerFunOracles (overwrite W t).1 i) := by
  rcases i with n | x
  · exact clsTo_of_classicalOn (classicalOn_coinImpl _ n)
  · exact clsTo_of_readsTo ((readsTo_readCall (t := t) (W := W) (m := m) (.readH x keepMem) rfl
      B).map _)

/-- A program on a fixed register run classically against `(overwrite W t).1` intertwines with a
read program that runs as the same sampler on the block. -/
theorem intertwines_of_classicalOn_clsTo {α : Type}
    {x₁ : QComp romSpec B B α} {x₂ : QComp (hwReadSpec HashOutput HashDomain M) B B α}
    {pa : ProbComp α}
    (h₁ : ClassicalOn (additiveOracleRuntime (overwrite W t).1) x₁ pa LinearMap.id)
    (h₂ : ClsTo t W m x₂ pa) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft B)
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments x₁)
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments x₂) :=
  fun a ↦ LinearMap.ext fun ρ ↦ by
    change ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments x₂).branch a
        ((hwAt W m).amplifyLeft B ρ) = (hwAt W m).amplifyLeft B
          (((additiveOracleRuntime (overwrite W t).1).run₂ .instruments x₁).branch a ρ)
    rw [h₂ a ρ, h₁ a]
    exact (((hwAt W m).amplifyLeft B).map_smul _ ρ).symm

end block

/-! ## The bridge -/

section bridge

variable {t : (HashDomain → HashOutput) × (HashOutput → HashDomain) × (HashOutput → HashDomain)}
  {W : Hw HashOutput HashDomain} {m : M}

variable (t W m) in
/-- **A mixed program in the QROM and its read program intertwine on every command**, on the
block `(W, m)`, the reads keeping the memory. -/
theorem intertwines_readSub (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec T)).A A) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A)
      (fun p : Σ u, {b : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec T)).B A c //
        (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec T)).src A c b = u} ↦
          (hwAt W m).amplifyLeft p.1)
      ((additiveOracleRuntime (overwrite W t).1).run .instruments
        (answerSub romWorld (romAns T) A c))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run .instruments
        (readSub (keepAll T M) A c)) := by
  rcases c with o | ⟨p | p, E, ℓ⟩
  · exact Quantum.Qrom.Xmss.intertwines_liftH t W m _
  · exact Quantum.Qrom.Xmss.intertwines_liftH t W m _
  · change DSubInstrument.Intertwines _ _
      ((additiveOracleRuntime (overwrite W t).1).run .instruments
        (QuantumComp.bind (callTree romWorld (romAns T) p E ℓ) _))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run .instruments
        (QuantumComp.bind (readTree (keepAll T M) p E ℓ) _))
    refine intertwines_run_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
      (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
      (intertwines_run_of_run₂ (R₁ := additiveOracleRuntime (overwrite W t).1)
        (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m) ?_) fun q ↦ ?_
    · rw [callTree, readTree]
      exact intertwines_run₂_act_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
        (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m) (A := A)
        (B := QReg.of ((MixSpec T).Out (.call p) × E)) _ fun _ ↦
          intertwines_of_classicalOn_clsTo
            (Quantum.Qrom.Xmss.classicalOn_toQuantumAt_romImpl _ _ _)
            (clsTo_toQuantumAt (fun i ↦ clsTo_readImpl i) _)
    · exact intertwines_run_pure (R₁ := additiveOracleRuntime (overwrite W t).1)
        (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m) _

variable (t W m) in
/-- **A mixed program in the QROM against `(overwrite W t).1` intertwines with its read
program** against the classical reads of `t`, on the block `(W, m)`. -/
theorem intertwines_romRun {A B : QReg} {α : Type} (x : QComp (MixSpec T) A B α) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A) (fun _ ↦ (hwAt W m).amplifyLeft B)
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments (romRun x))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments
        (toReads (keepAll T M) x)) :=
  intertwines_run₂_of_run (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
    (intertwines_substitute (R₁ := additiveOracleRuntime (overwrite W t).1)
      (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
      (fun A c ↦ intertwines_readSub t W m A c) x)

variable (t W) in
/-- **The QROM run of a mixed program against `(overwrite W t).1` wins with the probability of
its read program** against the classical reads of `t` with the hardwired cells `W`. -/
theorem probAt_romRun_eq (x : QComp (MixSpec T) (QReg.of Unit) (QReg.of Unit) Bool) :
    romWorld.probAt (overwrite W t).1 (romRun x) =
      (spongeFnReadRuntime HashOutput HashDomain t W ()).evalDistMap .instruments
        (toReads (keepAll T Unit) x) (SubState.basis ()) (fun p ↦ p.2.2) {true} := by
  have h := evalDistMap_eq_of_intertwines (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W ()) (K := hwCol W ())
    (conjTranspose_hwCol_mul_self W ()) (hwAt_basis W ())
    (intertwines_run_of_run₂ (intertwines_romRun t W () x)) (SubState.basis ())
    (fun p ↦ p.2.2)
  exact congrArg (fun μ : Measure Bool ↦ μ {true}) h

variable (W) in
/-- **Runtime 1 runs the read program as the average of the QROM runs**: started with the
hardwired cells `W`, it wins with the average over `t` of the QROM winning probabilities against
`(overwrite W t).1`. -/
theorem readLaw_eq_avg (x : QComp (MixSpec T) (QReg.of Unit) (QReg.of Unit) Bool) :
    (spongeHardwiredReadRuntime HashOutput HashDomain W ()).evalDistMap .instruments
        (toReads (keepAll T Unit) x) (SubState.basis ()) (fun p ↦ p.2.2) {true} =
      ∑ t : (HashDomain → HashOutput) × (HashOutput → HashDomain) × (HashOutput → HashDomain),
        (Fintype.card ((HashDomain → HashOutput) × (HashOutput → HashDomain) ×
          (HashOutput → HashDomain)) : ℝ≥0∞)⁻¹ * romWorld.probAt (overwrite W t).1 (romRun x) := by
  have h := read_port_eq_classical_read (X := HashOutput) (Z := HashDomain) W ()
    LocalSig.Interp.instruments (toReads (keepAll T Unit) x) (SubState.basis ()) (fun p ↦ p.2.2)
  refine (congrArg (fun μ : Measure Bool ↦ μ {true}) h).trans ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Measure.smul_apply, smul_eq_mul, probAt_romRun_eq]

/-- Averaging over a product a function of the first factor averages over the first factor. -/
theorem sum_inv_card_mul_fst {A B : Type*} [Fintype A] [Fintype B] [Nonempty B] (G : A → ℝ≥0∞) :
    ∑ t : A × B, (Fintype.card (A × B) : ℝ≥0∞)⁻¹ * G t.1 =
      ∑ a, (Fintype.card A : ℝ≥0∞)⁻¹ * G a := by
  have h := sum_inv_card_smul_fst (A := A) (B := B) (β := ℝ≥0∞) G
  simp only [smul_eq_mul] at h
  rw [h, Finset.mul_sum]

/-- **The QROM winning probability of a mixed program is the winning probability of its read
program in runtime 1** started with no hardwired cell. -/
theorem probAvg_romRun_eq (x : QComp (MixSpec T) (QReg.of Unit) (QReg.of Unit) Bool) :
    romWorld.probAvg (romRun x) =
      (spongeHardwiredReadRuntime HashOutput HashDomain (hwEmpty HashOutput HashDomain)
        ()).evalDistMap .instruments (toReads (keepAll T Unit) x) (SubState.basis ())
          (fun p ↦ p.2.2) {true} := by
  rw [readLaw_eq_avg, OracleWorld.probAvg_eq_sum]
  simp only [overwrite_hwEmpty]
  exact (sum_inv_card_mul_fst (fun H ↦ romWorld.probAt H (romRun x))).symm

end bridge

/-! ## The game of a straight-line reduction as a mixed program -/

/-- The callers of the classical calls of a property game: the challenger's setup, answers and
decision, and the reduction's honest work. -/
inductive Caller where
  /-- The challenger's setup. -/
  | setup
  /-- The challenger's answers to the reduction's classical queries. -/
  | answer
  /-- The challenger's decision. -/
  | judge
  /-- The reduction's honest work (setup, handlers, output). -/
  | red
  deriving DecidableEq

section game

variable {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type} {R' : OracleSpec.{0, 0} Q'} {St : Type}

/-- A classical call of the model's oracles by the caller `c`, beside `B`. -/
noncomputable def mixImpl (c : Caller) (B : QReg) :
    QueryImpl romWorld.Oracles (QComp (MixSpec Caller) B B) :=
  fun i ↦ callQ romWorld (tagSpec Caller) (c, i) B

/-- **The reduction's oracles as mixed calls** against the challenger `ans`, with the reduction's
transcript: the model's oracles by the reduction's calls, the reduction's ports by the
challenger's answers, logged. -/
noncomputable def redImpl (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (B : QReg) :
    QueryImpl (romWorld.Oracles + R') (StateT (QueryLog R') (QComp (MixSpec Caller) B B))
  | .inl i => fun log ↦ (mixImpl .red B i).map fun a ↦ (a, log)
  | .inr q' => fun log ↦
      ((ans q').toQuantumAt (mixImpl .answer B)).map fun a ↦ (a, log ++ [⟨q', a⟩])

variable (R St) in
/-- Call trees of mixed programs: the answer to the classical call `q` from the state `s` with
the register `A ≃ Unit × E` held, and the next state. -/
abbrev MixTrees :=
  (s : St) → (q : Q) → (E : QReg) → {A : QReg} →
    (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) →
      QComp (MixSpec Caller) A (QReg.of ((advSpec romWorld.spec R).Out (.call q) × E))
        (R.Range q × St)

/-- **The mixed run with call trees `Tr`**: local operations and hash calls kept, each classical
call answered by `Tr`, as `tRun`. -/
noncomputable def mixRun {X Y : QReg → Type} (Tr : MixTrees R St) (leaf : ∀ u, X u → St → Y u) :
    {A : QReg} →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A →
      St → IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Y A
  | _, .pure x, s => .pure (leaf _ x s)
  | _, .liftBind (.prim o) next, s => .liftBind (.prim o) fun b ↦ mixRun Tr leaf (next b) s
  | _, .liftBind (.query (.hash p) E ℓ) next, s =>
      .liftBind (.query (.hash p) E ℓ) fun b ↦ mixRun Tr leaf (next b) s
  | _, .liftBind (.query (.call q) E ℓ) next, s =>
      QuantumComp.bind (Tr s q E ℓ) fun _ l ↦ l.1 ▸ mixRun Tr leaf (next ⟨l.2.1⟩) l.2.2

/-- The reduction's call trees against the challenger `ans`, with the transcript in the state. -/
noncomputable def mixTrees (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (σ : HHandler romWorld R R' St) : MixTrees R (St × QueryLog R') := fun p q E _ ℓ ↦
  (QComp.act (B := QReg.of ((advSpec romWorld.spec R).Out (.call q) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦
      ((simulateQ (redImpl ans _) (σ p.1 q)).run p.2).map fun r ↦ (r.1.1, (r.1.2, r.2))

/-- The mixed run of the reduction against the challenger `ans`, returning the value, the handler
state and the reduction's transcript. -/
noncomputable def mixRunL (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (σ : HHandler romWorld R R' St) {A B : QReg} {α : Type}
    (x : QComp (advSpec romWorld.spec R) A B α) (s : St) (log : QueryLog R') :
    QComp (MixSpec Caller) A B ((α × St) × QueryLog R') :=
  mixRun (Y := QuantumComp₂.Leaf B ((α × St) × QueryLog R')) (mixTrees ans σ)
    (fun _ l q ↦ ⟨l.1, ((l.2, q.1), q.2)⟩) x (s, log)

/-- **A straight-line reduction against the challenger `ans`, as a mixed program**: its setup,
the adversary run against its handler, its output, each classical call tagged. -/
noncomputable def mixNormal (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    {S0 F Out : Type} (pre : OracleComp (romWorld.Oracles + R') S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R R' St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + R') Out) :
    QComp (MixSpec Caller) (QReg.of Unit) (QReg.of Unit) (Out × QueryLog R') :=
  QuantumComp₂.bind ((simulateQ (redImpl ans _) pre).run []) fun p ↦
    QuantumComp₂.bind (mixRunL ans σ (adv p.1) (st0 p.1) p.2) fun r ↦
      (simulateQ (redImpl ans _) (post p.1 r.1.1 r.1.2)).run r.2

/-- **The property game of a straight-line reduction as a mixed program**: the challenger's
setup, the reduction (`mixNormal`), the challenger's decision, each classical call tagged with
its caller. -/
noncomputable def mixGame {Pub Out : Type} (E : Experiment romWorld R' Pub Out) {S0 F : Type}
    (pre : Pub → OracleComp (romWorld.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler romWorld R R' St)
    (post : Pub → S0 → F → St → OracleComp (romWorld.Oracles + R') Out) :
    QComp (MixSpec Caller) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (E.setup.toQuantumAt (mixImpl .setup _)) fun s ↦
    QuantumComp₂.bind (mixNormal (E.answer s) (pre (E.pub s)) (adv (E.pub s)) (st0 (E.pub s))
      (σ (E.pub s)) (post (E.pub s))) fun r ↦
        (E.judge s r.2 r.1).toQuantumAt (mixImpl .judge _)

/-! ### The mixed game in the QROM at a fixed function -/

variable {H : romWorld.Tab}

/-- The QROM run of a sequence. -/
theorem romRun_bind {T : Type} {A B C : QReg} {α β : Type} (x : QComp (MixSpec T) A B α)
    (k : α → QComp (MixSpec T) B C β) :
    romRun (x.bind k) = (romRun x).bind fun a ↦ romRun (k a) :=
  answered_bind romWorld (romAns T) x k

/-- The QROM run of a tagged call: the call tree of the query, then the relabelling back. -/
theorem romRun_callQ_bind {T : Type} (p : T × RomOracles.Domain) {B C : QReg} {β : Type}
    (k : (tagSpec T).Range p → QComp (MixSpec T) B C β) :
    romRun ((callQ romWorld (tagSpec T) p B).bind k) =
      (callTree romWorld (romAns T) p B (callSplit romWorld (tagSpec T) p B)).bind fun a ↦
        (QComp.act (A := QReg.of ((MixSpec T).Out (.call p) × B)) (B := B)
          (SubInstrument.relabel (callSplit romWorld (tagSpec T) p B).symm)).bind fun _ ↦
            romRun (k a) := by
  refine (IFreeM.bind_assoc _ _ _).trans (congrArg (IFreeM.bind _) ?_)
  funext u l
  obtain ⟨rfl, a⟩ := l
  rfl

/-- **A tagged call runs classically** at `H`, as the query answered by `H`. -/
theorem classicalOn_romRun_mixImpl (c : Caller) (B : QReg) (i : RomOracles.Domain) :
    ClassicalOn (romWorld.runtime H) (romRun (mixImpl c B i)) (romWorld.eager H i)
      LinearMap.id := by
  have e : romRun (mixImpl c B i) = romRun ((callQ romWorld (tagSpec Caller) (c, i) B).bind
      fun a ↦ QuantumComp₂.pure a) := by
    rw [QuantumComp₂.bind_pure]
    rfl
  rw [e, romRun_callQ_bind]
  have h := ((classicalOn_act (R := romWorld.runtime H) (spec := romWorld.spec)
    (B := QReg.of ((MixSpec Caller).Out (.call (c, i)) × B))
    (SubInstrument.relabel (callSplit romWorld (tagSpec Caller) (c, i) B))).bind fun _ ↦
      romWorld.classicalOn_toQuantumAt H _ (romAns Caller (c, i))).bind fun a ↦
        (classicalOn_act (R := romWorld.runtime H) (spec := romWorld.spec)
          (A := QReg.of ((MixSpec Caller).Out (.call (c, i)) × B)) (B := B)
          (SubInstrument.relabel (callSplit romWorld (tagSpec Caller) (c, i) B).symm)).bind
            fun _ ↦ classicalOn_pure (R := romWorld.runtime H) (spec := romWorld.spec) a
  refine h.congr ?_ ?_
  · simp only [romAns, pure_bind, bind_pure]
    exact simulateQ_spec_query (r := ProbComp) (impl := romWorld.eager H) i
  · rw [LinearMap.id_comp, LinearMap.id_comp]
    exact relabel_symm_comp _ _

/-- **A classical algorithm by tagged calls runs classically** at `H`. -/
theorem classicalOn_romRun_toQuantumAt (c : Caller) (B : QReg) {α : Type}
    (oa : OracleComp romWorld.Oracles α) :
    ClassicalOn (romWorld.runtime H) (romRun (oa.toQuantumAt (mixImpl c B)))
      (simulateQ (romWorld.eager H) oa) LinearMap.id := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [toQuantumAt_pure, simulateQ_pure]
    exact classicalOn_pure a
  | query_bind i k ih =>
    rw [toQuantumAt_query_bind, romRun_bind, simulateQ_bind, simulateQ_spec_query]
    exact (classicalOn_romRun_mixImpl c B i).bind_id ih

/-- **The reduction's classical algorithm by tagged calls runs classically** at `H`, as the
algorithm answered by `logImpl`, with its transcript. -/
theorem classicalOn_romRun_redImpl (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (B : QReg) {α : Type} (oa : OracleComp (romWorld.Oracles + R') α) (log : QueryLog R') :
    ClassicalOn (romWorld.runtime H) (romRun ((simulateQ (redImpl ans B) oa).run log))
      ((simulateQ (logImpl H ans) oa).run log) LinearMap.id := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact classicalOn_pure (a, log)
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change ClassicalOn _ (romRun (((mixImpl .red B i).map fun a ↦ (a, log)) >>= fun p ↦
          (simulateQ (redImpl ans B) (k p.1)).run p.2)) _ _
      rw [QuantumComp₂.bind_eq, QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc,
        romRun_bind]
      simp only [QuantumComp₂.pure_bind]
      refine ((classicalOn_romRun_mixImpl .red B i).bind_id fun a ↦ ih a log).congr ?_ rfl
      simp [logImpl, StateT.run_lift]
    · change ClassicalOn _ (romRun ((((ans q').toQuantumAt (mixImpl .answer B)).map
          fun a ↦ (a, log ++ [⟨q', a⟩])) >>= fun p ↦
            (simulateQ (redImpl ans B) (k p.1)).run p.2)) _ _
      rw [QuantumComp₂.bind_eq, QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc,
        romRun_bind]
      simp only [QuantumComp₂.pure_bind]
      refine ((classicalOn_romRun_toQuantumAt .answer B (ans q')).bind_id fun a ↦
        ih a (log ++ [⟨q', a⟩])).congr ?_ rfl
      change _ = ((fun a ↦ (a, log ++ [⟨q', a⟩])) <$> simulateQ (romWorld.eager H) (ans q')) >>=
        fun p ↦ (simulateQ (logImpl H ans) (k p.1)).run p.2
      rw [bind_map_left]

/-- The QROM run of a mixed run is the run with the QROM call trees. -/
theorem romRun_mixRun {X Y : QReg → Type} (Tr : MixTrees R St) (leaf : ∀ u, X u → St → Y u)
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A)
    (s : St) :
    IFreeM.substitute (answerSub romWorld (romAns Caller)) (mixRun Tr leaf x s) =
      tRun romWorld (fun s q E _ ℓ ↦ romRun (Tr s q E ℓ)) leaf x s := by
  induction x using IFreeM.inductionOn generalizing s with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨p | q, E, ℓ⟩
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b s)
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b s)
    · refine (IFreeM.substitute_bind _ _ _).trans (congrArg (IFreeM.bind _) ?_)
      funext u l
      obtain ⟨rfl, ⟨a, s'⟩⟩ := l
      exact ih ⟨a⟩ s'

/-- The QROM run of a local operation followed by a continuation. -/
theorem romRun_act_bind {T : Type} {A B C : QReg} {α β : Type} (p : SubInstrument A B α)
    (k : α → QComp (MixSpec T) B C β) :
    romRun ((QComp.act p).bind k) = (QComp.act p).bind fun a ↦ romRun (k a) :=
  rfl

/-- The QROM run of a relabelled value. -/
theorem romRun_map {T : Type} {A B : QReg} {α β : Type} (x : QComp (MixSpec T) A B α)
    (f : α → β) : romRun (x.map f) = (romRun x).map f := by
  rw [QuantumComp₂.map_eq_bind_pure, romRun_bind, QuantumComp₂.map_eq_bind_pure]
  rfl

/-- **The reduction's call tree runs classically** at `H`, as its kernel. -/
theorem classicalOn_romRun_mixTrees (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (σ : HHandler romWorld R R' St) (p : St × QueryLog R') (q : Q) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) :
    ClassicalOn (romWorld.runtime H) (romRun (mixTrees ans σ p q E ℓ)) (hKernel H ans σ p q)
      (relabelMap (romWorld.runtime H)
        (B' := QReg.of ((advSpec romWorld.spec R).Out (.call q) × E)) ℓ) := by
  rw [mixTrees, romRun_act_bind]
  simp only [romRun_map]
  have h := (classicalOn_act (R := romWorld.runtime H) (spec := romWorld.spec)
    (B := QReg.of ((advSpec romWorld.spec R).Out (.call q) × E)) (SubInstrument.relabel ℓ)).bind
      fun _ ↦ (ClassicalOn.map (classicalOn_romRun_redImpl (H := H) ans _ (σ p.1 q) p.2)
        fun r ↦ (r.1.1, (r.1.2, r.2)))
  refine h.congr ?_ ?_
  · simp only [pure_bind, hKernel]
  · exact LinearMap.id_comp _

/-- **The reduction's mixed run in the QROM at `H` is the canonical run against its kernel.** -/
theorem run₂_romRun_mixRunL (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (σ : HHandler romWorld R R' St) {A B : QReg} {α : Type}
    (x : QComp (advSpec romWorld.spec R) A B α) (s : St) (log : QueryLog R') :
    (romWorld.runtime H).run₂ .instruments (romRun (mixRunL ans σ x s log)) =
      (romWorld.runtime H).run₂ .instruments (kRunL romWorld (hKernel H ans σ) x s log) := by
  have h : (romWorld.runtime H).run .instruments (romRun (mixRunL ans σ x s log)) =
      (romWorld.runtime H).run .instruments (kRunL romWorld (hKernel H ans σ) x s log) :=
    (congrArg ((romWorld.runtime H).run .instruments) (romRun_mixRun _ _ x (s, log))).trans
      (run_tRun_congr H (fun p q E A ℓ ↦ run₂_eq_of_classicalOn
        (classicalOn_romRun_mixTrees ans σ p q E ℓ) (classicalOn_kTree romWorld _ _ p q E ℓ))
        _ x (s, log))
  exact congrArg (fun d ↦ d.comap (QuantumComp₂.leafEquiv B ((α × St) × QueryLog R'))
    (QuantumComp₂.leafEquiv B _).injective) h

/-- **The mixed reduction in the QROM at `H` runs as its normal form** (`slNormal`). -/
theorem run₂_romRun_mixNormal (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    {S0 F Out : Type} (pre : OracleComp (romWorld.Oracles + R') S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R R' St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + R') Out) :
    (romWorld.runtime H).run₂ .instruments (slNormal H ans pre adv st0 σ post) =
      (romWorld.runtime H).run₂ .instruments (romRun (mixNormal ans pre adv st0 σ post)) := by
  rw [mixNormal, slNormal, romRun_bind]
  refine run₂_bind_congr (run₂_eq_of_classicalOn (classicalOn_coinImpl_toQuantumAt _ _)
    (classicalOn_romRun_redImpl ans _ pre [])) fun p ↦ ?_
  rw [romRun_bind]
  exact run₂_bind_congr (run₂_romRun_mixRunL ans σ (adv p.1) (st0 p.1) p.2).symm fun r ↦
    run₂_eq_of_classicalOn (classicalOn_coinImpl_toQuantumAt _ _)
      (classicalOn_romRun_redImpl ans _ _ _)

/-- **The property game of a straight-line reduction at `H` is the QROM run of its mixed
game**: they win with the same probability. -/
theorem probAt_game_slRed_eq {Pub Out : Type} (E : Experiment romWorld R' Pub Out) {S0 F : Type}
    (pre : Pub → OracleComp (romWorld.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler romWorld R R' St)
    (post : Pub → S0 → F → St → OracleComp (romWorld.Oracles + R') Out) (H : romWorld.Tab) :
    romWorld.probAt H (E.game fun p ↦ slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) =
      romWorld.probAt H (romRun (mixGame E pre adv st0 σ post)) := by
  refine probAt_congr (run_eq_of_run₂_eq ((run₂_game_slRed H E pre adv st0 σ post).trans ?_))
  rw [mixGame, romRun_bind]
  refine run₂_bind_congr (run₂_eq_of_classicalOn (classicalOn_coinImpl_toQuantumAt _ _)
    (classicalOn_romRun_toQuantumAt .setup _ E.setup)) fun s ↦ ?_
  rw [romRun_bind]
  exact run₂_bind_congr (run₂_romRun_mixNormal _ _ _ _ _ _) fun r ↦
    run₂_eq_of_classicalOn (classicalOn_coinImpl_toQuantumAt _ _)
      (classicalOn_romRun_toQuantumAt .judge _ _)

/-- **The QROM winning probability of the property game of a straight-line reduction is the
winning probability of its mixed game's read program in runtime 1**, started with no hardwired
cell, every read keeping the memory. -/
theorem probAvg_game_slRed_eq {Pub Out : Type} (E : Experiment romWorld R' Pub Out) {S0 F : Type}
    (pre : Pub → OracleComp (romWorld.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler romWorld R R' St)
    (post : Pub → S0 → F → St → OracleComp (romWorld.Oracles + R') Out) :
    romWorld.probAvg (E.game fun p ↦ slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) =
      (spongeHardwiredReadRuntime HashOutput HashDomain (hwEmpty HashOutput HashDomain)
        ()).evalDistMap .instruments (toReads (keepAll Caller Unit) (mixGame E pre adv st0 σ post))
          (SubState.basis ()) (fun p ↦ p.2.2) {true} := by
  rw [← probAvg_romRun_eq, OracleWorld.probAvg_eq_sum, OracleWorld.probAvg_eq_sum]
  exact Finset.sum_congr rfl fun H _ ↦ by rw [probAt_game_slRed_eq]

/-! ### Charges of the mixed game -/

/-- A tagged call makes no hash call. -/
theorem isChargeBound_mixImpl (c : Caller) (B : QReg) (i : RomOracles.Domain) :
    IFreeM.IsChargeBound (mixImpl c B i) (cmdCharge hashCharge) 0 := by
  unfold mixImpl callQ
  exact (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (isChargeBound_query₂ (S := romWorld.spec) hashCharge (.call (c, i)) B
      (callSplit romWorld (tagSpec Caller) (c, i) B)) fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (isChargeBound_act _ _ 0) fun _ ↦
      IFreeM.isChargeBound_pure _ 0).mono le_rfl

/-- A classical algorithm by tagged calls makes no hash call. -/
theorem isChargeBound_toQuantumAt_mixImpl (c : Caller) (B : QReg) {α : Type}
    (oa : OracleComp romWorld.Oracles α) :
    IFreeM.IsChargeBound (oa.toQuantumAt (mixImpl c B)) (cmdCharge hashCharge) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind i k ih =>
    rw [toQuantumAt_query_bind]
    exact (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (isChargeBound_mixImpl c B i)
      ih).mono le_rfl

/-- The reduction's classical algorithm by tagged calls makes no hash call. -/
theorem isChargeBound_redImpl (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (B : QReg) {α : Type} (oa : OracleComp (romWorld.Oracles + R') α) (log : QueryLog R') :
    IFreeM.IsChargeBound ((simulateQ (redImpl ans B) oa).run log) (cmdCharge hashCharge) 0 := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a => trivial
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change IFreeM.IsChargeBound (QuantumComp₂.bind ((mixImpl .red B i).map fun a ↦ (a, log))
          fun p ↦ (simulateQ (redImpl ans B) (k p.1)).run p.2) _ _
      rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc]
      exact (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (isChargeBound_mixImpl .red B i)
        fun a ↦ ih a log).mono le_rfl
    · change IFreeM.IsChargeBound (QuantumComp₂.bind (((ans q').toQuantumAt
          (mixImpl .answer B)).map fun a ↦ (a, log ++ [⟨q', a⟩])) fun p ↦
            (simulateQ (redImpl ans B) (k p.1)).run p.2) _ _
      rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc]
      exact (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
        (isChargeBound_toQuantumAt_mixImpl .answer B (ans q')) fun a ↦ ih a _).mono le_rfl

/-- **The mixed run keeps the adversary's hash calls** when its call trees make none. -/
theorem isChargeBound_mixRun {X Y : QReg → Type} (Tr : MixTrees R St)
    (hTr : ∀ s q (E A : QReg) (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E),
      IFreeM.IsChargeBound (Tr s q E ℓ) (cmdCharge hashCharge) 0)
    (leaf : ∀ u, X u → St → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A)
    (s : St) {n : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge hashCharge) n) :
    IFreeM.IsChargeBound (mixRun Tr leaf x s) (cmdCharge hashCharge) n := by
  induction x using IFreeM.inductionOn generalizing s n with
  | pure _ _ => trivial
  | liftBind A cmd next ih =>
    replace hx := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hx
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨hx.1, fun b ↦ ih b s (hx.2 b)⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨hx.1, fun b ↦ ih b s (hx.2 b)⟩
    · refine (IFreeM.isChargeBound_bind (n₂ := n) (hTr s q E A ℓ) fun u l ↦ ?_).mono
        (by omega)
      obtain ⟨rfl, v⟩ := l
      exact ih ⟨v.1⟩ v.2 ((hx.2 ⟨v.1⟩).mono (Nat.sub_le _ _))

/-- **The mixed game makes exactly the adversary's hash calls**: within `n` hash calls whenever
the adversary is, whatever the honest work of the challenger and the reduction. -/
theorem isChargeBound_mixGame {Pub Out : Type} (E : Experiment romWorld R' Pub Out) {S0 F : Type}
    (pre : Pub → OracleComp (romWorld.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler romWorld R R' St)
    (post : Pub → S0 → F → St → OracleComp (romWorld.Oracles + R') Out) {n : ℕ}
    (hn : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge hashCharge) n) :
    IFreeM.IsChargeBound (mixGame E pre adv st0 σ post) (cmdCharge hashCharge) n := by
  have hT : ∀ (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
      (σ' : HHandler romWorld R R' St) s q (E A : QReg)
      (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E),
      IFreeM.IsChargeBound (mixTrees ans σ' s q E ℓ) (cmdCharge hashCharge) 0 := by
    intro _ _ _ _ _ _ _
    unfold mixTrees
    rw [QuantumComp₂.map_eq_bind_pure]
    exact (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (isChargeBound_act _ _ 0)
      fun _ ↦ (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (isChargeBound_redImpl _ _ _ _)
        fun _ ↦ IFreeM.isChargeBound_pure _ 0).mono le_rfl).mono le_rfl
  have hN : ∀ s, IFreeM.IsChargeBound (mixNormal (E.answer s) (pre (E.pub s)) (adv (E.pub s))
      (st0 (E.pub s)) (σ (E.pub s)) (post (E.pub s))) (cmdCharge hashCharge) n := by
    intro s
    unfold mixNormal mixRunL
    exact (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := n) (isChargeBound_redImpl _ _ _ _) fun p ↦
      (FreeM₂.isChargeBound_bind (n₁ := n) (n₂ := 0)
        (isChargeBound_mixRun _ (hT _ _) _ _ _ (hn _ _)) fun _ ↦
          isChargeBound_redImpl _ _ _ _).mono (by omega)).mono (by omega)
  unfold mixGame
  exact (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := n)
    (isChargeBound_toQuantumAt_mixImpl .setup _ _) fun s ↦
      (FreeM₂.isChargeBound_bind (n₁ := n) (n₂ := 0) (hN s) fun _ ↦
        isChargeBound_toQuantumAt_mixImpl .judge _ _).mono (by omega)).mono (by omega)

end game

/-! ## Memory-updating reads and the hardwired runtime -/

section memory

open Quantum.Xmss.Assembly (DropRec liftReadProg runtime1R runtimeR recSpec recStep
  evalDistMap_runtime1R_eq dropsTo_liftReadProg evalDistMap_runtime1_eq_spongeHardwiredReadRuntime
  dropRec_substitute)
open Quantum.Xmss.Hybrid (runtime1 runtime2)
open Quantum.Sponge (spongeHardwiredRuntime hwSpec)

variable {T S M : Type} [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M]

section helpers

variable (S M) in
/-- The commands of the record signature. -/
abbrev RecP := QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (Quantum.Xmss.Assembly.recHwSpec HashOutput HashDomain S M)

/-- The commands of the hardwired signature with memory `Unit`. -/
abbrev HwP := QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Unit)

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- `DropRec` of a local operation, in `liftBind` form. -/
theorem dropRec_liftBind_prim {Ω : QReg → Type} {A : QReg} (o : LocalSig.instruments.{0}.Op A)
    {f : (b : (RecP S M).B A (.prim o)) → IFreeM (RecP S M) Ω ((RecP S M).src A (.prim o) b)}
    {g : (b : (RecP S M).B A (.prim o)) → IFreeM HwP Ω ((RecP S M).src A (.prim o) b)}
    (h : ∀ b, DropRec S (f b) (g b)) :
    DropRec S (IFreeM.liftBind (P := RecP S M) (.prim o) f)
      (IFreeM.liftBind (P := HwP) (.prim o) g) :=
  DropRec.prim o (k := fun b ↦ f ⟨b⟩) (k' := fun b ↦ g ⟨b⟩) fun b ↦ h ⟨b⟩

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- `DropRec` of a sponge call, in `liftBind` form. -/
theorem dropRec_liftBind_sponge {Ω : QReg → Type} {A : QReg} (i : Quantum.Sponge.SpongePort)
    (E : QReg) (ℓ : A ≃ (hwSpec HashOutput HashDomain Unit).In (.inl (.inl i)) × E)
    {f : (b : (RecP S M).B A (.query (.inl (.inl (.inl i))) E ℓ)) →
      IFreeM (RecP S M) Ω ((RecP S M).src A (.query (.inl (.inl (.inl i))) E ℓ) b)}
    {g : (b : (RecP S M).B A (.query (.inl (.inl (.inl i))) E ℓ)) →
      IFreeM HwP Ω ((RecP S M).src A (.query (.inl (.inl (.inl i))) E ℓ) b)}
    (h : ∀ b, DropRec S (f b) (g b)) :
    DropRec S (IFreeM.liftBind (P := RecP S M) (.query (.inl (.inl (.inl i))) E ℓ) f)
      (IFreeM.liftBind (P := HwP) (.query (.inl (.inl i)) E ℓ) g) :=
  DropRec.sponge i E ℓ (k := fun b ↦ f ⟨b⟩) (k' := fun b ↦ g ⟨b⟩) fun b ↦ h ⟨b⟩

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- `DropRec` of a read of `h` with any memory update, in `liftBind` form. -/
theorem dropRec_liftBind_readH {Ω : QReg → Type} {A : QReg} (z : HashDomain)
    (u : Finset S × M → Option HashOutput → Finset S × M) (E : QReg)
    (ℓ : A ≃ (hwSpec HashOutput HashDomain Unit).In (.inl (.inr (.readH z keepMem))) × E)
    {f : (b : (RecP S M).B A (.query (.inl (.inl (.inr (.readH z u)))) E ℓ)) →
      IFreeM (RecP S M) Ω ((RecP S M).src A (.query (.inl (.inl (.inr (.readH z u)))) E ℓ) b)}
    {g : (b : HwP.B A (.query (.inl (.inr (.readH z keepMem))) E ℓ)) →
      IFreeM HwP Ω (HwP.src A (.query (.inl (.inr (.readH z keepMem))) E ℓ) b)}
    (h : ∀ (o : Option HashOutput) (p : Finset S × M), DropRec S (f ⟨(o, p)⟩) (g ⟨(o, ())⟩)) :
    DropRec S (IFreeM.liftBind (P := RecP S M) (.query (.inl (.inl (.inr (.readH z u)))) E ℓ) f)
      (IFreeM.liftBind (P := HwP) (.query (.inl (.inr (.readH z keepMem))) E ℓ) g) :=
  DropRec.readH z u E ℓ (k := fun b ↦ f ⟨b⟩) (k' := fun b ↦ g ⟨b⟩) h

end helpers

/-- `DropRec` steps on two programs: normalize both heads, then match the command. -/
local macro "drop_prim" : tactic => `(tactic| (
  (conv => arg 2; whnf); (conv => arg 3; whnf);
  refine dropRec_liftBind_prim _ fun _ ↦ ?_))
local macro "drop_sponge" : tactic => `(tactic| (
  (conv => arg 2; whnf); (conv => arg 3; whnf);
  refine dropRec_liftBind_sponge _ _ _ fun _ ↦ ?_))
local macro "drop_readH" : tactic => `(tactic| (
  (conv => arg 2; whnf); (conv => arg 3; whnf);
  refine dropRec_liftBind_readH _ _ _ _ fun _ _ ↦ ?_))
local macro "drop_pure" : tactic => `(tactic| (
  (conv => arg 2; whnf); (conv => arg 3; whnf);
  exact DropRec.pure _))

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- **Dropping the memory updates of the reads**, for any program of tagged calls. -/
theorem dropRec_substitute_readSub
    (upd : T → HashDomain → Finset S × M → Option HashOutput → Finset S × M) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec T)) Ω A) :
    DropRec S (IFreeM.mapLens (QuantumComp.ordinaryLens (t := recSpec S M))
        (IFreeM.mapLens Quantum.Xmss.Assembly.liftReadLens (IFreeM.substitute (readSub upd) x)))
      (IFreeM.mapLens Quantum.Xmss.Assembly.liftReadLens
        (IFreeM.substitute (readSub (keepAll T Unit)) x)) := by
  rw [← IFreeM.substitute_toSubstitution, ← IFreeM.substitute_toSubstitution,
    ← IFreeM.substitute_toSubstitution, Quantum.Xmss.Assembly.substitute_substitute,
    Quantum.Xmss.Assembly.substitute_substitute, Quantum.Xmss.Assembly.substitute_substitute]
  refine dropRec_substitute (fun A c ↦ ?_) x
  rcases c with o | ⟨p | ⟨tag, n | z⟩, E, ℓ⟩
  · drop_prim
    drop_pure
  · drop_sponge
    drop_pure
  · drop_prim
    drop_prim
    drop_pure
  · drop_prim
    drop_readH
    drop_prim
    drop_pure

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- **Dropping the memory updates of the reads**: the read program with the memory policy `upd`,
lifted to the record signature, drops to the read program keeping the memory `Unit`. -/
theorem dropRec_toReads (upd : T → HashDomain → Finset S × M → Option HashOutput → Finset S × M)
    {A B : QReg} {α : Type} (x : QComp (MixSpec T) A B α) :
    DropRec S ((liftReadProg (toReads upd x)).liftOrdinary (t := recSpec S M))
      (liftReadProg (toReads (keepAll T Unit) x)) :=
  dropRec_substitute_readSub upd x

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- An extended runtime runs a lifted program with the law of the original runtime. -/
theorem evalDistMap_extend_liftOrdinary {s t : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime s)
    (step : ∀ i : t.Port, SubInstrument (t.In i × R.D) (t.Out i × R.D) (t.Result i))
    {Ω : QReg → Type} {A : QReg} (x : QuantumComp LocalSig.instruments.{0} s Ω A)
    (ρ : SubState A) {γ : Type} [MeasurableSpace γ] (f : (Σ u, Ω u) → γ) :
    (R.extend step).evalDistMap .instruments (x.liftOrdinary (t := t)) ρ f =
      R.evalDistMap .instruments x ρ f := by
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.jointPost,
    QuantumRuntime.run_liftOrdinary]
  rfl

/-- **The QROM winning probability of a mixed program is at most that of its read program with
any memory policy** in the hardwired runtime started with no hardwired cell and the memory `m₀`
(the reads' memory updates are invisible to the law: `DropRec`). -/
theorem probAvg_romRun_le_hw
    (upd : T → HashDomain → Finset S × M → Option HashOutput → Finset S × M)
    (m₀ : Finset S × M) (x : QComp (MixSpec T) (QReg.of Unit) (QReg.of Unit) Bool) :
    romWorld.probAvg (romRun x) ≤
      (spongeHardwiredRuntime HashOutput HashDomain (hwEmpty HashOutput HashDomain)
        m₀).evalDistMap .instruments (liftReadProg (toReads upd x)) (SubState.basis ())
          (fun p ↦ p.2.2) {true} := by
  have h2 := evalDistMap_runtime1_eq_spongeHardwiredReadRuntime (hwEmpty HashOutput HashDomain) ()
    (dropsTo_liftReadProg (hwEmpty HashOutput HashDomain) (toReads (keepAll T Unit) x))
    (SubState.basis ()) (fun p ↦ p.2.2)
  have h3 := evalDistMap_runtime1R_eq (hwEmpty HashOutput HashDomain) m₀ (dropRec_toReads upd x)
    (SubState.basis ()) (fun p ↦ p.2.2)
  have hCov : Quantum.Xmss.Hybrid.Covers (hwEmpty HashOutput HashDomain)
      (∅ : Set HashDomain) (∅ : Set HashOutput) ∅ :=
    ⟨fun _ h ↦ absurd rfl h, fun _ h ↦ absurd rfl h, fun _ h ↦ absurd rfl h⟩
  have hw : Quantum.Xmss.Assembly.extWeight (t := recSpec S M)
      (Quantum.Xmss.Hybrid.hiddenMass (M := Finset S × M) (∅ : Set HashDomain)
        (∅ : Set HashOutput) ∅) = fun _ _ ↦ 0 := by
    funext i σ
    rcases i with ((p | c) | c) | j
    · cases p <;> simp [Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight,
        Quantum.Xmss.Hybrid.hiddenMass, Quantum.Xmss.Hybrid.diagMass]
    · cases c <;> simp [Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight,
        Quantum.Xmss.Hybrid.hiddenMass, Quantum.Xmss.Hybrid.diagMass]
    · rfl
    · rfl
  have h4 := Quantum.Xmss.Assembly.sqrt_win_runtime1R_le LocalSig.Interp.instruments
    (hwEmpty HashOutput HashDomain) m₀ hCov
    ((liftReadProg (toReads upd x)).liftOrdinary (t := recSpec S M)) (SubState.basis ())
    (fun p ↦ p.2.2) (measurableSet_singleton true) (μ := fun _ ↦ 0)
    (fun j ↦ le_of_eq ((congrArg (fun w ↦ (runtimeR m₀).queryWeight LocalSig.Interp.instruments
      w ((liftReadProg (toReads upd x)).liftOrdinary (t := recSpec S M))
      ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix)
      j) hw).trans (Quantum.Xmss.Hybrid.queryWeight_zero_weight _ _ _ _ _)))
  simp only [mul_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), tsum_zero,
    add_zero] at h4
  have h5 := (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2⁻¹)).1 h4
  rw [probAvg_romRun_eq, ← h2, ← h3]
  exact h5.trans_eq (congrArg (fun μ : Measure Bool ↦ μ {true})
    (evalDistMap_extend_liftOrdinary _ _ _ _ _))

/-- One step of a charge bound on a command tree: normalize the head, then charge the command. -/
local macro "charge_step" : tactic => `(tactic| (
  (conv => arg 1; whnf);
  refine (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
    ⟨by first | exact Nat.zero_le _ | exact le_rfl, fun _ ↦ ?_⟩))

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- **Only the hash calls of a mixed program become calls of the oracle's port** in its read
program, for any program of tagged calls. -/
theorem isChargeBound_substitute_readSub (upd : T → HashDomain → M → Option HashOutput → M)
    {Ω : QReg → Type} {A : QReg}
    {x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec T)) Ω A} {n : ℕ}
    (hx : IFreeM.IsChargeBound x (cmdCharge hashCharge) n) :
    IFreeM.IsChargeBound (IFreeM.mapLens Quantum.Xmss.Assembly.liftReadLens
        (IFreeM.substitute (readSub upd) x))
      (Quantum.Sponge.portCharge fun i ↦ if Quantum.Sponge.hwCls i then 0 else 1) n := by
  rw [← IFreeM.substitute_toSubstitution, Quantum.Xmss.Assembly.substitute_substitute]
  refine IFreeM.IsChargeBound.substitute _ (fun A c ↦ ?_) hx
  rcases c with o | ⟨p | ⟨tag, n | z⟩, E, ℓ⟩
  · charge_step
    exact IFreeM.isChargeBound_pure _ _
  · charge_step
    exact IFreeM.isChargeBound_pure _ _
  · charge_step
    charge_step
    exact IFreeM.isChargeBound_pure _ _
  · charge_step
    charge_step
    charge_step
    exact IFreeM.isChargeBound_pure _ _

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- **Only the hash calls of a mixed program become calls of the oracle's port** in its read
program: a mixed program within `n` hash calls (any number of tagged calls) has a read program
within `n` calls of the non-classical ports. -/
theorem isChargeBound_toReads (upd : T → HashDomain → M → Option HashOutput → M) {A B : QReg}
    {α : Type} {x : QComp (MixSpec T) A B α} {n : ℕ}
    (hx : IFreeM.IsChargeBound x (cmdCharge hashCharge) n) :
    IFreeM.IsChargeBound (liftReadProg (toReads upd x))
      (Quantum.Sponge.portCharge fun i ↦ if Quantum.Sponge.hwCls i then 0 else 1) n :=
  isChargeBound_substitute_readSub upd hx

/-- **The property game of a straight-line reduction in the QROM, as a hardwired-runtime
program**: its winning probability is at most that of the read program of its mixed game, every
classical call a read of its cell updating the memory by its caller's policy `upd` (any policy),
and that program makes only the adversary's `n` calls of the oracle's port
(`isChargeBound_toReads`, `isChargeBound_mixGame`), whatever the reduction's honest work. -/
theorem probAvg_game_slRed_le_hw {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type}
    {R' : OracleSpec.{0, 0} Q'} {St Pub Out : Type} (E : Experiment romWorld R' Pub Out)
    {S0 F : Type} (pre : Pub → OracleComp (romWorld.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler romWorld R R' St)
    (post : Pub → S0 → F → St → OracleComp (romWorld.Oracles + R') Out)
    (upd : Caller → HashDomain → Finset S × M → Option HashOutput → Finset S × M)
    (m₀ : Finset S × M) :
    romWorld.probAvg (E.game fun p ↦ slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (spongeHardwiredRuntime HashOutput HashDomain (hwEmpty HashOutput HashDomain)
        m₀).evalDistMap .instruments (liftReadProg (toReads upd (mixGame E pre adv st0 σ post)))
          (SubState.basis ()) (fun p ↦ p.2.2) {true} := by
  refine le_of_eq_of_le ?_ (probAvg_romRun_le_hw upd m₀ _)
  rw [OracleWorld.probAvg_eq_sum, OracleWorld.probAvg_eq_sum]
  exact Finset.sum_congr rfl fun H _ ↦ by rw [probAt_game_slRed_eq]

end memory

/-! ## The graded event bound with exact read costs -/

section event

open Matrix

open Quantum.Sponge (spongeHardwiredRuntime hwSpec HwProg hwReadKraus hwProgKraus hwProjector
  hwCost hwCls portCharge)

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **The exact flip of a read port**: the weight of the event `E` it adds to the input `σ`. -/
noncomputable def readFlip (E : Set (RomReg HashDomain HashOutput M)) [DecidablePred (· ∈ E)]
    (c : HwRead HashOutput HashDomain M)
    (σ : Matrix (Unit × RomReg HashDomain HashOutput M) (Unit × RomReg HashDomain HashOutput M) ℂ) :
    ℝ≥0∞ :=
  (∑' r, QuantumRuntime.potential (hwProjector E) (MatrixMap.conj (hwReadKraus c r) σ)) -
    QuantumRuntime.potential (hwProjector E) σ

/-- **The exact flip of a program port.** -/
noncomputable def progFlip (E : Set (RomReg HashDomain HashOutput M)) [DecidablePred (· ∈ E)]
    (c : HwProg HashOutput HashDomain)
    (σ : Matrix (Unit × RomReg HashDomain HashOutput M) (Unit × RomReg HashDomain HashOutput M) ℂ) :
    ℝ≥0∞ :=
  (∑' r, QuantumRuntime.potential (hwProjector E) (MatrixMap.conj (hwProgKraus c r) σ)) -
    QuantumRuntime.potential (hwProjector E) σ

/-- **A read invisible to the event `E`**: a read of cell `z` with memory update `u` never moves a
state across `E`, whatever it leaves in the cell. -/
def ReadInvisible (E : Set (RomReg HashDomain HashOutput M)) (z : HashDomain)
    (u : M → Option HashOutput → M) : Prop :=
  ∀ (s s' : RomReg HashDomain HashOutput M) (o : Option HashOutput),
    (∀ b, b ≠ z → s'.1.1 b = s.1.1 b) → s'.1.2 = s.1.2 → s'.2.1 = s.2.1 →
      s'.2.2 = u s.2.2 o → (s' ∈ E ↔ s ∈ E)

/-- **Off-tweak insensitivity**: a read invisible to the event costs nothing. -/
theorem readFlip_eq_zero (E : Set (RomReg HashDomain HashOutput M)) [DecidablePred (· ∈ E)]
    {z : HashDomain} {u : M → Option HashOutput → M} (h : ReadInvisible E z u)
    (σ : Matrix (Unit × RomReg HashDomain HashOutput M) (Unit × RomReg HashDomain HashOutput M) ℂ)
    (hσ : σ.PosSemidef) : readFlip E (.readH z u) σ = 0 := by
  have hd : ∀ r (q' q : Unit × RomReg HashDomain HashOutput M),
      hwReadKraus (.readH z u) r q' q ≠ 0 → (q'.2 ∈ E ↔ q.2 ∈ E) := by
    intro r q' q hne
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ Quantum.Sponge.readKrausH z u r) q' q ≠ 0 at hne
    rw [kroneckerMap_apply] at hne
    have h2 := right_ne_zero_of_mul hne
    obtain ⟨hc, hk, hW⟩ := Quantum.Xmss.Assembly.readKrausH_ne_zero_rest z u r h2
    have hm : q'.2.2.2 = u q.2.2.2 r.1 := by
      rw [Quantum.Sponge.readKrausH, Quantum.Sponge.clsKraus_apply] at h2
      split_ifs at h2 with hcond
      · rw [hcond.2, hcond.1]
      · exact absurd rfl h2
    exact h q.2 q'.2 r.1 hc hk hW hm
  have hcomm : ∀ r, ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector E) * hwReadKraus (.readH z u) r =
      hwReadKraus (.readH z u) r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector E) := by
    intro r
    rw [Quantum.Sponge.one_kronecker_hwProjector]
    ext q' q
    simp only [Quantum.Sponge.indProj, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hk : hwReadKraus (.readH z u) r q' q = 0
    · rw [hk, mul_zero, zero_mul]
    · have hind : Quantum.Sponge.ind (Quantum.Sponge.liftSet E) q' =
          Quantum.Sponge.ind (Quantum.Sponge.liftSet E) q := by
        simp only [Quantum.Sponge.ind, Quantum.Sponge.mem_liftSet, hd r q' q hk]
      rw [hind, mul_comm]
  have hF : ∑ r, (hwReadKraus (.readH z u) r)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector E) *
      hwReadKraus (.readH z u) r = (1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector E := by
    simp_rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc]
    rw [← Finset.sum_mul, Quantum.Sponge.sum_hwReadKraus, Matrix.one_mul]
  have hle := Quantum.Sponge.potential_kraus_le E (hwReadKraus (.readH z u))
    (Quantum.Sponge.sum_hwReadKraus _) 0 (by simp) (by simp) σ hσ
  have hc : Quantum.Sponge.flipCost E (hwReadKraus (.readH z u)) 0 σ = 0 := by
    simp [Quantum.Sponge.flipCost, hF]
  rw [readFlip]
  exact tsub_eq_zero_of_le (hle.trans (by rw [hc, add_zero]))

omit [Fintype M] [DecidableEq M] in
/-- **A read of a cell without a target is invisible to the cell-target event** when its memory
update changes no target. -/
theorem readInvisible_cellTargetBad
    {tgt : Hw HashOutput HashDomain → M → HashDomain → Set HashOutput} {z : HashDomain}
    {u : M → Option HashOutput → M} (hz : ∀ W m, tgt W m z = ∅)
    (hu : ∀ W m o, tgt W (u m o) = tgt W m) : ReadInvisible (CellTargetBad tgt) z u := by
  intro s s' o hc hk hW hm
  have ht : tgt s'.2.1 s'.2.2 = tgt s.2.1 s.2.2 := by rw [hW, hm, hu]
  constructor
  · rintro ⟨x, y, hxy, hy⟩
    have hx : x ≠ z := fun hx ↦ by subst hx; rw [hz] at hy; exact hy
    refine ⟨x, y, ?_, ht ▸ hy⟩
    change (s.2.1.1 x).or (s.1.1 x) = some y
    change (s'.2.1.1 x).or (s'.1.1 x) = some y at hxy
    rwa [hW, hc x hx] at hxy
  · rintro ⟨x, y, hxy, hy⟩
    have hx : x ≠ z := fun hx ↦ by subst hx; rw [hz] at hy; exact hy
    refine ⟨x, y, ?_, ht.symm ▸ hy⟩
    change (s'.2.1.1 x).or (s'.1.1 x) = some y
    change (s.2.1.1 x).or (s.1.1 x) = some y at hxy
    rwa [hW, hc x hx]

open scoped Classical in
/-- **The graded event bound for a cell-target event with exact read costs**: with at most `q`
calls of the oracle's port and at most `K` classical calls (any number: `K` is not in the bound),
the final weight of `CellTargetBad tgt` is at most `(q √(6 ε) + √(∑ flips))²`, the flips summed
over the classical calls along the run (zero at reads invisible to the event,
`readFlip_eq_zero`). -/
theorem eventWeight_cellTargetBad_le
    (tgt : Hw HashOutput HashDomain → M → HashDomain → Set HashOutput) (m₀ : M) {ε : ℝ≥0∞}
    (hεtop : ε ≠ ⊤)
    (hε : ∀ (W : Hw HashOutput HashDomain) (m : M) (x : HashDomain), W.1 x = none →
      ((Finset.univ.filter fun y ↦ y ∈ tgt W m x).card : ℝ≥0∞) /
        Fintype.card HashOutput ≤ ε)
    {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {A : QReg}
    (x : QuantumComp L (hwSpec HashOutput HashDomain M) Ω A) {q K : ℕ}
    (hxq : IFreeM.IsChargeBound x (portCharge fun i ↦ if hwCls i then 0 else 1) q)
    (hxK : IFreeM.IsChargeBound x (portCharge fun i ↦ if hwCls i then 1 else 0) K)
    (ρ : SubState A) :
    (spongeHardwiredRuntime HashOutput HashDomain (hwEmpty HashOutput HashDomain) m₀).eventWeight
        I (hwProjector (CellTargetBad tgt)) x
        (ρ.matrix ⊗ₖ (spongeHardwiredRuntime HashOutput HashDomain
          (hwEmpty HashOutput HashDomain) m₀).init.matrix) ≤
      (q * (6 * ε) ^ (2⁻¹ : ℝ) +
        (spongeHardwiredRuntime HashOutput HashDomain (hwEmpty HashOutput HashDomain)
          m₀).totalWeight I (hwCost (readFlip (CellTargetBad tgt)) (progFlip (CellTargetBad tgt)))
          x (ρ.matrix ⊗ₖ (spongeHardwiredRuntime HashOutput HashDomain
            (hwEmpty HashOutput HashDomain) m₀).init.matrix) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := Quantum.Sponge.eventWeight_spongeHardwiredRuntime_le (CellTargetBad tgt)
    upClosed_slice_cellTargetBad (hwEmpty HashOutput HashDomain) m₀
    (not_mem_cellTargetBad_start _ m₀ fun _ _ h ↦ by simp [hwEmpty, Database.empty] at h)
    (q := q) (K := K) (fun _ ↦ ε) (fun _ _ ↦ hεtop)
    (fun _ _ W m ↦ freshBound_slice_cellTargetBad W m (hε W m) _)
    (readFlip (CellTargetBad tgt)) (progFlip (CellTargetBad tgt))
    (fun _ _ _ ↦ le_add_tsub) (fun _ _ _ ↦ le_add_tsub) I x hxq hxK ρ
  refine h.trans_eq ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end event

end Quantum.StdModel.Qrom

end
