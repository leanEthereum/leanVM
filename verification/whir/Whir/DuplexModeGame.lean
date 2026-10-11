import Whir.DuplexFraming
import Whir.DuplexCompression

/-! Source-pinned, classical public-compression games for #552. These definitions
contain no PCS relation or acceptance predicate. All primitive calls (including
verification, auxiliary hashing, and PoW) use the same public oracle; each
construction occurrence pays its complete uncached path. The only external
cryptographic boundaries below are explicitly named distinguishing games.
No small concrete-BLAKE2s idealization gap is proved or asserted. -/
namespace Whir.DuplexModeGame
open FiatShamirGame DuplexRefinement DuplexFraming

local instance : Finite UInt64 :=
  Finite.of_injective ByteCodec.encodeK ByteCodec.encodeK_injective
noncomputable local instance : Fintype UInt64 := Fintype.ofFinite _

private def nodeFields (n : Node) : Digest32 × Block64 × UInt64 × Bool :=
  (n.cv,n.block,n.tweak,n.last)

private theorem nodeFields_injective : Function.Injective nodeFields := by
  intro a b h
  cases a; cases b
  simp_all [nodeFields]

local instance : Finite Node := Finite.of_injective nodeFields nodeFields_injective
noncomputable local instance : Fintype Node := Fintype.ofFinite _

abbrev PrimitiveOracle := Node → Digest32

/-- The DMV capacity is the actual full, untruncated chaining-value space. -/
theorem digest_card : Fintype.card Digest32 = 2^256 := by
  norm_num [Digest32, Byte, Fintype.card_fun]

def compressionOf (oracle : PrimitiveOracle) : Compression :=
  fun cv block tweak last => oracle ⟨cv,block,tweak,last⟩

def blake2sOracle : PrimitiveOracle := fun n =>
  DuplexCompression.compress n.cv n.block n.tweak n.last

/-- Every purpose shares one primitive budget. The labels are accounting data,
not disjoint oracles or a reason to exclude verification/PoW from Q. -/
inductive Purpose where
  | direct | verification | auxiliary | pow
  deriving DecidableEq, Repr

inductive Query where
  | primitive (purpose : Purpose) (input : Node)
  | construction (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate)

def Query.cost : Query → Nat
  | .primitive _ _ => 1
  | .construction q _ => pathCost q

/-- An adaptive, single-stage oracle interaction. A continuation sees the
complete 256-bit answer. Branching, repeated coordinates, statements and clones
all remain in this one interaction with its one shared oracle. -/
inductive Program (Result : Type) where
  | done (result : Result)
  | ask (query : Query) (next : Digest32 → Program Result)

/-- A genuine worst-case resource certificate, quantified over every reply,
including replies on rejecting continuations. No budget is waived. -/
def Counts {Result : Type} : Nat → Program Result → Prop
  | _, .done _ => True
  | Q, .ask q next => q.cost ≤ Q ∧ ∀ d, Counts (Q-q.cost) (next d)

structure Observation where
  query : Query
  answer : Digest32

structure View (Result : Type) where
  observations : List Observation
  result : Result

/-- Internal meter state is deliberately absent from the distinguisher's view:
the ideal simulator's private RO queries are not public observations. -/
structure Execution (Result : Type) where
  view : View Result
  primitiveCost : Nat
  constructionRequests : Nat
  simulatorQueries : Nat

def prepend {Result : Type} (q : Query) (answer : Digest32) (simulatorCalls : Nat)
    (rest : Execution Result) : Execution Result :=
  {view := ⟨⟨q,answer⟩ :: rest.view.observations,rest.view.result⟩,
   primitiveCost := q.cost + rest.primitiveCost,
   constructionRequests := (match q with | .primitive _ _ => 0 | .construction _ _ => 1) + rest.constructionRequests,
   simulatorQueries := simulatorCalls + rest.simulatorQueries}

def realAnswer (oracle : PrimitiveOracle) (iv : Digest32) : Query → Digest32
  | .primitive _ input => oracle input
  | .construction q _ => evalCoordinate (compressionOf oracle) iv q

def runReal {Result : Type} (oracle : PrimitiveOracle) (iv : Digest32) : Program Result → Execution Result
  | .done r => ⟨⟨[],r⟩,0,0,0⟩
  | .ask q next =>
    let answer := realAnswer oracle iv q
    prepend q answer 0 (runReal oracle iv (next answer))

theorem runReal_counts {Result : Type} (oracle : PrimitiveOracle) (iv : Digest32)
    (p : Program Result) (Q : Nat) (h : Counts Q p) : (runReal oracle iv p).primitiveCost ≤ Q := by
  induction p generalizing Q with
  | done r => simp [runReal]
  | ask q next ih =>
    have hr := ih (realAnswer oracle iv q) (Q-q.cost) (h.2 _)
    simp only [runReal, prepend]
    have := h.1
    omega

/-- A finite representation of lists of length at most Q, used only to make
uniform random-oracle tables a literal finite probability experiment. -/
abbrev ShortList (α : Type) (Q : Nat) := (n : Fin (Q+1)) × (Fin n.val → α)
abbrev RawKey (Q : Nat) := ShortList (Option Digest32 × Block64) Q × ShortList (UInt64 × Bool) Q

/-- Explicit finite-table witnesses for downstream distributional couplings;
these do not install global UInt64 or function-space instances. -/
@[instance_reducible]
noncomputable def rawKeyFintype (Q : Nat) : Fintype (RawKey Q) := by
  classical
  infer_instance

@[instance_reducible]
noncomputable def rawOracleFintype (Q : Nat) : Fintype (RawKey Q → Digest32) := by
  classical
  infer_instance

def shortList {α : Type} (Q : Nat) (xs : List α) (h : xs.length ≤ Q) : ShortList α Q :=
  ⟨⟨xs.length,by omega⟩,fun i => xs[i.val]⟩

def expandShort {α : Type} {Q : Nat} (xs : ShortList α Q) : List α := List.ofFn xs.2

@[simp] theorem expandShort_shortList {α : Type} (Q : Nat) (xs : List α) (h : xs.length ≤ Q) :
    expandShort (shortList Q xs h) = xs := by simp [expandShort, shortList]

def expandKey {Q : Nat} (key : RawKey Q) : Extracted :=
  ⟨expandShort key.1,expandShort key.2⟩

def restrictKey (Q : Nat) (key : Extracted) (hm : key.message.length ≤ Q)
    (ht : key.template.length ≤ Q) : RawKey Q :=
  (shortList Q key.message hm,shortList Q key.template ht)

@[simp] theorem expandKey_restrictKey (Q : Nat) (key : Extracted)
    (hm : key.message.length ≤ Q) (ht : key.template.length ≤ Q) :
    expandKey (restrictKey Q key hm ht) = key := by
  cases key
  simp [expandKey, restrictKey]

theorem modeKey_lengths (iv : Digest32) (q : Coordinate) :
    (modeKey iv q).message.length = pathCost q ∧ (modeKey iv q).template.length = pathCost q := by
  simp [modeKey, keyFromPlan, pathCost]

def constructionKey (Q : Nat) (iv : Digest32) (q : Coordinate) (h : pathCost q ≤ Q) : RawKey Q :=
  restrictKey Q (modeKey iv q) (by simpa only [(modeKey_lengths iv q).1] using h)
    (by simpa only [(modeKey_lengths iv q).2] using h)

@[simp] theorem expand_constructionKey (Q : Nat) (iv : Digest32) (q : Coordinate)
    (h : pathCost q ≤ Q) : expandKey (constructionKey Q iv q h) = modeKey iv q := by
  exact expandKey_restrictKey _ _ _ _

/-- The simulator is an actual RO-query program, not a claimed query count.
Its queries are metered by the interpreter, and are not exposed to the caller. -/
inductive ROProgram (Q : Nat) (Result : Type) where
  | done (result : Result)
  | ask (key : RawKey Q) (next : Digest32 → ROProgram Q Result)

def runRO {Q : Nat} {Result : Type} (ro : RawKey Q → Digest32) : ROProgram Q Result → Result × Nat
  | .done result => (result,0)
  | .ask key next =>
    let r := runRO ro (next (ro key))
    (r.1,r.2+1)

structure Simulator (Q : Nat) (Seed State : Type) where
  initial : Seed → State
  answer : State → Node → ROProgram Q (State × Digest32)

def runIdeal {Q : Nat} {Seed State Result : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) :
    (p : Program Result) → (remaining : Nat) → remaining ≤ Q → Counts remaining p → Execution Result
  | .done r, _, _, _ => ⟨⟨[],r⟩,0,0,0⟩
  | .ask (.primitive purpose input) next, remaining, cap, counted =>
    let answer := runRO ro (sim.answer state input)
    prepend (.primitive purpose input) answer.1.2 answer.2
      (runIdeal sim ro iv answer.1.1 (next answer.1.2) (remaining-1) (by omega) (counted.2 _))
  | .ask (.construction q valid) next, remaining, cap, counted =>
    let key := constructionKey Q iv q (by exact counted.1.trans cap)
    let answer := ro key
    prepend (.construction q valid) answer 0
      (runIdeal sim ro iv state (next answer) (remaining-pathCost q) (by omega) (counted.2 _))

theorem runIdeal_counts {Q : Nat} {Seed State Result : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (p : Program Result)
    (remaining : Nat) (cap : remaining ≤ Q) (h : Counts remaining p) :
    (runIdeal sim ro iv state p remaining cap h).primitiveCost ≤ remaining := by
  induction p generalizing state remaining with
  | done r => simp [runIdeal]
  | ask q next ih =>
    cases q with
    | primitive purpose input =>
      have hr := ih (runRO ro (sim.answer state input)).1.2
        (runRO ro (sim.answer state input)).1.1 (remaining-1) (by omega) (h.2 _)
      simp only [runIdeal, prepend, Query.cost]
      have hh : 1 ≤ remaining := h.1
      omega
    | construction q valid =>
      have hr := ih (ro (constructionKey Q iv q (h.1.trans cap))) state
        (remaining-pathCost q) (by omega) (h.2 _)
      simp only [runIdeal, prepend, Query.cost]
      have hh : pathCost q ≤ remaining := h.1
      omega

/-- Classical real experiment: a uniformly sampled *public* compression table.
All direct and construction uses share it, including chosen chaining values. -/
noncomputable def realProbability {AdvCoins Result : Type} [Fintype AdvCoins]
    (iv : Digest32) (adversary : AdvCoins → Program Result) (D : View Result → Bool) : ℚ := by
  classical
  exact distinguishProbability
    (fun coins : PrimitiveOracle × AdvCoins => (runReal coins.1 iv (adversary coins.2)).view) D

/-- Classical ideal experiment: one uniformly sampled raw message/template RO
shared by construction requests and the stateful primitive simulator. -/
noncomputable def idealProbability {Q : Nat} {Seed State AdvCoins Result : Type}
    [Fintype Seed] [Fintype AdvCoins] (sim : Simulator Q Seed State) (iv : Digest32)
    (adversary : AdvCoins → Program Result) (counted : ∀ a, Counts Q (adversary a))
    (D : View Result → Bool) : ℚ := by
  classical
  exact distinguishProbability
    (fun coins : (RawKey Q → Digest32) × Seed × AdvCoins =>
      (runIdeal sim coins.1 iv (sim.initial coins.2.1) (adversary coins.2.2) Q (by omega)
        (counted coins.2.2)).view) D

noncomputable def concreteProbability {AdvCoins Result : Type} [Fintype AdvCoins]
    (iv : Digest32) (adversary : AdvCoins → Program Result) (D : View Result → Bool) : ℚ :=
  distinguishProbability (fun a => (runReal blake2sOracle iv (adversary a)).view) D

/-- Advantage in the actual public-compression construction/simulator games. -/
noncomputable def ModeAdv {Q : Nat} {Seed State AdvCoins Result : Type}
    [Fintype Seed] [Fintype AdvCoins] (sim : Simulator Q Seed State) (iv : Digest32)
    (adversary : AdvCoins → Program Result) (counted : ∀ a, Counts Q (adversary a))
    (D : View Result → Bool) : ℚ :=
  |realProbability iv adversary D - idealProbability sim iv adversary counted D|

/-- Whole-view bound certificate for a simulator. The actual pinned simulator
has a proved certificate, not an external distinguishing assumption. -/
structure PublicCompressionModeBound (Q : Nat) (Seed State : Type) [Fintype Seed]
    (sim : Simulator Q Seed State) (iv : Digest32) : Prop where
  distinguishing : ∀ (AdvCoins Result : Type) [Fintype AdvCoins]
    (adversary : AdvCoins → Program Result) (counted : ∀ a, Counts Q (adversary a))
    (D : View Result → Bool),
    ModeAdv sim iv adversary counted D ≤ duplexModeLoss Q

/-- An explicit full-public-view deterministic-primitive replacement game.
The known-answer theorem below rules out a small loss for any permitted class
containing the elementary local-evaluation observer, including ordinary
efficient classes. This is not a standard computational hash assumption. -/
def ConcretePrimitiveGap (Q : Nat) (iv : Digest32) (loss : ℚ)
    (Allowed : (AdvCoins : Type) → [Fintype AdvCoins] → (Result : Type) →
      (AdvCoins → Program Result) → (View Result → Bool) → Prop) : Prop :=
  ∀ (AdvCoins Result : Type) [Fintype AdvCoins] (adversary : AdvCoins → Program Result)
    (D : View Result → Bool), Allowed AdvCoins Result adversary D →
    (∀ a, Counts Q (adversary a)) →
    |concreteProbability iv adversary D - realProbability iv adversary D| ≤ loss

/-- One public primitive call, with no construction queries or hidden work. -/
def knownAnswerAdversary (input : Node) : Unit → Program Digest32 :=
  fun _ => .ask (.primitive .direct input) .done

/-- The observer can evaluate the same public deterministic implementation
locally. Resource bounds on oracle calls do not exclude this distinguisher. -/
def knownAnswerDistinguisher (input : Node) (view : View Digest32) : Bool :=
  decide (view.result = blake2sOracle input)

theorem knownAnswer_counted (input : Node) (Q : Nat) (budget : 1 ≤ Q) :
    ∀ coins, Counts Q (knownAnswerAdversary input coins) := by
  intro coins
  exact ⟨budget, fun _ => trivial⟩

theorem knownAnswer_concreteProbability (iv : Digest32) (input : Node) :
    concreteProbability iv (knownAnswerAdversary input) (knownAnswerDistinguisher input) = 1 := by
  unfold concreteProbability
  rw [distinguish_average (inferInstance : Fintype Unit)]
  simp [knownAnswerAdversary, knownAnswerDistinguisher, runReal, realAnswer, prepend,
    average]

theorem knownAnswer_realProbability (iv : Digest32) (input : Node) :
    realProbability iv (knownAnswerAdversary input) (knownAnswerDistinguisher input) =
      1 / (2^256 : ℚ) := by
  classical
  unfold realProbability
  rw [distinguish_average (inferInstance : Fintype (PrimitiveOracle × Unit))]
  simp only [knownAnswerAdversary, knownAnswerDistinguisher, runReal, realAnswer, prepend,
    decide_eq_true_eq]
  have product (f : PrimitiveOracle → ℚ) :
      average (fun coins : PrimitiveOracle × Unit => f coins.1) = average f := by
    simp [average, Fintype.sum_prod_type, Fintype.card_prod]
  rw [product (fun oracle => if oracle input = blake2sOracle input then 1 else 0)]
  rw [fresh_coordinate input
    (fun (_ : {j : Node // j ≠ input} → Digest32) d =>
      if d = blake2sOracle input then (1 : ℚ) else 0)]
  simp [average]
  norm_num

/-- The exact public-oracle replacement premise forces an essentially unit
loss whenever its permitted class includes the elementary known-answer
observer. This is an unconditional finite-game fact, not a hash conjecture. -/
theorem concretePrimitiveGap_knownAnswer_lower_bound (Q : Nat) (iv : Digest32)
    (input : Node) (loss : ℚ)
    (Allowed : (AdvCoins : Type) → [Fintype AdvCoins] → (Result : Type) →
      (AdvCoins → Program Result) → (View Result → Bool) → Prop)
    (gap : ConcretePrimitiveGap Q iv loss Allowed) (budget : 1 ≤ Q)
    (permitted : Allowed Unit Digest32 (knownAnswerAdversary input)
      (knownAnswerDistinguisher input)) :
    1 - 1 / (2^256 : ℚ) ≤ loss := by
  have h := gap Unit Digest32 (knownAnswerAdversary input)
    (knownAnswerDistinguisher input) permitted (knownAnswer_counted input Q budget)
  rw [knownAnswer_concreteProbability, knownAnswer_realProbability] at h
  exact (le_abs_self _).trans h

/-- The structural prerequisites and executable construction equation are
checked facts, never fields in either external cryptographic assumption. -/
theorem pinned_mode_structure : DMVConditions := dmv_conditions

theorem real_construction_refines (oracle : PrimitiveOracle) (iv : Digest32)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q) :
    realAnswer oracle iv (.construction q valid) = evalPlan (compressionOf oracle) iv (DuplexEncoding.plan q) :=
  (plan_evaluate (compressionOf oracle) iv q).symm

/-- Literal bounded raw-key encoding is injective on the exact checked
coordinate domain; no codec/framing bridge is an external assumption. -/
theorem constructionKey_injective (Q : Nat) (iv : Digest32)
    {a b : Coordinate} (ha : DuplexEncoding.Admissible a) (hb : DuplexEncoding.Admissible b)
    (ca : pathCost a ≤ Q) (cb : pathCost b ≤ Q)
    (same : constructionKey Q iv a ca = constructionKey Q iv b cb) : a = b := by
  apply modeKey_injective iv ha hb
  have h := congrArg expandKey same
  simpa only [expand_constructionKey] using h

/-- Any event of the full interaction view transfers. This theorem contains
no PCS relation and cannot supply or replace a caller's Counts certificate. -/
theorem randomCompression_transfer {Q : Nat} {Seed State AdvCoins Result : Type}
    [Fintype Seed] [Fintype AdvCoins] (sim : Simulator Q Seed State) (iv : Digest32)
    (security : PublicCompressionModeBound Q Seed State sim iv)
    (adversary : AdvCoins → Program Result) (counted : ∀ a, Counts Q (adversary a))
    (D : View Result → Bool) {bound : ℚ}
    (ideal : idealProbability sim iv adversary counted D ≤ bound) :
    realProbability iv adversary D ≤ bound + duplexModeLoss Q := by
  have h := (abs_le.mp (security.distinguishing AdvCoins Result adversary counted D)).2
  linarith

/-- The optional concrete-hash modeling gap is a separate public-primitive
game assumption and additive term, not part of the ideal mode coupling. -/
theorem concrete_transfer {Q : Nat} {Seed State AdvCoins Result : Type}
    [Fintype Seed] [Fintype AdvCoins] (sim : Simulator Q Seed State) (iv : Digest32)
    (security : PublicCompressionModeBound Q Seed State sim iv)
    (Allowed : (Coins : Type) → [Fintype Coins] → (Output : Type) →
      (Coins → Program Output) → (View Output → Bool) → Prop)
    {primitiveLoss bound : ℚ} (primitive : ConcretePrimitiveGap Q iv primitiveLoss Allowed)
    (adversary : AdvCoins → Program Result) (counted : ∀ a, Counts Q (adversary a))
    (D : View Result → Bool) (permitted : Allowed AdvCoins Result adversary D)
    (ideal : idealProbability sim iv adversary counted D ≤ bound) :
    concreteProbability iv adversary D ≤ bound + duplexModeLoss Q + primitiveLoss := by
  have hp := (abs_le.mp (primitive AdvCoins Result adversary D permitted counted)).2
  have hm := randomCompression_transfer sim iv security adversary counted D ideal
  linarith

/-- Force a construction's boxed instruction fold once at the data-valued
execution boundary. Merely returning a Digest32 from realAnswer permits the
compiler to defer the entire construction until each individual byte lookup. -/
def runRealStored {Result : Type} (oracle : PrimitiveOracle) (iv : Digest32) :
    Program Result → Execution Result
  | .done r => ⟨⟨[],r⟩,0,0,0⟩
  | .ask (.primitive purpose input) next =>
    let answer := oracle input
    prepend (.primitive purpose input) answer 0 (runRealStored oracle iv (next answer))
  | .ask (.construction q valid) next =>
    DuplexFraming.withCoordinate (compressionOf oracle) iv q fun answer =>
      prepend (.construction q valid) answer 0 (runRealStored oracle iv (next answer))

@[csimp] theorem runReal_stored : @runReal = @runRealStored := by
  funext Result oracle iv program
  induction program with
  | done r => rfl
  | ask q next ih =>
    cases q <;> simp only [runReal,runRealStored,realAnswer,
      DuplexFraming.withCoordinate_eq,ih]

end Whir.DuplexModeGame
