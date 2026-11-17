module

public import Common.PiOnly
public import Quantum.Qrom.SufCma.Classical
public import Quantum.SufCma.Classical
public import Quantum.Xmss.Keccak

@[expose] public section

/-!
# Oracle worlds: the standard model, the QROM and the QRPM at a fixed table

The standard-model reduction is stated relative to a fixed oracle table: the adversary and every
reduction have the same quantum access to it, and the schemes hash through it classically. An
`OracleWorld` packages one such setting:

* `Tab`: the tables (a function `HashDomain → HashOutput`, a permutation of the sponge state, or
  one fixed function);
* `spec`, `runtime tab`: the adversary's hash ports and their runtime at the table `tab`;
* `prim`, `impl`, `eager tab`: the schemes' classical primitive queries (beside coins), their
  classical calls of the ports, and their answers at `tab` (`classicalOn_impl`);
* `hash`, `hashOf tab`: Keccak-256 as the schemes call it, and its value at `tab`
  (`simulateQ_hash`).

Worlds: `romWorld` (QROM), `rpmWorld S e` (QRPM), `funWorld S e f` (one fixed state function
`f`, with the adversary's port the oracle of `f`), and `keccakWorld := funWorld … keccakF1600`,
the standard model, where `hashOf` is the statement's Keccak-256 (`keccakWorld_hashOf`).

Generic adversaries (`advSpec spec R`) have the hash ports of `spec` and classical ports `.call q`
answered in `R.Range q`. The SUF-CMA game over a world (`game`, `winProbAt`, `winProb`) copies
`Quantum.Qrom.SufCma.Game` with the signing ports as classical ports. Probabilities over a world
are uniform averages over its tables of fixed-table probabilities (`probAvg_eq_sum`,
`winProb_eq_sum`).

## Main statements

* `winProb_qrom_eq`, `winProb_qrpm_eq`: the existing QROM and QRPM winning probabilities are the
  world winning probabilities of the relabelled adversaries (`ofQrom`, `ofQrpm`), hence the
  averages over the fixed tables of the fixed-table winning probabilities
  (`winProb_qrom_eq_avg`, `winProb_qrpm_eq_avg`); the relabelling keeps every port charge
  (`isChargeBound_ofQrom`, `isChargeBound_ofQrpm`).
* `keccakWorld_hashOf_eq_keccak256`: the standard-model hash is the statement's `keccak256`.
* `probAt_toQuantumAt`: a classical program run by classical calls wins at a fixed table with the
  probability of the classical program answered by the table.
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal

universe u v w w₁

namespace Quantum.StdModel

open Common HashSig HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (absorbWith absorbBlockWith)

/-! ## Worlds -/

/-- **An oracle world**: tables, the adversary's hash ports and their runtime at each table, and
the schemes' classical oracles (coins and `prim`), with their classical calls of the ports, their
answers at each table, and Keccak-256 over them. -/
structure OracleWorld where
  /-- The oracle tables. -/
  Tab : Type
  [instFintypeTab : Fintype Tab]
  [instNonemptyTab : Nonempty Tab]
  /-- The queries of the schemes' classical primitive. -/
  Prim : Type
  /-- The schemes' classical primitive. -/
  prim : OracleSpec.{0, 0} Prim
  /-- The adversary's hash ports. -/
  spec : QuantumOracleSpec.{0, 0}
  /-- The ports at a fixed table. -/
  runtime : Tab → QuantumRuntime spec
  /-- Coins and primitive queries by classical calls of the ports beside a held register. -/
  impl : (B : QReg) → QueryImpl (unifSpec + prim) (QComp spec B B)
  /-- The port calls of a classical query. -/
  cost : (unifSpec + prim).Domain → ℕ
  isTotalQueryBound_impl : ∀ B t, (impl B t).IsTotalQueryBound (cost t)
  /-- Coins and primitive queries answered by a fixed table. -/
  eager : Tab → QueryImpl (unifSpec + prim) ProbComp
  trace_init : ∀ tab, ((runtime tab).init.matrix.trace.re) = 1
  /-- At a fixed table, the classical calls run as the table answers them. -/
  classicalOn_impl : ∀ tab B t, ClassicalOn (runtime tab) (impl B t) (eager tab t) LinearMap.id
  /-- Keccak-256 as the schemes call it. -/
  hash : HashInput → OracleComp (unifSpec + prim) HashOutput
  /-- Keccak-256 at a fixed table. -/
  hashOf : Tab → HashInput → HashOutput
  simulateQ_hash : ∀ tab l, simulateQ (eager tab) (hash l) = pure (hashOf tab l)

namespace OracleWorld

attribute [instance] OracleWorld.instFintypeTab OracleWorld.instNonemptyTab

variable (W : OracleWorld)

/-- The schemes' classical oracles: coins and the primitive. -/
abbrev Oracles := unifSpec + W.prim

/-- **The probability at the table `tab`** that a program on the trivial register returns `true`. -/
noncomputable def probAt (tab : W.Tab) (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) :
    ℝ≥0∞ :=
  (W.runtime tab).evalDistMap .instruments x (SubState.basis ()) (fun p ↦ p.2.2) {true}

/-- **The probability over a uniform table** that a program on the trivial register returns
`true`. -/
noncomputable def probAvg (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) : ℝ≥0∞ :=
  sampledEvalDistMap W.runtime .instruments x (SubState.basis ()) (fun _ p ↦ p.2.2) {true}

/-- **The probability over a uniform table is the average of the fixed-table probabilities.** -/
theorem probAvg_eq_sum (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) :
    W.probAvg x = ∑ tab, (Fintype.card W.Tab : ℝ≥0∞)⁻¹ * W.probAt tab x :=
  sampledEvalDistMap_apply _ _ _ _ _ (measurableSet_singleton true)

/-- At a fixed table, a classical algorithm run by classical calls runs as the algorithm answered
by the table. -/
theorem classicalOn_toQuantumAt (tab : W.Tab) (B : QReg) {α : Type}
    (oa : OracleComp W.Oracles α) :
    ClassicalOn (W.runtime tab) (oa.toQuantumAt (W.impl B)) (simulateQ (W.eager tab) oa)
      LinearMap.id :=
  Quantum.classicalOn_toQuantumAt (W.classicalOn_impl tab B) oa

/-- **A classical program at a fixed table**: run by classical calls on the trivial register, it
returns `true` with the probability that the program answered by the table does. -/
theorem probAt_toQuantumAt (tab : W.Tab) (oa : OracleComp W.Oracles Bool) :
    W.probAt tab (oa.toQuantumAt (W.impl _)) =
      Pr{let z ← simulateQ (W.eager tab) oa}[z = true] := by
  have h : (W.runtime tab).evalDistMap .instruments (oa.toQuantumAt (W.impl _))
      (SubState.basis () : SubState (QReg.of Unit)) (fun p ↦ p.2.2) =
        𝒟[simulateQ (W.eager tab) oa] := by
    refine (QuantumRuntime.evalDist₂_map_eq_evalDistMap _ _ id _ _).symm.trans ?_
    rw [QuantumRuntime.evalDist₂, ((W.classicalOn_toQuantumAt tab _ oa).map id).outcomeMeasure,
      SubState.trace_re_prod, W.trace_init, mul_one, SubState.matrix_basis,
      Matrix.trace_single_eq_same, Complex.one_re, ENNReal.ofReal_one, one_smul, id_map]
  rw [probAt, h, prEvent_eq_evalDist_singleton]

/-- Keccak-256 run by classical calls at a fixed table returns its value at the table. -/
theorem classicalOn_hash (tab : W.Tab) (B : QReg) (l : HashInput) :
    ClassicalOn (W.runtime tab) ((W.hash l).toQuantumAt (W.impl B)) (pure (W.hashOf tab l))
      LinearMap.id :=
  (W.classicalOn_toQuantumAt tab B (W.hash l)).congr (W.simulateQ_hash tab l) rfl

end OracleWorld

/-! ## The worlds -/

open Quantum.Qrom in
/-- **The QROM world**: tables the functions `H : HashDomain → HashOutput`, the adversary's port
the oracle of `H`, the schemes hashing by `hashQ`. -/
noncomputable def romWorld : OracleWorld where
  Tab := HashDomain → HashOutput
  Prim := HashDomain
  prim := HashDomain →ₒ HashOutput
  spec := romSpec
  runtime := additiveOracleRuntime
  impl := SufCma.romImpl
  cost := hashCallCost
  isTotalQueryBound_impl := SufCma.isTotalQueryBound_romImpl
  eager := eagerFunOracles
  trace_init := trace_re_additiveOracleRuntime_init
  classicalOn_impl H B t := by
    rw [SufCma.romImpl_eq_funImpl]
    exact classicalOn_funImpl B H t
  hash := hashQ
  hashOf H l := (encodeInput l).elim 0 H
  simulateQ_hash H l := by
    rcases h : encodeInput l with _ | x
    · simp [hashQ, h]
    · simp [hashQ, h, eagerFunOracles]

section Rpm

variable (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S] (e : KeccakState ≃ S)

/-- **The QRPM world** over the state type `S` with `e : KeccakState ≃ S`: tables the
permutations `φ` of `S`, the adversary's ports `φ` and `φ⁻¹`, the schemes hashing by Keccak-256
over `π = e⁻¹ φ e`. -/
noncomputable def rpmWorld : OracleWorld where
  Tab := Equiv.Perm S
  Prim := PermutationQuery KeccakState
  prim := permutationOracleSpec KeccakState
  spec := qrpmSpec S
  runtime := permutationRuntime
  impl := SufCma.permImpl e
  cost := permutationCallCost
  isTotalQueryBound_impl := SufCma.isTotalQueryBound_permImpl e
  eager φ := eagerPermOracles (e.symm.permCongr φ)
  trace_init := trace_re_permutationRuntime_init
  classicalOn_impl φ B t := by
    rw [SufCma.permImpl_eq_qrpmImpl]
    exact classicalOn_qrpmImpl e B φ t
  hash := keccakHash queryPermutation
  hashOf φ l := Id.run (keccakHash (fun s ↦ (pure (e.symm.permCongr φ s) : Id KeccakState)) l)
  simulateQ_hash φ l := (Xmss.simulateQ_keccakHash _ (e.symm.permCongr φ) (fun _ ↦ rfl) l).trans
    (congrArg pure (Xmss.keccakHash_eq_spongeHash (e.symm.permCongr φ) l).symm)

end Rpm

section Fun

/-- Absorbing with a function in a lawful monad returns the absorption in `Id`. -/
theorem absorbWith_pureFn {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : KeccakState → KeccakState) :
    ∀ (n : ℕ) (s : KeccakState) (data : List UInt8),
      absorbWith (m := m) (fun s ↦ pure (f s)) n s data =
        pure (absorbWith (m := Id) (fun s ↦ pure (f s)) n s data)
  | 0, _, _ => rfl
  | n + 1, s, data => by
    simp only [absorbWith, absorbBlockWith, pure_bind]
    exact absorbWith_pureFn f n _ _

/-- Keccak-256 over a function in a lawful monad returns its value in `Id`. -/
theorem keccakHash_pureFn {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : KeccakState → KeccakState) (l : HashInput) :
    keccakHash (fun s ↦ (pure (f s) : m KeccakState)) l =
      pure (Id.run (keccakHash (fun s ↦ (pure (f s) : Id KeccakState)) l)) := by
  simp only [keccakHash, LeanVM.Protocol.KeccakHash.keccak256With]
  rw [absorbWith_pureFn]
  simp only [pure_bind, map_pure]
  rfl

variable (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S] (e : KeccakState ≃ S)

/-- A call of the oracle of a function of `S` costs one, a coin nothing. -/
def funCallCost : (unifSpec + (S →ₒ S)).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- One state function `f` by a query of its transport to `S`. -/
def queryFn (s : KeccakState) : OracleComp (unifSpec + (S →ₒ S)) KeccakState :=
  e.symm <$> liftM ((unifSpec + (S →ₒ S)).query (.inr (e s)))

/-- **The world of one state function `f`**: a single table, the adversary's port the oracle of
`f` transported to `S`, the schemes hashing by Keccak-256 over `f`. -/
noncomputable def funWorld (f : KeccakState → KeccakState) : OracleWorld where
  Tab := Unit
  Prim := S
  prim := S →ₒ S
  spec := qromSpec S S
  runtime _ := additiveOracleRuntime fun x ↦ e (f (e.symm x))
  impl := Qrom.funImpl
  cost := funCallCost S
  isTotalQueryBound_impl B t := by
    rcases t with n | x
    · exact SufCma.isTotalQueryBound_act _ _
    · exact SufCma.isTotalQueryBound_callBasis _ _ _ _
  eager _ := Qrom.eagerFunOracles fun x ↦ e (f (e.symm x))
  trace_init _ := trace_re_additiveOracleRuntime_init _
  classicalOn_impl _ B t := Qrom.classicalOn_funImpl B _ t
  hash := keccakHash (queryFn S e)
  hashOf _ l := Id.run (keccakHash (fun s ↦ (pure (f s) : Id KeccakState)) l)
  simulateQ_hash _ l := by
    have hq : (fun s ↦ simulateQ (Qrom.eagerFunOracles fun x ↦ e (f (e.symm x)))
        (queryFn S e s)) = fun s ↦ (pure (f s) : ProbComp KeccakState) := by
      funext s
      simp [queryFn, Qrom.eagerFunOracles]
    simp only [keccakHash, simulateQ_map, simulateQ_keccak256With, hq]
    exact keccakHash_pureFn f l

end Fun

/-- **The standard-model world**: the single table Keccak-f[1600], the adversary's port its oracle
on the sponge state `X × Z`. -/
noncomputable def keccakWorld : OracleWorld :=
  funWorld (Xmss.X × Xmss.Z) Xmss.keccakStateEquiv LeanVM.Semantics.keccakF1600

/-- **The standard-model hash is the statement's Keccak-256**, read as `keccakHash` reads its
digest. -/
theorem keccakWorld_hashOf (l : HashInput) :
    keccakWorld.hashOf () l =
      Id.run (keccakHash (fun s ↦ (pure (LeanVM.Semantics.keccakF1600 s) : Id KeccakState)) l) :=
  rfl

/-- **The standard-model hash is the statement's `keccak256`**, its 32 digest bytes read as a
little-endian number as `keccakHash` reads them. -/
theorem keccakWorld_hashOf_eq_keccak256 (l : HashInput) :
    keccakWorld.hashOf () l = BitVec.ofNat 256
      ((LeanVM.Protocol.KeccakHash.digestBytes (LeanVM.Protocol.KeccakHash.keccak256 l)).foldr
        (fun b acc ↦ b.toNat + 256 * acc) 0) :=
  rfl

/-! ## Generic adversaries -/

/-- The ports of a generic adversary: a hash port `p`, or a classical port `q`. -/
inductive Port (P Q : Type) where
  /-- The hash port `p`. -/
  | hash (p : P)
  /-- The classical port `q`. -/
  | call (q : Q)

/-- **A generic adversary's signature**: the hash ports of `spec`, and one classical port per
query `q : Q`, on no register, reporting `R.Range q`. -/
@[reducible]
def advSpec (spec : QuantumOracleSpec.{0, 0}) {Q : Type} (R : OracleSpec.{0, 0} Q) :
    QuantumOracleSpec.{0, 0} where
  Port := Port spec.Port Q
  In
    | .hash p => spec.In p
    | .call _ => QReg.of Unit
  Out
    | .hash p => spec.Out p
    | .call _ => QReg.of Unit
  Result
    | .hash p => spec.Result p
    | .call q => R.Range q

/-- A hash call costs one, a classical call nothing. -/
def hashCharge {P Q : Type} : Port P Q → ℕ
  | .hash _ => 1
  | .call _ => 0

/-- A classical call costs one, a hash call nothing. -/
def callCharge {P Q : Type} : Port P Q → ℕ
  | .hash _ => 0
  | .call _ => 1

variable {spec : QuantumOracleSpec.{0, 0}} {Q : Type} {R : OracleSpec.{0, 0} Q}

/-- A charge on ports as a charge on commands: a call of port `i` costs `c i`, a local operation
nothing. -/
def cmdCharge {L : LocalSig.{u, v}} (c : Port spec.Port Q → ℕ) (A : QReg) :
    QuantumComp.Cmd L (advSpec spec R) A → ℕ
  | .prim _ => 0
  | .query i _ _ => c i

/-! ## The classical transcript -/

/-- The transcript after a command answered `b`: a classical call appends itself and its
answer. -/
def logAfter {L : LocalSig.{u, v}} {A : QReg} :
    (c : QuantumComp.Cmd L (advSpec spec R) A) → c.Resp → QueryLog R → QueryLog R
  | .query (.call q) _ _, b, log => log ++ [⟨q, b.down⟩]
  | _, _, log => log

/-- Run a program and keep its classical transcript, starting from `log`: the same commands, the
transcript handed to the leaf map `leaf` at the end. -/
def logCalls {L : LocalSig.{u, v}} {X : QReg → Type w} {Y : QReg → Type w₁}
    (leaf : ∀ u, X u → QueryLog R → Y u) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (advSpec spec R)) X A →
      QueryLog R → IFreeM (QuantumComp.toIPFunctor L (advSpec spec R)) Y A
  | _, .pure x, log => .pure (leaf _ x log)
  | _, .liftBind c next, log => .liftBind c fun b ↦ logCalls leaf (next b) (logAfter c b log)

/-- **The program with its classical transcript**. -/
def withCallLog {L : LocalSig.{u, v}} {A B : QReg} {α : Type w}
    (x : QuantumComp₂ L (advSpec spec R) A B α) :
    QuantumComp₂ L (advSpec spec R) A B (α × QueryLog R) :=
  logCalls (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x []

/-- Keeping the transcript keeps every roll bound. -/
theorem isRollBound_logCalls {L : LocalSig.{u, v}} {X : QReg → Type w} {Y : QReg → Type w₁}
    {β : Type*} {canRoll : (A : QReg) → QuantumComp.Cmd L (advSpec spec R) A → β → Prop}
    {cost : (A : QReg) → QuantumComp.Cmd L (advSpec spec R) A → β → β}
    (leaf : ∀ u, X u → QueryLog R → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L (advSpec spec R)) X A) (log : QueryLog R)
    {b : β} (hx : IFreeM.IsRollBound x b canRoll cost) :
    IFreeM.IsRollBound (logCalls leaf x log) b canRoll cost := by
  induction x using IFreeM.inductionOn generalizing log b with
  | pure _ _ => trivial
  | liftBind _ c next ih => exact ⟨hx.1, fun r ↦ ih r _ (hx.2 r)⟩

/-- Keeping the transcript keeps losslessness. -/
theorem lossless_withCallLog {A B : QReg} {α : Type} {x : QComp (advSpec spec R) A B α}
    (hx : x.Lossless .instruments) : (withCallLog x).Lossless .instruments :=
  isRollBound_logCalls _ x [] hx

/-- Keeping the transcript keeps every charge bound. -/
theorem isChargeBound_withCallLog {A B : QReg} {α : Type} {x : QComp (advSpec spec R) A B α}
    {c : Port spec.Port Q → ℕ} {n : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge c) n) :
    IFreeM.IsChargeBound (withCallLog x) (cmdCharge c) n :=
  isRollBound_logCalls _ x [] hx

/-! ## The SUF-CMA game over a world -/

section Game

variable (W : OracleWorld) (PK Req Resp F : Type)

/-- A quantum SUF-CMA adversary over the world `W`: the hash ports of `W` and one classical
signing port per request. -/
abbrev SufAdversary :=
  PK → QComp (advSpec W.spec (Req →ₒ Resp)) (QReg.of Unit) (QReg.of Unit) F

variable {PK Req Resp F} {Seed SK : Type} (sch : Qrom.SchemeOver W.Oracles Seed PK SK Req Resp F)

/-- The answer to the signing request `r` with the adversary's register `A ≃ Unit × E` held:
relabel the register, then run the signer by classical calls. -/
noncomputable def signTree (sk : SK) (r : Req) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec W.spec (Req →ₒ Resp)).In (.call r) × E) :
    QComp W.spec A (QReg.of ((advSpec W.spec (Req →ₒ Resp)).Out (.call r) × E)) Resp :=
  (QComp.act (B := QReg.of ((advSpec W.spec (Req →ₒ Resp)).Out (.call r) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ (sch.sign sk r).toQuantumAt (W.impl _)

/-- **The challenger**: a local operation stays, a hash call becomes the same call of `W.spec`,
and a signing request is answered by the signer. -/
noncomputable def challenge (sk : SK) :
    CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec (Req →ₒ Resp)))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} W.spec)
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query (.hash p) E ℓ =>
      QuantumComp.queryBind (spec := W.spec) p E ℓ fun r ↦ QuantumComp.pure ⟨ULift.up r, rfl⟩
  | _, .query (.call r) E ℓ =>
      QuantumComp.bind (signTree W sch sk r E ℓ) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's program with the challenger substituted. -/
noncomputable def challenged (sk : SK) {A B : QReg} {α : Type}
    (x : QComp (advSpec W.spec (Req →ₒ Resp)) A B α) : QComp W.spec A B α :=
  IFreeM.substitute (challenge W sch sk) x

/-- **The SUF-CMA game over `W`** at the seed `S0`: key generation, the adversary against the
challenger with its signing transcript, the verification of its forgery, and the winning
condition. -/
noncomputable def game (S0 : Seed) (A : SufAdversary W PK Req Resp F) :
    QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool :=
  ((sch.generateKeys S0).toQuantumAt (W.impl _)).bind fun keys ↦
    (challenged W sch keys.2 (withCallLog (A keys.1))).bind fun run ↦
      ((sch.verify keys.1 run.1).toQuantumAt (W.impl _)).bind fun verified ↦
        QuantumComp₂.pure (sch.winningCondition run.2 run.1 && verified)

/-- **The winning probability at the table `tab`**, averaged over the scheme's seed law. -/
noncomputable def winProbAt [Fintype Seed] (tab : W.Tab) (A : SufAdversary W PK Req Resp F) :
    ℝ≥0∞ :=
  ∑ S0 : Seed, Pr{let s ← sch.sampleSeed}[s = S0] * W.probAt tab (game W sch S0 A)

/-- **The winning probability over a uniform table**, averaged over the scheme's seed law. -/
noncomputable def winProb [Fintype Seed] (A : SufAdversary W PK Req Resp F) : ℝ≥0∞ :=
  ∑ S0 : Seed, Pr{let s ← sch.sampleSeed}[s = S0] * W.probAvg (game W sch S0 A)

/-- **The winning probability is the average over the tables** of the fixed-table winning
probabilities. -/
theorem winProb_eq_sum [Fintype Seed] (A : SufAdversary W PK Req Resp F) :
    winProb W sch A = ∑ tab, (Fintype.card W.Tab : ℝ≥0∞)⁻¹ * winProbAt W sch tab A := by
  simp only [winProb, winProbAt, OracleWorld.probAvg_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

end Game

/-! ## The QROM game as a game over `romWorld` -/

section Qrom

variable {PK Req Resp F : Type}

/-- The QROM adversary's ports as generic ports. -/
def qromPort : Qrom.SufCma.AdvPort Req → Port Unit Req
  | .hash => .hash ()
  | .sign r => .call r

/-- The QROM adversary's commands relabelled as the generic commands over `romWorld`. -/
noncomputable def qromLens :
    Lens (QuantumComp.toIPFunctor LocalSig.instruments.{0} (Qrom.SufCma.advSpec Req Resp))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec (Req →ₒ Resp)))
    where
  toFunA _
    | .prim o => .prim o
    | .query .hash E ℓ => .query (.hash ()) E ℓ
    | .query (.sign r) E ℓ => .query (.call r) E ℓ
  toFunB _ c := by rcases c with o | ⟨_ | r, E, ℓ⟩ <;> exact id
  src_eq _ c _ := by rcases c with o | ⟨_ | r, E, ℓ⟩ <;> rfl

/-- **A QROM adversary as an adversary over `romWorld`**: the same program, ports relabelled. -/
noncomputable def ofQrom (A : Qrom.SufCma.Adversary PK Req Resp F) :
    SufAdversary romWorld PK Req Resp F :=
  fun pk ↦ IFreeM.mapLens qromLens (A pk)

/-- **The relabelled QROM adversary keeps every charge.** -/
theorem isChargeBound_ofQrom (A : Qrom.SufCma.Adversary PK Req Resp F)
    (c : Port Unit Req → ℕ) (pk : PK) {n : ℕ}
    (h : IFreeM.IsChargeBound (A pk) (Qrom.SufCma.cmdCharge (c ∘ qromPort)) n) :
    IFreeM.IsChargeBound (ofQrom A pk) (cmdCharge c) n := by
  refine IFreeM.IsChargeBound.mapLens qromLens ?_
  have he : (fun s a ↦ cmdCharge (L := LocalSig.instruments.{0}) c s (qromLens.toFunA s a)) =
      Qrom.SufCma.cmdCharge (Req := Req) (Resp := Resp) (c ∘ qromPort) := by
    funext s a
    rcases a with o | ⟨_ | r, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

theorem hashCharge_comp_qromPort : hashCharge ∘ qromPort (Req := Req) = Qrom.SufCma.hashCharge :=
  funext fun i ↦ by cases i <;> rfl

theorem callCharge_comp_qromPort : callCharge ∘ qromPort (Req := Req) = Qrom.SufCma.signCharge :=
  funext fun i ↦ by cases i <;> rfl

variable {Seed SK : Type} (sch : Qrom.SchemeOver Qrom.RomOracles Seed PK SK Req Resp F)

/-- The QROM challenger on a program with its signing transcript is the world's challenger on
the relabelled program with its transcript. -/
theorem substitute_logSigns_ofQrom (sk : SK) {X : QReg → Type} {Y : QReg → Type}
    (leaf : ∀ u, X u → QueryLog (Req →ₒ Resp) → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (Qrom.SufCma.advSpec Req Resp)) X A) (log : QueryLog (Req →ₒ Resp)) :
    IFreeM.substitute (Qrom.SufCma.challenge sch sk) (Qrom.SufCma.logSigns leaf x log) =
      IFreeM.substitute (challenge romWorld sch sk)
        (logCalls leaf (IFreeM.mapLens qromLens x) log) := by
  induction x using IFreeM.inductionOn generalizing log with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨_ | r, E, ℓ⟩ <;>
    · refine congrArg (IFreeM.bind _) (funext fun u ↦ funext fun ans ↦ ?_)
      obtain ⟨b, h⟩ := ans
      cases h
      exact ih b _

/-- **The QROM game is the game over `romWorld`** of the relabelled adversary. -/
theorem game_ofQrom (S0 : Seed) (A : Qrom.SufCma.Adversary PK Req Resp F) :
    Qrom.SufCma.game sch S0 A = game romWorld sch S0 (ofQrom A) := by
  refine congrArg (QuantumComp₂.bind _) (funext fun keys ↦ ?_)
  exact congrArg (fun y ↦ QuantumComp₂.bind y _)
    (substitute_logSigns_ofQrom sch keys.2 _ (A keys.1) [])

/-- **The QROM winning probability is the winning probability over `romWorld`**, hence the
average over the functions `H` of the winning probabilities at `H` (`winProb_eq_sum`). -/
theorem winProb_qrom_eq [Fintype Seed] (A : Qrom.SufCma.Adversary PK Req Resp F) :
    Qrom.SufCma.winProb sch A = winProb romWorld sch (ofQrom A) :=
  Finset.sum_congr rfl fun S0 _ ↦ by
    rw [game_ofQrom]
    rfl

/-- **The QROM winning probability is the average over the functions `H`** of the winning
probabilities at the fixed table `H`. -/
theorem winProb_qrom_eq_avg [Fintype Seed] (A : Qrom.SufCma.Adversary PK Req Resp F) :
    Qrom.SufCma.winProb sch A = ∑ H, (Fintype.card romWorld.Tab : ℝ≥0∞)⁻¹ *
      winProbAt romWorld sch H (ofQrom A) :=
  (winProb_qrom_eq sch A).trans (winProb_eq_sum romWorld sch (ofQrom A))

end Qrom

/-! ## The QRPM game as a game over `rpmWorld` -/

section Qrpm

variable {PK Req Resp F : Type} {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
  (e : KeccakState ≃ S)

/-- The QRPM adversary's ports as generic ports. -/
def qrpmPort : SufCma.AdvPort Req → Port PermutationPort Req
  | .perm p => .hash p
  | .sign r => .call r

/-- The QRPM adversary's commands relabelled as the generic commands over `rpmWorld`. -/
noncomputable def qrpmLens :
    Lens (QuantumComp.toIPFunctor LocalSig.instruments.{0} (SufCma.advSpec Req Resp S))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0}
        (advSpec (rpmWorld S e).spec (Req →ₒ Resp)))
    where
  toFunA _
    | .prim o => .prim o
    | .query (.perm p) E ℓ => .query (.hash p) E ℓ
    | .query (.sign r) E ℓ => .query (.call r) E ℓ
  toFunB _ c := by rcases c with o | ⟨p | r, E, ℓ⟩ <;> exact id
  src_eq _ c _ := by rcases c with o | ⟨p | r, E, ℓ⟩ <;> rfl

/-- **A QRPM adversary as an adversary over `rpmWorld`**: the same program, ports relabelled. -/
noncomputable def ofQrpm (A : SufCma.Adversary PK Req Resp F S) :
    SufAdversary (rpmWorld S e) PK Req Resp F :=
  fun pk ↦ IFreeM.mapLens (qrpmLens e) (A pk)

/-- **The relabelled QRPM adversary keeps every charge.** -/
theorem isChargeBound_ofQrpm (A : SufCma.Adversary PK Req Resp F S)
    (c : Port PermutationPort Req → ℕ) (pk : PK) {n : ℕ}
    (h : IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge (c ∘ qrpmPort)) n) :
    IFreeM.IsChargeBound (ofQrpm e A pk) (cmdCharge c) n := by
  refine IFreeM.IsChargeBound.mapLens (qrpmLens e) ?_
  have he : (fun s a ↦ cmdCharge (L := LocalSig.instruments.{0}) c s ((qrpmLens e).toFunA s a)) =
      SufCma.cmdCharge (Req := Req) (Resp := Resp) (S := S) (c ∘ qrpmPort) := by
    funext s a
    rcases a with o | ⟨p | r, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

theorem hashCharge_comp_qrpmPort : hashCharge ∘ qrpmPort (Req := Req) = SufCma.permCharge :=
  funext fun i ↦ by cases i <;> rfl

theorem callCharge_comp_qrpmPort : callCharge ∘ qrpmPort (Req := Req) = SufCma.signCharge :=
  funext fun i ↦ by cases i <;> rfl

variable {Seed SK : Type} (sch : Common.SufCma.Scheme Seed PK SK Req Resp F)

/-- The QRPM challenger on a program with its signing transcript is the world's challenger on
the relabelled program with its transcript. -/
theorem substitute_logSigns_ofQrpm (sk : SK) {X : QReg → Type} {Y : QReg → Type}
    (leaf : ∀ u, X u → QueryLog (Req →ₒ Resp) → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (SufCma.advSpec Req Resp S)) X A) (log : QueryLog (Req →ₒ Resp)) :
    IFreeM.substitute (SufCma.challenge sch e sk) (SufCma.logSigns leaf x log) =
      IFreeM.substitute (challenge (rpmWorld S e) sch.toOver sk)
        (logCalls leaf (IFreeM.mapLens (qrpmLens e) x) log) := by
  induction x using IFreeM.inductionOn generalizing log with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨p | r, E, ℓ⟩ <;>
    · refine congrArg (IFreeM.bind _) (funext fun u ↦ funext fun ans ↦ ?_)
      obtain ⟨b, h⟩ := ans
      cases h
      exact ih b _

/-- **The QRPM game is the game over `rpmWorld`** of the relabelled adversary. -/
theorem game_ofQrpm (S0 : Seed) (A : SufCma.Adversary PK Req Resp F S) :
    SufCma.game sch e S0 A = game (rpmWorld S e) sch.toOver S0 (ofQrpm e A) := by
  refine congrArg (QuantumComp₂.bind _) (funext fun keys ↦ ?_)
  exact congrArg (fun y ↦ QuantumComp₂.bind y _)
    (substitute_logSigns_ofQrpm e sch keys.2 _ (A keys.1) [])

/-- **The QRPM winning probability is the winning probability over `rpmWorld`**, hence the
average over the permutations `φ` of the winning probabilities at `φ` (`winProb_eq_sum`). -/
theorem winProb_qrpm_eq [Fintype Seed] (A : SufCma.Adversary PK Req Resp F S) :
    SufCma.winProb sch e A = winProb (rpmWorld S e) sch.toOver (ofQrpm e A) :=
  Finset.sum_congr rfl fun S0 _ ↦ by
    rw [game_ofQrpm]
    rfl

/-- **The QRPM winning probability is the average over the permutations `φ`** of the winning
probabilities at the fixed permutation `φ`. -/
theorem winProb_qrpm_eq_avg [Fintype Seed] (A : SufCma.Adversary PK Req Resp F S) :
    SufCma.winProb sch e A = ∑ φ, (Fintype.card (rpmWorld S e).Tab : ℝ≥0∞)⁻¹ *
      winProbAt (rpmWorld S e) sch.toOver φ (ofQrpm e A) :=
  (winProb_qrpm_eq e sch A).trans (winProb_eq_sum (rpmWorld S e) sch.toOver (ofQrpm e A))

end Qrpm

end Quantum.StdModel

end
