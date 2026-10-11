import Whir.Concrete

/-! Dense executable replay of the production WHIR opening schedule.
Commitments are ideal immutable row arrays and authentication is exact lookup.
Challenges are an explicit independent input. This is not a hash, Fiat-Shamir,
proof-of-work, succinct verifier, or cryptographic soundness implementation. -/
namespace Whir.Protocol
open Concrete

structure Config where
  logN : Nat
  folds : Array Nat
  rates : Array Nat
  queries : Array Nat
  oodCounts : Array Nat
  deriving Repr, Inhabited

def Config.valid (c : Config) : Bool := Id.run do
  let levels := c.folds.size
  if levels < 2 || c.rates.size != levels || c.queries.size != levels ||
      c.oodCounts.size != levels || c.oodCounts[0]! != 0 then return false
  let mut n := c.logN
  for i in [:levels] do
    if c.folds[i]! == 0 || c.folds[i]! >= n || c.rates[i]! == 0 || c.queries[i]! == 0 then return false
    n := n-c.folds[i]!
    if n+c.rates[i]! >= 64 then return false
  return true

/-- The production query table, not a floating-point soundness derivation. -/
def productionQueries : Array (Array (Array Nat)) := #[
  #[#[222,55], #[223,56,30], #[223,56,31], #[223,56,32], #[223,56,32],
    #[223,56,32,22], #[223,56,32,22], #[224,56,32,23], #[224,56,32,23],
    #[224,56,32,23,17], #[224,56,32,23,17], #[224,56,32,23,18],
    #[225,56,32,23,18], #[225,56,32,23,18,14]],
  #[#[111,45], #[112,45,27], #[112,45,28], #[112,45,28], #[112,45,28],
    #[112,45,28,20], #[112,45,28,20], #[112,45,28,21], #[112,45,28,21],
    #[112,45,28,21,16], #[112,45,28,21,16], #[112,45,28,21,16],
    #[112,45,28,21,16], #[112,45,28,21,16,13]],
  #[#[75,37], #[75,37,24], #[75,37,25], #[75,38,25], #[75,38,25],
    #[75,38,25,18], #[75,38,25,19], #[75,38,25,19], #[75,38,25,19],
    #[75,38,25,19,15], #[75,38,25,19,15], #[75,38,25,19,15],
    #[75,38,25,19,15], #[75,38,25,19,15,13]],
  #[#[56,32], #[56,32,22], #[56,32,22], #[56,32,23], #[56,32,23],
    #[56,32,23,17], #[56,32,23,17], #[56,32,23,18], #[56,32,23,18],
    #[56,32,23,18,14], #[56,32,23,18,14], #[56,32,23,18,14],
    #[56,32,23,18,15], #[56,32,23,18,15,12]]]

/-- Production integer ladder. Grinding is deliberately external to this model. -/
def productionConfig (logN rate : Nat) : Option Config := Id.run do
  if logN < 15 || logN > 28 || rate < 1 || rate > 4 then return none
  let mut n := logN-6
  let mut folds := #[6]
  let mut rates := #[rate]
  let mut currentRate := rate
  for _ in [:logN] do
    if n > 5 then
      let k := min 4 n
      currentRate := currentRate + 3
      folds := folds.push k
      rates := rates.push currentRate
      n := n-k
  return some ⟨logN, folds, rates, productionQueries[rate-1]![logN-15]!,
    tab folds.size (fun i => if i == 0 then 0 else 1)⟩

structure LevelChallenges where
  folds : Array E
  oodPoints : Array (Array E)
  querySqueezes : Array E
  lambda : E
  deriving Repr, Inhabited

structure Challenges where
  levels : Array LevelChallenges
  tail : Array E
  deriving Repr, Inhabited

def Challenges.valid (c : Config) (ch : Challenges) : Bool := Id.run do
  if !c.valid || ch.levels.size != c.folds.size then return false
  let mut n := c.logN
  for i in [:c.folds.size] do
    n := n-c.folds[i]!
    let l := ch.levels[i]!
    let count := if i+1 < c.folds.size then c.oodCounts[i+1]! else 0
    if l.folds.size != c.folds[i]! || l.oodPoints.size != count then return false
    if !(l.oodPoints.all fun p => p.size == n) then return false
    if (deriveQueries (n+c.rates[i]!) c.queries[i]! l.querySqueezes).isNone then return false
  return ch.tail.size == n

/-- The actual two transmitted coefficients. The linear coefficient is claim+u2. -/
structure Message (R : Type u) where
  u0 : R
  u2 : R
  deriving Repr, Inhabited, BEq

def Message.eval {R : Type u} [Add R] [Mul R] (m : Message R) (claim r : R) : R :=
  m.u0 + r * (claim + m.u2) + (r*r) * m.u2

def Message.glue {R : Type u} [Add R] [Mul R] (m other : Message R) (s : R) : Message R :=
  ⟨m.u0 + s*other.u0, m.u2 + s*other.u2⟩

def roundMessage {R : Type u} [Zero R] [Add R] [Mul R] [Inhabited R]
    (f b : Array R) (block : Nat := 1) : Message R := Id.run do
  let mut m := Message.mk (0 : R) 0
  for i in [:f.size/2] do
    let offset := (i/block)*(2*block)+i%block
    let a := f[offset]!
    let a' := f[offset+block]!
    let w := b[offset]!
    let w' := b[offset+block]!
    m := ⟨m.u0 + a*w, m.u2 + (a+a')*(w+w')⟩
  return m

abbrev Oracle := Array (Array E)

structure OodClaim where
  value : E
  intro : Message E
  deriving Repr, Inhabited

structure LevelProof where
  afterFold : Array (Message E)
  nextOracle : Option Oracle
  oods : Array OodClaim
  rows : Array (Array E)
  intro : Message E
  deriving Repr, Inhabited

structure Opening where
  initial : Message E
  levels : Array LevelProof
  residual : Array E
  tailMessages : Array (Message E)
  deriving Repr, Inhabited

def weightGlue {R : Type u} [Add R] [Mul R] [Inhabited R]
    (b other : Array R) (s : R) : Array R :=
  tab b.size fun j => b[j]! + s*other[j]!

/-- The same low- or top-lane fold used by the prover and verifier. -/
def foldValues {R : Type u} [Add R] [Mul R] [Inhabited R]
    (values : Array R) (block : Nat) (r : R) : Array R :=
  if block == 1 then foldLow values r else foldLane values block r

structure VerifierState (R : Type u) where
  weight : Array R
  claim : R
  message : Message R
  deriving Repr, Inhabited

def VerifierState.fold {R : Type u} [Add R] [Mul R] [Inhabited R]
    (state : VerifierState R) (block : Nat) (r : R) (next : Message R) : VerifierState R :=
  ⟨foldValues state.weight block r, state.message.eval state.claim r, next⟩

def VerifierState.batch {R : Type u} [Add R] [Mul R] [Inhabited R]
    (state : VerifierState R) (basis : Array R) (value scale : R)
    (intro : Message R) : VerifierState R :=
  ⟨weightGlue state.weight basis scale, state.claim + scale * value,
    state.message.glue intro scale⟩

def VerifierState.checkTerminal {R : Type u} [Mul R] [BEq R] [Inhabited R]
    (state : VerifierState R) (value : R) : Bool :=
  state.claim == value * state.weight[0]!

def enforced {R : Type u} [Zero R] [One R] [Add R] [Mul R] [Inhabited R]
    (rows : Array (Array R)) (rs weights : Array R) (base : Bool) : R :=
  let eq := eqTable rs
  (tab rows.size fun i => weights[i]! * dot (if base then rows[i]!.reverse else rows[i]!) eq).foldl (· + ·) 0

def shapeValid (c : Config) (lanes : Nat) (b : Array E) : Bool :=
  c.valid && lanes > 0 && lanes ≤ 2^c.folds[0]! && b.size == 2^c.logN &&
    (b.extract (lanes * 2^(c.logN-c.folds[0]!)) b.size).all (· == E.zero)

def oracleValid (o : Oracle) (rows width : Nat) : Bool :=
  o.size == rows && o.all (fun row => row.size == width)

/-- Honest prover, with the same lane-first, OOD-before-query, intro/glue schedule. -/
def prove (c : Config) (ch : Challenges) (witness : Array K) (bInitial : Array E)
    (target : E) : Except String (Oracle × Opening) := do
  if !ch.valid c then throw "configuration/challenges"
  let block := 2^(c.logN-c.folds[0]!)
  let lanes := witness.size/block
  if witness.size != lanes*block || !shapeValid c lanes bInitial then throw "witness/weight shape"
  let mut f := tab (2^c.logN) fun i => E.ofK (witness[i]?.getD 0)
  let mut b := bInitial
  if dot f b != target then throw "incorrect target"
  let root := encodeBase witness c.logN c.folds[0]! c.rates[0]!
  let mut oracle := root
  let initial := roundMessage f b block
  let mut levels := #[]
  let mut residual := #[]
  let mut n := c.logN
  for i in [:c.folds.size] do
    let cs := ch.levels[i]!
    let mut afterFold := #[]
    for j in [:cs.folds.size] do
      let r := cs.folds[j]!
      f := foldValues f (if i == 0 then block else 1) r
      b := foldValues b (if i == 0 then block else 1) r
      n := n-1
      afterFold := afterFold.push (roundMessage f b (if i == 0 && j+1 < cs.folds.size then block else 1))
    let nextOracle := if i+1 < c.folds.size then some (encodeExt f n c.folds[i+1]! c.rates[i+1]!) else none
    if i+1 == c.folds.size then residual := f
    let mut oods := #[]
    let mut pending : Array (Array E) := #[]
    for z in cs.oodPoints do
      let weight := eqTable z
      oods := oods.push ⟨dot f weight, roundMessage f weight⟩
      pending := pending.push weight
    let qs ← (deriveQueries (n+c.rates[i]!) c.queries[i]! cs.querySqueezes).elim (throw "query challenges") pure
    let ws := powers cs.lambda qs.size
    let rows := qs.map fun q => oracle[q]!
    let basis := induced n qs ws
    let intro := roundMessage f basis
    let mut scalar := E.one
    for weight in pending do
      scalar := scalar*cs.lambda
      b := weightGlue b weight scalar
    scalar := scalar*cs.lambda
    b := weightGlue b basis scalar
    levels := levels.push ⟨afterFold, nextOracle, oods, rows, intro⟩
    oracle := nextOracle.getD #[]
  let mut tailMessages := #[]
  for j in [:ch.tail.size] do
    f := foldValues f 1 ch.tail[j]!
    b := foldValues b 1 ch.tail[j]!
    if j+1 < ch.tail.size then tailMessages := tailMessages.push (roundMessage f b)
  return (root, ⟨initial, levels, residual, tailMessages⟩)

/-- Allocation-free indexed replay; indices increase from `start`. -/
def runSteps {S : Type u} (step : Nat → S → S) : Nat → Nat → S → S
  | 0, _, s => s
  | count+1, start, s => runSteps step count (start+1) (step start s)

/-- Checked replay stops at the first error, without executing later transitions. -/
def runChecked {S : Type u} (step : Nat → S → Except String S) :
    Nat → Nat → S → Except String S
  | 0, _, s => .ok s
  | count+1, start, s => do
      let next ← step start s
      runChecked step count (start+1) next

structure CheckedState where
  n : Nat
  state : VerifierState E
  oracle : Oracle
  deriving Repr, Inhabited

/-- One transmitted fold message, without any honesty requirement. -/
def foldStep (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (j : Nat) (s : CheckedState) : CheckedState :=
  { s with n := s.n-1, state := s.state.fold block cs.folds[j]! p.afterFold[j]! }

def foldBlock (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (s : CheckedState) : CheckedState :=
  runSteps (foldStep block cs p) cs.folds.size 0 s

/-- The scalar is carried explicitly: the first OOD has coefficient lambda. -/
def oodStep (cs : LevelChallenges) (p : LevelProof)
    (j : Nat) (s : VerifierState E × E) : VerifierState E × E :=
  let scalar := s.2 * cs.lambda
  let ood := p.oods[j]!
  (s.1.batch (eqTable cs.oodPoints[j]!) ood.value scalar ood.intro, scalar)

def oodBatch (cs : LevelChallenges) (p : LevelProof) (s : VerifierState E) :
    VerifierState E × E :=
  runSteps (oodStep cs p) p.oods.size 0 (s, E.one)

def queryBatch (n i : Nat) (cs : LevelChallenges) (p : LevelProof)
    (qs : Array Nat) (s : VerifierState E × E) : VerifierState E :=
  let ws := powers cs.lambda qs.size
  s.1.batch (induced n qs ws) (enforced p.rows cs.folds ws (i == 0))
    (s.2 * cs.lambda) p.intro

def authenticateRow (oracle : Oracle) (qs : Array Nat) (p : LevelProof)
    (j : Nat) (_ : Unit) : Except String Unit := do
  if p.rows[j]! != oracle[qs[j]!]! then throw "authentication"

/-- One actual checked level. All length and authentication checks precede batching;
the commitment/final-length check precedes query derivation, as in the wire schedule. -/
def verifyLevel (c : Config) (ch : Challenges) (proof : Opening)
    (i : Nat) (s : CheckedState) : Except String CheckedState := do
  let cs := ch.levels[i]!
  let p := proof.levels[i]!
  if p.afterFold.size != cs.folds.size || p.oods.size != cs.oodPoints.size then
    throw "round/OOD length"
  let s := foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1) cs p s
  if i+1 < c.folds.size then
    let next ← p.nextOracle.elim (throw "missing commitment") pure
    if !oracleValid next (2^(s.n-c.folds[i+1]!+c.rates[i+1]!)) (2^c.folds[i+1]!) then
      throw "commitment shape"
  else
    if p.nextOracle.isSome || proof.residual.size != 2^s.n then throw "final length"
  let qs ← (deriveQueries (s.n+c.rates[i]!) c.queries[i]! cs.querySqueezes).elim
    (throw "query challenges") pure
  if p.rows.size != qs.size then throw "query length"
  let _ ← runChecked (authenticateRow s.oracle qs p) qs.size 0 ()
  let batched := queryBatch s.n i cs p qs (oodBatch cs p s.state)
  return ⟨s.n, batched, p.nextOracle.getD #[]⟩

def initializeVerifier (c : Config) (ch : Challenges) (lanes : Nat) (root : Oracle)
    (bInitial : Array E) (target : E) (proof : Opening) : Except String CheckedState := do
  if !ch.valid c || !shapeValid c lanes bInitial then throw "configuration/challenges/weight"
  if !oracleValid root (2^(c.logN-c.folds[0]!+c.rates[0]!)) lanes then throw "root shape"
  if proof.levels.size != c.folds.size || proof.tailMessages.size+1 != ch.tail.size then
    throw "proof length"
  return ⟨c.logN, ⟨bInitial, target, proof.initial⟩, root⟩

def replayLevels (c : Config) (ch : Challenges) (proof : Opening)
    (s : CheckedState) : Except String CheckedState :=
  runChecked (verifyLevel c ch proof) c.folds.size 0 s

def tailStep (ch : Challenges) (proof : Opening) (j : Nat)
    (s : VerifierState E) : VerifierState E :=
  let next := if j+1 < ch.tail.size then proof.tailMessages[j]! else s.message
  s.fold 1 ch.tail[j]! next

def closeTail (ch : Challenges) (proof : Opening) (s : VerifierState E) :
    VerifierState E :=
  runSteps (tailStep ch proof) ch.tail.size 0 s

def checkClosing (ch : Challenges) (proof : Opening) (s : VerifierState E) :
    Except String Unit := do
  if !s.checkTerminal (mle proof.residual ch.tail) then throw "terminal mismatch"
  return ()

/-- Untrusted opening verifier. The shared transitions consume arbitrary messages;
no access to a witness, honest-message constructor, or prover state is needed. -/
def verify (c : Config) (ch : Challenges) (lanes : Nat) (root : Oracle)
    (bInitial : Array E) (target : E) (proof : Opening) : Except String Unit := do
  let initial ← initializeVerifier c ch lanes root bInitial target proof
  let final ← replayLevels c ch proof initial
  checkClosing ch proof (closeTail ch proof final.state)

end Whir.Protocol
