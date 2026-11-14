module

public import PqDas.Defs
public import Common.SimDefs
public import Common.Duplex.Defs
public import Common.Lanes
public import LeanDa.WithHash
public import Statement.Field

@[expose] public section

/-!
# LeanDA in Benedikt Wagner's framework: the definitions of the proofs

LeanDA's code checker and vector commitment, the collision of two openings and the reduction that
computes it, the challenge's duplex (`daDuplex`, a `Common.SeedDuplex.DuplexSpec`), the opening's
check with a pure hash (`verifyCell`), the uniform samplers of `K` and `E`, and Wagner's
terms for a uniformly random table of the hash (`ksExpH`, `wpbCollExpH`, `forkCollExpH`), moved
here from `Statement/LeanDa.lean`: they are steps of the proofs, and no end statement names them.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

/-! ## Wagner's relation and verifier, with an oracle-free argument

His argument of LeanDA (`Argument`, an oracle-free `Nark`) proves `Relation`, the statement
carrying the challenges; his scheme's verification (`verifyRpm`) draws the challenges of the root
by the deployed duplex and verifies the argument for each opening. His theorems and his forking
route are about these; the end statements' arguments query the model's oracles instead
(`Statement/LeanDa.lean`). -/

section

namespace LeanDa

open PqDas

/-- **A draw**: what an answer of the grind carries, the challenge of its lanes `0, 1` and its
lane `2`, the proof of work. -/
abbrev Draw : Type := E × K

/-- The labels of a root's derivation: the seeded sponge's answer, then one per nonce. -/
abbrev nLabels : ℕ := nonceCount + 1

/-- **The challenges of the duplex**: the draws of the seeded sponge's answer (label `0`) and of
every nonce's answer (label `nonce + 1`). The deployed challenge of the membership test
(`membership_challenge`) is read off them by the nonce search (`selectChal`); the checker and the
relation read it alone. -/
abbrev MembershipChallenge : Type := Fin nLabels → Draw

/-- The draw of an answer: lanes `0, 1` as the challenge, lane `2` the proof of work. -/
def drawOfState (y : LeanVM.Semantics.KeccakState) : Draw := (chalOfState y, K.ofLane y[2])

/-- The draw of label `j`, zero past the labels. -/
def drawAt (v : MembershipChallenge) (j : ℕ) : Draw := if h : j < nLabels then v ⟨j, h⟩ else (0, 0)

/-- **The nonce search over the draws** (`grindMWithHash` read off the draws): from `nonce`, with
`fuel` nonces left, the first nonce whose draw has a valid proof of work gives its challenge; past
the last nonce, none. -/
def selectFrom (v : MembershipChallenge) : ℕ → ℕ → Option E
  | _, 0 => none
  | nonce, fuel + 1 =>
    if powValid (drawAt v (nonce + 1)).2.lane then some (drawAt v (nonce + 1)).1
    else selectFrom v (nonce + 1) fuel

/-- **The deployed challenge of a root's draws**: the nonce search from nonce `0`. -/
def selectChal (v : MembershipChallenge) : Option E := selectFrom v 0 nonceCount

/-- The draws of the nonces of the labels `js`, from the seeded sponge's answer `y`. -/
def branchDrawsM {m : Type → Type} [Monad m]
    (P : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (y : LeanVM.Semantics.KeccakState) : List (Fin nLabels) → m (List Draw)
  | [] => pure []
  | j :: js => do
    let o ← P (nonceInput y (j.val - 1))
    let zs ← branchDrawsM P y js
    pure (drawOfState o :: zs)

/-- The draws of a list, label by label. -/
def drawsVec (zs : List Draw) : MembershipChallenge := fun j ↦ zs.getD j default

/-- **The duplex's draws of a root**, in any monad: the transcript's sponge seeded with the
label's hash and the root (`Sponge::new`), its answer's draw, then every nonce's
(`absorb_nonce` on a copy of the seeded sponge). The nonce search reads the deployed challenge
off them (`selectChal`). -/
def membershipChallengeVecM {m : Type → Type} [Monad m] (H : List UInt8 → m Common.DigestBytes)
    (P : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState) (root : Common.DigestBytes) :
    m MembershipChallenge := do
  let iv ← H membershipLabel
  let s ← Sponge.newWith P iv root
  let zs ← branchDrawsM P s.state (Common.SeedDuplex.branchIdx nLabels)
  pure (drawsVec (drawOfState s.state :: zs))

/-- **Wagner's relation for LeanDA**: the cells commit to the root and pass the membership test on
the challenge the statement's draws give. -/
noncomputable def Relation (r : ℕ) (H : List UInt8 → Common.DigestBytes) (stmt : Unit × Common.DigestBytes × MembershipChallenge)
    (c : Fin (r * 128) → Cell) : Bool :=
  decide (commitCellsWithHash H c = stmt.2.1) && membershipCheckOpt (selectChal stmt.2.2) c

/-- An argument of knowledge for `Relation r H`. -/
abbrev Argument (r : ℕ) (H : List UInt8 → Common.DigestBytes) (Crs Proof : Type) :=
  Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs Proof
      (Relation r H)

/-- **Verification of an opening** in Wagner's scheme, with a hash `H` and the sponge's
permutation `P` in any monad: the draws of the commitment's root from the deployed duplex over
`P`, the argument's verification, and the opening's. -/
def verifyRpm {m : Type → Type} [Monad m] (H : List UInt8 → m Common.DigestBytes)
    (P : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs Proof rel) (crs : Crs)
    (com : Common.DigestBytes × Proof) (p : Fin (r * 128)) (x : Cell) (τ : CellOpening) : m
        Bool := do
  let z ← membershipChallengeVecM H P com.1
  let v ← verifyCellMWithHash H r com.1 p x τ
  pure (ps.verify crs ((), com.1, z) com.2 && v)

end LeanDa

end

/-! ## LeanDA's Merkle collisions -/

section

namespace LeanDa

/-- Uniform sampling of `K` through its bits. -/
instance : SampleableType K := SampleableType.ofEquiv BF64.equivFin.symm

/-- Uniform sampling of `E` limb by limb. -/
instance : SampleableType E := SampleableType.ofEquiv (CompPoly.Extension.Ext.equivFn _).symm

variable (H : List UInt8 → Common.DigestBytes)

/-- Climb from `node` at index `idx` along the siblings `path`. -/
def walk : ℕ → Common.DigestBytes → List Common.DigestBytes → Common.DigestBytes
  | _, node, [] => node
  | idx, node, s :: rest =>
    walk (idx / 2) (if idx % 2 = 0 then H (pairBytes node s) else H (pairBytes s node)) rest

/-- **Verification of a cell opening** with a pure hash (`verifyCellWith` over `Id`): a path of
`7 + logMaxRows` siblings that climbs from the cell's digest, at index the position, to the
commitment. -/
def verifyCell (r : ℕ) (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : CellOpening) : Bool :=
  decide (τ.path.length = 7 + logMaxRows) &&
    decide (walk H p (cellDigestWithHash H x) τ.path = com)

/-- The hash inputs from a cell's bytes `a` at index `idx` up to the root, the last one the
root's. -/
def hashInputs : ℕ → List UInt8 → List Common.DigestBytes → List (List UInt8)
  | _, a, [] => [a]
  | idx, a, s :: rest =>
    a :: hashInputs (idx / 2) (if idx % 2 = 0 then pairBytes (H a) s else pairBytes s (H a)) rest

/-- The first pair of inputs, level by level, that differ and hash alike. -/
def findCollision : List (List UInt8) → List (List UInt8) → List UInt8 × List UInt8
  | a :: as, b :: bs => if a ≠ b ∧ H a = H b then (a, b) else findCollision as bs
  | _, _ => ([], [])

/-- The collision two openings of one position give. -/
def openingsCollision (r : ℕ) (p : Fin (r * 128)) (x : Cell) (τ : CellOpening) (x' : Cell)
    (τ' : CellOpening) : List UInt8 × List UInt8 :=
  findCollision H (hashInputs H p (cellBytes x) τ.path)
    (hashInputs H p (cellBytes x') τ'.path)

end LeanDa

end

section

open PqDas OracleComp OracleSpec ENNReal Common
open LeanVM.Parameters (K.toBytes)

namespace LeanDa

/-- A `K` word's eight little-endian bytes (`K.toBytes`; a symbol's limb, or a digest word), byte
`t` its bits `8 t … 8 t + 7`. -/
theorem toBytes_eq_shift (a : K) :
    K.toBytes a = (List.range 8).map fun t ↦ (a.toBitVec.toNat >>> (8 * t)).toUInt8 := by
  unfold LeanVM.Parameters.K.toBytes LeanVM.Protocol.KeccakHash.wordBytes
  refine List.map_congr_left fun t ht => ?_
  have ht8 : t < 8 := List.mem_range.mp ht
  refine UInt8.toNat_inj.mp ?_
  simp only [Nat.toUInt8, UInt8.toNat_ofNat', UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    Nat.toUInt64, UInt64.toNat_ofNat', LeanVM.Parameters.K.lane]
  rw [Nat.mod_eq_of_lt (show 8 * t < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * t < 64 by omega)]
  rfl

/-- **LeanDA's code checker**: the membership test on the deployed challenge, component `1`. -/
noncomputable def checker (r : ℕ) : CodeChecker Cell (r * 128) MembershipChallenge :=
    ⟨fun z c ↦ membershipCheckOpt (selectChal z) c⟩

/-- **LeanDA's vector commitment** with hash `H`: the root of the tree of blob trees, cells
opened by their paths in it. It needs no key. -/
def merkleVC (r : ℕ) (H : List UInt8 → Common.DigestBytes) :
    VectorCommitment Cell (r * 128) Unit Common.DigestBytes CellOpening where
  setup := pure ()
  commit _ c := commitCellsWithHash H c
  openAt _ c p := openCellWithHash H c p
  verify _ com p x τ := verifyCell H r com p x τ

/-- The collision experiment for a hash function: a finder wins if it outputs two different
byte strings with the same hash. -/
def hashCollisionExp (H : List UInt8 → Common.DigestBytes) (B : ProbComp (List UInt8 × List UInt8)) :
    ProbComp Bool := do
  let (a, b) ← B
  return (decide (a ≠ b) && decide (H a = H b))

/-- **The reduction from position binding to a collision**: run the adversary and climb its two
openings (`openingsCollision`). -/
def merkleCollider (r : ℕ) (H : List UInt8 → Common.DigestBytes)
    (A : VectorCommitment.PosBindingAdv Cell (r * 128) Unit Common.DigestBytes CellOpening) :
    ProbComp (List UInt8 × List UInt8) := do
  let (_, p, x, τ, x', τ') ← A ()
  return openingsCollision H r p x τ x' τ'

/-- An argument of knowledge for Wagner's scheme relation of LeanDA (`Relation`, by
`relation_eq`). -/
abbrev WArgument (r : ℕ) (H : List UInt8 → Common.DigestBytes) (Crs Proof : Type) :=
  Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs Proof
    (schemeRel (merkleVC r H) (checker r))

/-! ### Lanes and bytes

The sponge's state is the statement's `KState` of `25` lanes of `u64`
(`LeanVM.Semantics.KeccakState`); the proofs read it on the permutation's `200` bytes (`KState` of
`common`), lane `i` at bytes `8 i … 8 i + 7`, little endian (`LeanVM.KState.toRpm`,
`Common/Lanes.lean`). -/

/-- The sponge's lanes, the statement's Keccak state. -/
abbrev Lanes := LeanVM.Semantics.KeccakState

/-- **The permutation's state of 25 lanes**, on bytes: lane `i` at bytes `8 i … 8 i + 7`. -/
def lanesToState (L : Lanes) : KState := LeanVM.KState.toRpm L

/-- **The lanes of a permutation's state.** -/
def stateToLanes (s : KState) : Lanes := LeanVM.Rpm.KState.ofRpm s

/-- **The permutation on lanes** from a permutation of the bytes, in any monad. -/
def lanePerm {m : Type → Type} [Monad m] (π : KState → m KState) (L : Lanes) : m Lanes :=
  stateToLanes <$> π (lanesToState L)

/-- **A lane's bytes**, little endian. -/
def laneBytes : K ≃ Vector UInt8 8 :=
  BF64.equivFin.trans <| (finCongr (show 2 ^ 64 = 256 ^ 8 by norm_num)).trans <|
    finFunctionFinEquiv.symm.trans <|
      (Equiv.arrowCongr (Equiv.refl _) Common.uInt8EquivFin.symm).trans
        (arrayVectorEquivFin UInt8 8).symm

/-- The statement's games on byte states: the oracles `KSpecB`, Keccak-256 `hKB` and the
permutation `pKB` read on lanes (`lanePerm`). -/
abbrev hKB (a : List UInt8) : OracleComp KSpecB Common.DigestBytes := liftM (KSpecB.query (.inr (.inl a)))

/-- A call `π x` among the oracles on byte states, on lanes. -/
abbrev pKB (L : Lanes) : OracleComp KSpecB Lanes :=
  lanePerm (fun x ↦ liftM (KSpecB.query (.inr (.inr (.forward x))))) L

/-- A position-binding adversary on byte states. -/
abbrev PosBindingAdvB (r : ℕ) (Crs Proof : Type) :=
  Unit × Crs → OracleComp KSpecB ((Common.DigestBytes × Proof) × Fin (r * 128) × Cell × CellOpening × Cell × CellOpening)

/-- A code-binding adversary on byte states. -/
abbrev CodeBindingAdvB (r : ℕ) (Crs Proof : Type) :=
  Unit × Crs → OracleComp KSpecB ((Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening))

/-- A knowledge-soundness adversary on byte states. -/
abbrev KsAdvB (Crs Proof : Type) := Crs → OracleComp KSpecB ((Unit × Common.DigestBytes × MembershipChallenge) × Proof)

/-! ### The games in the two-oracle form

The games of `Statement/LeanDa.lean` query `π` for the verifier's sponge (`hK`, `pK`); the proofs
take them in the two-oracle form of `Common.rpmGame2`, the verifier's calls of the permutation
direct calls `F` (`hR`, `pR`), which `Common.toOne` turns into `π` queries
(`LeanDa.RpmGames`). -/

/-- The verifier's oracles: coins, Keccak-256 `H` and the direct calls `F` of the permutation. -/
abbrev Rom2 := unifSpec + hfSpec (List UInt8) DigestBytes KState

/-- Keccak-256 among the verifier's oracles. -/
abbrev hR (a : List UInt8) : OracleComp Rom2 Common.DigestBytes :=
  hQuery (Msg := List UInt8) (Dg := DigestBytes) (E := KRest) (C := KCap) a

/-- The direct calls `F` of the permutation, on lanes. -/
abbrev pR (L : Lanes) : OracleComp Rom2 Lanes :=
  lanePerm (fun x ↦ fQuery (Msg := List UInt8) (Dg := DigestBytes) x) L

/-- The adversary's oracles: coins, Keccak-256, `π` and `π⁻¹`. -/
abbrev AdvSpec := KSpecB

/-- **Calls of the permutation** in the two-oracle form: a hash of `n` bytes costs
`⌊n / 136⌋ + 1`, a query of `π` or `π⁻¹` and a direct call one. -/
def permCalls2 : (dSpec2 (List UInt8) DigestBytes KState).Domain → ℕ
  | .inl _ => 0
  | .inr (.inl m) => m.length / 136 + 1
  | .inr (.inr _) => 1

section Games

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)

/-- The verifier's part of the position-binding game: both openings verify, at two different
cells. -/
def posBindingPost (crs : Crs)
    (out : (Common.DigestBytes × Proof) × Fin (r * 128) × Cell × CellOpening × Cell × CellOpening) :
    OracleComp Rom2 Bool := do
  let b ← verifyRpm hR pR r ps crs out.1 out.2.1 out.2.2.1 out.2.2.2.1
  let b' ← verifyRpm hR pR r ps crs out.1 out.2.1 out.2.2.2.2.1 out.2.2.2.2.2
  pure (decide (out.2.2.1 ≠ out.2.2.2.2.1) && b && b')

/-- The position-binding game in the two-oracle form. -/
def posBindingGame2 (A : PosBindingAdvB r Crs Proof) :
    OracleComp (dSpec2 (List UInt8) DigestBytes KState) Bool :=
  rpmGame2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (posBindingPost r ps)

/-- The position-binding experiment: the game against the lazily sampled random permutation. -/
noncomputable def posBindingExpRpm (A : PosBindingAdvB r Crs Proof) : ProbComp Bool :=
  realGame2 keccakPadding KState.zero (posBindingGame2 r ps A)

/-- The verifier's part of the code-binding game: every opening verifies, and no codeword agrees
with the opened cells. -/
noncomputable def codeBindingPost (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) : OracleComp Rom2 Bool := do
  let verdicts ← out.2.mapM fun o ↦ verifyRpm hR pR r ps crs out.1 o.1 o.2.1 o.2.2
  pure (verdicts.all id && !decide ((leanDaErasureCode r).Consistent (out.2.map fun o ↦ (o.1,
      o.2.1))))

/-- The code-binding game in the two-oracle form. -/
noncomputable def codeBindingGame2 (A : CodeBindingAdvB r Crs Proof) :
    OracleComp (dSpec2 (List UInt8) DigestBytes KState) Bool :=
  rpmGame2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (codeBindingPost r ps)

/-- The code-binding experiment: the game against the lazily sampled random permutation. -/
noncomputable def codeBindingExpRpm (A : CodeBindingAdvB r Crs Proof) : ProbComp Bool :=
  realGame2 keccakPadding KState.zero (codeBindingGame2 r ps A)

/-- The verifier's part of the knowledge-soundness game: the proof verifies, and the extracted
cells do not satisfy the relation (`Relation`), their root hashed with Keccak-256. -/
noncomputable def ksPost (crs : Crs) (out : (Unit × Common.DigestBytes × MembershipChallenge) ×
    Proof) :
    OracleComp Rom2 Bool := do
  let root ← commitCellsMWithHash hR (ext crs out.1 out.2)
  pure (ps.verify crs out.1 out.2 &&
    !(decide (root = out.1.2.1) && membershipCheckOpt (selectChal out.1.2.2) (ext crs out.1 out.2)))

/-- The knowledge-soundness game in the two-oracle form. -/
noncomputable def ksGame2 (B : KsAdvB Crs Proof) :
    OracleComp (dSpec2 (List UInt8) DigestBytes KState) Bool :=
  rpmGame2 (liftM ps.setup) B (ksPost r ps ext)

/-- The knowledge-soundness experiment: the game against the lazily sampled random permutation. -/
noncomputable def ksExpRpm (B : KsAdvB Crs Proof) : ProbComp Bool :=
  realGame2 keccakPadding KState.zero (ksGame2 r ps ext B)

end Games

/-- The relation is Wagner's scheme relation for LeanDA's vector commitment and code checker. -/
theorem relation_eq (r : ℕ) (H : List UInt8 → Common.DigestBytes) :
    Relation r H = schemeRel (merkleVC r H) (checker r) := rfl

end LeanDa

end

/-! ## LeanDA's challenge duplex -/

section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal
open LeanVM.Parameters (K.toBytes)

namespace LeanDa

/-- Byte `p` of a state. -/
def byteAt (y : KState) (p : ℕ) : UInt8 := y.toBytes.getD p 0

theorem toBytes_length (y : KState) : y.toBytes.length = 200 := by
  simp only [KState.toBytes, List.length_append, Vector.length_toList]

theorem getD_toBytes_lt32 (y : KState) (p : ℕ) (hp : p < 32) :
    y.toBytes.getD p 0 = y.1.1[p] := by
  rw [List.getD_eq_getElem?_getD, KState.toBytes, List.append_assoc,
    List.getElem?_append_left (by rw [Vector.length_toList]; exact hp),
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hp, Option.getD_some]

theorem getD_toBytes_lt136 (y : KState) (p : ℕ) (hp : 32 ≤ p) (hp' : p < 136) :
    y.toBytes.getD p 0 = y.1.2[p - 32]'(by omega) := by
  rw [List.getD_eq_getElem?_getD, KState.toBytes, List.append_assoc,
    List.getElem?_append_right (by rw [Vector.length_toList]; exact hp), Vector.length_toList,
    List.getElem?_append_left (by rw [Vector.length_toList]; omega),
    Vector.getElem?_toList, Vector.getElem?_eq_getElem (by omega), Option.getD_some]

theorem getD_toBytes_lt200 (y : KState) (p : ℕ) (hp : 136 ≤ p) (hp' : p < 200) :
    y.toBytes.getD p 0 = y.2[p - 136]'(by omega) := by
  have hlen : (y.1.1.toList ++ y.1.2.toList).length = 136 := by
    rw [List.length_append, Vector.length_toList, Vector.length_toList]
  rw [List.getD_eq_getElem?_getD, KState.toBytes, List.getElem?_append_right (by rw [hlen]; exact hp),
    hlen, Vector.getElem?_toList, Vector.getElem?_eq_getElem (by omega), Option.getD_some]

theorem ofBytes_toBytes (y : KState) : KState.ofBytes y.toBytes = y := by
  obtain ⟨⟨a, b⟩, c⟩ := y
  refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> apply Vector.ext <;> intro i hi <;>
    simp only [KState.ofBytes, Vector.getElem_ofFn]
  · exact getD_toBytes_lt32 ((a, b), c) i hi
  · rw [getD_toBytes_lt136 ((a, b), c) (32 + i) (by omega) (by omega)]
    simp only [Nat.add_sub_cancel_left]
  · rw [getD_toBytes_lt200 ((a, b), c) (136 + i) (by omega) (by omega)]
    simp only [Nat.add_sub_cancel_left]

theorem toBytes_ofBytes {l : List UInt8} (hl : l.length = 200) : (KState.ofBytes l).toBytes = l := by
  apply List.ext_getElem (by rw [toBytes_length, hl])
  intro p h1 h2
  rw [toBytes_length] at h1
  rw [← List.getD_eq_getElem _ 0]
  by_cases hp : p < 32
  · rw [getD_toBytes_lt32 _ p hp]
    simp only [KState.ofBytes, Vector.getElem_ofFn]
    rw [List.getD_eq_getElem _ 0 h2]
  · by_cases hp' : p < 136
    · rw [getD_toBytes_lt136 _ p (by omega) hp']
      simp only [KState.ofBytes, Vector.getElem_ofFn]
      rw [show 32 + (p - 32) = p by omega, List.getD_eq_getElem _ 0 h2]
    · rw [getD_toBytes_lt200 _ p (by omega) (by omega)]
      simp only [KState.ofBytes, Vector.getElem_ofFn]
      rw [show 136 + (p - 136) = p by omega, List.getD_eq_getElem _ 0 h2]

/-- **A state is its 200 bytes.** -/
def bytesEquiv : KState ≃ (Fin 200 → UInt8) where
  toFun y i := byteAt y i
  invFun f := KState.ofBytes (List.ofFn f)
  left_inv y := by
    have : List.ofFn (fun i : Fin 200 ↦ byteAt y i) = y.toBytes :=
      List.ext_getElem (by rw [List.length_ofFn, toBytes_length]) fun p h1 h2 ↦ by
        rw [List.getElem_ofFn]; exact List.getD_eq_getElem _ 0 h2
    show KState.ofBytes (List.ofFn _) = y
    rw [this, ofBytes_toBytes]
  right_inv f := by
    funext i
    show byteAt (KState.ofBytes (List.ofFn f)) i = f i
    rw [byteAt, toBytes_ofBytes (List.length_ofFn), List.getD_eq_getElem _ 0
      (by rw [List.length_ofFn]; exact i.2), List.getElem_ofFn]

theorem byteAt_lanesToState (L : Lanes) (p : ℕ) (hp : p < 200) :
    byteAt (lanesToState L) p = (LeanVM.Protocol.KeccakHash.wordBytes (L[p / 8]'(by omega))).getD
      (p % 8) 0 := by
  rw [byteAt, lanesToState, List.getD_eq_getElem _ _ (by simp; omega),
    LeanVM.Rpm.toBytes_toRpm_getElem _ _ hp]

theorem byteAt_stateToLanes (y : KState) (p : ℕ) (hp : p < 200) :
    (LeanVM.Protocol.KeccakHash.wordBytes ((stateToLanes y)[p / 8]'(by omega))).getD (p % 8) 0 =
      byteAt y p := by
  rw [← byteAt_lanesToState _ p hp, lanesToState, stateToLanes, LeanVM.Rpm.toRpm_ofRpm]

theorem stateToLanes_lanesToState (L : Lanes) : stateToLanes (lanesToState L) = L :=
  LeanVM.Rpm.ofRpm_toRpm L

theorem lanesToState_stateToLanes (y : KState) : lanesToState (stateToLanes y) = y :=
  LeanVM.Rpm.toRpm_ofRpm y

theorem lanesToState_injective : Function.Injective lanesToState := fun L L' h ↦ by
  rw [← stateToLanes_lanesToState L, h, stateToLanes_lanesToState]

/-- Bytes `0 … m-1` and `m … m+k-1`. -/
def splitEquiv (m k : ℕ) : (Fin (m + k) → UInt8) ≃ (Fin m → UInt8) × (Fin k → UInt8) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem splitEquiv_snd {m k : ℕ} (f : Fin (m + k) → UInt8) (j : Fin k) :
    (splitEquiv m k f).2 j = f (Fin.natAdd m j) := by
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

/-- Three lanes as a draw: the first two the limbs of the challenge, the third the proof of work. -/
def lanesDrawEquiv : (Fin 3 → K) ≃ Draw where
  toFun g := (ofLimbs (g 0) (g 1), g 2)
  invFun d := ![limb d.1 0, limb d.1 1, d.2]
  left_inv g := by
    funext a
    fin_cases a <;> rfl
  right_inv d := by
    obtain ⟨x, k⟩ := d
    refine Prod.ext (CompPoly.Extension.Ext.ext fun i ↦ ?_) rfl
    obtain ⟨i, hi⟩ := i
    have hi' : i < 2 := hi
    interval_cases i <;> rfl

/-- **The draw of 24 bytes**: three lanes, the limbs of the challenge and the proof of work. -/
def limbsEquiv : (Fin 24 → UInt8) ≃ Draw :=
  (Equiv.arrowCongr (finProdFinEquiv (m := 3) (n := 8)).symm (Equiv.refl UInt8)).trans <|
    (Equiv.curry _ _ _).trans <|
      (Equiv.arrowCongr (Equiv.refl _)
        ((arrayVectorEquivFin UInt8 8).symm.trans laneBytes.symm)).trans
        lanesDrawEquiv

/-- The rest of an answer after its challenge: bytes `24 … 127`, and the capacity, bytes
`128 … 199`. -/
abbrev DaW := (Fin 104 → UInt8) × (Fin 72 → UInt8)

/-- The capacity: bytes `128 … 199`, lanes `16 … 24`. -/
abbrev DaCp := Fin 72 → UInt8

/-- **An answer from its draw and its rest.** -/
def daBuild : Draw × DaW ≃ KState :=
  (Equiv.prodCongr limbsEquiv.symm (splitEquiv 104 72).symm).trans
    ((splitEquiv 24 176).symm.trans bytesEquiv.symm)

theorem daBuild_symm_cap (y : KState) (j : Fin 72) :
    (daBuild.symm y).2.2 j = byteAt y (128 + j) := by
  simp only [daBuild, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_snd]
  rw [splitEquiv_snd, splitEquiv_snd]
  show byteAt y (24 + (104 + (j : ℕ))) = _
  congr 1
  omega

/-- A state with the chains' first capacity, zero: the label's hash in lanes `0 … 3`, the rest
zero. -/
def daInit (iv : Common.DigestBytes) : KState := lanesToState (freshSpongeInput iv
    (Vector.replicate 32 0))

/-- **The first state of a root's chain** (`Sponge::new`): the label's hash in lanes `0 … 3`,
the root's words in lanes `4 … 7`, the rest zero. -/
def daFirst (root iv : Common.DigestBytes) : KState := lanesToState (freshSpongeInput iv root)

/-- **The state of label `j`'s nonce, `j - 1`, after the seeded sponge's answer `y`**: the nonce
and its tag over the rate, the capacity kept (`absorb_nonce` on a copy of the seeded sponge). -/
def daNext (j : Fin nLabels) (y : KState) : KState :=
  lanesToState (nonceInput (stateToLanes y) (j.val - 1))

theorem duplexInput_high (s : Sponge) (i : ℕ) (hi : 16 ≤ i) (hi' : i < 25) :
    (duplexInput s)[i] = s.state[i] := by
  simp only [duplexInput, Vector.getElem_ofFn, rateLanes, show ¬ i < 16 by omega, ↓reduceIte]
  rfl

theorem duplexInput_low (s : Sponge) (i : ℕ) (hi : i < 16) :
    (duplexInput s)[i] = ((rateWords s.pending).getD i 0).lane := by
  simp only [duplexInput, Vector.getElem_ofFn, rateLanes, hi, ↓reduceIte]

/-- A duplexing keeps the capacity bytes. -/
theorem byteAt_duplexInput (y : KState) (pending : List (E × K)) (p : ℕ) (hp : 128 ≤ p)
    (hp' : p < 200) : byteAt (lanesToState (duplexInput ⟨stateToLanes y, pending⟩)) p = byteAt y p := by
  rw [byteAt_lanesToState _ p hp', ← byteAt_stateToLanes y p hp']
  have := duplexInput_high ⟨stateToLanes y, pending⟩ (p / 8) (by omega) (by omega)
  simp only at this
  rw [this]

/-- A fresh sponge's capacity bytes are zero, whatever its public input. -/
theorem byteAt_freshSpongeInput (iv d d' : Common.DigestBytes) (p : ℕ) (hp : 128 ≤ p)
    (hp' : p < 200) :
    byteAt (lanesToState (freshSpongeInput iv d)) p =
      byteAt (lanesToState (freshSpongeInput iv d')) p := by
  rw [byteAt_lanesToState _ p hp', byteAt_lanesToState _ p hp']
  simp only [freshSpongeInput, Vector.getElem_ofFn, show ¬ p / 8 < 4 by omega,
    show ¬ p / 8 < 8 by omega, ↓reduceIte]

theorem word_bytes (d : Common.DigestBytes) (p : ℕ) (hp : p < 32) :
    d.toList[p]'(by simpa using hp) =
      (K.toBytes (digestWord d (p / 8)))[p % 8]'(by simp [toBytes_eq_shift]; omega) := by
  have e : K.toBytes (digestWord d (p / 8)) =
      (List.range 8).map fun k ↦ d.toList.getD (8 * (p / 8) + k) 0 :=
    LeanVM.Rpm.wordBytes_leLane d.toList (p / 8)
  simp only [e, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  congr 1
  omega

/-- **A digest is its four words.** -/
theorem eq_of_words {d d' : Common.DigestBytes} (h : ∀ i < 4, digestWord d i = digestWord d' i) : d
    = d' := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem (by simp)
  intro p h1 h2
  have hp : p < 32 := by simpa using h1
  rw [word_bytes d p hp, word_bytes d' p hp]
  congr 2
  exact h (p / 8) (by omega)

/-- **Different roots start different chains.** -/
theorem daFirst_injective (iv : Common.DigestBytes) : Function.Injective fun r ↦ daFirst r iv := by
  intro r r' h
  have h' := lanesToState_injective h
  refine eq_of_words fun i hi ↦ ?_
  have := congrArg (fun L : Lanes ↦ L[4 + i]'(by omega)) h'
  simp only [freshSpongeInput, Vector.getElem_ofFn, show ¬ 4 + i < 4 by omega,
    show 4 + i < 8 by omega, ↓reduceIte, show 4 + i - 4 = i by omega] at this
  exact congrArg K.ofLane this

/-- The root whose chain a state starts, if any. -/
noncomputable def daDec (iv : Common.DigestBytes) (x : KState) : Option Common.DigestBytes := by
  classical
  exact if h : ∃ r, daFirst r iv = x then some h.choose else none

theorem daDec_iff (iv : Common.DigestBytes) (x : KState) (r : Common.DigestBytes) :
    daDec iv x = some r ↔ daFirst r iv = x := by
  classical
  unfold daDec
  constructor
  · intro h
    split at h
    · next hx =>
      cases h
      exact hx.choose_spec
    · cases h
  · intro h
    have hx : ∃ r, daFirst r iv = x := ⟨r, h⟩
    simp only [hx, ↓reduceDIte]
    congr 1
    exact daFirst_injective iv (hx.choose_spec.trans h.symm)

/-- Lane `0` of a nonce's state is the nonce. -/
theorem nonceInput_lane0 (y : Lanes) (a : ℕ) :
    (nonceInput y a)[0] = (K.ofBits a).lane := by
  have h : limb (LeanVM.Protocol.Verifier.eOfNat a) 0 = K.ofBits a := by
    rfl
  simp [nonceInput, duplexInput, rateLanes, rateWords, h]

theorem lane_ofBits_toNat (a : ℕ) : (K.ofBits a).lane.toNat = a % 2 ^ 64 := by
  show (BitVec.ofNat 64 a).toNat = a % 2 ^ 64
  simp

/-- **Different nonces, different states.** -/
theorem daNext_inj (j j' : Fin nLabels) (y : KState) (hj : j.val ≠ 0) (hj' : j'.val ≠ 0)
    (h : daNext j y = daNext j' y) : j = j' := by
  have h' := congrArg (fun L : Lanes ↦ L[0]) (lanesToState_injective h)
  simp only [nonceInput_lane0] at h'
  have e := congrArg UInt64.toNat h'
  rw [lane_ofBits_toNat, lane_ofBits_toNat] at e
  have h1 := j.isLt
  have h2 := j'.isLt
  simp only [nLabels, nonceCount] at h1 h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e
  exact Fin.ext (by omega)

/-- **LeanDA's challenge as a duplex** (`membership_challenge`): a root's derivation starts at
`daFirst r iv`, the label's hash and the root, and branches from its answer, label `j` absorbing
the nonce `j - 1` (`daNext`); the deployed challenge is read off the nonces' draws by the nonce
search (`selectChal`). Every state has the capacity of `daInit iv`, zero, or keeps the seeded
answer's. -/
noncomputable def daDuplex :
    DuplexSpec (List UInt8) DigestBytes KState Common.DigestBytes Draw DaW DaCp nLabels where
  label := membershipLabel
  init := daInit
  first := daFirst
  next := daNext
  build := daBuild
  capW := Prod.snd
  dec := daDec
  dec_iff := daDec_iff
  n_pos := by simp
  cap_first r d := by
    funext j
    rw [daBuild_symm_cap, daBuild_symm_cap]
    exact byteAt_freshSpongeInput d r _ _ (by omega) (by omega)
  cap_next _ y := by
    funext j
    rw [daBuild_symm_cap, daBuild_symm_cap]
    exact byteAt_duplexInput y _ _ (by omega) (by omega)
  next_inj := daNext_inj

end LeanDa

end

/-! ## Wagner's terms, for a uniformly random table of the hash -/

section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace LeanDa

/-- Wagner's oracles: coins and the challenges `G`, a random oracle of the roots. -/
abbrev WSpec := unifSpec + (Common.DigestBytes →ₒ MembershipChallenge)

/-- The challenges and `H`. -/
abbrev TSpec := (Common.DigestBytes →ₒ MembershipChallenge) + roSpec (List UInt8) DigestBytes

/-- A cache of `H`. -/
abbrev HCache := (roSpec (List UInt8) DigestBytes).QueryCache

/-- A short string: at most `2048` bytes, a cell's. -/
def shortP (a : List UInt8) : Prop := a.length ≤ 2048

instance : DecidablePred shortP := fun a ↦ inferInstanceAs (Decidable (a.length ≤ 2048))

noncomputable instance : Fintype {a : List UInt8 // shortP a} :=
  (List.finite_length_le (α := UInt8) 2048).fintype

/-- A table of `H` on the short strings. -/
abbrev HTab := {a : List UInt8 // shortP a} → DigestBytes

/-- **The hash of a table**: the table's answer on a short string, `default` on a long one. -/
def Hh (h : HTab) (a : List UInt8) : Common.DigestBytes := if ha : shortP a then h ⟨a, ha⟩ else default

/-- **`H` from a table, in Wagner's world**: the table on short strings, lazily sampled on long
ones (the state), the challenges forwarded to Wagner's random oracle. -/
noncomputable def tImpl (h : HTab) : QueryImpl (unifSpec + TSpec) (StateT HCache (OracleComp WSpec))
  | .inl k => StateT.mk fun c ↦ (·, c) <$> liftM (WSpec.query (.inl k))
  | .inr (.inl d) => StateT.mk fun c ↦ (·, c) <$> liftM (WSpec.query (.inr d))
  | .inr (.inr a) =>
      if ha : shortP a then StateT.mk fun c ↦ pure (h ⟨a, ha⟩, c)
      else StateT.mk fun c ↦ liftM (((roSpec (List UInt8) DigestBytes).randomOracle a).run c)

/-- The simulated world's oracles from a table `h` of `H`. -/
noncomputable def phiG (h : HTab) :
    QueryImpl (unifSpec + GSpec (List UInt8) DigestBytes Common.DigestBytes Draw nLabels) (StateT HCache (OracleComp WSpec)) :=
  tImpl h ∘ₛ (swapImpl ∘ₛ toV)

section Adversary

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)

/-- The crs the adversary runs with: the given one when the setup can output it, else one it
can (the bound on the adversary's queries holds for these). -/
noncomputable def fixCrs (crs : Crs) : Crs := by
  classical
  exact if crs ∈ support ps.setup then crs else (support_nonempty ps.setup).some

/-- The adversary in the simulated world: `H` queried at the label, then the RPM adversary with
its permutation queries simulated from `H` and `F`, `F` answered by the duplex lemma's simulator. -/
noncomputable def advSim (A : CodeBindingAdvB r Crs Proof) (crs : Crs) :
    OracleComp (unifSpec + GSpec (List UInt8) DigestBytes Common.DigestBytes Draw nLabels)
      ((Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) :=
  (simulateQ (simImpl daDuplex hP gaP) (hQ (St := KState) daDuplex.label >>= fun _ ↦
    advS2 keccakPadding KState.zero (A ((), crs)))).run' SimSt.init

/-- **Wagner's adversary for the table `h` of `H`**: the simulated adversary, with `H` answered
from `h` on short strings and lazily on long ones, and the challenges `G` from Wagner's random
oracle. -/
noncomputable def advH (A : CodeBindingAdvB r Crs Proof) (h : HTab) :
    ErasureCodeCommitment.CodeBindingAdv (OracleComp WSpec) Cell (r * 128) (Unit × Crs)
      (Common.DigestBytes × Proof) CellOpening :=
  fun ck ↦ (simulateQ (phiG h) (advSim r A (fixCrs r ps ck.2))).run' ∅

end Adversary

section Verify

variable (r : ℕ) {Crs Proof : Type}

/-- The argument for the relation of a hash `H`, from an argument for any relation. -/
def argH {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
        Proof rel)
    (H : List UInt8 → Common.DigestBytes) : WArgument r H Crs Proof :=
  ⟨ps.setup, ps.prove, ps.verify⟩

end Verify

section Final

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)

/-- Wagner's knowledge-soundness experiment for the table `h`: his reduction `ksReduction` from
`advH h`, against the argument `ps` for the relation with the hash `Hh h`. -/
noncomputable def ksExpH
    (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
        Crs Proof)
    (A : CodeBindingAdvB r Crs Proof) (h : HTab) : ProbComp Bool :=
  (argH r ps (Hh h)).knowledgeSoundnessExp ext (ksReduction (merkleVC r (Hh h)) (advH r ps A h))

/-- The collision experiment of `Hh h` against Wagner's weak-position-binding reduction from
`advH h`, through `merkleCollider`. -/
noncomputable def wpbCollExpH [NeZero r]
    (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
        Crs Proof)
    (A : CodeBindingAdvB r Crs Proof) (h : HTab) : ProbComp Bool :=
  hashCollisionExp (Hh h) (merkleCollider r (Hh h)
    ((wpbReduction (argH r ps (Hh h)) ext (advH r ps A h)).toPosBindingAdv (merkleVC r (Hh h))))

/-- The collision experiment of `Hh h` against Wagner's forking reduction from `advH h` (at most
`Q + 1` queries of the challenges), through `merkleCollider`. -/
noncomputable def forkCollExpH [NeZero r]
    (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
        Crs Proof)
    (A : CodeBindingAdvB r Crs Proof) (Q : ℕ) (h : HTab) : ProbComp Bool :=
  hashCollisionExp (Hh h) (merkleCollider r (Hh h)
    ((CommittedSoundness.forkCollisionReduction (leanDaErasureCode r) (merkleVC r (Hh h))
        (checker r)
      (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) (Q + 1)).toPosBindingAdv
        (merkleVC r (Hh h))))

end Final

end LeanDa

end
