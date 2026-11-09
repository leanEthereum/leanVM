module

public import Statement.LeanDa
public import VCVio.CryptoFoundations.CommitmentScheme
public import VCVio.CryptoFoundations.ReplayFork
public import VCVio.OracleComp.Constructions.Fork.Basic
public import VCVio.OracleComp.HasQuery.Morphism
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.EvalDist.Inequalities
public import Mathlib.Data.Set.Finite.List

@[expose] public section

/-!
# Benedikt Wagner's framework: the definitions his proofs and reductions use

Benedikt Wagner's formalization (https://github.com/b-wagn/fv-pq-da), ported at 4475179c and
modified for VCVio afa6593: codewords of an erasure code, vector commitments and their
adversaries, code checkers, the code-binding adversary, the random-oracle simulation of his
reductions, the relation of the scheme's argument, and his reductions (committed soundness, the
fork and its collision, knowledge soundness and weak position binding). The erasure code's
consistency is in `Statement/LeanDa.lean`, which the end statements name; his arguments of
knowledge (`Nark`, oracle-free), moved back here when the end statements took arguments that
query the random-permutation model's oracles (`LeanDa.OracleArgument`), are below.
-/

section

open OracleComp ENNReal

namespace PqDas

/-- A non-interactive argument (of knowledge) for the `Bool`-valued relation
`rel`, with statement type `Stmt`, witness type `Wit`, common reference string
type `Crs`, and proof type `Proof` (Foundations Definition 18, with
deterministic `prove`). -/
structure Nark (Stmt Wit Crs Proof : Type) (rel : Stmt → Wit → Bool) where
  /-- Sample a common reference string. -/
  setup : ProbComp Crs
  /-- Produce a proof for `stmt` from witness `wit` (deterministic). -/
  prove : Crs → Stmt → Wit → Proof
  /-- Verify a proof (deterministic). -/
  verify : Crs → Stmt → Proof → Bool

namespace Nark

variable {Stmt Wit Crs Proof : Type} {rel : Stmt → Wit → Bool}

/-- Perfect completeness: honestly generated proofs for true statements verify. -/
def PerfectlyComplete (ps : Nark Stmt Wit Crs Proof rel) : Prop :=
  ∀ crs ∈ support ps.setup, ∀ stmt wit, rel stmt wit = true →
    ps.verify crs stmt (ps.prove crs stmt wit) = true

/-- A straightline knowledge extractor: computes a witness from the crs, the
statement, and the proof alone (Foundations Definition 18). -/
def Extractor (Stmt Wit Crs Proof : Type) := Crs → Stmt → Proof → Wit

variable {Stmt Wit Crs Proof : Type} {rel : Stmt → Wit → Bool}

/-- A knowledge-soundness adversary: outputs a statement and a proof. -/
def KnowledgeSoundnessAdv (Stmt Crs Proof : Type) := Crs → ProbComp (Stmt × Proof)

/-- Knowledge-soundness experiment (Foundations Definition 18): the adversary
wins if its proof verifies but the extracted witness does not satisfy the
relation. -/
def knowledgeSoundnessExp (ps : Nark Stmt Wit Crs Proof rel)
    (ext : Extractor Stmt Wit Crs Proof)
    (A : KnowledgeSoundnessAdv Stmt Crs Proof) : ProbComp Bool := do
  let crs ← ps.setup
  let (stmt, π) ← A crs
  return (ps.verify crs stmt π && !rel stmt (ext crs stmt π))

end Nark

end PqDas

end

section

namespace PqDas

namespace ErasureCode

variable {Γ Λ : Type} {k n : ℕ}

/-- The code itself: the set of codewords, i.e. the image of `encode`. -/
def code (C : ErasureCode Γ Λ k n) : Set (Fin n → Λ) := Set.range C.encode

/-- Codeword membership is decidable for finite alphabets. This is used to
state the winning conditions of security games as `Bool`s. -/
instance decidableMemCode (C : ErasureCode Γ Λ k n) [Fintype Γ] [DecidableEq Λ] :
    DecidablePred (· ∈ C.code) := fun c =>
  decidable_of_iff (∃ m, C.encode m = c) Set.mem_range

end ErasureCode

end PqDas

end

/-! ## Wagner's framework: vector commitments -/

section

open OracleComp ENNReal

namespace PqDas

/-- A vector commitment scheme for vectors in `Fin n → Λ`, with commitment key
type `Ck`, commitment type `Com`, and opening type `Opn` (Foundations
Definition 15, derandomized: `commit` and `openAt` are deterministic, and the
opening state is the committed vector itself, which is WLOG since `commit` is
deterministic). -/
structure VectorCommitment (Λ : Type) (n : ℕ) (Ck Com Opn : Type) where
  /-- Sample a commitment key. -/
  setup : ProbComp Ck
  /-- Commit to a vector (deterministic). -/
  commit : Ck → (Fin n → Λ) → Com
  /-- Open the commitment to position `i` (deterministic; takes the committed
  vector in place of an opening state). -/
  openAt : Ck → (Fin n → Λ) → Fin n → Opn
  /-- Verify an opening `τ` of symbol `x` at position `i` (deterministic). -/
  verify : Ck → Com → Fin n → Λ → Opn → Bool

namespace VectorCommitment

variable {Λ : Type} {n : ℕ} {Ck Com Opn : Type}

/-! #### Position-binding (Foundations Definition 16) -/

/-- A position-binding adversary: outputs a commitment, a position, and two
symbol/opening pairs. -/
def PosBindingAdv (Λ : Type) (n : ℕ) (Ck Com Opn : Type) :=
  Ck → ProbComp (Com × Fin n × Λ × Opn × Λ × Opn)

/-! #### Weak position-binding -/

/-- A weak position-binding adversary: outputs a full vector, a position, and a
symbol/opening pair. -/
def WeakPosBindingAdv (Λ : Type) (n : ℕ) (Ck Opn : Type) :=
  Ck → ProbComp ((Fin n → Λ) × Fin n × Λ × Opn)

/-- Reduction (an explicit PPT algorithm): a weak position-binding adversary
becomes a position-binding adversary by committing to `v` honestly and opening
position `i` honestly as the second symbol/opening pair. -/
def WeakPosBindingAdv.toPosBindingAdv (vc : VectorCommitment Λ n Ck Com Opn)
    (A : WeakPosBindingAdv Λ n Ck Opn) : PosBindingAdv Λ n Ck Com Opn := fun ck => do
  let (v, i, x, τ) ← A ck
  return (vc.commit ck v, i, x, τ, v i, vc.openAt ck v i)

/-! #### Collision resistance of `commit` -/

/-- A collision adversary: outputs two vectors, trying to make them collide
under the (deterministic) `commit`. -/
def CollisionAdv (Λ : Type) (n : ℕ) (Ck : Type) :=
  Ck → ProbComp ((Fin n → Λ) × (Fin n → Λ))

/-- Reduction (an explicit PPT algorithm): a collision adversary becomes a
position-binding adversary by locating a position where the two vectors differ
(`Fin.find`) and opening both honestly at that position. If the vectors do not
differ the adversary has lost anyway and we output a dummy tuple. -/
def CollisionAdv.toPosBindingAdv [NeZero n] [DecidableEq Λ]
    (vc : VectorCommitment Λ n Ck Com Opn) (A : CollisionAdv Λ n Ck) :
    PosBindingAdv Λ n Ck Com Opn := fun ck => do
  let (v, v') ← A ck
  if h : v = v' then
    return (vc.commit ck v, 0, v 0, vc.openAt ck v 0, v 0, vc.openAt ck v 0)
  else
    let i := Fin.find (fun j => v j ≠ v' j) (Function.ne_iff.mp h)
    return (vc.commit ck v, i, v i, vc.openAt ck v i, v' i, vc.openAt ck v' i)

end VectorCommitment

end PqDas

end

/-! ## Wagner's framework: code checkers -/

section

open OracleComp ENNReal

namespace PqDas

/-- A code checker for vectors in `Fin n → Λ` with check-randomness domain `L`:
a deterministic test `check`, intended to accept exactly-the-codewords with
high probability over `L`. -/
structure CodeChecker (Λ : Type) (n : ℕ) (L : Type) where
  /-- The (deterministic) membership check. -/
  check : L → (Fin n → Λ) → Bool

end PqDas

end

/-! ## Wagner's framework: the code-binding adversary of an erasure code commitment -/

section

open OracleComp ENNReal MeasureTheory

namespace PqDas

namespace ErasureCodeCommitment

/-! #### Code-binding (Foundations Definition 10) -/

/-- A code-binding adversary against an erasure code commitment whose algorithms run in the
monad `m`: outputs a commitment and a list of position/symbol/opening triples. Wagner's
reductions, which the code-binding bound names, take one. -/
def CodeBindingAdv (m : Type → Type) (Λ : Type) (n : ℕ) (Ck Com Opn : Type) :=
  Ck → m (Com × List (Fin n × Λ × Opn))

end ErasureCodeCommitment

end PqDas

end

/-! ## Wagner's framework: the random-oracle simulation of his reductions -/

section

open OracleComp OracleSpec ENNReal

namespace PqDas

section runtime

variable (ComVC L : Type) [DecidableEq ComVC] [SampleableType L]

/-- The query implementation underlying `simulateRom`: uniform-sampling queries are
forwarded, random-oracle queries are answered by lazy caching. -/
noncomputable def romImpl :
    QueryImpl (unifSpec + (ComVC →ₒ L)) (StateT ((ComVC →ₒ L).QueryCache) ProbComp) :=
  unifFwdImpl (ComVC →ₒ L) + (randomOracle :
    QueryImpl (ComVC →ₒ L) (StateT ((ComVC →ₒ L).QueryCache) ProbComp))

variable {ComVC L}

/-- Run a computation in the random-oracle world as a plain probabilistic
computation, lazily simulating the oracle starting from the given cache.
Reductions use this to simulate the random-oracle world for an adversary. -/
noncomputable def simulateRomWithCache (cache : (ComVC →ₒ L).QueryCache) {α : Type}
    (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) : ProbComp α :=
  (simulateQ (romImpl ComVC L) oa).run' cache

/-- Run a computation in the random-oracle world as a plain probabilistic
computation, with a fresh random oracle. -/
noncomputable def simulateRom {α : Type}
    (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) : ProbComp α :=
  simulateRomWithCache ∅ oa

variable {α β : Type}

end runtime

end PqDas

end

/-! ## Wagner's framework: the relation of the scheme's argument -/

section

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs Proof : Type}

/-- The relation proven by the argument of knowledge. The statement is a
commitment key, a commitment, and check randomness; the witness is an alleged
codeword `c`. The relation holds if `c` commits to the given commitment and
passes the code check. Note that code membership of `c` is *not* part of the
relation; this is the whole point of the construction, and the reason the
code-binding proof is nontrivial. -/
def schemeRel [DecidableEq ComVC] (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) : CkVC × ComVC × L → (Fin n → Λ) → Bool := fun stmt c =>
  decide (vc.commit stmt.1 c = stmt.2.1) && chk.check stmt.2.2 c

end PqDas

end

/-! ## Wagner's reductions: committed soundness -/

section

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

/-- An adversary against the non-interactive committed soundness game: given a
vector-commitment key and access to a random oracle (and uniform sampling), it
outputs a commitment and a vector. -/
def NiCsAdv (Λ : Type) (n : ℕ) (CkVC ComVC L : Type) :=
  CkVC → OracleComp (unifSpec + (ComVC →ₒ L)) (ComVC × (Fin n → Λ))

end PqDas

end

/-! ## Wagner's reductions: the fork -/

section

open OracleComp OracleSpec ENNReal

namespace PqDas

namespace CommittedSoundness

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

/-- Wrapped oracle spec: uniform sampling plus a single counted challenge
oracle exposing the random-oracle entropy. -/
abbrev wrappedSpec (L : Type) : OracleSpec (ℕ ⊕ Unit) := unifSpec + (Unit →ₒ L)

/-- Internal simulator state: the cached random-oracle answers paired with the
chronological list of cache-miss inputs. -/
abbrev SimState (ComVC L : Type) : Type := (ComVC →ₒ L).QueryCache × List ComVC

/-- Forwards a uniform-spec query to the wrapped spec's `Sum.inl` summand
without touching the simulator state. -/
def unifForward (ComVC L : Type) :
    QueryImpl unifSpec (StateT (SimState ComVC L) (OracleComp (wrappedSpec L))) :=
  fun i => (wrappedSpec L).query (Sum.inl i)

/-- Caching random-oracle implementation: on a cache hit the recorded answer
is returned; on a cache miss a fresh `Sum.inr ()` query is issued, the answer
is cached, and the miss input is appended to the internal log. -/
def roImpl (ComVC L : Type) [DecidableEq ComVC] :
    QueryImpl (ComVC →ₒ L) (StateT (SimState ComVC L) (OracleComp (wrappedSpec L))) :=
  fun com => do
    let (cache, log) ← get
    match cache com with
    | some v => pure v
    | none =>
        let v ← (wrappedSpec L).query (Sum.inr ())
        set (cache.cacheQuery com v, log ++ [com])
        pure v

/-- Trace of one run of the wrapped committed soundness game. -/
structure Trace (Λ : Type) (n : ℕ) (ComVC L : Type) where
  /-- The commitment output by the adversary. -/
  com : ComVC
  /-- The vector output by the adversary. -/
  vec : Fin n → Λ
  /-- The challenge for `com` (always cached, thanks to the wrapped
  computation's final query). -/
  chal : L
  /-- The final random-oracle cache. -/
  roCache : (ComVC →ₒ L).QueryCache
  /-- The chronological list of cache-miss inputs; the forking lemma rewinds
  at a position of this list. -/
  queryLog : List ComVC
  /-- Whether the run wins the committed soundness game. -/
  win : Bool

/-- The wrapped adversary: run the committed soundness adversary, then query
the oracle once more on the commitment it output, so its challenge is always
cached (and, on a miss, logged). -/
def wrappedAdv (A : NiCsAdv Λ n CkVC ComVC L) (ckVC : CkVC) :
    OracleComp (unifSpec + (ComVC →ₒ L)) (ComVC × (Fin n → Λ) × L) := do
  let (com, c) ← A ckVC
  let l ← HasQuery.query (spec := (ComVC →ₒ L)) com
  return (com, c, l)

/-- The winning predicate of the committed soundness game, as a function of
the wrapped adversary's output. -/
def winOn [Fintype Γ] [DecidableEq Λ] [DecidableEq ComVC]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (ckVC : CkVC) (out : ComVC × (Fin n → Λ) × L) : Bool :=
  decide (out.2.1 ∉ C.code) && chk.check out.2.2 out.2.1 &&
    decide (vc.commit ckVC out.2.1 = out.1)

/-- Run the wrapped adversary through the caching simulator against the
counted challenge oracle and record the run. -/
def runTrace [Fintype Γ] [DecidableEq Λ] [DecidableEq ComVC]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (ckVC : CkVC) :
    OracleComp (wrappedSpec L) (Trace Λ n ComVC L) := do
  let (out, st) ← StateT.run
    (simulateQ (unifForward ComVC L + roImpl ComVC L) (wrappedAdv A ckVC)) (∅, [])
  pure { com := out.1, vec := out.2.1, chal := out.2.2, roCache := st.1, queryLog := st.2,
         win := winOn C vc chk ckVC out }

/-- Rewinding point extracted from a trace: the position of the first cache
miss on the output commitment, provided the run wins and the position is
within the query budget. -/
def forkPoint [DecidableEq ComVC] (Q : ℕ) (trace : Trace Λ n ComVC L) :
    Option (Fin (Q + 1)) :=
  if trace.win then
    if trace.com ∈ trace.queryLog then
      let idx := trace.queryLog.findIdx (· == trace.com)
      if hidx : idx < Q + 1 then some ⟨idx, hidx⟩ else none
    else none
  else none

end CommittedSoundness

end PqDas

end

/-! ## Wagner's reductions: the collision from the fork -/

section

open OracleComp OracleSpec ENNReal

open scoped PFunctor

namespace PqDas

namespace CommittedSoundness

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

section forking

variable [DecidableEq ComVC] [SampleableType L] [Fintype L] [Inhabited L]
  [Fintype Γ] [DecidableEq Λ] [DecidableEq L] [Inhabited Λ]

variable (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
  (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (Q : ℕ)

/-- Wrapped-spec fork-and-extract computation: replay-fork the wrapped
committed soundness game at the fork point and output the two recorded
vectors. If the fork fails, output an (equal, hence losing) dummy pair. -/
noncomputable def forkVecPair (ckVC : CkVC) :
    OracleComp (wrappedSpec L) ((Fin n → Λ) × (Fin n → Λ)) :=
  contextFork (runTrace C vc chk A ckVC)
    (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
    (Sum.inr ()) (forkPoint Q) >>= fun
      | some (x₁, x₂) => pure (x₁.vec, x₂.vec)
      | none => pure (fun _ => default, fun _ => default)

/-- The collision reduction (an explicit algorithm): run the wrapped
fork-and-extract computation, interpreting its uniform queries and its counted
challenge oracle by plain uniform sampling. -/
noncomputable def forkCollisionReduction :
    VectorCommitment.CollisionAdv Λ n CkVC := fun ckVC =>
  simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      uniformSampleImpl (spec := ((Unit →ₒ L) : OracleSpec Unit)))
    (forkVecPair C vc chk A Q ckVC)

end forking

end CommittedSoundness

end PqDas

end

/-! ## Wagner's reductions: knowledge soundness and weak position binding -/

section

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs Proof : Type}

/-- The adversary's continuation shared by the reductions below: run the
code-binding adversary, then query the oracle once more on the commitment it
output (a cache hit if the adversary already queried it), obtaining the check
randomness that the scheme's verification would use. -/
def runWithChallenge
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn)
    (ck : CkVC × Crs) :
    OracleComp (unifSpec + (ComVC →ₒ L))
      (((ComVC × Proof) × List (Fin n × Λ × Opn)) × L) := do
  let out ← A ck
  let l ← HasQuery.query (spec := (ComVC →ₒ L)) out.1.1
  return (out, l)

/-- Reduction to knowledge soundness (an explicit PPT algorithm): sample the
vector-commitment key, simulate the random-oracle world for the code-binding
adversary, and output the statement `(ckVC, comVC, l)` together with the
adversary's proof. -/
noncomputable def ksReduction [DecidableEq ComVC] [SampleableType L]
    (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    Nark.KnowledgeSoundnessAdv (CkVC × ComVC × L) Crs Proof := fun crs => do
  let ckVC ← vc.setup
  let ((com, _), l) ← simulateRom (runWithChallenge A (ckVC, crs))
  return ((ckVC, com.1, l), com.2)

/-- Reduction to the non-interactive committed soundness game (an explicit PPT
algorithm): sample the crs, relay the code-binding adversary's oracle access,
and output the vector-commitment part of its commitment together with the
extracted witness. -/
noncomputable def csReduction [DecidableEq ComVC] [SampleableType L]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    NiCsAdv Λ n CkVC ComVC L := fun ckVC => do
  let crs ← liftM ps.setup
  let (com, _) ← A (ckVC, crs)
  let l ← HasQuery.query (spec := (ComVC →ₒ L)) com.1
  return (com.1, ext crs (ckVC, com.1, l) com.2)

/-- Reduction to weak position-binding (an explicit PPT algorithm): sample the
crs, simulate the random-oracle world for the code-binding adversary, extract
the witness `c` from its proof, and search its openings for one whose symbol
disagrees with `c`. If none disagrees the reduction has lost anyway and
outputs a dummy tuple. -/
noncomputable def wpbReduction [NeZero n] [DecidableEq Λ] [DecidableEq ComVC]
    [SampleableType L] [Inhabited Opn]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    VectorCommitment.WeakPosBindingAdv Λ n CkVC Opn := fun ckVC => do
  let crs ← ps.setup
  let ((com, openings), l) ← simulateRom (runWithChallenge A (ckVC, crs))
  let c := ext crs (ckVC, com.1, l) com.2
  match openings.find? (fun p => decide (p.2.1 ≠ c p.1)) with
  | some p => return (c, p.1, p.2.1, p.2.2)
  | none => return (c, 0, c 0, default)

end PqDas

end
