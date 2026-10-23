/-
# Erasure code commitments

Erasure code commitment schemes and their two binding notions, following
Foundations of Data Availability Sampling (eprint 2023/1079), Definitions 8-10.
An erasure code commitment is a vector commitment to codewords: one commits to
a *message*, and opens *positions of its encoding*; code-binding additionally
guarantees that whatever set of positions is opened, it is consistent with at
least one codeword.

The scheme's algorithms live in an ambient monad `m`. For the construction we
care about, `m` is an oracle computation monad providing a random oracle and
uniform sampling, and the security experiments are observed as
subdistributions through a `ProbCompRuntime m` which fixes the oracle
semantics (fresh lazily-sampled random oracle shared between the adversary and
the scheme's algorithms). Keeping `m` and the runtime abstract here follows
the conventions of VCVio (compare `SignatureAlg` and its experiments).

Deviations from the paper's definitions, both only strengthening the adversary:
* In the code-binding experiment the adversary outputs a *list* of
  position/symbol/opening triples rather than a family indexed by a set of
  positions. A list may repeat a position with different symbols, which no
  set-indexed family can; the security proofs go through unchanged.
* No lower bound is placed on the number of opened positions. (For codes where
  few symbols are always jointly consistent with some codeword, opening few
  positions simply cannot win.)

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import PqDas.Assumptions.ErasureCode
import VCVio.OracleComp.ProbCompLift

open OracleComp ENNReal MeasureTheory

namespace PqDas

/-- An erasure code commitment scheme for codes with code alphabet `Λ`, message
length `k`, and code length `n`, with commitment key type `Ck`, commitment type
`Com`, opening-state type `St`, and opening type `Opn` (Foundations
Definition 8). Algorithms run in the ambient monad `m`, which provides any
oracles they use (in particular a random oracle, for the scheme built later). -/
structure ErasureCodeCommitment (m : Type → Type) (Γ Λ : Type) (k n : ℕ)
    (Ck Com St Opn : Type) where
  /-- Sample a commitment key. -/
  setup : m Ck
  /-- Commit to a *message* (not a codeword), producing a commitment and an
  opening state. -/
  commit : Ck → (Fin k → Γ) → m (Com × St)
  /-- Open position `i` of the *encoding* of the committed message. -/
  openAt : Ck → St → Fin n → m Opn
  /-- Verify an opening `τ` of codeword symbol `x` at position `i`. -/
  verify : Ck → Com → Fin n → Λ → Opn → m Bool

namespace ErasureCodeCommitment

variable {m : Type → Type} [Monad m] {Γ Λ : Type} {k n : ℕ} {Ck Com St Opn : Type}

/-- Perfect completeness w.r.t. the code `C`: for every message and position,
committing, opening, and verifying the corresponding symbol of the encoding
always succeeds (Foundations Definition 8, with zero error). -/
def PerfectlyComplete (cc : ErasureCodeCommitment m Γ Λ k n Ck Com St Opn)
    (C : ErasureCode Γ Λ k n) (runtime : ProbCompRuntime m) : Prop :=
  ∀ (msg : Fin k → Γ) (i : Fin n),
    runtime.evalDist (do
      let ck ← cc.setup
      let (com, st) ← cc.commit ck msg
      let τ ← cc.openAt ck st i
      cc.verify ck com i (C.encode msg i) τ) {true} = 1

/-! ### Position-binding (Foundations Definition 9) -/

/-- A position-binding adversary: outputs a commitment, a position, and two
symbol/opening pairs. It runs in the same ambient monad `m` as the scheme, so
in the random-oracle instantiation it shares the scheme's random oracle. -/
def PosBindingAdv (m : Type → Type) (Λ : Type) (n : ℕ) (Ck Com Opn : Type) :=
  Ck → m (Com × Fin n × Λ × Opn × Λ × Opn)

/-- Position-binding experiment (Foundations Definition 9): the adversary wins
if it opens the same commitment at the same position to two different symbols.
The runtime threads one oracle state through the adversary and both
verifications. -/
noncomputable def posBindingExp [DecidableEq Λ]
    (cc : ErasureCodeCommitment m Γ Λ k n Ck Com St Opn)
    (runtime : ProbCompRuntime m) (A : PosBindingAdv m Λ n Ck Com Opn) : Measure Bool :=
  runtime.evalDist do
    let ck ← cc.setup
    let (com, i, x, τ, x', τ') ← A ck
    let b ← cc.verify ck com i x τ
    let b' ← cc.verify ck com i x' τ'
    return (decide (x ≠ x') && b && b')

/-! ### Code-binding (Foundations Definition 10) -/

/-- A code-binding adversary: outputs a commitment and a list of
position/symbol/opening triples. -/
def CodeBindingAdv (m : Type → Type) (Λ : Type) (n : ℕ) (Ck Com Opn : Type) :=
  Ck → m (Com × List (Fin n × Λ × Opn))

/-- Code-binding experiment (Foundations Definition 10): the adversary wins if
all its openings verify but no codeword is consistent with the opened
position/symbol pairs. -/
noncomputable def codeBindingExp [Fintype Γ] [DecidableEq Λ]
    (cc : ErasureCodeCommitment m Γ Λ k n Ck Com St Opn) (C : ErasureCode Γ Λ k n)
    (runtime : ProbCompRuntime m) (A : CodeBindingAdv m Λ n Ck Com Opn) : Measure Bool :=
  runtime.evalDist do
    let ck ← cc.setup
    let (com, openings) ← A ck
    let verdicts ← openings.mapM fun p => cc.verify ck com p.1 p.2.1 p.2.2
    return (verdicts.all id &&
      !decide (C.Consistent (openings.map fun p => (p.1, p.2.1))))

end ErasureCodeCommitment

end PqDas
