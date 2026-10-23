/-
# Non-interactive arguments of knowledge

Non-interactive arguments of knowledge with a straightline extractor, following
Foundations of Data Availability Sampling (eprint 2023/1079), Definitions 17
and 18. Modeling choices:

* the relation is `Bool`-valued rather than a `Prop`-valued relation with
  decidability assumptions; in our application the relation is decidable by
  construction (a commitment equality plus a code check);
* `prove` is deterministic; this holds for the instantiations of interest and
  nothing in the security proofs relies on it, but it keeps the scheme's
  commitment algorithm simpler;
* knowledge soundness is *straightline*: a universal extractor computes the
  witness from `(crs, stmt, π)` alone, and the adversary's advantage is the
  probability that the proof verifies while the extracted witness is invalid.
  There is no `∃ extractor` quantification: theorems take the extractor as a
  parameter and bound the advantage of an explicit reduction adversary.

The knowledge-soundness adversary is a plain probabilistic computation without
random-oracle access. Reductions from random-oracle games fit this interface by
simulating the random oracle for the outer adversary internally (lazy
sampling). Consequently, the argument system itself is modeled without any
random oracle; when instantiating it with a proof system that internally uses
one (e.g. for its own Fiat-Shamir transform), that oracle must be independent
of (domain-separated from) the oracle used elsewhere in the commitment scheme.

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import VCVio.CryptoFoundations.CommitmentScheme

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
