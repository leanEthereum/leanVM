module

public import Statement.LeanDa
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.EvalDist.Inequalities

@[expose] public section

/-!
# Benedikt Wagner's framework: the definitions the proofs use

Benedikt Wagner's formalization (https://github.com/b-wagn/fv-pq-da), ported at 4475179c and
modified (`lean_da/NOTICE`): of his framework for erasure code commitments, the definitions
LeanDA's proofs use: his arguments of knowledge (`Nark`, oracle-free) and their
straight-line extractors, erasure codes, their codewords and the consistency of opened cells
(`ErasureCode`, `ErasureCode.code`, `ErasureCode.Consistent`).

Removed from this file when LeanDA's end statements stopped naming an argument of knowledge, and
kept in his repository: vector commitments and their adversaries, the erasure code commitment's
position-binding and code-binding adversaries, the random-oracle simulation of his reductions, the
relation of the scheme's argument, the knowledge-soundness experiment, and his reductions
(committed soundness, the fork and its collision, knowledge soundness and weak position binding).
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

/-- A straightline knowledge extractor: computes a witness from the crs, the
statement, and the proof alone (Foundations Definition 18). -/
def Extractor (Stmt Wit Crs Proof : Type) := Crs → Stmt → Proof → Wit

end Nark

end PqDas

end

section

namespace PqDas

/-- An erasure code with message alphabet `Γ`, code alphabet `Λ`, message
length `k`, and code length `n`, given by its encoding function. -/
structure ErasureCode (Γ Λ : Type) (k n : ℕ) where
  /-- The encoding function of the code. -/
  encode : (Fin k → Γ) → (Fin n → Λ)

namespace ErasureCode

variable {Γ Λ : Type} {k n : ℕ}

/-- A list of position/symbol pairs is *consistent* with the code if some
codeword agrees with all of them. The winning condition of the code-binding
game is the negation of this, for the pairs the adversary opened. -/
def Consistent (C : ErasureCode Γ Λ k n) (openings : List (Fin n × Λ)) : Prop :=
  ∃ m : Fin k → Γ, ∀ p ∈ openings, C.encode m p.1 = p.2

/-- Consistency is decidable for finite alphabets. -/
instance decidableConsistent (C : ErasureCode Γ Λ k n) [Fintype Γ] [DecidableEq Λ]
    (openings : List (Fin n × Λ)) : Decidable (C.Consistent openings) :=
  decidable_of_iff (∃ m : Fin k → Γ, ∀ p ∈ openings, C.encode m p.1 = p.2) Iff.rfl

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

