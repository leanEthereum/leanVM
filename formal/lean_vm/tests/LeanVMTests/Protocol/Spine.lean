import LeanVM.Protocol.Spine.Toy
import LeanVM.Protocol.Spine.Compose
import LeanVM.Protocol.PublicInput
import LeanVM.Protocol.ToArkLib.Refinement
import LeanVM.Protocol.ToArkLib.Typed.PassThrough

/-!
# Protocol spine tests

`M3Holds` on the toy: the honest stack passes, each of the four checkable clauses fails alone on
a stack with one cell changed (the public line on either of its two cells), and balance is a
multiset equality (a stack a field-summed balance would accept is rejected). The instance's
closed forms on the toy: one sumcheck table of height 2 and width 3, one constraint, two push
leaves, no boundary column, four pooled claims. The slots: the protocol's tree opens with the
stack as an oracle message, the errors along every path are bounded on the toy, and the numeric
bound on the whole protocol's error. The composition: the commitment's extractor reads the stack
back; the public-input phase fills its slot, so the master theorems have a bundle with a real
phase in it; a pass-through that keeps the statement is knowledge sound at any seam; a refinement
transports an extracted witness slot. A plain file, so `#guard` evaluates the compiled decision
procedures and the kernel computes degrees.
-/

namespace LeanVMTests.Protocol.Spine

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Toy CompPoly CPoly OracleComp
  Interaction Interaction.Oracle Interaction.Oracle.Security Typed
open scoped NNReal

/-! ## The toy instance is honest -/

-- The honest stack satisfies the relation at statement `1` (cell 0 of column 2 is `1`). The toy
-- has no padding row (its row count is its height), so its padding rows are honest vacuously.
#guard M3Holds toy (1: K) honest
#guard toy.PaddingHonest honest

-- Each clause can fail alone.

/-- Column 2 changed to `[2, 0]`, where `2 : K` is the polynomial `x`, not Boolean. At statement
`2`, so that the public line still holds, only the constraint clause fails. -/
def badConstraint : Column 3 := ⟨#v[1, 1, 1, 1, K.ofBits 2, 0, 0, 0]⟩

#guard ¬ toy.ConstraintsVanish badConstraint
#guard toy.Balanced badConstraint
#guard toy.CountsNonzero badConstraint
#guard toy.PublicLinesHold (K.ofBits 2 : K) badConstraint
#guard ¬ M3Holds toy (K.ofBits 2 : K) badConstraint

/-- Column 0 changed to `[1, 0]`: pushed `{1, 0}` against pulled `{1, 1}`, only balance fails. -/
def badBalance : Column 3 := ⟨#v[1, 0, 1, 1, 1, 0, 0, 0]⟩

#guard toy.ConstraintsVanish badBalance
#guard ¬ toy.Balanced badBalance
#guard toy.CountsNonzero badBalance
#guard toy.PublicLinesHold (1: K) badBalance
#guard ¬ M3Holds toy (1: K) badBalance

/-- Column 1 changed to `[1, 0]`: only the count clause fails. -/
def badCount : Column 3 := ⟨#v[1, 1, 1, 0, 1, 0, 0, 0]⟩

#guard toy.ConstraintsVanish badCount
#guard toy.Balanced badCount
#guard ¬ toy.CountsNonzero badCount
#guard toy.PublicLinesHold (1: K) badCount
#guard ¬ M3Holds toy (1: K) badCount

-- The honest stack at the wrong statement: only the public clause fails.
#guard toy.PublicLinesHold (1: K) honest
#guard ¬ toy.PublicLinesHold (0: K) honest
#guard ¬ M3Holds toy (0: K) honest

/-- Column 2 changed to `[1, 1]`: still Boolean, so the constraint holds, and balance and counts
are untouched; cell 1 of the public line is not `0`, so only the line clause fails. -/
def badLine : Column 3 := ⟨#v[1, 1, 1, 1, 1, 1, 0, 0]⟩

#guard toy.ConstraintsVanish badLine
#guard toy.Balanced badLine
#guard toy.CountsNonzero badLine
#guard ¬ toy.PublicLinesHold (1: K) badLine
#guard ¬ M3Holds toy (1: K) badLine

/-- Column 0 changed to `[0, 0]`: the pushed values `0, 0` against the pulled `1, 1`. Their
sum in `K` is `0` on both sides, so a field-summed balance (Clean's, over characteristic two)
would accept it; the multiset balance rejects it, and only it fails. -/
def badBalanceSum : Column 3 := ⟨#v[0, 0, 1, 1, 1, 0, 0, 0]⟩

#guard toy.ConstraintsVanish badBalanceSum
#guard ¬ toy.Balanced badBalanceSum
#guard toy.CountsNonzero badBalanceSum
#guard toy.PublicLinesHold (1: K) badBalanceSum
#guard ¬ M3Holds toy (1: K) badBalanceSum
-- The value coordinates of both sides sum to zero: the sum does not see the imbalance.
#guard ((toy.tuples badBalanceSum .push).map fun t ↦ t.get 1).sum =
  ((toy.tuples badBalanceSum .pull).map fun t ↦ t.get 1).sum

-- The toy has no Flock region, so its Flock predicate holds of every stack.
#guard toy.aux badBalanceSum

-- The layout reads the three slices, through the lift alone.
#guard (toy.column honest ⟨0, 0⟩).values = #v[1, 1]
#guard (toy.column honest ⟨0, 2⟩).values = #v[1, 0]
#guard toy.row honest 0 1 = ![1, 1, 0]
#guard boolIndex (toy.layout.extend ⟨0, 2⟩ (boolVec (1 : Fin 2))) = (5 : Fin 8)

-- One pushed tuple per row of the table, one pulled tuple per row of the boundary block; the
-- separator slot is `0`, slot 1 carries column 0, the other slots are zero.
#guard (toy.tuples honest .push).length = 2
#guard (toy.tuples honest .pull).length = 2
#guard toy.tuples honest .push = toy.tuples honest .pull
#guard (toy.tuples honest .push).map (fun t ↦ t.get 0) = [0, 0]
#guard (toy.tuples honest .push).map (fun t ↦ t.get 1) = [1, 1]
#guard (toy.tuples honest .push).map (fun t ↦ t.get 2) = [0, 0]

/-! ## What the schedule reads off the toy -/

-- The one table has a constraint, so it is a sumcheck table; its height is the largest.
#guard toy.SumcheckTable 0
example : toy.τmax = 1 := by decide
example : toy.B = 1 := by decide
-- Two push leaves (the flush on two rows), no pushing boundary block: leaf stacks of height 2.
example : toy.pushLeaves = 2 := by decide
example : toy.μBus = 1 := by decide
-- No committed boundary column; three table columns; one public line; no Flock claim.
example : toy.boundaryColumns = [] := by decide
example : toy.tableColumns = 3 := by decide
example : toy.poolSize = 4 := by decide

/-! ## The slots -/

/-- The protocol's tree opens with the stack as an oracle message, before the five phases. -/
example : (piopSlot toy).tree = .oracle (Column 3) fun _ ↦ (phasesSlot toy).tree := rfl

/-- The opening's slot is one challenge, at error `J - 1 = 3` over `|E|` on the toy. -/
example : (openingErrors toy).1 = overE 3 := rfl

/-- The bus phase's errors on the toy: `4 · 2` on `(α, β)` and the binary layer's `2 + 1`. -/
example : Errors.Bounded (busSlot toy).tree (busSlot toy).roles (busErrors toy)
    (overE (4 * 2 ^ 1 + ((1 + 1) * 2 + 2 * 1 * 1 + 3 * 1 + 3))) :=
  busErrors_bounded toy

/-- The toy has no Flock region: its Flock slot has no error. -/
example : Errors.Bounded (flockPhaseSlot toy).tree (flockPhaseSlot toy).roles (flockErrors toy)
    0 :=
  doneErrors_bounded

/-- The toy meets the hypotheses of the bound on the protocol's error. -/
example : Errors.Bounded (piopSlot toy).tree (piopSlot toy).roles (piopErrors toy)
    (overE (2 ^ 32 + 2 ^ 31 + 2 ^ 20)) :=
  piopErrors_bounded toy (by decide) (by decide) (by decide) (fun _ h ↦ by cases h) (by decide)

/-- The bound of `piopErrors_bounded`, with `|E| = 2^192`, is below `2^{-159}`. -/
example : overE (2 ^ 32 + 2 ^ 31 + 2 ^ 20) < 1 / 2 ^ 159 := by
  rw [overE, card_E]
  norm_num

/-! ## The composition -/

/-- The commitment's step of the whole protocol's extractor reads the stack off the message,
whatever the phases' extractors. -/
example (P : Phases toy) (S : P.Security) (s : K) (q : Column 3) :
    ((piopExtractor P S s) q).2.1 () = q := rfl

/-- The stack the whole protocol's extractor returns is the committed message, at every instance.
-/
example (I : M3Instance) (P : Phases I) (S : P.Security) (s : I.Stmt)
    (path : (piopSlot I).tree.ExecutionPath)
    (w : ((piopExtractor P S s).terminalState path).Witness) :
    (piopExtractor P S s).extractWitness path w = path.1 :=
  piopExtractedStack_eq P S s path w

/-- The public-input phase fills its slot: its two halves typecheck against the spine's seams
and at the slot's errors. -/
example : Typed.Complete (PublicInput.phase toy) (Seam.table toy) (Seam.pub toy) :=
  PublicInput.complete toy

example : Typed.Security (PublicInput.phase toy) (Seam.table toy) (Seam.pub toy) pubErrors :=
  PublicInput.security toy

/-- A bundle whose public-input phase is the built one has both master theorems, given the four
other phases' proofs: the slots line up. -/
example (P : Phases toy) (C : P.Complete) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (input : K) (q : Column 3)
    (h : ((input, fun i ↦ i.elim0), q) ∈ M3HonestRel toy) :
    Pr{let x ← (leanVmPiop P initial).execute impl input q}[x.2.2 = some ()] = 1 :=
  piop_perfectCompleteness P C initial impl input q h

example (P : Phases toy) (S : P.Security) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : K) :
    ∃ cert : KnowledgeCertificate (piopSlot toy).tree (piopSlot toy).roles
        ⟨Column 3, M3Holds toy s⟩,
      cert.extractor = piopExtractor P S s ∧
      cert.challenges = schedule (piopSlot toy).tree (piopSlot toy).roles (piopSlot toy).samplers
        (piopErrors toy) ∧
      SamplesChallenges unifSpec (QueryImpl.id' unifSpec) (piopSlot toy).tree (piopSlot toy).roles
        (piopSlot toy).oracles initial impl _ (leanVmVerifier P initial s) cert.challenges :=
  piop_knowledgeSoundness P S initial impl s

/-- A false acceptance has a bad challenge on its path, at every instance. -/
example (I : M3Instance) (P : Phases I) (S : P.Security) (s : I.Stmt)
    (path : (piopSlot I).tree.ExecutionPath) (hacc : piopVerdict P s path = some ())
    (hbad : ¬ M3Holds I s path.1) :
    RoundExtractor.BadChallengeOnPath (piopExtractor P S s) (piopSlot I).roles path
      (((piopTerminal P S s).witnessEquiv path).symm ()) :=
  piop_badChallenge P S s path hacc hbad

/-- A pass-through that keeps the statement is knowledge sound at any seam, at no error: the
identity at the public-input seam. -/
example : Typed.Security (passThrough (TheOracle toy) (id : K × PubOut toy → K × PubOut toy))
    (Seam.pub toy) (Seam.pub toy) doneErrors :=
  passThroughSecurity fun _ _ _ ↦ Iff.rfl

/-- The relation the protocol starts from is `M3Holds`, in ArkLib's shape. -/
example (input : K) (q : Column 3) :
    ((input, fun i : Fin 0 ↦ i.elim0), q) ∈ M3Rel toy ↔ M3Holds toy input q := Iff.rfl

/-- The commit seam pins the oracle to the witness of record. -/
example (input : K) (q : Column 3) :
    ((input, fun _ : Fin 1 ↦ q), ()) ∈ Seam.commit toy ↔ M3Holds toy input q := Iff.rfl

/-- Completeness starts from `M3Honest`: `M3Holds`, and every padding row holds its public row. -/
example (input : K) (q : Column 3) :
    ((input, fun i : Fin 0 ↦ i.elim0), q) ∈ M3HonestRel toy ↔
      M3Holds toy input q ∧ toy.PaddingHonest q := Iff.rfl

example (input : K) (q : Column 3) :
    ((input, fun _ : Fin 1 ↦ q), ()) ∈ Seam.commitHonest toy ↔ M3Honest toy input q := Iff.rfl

/-- The last seam leaves nothing to check. -/
example (o : ∀ i, TheOracle toy i) : (((), o), ()) ∈ Seam.done toy := trivial

/-- Before the question, the opened seam is the final claim holding of the stack. -/
example (c : WeightedClaim toy) (q : Column 3) :
    ((c, fun _ : Fin 1 ↦ q), ()) ∈ Seam.opened toy ↔ c.Holds q :=
  Seam.opened_iff toy c _ ()

/-! ## The bus seam bounds the degree of its row polynomials -/

/-- The toy's constraint is a row polynomial of the bus seam: degree at most `d = 2`. -/
example : toy.RowPoly 0 := ⟨constraint, by decide +kernel⟩

/-- The cubic `X₂³` is not: the bound is not vacuous at `d = 2`. -/
example : ¬ ((CMvPolynomial.X 2 * CMvPolynomial.X 2 * CMvPolynomial.X 2 :
    CMvPolynomial 3 K).totalDegree ≤ toy.d) := by decide +kernel

/-! ## Refinements -/

/-- A refinement transports an extracted witness slot: the doubled relation on `ℕ`. -/
def double :
    Refinement (Stmt := Unit) {p : Unit × ℕ | p.2 % 2 = 0} {p : Unit × ℕ | p.2 % 4 = 0} where
  map := fun _ w ↦ 2 * w
  map_valid := fun _ w h ↦ by simp only [Set.mem_ofPred_eq] at h ⊢; omega

example : ∀ w' ∈ (some 6).map (double.map ()), ((), w') ∈ {p : Unit × ℕ | p.2 % 4 = 0} :=
  double.map_option_valid () (some 6) (by decide)

end LeanVMTests.Protocol.Spine
