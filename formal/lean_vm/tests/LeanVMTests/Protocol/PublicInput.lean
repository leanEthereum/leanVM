import LeanVM.Protocol.PublicInput
import LeanVM.Protocol.Spine.Toy
import LeanVM.Protocol.Spine.Compose

/-!
# Public-input phase tests

Every guard changes one thing.

* **The point.** `linePoint` is `(r, 0)` on two variables, and the extension there is the line
  through cells 0 and 1, not through cells 2 and 3.
* **The check**, on the toy, whose one public line is column 2 with cells `(statement, 0)`: it
  accepts the line's value and rejects a wrong value, a missing value and an extra value.
* **A wrong stack.** On `badLine`, whose cell 1 differs from the statement's, a prover that sends
  its column's true evaluation is rejected by the check, except at the one bad challenge
  `r = 0`; and the pooled claim is false of that stack, except at that challenge. A wrong
  statement behaves the same way, with bad challenge `r = 1`.
* **Which values are sent.** With no value sent, the shape of the leanISA instance and of the
  deployed verifiers (leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`), the message is empty
  and the line is still pooled, at the value the verifier computes. On three lines shaped like
  the memory limbs, two values sent and a third line with cells `(0, 0)`, a stack with a nonzero
  top cell passes the check and fails the third claim, and the pool without the third claim
  accepts it.
* **Two sent lines.** The check per limb rejects a wrong stack's true values, a message that is
  not the expected values, and a message of another length.
* **The pool reads the message.** A wrong value that passes no check is what the pool would
  carry; at the expected values the pool from the message is the pool of the lines' claims; a
  message without one value per sent line is rejected before any check.
* **The phase** fills its slot: two rounds, a challenge then a message, its verdict a function of
  the path alone, and its two halves typecheck against the spine's seams at the slot's errors.
* **The check is load-bearing.** On a statement outside the table seam, a prover that sends its
  stack's true values is accepted with a pool inside the public seam by the verifier without
  the check, by the verifier that checks the first value only, by the verifier that pools an
  unsent line's claim at zero, and by the one that pools it at the constant zero where the line
  is not zero; so none of them has a round-by-round knowledge error below one, whatever extractor
  it is given. The verifier whose check swaps the two cells, and the one with an extra check on
  the message's length, reject the honest prover: neither is complete. The bound `1/|E|` is attained at one challenge.

The toy's table seam carries three received claims, one per column of its table; the fixtures
give them true values at a cube point. A plain file, so `#guard` evaluates the compiled
definitions. Values of `E` written with numerals are named as definitions before a guard uses
them.
-/

namespace LeanVMTests.Protocol.PublicInput

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.PublicInput LeanVM.Protocol.Toy
  CompPoly OracleComp

/-- A column claim is decided by evaluating the column's extension. Spelled with
`inferInstanceAs` on the unfolded equation: the instance `by unfold ColumnClaim.Holds;
infer_instance` elaborates but does not terminate under `#guard`. -/
instance {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable (CMlPolynomialEval.eval₂Mle (I.column q c.col).values
    (algebraMap K E) c.point = c.value))

/-- What a prover that answers truthfully sends: the extensions of its own columns at
`(r, 0, …, 0)`, for the lines whose value is sent. -/
def trueValues (I : M3Instance) (q : Column I.μ) (input : I.Stmt) (r : E) : List E :=
  ((I.publicLines input).toList.filter (·.sent)).map fun l ↦
    CMlPolynomialEval.eval₂Mle (I.column q l.col).values (algebraMap K E) (linePoint l.pos r)

/-- A truthful prover's message has one value per sent line. -/
theorem trueValues_length (I : M3Instance) (q : Column I.μ) (input : I.Stmt) (r : E) :
    (trueValues I q input r).length = sentCount I (I.publicLines input) :=
  List.length_map ..

/-- Three received claims on the three columns of an instance's first table, at the cube point
`x`, with the given values: what the table seam carries into the phase. -/
def received (I : M3Instance) (h : I.tableClaims = 3) (h0 : 0 < I.ntab)
    (hw : 3 ≤ I.width ⟨0, h0⟩) (hτ : I.τ ⟨0, h0⟩ = 1) (x : Fin 2) (v : Fin 3 → K) :
    Vector (ColumnClaim I) I.tableClaims :=
  Vector.cast h.symm (Vector.ofFn fun i ↦
    ⟨⟨⟨0, h0⟩, ⟨i.val, by omega⟩⟩, Vector.cast hτ.symm (boolVec x), ofK (v i)⟩)

/-! ## The point -/

/-- The table `[1, 2, 3, 4]` on two variables. -/
def table : CMlPolynomialEval K 2 := #v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4]

/-- The point `(y, 0)`. -/
def onLine : List E := [y, 0]

/-- The point `(y, 1)`: second coordinate `1`. -/
def offLine : Vector E 2 := #v[y, ofK 1]

#guard (linePoint (n := 2) (by decide) y).toList = onLine
-- On the line: `(1 - y)·1 + y·2`, the line through cells 0 and 1.
#guard CMlPolynomialEval.eval₂Mle table (algebraMap K E) (linePoint (n := 2) (by decide) y) =
  (1 - y) * ofK 1 + y * ofK (K.ofBits 2)
-- Off the line the second coordinate selects cells 2 and 3.
#guard CMlPolynomialEval.eval₂Mle table (algebraMap K E) offLine =
  (1 - y) * ofK (K.ofBits 3) + y * ofK (K.ofBits 4)
#guard CMlPolynomialEval.eval₂Mle table (algebraMap K E) offLine ≠
  (1 - y) * ofK 1 + y * ofK (K.ofBits 2)

/-! ## The check -/

/-- A second sampled challenge, `y² + 1`. -/
def r₂ : E := y * y + 1

/-- The toy's statement `1` with the three columns' cells 0 received. -/
def stmt1 : K × TableOut toy :=
  (1, ⟨received toy (by decide) (by decide) (by decide) (by decide) 0 ![1, 1, 1]⟩)

/-- The toy's statement `0` with the same received claims. -/
def stmt0 : K × TableOut toy :=
  (0, ⟨received toy (by decide) (by decide) (by decide) (by decide) 0 ![1, 1, 1]⟩)

/-- The value of the toy's line at statement `1` and challenge `y`: `(1 + y)·1 + y·0`. -/
def good : List E := [1 + y]

/-- A wrong value. -/
def wrong : List E := [y]

/-- One value too many. -/
def extra : List E := [1 + y, 0]

-- The expected value of the one line, and the check on it.
#guard expectedValues toy (1: K) y = good
-- The check accepts the value and rejects a wrong, a missing and an extra value.
#guard check toy stmt1 y good
#guard ¬ check toy stmt1 y wrong
#guard ¬ check toy stmt1 y []
#guard ¬ check toy stmt1 y extra

-- On the honest stack, a prover that answers truthfully sends the expected values.
#guard trueValues toy honest (1: K) y = expectedValues toy (1: K) y
#guard trueValues toy honest (1: K) r₂ = expectedValues toy (1: K) r₂
#guard trueValues toy honest (1: K) 0 = expectedValues toy (1: K) 0

/-! ## A wrong stack -/

/-- Column 2 changed to `[1, 1]`: cell 1 is not the statement's `0`. -/
def badLine : Column 3 := ⟨#v[1, 1, 1, 1, 1, 1, 0, 0]⟩

-- A prover that sends its column's true evaluation is rejected by the check at a sampled
-- challenge, and accepted at the one bad challenge `r = 0`, where the line is cell 0 alone.
#guard ¬ check toy stmt1 y (trueValues toy badLine 1 y)
#guard ¬ check toy stmt1 r₂ (trueValues toy badLine 1 r₂)
#guard check toy stmt1 0 (trueValues toy badLine 1 0)

-- The same event on the claims: every pooled claim holds of the honest stack; of the wrong
-- stack one fails at a sampled challenge, and all hold at the bad challenge. So the bound
-- `1/|E|` is attained, and a prover that sends the expected value passes the check with a
-- claim that is false of its stack.
#guard ∀ c ∈ (pooled toy stmt1 y).2.columns.toList, c.Holds honest
#guard ¬ ∀ c ∈ (pooled toy stmt1 y).2.columns.toList, c.Holds badLine
#guard ∀ c ∈ (pooled toy stmt1 0).2.columns.toList, c.Holds badLine

-- A wrong statement (cell 0 is `0`, the honest stack's is `1`): rejected at a sampled
-- challenge, accepted at the one bad challenge `r = 1`, where `(1 + r)·cell0` vanishes.
#guard ¬ check toy stmt0 y (trueValues toy honest 0 y)
#guard check toy stmt0 1 (trueValues toy honest 0 1)

/-! ## The pool -/

-- The verifier keeps the statement and pools the received claims first, then the line.
#guard (pooled toy stmt1 y).1 = 1
#guard ((pooled toy stmt1 y).2.columns.toList.map fun c ↦ c.col) =
  [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 2⟩]
#guard ((pooled toy stmt1 y).2.columns.toList.map fun c ↦ c.value) = [1, 1, 1] ++ good
-- The pool the verifier builds reads the message: at the expected values it is the pool of
-- the lines' claims, and at a wrong value it carries that value, which is why the check must
-- reject it.
#guard ((pooledFrom toy stmt1 y good rfl).2.columns.toList.map fun c ↦ c.value) =
  ((pooled toy stmt1 y).2.columns.toList.map fun c ↦ c.value)
#guard ((pooledFrom toy stmt1 y wrong rfl).2.columns.toList.map fun c ↦ c.value) =
  [1, 1, 1] ++ wrong
#guard ¬ ∀ c ∈ (pooledFrom toy stmt1 y wrong rfl).2.columns.toList, c.Holds honest
-- A message without one value per sent line is rejected by every verifier of the phase's
-- shape, the one without a check included.
#guard accepts toy (check toy) stmt1 y good
#guard ¬ accepts toy (fun _ _ _ ↦ true) stmt1 y extra
#guard ¬ accepts toy (fun _ _ _ ↦ true) stmt1 y []

/-! ## Which values are sent -/

/-- The toy with its line's value not sent. -/
abbrev noneSent : M3Instance :=
  { toy with publicLines := fun v ↦ #v[⟨⟨0, 2⟩, v, 0, false, by decide⟩] }

/-- Its statement `1` with the received claims. -/
def stmtNone : K × TableOut noneSent :=
  (1, ⟨received noneSent (by decide) (by decide) (by decide) (by decide) 0 ![1, 1, 1]⟩)

-- The message is empty, a value is rejected, and the line is pooled all the same.
#guard expectedValues noneSent (1: K) y = []
#guard check noneSent stmtNone y []
#guard ¬ check noneSent stmtNone y good
#guard ((pooled noneSent stmtNone y).2.columns.toList.map fun c ↦ c.value) = [1, 1, 1] ++ good
#guard ¬ ∀ c ∈ (pooled noneSent stmtNone y).2.columns.toList, c.Holds badLine

/-- Three lines shaped like the memory limbs: two with their value sent, and a third with cells
`(0, 0)` and no value sent. -/
abbrev threeLimbs : M3Instance :=
  { toy with
    nLines := 3
    publicLines := fun v ↦
      #v[⟨⟨0, 0⟩, v, 1, true, by decide⟩, ⟨⟨0, 1⟩, 1, 1, true, by decide⟩,
        ⟨⟨0, 2⟩, 0, 0, false, by decide⟩] }

/-- Its statement `1` with the three columns' cells 1 received. -/
def stmtLimbs : K × TableOut threeLimbs :=
  (1, ⟨received threeLimbs (by decide) (by decide) (by decide) (by decide) 1 ![1, 1, 0]⟩)

/-- A stack whose three columns hold their lines: `[1, 1]`, `[1, 1]`, `[0, 0]`. -/
def goodLimbs : Column 3 := ⟨#v[1, 1, 1, 1, 0, 0, 0, 0]⟩

/-- The top column's cell 0 changed to `1`. -/
def badTopLimb : Column 3 := ⟨#v[1, 1, 1, 1, 1, 0, 0, 0]⟩

/-- The three lines' values at any challenge: `(1 + r) + r`, twice, and `0`. -/
def limbValues : List E := [1, 1, 0]

-- Two values are sent and three claims are pooled after the received ones, the third with
-- value `0`.
#guard (expectedValues threeLimbs (1: K) y).length = 2
#guard ((pooled threeLimbs stmtLimbs y).2.columns.toList.map fun c ↦ c.value).drop 3 =
  limbValues
#guard ((pooled threeLimbs stmtLimbs y).2.columns.toList.map fun c ↦ c.col).drop 3 =
  [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩]
#guard ∀ c ∈ (pooled threeLimbs stmtLimbs y).2.columns.toList, c.Holds goodLimbs
-- The wrong top cell passes the check, which sees the two sent values only, and fails the third
-- claim; the pool without the third claim accepts the stack.
#guard check threeLimbs stmtLimbs y (trueValues threeLimbs badTopLimb 1 y)
#guard ¬ ∀ c ∈ (pooled threeLimbs stmtLimbs y).2.columns.toList, c.Holds badTopLimb
#guard ∀ c ∈ ((pooled threeLimbs stmtLimbs y).2.columns.toList.take 5), c.Holds badTopLimb

/-! ## Two sent lines -/

/-- Two limbs with zero public words, both values sent. -/
abbrev twoLimbs : M3Instance :=
  { toy with
    nLines := 2
    publicLines := fun _ ↦
      #v[⟨⟨0, 0⟩, 0, 0, true, by decide⟩, ⟨⟨0, 1⟩, 0, 0, true, by decide⟩] }

/-- Its statement with the received claims. -/
def stmtTwo : K × TableOut twoLimbs :=
  (0, ⟨received twoLimbs (by decide) (by decide) (by decide) (by decide) 0 ![0, 1, 0]⟩)

/-- A stack whose two limbs are `[0, 1]` and `[1, 0]`: both violate the public input. -/
def badLimbs : Column 3 := ⟨#v[0, 1, 1, 0, 0, 0, 0, 0]⟩

/-- The challenge `y / (1 + y)`. -/
def rStar : E := y / (1 + y)

/-- The two true evaluations at that challenge: `r` and `1 + r`. -/
def atStar : List E := [rStar, 1 + rStar]

#guard trueValues twoLimbs badLimbs 0 rStar = atStar
-- The check per limb rejects the true evaluations of a wrong stack, at that challenge and at a
-- sampled one, and a message that is not the expected values.
#guard ¬ check twoLimbs stmtTwo rStar atStar
#guard ¬ check twoLimbs stmtTwo y (trueValues twoLimbs badLimbs 0 y)
#guard check twoLimbs stmtTwo y (expectedValues twoLimbs (0 : K) y)
#guard ¬ check twoLimbs stmtTwo y [y, 1]
-- With two sent lines the message has two values: any other length is rejected.
#guard ¬ check twoLimbs stmtTwo y []
#guard ¬ check twoLimbs stmtTwo y [0]
#guard ¬ check twoLimbs stmtTwo y [0, 0, 0]

/-! ## The phase in its slot -/

/-- Two rounds: the challenge, then the prover's values, which the verdict reads and nothing
else; the slot's error is `1/|E|` on the one challenge. -/
example : pubSlot.tree = .public E fun _ ↦ .public (List E) fun _ ↦ .done := rfl

example : pubErrors = (overE 1, fun _ _ ↦ PUnit.unit) := rfl

/-- The two halves typecheck against the two seams, at the slot's errors. -/
example : Typed.Complete (phase toy) (Seam.table toy) (Seam.pub toy) := complete toy

example : Typed.Security (phase toy) (Seam.table toy) (Seam.pub toy) pubErrors := security toy

/-- The phase is one field of a bundle: with the four other phases and their proofs, the master
completeness theorem applies. -/
example (P : Phases toy) (C : P.Complete) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (input : K) (q : Column toy.μ)
    (h : ((input, fun i ↦ i.elim0), q) ∈ M3HonestRel toy) :
    Pr{let x ← (leanVmPiop P initial).execute impl input q}[x.2.2 = some ()] = 1 :=
  piop_perfectCompleteness P C initial impl input q h

/-! ## The check is load-bearing -/

section Refutations

open OracleComp OracleSpec
open scoped NNReal

/-- Three received claims true of a stack by construction: the three columns of the first
table at the cube point `0`, each at the value its extension takes there. -/
def receivedTrue (I : M3Instance) (h : I.tableClaims = 3) (h0 : 0 < I.ntab)
    (hw : 3 ≤ I.width ⟨0, h0⟩) (hτ : I.τ ⟨0, h0⟩ = 1) (q : Column I.μ) :
    Vector (ColumnClaim I) I.tableClaims :=
  Vector.cast h.symm (Vector.ofFn fun i : Fin 3 ↦
    ⟨⟨⟨0, h0⟩, ⟨i.val, by omega⟩⟩, Vector.cast hτ.symm (boolVec 0),
      CMlPolynomialEval.eval₂Mle (I.column q ⟨⟨0, h0⟩, ⟨i.val, by omega⟩⟩).values
        (algebraMap K E) (Vector.cast hτ.symm (boolVec 0))⟩)

theorem receivedTrue_holds (I : M3Instance) (h : I.tableClaims = 3) (h0 : 0 < I.ntab)
    (hw : 3 ≤ I.width ⟨0, h0⟩) (hτ : I.τ ⟨0, h0⟩ = 1) (q : Column I.μ) :
    ∀ c ∈ (receivedTrue I h h0 hw hτ q).toList, c.Holds q := by
  intro c hc
  simp only [receivedTrue, Vector.toList_cast, Vector.toList_ofFn, List.mem_ofFn] at hc
  obtain ⟨i, rfl⟩ := hc
  rfl

/-- A stack as the one oracle. -/
def oracleOf {I : M3Instance} (q : Column I.μ) : ∀ i, TheOracle I i := fun _ ↦ q

/-- An instance without a Flock region has nothing to hold there. -/
theorem aux_of_none {I : M3Instance} (h : I.flock = none) (q : Column I.μ) : I.aux q := by
  intro r hr
  rw [h] at hr
  exact (Option.not_mem_none r hr).elim

/-- The path through the phase with challenge `c` and message `m`: no challenge after `c`. -/
abbrev restOf (m : List E) :
    (Interaction.Oracle.TypeTree.public (List E) fun _ ↦ .done).ExecutionPath :=
  ⟨m, PUnit.unit⟩

/-! ### The check removed -/

/-- The phase that accepts every message and pools the values sent. -/
abbrev noCheck := phaseWith toy (fun _ _ _ ↦ true) (pooledFrom toy)

/-- The statement `1` with the received claims true of `badLine`, whose line fails. -/
def stmtBad : K × TableOut toy :=
  (1, ⟨receivedTrue toy (by decide) (by decide) (by decide) (by decide) badLine⟩)

theorem stmtBad_not_table : ((stmtBad, oracleOf badLine), ()) ∉ Seam.table toy :=
  fun h ↦ absurd (h.2.1 ⟨⟨0, 2⟩, 1, 0, true, by decide⟩ (by simp [stmtBad])).2 (by decide)

/-- At every challenge, the verdict on the true values of `badLine` is in the public seam. -/
theorem noCheck_pub (c : E) :
    ((verdict toy (pooledFrom toy) stmtBad c (trueValues toy badLine 1 c), oracleOf badLine),
      ()) ∈ Seam.pub toy := by
  refine ⟨fun cl hcl ↦ ?_, aux_of_none rfl _⟩
  rw [verdict, dite_eq_left (show (trueValues toy badLine 1 c).length =
    sentCount toy (toy.publicLines stmtBad.1) from trueValues_length toy badLine 1 c)] at hcl
  simp only [pooledFrom, Vector.toList_append, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · exact receivedTrue_holds toy (by decide) (by decide) (by decide) (by decide) badLine cl hcl
  · simp only [claimsFrom, claimsWith, Vector.toList_ofFn, List.mem_ofFn] at hcl
    obtain ⟨i, rfl⟩ := hcl
    fin_cases i
    rfl

/-- Without the check there is no round-by-round knowledge error below one: at `stmtBad`, a
prover that sends its stack's true value at any challenge is accepted with a pool inside the
public seam. Whatever the extractor. -/
example {err : Typed.Errors pubSlot.tree pubSlot.roles}
    (S : Typed.Security noCheck (Seam.table toy) (Seam.pub toy) err) : 1 ≤ err.1 :=
  S.one_le_of_escape stmtBad (oracleOf badLine) (fun _ h ↦ stmtBad_not_table h) fun c ↦
    ⟨restOf (trueValues toy badLine 1 c), trivial, _, (),
      (@verdictWith_of_accepts toy (fun _ _ _ ↦ true) (pooledFrom toy) stmtBad c
        (trueValues toy badLine 1 c) (by
          simp only [accepts, Bool.and_true, decide_eq_true_eq]
          exact trueValues_length toy badLine 1 c)), noCheck_pub c⟩

/-! ### The check weakened to its first value -/

/-- The phase that checks the first value only, on `twoLimbs`. -/
abbrev firstOnly := phaseWith twoLimbs
  (fun s r cs ↦ decide (cs.head? = (expectedValues twoLimbs s.1 r).head?)) (pooledFrom twoLimbs)

/-- Limb 0 is `[0, 0]`, as its line says; limb 1 is `[1, 0]`, against its line. -/
def oneBadLimb : Column 3 := ⟨#v[0, 0, 1, 0, 0, 0, 0, 0]⟩

/-- The statement `0` with the received claims true of `oneBadLimb`. -/
def stmtOneBad : K × TableOut twoLimbs :=
  (0, ⟨receivedTrue twoLimbs (by decide) (by decide) (by decide) (by decide) oneBadLimb⟩)

theorem stmtOneBad_not_table : ((stmtOneBad, oracleOf oneBadLimb), ()) ∉ Seam.table twoLimbs :=
  fun h ↦ absurd (h.2.1 ⟨⟨0, 1⟩, 0, 0, true, by decide⟩ (by simp)).1 (by decide)

/-- The message that passes the first-value check: the expected value of limb 0, then the true
value of limb 1 on `oneBadLimb`, the line through its cells `1, 0` at `c`. -/
def firstOnlyMsg (c : E) : List E :=
  [lineValue twoLimbs c ⟨⟨0, 0⟩, 0, 0, true, by decide⟩, 1 - c]

theorem firstOnly_pub (c : E) :
    ((verdict twoLimbs (pooledFrom twoLimbs) stmtOneBad c (firstOnlyMsg c), oracleOf oneBadLimb),
      ()) ∈ Seam.pub twoLimbs := by
  have c0 : (twoLimbs.column oneBadLimb ⟨0, 0⟩).values.get ⟨0, by decide⟩ = 0 := by decide
  have c1 : (twoLimbs.column oneBadLimb ⟨0, 0⟩).values.get ⟨1, by decide⟩ = 0 := by decide
  have d0 : (twoLimbs.column oneBadLimb ⟨0, 1⟩).values.get ⟨0, by decide⟩ = 1 := by decide
  have d1 : (twoLimbs.column oneBadLimb ⟨0, 1⟩).values.get ⟨1, by decide⟩ = 0 := by decide
  refine ⟨fun cl hcl ↦ ?_, aux_of_none rfl _⟩
  rw [verdict, dite_eq_left (show (firstOnlyMsg c).length =
    sentCount twoLimbs (twoLimbs.publicLines stmtOneBad.1) from rfl)] at hcl
  simp only [pooledFrom, Vector.toList_append, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · exact receivedTrue_holds twoLimbs (by decide) (by decide) (by decide) (by decide) oneBadLimb
      cl hcl
  · simp only [claimsFrom, claimsWith, Vector.toList_ofFn, List.mem_ofFn] at hcl
    obtain ⟨i, rfl⟩ := hcl
    fin_cases i
    · show CMlPolynomialEval.eval₂Mle (twoLimbs.column oneBadLimb ⟨0, 0⟩).values
        (algebraMap K E) (linePoint (by decide) c) = lineValue twoLimbs c _
      rw [eval₂Mle_linePoint, c0, c1]
      simp [lineValue]
    · show CMlPolynomialEval.eval₂Mle (twoLimbs.column oneBadLimb ⟨0, 1⟩).values
        (algebraMap K E) (linePoint (by decide) c) = 1 - c
      rw [eval₂Mle_linePoint, d0, d1]
      simp

/-- Checking the first value only leaves no round-by-round knowledge error below one: the
second value is pooled unchecked. -/
example {err : Typed.Errors pubSlot.tree pubSlot.roles}
    (S : Typed.Security firstOnly (Seam.table twoLimbs) (Seam.pub twoLimbs) err) : 1 ≤ err.1 :=
  S.one_le_of_escape stmtOneBad (oracleOf oneBadLimb) (fun _ h ↦ stmtOneBad_not_table h)
    fun c ↦ ⟨restOf (firstOnlyMsg c), trivial, _, (),
      (@verdictWith_of_accepts twoLimbs
        (fun s r cs ↦ decide (cs.head? = (expectedValues twoLimbs s.1 r).head?))
        (pooledFrom twoLimbs) stmtOneBad c (firstOnlyMsg c) (by
          simp only [accepts, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨rfl, by simp [firstOnlyMsg, expectedValues]⟩)), firstOnly_pub c⟩

/-! ### An unsent line's claim dropped -/

/-- The pool with an unsent line's claim at zero, as if that claim were dropped, on
`noneSent`. -/
def poolDropped (s : K × TableOut noneSent) (r : E) (cs : List E)
    (h : cs.length = sentCount noneSent (noneSent.publicLines s.1)) : K × PubOut noneSent :=
  (s.1, ⟨s.2.columns ++ claimsWith noneSent r (fun _ ↦ 0) (noneSent.publicLines s.1) cs h⟩)

/-- The phase with the check and the dropped claim. -/
abbrev dropped := phaseWith noneSent (check noneSent) poolDropped

/-- The statement `1` with the received claims true of `goodLimbs`, whose column 2 is `[0, 0]`
against the line's cells `(1, 0)`. -/
def stmtDropped : K × TableOut noneSent :=
  (1, ⟨receivedTrue noneSent (by decide) (by decide) (by decide) (by decide) goodLimbs⟩)

theorem stmtDropped_not_table :
    ((stmtDropped, oracleOf goodLimbs), ()) ∉ Seam.table noneSent :=
  fun h ↦ absurd (h.2.1 ⟨⟨0, 2⟩, 1, 0, false, by decide⟩ (by simp [stmtDropped])).1 (by decide)

theorem dropped_pub (c : E) :
    ((verdict noneSent poolDropped stmtDropped c [], oracleOf goodLimbs), ()) ∈
      Seam.pub noneSent := by
  have c0 : (noneSent.column goodLimbs ⟨0, 2⟩).values.get ⟨0, by decide⟩ = 0 := by decide
  have c1 : (noneSent.column goodLimbs ⟨0, 2⟩).values.get ⟨1, by decide⟩ = 0 := by decide
  refine ⟨fun cl hcl ↦ ?_, aux_of_none rfl _⟩
  rw [verdict, dite_eq_left (show ([] : List E).length =
    sentCount noneSent (noneSent.publicLines stmtDropped.1) from rfl)] at hcl
  simp only [poolDropped, Vector.toList_append, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · exact receivedTrue_holds noneSent (by decide) (by decide) (by decide) (by decide) goodLimbs
      cl hcl
  · simp only [claimsWith, Vector.toList_ofFn, List.mem_ofFn] at hcl
    obtain ⟨i, rfl⟩ := hcl
    fin_cases i
    show CMlPolynomialEval.eval₂Mle (noneSent.column goodLimbs ⟨0, 2⟩).values (algebraMap K E)
      (linePoint (by decide) c) = 0
    rw [eval₂Mle_linePoint, c0, c1]
    simp

/-- Dropping an unsent line's claim leaves no round-by-round knowledge error below one: the
empty message passes the check and the pool says nothing of the line. -/
example {err : Typed.Errors pubSlot.tree pubSlot.roles}
    (S : Typed.Security dropped (Seam.table noneSent) (Seam.pub noneSent) err) : 1 ≤ err.1 :=
  S.one_le_of_escape stmtDropped (oracleOf goodLimbs) (fun _ h ↦ stmtDropped_not_table h)
    fun c ↦ ⟨restOf [], trivial, _, (),
      (@verdictWith_of_accepts noneSent (check noneSent) poolDropped stmtDropped c [] rfl),
      dropped_pub c⟩

/-! ### A check the honest prover fails -/

/-- The statement `1` with the received claims true of the honest stack: in the table seam. -/
def stmtHonest : K × TableOut toy :=
  (1, ⟨receivedTrue toy (by decide) (by decide) (by decide) (by decide) honest⟩)

theorem stmtHonest_table : ((stmtHonest, oracleOf honest), ()) ∈ Seam.table toy :=
  ⟨receivedTrue_holds toy (by decide) (by decide) (by decide) (by decide) honest, by decide,
    aux_of_none rfl _⟩

/-- The check with the two cells swapped: `(1 + r)·cell1 + r·cell0`. -/
def swappedValues (input : K) (r : E) : List E :=
  ((toy.publicLines input).toList.filter (·.sent)).map fun l ↦
    (1 + r) * ofK l.cell1 + r * ofK l.cell0

/-- The phase with the swapped check. -/
abbrev swapped := phaseWith toy (fun s r cs ↦ decide (cs = swappedValues s.1 r)) (pooledFrom toy)

/-- The honest run at challenge `r`: the expected values sent, the pool output. -/
theorem honest_runs {I : M3Instance} (accept) (pool) (s : I.Stmt × TableOut I)
    (o : ∀ i, TheOracle I i) (r : E) :
    Typed.Runs pubSlot.tree pubSlot.roles pubSlot.samplers
      ((phaseWith I accept pool).prover (s, o) ()) ⟨r, expectedValues I s.1 r, PUnit.unit⟩
      ((pooled I s r, o), ()) :=
  ⟨mem_support_uniformSample E, _, (mem_support_pure_iff _ _).mpr rfl, _,
    (mem_support_pure_iff _ _).mpr rfl, rfl⟩

/-- A phase of this shape whose check rejects the honest message at some challenge, on a
statement in the table seam, is not complete. -/
theorem not_complete_of_reject {I : M3Instance} (accept) (pool) (s : I.Stmt × TableOut I)
    (o : ∀ i, TheOracle I i) (hin : ((s, o), ()) ∈ Seam.table I) (r : E)
    (h : accepts I accept s r (expectedValues I s.1 r) = false) :
    ¬ Typed.Complete (phaseWith I accept pool) (Seam.table I) (Seam.pub I) := fun C ↦
  nomatch (verdictWith_of_reject I accept pool h).symm.trans
    (C s o () hin _ _ (honest_runs accept pool s o r)).1

/-- The swapped check rejects the honest prover at the challenge `y`: the line's value is
`1 + y` and the swapped one `y`. So the phase is not complete. -/
example : ¬ Typed.Complete swapped (Seam.table toy) (Seam.pub toy) :=
  not_complete_of_reject _ _ stmtHonest (oracleOf honest) stmtHonest_table y (by
    rw [accepts, show decide (expectedValues toy stmtHonest.1 y = swappedValues stmtHonest.1 y) =
      false from decide_eq_false fun h ↦ by
        simp [expectedValues, swappedValues, lineValue, stmtHonest] at h, Bool.and_false])

/-- The phase with an extra check: the message has two values. -/
abbrev extraCheck :=
  phaseWith toy (fun s r cs ↦ check toy s r cs && decide (cs.length = 2)) (pooledFrom toy)

/-- The extra check rejects the honest prover, whose message has one value. -/
example : ¬ Typed.Complete extraCheck (Seam.table toy) (Seam.pub toy) :=
  not_complete_of_reject _ _ stmtHonest (oracleOf honest) stmtHonest_table y (by
    rw [accepts, show decide ((expectedValues toy stmtHonest.1 y).length = 2) = false from rfl,
      Bool.and_false, Bool.and_false])

/-! ### The unsent line pooled at the constant zero -/

/-- The pool with every unsent line's claim at the constant `0`, as earlier deployed verifiers
pooled the top limb (`cpu/mod.rs:674-682` at leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`),
instead of the value computed from the statement, which the verifiers at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d` compute for every limb (`verifier.py:1393-1394`). -/
def poolZero (I : M3Instance) (s : I.Stmt × TableOut I) (r : E) (cs : List E)
    (h : cs.length = sentCount I (I.publicLines s.1)) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ claimsWith I r (fun _ ↦ 0) (I.publicLines s.1) cs h⟩)

-- The two pools are the same where the unsent line is zero, as the top limb is: on three lines
-- shaped like the memory limbs the claims are the same, the value pooled at `0` being the line's.
#guard ((poolZero threeLimbs stmtLimbs y [1, 1] rfl).2.columns.toList.map fun c ↦ c.value) =
  ((pooledFrom threeLimbs stmtLimbs y [1, 1] rfl).2.columns.toList.map fun c ↦ c.value)

/-- Three lines like the memory limbs, but with a top line that is not zero: cells `(1, 0)`. The
public words have a zero top limb, so the leanISA statements have no such line, and the
constant zero rests on that. -/
abbrev topOne : M3Instance :=
  { toy with
    nLines := 3
    publicLines := fun v ↦
      #v[⟨⟨0, 0⟩, v, 1, true, by decide⟩, ⟨⟨0, 1⟩, 1, 1, true, by decide⟩,
        ⟨⟨0, 2⟩, 1, 0, false, by decide⟩] }

-- There the two pools differ: the value computed for the top line at `y` is `1 + y`, and the
-- constant is `0`.
#guard ((poolZero topOne (1, ⟨receivedTrue topOne (by decide) (by decide) (by decide) (by decide)
    goodLimbs⟩) y [1, 1] rfl).2.columns.toList.map fun c ↦ c.value) ≠
  ((pooledFrom topOne (1, ⟨receivedTrue topOne (by decide) (by decide) (by decide) (by decide)
    goodLimbs⟩) y [1, 1] rfl).2.columns.toList.map fun c ↦ c.value)

/-- The phase with the specification's check and that pool, on the statement with the top line
`(1, 0)`. -/
abbrev zeroTop := phaseWith topOne (check topOne) (poolZero topOne)

/-- The statement `1` with the received claims true of `goodLimbs`, whose top column `[0, 0]`
is not the top line's `(1, 0)`. -/
def stmtTop : K × TableOut topOne :=
  (1, ⟨receivedTrue topOne (by decide) (by decide) (by decide) (by decide) goodLimbs⟩)

theorem stmtTop_not_table : ((stmtTop, oracleOf goodLimbs), ()) ∉ Seam.table topOne :=
  fun h ↦ absurd (h.2.1 ⟨⟨0, 2⟩, 1, 0, false, by decide⟩ (by simp [stmtTop])).1 (by decide)

/-- The two sent limbs hold their lines, so the message `[1, 1]`, their values at every
challenge, passes the check whatever the top column holds. -/
theorem zeroTop_accepts (c : E) :
    accepts topOne (check topOne) stmtTop c [1, 1] = true := by
  rw [accepts_check_iff]
  apply decide_eq_true
  have h1 : ofK (1 : K) = 1 := map_one (algebraMap K E)
  have hl : (1 + c) * ofK 1 + c * ofK 1 = 1 := by
    rw [h1]
    linear_combination c * CharTwo.add_self_eq_zero (1 : E)
  show ([1, 1] : List E) = [(1 + c) * ofK 1 + c * ofK 1, (1 + c) * ofK 1 + c * ofK 1]
  rw [hl]

/-- The verdict is in the public seam at every challenge: the top claim at `0` is true of the
all-zero top column. -/
theorem zeroTop_pub (c : E) :
    ((verdict topOne (poolZero topOne) stmtTop c [1, 1], oracleOf goodLimbs), ()) ∈
      Seam.pub topOne := by
  have c0 : (topOne.column goodLimbs ⟨0, 0⟩).values.get ⟨0, by decide⟩ = 1 := by decide
  have c1 : (topOne.column goodLimbs ⟨0, 0⟩).values.get ⟨1, by decide⟩ = 1 := by decide
  have d0 : (topOne.column goodLimbs ⟨0, 1⟩).values.get ⟨0, by decide⟩ = 1 := by decide
  have d1 : (topOne.column goodLimbs ⟨0, 1⟩).values.get ⟨1, by decide⟩ = 1 := by decide
  have e0 : (topOne.column goodLimbs ⟨0, 2⟩).values.get ⟨0, by decide⟩ = 0 := by decide
  have e1 : (topOne.column goodLimbs ⟨0, 2⟩).values.get ⟨1, by decide⟩ = 0 := by decide
  refine ⟨fun cl hcl ↦ ?_, aux_of_none rfl _⟩
  rw [verdict, dite_eq_left (show ([1, 1] : List E).length =
    sentCount topOne (topOne.publicLines stmtTop.1) from rfl)] at hcl
  simp only [poolZero, Vector.toList_append, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · exact receivedTrue_holds topOne (by decide) (by decide) (by decide) (by decide) goodLimbs
      cl hcl
  · simp only [claimsWith, Vector.toList_ofFn, List.mem_ofFn] at hcl
    obtain ⟨i, rfl⟩ := hcl
    fin_cases i
    · show CMlPolynomialEval.eval₂Mle (topOne.column goodLimbs ⟨0, 0⟩).values
        (algebraMap K E) (linePoint (by decide) c) = 1
      rw [eval₂Mle_linePoint, c0, c1]
      simp
    · show CMlPolynomialEval.eval₂Mle (topOne.column goodLimbs ⟨0, 1⟩).values
        (algebraMap K E) (linePoint (by decide) c) = 1
      rw [eval₂Mle_linePoint, d0, d1]
      simp
    · show CMlPolynomialEval.eval₂Mle (topOne.column goodLimbs ⟨0, 2⟩).values
        (algebraMap K E) (linePoint (by decide) c) = 0
      rw [eval₂Mle_linePoint, e0, e1]
      simp

/-- Pooling the unsent line at the constant zero leaves no round-by-round knowledge error below
one when the line is not zero: the stack whose top column is `[0, 0]` against the line's
`(1, 0)` is accepted at every challenge. It is sound where the line is zero, which is why the
sources may pool the top limb at `0`, and that the adaptor's statements have a zero top line
is the obligation behind it. -/
example {err : Typed.Errors pubSlot.tree pubSlot.roles}
    (S : Typed.Security zeroTop (Seam.table topOne) (Seam.pub topOne) err) : 1 ≤ err.1 :=
  S.one_le_of_escape stmtTop (oracleOf goodLimbs) (fun _ h ↦ stmtTop_not_table h) fun c ↦
    ⟨restOf [1, 1], trivial, _, (),
      (@verdictWith_of_accepts topOne (check topOne) (poolZero topOne) stmtTop c [1, 1]
        (zeroTop_accepts c)), zeroTop_pub c⟩

-- The specification's verifier, which pools the value computed, as the deployed verifiers now
-- do, is not fooled: the claim it pools for the top line is false of that stack.
#guard ¬ ∀ c ∈ (verdict topOne (pooledFrom topOne) stmtTop y [1, 1]).2.columns.toList,
  c.Holds goodLimbs

/-! ### The bad challenge is attained -/

-- On `oneBadLimb`, limb 1 holds the cells `(1, 0)` against `(0, 0)`. A prover that sends its
-- stack's true values passes the check at `r = 1` and at no other challenge tried, and at that
-- challenge every claim of the pool holds of its stack: the bound `1/|E|` of
-- `PublicInput.security` is attained, so it cannot be lowered.
#guard check twoLimbs stmtOneBad 1 (trueValues twoLimbs oneBadLimb 0 1)
#guard ¬ check twoLimbs stmtOneBad y (trueValues twoLimbs oneBadLimb 0 y)
#guard ¬ check twoLimbs stmtOneBad r₂ (trueValues twoLimbs oneBadLimb 0 r₂)
#guard ∀ c ∈ (pooled twoLimbs stmtOneBad 1).2.columns.toList, c.Holds oneBadLimb

end Refutations

end LeanVMTests.Protocol.PublicInput
