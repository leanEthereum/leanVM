import LeanVM.Protocol.Opening
import LeanVM.Protocol.PublicInput
import LeanVM.Protocol.Spine.Toy
import LeanVM.Protocol.Spine.Compose
import Mathlib.Algebra.CharP.Two

/-!
# Opening phase tests

Every guard changes one thing. The phase accepts a pool when the stack's answer to the pool's
weights, combined by the powers of the challenge, is the pool's values combined the same way.

* **An honest pool is accepted** on the toy: four true column claims on the honest stack,
  combined at two challenges.
* **A false claim is rejected**: one value changed by one, at a challenge that is no root of the
  difference.
* **The bound is attained.** A pool of four claims whose differences are the coefficients of
  `(λ + 1)(λ + y)(λ + y + 1)` is accepted at exactly those three roots, the slot's `J - 1`.
* **The empty pool** on an instance with no table: the question is the zero weight, the value
  `0`, the stack is accepted, and the slot's error is `0`.
* **The order of the powers.** On an instance with a Flock region, the weighted claim takes
  `λ^0` and the column claim `λ^1`, and the swapped order gives another value.
* **The phase fills its slot**: its two halves typecheck against the spine's seams at the slot's
  errors, compute at `E`, and with the public-input phase make a bundle the master
  theorems apply to, given the three other phases.
* **The check is load-bearing.** On a statement outside the Flock seam, four weakened openings
  each accept at every challenge, so none has a round-by-round knowledge error below one,
  whatever extractor it is given: with no check on the answer; checking the first pooled claim
  alone; combining with unit weights, where two copies of one false claim cancel in
  characteristic two; and combining the column claims alone, dropping the Flock phase's weighted
  claim.

Facts the refutations need are proved over an abstract instance and instantiated, and the
weakened verifiers' steps are named definitions: on a concrete instance, unifying a term the
library built with one elaborated here can time out. A plain file, so `#guard` evaluates the
compiled definitions.
-/

namespace LeanVMTests.Protocol.Opening

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Toy CompPoly OracleComp
open Interaction Interaction.Oracle Interaction.Oracle.Security
open scoped NNReal

/-- A column claim is decided by evaluating the column's extension. -/
instance {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable (CMlPolynomialEval.eval₂Mle (I.column q c.col).values
    (algebraMap K E) c.point = c.value))

/-! ## Claims on the toy -/

/-- The claim on column `c` of the toy at the point `(z)`, with the honest stack's value. -/
def trueClaim (c : toy.ColumnId) (z : E) : ColumnClaim toy :=
  ⟨c, #v[z], CMlPolynomialEval.eval₂Mle (toy.column honest c).values (algebraMap K E) #v[z]⟩

/-- The same claim with its value off by `d`. -/
def offBy (c : toy.ColumnId) (z d : E) : ColumnClaim toy :=
  ⟨c, #v[z], (trueClaim c z).value + d⟩

/-- A statement of the Flock seam on the toy: four column claims and no weighted claim. -/
def stmtOf (a b c d : ColumnClaim toy) : K × FlockOut toy :=
  (1, ⟨#v[a, b, c, d], #v[]⟩)

/-- Four true claims, two on the public line's column. -/
def honestStmt : K × FlockOut toy :=
  stmtOf (trueClaim ⟨0, 0⟩ y) (trueClaim ⟨0, 1⟩ y) (trueClaim ⟨0, 2⟩ y) (trueClaim ⟨0, 2⟩ (y + 1))

/-- The same with the second claim off by one. -/
def badStmt : K × FlockOut toy :=
  stmtOf (trueClaim ⟨0, 0⟩ y) (offBy ⟨0, 1⟩ y 1) (trueClaim ⟨0, 2⟩ y) (trueClaim ⟨0, 2⟩ (y + 1))

/-- Two copies of one claim off by one, then two true claims. -/
def dupStmt : K × FlockOut toy :=
  stmtOf (offBy ⟨0, 0⟩ y 1) (offBy ⟨0, 0⟩ y 1) (trueClaim ⟨0, 1⟩ y) (trueClaim ⟨0, 2⟩ y)

/-- Four claims on one column and point whose differences are the coefficients of
`(λ + 1)(λ + y)(λ + y + 1) = λ³ + (y² + y + 1)·λ + (y² + y)`. -/
def tightStmt : K × FlockOut toy :=
  stmtOf (offBy ⟨0, 0⟩ y (y * y + y)) (offBy ⟨0, 0⟩ y (y * y + y + 1)) (offBy ⟨0, 0⟩ y 0)
    (offBy ⟨0, 0⟩ y 1)

/-- The honest stack's answer to the pool's weights combined at `ρ`. -/
def answer (s : K × FlockOut toy) (ρ : E) : E :=
  (Opening.weight toy s ρ).pair (algebraMap K E) honest.values

/-- Whether the phase accepts the honest stack's answer at `ρ`. -/
def acceptsAt (s : K × FlockOut toy) (ρ : E) : Bool :=
  decide (answer s ρ = powerBatch (Opening.values toy s) ρ)

/-- A second challenge, `y² + 1`. -/
def ρ₂ : E := y * y + 1

/-- The challenge `y + 1`. -/
def y₁ : E := y + 1

/-! ## Honest and false pools -/

#guard ∀ c ∈ honestStmt.2.columns.toList, c.Holds honest
#guard acceptsAt honestStmt y
#guard acceptsAt honestStmt ρ₂

#guard ¬ ∀ c ∈ badStmt.2.columns.toList, c.Holds honest
#guard !acceptsAt badStmt y
#guard !acceptsAt badStmt ρ₂

-- The bound is attained: three bad challenges for four claims, the roots of a cubic.
#guard ¬ ∀ c ∈ tightStmt.2.columns.toList, c.Holds honest
#guard acceptsAt tightStmt 1
#guard acceptsAt tightStmt y
#guard acceptsAt tightStmt y₁
#guard !acceptsAt tightStmt ρ₂
#guard !acceptsAt tightStmt 0

/-! ## The empty pool -/

/-- An instance with no table, on a stack of one cell: nothing to pool. -/
abbrev empty : M3Instance where
  toShape := ⟨0, Fin.elim0, Fin.elim0⟩
  Stmt := Unit
  constraints := fun j ↦ j.elim0
  flushes := fun j ↦ j.elim0
  d := 0
  constraints_degree := fun j ↦ j.elim0
  flushes_degree := fun j ↦ j.elim0
  counts := fun j ↦ j.elim0
  rows := fun j ↦ j.elim0
  rows_le := fun j ↦ j.elim0
  padRow := fun j ↦ j.elim0
  boundary := []
  μ := 0
  layout := ⟨fun c ↦ c.1.elim0, fun _ c ↦ c.1.elim0⟩
  nLines := 0
  publicLines := fun _ ↦ #v[]
  flock := none

example : empty.poolSize = 0 := by decide

/-- The empty pool. -/
def emptyStmt : Unit × FlockOut empty := ((), ⟨#v[], #v[]⟩)

/-- A stack of one nonzero cell. -/
def one : Column 0 := ⟨#v[1]⟩

-- The question is the zero weight and the value `0`, so the stack is accepted.
#guard (Opening.weight empty emptyStmt y).onCube = #v[0]
#guard powerBatch (Opening.values empty emptyStmt) y = 0
#guard (Opening.weight empty emptyStmt y).pair (algebraMap K E) one.values = 0

/-- The slot's error on the empty pool is `0`. -/
example : openingErrors empty = (overE 0, fun _ ↦ PUnit.unit) := rfl

/-! ## The order of the powers -/

/-- One table of height `2^8` and width one, with a count column so that the table sumcheck
visits it, and the whole table as the Flock region. -/
abbrev flockShape : Shape := ⟨1, fun _ ↦ 8, fun _ ↦ 1⟩

/-- The stack is the one column. -/
theorem readWith_id (q : Column 8) (c : flockShape.ColumnId) :
    Layout.readWith (fun (_ : flockShape.ColumnId) (z : Vector E 8) ↦ z) q c = q := by
  obtain ⟨v⟩ := q
  apply congrArg Column.mk
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn, boolIndex_boolVec]
  rfl

/-- An instance with one column claim and one weighted claim to pool. -/
abbrev flocky : M3Instance where
  toShape := flockShape
  Stmt := Unit
  constraints := fun _ ↦ []
  flushes := fun _ ↦ []
  d := 0
  constraints_degree := fun _ _ h ↦ absurd h (List.not_mem_nil)
  flushes_degree := fun _ _ h ↦ absurd h (List.not_mem_nil)
  counts := fun _ ↦ [0]
  rows := fun j ↦ 2 ^ flockShape.τ j
  rows_le := fun _ ↦ le_rfl
  padRow := fun _ _ ↦ 0
  boundary := []
  μ := 8
  layout := ⟨fun _ z ↦ z, fun q c z ↦ by rw [readWith_id]⟩
  nLines := 0
  publicLines := fun _ ↦ #v[]
  flock := some ⟨⟨0, 0⟩, 0, rfl, BlockR1CS.ofMatrices (fun _ _ ↦ false) (fun _ _ ↦ false)⟩

example : flocky.pubClaims = 1 := by decide
example : flocky.flockClaims = 1 := rfl

/-- The point `(y, …, y)`. -/
def ys : Vector E 8 := Vector.replicate 8 y

/-- A weighted claim with value `y` and a column claim with value `1`. -/
def flockyStmt : Unit × FlockOut flocky := ((), ⟨#v[⟨⟨0, 0⟩, ys, 1⟩], #v[⟨eqWeight ys, y⟩]⟩)

-- The weighted claim takes `λ^0`, the column claim `λ^1`; the swapped order differs.
#guard powerBatch (Opening.values flocky flockyStmt) ρ₂ = y + ρ₂ * 1
#guard powerBatch (Opening.values flocky flockyStmt) ρ₂ ≠ 1 + ρ₂ * y

example : Opening.pool flocky flockyStmt.2 ⟨0, by decide⟩ = ⟨eqWeight ys, y⟩ :=
  Opening.pool_weighted flocky flockyStmt.2 ⟨0, by decide⟩

example : Opening.pool flocky flockyStmt.2 ⟨1, by decide⟩ =
    Opening.columnWeighted flocky ⟨⟨0, 0⟩, ys, 1⟩ :=
  Opening.pool_column flocky flockyStmt.2 ⟨0, by decide⟩

/-! ## The phase fills its slot -/

/-- The completeness half, at the spine's seams. -/
theorem complete : Typed.Complete (opening toy) (Seam.flock toy) (Seam.opened toy) :=
  openingComplete toy

/-- The security half, at the spine's seams and the slot's errors; a plain definition, so it
computes at `E`. -/
def security : Typed.Security (opening toy) (Seam.flock toy) (Seam.opened toy)
    (openingErrors toy) :=
  openingSecurity toy

/-- The slot's error on the toy: three, for the four pooled claims. -/
example : openingErrors toy = (overE 3, fun _ ↦ PUnit.unit) := rfl

/-- With the public-input phase and the opening phase in their slots, the master
theorems hold of the bundle, given the three other phases' proofs, at every instance. -/
example (I : M3Instance)
    (bus : Typed.Def (TheOracle I) I.Stmt Unit (I.Stmt × BusOut I) Unit (busSlot I))
    (table : Typed.Def (TheOracle I) (I.Stmt × BusOut I) Unit (I.Stmt × TableOut I) Unit
      (tableSlot I))
    (flock : Typed.Def (TheOracle I) (I.Stmt × PubOut I) Unit (I.Stmt × FlockOut I) Unit
      (flockPhaseSlot I))
    (cb : Typed.Complete bus (Seam.commitHonest I) (Seam.bus I))
    (ct : Typed.Complete table (Seam.bus I) (Seam.table I))
    (cf : Typed.Complete flock (Seam.pub I) (Seam.flock I)) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (input : I.Stmt) (q : Column I.μ)
    (h : ((input, fun i ↦ i.elim0), q) ∈ M3HonestRel I) :
    Pr{let x ← (leanVmPiop ⟨bus, table, PublicInput.phase I, flock, opening I⟩
      initial).execute impl input q}[x.2.2 = some ()] = 1 :=
  piop_perfectCompleteness _ ⟨cb, ct, PublicInput.complete I, cf, openingComplete I⟩
    initial impl input q h

example (I : M3Instance)
    (bus : Typed.Def (TheOracle I) I.Stmt Unit (I.Stmt × BusOut I) Unit (busSlot I))
    (table : Typed.Def (TheOracle I) (I.Stmt × BusOut I) Unit (I.Stmt × TableOut I) Unit
      (tableSlot I))
    (flock : Typed.Def (TheOracle I) (I.Stmt × PubOut I) Unit (I.Stmt × FlockOut I) Unit
      (flockPhaseSlot I))
    (sb : Typed.Security bus (Seam.commit I) (Seam.bus I) (busErrors I))
    (st : Typed.Security table (Seam.bus I) (Seam.table I) (tableErrors I))
    (sf : Typed.Security flock (Seam.pub I) (Seam.flock I) (flockErrors I))
    (initial : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : I.Stmt) :
    ∃ cert : KnowledgeCertificate (piopSlot I).tree (piopSlot I).roles
        ⟨Column I.μ, M3Holds I s⟩,
      cert.extractor = piopExtractor ⟨bus, table, PublicInput.phase I, flock, opening I⟩
        ⟨sb, st, PublicInput.security I, sf, openingSecurity I⟩ s ∧
      cert.challenges = Typed.schedule (piopSlot I).tree (piopSlot I).roles
        (piopSlot I).samplers (piopErrors I) ∧
      SamplesChallenges unifSpec (QueryImpl.id' unifSpec) (piopSlot I).tree (piopSlot I).roles
        (piopSlot I).oracles initial impl _
        (leanVmVerifier ⟨bus, table, PublicInput.phase I, flock, opening I⟩ initial s)
        cert.challenges :=
  piop_knowledgeSoundness _ _ initial impl s

/-! ## The weakened verifiers -/

section Weakened

variable (I : M3Instance)

/-- The question with no check on the answer. -/
def unchecked : Typed.Question (Column I.μ) (WeightedClaim I) Unit where
  query c := c.weight
  check _ _ := true
  out _ := ()

/-- The pool's claim `j` alone, whatever the challenge. -/
def onlyOut (j : Fin I.poolSize) (s : I.Stmt × FlockOut I) (_ _ : E) : WeightedClaim I :=
  Opening.pool I s.2 j

/-- The opening that checks the pool's claim `j` alone. -/
abbrev only (j : Fin I.poolSize) :
    Typed.Def (TheOracle I) (I.Stmt × FlockOut I) Unit (WeightedClaim I) Unit openingSlot :=
  Typed.batch (TheOracle I) E (Opening.values I) (onlyOut I j)

/-- The batched claim with unit weights, whatever the challenge. -/
def unitOut (s : I.Stmt × FlockOut I) (_ _ : E) : WeightedClaim I :=
  Opening.batched I s 1 (powerBatch (Opening.values I s) 1)

/-- The opening that combines the claims with unit weights. -/
abbrev unitWeights :
    Typed.Def (TheOracle I) (I.Stmt × FlockOut I) Unit (WeightedClaim I) Unit openingSlot :=
  Typed.batch (TheOracle I) E (Opening.values I) (unitOut I)

/-- The column claims alone, combined by the powers of the challenge. -/
def columnsOut (s : I.Stmt × FlockOut I) (ρ _ : E) : WeightedClaim I :=
  ⟨Weight.batch (fun j : Fin I.pubClaims ↦ (Opening.columnWeighted I s.2.columns[j]).weight) ρ,
    powerBatch (fun j : Fin I.pubClaims ↦ s.2.columns[j].value) ρ⟩

/-- The opening that drops the weighted claims. -/
abbrev columnsOnly :
    Typed.Def (TheOracle I) (I.Stmt × FlockOut I) Unit (WeightedClaim I) Unit openingSlot :=
  Typed.batch (TheOracle I) E (Opening.values I) (columnsOut I)

/-- Two copies of one pooled claim cancel under unit weights in characteristic two: when every
other pooled claim holds, the batched claim at `1` holds, whether or not the copies do. -/
theorem unit_holds_of_copies (s : I.Stmt × FlockOut I) (q : Column I.μ) (i j : Fin I.poolSize)
    (hij : i ≠ j) (heq : Opening.pool I s.2 i = Opening.pool I s.2 j)
    (hrest : ∀ k, k ≠ i → k ≠ j → (Opening.pool I s.2 k).Holds q) (ρ c : E) :
    (unitOut I s ρ c).Holds q := by
  refine (Opening.batched_holds_iff I s 1 _ q).mpr ?_
  simp only [Opening.values, powerBatch, one_pow, mul_one]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Finset.sum_eq_add i j hij (fun k _ hk ↦ sub_eq_zero.mpr (hrest k hk.1 hk.2)) (by simp)
      (by simp), heq]
  exact CharTwo.add_self_eq_zero _

/-- When every column claim holds, the column claims alone, combined at any challenge, hold. -/
theorem columns_holds (s : I.Stmt × FlockOut I) (q : Column I.μ)
    (h : ∀ c ∈ s.2.columns.toList, c.Holds q) (ρ c : E) : (columnsOut I s ρ c).Holds q := by
  unfold columnsOut WeightedClaim.Holds
  rw [Weight.pair_batch]
  exact congrArg (powerBatch · ρ) (funext fun j ↦ (Opening.columnWeighted_holds_iff I q _).mpr
    (h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem _))))

end Weakened

/-! ## The check is load-bearing -/

/-- The honest stack as the one oracle. -/
def theHonest : ∀ i, TheOracle toy i := fun _ ↦ honest

/-- A true claim holds of the honest stack. -/
theorem trueClaim_holds (c : toy.ColumnId) (z : E) : (trueClaim c z).Holds honest := rfl

/-- `badStmt` is outside the Flock seam: its second claim is false of the honest stack. -/
theorem badStmt_not_flock (w : Unit) : ((badStmt, theHonest), w) ∉ Seam.flock toy := by
  rintro ⟨h, -⟩
  have h1 := h (offBy ⟨0, 1⟩ y 1) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact one_ne_zero (add_left_cancel ((add_zero _).trans h1)).symm

/-- `dupStmt` is outside the Flock seam: its first claim is false of the honest stack. -/
theorem dupStmt_not_flock (w : Unit) : ((dupStmt, theHonest), w) ∉ Seam.flock toy := by
  rintro ⟨h, -⟩
  have h0 := h (offBy ⟨0, 0⟩ y 1) (List.mem_cons_self ..)
  exact one_ne_zero (add_left_cancel ((add_zero _).trans h0)).symm

/-- On the toy the pool is the column claims, in order. -/
theorem pool_toy (s : FlockOut toy) (j : Fin toy.poolSize) :
    Opening.pool toy s j = Opening.columnWeighted toy (s.columns[j.val]'j.isLt) :=
  (congrArg (Opening.pool toy s) (Fin.ext (Nat.zero_add j.val).symm)).trans
    (Opening.pool_column toy s ⟨j.val, j.isLt⟩)

/-- Without the check on the answer, a false pool is accepted at every challenge: no knowledge
error below one. -/
theorem unchecked_one_le {e : ℝ≥0}
    (S : Typed.Security (opening toy) (Seam.flock toy) ((unchecked toy).rel (Seam.done toy))
      (Typed.drawErrors E e)) : 1 ≤ e :=
  Typed.sampleChallenge_one_le S badStmt theHonest badStmt_not_flock rfl fun _ ↦
    ⟨(), rfl, trivial⟩

/-- The first claim of `badStmt` holds of the honest stack. -/
theorem badStmt_first : (Opening.pool toy badStmt.2 ⟨0, by decide⟩).Holds honest := by
  rw [pool_toy, Opening.columnWeighted_holds_iff]
  exact trueClaim_holds _ _

/-- Checking the first claim alone, a pool whose first claim holds is accepted at every
challenge: no knowledge error below one. -/
theorem only_one_le {e : ℝ≥0}
    (S : Typed.Security (only toy ⟨0, by decide⟩) (Seam.flock toy) (Seam.opened toy)
      (Typed.drawErrors E e)) : 1 ≤ e :=
  Typed.sampleChallenge_one_le S badStmt theHonest badStmt_not_flock rfl fun _ ↦
    ⟨(), (Seam.opened_iff toy _ theHonest ()).mpr badStmt_first⟩

/-- The two false claims of `dupStmt` are copies, and its other claims hold: the batched claim
at unit weights holds. -/
theorem dupStmt_unit (ρ c : E) : (unitOut toy dupStmt ρ c).Holds honest := by
  refine unit_holds_of_copies toy dupStmt honest ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    (by rw [pool_toy, pool_toy]; rfl) (fun ⟨k, hk⟩ h0 h1 ↦ ?_) ρ c
  rw [pool_toy, Opening.columnWeighted_holds_iff]
  have hk4 : k < 4 := (show toy.poolSize = 4 by decide) ▸ hk
  interval_cases k
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact trueClaim_holds _ _
  · exact trueClaim_holds _ _

/-- With unit weights, two copies of one false claim cancel in characteristic two, so the pool
is accepted at every challenge: no knowledge error below one. -/
theorem unitWeights_one_le {e : ℝ≥0}
    (S : Typed.Security (unitWeights toy) (Seam.flock toy) (Seam.opened toy)
      (Typed.drawErrors E e)) : 1 ≤ e :=
  Typed.sampleChallenge_one_le S dupStmt theHonest dupStmt_not_flock rfl fun ρ ↦
    ⟨(), (Seam.opened_iff toy _ theHonest ()).mpr (dupStmt_unit ρ _)⟩

/-- The zero stack of `flocky`. -/
def zero8 : Column 8 := ⟨Vector.replicate (2 ^ 8) 0⟩

/-- The zero stack as the one oracle. -/
def theZero : ∀ i, TheOracle flocky i := fun _ ↦ zero8

/-- The true column claim of `flocky` at `ys` on the zero stack. -/
def zeroColumn : ColumnClaim flocky :=
  ⟨⟨0, 0⟩, ys, CMlPolynomialEval.eval₂Mle (flocky.column zero8 ⟨0, 0⟩).values (algebraMap K E) ys⟩

/-- A weighted claim at `ys` off by one on the zero stack. -/
def offWeighted : WeightedClaim flocky :=
  ⟨eqWeight ys, (eqWeight ys).pair (algebraMap K E) zero8.values + 1⟩

/-- A true column claim and a false weighted claim. -/
def flockyBad : Unit × FlockOut flocky := ((), ⟨#v[zeroColumn], #v[offWeighted]⟩)

/-- `flockyBad` is outside the Flock seam: its weighted claim is false. -/
theorem flockyBad_not_flock (w : Unit) : ((flockyBad, theZero), w) ∉ Seam.flock flocky := by
  rintro ⟨-, h⟩
  have h0 := h offWeighted (List.mem_cons_self ..)
  exact one_ne_zero (add_left_cancel ((add_zero _).trans h0)).symm

/-- The column claims of `flockyBad` hold. -/
theorem flockyBad_columns : ∀ c ∈ flockyBad.2.columns.toList, c.Holds zero8 := by
  have hl : flockyBad.2.columns.toList = [zeroColumn] := rfl
  intro c hc
  rw [hl, List.mem_singleton] at hc
  subst hc
  rfl

/-- Dropping the weighted claims, a pool whose column claims hold is accepted at every
challenge, whatever its weighted claims: no knowledge error below one. -/
theorem columnsOnly_one_le {e : ℝ≥0}
    (S : Typed.Security (columnsOnly flocky) (Seam.flock flocky) (Seam.opened flocky)
      (Typed.drawErrors E e)) : 1 ≤ e :=
  Typed.sampleChallenge_one_le S flockyBad theZero flockyBad_not_flock rfl fun ρ ↦
    ⟨(), (Seam.opened_iff flocky _ theZero ()).mpr
      (columns_holds flocky flockyBad zero8 flockyBad_columns ρ _)⟩

end LeanVMTests.Protocol.Opening
