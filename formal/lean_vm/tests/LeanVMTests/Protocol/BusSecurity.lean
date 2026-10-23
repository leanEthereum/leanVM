import LeanVM.Protocol.BusSecurity
import LeanVMTests.Protocol.Bus

/-!
# Bus phase knowledge-soundness tests

* **The theorem has an inhabitant that computes** at the slot's errors `busErrors`: `busSecurity`
  on the bus tests' instance and on the spine's toy is a `def` without `noncomputable`, and so is
  its extractor, which the spine's composition reads.

* **The challenges' bound rests on the products.** A stack whose only failing clause is the
  balance (`a = [1, 0]`: the push tuple `(0, x + 1)` is pulled as `(1, x + 1)`) has different
  products at the tests' challenge: the state after the challenges is false there, and true only
  at a collision.

* **Padding rows flush nothing only behind a separator** (Proposition `prop:pad`). On a table
  with a padding row, the verifier replaces the row's leaf `φ(x)` by `φ(x) + 1 − φ(p)`, the
  fingerprint of the tuple `1 − t + t(p)`; the condition `separator` (slot 0 of a flush is
  constant) makes that tuple's slot 0 equal to `1`. `noSep` drops it: one table of two rows, one
  executed, pushing `(X₀, …, X₀)` and pulling `(X₁, …, X₁)`. On `collide` (executed row `(0, 1)`,
  padding row `(1, 1)` against the public `(0, 0)`) the bus is unbalanced and only the balance
  fails, yet both sides' padding tuple is the zero tuple, so both products are `0` at every
  challenge. Then the challenges have no security below error one
  (`padding_collision_no_security`, over any instance with such a stack, the facts the kernel
  cannot evaluate checked by the guards), where the side conditions give `4·2^{μ_bus}/|E|`.
  The separator is what rules it out: `noSep` meets every other side condition and fails exactly
  `separator` (kernel), under the side conditions no padding tuple is zero
  (`zeroTuple_not_mem`), and `withSep`, the same instance with a constant slot 0, meets them; on
  the same stack its padding tuples are `(1, 0, …)` and the products differ at the tests'
  challenge.

The refutation of the check `R_c ≠ 0` is in the bus tests (`roots_unchecked_no_security`).
-/

namespace LeanVMTests.Protocol.BusSecurity

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Bus LeanVMTests.Protocol.Bus
  CompPoly CPoly CMlPolynomialEval
open scoped NNReal

/-! ## The theorem has an inhabitant -/

/-- Knowledge soundness of the bus phase on the bus tests' instance, at the slot's error. -/
def security : Typed.Security (busPhase busToy conditions) (Seam.commit busToy)
    (Seam.bus busToy) (busErrors busToy) :=
  busSecurity busToy conditions

/-- Its extractor. -/
def extractor := security.extractor

/-- Knowledge soundness of the bus phase on the spine's toy. -/
def toySecurity : Typed.Security (busPhase Toy.toy toyConditions) (Seam.commit Toy.toy)
    (Seam.bus Toy.toy) (busErrors Toy.toy) :=
  busSecurity Toy.toy toyConditions

/-! ## The challenges' bound rests on the products -/

/-- `a = [1, 0]`: Boolean, counts nonzero, but unbalanced. -/
def unbalanced : Column 2 := ⟨#v[1, 0, K.ofBits 2, K.ofBits 3]⟩

#guard busToy.ConstraintsVanish unbalanced ∧ busToy.CountsNonzero unbalanced
#guard ¬ busToy.Balanced unbalanced
#guard ¬ M3Holds busToy () unbalanced

/-- Its push and pull leaf stacks at the tests' challenge. -/
def pushUnbalanced : CMlPolynomialEval E busToy.μBus := pushLeaves busToy α β unbalanced
def pullUnbalanced : CMlPolynomialEval E busToy.μBus := pullLeaves busToy α β unbalanced

#guard (∏ x : Fin (2 ^ busToy.μBus), pushUnbalanced[x]) ≠
  ∏ x : Fin (2 ^ busToy.μBus), pullUnbalanced[x]

/-! ## Padding rows flush nothing only behind a separator (Proposition `prop:pad`) -/

/-- The zero tuple. -/
def zeroTuple : Vector K 16 := Vector.replicate 16 0

/-- The zero tuple's fingerprint is `0` at every `α`. -/
theorem fingerprint_zeroTuple (α : Fin 4 → E) : fingerprint α zeroTuple = 0 := by
  simp only [fingerprint]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  change _ * algebraMap K E zeroTuple[i.val] = 0
  simp [zeroTuple]

/-- A side whose padding tuples include the zero tuple has padding product `0`. -/
theorem padProduct_of_zeroTuple_mem (α : Fin 4 → E) {U : List (Vector K 16)}
    (h : zeroTuple ∈ U) : padProduct α (U : Multiset (Vector K 16)) = 0 := by
  rw [padProduct, Multiset.map_coe, Multiset.prod_coe]
  exact List.prod_eq_zero (List.mem_map.mpr ⟨zeroTuple, h, fingerprint_zeroTuple α⟩)

/-- **Without the separator the challenges have no security.** A stack outside `M3Holds` whose
push and pull padding tuples both include the zero tuple, whose count product is nonzero and
that meets the clauses no challenge touches, enters `afterChallenge` at every challenge: both
products are `0`. So no security of the challenges from `Seam.commit` to `afterChallenge` has an
error below one, whatever the extractor. -/
theorem padding_collision_no_security {I : M3Instance} (s : I.Stmt) (q : Column I.μ)
    (hs : ¬ M3Holds I s q) (hfit : (blocks I 1).total ≤ 2 ^ I.μBus)
    (hpush : zeroTuple ∈ sidePadTuples I q .push) (hpull : zeroTuple ∈ sidePadTuples I q .pull)
    (hcount : ∀ (α : Fin 4 → E) (β : E), ∏ x : Fin (2 ^ I.μBus), (sideLeaves I 2 α β q)[x] ≠ 0)
    (hc : I.ConstraintsVanish q) (hl : I.PublicLinesHold s q) (ha : I.aux q) {e : ℝ≥0}
    (S : Typed.Security (challengeStep I) (Seam.commit I) (afterChallenge I)
      (Typed.drawErrors _ e)) : 1 ≤ e := by
  let o : ∀ i, TheOracle I i := fun _ ↦ q
  refine Typed.sampleChallenge_one_le S s o (fun _ hw ↦ hs hw) rfl fun ab ↦
    ⟨(), ?_, hcount ab.1 ab.2, hc, hl, ha⟩
  change ∏ x : Fin (2 ^ I.μBus), (pushLeaves I ab.1 ab.2 q)[x] =
    ∏ x : Fin (2 ^ I.μBus), (sideLeaves I 1 ab.1 ab.2 q)[x]
  rw [prod_pushLeaves, prod_sideLeaves_eq rfl ab.1 ab.2 q hfit,
    padProduct_of_zeroTuple_mem _ hpush, padProduct_of_zeroTuple_mem _ hpull, mul_zero, mul_zero]

/-- **The separator rules it out**: under the side conditions no padding tuple is the zero
tuple, since its slot 0 is `1` (`padTuple_ne_zero`). -/
theorem zeroTuple_not_mem {I : M3Instance} (h : Conditions I) (q : Column I.μ) (s : Side) :
    zeroTuple ∉ sidePadTuples I q s := fun h0 ↦ by
  obtain ⟨i, hi⟩ := padTuple_ne_zero h h0
  exact hi (by simp [zeroTuple])

/-- A variable has total degree at most two. -/
theorem X_totalDegree (i : Fin 2) : (CMvPolynomial.X i : CMvPolynomial 2 K).totalDegree ≤ 2 := by
  rw [totalDegree_equiv (S := K)]
  simp [CMvPolynomial.fromCMvPolynomial_X]

/-- The pad tests' instance on a list of flushes: the bus tests' table of two columns and two
rows, row 0 executed and row 1 padding, the public padding row `(0, 0)`; no constraint, count
column or boundary block. -/
abbrev padInst (fl : List (Side × Vector (CMvPolynomial 2 K) 16))
    (hfl : ∀ f ∈ fl, ∀ k, (f.2.get k).totalDegree ≤ 2) : M3Instance where
  toShape := shape
  Stmt := Unit
  constraints := fun _ ↦ []
  flushes := fun _ ↦ fl
  d := 2
  constraints_degree := fun _ _ h ↦ absurd h List.not_mem_nil
  flushes_degree := fun _ f h k ↦ hfl f h k
  counts := fun _ ↦ []
  rows := fun _ ↦ 1
  rows_le := fun _ ↦ Nat.one_le_two_pow
  padRow := fun _ _ ↦ 0
  boundary := []
  μ := 2
  layout := layout
  nLines := 0
  publicLines := fun _ ↦ #v[]
  flock := none

/-- Every slot `X₀`, pushed: no slot is constant. -/
def pushAll : Side × Vector (CMvPolynomial 2 K) 16 :=
  (.push, Vector.replicate 16 (CMvPolynomial.X 0))

/-- Every slot `X₁`, pulled. -/
def pullAll : Side × Vector (CMvPolynomial 2 K) 16 :=
  (.pull, Vector.replicate 16 (CMvPolynomial.X 1))

/-- `(0, X₀, …, X₀)`, pushed: slot 0 a constant separator. -/
def pushSep : Side × Vector (CMvPolynomial 2 K) 16 :=
  (.push, Vector.ofFn fun k ↦ if k.val = 0 then 0 else CMvPolynomial.X 0)

/-- `(0, X₁, …, X₁)`, pulled. -/
def pullSep : Side × Vector (CMvPolynomial 2 K) 16 :=
  (.pull, Vector.ofFn fun k ↦ if k.val = 0 then 0 else CMvPolynomial.X 1)

/-- The instance with no separator. -/
abbrev noSep : M3Instance := padInst [pushAll, pullAll] fun f hf k ↦ by
  rcases List.mem_pair.mp hf with rfl | rfl <;> simpa [pushAll, pullAll] using X_totalDegree _

/-- The same instance with a constant slot 0. -/
abbrev withSep : M3Instance := padInst [pushSep, pullSep] fun f hf k ↦ by
  rcases List.mem_pair.mp hf with rfl | rfl <;>
    (simp only [pushSep, pullSep, Vector.get_ofFn]; split
     · rw [totalDegree_equiv (S := K)]; simp
     · exact X_totalDegree _)

/-- Executed row `(0, 1)`, padding row `(1, 1)`: column 0 is `[0, 1]`, column 1 `[1, 1]`. -/
def collide : Column 2 := ⟨#v[0, 1, 1, 1]⟩

/-- Executed row `(1, 1)`, padding row `(0, 0)`, the public one. -/
def honestPad : Column 2 := ⟨#v[1, 0, 1, 0]⟩

-- On `noSep`, `collide` fails the balance alone: the executed row pushes `(0, …)` and pulls
-- `(1, …)`.
#guard noSep.ConstraintsVanish collide ∧ noSep.CountsNonzero collide ∧
  noSep.PublicLinesHold () collide ∧ noSep.aux collide
#guard ¬ noSep.Balanced collide
#guard ¬ M3Holds noSep () collide
-- Its padding row is dishonest, and both sides' padding tuple is the zero tuple.
#guard ¬ noSep.PaddingHonest collide
#guard (sidePadTuples noSep collide .push).map (·.toList) = [zeroTuple.toList]
#guard (sidePadTuples noSep collide .pull).map (·.toList) = [zeroTuple.toList]
#guard (blocks noSep 1).total ≤ 2 ^ noSep.μBus

/-- `collide`'s leaf stacks on `noSep` at the tests' challenge. -/
def pushNoSep : CMlPolynomialEval E noSep.μBus := pushLeaves noSep α β collide
def pullNoSep : CMlPolynomialEval E noSep.μBus := pullLeaves noSep α β collide
def countNoSep : CMlPolynomialEval E noSep.μBus := Bus.sideLeaves noSep 2 α β collide

-- Both products are `0`: they collide although the bus is unbalanced. No count column, so the
-- count product is the pad's `1` at every challenge.
#guard (∏ x : Fin (2 ^ noSep.μBus), pushNoSep[x]) = e0 ∧
  (∏ x : Fin (2 ^ noSep.μBus), pullNoSep[x]) = e0
#guard (∏ x : Fin (2 ^ noSep.μBus), countNoSep[x]) = e1

-- An honest padding row is harmless without the separator too: its padding leaves are `1`.
#guard M3Holds noSep () honestPad ∧ noSep.PaddingHonest honestPad
#guard (∏ x : Fin (2 ^ noSep.μBus), (pushLeaves noSep α β honestPad)[x]) =
  ∏ x : Fin (2 ^ noSep.μBus), (pullLeaves noSep α β honestPad)[x]

/-- `noSep` fails the separator condition: slot 0 of its push flush is `X₀`. -/
theorem noSep_separator_fails : ¬ ∀ j (f : Fin (noSep.flushes j).length)
    (r r' : Fin (noSep.width j) → K),
      ((flushPolys j f)[0]).eval r = ((flushPolys j f)[0]).eval r' := fun h ↦ by
  have h0 := h 0 ⟨0, by decide⟩ (fun _ ↦ 0) (fun _ ↦ 1)
  change (pushAll.2[0]).eval (fun _ ↦ (0 : K)) = (pushAll.2[0]).eval (fun _ ↦ 1) at h0
  simp [pushAll, CMvPolynomial.eval_X] at h0

/-- Two push leaves: `μ_bus = 1`, on both instances. -/
theorem padInst_μBus_eq (fl : List (Side × Vector (CMvPolynomial 2 K) 16))
    (hfl : ∀ f ∈ fl, ∀ k, (f.2.get k).totalDegree ≤ 2)
    (h : (padInst fl hfl).pushLeaves = 2 ^ 1) : (padInst fl hfl).μBus = 1 := by
  change Nat.clog 2 (padInst fl hfl).pushLeaves = 1
  rw [h, Nat.clog_pow _ _ one_lt_two]

theorem noSep_μBus_eq : noSep.μBus = 1 := padInst_μBus_eq _ _ (by decide)
theorem withSep_μBus_eq : withSep.μBus = 1 := padInst_μBus_eq _ _ (by decide)

/-- `noSep` meets every other side condition, so it fails them at the separator alone. -/
example : 1 ≤ noSep.d ∧ (∀ j, noSep.constraints j ≠ [] → noSep.τ j ≤ noSep.μBus) ∧
    leafCount noSep 1 ≤ 2 ^ noSep.μBus ∧ leafCount noSep 2 ≤ 2 ^ noSep.μBus := by
  rw [noSep_μBus_eq]
  exact ⟨by decide, fun _ h ↦ absurd rfl h, by decide, by decide⟩

theorem noSep_not_conditions : ¬ Conditions noSep := fun h ↦ noSep_separator_fails h.separator

/-- `withSep` meets the side conditions, the separator among them. -/
theorem withSep_conditions : Conditions withSep where
  one_le_d := by decide
  constrained := fun _ h ↦ absurd rfl h
  pull_fits := by rw [withSep_μBus_eq]; decide
  count_fits := by rw [withSep_μBus_eq]; decide
  separator := separator_of_zero fun _ f ↦ by
    obtain ⟨_ | _ | _, hf⟩ := f
    · show (pushSep.2)[0] = 0
      simp [pushSep]
    · show (pullSep.2)[0] = 0
      simp [pullSep]
    · simp at hf

/-- So its challenges are sound at the slot's error, `4·2^{μ_bus}/|E|`. -/
example : Typed.Security (challengeStep withSep) (Seam.commit withSep) (afterChallenge withSep)
    (Typed.drawErrors _ (overE (4 * 2 ^ withSep.μBus))) :=
  challengeSecurity withSep_conditions

-- On `withSep` the same stack is unbalanced and its padding tuples are `(1, 0, …)`: the products
-- differ at the tests' challenge.
#guard ¬ withSep.Balanced collide
#guard (sidePadTuples withSep collide .push).map (·.toList) = [1 :: List.replicate 15 0]
#guard (sidePadTuples withSep collide .pull).map (·.toList) = [1 :: List.replicate 15 0]
#guard (∏ x : Fin (2 ^ withSep.μBus), (pushLeaves withSep α β collide)[x]) ≠
  ∏ x : Fin (2 ^ withSep.μBus), (pullLeaves withSep α β collide)[x]

end LeanVMTests.Protocol.BusSecurity
