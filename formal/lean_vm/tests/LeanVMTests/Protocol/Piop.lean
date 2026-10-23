import LeanVM.Protocol.FlockSpec
import LeanVM.Protocol.Piop
import LeanVM.Protocol.Spine.Toy
import CompPoly.Multivariate.Eval
import CompPoly.Multivariate.MvPolyEquiv.Eval
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Oracle protocol tests

* **The side conditions have inhabitants, with and without a Flock region.** The toy instance
  (no Flock region, so the Flock phase is the pass-through) and `blocky`, one table of `2 ^ 8`
  rows with a push flush and a count column whose whole column is a Flock region with the BLAKE2s
  circuit's R1CS, both meet the bus phase's conditions and the degree bound. At `blocky` the
  Flock slot is the Flock phase itself.
* **The extractor computes**: on the toy, the composed extractor's first step evaluates and reads
  the committed stack back.
* **The statements, by type.** The two master theorems at both instances, with the relation, the
  extractor, the errors and the verifier spelled out: a change to their hypotheses or conclusions
  fails here.
-/

namespace LeanVMTests.Protocol.Piop

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Toy OracleComp OracleSpec CompPoly
  CPoly Interaction Interaction.Oracle Interaction.Oracle.Security

/-! ## The toy, with no Flock region -/

/-- A flush whose slot 0 is the zero polynomial meets the separator condition. -/
theorem separator_of_zero {I : M3Instance}
    (h0 : ∀ j (f : Fin (I.flushes j).length), (Bus.flushPolys j f)[0] = 0) :
    ∀ j (f : Fin (I.flushes j).length) (r r' : Fin (I.width j) → K),
      ((Bus.flushPolys j f)[0]).eval r = ((Bus.flushPolys j f)[0]).eval r' := fun j f r r' ↦ by
  rw [h0 j f, CMvPolynomial.eval_zero, CMvPolynomial.eval_zero]

/-- The toy meets the bus phase's conditions. -/
theorem toy_conditions : Bus.Conditions toy where
  one_le_d := by decide
  constrained := by decide
  pull_fits := by decide
  count_fits := by decide
  separator := separator_of_zero fun _ f ↦ by
    obtain ⟨_ | _, hf⟩ := f
    · show (Toy.flush.2)[0] = 0
      simp [Toy.flush]
    · simp at hf

example : toy.d ≤ 2 := by decide

example (initial : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (input : K)
    (q : Column toy.μ) (h : ((input, fun i ↦ i.elim0), q) ∈ M3HonestRel toy) :
    Pr{let x ← (leanVmPiop (leanVmPhases toy toy_conditions) initial).execute impl input q}[
      x.2.2 = some ()] = 1 :=
  leanVm_perfectCompleteness toy toy_conditions (by decide) initial impl input q h

/-- The verifier at the toy. -/
abbrev toyVerifier := leanVmVerifier (leanVmPhases toy toy_conditions)

example (initial : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : K) :
    ∃ cert : KnowledgeCertificate (piopSlot toy).tree (piopSlot toy).roles
        ⟨Column toy.μ, M3Holds toy s⟩,
      cert.extractor = piopExtractor _ (leanVmSecurity toy toy_conditions (by decide)) s ∧
      cert.challenges = Typed.schedule (piopSlot toy).tree (piopSlot toy).roles
        (piopSlot toy).samplers (piopErrors toy) ∧
      SamplesChallenges unifSpec (QueryImpl.id' unifSpec) (piopSlot toy).tree (piopSlot toy).roles
        (piopSlot toy).oracles initial impl _ (toyVerifier initial s) cert.challenges :=
  leanVm_knowledgeSoundness toy toy_conditions (by decide) initial impl s

-- The composed extractor computes: its commitment step reads the honest stack back.
#guard ((piopExtractor _ (leanVmSecurity toy toy_conditions (by decide)) (1 : K) honest).2.1
  ()).values = honest.values

/-! ## An instance with a Flock region -/

/-- One table of height `2 ^ 8` and width one. -/
abbrev blockyShape : Shape := ⟨1, fun _ ↦ 8, fun _ ↦ 1⟩

/-- The stack is the one column. -/
theorem readWith_id (q : Column 8) (c : blockyShape.ColumnId) :
    Layout.readWith (fun (_ : blockyShape.ColumnId) (z : Vector E 8) ↦ z) q c = q := by
  obtain ⟨v⟩ := q
  apply congrArg Column.mk
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn, boolIndex_boolVec]
  rfl

/-- The one flush: `(0, X₀, 0, …)`, pushed; slot 0, the domain separator, is constant. -/
def flush : Side × Vector (CMvPolynomial 1 K) 16 :=
  (.push, Vector.ofFn fun k ↦ if k.val = 1 then CMvPolynomial.X 0 else 0)

theorem flush_totalDegree (k : Fin 16) : (flush.2.get k).totalDegree ≤ 2 := by
  rw [totalDegree_equiv (S := K)]
  simp only [flush, Vector.get_ofFn]
  split
  · simp [CMvPolynomial.fromCMvPolynomial_X]
  · simp

/-- The instance: the table pushes its rows and counts with its column, which is a Flock region
of `2 ^ 0` blocks with the BLAKE2s circuit's R1CS. -/
abbrev blocky : M3Instance where
  toShape := blockyShape
  Stmt := Unit
  constraints := fun _ ↦ []
  flushes := fun _ ↦ [flush]
  d := 2
  constraints_degree := fun _ _ h ↦ absurd h (List.not_mem_nil)
  flushes_degree := fun _ f h k ↦ by rw [List.mem_singleton.mp h]; exact flush_totalDegree k
  counts := fun _ ↦ [0]
  rows := fun j ↦ 2 ^ blockyShape.τ j
  rows_le := fun _ ↦ le_rfl
  padRow := fun _ _ ↦ 0
  boundary := []
  μ := 8
  layout := ⟨fun _ z ↦ z, fun q c z ↦ by rw [readWith_id]⟩
  nLines := 0
  publicLines := fun _ ↦ #v[]
  flock := some ⟨⟨0, 0⟩, 0, rfl, Blake2sFlock.blake2sFlockSpec.r1cs⟩

/-- `blocky` meets the bus phase's conditions. -/
theorem blocky_conditions : Bus.Conditions blocky where
  one_le_d := by decide
  constrained := by decide
  pull_fits := by decide
  count_fits := by decide
  separator := separator_of_zero fun _ f ↦ by
    obtain ⟨_ | _, hf⟩ := f
    · show (LeanVMTests.Protocol.Piop.flush.2)[0] = 0
      simp [LeanVMTests.Protocol.Piop.flush]
    · simp at hf

example : blocky.flock.isSome := rfl

example (initial : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (input : Unit)
    (q : Column blocky.μ) (h : ((input, fun i ↦ i.elim0), q) ∈ M3HonestRel blocky) :
    Pr{let x ← (leanVmPiop (leanVmPhases blocky blocky_conditions) initial).execute impl input q}[
      x.2.2 = some ()] = 1 :=
  leanVm_perfectCompleteness blocky blocky_conditions (by decide) initial impl input q h

/-- The knowledge certificate at `blocky`, with the composed extractor and the slots' errors. -/
example (initial : PFunctor.{0, 0}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (s : Unit) :
    ∃ cert : KnowledgeCertificate (piopSlot blocky).tree (piopSlot blocky).roles
        ⟨Column blocky.μ, M3Holds blocky s⟩,
      cert.extractor = piopExtractor _ (leanVmSecurity blocky blocky_conditions (by decide)) s :=
  have ⟨cert, h, _⟩ := leanVm_knowledgeSoundness blocky blocky_conditions (by decide) initial impl s
  ⟨cert, h⟩

end LeanVMTests.Protocol.Piop
