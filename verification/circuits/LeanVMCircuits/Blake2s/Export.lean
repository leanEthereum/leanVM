module

public import LeanVMCircuits.Blake2s.Linkage
public import LeanVMCircuits.AdderFamily

@[expose] public section

/-!
The exported BLAKE2s compression: arbitrary-witness soundness against RFC 7693 and completeness of the exact artifact
the Clean circuit lowers to, and that artifact's additions as instances of the exported 32-bit and 31-bit adders.
-/

namespace LeanVMCircuits.Blake2s.Export

open LeanVMCircuits Gates Rfc7693 Compress

attribute [local irreducible] program

/-- The ports' bits under an assignment: `t`, `f0`, `h`, `m`. -/
def ports (a : ℕ → Bit) : Input Bit :=
  { t := Vector.ofFn fun i => a i.val, f0 := Vector.ofFn fun i => a (64 + i.val),
    h := Vector.ofFn fun i => a (96 + i.val), m := Vector.ofFn fun i => a (352 + i.val) }

/-- The artifact's 256 output bits under an assignment. -/
def result (a : ℕ → Bit) : Vector Bit 256 :=
  Vector.ofFn fun k => (outputAffine (modelAffs program.ops initialAffines inputBits) k).eval a

theorem eval_inputs (env : Environment Bit) : eval env inputs = ports env.get := by
  simp only [inputs, ports, circuit_norm]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i hi <;> simp [Expression.eval]

/-- Every assignment satisfying the artifact's steps outputs RFC 7693's F of its ports, for both finalization words.
The assignment is arbitrary: nothing assumes it was generated honestly. -/
theorem soundness (a : ℕ → Bit) (hholds : artifact.Holds a) (f : Bool)
    (hf : toWord (ports a).f0 = if f then BitVec.allOnes 32 else 0) :
    words (k := 8) (result a) =
      F (words (ports a).h) (words (ports a).m) (toWord (ports a).t) f := by
  set env : Environment Bit := { get := a, data := fun _ _ => #[] }
  have hs := lowerCircuit_soundness Compress.circuit inputBits inputs artifact lowered env trivial hholds
  have hres : eval env (Compress.circuit.output inputs inputBits) = result a := by
    have h2 := hs.2
    apply Vector.toList_inj.mp
    simp only [artifact, List.map_ofFn] at h2
    rw [result, Vector.toList_ofFn]
    refine Eq.trans ?_ h2.symm
    simp only [circuit_norm, Vector.toList_map]
    rfl
  have h1 := hs.1
  rw [eval_inputs, hres] at h1
  exact h1 f hf

/-- Every assignment of the ports extends to one satisfying every step of the artifact. -/
theorem completeness (a : ℕ → Bit) : ∃ final, Flock.AgreeBelow inputBits a final ∧ artifact.Holds final :=
  lowerCircuit_completeness Compress.circuit inputBits inputs artifact lowered a

/-! The 31-bit wrapping adder, for a literal addend with a zero low bit. -/

def adder31 : Flock.Artifact := Flock.checked (Flock.lowerCircuit 30) (by decide +kernel)

theorem adder31_source : Flock.lowerCircuit 30 = .ok adder31 := Flock.checked_eq _ _

theorem adder31_soundness (env : Environment Bit) (hrows : adder31.rows.Forall (Flock.Row.Holds env.get)) :
    adder31.value env.get =
      (Adder.value ((Flock.inputs 30).x.map (Expression.eval env)) +
        Adder.value ((Flock.inputs 30).y.map (Expression.eval env))) % 2 ^ 31 :=
  Flock.exported_soundness 30 adder31 adder31_source env hrows

theorem adder31_layout :
    adder31.rows.map Flock.Row.output = (List.range 30).map (62 + ·) ∧ adder31.outputs.length = 31 := by
  decide +kernel

theorem adder31_wellFormed : Flock.wellFormed 62 adder31.rows = true := by decide +kernel

theorem adder31_complete (inputs : ℕ → Bit) :
    ∃ assignment, Flock.AgreeBelow 62 inputs assignment ∧ adder31.rows.Forall (Flock.Row.Holds assignment) :=
  Flock.witness_exists adder31.rows 62 inputs adder31_wellFormed

/-! The artifact's additions are the exported adders' rows, renamed. -/

/-- The adder of `w + 1` bits as exported: inputs `0..2w+2`, products from `2w + 2`. -/
def canonicalRows (w : ℕ) : List Flock.Row :=
  (List.range w).map fun i =>
    { output := 2 * (w + 1) + i,
      left := .xor (.var i) (carryAffine (2 * (w + 1)) .zero i),
      right := .xor (.var (w + 1 + i)) (carryAffine (2 * (w + 1)) .zero i) }

def canonicalOutputs (w : ℕ) : List Flock.Affine :=
  (List.range (w + 1)).map (sumAffine (2 * (w + 1)) (.var ·) (fun i => .var (w + 1 + i)) .zero)

theorem adder32_canonical : Flock.adder32.rows = canonicalRows 31 ∧ Flock.adder32.outputs = canonicalOutputs 31 := by
  decide +kernel

theorem adder31_canonical : adder31.rows = canonicalRows 30 ∧ adder31.outputs = canonicalOutputs 30 := by
  decide +kernel

/-- Each variable replaced by an affine form: how a generated adder function binds its operand wires. -/
def subst (σ : ℕ → Flock.Affine) : Flock.Affine → Flock.Affine
  | .zero => .zero
  | .one => .one
  | .var i => σ i
  | .xor a b => .xor (subst σ a) (subst σ b)

/-- The renaming a call of the `w + 1`-bit adder at first variable `n` makes: `x`, `y`, then the products. -/
def binding (w n : ℕ) (x y : ℕ → Flock.Affine) (i : ℕ) : Flock.Affine :=
  if i < w + 1 then x i else if i < 2 * (w + 1) then y (i - (w + 1)) else .var (n + (i - 2 * (w + 1)))

theorem subst_carry (w n : ℕ) (x y : ℕ → Flock.Affine) (i : ℕ) :
    subst (binding w n x y) (carryAffine (2 * (w + 1)) .zero i) = carryAffine n .zero i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [carryAffine, subst, ih, binding]
    congr 2
    simp only [show ¬(2 * (w + 1) + i < w + 1) by omega, show ¬(2 * (w + 1) + i < 2 * (w + 1)) by omega, if_false]
    congr 2
    omega

/-- A call of the exported adder at `n` on operands `x`, `y`: the products of `adderSteps`, then the sum bits. -/
theorem adder_instance (w n : ℕ) (x y : ℕ → Flock.Affine) :
    (canonicalRows w).map (fun r => Step.product (n + (r.output - 2 * (w + 1))) (subst (binding w n x y) r.left)
        (subst (binding w n x y) r.right)) = adderSteps n w x y .zero ∧
      (canonicalOutputs w).map (subst (binding w n x y)) = (List.range (w + 1)).map (sumAffine n x y .zero) := by
  constructor
  · simp only [canonicalRows, adderSteps, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    simp only [Function.comp, subst, subst_carry, binding, show i < w + 1 by omega, if_true,
      show ¬(w + 1 + i < w + 1) by omega, show w + 1 + i < 2 * (w + 1) by omega, if_false]
    congr 3
    · omega
    · omega
  · simp only [canonicalOutputs, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    simp only [Function.comp, sumAffine, subst, subst_carry, binding, show i < w + 1 by omega, if_true,
      show ¬(w + 1 + i < w + 1) by omega, show w + 1 + i < 2 * (w + 1) by omega, if_false]
    congr 2
    omega


/-- An addition's products and sum bits are exactly a call of the exported 32-bit adder `adder32`. -/
theorem adder32_call (n : ℕ) (x y : ℕ → Flock.Affine) :
    Flock.adder32.rows.map (fun r => Step.product (n + (r.output - 64)) (subst (binding 31 n x y) r.left)
        (subst (binding 31 n x y) r.right)) = adderSteps n 31 x y .zero ∧
      Flock.adder32.outputs.map (subst (binding 31 n x y)) = (List.range 32).map (sumAffine n x y .zero) := by
  rw [adder32_canonical.1, adder32_canonical.2]
  exact adder_instance 31 n x y

/-- An even literal's addition is exactly a call of the exported 31-bit adder `adder31` on the upper bits. -/
theorem adder31_call (n : ℕ) (x y : ℕ → Flock.Affine) :
    adder31.rows.map (fun r => Step.product (n + (r.output - 62)) (subst (binding 30 n x y) r.left)
        (subst (binding 30 n x y) r.right)) = adderSteps n 30 x y .zero ∧
      adder31.outputs.map (subst (binding 30 n x y)) = (List.range 31).map (sumAffine n x y .zero) := by
  rw [adder31_canonical.1, adder31_canonical.2]
  exact adder_instance 30 n x y

end LeanVMCircuits.Blake2s.Export
