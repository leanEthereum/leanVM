module

public import LeanVMCircuits.MulDiv
public import LeanVMCircuits.Blake2s.Linkage
public import LeanVMCircuits.Blake2s.Export
import all Init.Data.Array.Basic
import all Init.Data.Vector.FinRange

-- Closed kernel reduction traverses the glue around the multiplier.
set_option maxRecDepth 65536

@[expose] public section

/-!
The multiplication classes lowered to gates: the multiplier's steps in closed form, the glue around them checked by
reduction in Lean's kernel.
-/

namespace LeanVMCircuits.MulDivExport

attribute [local semireducible] Multiply.elaborated

open LeanVMCircuits Gates Flock Netlist

theorem stepsFrom_length (inp : ℕ → Affine) (base : ℕ) : ∀ (i : ℕ) (gs : List Gate),
    (stepsFrom inp base i gs).length = gs.length
  | _, [] => rfl
  | i, _ :: gs => by simp [stepsFrom, stepsFrom_length inp base (i + 1) gs]

/-- The multiplier's gates from `start`, then glue lowering to `rest`. -/
theorem lower_split (start : ℕ) (gates : List Gate) (inp : ℕ → Expression Bit) (ainp : ℕ → Affine)
    (h : InputsLower inp ainp start) (hw : wellOrdered 0 gates = true) (rest : List (FlatOperation Bit))
    (restSteps : List Step) (hrest : Gates.lower (start + gates.length) rest = .ok restSteps) :
    Gates.lower start (Operations.toFlat (opsFrom inp start 0 gates) ++ rest) =
      .ok (stepsFrom ainp start 0 gates ++ restSteps) := by
  have hm := lower_opsFrom inp ainp start h 0 gates hw
  rw [Nat.add_zero] at hm
  rw [Gates.lower_append _ _ _ _ hm, stepsFrom_length, hrest]
  rfl

/-- A checked flattening and lowering of the glue gives its steps. -/
theorem lower_glue (next : ℕ) (glue : Operations Bit) (steps : List Step)
    (h : (flatten 128 (.nested ("post", Operations.toNested glue))).bind (Gates.lower next) = .ok steps) :
    Gates.lower next (Operations.toFlat glue) = .ok steps := by
  cases hf : flatten 128 (.nested ("post", Operations.toNested glue)) with
  | error m => rw [hf] at h; cases h
  | ok flat =>
    rw [hf] at h
    have := flatten_correct _ _ _ hf
    simp only [Operations.toNested_toFlat] at this
    rw [← this]
    exact h

/-! A multiplier's steps on any operands are the generated multiplier function's, renamed: what a call of it emits. -/

/-- The multiplier function's operands: ports `a` and `b` as variables `0..128`, its own wires from 128. -/
def canon (j : ℕ) : Affine := if j < 128 then .var j else .zero

/-- How a call at first variable `base` on operands `ainp` binds the function's variables. -/
def callBinding (ainp : ℕ → Affine) (base v : ℕ) : Affine := if v < 128 then ainp v else .var (base + (v - 128))

def Step.rename (σ : ℕ → Affine) (shift : ℕ → ℕ) : Step → Step
  | .define o v => .define (shift o) (Blake2s.Export.subst σ v)
  | .product o l r => .product (shift o) (Blake2s.Export.subst σ l) (Blake2s.Export.subst σ r)

theorem lower_call (ainp : ℕ → Affine) (base : ℕ) (hz : ∀ j, 128 ≤ j → ainp j = .zero) :
    ∀ a : Aff, a.lower ainp base = Blake2s.Export.subst (callBinding ainp base) (a.lower canon 128)
  | .zero => rfl
  | .one => rfl
  | .input j => by
    by_cases h : j < 128
    · simp [Aff.lower, canon, h, Blake2s.Export.subst, callBinding]
    · simp [Aff.lower, canon, h, Blake2s.Export.subst, hz j (by omega)]
  | .loc i => by simp [Aff.lower, Blake2s.Export.subst, callBinding]
  | .xor l r => by simp [Aff.lower, Blake2s.Export.subst, lower_call ainp base hz l, lower_call ainp base hz r]

/-- The steps of a multiplier at `base` on operands `ainp` are the multiplier function's steps, renamed by the call. -/
theorem multiplier_call (ainp : ℕ → Affine) (base : ℕ) (hz : ∀ j, 128 ≤ j → ainp j = .zero) :
    ∀ (i : ℕ) (gs : List Gate), stepsFrom ainp base i gs =
      (stepsFrom canon 128 i gs).map (Step.rename (callBinding ainp base) (fun o => base + (o - 128)))
  | _, [] => rfl
  | i, g :: gs => by
    simp only [stepsFrom, List.map_cons, multiplier_call ainp base hz (i + 1) gs]
    congr 1
    cases g <;> simp [Gate.step, Step.rename, lower_call ainp base hz]

namespace Mul

def inputs : Var LeanVMCircuits.Mul.Input Bit := {
  v1 := Vector.mapFinRange 64 fun i => .var ⟨i.val⟩
  v2 := Vector.mapFinRange 64 fun i => .var ⟨64 + i.val⟩
  word := .var ⟨128⟩
}

def start : ℕ := 129

def ops : Operations Bit := ((LeanVMCircuits.Mul.circuit.main inputs) start).2

def minp : Var Multiply.Input Bit := { a := inputs.v1, b := inputs.v2 }

theorem flat_split : (LeanVMCircuits.Mul.circuit.toSubcircuit start inputs).ops.toFlat =
    Operations.toFlat (opsFrom (Multiply.inputsOf minp) start 0 (Multiply.layout 64).gates) ++
      Operations.toFlat (ops.drop 1) := by
  rw [Blake2s.toSubcircuit_toFlat]
  have hops : ops = .subcircuit ((Multiply.circuit 64).toSubcircuit start minp) :: ops.drop 1 := rfl
  change Operations.toFlat ops = _
  rw [hops]
  simp only [Operations.toFlat, Blake2s.toSubcircuit_toFlat, List.drop_succ_cons, List.drop_zero]
  rfl

/-- The multiplier's inputs: the ports' variables. -/
def ainp (j : ℕ) : Affine := if j < 128 then .var j else .zero

theorem ainp_zero : ∀ j, 128 ≤ j → ainp j = .zero := fun j hj => by simp [ainp, show ¬ j < 128 by omega]

theorem inputsLower : InputsLower (Multiply.inputsOf minp) ainp start := by
  intro j
  unfold Multiply.inputsOf ainp
  by_cases h1 : j < 64
  · simp [h1, show j < 128 by omega, minp, inputs, lowerAffine, Affine.bounded, start, Vector.getElem_mapFinRange]
    omega
  · by_cases h2 : j < 128
    · simp [h1, h2, show j - 64 < 64 by omega, minp, inputs, lowerAffine, Affine.bounded, start,
        Vector.getElem_mapFinRange]
      omega
    · simp [h1, h2, show ¬ j - 64 < 64 by omega, lowerAffine, Affine.bounded]

/-- The glue after the multiplier, flattened by the kernel-computable `Flock.flatten`. -/
def postFlat : Except String (List (FlatOperation Bit)) := flatten 128 (.nested ("post", Operations.toNested (ops.drop 1)))

def post : Except String (List Step) := postFlat.bind (Gates.lower (start + Multiply.total 64))

theorem post_ok : post.isOk = true := by decide +kernel

def output : List (Expression Bit) := (LeanVMCircuits.Mul.circuit.output inputs start).toList

def outs : Except String (List Affine) := lowerOutputs output

theorem outs_ok : outs.isOk = true := by decide +kernel

def postSteps : List Step := checked post post_ok

def outputs : List Affine := checked outs outs_ok

def artifact : Gates.Artifact :=
  { start, steps := stepsFrom ainp start 0 (Multiply.layout 64).gates ++ postSteps, outputs }

theorem source : Gates.lowerCircuit LeanVMCircuits.Mul.circuit start inputs = .ok artifact := by
  have hrest : Gates.lower (start + (Multiply.layout 64).gates.length) (Operations.toFlat (ops.drop 1)) =
      .ok postSteps := by
    rw [Multiply.gates_length 64 (by decide)]
    exact lower_glue _ _ _ (checked_eq post post_ok)
  have hlow := lower_split start _ _ ainp inputsLower (Multiply.layout_wellOrdered _ (by decide)) _ _ hrest
  rw [← flat_split] at hlow
  simp only [Gates.lowerCircuit, Gates.lowerAt, hlow]
  rw [show lowerOutputs (toElements (M := fields 64) (LeanVMCircuits.Mul.circuit.output inputs start)).toList =
    .ok outputs from checked_eq outs outs_ok]
  rfl

/-- The ports' bits under an assignment: `v1`, `v2`, then the word flag. -/
def ports (a : ℕ → Bit) : LeanVMCircuits.Mul.Input Bit :=
  { v1 := Vector.ofFn fun i => a i.val, v2 := Vector.ofFn fun i => a (64 + i.val), word := a 128 }

theorem eval_inputs (env : Environment Bit) : eval env inputs = ports env.get := by
  simp only [inputs, ports, circuit_norm]
  refine ⟨?_, ?_⟩ <;> ext i hi <;> simp [Vector.getElem_mapFinRange, Expression.eval]

/-- Every assignment satisfying the artifact's steps outputs `MUL`, or `MULW` when the flag is set. The assignment
is arbitrary: nothing assumes it was generated honestly. -/
theorem soundness (a : ℕ → Bit) (hholds : artifact.Holds a) :
    ∃ out : Vector Bit 64, artifact.outputs.map (Affine.eval a) = out.toList ∧
      Adder.value out = Rv64.mul (a 128 = 1) (Adder.value (ports a).v1) (Adder.value (ports a).v2) := by
  set env : Environment Bit := { get := a, data := fun _ _ => #[] }
  have hs := lowerCircuit_soundness LeanVMCircuits.Mul.circuit start inputs artifact source env trivial hholds
  refine ⟨eval env (LeanVMCircuits.Mul.circuit.output inputs start), ?_, ?_⟩
  · rw [hs.2]; simp only [circuit_norm, Vector.toList_map]; rfl
  · have h1 := hs.1
    rw [eval_inputs] at h1
    exact h1

/-- Every assignment of the ports extends to one satisfying every step of the artifact. -/
theorem completeness (a : ℕ → Bit) : ∃ final, AgreeBelow start a final ∧ artifact.Holds final :=
  lowerCircuit_completeness LeanVMCircuits.Mul.circuit start inputs artifact source a

end Mul

namespace Mulh

def inputs : Var LeanVMCircuits.Mulh.Input Bit := {
  v1 := Vector.mapFinRange 64 fun i => .var ⟨i.val⟩
  v2 := Vector.mapFinRange 64 fun i => .var ⟨64 + i.val⟩
  signed1 := .var ⟨128⟩
  signed2 := .var ⟨129⟩
}

def start : ℕ := 130

def ops : Operations Bit := ((LeanVMCircuits.Mulh.circuit.main inputs) start).2

def minp : Var Multiply.Input Bit := { a := inputs.v1, b := inputs.v2 }

theorem flat_split : (LeanVMCircuits.Mulh.circuit.toSubcircuit start inputs).ops.toFlat =
    Operations.toFlat (opsFrom (Multiply.inputsOf minp) start 0 (Multiply.layout 128).gates) ++
      Operations.toFlat (ops.drop 1) := by
  rw [Blake2s.toSubcircuit_toFlat]
  have hops : ops = .subcircuit ((Multiply.circuit 128).toSubcircuit start minp) :: ops.drop 1 := rfl
  change Operations.toFlat ops = _
  rw [hops]
  simp only [Operations.toFlat, Blake2s.toSubcircuit_toFlat, List.drop_succ_cons, List.drop_zero]
  rfl

/-- The multiplier's inputs: the ports' variables. -/
def ainp (j : ℕ) : Affine := if j < 128 then .var j else .zero

theorem ainp_zero : ∀ j, 128 ≤ j → ainp j = .zero := fun j hj => by simp [ainp, show ¬ j < 128 by omega]

theorem inputsLower : InputsLower (Multiply.inputsOf minp) ainp start := by
  intro j
  unfold Multiply.inputsOf ainp
  by_cases h1 : j < 64
  · simp [h1, show j < 128 by omega, minp, inputs, lowerAffine, Affine.bounded, start, Vector.getElem_mapFinRange]
    omega
  · by_cases h2 : j < 128
    · simp [h1, h2, show j - 64 < 64 by omega, minp, inputs, lowerAffine, Affine.bounded, start,
        Vector.getElem_mapFinRange]
      omega
    · simp [h1, h2, show ¬ j - 64 < 64 by omega, lowerAffine, Affine.bounded]

/-- The glue after the multiplier, flattened by the kernel-computable `Flock.flatten`. -/
def postFlat : Except String (List (FlatOperation Bit)) := flatten 128 (.nested ("post", Operations.toNested (ops.drop 1)))

def post : Except String (List Step) := postFlat.bind (Gates.lower (start + Multiply.total 128))

theorem post_ok : post.isOk = true := by decide +kernel

def output : List (Expression Bit) := (LeanVMCircuits.Mulh.circuit.output inputs start).toList

def outs : Except String (List Affine) := lowerOutputs output

theorem outs_ok : outs.isOk = true := by decide +kernel

def postSteps : List Step := checked post post_ok

def outputs : List Affine := checked outs outs_ok

def artifact : Gates.Artifact :=
  { start, steps := stepsFrom ainp start 0 (Multiply.layout 128).gates ++ postSteps, outputs }

theorem source : Gates.lowerCircuit LeanVMCircuits.Mulh.circuit start inputs = .ok artifact := by
  have hrest : Gates.lower (start + (Multiply.layout 128).gates.length) (Operations.toFlat (ops.drop 1)) =
      .ok postSteps := by
    rw [Multiply.gates_length 128 (by decide)]
    exact lower_glue _ _ _ (checked_eq post post_ok)
  have hlow := lower_split start _ _ ainp inputsLower (Multiply.layout_wellOrdered _ (by decide)) _ _ hrest
  rw [← flat_split] at hlow
  simp only [Gates.lowerCircuit, Gates.lowerAt, hlow]
  rw [show lowerOutputs (toElements (M := fields 64) (LeanVMCircuits.Mulh.circuit.output inputs start)).toList =
    .ok outputs from checked_eq outs outs_ok]
  rfl

/-- The ports' bits under an assignment: `v1`, `v2`, then the two signedness flags. -/
def ports (a : ℕ → Bit) : LeanVMCircuits.Mulh.Input Bit :=
  { v1 := Vector.ofFn fun i => a i.val, v2 := Vector.ofFn fun i => a (64 + i.val), signed1 := a 128,
    signed2 := a 129 }

theorem eval_inputs (env : Environment Bit) : eval env inputs = ports env.get := by
  simp only [inputs, ports, circuit_norm]
  refine ⟨?_, ?_⟩ <;> ext i hi <;> simp [Vector.getElem_mapFinRange, Expression.eval]

/-- Every assignment satisfying the artifact's steps outputs `MULHU`, `MULHSU` or `MULH` as the flags select. The
assignment is arbitrary: nothing assumes it was generated honestly. -/
theorem soundness (a : ℕ → Bit) (hholds : artifact.Holds a) :
    ∃ out : Vector Bit 64, artifact.outputs.map (Affine.eval a) = out.toList ∧
      Adder.value out = Rv64.mulh (a 128 = 1) (a 129 = 1) (Adder.value (ports a).v1) (Adder.value (ports a).v2) := by
  set env : Environment Bit := { get := a, data := fun _ _ => #[] }
  have hs := lowerCircuit_soundness LeanVMCircuits.Mulh.circuit start inputs artifact source env trivial hholds
  refine ⟨eval env (LeanVMCircuits.Mulh.circuit.output inputs start), ?_, ?_⟩
  · rw [hs.2]; simp only [circuit_norm, Vector.toList_map]; rfl
  · have h1 := hs.1
    rw [eval_inputs] at h1
    exact h1

/-- Every assignment of the ports extends to one satisfying every step of the artifact. -/
theorem completeness (a : ℕ → Bit) : ∃ final, AgreeBelow start a final ∧ artifact.Holds final :=
  lowerCircuit_completeness LeanVMCircuits.Mulh.circuit start inputs artifact source a

end Mulh


namespace Div

attribute [local semireducible] LeanVMCircuits.Div.magnitudes LeanVMCircuits.Div.extend LeanVMCircuits.Div.negate

def inputs : Var LeanVMCircuits.Div.Input Bit := {
  v1 := Vector.mapFinRange 64 fun i => .var ⟨i.val⟩
  v2 := Vector.mapFinRange 64 fun i => .var ⟨64 + i.val⟩
  signed := .var ⟨128⟩
  rem := .var ⟨129⟩
  word := .var ⟨130⟩
  q := Vector.mapFinRange 64 fun i => .var ⟨131 + i.val⟩
  r := Vector.mapFinRange 64 fun i => .var ⟨195 + i.val⟩
}

def start : ℕ := 259

def ops : Operations Bit := ((LeanVMCircuits.Div.circuit.main inputs) start).2

def operands : Var LeanVMCircuits.Div.Operands Bit := ⟨inputs.signed, inputs.word, inputs.v1, inputs.v2⟩

def hints : Var LeanVMCircuits.Div.Hints Bit :=
  ⟨inputs.q, inputs.r, (LeanVMCircuits.Div.magnitudes.output operands start).nAbs,
    (LeanVMCircuits.Div.magnitudes.output operands start).dAbs⟩

/-- The multiplier's operands: the quotient and the divisor's magnitude. -/
def minp : Var Multiply.Input Bit := { a := hints.q, b := hints.dAbs }

def mid : ℕ := start + 196

def checkOps : Operations Bit := ((LeanVMCircuits.Div.check.main hints) mid).2

theorem flat_split : (LeanVMCircuits.Div.circuit.toSubcircuit start inputs).ops.toFlat =
    Operations.toFlat (ops.take 1) ++
      (Operations.toFlat (opsFrom (Multiply.inputsOf minp) mid 0 (Multiply.layout 128).gates) ++
        Operations.toFlat (checkOps.drop 1 ++ ops.drop 2)) := by
  rw [Blake2s.toSubcircuit_toFlat]
  have hops : ops = .subcircuit (LeanVMCircuits.Div.magnitudes.toSubcircuit start operands) ::
      .subcircuit (LeanVMCircuits.Div.check.toSubcircuit mid hints) :: ops.drop 2 := rfl
  have hc : checkOps = .subcircuit ((Multiply.circuit 128).toSubcircuit mid minp) :: checkOps.drop 1 := rfl
  change Operations.toFlat ops = _
  rw [hops]
  simp only [Operations.toFlat, Blake2s.toSubcircuit_toFlat, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
    List.take_zero, List.append_nil, Blake2s.toFlat_append]
  change _ ++ (Operations.toFlat checkOps ++ _) = _
  rw [hc]
  simp only [Operations.toFlat, Blake2s.toSubcircuit_toFlat, List.drop_succ_cons, List.drop_zero, List.append_assoc]
  rfl

def preFlat : Except String (List (FlatOperation Bit)) := flatten 128 (.nested ("post", Operations.toNested (ops.take 1)))

def pre : Except String (List Step) := preFlat.bind (Gates.lower start)

theorem pre_ok : pre.isOk = true := by decide +kernel

def preSteps : List Step := checked pre pre_ok

theorem pre_length : preSteps.length = 196 := by decide +kernel

/-- The multiplier's inputs, lowered. -/
def ainp (j : ℕ) : Affine :=
  match lowerAffine (Multiply.inputsOf minp j) with
  | .ok affine => affine
  | .error _ => .zero

theorem ainp_ok : ∀ j : Fin 128, (lowerAffine (Multiply.inputsOf minp j.val)).isOk && (ainp j.val).bounded mid :=
  by decide +kernel

theorem inputsLower : InputsLower (Multiply.inputsOf minp) ainp mid := by
  intro j
  by_cases hj : j < 128
  · have h := ainp_ok ⟨j, hj⟩
    simp only [Bool.and_eq_true] at h
    refine ⟨?_, h.2⟩
    have h1 := h.1
    unfold ainp
    cases hl : lowerAffine (Multiply.inputsOf minp j) with
    | error m => rw [hl] at h1; cases h1
    | ok a => rfl
  · have h0 : Multiply.inputsOf minp j = 0 := by simp [Multiply.inputsOf, show ¬ j < 64 by omega,
      show ¬ j - 64 < 64 by omega]
    simp [ainp, h0, lowerAffine, Affine.bounded]

theorem ainp_zero : ∀ j, 128 ≤ j → ainp j = .zero := fun j hj => by
  have h0 : Multiply.inputsOf minp j = 0 := by simp [Multiply.inputsOf, show ¬ j < 64 by omega,
    show ¬ j - 64 < 64 by omega]
  simp [ainp, h0, lowerAffine]

def postFlat : Except String (List (FlatOperation Bit)) :=
  flatten 128 (.nested ("post", Operations.toNested (checkOps.drop 1 ++ ops.drop 2)))

def post : Except String (List Step) := postFlat.bind (Gates.lower (mid + Multiply.total 128))

theorem post_ok : post.isOk = true := by decide +kernel

def postSteps : List Step := checked post post_ok

def output : List (Expression Bit) :=
  (toElements (M := LeanVMCircuits.Div.Output) (LeanVMCircuits.Div.circuit.output inputs start)).toList

def outs : Except String (List Affine) := lowerOutputs output

theorem outs_ok : outs.isOk = true := by decide +kernel

def outputs : List Affine := checked outs outs_ok

def artifact : Gates.Artifact :=
  { start, steps := preSteps ++ (stepsFrom ainp mid 0 (Multiply.layout 128).gates ++ postSteps), outputs }

theorem source : Gates.lowerCircuit LeanVMCircuits.Div.circuit start inputs = .ok artifact := by
  have hrest : Gates.lower (mid + (Multiply.layout 128).gates.length)
      (Operations.toFlat (checkOps.drop 1 ++ ops.drop 2)) = .ok postSteps := by
    rw [Multiply.gates_length 128 (by decide)]
    exact lower_glue _ _ _ (checked_eq post post_ok)
  have hmid := lower_split mid _ _ ainp inputsLower (Multiply.layout_wellOrdered _ (by decide)) _ _ hrest
  have hpre : Gates.lower start (Operations.toFlat (ops.take 1)) = .ok preSteps :=
    lower_glue _ _ _ (checked_eq pre pre_ok)
  have hlow : Gates.lower start ((LeanVMCircuits.Div.circuit.toSubcircuit start inputs).ops.toFlat) =
      .ok (preSteps ++ (stepsFrom ainp mid 0 (Multiply.layout 128).gates ++ postSteps)) := by
    rw [flat_split, Gates.lower_append _ _ _ _ hpre, pre_length, show start + 196 = mid from rfl, hmid]
    rfl
  simp only [Gates.lowerCircuit, Gates.lowerAt, hlow]
  rw [show lowerOutputs (toElements (M := LeanVMCircuits.Div.Output)
    (LeanVMCircuits.Div.circuit.output inputs start)).toList = .ok outputs from checked_eq outs outs_ok]
  rfl

/-- The ports' bits under an assignment: `v1`, `v2`, the flags `signed`, `rem`, `word`, then the hints `q`, `r`. -/
def ports (a : ℕ → Bit) : LeanVMCircuits.Div.Input Bit :=
  { v1 := Vector.ofFn fun i => a i.val, v2 := Vector.ofFn fun i => a (64 + i.val), signed := a 128, rem := a 129,
    word := a 130, q := Vector.ofFn fun i => a (131 + i.val), r := Vector.ofFn fun i => a (195 + i.val) }

theorem eval_inputs (env : Environment Bit) : eval env inputs = ports env.get := by
  simp only [inputs, ports, circuit_norm]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i hi <;> simp [Vector.getElem_mapFinRange, Expression.eval]

/-- Every assignment satisfying the artifact's steps outputs `out` then `bad` with `bad` set exactly when the divisor
is nonzero and the hints are not the magnitudes' quotient and remainder, and, while `bad` is clear, `out` is RISC-V's
`DIV`, `DIVU`, `REM`, `REMU` or word form as the flags select. The assignment is arbitrary: nothing assumes it was
generated honestly. -/
theorem soundness (a : ℕ → Bit) (hholds : artifact.Holds a) :
    ∃ o : LeanVMCircuits.Div.Output Bit, artifact.outputs.map (Affine.eval a) = (toElements o).toList ∧
      LeanVMCircuits.Div.Spec (ports a) o := by
  set env : Environment Bit := { get := a, data := fun _ _ => #[] }
  have hs := lowerCircuit_soundness LeanVMCircuits.Div.circuit start inputs artifact source env trivial hholds
  refine ⟨eval env (LeanVMCircuits.Div.circuit.output inputs start), ?_, ?_⟩
  · rw [hs.2, ProvableType.toElements_eval, Vector.toList_map]
  · have h1 := hs.1
    rw [eval_inputs] at h1
    exact h1

/-- Every assignment of the ports extends to one satisfying every step of the artifact. -/
theorem completeness (a : ℕ → Bit) : ∃ final, AgreeBelow start a final ∧ artifact.Holds final :=
  lowerCircuit_completeness LeanVMCircuits.Div.circuit start inputs artifact source a

end Div

end LeanVMCircuits.MulDivExport
