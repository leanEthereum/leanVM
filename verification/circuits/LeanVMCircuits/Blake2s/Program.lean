module

public import LeanVMCircuits.Blake2s.Ops

@[expose] public section

/-!
A straight-line program over 32-bit registers, and the Clean circuit running it.

Each operation appends one register: its result. The Clean circuit runs an operation as the subcircuit of its word
operation, so its constraints are exactly those of the subcircuits, in program order.
-/

namespace LeanVMCircuits.Blake2s

open LeanVMCircuits

abbrev Word := BitVec 32

inductive Op where
  /-- `x + y` modulo `2^32`. -/
  | add (x y : ℕ)
  /-- `k + y` modulo `2^32` for an odd literal `k`. -/
  | addOdd (k : Word) (y : ℕ)
  /-- `k + y` modulo `2^32` for an even literal `k`. -/
  | addEven (k : Word) (y : ℕ)
  /-- `(x ^ y) >>> r`. -/
  | xorRotr (r : Fin 32) (x y : ℕ)
  deriving Repr, DecidableEq

/-- A literal's parity matches the adder the operation names. -/
def Op.valid : Op → Bool
  | .addOdd k _ => k.getLsbD 0
  | .addEven k _ => !k.getLsbD 0
  | _ => true

/-- An operation's result on register values. -/
def Op.eval (values : List Word) : Op → Word
  | .add x y => values.getD x 0 + values.getD y 0
  | .addOdd k y | .addEven k y => k + values.getD y 0
  | .xorRotr r x y => (values.getD x 0 ^^^ values.getD y 0).rotateRight r.val

def evalOps (ops : List Op) (values : List Word) : List Word :=
  ops.foldl (fun values op => values ++ [op.eval values]) values

abbrev Reg := Vector (Expression Bit) 32

def get (registers : List Reg) (i : ℕ) : Reg := registers.getD i (Vector.replicate 32 0)

/-- The operation as its word circuit, on the registers so far. -/
def Op.circuit (registers : List Reg) : Op → Circuit Bit Reg
  | .add x y => Add32.circuit { x := get registers x, y := get registers y }
  | .addOdd k y => AddOdd.circuit k (get registers y)
  | .addEven k y => AddEven.circuit k (get registers y)
  | .xorRotr r x y => XorRotr.circuit r { x := get registers x, y := get registers y }

def run : List Op → List Reg → Circuit Bit (List Reg)
  | [], registers => pure registers
  | op :: ops, registers => do
    let result ← op.circuit registers
    run ops (registers ++ [result])

/-- The register values under an assignment. -/
def values (env : Environment Bit) (registers : List Reg) : List Word :=
  registers.map fun w => toWord (w.map (Expression.eval env))

theorem toWord_zeros (env : Environment Bit) :
    toWord ((Vector.replicate 32 (0 : Expression Bit)).map (Expression.eval env)) = 0 := by
  apply toWord_ext
  intro i hi
  simp [Expression.eval]

theorem values_getD (env : Environment Bit) (registers : List Reg) (i : ℕ) :
    (values env registers).getD i 0 = toWord ((get registers i).map (Expression.eval env)) := by
  unfold values get
  by_cases hi : i < registers.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show registers.length ≤ i by omega),
      Option.getD_none, List.getElem?_map, Option.map_none, toWord_zeros]

theorem op_soundness (op : Op) (hvalid : op.valid = true) (registers : List Reg) (n : ℕ) (env : Environment Bit)
    (h : ConstraintsHold.Soundness env ((op.circuit registers).operations n)) :
    toWord (((op.circuit registers).output n).map (Expression.eval env)) = op.eval (values env registers) := by
  cases op <;> simp only [Op.circuit, circuit_norm] at h ⊢
  · simp only [Add32.circuit, Add32.Spec] at h
    exact (h trivial).trans (by rw [Op.eval, values_getD, values_getD])
  · simp only [AddOdd.circuit, AddOdd.Spec] at h
    exact (h trivial).trans (by rw [Op.eval, values_getD])
  · simp only [AddEven.circuit, AddEven.Spec] at h
    simp only [Op.valid, Bool.not_eq_eq_eq_not, Bool.not_true] at hvalid
    exact (h trivial hvalid).trans (by rw [Op.eval, values_getD])
  · simp only [XorRotr.circuit, XorRotr.Spec] at h
    exact (h trivial).trans (by rw [Op.eval, values_getD, values_getD])

theorem run_soundness (ops : List Op) (hvalid : ∀ op ∈ ops, op.valid = true) (registers : List Reg) (n : ℕ)
    (env : Environment Bit) (h : ConstraintsHold.Soundness env ((run ops registers).operations n)) :
    values env ((run ops registers).output n) = evalOps ops (values env registers) := by
  induction ops generalizing registers n with
  | nil => simp [run, evalOps, circuit_norm]
  | cons op ops ih =>
    simp only [run, circuit_norm] at h ⊢
    rw [ih (fun o ho => hvalid o (List.mem_cons_of_mem _ ho)) _ _ h.2]
    have hop := op_soundness op (hvalid op List.mem_cons_self) registers n env h.1
    simp only [evalOps, List.foldl_cons, values, List.map_append, List.map_cons, List.map_nil] at hop ⊢
    rw [← hop]

theorem run_completeness (ops : List Op) (registers : List Reg) (n : ℕ) (env : ProverEnvironment Bit) :
    ConstraintsHold.Completeness env ((run ops registers).operations n) := by
  induction ops generalizing registers n with
  | nil => simp [run, circuit_norm]
  | cons op ops ih =>
    simp only [run, circuit_norm]
    refine ⟨?_, ih _ _⟩
    cases op <;> simp [Op.circuit, circuit_norm, Add32.circuit, AddOdd.circuit, AddEven.circuit, XorRotr.circuit]

/-- The operations' witness count, which does not depend on the registers. -/
def Op.length : Op → ℕ
  | .add _ _ | .addOdd _ _ => 63
  | .addEven _ _ => 62
  | .xorRotr _ _ _ => 32

theorem op_localLength (op : Op) (registers : List Reg) (offset : ℕ) :
    (op.circuit registers).localLength offset = op.length := by
  cases op <;> simp [Op.circuit, Op.length, circuit_norm, Add32.circuit, AddOdd.circuit, AddEven.circuit,
    XorRotr.circuit]

theorem run_localLength (ops : List Op) (registers : List Reg) (offset : ℕ) :
    (run ops registers).localLength offset = (ops.map Op.length).sum := by
  induction ops generalizing registers offset with
  | nil => rfl
  | cons op ops ih =>
    simp only [run, circuit_norm] at ih ⊢
    rw [ih, List.sum_cons, ← op_localLength op registers offset]

theorem evalOps_append (ops ops' : List Op) (values : List Word) :
    evalOps (ops ++ ops') values = evalOps ops' (evalOps ops values) := by
  simp [evalOps, List.foldl_append]

theorem run_consistent (ops : List Op) (registers : List Reg) (n : ℕ) :
    ((run ops registers).operations n).SubcircuitsConsistent n := by
  induction ops generalizing registers n with
  | nil => simp [run, circuit_norm]
  | cons op ops ih =>
    cases op <;> simp only [run, Op.circuit, circuit_norm] <;> simp_all [circuit_norm] <;>
      (rw [Nat.add_comm]; exact ih _ _)

theorem run_channelsLawful (ops : List Op) (registers : List Reg) (n : ℕ) :
    ((run ops registers).operations n).ChannelsLawful [] := by
  induction ops generalizing registers n with
  | nil => simp [run, circuit_norm]
  | cons op ops ih =>
    cases op <;> simp only [run, Op.circuit, circuit_norm] <;> simp_all [circuit_norm] <;> rfl

theorem run_requirementsChannelsLawful (ops : List Op) (registers : List Reg) (n : ℕ) :
    ((run ops registers).operations n).RequirementsChannelsLawful [] [] := by
  induction ops generalizing registers n with
  | nil => simp [run, circuit_norm]
  | cons op ops ih =>
    cases op <;> simp only [run, Op.circuit, circuit_norm] <;> simp_all [circuit_norm] <;> rfl

theorem run_exposedChannelsLawful (ops : List Op) (registers : List Reg) (n : ℕ) :
    ((run ops registers).operations n).ExposedChannelsLawful [] := by
  induction ops generalizing registers n with
  | nil => simp [run, circuit_norm]
  | cons op ops ih =>
    cases op <;> simp only [run, Op.circuit, circuit_norm]

theorem run_requirements (ops : List Op) (registers : List Reg) (n : ℕ) (env : Environment Bit) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_m} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      ((run ops registers).operations n) := by
  induction ops generalizing registers n with
  | nil => simp [run, circuit_norm]
  | cons op ops ih =>
    cases op <;> simp only [run, Op.circuit, circuit_norm] <;> simp_all [circuit_norm] <;> exact Or.inl rfl

end LeanVMCircuits.Blake2s
