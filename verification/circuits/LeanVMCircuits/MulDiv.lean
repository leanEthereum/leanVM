module

public import LeanVMCircuits.Multiply.Circuit
public import LeanVMCircuits.MulDivGadgets

set_option maxRecDepth 20000

@[expose] public section

/-!
The multiplication classes as Clean circuits, in the product order of their production circuits.
-/

namespace LeanVMCircuits.Mul

structure Input (F : Type) where
  v1 : Vector F 64
  v2 : Vector F 64
  word : F
  deriving ProvableStruct

/-- The low word of `v1 v2`, its low 32 bits sign-extended for `MULW`. -/
def main (input : Var Input Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let product ← (Multiply.circuit 64) { a := input.v1, b := input.v2 }
  WordMode.circuit { selector := input.word, fill := product[31], word := product }

instance elaborated : ElaboratedCircuit Bit Input (fields 64) main := by elaborate_circuit

def Spec (input : Input Bit) (output : Vector Bit 64) : Prop :=
  Adder.value output = Rv64.mul (input.word = 1) (Adder.value input.v1) (Adder.value input.v2)

def circuit : FormalCircuit Bit Input (fields 64) where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [Multiply.circuit, Multiply.Spec, WordMode.circuit]
    obtain ⟨hp, hout⟩ := h_holds
    rw [hout, ← MulDiv.mul_eq, ← hp]
    by_cases h : input_word = 1
    · simp only [h, if_true, decide_true, MulDiv.sextIf]
      rw [show ∀ P : Vector (Expression Bit) 64, Expression.eval env P[31] = (P.map (Expression.eval env))[31] from
        fun P => by simp, Words.value_high]
    · simp [h, MulDiv.sextIf]
  completeness := by circuit_proof_start [Multiply.circuit, WordMode.circuit]

end LeanVMCircuits.Mul

namespace LeanVMCircuits.Mulh

/-- One signed correction: subtract `other` from `high` when `signed` and `sign` are set. -/
structure CorrectionInput (F : Type) where
  signed : F
  sign : F
  other : Vector F 64
  high : Vector F 64
  deriving ProvableStruct

/-- `negative`, the gated complement of `other`, then `high` plus it plus `negative`, as `Mulh::circuit` orders them. -/
def correctionMain (input : Var CorrectionInput Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let negative ← Product.circuit { x := input.signed, y := input.sign }
  let subtrahend ← WordMux.circuit 64
    { selector := negative, x := input.other.map (· + 1), y := Vector.replicate 64 0 }
  let sum ← Adder.circuit 64 { x := input.high, y := subtrahend, carry := negative }
  return sum.sum

instance correctionElaborated : ElaboratedCircuit Bit CorrectionInput (fields 64) correctionMain := by
  elaborate_circuit

def CorrectionSpec (input : CorrectionInput Bit) (output : Vector Bit 64) : Prop :=
  Adder.value output = (Adder.value input.high +
    (if input.signed = 1 ∧ input.sign = 1 then 2 ^ 64 - 1 - Adder.value input.other + 1 else 0)) % 2 ^ 64

def correction : FormalCircuit Bit CorrectionInput (fields 64) where
  main := correctionMain
  Spec := CorrectionSpec
  soundness := by
    circuit_proof_start [correctionMain, Product.circuit, Product.Spec, WordMux.Spec, WordMux.select, Adder.Spec]
    rcases h_input with ⟨hs, hg, ho, hh⟩
    obtain ⟨hneg, hsub, hadd⟩ := h_holds
    simp only [FormalCircuitBase.output, ← ElaboratedCircuit.output_eq] at hsub hadd ⊢
    simp only [Adder.circuit, WordMux.circuit] at hsub hadd
    unfold CorrectionSpec
    rw [Words.sum_mod hadd, hsub, hneg]
    have hflip : Vector.map (Expression.eval env) (Vector.map (fun x => x + 1) input_var_other) =
        input_other.map (· + 1) := by
      rw [← ho]; apply Vector.ext; intro i hi; simp [circuit_norm]
    have hzero : Vector.map (Expression.eval env) (Vector.replicate 64 (0 : Expression Bit)) =
        Vector.replicate 64 0 := by
      apply Vector.ext; intro i hi; simp [circuit_norm]
    rw [hflip, hzero]
    have hlt := Adder.value_lt input_other
    rcases bit_zero_or_one input_signed with h1 | h1 <;> rcases bit_zero_or_one input_sign with h2 | h2 <;>
      simp [h1, h2, Words.value_flip, Words.value_replicate]
    omega
  completeness := by circuit_proof_start [correctionMain, Product.circuit, Adder.Spec]

structure Input (F : Type) where
  v1 : Vector F 64
  v2 : Vector F 64
  signed1 : F
  signed2 : F
  deriving ProvableStruct

/-- The unsigned product's high word, less `v2` if `v1` is signed and negative, less `v1` if `v2` is. -/
def main (input : Var Input Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let product ← (Multiply.circuit 128) { a := input.v1, b := input.v2 }
  let high ← correction
    { signed := input.signed1, sign := input.v1[63], other := input.v2, high := Words.highBits 64 (b := 64) product }
  correction { signed := input.signed2, sign := input.v2[63], other := input.v1, high }

instance elaborated : ElaboratedCircuit Bit Input (fields 64) main := by elaborate_circuit

def Spec (input : Input Bit) (output : Vector Bit 64) : Prop :=
  Adder.value output = Rv64.mulh (input.signed1 = 1) (input.signed2 = 1) (Adder.value input.v1) (Adder.value input.v2)

def circuit : FormalCircuit Bit Input (fields 64) where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [Multiply.circuit, Multiply.Spec, correction, CorrectionSpec]
    obtain ⟨hp, h1, h2⟩ := h_holds
    obtain ⟨hv1, hv2, hs1, hs2⟩ := h_input
    rw [Words.eval_sum, h2, h1, Words.highBits_map, Words.value_highBits, hp]
    have ha := Adder.value_lt input_v1
    have hb := Adder.value_lt input_v2
    rw [← MulDiv.mulh_eq _ _ _ _ ha hb]
    have e1 : Expression.eval env input_var_v1[63] = input_v1[63] := by rw [← hv1]; simp
    have e2 : Expression.eval env input_var_v2[63] = input_v2[63] := by rw [← hv2]; simp
    have t1 := Words.value_top (n := 63) input_v1
    have t2 := Words.value_top (n := 63) input_v2
    have hprod : Adder.value input_v1 * Adder.value input_v2 < 2 ^ 128 := by
      calc _ < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
        _ = 2 ^ 128 := by norm_num
    rw [e1, e2, Nat.mod_eq_of_lt hprod]
    simp only [MulDiv.mulhOut, MulDiv.negative, Bool.and_eq_true, decide_eq_true_eq, t1, t2]
  completeness := by circuit_proof_start [Multiply.circuit, correction]

end LeanVMCircuits.Mulh

namespace LeanVMCircuits.Div

theorem formal_output {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : FormalCircuit Bit Input Output) (x : Var Input Bit) (o : ℕ) : c.elaborated.output x o = c.output x o := rfl

theorem formal_localLength {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : FormalCircuit Bit Input Output) (x : Var Input Bit) : c.elaborated.localLength x = c.localLength x := rfl


/-- A division operand: a word division's low 32 bits, sign-extended if the division is signed. -/
structure ExtendInput (F : Type) where
  signed : F
  word : F
  x : Vector F 64
  deriving ProvableStruct

def extendMain (input : Var ExtendInput Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let sign ← Product.circuit { x := input.signed, y := input.x[31] }
  WordMode.circuit { selector := input.word, fill := sign, word := input.x }

instance extendElaborated : ElaboratedCircuit Bit ExtendInput (fields 64) extendMain := by elaborate_circuit

def extend : FormalCircuit Bit ExtendInput (fields 64) where
  main := extendMain
  Spec input output := Adder.value output = MulDiv.extend (input.signed = 1) (input.word = 1) (Adder.value input.x)
  soundness := by
    circuit_proof_start [extendMain, Product.circuit, Product.Spec, WordMode.circuit]
    obtain ⟨hs, hw, hx⟩ := h_input
    obtain ⟨hsign, hout⟩ := h_holds
    rw [hout, hsign, ← hx]
    rw [show Expression.eval env input_var_x[31] = (input_var_x.map (Expression.eval env))[31] by simp]
    by_cases h1 : input_word = 1
    · rcases bit_zero_or_one input_signed with h2 | h2
      · simp [h1, h2, MulDiv.extend, Words.value_high_fill]
      · simp only [h1, h2, one_mul, if_true]
        rw [Words.value_high]
        simp [MulDiv.extend]
    · simp [h1, MulDiv.extend]
  completeness := by circuit_proof_start [extendMain, Product.circuit, WordMode.circuit]

@[circuit_norm] theorem extend_assumptions : extend.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem extend_requirements : extend.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem extend_guarantees : extend.elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem extend_length (input : Var ExtendInput Bit) : extend.localLength input = 33 := rfl
@[circuit_norm] theorem extend_spec : extend.Spec = fun input output =>
    Adder.value output = MulDiv.extend (input.signed = 1) (input.word = 1) (Adder.value input.x) := rfl
theorem extend_output_eq (input : Var ExtendInput Bit) (offset : ℕ) :
    extend.elaborated.output input offset = extend.output input offset := rfl
theorem extend_localLength_eq (input : Var ExtendInput Bit) : extend.elaborated.localLength input = 33 := rfl

attribute [irreducible] extend

/-- `x`, or `-x` modulo `2^64`: `(x + negative) + negative`, as `WordGadgets::negate_if`. -/
structure NegateInput (F : Type) where
  negative : F
  x : Vector F 64
  deriving ProvableStruct

def negateMain (input : Var NegateInput Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let sum ← Adder.circuit 64
    { x := input.x.map (· + input.negative), y := Vector.replicate 64 0, carry := input.negative }
  return sum.sum

instance negateElaborated : ElaboratedCircuit Bit NegateInput (fields 64) negateMain := by elaborate_circuit

def negate : FormalCircuit Bit NegateInput (fields 64) where
  main := negateMain
  Spec input output := Adder.value output = MulDiv.negIf (input.negative = 1) (Adder.value input.x)
  soundness := by
    circuit_proof_start [negateMain, Adder.Spec]
    obtain ⟨hn, hx⟩ := h_input
    simp only [Adder.circuit] at h_holds
    simp only [FormalCircuitBase.output, ← ElaboratedCircuit.output_eq] at h_holds ⊢
    rw [Words.eval_sum] at h_holds ⊢
    rw [Words.sum_mod h_holds]
    have hflip : Vector.map (Expression.eval env) (Vector.map (fun x => x + input_var_negative) input_var_x) =
        input_x.map (· + input_negative) := by
      rw [← hx, ← hn]; apply Vector.ext; intro i hi; simp [circuit_norm]
    have hzero : Vector.map (Expression.eval env) (Vector.replicate 64 (0 : Expression Bit)) =
        Vector.replicate 64 0 := by
      apply Vector.ext; intro i hi; simp [circuit_norm]
    rw [hflip, hzero, Words.value_flip_if, Words.value_replicate]
    have hlt := Adder.value_lt input_x
    rcases bit_zero_or_one input_negative with h | h <;> simp [h, MulDiv.negIf]
    all_goals first | exact Nat.mod_eq_of_lt hlt | (congr 1; omega)
  completeness := by circuit_proof_start [negateMain, Adder.Spec]

@[circuit_norm] theorem negate_assumptions : negate.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem negate_requirements : negate.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem negate_guarantees : negate.elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem negate_length (input : Var NegateInput Bit) : negate.localLength input = 64 := rfl
@[circuit_norm] theorem negate_spec : negate.Spec = fun input output =>
    Adder.value output = MulDiv.negIf (input.negative = 1) (Adder.value input.x) := rfl
theorem negate_output_eq (input : Var NegateInput Bit) (offset : ℕ) :
    negate.elaborated.output input offset = negate.output input offset := rfl
theorem negate_localLength_eq (input : Var NegateInput Bit) : negate.elaborated.localLength input = 64 := rfl

attribute [irreducible] negate

theorem negative_bit (env : Environment Bit) (s : Bit) (v : Vector (Expression Bit) 64) (x : ℕ)
    (hv : Adder.value (v.map (Expression.eval env)) = x) :
    s * Expression.eval env v[63] = if MulDiv.negative (s = 1) x then 1 else 0 := by
  have ht := Words.value_top (n := 63) (v.map (Expression.eval env))
  rw [hv, Vector.getElem_map] at ht
  rcases bit_zero_or_one s with h | h <;> simp [h, MulDiv.negative]
  rcases bit_zero_or_one (Expression.eval env v[63]) with h' | h' <;> simp_all

theorem magnitude_of (s : Bool) (nn : Bit) (x : ℕ) (hn : nn = if MulDiv.negative s x then 1 else 0) :
    MulDiv.negIf (decide (nn = 1)) x = MulDiv.magnitude s x := by
  subst hn; unfold MulDiv.magnitude; cases MulDiv.negative s x <;> simp

/-- The operands and their magnitudes. -/
structure Operands (F : Type) where
  signed : F
  word : F
  v1 : Vector F 64
  v2 : Vector F 64
  deriving ProvableStruct

structure Magnitudes (F : Type) where
  n : Vector F 64
  d : Vector F 64
  nNegative : F
  dNegative : F
  nAbs : Vector F 64
  dAbs : Vector F 64
  deriving ProvableStruct

def magnitudesMain (input : Var Operands Bit) : Circuit Bit (Var Magnitudes Bit) := do
  let n ← extend { signed := input.signed, word := input.word, x := input.v1 }
  let d ← extend { signed := input.signed, word := input.word, x := input.v2 }
  let nNegative ← Product.circuit { x := input.signed, y := n[63] }
  let dNegative ← Product.circuit { x := input.signed, y := d[63] }
  let nAbs ← negate { negative := nNegative, x := n }
  let dAbs ← negate { negative := dNegative, x := d }
  return { n, d, nNegative, dNegative, nAbs, dAbs }

instance magnitudesElaborated : ElaboratedCircuit Bit Operands Magnitudes magnitudesMain := by elaborate_circuit

def MagnitudesSpec (input : Operands Bit) (output : Magnitudes Bit) : Prop :=
  let isSigned := decide (input.signed = 1)
  let word := decide (input.word = 1)
  let n := MulDiv.extend isSigned word (Adder.value input.v1)
  let d := MulDiv.extend isSigned word (Adder.value input.v2)
  Adder.value output.n = n ∧ Adder.value output.d = d ∧
    output.nNegative = (if MulDiv.negative isSigned n then 1 else 0) ∧
    output.dNegative = (if MulDiv.negative isSigned d then 1 else 0) ∧
    Adder.value output.nAbs = MulDiv.magnitude isSigned n ∧ Adder.value output.dAbs = MulDiv.magnitude isSigned d

def magnitudes : FormalCircuit Bit Operands Magnitudes where
  main := magnitudesMain
  Spec := MagnitudesSpec
  soundness := by
    circuit_proof_start [magnitudesMain, Product.circuit, Product.Spec]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h_holds
    simp only [extend_output_eq, negate_output_eq, extend_localLength_eq, negate_localLength_eq]
    have n3 := h3.trans (negative_bit _ _ _ _ h1)
    have n4 := h4.trans (negative_bit _ _ _ _ h2)
    exact ⟨h1, h2, n3, n4, by rw [h5, h1, magnitude_of _ _ _ n3], by rw [h6, h2, magnitude_of _ _ _ n4]⟩
  completeness := by circuit_proof_start [magnitudesMain, Product.circuit]

@[circuit_norm] theorem magnitudes_assumptions : magnitudes.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem magnitudes_requirements : magnitudes.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem magnitudes_guarantees : magnitudes.elaborated.channelsWithGuarantees = [] := by
  with_unfolding_all rfl
@[circuit_norm] theorem magnitudes_length (input : Var Operands Bit) : magnitudes.localLength input = 196 := by
  with_unfolding_all rfl
@[circuit_norm] theorem magnitudes_spec : magnitudes.Spec = MagnitudesSpec := rfl

attribute [irreducible] magnitudes

/-- The checks of the hints: `q |d|` has a high word, `low + r` carries, the sum is not `|n|`, `r ≥ |d|`. -/
structure Hints (F : Type) where
  q : Vector F 64
  r : Vector F 64
  nAbs : Vector F 64
  dAbs : Vector F 64
  deriving ProvableStruct

structure Checks (F : Type) where
  overflows : F
  carries : F
  differs : F
  tooLarge : F
  deriving ProvableStruct

def checkMain (input : Var Hints Bit) : Circuit Bit (Var Checks Bit) := do
  let product ← (Multiply.circuit 128) { a := input.q, b := input.dAbs }
  let overflows ← BooleanAny.circuit 63 { word := Words.highBits 64 (b := 64) product }
  let sum ← Adder.circuit 64 { x := Words.lowBits 64 (b := 64) product, y := input.r, carry := 0 }
  let differs ← Differs.circuit { x := sum.sum, y := input.nAbs }
  let tooLarge ← Adder.circuit 64 { x := input.r, y := input.dAbs.map (· + 1), carry := 1 }
  return { overflows, carries := sum.carry, differs, tooLarge := tooLarge.carry }

set_option maxHeartbeats 2000000 in
instance checkElaborated : ElaboratedCircuit Bit Hints Checks checkMain where
  localLength _ := Multiply.total 128 + 63 + 64 + 63 + 64
  output input offset :=
    let product := (Multiply.circuit 128).output { a := input.q, b := input.dAbs } offset
    let o1 := offset + Multiply.total 128
    let sum := (Adder.circuit 64).output
      { x := Words.lowBits 64 (b := 64) product, y := input.r, carry := 0 } (o1 + 63)
    { overflows := (BooleanAny.circuit 63).output { word := Words.highBits 64 (b := 64) product } o1,
      carries := sum.carry,
      differs := Differs.circuit.output { x := sum.sum, y := input.nAbs } (o1 + 63 + 64),
      tooLarge := ((Adder.circuit 64).output { x := input.r, y := input.dAbs.map (· + 1), carry := 1 }
        (o1 + 63 + 64 + 63)).carry }
  localLength_eq _ _ := by simp only [checkMain, circuit_norm]
  output_eq _ _ := by simp only [checkMain, circuit_norm]
  subcircuitsConsistent _ _ := by simp only [checkMain, circuit_norm]; omega
  channelsLawful := by simp [checkMain, circuit_norm, FormalCircuitBase.channelsWithGuarantees]

theorem eval_magnitudes (env : Environment Bit) (x : Var Magnitudes Bit) :
    eval env x = ⟨x.n.map (Expression.eval env), x.d.map (Expression.eval env), x.nNegative.eval env,
      x.dNegative.eval env, x.nAbs.map (Expression.eval env), x.dAbs.map (Expression.eval env)⟩ := by
  rcases x; simp [circuit_norm]

theorem peval_magnitudes (env : Environment Bit) (x : Var Magnitudes Bit) :
    ProvableStruct.eval env x = ⟨x.n.map (Expression.eval env), x.d.map (Expression.eval env), x.nNegative.eval env,
      x.dNegative.eval env, x.nAbs.map (Expression.eval env), x.dAbs.map (Expression.eval env)⟩ := by
  rcases x; simp [circuit_norm]

theorem eval_checks (env : Environment Bit) (x : Var Checks Bit) :
    eval env x = ⟨x.overflows.eval env, x.carries.eval env, x.differs.eval env, x.tooLarge.eval env⟩ := by
  rcases x; simp [circuit_norm]

theorem peval_checks (env : Environment Bit) (x : Var Checks Bit) :
    ProvableStruct.eval env x = ⟨x.overflows.eval env, x.carries.eval env, x.differs.eval env, x.tooLarge.eval env⟩ := by
  rcases x; simp [circuit_norm]

def ChecksSpec (input : Hints Bit) (output : Checks Bit) : Prop :=
  let A := Adder.value input.q * Adder.value input.dAbs
  let R := Adder.value input.r
  output.overflows = (if 2 ^ 64 ≤ A then 1 else 0) ∧
    output.carries = (if 2 ^ 64 ≤ A % 2 ^ 64 + R then 1 else 0) ∧
    output.differs = (if (A % 2 ^ 64 + R) % 2 ^ 64 = Adder.value input.nAbs then 0 else 1) ∧
    output.tooLarge = (if Adder.value input.dAbs ≤ R then 1 else 0)

set_option maxHeartbeats 4000000 in
def check : FormalCircuit Bit Hints Checks where
  main := checkMain
  Spec := ChecksSpec
  soundness := by
    intro offset env input_var input h_input _ h_holds
    simp only [checkMain, circuit_norm, Multiply.Spec, Adder.Spec, BooleanAny.Spec, Words.any_value] at h_holds
    refine ⟨?_, by simp only [checkMain, circuit_norm]⟩
    obtain ⟨hp, ho, hs, hdf, ht⟩ := h_holds
    have hin : input.q = input_var.q.map (Expression.eval env) ∧ input.r = input_var.r.map (Expression.eval env) ∧
        input.nAbs = input_var.nAbs.map (Expression.eval env) ∧
        input.dAbs = input_var.dAbs.map (Expression.eval env) := by
      subst h_input; rcases input_var; simp [circuit_norm]
    obtain ⟨hq, hr, hn, hd⟩ := hin
    rw [← hq, ← hd] at hp
    rw [← hr] at hs ht
    rw [eval_checks]
    simp only [ChecksSpec]
    dsimp only [ElaboratedCircuit.output]
    have hD := Adder.value_lt input.dAbs
    have hR := Adder.value_lt input.r
    have hA : Adder.value input.q * Adder.value input.dAbs < 2 ^ 128 := by
      calc _ < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' (Adder.value_lt _) hD
        _ = 2 ^ 128 := by norm_num
    rw [Nat.mod_eq_of_lt hA] at hp
    rw [Words.highBits_map, Words.value_highBits, hp] at ho
    rw [Words.eval_sum, Words.eval_carry, Words.lowBits_map, Words.value_lowBits, hp] at hs
    rw [Words.eval_sum, Words.eval_carry] at ht
    have hflip : Vector.map (Expression.eval env) (Vector.map (fun x => x + 1) input_var.dAbs) =
        input.dAbs.map (· + 1) := by
      rw [hd]; apply Vector.ext; intro i hi; simp [circuit_norm]
    rw [hflip, Words.value_flip] at ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ho]
      by_cases h : 2 ^ 64 ≤ Adder.value input.q * Adder.value input.dAbs
      · rw [if_neg (by omega), if_pos h]
      · rw [if_pos (by omega), if_neg h]
    · rw [Words.carry_eq hs]; simp
    · rw [hdf, Words.sum_mod hs, ← hn]; simp
    · rw [Words.carry_eq ht]
      simp only [ZMod.val_one]
      by_cases h : Adder.value input.dAbs ≤ Adder.value input.r
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
  completeness := by circuit_proof_start [checkMain, Adder.Spec]

@[circuit_norm] theorem check_assumptions : check.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem check_requirements : check.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem check_guarantees : check.elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem check_length (input : Var Hints Bit) :
    check.localLength input = Multiply.total 128 + 63 + 64 + 63 + 64 := rfl
@[circuit_norm] theorem check_spec : check.Spec = ChecksSpec := rfl

/-- Whether the divisor is nonzero, and the verdict on the hints: any failed check, unless the divisor is zero. -/
structure VerdictInput (F : Type) where
  d : Vector F 64
  checks : Checks F
  deriving ProvableStruct

structure Verdict (F : Type) where
  nonzero : F
  bad : F
  deriving ProvableStruct

theorem eval_verdict (env : Environment Bit) (x : Var Verdict Bit) :
    eval env x = ⟨x.nonzero.eval env, x.bad.eval env⟩ := by
  rcases x; simp [circuit_norm]

theorem peval_verdict (env : Environment Bit) (x : Var Verdict Bit) :
    ProvableStruct.eval env x = ⟨x.nonzero.eval env, x.bad.eval env⟩ := by
  rcases x; simp [circuit_norm]

def verdictMain (input : Var VerdictInput Bit) : Circuit Bit (Var Verdict Bit) := do
  let nonzero ← BooleanAny.circuit 63 { word := input.d }
  let wrong ← BooleanOr.circuit { x := input.checks.overflows, y := input.checks.carries }
  let wrong ← BooleanOr.circuit { x := wrong, y := input.checks.differs }
  let wrong ← BooleanOr.circuit { x := wrong, y := input.checks.tooLarge }
  let bad ← Product.circuit { x := nonzero, y := wrong }
  return { nonzero, bad }

instance verdictElaborated : ElaboratedCircuit Bit VerdictInput Verdict verdictMain := by elaborate_circuit

def VerdictSpec (input : VerdictInput Bit) (output : Verdict Bit) : Prop :=
  output.nonzero = (if Adder.value input.d = 0 then 0 else 1) ∧
    output.bad = (if Adder.value input.d ≠ 0 ∧ (input.checks.overflows = 1 ∨ input.checks.carries = 1 ∨
      input.checks.differs = 1 ∨ input.checks.tooLarge = 1) then 1 else 0)

def verdict : FormalCircuit Bit VerdictInput Verdict where
  main := verdictMain
  Spec := VerdictSpec
  soundness := by
    circuit_proof_start [verdictMain, BooleanAny.Spec, Words.any_value, BooleanOr.circuit, BooleanOr.select, Product.circuit,
      Product.Spec]
    obtain ⟨hnz, h1, h2, h3, hb⟩ := h_holds
    simp only [BooleanAny.circuit] at hnz hb
    simp only [FormalCircuitBase.output, ← ElaboratedCircuit.output_eq] at hnz hb ⊢
    simp only [VerdictSpec]
    refine ⟨hnz, ?_⟩
    rw [hb, hnz, h3, h2, h1]
    by_cases hd : Adder.value input_d = 0
    · simp [hd]
    · rcases bit_zero_or_one input_checks_overflows with a | a <;>
        rcases bit_zero_or_one input_checks_carries with b | b <;>
        rcases bit_zero_or_one input_checks_differs with c | c <;>
        rcases bit_zero_or_one input_checks_tooLarge with e | e <;> simp [hd, a, b, c, e]
  completeness := by circuit_proof_start [verdictMain, BooleanOr.circuit, Product.circuit]

@[circuit_norm] theorem verdict_assumptions : verdict.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem verdict_requirements : verdict.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem verdict_guarantees : verdict.elaborated.channelsWithGuarantees = [] := by
  with_unfolding_all rfl
@[circuit_norm] theorem verdict_length (input : Var VerdictInput Bit) : verdict.localLength input = 67 := by
  with_unfolding_all rfl
@[circuit_norm] theorem verdict_spec : verdict.Spec = VerdictSpec := rfl

/-- The output: the signed quotient or remainder, or the zero divisor's result, sign-extended for a word. -/
structure ResultInput (F : Type) where
  rem : F
  word : F
  nNegative : F
  dNegative : F
  nonzero : F
  q : Vector F 64
  r : Vector F 64
  n : Vector F 64
  deriving ProvableStruct

def resultMain (input : Var ResultInput Bit) : Circuit Bit (Var (fields 64) Bit) := do
  let qSigned ← negate { negative := input.nNegative + input.dNegative, x := input.q }
  let rSigned ← negate { negative := input.nNegative, x := input.r }
  let out ← DivSelect.circuit 64
    { rem := input.rem, nonzero := input.nonzero, r := rSigned, q := qSigned, dividend := input.n }
  WordMode.circuit { selector := input.word, fill := out[31], word := out }

instance resultElaborated : ElaboratedCircuit Bit ResultInput (fields 64) resultMain := by elaborate_circuit

def ResultSpec (input : ResultInput Bit) (output : Vector Bit 64) : Prop :=
  Adder.value output = MulDiv.sextIf (input.word = 1)
    (if input.nonzero = 1 then
      (if input.rem = 1 then MulDiv.negIf (input.nNegative = 1) (Adder.value input.r)
        else MulDiv.negIf (input.nNegative + input.dNegative = 1) (Adder.value input.q))
    else (if input.rem = 1 then Adder.value input.n else 2 ^ 64 - 1))

def result : FormalCircuit Bit ResultInput (fields 64) where
  main := resultMain
  Spec := ResultSpec
  soundness := by
    circuit_proof_start [resultMain, DivSelect.Spec, DivSelect.select, WordMode.circuit]
    obtain ⟨hq, hr, hsel, hout⟩ := h_holds
    simp only [formal_output, formal_localLength, negate_length] at hsel hout ⊢
    simp only [ResultSpec]
    refine (congrArg Adder.value hout).trans ?_
    rw [show ∀ P : Vector (Expression Bit) 64, Expression.eval env P[31] = (P.map (Expression.eval env))[31] from
      fun P => by simp]
    rw [hsel, Words.value_sextIf]
    congr 1
    split_ifs <;> simp [hq, hr, Words.value_replicate]
  completeness := by circuit_proof_start [resultMain, WordMode.circuit]

@[circuit_norm] theorem result_assumptions : result.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem result_requirements : result.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem result_guarantees : result.elaborated.channelsWithGuarantees = [] := by
  with_unfolding_all rfl
@[circuit_norm] theorem result_length (input : Var ResultInput Bit) : result.localLength input = 352 := by
  with_unfolding_all rfl
@[circuit_norm] theorem result_spec : result.Spec = ResultSpec := rfl


/-- The division's arithmetic: the subcircuits' specifications compose to `Spec`. -/
theorem compose (s w : Bool) (rem : Bit) (a b Q R n d nA dA out : ℕ) (nn dn ov c df tl nz bad : Bit)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hR : R < 2 ^ 64) (hnA' : nA < 2 ^ 64)
    (hn : n = MulDiv.extend s w a) (hd : d = MulDiv.extend s w b)
    (hnn : nn = if MulDiv.negative s n then 1 else 0) (hdn : dn = if MulDiv.negative s d then 1 else 0)
    (hnA : nA = MulDiv.magnitude s n) (hdA : dA = MulDiv.magnitude s d)
    (hov : ov = if 2 ^ 64 ≤ Q * dA then 1 else 0) (hc : c = if 2 ^ 64 ≤ Q * dA % 2 ^ 64 + R then 1 else 0)
    (hdf : df = if (Q * dA % 2 ^ 64 + R) % 2 ^ 64 = nA then 0 else 1) (htl : tl = if dA ≤ R then 1 else 0)
    (hnz : nz = if d = 0 then 0 else 1)
    (hbad : bad = if d ≠ 0 ∧ (ov = 1 ∨ c = 1 ∨ df = 1 ∨ tl = 1) then 1 else 0)
    (hout : out = MulDiv.sextIf w (if nz = 1 then
      (if rem = 1 then MulDiv.negIf (nn = 1) R else MulDiv.negIf (nn + dn = 1) Q)
      else (if rem = 1 then n else 2 ^ 64 - 1))) :
    (bad = if d ≠ 0 ∧ ¬(Q * dA + R = nA ∧ R < dA) then 1 else 0) ∧
      (bad = 0 → out = Rv64.div s (decide (rem = 1)) w a b) := by
  have hok : (ov = 1 ∨ c = 1 ∨ df = 1 ∨ tl = 1) ↔ ¬(Q * dA + R = nA ∧ R < dA) := by
    subst hov hc hdf htl
    constructor
    · rintro (h | h | h | h) ⟨h1, h2⟩ <;> split_ifs at h <;> first | omega | exact absurd h (by decide)
    · intro h
      by_contra hn'
      simp only [not_or] at hn'
      obtain ⟨h1, h2, h3, h4⟩ := hn'
      split_ifs at h1 h2 h3 h4 <;> first | omega | simp_all
  have hbad' : bad = if d ≠ 0 ∧ ¬(Q * dA + R = nA ∧ R < dA) then 1 else 0 := by
    rw [hbad]; simp only [hok]
  refine ⟨hbad', fun h0 => ?_⟩
  rw [← MulDiv.div_eq s _ w a b ha hb, hout]
  unfold MulDiv.divOut
  simp only [← hn, ← hd, ← hnA, ← hdA]
  by_cases hd0 : d = 0
  · rcases bit_zero_or_one rem with hrem | hrem <;> simp [hnz, hd0, hrem]
  · have hgood : Q * dA + R = nA ∧ R < dA := by
      by_contra h; rw [hbad', if_pos ⟨hd0, h⟩] at h0; exact one_ne_zero h0
    have hq : Q = nA / dA := by
      rw [← hgood.1, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hgood.2]; simp
    have hr : R = nA % dA := by
      rw [← hgood.1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hgood.2]
    rw [hnz, if_neg hd0, if_pos rfl, if_neg hd0, hq, hr, hnn, hdn]
    rcases bit_zero_or_one rem with hrem | hrem <;>
      cases MulDiv.negative s n <;> cases MulDiv.negative s d <;> simp [hrem]

structure Input (F : Type) where
  v1 : Vector F 64
  v2 : Vector F 64
  signed : F
  rem : F
  word : F
  q : Vector F 64
  r : Vector F 64
  deriving ProvableStruct

structure Output (F : Type) where
  out : Vector F 64
  bad : F
  deriving ProvableStruct

/-- `Div::circuit`: the operands' magnitudes, the checks of the hints `q` and `r` against them, the verdict, then
the result. -/
def main (input : Var Input Bit) : Circuit Bit (Var Output Bit) := do
  let m ← magnitudes { signed := input.signed, word := input.word, v1 := input.v1, v2 := input.v2 }
  let checks ← check { q := input.q, r := input.r, nAbs := m.nAbs, dAbs := m.dAbs }
  let v ← verdict { d := m.d, checks }
  let out ← result ⟨input.rem, input.word, m.nNegative, m.dNegative, v.nonzero, input.q, input.r, m.n⟩
  return { out, bad := v.bad }

/-- Written out so that callers see the subcircuits' outputs, not their gates. -/
instance elaborated : ElaboratedCircuit Bit Input Output main where
  localLength _ := 196 + (Multiply.total 128 + 63 + 64 + 63 + 64) + 67 + 352
  output input offset :=
    let m := magnitudes.output ⟨input.signed, input.word, input.v1, input.v2⟩ offset
    let o1 := offset + 196
    let checks := check.output ⟨input.q, input.r, m.nAbs, m.dAbs⟩ o1
    let o2 := o1 + (Multiply.total 128 + 63 + 64 + 63 + 64)
    let v := verdict.output ⟨m.d, checks⟩ o2
    { out := result.output ⟨input.rem, input.word, m.nNegative, m.dNegative, v.nonzero, input.q, input.r, m.n⟩
        (o2 + 67),
      bad := v.bad }
  localLength_eq _ _ := by simp only [main, circuit_norm]; omega
  output_eq _ _ := by simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp only [main, circuit_norm]; omega
  channelsLawful := by simp [main, circuit_norm, FormalCircuitBase.channelsWithGuarantees]

/-- `bad` is set exactly when the divisor is nonzero and the hints are not `|n|`'s quotient and remainder by
`|d|`; while it is clear, the output is RISC-V's. -/
def Spec (input : Input Bit) (output : Output Bit) : Prop :=
  let isSigned := decide (input.signed = 1)
  let word := decide (input.word = 1)
  let n := MulDiv.extend isSigned word (Adder.value input.v1)
  let d := MulDiv.extend isSigned word (Adder.value input.v2)
  let N := MulDiv.magnitude isSigned n
  let D := MulDiv.magnitude isSigned d
  (output.bad = if d ≠ 0 ∧ ¬(Adder.value input.q * D + Adder.value input.r = N ∧ Adder.value input.r < D) then 1
    else 0) ∧
  (output.bad = 0 → Adder.value output.out =
    Rv64.div isSigned (decide (input.rem = 1)) word (Adder.value input.v1) (Adder.value input.v2))

set_option maxHeartbeats 2000000 in
def circuit : FormalCircuit Bit Input Output where
  main
  elaborated
  Spec
  soundness := by
    circuit_proof_start [MagnitudesSpec, ChecksSpec, VerdictSpec, ResultSpec]
    simp only [peval_magnitudes, peval_checks, peval_verdict] at h_holds
    obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨c1, c2, c3, c4⟩, ⟨v1, v2⟩, hres⟩ := h_holds
    rw [← h6, ← h5, ← h2]
    rw [← h1] at h3 h5
    rw [← h2] at h4 h6
    have key := compose _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Adder.value_lt input_v1) (Adder.value_lt input_v2)
      (Adder.value_lt input_r) (Adder.value_lt _) h1 h2 h3 h4 h5 h6 c1 c2 c3 c4 v1 v2 hres
    exact key
  completeness := by circuit_proof_start

theorem magnitude_pos (s : Bool) (d : ℕ) (hd : d < 2 ^ 64) (h0 : d ≠ 0) : 0 < MulDiv.magnitude s d := by
  unfold MulDiv.magnitude MulDiv.negIf
  split
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · omega

/-- Honest hints pass: with a nonzero divisor, the magnitudes' quotient and remainder leave `bad` clear. -/
theorem honest_hints (input : Input Bit) (output : Output Bit) (h : Spec input output)
    (hd : MulDiv.extend (input.signed = 1) (input.word = 1) (Adder.value input.v2) ≠ 0)
    (hq : Adder.value input.q = MulDiv.magnitude (input.signed = 1)
      (MulDiv.extend (input.signed = 1) (input.word = 1) (Adder.value input.v1)) /
        MulDiv.magnitude (input.signed = 1) (MulDiv.extend (input.signed = 1) (input.word = 1) (Adder.value input.v2)))
    (hr : Adder.value input.r = MulDiv.magnitude (input.signed = 1)
      (MulDiv.extend (input.signed = 1) (input.word = 1) (Adder.value input.v1)) %
        MulDiv.magnitude (input.signed = 1) (MulDiv.extend (input.signed = 1) (input.word = 1) (Adder.value input.v2))) :
    output.bad = 0 := by
  rw [h.1, if_neg]
  rintro ⟨-, hn⟩
  apply hn
  have hD := magnitude_pos (input.signed = 1) _ (MulDiv.extend_lt _ _ _ (Adder.value_lt input.v2)) hd
  rw [hq, hr]
  exact ⟨Nat.div_add_mod' _ _, Nat.mod_lt _ hD⟩

end LeanVMCircuits.Div
