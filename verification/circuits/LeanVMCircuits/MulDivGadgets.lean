module

public import LeanVMCircuits.BooleanOps
public import LeanVMCircuits.BooleanAny
public import LeanVMCircuits.WordMode
public import LeanVMCircuits.WordValues
public import LeanVMCircuits.Rv64MulDiv

set_option maxRecDepth 20000

@[expose] public section

/-!
Word gadgets of the multiplication and division circuits, in the product order of `WordGadgets`.
-/


namespace LeanVMCircuits.DivSelect

/-- A division's output bits: the signed remainder or quotient, or, for a zero divisor, the dividend or all ones. -/
structure Input (n : ℕ) (F : Type) where
  rem : F
  nonzero : F
  r : Vector F n
  q : Vector F n
  dividend : Vector F n
  deriving ProvableStruct

def select (n : ℕ) (input : Input n Bit) : Vector Bit n :=
  if input.nonzero = 1 then (if input.rem = 1 then input.r else input.q)
  else (if input.rem = 1 then input.dividend else Vector.replicate n 1)

def Spec (n : ℕ) (input : Input n Bit) (output : Vector Bit n) : Prop := output = select n input

structure Certified (n : ℕ) where
  circuit : FormalCircuit Bit (Input n) (fields n)
  assumptions_eq : circuit.Assumptions = fun _ => True
  spec_eq : circuit.Spec = Spec n
  requirements_eq : circuit.channelsWithRequirements = []
  guarantees_eq : circuit.elaborated.channelsWithGuarantees = []
  length_eq : ∀ input, circuit.elaborated.localLength input = 3 * n

@[circuit_norm] theorem certified_length (n : ℕ) (previous : Certified n) (input : Var (Input n) Bit) :
    previous.circuit.elaborated.localLength input = 3 * n := previous.length_eq input

@[circuit_norm] theorem certified_guarantees (n : ℕ) (previous : Certified n) :
    previous.circuit.elaborated.channelsWithGuarantees = [] := previous.guarantees_eq

def zero : Certified 0 where
  circuit := {
    main := fun _ => pure #v[]
    Spec := Spec 0
    soundness := by
      circuit_proof_start
      simp only [select]
      split_ifs <;> exact (Array.eq_empty_of_size_eq_zero (by simp)).symm
    completeness := by circuit_proof_start
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := rfl
  length_eq := by intro input; rfl

def pop (n : ℕ) (input : Var (Input (n + 1)) Bit) : Var (Input n) Bit :=
  { rem := input.rem, nonzero := input.nonzero, r := input.r.pop, q := input.q.pop, dividend := input.dividend.pop }

/-- Bit `n`: the result, the zero divisor's result, then the choice between them, as `Div::circuit` orders them. -/
def step (n : ℕ) (previous : Certified n) : Certified (n + 1) where
  circuit := {
    main := fun input => do
      let lower ← previous.circuit (pop n input)
      let result ← Mux.circuit { selector := input.rem, x := input.r[n], y := input.q[n] }
      let byZero ← Mux.circuit { selector := input.rem, x := input.dividend[n], y := 1 }
      let upper ← Mux.circuit { selector := input.nonzero, x := result, y := byZero }
      return lower.push upper
    Spec := Spec (n + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [Mux.circuit, Mux.Spec, pop]
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.output, ← ElaboratedCircuit.output_eq,
        FormalCircuitBase.localLength, certified_length, Vector.map_push, circuit_norm] at h_holds ⊢
      rcases h_input with ⟨hrem, hnz, hr, hq, hd⟩
      have hrbit := congrArg (fun v : Vector Bit (n + 1) => v[n]) hr
      have hqbit := congrArg (fun v : Vector Bit (n + 1) => v[n]) hq
      have hdbit := congrArg (fun v : Vector Bit (n + 1) => v[n]) hd
      simp only [Vector.getElem_map] at hrbit hqbit hdbit
      simp only [Vector.map_pop, hr, hq, hd, hrbit, hqbit, hdbit] at h_holds ⊢
      rcases h_holds with ⟨hlower, hresult, hzero, hupper⟩
      rw [hlower, hupper, hresult, hzero]
      have hr' : input_r.pop.push input_r[n] = input_r := input_r.push_pop_back
      have hq' : input_q.pop.push input_q[n] = input_q := input_q.push_pop_back
      have hd' : input_dividend.pop.push input_dividend[n] = input_dividend := input_dividend.push_pop_back
      have h1 : (Vector.replicate n (1 : Bit)).push 1 = Vector.replicate (n + 1) 1 := by
        apply Vector.ext; intro i hi; simp [Vector.getElem_push]
      by_cases hz : input_nonzero = 1 <;> by_cases hm : input_rem = 1 <;>
        simp [select, Mux.select, hz, hm, hr', hq', hd', h1]
    completeness := by
      circuit_proof_start [Mux.circuit, Mux.Spec, pop]
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by simp only [circuit_norm, previous.guarantees_eq]
  length_eq := by
    intro input
    simp only [circuit_norm, certified_length]
    ring

def certified : (n : ℕ) → Certified n
  | 0 => zero
  | n + 1 => step n (certified n)

def circuit (n : ℕ) := (certified n).circuit

@[circuit_norm] theorem circuit_assumptions (n : ℕ) :
    (circuit n).Assumptions = fun _ => True := (certified n).assumptions_eq
@[circuit_norm] theorem circuit_spec (n : ℕ) :
    (circuit n).Spec = Spec n := (certified n).spec_eq
@[circuit_norm] theorem circuit_requirements (n : ℕ) :
    (circuit n).channelsWithRequirements = [] := (certified n).requirements_eq
@[circuit_norm] theorem circuit_guarantees (n : ℕ) :
    (circuit n).elaborated.channelsWithGuarantees = [] := (certified n).guarantees_eq
@[circuit_norm] theorem circuit_length (n : ℕ) (input : Var (Input n) Bit) :
    (circuit n).localLength input = 3 * n := (certified n).length_eq input

end LeanVMCircuits.DivSelect

namespace LeanVMCircuits.Words

open BigOperators

variable {α : Type}

/-- The low `a` and the high `b` bits of `a + b`. -/
def lowBits (a : ℕ) {b : ℕ} (v : Vector α (a + b)) : Vector α a := Vector.mapFinRange a fun i => v[i.val]
def highBits (a : ℕ) {b : ℕ} (v : Vector α (a + b)) : Vector α b := Vector.mapFinRange b fun i => v[a + i.val]

theorem value_sum : ∀ {n : ℕ} (v : Vector Bit n), Adder.value v = ∑ i : Fin n, 2 ^ i.val * v[i.val].val
  | 0, v => by simp [Adder.value_zero]
  | n + 1, v => by
    rw [Adder.value_pop, Fin.sum_univ_castSucc, value_sum v.pop]
    simp

theorem value_split (a b : ℕ) (v : Vector Bit (a + b)) :
    Adder.value v = Adder.value (lowBits a v) + 2 ^ a * Adder.value (highBits a v) := by
  rw [value_sum, value_sum, value_sum, Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  · simp [lowBits, Vector.getElem_mapFinRange]
  · apply Finset.sum_congr rfl
    intro i _
    simp [highBits, Vector.getElem_mapFinRange, pow_add, Nat.mul_assoc]

theorem value_lowBits (a b : ℕ) (v : Vector Bit (a + b)) : Adder.value (lowBits a v) = Adder.value v % 2 ^ a := by
  rw [value_split a b v, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Adder.value_lt _)]

theorem value_highBits (a b : ℕ) (v : Vector Bit (a + b)) : Adder.value (highBits a v) = Adder.value v / 2 ^ a := by
  rw [value_split a b v, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (Adder.value_lt _), zero_add]

theorem value_top {n : ℕ} (v : Vector Bit (n + 1)) : v[n] = 1 ↔ 2 ^ n ≤ Adder.value v := by
  rw [Adder.value_pop]
  have : Adder.value v.pop < 2 ^ n := by simpa using Adder.value_lt v.pop
  rcases bit_zero_or_one v[n] with h | h <;> simp only [h, ZMod.val_zero, bit_one_val] <;> simp
  omega

theorem value_flip : ∀ {n : ℕ} (v : Vector Bit n), Adder.value (v.map (· + 1)) = 2 ^ n - 1 - Adder.value v
  | 0, v => by simp [Adder.value_zero]
  | n + 1, v => by
    rw [Adder.value_pop, Adder.value_pop v, ← Vector.map_pop, value_flip v.pop, Vector.getElem_map]
    have : Adder.value v.pop < 2 ^ n := by simpa using Adder.value_lt v.pop
    rcases bit_zero_or_one v[n] with h | h <;> simp [h, pow_succ] <;> omega

theorem value_replicate (n : ℕ) (b : Bit) : Adder.value (Vector.replicate n b) = b.val * (2 ^ n - 1) := by
  induction n with
  | zero => simp [Adder.value_zero]
  | succ n ih =>
    rw [Adder.value_pop]
    have hpop : (Vector.replicate (n + 1) b).pop = Vector.replicate n b := by
      apply Vector.ext; intro i hi; simp
    rw [hpop, ih]
    simp only [Vector.getElem_replicate]
    rcases bit_zero_or_one b with h | h <;> simp [h, pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

theorem sext32_eq (y : ℕ) (hy : y < 2 ^ 32) :
    Rv64.sext32 y = if y < 2 ^ 31 then y else y + (2 ^ 64 - 2 ^ 32) := by
  unfold Rv64.sext32 Rv64.signed Rv64.bits
  rw [Nat.mod_eq_of_lt hy]
  split_ifs with h
  · rw [Int.emod_eq_of_lt (by positivity) (by push_cast; omega)]; simp
  · have : ((y : ℤ) - 2 ^ 32) % 2 ^ 64 = (y : ℤ) - 2 ^ 32 + 2 ^ 64 := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by push_cast; omega) (by push_cast; omega)]
    simp only [Nat.reduceSub, Nat.reducePow] at this ⊢
    rw [this]; omega

theorem value_high_fill (f : Bit) (w : Vector Bit 64) :
    Adder.value (high f w) = Adder.value w % 2 ^ 32 + 2 ^ 32 * (f.val * (2 ^ 32 - 1)) := by
  have hsplit := value_split 32 32 (high f w)
  have hlo : lowBits 32 (b := 32) (high f w) = lowBits 32 (b := 32) w := by
    apply Vector.ext; intro i hi
    simp [high, join, lower, lowBits, Vector.getElem_mapFinRange]
  have hhi : highBits 32 (b := 32) (high f w) = Vector.replicate 32 f := by
    apply Vector.ext; intro i hi
    simp [high, join, highBits, Vector.getElem_mapFinRange]
  rw [hsplit, hlo, hhi, value_replicate, value_lowBits]

theorem value_high (w : Vector Bit 64) : Adder.value (high w[31] w) = Rv64.sext32 (Adder.value w % 2 ^ 32) := by
  rw [value_high_fill]
  have hy := Nat.mod_lt (Adder.value w) (show 0 < 2 ^ 32 by norm_num)
  rw [sext32_eq _ hy]
  have htop := value_top (n := 31) (lowBits 32 (b := 32) w)
  rw [value_lowBits] at htop
  have h31 : (lowBits 32 (b := 32) w)[31] = w[31] := by simp [lowBits, Vector.getElem_mapFinRange]
  rw [h31] at htop
  rcases bit_zero_or_one w[31] with h | h
  · rw [h]; simp [h] at htop; simp; omega
  · rw [h]; simp [h] at htop; simp; omega

theorem value_flip_if (w : Vector Bit 64) (s : Bit) :
    Adder.value (w.map (· + s)) = if s = 1 then 2 ^ 64 - 1 - Adder.value w else Adder.value w := by
  rcases bit_zero_or_one s with h | h
  · subst h; simp
  · subst h; simp [value_flip]

theorem sum_mod {n t : ℕ} {s : Vector Bit n} {c : Bit} (h : Adder.value s + 2 ^ n * c.val = t) :
    Adder.value s = t % 2 ^ n := by
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Adder.value_lt s)]

theorem highBits_map {β : Type} (f : α → β) (a : ℕ) {b : ℕ} (v : Vector α (a + b)) :
    (highBits a v).map f = highBits a (v.map f) := by
  apply Vector.ext; intro i hi; simp [highBits, Vector.getElem_mapFinRange]

theorem lowBits_map {β : Type} (f : α → β) (a : ℕ) {b : ℕ} (v : Vector α (a + b)) :
    (lowBits a v).map f = lowBits a (v.map f) := by
  apply Vector.ext; intro i hi; simp [lowBits, Vector.getElem_mapFinRange]

theorem eval_sum {n : ℕ} (env : Environment Bit) (x : Var (Adder.Output n) Bit) :
    (ProvableStruct.eval env x).sum = x.sum.map (Expression.eval env) := by
  rcases x with ⟨s, c⟩; simp [circuit_norm]

theorem eval_carry {n : ℕ} (env : Environment Bit) (x : Var (Adder.Output n) Bit) :
    (ProvableStruct.eval env x).carry = x.carry.eval env := by
  rcases x with ⟨s, c⟩; simp [circuit_norm]

theorem carry_eq {n t : ℕ} {s : Vector Bit n} {c : Bit} (h : Adder.value s + 2 ^ n * c.val = t) :
    c = if 2 ^ n ≤ t then 1 else 0 := by
  have hs := Adder.value_lt s
  rcases bit_zero_or_one c with hc | hc <;> subst hc <;> simp at h
  · rw [if_neg (by omega)]
  · rw [if_pos (by omega)]

theorem value_sextIf (w : Bit) (V : Vector Bit 64) :
    Adder.value (if w = 1 then high V[31] V else V) = MulDiv.sextIf (decide (w = 1)) (Adder.value V) := by
  by_cases h : w = 1 <;> simp [h, MulDiv.sextIf, value_high]

theorem value_eq_zero_iff : ∀ {n : ℕ} (w : Vector Bit n), Adder.value w = 0 ↔ ¬ BooleanAny.present w
  | 0, w => by
    have hw : w = #v[] := by ext i hi; omega
    subst hw; simp [Adder.value_zero, BooleanAny.present]
  | n + 1, w => by
    rw [Adder.value_pop, BooleanAny.present_pop, not_or, ← value_eq_zero_iff w.pop]
    rcases bit_zero_or_one w[n] with h | h <;> simp [h]

/-- `BooleanAny`'s output, as a value test. -/
theorem any_value {n : ℕ} (w : Vector Bit n) :
    (if BooleanAny.present w then (1 : Bit) else 0) = if Adder.value w = 0 then 0 else 1 := by
  by_cases h : BooleanAny.present w <;> simp [h, value_eq_zero_iff]

end LeanVMCircuits.Words

namespace LeanVMCircuits.Differs

structure Input (F : Type) where
  x : Vector F 64
  y : Vector F 64
  deriving ProvableStruct

/-- Whether two words differ: whether any bit of `x + y` is set, as `any(xor_word(x, y))`. -/
def main (input : Var Input Bit) : Circuit Bit (Var field Bit) :=
  BooleanAny.circuit 63 { word := Vector.mapFinRange 64 fun i => input.x[i.val] + input.y[i.val] }

instance elaborated : ElaboratedCircuit Bit Input field main := by elaborate_circuit

theorem value_xor_eq_zero (x y : Vector Bit 64) :
    Adder.value (Vector.mapFinRange 64 fun i => x[i.val] + y[i.val]) = 0 ↔ Adder.value x = Adder.value y := by
  constructor
  · intro h
    have hz : (Vector.mapFinRange 64 fun i => x[i.val] + y[i.val]) = Vector.replicate 64 0 :=
      Adder.value_injective (by rw [h, Words.value_replicate]; simp)
    congr 1
    apply Vector.ext; intro i hi
    have := congrArg (fun v : Vector Bit 64 => v[i]) hz
    simp [Vector.getElem_mapFinRange] at this
    have h2 : x[i] + y[i] + y[i] = y[i] := by rw [this, zero_add]
    rwa [add_assoc, ← two_mul, show (2 : Bit) = 0 by decide, zero_mul, add_zero] at h2
  · intro h
    have := Adder.value_injective h
    subst this
    rw [show (Vector.mapFinRange 64 fun i => x[i.val] + x[i.val]) = Vector.replicate 64 0 by
      apply Vector.ext; intro i hi
      simp [Vector.getElem_mapFinRange, ← two_mul, show (2 : Bit) = 0 by decide]]
    simp [Words.value_replicate]

def circuit : FormalCircuit Bit Input field where
  main
  elaborated
  Spec input output := output = if Adder.value input.x = Adder.value input.y then 0 else 1
  soundness := by
    circuit_proof_start [BooleanAny.Spec]
    rcases h_input with ⟨hx, hy⟩
    simp only [BooleanAny.circuit] at h_holds
    simp only [FormalCircuitBase.output, ← ElaboratedCircuit.output_eq] at h_holds ⊢
    rw [h_holds, Words.any_value]
    have : (Vector.map (Expression.eval env) (Vector.mapFinRange 64 fun i => input_var_x[i.val] + input_var_y[i.val])) =
        Vector.mapFinRange 64 fun i => input_x[i.val] + input_y[i.val] := by
      rw [← hx, ← hy]; apply Vector.ext; intro i hi; simp [Vector.getElem_mapFinRange, circuit_norm]
    rw [this]
    by_cases h : Adder.value input_x = Adder.value input_y
    · simp [h, (value_xor_eq_zero _ _).mpr h]
    · simp [h, mt (value_xor_eq_zero _ _).mp h]
  completeness := by circuit_proof_start

@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_requirements : circuit.channelsWithRequirements = [] := rfl
@[circuit_norm] theorem circuit_guarantees : circuit.elaborated.channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem circuit_length (input : Var Input Bit) : circuit.localLength input = 63 := by
  simp [circuit, elaborated, circuit_norm]
@[circuit_norm] theorem circuit_spec : circuit.Spec = fun input output =>
    output = if Adder.value input.x = Adder.value input.y then 0 else 1 := rfl

end LeanVMCircuits.Differs
