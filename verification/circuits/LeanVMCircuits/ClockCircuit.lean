module

public import LeanVMCircuits.ClockValues
public import LeanVMCircuits.WordScale

@[expose] public section

/-!
# The clock circuit in Clean

The gate list of `Clock::builder` in `crates/leanvm_core/src/tables/clock.rs`, product for product, for any nonempty
list of access slots below `2^5`:

- per access, the carry out of bit 39 of `(ts | slot) + !prev`: over the slot bits a chain of ORs and ANDs whose
  products before the slot's lowest set bit are structural zeros and skipped (`LowChain`), then 35 majority products
  (`Adder`); then the OR of its live-bit disagreement into the row's, the first access's free;
- the AND of the in-order bits (`All`), `late = live * !ordered`, `fail = late OR disagree`;
- the step: bit 5 `live`, bits 6 to 40 the AND chain of the clock's bits 5 to 39 from `live` (`ClockChain`), bit 41
  `fail`.
-/

namespace LeanVMCircuits

open ClockValues

/-- A subcircuit's output and length, as its elaboration states them, read back at the circuit's level, where its
certificate's lemmas apply. -/
theorem main_output {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit Bit Input Output) (input : Var Input Bit) (offset : ℕ) :
    circuit.elaborated.output input offset = circuit.output input offset := rfl

theorem main_length {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit Bit Input Output) (input : Var Input Bit) :
    circuit.elaborated.localLength input = circuit.localLength input := rfl

theorem pop_get {α : Type} {n : ℕ} (v : Vector α (n + 1)) (i : ℕ) (h : i < n) :
    v.pop[i]'(by omega) = v[i] := by
  simp

theorem toList_singleton_append {α : Type} {n : ℕ} (a : α) (v : Vector α n) :
    (#v[a] ++ v).toList = a :: v.toList := by
  simp [Vector.toList_append]

namespace ClockChain

structure Input (n : ℕ) (F : Type) where
  x : Vector F n
  carry : F
  deriving ProvableStruct

structure Output (n : ℕ) (F : Type) where
  bits : Vector F n
  carry : F
  deriving ProvableStruct

/-- The chain's products are `carry * x_0 * .. * x_j`; its carry out is the last, or `carry` on no bits. -/
def Spec (n : ℕ) (input : Input n Bit) (output : Output n Bit) : Prop :=
  output.bits.toList = prefixes input.carry input.x.toList ∧ output.carry = input.carry * input.x.toList.prod

structure Certified (n : ℕ) where
  circuit : FormalCircuit Bit (Input n) (Output n)
  assumptions_eq : circuit.Assumptions = fun _ => True
  spec_eq : circuit.Spec = Spec n
  requirements_eq : circuit.channelsWithRequirements = []
  guarantees_eq : circuit.elaborated.channelsWithGuarantees = []
  length_eq : ∀ input, circuit.elaborated.localLength input = n

@[circuit_norm] theorem certified_length (n : ℕ) (previous : Certified n) (input : Var (Input n) Bit) :
    previous.circuit.elaborated.localLength input = n := previous.length_eq input
@[circuit_norm] theorem certified_guarantees (n : ℕ) (previous : Certified n) :
    previous.circuit.elaborated.channelsWithGuarantees = [] := previous.guarantees_eq

theorem toList_pop_push {α : Type} {n : ℕ} (v : Vector α (n + 1)) : v.toList = v.pop.toList ++ [v[n]] := by
  conv_lhs => rw [← v.push_pop_back]
  rw [Vector.toList_push, Vector.back_eq_getElem]
  rfl

@[circuit_norm] theorem eval_output (env : Environment Bit) {n : ℕ} (output : Output n (Expression Bit)) :
    ProvableStruct.eval env output =
      ({ bits := output.bits.map (Expression.eval env), carry := Expression.eval env output.carry } : Output n Bit) := by
  rcases output with ⟨bits, carry⟩
  simp only [circuit_norm]

def zero : Certified 0 where
  circuit := {
    main := fun input => pure { bits := #v[], carry := input.carry }
    Spec := Spec 0
    soundness := by
      circuit_proof_start
      rcases h_input with ⟨hx, hc⟩
      have hx0 : input_x = #v[] := by apply Vector.ext; intro i hi; omega
      simp [hx0, prefixes]
    completeness := by circuit_proof_start
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := rfl
  length_eq := by intro input; rfl

def step (n : ℕ) (previous : Certified n) : Certified (n + 1) where
  circuit := {
    main := fun input => do
      let lower ← previous.circuit { x := input.x.pop, carry := input.carry }
      let upper ← Product.circuit { x := input.x[n], y := lower.carry }
      return { bits := lower.bits.push upper, carry := upper }
    Spec := Spec (n + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [Product.circuit, Product.Spec]
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.output, FormalCircuitBase.localLength, certified_length,
        circuit_norm] at h_holds ⊢
      rcases h_input with ⟨hx, hc⟩
      simp only [Vector.map_pop, hx] at h_holds
      rcases h_holds with ⟨⟨hbits, hcarry⟩, hupper⟩
      have hb := congrArg (fun word : Vector Bit (n + 1) => word[n]) hx
      simp only [Vector.getElem_map] at hb
      rw [hb, hcarry] at hupper
      refine ⟨?_, ?_⟩
      · rw [Vector.map_push, Vector.toList_push, hbits, toList_pop_push input_x, prefixes_append_single]
        congr 2
        simp only [circuit_norm]
        rw [hupper]
        ring
      · rw [hupper, toList_pop_push input_x, List.prod_append, List.prod_singleton]
        ring
    completeness := by
      circuit_proof_start [Product.circuit]
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by simp only [circuit_norm, previous.guarantees_eq]
  length_eq := by intro input; simp only [circuit_norm, certified_length]

def certified : (n : ℕ) → Certified n
  | 0 => zero
  | n + 1 => step n (certified n)

def circuit (n : ℕ) := (certified n).circuit

@[circuit_norm] theorem circuit_assumptions (n : ℕ) :
    (circuit n).Assumptions = fun _ => True := (certified n).assumptions_eq
@[circuit_norm] theorem circuit_spec (n : ℕ) : (circuit n).Spec = Spec n := (certified n).spec_eq
@[circuit_norm] theorem circuit_requirements (n : ℕ) :
    (circuit n).channelsWithRequirements = [] := (certified n).requirements_eq
@[circuit_norm] theorem circuit_guarantees (n : ℕ) :
    (circuit n).elaborated.channelsWithGuarantees = [] := (certified n).guarantees_eq
@[circuit_norm] theorem circuit_length (n : ℕ) (input : Var (Input n) Bit) :
    (circuit n).localLength input = n := (certified n).length_eq input

end ClockChain

namespace ClockLow

/-- The products bit `b` of the low compare takes: none while its carry in is a structural zero, no slot bit below `b`
set, else one, an OR on a set slot bit and an AND on a clear one. -/
def bitLength (slot : Fin 32) (b : ℕ) : ℕ := if slot.val % 2 ^ b = 0 then 0 else 1

structure Input (b : ℕ) (F : Type) where
  p : Vector F b
  deriving ProvableStruct

/-- The carry out of the low `b` bits of `slot + !p`: whether `p` is below the slot's low bits. -/
def Spec (slot : Fin 32) (b : ℕ) (input : Input b Bit) (output : Bit) : Prop :=
  output = if Adder.value input.p < slot.val % 2 ^ b then 1 else 0

def length (slot : Fin 32) : ℕ → ℕ
  | 0 => 0
  | b + 1 => length slot b + bitLength slot b

structure Certified (slot : Fin 32) (b : ℕ) where
  circuit : FormalCircuit Bit (Input b) field
  assumptions_eq : circuit.Assumptions = fun _ => True
  spec_eq : circuit.Spec = Spec slot b
  requirements_eq : circuit.channelsWithRequirements = []
  guarantees_eq : circuit.elaborated.channelsWithGuarantees = []
  length_eq : ∀ input, circuit.elaborated.localLength input = length slot b

def zero (slot : Fin 32) : Certified slot 0 where
  circuit := {
    main := fun _ => pure 0
    Spec := Spec slot 0
    soundness := by
      circuit_proof_start
      simp [Nat.mod_one]
    completeness := by circuit_proof_start
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := rfl
  length_eq := by intro input; rfl

theorem step_cases (r t P lowP : ℕ) (pb : Bit) (hr : r < P) (hlow : lowP < P) (ht : t = 0 ∨ t = 1) :
    (if r = 0 then (if t = 1 then pb + 1 else 0)
      else if t = 1 then (pb + 1) + (if lowP < r then 1 else 0) + (pb + 1) * (if lowP < r then 1 else 0)
      else (pb + 1) * (if lowP < r then 1 else 0)) =
      (if lowP + P * pb.val < r + P * t then (1 : Bit) else 0) := by
  rcases ht with rfl | rfl <;> rcases bit_zero_or_one pb with rfl | rfl <;>
    simp only [ZMod.val_zero, bit_one_val, mul_zero, mul_one, add_zero] <;>
    split_ifs <;> first | rfl | decide | contradiction | omega

theorem step_value (slot : Fin 32) (b : ℕ) (lowP : ℕ) (pb : Bit) (hlow : lowP < 2 ^ b) :
    (if slot.val % 2 ^ b = 0 then (if slot.val / 2 ^ b % 2 = 1 then pb + 1 else 0)
      else if slot.val / 2 ^ b % 2 = 1 then
        (pb + 1) + (if lowP < slot.val % 2 ^ b then 1 else 0) + (pb + 1) * (if lowP < slot.val % 2 ^ b then 1 else 0)
      else (pb + 1) * (if lowP < slot.val % 2 ^ b then 1 else 0)) =
      (if lowP + 2 ^ b * pb.val < slot.val % 2 ^ (b + 1) then (1 : Bit) else 0) := by
  rw [Nat.mod_pow_succ]
  exact step_cases _ _ _ _ pb (Nat.mod_lt _ (Nat.two_pow_pos b)) hlow (by omega)

/-- The step's value from the lower carry, by `step_value`, the carry in read off the lower bits' spec. -/
theorem step_spec (slot : Fin 32) (b : ℕ) (p : Vector Bit (b + 1)) (lower out : Bit)
    (hlower : lower = if Adder.value p.pop < slot.val % 2 ^ b then 1 else 0)
    (hout : out =
      if slot.val % 2 ^ b = 0 then (if slot.val / 2 ^ b % 2 = 1 then p[b] + 1 else 0)
      else if slot.val / 2 ^ b % 2 = 1 then (p[b] + 1) + lower + (p[b] + 1) * lower
      else (p[b] + 1) * lower) :
    out = if Adder.value p < slot.val % 2 ^ (b + 1) then 1 else 0 := by
  rw [hout, hlower, Adder.value_pop p, step_value slot b _ _ (Adder.value_lt _)]

/-- Bit `b` while the carry in is a structural zero and the slot bit is set: `!p_b`, no product. -/
def stepPass (slot : Fin 32) (b : ℕ) (previous : Certified slot b) (h0 : slot.val % 2 ^ b = 0)
    (h1 : slot.val / 2 ^ b % 2 = 1) : Certified slot (b + 1) where
  circuit := {
    main := fun input => do
      let _ ← previous.circuit { p := input.p.pop }
      return input.p[b] + 1
    Spec := Spec slot (b + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.output, circuit_norm, Vector.map_pop] at h_holds ⊢
      have hb := congrArg (fun word : Vector Bit (b + 1) => word[b]) h_input
      simp only [Vector.getElem_map] at hb
      rw [h_input] at h_holds
      rw [hb]
      exact step_spec slot b input_p _ _ h_holds (by simp only [h0, h1, ↓reduceIte])
    completeness := by
      circuit_proof_start
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by simp only [circuit_norm, previous.guarantees_eq]
  length_eq := by
    intro input
    simp only [circuit_norm, previous.length_eq, length, bitLength, h0, ↓reduceIte]

/-- Bit `b` while the carry in is a structural zero and the slot bit is clear: zero, no product. -/
def stepZero (slot : Fin 32) (b : ℕ) (previous : Certified slot b) (h0 : slot.val % 2 ^ b = 0)
    (h1 : ¬slot.val / 2 ^ b % 2 = 1) : Certified slot (b + 1) where
  circuit := {
    main := fun input => do
      let _ ← previous.circuit { p := input.p.pop }
      return 0
    Spec := Spec slot (b + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.output, circuit_norm, Vector.map_pop] at h_holds ⊢
      rw [h_input] at h_holds
      exact step_spec slot b input_p _ _ h_holds (by simp only [h0, h1, ↓reduceIte])
    completeness := by
      circuit_proof_start
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by simp only [circuit_norm, previous.guarantees_eq]
  length_eq := by
    intro input
    simp only [circuit_norm, previous.length_eq, length, bitLength, h0, ↓reduceIte]

/-- Bit `b` on a set slot bit: the carry is `!p_b OR` the carry in, one product. -/
def stepOr (slot : Fin 32) (b : ℕ) (previous : Certified slot b) (h0 : ¬slot.val % 2 ^ b = 0)
    (h1 : slot.val / 2 ^ b % 2 = 1) : Certified slot (b + 1) where
  circuit := {
    main := fun input => do
      let lower ← previous.circuit { p := input.p.pop }
      BooleanOr.circuit { x := input.p[b] + 1, y := lower }
    Spec := Spec slot (b + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [BooleanOr.circuit]
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.output, FormalCircuitBase.localLength, previous.length_eq,
        circuit_norm, Vector.map_pop] at h_holds ⊢
      have hb := congrArg (fun word : Vector Bit (b + 1) => word[b]) h_input
      simp only [Vector.getElem_map] at hb
      rw [h_input] at h_holds
      rcases h_holds with ⟨hlower, hupper⟩
      rw [hupper, hb, ← BooleanOr.selection]
      exact step_spec slot b input_p _ _ hlower (by simp only [h0, h1, ↓reduceIte])
    completeness := by
      circuit_proof_start [BooleanOr.circuit]
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by simp only [circuit_norm, previous.guarantees_eq]
  length_eq := by
    intro input
    simp only [circuit_norm, previous.length_eq, length, bitLength, h0, ↓reduceIte]

/-- Bit `b` on a clear slot bit: the carry is `!p_b AND` the carry in, one product. -/
def stepAnd (slot : Fin 32) (b : ℕ) (previous : Certified slot b) (h0 : ¬slot.val % 2 ^ b = 0)
    (h1 : ¬slot.val / 2 ^ b % 2 = 1) : Certified slot (b + 1) where
  circuit := {
    main := fun input => do
      let lower ← previous.circuit { p := input.p.pop }
      Product.circuit { x := input.p[b] + 1, y := lower }
    Spec := Spec slot (b + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [Product.circuit, Product.Spec]
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.output, FormalCircuitBase.localLength, previous.length_eq,
        circuit_norm, Vector.map_pop] at h_holds ⊢
      have hb := congrArg (fun word : Vector Bit (b + 1) => word[b]) h_input
      simp only [Vector.getElem_map] at hb
      rw [h_input] at h_holds
      rcases h_holds with ⟨hlower, hupper⟩
      rw [hupper, hb]
      exact step_spec slot b input_p _ _ hlower (by simp only [h0, h1, ↓reduceIte])
    completeness := by
      circuit_proof_start [Product.circuit]
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by simp only [circuit_norm, previous.guarantees_eq]
  length_eq := by
    intro input
    simp only [circuit_norm, previous.length_eq, length, bitLength, h0, ↓reduceIte]

/-- Bit `b`'s gate, by the slot's bits, which are constants. -/
def step (slot : Fin 32) (b : ℕ) (previous : Certified slot b) : Certified slot (b + 1) :=
  if h0 : slot.val % 2 ^ b = 0 then
    if h1 : slot.val / 2 ^ b % 2 = 1 then stepPass slot b previous h0 h1 else stepZero slot b previous h0 h1
  else if h1 : slot.val / 2 ^ b % 2 = 1 then stepOr slot b previous h0 h1 else stepAnd slot b previous h0 h1

def certified (slot : Fin 32) : (b : ℕ) → Certified slot b
  | 0 => zero slot
  | b + 1 => step slot b (certified slot b)

def circuit (slot : Fin 32) (b : ℕ) := (certified slot b).circuit

@[circuit_norm] theorem circuit_assumptions (slot : Fin 32) (b : ℕ) :
    (circuit slot b).Assumptions = fun _ => True := (certified slot b).assumptions_eq
@[circuit_norm] theorem circuit_spec (slot : Fin 32) (b : ℕ) :
    (circuit slot b).Spec = Spec slot b := (certified slot b).spec_eq
@[circuit_norm] theorem circuit_requirements (slot : Fin 32) (b : ℕ) :
    (circuit slot b).channelsWithRequirements = [] := (certified slot b).requirements_eq
@[circuit_norm] theorem circuit_guarantees (slot : Fin 32) (b : ℕ) :
    (circuit slot b).elaborated.channelsWithGuarantees = [] := (certified slot b).guarantees_eq
@[circuit_norm] theorem circuit_length (slot : Fin 32) (b : ℕ) (input : Var (Input b) Bit) :
    (circuit slot b).localLength input = length slot b := (certified slot b).length_eq input

end ClockLow

/-! Each circuit is irreducible to its callers in this file past its certificate, so that their proofs see its output as
a variable rather than elaborating every level of a recursive circuit of concrete width. The attribute is local: a
global one would hide the definitions from the kernel's checks of the callers. -/
attribute [local irreducible] Adder.circuit ClockChain.circuit ClockLow.circuit

namespace ClockCompare

structure Input (F : Type) where
  cycle : Vector F 35
  low : Vector F 5
  high : Vector F 35
  deriving ProvableStruct

/-- An access in slot `slot` with previous timestamp `low + 2^5 high` is in order on the clock `2^5 cycle`. -/
def Spec (slot : Fin 32) (input : Input Bit) (output : Bit) : Prop :=
  output = if Adder.value input.low + 32 * Adder.value input.high < 32 * Adder.value input.cycle + slot.val
    then 1 else 0

@[circuit_norm] theorem eval_adder_output (env : Environment Bit) {n : ℕ} (output : Adder.Output n (Expression Bit)) :
    ProvableStruct.eval env output =
      ({ sum := output.sum.map (Expression.eval env), carry := Expression.eval env output.carry } :
        Adder.Output n Bit) := by
  rcases output with ⟨sum, carry⟩
  simp only [circuit_norm]

theorem order_value (slot : Fin 32) (low : Vector Bit 5) (high cycle sum : Vector Bit 35) (carry : Bit)
    (h : Adder.value sum + 2 ^ 35 * carry.val = Adder.value cycle + Adder.value (high.map (· + 1)) +
      (if Adder.value low < slot.val then (1 : Bit) else 0).val) :
    carry = if Adder.value low + 32 * Adder.value high < 32 * Adder.value cycle + slot.val then 1 else 0 := by
  have hs := slot.isLt
  have hc := value_complement high
  have h1 := Adder.value_lt low
  have h2 := Adder.value_lt high
  have h3 := Adder.value_lt sum
  rcases bit_zero_or_one carry with rfl | rfl <;>
    simp only [ZMod.val_zero, bit_one_val, mul_zero, mul_one, add_zero] at h <;>
    split_ifs at h ⊢ <;> simp only [ZMod.val_zero, bit_one_val] at h <;> first | rfl | omega

def circuit (slot : Fin 32) : FormalCircuit Bit Input field where
  main := fun input => do
    let low ← ClockLow.circuit slot 5 { p := input.low }
    let high ← Adder.circuit 35 { x := input.cycle, y := input.high.map (· + 1), carry := low }
    return high.carry
  Spec := Spec slot
  soundness := by
    circuit_proof_start [Spec, Adder.Spec]
    rcases h_input with ⟨hcycle, hlow, hhigh⟩
    simp only [ClockLow.Spec, main_output, main_length, ClockLow.circuit_length]
      at h_holds ⊢
    rcases h_holds with ⟨hl, ha⟩
    rw [hl] at ha
    have hy : Vector.map (Expression.eval env ∘ fun x => x + 1) input_var_high = input_high.map (· + 1) := by
      rw [← hhigh, Vector.map_map]; rfl
    simp only [Vector.map_map] at ha
    rw [hy] at ha
    have hslot : slot.val % 2 ^ 5 = slot.val := Nat.mod_eq_of_lt slot.isLt
    rw [hslot] at ha
    exact order_value slot input_low input_high input_cycle _ _ ha
  completeness := by circuit_proof_start

@[circuit_norm] theorem circuit_assumptions (slot : Fin 32) :
    (circuit slot).Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec (slot : Fin 32) : (circuit slot).Spec = Spec slot := rfl
@[circuit_norm] theorem circuit_requirements (slot : Fin 32) :
    (circuit slot).channelsWithRequirements = [] := by with_unfolding_all rfl
@[circuit_norm] theorem circuit_guarantees (slot : Fin 32) :
    (circuit slot).elaborated.channelsWithGuarantees = [] := by
  simp +instances only [circuit, circuit_norm]
@[circuit_norm] theorem circuit_length (slot : Fin 32) (input : Var Input Bit) :
    (circuit slot).localLength input = ClockLow.length slot 5 + 35 := by
  simp only [circuit, main_length, circuit_norm]

end ClockCompare

attribute [local irreducible] ClockCompare.circuit

/-- The clock's integer: its port's bits are bits 5 to 40. -/
def tsNum (ts : Vector Bit 36) : ℕ := 2 ^ 5 * Adder.value ts

namespace ClockAccess

structure Input (F : Type) where
  ts : Vector F 36
  prev : Vector F 41
  deriving ProvableStruct

/-- One access's order check (bit 0), and whether its previous timestamp has the other live bit (bit 1). -/
def Spec (slot : Fin 32) (input : Input Bit) (output : Vector Bit 2) : Prop :=
  output[0] = (if Clock.ordered (tsNum input.ts) (Adder.value input.prev) slot.val then 1 else 0) ∧
    output[1] = if Clock.disagrees (tsNum input.ts) (Adder.value input.prev) then 1 else 0

theorem differs_value (p t : Bit) :
    p + t = if (decide (p = 1) != decide (t = 1)) = true then 1 else 0 := by
  rcases bit_zero_or_one p with rfl | rfl <;> rcases bit_zero_or_one t with rfl | rfl <;> decide

def circuit (slot : Fin 32) : FormalCircuit Bit Input (fields 2) where
  main := fun input => do
    let inOrder ← ClockCompare.circuit slot {
      cycle := slice input.ts 0 35 (by omega)
      low := slice input.prev 0 5 (by omega)
      high := slice input.prev 5 35 (by omega) }
    return #v[inOrder, input.prev[40] + input.ts[35]]
  Spec := Spec slot
  soundness := by
    circuit_proof_start [ClockCompare.Spec]
    rcases h_input with ⟨hts, hprev⟩
    simp only [map_slice, hts, hprev, main_output] at h_holds ⊢
    have hp := congrArg (fun v : Vector Bit 41 => v[40]) hprev
    have ht := congrArg (fun v : Vector Bit 36 => v[35]) hts
    simp only [Vector.getElem_map] at hp ht
    refine ⟨?_, ?_⟩ <;> try simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, circuit_norm]
    · rw [h_holds, Clock.ordered, tsNum, prev_low, ts_low]
      simp only [decide_eq_true_eq]
    · rw [hp, ht, Clock.disagrees, tsNum, ts_live, testBit_value_top]
      exact differs_value _ _
  completeness := by circuit_proof_start

@[circuit_norm] theorem circuit_assumptions (slot : Fin 32) :
    (circuit slot).Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec (slot : Fin 32) : (circuit slot).Spec = Spec slot := rfl
@[circuit_norm] theorem circuit_requirements (slot : Fin 32) :
    (circuit slot).channelsWithRequirements = [] := by with_unfolding_all rfl
@[circuit_norm] theorem circuit_guarantees (slot : Fin 32) :
    (circuit slot).elaborated.channelsWithGuarantees = [] := by
  simp +instances only [circuit, circuit_norm]
@[circuit_norm] theorem circuit_length (slot : Fin 32) (input : Var Input Bit) :
    (circuit slot).localLength input = ClockLow.length slot 5 + 35 := by
  simp only [circuit, main_length, circuit_norm]

end ClockAccess

attribute [local irreducible] ClockAccess.circuit

namespace ClockAccesses

def slotAt (slots : List (Fin 32)) (i : ℕ) : Fin 32 := slots.getD i 0

structure Input (n : ℕ) (F : Type) where
  ts : Vector F 36
  prev : Vector (fields 41 F) n
  deriving ProvableStruct

structure Output (n : ℕ) (F : Type) where
  inOrder : Vector F n
  disagree : F
  deriving ProvableStruct

theorem eval_inOrder (env : Environment Bit) {n : ℕ} (output : Output n (Expression Bit)) :
    (ProvableStruct.eval env output).inOrder = output.inOrder.map (Expression.eval env) := by
  rcases output with ⟨inOrder, disagree⟩
  simp only [circuit_norm]

theorem eval_disagree (env : Environment Bit) {n : ℕ} (output : Output n (Expression Bit)) :
    (ProvableStruct.eval env output).disagree = Expression.eval env output.disagree := by
  rcases output with ⟨inOrder, disagree⟩
  simp only [circuit_norm]

/-- The first `k + 1` accesses: each one's order check, and whether any previous timestamp has the other live bit. -/
def Spec (slots : List (Fin 32)) (k : ℕ) (input : Input (k + 1) Bit) (output : Output (k + 1) Bit) : Prop :=
  (∀ i (hi : i < k + 1), output.inOrder[i] =
      if Clock.ordered (tsNum input.ts) (Adder.value input.prev[i]) (slotAt slots i).val then 1 else 0) ∧
    output.disagree =
      if ∃ i, ∃ hi : i < k + 1, Clock.disagrees (tsNum input.ts) (Adder.value input.prev[i]) = true then 1 else 0

def length (slots : List (Fin 32)) : ℕ → ℕ
  | 0 => ClockLow.length (slotAt slots 0) 5 + 35
  | k + 1 => length slots k + (ClockLow.length (slotAt slots (k + 1)) 5 + 35) + 1

structure Certified (slots : List (Fin 32)) (k : ℕ) where
  circuit : FormalCircuit Bit (Input (k + 1)) (Output (k + 1))
  assumptions_eq : circuit.Assumptions = fun _ => True
  spec_eq : circuit.Spec = Spec slots k
  requirements_eq : circuit.channelsWithRequirements = []
  guarantees_eq : circuit.elaborated.channelsWithGuarantees = []
  length_eq : ∀ input, circuit.elaborated.localLength input = length slots k

def zero (slots : List (Fin 32)) : Certified slots 0 where
  circuit := {
    main := fun input => do
      let access ← ClockAccess.circuit (slotAt slots 0) { ts := input.ts, prev := input.prev[0] }
      return { inOrder := #v[access[0]], disagree := access[1] }
    Spec := Spec slots 0
    soundness := by
      circuit_proof_start [ClockAccess.Spec]
      rcases h_input with ⟨hts, hprev⟩
      have hp : Vector.map (Expression.eval env) input_var_prev[0] = input_prev[0] := by
        rw [← hprev, ← getElem_eval_vector]; simp only [circuit_norm]
      simp only [hp, FormalCircuitBase.output] at h_holds
      rcases h_holds with ⟨ho, hd⟩
      refine ⟨?_, ?_⟩
      · intro i hi
        obtain rfl : i = 0 := by omega
        simpa using ho
      · rw [hd]
        congr 1
        apply propext
        constructor
        · intro h; exact ⟨0, by omega, h⟩
        · rintro ⟨i, hi, h⟩
          obtain rfl : i = 0 := by omega
          exact h
    completeness := by circuit_proof_start
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := by simp only [circuit_norm]
  guarantees_eq := by simp only [circuit_norm]
  length_eq := by intro input; simp only [circuit_norm, main_length, length]

def step (slots : List (Fin 32)) (k : ℕ) (previous : Certified slots k) : Certified slots (k + 1) where
  circuit := {
    main := fun input => do
      let lower ← previous.circuit { ts := input.ts, prev := input.prev.pop }
      let access ← ClockAccess.circuit (slotAt slots (k + 1)) {
        ts := input.ts, prev := input.prev[k + 1] }
      let disagree ← BooleanOr.circuit { x := lower.disagree, y := access[1] }
      return { inOrder := lower.inOrder.push access[0], disagree }
    Spec := Spec slots (k + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [ClockAccess.Spec, BooleanOr.circuit]
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.localLength, previous.length_eq, circuit_norm] at h_holds ⊢
      rcases h_input with ⟨hts, hprev⟩
      have hp : Vector.map (Expression.eval env) input_var_prev[k + 1] = input_prev[k + 1] := by
        rw [← hprev, ← getElem_eval_vector]; simp only [circuit_norm]
      have hpop : eval env input_var_prev.pop = input_prev.pop := by
        rw [← hprev]; apply Vector.ext; intro i hi
        rw [Vector.getElem_pop, ← getElem_eval_vector, ← getElem_eval_vector, Vector.getElem_pop]
      simp only [eval_inOrder, eval_disagree, FormalCircuitBase.output, hp, hpop]
        at h_holds
      rcases h_holds with ⟨⟨hlo, hld⟩, ⟨ho, hd⟩, hor⟩
      refine ⟨?_, ?_⟩
      · intro i hi
        by_cases h : i < k + 1
        · have hl := hlo i h
          rw [Vector.getElem_map] at hl
          simp only [h, dite_true, hl, pop_get _ _ h]
        · obtain rfl : i = k + 1 := by omega
          simp only [lt_irrefl, dite_false, ho]
      · simp only [main_length, ClockAccess.circuit_length]
        rw [hor, hld, hd, BooleanOr.select]
        congr 1
        apply propext
        constructor
        · rintro (h | h)
          · split_ifs at h with hx
            · obtain ⟨i, hi, hx⟩ := hx
              exact ⟨i, by omega, by rwa [pop_get _ _ hi] at hx⟩
            · exact absurd h (by decide)
          · split_ifs at h with hx
            · exact ⟨k + 1, by omega, hx⟩
            · exact absurd h (by decide)
        · rintro ⟨i, hi, hx⟩
          by_cases h : i < k + 1
          · left
            rw [if_pos ⟨i, h, by rwa [pop_get _ _ h]⟩]
          · right
            obtain rfl : i = k + 1 := by omega
            rw [if_pos hx]
    completeness := by
      circuit_proof_start [BooleanOr.circuit]
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by simp only [circuit_norm, previous.guarantees_eq]
  length_eq := by
    intro input
    simp only [circuit_norm, main_length, previous.length_eq, ClockAccess.circuit_length, length]
    omega

def certified (slots : List (Fin 32)) : (k : ℕ) → Certified slots k
  | 0 => zero slots
  | k + 1 => step slots k (certified slots k)

def circuit (slots : List (Fin 32)) (k : ℕ) := (certified slots k).circuit

theorem certified_length (slots : List (Fin 32)) (k : ℕ) (input : Var (Input (k + 1)) Bit) :
    (certified slots k).circuit.localLength input = length slots k := (certified slots k).length_eq input

@[circuit_norm] theorem circuit_assumptions (slots : List (Fin 32)) (k : ℕ) :
    (circuit slots k).Assumptions = fun _ => True := (certified slots k).assumptions_eq
@[circuit_norm] theorem circuit_spec (slots : List (Fin 32)) (k : ℕ) :
    (circuit slots k).Spec = Spec slots k := (certified slots k).spec_eq
@[circuit_norm] theorem circuit_requirements (slots : List (Fin 32)) (k : ℕ) :
    (circuit slots k).channelsWithRequirements = [] := (certified slots k).requirements_eq
@[circuit_norm] theorem circuit_guarantees (slots : List (Fin 32)) (k : ℕ) :
    (circuit slots k).elaborated.channelsWithGuarantees = [] := (certified slots k).guarantees_eq
@[circuit_norm] theorem circuit_length (slots : List (Fin 32)) (k : ℕ) (input : Var (Input (k + 1)) Bit) :
    (circuit slots k).localLength input = length slots k := (certified slots k).length_eq input

end ClockAccesses

namespace ClockAll

structure Input (n : ℕ) (F : Type) where
  word : Vector F n
  deriving ProvableStruct

/-- The AND of the bits, by a chain of products from the first. -/
def Spec (n : ℕ) (input : Input (n + 1) Bit) (output : Bit) : Prop :=
  output = if ∀ i (hi : i < n + 1), input.word[i] = 1 then 1 else 0

structure Certified (n : ℕ) where
  circuit : FormalCircuit Bit (Input (n + 1)) field
  assumptions_eq : circuit.Assumptions = fun _ => True
  spec_eq : circuit.Spec = Spec n
  requirements_eq : circuit.channelsWithRequirements = []
  guarantees_eq : circuit.elaborated.channelsWithGuarantees = []
  length_eq : ∀ input, circuit.elaborated.localLength input = n

def zero : Certified 0 where
  circuit := {
    main := fun input => pure input.word[0]
    Spec := Spec 0
    soundness := by
      circuit_proof_start
      rcases bit_zero_or_one input_word[0] with h | h
      · rw [if_neg (fun hall => by have := hall 0 (by omega); simp_all)]; exact h
      · rw [if_pos (fun i hi => by obtain rfl : i = 0 := (by omega); exact h)]; exact h
    completeness := by circuit_proof_start
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := rfl
  length_eq := by intro input; rfl

def step (n : ℕ) (previous : Certified n) : Certified (n + 1) where
  circuit := {
    main := fun input => do
      let lower ← previous.circuit { word := input.word.pop }
      Product.circuit { x := lower, y := input.word[n + 1] }
    Spec := Spec (n + 1)
    requirementsChannelsLawful := by simp only [circuit_norm, previous.requirements_eq]
    soundness := by
      circuit_proof_start [Product.circuit, Product.Spec]
      simp only [previous.assumptions_eq, previous.spec_eq, previous.requirements_eq,
        true_implies, or_true, and_true] at *
      simp only [Spec, FormalCircuitBase.output, FormalCircuitBase.localLength, previous.length_eq,
        circuit_norm, Vector.map_pop] at h_holds ⊢
      simp only [h_input] at h_holds
      rcases h_holds with ⟨hlower, hupper⟩
      have hb := congrArg (fun word : Vector Bit (n + 1 + 1) => word[n + 1]) h_input
      simp only [Vector.getElem_map] at hb
      rw [hupper, hlower, hb]
      have hall : (∀ i (hi : i < n + 1 + 1), input_word[i] = 1) ↔
          (∀ i (hi : i < n + 1), input_word.pop[i] = 1) ∧ input_word[n + 1] = 1 := by
        constructor
        · intro h; exact ⟨fun i hi => by rw [pop_get _ _ hi]; exact h i (by omega), h (n + 1) (by omega)⟩
        · rintro ⟨h, hl⟩ i hi
          by_cases hi' : i < n + 1
          · rw [← pop_get _ _ hi']; exact h i hi'
          · obtain rfl : i = n + 1 := by omega
            exact hl
      rw [if_congr hall rfl rfl]
      by_cases h : ∀ i (hi : i < n + 1), input_word.pop[i] = 1 <;>
        rcases bit_zero_or_one input_word[n + 1] with hl | hl <;> simp [h, hl]
    completeness := by
      circuit_proof_start [Product.circuit]
      simp [previous.assumptions_eq]
  }
  assumptions_eq := rfl
  spec_eq := rfl
  requirements_eq := rfl
  guarantees_eq := by simp only [circuit_norm, previous.guarantees_eq]
  length_eq := by intro input; simp only [circuit_norm, previous.length_eq]

def certified : (n : ℕ) → Certified n
  | 0 => zero
  | n + 1 => step n (certified n)

def circuit (n : ℕ) := (certified n).circuit

theorem certified_length (n : ℕ) (input : Var (Input (n + 1)) Bit) :
    (certified n).circuit.localLength input = n := (certified n).length_eq input

@[circuit_norm] theorem circuit_assumptions (n : ℕ) :
    (circuit n).Assumptions = fun _ => True := (certified n).assumptions_eq
@[circuit_norm] theorem circuit_spec (n : ℕ) : (circuit n).Spec = Spec n := (certified n).spec_eq
@[circuit_norm] theorem circuit_requirements (n : ℕ) :
    (circuit n).channelsWithRequirements = [] := (certified n).requirements_eq
@[circuit_norm] theorem circuit_guarantees (n : ℕ) :
    (circuit n).elaborated.channelsWithGuarantees = [] := (certified n).guarantees_eq
@[circuit_norm] theorem circuit_length (n : ℕ) (input : Var (Input (n + 1)) Bit) :
    (circuit n).localLength input = n := (certified n).length_eq input

end ClockAll

end LeanVMCircuits
