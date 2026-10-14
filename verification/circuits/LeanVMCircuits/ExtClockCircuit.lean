module

public import LeanVMCircuits.ExtClockValues
public import LeanVMCircuits.WordScale

@[expose] public section

/-!
# The Ext table's clock extras in Clean

The gates `Ext::clock_circuit` in `crates/leanvm_core/src/rv/semantics/ext.rs` adds after `Clock::builder`, product
for product: for each pointer `a`, `b`, `d` (the ports `v1`, `v2`, `vd`) the incrementers adding 8 and 16 (`Increment`:
the chain of ANDs over bits `bit + 1 ..= 62` from bit `bit`, `bit` being 3 and 4), `b`'s two addresses gated by
`!base` (`WordScale`), the flags' two bits copied out.
-/

namespace LeanVMCircuits.ExtClock

open ExtClockValues

/-- A subcircuit's output and length, as its elaboration states them, read back at the circuit's level. -/
theorem main_output {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit Bit Input Output) (input : Var Input Bit) (offset : ℕ) :
    circuit.elaborated.output input offset = circuit.output input offset := rfl

theorem main_length {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit Bit Input Output) (input : Var Input Bit) :
    circuit.elaborated.localLength input = circuit.localLength input := rfl

/-! ## Words of a list of output bits -/

/-- The 64-bit word of `outs` from bit `start`, read as an integer. -/
def word (outs : List Bit) (start : ℕ) : ℕ := valueL ((outs.drop start).take 64)

theorem word_append_left (X Y : List Bit) (s : ℕ) (h : s + 64 ≤ X.length) : word (X ++ Y) s = word X s := by
  simp only [word]
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by rw [List.length_drop]; omega)]

theorem drop_length_add_append (X Y : List Bit) (s : ℕ) : (X ++ Y).drop (X.length + s) = Y.drop s := by
  induction X with
  | nil => simp
  | cons x X ih =>
    rw [List.cons_append, List.length_cons, show X.length + 1 + s = (X.length + s) + 1 by omega,
      List.drop_succ_cons, ih]

theorem word_append_right (X Y : List Bit) (s t : ℕ) (h : t = X.length + s) : word (X ++ Y) t = word Y s := by
  simp only [word, h, drop_length_add_append]

theorem word_full (v : Vector Bit 64) : word v.toList 0 = Adder.value v := by
  simp only [word, List.drop_zero, value_eq]
  rw [List.take_of_length_le (by simp)]

/-- `n`, or zero when `base` is set: the address of a limb of `b`, which is `x0` on a base-field `b`. -/
def gate (base : Bit) (n : ℕ) : ℕ := if base = 1 then 0 else n

theorem valueL_map_zero (l : List Bit) : valueL (l.map (fun x => 0 * x)) = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, valueL_cons, ih, zero_mul, ZMod.val_zero]

theorem gate_value (base : Bit) (w : Vector Bit 64) :
    Adder.value (w.map ((base + 1) * ·)) = gate base (Adder.value w) := by
  rcases bit_zero_or_one base with rfl | rfl
  · simp [gate]
  · simp only [gate, bit_one_add_one, if_true, value_eq, Vector.toList_map]
    exact valueL_map_zero _

/-! ## The AND chain -/

namespace Chain

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
      rcases h_input with ⟨hx, -⟩
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
      rcases h_input with ⟨hx, -⟩
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

end Chain

end LeanVMCircuits.ExtClock

/-! Each circuit is irreducible to its callers in this file past its certificate, so that their proofs see its output
as a variable rather than elaborating every level of a recursive circuit of concrete width. The attribute is local: a
global one would hide the definitions from the kernel's checks of the callers. -/
attribute [local irreducible] LeanVMCircuits.ExtClock.Chain.circuit

namespace LeanVMCircuits.ExtClock

open ExtClockValues

/-! ## The incrementer -/

namespace Increment

structure Input (n : ℕ) (F : Type) where
  x : Vector F n
  deriving ProvableStruct

/-- `x + 2^b` modulo `2^(b + m + 2)`. -/
def Spec (b m : ℕ) (input : Input (b + m + 2) Bit) (output : Vector Bit (b + m + 2)) : Prop :=
  Adder.value output = (Adder.value input.x + 2 ^ b) % 2 ^ (b + m + 2)

theorem eval_one (env : Environment Bit) : Expression.eval env (1 : Expression Bit) = 1 := by
  rfl

/-- The chain of ANDs over bits `b + 1 ..= b + m` from bit `b`, its products those of `increment` in `ext.rs`. -/
def circuit (b m : ℕ) : FormalCircuit Bit (Input (b + m + 2)) (fields (b + m + 2)) where
  main := fun input => do
    let chain ← Chain.circuit m { x := slice input.x (b + 1) m (by omega), carry := input.x[b] }
    return incrOut 1 b m input.x chain.bits
  Spec := Spec b m
  soundness := by
    circuit_proof_start [Chain.Spec]
    simp only [map_slice, h_input, main_output] at h_holds ⊢
    rw [map_incrOut (Expression.eval env) (fun _ _ => rfl), eval_one, h_input]
    have hb := congrArg (fun v : Vector Bit (b + m + 2) => v[b]) h_input
    simp only [Vector.getElem_map] at hb
    rw [hb] at h_holds
    exact incrOut_value b m input_x _ h_holds.1
  completeness := by circuit_proof_start

@[circuit_norm] theorem circuit_assumptions (b m : ℕ) :
    (circuit b m).Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec (b m : ℕ) : (circuit b m).Spec = Spec b m := rfl
@[circuit_norm] theorem circuit_requirements (b m : ℕ) :
    (circuit b m).channelsWithRequirements = [] := by with_unfolding_all rfl
@[circuit_norm] theorem circuit_guarantees (b m : ℕ) :
    (circuit b m).elaborated.channelsWithGuarantees = [] := by
  simp +instances only [circuit, circuit_norm]
@[circuit_norm] theorem circuit_length (b m : ℕ) (input : Var (Input (b + m + 2)) Bit) :
    (circuit b m).localLength input = m := by
  simp only [circuit, main_length, circuit_norm]

end Increment

end LeanVMCircuits.ExtClock

attribute [local irreducible] LeanVMCircuits.ExtClock.Increment.circuit

namespace LeanVMCircuits.ExtClock

open ExtClockValues

/-! ## A pointer's two addresses -/

namespace Address

structure Input (F : Type) where
  p : Vector F 64
  deriving ProvableStruct

/-- `p + 8` and `p + 16`, modulo `2^64`. -/
def Spec (input : Input Bit) (output : Vector Bit 128) : Prop :=
  word output.toList 0 = (Adder.value input.p + 8) % 2 ^ 64 ∧
    word output.toList 64 = (Adder.value input.p + 16) % 2 ^ 64

def circuit : FormalCircuit Bit Input (fields 128) where
  main := fun input => do
    let low : Vector (Expression Bit) 64 ← Increment.circuit 3 59 { x := input.p }
    let high : Vector (Expression Bit) 64 ← Increment.circuit 4 58 { x := input.p }
    return low ++ high
  Spec := Spec
  soundness := by
    circuit_proof_start [Increment.Spec]
    simp only [main_output, main_length, Increment.circuit_length] at h_holds ⊢
    rcases h_holds with ⟨hlow, hhigh⟩
    rw [Vector.map_append, Vector.toList_append]
    refine ⟨?_, ?_⟩
    · rw [word_append_left _ _ 0 (by simp), word_full]
      exact hlow
    · rw [word_append_right _ _ 0 64 (by simp), word_full]
      exact hhigh
  completeness := by circuit_proof_start

@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_requirements : circuit.channelsWithRequirements = [] := by with_unfolding_all rfl
@[circuit_norm] theorem circuit_guarantees : circuit.elaborated.channelsWithGuarantees = [] := by
  simp +instances only [circuit, circuit_norm]
@[circuit_norm] theorem circuit_length (input : Var Input Bit) : circuit.localLength input = 117 := by
  simp only [circuit, main_length, circuit_norm]

end Address

/-! ## `b`'s two addresses, gated by `!base` -/

namespace GatedAddress

structure Input (F : Type) where
  base : F
  p : Vector F 64
  deriving ProvableStruct

/-- `p + 8` and `p + 16` modulo `2^64`, or zero when `base` is set. -/
def Spec (input : Input Bit) (output : Vector Bit 128) : Prop :=
  word output.toList 0 = gate input.base ((Adder.value input.p + 8) % 2 ^ 64) ∧
    word output.toList 64 = gate input.base ((Adder.value input.p + 16) % 2 ^ 64)

def circuit : FormalCircuit Bit Input (fields 128) where
  main := fun input => do
    let low : Vector (Expression Bit) 64 ← Increment.circuit 3 59 { x := input.p }
    let gatedLow : Vector (Expression Bit) 64 ← WordScale.circuit 64 { selector := input.base + 1, word := low }
    let high : Vector (Expression Bit) 64 ← Increment.circuit 4 58 { x := input.p }
    let gatedHigh : Vector (Expression Bit) 64 ← WordScale.circuit 64 { selector := input.base + 1, word := high }
    return gatedLow ++ gatedHigh
  Spec := Spec
  soundness := by
    circuit_proof_start [Increment.Spec, WordScale.Spec, WordScale.select]
    simp only [main_output, main_length, Increment.circuit_length]
      at h_holds ⊢
    rcases h_holds with ⟨hlow, hgl, hhigh, hgh⟩
    simp only [WordScale.circuit] at hgl hgh
    rw [Vector.map_append, Vector.toList_append, hgl, hgh]
    refine ⟨?_, ?_⟩
    · rw [word_append_left _ _ 0 (by simp), word_full, gate_value]
      congr 1
    · rw [word_append_right _ _ 0 64 (by simp), word_full, gate_value]
      congr 1
  completeness := by circuit_proof_start

@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_requirements : circuit.channelsWithRequirements = [] := by with_unfolding_all rfl
@[circuit_norm] theorem circuit_guarantees : circuit.elaborated.channelsWithGuarantees = [] := by
  simp +instances only [circuit, circuit_norm]
@[circuit_norm] theorem circuit_length (input : Var Input Bit) : circuit.localLength input = 245 := by
  have h : ∀ i, (WordScale.certified 64).circuit.localLength i = 64 := (WordScale.certified 64).length_eq
  simp only [circuit, main_length, circuit_norm, h]

end GatedAddress

end LeanVMCircuits.ExtClock

attribute [local irreducible] LeanVMCircuits.ExtClock.Address.circuit LeanVMCircuits.ExtClock.GatedAddress.circuit

namespace LeanVMCircuits.ExtClock

open ExtClockValues

/-! ## The extras -/

structure Input (F : Type) where
  v1 : Vector F 64
  v2 : Vector F 64
  vd : Vector F 64
  flags : Vector F 2
  deriving ProvableStruct

/-- The extras' outputs: the flags' two bits, then `p + 8` and `p + 16` for `p` = `v1`, `v2`, `vd`, `v2`'s gated off
to zero on a set `base`, flag bit 1. -/
def Addresses (input : Input Bit) (outs : List Bit) : Prop :=
  outs.take 2 = input.flags.toList ∧
    word outs 2 = (Adder.value input.v1 + 8) % 2 ^ 64 ∧ word outs 66 = (Adder.value input.v1 + 16) % 2 ^ 64 ∧
    word outs 130 = gate input.flags[1] ((Adder.value input.v2 + 8) % 2 ^ 64) ∧
    word outs 194 = gate input.flags[1] ((Adder.value input.v2 + 16) % 2 ^ 64) ∧
    word outs 258 = (Adder.value input.vd + 8) % 2 ^ 64 ∧ word outs 322 = (Adder.value input.vd + 16) % 2 ^ 64

def Spec (input : Input Bit) (output : Vector Bit 386) : Prop := Addresses input output.toList

theorem addresses_split (F A B D : List Bit) (flags : Vector Bit 2) (v1 v2 vd : Vector Bit 64)
    (hF : F = flags.toList) (hA : A.length = 128) (hB : B.length = 128)
    (ha : word A 0 = (Adder.value v1 + 8) % 2 ^ 64 ∧ word A 64 = (Adder.value v1 + 16) % 2 ^ 64)
    (hb : word B 0 = gate flags[1] ((Adder.value v2 + 8) % 2 ^ 64) ∧
      word B 64 = gate flags[1] ((Adder.value v2 + 16) % 2 ^ 64))
    (hd : word D 0 = (Adder.value vd + 8) % 2 ^ 64 ∧ word D 64 = (Adder.value vd + 16) % 2 ^ 64) :
    Addresses { v1, v2, vd, flags } (F ++ A ++ B ++ D) := by
  have hFl : F.length = 2 := by rw [hF]; simp
  have hFA : (F ++ A).length = 130 := by simp [hFl, hA]
  have hFAB : (F ++ A ++ B).length = 258 := by simp [hFl, hA, hB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.append_assoc, List.append_assoc, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega), hF]
  · rw [word_append_left _ _ 2 (by omega), word_append_left _ _ 2 (by omega), word_append_right _ _ 0 2 (by omega)]
    exact ha.1
  · rw [word_append_left _ _ 66 (by omega), word_append_left _ _ 66 (by omega),
      word_append_right _ _ 64 66 (by omega)]
    exact ha.2
  · rw [word_append_left _ _ 130 (by omega), word_append_right _ _ 0 130 (by omega)]
    exact hb.1
  · rw [word_append_left _ _ 194 (by omega), word_append_right _ _ 64 194 (by omega)]
    exact hb.2
  · rw [word_append_right _ _ 0 258 (by omega)]
    exact hd.1
  · rw [word_append_right _ _ 64 322 (by omega)]
    exact hd.2

def circuit : FormalCircuit Bit Input (fields 386) where
  main := fun input => do
    let a : Vector (Expression Bit) 128 ← Address.circuit { p := input.v1 }
    let b : Vector (Expression Bit) 128 ← GatedAddress.circuit { base := input.flags[1], p := input.v2 }
    let d : Vector (Expression Bit) 128 ← Address.circuit { p := input.vd }
    return #v[input.flags[0], input.flags[1]] ++ a ++ b ++ d
  Spec := Spec
  soundness := by
    circuit_proof_start [Address.Spec, GatedAddress.Spec]
    obtain ⟨-, -, -, hflags⟩ := h_input
    have hf0 := congrArg (fun v : Vector Bit 2 => v[0]) hflags
    have hf1 := congrArg (fun v : Vector Bit 2 => v[1]) hflags
    simp only [Vector.getElem_map] at hf0 hf1
    simp only [hf1, main_output, main_length, Address.circuit_length,
      GatedAddress.circuit_length] at h_holds ⊢
    rcases h_holds with ⟨ha, hb, hd⟩
    rw [Vector.map_append, Vector.map_append, Vector.map_append, Vector.toList_append, Vector.toList_append,
      Vector.toList_append]
    refine addresses_split _ _ _ _ input_flags input_v1 input_v2 input_vd ?_ (by simp) (by simp) ha hb hd
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hi : i < 2 := by simpa using h1
      interval_cases i
      · simp [hf0]
      · simp [hf1]
  completeness := by circuit_proof_start

@[circuit_norm] theorem circuit_assumptions : circuit.Assumptions = fun _ => True := rfl
@[circuit_norm] theorem circuit_spec : circuit.Spec = Spec := rfl
@[circuit_norm] theorem circuit_length (input : Var Input Bit) : circuit.localLength input = 479 := by
  simp only [circuit, main_length, circuit_norm]

end LeanVMCircuits.ExtClock
