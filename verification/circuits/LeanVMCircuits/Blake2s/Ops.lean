module

public import LeanVMCircuits.Blake2s.Words
public import Clean.Circuit.Loops

@[expose] public section

/-!
The word operations of the BLAKE2s circuit, as Clean circuits over GF(2).

Each operation names the 32 bits of its result as free wires: a witness constrained to an affine expression of earlier
wires, which costs no product. Only the additions' carries are products.
-/

namespace LeanVMCircuits.Blake2s

open LeanVMCircuits

/-- A word's bits, each named by a witness constrained to equal it. -/
def defineBit (e : Expression Bit) : Circuit Bit (Expression Bit) := do
  let w ← witness e
  assertZero (w - e)
  return w

instance : Circuit.ConstantLength defineBit where
  localLength := 1
  localLength_eq _ _ := rfl

namespace Define

def main (input : Var (fields 32) Bit) : Circuit Bit (Var (fields 32) Bit) := Circuit.map input defineBit

instance elaborated : ElaboratedCircuit Bit (fields 32) (fields 32) main where
  localLength _ := 32
  localLength_eq _ _ := by simp only [main, circuit_norm]; rfl
  subcircuitsConsistent _ _ := by simp only [main, circuit_norm, defineBit]

def Spec (input : fields 32 Bit) (output : fields 32 Bit) : Prop := output = input

theorem soundness : Soundness Bit main (fun _ => True) Spec := by
  circuit_proof_start [defineBit]
  rw [← h_input]
  ext i hi
  simpa [sub_eq_zero, Expression.eval] using h_holds ⟨i, hi⟩

theorem completeness : Completeness Bit main (fun _ => True) := by
  circuit_proof_start [defineBit]
  intro i
  rw [h_env i, sub_self]

def circuit : FormalCircuit Bit (fields 32) (fields 32) where
  main
  Spec
  soundness
  completeness

end Define

namespace Add32

/-- `x + y` modulo `2^32`: Clean's 32-bit wrapping adder, 31 carry products, then the sum's bits named. -/
def main (input : Var (WrappingAdder.Input 32) Bit) : Circuit Bit (Var (fields 32) Bit) := do
  let sum ← WrappingAdder.circuit 31 input
  Define.circuit sum

instance elaborated : ElaboratedCircuit Bit (WrappingAdder.Input 32) (fields 32) main := by
  elaborate_circuit

def Spec (input : WrappingAdder.Input 32 Bit) (output : fields 32 Bit) : Prop :=
  toWord output = toWord input.x + toWord input.y

theorem soundness : Soundness Bit main (fun _ => True) Spec := by
  circuit_proof_start [WrappingAdder.circuit, Define.circuit, Define.Spec]
  obtain ⟨hadd, hdef⟩ := h_holds
  rw [hdef]
  exact toWord_add _ _ _ hadd

theorem completeness : Completeness Bit main (fun _ => True) := by
  circuit_proof_start [WrappingAdder.circuit, Define.circuit]

def circuit : FormalCircuit Bit (WrappingAdder.Input 32) (fields 32) where
  main
  Spec
  soundness
  completeness

end Add32

theorem value_literal {n : ℕ} (k : BitVec n) : Adder.value (literal k : Vector Bit n) = k.toNat := by
  have h := congrArg BitVec.toNat (toWord_literal k)
  rwa [toWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Adder.value_lt _)] at h

theorem value_cons {n : ℕ} (b : Bit) (v : Vector Bit n) :
    Adder.value (#v[b] ++ v) = b.val + 2 * Adder.value v := by
  simp [Adder.value]

/-- The bits of `y` above its lowest. -/
def upper {α : Type} (y : Vector α 32) : Vector α 31 := Vector.ofFn fun i => y[i.val + 1]

theorem map_upper {α β : Type} (f : α → β) (y : Vector α 32) : (upper y).map f = upper (y.map f) := by
  ext i hi
  simp [upper]

theorem toList_upper {α : Type} (y : Vector α 32) : y.toList = y[0] :: (upper y).toList := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rcases i with _ | i <;> simp [upper]

theorem value_upper (y : Vector Bit 32) : Adder.value y = y[0].val + 2 * Adder.value (upper y) := by
  simp only [Adder.value, toList_upper y, List.foldr_cons]

/-- `b` below the 31 bits of `v`. -/
def consLow {α : Type} (b : α) (v : Vector α 31) : Vector α 32 := ⟨#[b] ++ v.toArray, by simp⟩

theorem toList_consLow {α : Type} (b : α) (v : Vector α 31) : (consLow b v).toList = b :: v.toList := by
  simp [consLow, Vector.toList]

theorem value_consLow (b : Bit) (v : Vector Bit 31) : Adder.value (consLow b v) = b.val + 2 * Adder.value v := by
  simp only [Adder.value, toList_consLow, List.foldr_cons]

theorem map_consLow {α β : Type} (f : α → β) (b : α) (v : Vector α 31) :
    (consLow b v).map f = consLow (f b) (v.map f) := by
  ext i hi
  rcases i with _ | i <;> simp [consLow]

theorem eval_literal {n : ℕ} (env : Environment Bit) (k : BitVec n) :
    (literal k : Vector (Expression Bit) n).map (Expression.eval env) = literal k := by
  ext i hi
  simp only [literal, Vector.getElem_map, Vector.getElem_ofFn]
  split <;> rfl

theorem map_xorBits {n : ℕ} (env : Environment Bit) (x y : Vector (Expression Bit) n) :
    (xorBits x y).map (Expression.eval env) = xorBits (x.map (Expression.eval env)) (y.map (Expression.eval env)) := by
  ext i hi
  simp [xorBits, Expression.eval]

theorem map_rotr {α β : Type} {n : ℕ} [NeZero n] (f : α → β) (x : Vector α n) (r : ℕ) :
    (rotr x r).map f = rotr (x.map f) r := by
  ext i hi
  simp [rotr]

theorem toNat_toWord {n : ℕ} (v : Vector Bit n) : (toWord v).toNat = Adder.value v := by
  rw [toWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Adder.value_lt _)]

private theorem even_sum (q u b : ℕ) (hb : b < 2) :
    b + 2 * ((q + u) % 2 ^ 31) = (2 * q + (b + 2 * u)) % 2 ^ 32 := by
  norm_num
  omega

namespace AddOdd

/-- `k + y` modulo `2^32` for an odd literal `k`: the 32-bit adder on the literal's bits. -/
def main (k : BitVec 32) (y : Var (fields 32) Bit) : Circuit Bit (Var (fields 32) Bit) := do
  let sum ← WrappingAdder.circuit 31 { x := literal k, y }
  Define.circuit sum

instance elaborated (k : BitVec 32) : ElaboratedCircuit Bit (fields 32) (fields 32) (main k) := by
  elaborate_circuit

def Spec (k : BitVec 32) (y : fields 32 Bit) (output : fields 32 Bit) : Prop := toWord output = k + toWord y

theorem soundness (k : BitVec 32) : Soundness Bit (main k) (fun _ => True) (Spec k) := by
  circuit_proof_start [WrappingAdder.circuit, Define.circuit, Define.Spec]
  obtain ⟨hadd, hdef⟩ := h_holds
  rw [hdef, toWord_add _ _ _ hadd, eval_literal, toWord_literal]

theorem completeness (k : BitVec 32) : Completeness Bit (main k) (fun _ => True) := by
  circuit_proof_start [WrappingAdder.circuit, Define.circuit]

def circuit (k : BitVec 32) : FormalCircuit Bit (fields 32) (fields 32) where
  main := main k
  Spec := Spec k
  soundness := soundness k
  completeness := completeness k

end AddOdd

namespace AddEven

/-- `k + y` modulo `2^32` for an even literal `k`: the low bit is `y_0`, its carry zero, and `k / 2` is added to
the upper 31 bits with 30 carry products. -/
def main (k : BitVec 32) (y : Var (fields 32) Bit) : Circuit Bit (Var (fields 32) Bit) := do
  let sum ← WrappingAdder.circuit 30 { x := literal (BitVec.ofNat 31 (k.toNat / 2)), y := upper y }
  Define.circuit (consLow y[0] sum)

instance elaborated (k : BitVec 32) : ElaboratedCircuit Bit (fields 32) (fields 32) (main k) := by
  elaborate_circuit

def Spec (k : BitVec 32) (y : fields 32 Bit) (output : fields 32 Bit) : Prop :=
  k.getLsbD 0 = false → toWord output = k + toWord y

theorem soundness (k : BitVec 32) : Soundness Bit (main k) (fun _ => True) (Spec k) := by
  circuit_proof_start [WrappingAdder.circuit, Define.circuit, Define.Spec]
  intro heven
  obtain ⟨hadd, hdef⟩ := h_holds
  rw [hdef, map_consLow]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_toWord, value_consLow, BitVec.toNat_add, toNat_toWord, ← h_input, value_upper]
  simp only [WrappingAdder.Spec, eval_literal, value_literal] at hadd
  rw [hadd]
  have hk : k.toNat % 2 = 0 := by
    have := heven
    rw [BitVec.getLsbD, Nat.testBit_zero] at this
    simpa using this
  have hq : (BitVec.ofNat 31 (k.toNat / 2)).toNat = k.toNat / 2 := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; have := k.isLt; omega
  rw [hq]
  have hb := ZMod.val_lt (Expression.eval env input_var[0])
  have hk2 := k.isLt
  rw [even_sum _ _ _ hb, Vector.getElem_map, map_upper]
  congr 1
  omega

theorem completeness (k : BitVec 32) : Completeness Bit (main k) (fun _ => True) := by
  circuit_proof_start [WrappingAdder.circuit, Define.circuit]

def circuit (k : BitVec 32) : FormalCircuit Bit (fields 32) (fields 32) where
  main := main k
  Spec := Spec k
  soundness := soundness k
  completeness := completeness k

end AddEven

namespace XorRotr

/-- `(x ^ y) >>> r`: free wires only, the result's bits named. -/
def main (r : Fin 32) (input : Var (WrappingAdder.Input 32) Bit) : Circuit Bit (Var (fields 32) Bit) :=
  Define.circuit (rotr (xorBits input.x input.y) r.val)

instance elaborated (r : Fin 32) : ElaboratedCircuit Bit (WrappingAdder.Input 32) (fields 32) (main r) := by
  elaborate_circuit

def Spec (r : Fin 32) (input : WrappingAdder.Input 32 Bit) (output : fields 32 Bit) : Prop :=
  toWord output = (toWord input.x ^^^ toWord input.y).rotateRight r.val

theorem soundness (r : Fin 32) : Soundness Bit (main r) (fun _ => True) (Spec r) := by
  circuit_proof_start [Define.circuit, Define.Spec]
  rw [h_holds, map_rotr, map_xorBits, h_input.1, h_input.2, toWord_rotr _ _ r.isLt, toWord_xor]

theorem completeness (r : Fin 32) : Completeness Bit (main r) (fun _ => True) := by
  circuit_proof_start [Define.circuit]

def circuit (r : Fin 32) : FormalCircuit Bit (WrappingAdder.Input 32) (fields 32) where
  main := main r
  Spec := Spec r
  soundness := soundness r
  completeness := completeness r

end XorRotr

end LeanVMCircuits.Blake2s
