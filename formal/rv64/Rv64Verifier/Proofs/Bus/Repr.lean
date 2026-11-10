import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Model.Bus
import Rv64Verifier.Model.Layout

/-!
# The bus's values in memory

What `bus.rs`'s functions read, as `Proofs/Runtime` holds it: an `E` is three doublewords
(`eAt`), a `Vec<E>` its capacity, pointer and length (`vecEs`). A value a function only reads is
`Held`: valid, outside the free heap and `NEXT` (no allocation writes it), apart from the
function's stack (`n` bytes below `sp`). `fingerprintsRust` is `verify_bus_balance`'s
`fingerprints` closure, as `verifyBusBalanceM` writes it.

A `Form` is a `Vec` of 48-byte terms, each a `Monomial` (tag at `+0`: `0` for `One`, `1` for
`X(i)`, any other for `Xy(i, j)`, as `Form::evaluate` and `Form::add_scaled` branch; `i`, `j` at
`+8`, `+16`) and its coefficient at `+24` (`formAt`). The layout agent's `Proofs/Layout/Repr.lean`
reads them the same way (`monoOf`, `termsOf`, `formOf`); these are kept separate here because the
two files cannot yet be imported together.
-/

namespace Rv64Verifier.Bus
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model

/-- The `m` bytes from `a`, read only by a function with an `n`-byte stack: valid, outside the
free heap and `NEXT`, apart from the stack. -/
structure Held (s : MachineState) (n : Nat) (a : Word) (m : Nat) : Prop where
  valid : ValidMemRange a (m / 8)
  free : Outside s a m
  stack : Apart a m (stackLo s n) n

/-- A `Vec<E>` read only: its header and its elements. -/
structure EVecHeld (s : MachineState) (n : Nat) (a : Word) : Prop where
  header : Held s n a 24
  elems : Held s n (vecPtr s a) (24 * (vecLen s a).toNat)

/-- The linear facts of a region read only. -/
theorem Held.facts {s : MachineState} {n : Nat} {a : Word} {m : Nat} (h : Held s n a m)
    (hm : 8 ≤ m) (h8 : m % 8 = 0) :
    a.toNat % 8 = 0 ∧ 0x20 ≤ a.toNat ∧ a.toNat + m ≤ 0xc0000008 ∧ Apart a m nextAddr 8 ∧
      Apart a m (stackLo s n) n := by
  have hb := ValidMemRange.bounds h.valid (by omega)
  refine ⟨hb.2.1, hb.1, by omega, h.free.2, h.stack⟩

/-- `verify_bus_balance`'s `fingerprints(pc, memory_count, bytecode_count)`: the three framework
tuples' fingerprints, over the captured `weights`, `memory_index`, `memory`, `bytecode_index` and
`bytecode_value`. -/
def fingerprintsRust (weights : List E) (memoryIndex : E) (memory : List E)
    (bytecodeIndex bytecodeValue : E) (pc memoryCount bytecodeCount : E) : List E :=
  [dotRust (weights.take 3) [sepStateRust, pc, gpowRust 0#64],
    dotRust (weights.take 6) [sepMemRust, memoryIndex, memoryCount, memory.getD 0 0,
      memory.getD 1 0, memory.getD 2 0],
    dotRust (weights.take 3) [sepBytecodeRust, bytecodeIndex, bytecodeCount] + bytecodeValue]

theorem eListAt_take (s : MachineState) (p : Word) {n k : Nat} (h : k ≤ n) :
    (eListAt s p n).take k = eListAt s p k := by
  simp only [eListAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem eListAt_getD (s : MachineState) (p : Word) {n i : Nat} (h : i < n) :
    (eListAt s p n).getD i 0 = eAt s (p + BitVec.ofNat 64 (24 * i)) := by
  rw [List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact h), eListAt_getElem]

theorem eListAt_congr {s t : MachineState} {p : Word} {n : Nat}
    (h : ∀ i < n, eAt t (p + BitVec.ofNat 64 (24 * i)) = eAt s (p + BitVec.ofNat 64 (24 * i))) :
    eListAt t p n = eListAt s p n :=
  List.map_congr_left fun i hi ↦ h i (List.mem_range.mp hi)

theorem eListAt_three (s : MachineState) (p : Word) :
    eListAt s p 3 = [eAt s p, eAt s (p + 24), eAt s (p + 48)] := by
  simp [eListAt, List.range_succ]

theorem eListAt_six (s : MachineState) (p : Word) :
    eListAt s p 6 = [eAt s p, eAt s (p + 24), eAt s (p + 48), eAt s (p + 72), eAt s (p + 96),
      eAt s (p + 120)] := by
  simp [eListAt, List.range_succ]

theorem limbs_eNew (x : BitVec 64) : limbs (eNew x) = (x, 0, 0) := by
  rw [eNew, limbs_ofK, BF64.toBitVec_ofBitVec]
  rfl

/-- The `E` whose limbs are `(c, 0, 0)`, a constant the code stores. -/
theorem eAt_const {t : MachineState} {a : Word} {c : BitVec 64} (h0 : t.getMem a = c)
    (h1 : t.getMem (a + 8) = 0) (h2 : t.getMem (a + 16) = 0) : eAt t a = eNew c :=
  eAt_eq_of_limbs (by rw [limbs_eNew, h0, h1, h2])

theorem sepStateRust_eNew : sepStateRust = eNew 1 := by
  apply eq_of_limbs; rw [limbs_eNew]; exact limbs_one

theorem gpowRust_zero : gpowRust 0#64 = eNew 1 := by
  rw [gpowRust, BitVec.toNat_ofNat, Nat.zero_mod, pow_zero]
  apply eq_of_limbs; rw [limbs_eNew]; exact limbs_one

theorem sepMemRust_eNew : sepMemRust = eNew 2 := rfl

theorem sepBytecodeRust_eNew : sepBytecodeRust = eNew 4 := rfl

/-! ## Forms -/

/-- The `Monomial` at `a`. -/
def monoAt (s : MachineState) (a : Word) : LayoutMirror.Monomial :=
  if s.getMem a = 0 then .one
  else if s.getMem a = 1 then .x (s.getMem (a + 8)).toNat
  else .xy (s.getMem (a + 8)).toNat (s.getMem (a + 16)).toNat

/-- The `n` terms from `p`, 48 bytes apart. -/
def termsAt (s : MachineState) (p : Word) (n : Nat) : List LayoutMirror.Term :=
  (List.range n).map fun i ↦
    (monoAt s (p + BitVec.ofNat 64 (48 * i)), eAt s (p + BitVec.ofNat 64 (48 * i) + 24))

/-- The `Form` at `a`. -/
def formAt (s : MachineState) (a : Word) : LayoutMirror.FormRust :=
  ⟨termsAt s (vecPtr s a) (vecLen s a).toNat⟩

/-- The statement's forms of the `Vec<Form>` at `a`. -/
def formVecAt (s : MachineState) (a : Word) : List Form :=
  (List.range (vecLen s a).toNat).map fun j ↦
    (formAt s (vecPtr s a + BitVec.ofNat 64 (24 * j))).toSpec

/-- The `n` `Vec<Form>`s from `a`. -/
def formRowsAt (s : MachineState) (a : Word) (n : Nat) : List (List Form) :=
  (List.range n).map fun i ↦ formVecAt s (a + BitVec.ofNat 64 (24 * i))

end Rv64Verifier.Bus
