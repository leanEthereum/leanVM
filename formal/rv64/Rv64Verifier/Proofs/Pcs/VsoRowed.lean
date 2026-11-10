import Rv64Verifier.Proofs.Pcs.VsoKernelCall

/-!
# `verify_stacked_opening`'s level loop: the rows, where both paths join

From `eq_kernel`'s return (`Kerneled`, `0x8000b150`) the level computes its rows' values: by
`base_dot` at level `0` (from `0x8000b2e0`), by `dot(ext_row(row), _)` deeper (from
`0x8000b158`). Both paths join at `0x8000b42c` (`Rowed`): the rows' buffer and count in
`s9`/`s11` (`x25`/`x27`), the registers the level's tail reads kept, the frame `RowW`.

`LeavesAt` is what the rows read: pair `i` of the slices at `S - 832` (`sliceP`, `sliceL`) points
to row `i`'s words, `Clear` of everything the rows write. `RowsZero` and `RowsDeep` state the two
paths.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- Row `i`'s pointer, in pair `i` of the slices at `S - 832`. -/
def sliceP (s k : MachineState) (i : ℕ) : Word :=
  k.getMem (k.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (16 * i))

/-- Row `i`'s length in words. -/
def sliceL (s k : MachineState) (i : ℕ) : Word :=
  k.getMem (k.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (16 * i + 8))

/-- At `k`, the rows `ws`: their count in `s4` (`x20`), the slices' buffer at `S - 832` and every
row's words `Clear` from `heapNext k`. -/
structure LeavesAt (s k : MachineState) (ws : List (List K)) : Prop where
  n : (k.getReg .x20).toNat = ws.length
  slices : ws.length = 0 ∨ Region (k.getMem (s.getReg .x2 - 832)) (16 * ws.length) ∧
    Clear s (heapNext k) (k.getMem (s.getReg .x2 - 832)) (16 * ws.length)
  buf : ∀ i < ws.length, (sliceL s k i).toNat = 0 ∨
    Region (sliceP s k i) (8 * (sliceL s k i).toNat) ∧
      Clear s (heapNext k) (sliceP s k i) (8 * (sliceL s k i).toNat)
  words : ∀ i (h : i < ws.length),
    (k.readWords (sliceP s k i) (sliceL s k i).toNat).map BF64.ofBitVec = ws[i]

/-- What the rows write from `k` on: the spill `S - 904`, the slot `S - 784`, the rows' `Vec` at
`S - 464`, the scratch `S - 384`, the callees' stacks, `NEXT`, the heap allocated since `k`. -/
def RowW (s k r : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 904) 8 ∨ Within a (s.getReg .x2 - 784) 8 ∨
    Within a (s.getReg .x2 - 464) 24 ∨ Within a (s.getReg .x2 - 384) 24 ∨
    Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh k r a

/-- At `0x8000b42c`, the rows' values `rows` from `eq_kernel`'s return `k`: the buffer in `x25`,
the count in `x27`. -/
structure Rowed (s k r : MachineState) (rows : List E) : Prop where
  pc : r.pc = 0x8000b42c
  sp : r.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ q ∈ [Reg.x9, .x23, .x26], r.getReg q = k.getReg q
  inv : InvR s r (r.getMem nextAddr)
  heap : HeapOk r
  mono : heapNext k ≤ heapNext r
  value : eListAt r (r.getReg .x25) (r.getReg .x27).toNat = rows
  buf : NewBuf k r (r.getReg .x25) (24 * (r.getReg .x27).toNat) 8
  fr : DFrame k r (RowW s k r)

/-- **Level `0`'s rows**, `base_dot` against the kernel, from `0x8000b2e0`. -/
def RowsZero : Prop :=
  ∀ (s t' k k' : MachineState) (lf : List E) (ws : List (List K)), VsoPre s →
    Kerneled s t' k lf → LeavesAt s k ws → k.getMem (s.getReg .x2 - 808) = k.getReg .x23 →
    k'.pc = 0x8000b2e0 → (∀ a, k'.getMem a = k.getMem a) →
    (∀ q ∈ calleeSaved, k'.getReg q = k.getReg q) →
    ∃ r, Reaches Image.code k' r ∧
      (FailR s r ∨ Rowed s k r (Model.Pcs.rowValuesRust 0 ws (Model.eqKernelRust lf)))

/-- **A deeper level's rows**, `dot(ext_row(row), _)` against the kernel, from `0x8000b158`;
`S - 880` holds the constant of the division by three. -/
def RowsDeep : Prop :=
  ∀ (s t' k k' : MachineState) (lf : List E) (ws : List (List K)) (ℓ : ℕ), VsoPre s → ℓ ≠ 0 →
    Kerneled s t' k lf → LeavesAt s k ws →
    k.getMem (s.getReg .x2 - 880) = 0xffffffffaaaaaaab →
    k'.pc = 0x8000b158 → (∀ a, k'.getMem a = k.getMem a) →
    (∀ q ∈ calleeSaved, k'.getReg q = k.getReg q) →
    ∃ r, Reaches Image.code k' r ∧
      (FailR s r ∨ Rowed s k r (Model.Pcs.rowValuesRust ℓ ws (Model.eqKernelRust lf)))

end Rv64Verifier.Proofs.Pcs.Vso
