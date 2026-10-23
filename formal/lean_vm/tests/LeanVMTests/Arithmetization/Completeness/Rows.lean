import LeanVM.Arithmetization.Completeness.Bus
import LeanVMTests.Arithmetization.Completeness.Fixture

/-!
# Tests: the rows of executed instructions

`rowOf_sends` says that the row of an instruction that executes sends the state step, the bytecode
read of its entry and the reads of the cells it reads, each with the limbs the image holds there.
An `XOR` on the all-zero image executes, and its row sends exactly that. On the image of
`Fixture`, where no word is the sum of two, no `XOR` executes, and the same row
sends something else: its third read carries the sum, not the cell. A `JUMP`'s pushed successor
is the one thing that depends on a local witness, the indicator `b`: a taken jump with `b = 0`
pushes the fall-through (the constraints that reject that witness are in
`Completeness.Satisfied`'s tests). The numbers of a row's reads are
the chain's (`Completeness.Bus`): two rows reading one cell number its reads `0, 1, 2, 3, …`.
-/

namespace LeanVMTests.Arithmetization.Completeness.Rows

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVMTests.Arithmetization.Completeness.Fixture

/-- The sentinel counter of a `2^11`-slot program, as a literal term, as in `Fixture`. -/
local notation "d₀" => (gpow 2047 : K)

/-! ## An `XOR` that executes -/

/-- The row of an `XOR` of three cells of the zero image sends what `sendsOf` says, for any
counts. -/
theorem xor_row_sends (cnt : ℕ → K) (rbc : K) (data : ProverData K) :
    rowSends (opComponent (Instr.xor (gpow 0) (gpow 0) (gpow 0)).opcode)
        (Environment.fromArray
          (rowOf zeroImage (gpow 5) 1 cnt rbc (.xor (gpow 0) (gpow 0) (gpow 0))) data) =
      sendsOf (gpow 5) 1 (Regs.next ⟨gpow 5, 1⟩) rbc (entry (.xor (gpow 0) (gpow 0) (gpow 0)))
        (readsOf zeroImage 1 cnt (.xor (gpow 0) (gpow 0) (gpow 0))) :=
  rowOf_sends zeroImage_xor cnt rbc data

/-- The state pull is `(pc, fp)` and the push the fall-through. -/
example (rbc : K) (e : Vector K 8) (reads : List (K × K × Vector K 3)) :
    (sendsOf (gpow 5) 1 (Regs.next ⟨gpow 5, 1⟩) rbc e reads).take 2 =
      [(StatePull.name, #[gpow 5, 1]), (StatePush.name, #[g * gpow 5, 1])] := by
  simp only [sendsOf, List.cons_append, List.take_succ_cons, List.take_zero, Regs.next]

/-- The three cells an `XOR` reads, in the circuit's order. -/
example : readAddrs zeroImage 1 (.xor (gpow 0) (gpow 1) (gpow 2)) =
    [1 * gpow 0, 1 * gpow 1, 1 * gpow 2] := by simp only [readAddrs]

/-- A `DEREF` reads its target at `p · o₂`, with `p` the word at `fp · o₁`, not at `fp · o₂`; the
pointer, the target, then the local cell, the deployed order (`tables.rs:642-647`). -/
example {κ : ℕ} (mem : MemImage κ) (fp o1 o2 o3 : K) (m : DerefMode) :
    readAddrs mem fp (.deref o1 o2 o3 m) = [fp * o1, (mem.limbsAt (fp * o1))[0] * o2, fp * o3] :=
  rfl

/-! ## The execution is load-bearing -/

/-- On the sum-free image the `XOR` of the cell `g^0` with itself into itself does not execute. -/
example : execute (badImage d₀) ⟨gpow 5, 1⟩ (.xor (gpow 0) (gpow 0) (gpow 0)) = none :=
  badImage_no_xor _ _ _ _

/-- The row `xor_exec_sends` would describe is not `sendsOf` there: the third read of the row
carries `v_A + v_B`, the cell's limbs plus themselves, which in characteristic two is `0`, while
the image holds `y = (0, 1, 0)` at that cell. -/
theorem xor_row_not_sendsOf (next : Regs K) (rA rB rC rbc : K) (data : ProverData K) :
    rowSends ⟨xorTable⟩
        (Environment.fromArray
          (rawRow (xorRowOf (badImage d₀) (gpow 5) 1 (gpow 0) (gpow 0) (gpow 0) rA rB rC rbc))
          data) ≠
      sendsOf (gpow 5) 1 next rbc (entry (.xor (gpow 0) (gpow 0) (gpow 0)))
        [(1 * gpow 0, rA, (badImage d₀).limbsAt (1 * gpow 0)),
          (1 * gpow 0, rB, (badImage d₀).limbsAt (1 * gpow 0)),
          (1 * gpow 0, rC, (badImage d₀).limbsAt (1 * gpow 0))] := by
  intro h
  rw [rowSends_mk, xor_sends_gen _ _ _ _ (eval_rowVar _ data)] at h
  have hA : (badImage d₀).limbsAt (gpow 0) = #v[0, 1, 0] := by
    rw [MemImage.limbsAt_eq_of_read (read_lit (badImage d₀) 0)]
    rfl
  simp only [xorRowOf, sendsOf, memMsgOf, bcMsgOf, entry, one_mul, List.cons.injEq,
    Prod.mk.injEq, true_and, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append] at h
  have h3 := h.2.2.2.1
  simp only [hA] at h3
  have h4 := congrArg Array.toList h3
  simp only [List.cons.injEq] at h4
  have h5 : (1 : K) + 1 = 1 := h4.2.2.2.1
  rw [CharTwo.add_self_eq_zero] at h5
  exact zero_ne_one h5

/-! ## The `JUMP` witness -/

/-- A taken `JUMP` row: destination `g^9`, frame `g^3`. -/
def takenRow : JumpRow K :=
  ⟨gpow 5, 1, gpow 0, gpow 1, gpow 2, 1, gpow 9, gpow 3, 1, 1, 1, 1⟩

/-- With the honest indicator `b = 1` the pushed successor is the destination and the frame. -/
example (w : K) (data : ProverData K) :
    ((rowSends ⟨jumpTable⟩ (Environment.fromArray (jumpRaw takenRow w 1) data)).filter
      (·.1 = StatePush.name)).map (·.2) = [#[gpow 9, gpow 3]] := by
  rw [jumpRaw_sends]
  simp [takenRow, StatePush, StatePull, BytecodePush, BytecodePull, MemPull, MemPush,
    CharTwo.add_self_eq_zero, add_assoc]

/-- With `b = 0` the same row pushes the fall-through `(g · pc, fp)`. -/
example (w : K) (data : ProverData K) :
    ((rowSends ⟨jumpTable⟩ (Environment.fromArray (jumpRaw takenRow w 0) data)).filter
      (·.1 = StatePush.name)).map (·.2) = [#[g * gpow 5, 1]] := by
  rw [jumpRaw_sends]
  simp [takenRow, StatePush, StatePull, BytecodePush, BytecodePull, MemPull, MemPush]

/-- The two successors differ, so the indicator is what the push depends on. -/
example : (#[gpow 9, gpow 3] : Array K) ≠ #[g * gpow 5, 1] := by
  intro h
  simp at h
  exact absurd h.1 (by decide +kernel)

/-! ## The numbers of the reads -/

/-- A skeleton of an `XOR` of one cell with itself, at the state `(g^5, 1)`. -/
def xorSk : Skel := ⟨gpow 5, 1, .xor (gpow 0) (gpow 0) (gpow 0)⟩

/-- Two rows reading the same cell number its six reads `0 .. 5` in order: the chain runs across
rows. -/
example : (mkRows zeroImage (fun _ ↦ 0) (fun _ ↦ 0) [xorSk, xorSk]).map (·.exps) =
    [[0, 1, 2], [3, 4, 5]] := by
  simp [mkRows, xorSk, readAddrs, readExps, readBump, Function.update_self]

/-- Both rows read the bytecode slot of the same counter: its numbers are `0` and `1`. -/
example : (mkRows zeroImage (fun _ ↦ 0) (fun _ ↦ 0) [xorSk, xorSk]).map (·.bc) = [0, 1] := by
  simp [mkRows, xorSk, readAddrs, readBump, Function.update_self]

end LeanVMTests.Arithmetization.Completeness.Rows
