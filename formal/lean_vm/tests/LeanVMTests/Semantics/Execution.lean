import LeanVM.Semantics.Lemmas
import LeanVM.Semantics.KeccakCells

/-!
# Tests: steps, runs, and valid executions

A plain file: each fixture is a proof that peels `run` one step at a time and decides the
step's relation on literal words in the kernel, which needs `E` arithmetic and `DecidableEq E`
to reduce there; they do from a plain file and not from a `module`.
Nothing here evaluates `addressIndex?`: every fetch and read is `LeanIsaProgram.fetch_gpow` or
`MemoryImage.read_gpow` at a literal index, or one of the failure lemmas.

Fixtures, from leanVM's executor tests: `mul_128bit_word` (`crates/leanvm_core/src/cpu/mod.rs:853-869`
at `leanvm-rev`, the operands the test's and the product as its executor's `F128` arithmetic
computes it, checked against `crates/primitives/src/field/gf2_64x2.rs`'s reference) as a
`ValidExecution`; the first `KECCAK` row of
`keccak_permutes_in_both_layouts` (`cpu/mod.rs:835-868`) on that test's cells, with a mutation;
`halts_in_the_final_state` (`cpu/mod.rs:878-916`): the machine halts in the final state
`(g^(N_prog - 1), 1)`, so a `JUMP` in the last slot, reached in another frame, is a step of a valid
execution, and a `SET_CONSTANT` there leaves no valid execution, whatever the memory. Also a taken
`JUMP`; a `DEREF` in `pc` mode; the rejections of failed reads, a step from the final state, the
last slot reached with a wrong frame pointer, an out-of-range `DEREF` cell, a `JUMP` destination
outside `K`.
-/

namespace LeanVMTests.Semantics.Execution

open LeanVM.Parameters LeanVM.Semantics

/-! ## Helpers: fetch and read at a literal index -/

/-- `LeanIsaProgram.fetch_gpow` at a literal exponent. -/
theorem fetch_lit (prog : LeanIsaProgram) (j : ℕ) (hj : j < 2 ^ prog.logSize := by decide) :
    prog.fetch (addressOfIndex j) = some (prog.instructions ⟨j, hj⟩) :=
  prog.fetch_gpow ⟨j, hj⟩

/-- `LeanIsaProgram.fetch` at the counter `1 = g^0`. -/
theorem fetch_one (prog : LeanIsaProgram) : prog.fetch 1 = some (prog.instructions ⟨0,
    Nat.two_pow_pos _⟩) := by
  simpa using prog.fetch_gpow ⟨0, Nat.two_pow_pos _⟩

/-- `MemoryImage.read_gpow` at a literal exponent. -/
theorem read_lit {κ : ℕ} (L : MemoryImage κ) (j : ℕ) (hκ : κ < 64 := by decide)
    (hj : j < 2 ^ κ := by decide) : L.read (addressOfIndex j) = some (L ⟨j, hj⟩) :=
  MemoryImage.read_gpow hκ L ⟨j, hj⟩

/-- `MemoryImage.read` at the address `1 = g^0`. -/
theorem read_one {κ : ℕ} (L : MemoryImage κ) (hκ : κ < 64 := by decide) :
    L.read 1 = some (L ⟨0, Nat.two_pow_pos _⟩) := by
  simpa using MemoryImage.read_gpow hκ L ⟨0, Nat.two_pow_pos _⟩

/-- `MemoryImage.read` at the address `g = g^1`. -/
theorem read_g {κ : ℕ} (L : MemoryImage κ) (hκ : κ < 64 := by decide)
    (h1 : 1 < 2 ^ κ := by decide) : L.read g = some (L ⟨1, h1⟩) := by
  simpa using MemoryImage.read_gpow hκ L ⟨1, h1⟩

/-- `MemoryImage.read` one past the end of a sixteen-cell memory. -/
theorem read_sixteen (L : MemoryImage 4) : L.read (addressOfIndex 16) = none := by
  rw [MemoryImage.read, gLog?_gpow_eq_none (by decide) (by decide), Option.map_none]

/-- `g · g^i = g^(i+1)`, oriented for `simp`. -/
theorem g_mul_gpow (i : ℕ) : g * addressOfIndex i = addressOfIndex (i + 1) := (gpow_succ i).symm

/-! ## The successor -/

/-- The fall-through successor multiplies by `g`. -/
example : Registers.next ⟨1, 1⟩ = ⟨g, 1⟩ := by simp [Registers.next]

/-- `pc + 1` would not even be injective on a run: `1 + 1 = 0` in `K`. -/
example : (1: K) + 1 = 0 := by decide

/-- Register equality decides in the kernel on a product against a power. -/
example : Registers.next ⟨1, 1⟩ = ⟨addressOfIndex 1, 1⟩ := by decide +kernel

/-! ## `mul_128bit_word` (`cpu/mod.rs:853-869`) -/

-- The operands and product of the executor test `mul_128bit_word`.
def mulX : E := E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfeedfacedeadbeef)
def mulY : E := E.ofLimbs (K.ofBits 0x9999aaaabbbbcccc) (K.ofBits 0x13579bdf2468ace0)
def mulXY : E := E.ofLimbs (K.ofBits 0x1b4ac62c35ac2ecc) (K.ofBits 0x421e3037aaa197d0)

/-- CompPoly's product of the two words is the executor's. -/
example : mulX * mulY = mulXY := by decide +kernel

/-- The bytecode: two `SET_CONSTANT`s, the `MUL_NATIVE`, and the never-executed last slot. -/
def mulProg : LeanIsaProgram :=
  ⟨2, by decide, ![.setConstant (addressOfIndex 2) mulX, .setConstant (addressOfIndex 3) mulY,
    .mulNative (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4), .xor 1 1 1]⟩

/-- The public input `[w(1), w(2)]`. -/
def mulInput : PublicInput := ⟨![1, 0, K.ofBits 2, 0]⟩

/-- The image the executor commits, at the smallest size: the public words, the operands, the
product, and zero elsewhere. -/
def mulImage : MemoryImage minLogMem := fun i ↦
  match (i : ℕ) with
  | 0 => mulInput.word0
  | 1 => mulInput.word1
  | 2 => mulX
  | 3 => mulY
  | 4 => mulXY
  | _ => 0

/-- Three instructions execute before the final state. -/
def mulTrace : Execution mulProg := ⟨minLogMem, mulImage, 3⟩

theorem mul_step0 : step mulProg mulImage ⟨1, 1⟩ = some ⟨addressOfIndex 1, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one mulProg)]
  show execute mulImage ⟨1, 1⟩ (.setConstant (addressOfIndex 2) mulX) = _
  simp only [execute, executeWith, one_mul, read_lit mulImage 2]
  decide +kernel

theorem mul_step1 : step mulProg mulImage ⟨addressOfIndex 1, 1⟩ = some ⟨addressOfIndex 2, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨addressOfIndex 1, 1⟩) (fetch_lit mulProg 1)]
  show execute mulImage ⟨addressOfIndex 1, 1⟩ (.setConstant (addressOfIndex 3) mulY) = _
  simp only [execute, executeWith, one_mul, read_lit mulImage 3]
  decide +kernel

theorem mul_step2 : step mulProg mulImage ⟨addressOfIndex 2, 1⟩ = some ⟨addressOfIndex 3, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨addressOfIndex 2, 1⟩) (fetch_lit mulProg 2)]
  show execute mulImage ⟨addressOfIndex 2, 1⟩ (.mulNative (addressOfIndex 2) (addressOfIndex 3)
      (addressOfIndex 4)) = _
  simp only [execute, executeWith, one_mul, read_lit mulImage 2, read_lit mulImage 3, read_lit mulImage 4]
  decide +kernel

/-- The run: three steps from `(1, 1)`, halting in the final state `(g^3, 1)`. -/
theorem mul_run : run mulProg mulImage 3 Registers.initial = some (Registers.final mulProg) := by
  show run mulProg mulImage 3 ⟨1, 1⟩ = some ⟨addressOfIndex 3, 1⟩
  simp (disch := decide +kernel) only [run_succ_of_ne, mul_step0, mul_step1, mul_step2,
    Option.bind_eq_bind, Option.bind_some, run_zero]

/-- The two public words are in place, whatever the program and the step count. -/
theorem mulImage_boundary {prog : LeanIsaProgram} (steps : ℕ) :
    HoldsPublicInput mulInput (⟨minLogMem, mulImage, steps⟩ : Execution prog) := by
  refine ⟨le_rfl, (by decide : minLogMem ≤ maxLogMem), ?_, ?_⟩
  · show mulImage.read (addressOfIndex 0) = some (mulImage ⟨0, by decide⟩)
    exact read_lit mulImage 0
  · show mulImage.read (addressOfIndex 1) = some (mulImage ⟨1, by decide⟩)
    exact read_lit mulImage 1

/-- `mul_128bit_word` is a valid execution. -/
example : ValidExecution mulProg mulInput mulTrace := ⟨mulImage_boundary 3, mul_run⟩

/-- Its register sequence has four states. -/
example : mulTrace.regs.length = 4 := Execution.regs_length mul_run

/-- A fourth step is refused: the machine halts in the final state. -/
example : run mulProg mulImage 4 Registers.initial = none := by
  rw [show 4 = 3 + 1 by rfl, run_add, mul_run, Option.bind_eq_bind, Option.bind_some]
  exact run_succ_of_eq (r := Registers.final mulProg) rfl 0

/-! ## `N_prog = 1`: the empty execution -/

/-- One slot, the last. -/
def oneProg : LeanIsaProgram := ⟨0, by decide, ![.xor 1 1 1]⟩

/-- Zero steps from `(1, 1)` reach `(g^0, 1)`, so the program has a valid execution... -/
example : ValidExecution oneProg mulInput ⟨minLogMem, mulImage, 0⟩ :=
  ⟨mulImage_boundary 0, by rw [run_zero]; decide +kernel⟩

/-- ...and its one slot is not executed, whatever it holds: the initial state is the final one. -/
example : run oneProg mulImage 1 Registers.initial = none := run_succ_of_eq (by decide +kernel) 0

/-- The same with a `JUMP` in that slot. -/
def oneJumpProg : LeanIsaProgram := ⟨0, by decide, ![.jump 0 0 0]⟩

example : ValidExecution oneJumpProg mulInput ⟨minLogMem, mulImage, 0⟩ :=
  ⟨mulImage_boundary 0, by rw [run_zero]; decide +kernel⟩
example : run oneJumpProg mulImage 1 Registers.initial = none :=
  run_succ_of_eq (by decide +kernel) 0

/-! ## Control flow: `JUMP` and `DEREF` on a sixteen-cell image -/

/-- Sixteen cells. `JUMP` reads `c, d, f` at `2, 3, 4` (all in `K`), or `c = 0` at `12` and
`d = y ∉ K` at `13`; `DEREF` reads the pointer `g^7` at `5`, its local cell at `6`, and the
target `g² · pc` at `7`; the `JUMP` to the last slot reads `g` at `14`. -/
def ctlImage : MemoryImage 4 := fun i ↦
  match (i : ℕ) with
  | 2 => E.ofLimbs 1 0
  | 3 => E.ofLimbs (addressOfIndex 3) 0
  | 4 => E.ofLimbs (addressOfIndex 5) 0
  | 5 => E.ofLimbs (addressOfIndex 7) 0
  | 6 => E.ofLimbs (K.ofBits 9) (K.ofBits 9)
  | 7 => E.ofLimbs (addressOfIndex 2) 0
  | 13 => E.ofLimbs 0 1
  | 14 => E.ofLimbs g 0
  | _ => 0

/-- A two-slot program: the instruction under test, then the last slot. -/
def oneStep (i : LeanIsaInstruction) : LeanIsaProgram := ⟨1, by decide, ![i, .xor 1 1 1]⟩

/-- A taken `JUMP`: `c = 1 ≠ 0`, so the registers become `(d, f) = (g^3, g^5)`. -/
example : step (oneStep (.jump (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4))) ctlImage
    ⟨1, 1⟩ =
    some ⟨addressOfIndex 3, addressOfIndex 5⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.jump (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4)) = _
  simp only [execute, executeWith, one_mul, read_lit ctlImage 2, read_lit ctlImage 3, read_lit ctlImage 4]
  decide +kernel

/-- A `JUMP` not taken: `c = 0`, so it falls through to `(g, 1)`. -/
example : step (oneStep (.jump (addressOfIndex 12) (addressOfIndex 3) (addressOfIndex 4))) ctlImage
    ⟨1, 1⟩ = some ⟨g, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.jump (addressOfIndex 12) (addressOfIndex 3) (addressOfIndex 4)) = _
  simp only [execute, executeWith, one_mul, read_lit ctlImage 12, read_lit ctlImage 3, read_lit ctlImage 4]
  decide +kernel

/-- The same `JUMP` with `d = y ∉ K` is invalid although it is not taken. -/
example : step (oneStep (.jump (addressOfIndex 12) (addressOfIndex 13) (addressOfIndex 4))) ctlImage
    ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.jump (addressOfIndex 12) (addressOfIndex 13) (addressOfIndex
      4)) = _
  simp only [execute, executeWith, one_mul, read_lit ctlImage 12, read_lit ctlImage 13, read_lit ctlImage 4]
  decide +kernel

/-- A taken branch also rejects a destination outside `K`. -/
example : step (oneStep (.jump (addressOfIndex 2) (addressOfIndex 13) (addressOfIndex 4))) ctlImage
    ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.jump (addressOfIndex 2) (addressOfIndex 13) (addressOfIndex 4)) = _
  simp only [execute, executeWith, one_mul, read_lit ctlImage 2, read_lit ctlImage 13, read_lit ctlImage 4]
  decide +kernel

/-- The pointer cell holds the address `g^7`. -/
theorem ctl_pointer : (ctlImage ⟨5, by decide⟩).limb 0 = addressOfIndex 7 := by decide +kernel

/-- A `DEREF` in `pc` mode at `pc = 1`: the pointer `g^7` is in `K`, the local cell is read,
and `mem[g^7 · 1] = g² · 1`. The kernel decides an `E` equality only against a word in
`E.ofLimbs` form, so the `DEREF` source is put in that form first
(`ofK_eq_ofLimbs`). -/
example : step (oneStep (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .pc)) ctlImage ⟨1, 1⟩ = some
    ⟨g, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .pc) = _
  simp only [execute, executeWith, one_mul, mul_one, read_lit ctlImage 5, Option.bind_eq_bind,
    Option.bind_some, ctl_pointer, read_lit ctlImage 6, read_lit ctlImage 7, derefSource,
    ofK_eq_ofLimbs]
  decide +kernel

/-- Change only the target cell so the same pointer and local reads exercise `cell` mode. -/
def derefCellImage : MemoryImage 4 := fun i ↦
  if i.val = 7 then ctlImage ⟨6, by decide⟩ else ctlImage i

theorem derefCell_pointer : (derefCellImage ⟨5, by decide⟩).limb 0 = addressOfIndex 7 :=
  by decide +kernel

/-- `cell` mode copies the local cell value to the pointed-to target. -/
example : step (oneStep (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .cell)) derefCellImage
    ⟨1, 1⟩ =
    some ⟨g, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute derefCellImage ⟨1, 1⟩ (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .cell) = _
  simp only [execute, executeWith, one_mul, mul_one, read_lit derefCellImage 5,
    Option.bind_eq_bind, Option.bind_some, derefCell_pointer, read_lit derefCellImage 6,
    read_lit derefCellImage 7, derefSource]
  decide +kernel

/-- Change the target to the frame pointer embedded in `E`; the local cell is still read. -/
def derefFpImage : MemoryImage 4 := fun i ↦
  if i.val = 7 then E.ofLimbs 1 0 else ctlImage i

theorem derefFp_pointer : (derefFpImage ⟨5, by decide⟩).limb 0 = addressOfIndex 7 :=
  by decide +kernel

/-- `fp` mode stores the current frame pointer at the target. -/
example : step (oneStep (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .fp)) derefFpImage ⟨1, 1⟩ =
    some ⟨g, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute derefFpImage ⟨1, 1⟩ (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .fp) = _
  simp only [execute, executeWith, one_mul, mul_one, read_lit derefFpImage 5,
    Option.bind_eq_bind, Option.bind_some, derefFp_pointer, read_lit derefFpImage 6,
    read_lit derefFpImage 7, derefSource, ofK_eq_ofLimbs]
  decide +kernel

/-- The same image cannot satisfy `cell` mode: its target differs from the local cell. -/
example : step (oneStep (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .cell)) ctlImage ⟨1, 1⟩ =
    none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .cell) = none
  simp only [execute, executeWith, one_mul, mul_one, read_lit ctlImage 5, Option.bind_eq_bind,
    Option.bind_some, ctl_pointer, read_lit ctlImage 6, read_lit ctlImage 7, derefSource]
  decide +kernel

/-- The same target also differs from the frame pointer required by `fp` mode. -/
example : step (oneStep (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .fp)) ctlImage ⟨1, 1⟩ =
    none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .fp) = none
  simp only [execute, executeWith, one_mul, mul_one, read_lit ctlImage 5, Option.bind_eq_bind,
    Option.bind_some, ctl_pointer, read_lit ctlImage 6, read_lit ctlImage 7,
    derefSource, ofK_eq_ofLimbs]
  decide +kernel

/-- Every mode rejects a pointer whose upper limbs are nonzero, before using it as an address. -/
def nonKPointerImage : MemoryImage 4 := fun i ↦
  if i.val = 5 then E.ofLimbs (addressOfIndex 7) 1 else ctlImage i

example : step (oneStep (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .cell)) nonKPointerImage
    ⟨1, 1⟩ =
    none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute nonKPointerImage ⟨1, 1⟩ (.deref (addressOfIndex 5) 1 (addressOfIndex 6) .cell) = none
  simp only [execute, executeWith, one_mul, read_lit nonKPointerImage 5, Option.bind_eq_bind,
    Option.bind_some]
  decide +kernel

/-- The same `DEREF` with its local cell `g^16` out of range is invalid, although `pc` mode
ignores the cell's value. -/
example : step (oneStep (.deref (addressOfIndex 5) 1 (addressOfIndex 16) .pc)) ctlImage ⟨1, 1⟩ =
    none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.deref (addressOfIndex 5) 1 (addressOfIndex 16) .pc) = _
  simp only [execute, executeWith, one_mul, mul_one, read_lit ctlImage 5, Option.bind_eq_bind,
    Option.bind_some, Option.bind_none, read_sixteen]
  decide +kernel

/-! ## Failed reads -/

/-- An operand past the end of memory reads nothing. -/
example : step (oneStep (.xor (addressOfIndex 16) (addressOfIndex 2) (addressOfIndex 3))) ctlImage
    ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.xor (addressOfIndex 16) (addressOfIndex 2) (addressOfIndex 3)) = _
  simp only [execute, executeWith, one_mul, read_sixteen, Option.bind_eq_bind, Option.bind_none]

/-- The operand `0` names no cell. -/
example : step (oneStep (.xor 0 (addressOfIndex 2) (addressOfIndex 3))) ctlImage ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.xor 0 (addressOfIndex 2) (addressOfIndex 3)) = _
  simp only [execute, executeWith, mul_zero, MemoryImage.read_zero, Option.bind_eq_bind, Option.bind_none]

/-- A counter past the bytecode fetches nothing. -/
example : step (oneStep (.xor 1 1 1)) ctlImage ⟨addressOfIndex 2, 1⟩ = none :=
  step_eq_none_of_fetch_eq_none (by
    show (oneStep (.xor 1 1 1)).fetch (addressOfIndex 2) = none
    rw [LeanIsaProgram.fetch, gLog?_gpow_eq_none (by decide) (by decide), Option.map_none])

/-! ## The final frame pointer -/

/-- A `JUMP` to the last slot `g` with `fp ← g`. -/
def haltProg : LeanIsaProgram := oneStep (.jump (addressOfIndex 2) (addressOfIndex 14)
    (addressOfIndex 14))

theorem halt_step : step haltProg ctlImage Registers.initial = some ⟨g, g⟩ := by
  rw [step_of_fetch_eq_some (r := Registers.initial) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.jump (addressOfIndex 2) (addressOfIndex 14) (addressOfIndex
      14)) = _
  simp only [execute, executeWith, one_mul, read_lit ctlImage 2, read_lit ctlImage 14]
  decide +kernel

/-- The last slot in the frame `g` is not the final state `(g, 1)`. -/
theorem halt_ne_final : (⟨g, g⟩ : Registers K) ≠ Registers.final haltProg := by decide +kernel

/-- There the `XOR` executes (cell `g`, the word `0`, is `0 + 0`) and falls through to `g^2`. -/
theorem halt_last : step haltProg ctlImage ⟨g, g⟩ = some ⟨addressOfIndex 2, g⟩ := by
  have hf := haltProg.fetch_gpow ⟨1, by decide⟩
  simp only [addressOfIndex, pow_one] at hf
  rw [step_of_fetch_eq_some (r := ⟨g, g⟩) hf]
  show execute ctlImage ⟨g, g⟩ (.xor 1 1 1) = _
  simp only [execute, executeWith, mul_one, read_g ctlImage]
  decide +kernel

/-- `g^2` is no slot of a two-slot program: the run fails there. -/
theorem halt_past : step haltProg ctlImage ⟨addressOfIndex 2, g⟩ = none :=
  step_eq_none_of_fetch_eq_none (by
    show haltProg.fetch (addressOfIndex 2) = none
    rw [LeanIsaProgram.fetch, gLog?_gpow_eq_none (by decide) (by decide), Option.map_none])

/-- The run reaches the last slot after one step with `fp = g`, which is not the final state;
it steps on to `(g^2, g)` and fails there, so no number of steps reaches `(g, 1)`: no trace over
this image is a valid execution. -/
example : ∀ n, run haltProg ctlImage n Registers.initial ≠ some (Registers.final haltProg) := by
  intro n
  match n with
  | 0 => rw [run_zero]; decide +kernel
  | 1 =>
    rw [run_succ_of_ne (prog := haltProg) (r := Registers.initial) (by decide +kernel) 0, halt_step]
    decide +kernel
  | 2 =>
    rw [show (2 : ℕ) = 1 + 1 from rfl, run_succ_of_ne (prog := haltProg) (r := Registers.initial) (by decide +kernel) 1, halt_step,
      Option.bind_eq_bind, Option.bind_some, run_succ_of_ne_final halt_ne_final 0, halt_last,
      Option.bind_eq_bind, Option.bind_some, run_zero]
    decide +kernel
  | n + 3 =>
    rw [show n + 3 = n + 2 + 1 from rfl, run_succ_of_ne (prog := haltProg) (r := Registers.initial) (by decide +kernel) (n + 2),
      halt_step, Option.bind_eq_bind, Option.bind_some, run_succ_of_ne_final halt_ne_final (n + 1),
      halt_last, Option.bind_eq_bind, Option.bind_some,
      run_succ_of_ne (prog := haltProg) (r := ⟨addressOfIndex 2, g⟩)
          (by decide +kernel) n, halt_past]
    exact fun h ↦ Option.some_ne_none _ h.symm

/-! ## `KECCAK` (`keccak_permutes_in_both_layouts`, `cpu/mod.rs:835-868`) -/

-- The input cells of the executor test `keccak_permutes_in_both_layouts` at leanVM `990b9352`:
-- the words `a, b` (each read twice through the aliased `m` pairs), the padding's first byte in
-- the tail, its last bit in `b8` (whose free high limb `0x5555` is ignored), and a zero capacity.
def kA : E := E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfedcba9876543210)
def kB : E := E.ofLimbs (K.ofBits 0xdeadbeefcafebabe) (K.ofBits 0x0badf00d0badf00d)
def kPad : E := E.ofLimbs (K.ofBits 0x01) 0
def kEnd : E := E.ofLimbs (K.ofBits 0x8000000000000000) (K.ofBits 0x5555)

/-- The thirteen output cells in the odd layout, `permute_cells(input, false, true)` as the
pinned verifier's `keccak_f` and `keccak_cell_lanes` compute it
(`crates/verifier/src/hash.rs:50-69`, `layout.rs:299-309`, computed outside Lean; their first four
lanes are the Keccak-256 digest
`456db617edafbf8d35b9f83bbe63fd305a2a1a857a7d16775e00d9e0374917d9` of the 64 message bytes, the
test's own check). -/
def kOut : Fin 13 → E := fun c ↦
  match (c : ℕ) with
  | 0 => E.ofLimbs (K.ofBits 0x0) (K.ofBits 0x8dbfafed17b66d45)
  | 1 => E.ofLimbs (K.ofBits 0x30fd63be3bf8b935) (K.ofBits 0x77167d7a851a2a5a)
  | 2 => E.ofLimbs (K.ofBits 0xd9174937e0d9005e) (K.ofBits 0xa6a08643e0752e62)
  | 3 => E.ofLimbs (K.ofBits 0x96fa9d5eb49e3867) (K.ofBits 0xd3075d1a22781d5)
  | 4 => E.ofLimbs (K.ofBits 0x81ae728bf7328686) (K.ofBits 0xf51da81b6f1b6499)
  | 5 => E.ofLimbs (K.ofBits 0xdaf2a8af5b43dbf9) (K.ofBits 0xdbf85b3cc1312641)
  | 6 => E.ofLimbs (K.ofBits 0x993d35c56291827e) (K.ofBits 0x47fd59ac60e225e2)
  | 7 => E.ofLimbs (K.ofBits 0x36607d1d9e6abed) (K.ofBits 0x6cee5561314ca0f3)
  | 8 => E.ofLimbs (K.ofBits 0x3e20ee955c09012e) (K.ofBits 0x8a928dc9e22c3dcf)
  | 9 => E.ofLimbs (K.ofBits 0x7f24a1dac6837929) (K.ofBits 0xd22b33eacce5fcd2)
  | 10 => E.ofLimbs (K.ofBits 0x2b1e71fdcd52b881) (K.ofBits 0x427618061608ac91)
  | 11 => E.ofLimbs (K.ofBits 0x44c480aa40bfdbf9) (K.ofBits 0x7a29ee993739ddb0)
  | 12 => E.ofLimbs (K.ofBits 0xf7f9aa87f90247d1) (K.ofBits 0xe5177d767bf6bd92)
  | _ => 0

/-- The executor's cells: the public input at `0, 1`, `a, b` at `2, 3`, the tail at `4..7`, `b8` at
`8`, the capacity at `9..12`, and the output at `13..25`; `out` is the output cell `0`, mutated
below. -/
def keccakImage (out0 : E) : MemoryImage 5 := fun i ↦
  match (i : ℕ) with
  | 0 => ofK 7
  | 1 => ofK 11
  | 2 => kA
  | 3 => kB
  | 4 => kPad
  | 8 => kEnd
  | 13 => out0
  | n + 14 => if h : n < 12 then kOut ⟨n + 1, by omega⟩ else 0
  | _ => 0

/-- The executor's first `KECCAK` row: `m: [2, 3, 2, 3], tail: 4, b8: 8, cap: 9, out: 13`, even
input layout, odd output layout, all thirteen output cells written. -/
def keccakIns : LeanIsaInstruction := .keccak ![addressOfIndex 2, addressOfIndex 3, addressOfIndex
    2, addressOfIndex 3] (addressOfIndex 4) (addressOfIndex 8) (addressOfIndex 9)
  (addressOfIndex 13) false true .all

/-- The cells the row reads. -/
def kIn : Fin 13 → E := ![kA, kB, kA, kB, kPad, 0, 0, 0, kEnd, 0, 0, 0, 0]

/-- The memory index of read cell `c`: the aliased pairs, the tail, `b8`, the capacity. -/
def kInIdx : Fin 13 → ℕ := ![2, 3, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

theorem keccakInOffset_eq : ∀ c : Fin 13,
    1 * keccakInputCellOffset ![addressOfIndex 2, addressOfIndex 3, addressOfIndex 2, addressOfIndex
        3] (addressOfIndex 4) (addressOfIndex 8) (addressOfIndex 9) c =
      addressOfIndex (kInIdx c) := by
  decide +kernel

theorem keccakOutOffset_eq : ∀ c : Fin 13, 1 * (g ^ c.val * addressOfIndex 13) = addressOfIndex
    (c.val + 13) := by
  decide +kernel

/-- The row's reads, on the image with output cell `0` set to `out0`. -/
theorem keccak_reads (out0 : E) :
    execute (keccakImage out0) ⟨1, 1⟩ keccakIns =
      (do guard (KeccakCellsRelation kIn false (Function.update kOut 0 out0) true
            KeccakOutputCells.all);
          pure ⟨g, 1⟩) := by
  have hin : readCells (keccakImage out0).read 1 (keccakInputCellOffset ![addressOfIndex 2,
      addressOfIndex 3, addressOfIndex 2, addressOfIndex 3]
      (addressOfIndex 4) (addressOfIndex 8) (addressOfIndex 9)) = some kIn := by
    refine (readCells_eq_some_iff _ _ _ _).mpr fun c ↦ ?_
    rw [keccakInOffset_eq c]
    fin_cases c <;> exact (read_lit (keccakImage out0) _ (by decide) (by decide)).trans rfl
  have hout : readFirstCells (keccakImage out0).read 1 (fun c ↦ g ^ c.val * addressOfIndex 13) 13 =
      some (Function.update kOut 0 out0) := by
    refine (readFirstCells_eq_some_iff _ _ _ _ _).mpr ⟨fun c _ ↦ ?_, fun c hc ↦ absurd c.isLt (by omega)⟩
    rw [keccakOutOffset_eq c]
    fin_cases c <;> exact (read_lit (keccakImage out0) _ (by decide) (by decide)).trans rfl
  simp only [keccakIns, execute, executeWith, KeccakOutputCells.cellCount, hin, hout,
    Option.bind_eq_bind, Option.bind_some, Registers.next, mul_one]

/-- The row steps: the cells are a Keccak-f[1600] permutation, even layout in, odd layout out. -/
example : step (oneStep keccakIns) (keccakImage (kOut 0)) ⟨1, 1⟩ = some ⟨g, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute (keccakImage (kOut 0)) ⟨1, 1⟩ keccakIns = _
  rw [keccak_reads]
  decide +kernel

/-- Mutation: output cell `0` holds lane `0` in its high limb (odd layout); with a nonzero low
limb, which holds no lane and must be written zero, the row is invalid. -/
example : step (oneStep keccakIns) (keccakImage (kOut 0 + ofK 1)) ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute (keccakImage _) ⟨1, 1⟩ keccakIns = _
  rw [keccak_reads]
  decide +kernel

/-- The same row writing only output cell `0` (`out_cells = One`, leanVM main `40f877dc`,
`keccak_writes_only_requested_cells`, `cpu/mod.rs`): it reads cell `13` alone of the output. -/
def keccakIns1 : LeanIsaInstruction := .keccak ![addressOfIndex 2, addressOfIndex 3, addressOfIndex
    2, addressOfIndex 3] (addressOfIndex 4) (addressOfIndex 8) (addressOfIndex 9)
  (addressOfIndex 13) false true .one

/-- The image of the one-cell row: output cell `0` at `13`, then anything at `14..25`, here `w`. -/
def keccakImage1 (out0 w : E) : MemoryImage 5 := fun i ↦
  match (i : ℕ) with
  | 0 => ofK 7
  | 1 => ofK 11
  | 2 => kA
  | 3 => kB
  | 4 => kPad
  | 8 => kEnd
  | 13 => out0
  | _ + 14 => w
  | _ => 0

/-- The one-cell row's reads: the input cells, and output cell `0` only. -/
theorem keccak_reads_one (out0 w : E) :
    execute (keccakImage1 out0 w) ⟨1, 1⟩ keccakIns1 =
      (do guard (KeccakCellsRelation kIn false (fun c ↦ if c.val < 1 then out0 else 0) true
            KeccakOutputCells.one);
          pure ⟨g, 1⟩) := by
  have hin : readCells (keccakImage1 out0 w).read 1 (keccakInputCellOffset ![addressOfIndex 2,
      addressOfIndex 3, addressOfIndex 2, addressOfIndex 3]
      (addressOfIndex 4) (addressOfIndex 8) (addressOfIndex 9)) = some kIn := by
    refine (readCells_eq_some_iff _ _ _ _).mpr fun c ↦ ?_
    rw [keccakInOffset_eq c]
    fin_cases c <;> exact (read_lit (keccakImage1 out0 w) _ (by decide) (by decide)).trans rfl
  have hout : readFirstCells (keccakImage1 out0 w).read 1 (fun c ↦ g ^ c.val * addressOfIndex 13)
      1 = some (fun c ↦ if c.val < 1 then out0 else 0) := by
    refine (readFirstCells_eq_some_iff _ _ _ _ _).mpr ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
    · obtain rfl : c = 0 := Fin.ext (by omega)
      rw [keccakOutOffset_eq 0]
      exact (read_lit (keccakImage1 out0 w) _ (by decide) (by decide)).trans rfl
    · split_ifs <;> first | omega | rfl
  simp only [keccakIns1, execute, executeWith, KeccakOutputCells.cellCount, hin, hout,
    Option.bind_eq_bind, Option.bind_some, Registers.next, mul_one]

/-- The one-cell row steps whatever the cells past output cell `0` hold: it does not write them. -/
example (w : E) : step (oneStep keccakIns1) (keccakImage1 (kOut 0) w) ⟨1, 1⟩ = some ⟨g, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute (keccakImage1 (kOut 0) w) ⟨1, 1⟩ keccakIns1 = _
  rw [keccak_reads_one]
  decide +kernel

/-- … but not with a wrong output cell `0`, the one it writes. -/
example (w : E) : step (oneStep keccakIns1) (keccakImage1 (kOut 0 + ofK 1) w) ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute (keccakImage1 _ w) ⟨1, 1⟩ keccakIns1 = _
  rw [keccak_reads_one]
  decide +kernel

/-! ## `halts_in_the_final_state` (`cpu/mod.rs:878-916`)

The machine halts in the final state `(g^7, 1)`, not at the last slot: leanVM's eight-slot program
sets cell `2` to `1`, cell `3` to `g^7` and cell `4` to `g`, jumps to `(g^7, g)`, the last slot in
the frame `g`, and executes the instruction there like any other. With a `JUMP` there (reading
cells `2`, `3`, `2` in that frame) it lands in the final state: a valid execution of five steps,
three `SET_CONSTANT`s and two `JUMP`s (leanVM's row counts), which leanVM proves and its verifier
accepts. With a
`SET_CONSTANT` there it falls through to `g^8`, no slot: no valid execution, whatever the
memory. -/

/-- The words `1`, `g^7` (the last slot's counter) and `g` (a frame pointer other than
`main`'s). -/
def wOne : E := E.ofLimbs 1 0
def wLast : E := E.ofLimbs (addressOfIndex 7) 0
def wFp : E := E.ofLimbs g 0

/-- leanVM's program with `last` in its last slot. -/
def finalProg (last : LeanIsaInstruction) : LeanIsaProgram :=
  ⟨3, by decide, ![.setConstant (addressOfIndex 2) wOne, .setConstant (addressOfIndex 3) wLast,
    .setConstant (addressOfIndex 4) wFp, .jump (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex
        4), .xor 1 1 1, .xor 1 1 1,
    .xor 1 1 1, last]⟩

/-- The last slot a `JUMP`: in the frame `g` it reads cells `2`, `3`, `2`. -/
abbrev jumpLast : LeanIsaProgram := finalProg (.jump (addressOfIndex 1) (addressOfIndex 2)
    (addressOfIndex 1))

/-- The last slot a `SET_CONSTANT` of cell `5` of its frame. -/
abbrev setLast : LeanIsaProgram := finalProg (.setConstant (addressOfIndex 5) wOne)

/-- The public input `[w(7), w(11)]`. -/
def finalInput : PublicInput := ⟨![K.ofBits 7, 0, K.ofBits 11, 0]⟩

/-- The memory leanVM's executor writes: the public words and the three cells set. -/
def finalImage : MemoryImage minLogMem := fun i ↦
  match (i : ℕ) with
  | 0 => finalInput.word0
  | 1 => finalInput.word1
  | 2 => wOne
  | 3 => wLast
  | 4 => wFp
  | _ => 0

theorem final_step0 (last : LeanIsaInstruction) :
    step (finalProg last) finalImage Registers.initial = some ⟨addressOfIndex 1, 1⟩ := by
  rw [step_of_fetch_eq_some (r := Registers.initial) (fetch_one _)]
  show execute finalImage ⟨1, 1⟩ (.setConstant (addressOfIndex 2) wOne) = _
  simp only [execute, executeWith, one_mul, read_lit finalImage 2]
  decide +kernel

theorem final_step1 (last : LeanIsaInstruction) :
    step (finalProg last) finalImage ⟨addressOfIndex 1, 1⟩ = some ⟨addressOfIndex 2, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨addressOfIndex 1, 1⟩) (fetch_lit (finalProg last) 1 (show _ < 2 ^ 3 by decide))]
  show execute finalImage ⟨addressOfIndex 1, 1⟩ (.setConstant (addressOfIndex 3) wLast) = _
  simp only [execute, executeWith, one_mul, read_lit finalImage 3]
  decide +kernel

theorem final_step2 (last : LeanIsaInstruction) :
    step (finalProg last) finalImage ⟨addressOfIndex 2, 1⟩ = some ⟨addressOfIndex 3, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨addressOfIndex 2, 1⟩) (fetch_lit (finalProg last) 2 (show _ < 2 ^ 3 by decide))]
  show execute finalImage ⟨addressOfIndex 2, 1⟩ (.setConstant (addressOfIndex 4) wFp) = _
  simp only [execute, executeWith, one_mul, read_lit finalImage 4]
  decide +kernel

/-- The `JUMP` to the last slot in the frame `g`. -/
theorem final_step3 (last : LeanIsaInstruction) :
    step (finalProg last) finalImage ⟨addressOfIndex 3, 1⟩ = some ⟨addressOfIndex 7, g⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨addressOfIndex 3, 1⟩) (fetch_lit (finalProg last) 3 (show _ < 2 ^ 3 by decide))]
  show execute finalImage ⟨addressOfIndex 3, 1⟩ (.jump (addressOfIndex 2) (addressOfIndex 3)
      (addressOfIndex 4)) = _
  simp only [execute, executeWith, one_mul, read_lit finalImage 2, read_lit finalImage 3,
    read_lit finalImage 4]
  decide +kernel

/-- The `JUMP` in the last slot, in the frame `g`, lands in the final state. -/
theorem jumpLast_step4 : step jumpLast finalImage ⟨addressOfIndex 7, g⟩ = some (Registers.final jumpLast) := by
  rw [step_of_fetch_eq_some (r := ⟨addressOfIndex 7, g⟩) (fetch_lit jumpLast 7)]
  show execute finalImage ⟨addressOfIndex 7, g⟩ (.jump (addressOfIndex 1) (addressOfIndex 2)
      (addressOfIndex 1)) = some ⟨addressOfIndex 7, 1⟩
  simp only [execute, executeWith, g_mul_gpow, read_lit finalImage 2, read_lit finalImage 3]
  decide +kernel

/-- The final state of the program is `(g^7, 1)`. -/
theorem final_eq (last : LeanIsaInstruction) : Registers.final (finalProg last) = ⟨addressOfIndex 7,
    1⟩ := rfl

/-- The last slot in the frame `g` is not the final state. -/
theorem lastInG_ne_final (last : LeanIsaInstruction) : (⟨addressOfIndex 7, g⟩ : Registers K) ≠ Registers.final (finalProg last) := by
  rw [final_eq]
  decide +kernel

/-- Nor is the initial state. -/
theorem initial_ne_final (last : LeanIsaInstruction) : Registers.initial ≠ Registers.final
    (finalProg last) := by
  rw [final_eq]
  decide +kernel

/-- Nor is any state of `main`'s frame before the last slot. -/
theorem main_ne_final (last : LeanIsaInstruction) (j : ℕ) (hj : j < 7) :
    (⟨addressOfIndex j, 1⟩ : Registers K) ≠ Registers.final (finalProg last) := by
  rw [final_eq]
  interval_cases j <;> decide +kernel

/-- **The run halts in the final state after five steps**, the last slot's `JUMP` among them. -/
theorem jumpLast_run : run jumpLast finalImage 5 Registers.initial = some (Registers.final jumpLast) := by
  simp (disch := decide +kernel) only [run_succ_of_ne, final_step0, final_step1, final_step2,
    final_step3, Option.bind_eq_bind, Option.bind_some]
  rw [run_succ_of_ne_final (lastInG_ne_final (.jump (addressOfIndex 1) (addressOfIndex 2) (addressOfIndex 1))), jumpLast_step4, Option.bind_eq_bind,
    Option.bind_some, run_zero]

/-- **`halts_in_the_final_state` is a valid execution.** -/
theorem jumpLast_valid : ValidExecution jumpLast finalInput ⟨minLogMem, finalImage, 5⟩ := by
  refine ⟨⟨le_rfl, (by decide : minLogMem ≤ maxLogMem), ?_, ?_⟩, jumpLast_run⟩
  · show finalImage.read (addressOfIndex 0) = some (finalImage ⟨0, by decide⟩)
    exact read_lit finalImage 0
  · show finalImage.read (addressOfIndex 1) = some (finalImage ⟨1, by decide⟩)
    exact read_lit finalImage 1

/-! The `SET_CONSTANT` in the last slot: no valid execution, whatever the memory. -/

/-- A step through a `SET_CONSTANT` that succeeds falls through, and the cell holds the
constant. -/
theorem set_step {κ : ℕ} {L : MemoryImage κ} {r r' : Registers K} {o : K} {k : E}
    (h : execute L r (.setConstant o k) = some r') : L.read (r.fp * o) = some k ∧ r' = r.next := by
  simp only [execute, executeWith, Option.bind_eq_bind] at h
  cases hv : L.read (r.fp * o) with
  | none => rw [hv] at h; cases h
  | some v =>
    rw [hv] at h
    by_cases hk : v = k
    · subst hk
      refine ⟨rfl, ?_⟩
      simpa [guard, eq_comm] using h
    · simp [guard, hk] at h

/-- From the last slot in the frame `g`, the `SET_CONSTANT` falls through to `g^8`, no slot: no
number of steps reaches the final state, whatever the memory. -/
theorem setLast_from_last {κ : ℕ} (L : MemoryImage κ) :
    ∀ n, run setLast L n ⟨addressOfIndex 7, g⟩ ≠ some (Registers.final setLast)
  | 0 => by
    rw [run_zero]
    exact fun h ↦ lastInG_ne_final (.setConstant (addressOfIndex 5) wOne) (Option.some.inj h)
  | n + 1 => by
    intro h
    rw [run_succ_of_ne_final (lastInG_ne_final (.setConstant (addressOfIndex 5) wOne)),
      step_of_fetch_eq_some (r := ⟨addressOfIndex 7, g⟩) (fetch_lit setLast 7)] at h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨-, rfl⟩ := set_step (r := ⟨addressOfIndex 7, g⟩) hr
    have h8 : Registers.next ⟨addressOfIndex 7, g⟩ = ⟨addressOfIndex 8, g⟩ := by decide +kernel
    rw [h8] at h
    cases n with
    | zero =>
      rw [run_zero] at h
      exact absurd (Option.some.inj h) (by rw [final_eq]; decide +kernel)
    | succ n =>
      rw [run_succ_of_ne (prog := setLast) (r := ⟨addressOfIndex 8, g⟩)
          (by show addressOfIndex 8 ≠ addressOfIndex 7; decide +kernel),
        step_eq_none_of_fetch_eq_none (by
          show setLast.fetch (addressOfIndex 8) = none
          rw [LeanIsaProgram.fetch, gLog?_gpow_eq_none
              (by decide) (by decide), Option.map_none])] at h
      cases h

/-- **With a `SET_CONSTANT` in the last slot there is no valid execution**, on any memory: the
first three steps fix cells `2`, `3`, `4`, the `JUMP` then goes to the last slot in the frame `g`,
and from there no run reaches the final state; no state before it is the final state. -/
theorem setLast_no_run {κ : ℕ} (L : MemoryImage κ) (n : ℕ) :
    run setLast L n Registers.initial ≠ some (Registers.final setLast) := by
  intro h
  have hne := main_ne_final (.setConstant (addressOfIndex 5) wOne)
  -- step 0
  rcases n with _ | n
  · exact initial_ne_final _ (Option.some.inj h)
  rw [run_succ_of_ne_final (initial_ne_final (.setConstant (addressOfIndex 5) wOne)),
    step_of_fetch_eq_some (r := Registers.initial) (fetch_one setLast)] at h
  obtain ⟨r1, he, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h2, rfl⟩ := set_step (r := Registers.initial) he
  have e1 : Registers.next Registers.initial = ⟨addressOfIndex 1, 1⟩ := by decide +kernel
  rw [e1] at h
  -- step 1
  rcases n with _ | n
  · exact hne 1 (by decide) (Option.some.inj h)
  rw [run_succ_of_ne_final (hne 1 (by decide)),
    step_of_fetch_eq_some (r := ⟨addressOfIndex 1, 1⟩) (fetch_lit setLast 1)] at h
  obtain ⟨r2, he, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h3, rfl⟩ := set_step (r := ⟨addressOfIndex 1, 1⟩) he
  have e2 : Registers.next ⟨addressOfIndex 1, 1⟩ = ⟨addressOfIndex 2, 1⟩ := by decide +kernel
  rw [e2] at h
  -- step 2
  rcases n with _ | n
  · exact hne 2 (by decide) (Option.some.inj h)
  rw [run_succ_of_ne_final (hne 2 (by decide)),
    step_of_fetch_eq_some (r := ⟨addressOfIndex 2, 1⟩) (fetch_lit setLast 2)] at h
  obtain ⟨r3, he, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h4, rfl⟩ := set_step (r := ⟨addressOfIndex 2, 1⟩) he
  have e3 : Registers.next ⟨addressOfIndex 2, 1⟩ = ⟨addressOfIndex 3, 1⟩ := by decide +kernel
  rw [e3] at h
  -- step 3, the `JUMP`, on the cells the `SET_CONSTANT`s fixed
  rcases n with _ | n
  · exact hne 3 (by decide) (Option.some.inj h)
  rw [run_succ_of_ne_final (hne 3 (by decide)),
    step_of_fetch_eq_some (r := ⟨addressOfIndex 3, 1⟩) (fetch_lit setLast 3)] at h
  obtain ⟨r4, he, h⟩ := Option.bind_eq_some_iff.mp h
  have hj : execute L ⟨addressOfIndex 3, 1⟩ (.jump (addressOfIndex 2) (addressOfIndex 3)
      (addressOfIndex 4)) = some ⟨addressOfIndex 7, g⟩ := by
    simp only [Registers.initial, one_mul] at h2 h3 h4
    simp only [execute, executeWith, one_mul, h2, h3, h4]
    decide +kernel
  change execute L ⟨addressOfIndex 3, 1⟩ (.jump (addressOfIndex 2) (addressOfIndex 3)
      (addressOfIndex 4)) = some r4 at he
  rw [hj] at he
  obtain rfl := Option.some.inj he
  exact setLast_from_last L n h

end LeanVMTests.Semantics.Execution
