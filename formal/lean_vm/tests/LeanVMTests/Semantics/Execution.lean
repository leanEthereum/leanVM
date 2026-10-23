import LeanVM.Semantics.Lemmas

/-!
# Tests: steps, runs, and valid executions

A plain file: each fixture is a proof that peels `run` one step at a time and decides the
step's relation on literal words in the kernel, which needs `E` arithmetic and `DecidableEq E`
to reduce there; they do from a plain file and not from a `module`.
Nothing here evaluates `gLog?`: every fetch and read is `Program.fetch_gpow` or
`MemImage.read_gpow` at a literal index, or one of the failure lemmas.

Fixtures: the executor test `mul_192bit_word` (`crates/leanvm_core/src/cpu/mod.rs:887-904` at
the pin, operands and product as the test computes them with the executor's `F192` arithmetic at
`a386121f`, the test unchanged since but for unwrapping the now fallible `execute`) as a
`ValidExecution`; the `BLAKE2S` row of `blake2s_computes_the_compression` (`cpu/mod.rs:774-836`)
on that test's cells at `a386121f`; a taken `JUMP`; a `DEREF` in `pc` mode; the rejections of
failed reads, a step past the sentinel, a wrong final frame pointer, an out-of-range `DEREF`
cell, a `JUMP` destination outside `K` and a non-canonical cell; and a `JUMP` sentinel, whose two
rows are steps that chain to the final registers while `run` never reaches them.
-/

namespace LeanVMTests.Semantics.Execution

open LeanVM.Parameters LeanVM.Semantics

/-! ## Helpers: fetch and read at a literal index -/

/-- `Program.fetch_gpow` at a literal exponent. -/
theorem fetch_lit (prog : Program) (j : ℕ) (hj : j < 2 ^ prog.logSize := by decide) :
    prog.fetch (gpow j) = some (prog.code ⟨j, hj⟩) :=
  prog.fetch_gpow ⟨j, hj⟩

/-- `Program.fetch` at the counter `1 = g^0`. -/
theorem fetch_one (prog : Program) : prog.fetch 1 = some (prog.code ⟨0, Nat.two_pow_pos _⟩) := by
  simpa using prog.fetch_gpow ⟨0, Nat.two_pow_pos _⟩

/-- `MemImage.read_gpow` at a literal exponent. -/
theorem read_lit {κ : ℕ} (L : MemImage κ) (j : ℕ) (hκ : κ < 64 := by decide)
    (hj : j < 2 ^ κ := by decide) : L.read (gpow j) = some (L ⟨j, hj⟩) :=
  MemImage.read_gpow hκ L ⟨j, hj⟩

/-- `MemImage.read` at the address `1 = g^0`. -/
theorem read_one {κ : ℕ} (L : MemImage κ) (hκ : κ < 64 := by decide) :
    L.read 1 = some (L ⟨0, Nat.two_pow_pos _⟩) := by
  simpa using MemImage.read_gpow hκ L ⟨0, Nat.two_pow_pos _⟩

/-- `MemImage.read` at the address `g = g^1`. -/
theorem read_g {κ : ℕ} (L : MemImage κ) (hκ : κ < 64 := by decide)
    (h1 : 1 < 2 ^ κ := by decide) : L.read g = some (L ⟨1, h1⟩) := by
  simpa using MemImage.read_gpow hκ L ⟨1, h1⟩

/-- `MemImage.read` one past the end of a sixteen-cell memory. -/
theorem read_sixteen (L : MemImage 4) : L.read (gpow 16) = none := by
  rw [MemImage.read, gLog?_gpow_eq_none (by decide) (by decide), Option.map_none]

/-- `g · g^i = g^(i+1)`, oriented for `simp`. -/
theorem g_mul_gpow (i : ℕ) : g * gpow i = gpow (i + 1) := (gpow_succ i).symm

/-! ## The successor -/

/-- The fall-through successor multiplies by `g`. -/
example : Regs.next ⟨1, 1⟩ = ⟨g, 1⟩ := rfl

/-- `pc + 1` would not even be injective on a run: `1 + 1 = 0` in `K`. -/
example : (1: K) + 1 = 0 := by decide

/-- Register equality decides in the kernel on a product against a power. -/
example : Regs.next ⟨1, 1⟩ = ⟨gpow 1, 1⟩ := by decide +kernel

/-! ## `mul_192bit_word` (`cpu/mod.rs:887-904`) -/

-- The operands and product of the executor test `mul_192bit_word` at leanVM a386121f.
def mulX : E :=
  E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfeedfacedeadbeef) (K.ofBits 0x1111222233334444)
def mulY : E :=
  E.ofLimbs (K.ofBits 0x9999aaaabbbbcccc) (K.ofBits 0x13579bdf2468ace0) (K.ofBits 0x5555666677778888)
def mulXY : E :=
  E.ofLimbs (K.ofBits 0xf4bccd9a2e8e525b) (K.ofBits 0xf85ebb9433986f2f) (K.ofBits 0x918137982bf175ac)

/-- CompPoly's product of the two words is the executor's. -/
example : mulX * mulY = mulXY := by decide +kernel

/-- The bytecode: two `SET_CONSTANT`s, the `MUL_NATIVE`, and the never-executed sentinel. -/
def mulProg : Program :=
  ⟨2, by decide, ![.setConstant (gpow 2) mulX, .setConstant (gpow 3) mulY,
    .mulNative (gpow 2) (gpow 3) (gpow 4), .xor 1 1 1]⟩

/-- The public input `[w(1), w(2)]`. -/
def mulInput : PublicInput := ⟨![1, 0, K.ofBits 2, 0]⟩

/-- The image the executor commits, at the smallest size: the public words, the operands, the
product, and zero elsewhere. -/
def mulImage : MemImage minLogMem := fun i ↦
  match (i : ℕ) with
  | 0 => mulInput.word0
  | 1 => mulInput.word1
  | 2 => mulX
  | 3 => mulY
  | 4 => mulXY
  | _ => 0

/-- Three instructions execute before the sentinel. -/
def mulTrace : Trace mulProg := ⟨minLogMem, mulImage, 3⟩

theorem mul_step0 : step mulProg mulImage ⟨1, 1⟩ = some ⟨gpow 1, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one mulProg)]
  show execute mulImage ⟨1, 1⟩ (.setConstant (gpow 2) mulX) = _
  simp only [execute, executeWith, one_mul, read_lit mulImage 2]
  decide +kernel

theorem mul_step1 : step mulProg mulImage ⟨gpow 1, 1⟩ = some ⟨gpow 2, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 1, 1⟩) (fetch_lit mulProg 1)]
  show execute mulImage ⟨gpow 1, 1⟩ (.setConstant (gpow 3) mulY) = _
  simp only [execute, executeWith, one_mul, read_lit mulImage 3]
  decide +kernel

theorem mul_step2 : step mulProg mulImage ⟨gpow 2, 1⟩ = some ⟨gpow 3, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 2, 1⟩) (fetch_lit mulProg 2)]
  show execute mulImage ⟨gpow 2, 1⟩ (.mulNative (gpow 2) (gpow 3) (gpow 4)) = _
  simp only [execute, executeWith, one_mul, read_lit mulImage 2, read_lit mulImage 3, read_lit mulImage 4]
  decide +kernel

/-- The run: three steps from `(1, 1)`, halting at the sentinel `(g^3, 1)`. -/
theorem mul_run : run mulProg mulImage 3 Regs.initial = some (Regs.final mulProg) := by
  show run mulProg mulImage 3 ⟨1, 1⟩ = some ⟨gpow 3, 1⟩
  simp (disch := decide +kernel) only [run_succ_of_ne, mul_step0, mul_step1, mul_step2,
    Option.bind_eq_bind, Option.bind_some, run_zero]

/-- The two public words are in place, whatever the program and the step count. -/
theorem mulImage_boundary {prog : Program} (steps : ℕ) :
    HasPublicBoundary mulInput (⟨minLogMem, mulImage, steps⟩ : Trace prog) := by
  refine ⟨le_rfl, (by decide : minLogMem ≤ maxLogMem), ?_, ?_⟩
  · show mulImage.read (gpow 0) = some (mulImage ⟨0, by decide⟩)
    exact read_lit mulImage 0
  · show mulImage.read (gpow 1) = some (mulImage ⟨1, by decide⟩)
    exact read_lit mulImage 1

/-- `mul_192bit_word` is a valid execution. -/
example : ValidExecution mulProg mulInput mulTrace := ⟨mulImage_boundary 3, mul_run⟩

/-- Its register sequence has four states. -/
example : mulTrace.regs.length = 4 := Trace.regs_length mul_run

/-- A fourth step is refused: the sentinel is never executed. -/
example : run mulProg mulImage 4 Regs.initial = none := by
  rw [show 4 = 3 + 1 by rfl, run_add, mul_run, Option.bind_eq_bind, Option.bind_some]
  exact run_succ_of_eq (r := Regs.final mulProg) rfl 0

/-! ## `N_prog = 1`: the empty execution -/

/-- One slot, the sentinel. -/
def oneProg : Program := ⟨0, by decide, ![.xor 1 1 1]⟩

/-- Sentinel safety is inhabited even for the zero-step program. -/
example : SentinelSafe oneProg := by decide

/-- Zero steps from `(1, 1)` reach `(g^0, 1)`, so the program has a valid execution... -/
example : ValidExecution oneProg mulInput ⟨minLogMem, mulImage, 0⟩ :=
  ⟨mulImage_boundary 0, by rw [run_zero]; decide +kernel⟩

/-- ...and its sentinel is not executed, whatever it holds. -/
example : run oneProg mulImage 1 Regs.initial = none := run_succ_of_eq (by decide +kernel) 0

/-- A one-slot program also permits a `JUMP` in its unexecuted sentinel. Sentinel safety is
needed by the current constraint-soundness theorem, not by ISA execution. -/
def oneJumpProg : Program := ⟨0, by decide, ![.jump 0 0 0]⟩

example : ¬ SentinelSafe oneJumpProg := by decide
example : ValidExecution oneJumpProg mulInput ⟨minLogMem, mulImage, 0⟩ :=
  ⟨mulImage_boundary 0, by rw [run_zero]; decide +kernel⟩
example : run oneJumpProg mulImage 1 Regs.initial = none :=
  run_succ_of_eq (by decide +kernel) 0

/-! ## Control flow: `JUMP` and `DEREF` on a sixteen-cell image -/

/-- Sixteen cells. `JUMP` reads `c, d, f` at `2, 3, 4` (all in `K`), or `c = 0` at `12` and
`d = y ∉ K` at `13`; `DEREF` reads the pointer `g^7` at `5`, its local cell at `6`, and the
target `g² · pc` at `7`; the halting `JUMP` reads the sentinel `g` at `14`. -/
def ctlImage : MemImage 4 := fun i ↦
  match (i : ℕ) with
  | 2 => E.ofLimbs 1 0 0
  | 3 => E.ofLimbs (gpow 3) 0 0
  | 4 => E.ofLimbs (gpow 5) 0 0
  | 5 => E.ofLimbs (gpow 7) 0 0
  | 6 => E.ofLimbs (K.ofBits 9) (K.ofBits 9) (K.ofBits 9)
  | 7 => E.ofLimbs (gpow 2) 0 0
  | 13 => E.ofLimbs 0 1 0
  | 14 => E.ofLimbs g 0 0
  | _ => 0

/-- A two-slot program: the instruction under test, then the sentinel. -/
def oneStep (i : Instr) : Program := ⟨1, by decide, ![i, .xor 1 1 1]⟩

/-- A taken `JUMP`: `c = 1 ≠ 0`, so the registers become `(d, f) = (g^3, g^5)`. -/
example : step (oneStep (.jump (gpow 2) (gpow 3) (gpow 4))) ctlImage ⟨1, 1⟩ =
    some ⟨gpow 3, gpow 5⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.jump (gpow 2) (gpow 3) (gpow 4)) = _
  simp only [execute, executeWith, one_mul, read_lit ctlImage 2, read_lit ctlImage 3, read_lit ctlImage 4]
  decide +kernel

/-- A `JUMP` not taken: `c = 0`, so it falls through to `(g, 1)`. -/
example : step (oneStep (.jump (gpow 12) (gpow 3) (gpow 4))) ctlImage ⟨1, 1⟩ = some ⟨g, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.jump (gpow 12) (gpow 3) (gpow 4)) = _
  simp only [execute, executeWith, one_mul, read_lit ctlImage 12, read_lit ctlImage 3, read_lit ctlImage 4]
  decide +kernel

/-- The same `JUMP` with `d = y ∉ K` is invalid although it is not taken. -/
example : step (oneStep (.jump (gpow 12) (gpow 13) (gpow 4))) ctlImage ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.jump (gpow 12) (gpow 13) (gpow 4)) = _
  simp only [execute, executeWith, one_mul, read_lit ctlImage 12, read_lit ctlImage 13, read_lit ctlImage 4]
  decide +kernel

/-- A taken branch also rejects a destination outside `K`. -/
example : step (oneStep (.jump (gpow 2) (gpow 13) (gpow 4))) ctlImage ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.jump (gpow 2) (gpow 13) (gpow 4)) = _
  simp only [execute, executeWith, one_mul, read_lit ctlImage 2, read_lit ctlImage 13, read_lit ctlImage 4]
  decide +kernel

/-- The pointer cell holds the address `g^7`. -/
theorem ctl_pointer : (ctlImage ⟨5, by decide⟩).limb 0 = gpow 7 := by decide +kernel

/-- A `DEREF` in `pc` mode at `pc = 1`: the pointer `g^7` is in `K`, the local cell is read,
and `mem[g^7 · 1] = g² · 1`. The kernel decides an `E` equality only against a word in
`E.ofLimbs` form, so the `DEREF` source is put in that form first
(`ofK_eq_ofLimbs`). -/
example : step (oneStep (.deref (gpow 5) 1 (gpow 6) .pc)) ctlImage ⟨1, 1⟩ = some ⟨g, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.deref (gpow 5) 1 (gpow 6) .pc) = _
  simp only [execute, executeWith, one_mul, mul_one, read_lit ctlImage 5, Option.bind_eq_bind,
    Option.bind_some, ctl_pointer, read_lit ctlImage 6, read_lit ctlImage 7, derefSource,
    ofK_eq_ofLimbs]
  decide +kernel

/-- Change only the target cell so the same pointer and local reads exercise `cell` mode. -/
def derefCellImage : MemImage 4 := fun i ↦
  if i.val = 7 then ctlImage ⟨6, by decide⟩ else ctlImage i

theorem derefCell_pointer : (derefCellImage ⟨5, by decide⟩).limb 0 = gpow 7 :=
  by decide +kernel

/-- `cell` mode copies the local cell value to the pointed-to target. -/
example : step (oneStep (.deref (gpow 5) 1 (gpow 6) .cell)) derefCellImage ⟨1, 1⟩ =
    some ⟨g, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute derefCellImage ⟨1, 1⟩ (.deref (gpow 5) 1 (gpow 6) .cell) = _
  simp only [execute, executeWith, one_mul, mul_one, read_lit derefCellImage 5,
    Option.bind_eq_bind, Option.bind_some, derefCell_pointer, read_lit derefCellImage 6,
    read_lit derefCellImage 7, derefSource]
  decide +kernel

/-- Change the target to the frame pointer embedded in `E`; the local cell is still read. -/
def derefFpImage : MemImage 4 := fun i ↦
  if i.val = 7 then E.ofLimbs 1 0 0 else ctlImage i

theorem derefFp_pointer : (derefFpImage ⟨5, by decide⟩).limb 0 = gpow 7 :=
  by decide +kernel

/-- `fp` mode stores the current frame pointer at the target. -/
example : step (oneStep (.deref (gpow 5) 1 (gpow 6) .fp)) derefFpImage ⟨1, 1⟩ =
    some ⟨g, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute derefFpImage ⟨1, 1⟩ (.deref (gpow 5) 1 (gpow 6) .fp) = _
  simp only [execute, executeWith, one_mul, mul_one, read_lit derefFpImage 5,
    Option.bind_eq_bind, Option.bind_some, derefFp_pointer, read_lit derefFpImage 6,
    read_lit derefFpImage 7, derefSource, ofK_eq_ofLimbs]
  decide +kernel

/-- The same image cannot satisfy `cell` mode: its target differs from the local cell. -/
example : step (oneStep (.deref (gpow 5) 1 (gpow 6) .cell)) ctlImage ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.deref (gpow 5) 1 (gpow 6) .cell) = none
  simp only [execute, executeWith, one_mul, mul_one, read_lit ctlImage 5, Option.bind_eq_bind,
    Option.bind_some, ctl_pointer, read_lit ctlImage 6, read_lit ctlImage 7, derefSource]
  decide +kernel

/-- The same target also differs from the frame pointer required by `fp` mode. -/
example : step (oneStep (.deref (gpow 5) 1 (gpow 6) .fp)) ctlImage ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.deref (gpow 5) 1 (gpow 6) .fp) = none
  simp only [execute, executeWith, one_mul, mul_one, read_lit ctlImage 5, Option.bind_eq_bind,
    Option.bind_some, ctl_pointer, read_lit ctlImage 6, read_lit ctlImage 7,
    derefSource, ofK_eq_ofLimbs]
  decide +kernel

/-- Every mode rejects a pointer whose upper limbs are nonzero, before using it as an address. -/
def nonKPointerImage : MemImage 4 := fun i ↦
  if i.val = 5 then E.ofLimbs (gpow 7) 1 0 else ctlImage i

example : step (oneStep (.deref (gpow 5) 1 (gpow 6) .cell)) nonKPointerImage ⟨1, 1⟩ =
    none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute nonKPointerImage ⟨1, 1⟩ (.deref (gpow 5) 1 (gpow 6) .cell) = none
  simp only [execute, executeWith, one_mul, read_lit nonKPointerImage 5, Option.bind_eq_bind,
    Option.bind_some]
  decide +kernel

/-- The same `DEREF` with its local cell `g^16` out of range is invalid, although `pc` mode
ignores the cell's value. -/
example : step (oneStep (.deref (gpow 5) 1 (gpow 16) .pc)) ctlImage ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.deref (gpow 5) 1 (gpow 16) .pc) = _
  simp only [execute, executeWith, one_mul, mul_one, read_lit ctlImage 5, Option.bind_eq_bind,
    Option.bind_some, Option.bind_none, read_sixteen]
  decide +kernel

/-! ## Failed reads -/

/-- An operand past the end of memory reads nothing. -/
example : step (oneStep (.xor (gpow 16) (gpow 2) (gpow 3))) ctlImage ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.xor (gpow 16) (gpow 2) (gpow 3)) = _
  simp only [execute, executeWith, one_mul, read_sixteen, Option.bind_eq_bind, Option.bind_none]

/-- The operand `0` names no cell. -/
example : step (oneStep (.xor 0 (gpow 2) (gpow 3))) ctlImage ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.xor 0 (gpow 2) (gpow 3)) = _
  simp only [execute, executeWith, mul_zero, MemImage.read_zero, Option.bind_eq_bind, Option.bind_none]

/-- A counter past the bytecode fetches nothing. -/
example : step (oneStep (.xor 1 1 1)) ctlImage ⟨gpow 2, 1⟩ = none :=
  step_eq_none_of_fetch_eq_none (by
    show (oneStep (.xor 1 1 1)).fetch (gpow 2) = none
    rw [Program.fetch, gLog?_gpow_eq_none (by decide) (by decide), Option.map_none])

/-! ## The final frame pointer -/

/-- A `JUMP` to the sentinel `g` with `fp ← g`. -/
def haltProg : Program := oneStep (.jump (gpow 2) (gpow 14) (gpow 14))

theorem halt_step : step haltProg ctlImage Regs.initial = some ⟨g, g⟩ := by
  rw [step_of_fetch_eq_some (r := Regs.initial) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.jump (gpow 2) (gpow 14) (gpow 14)) = _
  simp only [execute, executeWith, one_mul, read_lit ctlImage 2, read_lit ctlImage 14]
  decide +kernel

/-- The run reaches the sentinel after one step with `fp = g`, and no number of steps reaches
`(g, 1)`: no trace over this image is a valid execution. -/
example : ∀ n, run haltProg ctlImage n Regs.initial ≠ some (Regs.final haltProg) := by
  intro n
  match n with
  | 0 => rw [run_zero]; decide +kernel
  | 1 =>
    rw [run_succ_of_ne (prog := haltProg) (r := Regs.initial) (by decide +kernel) 0, halt_step]
    decide +kernel
  | n + 2 =>
    rw [show n + 2 = 2 + n by omega, run_add,
      run_succ_of_ne (prog := haltProg) (r := Regs.initial) (by decide +kernel) 1, halt_step,
      Option.bind_eq_bind, Option.bind_some,
      run_succ_of_eq (prog := haltProg) (r := ⟨g, g⟩) (by decide +kernel) 0]
    exact fun h ↦ Option.some_ne_none _ h.symm

/-! ## `BLAKE2S` (`blake2s_computes_the_compression`, `cpu/mod.rs:774-836`) -/

-- The cells of the executor test `blake2s_computes_the_compression` at leanVM a386121f.
def rustM0 : E :=
  E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfedcba9876543210) 0x0000000000000000
def rustM1 : E :=
  E.ofLimbs (K.ofBits 0x1111222233334444) (K.ofBits 0x5555666677778888) 0x0000000000000000
def rustM2 : E :=
  E.ofLimbs (K.ofBits 0xdeadbeefcafebabe) (K.ofBits 0x0badf00d0badf00d) 0x0000000000000000
def rustM3 : E :=
  E.ofLimbs (K.ofBits 0x9999aaaabbbbcccc) (K.ofBits 0xddddeeeeffff0000) 0x0000000000000000
def rustCv0 : E := E.ofLimbs (K.ofBits 0x0000000000000007) 0x0000000000000000 0x0000000000000000
def rustCv1 : E := E.ofLimbs (K.ofBits 0x000000000000000b) 0x0000000000000000 0x0000000000000000
def rustMd : E :=
  E.ofLimbs (K.ofBits 0x0000000000000040) (K.ofBits 0x00000000ffffffff) 0x0000000000000000
def rustOut0 : E :=
  E.ofLimbs (K.ofBits 0x583fffe1350e2137) (K.ofBits 0x0de9e32629a5c508) 0x0000000000000000
def rustOut1 : E :=
  E.ofLimbs (K.ofBits 0xf1b0679a15df60bb) (K.ofBits 0x0228c8d4ed9b3a24) 0x0000000000000000

/-- The executor's cells: the chaining value at `0, 1` (the public input `[w(7), w(11)]`), the
message at `2..5`, the output at `6, 7`, and the metadata at `8`; `out1` is the second output
cell, mutated below. -/
def blakeImage (out1 : E) : MemImage 4 := fun i ↦
  match (i : ℕ) with
  | 0 => rustCv0
  | 1 => rustCv1
  | 2 => rustM0
  | 3 => rustM1
  | 4 => rustM2
  | 5 => rustM3
  | 6 => rustOut0
  | 7 => out1
  | 8 => rustMd
  | _ => 0

/-- The executor's `BLAKE2S` row: `ins: [2, 3, 4, 5], cv: 0, out: 6, md: 8`. -/
def blakeIns : Instr := .blake2s ![gpow 2, gpow 3, gpow 4, gpow 5] 1 (gpow 6) (gpow 8)

/-- The nine reads of the row, on the image with second output cell `out1`. -/
theorem blake_reads (out1 : E) :
    execute (blakeImage out1) ⟨1, 1⟩ blakeIns =
      (do
        guard (CompressCells ![rustM0, rustM1, rustM2, rustM3] rustCv0 rustCv1 rustOut0 out1
          rustMd)
        pure (Regs.next ⟨1, 1⟩)) := by
  simp only [blakeIns, execute, executeWith, one_mul, mul_one, Matrix.cons_val, g_mul_gpow, Nat.reduceAdd,
    read_one (blakeImage out1), read_g (blakeImage out1), read_lit (blakeImage out1) 2,
    read_lit (blakeImage out1) 3, read_lit (blakeImage out1) 4, read_lit (blakeImage out1) 5,
    read_lit (blakeImage out1) 6, read_lit (blakeImage out1) 7, read_lit (blakeImage out1) 8,
    Option.bind_eq_bind, Option.bind_some]
  rfl

/-- The row steps: the nine cells satisfy `CompressCells`. -/
example : step (oneStep blakeIns) (blakeImage rustOut1) ⟨1, 1⟩ = some ⟨g, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute (blakeImage rustOut1) ⟨1, 1⟩ blakeIns = _
  rw [blake_reads]
  decide +kernel

/-- With a nonzero top limb on the second output cell the row is invalid, although the
cell's words are right. -/
example : step (oneStep blakeIns)
    (blakeImage (E.ofLimbs (K.ofBits 0xf1b0679a15df60bb) (K.ofBits 0x0228c8d4ed9b3a24) 1)) ⟨1, 1⟩ = none := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) (fetch_one _)]
  show execute (blakeImage _) ⟨1, 1⟩ blakeIns = _
  rw [blake_reads]
  decide +kernel

/-! ## A `JUMP` sentinel -/

/-- `haltProg` with a `JUMP` in the sentinel slot. Read in frame `fp = g`, its operands `g` and
`g^13` name cells `2` and `14`: `c = 1`, `d = g` (the sentinel), `f = 1`. -/
def jumpSentinelProg : Program :=
  ⟨1, by decide, ![.jump (gpow 2) (gpow 14) (gpow 14), .jump g (gpow 13) g]⟩

/-- The load-bearing soundness premise rejects the JUMP sentinel. -/
example : ¬ SentinelSafe jumpSentinelProg := by decide

/-- Row 1: `(1, 1)` jumps to the sentinel counter with `fp = g`. -/
theorem jumpSentinel_row1 : step jumpSentinelProg ctlImage Regs.initial = some ⟨g, g⟩ := by
  rw [step_of_fetch_eq_some (r := Regs.initial) (fetch_one _)]
  show execute ctlImage ⟨1, 1⟩ (.jump (gpow 2) (gpow 14) (gpow 14)) = _
  simp only [execute, executeWith, one_mul, read_lit ctlImage 2, read_lit ctlImage 14]
  decide +kernel

/-- Row 2, at the sentinel counter: `(g, g)` jumps to the final registers `(g, 1)`. -/
theorem jumpSentinel_row2 :
    step jumpSentinelProg ctlImage ⟨g, g⟩ = some (Regs.final jumpSentinelProg) := by
  rw [step_of_fetch_eq_some (r := ⟨g, g⟩) (jumpSentinelProg.fetch_gpow 1)]
  show execute ctlImage ⟨g, g⟩ (.jump g (gpow 13) g) = some ⟨gpow 1, 1⟩
  have hgg : g * g = gpow 2 := (pow_two g).symm
  simp only [execute, executeWith, hgg, g_mul_gpow, read_lit ctlImage 2, read_lit ctlImage 14]
  decide +kernel

/-- The two rows are steps that chain from the initial to the final registers, which is all the
state channel asks of them. -/
example : (step jumpSentinelProg ctlImage Regs.initial >>= step jumpSentinelProg ctlImage) =
    some (Regs.final jumpSentinelProg) := by
  rw [jumpSentinel_row1, Option.bind_eq_bind, Option.bind_some, jumpSentinel_row2]

/-- Yet `run` halts at `(g, g)`, so no step count is a `ValidExecution`: without
`SentinelSafe`, constraint soundness would be false for this program. -/
example :
    ∀ n, run jumpSentinelProg ctlImage n Regs.initial ≠ some (Regs.final jumpSentinelProg) := by
  intro n
  match n with
  | 0 => rw [run_zero]; decide +kernel
  | 1 =>
    rw [run_succ_of_ne (prog := jumpSentinelProg) (r := Regs.initial) (by decide +kernel) 0,
      jumpSentinel_row1]
    decide +kernel
  | n + 2 =>
    rw [show n + 2 = 2 + n by omega, run_add,
      run_succ_of_ne (prog := jumpSentinelProg) (r := Regs.initial) (by decide +kernel) 1,
      jumpSentinel_row1, Option.bind_eq_bind, Option.bind_some,
      run_succ_of_eq (prog := jumpSentinelProg) (r := ⟨g, g⟩) (by decide +kernel) 0]
    exact fun h ↦ Option.some_ne_none _ h.symm

end LeanVMTests.Semantics.Execution
