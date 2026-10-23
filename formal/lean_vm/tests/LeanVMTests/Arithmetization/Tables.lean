import LeanVM.Arithmetization.Tables.Xor
import LeanVM.Arithmetization.Tables.MulNative
import LeanVM.Arithmetization.Tables.SetConstant
import LeanVM.Arithmetization.Tables.Deref
import LeanVM.Arithmetization.Tables.Jump
import LeanVM.Arithmetization.Tables.Blake2s
import Clean.Circuit.WitnessGeneration

/-!
# Tests: the six opcode tables

A classic test for kernel evaluation: the fixtures decide `E` arithmetic and `Regs`
equalities in the kernel. One prover data serves every table: a thirty-two-word image
(`κ = 5`) holding the cells of one instruction per opcode, a `DEREF` in each of the three store
modes and a `JUMP` on each branch, read through `imageOf` at literal indices as in the channel
tests. There is no program fixture: the tables are program-free, each row naming
the instruction it executes in its own columns.

For each table: the honest row is bound (`*Bindings`, over `imageOf tabData`) and satisfies its
functional specification (`*Spec`, with `execute` of the row's instruction decided in
the kernel, which also names the successor `main` returns), and every valid execution of the
fixture yields a satisfying row from the execution alone (`*_exec_complete`, on the row
`*RowOf` reads back from the image): the `DEREF` executions in the three store modes, the `JUMP`
executions on both branches in their honest environment `jumpEnv`, whose two witness slots are
what the witness programs compute (`jump_env_iff`); Clean's array generator `Circuit.witgen`
computes the same two values (`#guard`, compiled).

Rejections use actual rows and the tables' own theorems: the counterexample to a
step-only contract, a `DEREF` row with the flag pair `(1, 1)`, executes from its registers
and fails its bindings; a changed input limb (`XOR`, `MUL_NATIVE`), a changed immediate
(`SET_CONSTANT`, which the cell does not hold), and a non-canonical image cell (`BLAKE2S`)
fail the constraints `main` emits in every environment over the data, read
back through each table's `soundness`; the two `JUMP` residuals reject the wrong witness `b = 1`
at `v_cond = 0` (`flags_sound`). What a table does not reject is a row
naming an instruction the program does not hold at its counter (an `XOR` row at `pc = g^2`
with honest reads is accepted): that is the bus's, as it is for leanVM's AIRs, and the
boundary tests reject it at the block. The `BLAKE2S` boundary: a bound row whose output cell is
a wrong but canonical word, consistently in row and image, is locally complete
(`blake2sRow_complete`) and fails `Blake2sRelation` and `Blake2sSpec`, the failure Flock
enforces.

The `MUL_NATIVE` row reproduces the executor's `mul_192bit_word` product (`cpu/mod.rs:887-904`)
from the twelve-product coordinates, and the `BLAKE2S` row the cells of the executor's
`blake2s_computes_the_compression`, both tests at leanVM `a386121f`.
-/

namespace LeanVMTests.Arithmetization.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization

/-! ## The fixture: one image -/

-- The executor test `mul_192bit_word` at leanVM a386121f: the operands `x`, `y` and the product
-- `x · y`.
def x0 : K := (K.ofBits 0x0123456789abcdef)
def x1 : K := (K.ofBits 0xfeedfacedeadbeef)
def x2 : K := (K.ofBits 0x1111222233334444)
def y0 : K := (K.ofBits 0x9999aaaabbbbcccc)
def y1 : K := (K.ofBits 0x13579bdf2468ace0)
def y2 : K := (K.ofBits 0x5555666677778888)
def mulXY : E :=
  E.ofLimbs (K.ofBits 0xf4bccd9a2e8e525b) (K.ofBits 0xf85ebb9433986f2f) (K.ofBits 0x918137982bf175ac)

-- The executor test `blake2s_computes_the_compression` at leanVM a386121f: the nine cells, as
-- `(lo, hi)`.
def rustM0 : Vector K 2 := #v[K.ofBits 0x0123456789abcdef, K.ofBits 0xfedcba9876543210]
def rustM1 : Vector K 2 := #v[K.ofBits 0x1111222233334444, K.ofBits 0x5555666677778888]
def rustM2 : Vector K 2 := #v[K.ofBits 0xdeadbeefcafebabe, K.ofBits 0x0badf00d0badf00d]
def rustM3 : Vector K 2 := #v[K.ofBits 0x9999aaaabbbbcccc, K.ofBits 0xddddeeeeffff0000]
def rustCv0 : Vector K 2 := #v[K.ofBits 0x0000000000000007, 0x0000000000000000]
def rustCv1 : Vector K 2 := #v[K.ofBits 0x000000000000000b, 0x0000000000000000]
def rustMd : Vector K 2 := #v[K.ofBits 0x0000000000000040, K.ofBits 0x00000000ffffffff]
def rustOut0 : Vector K 2 := #v[K.ofBits 0x583fffe1350e2137, K.ofBits 0x0de9e32629a5c508]
def rustOut1 : Vector K 2 := #v[K.ofBits 0xf1b0679a15df60bb, K.ofBits 0x0228c8d4ed9b3a24]

/-- The canonical image word of a two-limb cell. -/
def cell (v : Vector K 2) : Vector K 3 := #v[v[0], v[1], 0]

/-- The twelve-product coordinates of `x · y` (`TOWER_LANES`). -/
def xyLanes : Vector K 3 :=
  #v[x0 * y0 + x1 * y2 + x2 * y1, x0 * y1 + x1 * y0 + x1 * y2 + x2 * y1 + x2 * y2,
     x0 * y2 + x1 * y1 + x2 * y0 + x2 * y2]

/-- The image, thirty-two words: `x`, `y`, `x + y`, `x · y` at `2..5`; the `SET` immediate at
`6`; the `pc`-mode `DEREF` pointer `g^8` at `7`, its target `g²·g³` (the return address of
`pc = g^3`) at `8`, its local cell at `9`; the `JUMP` cells `c = 1`, `d = g^6`, `f = 1` at
`10..12` and the untaken condition `c = 0` at `13`; the nine `BLAKE2S` cells at `16..24`; the
`cell`-mode `DEREF` pointer `g^26` at `25`, its target at `26` holding the local word at `27`;
the `fp`-mode `DEREF` pointer `g^29` at `28`, its target at `29` holding `fp = 1`, its local cell
at `30`; zero elsewhere. -/
def memTable : Array (Vector K 3) :=
  #[#v[0, 0, 0], #v[0, 0, 0],
    #v[x0, x1, x2], #v[y0, y1, y2], #v[x0 + y0, x1 + y1, x2 + y2], xyLanes,
    #v[K.ofBits 7, K.ofBits 8, K.ofBits 9],
    #v[gpow 8, 0, 0], #v[g ^ 2 * gpow 3, 0, 0], #v[K.ofBits 5, K.ofBits 6, K.ofBits 7],
    #v[1, 0, 0], #v[gpow 6, 0, 0], #v[1, 0, 0],
    #v[0, 0, 0], #v[0, 0, 0], #v[0, 0, 0],
    cell rustM0, cell rustM1, cell rustM2, cell rustM3, cell rustCv0, cell rustCv1,
    cell rustOut0, cell rustOut1, cell rustMd,
    #v[gpow 26, 0, 0], #v[K.ofBits 3, K.ofBits 4, K.ofBits 5], #v[K.ofBits 3, K.ofBits 4, K.ofBits 5],
    #v[gpow 29, 0, 0], #v[1, 0, 0], #v[K.ofBits 9, K.ofBits 9, K.ofBits 9],
    #v[0, 0, 0]]

/-- The prover data of an image, its one table matched on arity so that the kernel never
compares names (as in the channel tests). -/
def dataOf (mem : Array (Vector K 3)) : ProverData K := fun _ n ↦
  match n with
  | 3 => mem
  | _ => #[]

/-- The fixture's prover data. -/
def tabData : ProverData K := dataOf memTable

theorem dataOf_logSize {mem : Array (Vector K 3)} (h : mem.size = 32) :
    (imageOf (dataOf mem)).1 = 5 := by
  show min (Nat.log 2 (memRows (dataOf mem)).size) maxLogMem = 5
  rw [show memRows (dataOf mem) = mem from rfl, h, show (32 : ℕ) = 2 ^ 5 by decide,
    Nat.log_pow (by norm_num)]
  decide

theorem dataOf_wellShaped {mem : Array (Vector K 3)} (h : mem.size = 32) :
    WellShapedData (dataOf mem) where
  memRows_size := by rw [dataOf_logSize h]; exact h

/-- On a well-shaped thirty-two-word data, the word at `g^k` is row `k` of the image, as
limbs. -/
theorem readAt {data : ProverData K} (hlog : (imageOf data).1 = 5) (hws : WellShapedData data)
    (k : ℕ) (v : Vector K 3) (hk : k < 32 := by decide)
    (hv : (memRows data)[k]'(by rw [hws.memRows_size, hlog]; exact hk) = v := by decide +kernel) :
    (imageOf data).2.read (gpow k) = some (E.ofLimbs v[0] v[1] v[2]) := by
  have hk' : k < 2 ^ (imageOf data).1 := by rw [hlog]; omega
  rw [show gpow k = gpow ((⟨k, hk'⟩ : Fin (2 ^ (imageOf data).1)) : ℕ) from rfl,
    MemImage.read_gpow (by rw [hlog]; decide), imageOf_apply hws _ hv]

/-- The word at `g^k` of the fixture's image. -/
theorem read_at (k : ℕ) (v : Vector K 3) (hk : k < 32 := by decide)
    (hv : memTable[k]'(by rw [show memTable.size = 32 from rfl]; exact hk) = v :=
      by decide +kernel) :
    (imageOf tabData).2.read (gpow k) = some (E.ofLimbs v[0] v[1] v[2]) :=
  readAt (dataOf_logSize rfl) (dataOf_wellShaped rfl) k v hk hv

/-- `read_at` with the word's three limbs spelled out, for the kernel fixtures. -/
theorem read_lit (k : ℕ) (a b c : K) (hk : k < 32 := by decide)
    (hv : memTable[k]'(by rw [show memTable.size = 32 from rfl]; exact hk) = #v[a, b, c] :=
      by decide +kernel) :
    (imageOf tabData).2.read (gpow k) = some (E.ofLimbs a b c) :=
  read_at k #v[a, b, c] hk hv

/-- `g · g^k = g^(k + 1)`, oriented for `simp`. -/
theorem g_mul_gpow (k : ℕ) : g * gpow k = gpow (k + 1) := (gpow_succ k).symm

/-! ## `XOR` -/

/-- The honest `XOR` row at `pc = g^0`, `fp = 1`: operands `g^2, g^3, g^4`, the words `x`, `y`. -/
def xorRow : XorRow K :=
  ⟨gpow 0, 1, gpow 2, gpow 3, gpow 4, #v[x0, x1, x2], #v[y0, y1, y2], 1, 1, 1, 1⟩

/-- The honest row is bound: the two operand words are the fixture's. -/
theorem xor_bindings : XorBindings (imageOf tabData).2 xorRow := by
  refine ⟨?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 2) = some (E.ofLimbs x0 x1 x2)
    rw [one_mul]; exact read_at 2 #v[x0, x1, x2]
  · show (imageOf tabData).2.read (1 * gpow 3) = some (E.ofLimbs y0 y1 y2)
    rw [one_mul]; exact read_at 3 #v[y0, y1, y2]

/-- `XorSpec` on the honest row: bound, and `XOR g^2 g^3 g^4` executes from `(1, 1)` to
`(g, 1)`. -/
theorem xor_spec : XorSpec xorRow ⟨g * gpow 0, 1⟩ tabData :=
  ⟨xor_bindings, by
    show execute (imageOf tabData).2 ⟨gpow 0, 1⟩ (.xor (gpow 2) (gpow 3) (gpow 4)) =
      some ⟨g * gpow 0, 1⟩
    simp only [execute, executeWith, one_mul, read_at 2 #v[x0, x1, x2], read_at 3 #v[y0, y1, y2],
      read_at 4 #v[x0 + y0, x1 + y1, x2 + y2]]
    decide +kernel⟩

/-- The valid execution alone yields a satisfying row (`xor_exec_complete`): no assumption on
the row, the honest prover builds it; `xor_spec` names the successor `main` returns. -/
example : ConstraintsHold.Completeness (rowEnv tabData)
    ((xorTable.main (const (xorRowOf (imageOf tabData).2
      (gpow 0) 1 (gpow 2) (gpow 3) (gpow 4) 1 1 1 1))).operations 0) :=
  xor_exec_complete xor_spec.exec_eq 1 1 1 1

/-- The table is program-free: the same honest reads at `pc = g^2`, a counter
whose instruction in the boundary tests' kind of program would be a `SET`, satisfy `XorSpec`
all the same. Which instruction the program holds at a counter is the bus's to check,
as it is for leanVM's `XOR` AIR. -/
def xorRow2 : XorRow K := { xorRow with pc := gpow 2 }

example : XorSpec xorRow2 ⟨g * gpow 2, 1⟩ tabData :=
  ⟨⟨xor_bindings.readA_eq, xor_bindings.readB_eq⟩, by
    show execute (imageOf tabData).2 ⟨gpow 2, 1⟩ (.xor (gpow 2) (gpow 3) (gpow 4)) =
      some ⟨g * gpow 2, 1⟩
    simp only [execute, executeWith, one_mul, read_at 2 #v[x0, x1, x2], read_at 3 #v[y0, y1, y2],
      read_at 4 #v[x0 + y0, x1 + y1, x2 + y2]]
    decide +kernel⟩

/-- An alleged `XOR` row with operands `0` fails `XorSpec` for every successor: the address `0`
reads nothing. Its counter plays no part. -/
def bogusXor : XorRow K :=
  { xorRow with pc := gpow 2, oA := 0, oB := 0, oC := 0, vA := #v[0, 0, 0] }

example (next : Regs K) : ¬ XorSpec bogusXor next tabData := by
  rintro ⟨⟨hA, -⟩, -⟩
  rw [show bogusXor.fp * bogusXor.oA = 0 from mul_zero 1, MemImage.read_zero] at hA
  cases hA

/-- A changed input limb: `execute` from the registers is unchanged, the bindings fail. -/
def xorRow' : XorRow K := { xorRow with vA := #v[x0 + 1, x1, x2] }

example (next : Regs K) : ¬ XorSpec xorRow' next tabData := by
  rintro ⟨⟨hA, -⟩, -⟩
  rw [show xorRow'.fp * xorRow'.oA = 1 * gpow 2 from rfl, one_mul, read_at 2 #v[x0, x1, x2]] at hA
  exact absurd (Option.some.inj hA) (by decide +kernel)

/-- …so the constraints `main` emits on it fail in every environment over the fixture: its
second pull is no read of the image (`soundness`, read back). -/
example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, tabData⟩ ((xorTable.main (const xorRow')).operations 0) := by
  intro h
  have hs : XorSpec xorRow' _ tabData := (xorTable.soundness 0 ⟨get, tabData⟩ (const xorRow')
    xorRow' ProvableType.eval_const trivial h).1
  obtain ⟨⟨hA, -⟩, -⟩ := hs
  rw [show xorRow'.fp * xorRow'.oA = 1 * gpow 2 from rfl, one_mul, read_at 2 #v[x0, x1, x2]] at hA
  exact absurd (Option.some.inj hA) (by decide +kernel)

/-! ## `MUL_NATIVE` -/

/-- The twelve-product coordinates of the Rust operands are the Rust product. -/
example : E.ofLimbs xyLanes[0] xyLanes[1] xyLanes[2] = mulXY := by decide +kernel

/-- The honest `MUL_NATIVE` row at `pc = g^1`. -/
def mulRow : MulRow K :=
  ⟨gpow 1, 1, gpow 2, gpow 3, gpow 5, #v[x0, x1, x2], #v[y0, y1, y2], 1, 1, 1, 1⟩

theorem mul_bindings : MulBindings (imageOf tabData).2 mulRow := by
  refine ⟨?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 2) = some (E.ofLimbs x0 x1 x2)
    rw [one_mul]; exact read_at 2 #v[x0, x1, x2]
  · show (imageOf tabData).2.read (1 * gpow 3) = some (E.ofLimbs y0 y1 y2)
    rw [one_mul]; exact read_at 3 #v[y0, y1, y2]

/-- `MulSpec` on the honest row, through the product of the Rust vectors. -/
theorem mul_spec : MulSpec mulRow ⟨g * gpow 1, 1⟩ tabData :=
  ⟨mul_bindings, by
    show execute (imageOf tabData).2 ⟨gpow 1, 1⟩ (.mulNative (gpow 2) (gpow 3) (gpow 5)) =
      some ⟨g * gpow 1, 1⟩
    simp only [execute, executeWith, one_mul, read_at 2 #v[x0, x1, x2], read_at 3 #v[y0, y1, y2],
      read_at 5 xyLanes]
    decide +kernel⟩

example : ConstraintsHold.Completeness (rowEnv tabData)
    ((mulTable.main (const (mulRowOf (imageOf tabData).2
      (gpow 1) 1 (gpow 2) (gpow 3) (gpow 5) 1 1 1 1))).operations 0) :=
  mul_exec_complete mul_spec.exec_eq 1 1 1 1

/-- A changed input limb fails the bindings, and the constraints in every environment. -/
def mulRow' : MulRow K := { mulRow with vB := #v[y0, y1 + 1, y2] }

example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, tabData⟩ ((mulTable.main (const mulRow')).operations 0) := by
  intro h
  have hs : MulSpec mulRow' _ tabData := (mulTable.soundness 0 ⟨get, tabData⟩ (const mulRow')
    mulRow' ProvableType.eval_const trivial h).1
  obtain ⟨⟨-, hB⟩, -⟩ := hs
  rw [show mulRow'.fp * mulRow'.oB = 1 * gpow 3 from rfl, one_mul, read_at 3 #v[y0, y1, y2]] at hB
  exact absurd (Option.some.inj hB) (by decide +kernel)

/-! ## `SET_CONSTANT` -/

/-- The honest `SET_CONSTANT` row at `pc = g^2`: the immediate `7 + 8·y + 9·y²` at `g^6`. -/
def setRow : SetRow K := ⟨gpow 2, 1, gpow 6, #v[K.ofBits 7, K.ofBits 8, K.ofBits 9], 1, 1⟩

/-- `SetSpec` on the honest row: `SET_CONSTANT g^6 (7 + 8·y + 9·y²)` executes, the cell holding
the immediate. -/
theorem set_spec : SetSpec setRow ⟨g * gpow 2, 1⟩ tabData :=
  ⟨by
    show execute (imageOf tabData).2 ⟨gpow 2, 1⟩ (.setConstant (gpow 6) (E.ofLimbs (K.ofBits 7) (K.ofBits 8) (K.ofBits 9))) =
      some ⟨g * gpow 2, 1⟩
    simp only [execute, executeWith, one_mul, read_at 6 #v[K.ofBits 7, K.ofBits 8, K.ofBits 9]]
    decide +kernel⟩

example : ConstraintsHold.Completeness (rowEnv tabData)
    ((setTable.main (const (setRowOf (gpow 2) 1 (gpow 6) (E.ofLimbs (K.ofBits 7) (K.ofBits 8) (K.ofBits 9)) 1 1))).operations 0) :=
  set_exec_complete set_spec.exec_eq 1 1

/-- A changed immediate limb: the cell `fp·o` does not hold the row's immediate, so the row
fails `SetRefines` and the constraints fail in every environment. (Whether the program holds
this immediate at `g^2` is the bus's to check.) -/
def setRow' : SetRow K := { setRow with k := #v[K.ofBits 7, K.ofBits 8, K.ofBits 10] }

example (next : Regs K) : ¬ SetSpec setRow' next tabData := by
  intro h
  obtain ⟨hk, -⟩ := (set_refines_iff _ _ _).mp h
  rw [show setRow'.fp * setRow'.o = 1 * gpow 6 from rfl, one_mul, read_at 6 #v[K.ofBits 7, K.ofBits 8, K.ofBits 9]] at hk
  exact absurd (Option.some.inj hk) (by decide +kernel)

example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, tabData⟩ ((setTable.main (const setRow')).operations 0) := by
  intro h
  have hs : SetSpec setRow' _ tabData := (setTable.soundness 0 ⟨get, tabData⟩ (const setRow')
    setRow' ProvableType.eval_const trivial h).1
  obtain ⟨hk, -⟩ := (set_refines_iff _ _ _).mp hs
  rw [show setRow'.fp * setRow'.o = 1 * gpow 6 from rfl, one_mul, read_at 6 #v[K.ofBits 7, K.ofBits 8, K.ofBits 9]] at hk
  exact absurd (Option.some.inj hk) (by decide +kernel)

/-! ## `DEREF` -/

/-- The honest `DEREF` row at `pc = g^3` in `pc` mode (`f_pc = 1`, `f_fp = 0`): pointer `g^8`
at `g^7`, local cell `g^9`, target `g^8 · 1` holding `g² · g^3`. -/
def derefRow : DerefRow K :=
  ⟨gpow 3, 1, gpow 7, 1, gpow 9, 1, 0, gpow 8, #v[K.ofBits 5, K.ofBits 6, K.ofBits 7], 1, 1, 1, 1⟩

/-- The `cell`-mode row at `pc = g^6`: pointer `g^26` at `g^25`, local cell `g^27`, target
`g^26 · 1` holding the local word. -/
def derefCellRow : DerefRow K :=
  ⟨gpow 6, 1, gpow 25, 1, gpow 27, 0, 0, gpow 26, #v[K.ofBits 3, K.ofBits 4, K.ofBits 5], 1, 1, 1, 1⟩

/-- The `fp`-mode row at `pc = g^7`: pointer `g^29` at `g^28`, local cell `g^30` (read, not
stored), target `g^29 · 1` holding `fp = 1`. -/
def derefFpRow : DerefRow K :=
  ⟨gpow 7, 1, gpow 28, 1, gpow 30, 0, 1, gpow 29, #v[K.ofBits 9, K.ofBits 9, K.ofBits 9], 1, 1, 1, 1⟩

theorem deref_bindings : DerefBindings (imageOf tabData).2 derefRow .pc := by
  refine ⟨rfl, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 7) = some (E.ofLimbs (gpow 8) 0 0)
    rw [one_mul]; exact read_at 7 #v[gpow 8, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 9) = some (E.ofLimbs (K.ofBits 5) (K.ofBits 6) (K.ofBits 7))
    rw [one_mul]; exact read_at 9 #v[K.ofBits 5, K.ofBits 6, K.ofBits 7]

theorem derefCell_bindings : DerefBindings (imageOf tabData).2 derefCellRow .cell := by
  refine ⟨rfl, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 25) = some (E.ofLimbs (gpow 26) 0 0)
    rw [one_mul]; exact read_at 25 #v[gpow 26, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 27) = some (E.ofLimbs (K.ofBits 3) (K.ofBits 4) (K.ofBits 5))
    rw [one_mul]; exact read_at 27 #v[K.ofBits 3, K.ofBits 4, K.ofBits 5]

theorem derefFp_bindings : DerefBindings (imageOf tabData).2 derefFpRow .fp := by
  refine ⟨rfl, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 28) = some (E.ofLimbs (gpow 29) 0 0)
    rw [one_mul]; exact read_at 28 #v[gpow 29, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 30) = some (E.ofLimbs (K.ofBits 9) (K.ofBits 9) (K.ofBits 9))
    rw [one_mul]; exact read_at 30 #v[K.ofBits 9, K.ofBits 9, K.ofBits 9]

/-- `DEREF g^7 1 g^9` in `pc` mode executes from `(g^3, 1)`: the target holds the return address
`g² · g^3`. -/
theorem deref_exec :
    execute (imageOf tabData).2 ⟨gpow 3, 1⟩ (.deref (gpow 7) 1 (gpow 9) .pc) =
      some ⟨g * gpow 3, 1⟩ := by
  simp only [execute, executeWith, one_mul, mul_one, read_lit 7 (gpow 8) 0 0, Option.bind_eq_bind,
    Option.bind_some, guard, isInK_ofLimbs, ite_true, limb_ofLimbs, Matrix.cons_val_zero,
    read_lit 9 (K.ofBits 5) (K.ofBits 6) (K.ofBits 7), read_lit 8 (g ^ 2 * gpow 3) 0 0, derefSource, ofK_eq_ofLimbs]
  decide +kernel

/-- In `cell` mode from `(g^6, 1)`: the target holds the local word. -/
theorem derefCell_exec :
    execute (imageOf tabData).2 ⟨gpow 6, 1⟩ (.deref (gpow 25) 1 (gpow 27) .cell) =
      some ⟨g * gpow 6, 1⟩ := by
  simp only [execute, executeWith, one_mul, mul_one, read_lit 25 (gpow 26) 0 0, Option.bind_eq_bind,
    Option.bind_some, guard, isInK_ofLimbs, ite_true, limb_ofLimbs, Matrix.cons_val_zero,
    read_lit 27 (K.ofBits 3) (K.ofBits 4) (K.ofBits 5), read_lit 26 (K.ofBits 3) (K.ofBits 4) (K.ofBits 5), derefSource]
  decide +kernel

/-- In `fp` mode from `(g^7, 1)`: the target holds `fp = 1`; the local cell is read all the
same. -/
theorem derefFp_exec :
    execute (imageOf tabData).2 ⟨gpow 7, 1⟩ (.deref (gpow 28) 1 (gpow 30) .fp) =
      some ⟨g * gpow 7, 1⟩ := by
  simp only [execute, executeWith, one_mul, mul_one, read_lit 28 (gpow 29) 0 0, Option.bind_eq_bind,
    Option.bind_some, guard, isInK_ofLimbs, ite_true, limb_ofLimbs, Matrix.cons_val_zero,
    read_lit 30 (K.ofBits 9) (K.ofBits 9) (K.ofBits 9), read_lit 29 1 0 0, derefSource, ofK_eq_ofLimbs]
  decide +kernel

/-- `DerefSpec` in each store mode: the bindings and the execution, with the same mode. -/
theorem deref_spec : DerefSpec derefRow ⟨g * gpow 3, 1⟩ tabData :=
  ⟨.pc, deref_bindings, deref_exec⟩

theorem derefCell_spec : DerefSpec derefCellRow ⟨g * gpow 6, 1⟩ tabData :=
  ⟨.cell, derefCell_bindings, derefCell_exec⟩

theorem derefFp_spec : DerefSpec derefFpRow ⟨g * gpow 7, 1⟩ tabData :=
  ⟨.fp, derefFp_bindings, derefFp_exec⟩

/-- A valid execution in each store mode alone yields a satisfying row
(`deref_exec_complete`); its successor is the one `DerefSpec` names. -/
example : ConstraintsHold.Completeness (rowEnv tabData)
    ((derefTable.main (const (derefRowOf (imageOf tabData).2
      (gpow 3) 1 (gpow 7) 1 (gpow 9) .pc 1 1 1 1))).operations 0) :=
  deref_exec_complete deref_exec 1 1 1 1

example : ConstraintsHold.Completeness (rowEnv tabData)
    ((derefTable.main (const (derefRowOf (imageOf tabData).2
      (gpow 6) 1 (gpow 25) 1 (gpow 27) .cell 1 1 1 1))).operations 0) :=
  deref_exec_complete derefCell_exec 1 1 1 1

example : ConstraintsHold.Completeness (rowEnv tabData)
    ((derefTable.main (const (derefRowOf (imageOf tabData).2
      (gpow 7) 1 (gpow 28) 1 (gpow 30) .fp 1 1 1 1))).operations 0) :=
  deref_exec_complete derefFp_exec 1 1 1 1

/-- The counterexample to a step-only contract: the honest row with the flag pair
`(1, 1)` executes the `pc`-mode instruction from its registers (the flags are no input of
`execute`)… -/
def invalidDeref : DerefRow K := { derefRow with fpc := 1, ffp := 1 }

example : execute (imageOf tabData).2 ⟨invalidDeref.pc, invalidDeref.fp⟩
    (.deref (gpow 7) 1 (gpow 9) .pc) = some ⟨g * gpow 3, 1⟩ :=
  deref_exec

/-- …and fails `DerefSpec` for every successor: `(1, 1)` is no store mode's flags. -/
example (next : Regs K) : ¬ DerefSpec invalidDeref next tabData := by
  rintro ⟨mode, ⟨hflags, -, -⟩, -⟩
  cases mode <;> exact absurd hflags (by decide +kernel)

/-- The flag pair `(1, 1)` cannot be pulled either: its bytecode tuple decodes to nothing, at
this counter or any other and over any data. -/
example (pc : K) (data : ProverData K) :
    ¬ BytecodePull.Guarantees ⟨pc, 1, Opcode.deref.code, #v[gpow 7, 1, gpow 9, 1, 1, 0, 0]⟩
      data := by
  rintro ⟨ins, hdec⟩
  have h : decode (#v[Opcode.deref.code] ++ #v[gpow 7, 1, gpow 9, 1, 1, 0, 0]) = none := by
    decide +kernel
  exact nomatch h.symm.trans hdec

/-! ## `JUMP` -/

/-- The honest `JUMP` row at `pc = g^4`, taken: `c = 1`, `d = g^6`, `f = 1`. -/
def jumpRow : JumpRow K := ⟨gpow 4, 1, gpow 10, gpow 11, gpow 12, 1, gpow 6, 1, 1, 1, 1, 1⟩

/-- The untaken `JUMP` row at `pc = g^8`: `c = 0`, the same `d`, `f`. -/
def jumpRow0 : JumpRow K := ⟨gpow 8, 1, gpow 13, gpow 11, gpow 12, 0, gpow 6, 1, 1, 1, 1, 1⟩

theorem jump_bindings : JumpBindings (imageOf tabData).2 jumpRow := by
  refine ⟨?_, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 10) = some (E.ofLimbs 1 0 0)
    rw [one_mul]; exact read_at 10 #v[1, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 11) = some (E.ofLimbs (gpow 6) 0 0)
    rw [one_mul]; exact read_at 11 #v[gpow 6, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 12) = some (E.ofLimbs 1 0 0)
    rw [one_mul]; exact read_at 12 #v[1, 0, 0]

theorem jump0_bindings : JumpBindings (imageOf tabData).2 jumpRow0 := by
  refine ⟨?_, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * gpow 13) = some (E.ofLimbs 0 0 0)
    rw [one_mul]; exact read_at 13 #v[0, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 11) = some (E.ofLimbs (gpow 6) 0 0)
    rw [one_mul]; exact read_at 11 #v[gpow 6, 0, 0]
  · show (imageOf tabData).2.read (1 * gpow 12) = some (E.ofLimbs 1 0 0)
    rw [one_mul]; exact read_at 12 #v[1, 0, 0]

/-- `JumpSpec` on the taken row: the branch is taken, to `(g^6, 1)`. -/
theorem jump_spec : JumpSpec jumpRow ⟨gpow 6, 1⟩ tabData :=
  ⟨jump_bindings, by
    show execute (imageOf tabData).2 ⟨gpow 4, 1⟩ (.jump (gpow 10) (gpow 11) (gpow 12)) =
      some ⟨gpow 6, 1⟩
    simp only [execute, executeWith, one_mul, read_at 10 #v[1, 0, 0], read_at 11 #v[gpow 6, 0, 0],
      read_at 12 #v[1, 0, 0]]
    decide +kernel⟩

/-- `JumpSpec` on the untaken row: fall-through to `(g^9, 1)`. -/
theorem jump0_spec : JumpSpec jumpRow0 ⟨g * gpow 8, 1⟩ tabData :=
  ⟨jump0_bindings, by
    show execute (imageOf tabData).2 ⟨gpow 8, 1⟩ (.jump (gpow 13) (gpow 11) (gpow 12)) =
      some ⟨g * gpow 8, 1⟩
    simp only [execute, executeWith, one_mul, read_at 13 #v[0, 0, 0], read_at 11 #v[gpow 6, 0, 0],
      read_at 12 #v[1, 0, 0]]
    decide +kernel⟩

/-- Either valid execution alone yields a satisfying row, in its honest environment, witnesses
included; `jump_spec` and `jump0_spec` name the successors `main` returns. -/
example : ConstraintsHold.Completeness
    (jumpEnv tabData
      (jumpRowOf (imageOf tabData).2 (gpow 4) 1 (gpow 10) (gpow 11) (gpow 12) 1 1 1 1))
    ((jumpTable.main (const (jumpRowOf (imageOf tabData).2
      (gpow 4) 1 (gpow 10) (gpow 11) (gpow 12) 1 1 1 1))).operations 0) :=
  jump_exec_complete jump_spec.exec_eq 1 1 1 1

example : ConstraintsHold.Completeness
    (jumpEnv tabData
      (jumpRowOf (imageOf tabData).2 (gpow 8) 1 (gpow 13) (gpow 11) (gpow 12) 1 1 1 1))
    ((jumpTable.main (const (jumpRowOf (imageOf tabData).2
      (gpow 8) 1 (gpow 13) (gpow 11) (gpow 12) 1 1 1 1))).operations 0) :=
  jump_exec_complete jump0_spec.exec_eq 1 1 1 1

-- Clean's array generator computes the same two witnesses as `jumpEnv` holds: `w = 1⁻¹ = 1`,
-- `b = 1` on the taken row, `w = 0`, `b = 0` on the untaken one (compiled).
#guard (jumpTable.main (const jumpRow)).witgen default #[] = #[1, 1]
#guard (jumpTable.main (const jumpRow0)).witgen default #[] = #[0, 0]

example : (jumpEnv tabData jumpRow).get 0 = 1 ∧ (jumpEnv tabData jumpRow).get 1 = 1 := by
  decide +kernel

/-- With `v_cond = 0` the two residuals `main` asserts force `b = 0`, whatever the inverse `w`:
booleanity of `b` alone would have accepted `b = 1`. -/
example (w b : K) (h1 : b + 0 * w = 0) (h2 : 0 * (b + 1) = 0) : b = 0 := by
  simpa using flags_sound h1 h2

/-! ## `BLAKE2S` -/

/-- The honest `BLAKE2S` row at `pc = g^5`: the executor's cells at `g^16 … g^24`. -/
def blake2sRow : Blake2sRow K :=
  ⟨gpow 5, 1, gpow 16, gpow 17, gpow 18, gpow 19, gpow 20, gpow 22, gpow 24,
    rustM0, rustM1, rustM2, rustM3, rustOut0, rustOut1, rustCv0, rustCv1, rustMd,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

/-- A canonical cell read at `1 · g^k` of a well-shaped thirty-two-word data. -/
theorem readCell {data : ProverData K} (hlog : (imageOf data).1 = 5) (hws : WellShapedData data)
    (k : ℕ) (c : Vector K 2) (hk : k < 32 := by decide)
    (hv : (memRows data)[k]'(by rw [hws.memRows_size, hlog]; exact hk) = cell c :=
      by decide +kernel) :
    (imageOf data).2.read (1 * gpow k) = some (E.ofCell c) := by
  rw [one_mul]; exact readAt hlog hws k (cell c) hk hv

/-- The nine cell reads of a row over a well-shaped data whose cells at `16..24` are the row's:
the binding. -/
theorem blake2s_reads {data : ProverData K} (hlog : (imageOf data).1 = 5)
    (hws : WellShapedData data) (r : Blake2sRow K)
    (hr : r = ⟨gpow 5, 1, gpow 16, gpow 17, gpow 18, gpow 19, gpow 20, gpow 22, gpow 24,
      r.m0, r.m1, r.m2, r.m3, r.out0, r.out1, r.cv0, r.cv1, r.md, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩)
    (h16 : (memRows data)[16]'(by rw [hws.memRows_size, hlog]; decide) = cell r.m0)
    (h17 : (memRows data)[17]'(by rw [hws.memRows_size, hlog]; decide) = cell r.m1)
    (h18 : (memRows data)[18]'(by rw [hws.memRows_size, hlog]; decide) = cell r.m2)
    (h19 : (memRows data)[19]'(by rw [hws.memRows_size, hlog]; decide) = cell r.m3)
    (h20 : (memRows data)[20]'(by rw [hws.memRows_size, hlog]; decide) = cell r.cv0)
    (h21 : (memRows data)[21]'(by rw [hws.memRows_size, hlog]; decide) = cell r.cv1)
    (h22 : (memRows data)[22]'(by rw [hws.memRows_size, hlog]; decide) = cell r.out0)
    (h23 : (memRows data)[23]'(by rw [hws.memRows_size, hlog]; decide) = cell r.out1)
    (h24 : (memRows data)[24]'(by rw [hws.memRows_size, hlog]; decide) = cell r.md) :
    Blake2sBindings (imageOf data).2 r := by
  rw [hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact readCell hlog hws 16 r.m0 (by decide) h16
  · exact readCell hlog hws 17 r.m1 (by decide) h17
  · exact readCell hlog hws 18 r.m2 (by decide) h18
  · exact readCell hlog hws 19 r.m3 (by decide) h19
  · exact readCell hlog hws 20 r.cv0 (by decide) h20
  · show (imageOf data).2.read (1 * (g * gpow 20)) = some (E.ofCell r.cv1)
    rw [g_mul_gpow]; exact readCell hlog hws 21 r.cv1 (by decide) h21
  · exact readCell hlog hws 22 r.out0 (by decide) h22
  · show (imageOf data).2.read (1 * (g * gpow 22)) = some (E.ofCell r.out1)
    rw [g_mul_gpow]; exact readCell hlog hws 23 r.out1 (by decide) h23
  · exact readCell hlog hws 24 r.md (by decide) h24

theorem blake2s_bindings : Blake2sBindings (imageOf tabData).2 blake2sRow :=
  blake2s_reads (dataOf_logSize rfl) (dataOf_wellShaped rfl) blake2sRow rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The named assumption holds of the honest row: the executor's cells compress. -/
theorem blake2s_relation : Blake2sRelation blake2sRow := by
  show CompressCells _ _ _ _ _ _
  decide +kernel

/-- `Blake2sSpec` on the honest row, through `blake2s_refines_iff`: bound, compressing, and the
successor is `(g · g^5, 1)`. -/
theorem blake2s_spec : Blake2sSpec blake2sRow ⟨g * gpow 5, 1⟩ tabData :=
  (blake2s_refines_iff _ _ _).mpr ⟨blake2s_bindings, blake2s_relation, rfl⟩

/-- …and its execution, decided in the kernel directly. -/
example : execute (imageOf tabData).2 ⟨gpow 5, 1⟩
    (.blake2s ![gpow 16, gpow 17, gpow 18, gpow 19] (gpow 20) (gpow 22) (gpow 24)) =
      some ⟨g * gpow 5, 1⟩ := by
  simp only [execute, executeWith, one_mul, g_mul_gpow, Matrix.cons_val, Fin.isValue, read_at 16 (cell rustM0),
    read_at 17 (cell rustM1), read_at 18 (cell rustM2), read_at 19 (cell rustM3),
    read_at 20 (cell rustCv0), read_at 21 (cell rustCv1), read_at 22 (cell rustOut0),
    read_at 23 (cell rustOut1), read_at 24 (cell rustMd), Option.bind_eq_bind, Option.bind_some]
  decide +kernel

/-- The honest row is bound, so locally complete: `main` accepts it without checking the
compression. -/
example : ConstraintsHold.Completeness (rowEnv tabData)
    ((blake2sTable.main (const blake2sRow)).operations 0) :=
  blake2sRow_complete blake2s_bindings

/-- The valid execution alone yields a satisfying row. -/
example : ConstraintsHold.Completeness (rowEnv tabData)
    ((blake2sTable.main (const (blake2sRowOf (imageOf tabData).2 (gpow 5) 1 (gpow 16) (gpow 17)
      (gpow 18) (gpow 19) (gpow 20) (gpow 22) (gpow 24) 1 1 1 1 1 1 1 1 1 1))).operations 0) :=
  blake2s_exec_complete blake2s_spec.exec_eq 1 1 1 1 1 1 1 1 1 1

/-- A non-canonical cell is rejected: an image whose second output cell has
a nonzero top limb does not balance the row's canonical read of it, so the constraints `main`
emits on the honest row fail in every environment over that image. -/
def badMem : Array (Vector K 3) := memTable.set! 23 #v[rustOut1[0], rustOut1[1], 1]

example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, dataOf badMem⟩
      ((blake2sTable.main (const blake2sRow)).operations 0) := by
  intro h
  have hs : Blake2sSpec blake2sRow _ (dataOf badMem) :=
    (blake2sTable.soundness 0 ⟨get, dataOf badMem⟩ (const blake2sRow) blake2sRow
      ProvableType.eval_const blake2s_relation h).1
  obtain ⟨⟨-, -, -, -, -, -, -, hout1, -⟩, -⟩ := hs
  rw [show blake2sRow.fp * (g * blake2sRow.oout) = 1 * (g * gpow 22) from rfl, one_mul,
    g_mul_gpow, readAt (dataOf_logSize (mem := badMem) rfl) (dataOf_wellShaped rfl) 23
      #v[rustOut1[0], rustOut1[1], 1]] at hout1
  exact absurd (Option.some.inj hout1) (by decide +kernel)

/-- The boundary with Flock: an output cell holding a wrong but canonical word, consistently in
the row and in the image. The row is bound and locally complete, and it fails the compression
relation and the functional specification: that failure is Flock's to enforce. -/
def wrongOut1 : Vector K 2 := #v[rustOut1[0], rustOut1[1] + 1]

def wrongMem : Array (Vector K 3) := memTable.set! 23 (cell wrongOut1)

def blake2sRow' : Blake2sRow K := { blake2sRow with out1 := wrongOut1 }

theorem blake2s'_bindings : Blake2sBindings (imageOf (dataOf wrongMem)).2 blake2sRow' :=
  blake2s_reads (dataOf_logSize (mem := wrongMem) rfl) (dataOf_wellShaped rfl) blake2sRow' rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : ConstraintsHold.Completeness (rowEnv (dataOf wrongMem))
    ((blake2sTable.main (const blake2sRow')).operations 0) :=
  blake2sRow_complete blake2s'_bindings

theorem blake2s'_no_relation : ¬ Blake2sRelation blake2sRow' := by
  show ¬ CompressCells _ _ _ _ _ _
  decide +kernel

example (next : Regs K) : ¬ Blake2sSpec blake2sRow' next (dataOf wrongMem) := fun h ↦
  blake2s'_no_relation ((blake2s_refines_iff _ _ _).mp h).2.1

end LeanVMTests.Arithmetization.Tables
