import LeanVM.Arithmetization.Tables.Xor
import LeanVM.Arithmetization.Tables.MulNative
import LeanVM.Arithmetization.Tables.SetConstant
import LeanVM.Arithmetization.Tables.Deref
import LeanVM.Arithmetization.Tables.Jump
import LeanVM.Arithmetization.Tables.Keccak
import Clean.Circuit.WitnessGeneration

/-!
# Tests: the six opcode tables

A classic test for kernel evaluation: the fixtures decide `E` arithmetic and `Regs`
equalities in the kernel. One prover data serves the five small tables: a thirty-two-word image
(`κ = 5`) holding the cells of one instruction per opcode, a `DEREF` in each of the three store
modes and a `JUMP` on each branch, read through `imageOf` at literal indices as in the channel
tests; `KECCAK`, whose row reads twenty-six cells, has a thirty-two-word image of its own. There is no program fixture: the tables are program-free, each row naming
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
(`SET_CONSTANT`, which the cell does not hold), and an image cell with a nonzero free limb (`KECCAK`)
fail the constraints `main` emits in every environment over the data, read
back through each table's `soundness`; the two `JUMP` residuals reject the wrong witness `b = 1`
at `v_cond = 0` (`flags_sound`). What a table does not reject is a row
naming an instruction the program does not hold at its counter (an `XOR` row at `pc = g^2`
with honest reads is accepted): that is the bus's, as it is for leanVM's AIRs, and the
boundary tests reject it at the block. The `KECCAK` boundary: a bound row whose output lane is
a wrong but canonical word, consistently in row and image, is locally complete (the table's
`completeness`) and fails `KeccakRelation` and `KeccakSpec`, the failure the Keccak reduction
(the verifier's GKR over the rounds) enforces.

The `MUL_NATIVE` row reproduces the executor's `mul_128bit_word` product (`cpu/mod.rs:873-890`)
from the twelve-product coordinates (test at leanVM `a386121f`), and the `KECCAK` row the first
permutation of the executor's `keccak_permutes_in_both_layouts` (`cpu/mod.rs:842-875` at leanVM
`4af2cddd`): even layout in, odd layout out, the output lanes Keccak-f[1600] as the pinned
verifier's `keccak_f` (`crates/verifier/src/hash.rs:50-69`) computes it.
-/

namespace LeanVMTests.Arithmetization.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization

/-! ## The fixture: one image -/

-- The executor test `mul_128bit_word` (`cpu/mod.rs:853-869`): the operands `x`, `y`
-- and the product `x · y`.
def x0 : K := (K.ofBits 0x0123456789abcdef)
def x1 : K := (K.ofBits 0xfeedfacedeadbeef)
def y0 : K := (K.ofBits 0x9999aaaabbbbcccc)
def y1 : K := (K.ofBits 0x13579bdf2468ace0)
def mulXY : E := E.ofLimbs (K.ofBits 0x1b4ac62c35ac2ecc) (K.ofBits 0x421e3037aaa197d0)

/-- The four-product coordinates of `x · y` (`TOWER_LANES`). -/
def xyLanes : Vector K 2 := #v[x0 * y0 + x1 * y1, x0 * y1 + x1 * y0 + g * (x1 * y1)]

/-- The image, thirty-two words: `x`, `y`, `x + y`, `x · y` at `2..5`; the `SET` immediate at
`6`; the `pc`-mode `DEREF` pointer `g^8` at `7`, its target `g²·g³` (the return address of
`pc = g^3`) at `8`, its local cell at `9`; the `JUMP` cells `c = 1`, `d = g^6`, `f = 1` at
`10..12` and the untaken condition `c = 0` at `13`; zero at `16..24`; the
`cell`-mode `DEREF` pointer `g^26` at `25`, its target at `26` holding the local word at `27`;
the `fp`-mode `DEREF` pointer `g^29` at `28`, its target at `29` holding `fp = 1`, its local cell
at `30`; zero elsewhere. -/
def memTable : Array (Vector K 2) :=
  #[#v[0, 0], #v[0, 0],
    #v[x0, x1], #v[y0, y1], #v[x0 + y0, x1 + y1], xyLanes,
    #v[K.ofBits 7, K.ofBits 8],
    #v[addressOfIndex 8, 0], #v[g ^ 2 * addressOfIndex 3, 0], #v[K.ofBits 5, K.ofBits 6],
    #v[1, 0], #v[addressOfIndex 6, 0], #v[1, 0],
    #v[0, 0], #v[0, 0], #v[0, 0],
    #v[0, 0], #v[0, 0], #v[0, 0], #v[0, 0], #v[0, 0], #v[0, 0],
    #v[0, 0], #v[0, 0], #v[0, 0],
    #v[addressOfIndex 26, 0], #v[K.ofBits 3, K.ofBits 4], #v[K.ofBits 3, K.ofBits 4],
    #v[addressOfIndex 29, 0], #v[1, 0], #v[K.ofBits 9, K.ofBits 9],
    #v[0, 0]]

/-- The prover data of an image, its one table matched on arity so that the kernel never
compares names (as in the channel tests). -/
def dataOf (mem : Array (Vector K 2)) : ProverData K := fun _ n ↦
  match n with
  | 2 => mem
  | _ => #[]

/-- The fixture's prover data. -/
def tabData : ProverData K := dataOf memTable

theorem dataOf_logSize {mem : Array (Vector K 2)} (h : mem.size = 32) :
    (imageOf (dataOf mem)).1 = 5 := by
  show min (Nat.log 2 (memRows (dataOf mem)).size) maxLogMem = 5
  rw [show memRows (dataOf mem) = mem from rfl, h, show (32 : ℕ) = 2 ^ 5 by decide,
    Nat.log_pow (by norm_num)]
  decide

theorem dataOf_wellShaped {mem : Array (Vector K 2)} (h : mem.size = 32) :
    WellShapedData (dataOf mem) where
  memRows_size := by rw [dataOf_logSize h]; exact h

/-- On a well-shaped thirty-two-word data, the word at `g^k` is row `k` of the image, as
limbs. -/
theorem readAt {data : ProverData K} (hlog : (imageOf data).1 = 5) (hws : WellShapedData data)
    (k : ℕ) (v : Vector K 2) (hk : k < 32 := by decide)
    (hv : (memRows data)[k]'(by rw [hws.memRows_size, hlog]; exact hk) = v := by decide +kernel) :
    (imageOf data).2.read (addressOfIndex k) = some (E.ofLimbs v[0] v[1]) := by
  have hk' : k < 2 ^ (imageOf data).1 := by rw [hlog]; omega
  rw [show addressOfIndex k = addressOfIndex ((⟨k, hk'⟩ : Fin (2 ^ (imageOf data).1)) : ℕ) from rfl,
    MemoryImage.read_gpow (by rw [hlog]; decide), imageOf_apply hws _ hv]

/-- The word at `g^k` of the fixture's image. -/
theorem read_at (k : ℕ) (v : Vector K 2) (hk : k < 32 := by decide)
    (hv : memTable[k]'(by rw [show memTable.size = 32 from rfl]; exact hk) = v :=
      by decide +kernel) :
    (imageOf tabData).2.read (addressOfIndex k) = some (E.ofLimbs v[0] v[1]) :=
  readAt (dataOf_logSize rfl) (dataOf_wellShaped rfl) k v hk hv

/-- `read_at` with the word's two limbs spelled out, for the kernel fixtures. -/
theorem read_lit (k : ℕ) (a b : K) (hk : k < 32 := by decide)
    (hv : memTable[k]'(by rw [show memTable.size = 32 from rfl]; exact hk) = #v[a, b] :=
      by decide +kernel) :
    (imageOf tabData).2.read (addressOfIndex k) = some (E.ofLimbs a b) :=
  read_at k #v[a, b] hk hv

/-- `g · g^k = g^(k + 1)`, oriented for `simp`. -/
theorem g_mul_gpow (k : ℕ) : g * addressOfIndex k = addressOfIndex (k + 1) := (gpow_succ k).symm

/-! ## `XOR` -/

/-- The honest `XOR` row at `pc = g^0`, `fp = 1`: operands `g^2, g^3, g^4`, the words `x`, `y`. -/
def xorRow : XorRow K :=
  ⟨addressOfIndex 0, 1, addressOfIndex 2, addressOfIndex 3, addressOfIndex 4, #v[x0, x1], #v[y0,
      y1], 1, 1, 1, 1⟩

/-- The honest row is bound: the two operand words are the fixture's. -/
theorem xor_bindings : XorBindings (imageOf tabData).2 xorRow := by
  refine ⟨?_, ?_⟩
  · show (imageOf tabData).2.read (1 * addressOfIndex 2) = some (E.ofLimbs x0 x1)
    rw [one_mul]; exact read_at 2 #v[x0, x1]
  · show (imageOf tabData).2.read (1 * addressOfIndex 3) = some (E.ofLimbs y0 y1)
    rw [one_mul]; exact read_at 3 #v[y0, y1]

/-- `XorSpec` on the honest row: bound, and `XOR g^2 g^3 g^4` executes from `(1, 1)` to
`(g, 1)`. -/
theorem xor_spec : XorSpec xorRow ⟨g * addressOfIndex 0, 1⟩ tabData :=
  ⟨xor_bindings, by
    show execute (imageOf tabData).2 ⟨addressOfIndex 0, 1⟩ (.xor (addressOfIndex 2) (addressOfIndex
        3) (addressOfIndex 4)) =
      some ⟨g * addressOfIndex 0, 1⟩
    simp only [execute, executeWith, one_mul, read_at 2 #v[x0, x1], read_at 3 #v[y0, y1],
      read_at 4 #v[x0 + y0, x1 + y1]]
    decide +kernel⟩

/-- The valid execution alone yields a satisfying row (`xor_exec_complete`): no assumption on
the row, the honest prover builds it; `xor_spec` names the successor `main` returns. -/
example : ConstraintsHold.Completeness (rowEnv tabData)
    ((xorTable.main (const (xorRowOf (imageOf tabData).2
      (addressOfIndex 0) 1 (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4) 1 1 1
          1))).operations 0) :=
  xor_exec_complete xor_spec.exec_eq 1 1 1 1

/-- The table is program-free: the same honest reads at `pc = g^2`, a counter
whose instruction in the boundary tests' kind of program would be a `SET`, satisfy `XorSpec`
all the same. Which instruction the program holds at a counter is the bus's to check,
as it is for leanVM's `XOR` AIR. -/
def xorRow2 : XorRow K := { xorRow with pc := addressOfIndex 2 }

example : XorSpec xorRow2 ⟨g * addressOfIndex 2, 1⟩ tabData :=
  ⟨⟨xor_bindings.readA_eq, xor_bindings.readB_eq⟩, by
    show execute (imageOf tabData).2 ⟨addressOfIndex 2, 1⟩ (.xor (addressOfIndex 2) (addressOfIndex
        3) (addressOfIndex 4)) =
      some ⟨g * addressOfIndex 2, 1⟩
    simp only [execute, executeWith, one_mul, read_at 2 #v[x0, x1], read_at 3 #v[y0, y1],
      read_at 4 #v[x0 + y0, x1 + y1]]
    decide +kernel⟩

/-- An alleged `XOR` row with operands `0` fails `XorSpec` for every successor: the address `0`
reads nothing. Its counter plays no part. -/
def bogusXor : XorRow K :=
  { xorRow with pc := addressOfIndex 2, oA := 0, oB := 0, oC := 0, vA := #v[0, 0] }

example (next : Registers K) : ¬ XorSpec bogusXor next tabData := by
  rintro ⟨⟨hA, -⟩, -⟩
  rw [show bogusXor.fp * bogusXor.oA = 0 from mul_zero 1, MemoryImage.read_zero] at hA
  cases hA

/-- A changed input limb: `execute` from the registers is unchanged, the bindings fail. -/
def xorRow' : XorRow K := { xorRow with vA := #v[x0 + 1, x1] }

example (next : Registers K) : ¬ XorSpec xorRow' next tabData := by
  rintro ⟨⟨hA, -⟩, -⟩
  rw [show xorRow'.fp * xorRow'.oA = 1 * addressOfIndex 2 from rfl, one_mul, read_at 2 #v[x0, x1]] at hA
  exact absurd (Option.some.inj hA) (by decide +kernel)

/-- …so the constraints `main` emits on it fail in every environment over the fixture: its
second pull is no read of the image (`soundness`, read back). -/
example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, tabData⟩ ((xorTable.main (const xorRow')).operations 0) := by
  intro h
  have hs : XorSpec xorRow' _ tabData := (xorTable.soundness 0 ⟨get, tabData⟩ (const xorRow')
    xorRow' ProvableType.eval_const trivial h).1
  obtain ⟨⟨hA, -⟩, -⟩ := hs
  rw [show xorRow'.fp * xorRow'.oA = 1 * addressOfIndex 2 from rfl, one_mul, read_at 2 #v[x0, x1]] at hA
  exact absurd (Option.some.inj hA) (by decide +kernel)

/-! ## `MUL_NATIVE` -/

/-- The four-product coordinates of the Rust operands are the Rust product. -/
example : E.ofLimbs xyLanes[0] xyLanes[1] = mulXY := by decide +kernel

/-- The honest `MUL_NATIVE` row at `pc = g^1`. -/
def mulRow : MulRow K :=
  ⟨addressOfIndex 1, 1, addressOfIndex 2, addressOfIndex 3, addressOfIndex 5, #v[x0, x1], #v[y0,
      y1], 1, 1, 1, 1⟩

theorem mul_bindings : MulBindings (imageOf tabData).2 mulRow := by
  refine ⟨?_, ?_⟩
  · show (imageOf tabData).2.read (1 * addressOfIndex 2) = some (E.ofLimbs x0 x1)
    rw [one_mul]; exact read_at 2 #v[x0, x1]
  · show (imageOf tabData).2.read (1 * addressOfIndex 3) = some (E.ofLimbs y0 y1)
    rw [one_mul]; exact read_at 3 #v[y0, y1]

/-- `MulSpec` on the honest row, through the product of the Rust vectors. -/
theorem mul_spec : MulSpec mulRow ⟨g * addressOfIndex 1, 1⟩ tabData :=
  ⟨mul_bindings, by
    show execute (imageOf tabData).2 ⟨addressOfIndex 1, 1⟩ (.mulNative (addressOfIndex 2)
        (addressOfIndex 3) (addressOfIndex 5)) =
      some ⟨g * addressOfIndex 1, 1⟩
    simp only [execute, executeWith, one_mul, read_at 2 #v[x0, x1], read_at 3 #v[y0, y1],
      read_at 5 xyLanes]
    decide +kernel⟩

example : ConstraintsHold.Completeness (rowEnv tabData)
    ((mulTable.main (const (mulRowOf (imageOf tabData).2
      (addressOfIndex 1) 1 (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 5) 1 1 1
          1))).operations 0) :=
  mul_exec_complete mul_spec.exec_eq 1 1 1 1

/-- A changed input limb fails the bindings, and the constraints in every environment. -/
def mulRow' : MulRow K := { mulRow with vB := #v[y0, y1 + 1] }

example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, tabData⟩ ((mulTable.main (const mulRow')).operations 0) := by
  intro h
  have hs : MulSpec mulRow' _ tabData := (mulTable.soundness 0 ⟨get, tabData⟩ (const mulRow')
    mulRow' ProvableType.eval_const trivial h).1
  obtain ⟨⟨-, hB⟩, -⟩ := hs
  rw [show mulRow'.fp * mulRow'.oB = 1 * addressOfIndex 3 from rfl, one_mul, read_at 3 #v[y0, y1]] at hB
  exact absurd (Option.some.inj hB) (by decide +kernel)

/-! ## `SET_CONSTANT` -/

/-- The honest `SET_CONSTANT` row at `pc = g^2`: the immediate `7 + 8·y` at `g^6`. -/
def setRow : SetRow K := ⟨addressOfIndex 2, 1, addressOfIndex 6, #v[K.ofBits 7, K.ofBits 8], 1, 1⟩

/-- `SetSpec` on the honest row: `SET_CONSTANT g^6 (7 + 8·y)` executes, the cell holding
the immediate. -/
theorem set_spec : SetSpec setRow ⟨g * addressOfIndex 2, 1⟩ tabData :=
  ⟨by
    show execute (imageOf tabData).2 ⟨addressOfIndex 2, 1⟩ (.setConstant (addressOfIndex 6) (E.ofLimbs (K.ofBits 7) (K.ofBits 8))) =
      some ⟨g * addressOfIndex 2, 1⟩
    simp only [execute, executeWith, one_mul, read_at 6 #v[K.ofBits 7, K.ofBits 8]]
    decide +kernel⟩

example : ConstraintsHold.Completeness (rowEnv tabData)
    ((setTable.main (const (setRowOf (addressOfIndex 2) 1 (addressOfIndex 6) (E.ofLimbs (K.ofBits 7) (K.ofBits 8)) 1 1))).operations 0) :=
  set_exec_complete set_spec.exec_eq 1 1

/-- A changed immediate limb: the cell `fp·o` does not hold the row's immediate, so the row
fails `SetRefines` and the constraints fail in every environment. (Whether the program holds
this immediate at `g^2` is the bus's to check.) -/
def setRow' : SetRow K := { setRow with k := #v[K.ofBits 7, K.ofBits 10] }

example (next : Registers K) : ¬ SetSpec setRow' next tabData := by
  intro h
  obtain ⟨hk, -⟩ := (set_refines_iff _ _ _).mp h
  rw [show setRow'.fp * setRow'.o = 1 * addressOfIndex 6 from rfl, one_mul, read_at 6 #v[K.ofBits 7, K.ofBits 8]] at hk
  exact absurd (Option.some.inj hk) (by decide +kernel)

example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, tabData⟩ ((setTable.main (const setRow')).operations 0) := by
  intro h
  have hs : SetSpec setRow' _ tabData := (setTable.soundness 0 ⟨get, tabData⟩ (const setRow')
    setRow' ProvableType.eval_const trivial h).1
  obtain ⟨hk, -⟩ := (set_refines_iff _ _ _).mp hs
  rw [show setRow'.fp * setRow'.o = 1 * addressOfIndex 6 from rfl, one_mul, read_at 6 #v[K.ofBits 7, K.ofBits 8]] at hk
  exact absurd (Option.some.inj hk) (by decide +kernel)

/-! ## `DEREF` -/

/-- The honest `DEREF` row at `pc = g^3` in `pc` mode (`f_pc = 1`, `f_fp = 0`): pointer `g^8`
at `g^7`, local cell `g^9`, target `g^8 · 1` holding `g² · g^3`. -/
def derefRow : DerefRow K :=
  ⟨addressOfIndex 3, 1, addressOfIndex 7, 1, addressOfIndex 9, 1, 0, addressOfIndex 8, #v[K.ofBits
      5, K.ofBits 6], 1, 1, 1, 1⟩

/-- The `cell`-mode row at `pc = g^6`: pointer `g^26` at `g^25`, local cell `g^27`, target
`g^26 · 1` holding the local word. -/
def derefCellRow : DerefRow K :=
  ⟨addressOfIndex 6, 1, addressOfIndex 25, 1, addressOfIndex 27, 0, 0, addressOfIndex 26, #v[K.ofBits 3, K.ofBits 4], 1, 1, 1, 1⟩

/-- The `fp`-mode row at `pc = g^7`: pointer `g^29` at `g^28`, local cell `g^30` (read, not
stored), target `g^29 · 1` holding `fp = 1`. -/
def derefFpRow : DerefRow K :=
  ⟨addressOfIndex 7, 1, addressOfIndex 28, 1, addressOfIndex 30, 0, 1, addressOfIndex 29, #v[K.ofBits 9, K.ofBits 9], 1, 1, 1, 1⟩

theorem deref_bindings : DerefBindings (imageOf tabData).2 derefRow .pc := by
  refine ⟨rfl, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * addressOfIndex 7) = some (E.ofLimbs (addressOfIndex 8) 0)
    rw [one_mul]; exact read_at 7 #v[addressOfIndex 8, 0]
  · show (imageOf tabData).2.read (1 * addressOfIndex 9) = some (E.ofLimbs (K.ofBits 5) (K.ofBits 6))
    rw [one_mul]; exact read_at 9 #v[K.ofBits 5, K.ofBits 6]

theorem derefCell_bindings : DerefBindings (imageOf tabData).2 derefCellRow .cell := by
  refine ⟨rfl, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * addressOfIndex 25) = some (E.ofLimbs (addressOfIndex 26) 0)
    rw [one_mul]; exact read_at 25 #v[addressOfIndex 26, 0]
  · show (imageOf tabData).2.read (1 * addressOfIndex 27) = some (E.ofLimbs (K.ofBits 3) (K.ofBits 4))
    rw [one_mul]; exact read_at 27 #v[K.ofBits 3, K.ofBits 4]

theorem derefFp_bindings : DerefBindings (imageOf tabData).2 derefFpRow .fp := by
  refine ⟨rfl, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * addressOfIndex 28) = some (E.ofLimbs (addressOfIndex 29) 0)
    rw [one_mul]; exact read_at 28 #v[addressOfIndex 29, 0]
  · show (imageOf tabData).2.read (1 * addressOfIndex 30) = some (E.ofLimbs (K.ofBits 9) (K.ofBits 9))
    rw [one_mul]; exact read_at 30 #v[K.ofBits 9, K.ofBits 9]

/-- `DEREF g^7 1 g^9` in `pc` mode executes from `(g^3, 1)`: the target holds the return address
`g² · g^3`. -/
theorem deref_exec :
    execute (imageOf tabData).2 ⟨addressOfIndex 3, 1⟩ (.deref (addressOfIndex 7) 1 (addressOfIndex
        9) .pc) =
      some ⟨g * addressOfIndex 3, 1⟩ := by
  simp only [execute, executeWith, one_mul, mul_one, read_lit 7 (addressOfIndex 8) 0,
      Option.bind_eq_bind,
    Option.bind_some, guard, isInK_ofLimbs, ite_true, limb_ofLimbs, Matrix.cons_val_zero,
    read_lit 9 (K.ofBits 5) (K.ofBits 6), read_lit 8 (g ^ 2 * addressOfIndex 3) 0, derefSource, ofK_eq_ofLimbs]
  decide +kernel

/-- In `cell` mode from `(g^6, 1)`: the target holds the local word. -/
theorem derefCell_exec :
    execute (imageOf tabData).2 ⟨addressOfIndex 6, 1⟩ (.deref (addressOfIndex 25) 1 (addressOfIndex
        27) .cell) =
      some ⟨g * addressOfIndex 6, 1⟩ := by
  simp only [execute, executeWith, one_mul, mul_one, read_lit 25 (addressOfIndex 26) 0,
      Option.bind_eq_bind,
    Option.bind_some, guard, isInK_ofLimbs, ite_true, limb_ofLimbs, Matrix.cons_val_zero,
    read_lit 27 (K.ofBits 3) (K.ofBits 4), read_lit 26 (K.ofBits 3) (K.ofBits 4), derefSource]
  decide +kernel

/-- In `fp` mode from `(g^7, 1)`: the target holds `fp = 1`; the local cell is read all the
same. -/
theorem derefFp_exec :
    execute (imageOf tabData).2 ⟨addressOfIndex 7, 1⟩ (.deref (addressOfIndex 28) 1 (addressOfIndex
        30) .fp) =
      some ⟨g * addressOfIndex 7, 1⟩ := by
  simp only [execute, executeWith, one_mul, mul_one, read_lit 28 (addressOfIndex 29) 0,
      Option.bind_eq_bind,
    Option.bind_some, guard, isInK_ofLimbs, ite_true, limb_ofLimbs, Matrix.cons_val_zero,
    read_lit 30 (K.ofBits 9) (K.ofBits 9), read_lit 29 1 0, derefSource, ofK_eq_ofLimbs]
  decide +kernel

/-- `DerefSpec` in each store mode: the bindings and the execution, with the same mode. -/
theorem deref_spec : DerefSpec derefRow ⟨g * addressOfIndex 3, 1⟩ tabData :=
  ⟨.pc, deref_bindings, deref_exec⟩

theorem derefCell_spec : DerefSpec derefCellRow ⟨g * addressOfIndex 6, 1⟩ tabData :=
  ⟨.cell, derefCell_bindings, derefCell_exec⟩

theorem derefFp_spec : DerefSpec derefFpRow ⟨g * addressOfIndex 7, 1⟩ tabData :=
  ⟨.fp, derefFp_bindings, derefFp_exec⟩

/-- A valid execution in each store mode alone yields a satisfying row
(`deref_exec_complete`); its successor is the one `DerefSpec` names. -/
example : ConstraintsHold.Completeness (rowEnv tabData)
    ((derefTable.main (const (derefRowOf (imageOf tabData).2
      (addressOfIndex 3) 1 (addressOfIndex 7) 1 (addressOfIndex 9) .pc 1 1 1 1))).operations 0) :=
  deref_exec_complete deref_exec 1 1 1 1

example : ConstraintsHold.Completeness (rowEnv tabData)
    ((derefTable.main (const (derefRowOf (imageOf tabData).2
      (addressOfIndex 6) 1 (addressOfIndex 25) 1 (addressOfIndex 27) .cell 1 1 1
          1))).operations 0) :=
  deref_exec_complete derefCell_exec 1 1 1 1

example : ConstraintsHold.Completeness (rowEnv tabData)
    ((derefTable.main (const (derefRowOf (imageOf tabData).2
      (addressOfIndex 7) 1 (addressOfIndex 28) 1 (addressOfIndex 30) .fp 1 1 1 1))).operations 0) :=
  deref_exec_complete derefFp_exec 1 1 1 1

/-- The counterexample to a step-only contract: the honest row with the flag pair
`(1, 1)` executes the `pc`-mode instruction from its registers (the flags are no input of
`execute`)… -/
def invalidDeref : DerefRow K := { derefRow with fpc := 1, ffp := 1 }

example : execute (imageOf tabData).2 ⟨invalidDeref.pc, invalidDeref.fp⟩
    (.deref (addressOfIndex 7) 1 (addressOfIndex 9) .pc) = some ⟨g * addressOfIndex 3, 1⟩ :=
  deref_exec

/-- …and fails `DerefSpec` for every successor: `(1, 1)` is no store mode's flags. -/
example (next : Registers K) : ¬ DerefSpec invalidDeref next tabData := by
  rintro ⟨mode, ⟨hflags, -, -⟩, -⟩
  cases mode <;> exact absurd hflags (by decide +kernel)

/-- The flag pair `(1, 1)` cannot be pulled either: its bytecode tuple decodes to nothing, at
this counter or any other and over any data. -/
example (pc : K) (data : ProverData K) :
    ¬ BytecodePull.Guarantees ⟨pc, 1, Opcode.deref.busCode, #v[addressOfIndex 7, 1, addressOfIndex
        9, 1, 1, 0, 0, 0, 0, 0, 0, 0]⟩
      data := by
  rintro ⟨ins, hdec⟩
  have h : decode (#v[Opcode.deref.busCode] ++ #v[addressOfIndex 7, 1, addressOfIndex 9, 1, 1, 0, 0,
      0, 0, 0, 0, 0]) = none := by
    decide +kernel
  exact nomatch h.symm.trans hdec

/-! ## `JUMP` -/

/-- The honest `JUMP` row at `pc = g^4`, taken: `c = 1`, `d = g^6`, `f = 1`. -/
def jumpRow : JumpRow K := ⟨addressOfIndex 4, 1, addressOfIndex 10, addressOfIndex 11,
    addressOfIndex 12, 1, addressOfIndex 6, 1, 1, 1, 1, 1⟩

/-- The untaken `JUMP` row at `pc = g^8`: `c = 0`, the same `d`, `f`. -/
def jumpRow0 : JumpRow K := ⟨addressOfIndex 8, 1, addressOfIndex 13, addressOfIndex 11,
    addressOfIndex 12, 0, addressOfIndex 6, 1, 1, 1, 1, 1⟩

theorem jump_bindings : JumpBindings (imageOf tabData).2 jumpRow := by
  refine ⟨?_, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * addressOfIndex 10) = some (E.ofLimbs 1 0)
    rw [one_mul]; exact read_at 10 #v[1, 0]
  · show (imageOf tabData).2.read (1 * addressOfIndex 11) = some (E.ofLimbs (addressOfIndex 6) 0)
    rw [one_mul]; exact read_at 11 #v[addressOfIndex 6, 0]
  · show (imageOf tabData).2.read (1 * addressOfIndex 12) = some (E.ofLimbs 1 0)
    rw [one_mul]; exact read_at 12 #v[1, 0]

theorem jump0_bindings : JumpBindings (imageOf tabData).2 jumpRow0 := by
  refine ⟨?_, ?_, ?_⟩
  · show (imageOf tabData).2.read (1 * addressOfIndex 13) = some (E.ofLimbs 0 0)
    rw [one_mul]; exact read_at 13 #v[0, 0]
  · show (imageOf tabData).2.read (1 * addressOfIndex 11) = some (E.ofLimbs (addressOfIndex 6) 0)
    rw [one_mul]; exact read_at 11 #v[addressOfIndex 6, 0]
  · show (imageOf tabData).2.read (1 * addressOfIndex 12) = some (E.ofLimbs 1 0)
    rw [one_mul]; exact read_at 12 #v[1, 0]

/-- `JumpSpec` on the taken row: the branch is taken, to `(g^6, 1)`. -/
theorem jump_spec : JumpSpec jumpRow ⟨addressOfIndex 6, 1⟩ tabData :=
  ⟨jump_bindings, by
    show execute (imageOf tabData).2 ⟨addressOfIndex 4, 1⟩ (.jump (addressOfIndex 10)
        (addressOfIndex 11) (addressOfIndex 12)) =
      some ⟨addressOfIndex 6, 1⟩
    simp only [execute, executeWith, one_mul, read_at 10 #v[1, 0], read_at 11 #v[addressOfIndex
        6, 0],
      read_at 12 #v[1, 0]]
    decide +kernel⟩

/-- `JumpSpec` on the untaken row: fall-through to `(g^9, 1)`. -/
theorem jump0_spec : JumpSpec jumpRow0 ⟨g * addressOfIndex 8, 1⟩ tabData :=
  ⟨jump0_bindings, by
    show execute (imageOf tabData).2 ⟨addressOfIndex 8, 1⟩ (.jump (addressOfIndex 13)
        (addressOfIndex 11) (addressOfIndex 12)) =
      some ⟨g * addressOfIndex 8, 1⟩
    simp only [execute, executeWith, one_mul, read_at 13 #v[0, 0], read_at 11 #v[addressOfIndex
        6, 0],
      read_at 12 #v[1, 0]]
    decide +kernel⟩

/-- Either valid execution alone yields a satisfying row, in its honest environment, witnesses
included; `jump_spec` and `jump0_spec` name the successors `main` returns. -/
example : ConstraintsHold.Completeness
    (jumpEnv tabData
      (jumpRowOf (imageOf tabData).2 (addressOfIndex 4) 1 (addressOfIndex 10) (addressOfIndex 11)
          (addressOfIndex 12) 1 1 1 1))
    ((jumpTable.main (const (jumpRowOf (imageOf tabData).2
      (addressOfIndex 4) 1 (addressOfIndex 10) (addressOfIndex 11) (addressOfIndex 12) 1 1 1
          1))).operations 0) :=
  jump_exec_complete jump_spec.exec_eq 1 1 1 1

example : ConstraintsHold.Completeness
    (jumpEnv tabData
      (jumpRowOf (imageOf tabData).2 (addressOfIndex 8) 1 (addressOfIndex 13) (addressOfIndex 11)
          (addressOfIndex 12) 1 1 1 1))
    ((jumpTable.main (const (jumpRowOf (imageOf tabData).2
      (addressOfIndex 8) 1 (addressOfIndex 13) (addressOfIndex 11) (addressOfIndex 12) 1 1 1
          1))).operations 0) :=
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

/-! ## `KECCAK` -/

-- The executor test `keccak_permutes_in_both_layouts` at leanVM 4af2cddd, its first permutation:
-- the input lanes (the words `a, b, a, b`, the padding's first byte in lane `8`, its last bit in
-- lane `16`, a zero capacity), and their image under `keccak_f` (`hash.rs:50-69`, computed
-- outside Lean).
def kLin : Vector K 25 :=
  #v[K.ofBits 0x123456789abcdef, K.ofBits 0xfedcba9876543210, K.ofBits 0xdeadbeefcafebabe,
    K.ofBits 0xbadf00d0badf00d, K.ofBits 0x123456789abcdef, K.ofBits 0xfedcba9876543210,
    K.ofBits 0xdeadbeefcafebabe, K.ofBits 0xbadf00d0badf00d, K.ofBits 0x1, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0,
    K.ofBits 0x8000000000000000, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0]

def kLout : Vector K 25 :=
  #v[K.ofBits 0x8dbfafed17b66d45, K.ofBits 0x30fd63be3bf8b935, K.ofBits 0x77167d7a851a2a5a,
    K.ofBits 0xd9174937e0d9005e, K.ofBits 0xa6a08643e0752e62, K.ofBits 0x96fa9d5eb49e3867,
    K.ofBits 0xd3075d1a22781d5, K.ofBits 0x81ae728bf7328686, K.ofBits 0xf51da81b6f1b6499,
    K.ofBits 0xdaf2a8af5b43dbf9, K.ofBits 0xdbf85b3cc1312641, K.ofBits 0x993d35c56291827e,
    K.ofBits 0x47fd59ac60e225e2, K.ofBits 0x36607d1d9e6abed, K.ofBits 0x6cee5561314ca0f3,
    K.ofBits 0x3e20ee955c09012e, K.ofBits 0x8a928dc9e22c3dcf, K.ofBits 0x7f24a1dac6837929,
    K.ofBits 0xd22b33eacce5fcd2, K.ofBits 0x2b1e71fdcd52b881, K.ofBits 0x427618061608ac91,
    K.ofBits 0x44c480aa40bfdbf9, K.ofBits 0x7a29ee993739ddb0, K.ofBits 0xf7f9aa87f90247d1,
    K.ofBits 0xe5177d767bf6bd92]

/-- Output cell `c` in the odd layout: lane `0` alone in the high limb of cell `0`, then the lane
pairs `(2c - 1, 2c)`. -/
def kOutCell (L : Vector K 25) (c : ℕ) : Vector K 2 :=
  if c = 0 then #v[0, L[0]] else #v[L.getD (2 * c - 1) 0, L.getD (2 * c) 0]

/-- The `KECCAK` image: `a, b` at `2, 3`, the tail at `4..7`, `b8` at `8` (its high limb
`0x5555`, which holds no lane in the even layout, is free), the zero capacity at `9..12`, and the
thirteen output cells at `13..25`. -/
def kMemOf (L : Vector K 25) : Array (Vector K 2) :=
  #[(#v[0, 0] : Vector K 2), #v[0, 0], #v[kLin[0], kLin[1]], #v[kLin[2], kLin[3]],
    #v[kLin[8], 0], #v[0, 0], #v[0, 0], #v[0, 0], #v[kLin[16], K.ofBits 0x5555],
    #v[0, 0], #v[0, 0], #v[0, 0], #v[0, 0]] ++
  (List.range 13).toArray.map (kOutCell L) ++ (List.replicate 6 (#v[0, 0] : Vector K 2)).toArray

def kMem : Array (Vector K 2) := kMemOf kLout

/-- The honest `KECCAK` row at `pc = g^5`, `fp = 1`: `m = [2, 3, 2, 3]`, `tail = 4`, `b8 = 8`,
`cap = 9`, `out = 13`, even in, odd out, all thirteen output cells written, the free limb
`0x5555`, every count `1`. -/
def keccakRow : KeccakRow K :=
  ⟨addressOfIndex 5, 1, #v[addressOfIndex 2, addressOfIndex 3, addressOfIndex 2, addressOfIndex 3],
      addressOfIndex 4, addressOfIndex 8, addressOfIndex 9, addressOfIndex 13, 0, 1, 1, 1,
    K.ofBits 0x5555, kLin, kLout, Vector.replicate 26 1, 1⟩

/-- The word at `g^k` of a thirty-two-word image, as a value `e` of its limbs. -/
theorem readMem (mem : Array (Vector K 2)) (hs : mem.size = 32) (k : ℕ) (hk : k < 32) (e : E)
    (h : E.ofLimbs (mem[k]'(by rw [hs]; exact hk))[0] (mem[k]'(by rw [hs]; exact hk))[1] = e) :
    (imageOf (dataOf mem)).2.read (addressOfIndex k) = some e :=
  (readAt (dataOf_logSize hs) (dataOf_wellShaped hs) k _ hk rfl).trans (congrArg some h)

/-- The memory index of read cell `c`. -/
def kInIdx : Fin 13 → ℕ := ![2, 3, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

theorem keccakRow_inOffset : ∀ c : Fin 13,
    keccakRow.fp * keccakInputCellOffset keccakRow.oms keccakRow.otail keccakRow.ob8
        keccakRow.ocap c =
      addressOfIndex (kInIdx c) := by
  decide +kernel

theorem keccakRow_outOffset : ∀ c : Fin 13,
    keccakRow.fp * (g ^ c.val * keccakRow.oout) = addressOfIndex (c.val + 13) := by
  decide +kernel

/-- The honest row is bound to the image. -/
theorem keccak_bindings : KeccakBindings (imageOf (dataOf kMem)).2 keccakRow false true .all := by
  refine ⟨fun c ↦ ?_, fun c _ ↦ ?_⟩
  · refine (congrArg (imageOf (dataOf kMem)).2.read (keccakRow_inOffset c)).trans ?_
    fin_cases c <;> exact readMem _ (by decide +kernel) _ (by decide) _ (by decide +kernel)
  · refine (congrArg (imageOf (dataOf kMem)).2.read (keccakRow_outOffset c)).trans ?_
    fin_cases c <;> exact readMem _ (by decide +kernel) _ (by decide) _ (by decide +kernel)

/-- The permutation of the input lanes is the executor's, in one kernel evaluation of
Keccak-f[1600]. -/
theorem keccak_lanes :
    ∀ l : Fin 25, stateLanes (keccakF1600 (laneState keccakRow.inLanes)) l = kLout[l] := by
  decide +kernel

/-- The named assumption holds of the honest row. -/
theorem keccak_relation : KeccakRelation keccakRow := by
  funext l
  exact (keccak_lanes l).symm

/-- The honest row's flags: even in, odd out, all thirteen cells. -/
theorem keccak_flags : KeccakFlags keccakRow false true .all := ⟨rfl, rfl, rfl, rfl⟩

/-- `KeccakSpec` on the honest row, through `keccak_refines_of`: bound, permuting, and the
successor is `(g · g^5, 1)`. -/
theorem keccak_spec : KeccakSpec keccakRow ⟨g * addressOfIndex 5, 1⟩ (dataOf kMem) :=
  keccak_refines_of ⟨false, true, .all, keccak_flags, keccak_bindings⟩ keccak_relation

/-- The valid execution alone yields a satisfying row, with any counts. -/
example : ConstraintsHold.Completeness (rowEnv (dataOf kMem))
    ((keccakTable.main (const (keccakRowOf (imageOf (dataOf kMem)).2 (addressOfIndex 5) 1
        keccakRow.oms
      (addressOfIndex 4) (addressOfIndex 8) (addressOfIndex 9) (addressOfIndex 13) false true .all
        (Vector.replicate 26 1) 1))).operations 0) := by
  obtain ⟨i, o, oc, ⟨hi, ho, ht, ha⟩, -, hexec⟩ := keccak_spec
  cases i <;> cases o <;> cases oc <;>
    first
    | exact absurd hi (by decide +kernel)
    | exact absurd ho (by decide +kernel)
    | exact absurd ht (by decide +kernel)
    | exact absurd ha (by decide +kernel)
    | exact keccak_exec_complete hexec _ _

/-- A nonzero free limb is rejected: an image whose first output cell (odd layout) has a nonzero
low limb, which holds no lane, does not balance the row's read of it, so the constraints `main`
emits on the honest row fail in every environment over that image. -/
def badMem : Array (Vector K 2) := kMem.set! 13 #v[1, kLout[0]]

example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, dataOf badMem⟩
      ((keccakTable.main (const keccakRow)).operations 0) := by
  intro h
  have hs : KeccakSpec keccakRow _ (dataOf badMem) :=
    (keccakTable.soundness 0 ⟨get, dataOf badMem⟩ (const keccakRow) keccakRow
      ProvableType.eval_const keccak_relation h).1
  obtain ⟨i, o, oc, ⟨-, ho, -, -⟩, hb, -⟩ := hs
  have h0 := hb.out_eq 0 (by cases oc <;> decide)
  rw [keccakRow_outOffset 0] at h0
  change (imageOf (dataOf badMem)).2.read (addressOfIndex 13) = _ at h0
  rw [readMem badMem (by decide +kernel) 13 (by decide) _ rfl] at h0
  cases o
  · exact absurd ho (by decide +kernel)
  · exact absurd (Option.some.inj h0) (by decide +kernel)

/-- The boundary with the Keccak reduction: an output lane holding a wrong but canonical word,
consistently in the row and in the image. The row is bound and locally complete, and it fails
the permutation relation and the functional specification: that failure is the Keccak GKR's to
enforce. -/
def wrongLout : Vector K 25 := kLout.set 0 (kLout[0] + 1)

def keccakRow' : KeccakRow K := { keccakRow with lout := wrongLout }

/-- The wrong row is bound to the image holding its output lanes. -/
theorem keccak'_bindings :
    KeccakBindings (imageOf (dataOf (kMemOf wrongLout))).2 keccakRow' false true .all := by
  refine ⟨fun c ↦ ?_, fun c _ ↦ ?_⟩
  · refine (congrArg (imageOf (dataOf (kMemOf wrongLout))).2.read (keccakRow_inOffset c)).trans ?_
    fin_cases c <;> exact readMem _ (by decide +kernel) _ (by decide) _ (by decide +kernel)
  · refine (congrArg (imageOf (dataOf (kMemOf wrongLout))).2.read (keccakRow_outOffset c)).trans ?_
    fin_cases c <;> exact readMem _ (by decide +kernel) _ (by decide) _ (by decide +kernel)

example : ConstraintsHold.Completeness (rowEnv (dataOf (kMemOf wrongLout)))
    ((keccakTable.main (const keccakRow')).operations 0) :=
  (keccakTable.completeness 0 (rowEnv (dataOf (kMemOf wrongLout))) (const _)
    (by simp only [circuit_norm, keccakTable, memRead, memReadIf, bytecodeRead, -BitVec.reduceNeg])
    _ ProvableType.eval_const_prover ⟨false, true, .all, ⟨rfl, rfl, rfl, rfl⟩, keccak'_bindings⟩).1

theorem keccak'_no_relation : ¬ KeccakRelation keccakRow' := by
  intro h
  exact absurd ((congrFun h 0).trans (keccak_lanes 0)) (by decide +kernel)

/-- Writing all thirteen cells, the wrong row fails the functional specification: every output lane
is bound to a written cell, which the execution checks against Keccak-f[1600]. -/
example (next : Registers K) : ¬ KeccakSpec keccakRow' next (dataOf (kMemOf wrongLout)) := fun h ↦
  keccak'_no_relation (KeccakRefines.relation_of_all h rfl)

/-- The same wrong lanes in a row writing output cell `0` alone (`out_cells = One`): lane `0` is
in cell `0` (odd layout), so the row still fails; a wrong lane the row writes to no cell would not
be seen by memory at all, and is the Keccak reduction's to reject (`KeccakRelation`). -/
def keccakRowOne : KeccakRow K := { keccakRow' with outTwo := 0, outAll := 0 }

example (next : Registers K) : ¬ KeccakSpec keccakRowOne next (dataOf (kMemOf wrongLout)) := by
  rintro ⟨i, o, oc, ⟨-, ho, -, -⟩, hb, hexec⟩
  obtain ⟨input, output, hin, hout, hcells, -⟩ :=
    (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _ _).mp hexec
  have h0 : output 0 = laneCells keccakRowOne.outLanes o 0 0 :=
    Option.some.inj ((hout 0 (by cases oc <;> decide)).symm.trans (hb.out_eq 0 (by cases oc <;> decide)))
  have hc := hcells 0 (by cases oc <;> decide)
  have hinput : input = laneCells keccakRowOne.inLanes i keccakRowOne.free := by
    funext c; exact Option.some.inj ((hin c).symm.trans (hb.in_eq c))
  rw [h0, hinput, stateOfCells_laneCells, cellsOfState_eq_laneCells] at hc
  cases o
  · exact absurd ho (by decide +kernel)
  · revert hc
    show ¬ laneCells wrongLout.get true 0 0 =
      laneCells (stateLanes (keccakF1600 (laneState keccakRow.inLanes))) true 0 0
    rw [show stateLanes (keccakF1600 (laneState keccakRow.inLanes)) = kLout.get from
      funext keccak_lanes]
    decide +kernel

end LeanVMTests.Arithmetization.Tables
