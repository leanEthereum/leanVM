import Rv64Verifier.Proofs.Walk.Head
import Rv64Verifier.Proofs.Layout.ReprVec

/-!
# `walk` at `0x80002e40`: the tables built, before the bus blocks

`build_layout` has built `table_log_heights` (`Q`, six words) and `tables()`: the six 80-byte
`Table`s in the buffer `B` (`TableAt`: the padding `Vec<E>` at `+0`, the `Flushes` at `+24`, the
opcode at `+72`), all but the last opcode stored (it is in `s0`, stored by the next instruction).
`table_rows` is at `R`. Nothing has moved the transcript since the announced sizes: the code still
runs `afterRate s A`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror

/-- The `Table` at `a` holds `t` but for its opcode: its padding `Vec<E>` at `+0`, its `Flushes`
at `+24`, both sound. -/
structure TableAt (u : MachineState) (a : Word) (t : TableRust) : Prop where
  padVec : VecOk u a 24 8
  pad : vecEs u a = t.padding
  ok : FlushesOk u (a + 24)
  flushes : flushesOf u (a + 24) = t.flushes

/-- What the `Table` at `a` reaches: its padding's buffer and its flushes' deep footprint. -/
@[rv_addr] def tableDeep (u : MachineState) (a : Word) (x : Word) : Prop :=
  Within x (vecPtr u a) (24 * (vecCap u a).toNat) ∨ flushesDeep u (a + 24) x

/-- At `0x80002e40`. `R` holds `table_rows`, `Q` `table_log_heights`, `B` the six tables. -/
structure AtR10 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) : Prop where
  pc : u.pc = 0x80002e40
  inv : Inv s u
  proofPtr : u.getMem (tp s) = s.getReg .x13
  checked : byteAt u (tp s + 360) = 1
  ok : HeadOk s A k
  rate : 1#64 ≤ rateOf A ∧ rateOf A ≤ 4#64
  tracks : Tracks OI s u (afterRate s A)
  /-- `s0` = the last table's opcode, `s1` = an empty `Vec`'s pointer, `s2` = `B`,
  `s4` = `sp + 2144`, `s5` = `s11` = the number of tables. -/
  x8 : u.getReg .x8 = 5
  x9 : u.getReg .x9 = 8
  x18 : u.getReg .x18 = B
  x20 : u.getReg .x20 = s.getReg .x2 - 512
  x21 : u.getReg .x21 = 6
  x27 : u.getReg .x27 = 6
  /-- `sp + 72` the rate, `sp + 80 .. 104` the public input's words, `sp + 128` the `Bytecode`,
  `sp + 144` `log_memory`, `sp + 160` `log_bytecode - 4`, `sp + 168` the result. -/
  spills : u.getMem (s.getReg .x2 - 2584) = rateOf A ∧
    u.getMem (s.getReg .x2 - 2576) = s.getMem (s.getReg .x12 + 16) ∧
    u.getMem (s.getReg .x2 - 2568) = s.getMem (s.getReg .x12) ∧
    u.getMem (s.getReg .x2 - 2560) = s.getMem (s.getReg .x12 + 24) ∧
    u.getMem (s.getReg .x2 - 2552) = s.getMem (s.getReg .x12 + 8) ∧
    u.getMem (s.getReg .x2 - 2528) = s.getReg .x11 ∧ u.getMem (s.getReg .x2 - 2512) = lmOf A ∧
    u.getMem (s.getReg .x2 - 2496) = BitVec.ofNat 64 (k - 4) ∧
    u.getMem (s.getReg .x2 - 2488) = s.getReg .x10
  /-- `sp + 120` the heights' capacity, `sp + 136` their length, `sp + 152` the length before
  `extend` (zero), `sp + 176` `R`, `sp + 192` `Q`, `sp + 200` `B`. -/
  slots : u.getMem (s.getReg .x2 - 2536) = 6 ∧ u.getMem (s.getReg .x2 - 2520) = 6 ∧
    u.getMem (s.getReg .x2 - 2504) = 0 ∧ u.getMem (s.getReg .x2 - 2480) = R ∧
    u.getMem (s.getReg .x2 - 2464) = Q ∧ u.getMem (s.getReg .x2 - 2456) = B
  /-- The three buffers: aligned, allocated (`Q` and `B` by `walk`), `B` apart from the other two. -/
  bufR : R.toNat % 8 = 0 ∧ 0x20000000 ≤ R.toNat ∧ R.toNat + 48 ≤ heapNext u
  bufQ : heapNext s ≤ Q.toNat ∧ Q.toNat % 8 = 0 ∧ Q.toNat + 48 ≤ heapNext u
  bufB : heapNext s ≤ B.toNat ∧ B.toNat % 8 = 0 ∧ B.toNat + 480 ≤ heapNext u
  apartB : Apart B 480 R 48 ∧ Apart B 480 Q 48
  rows : [u.getMem R, u.getMem (R + 8), u.getMem (R + 16), u.getMem (R + 24), u.getMem (R + 32),
    u.getMem (R + 40)] = rowsOf A
  heights : ∀ i < 6, u.getMem (Q + BitVec.ofNat 64 (8 * i)) =
    BitVec.ofNat 64 ((tableLogHeightsRust (rowsOf A)).getD i 0)
  tables : ∀ i t, tablesRust[i]? = some t → TableAt u (B + BitVec.ofNat 64 (80 * i)) t
  opcodes : ∀ i < 5, u.getMem (B + BitVec.ofNat 64 (80 * i + 72)) = BitVec.ofNat 64 i
  /-- What a table reaches misses `B`. -/
  sep : ∀ i < 6, ∀ x, tableDeep u (B + BitVec.ofNat 64 (80 * i)) x → ¬ Within x B 480

end Rv64Verifier.Proofs.Walk
