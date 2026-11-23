import LeanVM.Guest.Bytecode
import LeanVM.Guest.Data.Names
import LeanVM.Guest.Mode.JumpTables

/-!
# The guest bytecode

`guest_fetch_of` at the first and last pcs of the largest compiled function after `__loop2_main`
(`sp_wots`, over chunks in three modules), at a `KECCAK` of each layout, at the first and last pcs
of `verify_sig_lean_sphincs` and its first `KECCAK`, at `main`'s entry, at pc `0`, and the padding;
each side condition is one `decide +kernel`. The expected instructions are those of the guest's
`DBG_DISASM` dump. The functions are named by their stable names (`fn_idx%`) and the pcs are
offsets from their entries, so another function's change moves none. And the offset form of
`KECCAK`'s cells.
-/

namespace LeanVMTests.Guest.Bytecode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

example : Data.functions.length = fn_count% := by decide +kernel

example : Data.codeLen = (Data.functions.map (·.instructionCount)).sum := by decide +kernel

/-- `sp_wots`, the largest function after `__loop2_main`. -/
abbrev spWots : CompiledFunction := Data.functions[fn_idx% «sp_wots»]'(by decide +kernel)

theorem spWots_mem : spWots ∈ Data.functions := List.getElem_mem _

example : spWots.name = "sp_wots" ∧ spWots.instructionCount = 23650 ∧ spWots.chunks.length = 12 := by
  decide +kernel

/-- Its first instruction, `SET fp[9] = 1`. -/
example : guestProgram.fetch (addressOfIndex spWots.entryPc) = some (OffsetInstruction.set 9 1
    0).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 0) (by decide +kernel) rfl (by decide +kernel)

/-- Its last, the return `JUMP if fp[9] ≠ 0: pc = fp[0], fp = fp[1]`. -/
example : guestProgram.fetch (addressOfIndex (spWots.entryPc + 23649)) = some (OffsetInstruction.jump 9 0
    1).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 23649) (by decide +kernel) rfl (by decide +kernel)

/-- A `KECCAK` writing the odd layout, all thirteen cells, `KECCAK fp[974..+13] odd =
keccak_f(fp[987], fp[988], fp[989], fp[990], tail = fp[991..+4], b8 = fp[995],
cap = fp[961..+4]) even`. -/
example : guestProgram.fetch (addressOfIndex (spWots.entryPc + 23636)) =
    some (OffsetInstruction.keccak 987 988 989 990 991 995 961 974 false
        true .all).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 23636) (by decide +kernel) rfl (by decide +kernel)

/-- The next, reading the odd layout and writing one cell, the 16-byte digest,
`KECCAK fp[844..+1] even = keccak_f(fp[996], fp[997], fp[998], fp[999], tail = fp[1000..+4],
b8 = fp[1005], cap = fp[983..+4]) odd`. -/
example : guestProgram.fetch (addressOfIndex (spWots.entryPc + 23647)) =
    some (OffsetInstruction.keccak 996 997 998 999 1000 1005 983 844 true
        false .one).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 23647) (by decide +kernel) rfl (by decide +kernel)

/-- `verify_sig_lean_sphincs`, the function after `sp_wots`. -/
abbrev sphincs : CompiledFunction := Data.functions[fn_idx% «verify_sig_lean_sphincs»]'(by decide +kernel)

theorem sphincs_mem : sphincs ∈ Data.functions := List.getElem_mem _

example : sphincs.name = "verify_sig_lean_sphincs" ∧ sphincs.entryPc = spWots.entryPc + spWots.instructionCount ∧
    sphincs.instructionCount = 3882 := by
  decide +kernel

/-- Its first instruction, `DEREF *(fp[2]·g^0) = fp[4]`. -/
example : guestProgram.fetch (addressOfIndex sphincs.entryPc) = some (OffsetInstruction.deref 2 0 4
    .cell).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 0) (by decide +kernel) rfl (by decide +kernel)

/-- Its last, the return `JUMP if fp[15] ≠ 0: pc = fp[0], fp = fp[1]`. -/
example : guestProgram.fetch (addressOfIndex (sphincs.entryPc + 3881)) = some (OffsetInstruction.jump 15 0
    1).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 3881) (by decide +kernel) rfl (by decide +kernel)

/-- Its first `KECCAK`, `H_msg`'s first call, writing the two-cell digest, `KECCAK fp[8..+2] =
keccak_f(fp[7], fp[4], fp[5], fp[6], tail = fp[11..+4], b8 = fp[16], cap = fp[18..+4])`, both
layouts even. -/
example : guestProgram.fetch (addressOfIndex (sphincs.entryPc + 14)) =
    some (OffsetInstruction.keccak 7 4 5 6 11 16 18 8 false
        false .two).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 14) (by decide +kernel) rfl (by decide +kernel)

/-- `main`'s first instruction, `DEREF *(fp[2]·g^0) = fp[10]`. -/
example : guestProgram.fetch (addressOfIndex Data.f1.entryPc) = some (OffsetInstruction.deref 2 0 10
    .cell).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f1) (mem_functions (j := 1) rfl) (i := 0) (by decide +kernel) rfl
    (by decide +kernel)

/-- `main`'s `KECCAK`, both layouts even: the digest of the DA claim it checks directly
(`keccak([root_0, root_1], [z_0, z_1], own_da[0:2])`), written in place, two cells,
`KECCAK fp[384..+2] even = keccak_f(fp[379], fp[380], fp[381], fp[387], tail = fp[386..+4],
b8 = fp[391], cap = fp[387..+4]) even`. -/
example : guestProgram.fetch (addressOfIndex (Data.f1.entryPc + 726)) =
    some (OffsetInstruction.keccak 379 380 381 387 386 391 387 384 false
        false .two).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f1) (mem_functions (j := 1) rfl) (i := 726) (by decide +kernel) rfl
    (by decide +kernel)

/-- The first instruction of the program, in `__jump_tables`: `SET fp[Data.mainCells]`, the jump
table's first slot, to its target's power of `g`. -/
example : ∃ k t, guestProgram.fetch (addressOfIndex 0) = some (OffsetInstruction.set Data.mainCells
    k 0).toLeanIsaInstruction ∧ Data.jtTrie.get Data.mainCells = some t ∧ Data.powTree.find k = some t := by
  obtain ⟨k, t, h, hj, hp⟩ := Mode.f0_slot (i := 0) (by decide +kernel)
  exact ⟨k, t, guest_fetch_of (f := Data.f0) (mem_functions (j := 0) rfl) (i := 0) (by decide +kernel) rfl h,
    hj, hp⟩

/-- The last slot is padding. -/
example : guestProgram.fetch (addressOfIndex (2 ^ 19 - 1)) = some
    OffsetInstruction.padding.toLeanIsaInstruction :=
  guest_fetch_pad (by decide) (by decide)

/-- The code list agrees with `instructionAt`. -/
example : sphincs.code[3881]? = some (OffsetInstruction.jump 15 0 1) := by
  rw [CompiledFunction.getElem?_code (CompiledFunction.wellChunked_of_mem sphincs_mem)
      (by decide +kernel)]
  decide +kernel

/-! ## `KECCAK`'s cells in offset form -/

example : keccakIns 139 140 141 142 143 147 29 =
    [139, 140, 141, 142, 143, 144, 145, 146, 147, 29, 30, 31, 32] := by decide

example : keccakOuts 3296 13 = (List.range 13).map (3296 + ·) := rfl

example : keccakOuts 844 1 = [844] := rfl

/-- The instruction's read addresses are the offsets `keccakIns`, its written ones `keccakOuts`. -/
example (c : Fin 13) :
    keccakInputCellOffset ![addressOfIndex 139, addressOfIndex 140, addressOfIndex 141,
        addressOfIndex 142] (addressOfIndex 143) (addressOfIndex 147) (addressOfIndex 29) c =
      addressOfIndex ((keccakIns 139 140 141 142 143 147 29).getD c 0) := by
  rw [keccakInOffset_gpow, keccakIns_getD _ _ _ _ _ _ _ c.isLt]

example (k : Fin 13) : g ^ k.val * addressOfIndex 3296 = addressOfIndex ((keccakOuts 3296 13).getD k
    0) := by
  rw [keccakOutOffset_gpow, keccakOuts_getD _ _ k.isLt]

end LeanVMTests.Guest.Bytecode
