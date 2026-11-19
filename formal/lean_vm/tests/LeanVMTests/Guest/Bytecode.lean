import LeanVM.Guest.Bytecode
import LeanVM.Guest.Data.NameStrings

/-!
# The guest bytecode

`guest_fetch_of` at the first and last pcs of the largest compiled function after `__loop2`
(`sp_wots`, 25442 instructions over 13 chunks in three modules), at a `KECCAK` of each layout, at
the first and last
pcs of `verify_sig_lean_sphincs` and its first `KECCAK`, at `main`'s entry, at pc `0`, and the
padding; each side condition is one `decide +kernel`. The expected instructions are those of the guest's `DBG_DISASM` dump. And the
offset form of `KECCAK`'s cells.
-/

namespace LeanVMTests.Guest.Bytecode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Core

example : Data.functions.length = fn_count% := by decide +kernel

example : Data.codeLen = 455612 := rfl

/-- `sp_wots` is function 20, the largest after `__loop2` (function 37, 113678 instructions). -/
theorem spWots_mem : Data.f20 ∈ Data.functions := mem_functions (j := 20) rfl

example : Data.f20.name = "sp_wots" ∧ Data.f20.entryPc = 33128 ∧
    Data.f20.instructionCount = 25442 ∧ Data.f20.chunks.length = 13 := ⟨rfl, rfl, rfl, rfl⟩

/-- Its first instruction, `SET fp[9] = 1`. -/
example : guestProgram.fetch (addressOfIndex 33128) = some (OffsetInstruction.set 9 1
    0).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Its last, the return `JUMP if fp[9] ≠ 0: pc = fp[0], fp = fp[1]`. -/
example : guestProgram.fetch (addressOfIndex 58569) = some (OffsetInstruction.jump 9 0
    1).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 25441) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- A `KECCAK` writing the odd layout, all thirteen cells, `KECCAK fp[951..+13] odd =
keccak_f(fp[964], fp[965], fp[966], fp[967], tail = fp[968..+4], b8 = fp[972],
cap = fp[938..+4]) even`. -/
example : guestProgram.fetch (addressOfIndex (33128 + 25428)) =
    some (OffsetInstruction.keccak 964 965 966 967 968 972 938 951 false
        true .all).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 25428) (by decide +kernel) rfl (by decide +kernel)

/-- The next, reading the odd layout and writing one cell, the 16-byte digest,
`KECCAK fp[821..+1] even = keccak_f(fp[973], fp[974], fp[975], fp[976], tail = fp[977..+4],
b8 = fp[982], cap = fp[960..+4]) odd`. -/
example : guestProgram.fetch (addressOfIndex (33128 + 25439)) =
    some (OffsetInstruction.keccak 973 974 975 976 977 982 960 821 true
        false .one).toLeanIsaInstruction :=
  guest_fetch_of spWots_mem (i := 25439) (by decide +kernel) rfl (by decide +kernel)

/-- `verify_sig_lean_sphincs` is function 21 (after `sp_wots`, 20). -/
theorem sphincs_mem : Data.f21 ∈ Data.functions := mem_functions (j := 21) rfl

example : Data.f21.name = "verify_sig_lean_sphincs" ∧ Data.f21.entryPc = 58570 ∧
    Data.f21.instructionCount = 3887 := ⟨rfl, rfl, rfl⟩

/-- Its first instruction, `DEREF *(fp[2]·g^0) = fp[4]`. -/
example : guestProgram.fetch (addressOfIndex 58570) = some (OffsetInstruction.deref 2 0 4
    .cell).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Its last, the return `JUMP if fp[16] ≠ 0: pc = fp[0], fp = fp[1]`. -/
example : guestProgram.fetch (addressOfIndex 62456) = some (OffsetInstruction.jump 16 0
    1).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 3886) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- Its first `KECCAK`, `H_msg`'s first call, writing the two-cell digest, `KECCAK fp[9..+2] =
keccak_f(fp[8], fp[4], fp[5], fp[6], tail = fp[12..+4], b8 = fp[17], cap = fp[19..+4])`, both
layouts even. -/
example : guestProgram.fetch (addressOfIndex (58570 + 15)) =
    some (OffsetInstruction.keccak 8 4 5 6 12 17 19 9 false
        false .two).toLeanIsaInstruction :=
  guest_fetch_of sphincs_mem (i := 15) (by decide +kernel) rfl (by decide +kernel)

/-- `main`'s first instruction, `DEREF *(fp[2]·g^0) = fp[10]`. -/
example : guestProgram.fetch (addressOfIndex 13986) = some (OffsetInstruction.deref 2 0 10
    .cell).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f1) (mem_functions (j := 1) rfl) (i := 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- `main`'s `KECCAK`, both layouts even: the digest of the DA claim it checks directly
(`keccak([root_0, root_1], [z_0, z_1], own_da[0:2])`), written in place, two cells,
`KECCAK fp[329..+2] even = keccak_f(fp[324], fp[325], fp[326], fp[332], tail = fp[331..+4],
b8 = fp[336], cap = fp[332..+4]) even`. -/
example : guestProgram.fetch (addressOfIndex 14657) =
    some (OffsetInstruction.keccak 324 325 326 332 331 336 332 329 false
        false .two).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f1) (mem_functions (j := 1) rfl) (i := 671) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The first instruction of the program, in `__jump_tables`: `SET fp[379]` to a jump target, a
power of `g`. -/
example : guestProgram.fetch (addressOfIndex 0) = some (OffsetInstruction.set 379
    7887744672993903533 0).toLeanIsaInstruction :=
  guest_fetch_of (f := Data.f0) (mem_functions (j := 0) rfl) (i := 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The last slot is padding. -/
example : guestProgram.fetch (addressOfIndex (2 ^ 19 - 1)) = some
    OffsetInstruction.padding.toLeanIsaInstruction :=
  guest_fetch_pad (by decide) (by decide)

/-- The code list agrees with `instructionAt`. -/
example : Data.f21.code[3886]? = some (OffsetInstruction.jump 16 0 1) := by
  rw [CompiledFunction.getElem?_code (CompiledFunction.wellChunked_of_mem sphincs_mem)
      (by decide +kernel)]
  decide +kernel

/-! ## `KECCAK`'s cells in offset form -/

example : keccakIns 139 140 141 142 143 147 29 =
    [139, 140, 141, 142, 143, 144, 145, 146, 147, 29, 30, 31, 32] := by decide

example : keccakOuts 3296 13 = (List.range 13).map (3296 + ·) := rfl

example : keccakOuts 845 1 = [845] := rfl

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
