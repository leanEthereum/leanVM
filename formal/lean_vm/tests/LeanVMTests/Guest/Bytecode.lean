import LeanVM.Guest.Bytecode

/-!
# The guest bytecode

`guest_fetch_of` at the first and last pcs of the largest compiled function
(`verify_sig_lean_sphincs`, 27232 instructions over 14 chunks), at `main`'s entry, at pc `0`, and
the padding; each side condition is one `decide +kernel`. The expected instructions are those of
the guest's `DBG_DISASM` dump.
-/

namespace LeanVMTests.Guest.Bytecode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

example : Data.functions.length = 1044 := by decide +kernel

example : Data.codeLen = 244706 := rfl

/-- `verify_sig_lean_sphincs` is function 18. -/
theorem sphincs_mem : Data.f18 ∈ Data.functions := mem_functions (j := 18) rfl

example : Data.f18.name = "verify_sig_lean_sphincs" ∧ Data.f18.len = 27232 := ⟨rfl, rfl⟩

/-- Its first instruction, `DEREF *(fp[2]·g^1) = fp[3]`. -/
example : guest.fetch (gpow 47451) = some (OInstr.deref 2 1 3 .cell).toInstr :=
  guest_fetch_of sphincs_mem (i := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Its last, the return `JUMP if fp[93] ≠ 0: pc = fp[0], fp = fp[1]`. -/
example : guest.fetch (gpow 74682) = some (OInstr.jump 93 0 1).toInstr :=
  guest_fetch_of sphincs_mem (i := 27231) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `main`'s first instruction, `SET fp[10] = g^65535`, the immediate as its bits. -/
example : guest.fetch (gpow 4478) = some (OInstr.set 10 9272771591053052074 0 0).toInstr :=
  guest_fetch_of (f := Data.f1) (mem_functions (j := 1) rfl) (i := 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The first instruction of the program, in `__jump_tables`. -/
example : guest.fetch (gpow 0) = some (OInstr.set 167 17762821799675167344 0 0).toInstr :=
  guest_fetch_of (f := Data.f0) (mem_functions (j := 0) rfl) (i := 0) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The last slot is padding. -/
example : guest.fetch (gpow (2 ^ 18 - 1)) = some OInstr.pad.toInstr :=
  guest_fetch_pad (by decide) (by decide)

example : SentinelSafe guest := guest_sentinelSafe

/-- The code list agrees with `instrAt`. -/
example : Data.f18.code[27231]? = some (OInstr.jump 93 0 1) := by
  rw [CompiledFn.getElem?_code (CompiledFn.wellChunked_of_mem sphincs_mem) (by decide +kernel)]
  decide +kernel

end LeanVMTests.Guest.Bytecode
