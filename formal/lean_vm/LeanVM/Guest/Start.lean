/-
  LeanVM.Guest.Start

  What both end theorems of the guest start from: the guest's bytecode as the verifier reads it,
  the public input of a digest, and the run's start (`__jump_tables`, `Guest/JumpTable.lean`).
-/

module

public import Statement.LeanVm
public import LeanVM.Facts.Verifier
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
public import LeanVM.Protocol.EndToEnd.Front.PubPhase
public import LeanVM.Guest.JumpTable
public import Statement.LeanVmGuest
public import LeanVM.Facts.Guest

/-!
# The run's start

`bytecode` is the guest's stacked bytecode, `2^23` words (`16 · 2^19`), the polynomial
`NodeRelation` and the verifier read; `publicInputOf d` is the public input whose digest is `d`
(`publicDigest_publicInputOf`), and `hdrOf d` its two memory words, `main`'s header.

The run's start is `Guest/JumpTable.lean`'s: a run starts at `(g^0, 1)` in `__jump_tables`, the
`SET`s of the jump table's slots in `main`'s frame, and falls through into `main` at
`mainEntry`, with `fp = 1`; `safe_jumpTables` (soundness: a halting run writes the table and
halts from `main`'s entry) and `reach_jumpTables` (completeness: on a memory holding the table,
the start reaches `main`'s entry).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

theorem bytecode_length : bytecode.length = 2 ^ 23 := by
  simp [bytecode, bytecodeWords, guest_logSize]

theorem publicDigest_publicInputOf (d : Digest) : publicInputDigest (publicInputOf d) = d := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [_, _, _, _], _ => rfl

end
end LeanVM.Guest.End
