/-
  LeanVM.Prover.Complete.Link.Sizes

  The sizes the link reads of the honest witness's layout: its tables, its chunks, its row
  variables and the program's length.
-/

module

public import LeanVM.Prover.Complete.Link.Skeleton

/-!
# The link's sizes

`linkSizes`: on the honest witness the layout's tables are `tables()`, the chunks are `Chunks::new`
of the pointer width the layout's sizes give, the tallest table has at most `30` row variables, and
the program has `2^log_bytecode` instructions of `2^BYTECODE_SLOT_BITS` words, `log_bytecode` at
most the pointer width. These are `LinkFacts`' first four fields.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

theorem foldl_add_eq_sum (l : List ℕ) : l.foldl (· + ·) 0 = l.sum := by
  rw [List.foldl_eq_foldr, List.sum]

/-- **The link's sizes on the honest witness.** -/
theorem linkSizes {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {W : Witness}
    (hW : witness? prog input t = some W) :
    W.layout.tables = tables ∧
      Chunks.new (pointerWidth W.layout.logMemory W.layout.logBytecode
        (W.layout.tableRows.foldl (· + ·) 0)) = some W.chunks ∧
      linkNRows W ≤ 30 ∧
      (W.layout.logBytecode ≤ W.chunks.width ∧
        W.layout.bytecode.length >>> bytecodeSlotBits = 2 ^ W.layout.logBytecode) := by
  obtain ⟨-, steps, -, hrows, hl, -, hc, -, -⟩ := witness?_spec hW
  obtain ⟨hlm, htr, -⟩ := buildLayout_spec hl
  obtain ⟨hbc, htab, hshift, -⟩ := buildLayout_facts hl
  obtain ⟨-, hh⟩ := Wire.buildLayout_sizes hl
  have hlen : (bytecodeWords prog).length = 2 ^ (prog.logSize + bytecodeSlotBits) := by
    rw [LeanVM.Rpm.bytecodeWords_length, pow_add, mul_comm]; rfl
  have hlog : W.layout.logBytecode = prog.logSize := by
    rw [hlen, Nat.shiftRight_eq_div_pow, Nat.pow_div (by omega) (by norm_num),
      Nat.add_sub_cancel] at hshift
    exact (Nat.pow_right_injective (le_refl 2) hshift).symm
  have hchunks : Chunks.new (pointerWidth W.layout.logMemory W.layout.logBytecode
      (W.layout.tableRows.foldl (· + ·) 0)) = some W.chunks := by
    rw [hlm, hlog, htr, foldl_add_eq_sum]
    exact hc
  refine ⟨htab, hchunks, ?_, ?_, by rw [hbc]; exact hshift⟩
  · exact Wire.foldl_max_le hh 0 (by omega)
  · rw [Chunks.new_width hchunks]
    unfold pointerWidth
    omega

/-- **The message's length**: the non-pointer values, then `64` slices. -/
theorem linkMessage_length (W : Witness) (htab : W.layout.tables = tables) (x : LinkProverPre)
    (chi qPoint : List E) (st : RowState) :
    (linkMessage W x chi qPoint st).length = linkNValues W.layout + kBits := by
  unfold linkMessage linkNValues
  rw [htab]
  simp only [List.length_append, List.length_map, List.length_range, List.length_flatMap]
  decide +kernel

end LeanVM.Prover.Complete

end
