/-
  LeanVM.Guest.JumpTable

  The jump table of the checker's `Glob` holds in a memory that holds `__jump_tables`' writes.
-/

module

public import LeanVM.Guest.End
public import LeanVM.Guest.JumpTable.Ok0
public import LeanVM.Guest.JumpTable.Ok1
public import LeanVM.Guest.JumpTable.Ok2
public import LeanVM.Guest.JumpTable.Ok3
public import LeanVM.Guest.JumpTable.Ok4
public import LeanVM.Guest.JumpTable.Ok5
public import LeanVM.Guest.JumpTable.Ok6
public import LeanVM.Guest.JumpTable.Ok7

/-!
# The jump table by the `SET`s of `__jump_tables`

`End.JumpTables L` says each `SET` of `__jump_tables` holds in `L`. `Data.jtTrie` maps a slot `s`
to the exponent `t` of the target `g^t` the checker expects there. `jtOk` checks, at every entry
`(s, t)` of the trie, that instruction `s - 167` of `__jump_tables` is `SET s, k0, 0, 0` with
`Data.powTree` giving `k0 ↦ t`, so that `K.ofBits k0 = g^t` (`PowTree.Ok`): sixteen subtrees,
each checked in four parts by the kernel in `JumpTable.Ok*` (`JumpTable.Entries` the check).
-/

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

set_option maxRecDepth 100000 in
theorem jtOk : allEntries entryOk Data.jtTrie 1 0 = true :=
  allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) jtOk_0 jtOk_1) (allEntries_split (by decide +kernel) jtOk_2 jtOk_3)) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) jtOk_4 jtOk_5) (allEntries_split (by decide +kernel) jtOk_6 jtOk_7))) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) jtOk_8 jtOk_9) (allEntries_split (by decide +kernel) jtOk_10 jtOk_11)) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) jtOk_12 jtOk_13) (allEntries_split (by decide +kernel) jtOk_14 jtOk_15)))

/-- The jump table the checker reads is what `__jump_tables` wrote. -/
theorem jt_of_jumpTables {κ : ℕ} {L : MemImage κ} (h : End.JumpTables L) (hpows : Data.powTree.Ok) :
    ∀ s t, Data.jtTrie.get s = some t → L.read (gpow s) = some (ofK (gpow t)) := by
  intro s t hs
  have he := allEntries_get jtOk hs
  rw [Nat.one_mul, Nat.add_zero] at he
  unfold entryOk at he
  rw [Bool.and_eq_true] at he
  obtain ⟨hlt, he⟩ := he
  have hlen : s - 167 < Data.f0.len := by simpa using hlt
  obtain ⟨o, k0, k1, k2, hins, hmem⟩ := End.f0_instr hlen
  rw [hins] at he
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨⟨⟨ho, hk1⟩, hk2⟩, hf⟩ := he
  subst ho hk1 hk2
  have := h _ hmem
  rwa [imm_of_ofBits (PowTree.find_ok hpows hf)] at this

end
end LeanVM.Guest.JumpTable
