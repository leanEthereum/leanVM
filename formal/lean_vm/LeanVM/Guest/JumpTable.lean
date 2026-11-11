/-
  LeanVM.Guest.JumpTable

  `main`'s entry and the jump table `__jump_tables` writes: the run's start, and the jump table of
  the checker's `Glob` holding in a memory that holds `__jump_tables`' writes.
-/

module

public import LeanVM.Guest.Exec
public import LeanVM.Guest.Bytecode
public import LeanVM.Guest.Logic
public import LeanVM.Guest.Memory
public import LeanVM.Guest.JumpTable.Ok0
public import LeanVM.Guest.JumpTable.Ok1
public import LeanVM.Guest.JumpTable.Ok2
public import LeanVM.Guest.JumpTable.Ok3
public import LeanVM.Guest.JumpTable.Ok4
public import LeanVM.Guest.JumpTable.Ok5
public import LeanVM.Guest.JumpTable.Ok6
public import LeanVM.Guest.JumpTable.Ok7

/-!
# The jump table

`__jump_tables` (function `0`, from pc `0`) is `13952` `SET`s of the slots `429 + i` of `main`'s
frame, then `main` runs from its entry `mainEntry = 13952` at `fp = 1`. `JumpTables L` says each
`SET` holds in `L` (each slot of `Memory.tableCells` holds its word). `safe_jumpTables`: a halting
run from `(g^0, 1)` writes the table and halts from `(g^mainEntry, 1)`; `reach_jumpTables` is the
converse for completeness.

`Data.jtTrie` maps a slot `s` to the exponent `t` of the target `g^t` the checker expects there.
`jtOk` checks, at every entry `(s, t)` of the trie, that instruction `s - 429` of `__jump_tables`
is `SET s, k0, 0, 0` with `Data.powTree` giving `k0 ↦ t`, so that `K.ofBits k0 = g^t`
(`PowTree.Ok`): sixteen subtrees, each checked in eight parts by the kernel in `JumpTable.Ok*`
(`JumpTable.Entries` the check). So the table the checks read is the one `__jump_tables` writes
(`jt_of_jumpTables`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

/-- `main`'s entry pc, after `__jump_tables`. -/
def mainEntry : ℕ := Data.f0.instructionCount

/-- **The jump table is written**: every slot of `Memory.tableCells` holds its word. -/
def JumpTables {κ : ℕ} (L : MemoryImage κ) : Prop := ∀ q ∈ Memory.tableCells, L.read (addressOfIndex q.1) = some q.2

/-- The slot a `SET` writes. -/
def setCell? : OffsetInstruction → Option (ℕ × E)
  | .set o k0 k1 k2 => some (o, OffsetInstruction.immediateWord k0 k1 k2)
  | _ => none

theorem tableCells_eq : Memory.tableCells = Data.f0.code.filterMap setCell? := by
  unfold Memory.tableCells
  congr 1

set_option maxRecDepth 100000 in
theorem f0_all_set : Data.f0.code.all (fun ins ↦ (setCell? ins).isSome) = true := by
  decide +kernel

theorem f0_mem : Data.f0 ∈ Data.functions := List.mem_cons_self

theorem f0_entry : Data.f0.entryPc = 0 := rfl

/-- Instruction `i` of `__jump_tables` is a `SET` of a slot of the table. -/
theorem f0_instr {i : ℕ} (hi : i < Data.f0.instructionCount) :
    ∃ o k0 k1 k2, Data.f0.instructionAt i = .set o k0 k1 k2 ∧ (o, OffsetInstruction.immediateWord k0 k1 k2) ∈ Memory.tableCells := by
  have hc := CompiledFunction.getElem?_code (CompiledFunction.wellChunked_of_mem f0_mem) hi
  have hmem : Data.f0.instructionAt i ∈ Data.f0.code := List.mem_of_getElem? hc
  have hs := List.all_eq_true.mp f0_all_set _ hmem
  rcases h : Data.f0.instructionAt i with
      _ | _ | ⟨o, k0, k1, k2⟩ | _ | _ | _ <;> rw [h] at hs hmem <;>
    simp only [setCell?, Option.isSome_none, Bool.false_eq_true] at hs
  exact ⟨o, k0, k1, k2, rfl, tableCells_eq ▸ List.mem_filterMap.mpr ⟨_, hmem, rfl⟩⟩

theorem f0_fetch {i : ℕ} (hi : i < Data.f0.instructionCount) :
    guestProgram.fetch (addressOfIndex i) = some (Data.f0.instructionAt
        i).toLeanIsaInstruction := by
  have := guest_fetch f0_mem hi
  rwa [f0_entry, Nat.zero_add] at this

theorem f0_pc_lt {i : ℕ} (hi : i < Data.f0.instructionCount) : i < 2 ^ guestProgram.logSize -
    1 := by
  have := guest_pc_lt f0_mem hi
  rwa [f0_entry, Nat.zero_add] at this

theorem gpow_mul_one (o : ℕ) : (1 : K) * addressOfIndex o = addressOfIndex o := one_mul _

/-- **The run's start, soundly**: a halting run from `(g^0, 1)` writes the jump table and halts
from `main`'s entry at `fp = 1`. -/
theorem safe_jumpTables {κ : ℕ} {L : MemoryImage κ} {k : ℕ} (h : Safe guestProgram L k ⟨addressOfIndex 0, 1⟩) :
    JumpTables L ∧ ∃ k', Safe guestProgram L k' ⟨addressOfIndex mainEntry, 1⟩ := by
  have hwalk : ∀ i ≤ Data.f0.instructionCount, (∀ j < i, Holds L j 1 (Data.f0.instructionAt j)) ∧
      ∃ k', Safe guestProgram L k' ⟨addressOfIndex i, 1⟩ := by
    intro i
    induction i with
    | zero => exact fun _ ↦ ⟨fun _ hj ↦ absurd hj (Nat.not_lt_zero _), k, h⟩
    | succ i ih =>
      intro hi
      obtain ⟨hh, k', hk'⟩ := ih (by omega)
      obtain ⟨o, k0, k1, k2, hins, -⟩ := f0_instr (show i < Data.f0.instructionCount by omega)
      have hf := f0_fetch (show i < Data.f0.instructionCount by omega)
      rw [hins] at hf
      obtain ⟨k'', -, hH, hs⟩ := hk'.fallThrough hf (f0_pc_lt (by omega)) rfl
      refine ⟨fun j hj ↦ ?_, k'', hs⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hh j hj
      · rw [hins]; exact hH
  obtain ⟨hh, hrun⟩ := hwalk _ le_rfl
  refine ⟨fun q hq ↦ ?_, hrun⟩
  obtain ⟨ins, hmem, hq⟩ := List.mem_filterMap.mp (tableCells_eq ▸ hq)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  have hlen : i < Data.f0.instructionCount := CompiledFunction.length_code
      (CompiledFunction.wellChunked_of_mem f0_mem) ▸ hi
  have hc := CompiledFunction.getElem?_code (CompiledFunction.wellChunked_of_mem f0_mem) hlen
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hc
  obtain ⟨o, k0, k1, k2, hins, -⟩ := f0_instr hlen
  have hH := hh i hlen
  rw [hc, hins] at hq
  rw [hins] at hH
  simp only [setCell?, Option.some.injEq] at hq
  subst hq
  rw [← gpow_mul_one]
  exact hH

/-- **The run's start, completely**: on a memory holding the jump table, `__jump_tables` runs
from `(g^0, 1)` to `main`'s entry at `fp = 1`. -/
theorem reach_jumpTables {κ : ℕ} {L : MemoryImage κ} (h : JumpTables L) :
    Reach guestProgram L ⟨addressOfIndex 0, 1⟩ ⟨addressOfIndex mainEntry, 1⟩ := by
  have hwalk : ∀ i ≤ Data.f0.instructionCount, Reach guestProgram L ⟨addressOfIndex 0, 1⟩
      ⟨addressOfIndex i, 1⟩ := by
    intro i
    induction i with
    | zero => exact fun _ ↦ Reach.refl _
    | succ i ih =>
      intro hi
      obtain ⟨o, k0, k1, k2, hins, hq⟩ := f0_instr (show i < Data.f0.instructionCount by omega)
      have hf := f0_fetch (show i < Data.f0.instructionCount by omega)
      rw [hins] at hf
      have hH : Holds L i 1 (.set o k0 k1 k2) := by
        show L.read (1 * addressOfIndex o) = some (OffsetInstruction.immediateWord k0 k1 k2)
        rw [gpow_mul_one]
        exact h _ hq
      exact (ih (by omega)).trans (reach_fallThrough hf (f0_pc_lt (by omega)) rfl hH)
  exact hwalk _ le_rfl

end
end LeanVM.Guest.End

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

set_option maxRecDepth 100000 in
theorem jtOk : allEntries entryOk Data.jtTrie 1 0 = true :=
  allEntries_split (by decide +kernel)
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        (allEntries_split (by decide +kernel) jtOk_0 jtOk_1)
        (allEntries_split (by decide +kernel) jtOk_2 jtOk_3))
      (allEntries_split (by decide +kernel)
        (allEntries_split (by decide +kernel) jtOk_4 jtOk_5)
        (allEntries_split (by decide +kernel) jtOk_6 jtOk_7)))
    (allEntries_split (by decide +kernel)
      (allEntries_split (by decide +kernel)
        (allEntries_split (by decide +kernel) jtOk_8 jtOk_9)
        (allEntries_split (by decide +kernel) jtOk_10 jtOk_11))
      (allEntries_split (by decide +kernel)
        (allEntries_split (by decide +kernel) jtOk_12 jtOk_13)
        (allEntries_split (by decide +kernel) jtOk_14 jtOk_15)))

/-- The jump table the checker reads is what `__jump_tables` wrote. -/
theorem jt_of_jumpTables {κ : ℕ} {L : MemoryImage κ} (h : End.JumpTables L) (hpows : Data.powTree.Ok) :
    ∀ s t, Data.jtTrie.get s = some t → L.read (addressOfIndex s) = some (ofK (addressOfIndex
        t)) := by
  intro s t hs
  have he := allEntries_get jtOk hs
  rw [Nat.one_mul, Nat.add_zero] at he
  unfold entryOk at he
  rw [Bool.and_eq_true] at he
  obtain ⟨hlt, he⟩ := he
  have hlen : s - 429 < Data.f0.instructionCount := by simpa using hlt
  obtain ⟨o, k0, k1, k2, hins, hmem⟩ := End.f0_instr hlen
  rw [hins] at he
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨⟨⟨ho, hk1⟩, hk2⟩, hf⟩ := he
  subst ho hk1 hk2
  have := h _ hmem
  rwa [imm_of_ofBits (PowTree.find_ok hpows hf)] at this

end
end LeanVM.Guest.JumpTable
