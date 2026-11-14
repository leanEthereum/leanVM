module

public import LeanVM.Guest.JumpTable.Entries

/-!
# `__jump_tables` for the mode walk

`__jump_tables` (function `0`, from pc `0`) has no walk: it is straight-line `SET`s, which the
walk's environment (`Mode.Env`, its table `Data.jtTrie` over the cells `jtLo = 430` up to
`jtHi = 14367`, `Data.powTree` naming its words) reads as written before `main` starts. `jtSlots`,
the kernel's check of its code: instruction `i` sets cell `jtLo + i` to the word `g^t` of the
table's target `t` there (`f0_slot`), and the instructions are exactly the cells from `jtLo` to
`jtHi` (`jt_span`). So a run of it writes every cell of the walk's jump table run (`jtRng`) with
the words `EnvOk` asks for, the state `Inv` starts `main` from.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest LeanVM.Guest.Exec LeanVM.Guest.Memory

@[expose] public section

/-- Instruction `i` of `__jump_tables` sets cell `jtLo + i` to the word of the table's target there. -/
noncomputable def slotOk (i : ℕ) : OffsetInstruction → Bool
  | .set o k0 k1 => o == Data.mainCells + i && k1 == 0 &&
      match Data.jtTrie.get (Data.mainCells + i) with
      | some t => Data.powTree.find k0 == some t
      | none => false
  | _ => false

set_option maxRecDepth 100000 in
/-- **`__jump_tables` writes the jump table, slot by slot.** -/
theorem jtSlots : walkOk slotOk 0 Data.f0.code = true := by decide +kernel

/-- Its cells are the walk's jump table run's. -/
theorem jt_span : Data.mainCells = 430 ∧ Data.mainCells + Data.f0.instructionCount = 14367 := by
  decide

/-- Instruction `i` of `__jump_tables` sets cell `jtLo + i` to `g^t`, `t` the table's target. -/
theorem f0_slot {i : ℕ} (hi : i < Data.f0.instructionCount) :
    ∃ k0 t, Data.f0.instructionAt i = .set (Data.mainCells + i) k0 0 ∧
      Data.jtTrie.get (Data.mainCells + i) = some t ∧ Data.powTree.find k0 = some t := by
  have hc := CompiledFunction.getElem?_code
    (CompiledFunction.wellChunked_of_mem (List.mem_cons_self : Data.f0 ∈ Data.functions)) hi
  have hw := walkOk_get jtSlots hc
  rw [Nat.zero_add] at hw
  rcases h : Data.f0.instructionAt i with _ | _ | ⟨o, k0, k1⟩ | _ | _ | _ <;>
    rw [h] at hw <;> simp only [slotOk, Bool.false_eq_true] at hw
  simp only [Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨rfl, rfl⟩, hw⟩ := hw
  split at hw
  · rename_i t ht
    exact ⟨k0, t, rfl, ht, beq_iff_eq.mp hw⟩
  · cases hw

end

end LeanVM.Guest.Mode
