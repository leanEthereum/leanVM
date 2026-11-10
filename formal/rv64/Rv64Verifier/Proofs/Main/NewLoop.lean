import Rv64Verifier.Proofs.Main.NewEnd

/-!
# `Bytecode::new`'s loop over the blocks

`block_step`: one block, from the loop's head (`NewL`) through `group` to the next head or out of
the loop, given `BlockFull`, a block with a nonzero word from `group`'s exit (`0x8000064c`) to its
end (`BE`). `newStage_of`: `NewStage` from `new_head`, `new_init` and `Reaches.loop` over `NewL`,
measured by the words left (`s10`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

/-- A block with a nonzero word, from `group`'s exit to its end: the counting sort, the buckets and
the `blocks` push (`0x80000650` to `0x80000510`). -/
def BlockFull : Prop :=
  ∀ (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat) (st : Model.NewState)
    (g : GrpSt) (t : MachineState), GS s words u₀ i L Hb st L g t → t.pc = 0x8000064c →
    gfold words i st L = some g → g.2.2 ≠ [] →
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ st', BE s words u₀ i L st' v)

section
variable {s u₀ t : MachineState} {words : List Word} {i : Nat} {st : Model.NewState}

/-- One block of `Bytecode::new`'s loop. -/
theorem block_step (hfull : BlockFull) (h : NewL s words u₀ i st t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ AfterNew s words v ∨
      ∃ st', NewL s words u₀ (i + 1) st' v) := by
  obtain ⟨v₁, r₁, gh⟩ := block_entry h
  obtain ⟨v₂, r₂, hd | ⟨g, hf, gs, hpc⟩⟩ := group_loop _ 0 _ v₁ rfl gh
  · exact ⟨v₂, r₁.trans r₂, Or.inl hd⟩
  have hbe : ∃ v, Reaches Image.code v₂ v ∧ (Dead Image.code v ∨ ∃ st' L,
      BE s words u₀ i L st' v) := by
    by_cases he : g.2.2 = []
    · obtain ⟨v, rv, hv⟩ := block_empty gs hpc hf he
      exact ⟨v, rv, Or.inr ⟨_, _, hv⟩⟩
    · obtain ⟨v, rv, hd | ⟨st', hv⟩⟩ := hfull _ _ _ _ _ _ _ _ _ gs hpc hf he
      · exact ⟨v, rv, Or.inl hd⟩
      · exact ⟨v, rv, Or.inr ⟨_, _, hv⟩⟩
  obtain ⟨v₃, r₃, hd | ⟨st', L, hv⟩⟩ := hbe
  · exact ⟨v₃, r₁.trans (r₂.trans r₃), Or.inl hd⟩
  obtain ⟨v, rv, hn | ha⟩ := block_next hv
  · exact ⟨v, r₁.trans (r₂.trans (r₃.trans rv)), Or.inr (Or.inr ⟨st', hn⟩)⟩
  · exact ⟨v, r₁.trans (r₂.trans (r₃.trans rv)), Or.inr (Or.inl ha)⟩

end

/-- **`Bytecode::new`**, given its blocks with a nonzero word. -/
theorem newStage_of (hfull : BlockFull) : NewStage := by
  intro s words u hu
  obtain ⟨v, rv, (ha | hn) | hd⟩ := new_head hu
  · exact ⟨v, rv, Or.inl ha⟩
  · obtain ⟨w, rw', hl⟩ := new_init hn
    obtain ⟨x, rx, hx⟩ := Reaches.loop (code := Image.code)
      (fun t ↦ ∃ i st, NewL s words v i st t) (fun t ↦ (t.getReg .x26).toNat)
      (fun t ↦ AfterNew s words t ∨ Dead Image.code t) (fun t ⟨i, st, ht⟩ ↦ by
        obtain ⟨y, ry, hd | ha | ⟨st', hy⟩⟩ := block_step hfull ht
        · exact Or.inl ⟨y, ry, Or.inr hd⟩
        · exact Or.inl ⟨y, ry, Or.inl ha⟩
        · refine Or.inr ⟨y, ry, ⟨i + 1, st', hy⟩, ?_⟩
          have h1 := ht.x26
          have h2 := hy.x26
          have h3 := hy.lt
          omega) w ⟨0, _, hl⟩
    exact ⟨x, rv.trans (rw'.trans rx), hx⟩
  · exact ⟨v, rv, Or.inr hd⟩

end Rv64Verifier.Proofs.Main
