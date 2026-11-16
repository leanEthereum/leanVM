/-
  LeanVM.Guest.Backend.Guest.Cpl.Jt

  The jump table slots the back end writes are the cells `__jump_tables` sets in `main`'s frame
  (`Memory.tableCells`).
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.Frames
public import LeanVM.Guest.Backend.Sound.Main

/-!
# The jump table's cells

`jt_fetch`: in any compiled program, instruction `s` (`__jump_tables` comes first) is the `SET` of
slot `s` of the tables, its cell `tablesBase + s` and word the slot's (`SlotWord`), as `jt_of_run`
reads it. At the guest the program is `guestProgram`, whose first function `Data.f0` sets the cells
`tableCells` (`End.f0_instr`, `End.f0_fetch`), as many as there are slots (`guest_jt`): so every
slot's word is a table cell's, at the slot's address (`jtCells`).
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory GuestPiece

@[expose] public section

/-- **Instruction `s` of a compiled program** sets slot `s` of the jump tables. -/
theorem jt_fetch {κ : ℕ} {W : World κ} (hW : W.Compiled) {s : ℕ} {kv : KVal} {w : E}
    (hsk : W.slots[s]? = some kv) (hw : SlotWord W.layout kv = some w) :
    W.prog.fetch (addressOfIndex s) =
      some (LeanIsaInstruction.setConstant (addressOfIndex (W.layout.tablesBase + s)) w) := by
  obtain ⟨hn, -, -, hmain⟩ := World.names hW
  obtain ⟨m, rest, hfns⟩ : ∃ m rest, W.fns = m :: rest := by
    cases hf : W.fns with
    | nil =>
        rw [← hn, hf] at hmain
        cases hmain
    | cons m rest => exact ⟨m, rest, rfl⟩
  have hndw := World.nodup hW
  have hslt := (Array.getElem?_eq_some_iff.mp hsk).1
  have he : W.slots.isEmpty = false := by
    cases h : W.slots.isEmpty
    · rfl
    · have : W.slots.size = 0 := by simpa using h
      omega
  have hsplit0 : (withTables W.fns W.slots).1 = [] ++
      (⟨"__jump_tables", W.slots.zipIdx.map fun (kv, j) => (⟨.set (m.frameSize + j) kv, []⟩ : LInstr),
        m.frameSize + W.slots.size⟩ : Lowered) ::
        ({ m with frameSize := m.frameSize + W.slots.size } :: rest) := by
    rw [hfns]
    simp [withTables, he]
  have hbase : W.layout.tablesBase = m.frameSize := by
    rw [World.layout, layoutOf, layout_tablesBase, hfns]
    simp [withTables, he]
  have hL := loaded_of_assemble W.L hndw hsplit0 W.hl hW.2 W.Pre W.Post
  have hf := hL.fetch s (by simpa [opsOf] using hslt)
  obtain ⟨hlt', hget⟩ := Array.getElem?_eq_some_iff.mp hsk
  simp only [opsOf, List.getElem_map, Array.getElem_toList, Array.getElem_map,
    Array.getElem_zipIdx, siteOf, Nat.zero_add] at hf
  rw [hget] at hf
  rw [hbase]
  cases kv with
  | «at» f i =>
      cases hw
      simpa [Site.R, resolveOp, resolveK, World.layout, World.prog, totalSize,
        OffsetInstruction.toLeanIsaInstruction] using hf
  | entry f =>
      cases hw
      simpa [Site.R, resolveOp, resolveK, World.layout, World.prog, totalSize,
        OffsetInstruction.toLeanIsaInstruction] using hf
  | _ => cases hw

theorem f0_count : Data.f0.instructionCount = W0.slots.size := by
  have h := congrArg CompiledFunction.instructionCount guest_jt
  dsimp only at h
  rw [h, slotsOfOuts_eq]
  rfl

/-- **Every slot's word is a table cell's**, at the slot's address. -/
theorem jtCells : JTCells := by
  intro s kv w hsk hw
  have hslt := (Array.getElem?_eq_some_iff.mp hsk).1
  have hs : s < Data.f0.instructionCount := by rw [f0_count]; exact hslt
  have h1 := jt_fetch W0_compiled hsk hw
  have hp : W0.prog = guestProgram := guestWorld_prog guest_compiles
  rw [hp, End.f0_fetch hs] at h1
  obtain ⟨o, k0, k1, hins, hq⟩ := End.f0_instr hs
  rw [hins] at h1
  simp only [OffsetInstruction.toLeanIsaInstruction, Option.some.injEq,
    LeanIsaInstruction.setConstant.injEq] at h1
  exact ⟨_, hq, h1.1, h1.2⟩

end
end LeanVM.Guest.Backend.Cpl

/-- info: 'LeanVM.Guest.Backend.Cpl.jtCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Cpl.jtCells
