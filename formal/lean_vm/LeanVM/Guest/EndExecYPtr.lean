/-
  LeanVM.Guest.EndExecYPtr

  The heap witness pointers as powers below `maxCells`: those a spine pins (`ptr_pow`), and what is left
  open of the others (`WitPtrRes`), apart from the deployed alignment's checks (`EndExecYWitCells`).
-/

module

public import LeanVM.Guest.EndExecY
public import LeanVM.Guest.Bridge.WitSound

/-!
# The heap witness pointers

A heap pointer is a power below `maxCells` when its function's spine pins it (`Bridge.ptrOk_sound`,
`ptr_pow`): in `K` by its allocation (`Inst.nodeAt`) or a load through it (the tree is valid on the
reference), and a word of the memory by a load through it at offset `0` or a heap hint's first word
(`Ref.Ok.hintWords`).

Left open, `WitPtrRes`: the heap witness pointers no atom of the spine pins, a power below
`maxCells`. The deployed guest has three: `dup_claims` in `main_loop0` and `main_loop1`, and
`child_defer` in `main_loop4`, each a pointer into `main`'s buffers computed from parameters.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec

@[expose] public section

/-- **The heap witness pointers the spine does not pin** are powers below `maxCells`, at each
honest instance. -/
def WitPtrRes : Prop :=
  ∀ r : Ref, r.Ok → ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ f σ bufs kids,
    I.t = .node f σ bufs kids → ∀ fn, coreProgram.find? f = some fn → ∀ S p off len,
      Ev.atom (.hint (.witness S (.heap p off len))) ∈ I.t.events coreProgram →
        Bridge.ptrOk (Bridge.spine fn.body) p = false → ∃ b < maxCells, σ p = ofK (Parameters.g ^ b)

end

public section

/-- A word the reference holds at an address is at a power below `2^κ`. -/
theorem read_pow {r : Ref} {a : K} {v : E} (h : r.img.read a = some v) (hκ : r.κ ≤ 28) :
    ∃ i < maxCells, a = Parameters.g ^ i := by
  obtain ⟨i, hi, -⟩ := (MemoryImage.read_eq_some_iff (by omega) r.img).mp h
  have : (i : ℕ) < 2 ^ 28 := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκ)
  exact ⟨i, by unfold maxCells; omega, hi⟩

/-- **A pinned heap pointer is a power below `maxCells`**, at an honest instance of the reference's
tree. -/
theorem ptr_pow {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} (hIt : I.t = .node f σ bufs kids) {p : V}
    (hin : p ∈ allocDsts (I.t.events coreProgram) ∨ ∃ d off, Ev.atom (.load d p off) ∈ I.t.events coreProgram)
    (hw : (∃ d, Ev.atom (.load d p 0) ∈ I.t.events coreProgram) ∨
      ∃ a len, Ev.atom a ∈ I.t.events coreProgram ∧ atomHeapDest? a = some (p, 0, len + 1)) :
    ∃ b < maxCells, σ p = ofK (Parameters.g ^ b) := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  -- the tree's atoms hold on the reference
  have hholds : ∀ a, Ev.atom a ∈ I.t.events coreProgram → a.Holds r.img.read σ := by
    intro a ha
    have hv := hHX.covers.valid hHon.toHonest
    rcases insts_good r.T _ r.hdr hv I hI with ⟨args, rets, hv'⟩ | ⟨_, _, hph⟩
    · rw [hIt] at hv' ha
      obtain ⟨fn, hf, -, es, vs, hwk, -, hall, -⟩ := hv'
      rw [events_node hf hwk] at ha
      exact hall _ ha
    · rw [hIt] at hph; cases hph
  -- in `K`
  have hK : IsInK (σ p) := by
    rcases hin with hal | ⟨d, off, hl⟩
    · obtain ⟨t, ν, hv, -, hpl, -, -, -, hTt⟩ := hr.tree
      have hTp : r.T.Placed coreProgram B2C.fs B2C.cert (0, r.T.block B2C.fs coreProgram.loop) := by
        rw [hTt, block_retemp]
        exact placed_retemp coreProgram_fresh t _ hv hpl
      have hI' : I ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := hI
      have h1 := (Inst.nodeAt (insts_placedAt r.T _ r.hdr hTp I hI') (insts_placed r.T _ r.hdr (by omega) I hI') hIt).1
      have h2 : σ p ∈ (allocDsts (I.t.events coreProgram)).map σ := List.mem_map.mpr ⟨p, hal, rfl⟩
      rw [h1] at h2
      obtain ⟨b, -, hb⟩ := List.mem_map.mp h2
      rw [← hb]
      exact B2C.isInK_ofK _
    · exact (hholds _ hl).1
  -- a word of the memory
  obtain ⟨v, hrd⟩ : ∃ v, r.img.read ((σ p).limb 0) = some v := by
    rcases hw with ⟨d, hl⟩ | ⟨a, len, ha, had⟩
    · have := (hholds _ hl).2
      rw [show addressOfIndex 0 = 1 by simp [addressOfIndex], mul_one] at this
      exact ⟨_, this⟩
    · have hA : (σ p).limb 0 * addressOfIndex (0 + 0) ∈ hintWords coreProgram B2C.fs B2C.H r.hdr r.T := by
        refine List.mem_flatMap.mpr ⟨I, hI, ?_⟩
        simp only [Inst.hintAddrs, hIt]
        refine List.mem_flatMap.mpr ⟨.atom a, hIt ▸ ha, ?_⟩
        cases a with
        | hint h =>
          simp only [atomHeapDest?] at had
          simp only [Ev.hintAddrs, had]
          exact List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos _), rfl⟩
        | _ => simp [atomHeapDest?] at had
      obtain ⟨v, -, hv⟩ := hr.hintWords _ hA
      rw [show addressOfIndex (0 + 0) = 1 by simp [addressOfIndex], mul_one] at hv
      exact ⟨v, hv⟩
  obtain ⟨i, hi, he⟩ := read_pow hrd hκ
  exact ⟨i, hi, by rw [Core.eq_ofK_limb hK, he]⟩


end

end LeanVM.Guest.EndExec
