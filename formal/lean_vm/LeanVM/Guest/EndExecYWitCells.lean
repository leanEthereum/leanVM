/-
  LeanVM.Guest.EndExecYWitCells

  The witness atoms' destinations in the reference, on the deployed alignment: `WitCells alignA`,
  but for the heap pointers no atom of their function's spine pins.
-/

module

public import LeanVM.Guest.EndExecYPtr
public import LeanVM.Guest.EndExecCAlign
public import LeanVM.Guest.Bridge.WitChk.All

/-!
# The witness destinations on the reference

At a frame of the tree track (an honest instance, `RefOk.frames`), a witness atom of its path has
its stack values, and its heap pointer, at their certificate cells in the frame
(`Bridge.witChk_sound`, every function passing the check, `Bridge.WitChk.witJ_all`), or the pointer
at a hint-only cell (`Ref.Ok.extra`); the frame holds each value its path names at its cell
(`FrameHolds.val`), which the alignment's cell map reads (`pairOk_alignA`). The heap pointers are
powers below `maxCells` by `EndExecYPtr` (`ptr_pow`, and `WitPtrRes` for those no spine pins).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (alignA alignA_of)
open LeanVM.Prover.Exec

public section

/-- **The witness atoms' destinations in the reference**, on the deployed alignment, but for the heap
pointers no atom of their function's spine pins. -/
theorem witCells_alignA (hR : WitPtrRes) : WitCells alignA := by
  intro r hr pc fp done e st hT es vs hw S d ha
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  have hE := hT.track.ents e List.mem_cons_self
  obtain ⟨hI, j, bufs, kids, vs', hj, hIt, hfn, hw', hFH⟩ :=
    (hT.frames hr.name hHon hHX.covers) e List.mem_cons_self
  rw [hw] at hw'
  obtain ⟨rfl, rfl⟩ : es = e.pre ++ e.es ∧ vs = vs' := by cases hw'; exact ⟨rfl, rfl⟩
  have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw
  obtain ⟨i, rfl, -, -, -, -, hfs, -, h1, h2⟩ := B2C.fn_of_idx hj
  have hW : Bridge.WitJ (i + 1) := Bridge.WitChk.witJ_all _ h1 h2
  rw [Bridge.WitJ, hfn] at hW
  have hcells := Bridge.witChk_sound hW hw ha
  have hlocAt := (pairOk_alignA e.I.t.name e.fn (i + 1) hE.find hj).2
  have hA : alignA e.I.t.name = Bridge.fnAl (i + 1) := alignA_of hj
  have hwithin : e.I.fp + B2C.fs e.I.t.name ≤ r.T.total B2C.fs :=
    honest_within_node hI hIt (by have := hHon.cells.two_le e.I hI; omega)
  have h28 : r.T.total B2C.fs ≤ 2 ^ 28 :=
    le_trans (le_two_pow_logMem _) (Nat.pow_le_pow_right (by norm_num) hκ)
  have hnamed : ∀ v ∈ destUses d, v ∈ B2C.namedOf (coreOf (i + 1)).params (e.pre ++ e.es) vs := fun v hv ↦
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ha, hv⟩))
  have hX : (alignA e.I.t.name).X = Bridge.ctxOf (i + 1) := by rw [hA]; rfl
  rw [← hX] at hcells
  -- a value at its cell, or at a hint-only one
  have hcell' : ∀ v ∈ destUses d,
      e.I.fp + (alignA e.I.t.name).X.locAt v.idx < maxCells ∧
        refMem r.img (e.I.fp + (alignA e.I.t.name).X.locAt v.idx) = e.σ v := by
    intro v hv
    rcases hcells v hv with ⟨hx, hidx, hl2, hlt⟩ | ⟨p, off, len, rfl, rfl, hx⟩
    · have hl := hlocAt _ hx hidx
      rw [hl] at hl2 hlt ⊢
      have hrd := hFH.val v (hnamed v hv) hl2 hlt
      rw [hfs] at hwithin
      exact refRd_img hκ r.img (e.I.fp + (certOf (i + 1)).locs.getD v.idx 0) (e.σ v) (by omega) hrd
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
      have hlc : (alignA e.I.t.name).X.locAt v.idx = c := by
        unfold Bridge.AlignCtx.locAt; rw [hc]; rfl
      have hc' : (Bridge.extraOf (i + 1)).lookup v.idx = some c := by rw [hX] at hc; exact hc
      obtain ⟨hlt, hrd⟩ := hr.extra e.I hI _ _ bufs kids hIt v (by rw [hevs]; exact List.mem_flatMap.mpr ⟨_, ha, hv⟩)
        c (by simp only [refExtra, hj, Option.getD_some]; exact hc')
      rw [hlc]
      exact refRd_img hκ r.img (e.I.fp + c) (e.σ v) (by omega) hrd
  cases d with
  | stack ws => exact fun v hv ↦ hcell' v hv
  | heap p off len =>
    obtain ⟨b, hb, hσ⟩ : ∃ b < maxCells, e.σ p = ofK (Parameters.g ^ b) := by
      by_cases hpk : Bridge.ptrOk (Bridge.spine e.fn.body) p = true
      · obtain ⟨hin, hwd⟩ := Bridge.ptrOk_sound hpk hw
        rw [← hevs] at hin hwd
        exact ptr_pow hr hI hIt hin hwd
      · exact hR r hr e.I hI _ _ bufs kids hIt e.fn hE.find S p off len (by rw [hevs]; exact ha)
          (by simpa using hpk)
    exact ⟨b, hb, hσ, hcell' p (by simp [destUses])⟩

end

end LeanVM.Guest.EndExec
