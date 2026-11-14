/-
  LeanVM.Guest.EndExecYWitCells

  The witness atoms' destinations in the reference, on the deployed alignment: `WitCells alignA`,
  but for the heap pointers no atom of their function's spine pins.
-/

module

public import LeanVM.Guest.EndExecY
public import LeanVM.Guest.EndExecCAlign
public import LeanVM.Guest.Bridge.WitSound
public import LeanVM.Guest.Bridge.WitChk.All

/-!
# The witness destinations on the reference

At a frame of the tree track (an honest instance, `RefOk.frames`), a witness atom of its path has
its stack values, and its heap pointer, at their certificate cells in the frame
(`Bridge.witChk_sound`, every function passing the check, `Bridge.WitChk.witJ_all`), or the pointer
at a hint-only cell (`Ref.Ok.extra`); the frame holds each value its path names at its cell
(`FrameHolds.val`), which the alignment's cell map reads (`pairOk_alignA`). A heap pointer is a
power below `maxCells` when its function's spine pins it (`Bridge.ptrOk_sound`): in `K` by its
allocation (`Inst.nodeAt`) or a load through it (the tree is valid on the reference), and a word
of the memory by a load through it at offset `0` or a heap hint's first word (`Ref.Ok.hintWords`).

Left open, `WitPtrRes`: the heap witness pointers no atom of the spine pins, a power below
`maxCells`. The deployed guest has three: `dup_claims` in `main_loop0` and `main_loop1`, and
`child_defer` in `main_loop4`, each a pointer into `main`'s buffers computed from parameters.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (alignA alignA_of)
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
    honest_within hI (by have := hHon.cells.two_le e.I hI; omega)
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
