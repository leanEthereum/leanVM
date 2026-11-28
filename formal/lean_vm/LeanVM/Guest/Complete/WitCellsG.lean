/-
  LeanVM.Guest.Complete.WitCellsG

  The witness atoms' destinations in the reference, at the deployed alignment: `WitCells`, but for
  the heap pointers no spine pins being in `K`.
-/

module

public import LeanVM.Guest.Complete.JumpCellsG
public import LeanVM.Guest.Bridge.WitSound
public import LeanVM.Guest.Bridge.WitChk.All
public import LeanVM.Guest.Bridge.FrameMapA
public import LeanVM.Guest.Bridge.JumpCellsPack

/-!
# The witness destinations on the reference

The tag's `EndExecYWitCells` on b2c's aligned layout. At a frame of the tree track (an honest
instance, `Bridge.RefOk.framesA`), a witness atom of its path has its stack values, and its heap
pointer, at their alignment cells in the frame (`Bridge.witChk_sound`, every function passing the
check, `Bridge.WitChk.witJ_all`), or the pointer at a hint-only cell (`RefH.extra`); the frame holds
each value its path names at its certificate cell (`FrameHolds.val`), which the alignment's cell map
reads off the hint-only cells (`locAt_ofData`). A heap pointer is a power below `maxCells`: in `K`
by its allocation or a load through it, and a word of the memory by a load through it at offset `0`
or a heap hint's first word (`ptr_powA`), when its spine pins it (`Bridge.ptrOk`); otherwise by
`WitPtrK`, what the route's carried facts give (`CoreMode.Fam.CarryDefs`' `witAtomC`): in `K`,
written from offset `0`.

Left open, `WitPtrK`: the four heap witness pointers no spine pins are in `K`, `stream`'s in
`__loop0_hint_stream`, `dup_claims`' in `__loop0_main` and `__loop1_main`, `child_defer`'s in
`__loop4_main`, each a pointer into a caller's buffer computed from parameters.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Guest.Bridge (alignA alignA_of fnAl ctxOf)
open LeanVM.Prover.Exec

@[expose] public section

/-- **The heap witness pointers no spine pins are in `K`**, written from offset `0`, at each honest
instance of a reference run (the route's `witAtomC`). -/
def WitPtrK (L : Lay) (D : Ref → RefD) : Prop :=
  ∀ r, RefH L (D r) r → r.Ok → ∀ I ∈ instsOf L (D r) r, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
    ∀ fn, coreProgram.find? f = some fn → ∀ S p off len,
      Ev.atom (.hint (.witness S (.heap p off len))) ∈ I.t.events coreProgram →
        Bridge.ptrOk (Bridge.spine fn.body) p = false → IsInK (σ p) ∧ off = 0 ∧ 0 < len

end

public section

variable {al : String → Bool} {D : Ref → RefD}

/-- A word the reference holds at an address is at a power below `maxCells`. -/
theorem read_powR {r : Ref} {a : K} {v : E} (h : r.img.read a = some v) (hκ : r.κ ≤ 28) :
    ∃ i < maxCells, a = Parameters.g ^ i := by
  obtain ⟨i, hi, -⟩ := (MemoryImage.read_eq_some_iff (by omega) r.img).mp h
  have : (i : ℕ) < 2 ^ 28 := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκ)
  exact ⟨i, by unfold maxCells; omega, hi⟩

/-- **A value of `K` the reference reads a word at is a power below `maxCells`.** -/
theorem pow_of_inK {r : Ref} (hκ : r.κ ≤ 28) {x : E} (hK : IsInK x) {v : E} (hrd : r.img.read (x.limb 0) = some v) :
    ∃ b < maxCells, x = ofK (Parameters.g ^ b) := by
  obtain ⟨i, hi, he⟩ := read_powR hrd hκ
  exact ⟨i, hi, by rw [Core.eq_ofK_limb hK, he]⟩

/-- **A heap hint's words are hint words of the honest tree.** -/
theorem hintWord_mem {L : Lay} {d : RefD} {r : Ref} {I : Inst} (hI : I ∈ instsOf L d r) {f : String} {σ : Val}
    {bufs : List ℕ} {kids : List Memory.Tree} (hIt : I.t = .node f σ bufs kids) {a : Atom}
    (ha : Ev.atom a ∈ I.t.events coreProgram) {p : V} {off len : ℕ} (had : atomHeapDest? a = some (p, off, len))
    {k : ℕ} (hk : k < len) :
    (σ p).limb 0 * addressOfIndex (off + k) ∈ hintWords coreProgram L.fs L.al L.H r.hdr d.T := by
  refine List.mem_flatMap.mpr ⟨I, hI, ?_⟩
  simp only [Inst.hintAddrs, hIt, heapHintAddrs]
  refine List.mem_flatMap.mpr ⟨.atom a, hIt ▸ ha, ?_⟩
  cases a with
  | hint h =>
    simp only [atomHeapDest?] at had
    simp only [Ev.hintAddrs, had]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  | _ => simp [atomHeapDest?] at had

/-- **A pinned heap pointer is a power below `maxCells`**, at an honest instance of a reference
run. -/
theorem ptr_powA {r : Ref} (hRH : RefH ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ (D r) r) (hr : r.Ok) {I : Inst}
    (hI : I ∈ instsOf ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ (D r) r) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Memory.Tree} (hIt : I.t = .node f σ bufs kids) {p : V}
    (hin : p ∈ allocDsts (I.t.events coreProgram) ∨ ∃ d off, Ev.atom (.load d p off) ∈ I.t.events coreProgram)
    (hw : (∃ d, Ev.atom (.load d p 0) ∈ I.t.events coreProgram) ∨
      ∃ a len, Ev.atom a ∈ I.t.events coreProgram ∧ atomHeapDest? a = some (p, 0, len + 1)) :
    ∃ b < maxCells, σ p = ofK (Parameters.g ^ b) := by
  have hκ : r.κ ≤ 28 := hr.log
  obtain ⟨rd, hH, hX⟩ := hRH.honest
  have hcov : Covers coreProgram B2C.fs al B2C.H B2C.C r.hdr (D r).T r.img :=
    fun q hq ha ↦ (hRH.img q.1).trans (hX.covers q hq ha)
  -- the tree's atoms hold on the reference
  have hholds : ∀ a, Ev.atom a ∈ I.t.events coreProgram → a.Holds r.img.read σ := by
    intro a ha
    rcases instsA_good (P := coreProgram) _ _ _ (Covers.valid hH.toHonestA hcov) I hI with
      ⟨args, rets, hv'⟩ | ⟨_, _, hph⟩
    · rw [hIt] at hv' ha
      obtain ⟨fn, hf, -, es, vs, hwk, -, hall, -⟩ := hv'
      rw [events_node hf hwk] at ha
      exact hall _ ha
    · rw [hIt] at hph; cases hph
  -- in `K`
  have hK : IsInK (σ p) := by
    rcases hin with hal | ⟨d, off, hl⟩
    · have h1 := (hH.nodeAt hI hIt).1
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
    · obtain ⟨v, -, hv⟩ := hRH.hintWords _ (hintWord_mem hI hIt ha had (Nat.succ_pos len))
      rw [show addressOfIndex (0 + 0) = 1 by simp [addressOfIndex], mul_one] at hv
      exact ⟨v, hv⟩
  exact pow_of_inK hκ hK hrd

/-- **The witness atoms' destinations in the reference**, on the deployed alignment, at any flags,
given the heap pointers no spine pins in `K`. -/
theorem witCells_alignA (hP : WitPtrK ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ D) :
    WitCells ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ D alignA := by
  intro r hRH hr pc fp done e st hT es vs hw S d ha
  have hκ : r.κ ≤ 28 := hr.log
  obtain ⟨rd, hH, hX⟩ := hRH.honest
  have hcov : Covers coreProgram B2C.fs al B2C.H B2C.C r.hdr (D r).T r.img :=
    fun q hq ha ↦ (hRH.img q.1).trans (hX.covers q hq ha)
  obtain ⟨hI, j, bufs, kids, vs', hj, hIt, hfn, hw', hFH⟩ :=
    Bridge.RefOk.framesA hRH.name hH hcov hT e List.mem_cons_self
  rw [hw] at hw'
  obtain ⟨rfl, rfl⟩ : es = e.pre ++ e.es ∧ vs = vs' := by cases hw'; exact ⟨rfl, rfl⟩
  have hE := hT.track.ents e List.mem_cons_self
  have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw
  obtain ⟨i, rfl, -, -, -, -, hfs, -, h1, h2⟩ := B2C.fn_of_idx hj
  have hW : Bridge.WitJ (i + 1) := Bridge.WitChk.witJ_all _ h1 (by have : nFns = fn_count% := rfl; omega)
  rw [Bridge.WitJ, hfn] at hW
  have hcells := Bridge.witChk_sound hW hw ha
  have hA : alignA e.I.t.name = fnAl (i + 1) := alignA_of hj
  have hX' : (alignA e.I.t.name).X = ctxOf (i + 1) := by rw [hA]; rfl
  rw [← hX'] at hcells
  -- the alignment's cell map is the certificate's off the hint-only cells
  have hok := Bridge.progAl.ok _ _ hE.find
  rw [hA] at hok
  have hlocs : (certOf (i + 1)).locs.all (fun c ↦ Nat.blt c (2 ^ Bridge.cellBits)) = true := by
    rw [Bridge.alignOk, Bridge.AlignCtx.seq_eq] at hok
    simp only [Bool.and_eq_true] at hok
    exact hok.1.1.1.1
  have hlocAt : ∀ k, (alignA e.I.t.name).X.extra.lookup k = none → k < 2 ^ 30 →
      (alignA e.I.t.name).X.locAt k = (certOf (i + 1)).locs.getD k 0 := fun k hx hk ↦ by
    rw [hX'] at hx ⊢
    exact Bridge.locAt_ofData hlocs hx hk
  -- the frame within the memory's `2^30` words
  have h2f : 2 ≤ e.I.t.fsz B2C.fs := hH.cells.two_le e.I hI
  have hwithin : e.I.fp + B2C.fs e.I.t.name ≤ (D r).T.wordsA B2C.fs coreProgram.loop al :=
    honestA_within_node hI hIt (by omega)
  have hsize : (D r).T.wordsA B2C.fs coreProgram.loop al ≤ 2 ^ 30 := hH.size
  have hnamed : ∀ v ∈ destUses d, v ∈ B2C.namedOf (coreOf (i + 1)).params (e.pre ++ e.es) vs := fun v hv ↦
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ha, hv⟩))
  -- a value at its cell, or at a hint-only one
  have hcell' : ∀ v ∈ destUses d,
      e.I.fp + (alignA e.I.t.name).X.locAt v.idx < maxCells ∧
        refMem r.img (e.I.fp + (alignA e.I.t.name).X.locAt v.idx) = e.σ v := by
    intro v hv
    rcases hcells v hv with ⟨hx, hidx, hl2, hlt⟩ | ⟨p, off, len, rfl, rfl, hx⟩
    · have hl := hlocAt _ hx hidx
      rw [hl] at hl2 hlt ⊢
      have hrd := hFH.val v (hnamed v hv) (by rw [B2C.cellJ]; exact hl2) (by rw [B2C.cellJ]; exact hlt)
      rw [B2C.cellJ] at hrd
      exact refRd_img hκ r.img _ _ (by omega) hrd
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
      have hlc : (alignA e.I.t.name).X.locAt v.idx = c := by
        unfold Bridge.AlignCtx.locAt; rw [hc]; rfl
      have hc' : (exA ((B2C.idxOf e.I.t.name).getD 0)).lookup v.idx = some c := by
        rw [hj, Option.getD_some]; rw [hX'] at hc; exact hc
      obtain ⟨hlt, hrd⟩ := hRH.extra e.I hI _ _ bufs kids hIt v
        (by rw [hevs]; exact List.mem_flatMap.mpr ⟨_, ha, hv⟩) c hc'
      rw [hlc]
      exact refRd_img hκ r.img _ _ (by omega) hrd
  cases d with
  | stack ws => exact fun v hv ↦ hcell' v hv
  | heap p off len =>
    obtain ⟨b, hb, hσ⟩ : ∃ b < maxCells, e.σ p = ofK (Parameters.g ^ b) := by
      by_cases hpk : Bridge.ptrOk (Bridge.spine e.fn.body) p = true
      · obtain ⟨hin, hwd⟩ := Bridge.ptrOk_sound hpk hw
        rw [← hevs] at hin hwd
        exact ptr_powA hRH hr hI hIt hin hwd
      · obtain ⟨hK, rfl, hl⟩ := hP r hRH hr e.I hI _ _ bufs kids hIt e.fn hE.find S p off len
          (by rw [hevs]; exact ha) (by simpa using hpk)
        obtain ⟨v, -, hv⟩ := hRH.hintWords _
          (hintWord_mem hI hIt (by rw [hevs]; exact ha) (p := p) (off := 0) (len := len) rfl hl)
        rw [show addressOfIndex (0 + 0) = 1 by simp [addressOfIndex], mul_one] at hv
        exact pow_of_inK hκ hK hv
    exact ⟨b, hb, hσ, hcell' p (by simp [destUses])⟩

end

end LeanVM.Guest.Complete
