/-
  LeanVM.Guest.Complete.CompRefG

  What the reference holds of each computed hint atom, at the deployed alignment: `CompRef`.
-/

module

public import LeanVM.Guest.Complete.WitCellsG
public import LeanVM.Guest.Bridge.Pair
public import LeanVM.Guest.Bridge.PairLink
public import LeanVM.Guest.Bridge.PairChk.All
public import LeanVM.Guest.Memory.RetempExactA

/-!
# The computed hints on the reference

At a frame of the tree track (an honest instance, `Bridge.RefOk.framesA`), a computed hint atom of
its path is exact on `rd0` (`RefH.exact` at the instance, `every_instsA`). The function's data
check (`Bridge.pairChk`, every function passing it, `Bridge.PairChk.pairJ_all`) puts each of its
frame values at its certificate cell, where the frame holds it (`FrameHolds.val`) and the
alignment's cell map reads it (`locAt_ofData`), or at a hint-only cell (`RefH.extra`); and its
buffer from offset `0`, its pointer at such a cell, allocated or loaded through on the path (so in
`K`) and written whole by a heap hint of the path, whose words the reference holds as `rd0` does
(`RefH.hintWords`): the pointer is a power `g^b` below `maxCells` (`ptr_powA`) and the buffer's
words are the reference's from `b` on. `compRef_alignA : CompRef … alignA` at any flags.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Guest.Bridge (alignA alignA_of fnAl ctxOf)
open LeanVM.Prover.Exec

public section

variable {al : String → Bool} {D : Ref → RefD}

/-- **What the reference holds of each computed hint atom**, on the deployed alignment, at any
flags. -/
theorem compRef_alignA : CompRef ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ D alignA := by
  intro r hRH hr pc fp done e st hT hc hev hcomp
  have hκ : r.κ ≤ 28 := hr.log
  obtain ⟨rd, hH, hX⟩ := hRH.honest
  have hcov : Covers coreProgram B2C.fs al B2C.H B2C.C r.hdr (D r).T r.img :=
    fun q hq ha ↦ (hRH.img q.1).trans (hX.covers q hq ha)
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, hfn, hw, hFH⟩ :=
    Bridge.RefOk.framesA hRH.name hH hcov hT e List.mem_cons_self
  have hE := hT.track.ents e List.mem_cons_self
  have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw
  obtain ⟨i, rfl, -, -, -, -, hfs, -, h1, h2⟩ := B2C.fn_of_idx hj
  -- the atom is exact on `rd0`
  have hxc : hc.Exact (D r).rd0 e.σ := by
    have hexI := every_instsA (D r).T _ r.hdr hRH.exact e.I hI _ _ bufs kids hIt
    have hevs0 : (Memory.Tree.node e.I.t.name e.σ [] []).events coreProgram = e.pre ++ e.es :=
      events_node hE.find hw
    exact hexI _ (by rw [hevs0]; exact hev)
  -- the data check
  have hPJ : Bridge.PairJ (i + 1) :=
    Bridge.PairChk.pairJ_all _ h1 (by have : nFns = fn_count% := rfl; omega)
  have hchk := hPJ.1
  rw [hfn] at hchk
  obtain ⟨hframe, hbuf⟩ := Bridge.pairChk_sound hchk hw hev hcomp
  have hA : alignA e.I.t.name = fnAl (i + 1) := alignA_of hj
  have hX' : (alignA e.I.t.name).X = ctxOf (i + 1) := by rw [hA]; rfl
  have hok := Bridge.progAl.ok _ _ hE.find
  rw [hA] at hok
  have hlocs : (certOf (i + 1)).locs.all (fun c ↦ Nat.blt c (2 ^ Bridge.cellBits)) = true := by
    rw [Bridge.alignOk, Bridge.AlignCtx.seq_eq] at hok
    simp only [Bool.and_eq_true] at hok
    exact hok.1.1.1.1
  have hlocAt : ∀ k, (Bridge.extraOf (i + 1)).lookup k = none → k < 2 ^ 30 →
      (alignA e.I.t.name).X.locAt k = (certOf (i + 1)).locs.getD k 0 := fun k hx hk ↦ by
    rw [hX']
    exact Bridge.locAt_ofData hlocs hx hk
  -- the frame within the memory's `2^30` words
  have h2f : 2 ≤ e.I.t.fsz B2C.fs := hH.cells.two_le e.I hI
  have hwithin : e.I.fp + B2C.fs e.I.t.name ≤ (D r).T.wordsA B2C.fs coreProgram.loop al :=
    honestA_within_node hI hIt (by omega)
  have hsize : (D r).T.wordsA B2C.fs coreProgram.loop al ≤ 2 ^ 30 := hH.size
  have huses : ∀ v ∈ hintUses hc, v ∈ (e.I.t.events coreProgram).flatMap Ev.uses := fun v hv ↦ by
    rw [hevs]; exact List.mem_flatMap.mpr ⟨_, hev, hv⟩
  have hnamed : ∀ v ∈ hintUses hc, v ∈ B2C.namedOf (coreOf (i + 1)).params (e.pre ++ e.es) vs := fun v hv ↦
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hev, hv⟩))
  -- a value at its certificate cell
  have hcell : ∀ v ∈ hintUses hc, (Bridge.extraOf (i + 1)).lookup v.idx = none → v.idx < 2 ^ 30 →
      2 ≤ (certOf (i + 1)).locs.getD v.idx 0 → (certOf (i + 1)).locs.getD v.idx 0 < B2C.fsN (i + 1) →
      e.I.fp + (alignA e.I.t.name).X.locAt v.idx < maxCells ∧
        refMem r.img (e.I.fp + (alignA e.I.t.name).X.locAt v.idx) = e.σ v := by
    intro v hv hx hidx h2 hlt
    rw [hlocAt _ hx hidx]
    have hrd := hFH.val v (hnamed v hv) (by rw [B2C.cellJ]; exact h2) (by rw [B2C.cellJ]; exact hlt)
    rw [B2C.cellJ] at hrd
    exact refRd_img hκ r.img _ _ (by omega) hrd
  -- a value at a hint-only cell
  have hextra : ∀ v ∈ hintUses hc, ∀ c, (Bridge.extraOf (i + 1)).lookup v.idx = some c →
      e.I.fp + (alignA e.I.t.name).X.locAt v.idx < maxCells ∧
        refMem r.img (e.I.fp + (alignA e.I.t.name).X.locAt v.idx) = e.σ v := by
    intro v hv c hc
    have hlc : (alignA e.I.t.name).X.locAt v.idx = c := by
      rw [hX']; unfold Bridge.AlignCtx.locAt
      rw [show (ctxOf (i + 1)).extra = Bridge.extraOf (i + 1) from rfl, hc]
      rfl
    have hc' : (exA ((B2C.idxOf e.I.t.name).getD 0)).lookup v.idx = some c := by
      rw [hj, Option.getD_some]; exact hc
    obtain ⟨hlt, hrd⟩ := hRH.extra e.I hI _ _ bufs kids hIt v (huses v hv) c hc'
    rw [hlc]
    exact refRd_img hκ r.img _ _ (by omega) hrd
  have hval : ∀ v ∈ hintUses hc, ((Bridge.extraOf (i + 1)).lookup v.idx = none ∧ v.idx < 2 ^ 30 ∧
      2 ≤ (certOf (i + 1)).locs.getD v.idx 0 ∧ (certOf (i + 1)).locs.getD v.idx 0 < B2C.fsN (i + 1)) ∨
      ((Bridge.extraOf (i + 1)).lookup v.idx).isSome →
      e.I.fp + (alignA e.I.t.name).X.locAt v.idx < maxCells ∧
        refMem r.img (e.I.fp + (alignA e.I.t.name).X.locAt v.idx) = e.σ v := by
    intro v hv h
    rcases h with ⟨hx, hidx, h2, hlt⟩ | hx
    · exact hcell v hv hx hidx h2 hlt
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
      exact hextra v hv c hc
  refine ⟨hxc, fun v hv ↦ ?_, fun p off len hb ↦ ?_⟩
  · rcases hframe v hv with hf | ⟨c, hc, -, -⟩
    · exact hval v (hintFrame_uses hv) (Or.inl hf)
    · exact hval v (hintFrame_uses hv) (Or.inr (by rw [hc]; rfl))
  · obtain ⟨rfl, hl0, hl, hcl, hin, a, ha, had⟩ := hbuf p off len hb
    have hp := hval p (hintBuf_uses hb) hcl
    rw [← hevs] at hin ha
    obtain ⟨len', rfl⟩ : ∃ len', len = len' + 1 := ⟨len - 1, by omega⟩
    obtain ⟨b, hb', hσp⟩ := ptr_powA hRH hr hI hIt hin (Or.inr ⟨a, len', ha, had⟩)
    refine ⟨rfl, b, hb', by rw [hp.2, hσp], fun k hk ↦ ?_⟩
    obtain ⟨v, hv0, hvi⟩ := hRH.hintWords _ (hintWord_mem hI hIt ha had hk)
    have ha' : (e.σ p).limb 0 * addressOfIndex (0 + k) = Parameters.g ^ (b + k) := by
      rw [hσp]; simp [addressOfIndex, pow_add]
    rw [ha'] at hv0 hvi
    obtain ⟨hk1, hk2⟩ := refRd_imgK hκ r.img (c := b + k) (by unfold maxCells at hb'; omega) hvi
    refine ⟨hk1, ?_⟩
    rw [hk2, words_heap_getD hk, ha', hv0]
    rfl

end

end LeanVM.Guest.Complete
