/-
  LeanVM.Guest.EndExecAStat

  The fixed cells' words at every frame of the tree track, on B2's layout: `AddrFacts.stat` from
  what each honest frame holds (`B2C.FrameHolds.stat`).
-/

module

public import LeanVM.Guest.EndExecAAddr
public import LeanVM.Guest.Bridge.FrameMapA
public import LeanVM.Guest.B2C.Shared
public import LeanVM.Guest.Bridge.JumpCellsPack

/-!
# The fixed cells' words

The bus era's `FrameHolds.stat` on the aligned layout: at every frame of the tree track on a
reference of the honest tree (`RefOk.framesA`, on B2's frame sizes, headers, cells and certificate
cells), each fixed cell of the plumbing (`(plumbOf j).stat`) holds its word, the frame's cell `o`'s
address for an `fpg o`. The alignment context's `statOf` is the plumbing's table (`getF_trieOf`),
whose cells are at least `2` (`B2C.stat_in`, the sharing check).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

public section

variable {D : Ref → RefD}

/-- **The fixed cells' words at every frame of the tree track**, on B2's layout at any aligned
flags. -/
theorem addrStat_of {L : Lay} (hfs : L.fs = B2C.fs) (hH : L.H = B2C.H) (hC : L.C = B2C.C)
    (hc : L.cert = B2C.cert) :
    ∀ r, RefH L (D r) r → r.Ok → ∀ pc fp done e st, RefTrack L D alignA r pc fp (done, e :: st) →
      ∀ q o, (alignA e.I.t.name).X.statOf q = some (.fpg o) → q < L.fs e.I.t.name →
        refMem r.img (e.I.fp + q) = ofK (g ^ (e.I.fp + o)) := by
  obtain ⟨fs, al, H, C, cert⟩ := L
  simp only at hfs hH hC hc
  subst hfs hH hC hc
  intro r hR hr pc fp done e st htr q o hso hq
  dsimp only at hR htr hq
  obtain ⟨rd, hHa, hX⟩ := hR.honest
  have hcov : Covers coreProgram B2C.fs al B2C.H B2C.C r.hdr (D r).T r.img :=
    fun w hw ha ↦ (hR.img w.1).trans (hX.covers w hw ha)
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, -, -, hF⟩ :=
    Bridge.RefOk.framesA hR.name hHa hcov htr e List.mem_cons_self
  obtain ⟨i, rfl, -, -, -, -, hfsj, -, h1, h2⟩ := B2C.fn_of_idx hj
  rw [alignA_of hj] at hso
  have hmem : (q, B2C.PC.fpg o) ∈ (B2C.plumbOf (i + 1)).stat := getF_trieOf hso
  obtain ⟨h2q, -⟩ := B2C.stat_in (B2C.Shared.all _ h1 h2) hmem
  have hrd := hF.stat _ hmem h2q (by simpa [hfsj] using hq)
  have h2 : 2 ≤ e.I.t.fsz B2C.fs := hHa.cells.two_le e.I hI
  have hw : e.I.fp + B2C.fs e.I.t.name ≤ (D r).T.wordsA B2C.fs coreProgram.loop al :=
    honestA_within_node hI hIt (by omega)
  have hle := le_two_pow_logMem ((D r).T.wordsA B2C.fs coreProgram.loop al)
  have hlog : logMem ((D r).T.wordsA B2C.fs coreProgram.loop al) ≤ 28 := hR.log hr
  have h28 : 2 ^ logMem ((D r).T.wordsA B2C.fs coreProgram.loop al) ≤ 2 ^ 28 :=
    Nat.pow_le_pow_right (by norm_num) hlog
  have hκ : r.κ ≤ 28 := by rw [hR.κ]; exact hlog
  obtain ⟨-, hv⟩ := refRd_img hκ r.img _ _ (by omega) hrd
  rw [hv]
  rfl

end

end LeanVM.Guest.EndExec
