/-
  LeanVM.Guest.Bridge.FrameMapA

  The frame-to-instance map along the reference run, on the aligned allocator: every frame of every
  state of the tree track is an honest instance, a node of its function, whose frame holds what the
  completeness check reads.
-/

module

public import LeanVM.Guest.Bridge.RefTrace
public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.B2C.FrameAll

/-!
# The frame-to-instance map, aligned

`RefOk.framesA`: on the deployed guest's honest tree `T` placed by the aligned allocator (`al` the
per-callee flag) and any memory `L` covering its writes, every frame `e` of a state of the track
against the run is an honest instance, a node of the function of index `j` (`idxOf`, `coreOf j` its
function), on its whole path `e.pre ++ e.es`, and its frame holds on `L` what B2's completeness check
reads (`FrameHolds`), by `B2C.b2Hyps.frame`. The bus era's `RefOk.frames` on Hotwire's layout.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

public section

variable {al : String → Bool} {hdr : E × E} {rd rd0 : Reader} {T : Tree} {κ : ℕ} {L : MemoryImage κ}

/-- **The frame-to-instance map**: every frame of a state of the track is an honest instance, a node of
the function of index `j`, whose frame holds what the completeness check reads on its path. -/
theorem RefOk.framesA (hT : T.name = "main")
    (hH : HonestAtA coreProgram B2C.fs al B2C.H B2C.C hdr T B2C.cert rd [] [])
    (hL : Covers coreProgram B2C.fs al B2C.H B2C.C hdr T L) {M : ℕ → E} {ent : String → ℕ}
    {alg : String → ℕ → Option (List Stmt)} {pc fp : ℕ} {s : List Pop × List Ent}
    (h : RefOk coreProgram rd0 (honestInstsA coreProgram B2C.fs al B2C.H hdr T) T M ent alg pc fp s) :
    ∀ e ∈ s.2, e.I ∈ honestInstsA coreProgram B2C.fs al B2C.H hdr T ∧ ∃ j bufs kids vs,
      idxOf e.I.t.name = some j ∧ e.I.t = .node e.I.t.name e.σ bufs kids ∧ coreOf j = e.fn ∧
      walk e.σ e.fn.body = .ret (e.pre ++ e.es) vs ∧ FrameHolds L j e.I.fp e.σ (e.pre ++ e.es) vs e.I.kidFps e.I.hdr := by
  intro e he
  have hE := h.track.ents e he
  obtain ⟨f, bufs, kids, ht⟩ := hE.node
  obtain ⟨vs, hw, -⟩ := hE.path
  have hn : e.I.t.name = f := by rw [ht]; rfl
  obtain ⟨j, hj⟩ := idxOf_of_find hE.find
  obtain ⟨i, rfl, hi, -, hfi, hc, -⟩ := fn_of_idx hj
  have hfn : coreOf (i + 1) = e.fn := by rw [hc]; exact Option.some.inj (hfi.symm.trans hE.find)
  refine ⟨hE.mem, i + 1, bufs, kids, vs, hj, by rw [hn]; exact ht, hfn, hw, ?_⟩
  exact b2Hyps.frame al hdr rd T hT hH L hL e.I hE.mem f e.σ bufs kids ht (i + 1) (hn ▸ hj) (e.pre ++ e.es) vs
    (by rw [hfn]; exact hw)

end

end LeanVM.Guest.Bridge
