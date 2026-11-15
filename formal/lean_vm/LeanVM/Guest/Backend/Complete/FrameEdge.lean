/-
  LeanVM.Guest.Backend.Complete.FrameEdge

  The invariant at a block's edge flush and past an event that makes no value.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameInner

/-!
# The invariant at a block's edges

`winv_edge`: the walk's invariant after the flush before a branch or a `match` (`flushEdge`) and
the cells taken after it. `WInv.past`: past an event that makes no value (a branch's `emit`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The invariant at a branch's edges -/

section Inv

variable {ctx : Backend.Ctx} {I : Inst}

/-- **The invariant after a block's edge flush** (`flushEdge`), once the cells after it are
taken: the constraint's properties, the trace and the values in scope the scope walk's, the flush
placing only values it makes. -/
theorem winv_edge {C C' : (ℕ → E) → Prop} {st st' : St} {sc s₀ : SSt}
    (hinv : WInv ctx I C st sc) (h₀ : flushEdge ctx.retCells sc = .ok s₀)
    (hcok : COk I C' st'.next st'.scope st'.locs) (hn : st.next ≤ st'.next)
    (hr : st'.rest = s₀.rest) (hvw : VW I C' st' fun v => s₀.live.contains v = true)
    (hret : s₀.retDone = false → RetBlind ctx C')
    (hloc : ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest))
    (hch : st'.chainIn = none) (hpnt : PoolNT I st'.scope) (hlz : st'.lazy = none) :
    WInv ctx I C' st' s₀ := by
  have hfl : flushS ctx.retCells st.rest sc.live sc.retDone = .ok s₀ := by
    rw [← hinv.rest]
    exact (flushEdge_ok h₀).2
  obtain ⟨hseg, hlive, -⟩ := flushS_seg _ _ _ _ _ hfl
  have hall : allocsOf st.rest = allocsOf (flushSeg st.rest) ++ allocsOf s₀.rest := by
    conv_lhs => rw [hseg]
    rw [allocsOf_append]
  have hnd : (allocsOf (flushSeg st.rest) ++ allocsOf s₀.rest).Nodup := hall ▸ hinv.nodup
  have hlen : s₀.rest.length ≤ st.rest.length := by
    have h' := congrArg List.length hseg
    rw [List.length_append] at h'
    omega
  have hfr : ∀ v ∈ allocsOf st'.rest, st'.locs[v]? = none ∧ s₀.live.contains v = false := by
    intro v hv
    rw [hr] at hv
    obtain ⟨hst, hlv⟩ := hinv.fresh v (by rw [hall]; exact List.mem_append_right _ hv)
    have hns : v ∉ allocsOf (flushSeg st.rest) := fun h => List.disjoint_of_nodup_append hnd h hv
    have hlv' : s₀.live.contains v = false := by
      cases hx : s₀.live.contains v with
      | false => rfl
      | true => exact ((hlive v hx).elim (fun h => by rw [hlv] at h; cases h) hns).elim
    refine ⟨?_, hlv'⟩
    cases hx : st'.locs[v]? with
    | none => rfl
    | some x =>
      rcases hloc v (by rw [hx]; simp) with h | h
      · exact absurd hst h
      · exact absurd h hns
  exact ⟨hcok, hr.symm, hvw, le_trans hinv.two hn, le_trans hinv.abi hn,
    by rw [hr]; exact le_trans hlen hinv.fuel, fun hr' Ψ k w hk hC => hret hr' k hk Ψ w hC,
    by rw [hr]; exact hnd.of_append_right, hfr, hch, hpnt, hlz⟩

/-- **The invariant past an event that makes no value** (a branch's `emit`), the state's cells,
places, pools and chaining kept and no value waiting, the return area made later or no
earlier. -/
theorem WInv.past {C : (ℕ → E) → Prop} {st st' : St} {s s' : SSt} (hinv : WInv ctx I C st s)
    (hev : ∃ ev, s.rest = ev :: s'.rest ∧ ∀ vs k, ev ≠ .alloc vs k)
    (hlv : s'.live = s.live) (hrd : s'.retDone = false → s.retDone = false)
    (hn : st'.next = st.next) (hl : st'.locs = st.locs) (hs : st'.scope = st.scope)
    (hr : st'.rest = s'.rest) (hch : st'.chainIn = st.chainIn) (hz : st'.lazy = none) :
    WInv ctx I C st' s' := by
  obtain ⟨ev, hev, hna⟩ := hev
  have hst : st.rest = ev :: st'.rest := by rw [← hinv.rest, hev, hr]
  have hall : allocsOf st.rest = allocsOf st'.rest := by rw [hst, allocsOf_other hna]
  refine ⟨by rw [hn, hs, hl]; exact hinv.cok, hr.symm, fun v l hv hvl => ?_,
    by rw [hn]; exact hinv.two, by rw [hn]; exact hinv.abi, ?_, fun h => hinv.ret (hrd h),
    by rw [← hall]; exact hinv.nodup, fun v hv => ?_, by rw [hch]; exact hinv.chain,
    by rw [hs]; exact hinv.pnt, hz⟩
  · rw [hl] at hvl
    rw [hn]
    exact hinv.vw v l (by rw [← hlv]; exact hv) hvl
  · have := hinv.fuel
    rw [hst, List.length_cons] at this
    omega
  · obtain ⟨h1, h2⟩ := hinv.fresh v (by rw [hall]; exact hv)
    exact ⟨by rw [hl]; exact h1, by rw [hlv]; exact h2⟩

/-- A branch's `emit`, past the scope walk's. -/
theorem emit_past {s s' : SSt} (h : expectS isEmit "a branch" s = .ok s') :
    ∃ ev, s.rest = ev :: s'.rest ∧ ∀ vs k, ev ≠ .alloc vs k := by
  obtain ⟨ev, hr, he, -, -⟩ := expectS_ok h
  exact ⟨ev, hr, fun vs k h' => by subst h'; simp [isEmit] at he⟩

end Inv

end

end LeanVM.Guest.Backend.Complete
