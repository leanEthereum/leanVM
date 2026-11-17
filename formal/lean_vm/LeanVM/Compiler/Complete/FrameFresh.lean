/-
  LeanVM.Compiler.Complete.FrameFresh

  A block's placement leaves unplaced the values the trace it leaves makes.
-/

module

public import LeanVM.Compiler.Complete.FrameRest

/-!
# Values the trace makes later stay unplaced

A placement step places no value but one an event it passes makes, the value made lazily at its
start and a frame address's pointer (`RR`, `placeBlock_r`). From a state with no lazy value and a
trace whose values are distinct, a value the trace left at the end still makes is made by no
event passed; a frame address's pointer is not one of them when the scope walk's trace left
makes none (`blockRest` and `inBlock_rs` tie the two traces left). So such a value unplaced at the
start is unplaced at the end (`blockFresh`, `inBlockFresh`).
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- A value the trace left at `st'` makes, unplaced at `st`, is unplaced at `st'`, when no value
is lazy at `st`, the trace at `st` makes distinct values and `S` allows none of them. -/
theorem rR_fresh {S : V → Prop} {st st' : St} (h : RR S st st') (hnd : (allocsOf st.rest).Nodup)
    (hz : st.lazy = none) (hS : ∀ v ∈ allocsOf st'.rest, ¬S v) :
    ∀ v ∈ allocsOf st'.rest, st.locs[v]? = none → st'.locs[v]? = none := by
  obtain ⟨pre, he, h1, _, _⟩ := h
  intro v hv hn
  by_contra hne
  rcases h1 v hne with h | h | ⟨k, h⟩ | h
  · exact h hn
  · rw [he, allocsOf_app_rr, List.nodup_append] at hnd
    exact hnd.2.2 v h v hv rfl
  · rw [hz] at h; cases h
  · exact hS v hv h

/-- **`BlockFresh`**: a block from a state with no lazy value and a trace of distinct values
leaves unplaced every value the trace left makes, the frame addresses among its atoms being none
of the scope walk's. -/
theorem blockFresh : ∀ (ctx : Ctx) (ss : List Stmt) (st : St) (s s' : SSt),
    scopeBlock ctx.retCells ss s = .ok s' → st.rest = s.rest → st.rest.length ≤ ctx.fuel →
    (allocsOf st.rest).Nodup → st.lazy = none →
    (∀ v run, Atom.frameAddr v run ∈ atomsIn ss → v ∉ allocsOf s'.rest) →
    wpP (placeBlock ss) ctx st fun _ st' =>
      ∀ v ∈ allocsOf st'.rest, st.locs[v]? = none → st'.locs[v]? = none := by
  intro ctx ss st s s' h hr hf hnd hz hfa
  exact wp_mono (wp_and (placeBlock_r ss st) (blockRest ss st s s' h hr hf))
    fun _ _ ⟨hq, he⟩ => rR_fresh hq hnd hz fun v hv ⟨run, hm⟩ => hfa v run hm (he ▸ hv)

/-- **`InBlockFresh`**: the same for a block in a scope of its own, against `scopeInner`. -/
theorem inBlockFresh : ∀ (ctx : Ctx) (z : List Stmt) (st : St) (sc sc' : SSt),
    scopeInner ctx.retCells (fun s' => scopeBlock ctx.retCells z s') sc = .ok sc' →
    st.rest = sc.rest → st.rest.length ≤ ctx.fuel → (allocsOf st.rest).Nodup →
    st.lazy = none → (∀ v run, Atom.frameAddr v run ∈ atomsIn z → v ∉ allocsOf sc'.rest) →
    wpP (inBlock (placeBlock z)) ctx st fun _ st' =>
      ∀ v ∈ allocsOf st'.rest, st.locs[v]? = none → st'.locs[v]? = none := by
  intro ctx z st sc sc' h hr hf hnd hz hfa
  have hrest : wpP (inBlock (placeBlock z)) ctx st fun _ st' => st'.rest = sc'.rest :=
    inBlock_rs (m := placeBlock z) (s := st)
      (fun s₁ s₂ st h₂ l => placeBlock_rs z s₁ s₂ st h₂ l) (scopeBlock_cons _ z) h
      (by rw [← hr]; exact hf) hr
  exact wp_mono (wp_and (inBlock_r (fun st => placeBlock_r z st) st) hrest)
    fun _ _ ⟨hq, he⟩ => rR_fresh hq hnd hz fun v hv ⟨run, hm⟩ => hfa v run hm (he ▸ hv)

end

end LeanVM.Compiler.Complete
