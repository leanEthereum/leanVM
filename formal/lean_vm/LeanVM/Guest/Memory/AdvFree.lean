/-
  LeanVM.Guest.Memory.AdvFree

  The functions of the guest from which no function with advised buffers is reachable, by one check per
  function against its callee table (`advFreeChk`).
-/

module

public import LeanVM.Guest.Memory.HeapSlots
public import LeanVM.Guest.Memory.Family
public import LeanVM.Guest.CoreRef

/-!
# Functions below no advised buffer

`advBad`: the functions whose subtrees hold an advised buffer (`main`, the children's loop, `verify_sub`,
`verify_tables`, `claim_list_digest`, `da_verify`). `advFreeChk j fn`: function `j` is one of them, or it has no
advised buffer and each of its callees has an index (`calleeIdx`) outside them. `AdvFreeOk`: every function passes
it (kernel-checked in `AdvFreeOk`'s module). `AdvFree`: the functions outside `advBad`; given `AdvFreeOk`, they are
call-closed (`advFree_callsIn`) without advised buffers (`advFree_slots`), so a valid tree of one pops no advised size
(`heapPops_advFree`). `advFreeBut j ex`: each callee of function `j` is in `AdvFree` or named in `ex`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The functions whose subtrees hold an advised buffer, by index. -/
def advBad : List ℕ :=
  [idx% «main», idx% «main_loop4», idx% «verify_sub», idx% «verify_tables», idx% «claim_list_digest»,
    idx% «da_verify»]

/-- **Function `j`'s check**: one of `advBad`, or no advised buffer and its callees outside them. -/
noncomputable def advFreeChk (j : ℕ) (fn : Fn) : Bool :=
  decide (j ∈ advBad) || ((heapSlots fn.name).isEmpty && (Stmt.blockCallees fn.body).all fun g =>
    match calleeIdx j g with
    | some k => !decide (k ∈ advBad)
    | none => false)

/-- **Every function passes `advFreeChk`.** -/
def AdvFreeOk : Prop := RangeOk advFreeChk 0 coreProgram.length

/-- The functions outside `advBad`. -/
def AdvFree (g : String) : Prop := ∃ j, (coreProgram[j]?).map Fn.name = some g ∧ j ∉ advBad

variable (hA : AdvFreeOk)
include hA

theorem advFree_get {g : String} (h : AdvFree g) : ∃ j fn, coreProgram[j]? = some fn ∧ fn.name = g ∧
    (heapSlots fn.name).isEmpty = true ∧ ∀ g' ∈ Stmt.blockCallees fn.body, ∃ k, calleeIdx j g' = some k ∧ k ∉ advBad := by
  obtain ⟨j, hn, hb⟩ := h
  obtain ⟨fn, hfn, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hfn
  have hc := RangeOk.all hA hj
  simp only [advFreeChk, Bool.or_eq_true, decide_eq_true_eq, hb, false_or, Bool.and_eq_true,
    List.all_eq_true] at hc
  refine ⟨j, _, hfn, rfl, hc.1, fun g' hg' => ?_⟩
  have h2 := hc.2 g' hg'
  split at h2
  · next k hk => exact ⟨k, hk, by simpa using h2⟩
  · exact absurd h2 Bool.false_ne_true

theorem advFree_slots {g : String} (h : AdvFree g) : heapSlots g = [] := by
  obtain ⟨j, fn, -, rfl, hs, -⟩ := advFree_get hA h
  exact List.isEmpty_iff.mp hs

/-- **The functions outside `advBad` are call-closed.** -/
theorem advFree_callsIn : CallsIn coreProgram AdvFree := by
  refine callsIn_of_callees fun f hf fn hfn g hg => ?_
  obtain ⟨j, fn', hfn', rfl, -, hc⟩ := advFree_get hA hf
  have e : fn = fn' := Option.some.inj (hfn.symm.trans (coreProgram_find?_at hfn'))
  subst e
  obtain ⟨k, hk, hb⟩ := hc g hg
  exact ⟨k, calleeIdx_spec hk, hb⟩

/-- **A valid tree of a function outside `advBad` pops no advised size.** -/
theorem heapPops_advFree {rd : Reader} {t : Tree} {args rets : List E} (hg : AdvFree t.name)
    (hv : t.Valid coreProgram rd args rets) : t.heapPops heapSlots = [] :=
  heapPops_nil (advFree_callsIn hA) (fun _ h => advFree_slots hA h) t hg hv

omit hA in
/-- **Each callee of function `j` has an index outside `advBad`, or is named in `ex`.** -/
noncomputable def advFreeBut (j : ℕ) (ex : List String) : Bool :=
  match coreProgram[j]? with
  | none => false
  | some fn => (Stmt.blockCallees fn.body).all fun g => decide (g ∈ ex) ||
      match calleeIdx j g with
      | some k => !decide (k ∈ advBad)
      | none => false

omit hA in
theorem advFreeBut_calls {j : ℕ} {ex : List String} {f : String} {fn : Fn} (h : advFreeBut j ex = true)
    (hn : (coreProgram[j]?).map Fn.name = some f) (hf : coreProgram.find? f = some fn) {σ : Val}
    {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs) : ∀ c ∈ calls es, AdvFree c.f ∨ c.f ∈ ex := by
  intro c hc
  have hg := walk_callees (σ := σ) fn.body (c := c) (by rw [hw]; exact hc)
  obtain ⟨fn', hfn', rfl⟩ := Option.map_eq_some_iff.mp hn
  have e : fn = fn' := Option.some.inj (hf.symm.trans (coreProgram_find?_at hfn'))
  subst e
  rw [advFreeBut, hfn'] at h
  have h2 := List.all_eq_true.mp h c.f hg
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
  rcases h2 with h2 | h2
  · exact Or.inr h2
  · split at h2
    · next k hk => exact Or.inl ⟨k, calleeIdx_spec hk, by simpa using h2⟩
    · exact absurd h2 Bool.false_ne_true

end

end LeanVM.Guest.Memory
