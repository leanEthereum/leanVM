/-
  LeanVM.Guest.Memory.HeapSlots

  The deployed guest's advised buffers by function (`heapSlots`), and a decidable check that a
  function's subtree has none (`NoAdvG`), so that every valid tree of it pops no advised size.
-/

module

public import LeanVM.Guest.Memory.HeapPopsL
public import LeanVM.Guest.Memory.CalleeIdx
public import LeanVM.Guest.B1.Common.Find

/-!
# The advised buffers by function

`heapSlots f`: the indices, among the buffers `f` allocates, of those its `allocAdvice` hints stand
for (`EndExec.advSlots` is it on the program's functions, `advSlots_eq`).

`noAdvJ d j`: function `j` has no advised buffer, each of its callees has an index (`calleeIdx`),
and each callee index is `j` itself (a loop's tail call) or passes `noAdvJ (d - 1)`. `NoAdvG`
collects the functions passing it at some depth; it is call-closed (`noAdv_callsIn`), so a valid
tree of such a function pops no advised size (`heapPops_noAdv`). `noAdvBut j ex`: each callee of
function `j` passes it or is named in `ex` (`noAdvBut_spec`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- **The advised buffers' indices of each function** of the deployed guest. -/
def heapSlots (f : String) : List ℕ :=
  match f with
  | "main" => [0, 1, 4, 5, 6, 7, 8]
  | "claim_list_digest" => [0]
  | "da_verify" => [0, 2]
  | "verify_sub" => [5]
  | "verify_tables" => [108, 109, 111]
  | _ => []

/-- **Function `j` and its callees, `d` calls deep, have no advised buffer.** -/
noncomputable def noAdvJ : ℕ → ℕ → Bool
  | 0, _ => false
  | d + 1, j => match coreProgram[j]? with
    | none => false
    | some fn => (heapSlots fn.name).isEmpty && (Stmt.blockCallees fn.body).all (fun g => (calleeIdx j g).isSome) &&
        (Data.calleesJ j).all fun k => k == j || noAdvJ d k

/-- The functions passing the check at some depth. -/
def NoAdvG (g : String) : Prop := ∃ d j, (coreProgram[j]?).map Fn.name = some g ∧ noAdvJ d j = true

theorem noAdvG_slots {g : String} (h : NoAdvG g) : heapSlots g = [] := by
  obtain ⟨d, j, hn, hj⟩ := h
  cases d with
  | zero => simp [noAdvJ] at hj
  | succ d =>
    obtain ⟨fn, hfn, rfl⟩ := Option.map_eq_some_iff.mp hn
    rw [noAdvJ, hfn] at hj
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hj
    exact hj.1.1

/-- **The functions passing the check are call-closed.** -/
theorem noAdv_callsIn : CallsIn coreProgram NoAdvG := by
  refine callsIn_of_callees fun f hf fn hfn g hg => ?_
  obtain ⟨d, j, hn, hj⟩ := hf
  cases d with
  | zero => simp [noAdvJ] at hj
  | succ d =>
    obtain ⟨fn', hfn', rfl⟩ := Option.map_eq_some_iff.mp hn
    have e : fn = fn' := Option.some.inj (hfn.symm.trans (coreProgram_find?_at hfn'))
    subst e
    have hj' := hj
    rw [noAdvJ, hfn'] at hj'
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hj'
    obtain ⟨⟨-, hcal⟩, hks⟩ := hj'
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hcal g hg)
    have hs := calleeIdx_spec hk
    rcases hks k (List.mem_of_find?_eq_some hk) with rfl | h
    · exact ⟨d + 1, k, hs, hj⟩
    · exact ⟨d, k, hs, h⟩

/-- **A valid tree of a function passing the check pops no advised size.** -/
theorem heapPops_noAdv {rd : Reader} {t : Tree} {args rets : List E} (hg : NoAdvG t.name)
    (hv : t.Valid coreProgram rd args rets) : t.heapPops heapSlots = [] :=
  heapPops_nil noAdv_callsIn (fun _ h => noAdvG_slots h) t hg hv

/-- **Each callee of function `j` passes the check, `d` calls deep, or is named in `ex`.** -/
noncomputable def noAdvBut (d j : ℕ) (ex : List String) : Bool :=
  match coreProgram[j]? with
  | none => false
  | some fn => (Stmt.blockCallees fn.body).all (fun g => (calleeIdx j g).isSome) &&
      (Data.calleesJ j).all fun k => noAdvJ d k || ex.any fun e => decide (Data.nameT.find k = some e)

theorem noAdvBut_spec {d j : ℕ} {ex : List String} {f : String} {fn : Fn} (h : noAdvBut d j ex = true)
    (hn : (coreProgram[j]?).map Fn.name = some f) (hf : coreProgram.find? f = some fn) :
    ∀ g ∈ Stmt.blockCallees fn.body, NoAdvG g ∨ g ∈ ex := by
  intro g hg
  obtain ⟨fn', hfn', rfl⟩ := Option.map_eq_some_iff.mp hn
  have e : fn = fn' := Option.some.inj (hf.symm.trans (coreProgram_find?_at hfn'))
  subst e
  rw [noAdvBut, hfn'] at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcal, hks⟩ := h
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hcal g hg)
  have hs := calleeIdx_spec hk
  rcases hks k (List.mem_of_find?_eq_some hk) with h | ⟨e, he, hke⟩
  · exact Or.inl ⟨d, k, hs, h⟩
  · have hn' := List.find?_some hk
    simp only [decide_eq_true_eq] at hn'
    rw [hn'] at hke
    exact Or.inr (Option.some.inj hke ▸ he)

/-- **The calls of a path of function `j` are to functions passing the check or named in `ex`.** -/
theorem noAdvBut_calls {d j : ℕ} {ex : List String} {f : String} {fn : Fn} (h : noAdvBut d j ex = true)
    (hn : (coreProgram[j]?).map Fn.name = some f) (hf : coreProgram.find? f = some fn) {σ : Val}
    {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs) : ∀ c ∈ calls es, NoAdvG c.f ∨ c.f ∈ ex :=
  fun c hc => noAdvBut_spec h hn hf c.f (walk_callees (σ := σ) fn.body (by rw [hw]; exact hc))

/-- Function `j`'s callee `g` passes the check. -/
noncomputable def noAdvCallee (j : ℕ) (g : String) : Bool :=
  match calleeIdx j g with
  | some k => noAdvJ 16 k
  | none => false

theorem noAdvG_of_callee {j : ℕ} {g : String} (h : noAdvCallee j g = true) : NoAdvG g := by
  unfold noAdvCallee at h
  split at h
  · next k hk => exact ⟨16, k, calleeIdx_spec hk, h⟩
  · exact absurd h Bool.false_ne_true

/-- **A callee passing the check pops no advised size**, entered or not. -/
theorem heapPops_kid_noAdv {rd : Reader} {σ : Val} {c : Call} {k : Tree} (hn : k.name = c.f) (hg : NoAdvG c.f)
    (hv : if c.taken then k.Valid coreProgram rd (c.args.map σ) (c.rets.map σ)
      else (∃ f σ', k = .phantom f σ') ∧ Phantom coreProgram k (c.args.map σ)) : k.heapPops heapSlots = [] := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at hv
    exact heapPops_noAdv (hn ▸ hg) hv
  · rw [ite_eq_right ht] at hv
    obtain ⟨⟨f, σ', rfl⟩, -⟩ := hv
    rw [Tree.heapPops]

/-- **A node whose callees all pass the check pops its own advised sizes alone.** -/
theorem heapPops_own {d j : ℕ} {f : String} {σ : Val} {bufs : List ℕ} {ks : List Tree} {rd : Reader}
    {args rets : List E} (h : noAdvBut d j [] = true) (hn : (coreProgram[j]?).map Fn.name = some f)
    (hv : (Tree.node f σ bufs ks).Valid coreProgram rd args rets) :
    (Tree.node f σ bufs ks).heapPops heapSlots = (heapSlots f).map (advEntry bufs) := by
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
  rw [heapPops_node, heapPopsKids_nil noAdv_callsIn (fun _ h => noAdvG_slots h) ks σ (calls es)
    (fun c hc => (noAdvBut_calls h hn hf hw c hc).resolve_right (by simp)) hk, List.append_nil]

end

end LeanVM.Guest.Memory
