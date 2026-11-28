module

public import LeanVM.Guest.Complete.Compose

/-!
# Calls that take no words of their own

A call whose subtree allocates nothing it stores into and writes no heap word through a hint takes
no words of its own (`CallCompletes0`): on every memory satisfying its inputs it has a valid tree,
its valuation chosen per memory (a range check's witnesses are reads). Such a call completes
(`CallCompletes0.toCallCompletes`). `callCompletes0_node`: a node from a valuation per memory and
its callees' trees.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1

@[expose] public section

/-- **A call completes with no words of its own**: on every memory defined on its first `2^k` words
satisfying `Pre`, it has a valid tree satisfying `Post`, its buffers its body's. -/
def CallCompletes0 (k : ℕ) (f : String) (args rets : List E) (Pre : Reader → Prop)
    (Post : Reader → Tree → Prop) : Prop :=
  ∀ rd, LowDef k rd → Pre rd →
    ∃ t : Tree, t.name = f ∧ t.Valid coreProgram rd args rets ∧ t.BufsOk coreProgram ∧ Post rd t

theorem CallCompletes0.toCallCompletes {k : ℕ} {f : String} {args rets : List E} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} (h : CallCompletes0 k f args rets Pre Post) :
    CallCompletes k f args rets Pre Post :=
  fun b => ⟨0, [], wordsIn_nil b, fun rd hl _ hp => h rd hl hp⟩

theorem CallCompletes0.mono {k : ℕ} {f : String} {args rets : List E} {Pre Pre' : Reader → Prop}
    {Post Post' : Reader → Tree → Prop} (h : CallCompletes0 k f args rets Pre Post)
    (hpre : ∀ rd, Pre' rd → Pre rd) (hpost : ∀ rd t, Pre' rd → Post rd t → Post' rd t) :
    CallCompletes0 k f args rets Pre' Post' := fun rd hl hp => by
  obtain ⟨t, hn, hv, hb, hq⟩ := h rd hl (hpre rd hp)
  exact ⟨t, hn, hv, hb, hpost rd t hp hq⟩

/-- A node's events are its path's. -/
theorem events_node {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn} {es : List Ev}
    {vs : List V} (hf : coreProgram.find? f = some fn) (hw : walk σ fn.body = .ret es vs) :
    (Memory.Tree.node f σ bufs kids).events coreProgram = es := by
  simp only [Tree.events, Tree.name, Tree.val, hf, hw]

/-- A node's entries: its path's, its callees' spliced in. -/
theorem pops_node {rd : Reader} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn}
    {es : List Ev} {vs : List V} (hf : coreProgram.find? f = some fn) (hw : walk σ fn.body = .ret es vs) :
    (Memory.Tree.node f σ bufs kids).pops coreProgram rd = splice rd σ es (Tree.popsKids coreProgram rd kids) := by
  rw [Tree.pops, events_node hf hw]

/-- **A node completes with no words of its own** from a valuation per memory whose path returns
`rets` from `args`, its events holding, and its callees' trees. -/
theorem callCompletes0_node {k : ℕ} {f : String} {args rets : List E} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop}
    (h : ∀ rd, LowDef k rd → Pre rd → ∃ (σ : Val) (fn : Fn) (es : List Ev) (vs : List V) (ts : List Tree),
      coreProgram.find? f = some fn ∧ fn.params.map σ = args ∧ walk σ fn.body = .ret es vs ∧
      vs.map σ = rets ∧ (∀ e ∈ es, e.Holds rd σ) ∧ Tree.KidsValid coreProgram rd σ (calls es) ts ∧
      Tree.BufsOkKids coreProgram ts ∧ Post rd (.node f σ (allocs σ es) ts)) :
    CallCompletes0 k f args rets Pre Post := fun rd hl hp => by
  obtain ⟨σ, fn, es, vs, ts, hf, hpar, hw, hr, hev, hk, hbs, hpost⟩ := h rd hl hp
  refine ⟨.node f σ (allocs σ es) ts, rfl, ⟨fn, hf, hpar, es, vs, hw, hr, hev, hk⟩, ?_, hpost⟩
  rw [Tree.BufsOk, events_node hf hw]
  exact ⟨rfl, hbs⟩

/-- A taken call's tree among a node's callees. -/
theorem kidsValid_cons_taken {rd : Reader} {σ : Val} {c : Call} {cs : List Call} {t : Tree} {ts : List Tree}
    (hc : c.taken = true) (hn : t.name = c.f) (hv : t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ))
    (hs : Tree.KidsValid coreProgram rd σ cs ts) : Tree.KidsValid coreProgram rd σ (c :: cs) (t :: ts) := by
  rw [Tree.KidsValid]
  simp only [hc, ↓reduceIte]
  exact ⟨hn, hv, hs⟩

/-- A skipped call's phantom among a node's callees. -/
theorem kidsValid_cons_skip {rd : Reader} {σ σ' : Val} {c : Call} {cs : List Call} {ts : List Tree} {fn : Fn}
    (hc : c.taken = false) (hf : coreProgram.find? c.f = some fn) (hp : fn.params.map σ' = c.args.map σ)
    (hs : Tree.KidsValid coreProgram rd σ cs ts) :
    Tree.KidsValid coreProgram rd σ (c :: cs) (.phantom c.f σ' :: ts) := by
  rw [Tree.KidsValid]
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  exact ⟨rfl, ⟨⟨c.f, σ', rfl⟩, fn, hf, hp⟩, hs⟩

theorem kidsValid_nil {rd : Reader} {σ : Val} : Tree.KidsValid coreProgram rd σ [] [] := by
  rw [Tree.KidsValid]; trivial

end
end LeanVM.Guest.Complete
