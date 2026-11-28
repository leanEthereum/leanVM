module

public import LeanVM.Guest.Complete.Call0
public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.Memory.Straight

/-!
# Straight nodes

A function whose body is a straight block (atoms, calls, guarded calls) then a `ret` walks every
statement (`walk_straight`), its calls those of its block (`straight_parts`). Such a node completes
from a valuation on which every atom holds and every guard is in `K`, and its callees' trees:
per memory with no words of its own (`callCompletes0_straight`), or from every base with its own
words (`callCompletes_straight`). Its entries are its block's, its callees' spliced in
(`pops_straight`). A function whose subtree pins its computed hints is exact on every valid tree
(`CallCompletes0.exact`, `CallCompletes.exact`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1

@[expose] public section

/-- What a straight statement asks of a valuation: an atom holds, a guard is in `K`. -/
def SOk (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .callIf c _ _ => IsInK (σ c)
  | _ => True

theorem events_straight {rd : Reader} {σ : Val} {pre : List Stmt} (h : ∀ s ∈ pre, SOk rd σ s) :
    ∀ e ∈ pre.flatMap (slEvs σ), e.Holds rd σ := by
  intro e he
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  have h0 := h s hs
  cases s with
  | atom a =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; exact h0
  | call f args rets =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; trivial
  | callIf c f args =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact h0
    · split <;> trivial
  | _ => simp [slEvs] at he

/-- **A straight node's entries**: its block's, its callees' spliced in. -/
theorem pops_straight {rd : Reader} {f : String} {fn : Fn} {pre : List Stmt} {vs : List V}
    (hf : coreProgram.find? f = some fn) (hb : fn.body = pre ++ [.ret vs])
    (hs : pre.all Stmt.straight = true) (σ : Val) (bufs : List ℕ) (ts : List Tree) :
    (Memory.Tree.node f σ bufs ts).pops coreProgram rd =
      splice rd σ (pre.flatMap (slEvs σ)) (Tree.popsKids coreProgram rd ts) := by
  rw [pops_node hf (by rw [hb]; exact walk_straight σ vs pre hs)]

/-- **A straight node completes with no words of its own** from a valuation per memory. -/
theorem callCompletes0_straight {k : ℕ} {f : String} {args rets : List E} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {fn : Fn} {pre : List Stmt} {vs : List V}
    (hf : coreProgram.find? f = some fn) (hb : fn.body = pre ++ [.ret vs]) (hs : pre.all Stmt.straight = true)
    (h : ∀ rd, LowDef k rd → Pre rd → ∃ (σ : Val) (ts : List Tree), fn.params.map σ = args ∧
      vs.map σ = rets ∧ (∀ s ∈ pre, SOk rd σ s) ∧
      Tree.KidsValid coreProgram rd σ ((pre.filterMap Stmt.callS).map (mkCall σ)) ts ∧
      Tree.BufsOkKids coreProgram ts ∧ Post rd (.node f σ (allocs σ (pre.flatMap (slEvs σ))) ts)) :
    CallCompletes0 k f args rets Pre Post :=
  callCompletes0_node fun rd hl hp => by
    obtain ⟨σ, ts, hpar, hr, hok, hk, hbs, hpost⟩ := h rd hl hp
    have hw : walk σ fn.body = .ret (pre.flatMap (slEvs σ)) vs := by rw [hb]; exact walk_straight σ vs pre hs
    exact ⟨σ, fn, _, vs, ts, hf, hpar, hw, hr, events_straight hok,
      by rw [(straight_parts σ pre hs).2.2.2]; exact hk, hbs, hpost⟩

/-- **A straight node completes** from every base: its own words, a valuation fixed before the
memory, its atoms and guards holding on every memory holding its words and inputs, its callees
complete after its words. -/
theorem callCompletes_straight {k : ℕ} {f : String} {args rets : List E} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {fn : Fn} {pre : List Stmt} {vs : List V}
    (hf : coreProgram.find? f = some fn) (hb : fn.body = pre ++ [.ret vs]) (hs : pre.all Stmt.straight = true)
    (h : ∀ b, ∃ (m : ℕ) (Wo : Words) (σ : Val) (Qs : List (Reader → Tree → Prop)),
      WordsIn Wo b m ∧ fn.params.map σ = args ∧ vs.map σ = rets ∧
      (∀ rd, LowDef k rd → HoldsWords rd Wo → Pre rd → ∀ s ∈ pre, SOk rd σ s) ∧
      KidsCompl k σ (fun rd => HoldsWords rd Wo ∧ Pre rd) Qs ((pre.filterMap Stmt.callS).map (mkCall σ)) ∧
      ∀ rd ts, LowDef k rd → HoldsWords rd Wo → Pre rd →
        Tree.KidsValid coreProgram rd σ ((pre.filterMap Stmt.callS).map (mkCall σ)) ts →
        KidsPost rd Qs ((pre.filterMap Stmt.callS).map (mkCall σ)) ts →
        Post rd (.node f σ (allocs σ (pre.flatMap (slEvs σ))) ts)) :
    CallCompletes k f args rets Pre Post :=
  callCompletes_node fun b => by
    obtain ⟨m, Wo, σ, Qs, hW, hpar, hr, hok, hk, hpost⟩ := h b
    have hw : walk σ fn.body = .ret (pre.flatMap (slEvs σ)) vs := by rw [hb]; exact walk_straight σ vs pre hs
    have hc := (straight_parts σ pre hs).2.2.2
    refine ⟨m, Wo, σ, fn, _, vs, Qs, hW, hf, hpar, hw, hr,
      fun rd hl ho hp => events_straight (hok rd hl ho hp), by rw [hc]; exact hk, fun rd ts hl ho hp hv hq => ?_⟩
    rw [hc] at hv hq
    exact hpost rd ts hl ho hp hv hq

/-- A call whose subtree pins its computed hints completes exact at every node. -/
theorem CallCompletes0.exact {k : ℕ} {f : String} {args rets : List E} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} (h : CallCompletes0 k f args rets Pre Post) (hx : ExactFreeG f) :
    CallCompletes0 k f args rets Pre (fun rd t => Post rd t ∧ t.Every (ExactAt coreProgram rd)) :=
  fun rd hl hp =>
    let ⟨t, hn, hv, hb, hq⟩ := h rd hl hp
    ⟨t, hn, hv, hb, hq, every_exact_of_free hx hv hn rd⟩

theorem CallCompletes.exact {k : ℕ} {f : String} {args rets : List E} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} (h : CallCompletes k f args rets Pre Post) (hx : ExactFreeG f) :
    CallCompletes k f args rets Pre (fun rd t => Post rd t ∧ t.Every (ExactAt coreProgram rd)) :=
  fun b =>
    let ⟨n, W, hW, h'⟩ := h b
    ⟨n, W, hW, fun rd hl hw hp =>
      let ⟨t, hn, hv, hb, hq⟩ := h' rd hl hw hp
      ⟨t, hn, hv, hb, hq, every_exact_of_free hx hv hn rd⟩⟩

theorem CallCompletes.monoPP {k : ℕ} {f : String} {args rets : List E} {Pre Pre' : Reader → Prop}
    {Post Post' : Reader → Tree → Prop} (h : CallCompletes k f args rets Pre Post)
    (hpre : ∀ rd, Pre' rd → Pre rd) (hpost : ∀ rd t, Pre' rd → Post rd t → Post' rd t) :
    CallCompletes k f args rets Pre' Post' :=
  fun b =>
    let ⟨n, W, hW, h'⟩ := h b
    ⟨n, W, hW, fun rd hl hw hp =>
      let ⟨t, hn, hv, hb, hq⟩ := h' rd hl hw (hpre rd hp)
      ⟨t, hn, hv, hb, hpost rd t hp hq⟩⟩

/-! ## Callees -/

theorem kidsCompl_nil {k : ℕ} {σ : Val} {Pk : Reader → Prop} {Qs : List (Reader → Tree → Prop)} :
    KidsCompl k σ Pk Qs [] := by rw [KidsCompl]; trivial

/-- An entered call completing among a node's callees. -/
theorem kidsCompl_cons_taken {k : ℕ} {σ : Val} {Pk : Reader → Prop} {Q : Reader → Tree → Prop}
    {Qs : List (Reader → Tree → Prop)} {c : Call} {cs : List Call} {f : String} {args rets : List E}
    (ht : c.taken = true) (hf : c.f = f) (ha : c.args.map σ = args) (hr : c.rets.map σ = rets)
    (h : CallCompletes k f args rets Pk Q) (hs : KidsCompl k σ Pk Qs cs) :
    KidsCompl k σ Pk (Q :: Qs) (c :: cs) := by
  rw [KidsCompl]
  simp only [ht, ↓reduceIte, List.headD_cons, List.tail_cons]
  rw [hf, ha, hr]
  exact ⟨h, hs⟩

/-- A skipped call among a node's callees: a phantom on its arguments. -/
theorem kidsCompl_cons_skip {k : ℕ} {σ σ' : Val} {Pk : Reader → Prop} {Q : Reader → Tree → Prop}
    {Qs : List (Reader → Tree → Prop)} {c : Call} {cs : List Call} {fn : Fn}
    (ht : c.taken = false) (hf : coreProgram.find? c.f = some fn) (hp : fn.params.map σ' = c.args.map σ)
    (hs : KidsCompl k σ Pk Qs cs) : KidsCompl k σ Pk (Q :: Qs) (c :: cs) := by
  rw [KidsCompl]
  simp only [ht, Bool.false_eq_true, ↓reduceIte, List.tail_cons]
  exact ⟨⟨σ', fn, hf, hp⟩, hs⟩

end
end LeanVM.Guest.Complete
