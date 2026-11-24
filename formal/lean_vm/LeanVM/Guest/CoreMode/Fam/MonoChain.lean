/-
  LeanVM.Guest.CoreMode.Fam.MonoChain

  A valid node's body holding at its own valuation, its callees as trees within its words.
-/

module

public import LeanVM.Guest.CoreMode.Fam.Down
public import LeanVM.Guest.CoreMode.Fam.LoopTree

/-!
# Trees, their words and their bodies

`KidRel P rd fs T`: a call relation of trees, a valid tree of the callee within `T` words.
`holds_of_valid`: a valid node's body holds at the node's valuation, its calls of `KidRel` within
the node's words (`Tree.Valid.rel` keeps no valuation). `insts_total`: each callee's words are
below its caller's, so every instance's words are at most the root's (`insts_down`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

section

variable {rd : Reader} {fs : String → ℕ} {P : Core.Program}

/-- **Calls as trees**: a valid tree of the callee, of fewer than `T` words. -/
def KidRel (P : Core.Program) (rd : Reader) (fs : String → ℕ) (T : ℕ) : CallRel :=
  fun g args rets => ∃ t : Tree, t.Valid P rd args rets ∧ t.name = g ∧ t.total fs < T

theorem kidsValid_kidRel {T : ℕ} : ∀ (σ : Val) (ks : List Tree) (cs : List Call),
    Tree.KidsValid P rd σ cs ks → (∀ k ∈ ks, k.total fs < T) → ∀ c ∈ cs, c.taken = true →
      KidRel P rd fs T c.f (c.args.map σ) (c.rets.map σ)
  | _, [], [], _, _, _, hc, _ => (List.not_mem_nil hc).elim
  | σ, k :: ks, c :: cs, ⟨hn, hk, hks⟩, hT, c', hc', ht => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · rw [ite_eq_left ht] at hk
        exact ⟨k, hk, hn, hT k List.mem_cons_self⟩
      · exact kidsValid_kidRel σ ks cs hks (fun k' h ↦ hT k' (List.mem_cons_of_mem _ h)) c' hc' ht
  | _, [], _ :: _, h, _, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _, _ => h.elim

/-- **A valid node's body holds at its own valuation**, its calls as trees within its words. -/
theorem holds_of_valid (hfs : ∀ f, 1 ≤ fs f) {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    {args rets : List E} {fn : Fn} (hv : (Memory.Tree.node f σ bufs kids).Valid P rd args rets)
    (hf : P.find? f = some fn) :
    fn.params.map σ = args ∧ Stmt.HoldsList (KidRel P rd fs ((Memory.Tree.node f σ bufs kids).total fs)) rd σ
      fn.body False (· = rets) := by
  obtain ⟨fn', hf', hp, es, vs, hw, hr, hes, hk⟩ := hv
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  have hT : ∀ k ∈ kids, k.total fs < (Memory.Tree.node f σ bufs kids).total fs := fun k hk' ↦ by
    have := kid_total_lt (σ := σ) (bufs := bufs) (f := f) hfs hk'
    omega
  refine ⟨hp, holdsList_of_walk fn.body ?_⟩
  rw [hw]
  refine ⟨fun e he => ⟨hes e he, fun g a r hg => ?_⟩, hr⟩
  subst hg
  exact kidsValid_kidRel σ kids (calls es) hk hT _ (mem_calls_of_call he) rfl

/-- A call of trees is a call of `Program.Rel`. -/
theorem KidRel.rel {T : ℕ} {g : String} {args rets : List E} (h : KidRel P rd fs T g args rets) :
    P.Rel rd g args rets := by
  obtain ⟨t, hv, rfl, -⟩ := h
  exact Tree.Valid.rel t hv

variable {H : Inst → ℕ → E × E}

/-- **Each callee's words are below its caller's.** -/
theorem insts_total (hfs : ∀ f, 1 ≤ fs f) (S : List Inst) (T0 : ℕ) :
    KidStep P rd H S (fun J ↦ J.t.total fs ≤ T0) := by
  intro I _ f σ bufs kids hIt _ _ _ _ _ _ i c J _ _ hk _ _ _ _ _ hQ
  have := kid_total_lt (σ := σ) (bufs := bufs) (f := f) hfs (List.mem_of_getElem? hk)
  rw [hIt] at hQ
  omega

end

end

end LeanVM.Guest.Res
