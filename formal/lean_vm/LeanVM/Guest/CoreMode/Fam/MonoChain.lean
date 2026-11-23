/-
  LeanVM.Guest.CoreMode.Fam.MonoChain

  A valid node's body holding at its own valuation, its callees as trees within its words; a loop's
  iterations times its frame within its tree's words.
-/

module

public import LeanVM.Guest.CoreMode.Fam.Down
public import LeanVM.Guest.CoreMode.Fam.LoopTree

/-!
# Trees, their words and their bodies

`chainF`: a valid tree of a loop helper at counter `i` makes `m` iterations, `i·g^m` its end, with
`m` frames of its function within the tree's words (`Res.chain` with the frame size).

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

/-- **A loop's run, its frames counted**: a valid tree of a loop helper of its shape at counter `i`
makes `m` iterations, `1 ≤ m`, `m` frames within its words, `i·g^m` its end. -/
theorem chainF (hfs : ∀ f, 1 ≤ fs f) : ∀ (n : ℕ) {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    {args rets : List E} {fn : Fn} {e : Option ℕ}, (Memory.Tree.node f σ bufs kids).total fs ≤ n →
    (Memory.Tree.node f σ bufs kids).Valid P rd args rets → P.find? f = some fn →
    loopShape fn e = some (loopBody fn) →
    ∃ m p0 prest, fn.params = p0 :: prest ∧ 1 ≤ m ∧ m * fs f ≤ (Memory.Tree.node f σ bufs kids).total fs ∧
      σ p0 * ofK (addressOfIndex m) = endVal σ fn e
  | 0, f, σ, bufs, kids, _, _, _, _, htot, _, _, _ => by
    have := le_total (fs := fs) (Memory.Tree.node f σ bufs kids)
    have := hfs f
    simp only [Tree.name] at *
    omega
  | n + 1, f, σ, bufs, kids, args, rets, fn, e, htot, hv, hf, hs => by
    unfold Tree.Valid at hv
    obtain ⟨fn', hf', -, es, vs, hw, -, hh, hk⟩ := hv
    have hfe := Option.some.inj (hf'.symm.trans hf)
    subst fn'
    obtain ⟨p0, prest, c, i', es1, hps, -, hes, hi, hc⟩ := loop_path hs hw hh
    subst hes
    rw [loop_calls] at hk
    have hname : fn.name = f := fn_name_of_find hf
    have htk : fs f + Tree.totalKids fs kids + bufs.sum = (Memory.Tree.node f σ bufs kids).total fs :=
      (total_node f σ bufs kids).symm
    have h1 := hfs f
    by_cases h0 : σ c = 0
    · refine ⟨1, p0, prest, hps, le_rfl, by omega, ?_⟩
      rw [h0] at hc
      exact char2_eq hc.symm
    · obtain ⟨ks', k, rfl, -, hkn, hkv⟩ := kidsValid_snoc hk
      simp only [ne_eq, h0, not_false_eq_true, decide_true, ↓reduceIte] at hkv hkn
      rcases k with ⟨f', σ', bufs', kids'⟩ | ⟨f', σ'⟩
      · simp only [Tree.name, hname] at hkn
        subst f'
        have hkt := totalKids_snoc (fs := fs) ks' (Memory.Tree.node f σ' bufs' kids')
        have hkv' := hkv
        unfold Tree.Valid at hkv'
        obtain ⟨fn'', hf'', hpm, -⟩ := hkv'
        have hfe' := Option.some.inj (hf''.symm.trans hf)
        subst fn''
        obtain ⟨m, p0', prest', hps', hm1, hm2, hm⟩ := chainF hfs n (by omega) hkv hf hs
        rw [hps] at hps'
        obtain ⟨rfl, rfl⟩ := List.cons.inj hps'
        rw [hps] at hpm
        simp only [List.map_cons, List.cons.injEq] at hpm
        obtain ⟨h0', hrest⟩ := hpm
        have hend : endVal σ' fn e = endVal σ fn e := by
          cases e with
          | some _ => rfl
          | none =>
            simp only [endVal, hps]
            cases prest with
            | nil => rfl
            | cons p1 _ => simp only [List.map_cons, List.cons.injEq] at hrest; exact hrest.1
        refine ⟨m + 1, p0, prest, hps, by omega, by rw [Nat.succ_mul]; omega, ?_⟩
        rw [← hend, ← hm, h0', hi, mul_assoc, ofK_gpow_add, Nat.add_comm 1 m]
      · exact hkv.elim

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
