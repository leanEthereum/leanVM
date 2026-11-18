/-
  LeanVM.Guest.CoreMode.HeapCTree

  The heap check over an honest call tree: every instance's path is sound, and each callee's
  subtree writes its guarantees.
-/

module

public import LeanVM.Guest.CoreMode.HeapCSound

/-!
# The heap check over a call tree

`heapOkC_sound` is about one instance, a call event writing its callee's guarantees by its signature.
On a valid tree (`Tree.Valid`) whose every function passes `heapOkC` against the certificates'
signatures (`CertsOk`), with every instance's entry facts and residuals (`treeAll (FactsAt …)`), the
signatures are kept: `tree_post`, each instance's guarantees at its words are its preconditions or
written by an atom of its subtree (`treeWr`); `tree_inst`, each instance's path is sound
(`ReadsOkC`, `PostOkC`). By induction over the tree: an entered call's
guarantees are its callee's subtree's writes or its callee's preconditions, which the caller's path
wrote before the call (`written_tree`, by induction on the events before).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (PowTree)

public section

/-! ## Trees -/

mutual
/-- **The addresses a subtree writes**: an atom of an instance's path, or a callee's subtree's. -/
@[expose] def treeWr (P : Program) : Tree → K → Prop
  | .node f σ _ kids, x => (∃ fn es vs, P.find? f = some fn ∧ walk σ fn.body = .ret es vs ∧
      ∃ a, Ev.atom a ∈ es ∧ Writes σ a x) ∨ kidsWr P kids x
  | .phantom .., _ => False

/-- The addresses the callees' subtrees write. -/
@[expose] def kidsWr (P : Program) : List Tree → K → Prop
  | [], _ => False
  | k :: ks, x => treeWr P k x ∨ kidsWr P ks x
end

mutual
/-- `Q` at every instance of a tree. -/
@[expose] def treeAll (Q : String → Val → Prop) : Tree → Prop
  | .node f σ _ kids => Q f σ ∧ kidsAll Q kids
  | .phantom .. => True

/-- `Q` at every instance of the callees' trees. -/
@[expose] def kidsAll (Q : String → Val → Prop) : List Tree → Prop
  | [] => True
  | k :: ks => treeAll Q k ∧ kidsAll Q ks
end

/-- **An instance's facts**: its entry facts and residuals, under its function's certificate. -/
def FactsAt (P : Program) (cert : String → HCert) (f : String) (σ : Val) : Prop :=
  ∀ fn, P.find? f = some fn → EntryF (cert f) (fn.params.map σ) ∧ ResF (cert f) σ

/-- **Every function's certificate passes**, against the certificates' signatures. -/
def CertsOk (pows : PowTree) (P : Program) (cert : String → HCert) : Prop :=
  ∀ f fn, P.find? f = some fn → heapOkC pows (fun g ↦ (cert g).sig) fn (cert f) = true

/-- **What a subtree keeps of its signature**: each guarantee at its words is its precondition or
written by its subtree, and its returned words are its `retM` monomials. -/
def PostT (P : Program) (cert : String → HCert) (t : Tree) (args rets : List E) : Prop :=
  (∀ x, SigSet (cert t.name).sig.post (cert t.name).sig.postR (args ++ rets) x →
    SigSet (cert t.name).sig.pre (cert t.name).sig.preR args x ∨ treeWr P t x) ∧
  RetMOk (cert t.name).sig args rets

theorem kidsWr_of_mem {P : Program} {x : K} : ∀ {ks : List Tree} {k : Tree}, k ∈ ks → treeWr P k x → kidsWr P ks x
  | [], _, hk, _ => by simp at hk
  | k' :: ks, k, hk, h => by
    rcases List.mem_cons.mp hk with rfl | hk
    · exact Or.inl h
    · exact Or.inr (kidsWr_of_mem hk h)

/-! ## Written before, over the tree -/

section Written

variable {sigOf : String → HSig} {H : HCert} {σ : Val} {ws0 : List E} {es : List Ev}

/-- **What a path writes, over the tree**: an address written after some of its events is a
precondition's or written by `T`, given that `T` holds each atom's writes and each entered call's
guarantees but its callee's preconditions, the path's needs being written before each event. -/
theorem written_tree (hreads : ReadsOkC sigOf H σ ws0 es) {T : K → Prop}
    (hatom : ∀ a x, Ev.atom a ∈ es → Writes σ a x → T x)
    (hkid : ∀ g a r, Ev.call g a r ∈ es → ∀ x, SigSet (sigOf g).post (sigOf g).postR ((a ++ r).map σ) x →
      SigSet (sigOf g).pre (sigOf g).preR (a.map σ) x ∨ T x) :
    ∀ (n : ℕ) (es1 es2 : List Ev), es1.length ≤ n → es = es1 ++ es2 → ∀ x,
      WrittenC sigOf H σ ws0 es1 x → SigSet H.sig.pre H.sig.preR ws0 x ∨ T x := by
  intro n
  induction n with
  | zero =>
    intro es1 es2 hl _ x hx
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)] at hx
    rcases hx with hx | ⟨e, he, -⟩
    · exact Or.inl hx
    · simp at he
  | succ n ih =>
    intro es1 es2 hl hes x hx
    rcases hx with hx | ⟨e, he, hx⟩
    · exact Or.inl hx
    obtain ⟨A, B, rfl⟩ := List.append_of_mem he
    have hmem : e ∈ es := by rw [hes]; simp
    cases e with
    | atom a => exact Or.inr (hatom a x hmem hx)
    | call g a r =>
      rcases hkid g a r hmem x hx with hx | hx
      · have hreq := hreads A (.call g a r) (B ++ es2) (by rw [hes]; simp)
        have hA : WrittenC sigOf H σ ws0 A x := by
          rcases hx with ⟨c, hc, rfl⟩ | ⟨r', hr', hx⟩
          · exact hreq.1 c hc
          · exact hreq.2 r' hr' x hx
        exact ih A (Ev.call g a r :: B ++ es2) (by simp at hl; omega) (by rw [hes]; simp) x hA
      · exact Or.inr hx
    | inK _ => exact hx.elim
    | skip _ _ => exact hx.elim

end Written

/-! ## The tree -/

section Tree

variable {pows : PowTree} {P : Program} {cert : String → HCert} {rd : Reader}

/-- An entered call's callee, of the tree's callees. -/
theorem kid_of_call {σ : Val} : ∀ {ks : List Tree} {cs : List Call}, Tree.KidsValid P rd σ cs ks →
    ∀ c ∈ cs, c.taken = true → ∃ k ∈ ks, k.name = c.f ∧ k.Valid P rd (c.args.map σ) (c.rets.map σ)
  | [], [], _, c, hc, _ => by simp at hc
  | k :: ks, c :: cs, ⟨hn, hk, hks⟩, c', hc', ht => by
    rcases List.mem_cons.mp hc' with rfl | hc'
    · rw [ite_eq_left ht] at hk
      exact ⟨k, List.mem_cons_self, hn, hk⟩
    · obtain ⟨k', hk', h1, h2⟩ := kid_of_call hks c' hc' ht
      exact ⟨k', List.mem_cons_of_mem _ hk', h1, h2⟩
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

theorem kidsAll_mem {Q : String → Val → Prop} : ∀ {ks : List Tree} {k : Tree}, kidsAll Q ks → k ∈ ks → treeAll Q k
  | [], _, _, hk => by simp at hk
  | k' :: ks, k, h, hk => by
    rcases List.mem_cons.mp hk with rfl | hk
    · exact h.1
    · exact kidsAll_mem h.2 hk

/-- Each entered call's returned words are its callee's `retM` monomials, the callees keeping their
signatures. -/
theorem evM_of_kids {σ : Val} {es : List Ev} {kids : List Tree}
    (hkids : ∀ c ∈ calls es, c.taken = true → ∃ k ∈ kids, k.name = c.f ∧ k.Valid P rd (c.args.map σ) (c.rets.map σ) ∧
      PostT P cert k (c.args.map σ) (c.rets.map σ)) :
    ∀ e ∈ es, EvM (fun g ↦ (cert g).sig) σ e
  | .call g a r, he => by
    obtain ⟨k, -, hn, -, hkp⟩ := hkids _ (mem_calls_of_call he) rfl
    have := hkp.2
    simp only [hn] at this
    exact this
  | .atom _, _ => trivial
  | .inK _, _ => trivial
  | .skip _ _, _ => trivial

mutual
/-- **Each subtree keeps its signature**: each guarantee at its words is its precondition or written by
an atom of its subtree; its returned words are its `retM` monomials. -/
theorem tree_post (hp : pows.Ok) (hC : CertsOk pows P cert) : ∀ (t : Tree) {args rets : List E},
    t.Valid P rd args rets → treeAll (FactsAt P cert) t → PostT P cert t args rets
  | .node f σ bufs kids, args, rets, hv, ht => by
    obtain ⟨fn, hf, hpar, es, vs, hw, hret, hh, hk⟩ := hv
    have hkids := kids_post hp hC kids σ (calls es) hk ht.2
    have hname : fn.name = f := fn_name_of_find hf
    obtain ⟨hE, hR⟩ := ht.1 fn hf
    obtain ⟨hreads, hpost, hrm⟩ := heapOkC_sound hp (hC f fn hf) (by rw [hname]) hw hh (evM_of_kids hkids) hE hR
    rw [← hpar, ← hret] at *
    refine ⟨fun x hx ↦ ?_, hrm⟩
    have hW : WrittenC (fun g ↦ (cert g).sig) (cert f) σ (fn.params.map σ) es x := by
      rcases hx with ⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩
      · exact hpost.1 c hc
      · exact hpost.2 r hr x hx
    refine written_tree hreads (T := treeWr P (.node f σ bufs kids))
      (fun a x ha hx ↦ Or.inl ⟨fn, es, vs, hf, hw, a, ha, hx⟩) (fun g a r hg x hx ↦ ?_) es.length es [] le_rfl
      (by simp) x hW
    obtain ⟨k, hk', hn, -, hkp⟩ := hkids _ (mem_calls_of_call hg) rfl
    have := hkp.1 x (by simp only [hn]; rw [← List.map_append]; exact hx)
    simp only [hn] at this
    exact this.imp_right fun h ↦ Or.inr (kidsWr_of_mem hk' h)
  | .phantom .., _, _, hv, _ => hv.elim

/-- **The callees keep their signatures**: each entered call's callee. -/
theorem kids_post (hp : pows.Ok) (hC : CertsOk pows P cert) : ∀ (ks : List Tree) (σ : Val) (cs : List Call),
    Tree.KidsValid P rd σ cs ks → kidsAll (FactsAt P cert) ks → ∀ c ∈ cs, c.taken = true →
      ∃ k ∈ ks, k.name = c.f ∧ k.Valid P rd (c.args.map σ) (c.rets.map σ) ∧
        PostT P cert k (c.args.map σ) (c.rets.map σ)
  | [], _, [], _, _, c, hc, _ => by simp at hc
  | k :: ks, σ, c :: cs, ⟨hn, hk, hks⟩, ⟨ha, has⟩, c', hc', ht => by
    rcases List.mem_cons.mp hc' with rfl | hc'
    · rw [ite_eq_left ht] at hk
      exact ⟨k, List.mem_cons_self, hn, hk, tree_post hp hC k hk ha⟩
    · obtain ⟨k', hk', h1, h2, h3⟩ := kids_post hp hC ks σ cs hks has c' hc' ht
      exact ⟨k', List.mem_cons_of_mem _ hk', h1, h2, h3⟩
  | [], _, _ :: _, h, _, _, _, _ => h.elim
  | _ :: _, _, [], h, _, _, _, _ => h.elim
end

/-- **Every instance's path is sound**: on a valid tree whose functions pass `heapOkC` against the
certificates' signatures, every instance having its facts, the root's path reads only what is
written before and writes its guarantees (`heapOkC_sound`; the callees' facts give their returned
words' monomials, `tree_post`). -/
theorem tree_inst (hp : pows.Ok) (hC : CertsOk pows P cert) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} {args rets : List E} (hv : (Memory.Tree.node f σ bufs kids).Valid P rd args rets)
    (ht : treeAll (FactsAt P cert) (.node f σ bufs kids)) :
    ∃ fn es vs, P.find? f = some fn ∧ walk σ fn.body = .ret es vs ∧
      ReadsOkC (fun g ↦ (cert g).sig) (cert f) σ (fn.params.map σ) es ∧
      PostOkC (fun g ↦ (cert g).sig) (cert f) σ (fn.params.map σ) es vs := by
  obtain ⟨fn, hf, -, es, vs, hw, -, hh, hk⟩ := hv
  obtain ⟨hE, hR⟩ := ht.1 fn hf
  obtain ⟨h1, h2, -⟩ := heapOkC_sound hp (hC f fn hf) (by rw [fn_name_of_find hf]) hw hh
    (evM_of_kids (kids_post hp hC kids σ (calls es) hk ht.2)) hE hR
  exact ⟨fn, es, vs, hf, hw, h1, h2⟩

end Tree

end

end LeanVM.Guest.CoreMode
