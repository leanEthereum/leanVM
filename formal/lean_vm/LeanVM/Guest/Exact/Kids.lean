/-
  LeanVM.Guest.Exact.Kids

  `Tree.Every` from a node's callees' predicates (`everyKids_of_kidsT`, `NodeHonest.every`), a node exact by its body
  (`exactAt_of_body`).
-/

module

public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.Budget.Kids

/-!
# Every node, from the callees' predicates

`everyKids_of_kidsT`: the callees of a valid node, each entered one's tree satisfying its predicate of `KidsT`, satisfy
`Every Q` when each predicate gives it on a valid tree of its callee (a callee exact for free gives it whatever its
predicate). `NodeHonest.every`: a valid node of honest shape satisfies `Every Q`, given its own `Q f σ`.
`exactAt_of_body`: a node whose function's computed hints are all pinned by the next atom is exact, on every reader.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {P : Core.Program} {rd : Reader} {Q : String → Val → Prop}

/-- **The callees of a valid node satisfy `Every Q`** when each entered one's predicate gives it. -/
theorem everyKids_of_kidsT {σ : Val} : ∀ {cs : List Call} {Ts : List (Tree → Prop)} {ks : List Tree},
    Tree.KidsValid P rd σ cs ks → cs.length ≤ Ts.length → KidsT cs Ts ks →
    (∀ c T, (c, T) ∈ cs.zip Ts → c.taken = true → ∀ t : Tree, t.name = c.f →
      t.Valid P rd (c.args.map σ) (c.rets.map σ) → T t → t.Every Q) → Tree.EveryKids Q ks
  | [], _, [], _, _, _, _ => by rw [Tree.EveryKids]; trivial
  | c :: cs, T :: Ts, k :: ks, ⟨hn, hc, hv⟩, hl, ⟨hT, hTs⟩, hE => by
      rw [Tree.EveryKids]
      refine ⟨?_, everyKids_of_kidsT hv (by simpa using hl) hTs fun c' T' h =>
        hE c' T' (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ h)⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact hE c T (by rw [List.zip_cons_cons]; exact List.mem_cons_self) ht k hn hc (hT ht)
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact Tree.every_phantom
  | _ :: _, [], _, _, hl, _, _ => absurd hl (by simp)
  | [], _, _ :: _, h, _, _, _ | _ :: _, _, [], h, _, _, _ => h.elim

/-- **A valid node of honest shape satisfies `Every Q`**: its own `Q f σ`, each entered callee's predicate giving
`Every Q` on its valid trees. -/
theorem _root_.LeanVM.Guest.Budget.NodeHonest.every {f : String} {Qh : Val → Prop} {cs : Val → List Call}
    {bs : Val → List ℕ} {Ts : List (Tree → Prop)} {t : Tree} {args rets : List E}
    (h : Budget.NodeHonest P f Qh cs bs Ts t) (hv : t.Valid P rd args rets)
    (hq : ∀ σ bufs ks, (Tree.node f σ bufs ks).Valid P rd args rets → Q f σ)
    (hE : ∀ σ, Qh σ → ∀ c T, (c, T) ∈ (cs σ).zip Ts → c.taken = true → ∀ t : Tree, t.name = c.f →
      t.Valid P rd (c.args.map σ) (c.rets.map σ) → T t → t.Every Q) : t.Every Q := by
  obtain ⟨σ, ks, rfl, hQ, hc, hl, hT⟩ := h
  have hv' := hv
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hv'
  rw [hc fn es vs hf hw] at hkv
  exact Tree.every_node.mpr ⟨hq σ _ ks hv, everyKids_of_kidsT hkv hl hT (hE σ hQ)⟩

/-- **A node whose function's computed hints are pinned by the next atom is exact**, on every reader. -/
theorem exactAt_of_body {f : String} {fn : Fn} (hf : P.find? f = some fn)
    (hpin : Stmt.blockNextOk isComputed pinsInverse fn.body = true) {σ : Val} {bufs : List ℕ} {ks : List Tree}
    {args rets : List E} (hv : (Tree.node f σ bufs ks).Valid P rd args rets) (rd' : Reader) :
    ExactAt P rd' f σ := by
  obtain ⟨fn', hf', -, es, vs, hw, -, hes, -⟩ := hv
  rw [hf] at hf'; cases hf'
  exact exactAt_of_walk hf hw (exact_of_pinned hpin hw hes rd')

end
end LeanVM.Guest.Memory
