/-
  LeanVM.Guest.B1.Main.L5Segs

  The children loop's entries against the children's segment of `Hints.honestPushes`: each child's `l5Seg` agreeing with its segment, the loop's agree with `childSeg`.
-/

module

public import LeanVM.Guest.B1.Main.L5Pops
public import LeanVM.Guest.B1.Main.MainPushes

/-!
# The children loop against the honest pushes

* `flatMap_eq_range`: a list's `flatMap` is its entries' by index;
* `l5Segs_honest`: the children's `l5Seg`s, each child's counts, claim lists' entries, deferred claim, DA digest and `verify_sub`'s entries agreeing with its pushes, agree with `childSeg` stream by stream.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **A list's `flatMap` is its entries' by index.** -/
theorem flatMap_eq_range {α β : Type} (F : α → List β) : ∀ L : List α,
    L.flatMap F = (List.range L.length).flatMap fun c => (L[c]?.map F).getD []
  | [] => rfl
  | a :: L => by
    rw [List.flatMap_cons, flatMap_eq_range F L, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    rfl

theorem SameStreams.flatMap {A B : ℕ → List Pop} :
    ∀ l : List ℕ, (∀ c ∈ l, SameStreams (A c) (B c)) → SameStreams (l.flatMap A) (l.flatMap B)
  | [], _ => SameStreams.refl _
  | c :: l, hl => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (hl c List.mem_cons_self).append (SameStreams.flatMap l fun c hc => hl c (List.mem_cons_of_mem _ hc))

/-- **The children's entries against `childSeg`**: each child's counts, claim lists' entries, deferred claim, DA
digest and `verify_sub`'s entries agreeing with its pushes, the loop's agree with the children's segment, stream by
stream. -/
theorem l5Segs_honest {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness} {ex es : ℕ → ℕ}
    {px ps pv : ℕ → List Pop} {defer : ℕ → List E} {da : ℕ → E × E}
    (h : ∀ c (hc : c < w.children.length),
      gen ^ ex c = Hints.count w.children[c].statement.claims.xmss.length ∧
      gen ^ es c = Hints.count w.children[c].statement.claims.sphincs.length ∧
      SameStreams (px c) (Hints.childSlotPushes ((xPlan s w).childSlots.getD c [])) ∧
      SameStreams (ps c) (Hints.childSlotPushes ((sPlan s w).childSlots.getD c [])) ∧
      defer c = w.children[c].statement.deferredClaim.cells ∧
      [(da c).1, (da c).2] = Hints.digestCells w.children[c].statement.claims.daDigest ∧
      SameStreams (pv c) (Hints.childHints bytecode seed w.children[c])) :
    SameStreams ((List.range' 0 w.children.length).flatMap fun c =>
      l5Seg (ex c) (es c) (px c) (ps c) (defer c) (da c) (pv c)) (childSeg bytecode seed s w) := by
  have hx : (xPlan s w).childSlots.length = w.children.length := by
    have := congrArg List.length (plan_children_lengths s.claims.xmss (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss)))
    simp only [List.length_map] at this
    exact this
  have hs : (sPlan s w).childSlots.length = w.children.length := by
    have := congrArg List.length (plan_children_lengths s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs)))
    simp only [List.length_map] at this
    exact this
  have hlen : ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots).length = w.children.length := by
    simp [hx, hs]
  rw [childSeg, flatMap_eq_range _ ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots), hlen,
    ← List.range_eq_range']
  refine SameStreams.flatMap _ fun c hc => ?_
  have hc' : c < w.children.length := List.mem_range.mp hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h c hc'
  have e : ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots)[c]? =
      some ((w.children[c], (xPlan s w).childSlots.getD c []), (sPlan s w).childSlots.getD c []) := by
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hc'), List.getElem_zip, List.getElem_zip,
      List.getD_eq_getElem _ _ (by rw [hx]; exact hc'), List.getD_eq_getElem _ _ (by rw [hs]; exact hc')]
  rw [e, Option.map_some, Option.getD_some]
  simp only [l5Seg, h1, h2, h5, h6, List.cons_append]
  exact SameStreams.cons _ (((h3.append h4).append (SameStreams.refl _)).append h7)

end
end LeanVM.Guest.B1.Main
