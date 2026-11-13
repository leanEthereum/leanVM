/-
  LeanVM.Guest.B1.Main.L5Segs

  The children loop's entries against the children's segment of `Hints.honestPushes`: each child's `l5Seg` agreeing with its segment, but the advised sizes, the loop's agree with `childSeg`.
-/

module

public import LeanVM.Guest.B1.Main.L5Pops
public import LeanVM.Guest.B1.Main.MainPushes

/-!
# The children loop against the honest pushes

* `childHints_take_heap`: a child's first four pushes are advised sizes;
* `flatMap_eq_range`: a list's `flatMap` is its entries' by index;
* `l5Segs_honest`: the children's `l5Seg`s, each child's counts, claim lists' entries, deferred claim, DA digest and `verify_sub`'s entries agreeing with its pushes, agree with `childSeg` on every stream but `heap_sizes`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **A child's first four pushes are advised sizes.** -/
theorem childHints_take_heap (bytecode : List K) (seed : Digest) (c : Child) :
    ∀ p ∈ (Hints.childHints bytecode seed c).take 4, p.1 = Hints.heapSizeStream := by
  intro p hp
  unfold Hints.childHints at hp
  split at hp
  · simp at hp
  · rw [List.append_assoc, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)] at hp
    obtain ⟨n, -, rfl⟩ := List.mem_map.mp hp
    rfl

/-- `verify_sub`'s entries agreeing with a child's pushes past its advised sizes agree with them but the sizes. -/
theorem sameStreamsBut_childHints {bytecode : List K} {seed : Digest} {c : Child} {pv : List Pop}
    (h : SameStreams pv ((Hints.childHints bytecode seed c).drop 4)) :
    SameStreamsBut Hints.heapSizeStream pv (Hints.childHints bytecode seed c) := by
  refine (sameStreamsBut_of h).trans ?_
  have := (sameStreamsBut_drop (a := (Hints.childHints bytecode seed c).drop 4)
    (childHints_take_heap bytecode seed c)).symm
  rwa [List.take_append_drop] at this

/-- **A list's `flatMap` is its entries' by index.** -/
theorem flatMap_eq_range {α β : Type} (F : α → List β) : ∀ L : List α,
    L.flatMap F = (List.range L.length).flatMap fun c => (L[c]?.map F).getD []
  | [] => rfl
  | a :: L => by
    rw [List.flatMap_cons, flatMap_eq_range F L, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    rfl

theorem SameStreamsBut.flatMap {h : String} {A B : ℕ → List Pop} :
    ∀ l : List ℕ, (∀ c ∈ l, SameStreamsBut h (A c) (B c)) → SameStreamsBut h (l.flatMap A) (l.flatMap B)
  | [], _ => SameStreamsBut.refl _
  | c :: l, hl => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (hl c List.mem_cons_self).append (SameStreamsBut.flatMap l fun c hc => hl c (List.mem_cons_of_mem _ hc))

/-- **The children's entries against `childSeg`**: each child's counts, claim lists' entries, deferred claim, DA
digest and `verify_sub`'s entries agreeing with its pushes, the loop's agree with the children's segment on every
stream but `heap_sizes`. -/
theorem l5Segs_honest {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness} {ex es : ℕ → ℕ}
    {px ps pv : ℕ → List Pop} {defer : ℕ → List E} {da : ℕ → E × E}
    (h : ∀ c (hc : c < w.children.length),
      gen ^ ex c = Hints.count w.children[c].statement.claims.xmss.length ∧
      gen ^ es c = Hints.count w.children[c].statement.claims.sphincs.length ∧
      SameStreams (px c) (Hints.childSlotPushes ((xPlan s w).childSlots.getD c [])) ∧
      SameStreams (ps c) (Hints.childSlotPushes ((sPlan s w).childSlots.getD c [])) ∧
      defer c = w.children[c].statement.deferredClaim.cells ∧
      [(da c).1, (da c).2] = Hints.digestCells w.children[c].statement.claims.daDigest ∧
      SameStreams (pv c) ((Hints.childHints bytecode seed w.children[c]).drop 4)) :
    SameStreamsBut Hints.heapSizeStream ((List.range' 0 w.children.length).flatMap fun c =>
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
  refine SameStreamsBut.flatMap _ fun c hc => ?_
  have hc' : c < w.children.length := List.mem_range.mp hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h c hc'
  have e : ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots)[c]? =
      some ((w.children[c], (xPlan s w).childSlots.getD c []), (sPlan s w).childSlots.getD c []) := by
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hc'), List.getElem_zip, List.getElem_zip,
      List.getD_eq_getElem _ _ (by rw [hx]; exact hc'), List.getD_eq_getElem _ _ (by rw [hs]; exact hc')]
  rw [e, Option.map_some, Option.getD_some]
  simp only [l5Seg, h1, h2, h5, h6, List.cons_append]
  refine SameStreamsBut.cons _ (((sameStreamsBut_of (h3.append h4)).append (SameStreamsBut.refl _)).append
    (sameStreamsBut_childHints h7))

end
end LeanVM.Guest.B1.Main
