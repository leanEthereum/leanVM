/-
  LeanVM.Guest.Bridge.RetempPops

  Re-choosing a tree's temporaries keeps its pops, so the honest memory's tree pops what the tree B1's completeness builds pops.
-/

module

public import LeanVM.Guest.Bridge.Track
public import LeanVM.Guest.Memory.Retemp

/-!
# The pops of a re-chosen tree

`Memory.Tree.retemp` re-chooses each instance's temporaries (`Memory/Retemp.lean`); no hint names a temporary (a temporary is a range check's or a touch's own), so a path's entries are the same under either valuation (`splice_congr`), and the re-chosen tree pops what the tree pops (`pops_retemp`): `SameStreams` of the tree B1's completeness gives (`MainCompleteP`) holds of the honest memory's tree, on the same reader.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

public section

/-- **A path's entries depend only on the values its events name.** -/
theorem splice_congr {rd : Reader} {σ σ' : Val} :
    ∀ {es : List Ev} (ks : List (List Pop)), EvAgree σ σ' es → splice rd σ' es ks = splice rd σ es ks
  | [], _, _ => rfl
  | .atom a :: es, ks, h => by
    have ih := splice_congr (rd := rd) (es := es) ks fun e he ↦ h e (List.mem_cons_of_mem _ he)
    have hu : ∀ v ∈ atomUses a, σ' v = σ v := fun v hv ↦ h _ List.mem_cons_self v hv
    rw [splice, splice, ih]
    congr 1
    cases a with
    | hint hh =>
      cases hh with
      | witness s d =>
        cases d with
        | stack vs =>
          simp only [Atom.pops, Core.Hint.pops, Dest.words, List.cons.injEq, Prod.mk.injEq, true_and,
            and_true]
          exact List.map_congr_left fun v hv ↦ hu v hv
        | heap p off len =>
          simp only [Atom.pops, Core.Hint.pops, Dest.words]
          rw [hu p (by simp [atomUses, hintUses, destUses])]
      | _ => rfl
    | _ => rfl
  | .inK _ :: es, ks, h => by
    rw [splice, splice, splice_congr (rd := rd) ks fun e he ↦ h e (List.mem_cons_of_mem _ he)]
  | .call .. :: es, ks, h => by
    rw [splice, splice, splice_congr (rd := rd) ks.tail fun e he ↦ h e (List.mem_cons_of_mem _ he)]
  | .skip .. :: es, ks, h => by
    rw [splice, splice, splice_congr (rd := rd) ks.tail fun e he ↦ h e (List.mem_cons_of_mem _ he)]

variable {P : Core.Program} {fs : String → ℕ} {ν : ℕ → String → Val → V → E} {rd : Reader}

mutual
/-- **A re-chosen tree pops what the tree pops.** -/
theorem pops_retemp (hF : P.Fresh) : ∀ (t : Tree) (pos : ℕ × ℕ), (t.retemp P fs ν pos).pops P rd = t.pops P rd
  | .node f σ bufs kids, pos => by
    rw [retemp_node, Tree.pops, Tree.pops, events_retemp hF (bufs' := bufs) (ks' := kids),
      popsKids_retempKids hF]
    apply splice_congr
    intro e he v hv
    unfold Tree.events at he
    simp only [Tree.name, Tree.val] at he
    cases hf : P.find? f with
    | none => simp [hf] at he
    | some fn =>
      simp only [hf] at he
      cases hw : walk σ fn.body with
      | ret es vs => simp only [hw] at he; exact evAgree_retemp hF hf hw e he v hv
      | fall _ => simp [hw] at he
      | stuck => simp [hw] at he
  | .phantom f σ, pos => by rw [retemp_phantom]

/-- `pops_retemp` for the callees. -/
theorem popsKids_retempKids (hF : P.Fresh) : ∀ (ps : List (ℕ × ℕ)) (ks : List Tree),
    Tree.popsKids P rd (Tree.retempKids P fs ν ps ks) = Tree.popsKids P rd ks
  | _, [] => by rw [retempKids_nil]
  | [], k :: ks => by rw [Tree.retempKids]
  | p :: ps, k :: ks => by
    rw [retempKids_cons, Tree.popsKids, Tree.popsKids, pops_retemp hF k p, popsKids_retempKids hF ps ks]
end

end

end LeanVM.Guest.Bridge
