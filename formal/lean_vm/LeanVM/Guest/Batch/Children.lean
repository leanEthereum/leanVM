/-
  LeanVM.Guest.Batch.Children

  A node's children, under the deployed seed with the node's deferred claim true: every child's
  proof is accepted by the deployed verifier and its deferred claim holds, unless a batching
  challenge is bad.
-/

module

public import LeanVM.Guest.Batch.Sound
public import LeanVM.Protocol.Verifier.DeferredShape
public import LeanVM.Guest.Batch.Node
public import LeanVM.Guest.AcceptableChild

/-!
# A node's children

`NodeRelation` says the deferring verifier accepts each child's proof, its claim on the bytecode
handed on to the node's batching. Under the deployed seed and with the node's deferred claim true
(what the outer verifier checks of the root), `batch_sound` makes the children's claims true, or
a batching challenge is bad; and a proof the deferring verifier accepts under the deployed IV with
true claims is one the deployed verifier accepts (`verify_of_verifyDeferred`); and the claim it
accepts has the bytecode's shape (`verifyDeferred_shaped`). So
`children_sound`: every child's proof verifies and its own deferred claim holds, or a challenge of
the node's batching is bad (`BatchBad`).

A child whose proof verifies and whose deferred claim holds passes the outer verifier's checks but
the DA digests'. That its statement then holds is the child proof's soundness under Keccak as the
guest computes it, the in-guest hash heuristic, as is that no batching challenge is bad; the
latter is bounded with Keccak-256 and Keccak-f[1600] built from one random permutation by
`batch_rpm` (`Batch/Rpm.lean`), from the random-oracle bound `batch_rom`.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-- What a node batches of its children under `seed`: each child's public input, its proof's
claims and its statement's deferred claim. -/
def childClaimsOf (seed : Digest) (w : NodeWitness) : List ChildClaims :=
  w.children.map fun c ↦ ⟨statementDigest seed c.statement, c.freshClaim, c.statement.deferredClaim⟩

/-- **A node's children verify**, under the deployed seed with the node's deferred claim true:
every child's proof is accepted by the deployed verifier and its deferred claim holds, or a
challenge of the node's batching is bad. -/
theorem children_sound {bytecode : List K} {s : NodeStatement} {w : NodeWitness}
    (hN : NodeRelation bytecode (fiatShamirIv bytecode) s w) (hs : s.deferredClaim.HoldsWithShape bytecode) :
    (∀ c ∈ w.children,
        Verifier.verify bytecode (statementDigest (fiatShamirIv bytecode) c.statement) c.proof =
          true ∧
          c.statement.deferredClaim.HoldsWithShape bytecode) ∨
      BatchBad bytecode (childClaimsOf (fiatShamirIv bytecode) w) w.batchingHints := by
  obtain ⟨-, hch, -, -, hbat⟩ := nodeRel_iff.mp hN
  by_cases hw : w.children = []
  · exact Or.inl fun c hc ↦ absurd hc (by simp [hw])
  simp only [hw, ↓reduceIte] at hbat
  rcases batch_sound hbat hs
      (fun c hc ↦ by
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
        exact verifyDeferred_shaped (hch c' hc').2)
      (fun c hc ↦ by
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
        exact (hch c' hc').1) with hok | hbad
  · refine Or.inl fun c hc ↦ ?_
    obtain ⟨hfr, hcar⟩ := hok _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    exact ⟨verify_of_verifyDeferred hfr (hch c hc).2, hcar⟩
  · exact Or.inr hbad

end
end LeanVM.Guest.Batch
