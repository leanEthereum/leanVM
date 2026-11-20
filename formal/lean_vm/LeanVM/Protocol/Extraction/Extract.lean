/-
  LeanVM.Protocol.Extraction.Extract

  The committed leaves (`LeanVM/Protocol/Extraction/Extractor.lean`) do not depend on which keys
  they are given, as long as they cover the answers.
-/

module

public import LeanVM.Protocol.Extraction.Merkle
import LeanVM.Protocol.Extraction.Run
import Statement.LeanVm
import LeanVM.Protocol.WithHash

/-!
# The keys of the extractor's evaluations

* `committedLeaves_keys_congr`: two key lists that cover the answers give the same committed leaves
  (no injectivity needed);
* `keysCover_supportKeys`: `supportKeys` covers a finite support, and any covering list makes the
  support finite (`finite_of_keysCover`);
* `keysCover_hashesOf`: the paths' byte strings cover their evaluations.
-/

namespace LeanVM.Extraction.ExtractProofs

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Extraction LeanVM.Extraction.MerkleProofs

@[expose] public section

/-- **The computed leaves do not depend on the covering keys.** -/
theorem committedLeaves_keys_congr {answers : Bytes → Option Digest} {keys keys' : List Bytes}
    (hc : KeysCover answers keys) (hc' : KeysCover answers keys') (root : Digest)
    (height width : ℕ) :
    committedLeaves answers keys root height width =
      committedLeaves answers keys' root height width := by
  simp only [committedLeaves, subtreeLeaves_congr (preimage_keys_congr hc hc')]

/-- A covering key list makes the answers' support finite. -/
theorem finite_of_keysCover {answers : Bytes → Option Digest} {keys : List Bytes}
    (hc : KeysCover answers keys) : {x | answers x ≠ none}.Finite := by
  refine (List.finite_toSet keys).subset fun x hx ↦ ?_
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hx
  exact hc x d hd

/-- **The keys of a finite support cover it.** -/
theorem keysCover_supportKeys {answers : Bytes → Option Digest}
    (h : {x | answers x ≠ none}.Finite) : KeysCover answers (supportKeys answers) := by
  intro x d hx
  simp only [supportKeys, h, ↓reduceDIte, Finset.mem_toList, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq, hx]
  exact Option.some_ne_none d

/-- The paths' byte strings cover their evaluations. -/
theorem keysCover_hashesOf (P : List (Bytes × Digest)) :
    KeysCover (LeanVM.lookupEvaluation P) (P.map (·.1)) := by
  intro x d h
  simp only [LeanVM.lookupEvaluation, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, -⟩ := h
  have hpx := List.find?_some hp
  simp only [decide_eq_true_eq] at hpx
  exact List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some hp, hpx⟩

end
end LeanVM.Extraction.ExtractProofs
