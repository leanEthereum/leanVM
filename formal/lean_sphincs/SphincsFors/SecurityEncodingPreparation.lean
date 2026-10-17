import SphincsFors.SecurityReferenceChoice
import SphincsFors.SecurityGraphCache

/-! The canonical encoding reference search queries only rejected trials and its one exempt
successful trial. So no queried input of the search hits its structural target, including under
complete counter exhaustion. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.ReferenceChoice
open Concrete Completeness Prefix TargetAssignment

attribute [local instance] Classical.propDecidable
attribute [local irreducible] firstEncoding encodingAttemptLimit encode

def search (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) : Nat → Nat → OracleComp HashSpec (Option (Counter × Encoding))
  | 0, _ => pure none
  | attempts + 1, start => do
      let found ← encode parameter lay tree leaf message (BitVec.ofNat counterBits start)
      match found with
      | none => search parameter lay tree leaf message attempts (start + 1)
      | some encoding => pure (some (BitVec.ofNat counterBits start, encoding))

theorem eval_search (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (attempts start : Nat) :
    evalWithAnswerFn f (search parameter lay tree leaf message attempts start) =
      firstEncoding f parameter lay tree leaf message attempts start := by
  induction attempts generalizing start with
  | zero => simp only [search, firstEncoding, evalWithAnswerFn_pure]
  | succ attempts ih =>
      cases he : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) <;>
        simp only [search, evalWithAnswerFn_bind, firstEncoding, he, evalWithAnswerFn_pure, ih]

theorem queriedInputs_encode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    queriedInputs f (encode parameter lay tree leaf message counter : OracleComp HashSpec _) =
      [Wots.encodingInput parameter lay tree leaf message counter] := by
  simp only [encode, queriedInputs_bind, queriedInputs_tweakableHash, queriedInputs_pure,
    List.append_nil, Wots.encodingInput]

theorem search_query_classification (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (attempts start : Nat)
    (input : HashInput) (hinput : input ∈ queriedInputs f
      (search parameter lay tree leaf message attempts start)) :
    ∃ counter, input = Wots.encodingInput parameter lay tree leaf message counter ∧
      (evalWithAnswerFn f (encode parameter lay tree leaf message counter :
        OracleComp HashSpec (Option Encoding)) = none ∨
       (firstEncoding f parameter lay tree leaf message attempts start).map
         (fun pair => Wots.encodingInput parameter lay tree leaf message pair.1) = some input) := by
  induction attempts generalizing start with
  | zero => simp only [search, queriedInputs_pure, List.not_mem_nil] at hinput
  | succ attempts ih =>
      rw [search, queriedInputs_bind, queriedInputs_encode, List.mem_append,
        List.mem_singleton] at hinput
      cases he : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [he] at hinput
          rcases hinput with rfl | hinput
          · exact ⟨_, rfl, Or.inl he⟩
          · obtain ⟨counter, hcounter, hcase⟩ := ih (start + 1) hinput
            exact ⟨counter, hcounter, by simpa only [firstEncoding, he] using hcase⟩
      | some encoding =>
          simp only [he, queriedInputs_pure, List.not_mem_nil, or_false] at hinput
          subst input
          refine ⟨_, rfl, Or.inr ?_⟩
          simp only [firstEncoding, he, Option.map_some]

/-- The prepared search cannot itself contain an exceptional encoding query. -/
theorem search_targets_empty_or_miss (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest)
    (table : Table)
    (hentry : table (hashDomainFields (.encoding lay tree leaf)) =
      some ⟨exemptInput f parameter lay tree leaf message, target f parameter lay tree leaf message⟩)
    (input : HashInput)
    (hinput : input ∈ queriedInputs f
      (search parameter lay tree leaf message encodingAttemptLimit 0)) :
    truncateHash (f input) ∉ targets parameter table input := by
  obtain ⟨counter, rfl, hcase⟩ := search_query_classification f parameter lay tree leaf message
    encodingAttemptLimit 0 input hinput
  rw [Wots.encodingInput, targets_at_entry _ _ _ _ _ hentry]
  rcases hcase with hrejected | hexempt
  · split_ifs with hexempt
    · exact Finset.notMem_empty _
    · simp only [Finset.mem_singleton]
      intro hmatch
      have hd := target_decodes f parameter lay tree leaf message
      have hencode := hrejected
      simp only [encode, evalWithAnswerFn_bind, eval_tweakableHash, evalWithAnswerFn_pure] at hencode
      rw [hmatch] at hencode
      rw [hd] at hencode
      cases hencode
  · have hexempt' : exemptInput f parameter lay tree leaf message =
        some (tweakableHashInput parameter (.encoding lay tree leaf)
          (bytesLE 16 message ++ bytesLE 4 counter)) := hexempt
    rw [if_pos hexempt']
    exact Finset.notMem_empty _

end SphincsFors.Security.ReferenceChoice
