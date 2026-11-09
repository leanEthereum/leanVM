module

public import LeanVM.Cost.Bounds.Sizes.Lane
public import LeanVM.Protocol.Extraction.Sound

/-!
# Sizes along the decoder: the pruning's survivors, by the Johnson bound

At every admissible shape (`Whir.Admissible μ R`), after any `U ≥ 1` lanes at most `2^12` prefixes
survive the pruning the extractor runs (`pruneUpToDistinct_length_le_johnson`), and the decoder
returns at most `2^12` stacks (`decodeStacksDistinct_length_le_johnson`): the statement's chain's
bounds (`pruneUpTo_length_le`, `decodeStacks_length_le`, `Extraction/Sound.lean`, through the
interleaved Johnson bound `card_iList_johnsonAgreement_le_floor`), transported along
`pruneUpToDistinct_eq`/`pruneUpToFast_eq` and `decodeStacksDistinct_eq`/`decodeStacksFast_eq`.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Extraction.Fast LeanVM.Extraction LeanVM.Parameters

public section

/-- **At most `2^12` survivors after any `U ≥ 1` lanes**, at every admissible shape. -/
theorem pruneUpToDistinct_length_le_johnson {μ R : ℕ} (h : Whir.Admissible μ R) (W : ℕ → List K)
    {U : ℕ} (hU : 0 < U) :
    (pruneUpToDistinct (μ - Whir.initialFold) R (johnsonThreshold μ R) W U).length ≤ 2 ^ 12 := by
  rw [pruneUpToDistinct_eq (checkRedundant_johnson h), pruneUpToFast_eq]
  exact LeanVM.Protocol.EndToEnd.Sound.pruneUpTo_length_le h W hU

/-- **At most `2^12` decoded stacks**, at every admissible shape. -/
theorem decodeStacksDistinct_length_le_johnson {μ R : ℕ} (h : Whir.Admissible μ R)
    (W : ℕ → List K) : (decodeStacksDistinct μ R W).length ≤ 2 ^ 12 := by
  rw [decodeStacksDistinct_eq h, decodeStacksFast_eq]
  exact LeanVM.Protocol.EndToEnd.Sound.decodeStacks_length_le h W

end

end LeanVM.Cost.Bounds
