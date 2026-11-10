/-
  LeanVM.Guest.B1.Opening.Meaning

  The WHIR queries' meanings: `Interface.lean`.
-/

module

public import LeanVM.Guest.B1.Opening.Interface

/-!
# The WHIR queries' meanings

The meanings of `opening_queries` (with its inline `opening_query` and `novel_eval`) are in
`B1/Opening/Interface.lean`. The f128 guest has no `opening_fold`, `opening_ood_point`,
`opening_final_message` or `opening_row_weights`: the WHIR body's rounds are `B1/Whir/`'s.
-/
