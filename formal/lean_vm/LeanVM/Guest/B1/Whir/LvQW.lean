/-
  LeanVM.Guest.B1.Whir.LvQW

  A level's `opening_queries` calls, sound with their queries named.
-/

module

public import LeanVM.Guest.B1.Whir.InterfaceW
public import LeanVM.Guest.B1.Opening.Witness

/-!
# A level's `opening_queries` calls

`LvQW rd C lvl lv W`: the calls of `C` of the `opening_queries` specialization a level's
`level_queries` calls (`oqNameOf`) are sound with their queries `W` at the call's words
(`MeaningOpeningQueriesW`), given their iterations and the window pointers.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- A level's `opening_queries` calls of `C`, sound with their queries `W` at the call's words. -/
def LvQW (rd : Reader) (C : CallRel) (lvl : ℕ) (lv : OsLv) (W : List E → List E → List QW) :
    Prop :=
  ∀ args rets, C (oqNameOf lvl lv) args rets →
    args.getD 6 0 = gen ^ (lv.queries / (1 + if lvl = 0 then 1 else 0)) →
    lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG → lv.capDepth ≤ lv.depth →
    (∀ N, args.getD 6 0 = gen ^ N → N < ordG → QueryWinsOk rd (args.getD 4 0)
      (oqCount (lv.queries % 2 * (if lvl = 0 then 1 else 0)) (if lvl = 0 then 1 else 0) N)
      lv.depth lv.capDepth) →
    MeaningOpeningQueriesW (lv.queries % 2 * (if lvl = 0 then 1 else 0))
      (if lvl = 0 then 1 else 0) lv.interleave lv.depth lv.capDepth rd (W args rets) args rets

end
end LeanVM.Guest.B1.Whir
