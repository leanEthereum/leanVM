/-
  LeanVM.Guest.B1.Main.KidCoverAtB

  A child's statement digest within bounds before the memory (`CompleteAtDTB`): the pure
  `statement_digest` within its static bound. Same proof as `KidCoverAt`.
-/

module

public import LeanVM.Guest.B1.Main.KidCoverAt
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.Memory.Size

/-!
# A child's statement digest, bounded

`statement_completeAtB` from a `TotalLe` bound.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtDTB Returns completeAt_of_rel_pureBat)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **`statement_digest` within its static bound.** -/
theorem statement_completeAtB {Lin : Layout} {args rets : List E} (SB : String → ℕ)
    (hT : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest"))
    (h : ∀ rd, MemL rd Lin → MeaningStatementDigest rd args rets) :
    CompleteAtDTB fs cert 16 "statement_digest" Lin args (Returns rets) (fun _ => True)
      (SB "statement_digest") :=
  (completeAt_of_rel_pureBat sd_pure (List.mem_singleton_self _)
    (fun rd hm => statement_digest_complete rd args rets (h rd hm)) 16
    (fun rd t hn hv hb => hT rd t _ _ hn hv hb)).toDTB

end
end LeanVM.Guest.B1.Main
