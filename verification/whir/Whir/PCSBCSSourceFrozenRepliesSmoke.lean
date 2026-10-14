import Whir.PCSBCSSourceFrozenReplies
import Whir.PCSBCSSourceFrozenAccessorSmoke

set_option autoImplicit false
namespace Whir.PCSBCSSourceFrozenRepliesSmoke
open Concrete Protocol CausalGame CausalProbability WHIRHistory
open PCSBCSSourceFrozenAccessorSmoke

def smoke : IO Unit := do
  let answers ← match PCSBCSSourceFrozenReplies.replies current saved registry messages past with
    | none => throw (IO.userError "checked chronological prefix rejected")
    | some answers => pure answers
  check "checked assembly covers exactly the strict earlier protocol prefix"
    (answers.size == position current)
  match answers[position query]? with
  | some (.query rows _) =>
    check "assembly retains repeated source query order"
      (rows == #[#[E.ofK 13],#[E.ofK 17],#[E.ofK 13]])
  | _ => throw (IO.userError "assembled query position/tag")
  match answers[position boundary]? with
  | some (.fold _ (some next) residual) =>
    check "assembly retains full announced next oracle"
      (next[0]! == #[⟨100,200,300⟩,⟨400,500,600⟩] && residual.isEmpty)
  | _ => throw (IO.userError "assembled boundary position/tag")
  check "assembly rejects a missing referenced capture"
    (PCSBCSSourceFrozenReplies.replies current saved (fun _ => none) messages past).isNone
  let replacedTape := CausalProbability.set current tape (fun _ => ⟨99,98,97⟩,E.ofK 96)
  let replacedPast := WHIRFiatShamir.Prefix.ofTape current replacedTape
  let changed ← match PCSBCSSourceFrozenReplies.replies current saved registry messages replacedPast with
    | none => throw (IO.userError "whole current replacement rejected prefix")
    | some answers => pure answers
  match changed[position query]? with
  | some (.query rows _) =>
    check "whole current packet cannot warm predecessor queries"
      (rows == #[#[E.ofK 13],#[E.ofK 17],#[E.ofK 13]])
  | _ => throw (IO.userError "replacement query position/tag")

end Whir.PCSBCSSourceFrozenRepliesSmoke

#eval Whir.PCSBCSSourceFrozenRepliesSmoke.smoke
