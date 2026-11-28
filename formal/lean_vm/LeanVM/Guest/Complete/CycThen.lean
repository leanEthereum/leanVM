/-
  LeanVM.Guest.Complete.CycThen

  The two claim-list digests' empty-list arms (`ThenSame`): their split's values are named only on the other arm, so
  set to `1` they keep the path (`hand3`'s `sameOnPath_setVals`).
-/

module

public import LeanVM.Guest.Complete.CycCall

/-!
# The digests' empty-list arms

`claim_list_digest` (`thenSame_claim`, as `claimThenHand`) and `child_claim_list_digest` (`thenSame_child`): on the
empty list's arm (`v3 = 0`, `v6 = 0`) the bodies walk as with the other arm emptied (`walk_ite_zero`), which names
neither split value, so `setVals σ [split values] 1` runs the same path. With them, `MainCycles` from `verify_sub`'s
values and the loop's counts (`mainCycles_of_vs`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-- **`claim_list_digest`'s empty arm keeps its path with its split's values `1`.** -/
theorem thenSame_claim : ThenSame "claim_list_digest" (.n 3) (.n 12) (.n 13) := by
  intro rd σ _ h3
  have h3' : setVals σ [.n 12, .n 13] 1 (.n 3) = 0 := by rw [setVals_of_not_mem (by decide)]; exact h3
  refine ⟨setVals σ [.n 12, .n 13] 1, ?_, setVals_of_mem (by simp), setVals_of_mem (by simp)⟩
  refine sameOnPath_setVals (b := clThenBody) (fun fn hfn => ?_) clThen_names.1
  rw [Digest.find_claim_list_digest] at hfn
  obtain rfl := Option.some.inj hfn
  refine ⟨clThen_names.2, ?_, ?_⟩
  · rw [cl_body_split]; exact walk_ite_zero h3 _ _
  · rw [cl_body_split]; exact walk_ite_zero h3' _ _

/-- `child_claim_list_digest`'s nonempty list's arm. -/
noncomputable def cclElse : List Stmt := match Fn.body fn% «child_claim_list_digest» with
  | [_, _, .ite _ _ n, _, _, _] => n
  | _ => []

/-- `child_claim_list_digest`'s body with its nonempty list's arm emptied. -/
noncomputable def cclThenBody : List Stmt :=
  (fn% «child_claim_list_digest»).body.take 2 ++ .ite (.n 6) Digest.cc25Zero [] ::
    (fn% «child_claim_list_digest»).body.drop 3

set_option maxRecDepth 100000 in
theorem ccl_body_split : (fn% «child_claim_list_digest»).body = (fn% «child_claim_list_digest»).body.take 2 ++
    .ite (.n 6) Digest.cc25Zero cclElse :: (fn% «child_claim_list_digest»).body.drop 3 := by
  rw [Digest.child_claim_list_digest_shape]; rfl

set_option maxRecDepth 100000 in
theorem cclThen_names : (Stmt.usesList cclThenBody ++ Stmt.tmpsList cclThenBody).all (· ∉ [V.n 15, V.n 16]) = true ∧
    (fn% «child_claim_list_digest»).params.all (· ∉ [V.n 15, V.n 16]) = true := by
  decide +kernel

/-- **`child_claim_list_digest`'s empty arm keeps its path with its split's values `1`.** -/
theorem thenSame_child : ThenSame "child_claim_list_digest" (.n 6) (.n 15) (.n 16) := by
  intro rd σ _ h6
  have h6' : setVals σ [.n 15, .n 16] 1 (.n 6) = 0 := by rw [setVals_of_not_mem (by decide)]; exact h6
  refine ⟨setVals σ [.n 15, .n 16] 1, ?_, setVals_of_mem (by simp), setVals_of_mem (by simp)⟩
  refine sameOnPath_setVals (b := cclThenBody) (fun fn hfn => ?_) cclThen_names.1
  rw [Digest.find_child_claim_list_digest] at hfn
  obtain rfl := Option.some.inj hfn
  refine ⟨cclThen_names.2, ?_, ?_⟩
  · rw [ccl_body_split]; exact walk_ite_zero h6 _ _
  · rw [ccl_body_split]; exact walk_ite_zero h6' _ _

/-- **`main`'s cycle hand facts from what `verify_sub` certifies and each iteration's counts.** -/
theorem mainCycles_of_vs {al : String → Bool} (hV : VsVals al) (hM : LoopMeta al) : MainCycles al true :=
  mainCycles_of_vals thenSame_claim thenSame_child hV hM (mainLoopCall al)

end
end LeanVM.Guest.Complete
