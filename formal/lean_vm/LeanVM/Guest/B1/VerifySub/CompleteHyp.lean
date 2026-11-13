/-
  LeanVM.Guest.B1.VerifySub.CompleteHyp

  `verify_sub`'s completeness in the form main's goals take (`Main.VsCompleteHyp`).
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteBT
public import LeanVM.Guest.B1.Main.VerifySubGoals

/-!
# `VsCompleteHyp`, discharged

`vsCompleteHyp_fs`: at the deployed frame sizes `B2C.fs`, for certificates whose runs fit their
frames with consecutive cells, `verify_sub` is complete on every child `VsChildOk` holds of, by a
tree of `vsTsAny` within `vsBoundAt W vkBound` at its announced stack log and rate
(`verify_sub_completeBT_fs`), and that shape is an opening arm (`child_segments`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **`verify_sub`'s completeness hypothesis of main's goals, discharged** at `B2C.fs`. -/
theorem vsCompleteHyp_fs {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {cert : String → V → ℕ} (hrf : Lift.RunsFit LeanVM.Guest.B2C.fs cert)
    (hcons : RunsConsec cert) (W : VsWordsOs LeanVM.Guest.B2C.fs) :
    Main.VsCompleteHyp bytecode LeanVM.Guest.B2C.fs cert 16
      (vsTsAny LeanVM.Guest.B2C.fs W vkBound) (vsBoundAt W vkBound) where
  complete seed c sqE outE Lin hc hexp hout :=
    verify_sub_completeBT_fs hbl hrf hcons W le_rfl seed c sqE outE Lin hc.1 hc.2.1 hc.2.2.1
      hc.2.2.2 hexp hout
  shape seed c hc := by
    obtain ⟨S⟩ := child_segments hbl seed c hc.1 hc.2.2.1 hc.2.2.2
    rw [childShape_of S.hann]
    exact ⟨S.hmu20, S.hmu30, S.hr1, S.hr4⟩

end
end LeanVM.Guest.B1.VerifySub
