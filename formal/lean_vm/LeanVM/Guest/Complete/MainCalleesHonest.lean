/-
  LeanVM.Guest.Complete.MainCalleesHonest

  `main`'s callees at the honest coverage table, given the children's claim lists.
-/

module

public import LeanVM.Guest.Complete.Claims.Field
public import LeanVM.Guest.Complete.Claims.Kids
public import LeanVM.Guest.Complete.Claims.CoverRaw
public import LeanVM.Guest.Complete.RawFields
public import LeanVM.Guest.Complete.DaFieldA
public import LeanVM.Guest.Complete.Agg.Exact
public import LeanVM.Guest.Memory.GuestWf

/-!
# `main`'s callees, at the honest coverage table

`mainCalleesOpenA_of_kids : KidsListsOpen alW 17 → MainCalleesOpenA alW 17`: at `honestCover`
(`honestCover_length`, `kidCover_honest`, `rawMarks_honest`), every field of `MainCalleesOpenAt`
bounded (`AtEveryB … (2^60) (2^40)`): the claim lists (`mainClaimListsE`), the raw signatures' loops
(`rawx_field`, `raws_field`), `da_verify` (`da_field_b2c`), `aggregate_claims` (`aggField_honest`),
and the children's claim lists from `KidsListsOpen`. `mainCalleesOpenA`: the same from claims'
`kidsListsOpen`, so `main`'s callees are closed.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node

@[expose] public section

/-- **`main`'s callees left, at the deployed choices, from the children's claim lists.** -/
theorem mainCalleesOpenA_of_kids (H : KidsListsOpen alW 17) : MainCalleesOpenA alW 17 :=
  ⟨fun s w hr hl hok => by
    have hcv := honestCover_length s w
    obtain ⟨hkx, hks⟩ := H s w (honestCover s w) hr hl hok hcv (kidCover_honest s w)
    obtain ⟨hclx, hcsp⟩ := mainClaimListsE (al := alW) (k := 17) (by norm_num) hr hl (honestCover s w)
    exact ⟨honestCover s w, hcv,
      { clx := hclx
        csp := hcsp
        rawx := rawx_field (by norm_num) hr hl hok hcv (rawMarks_honest s w)
        raws := raws_field (by norm_num) hr hl hok hcv (rawMarks_honest s w)
        da := da_field_b2c coreProgram_wf (by norm_num) hr.2.1
        kidx := hkx
        kids := hks
        agg := Agg.aggField_honest hr hl hok }⟩⟩

/-- **`main`'s callees, at the deployed choices**: none left open. -/
theorem mainCalleesOpenA : MainCalleesOpenA alW 17 :=
  mainCalleesOpenA_of_kids kidsListsOpen

end
end LeanVM.Guest.Complete
