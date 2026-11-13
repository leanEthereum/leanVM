/-
  LeanVM.Guest.B1.Opening.QueriesAllW

  Every deployed specialization of `opening_queries` is sound with its queries named.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesFns
public import LeanVM.Guest.B1.Opening.QueriesMainW

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-- `Witness.lean`'s statement at the guest's `coreProgram`. -/
abbrev opening_queries_sound_w_Spec (name loop : String) (sh : OqShape) : Prop :=
  opening_queries_sound_w_SpecP coreProgram name loop sh

/-- `Witness.lean`'s statement at the guest's `coreProgram`, every specialization. -/
abbrev opening_queries_all_sound_w_Spec : Prop := opening_queries_all_sound_w_SpecP coreProgram

/-- **Every deployed `opening_queries` is sound with its queries named**: its base's theorem at
its functions (`oqFns_all`) and its shape's facts (`oqSide_all`). -/
theorem opening_queries_all_sound_w : opening_queries_all_sound_w_Spec := by
  intro p hp
  obtain ⟨hW, fm, fl, hfm, hpm, hbm, hfl, hpl, hbl⟩ := oqFns_all p hp
  obtain ⟨hs, hfin, hb, hpd, hcd, hcd8, hdep, -⟩ := oqSide_all p hp
  rcases hb with ⟨hb0, hodd⟩ | ⟨hb1, hnf, hodd⟩
  · rw [hodd] at hbm
    exact oqMain0_sound_w hs hfin hb0 hodd hpd (by omega) hcd8 hdep hW hfm hpm hbm hfl hpl
      (hbl.trans (oqLoopT_zero hb0 _ _ _))
  · exact oqMain1_sound_w hs hfin hb1 hnf hodd hpd (by omega) hcd8 hdep hW hfm hpm hbm hfl hpl
      (hbl.trans (oqLoopT_one hb1 _ _ _))

end
end LeanVM.Guest.B1
