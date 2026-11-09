/-
  LeanVM.Guest.Memory.GuestCntD.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntD.Part00
public import LeanVM.Guest.Memory.GuestCntD.Part01
public import LeanVM.Guest.Memory.GuestCntD.Part02
public import LeanVM.Guest.Memory.GuestCntD.Part03
public import LeanVM.Guest.Memory.GuestCntD.Part04
public import LeanVM.Guest.Memory.GuestCntD.Part05
public import LeanVM.Guest.Memory.GuestCntD.Part06
public import LeanVM.Guest.Memory.GuestCntD.Part07

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdchkIdx_19 : kwdchkIdx 19 = true := by
  have hb : blockB (kwdlookJ 19) (kwdomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwdsplit_19_0.1 rfl kwdsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwdsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwdsplit_19_96]
    rfl
  exact kwdchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwdchkIdx_all : ∀ j < 991, kwdchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwdchkIdx_19
  by_cases h0 : j < 11
  · exact kwdstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwdstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwdstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwdstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwdstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwdstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwdstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwdstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwdstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwdstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwdstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwdstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwdstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwdstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kwdstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kwdstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 328
  · exact kwdstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 358
  · exact kwdstaticRange_328.get (by omega) (by omega)
  by_cases h18 : j < 388
  · exact kwdstaticRange_358.get (by omega) (by omega)
  by_cases h19 : j < 418
  · exact kwdstaticRange_388.get (by omega) (by omega)
  by_cases h20 : j < 448
  · exact kwdstaticRange_418.get (by omega) (by omega)
  by_cases h21 : j < 478
  · exact kwdstaticRange_448.get (by omega) (by omega)
  by_cases h22 : j < 508
  · exact kwdstaticRange_478.get (by omega) (by omega)
  by_cases h23 : j < 538
  · exact kwdstaticRange_508.get (by omega) (by omega)
  by_cases h24 : j < 568
  · exact kwdstaticRange_538.get (by omega) (by omega)
  by_cases h25 : j < 598
  · exact kwdstaticRange_568.get (by omega) (by omega)
  by_cases h26 : j < 628
  · exact kwdstaticRange_598.get (by omega) (by omega)
  by_cases h27 : j < 658
  · exact kwdstaticRange_628.get (by omega) (by omega)
  by_cases h28 : j < 688
  · exact kwdstaticRange_658.get (by omega) (by omega)
  by_cases h29 : j < 718
  · exact kwdstaticRange_688.get (by omega) (by omega)
  by_cases h30 : j < 748
  · exact kwdstaticRange_718.get (by omega) (by omega)
  by_cases h31 : j < 778
  · exact kwdstaticRange_748.get (by omega) (by omega)
  by_cases h32 : j < 808
  · exact kwdstaticRange_778.get (by omega) (by omega)
  by_cases h33 : j < 838
  · exact kwdstaticRange_808.get (by omega) (by omega)
  by_cases h34 : j < 868
  · exact kwdstaticRange_838.get (by omega) (by omega)
  by_cases h35 : j < 898
  · exact kwdstaticRange_868.get (by omega) (by omega)
  by_cases h36 : j < 928
  · exact kwdstaticRange_898.get (by omega) (by omega)
  by_cases h37 : j < 958
  · exact kwdstaticRange_928.get (by omega) (by omega)
  by_cases h38 : j < 988
  · exact kwdstaticRange_958.get (by omega) (by omega)
  exact kwdstaticRange_988.get (by omega) (by omega)

end
end LeanVM.Guest
