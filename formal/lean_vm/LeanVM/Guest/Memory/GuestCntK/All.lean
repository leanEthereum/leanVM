/-
  LeanVM.Guest.Memory.GuestCntK.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntK.Part00
public import LeanVM.Guest.Memory.GuestCntK.Part01
public import LeanVM.Guest.Memory.GuestCntK.Part02
public import LeanVM.Guest.Memory.GuestCntK.Part03
public import LeanVM.Guest.Memory.GuestCntK.Part04
public import LeanVM.Guest.Memory.GuestCntK.Part05
public import LeanVM.Guest.Memory.GuestCntK.Part06
public import LeanVM.Guest.Memory.GuestCntK.Part07

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkchkIdx_19 : kwkchkIdx 19 = true := by
  have hb : blockB (kwklookJ 19) (kwkomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwksplit_19_0.1 rfl kwksplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwksplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwksplit_19_96]
    rfl
  exact kwkchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwkchkIdx_all : ∀ j < 991, kwkchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwkchkIdx_19
  by_cases h0 : j < 11
  · exact kwkstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwkstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwkstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwkstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwkstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwkstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwkstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwkstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwkstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwkstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwkstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwkstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwkstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwkstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kwkstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kwkstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 328
  · exact kwkstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 358
  · exact kwkstaticRange_328.get (by omega) (by omega)
  by_cases h18 : j < 388
  · exact kwkstaticRange_358.get (by omega) (by omega)
  by_cases h19 : j < 418
  · exact kwkstaticRange_388.get (by omega) (by omega)
  by_cases h20 : j < 448
  · exact kwkstaticRange_418.get (by omega) (by omega)
  by_cases h21 : j < 478
  · exact kwkstaticRange_448.get (by omega) (by omega)
  by_cases h22 : j < 508
  · exact kwkstaticRange_478.get (by omega) (by omega)
  by_cases h23 : j < 538
  · exact kwkstaticRange_508.get (by omega) (by omega)
  by_cases h24 : j < 568
  · exact kwkstaticRange_538.get (by omega) (by omega)
  by_cases h25 : j < 598
  · exact kwkstaticRange_568.get (by omega) (by omega)
  by_cases h26 : j < 628
  · exact kwkstaticRange_598.get (by omega) (by omega)
  by_cases h27 : j < 658
  · exact kwkstaticRange_628.get (by omega) (by omega)
  by_cases h28 : j < 688
  · exact kwkstaticRange_658.get (by omega) (by omega)
  by_cases h29 : j < 718
  · exact kwkstaticRange_688.get (by omega) (by omega)
  by_cases h30 : j < 748
  · exact kwkstaticRange_718.get (by omega) (by omega)
  by_cases h31 : j < 778
  · exact kwkstaticRange_748.get (by omega) (by omega)
  by_cases h32 : j < 808
  · exact kwkstaticRange_778.get (by omega) (by omega)
  by_cases h33 : j < 838
  · exact kwkstaticRange_808.get (by omega) (by omega)
  by_cases h34 : j < 868
  · exact kwkstaticRange_838.get (by omega) (by omega)
  by_cases h35 : j < 898
  · exact kwkstaticRange_868.get (by omega) (by omega)
  by_cases h36 : j < 928
  · exact kwkstaticRange_898.get (by omega) (by omega)
  by_cases h37 : j < 958
  · exact kwkstaticRange_928.get (by omega) (by omega)
  by_cases h38 : j < 988
  · exact kwkstaticRange_958.get (by omega) (by omega)
  exact kwkstaticRange_988.get (by omega) (by omega)

end
end LeanVM.Guest
