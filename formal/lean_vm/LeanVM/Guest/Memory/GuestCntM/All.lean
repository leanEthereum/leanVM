/-
  LeanVM.Guest.Memory.GuestCntM.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntM.Part00
public import LeanVM.Guest.Memory.GuestCntM.Part01
public import LeanVM.Guest.Memory.GuestCntM.Part02
public import LeanVM.Guest.Memory.GuestCntM.Part03
public import LeanVM.Guest.Memory.GuestCntM.Part04
public import LeanVM.Guest.Memory.GuestCntM.Part05
public import LeanVM.Guest.Memory.GuestCntM.Part06
public import LeanVM.Guest.Memory.GuestCntM.Part07

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmchkIdx_19 : kwmchkIdx 19 = true := by
  have hb : blockB (kwmlookJ 19) (kwmomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwmsplit_19_0.1 rfl kwmsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwmsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwmsplit_19_96]
    rfl
  exact kwmchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwmchkIdx_all : ∀ j < 991, kwmchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwmchkIdx_19
  by_cases h0 : j < 11
  · exact kwmstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwmstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwmstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwmstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwmstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwmstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwmstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwmstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwmstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwmstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwmstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwmstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwmstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwmstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kwmstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kwmstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 328
  · exact kwmstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 358
  · exact kwmstaticRange_328.get (by omega) (by omega)
  by_cases h18 : j < 388
  · exact kwmstaticRange_358.get (by omega) (by omega)
  by_cases h19 : j < 418
  · exact kwmstaticRange_388.get (by omega) (by omega)
  by_cases h20 : j < 448
  · exact kwmstaticRange_418.get (by omega) (by omega)
  by_cases h21 : j < 478
  · exact kwmstaticRange_448.get (by omega) (by omega)
  by_cases h22 : j < 508
  · exact kwmstaticRange_478.get (by omega) (by omega)
  by_cases h23 : j < 538
  · exact kwmstaticRange_508.get (by omega) (by omega)
  by_cases h24 : j < 568
  · exact kwmstaticRange_538.get (by omega) (by omega)
  by_cases h25 : j < 598
  · exact kwmstaticRange_568.get (by omega) (by omega)
  by_cases h26 : j < 628
  · exact kwmstaticRange_598.get (by omega) (by omega)
  by_cases h27 : j < 658
  · exact kwmstaticRange_628.get (by omega) (by omega)
  by_cases h28 : j < 688
  · exact kwmstaticRange_658.get (by omega) (by omega)
  by_cases h29 : j < 718
  · exact kwmstaticRange_688.get (by omega) (by omega)
  by_cases h30 : j < 748
  · exact kwmstaticRange_718.get (by omega) (by omega)
  by_cases h31 : j < 778
  · exact kwmstaticRange_748.get (by omega) (by omega)
  by_cases h32 : j < 808
  · exact kwmstaticRange_778.get (by omega) (by omega)
  by_cases h33 : j < 838
  · exact kwmstaticRange_808.get (by omega) (by omega)
  by_cases h34 : j < 868
  · exact kwmstaticRange_838.get (by omega) (by omega)
  by_cases h35 : j < 898
  · exact kwmstaticRange_868.get (by omega) (by omega)
  by_cases h36 : j < 928
  · exact kwmstaticRange_898.get (by omega) (by omega)
  by_cases h37 : j < 958
  · exact kwmstaticRange_928.get (by omega) (by omega)
  by_cases h38 : j < 988
  · exact kwmstaticRange_958.get (by omega) (by omega)
  exact kwmstaticRange_988.get (by omega) (by omega)

end
end LeanVM.Guest
