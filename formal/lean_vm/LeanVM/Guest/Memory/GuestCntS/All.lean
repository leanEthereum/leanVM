/-
  LeanVM.Guest.Memory.GuestCntS.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntS.Part00
public import LeanVM.Guest.Memory.GuestCntS.Part01
public import LeanVM.Guest.Memory.GuestCntS.Part02
public import LeanVM.Guest.Memory.GuestCntS.Part03
public import LeanVM.Guest.Memory.GuestCntS.Part04
public import LeanVM.Guest.Memory.GuestCntS.Part05
public import LeanVM.Guest.Memory.GuestCntS.Part06
public import LeanVM.Guest.Memory.GuestCntS.Part07

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwschkIdx_19 : kwschkIdx 19 = true := by
  have hb : blockB (kwslookJ 19) (kwsomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwssplit_19_0.1 rfl kwssplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwssplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwssplit_19_96]
    rfl
  exact kwschkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwschkIdx_all : ∀ j < 991, kwschkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwschkIdx_19
  by_cases h0 : j < 11
  · exact kwsstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwsstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwsstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwsstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwsstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwsstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwsstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwsstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwsstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwsstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwsstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwsstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwsstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwsstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kwsstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kwsstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 328
  · exact kwsstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 358
  · exact kwsstaticRange_328.get (by omega) (by omega)
  by_cases h18 : j < 388
  · exact kwsstaticRange_358.get (by omega) (by omega)
  by_cases h19 : j < 418
  · exact kwsstaticRange_388.get (by omega) (by omega)
  by_cases h20 : j < 448
  · exact kwsstaticRange_418.get (by omega) (by omega)
  by_cases h21 : j < 478
  · exact kwsstaticRange_448.get (by omega) (by omega)
  by_cases h22 : j < 508
  · exact kwsstaticRange_478.get (by omega) (by omega)
  by_cases h23 : j < 538
  · exact kwsstaticRange_508.get (by omega) (by omega)
  by_cases h24 : j < 568
  · exact kwsstaticRange_538.get (by omega) (by omega)
  by_cases h25 : j < 598
  · exact kwsstaticRange_568.get (by omega) (by omega)
  by_cases h26 : j < 628
  · exact kwsstaticRange_598.get (by omega) (by omega)
  by_cases h27 : j < 658
  · exact kwsstaticRange_628.get (by omega) (by omega)
  by_cases h28 : j < 688
  · exact kwsstaticRange_658.get (by omega) (by omega)
  by_cases h29 : j < 718
  · exact kwsstaticRange_688.get (by omega) (by omega)
  by_cases h30 : j < 748
  · exact kwsstaticRange_718.get (by omega) (by omega)
  by_cases h31 : j < 778
  · exact kwsstaticRange_748.get (by omega) (by omega)
  by_cases h32 : j < 808
  · exact kwsstaticRange_778.get (by omega) (by omega)
  by_cases h33 : j < 838
  · exact kwsstaticRange_808.get (by omega) (by omega)
  by_cases h34 : j < 868
  · exact kwsstaticRange_838.get (by omega) (by omega)
  by_cases h35 : j < 898
  · exact kwsstaticRange_868.get (by omega) (by omega)
  by_cases h36 : j < 928
  · exact kwsstaticRange_898.get (by omega) (by omega)
  by_cases h37 : j < 958
  · exact kwsstaticRange_928.get (by omega) (by omega)
  by_cases h38 : j < 988
  · exact kwsstaticRange_958.get (by omega) (by omega)
  exact kwsstaticRange_988.get (by omega) (by omega)

end
end LeanVM.Guest
