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

theorem kwmchkIdx_all : ∀ j < 1037, kwmchkIdx j = true := by
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
  by_cases h14 : j < 337
  · exact kwmstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 344
  · exact kwmstaticRange_337.get (by omega) (by omega)
  by_cases h16 : j < 350
  · exact kwmstaticRange_344.get (by omega) (by omega)
  by_cases h17 : j < 357
  · exact kwmstaticRange_350.get (by omega) (by omega)
  by_cases h18 : j < 387
  · exact kwmstaticRange_357.get (by omega) (by omega)
  by_cases h19 : j < 417
  · exact kwmstaticRange_387.get (by omega) (by omega)
  by_cases h20 : j < 447
  · exact kwmstaticRange_417.get (by omega) (by omega)
  by_cases h21 : j < 477
  · exact kwmstaticRange_447.get (by omega) (by omega)
  by_cases h22 : j < 507
  · exact kwmstaticRange_477.get (by omega) (by omega)
  by_cases h23 : j < 537
  · exact kwmstaticRange_507.get (by omega) (by omega)
  by_cases h24 : j < 567
  · exact kwmstaticRange_537.get (by omega) (by omega)
  by_cases h25 : j < 597
  · exact kwmstaticRange_567.get (by omega) (by omega)
  by_cases h26 : j < 627
  · exact kwmstaticRange_597.get (by omega) (by omega)
  by_cases h27 : j < 657
  · exact kwmstaticRange_627.get (by omega) (by omega)
  by_cases h28 : j < 687
  · exact kwmstaticRange_657.get (by omega) (by omega)
  by_cases h29 : j < 717
  · exact kwmstaticRange_687.get (by omega) (by omega)
  by_cases h30 : j < 747
  · exact kwmstaticRange_717.get (by omega) (by omega)
  by_cases h31 : j < 777
  · exact kwmstaticRange_747.get (by omega) (by omega)
  by_cases h32 : j < 807
  · exact kwmstaticRange_777.get (by omega) (by omega)
  by_cases h33 : j < 837
  · exact kwmstaticRange_807.get (by omega) (by omega)
  by_cases h34 : j < 867
  · exact kwmstaticRange_837.get (by omega) (by omega)
  by_cases h35 : j < 897
  · exact kwmstaticRange_867.get (by omega) (by omega)
  by_cases h36 : j < 927
  · exact kwmstaticRange_897.get (by omega) (by omega)
  by_cases h37 : j < 957
  · exact kwmstaticRange_927.get (by omega) (by omega)
  by_cases h38 : j < 987
  · exact kwmstaticRange_957.get (by omega) (by omega)
  by_cases h39 : j < 1017
  · exact kwmstaticRange_987.get (by omega) (by omega)
  exact kwmstaticRange_1017.get (by omega) (by omega)

end
end LeanVM.Guest
