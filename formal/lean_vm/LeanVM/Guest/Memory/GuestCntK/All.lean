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

theorem kwkchkIdx_all : ∀ j < 1037, kwkchkIdx j = true := by
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
  by_cases h14 : j < 337
  · exact kwkstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 344
  · exact kwkstaticRange_337.get (by omega) (by omega)
  by_cases h16 : j < 350
  · exact kwkstaticRange_344.get (by omega) (by omega)
  by_cases h17 : j < 357
  · exact kwkstaticRange_350.get (by omega) (by omega)
  by_cases h18 : j < 387
  · exact kwkstaticRange_357.get (by omega) (by omega)
  by_cases h19 : j < 417
  · exact kwkstaticRange_387.get (by omega) (by omega)
  by_cases h20 : j < 447
  · exact kwkstaticRange_417.get (by omega) (by omega)
  by_cases h21 : j < 477
  · exact kwkstaticRange_447.get (by omega) (by omega)
  by_cases h22 : j < 507
  · exact kwkstaticRange_477.get (by omega) (by omega)
  by_cases h23 : j < 537
  · exact kwkstaticRange_507.get (by omega) (by omega)
  by_cases h24 : j < 567
  · exact kwkstaticRange_537.get (by omega) (by omega)
  by_cases h25 : j < 597
  · exact kwkstaticRange_567.get (by omega) (by omega)
  by_cases h26 : j < 627
  · exact kwkstaticRange_597.get (by omega) (by omega)
  by_cases h27 : j < 657
  · exact kwkstaticRange_627.get (by omega) (by omega)
  by_cases h28 : j < 687
  · exact kwkstaticRange_657.get (by omega) (by omega)
  by_cases h29 : j < 717
  · exact kwkstaticRange_687.get (by omega) (by omega)
  by_cases h30 : j < 747
  · exact kwkstaticRange_717.get (by omega) (by omega)
  by_cases h31 : j < 777
  · exact kwkstaticRange_747.get (by omega) (by omega)
  by_cases h32 : j < 807
  · exact kwkstaticRange_777.get (by omega) (by omega)
  by_cases h33 : j < 837
  · exact kwkstaticRange_807.get (by omega) (by omega)
  by_cases h34 : j < 867
  · exact kwkstaticRange_837.get (by omega) (by omega)
  by_cases h35 : j < 897
  · exact kwkstaticRange_867.get (by omega) (by omega)
  by_cases h36 : j < 927
  · exact kwkstaticRange_897.get (by omega) (by omega)
  by_cases h37 : j < 957
  · exact kwkstaticRange_927.get (by omega) (by omega)
  by_cases h38 : j < 987
  · exact kwkstaticRange_957.get (by omega) (by omega)
  by_cases h39 : j < 1017
  · exact kwkstaticRange_987.get (by omega) (by omega)
  exact kwkstaticRange_1017.get (by omega) (by omega)

end
end LeanVM.Guest
