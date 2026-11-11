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

theorem kwkchkIdx_all : ∀ j < 1035, kwkchkIdx j = true := by
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
  by_cases h14 : j < 336
  · exact kwkstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 342
  · exact kwkstaticRange_336.get (by omega) (by omega)
  by_cases h16 : j < 348
  · exact kwkstaticRange_342.get (by omega) (by omega)
  by_cases h17 : j < 354
  · exact kwkstaticRange_348.get (by omega) (by omega)
  by_cases h18 : j < 384
  · exact kwkstaticRange_354.get (by omega) (by omega)
  by_cases h19 : j < 414
  · exact kwkstaticRange_384.get (by omega) (by omega)
  by_cases h20 : j < 444
  · exact kwkstaticRange_414.get (by omega) (by omega)
  by_cases h21 : j < 474
  · exact kwkstaticRange_444.get (by omega) (by omega)
  by_cases h22 : j < 504
  · exact kwkstaticRange_474.get (by omega) (by omega)
  by_cases h23 : j < 534
  · exact kwkstaticRange_504.get (by omega) (by omega)
  by_cases h24 : j < 564
  · exact kwkstaticRange_534.get (by omega) (by omega)
  by_cases h25 : j < 594
  · exact kwkstaticRange_564.get (by omega) (by omega)
  by_cases h26 : j < 624
  · exact kwkstaticRange_594.get (by omega) (by omega)
  by_cases h27 : j < 654
  · exact kwkstaticRange_624.get (by omega) (by omega)
  by_cases h28 : j < 684
  · exact kwkstaticRange_654.get (by omega) (by omega)
  by_cases h29 : j < 714
  · exact kwkstaticRange_684.get (by omega) (by omega)
  by_cases h30 : j < 744
  · exact kwkstaticRange_714.get (by omega) (by omega)
  by_cases h31 : j < 774
  · exact kwkstaticRange_744.get (by omega) (by omega)
  by_cases h32 : j < 804
  · exact kwkstaticRange_774.get (by omega) (by omega)
  by_cases h33 : j < 834
  · exact kwkstaticRange_804.get (by omega) (by omega)
  by_cases h34 : j < 864
  · exact kwkstaticRange_834.get (by omega) (by omega)
  by_cases h35 : j < 894
  · exact kwkstaticRange_864.get (by omega) (by omega)
  by_cases h36 : j < 924
  · exact kwkstaticRange_894.get (by omega) (by omega)
  by_cases h37 : j < 954
  · exact kwkstaticRange_924.get (by omega) (by omega)
  by_cases h38 : j < 984
  · exact kwkstaticRange_954.get (by omega) (by omega)
  by_cases h39 : j < 1014
  · exact kwkstaticRange_984.get (by omega) (by omega)
  exact kwkstaticRange_1014.get (by omega) (by omega)

end
end LeanVM.Guest
