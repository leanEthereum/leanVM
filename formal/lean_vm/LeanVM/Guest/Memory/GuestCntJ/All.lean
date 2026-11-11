/-
  LeanVM.Guest.Memory.GuestCntJ.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntJ.Part00
public import LeanVM.Guest.Memory.GuestCntJ.Part01
public import LeanVM.Guest.Memory.GuestCntJ.Part02
public import LeanVM.Guest.Memory.GuestCntJ.Part03
public import LeanVM.Guest.Memory.GuestCntJ.Part04
public import LeanVM.Guest.Memory.GuestCntJ.Part05
public import LeanVM.Guest.Memory.GuestCntJ.Part06
public import LeanVM.Guest.Memory.GuestCntJ.Part07

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjchkIdx_19 : kwjchkIdx 19 = true := by
  have hb : blockB (kwjlookJ 19) (kwjomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwjsplit_19_0.1 rfl kwjsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwjsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwjsplit_19_96]
    rfl
  exact kwjchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwjchkIdx_all : ∀ j < 1035, kwjchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwjchkIdx_19
  by_cases h0 : j < 11
  · exact kwjstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwjstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwjstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwjstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwjstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwjstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwjstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwjstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwjstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwjstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwjstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwjstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwjstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwjstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 336
  · exact kwjstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 342
  · exact kwjstaticRange_336.get (by omega) (by omega)
  by_cases h16 : j < 348
  · exact kwjstaticRange_342.get (by omega) (by omega)
  by_cases h17 : j < 354
  · exact kwjstaticRange_348.get (by omega) (by omega)
  by_cases h18 : j < 384
  · exact kwjstaticRange_354.get (by omega) (by omega)
  by_cases h19 : j < 414
  · exact kwjstaticRange_384.get (by omega) (by omega)
  by_cases h20 : j < 444
  · exact kwjstaticRange_414.get (by omega) (by omega)
  by_cases h21 : j < 474
  · exact kwjstaticRange_444.get (by omega) (by omega)
  by_cases h22 : j < 504
  · exact kwjstaticRange_474.get (by omega) (by omega)
  by_cases h23 : j < 534
  · exact kwjstaticRange_504.get (by omega) (by omega)
  by_cases h24 : j < 564
  · exact kwjstaticRange_534.get (by omega) (by omega)
  by_cases h25 : j < 594
  · exact kwjstaticRange_564.get (by omega) (by omega)
  by_cases h26 : j < 624
  · exact kwjstaticRange_594.get (by omega) (by omega)
  by_cases h27 : j < 654
  · exact kwjstaticRange_624.get (by omega) (by omega)
  by_cases h28 : j < 684
  · exact kwjstaticRange_654.get (by omega) (by omega)
  by_cases h29 : j < 714
  · exact kwjstaticRange_684.get (by omega) (by omega)
  by_cases h30 : j < 744
  · exact kwjstaticRange_714.get (by omega) (by omega)
  by_cases h31 : j < 774
  · exact kwjstaticRange_744.get (by omega) (by omega)
  by_cases h32 : j < 804
  · exact kwjstaticRange_774.get (by omega) (by omega)
  by_cases h33 : j < 834
  · exact kwjstaticRange_804.get (by omega) (by omega)
  by_cases h34 : j < 864
  · exact kwjstaticRange_834.get (by omega) (by omega)
  by_cases h35 : j < 894
  · exact kwjstaticRange_864.get (by omega) (by omega)
  by_cases h36 : j < 924
  · exact kwjstaticRange_894.get (by omega) (by omega)
  by_cases h37 : j < 954
  · exact kwjstaticRange_924.get (by omega) (by omega)
  by_cases h38 : j < 984
  · exact kwjstaticRange_954.get (by omega) (by omega)
  by_cases h39 : j < 1014
  · exact kwjstaticRange_984.get (by omega) (by omega)
  exact kwjstaticRange_1014.get (by omega) (by omega)

end
end LeanVM.Guest
