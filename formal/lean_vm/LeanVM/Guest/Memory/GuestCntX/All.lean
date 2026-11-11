/-
  LeanVM.Guest.Memory.GuestCntX.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntX.Part00
public import LeanVM.Guest.Memory.GuestCntX.Part01
public import LeanVM.Guest.Memory.GuestCntX.Part02
public import LeanVM.Guest.Memory.GuestCntX.Part03
public import LeanVM.Guest.Memory.GuestCntX.Part04
public import LeanVM.Guest.Memory.GuestCntX.Part05
public import LeanVM.Guest.Memory.GuestCntX.Part06
public import LeanVM.Guest.Memory.GuestCntX.Part07

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxchkIdx_19 : kwxchkIdx 19 = true := by
  have hb : blockB (kwxlookJ 19) (kwxomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwxsplit_19_0.1 rfl kwxsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwxsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwxsplit_19_96]
    rfl
  exact kwxchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwxchkIdx_all : ∀ j < 1035, kwxchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwxchkIdx_19
  by_cases h0 : j < 11
  · exact kwxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwxstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwxstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwxstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwxstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwxstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwxstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwxstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwxstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwxstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwxstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwxstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwxstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwxstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 336
  · exact kwxstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 342
  · exact kwxstaticRange_336.get (by omega) (by omega)
  by_cases h16 : j < 348
  · exact kwxstaticRange_342.get (by omega) (by omega)
  by_cases h17 : j < 354
  · exact kwxstaticRange_348.get (by omega) (by omega)
  by_cases h18 : j < 384
  · exact kwxstaticRange_354.get (by omega) (by omega)
  by_cases h19 : j < 414
  · exact kwxstaticRange_384.get (by omega) (by omega)
  by_cases h20 : j < 444
  · exact kwxstaticRange_414.get (by omega) (by omega)
  by_cases h21 : j < 474
  · exact kwxstaticRange_444.get (by omega) (by omega)
  by_cases h22 : j < 504
  · exact kwxstaticRange_474.get (by omega) (by omega)
  by_cases h23 : j < 534
  · exact kwxstaticRange_504.get (by omega) (by omega)
  by_cases h24 : j < 564
  · exact kwxstaticRange_534.get (by omega) (by omega)
  by_cases h25 : j < 594
  · exact kwxstaticRange_564.get (by omega) (by omega)
  by_cases h26 : j < 624
  · exact kwxstaticRange_594.get (by omega) (by omega)
  by_cases h27 : j < 654
  · exact kwxstaticRange_624.get (by omega) (by omega)
  by_cases h28 : j < 684
  · exact kwxstaticRange_654.get (by omega) (by omega)
  by_cases h29 : j < 714
  · exact kwxstaticRange_684.get (by omega) (by omega)
  by_cases h30 : j < 744
  · exact kwxstaticRange_714.get (by omega) (by omega)
  by_cases h31 : j < 774
  · exact kwxstaticRange_744.get (by omega) (by omega)
  by_cases h32 : j < 804
  · exact kwxstaticRange_774.get (by omega) (by omega)
  by_cases h33 : j < 834
  · exact kwxstaticRange_804.get (by omega) (by omega)
  by_cases h34 : j < 864
  · exact kwxstaticRange_834.get (by omega) (by omega)
  by_cases h35 : j < 894
  · exact kwxstaticRange_864.get (by omega) (by omega)
  by_cases h36 : j < 924
  · exact kwxstaticRange_894.get (by omega) (by omega)
  by_cases h37 : j < 954
  · exact kwxstaticRange_924.get (by omega) (by omega)
  by_cases h38 : j < 984
  · exact kwxstaticRange_954.get (by omega) (by omega)
  by_cases h39 : j < 1014
  · exact kwxstaticRange_984.get (by omega) (by omega)
  exact kwxstaticRange_1014.get (by omega) (by omega)

end
end LeanVM.Guest
