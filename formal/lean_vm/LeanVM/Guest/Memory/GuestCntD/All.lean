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

theorem kwdchkIdx_all : ∀ j < 1035, kwdchkIdx j = true := by
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
  by_cases h14 : j < 336
  · exact kwdstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 342
  · exact kwdstaticRange_336.get (by omega) (by omega)
  by_cases h16 : j < 348
  · exact kwdstaticRange_342.get (by omega) (by omega)
  by_cases h17 : j < 354
  · exact kwdstaticRange_348.get (by omega) (by omega)
  by_cases h18 : j < 384
  · exact kwdstaticRange_354.get (by omega) (by omega)
  by_cases h19 : j < 414
  · exact kwdstaticRange_384.get (by omega) (by omega)
  by_cases h20 : j < 444
  · exact kwdstaticRange_414.get (by omega) (by omega)
  by_cases h21 : j < 474
  · exact kwdstaticRange_444.get (by omega) (by omega)
  by_cases h22 : j < 504
  · exact kwdstaticRange_474.get (by omega) (by omega)
  by_cases h23 : j < 534
  · exact kwdstaticRange_504.get (by omega) (by omega)
  by_cases h24 : j < 564
  · exact kwdstaticRange_534.get (by omega) (by omega)
  by_cases h25 : j < 594
  · exact kwdstaticRange_564.get (by omega) (by omega)
  by_cases h26 : j < 624
  · exact kwdstaticRange_594.get (by omega) (by omega)
  by_cases h27 : j < 654
  · exact kwdstaticRange_624.get (by omega) (by omega)
  by_cases h28 : j < 684
  · exact kwdstaticRange_654.get (by omega) (by omega)
  by_cases h29 : j < 714
  · exact kwdstaticRange_684.get (by omega) (by omega)
  by_cases h30 : j < 744
  · exact kwdstaticRange_714.get (by omega) (by omega)
  by_cases h31 : j < 774
  · exact kwdstaticRange_744.get (by omega) (by omega)
  by_cases h32 : j < 804
  · exact kwdstaticRange_774.get (by omega) (by omega)
  by_cases h33 : j < 834
  · exact kwdstaticRange_804.get (by omega) (by omega)
  by_cases h34 : j < 864
  · exact kwdstaticRange_834.get (by omega) (by omega)
  by_cases h35 : j < 894
  · exact kwdstaticRange_864.get (by omega) (by omega)
  by_cases h36 : j < 924
  · exact kwdstaticRange_894.get (by omega) (by omega)
  by_cases h37 : j < 954
  · exact kwdstaticRange_924.get (by omega) (by omega)
  by_cases h38 : j < 984
  · exact kwdstaticRange_954.get (by omega) (by omega)
  by_cases h39 : j < 1014
  · exact kwdstaticRange_984.get (by omega) (by omega)
  exact kwdstaticRange_1014.get (by omega) (by omega)

end
end LeanVM.Guest
