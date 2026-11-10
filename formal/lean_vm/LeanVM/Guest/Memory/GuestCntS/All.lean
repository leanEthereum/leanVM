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

theorem kwschkIdx_all : ∀ j < 1055, kwschkIdx j = true := by
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
  by_cases h14 : j < 336
  · exact kwsstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 342
  · exact kwsstaticRange_336.get (by omega) (by omega)
  by_cases h16 : j < 348
  · exact kwsstaticRange_342.get (by omega) (by omega)
  by_cases h17 : j < 354
  · exact kwsstaticRange_348.get (by omega) (by omega)
  by_cases h18 : j < 384
  · exact kwsstaticRange_354.get (by omega) (by omega)
  by_cases h19 : j < 414
  · exact kwsstaticRange_384.get (by omega) (by omega)
  by_cases h20 : j < 444
  · exact kwsstaticRange_414.get (by omega) (by omega)
  by_cases h21 : j < 474
  · exact kwsstaticRange_444.get (by omega) (by omega)
  by_cases h22 : j < 504
  · exact kwsstaticRange_474.get (by omega) (by omega)
  by_cases h23 : j < 534
  · exact kwsstaticRange_504.get (by omega) (by omega)
  by_cases h24 : j < 564
  · exact kwsstaticRange_534.get (by omega) (by omega)
  by_cases h25 : j < 594
  · exact kwsstaticRange_564.get (by omega) (by omega)
  by_cases h26 : j < 624
  · exact kwsstaticRange_594.get (by omega) (by omega)
  by_cases h27 : j < 654
  · exact kwsstaticRange_624.get (by omega) (by omega)
  by_cases h28 : j < 684
  · exact kwsstaticRange_654.get (by omega) (by omega)
  by_cases h29 : j < 714
  · exact kwsstaticRange_684.get (by omega) (by omega)
  by_cases h30 : j < 744
  · exact kwsstaticRange_714.get (by omega) (by omega)
  by_cases h31 : j < 774
  · exact kwsstaticRange_744.get (by omega) (by omega)
  by_cases h32 : j < 804
  · exact kwsstaticRange_774.get (by omega) (by omega)
  by_cases h33 : j < 834
  · exact kwsstaticRange_804.get (by omega) (by omega)
  by_cases h34 : j < 864
  · exact kwsstaticRange_834.get (by omega) (by omega)
  by_cases h35 : j < 894
  · exact kwsstaticRange_864.get (by omega) (by omega)
  by_cases h36 : j < 924
  · exact kwsstaticRange_894.get (by omega) (by omega)
  by_cases h37 : j < 954
  · exact kwsstaticRange_924.get (by omega) (by omega)
  by_cases h38 : j < 984
  · exact kwsstaticRange_954.get (by omega) (by omega)
  by_cases h39 : j < 1014
  · exact kwsstaticRange_984.get (by omega) (by omega)
  by_cases h40 : j < 1044
  · exact kwsstaticRange_1014.get (by omega) (by omega)
  exact kwsstaticRange_1044.get (by omega) (by omega)

end
end LeanVM.Guest
