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

theorem kwxchkIdx_all : ∀ j < 1037, kwxchkIdx j = true := by
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
  by_cases h14 : j < 337
  · exact kwxstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 344
  · exact kwxstaticRange_337.get (by omega) (by omega)
  by_cases h16 : j < 350
  · exact kwxstaticRange_344.get (by omega) (by omega)
  by_cases h17 : j < 357
  · exact kwxstaticRange_350.get (by omega) (by omega)
  by_cases h18 : j < 387
  · exact kwxstaticRange_357.get (by omega) (by omega)
  by_cases h19 : j < 417
  · exact kwxstaticRange_387.get (by omega) (by omega)
  by_cases h20 : j < 447
  · exact kwxstaticRange_417.get (by omega) (by omega)
  by_cases h21 : j < 477
  · exact kwxstaticRange_447.get (by omega) (by omega)
  by_cases h22 : j < 507
  · exact kwxstaticRange_477.get (by omega) (by omega)
  by_cases h23 : j < 537
  · exact kwxstaticRange_507.get (by omega) (by omega)
  by_cases h24 : j < 567
  · exact kwxstaticRange_537.get (by omega) (by omega)
  by_cases h25 : j < 597
  · exact kwxstaticRange_567.get (by omega) (by omega)
  by_cases h26 : j < 627
  · exact kwxstaticRange_597.get (by omega) (by omega)
  by_cases h27 : j < 657
  · exact kwxstaticRange_627.get (by omega) (by omega)
  by_cases h28 : j < 687
  · exact kwxstaticRange_657.get (by omega) (by omega)
  by_cases h29 : j < 717
  · exact kwxstaticRange_687.get (by omega) (by omega)
  by_cases h30 : j < 747
  · exact kwxstaticRange_717.get (by omega) (by omega)
  by_cases h31 : j < 777
  · exact kwxstaticRange_747.get (by omega) (by omega)
  by_cases h32 : j < 807
  · exact kwxstaticRange_777.get (by omega) (by omega)
  by_cases h33 : j < 837
  · exact kwxstaticRange_807.get (by omega) (by omega)
  by_cases h34 : j < 867
  · exact kwxstaticRange_837.get (by omega) (by omega)
  by_cases h35 : j < 897
  · exact kwxstaticRange_867.get (by omega) (by omega)
  by_cases h36 : j < 927
  · exact kwxstaticRange_897.get (by omega) (by omega)
  by_cases h37 : j < 957
  · exact kwxstaticRange_927.get (by omega) (by omega)
  by_cases h38 : j < 987
  · exact kwxstaticRange_957.get (by omega) (by omega)
  by_cases h39 : j < 1017
  · exact kwxstaticRange_987.get (by omega) (by omega)
  exact kwxstaticRange_1017.get (by omega) (by omega)

end
end LeanVM.Guest
