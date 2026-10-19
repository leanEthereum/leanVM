/-
  LeanVM.Guest.Memory.GuestStatic.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestStatic.Part00
public import LeanVM.Guest.Memory.GuestStatic.Part01
public import LeanVM.Guest.Memory.GuestStatic.Part02
public import LeanVM.Guest.Memory.GuestStatic.Part03
public import LeanVM.Guest.Memory.GuestStatic.Part04
public import LeanVM.Guest.Memory.GuestStatic.Part05
public import LeanVM.Guest.Memory.GuestStatic.Part06
public import LeanVM.Guest.Memory.GuestStatic.Part07
public import LeanVM.Guest.Memory.GuestStatic.Part08
public import LeanVM.Guest.Memory.GuestStatic.Part09
public import LeanVM.Guest.Memory.GuestStatic.Part10
public import LeanVM.Guest.Memory.GuestStatic.Part11
public import LeanVM.Guest.Memory.GuestStatic.Part12
public import LeanVM.Guest.Memory.GuestStatic.Part13
public import LeanVM.Guest.Memory.GuestStatic.Part14
public import LeanVM.Guest.Memory.GuestStatic.Part15
public import LeanVM.Guest.Memory.GuestStatic.Part16
public import LeanVM.Guest.Memory.GuestStatic.Part17
public import LeanVM.Guest.Memory.GuestStatic.Part18
public import LeanVM.Guest.Memory.GuestStatic.Part19
public import LeanVM.Guest.Memory.GuestStatic.Part20
public import LeanVM.Guest.Memory.GuestStatic.Part21
public import LeanVM.Guest.Memory.GuestStatic.Part22
public import LeanVM.Guest.Memory.GuestStatic.Part23
public import LeanVM.Guest.Memory.GuestStatic.Part24
public import LeanVM.Guest.Memory.GuestStatic.Part25
public import LeanVM.Guest.Memory.GuestStatic.Part26
public import LeanVM.Guest.Memory.GuestStatic.Part27
public import LeanVM.Guest.Memory.GuestStatic.Part28
public import LeanVM.Guest.Memory.GuestStatic.Part29
public import LeanVM.Guest.Memory.GuestStatic.Part30
public import LeanVM.Guest.Memory.GuestStatic.Part31
public import LeanVM.Guest.Memory.GuestStatic.Part32
public import LeanVM.Guest.Memory.GuestStatic.Part33
public import LeanVM.Guest.Memory.GuestStatic.Part34
public import LeanVM.Guest.Memory.GuestStatic.Part35

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem chkIdx_16 : chkIdx 16 = true := by
  have hb : blockB (lookJ 16) (omLookJ 16) false [] Data.core16.params Data.core16.name ([], []) Data.core16.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core16.body)]
    rw [blockB_drop' _ _ 0 506 506 split_16_0.1 rfl, ← blockR_eq ((Data.core16.body.drop 0).take 506), split_16_0.2]
    rw [← blockR_eq (Data.core16.body.drop 506), split_16_506]
    rfl
  exact chkIdx_of_split (fn := Data.core16) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem chkIdx_17 : chkIdx 17 = true := by
  have hb : blockB (lookJ 17) (omLookJ 17) false [] Data.core17.params Data.core17.name ([], []) Data.core17.body = some (⟨464, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core17.body)]
    rw [blockB_drop' _ _ 0 232 232 split_17_0.1 rfl, ← blockR_eq ((Data.core17.body.drop 0).take 232), split_17_0.2]
    rw [blockB_drop' _ _ 232 28 260 split_17_232.1 rfl, ← blockR_eq ((Data.core17.body.drop 232).take 28), split_17_232.2]
    rw [blockB_drop' _ _ 260 12 272 split_17_260.1 rfl, ← blockR_eq ((Data.core17.body.drop 260).take 12), split_17_260.2]
    rw [blockB_drop' _ _ 272 28 300 split_17_272.1 rfl, ← blockR_eq ((Data.core17.body.drop 272).take 28), split_17_272.2]
    rw [blockB_drop' _ _ 300 12 312 split_17_300.1 rfl, ← blockR_eq ((Data.core17.body.drop 300).take 12), split_17_300.2]
    rw [blockB_drop' _ _ 312 28 340 split_17_312.1 rfl, ← blockR_eq ((Data.core17.body.drop 312).take 28), split_17_312.2]
    rw [blockB_drop' _ _ 340 12 352 split_17_340.1 rfl, ← blockR_eq ((Data.core17.body.drop 340).take 12), split_17_340.2]
    rw [blockB_drop' _ _ 352 28 380 split_17_352.1 rfl, ← blockR_eq ((Data.core17.body.drop 352).take 28), split_17_352.2]
    rw [blockB_drop' _ _ 380 12 392 split_17_380.1 rfl, ← blockR_eq ((Data.core17.body.drop 380).take 12), split_17_380.2]
    rw [blockB_drop' _ _ 392 28 420 split_17_392.1 rfl, ← blockR_eq ((Data.core17.body.drop 392).take 28), split_17_392.2]
    rw [blockB_drop' _ _ 420 12 432 split_17_420.1 rfl, ← blockR_eq ((Data.core17.body.drop 420).take 12), split_17_420.2]
    rw [blockB_drop' _ _ 432 28 460 split_17_432.1 rfl, ← blockR_eq ((Data.core17.body.drop 432).take 28), split_17_432.2]
    rw [blockB_drop' _ _ 460 12 472 split_17_460.1 rfl, ← blockR_eq ((Data.core17.body.drop 460).take 12), split_17_460.2]
    rw [blockB_drop' _ _ 472 28 500 split_17_472.1 rfl, ← blockR_eq ((Data.core17.body.drop 472).take 28), split_17_472.2]
    rw [blockB_drop' _ _ 500 12 512 split_17_500.1 rfl, ← blockR_eq ((Data.core17.body.drop 500).take 12), split_17_500.2]
    rw [blockB_drop' _ _ 512 237 749 split_17_512.1 rfl, ← blockR_eq ((Data.core17.body.drop 512).take 237), split_17_512.2]
    rw [← blockR_eq (Data.core17.body.drop 749), split_17_749]
    rfl
  exact chkIdx_of_split (fn := Data.core17) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem chkIdx_all : ∀ j < 1043, chkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 16
  · subst h1000; exact chkIdx_16
  by_cases h1001 : j = 17
  · subst h1001; exact chkIdx_17
  by_cases h0 : j < 11
  · exact staticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 12
  · exact staticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 14
  · exact staticRange_12.get (by omega) (by omega)
  by_cases h3 : j < 15
  · exact staticRange_14.get (by omega) (by omega)
  by_cases h4 : j < 16
  · exact staticRange_15.get (by omega) (by omega)
  by_cases h5 : j < 46
  · exact staticRange_18.get (by omega) (by omega)
  by_cases h6 : j < 76
  · exact staticRange_46.get (by omega) (by omega)
  by_cases h7 : j < 106
  · exact staticRange_76.get (by omega) (by omega)
  by_cases h8 : j < 136
  · exact staticRange_106.get (by omega) (by omega)
  by_cases h9 : j < 166
  · exact staticRange_136.get (by omega) (by omega)
  by_cases h10 : j < 180
  · exact staticRange_166.get (by omega) (by omega)
  by_cases hs180 : j < 181
  · exact staticRange_180.get (by omega) (by omega)
  by_cases hs181 : j < 182
  · exact staticRange_181.get (by omega) (by omega)
  by_cases hs182 : j < 183
  · exact staticRange_182.get (by omega) (by omega)
  by_cases hs183 : j < 184
  · exact staticRange_183.get (by omega) (by omega)
  by_cases hs184 : j < 185
  · exact staticRange_184.get (by omega) (by omega)
  by_cases hs185 : j < 186
  · exact staticRange_185.get (by omega) (by omega)
  by_cases hs186 : j < 187
  · exact staticRange_186.get (by omega) (by omega)
  by_cases hs187 : j < 188
  · exact staticRange_187.get (by omega) (by omega)
  by_cases hs188 : j < 189
  · exact staticRange_188.get (by omega) (by omega)
  by_cases hs189 : j < 190
  · exact staticRange_189.get (by omega) (by omega)
  by_cases hs190 : j < 191
  · exact staticRange_190.get (by omega) (by omega)
  by_cases hs191 : j < 192
  · exact staticRange_191.get (by omega) (by omega)
  by_cases hs192 : j < 193
  · exact staticRange_192.get (by omega) (by omega)
  by_cases hs193 : j < 194
  · exact staticRange_193.get (by omega) (by omega)
  by_cases hs194 : j < 195
  · exact staticRange_194.get (by omega) (by omega)
  by_cases hs195 : j < 196
  · exact staticRange_195.get (by omega) (by omega)
  by_cases hs196 : j < 197
  · exact staticRange_196.get (by omega) (by omega)
  by_cases hs197 : j < 198
  · exact staticRange_197.get (by omega) (by omega)
  by_cases hs198 : j < 199
  · exact staticRange_198.get (by omega) (by omega)
  by_cases hs199 : j < 200
  · exact staticRange_199.get (by omega) (by omega)
  by_cases hs200 : j < 201
  · exact staticRange_200.get (by omega) (by omega)
  by_cases hs201 : j < 202
  · exact staticRange_201.get (by omega) (by omega)
  by_cases hs202 : j < 203
  · exact staticRange_202.get (by omega) (by omega)
  by_cases hs203 : j < 204
  · exact staticRange_203.get (by omega) (by omega)
  by_cases h19 : j < 234
  · exact staticRange_204.get (by omega) (by omega)
  by_cases h20 : j < 264
  · exact staticRange_234.get (by omega) (by omega)
  by_cases h21 : j < 294
  · exact staticRange_264.get (by omega) (by omega)
  by_cases h22 : j < 324
  · exact staticRange_294.get (by omega) (by omega)
  by_cases h23 : j < 354
  · exact staticRange_324.get (by omega) (by omega)
  by_cases h24 : j < 384
  · exact staticRange_354.get (by omega) (by omega)
  by_cases h25 : j < 414
  · exact staticRange_384.get (by omega) (by omega)
  by_cases h26 : j < 444
  · exact staticRange_414.get (by omega) (by omega)
  by_cases h27 : j < 474
  · exact staticRange_444.get (by omega) (by omega)
  by_cases h28 : j < 504
  · exact staticRange_474.get (by omega) (by omega)
  by_cases h29 : j < 534
  · exact staticRange_504.get (by omega) (by omega)
  by_cases h30 : j < 564
  · exact staticRange_534.get (by omega) (by omega)
  by_cases h31 : j < 594
  · exact staticRange_564.get (by omega) (by omega)
  by_cases h32 : j < 624
  · exact staticRange_594.get (by omega) (by omega)
  by_cases h33 : j < 654
  · exact staticRange_624.get (by omega) (by omega)
  by_cases h34 : j < 684
  · exact staticRange_654.get (by omega) (by omega)
  by_cases h35 : j < 714
  · exact staticRange_684.get (by omega) (by omega)
  by_cases h36 : j < 744
  · exact staticRange_714.get (by omega) (by omega)
  by_cases h37 : j < 774
  · exact staticRange_744.get (by omega) (by omega)
  by_cases h38 : j < 804
  · exact staticRange_774.get (by omega) (by omega)
  by_cases h39 : j < 834
  · exact staticRange_804.get (by omega) (by omega)
  by_cases h40 : j < 864
  · exact staticRange_834.get (by omega) (by omega)
  by_cases h41 : j < 894
  · exact staticRange_864.get (by omega) (by omega)
  by_cases h42 : j < 924
  · exact staticRange_894.get (by omega) (by omega)
  by_cases h43 : j < 954
  · exact staticRange_924.get (by omega) (by omega)
  by_cases h44 : j < 984
  · exact staticRange_954.get (by omega) (by omega)
  by_cases h45 : j < 994
  · exact staticRange_984.get (by omega) (by omega)
  by_cases h46 : j < 1004
  · exact staticRange_994.get (by omega) (by omega)
  by_cases h47 : j < 1014
  · exact staticRange_1004.get (by omega) (by omega)
  by_cases h48 : j < 1024
  · exact staticRange_1014.get (by omega) (by omega)
  by_cases h49 : j < 1034
  · exact staticRange_1024.get (by omega) (by omega)
  exact staticRange_1034.get (by omega) (by omega)

end
end LeanVM.Guest
