/-
  LeanVM.Guest.Memory.GuestWords.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestWords.Part00
public import LeanVM.Guest.Memory.GuestWords.Part01
public import LeanVM.Guest.Memory.GuestWords.Part02
public import LeanVM.Guest.Memory.GuestWords.Part03
public import LeanVM.Guest.Memory.GuestWords.Part04
public import LeanVM.Guest.Memory.GuestWords.Part05
public import LeanVM.Guest.Memory.GuestWords.Part06
public import LeanVM.Guest.Memory.GuestWords.Part07
public import LeanVM.Guest.Memory.GuestWords.Part08
public import LeanVM.Guest.Memory.GuestWords.Part09
public import LeanVM.Guest.Memory.GuestWords.Part10
public import LeanVM.Guest.Memory.GuestWords.Part11
public import LeanVM.Guest.Memory.GuestWords.Part12
public import LeanVM.Guest.Memory.GuestWords.Part13
public import LeanVM.Guest.Memory.GuestWords.Part14
public import LeanVM.Guest.Memory.GuestWords.Part15
public import LeanVM.Guest.Memory.GuestWords.Part16
public import LeanVM.Guest.Memory.GuestWords.Part17
public import LeanVM.Guest.Memory.GuestWords.Part18

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wchkIdx_19 : wchkIdx 19 = true := by
  have hb : blockB (wlookJ 19) (womLookJ 19) true [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 wsplit_19_0.1 rfl wsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), wsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), wsplit_19_96]
    rfl
  exact wchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_315 : wchkIdx 315 = true := by
  have hb : blockB (wlookJ 315) (womLookJ 315) true [(.n 13, 8), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1392), (.n 25, 1392), (.n 27, 128), (.n 157, 144), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1644, 144), (.n 1646, 6), (.n 2188, 7)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨259750, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 1627 1627 wsplit_315_0.1 rfl wsplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 1627), wsplit_315_0.2.1]
    rw [← blockR_eq (Data.core315.body.drop 1627), wsplit_315_1627]
    rfl
  exact wchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_316 : wchkIdx 316 = true := by
  have hb : blockB (wlookJ 316) (womLookJ 316) true [(.n 13, 16), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1392), (.n 25, 1392), (.n 27, 128), (.n 157, 144), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1656, 144), (.n 1658, 6), (.n 2242, 7)] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨264511, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [blockB_dropE _ _ _ 0 1627 1627 wsplit_316_0.1 rfl wsplit_316_0.2.2,
      ← blockR_eq ((Data.core316.body.drop 0).take 1627), wsplit_316_0.2.1]
    rw [← blockR_eq (Data.core316.body.drop 1627), wsplit_316_1627]
    rfl
  exact wchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem wchkIdx_all : ∀ j < 1535, wchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact wchkIdx_19
  by_cases h1001 : j = 315
  · subst h1001; exact wchkIdx_315
  by_cases h1002 : j = 316
  · subst h1002; exact wchkIdx_316
  by_cases h0 : j < 11
  · exact wstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact wstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact wstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact wstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact wstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 65
  · exact wstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 86
  · exact wstaticRange_65.get (by omega) (by omega)
  by_cases h7 : j < 110
  · exact wstaticRange_86.get (by omega) (by omega)
  by_cases h8 : j < 135
  · exact wstaticRange_110.get (by omega) (by omega)
  by_cases h9 : j < 162
  · exact wstaticRange_135.get (by omega) (by omega)
  by_cases h10 : j < 187
  · exact wstaticRange_162.get (by omega) (by omega)
  by_cases h11 : j < 212
  · exact wstaticRange_187.get (by omega) (by omega)
  by_cases h12 : j < 238
  · exact wstaticRange_212.get (by omega) (by omega)
  by_cases h13 : j < 265
  · exact wstaticRange_238.get (by omega) (by omega)
  by_cases h14 : j < 285
  · exact wstaticRange_265.get (by omega) (by omega)
  by_cases h15 : j < 306
  · exact wstaticRange_285.get (by omega) (by omega)
  by_cases h16 : j < 307
  · exact wstaticRange_306.get (by omega) (by omega)
  by_cases h17 : j < 308
  · exact wstaticRange_307.get (by omega) (by omega)
  by_cases h18 : j < 309
  · exact wstaticRange_308.get (by omega) (by omega)
  by_cases h19 : j < 310
  · exact wstaticRange_309.get (by omega) (by omega)
  by_cases h20 : j < 311
  · exact wstaticRange_310.get (by omega) (by omega)
  by_cases h21 : j < 312
  · exact wstaticRange_311.get (by omega) (by omega)
  by_cases h22 : j < 313
  · exact wstaticRange_312.get (by omega) (by omega)
  by_cases h23 : j < 314
  · exact wstaticRange_313.get (by omega) (by omega)
  by_cases h24 : j < 315
  · exact wstaticRange_314.get (by omega) (by omega)
  by_cases h25 : j < 338
  · exact wstaticRange_317.get (by omega) (by omega)
  by_cases h26 : j < 360
  · exact wstaticRange_338.get (by omega) (by omega)
  by_cases h27 : j < 383
  · exact wstaticRange_360.get (by omega) (by omega)
  by_cases h28 : j < 397
  · exact wstaticRange_383.get (by omega) (by omega)
  by_cases h29 : j < 417
  · exact wstaticRange_397.get (by omega) (by omega)
  by_cases h30 : j < 440
  · exact wstaticRange_417.get (by omega) (by omega)
  by_cases h31 : j < 462
  · exact wstaticRange_440.get (by omega) (by omega)
  by_cases h32 : j < 484
  · exact wstaticRange_462.get (by omega) (by omega)
  by_cases h33 : j < 506
  · exact wstaticRange_484.get (by omega) (by omega)
  by_cases h34 : j < 528
  · exact wstaticRange_506.get (by omega) (by omega)
  by_cases h35 : j < 550
  · exact wstaticRange_528.get (by omega) (by omega)
  by_cases h36 : j < 572
  · exact wstaticRange_550.get (by omega) (by omega)
  by_cases h37 : j < 594
  · exact wstaticRange_572.get (by omega) (by omega)
  by_cases h38 : j < 616
  · exact wstaticRange_594.get (by omega) (by omega)
  by_cases h39 : j < 638
  · exact wstaticRange_616.get (by omega) (by omega)
  by_cases h40 : j < 660
  · exact wstaticRange_638.get (by omega) (by omega)
  by_cases h41 : j < 682
  · exact wstaticRange_660.get (by omega) (by omega)
  by_cases h42 : j < 704
  · exact wstaticRange_682.get (by omega) (by omega)
  by_cases h43 : j < 725
  · exact wstaticRange_704.get (by omega) (by omega)
  by_cases h44 : j < 747
  · exact wstaticRange_725.get (by omega) (by omega)
  by_cases h45 : j < 768
  · exact wstaticRange_747.get (by omega) (by omega)
  by_cases h46 : j < 790
  · exact wstaticRange_768.get (by omega) (by omega)
  by_cases h47 : j < 811
  · exact wstaticRange_790.get (by omega) (by omega)
  by_cases h48 : j < 833
  · exact wstaticRange_811.get (by omega) (by omega)
  by_cases h49 : j < 854
  · exact wstaticRange_833.get (by omega) (by omega)
  by_cases h50 : j < 875
  · exact wstaticRange_854.get (by omega) (by omega)
  by_cases h51 : j < 896
  · exact wstaticRange_875.get (by omega) (by omega)
  by_cases h52 : j < 917
  · exact wstaticRange_896.get (by omega) (by omega)
  by_cases h53 : j < 941
  · exact wstaticRange_917.get (by omega) (by omega)
  by_cases h54 : j < 965
  · exact wstaticRange_941.get (by omega) (by omega)
  by_cases h55 : j < 986
  · exact wstaticRange_965.get (by omega) (by omega)
  by_cases h56 : j < 1007
  · exact wstaticRange_986.get (by omega) (by omega)
  by_cases h57 : j < 1029
  · exact wstaticRange_1007.get (by omega) (by omega)
  by_cases h58 : j < 1049
  · exact wstaticRange_1029.get (by omega) (by omega)
  by_cases h59 : j < 1071
  · exact wstaticRange_1049.get (by omega) (by omega)
  by_cases h60 : j < 1092
  · exact wstaticRange_1071.get (by omega) (by omega)
  by_cases h61 : j < 1113
  · exact wstaticRange_1092.get (by omega) (by omega)
  by_cases h62 : j < 1134
  · exact wstaticRange_1113.get (by omega) (by omega)
  by_cases h63 : j < 1155
  · exact wstaticRange_1134.get (by omega) (by omega)
  by_cases h64 : j < 1176
  · exact wstaticRange_1155.get (by omega) (by omega)
  by_cases h65 : j < 1195
  · exact wstaticRange_1176.get (by omega) (by omega)
  by_cases h66 : j < 1216
  · exact wstaticRange_1195.get (by omega) (by omega)
  by_cases h67 : j < 1237
  · exact wstaticRange_1216.get (by omega) (by omega)
  by_cases h68 : j < 1258
  · exact wstaticRange_1237.get (by omega) (by omega)
  by_cases h69 : j < 1279
  · exact wstaticRange_1258.get (by omega) (by omega)
  by_cases h70 : j < 1300
  · exact wstaticRange_1279.get (by omega) (by omega)
  by_cases h71 : j < 1321
  · exact wstaticRange_1300.get (by omega) (by omega)
  by_cases h72 : j < 1343
  · exact wstaticRange_1321.get (by omega) (by omega)
  by_cases h73 : j < 1363
  · exact wstaticRange_1343.get (by omega) (by omega)
  by_cases h74 : j < 1384
  · exact wstaticRange_1363.get (by omega) (by omega)
  by_cases h75 : j < 1405
  · exact wstaticRange_1384.get (by omega) (by omega)
  by_cases h76 : j < 1426
  · exact wstaticRange_1405.get (by omega) (by omega)
  by_cases h77 : j < 1442
  · exact wstaticRange_1426.get (by omega) (by omega)
  by_cases h78 : j < 1458
  · exact wstaticRange_1442.get (by omega) (by omega)
  by_cases h79 : j < 1471
  · exact wstaticRange_1458.get (by omega) (by omega)
  by_cases h80 : j < 1485
  · exact wstaticRange_1471.get (by omega) (by omega)
  by_cases h81 : j < 1498
  · exact wstaticRange_1485.get (by omega) (by omega)
  by_cases h82 : j < 1510
  · exact wstaticRange_1498.get (by omega) (by omega)
  by_cases h83 : j < 1521
  · exact wstaticRange_1510.get (by omega) (by omega)
  by_cases h84 : j < 1531
  · exact wstaticRange_1521.get (by omega) (by omega)
  exact wstaticRange_1531.get (by omega) (by omega)

end
end LeanVM.Guest
