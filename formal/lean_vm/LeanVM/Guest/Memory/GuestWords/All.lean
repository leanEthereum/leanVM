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
public import LeanVM.Guest.Memory.GuestWords.Part19
public import LeanVM.Guest.Memory.GuestWords.Part20
public import LeanVM.Guest.Memory.GuestWords.Part21
public import LeanVM.Guest.Memory.GuestWords.Part22

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
theorem wchkIdx_320 : wchkIdx 320 = true := by
  have hb : blockB (wlookJ 320) (womLookJ 320) true [(.n 13, 8), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1404), (.n 25, 1404), (.n 27, 128), (.n 157, 156), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1644, 156), (.n 1646, 6), (.n 2188, 7)] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨259798, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [blockB_dropE _ _ _ 0 1627 1627 wsplit_320_0.1 rfl wsplit_320_0.2.2,
      ← blockR_eq ((Data.core320.body.drop 0).take 1627), wsplit_320_0.2.1]
    rw [← blockR_eq (Data.core320.body.drop 1627), wsplit_320_1627]
    rfl
  exact wchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_321 : wchkIdx 321 = true := by
  have hb : blockB (wlookJ 321) (womLookJ 321) true [(.n 13, 16), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1404), (.n 25, 1404), (.n 27, 128), (.n 157, 156), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1656, 156), (.n 1658, 6), (.n 2242, 7)] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨264559, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [blockB_dropE _ _ _ 0 1627 1627 wsplit_321_0.1 rfl wsplit_321_0.2.2,
      ← blockR_eq ((Data.core321.body.drop 0).take 1627), wsplit_321_0.2.1]
    rw [← blockR_eq (Data.core321.body.drop 1627), wsplit_321_1627]
    rfl
  exact wchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_322 : wchkIdx 322 = true := by
  have hb : blockB (wlookJ 322) (womLookJ 322) true [(.n 13, 32), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1404), (.n 25, 1404), (.n 27, 128), (.n 157, 156), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1668, 156), (.n 1670, 6), (.n 2296, 7)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨269024, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 1627 1627 wsplit_322_0.1 rfl wsplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 1627), wsplit_322_0.2.1]
    rw [← blockR_eq (Data.core322.body.drop 1627), wsplit_322_1627]
    rfl
  exact wchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_323 : wchkIdx 323 = true := by
  have hb : blockB (wlookJ 323) (womLookJ 323) true [(.n 13, 4), (.n 15, 14), (.n 17, 30), (.n 19, 7), (.n 21, 7), (.n 23, 1638), (.n 25, 1638), (.n 27, 128), (.n 157, 182), (.n 159, 28), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1507, 64), (.n 1632, 64), (.n 1654, 5), (.n 1867, 182), (.n 1869, 7), (.n 2550, 8)] Data.core323.params Data.core323.name ([], []) Data.core323.body = some (⟨287383, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core323.body)]
    rw [blockB_dropE _ _ _ 0 1555 1555 wsplit_323_0.1 rfl wsplit_323_0.2.2,
      ← blockR_eq ((Data.core323.body.drop 0).take 1555), wsplit_323_0.2.1]
    rw [← blockR_eq (Data.core323.body.drop 1555), wsplit_323_1555]
    rfl
  exact wchkIdx_of_split (fn := Data.core323) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem wchkIdx_all : ∀ j < 1803, wchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact wchkIdx_19
  by_cases h1001 : j = 320
  · subst h1001; exact wchkIdx_320
  by_cases h1002 : j = 321
  · subst h1002; exact wchkIdx_321
  by_cases h1003 : j = 322
  · subst h1003; exact wchkIdx_322
  by_cases h1004 : j = 323
  · subst h1004; exact wchkIdx_323
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
  by_cases h8 : j < 134
  · exact wstaticRange_110.get (by omega) (by omega)
  by_cases h9 : j < 161
  · exact wstaticRange_134.get (by omega) (by omega)
  by_cases h10 : j < 186
  · exact wstaticRange_161.get (by omega) (by omega)
  by_cases h11 : j < 211
  · exact wstaticRange_186.get (by omega) (by omega)
  by_cases h12 : j < 237
  · exact wstaticRange_211.get (by omega) (by omega)
  by_cases h13 : j < 265
  · exact wstaticRange_237.get (by omega) (by omega)
  by_cases h14 : j < 284
  · exact wstaticRange_265.get (by omega) (by omega)
  by_cases h15 : j < 310
  · exact wstaticRange_284.get (by omega) (by omega)
  by_cases h16 : j < 311
  · exact wstaticRange_310.get (by omega) (by omega)
  by_cases h17 : j < 312
  · exact wstaticRange_311.get (by omega) (by omega)
  by_cases h18 : j < 313
  · exact wstaticRange_312.get (by omega) (by omega)
  by_cases h19 : j < 314
  · exact wstaticRange_313.get (by omega) (by omega)
  by_cases h20 : j < 315
  · exact wstaticRange_314.get (by omega) (by omega)
  by_cases h21 : j < 316
  · exact wstaticRange_315.get (by omega) (by omega)
  by_cases h22 : j < 317
  · exact wstaticRange_316.get (by omega) (by omega)
  by_cases h23 : j < 318
  · exact wstaticRange_317.get (by omega) (by omega)
  by_cases h24 : j < 319
  · exact wstaticRange_318.get (by omega) (by omega)
  by_cases h25 : j < 320
  · exact wstaticRange_319.get (by omega) (by omega)
  by_cases h26 : j < 345
  · exact wstaticRange_324.get (by omega) (by omega)
  by_cases h27 : j < 367
  · exact wstaticRange_345.get (by omega) (by omega)
  by_cases h28 : j < 390
  · exact wstaticRange_367.get (by omega) (by omega)
  by_cases h29 : j < 404
  · exact wstaticRange_390.get (by omega) (by omega)
  by_cases h30 : j < 424
  · exact wstaticRange_404.get (by omega) (by omega)
  by_cases h31 : j < 447
  · exact wstaticRange_424.get (by omega) (by omega)
  by_cases h32 : j < 469
  · exact wstaticRange_447.get (by omega) (by omega)
  by_cases h33 : j < 491
  · exact wstaticRange_469.get (by omega) (by omega)
  by_cases h34 : j < 513
  · exact wstaticRange_491.get (by omega) (by omega)
  by_cases h35 : j < 535
  · exact wstaticRange_513.get (by omega) (by omega)
  by_cases h36 : j < 557
  · exact wstaticRange_535.get (by omega) (by omega)
  by_cases h37 : j < 579
  · exact wstaticRange_557.get (by omega) (by omega)
  by_cases h38 : j < 601
  · exact wstaticRange_579.get (by omega) (by omega)
  by_cases h39 : j < 623
  · exact wstaticRange_601.get (by omega) (by omega)
  by_cases h40 : j < 645
  · exact wstaticRange_623.get (by omega) (by omega)
  by_cases h41 : j < 666
  · exact wstaticRange_645.get (by omega) (by omega)
  by_cases h42 : j < 688
  · exact wstaticRange_666.get (by omega) (by omega)
  by_cases h43 : j < 709
  · exact wstaticRange_688.get (by omega) (by omega)
  by_cases h44 : j < 731
  · exact wstaticRange_709.get (by omega) (by omega)
  by_cases h45 : j < 752
  · exact wstaticRange_731.get (by omega) (by omega)
  by_cases h46 : j < 774
  · exact wstaticRange_752.get (by omega) (by omega)
  by_cases h47 : j < 795
  · exact wstaticRange_774.get (by omega) (by omega)
  by_cases h48 : j < 817
  · exact wstaticRange_795.get (by omega) (by omega)
  by_cases h49 : j < 838
  · exact wstaticRange_817.get (by omega) (by omega)
  by_cases h50 : j < 860
  · exact wstaticRange_838.get (by omega) (by omega)
  by_cases h51 : j < 881
  · exact wstaticRange_860.get (by omega) (by omega)
  by_cases h52 : j < 902
  · exact wstaticRange_881.get (by omega) (by omega)
  by_cases h53 : j < 924
  · exact wstaticRange_902.get (by omega) (by omega)
  by_cases h54 : j < 945
  · exact wstaticRange_924.get (by omega) (by omega)
  by_cases h55 : j < 967
  · exact wstaticRange_945.get (by omega) (by omega)
  by_cases h56 : j < 988
  · exact wstaticRange_967.get (by omega) (by omega)
  by_cases h57 : j < 1010
  · exact wstaticRange_988.get (by omega) (by omega)
  by_cases h58 : j < 1031
  · exact wstaticRange_1010.get (by omega) (by omega)
  by_cases h59 : j < 1052
  · exact wstaticRange_1031.get (by omega) (by omega)
  by_cases h60 : j < 1076
  · exact wstaticRange_1052.get (by omega) (by omega)
  by_cases h61 : j < 1100
  · exact wstaticRange_1076.get (by omega) (by omega)
  by_cases h62 : j < 1119
  · exact wstaticRange_1100.get (by omega) (by omega)
  by_cases h63 : j < 1140
  · exact wstaticRange_1119.get (by omega) (by omega)
  by_cases h64 : j < 1161
  · exact wstaticRange_1140.get (by omega) (by omega)
  by_cases h65 : j < 1182
  · exact wstaticRange_1161.get (by omega) (by omega)
  by_cases h66 : j < 1203
  · exact wstaticRange_1182.get (by omega) (by omega)
  by_cases h67 : j < 1225
  · exact wstaticRange_1203.get (by omega) (by omega)
  by_cases h68 : j < 1246
  · exact wstaticRange_1225.get (by omega) (by omega)
  by_cases h69 : j < 1268
  · exact wstaticRange_1246.get (by omega) (by omega)
  by_cases h70 : j < 1289
  · exact wstaticRange_1268.get (by omega) (by omega)
  by_cases h71 : j < 1310
  · exact wstaticRange_1289.get (by omega) (by omega)
  by_cases h72 : j < 1331
  · exact wstaticRange_1310.get (by omega) (by omega)
  by_cases h73 : j < 1352
  · exact wstaticRange_1331.get (by omega) (by omega)
  by_cases h74 : j < 1373
  · exact wstaticRange_1352.get (by omega) (by omega)
  by_cases h75 : j < 1394
  · exact wstaticRange_1373.get (by omega) (by omega)
  by_cases h76 : j < 1415
  · exact wstaticRange_1394.get (by omega) (by omega)
  by_cases h77 : j < 1436
  · exact wstaticRange_1415.get (by omega) (by omega)
  by_cases h78 : j < 1457
  · exact wstaticRange_1436.get (by omega) (by omega)
  by_cases h79 : j < 1478
  · exact wstaticRange_1457.get (by omega) (by omega)
  by_cases h80 : j < 1499
  · exact wstaticRange_1478.get (by omega) (by omega)
  by_cases h81 : j < 1519
  · exact wstaticRange_1499.get (by omega) (by omega)
  by_cases h82 : j < 1540
  · exact wstaticRange_1519.get (by omega) (by omega)
  by_cases h83 : j < 1560
  · exact wstaticRange_1540.get (by omega) (by omega)
  by_cases h84 : j < 1581
  · exact wstaticRange_1560.get (by omega) (by omega)
  by_cases h85 : j < 1602
  · exact wstaticRange_1581.get (by omega) (by omega)
  by_cases h86 : j < 1623
  · exact wstaticRange_1602.get (by omega) (by omega)
  by_cases h87 : j < 1644
  · exact wstaticRange_1623.get (by omega) (by omega)
  by_cases h88 : j < 1665
  · exact wstaticRange_1644.get (by omega) (by omega)
  by_cases h89 : j < 1686
  · exact wstaticRange_1665.get (by omega) (by omega)
  by_cases h90 : j < 1700
  · exact wstaticRange_1686.get (by omega) (by omega)
  by_cases h91 : j < 1714
  · exact wstaticRange_1700.get (by omega) (by omega)
  by_cases h92 : j < 1729
  · exact wstaticRange_1714.get (by omega) (by omega)
  by_cases h93 : j < 1743
  · exact wstaticRange_1729.get (by omega) (by omega)
  by_cases h94 : j < 1755
  · exact wstaticRange_1743.get (by omega) (by omega)
  by_cases h95 : j < 1767
  · exact wstaticRange_1755.get (by omega) (by omega)
  by_cases h96 : j < 1777
  · exact wstaticRange_1767.get (by omega) (by omega)
  by_cases h97 : j < 1788
  · exact wstaticRange_1777.get (by omega) (by omega)
  by_cases h98 : j < 1798
  · exact wstaticRange_1788.get (by omega) (by omega)
  exact wstaticRange_1798.get (by omega) (by omega)

end
end LeanVM.Guest
