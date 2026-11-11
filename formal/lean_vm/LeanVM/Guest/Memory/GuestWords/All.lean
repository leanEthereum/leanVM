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
theorem wchkIdx_319 : wchkIdx 319 = true := by
  have hb : blockB (wlookJ 319) (womLookJ 319) true [(.n 13, 8), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1392), (.n 25, 1392), (.n 27, 128), (.n 157, 156), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1644, 156), (.n 1646, 6), (.n 2188, 7)] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨259774, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [blockB_dropE _ _ _ 0 1627 1627 wsplit_319_0.1 rfl wsplit_319_0.2.2,
      ← blockR_eq ((Data.core319.body.drop 0).take 1627), wsplit_319_0.2.1]
    rw [← blockR_eq (Data.core319.body.drop 1627), wsplit_319_1627]
    rfl
  exact wchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_320 : wchkIdx 320 = true := by
  have hb : blockB (wlookJ 320) (womLookJ 320) true [(.n 13, 16), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1392), (.n 25, 1392), (.n 27, 128), (.n 157, 156), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1656, 156), (.n 1658, 6), (.n 2242, 7)] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨264535, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [blockB_dropE _ _ _ 0 1627 1627 wsplit_320_0.1 rfl wsplit_320_0.2.2,
      ← blockR_eq ((Data.core320.body.drop 0).take 1627), wsplit_320_0.2.1]
    rw [← blockR_eq (Data.core320.body.drop 1627), wsplit_320_1627]
    rfl
  exact wchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_321 : wchkIdx 321 = true := by
  have hb : blockB (wlookJ 321) (womLookJ 321) true [(.n 13, 32), (.n 15, 12), (.n 17, 26), (.n 19, 6), (.n 21, 6), (.n 23, 1392), (.n 25, 1392), (.n 27, 128), (.n 157, 156), (.n 159, 24), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1405, 64), (.n 1427, 5), (.n 1668, 156), (.n 1670, 6), (.n 2296, 7)] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨269000, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [blockB_dropE _ _ _ 0 1627 1627 wsplit_321_0.1 rfl wsplit_321_0.2.2,
      ← blockR_eq ((Data.core321.body.drop 0).take 1627), wsplit_321_0.2.1]
    rw [← blockR_eq (Data.core321.body.drop 1627), wsplit_321_1627]
    rfl
  exact wchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_322 : wchkIdx 322 = true := by
  have hb : blockB (wlookJ 322) (womLookJ 322) true [(.n 13, 4), (.n 15, 14), (.n 17, 30), (.n 19, 7), (.n 21, 7), (.n 23, 1624), (.n 25, 1624), (.n 27, 128), (.n 157, 182), (.n 159, 28), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1507, 64), (.n 1632, 64), (.n 1654, 5), (.n 1867, 182), (.n 1869, 7), (.n 2550, 8)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨287355, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 1555 1555 wsplit_322_0.1 rfl wsplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 1555), wsplit_322_0.2.1]
    rw [← blockR_eq (Data.core322.body.drop 1555), wsplit_322_1555]
    rfl
  exact wchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem wchkIdx_all : ∀ j < 1752, wchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact wchkIdx_19
  by_cases h1001 : j = 319
  · subst h1001; exact wchkIdx_319
  by_cases h1002 : j = 320
  · subst h1002; exact wchkIdx_320
  by_cases h1003 : j = 321
  · subst h1003; exact wchkIdx_321
  by_cases h1004 : j = 322
  · subst h1004; exact wchkIdx_322
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
  by_cases h25 : j < 344
  · exact wstaticRange_323.get (by omega) (by omega)
  by_cases h26 : j < 366
  · exact wstaticRange_344.get (by omega) (by omega)
  by_cases h27 : j < 389
  · exact wstaticRange_366.get (by omega) (by omega)
  by_cases h28 : j < 403
  · exact wstaticRange_389.get (by omega) (by omega)
  by_cases h29 : j < 423
  · exact wstaticRange_403.get (by omega) (by omega)
  by_cases h30 : j < 446
  · exact wstaticRange_423.get (by omega) (by omega)
  by_cases h31 : j < 468
  · exact wstaticRange_446.get (by omega) (by omega)
  by_cases h32 : j < 490
  · exact wstaticRange_468.get (by omega) (by omega)
  by_cases h33 : j < 512
  · exact wstaticRange_490.get (by omega) (by omega)
  by_cases h34 : j < 534
  · exact wstaticRange_512.get (by omega) (by omega)
  by_cases h35 : j < 556
  · exact wstaticRange_534.get (by omega) (by omega)
  by_cases h36 : j < 578
  · exact wstaticRange_556.get (by omega) (by omega)
  by_cases h37 : j < 600
  · exact wstaticRange_578.get (by omega) (by omega)
  by_cases h38 : j < 622
  · exact wstaticRange_600.get (by omega) (by omega)
  by_cases h39 : j < 644
  · exact wstaticRange_622.get (by omega) (by omega)
  by_cases h40 : j < 666
  · exact wstaticRange_644.get (by omega) (by omega)
  by_cases h41 : j < 688
  · exact wstaticRange_666.get (by omega) (by omega)
  by_cases h42 : j < 710
  · exact wstaticRange_688.get (by omega) (by omega)
  by_cases h43 : j < 731
  · exact wstaticRange_710.get (by omega) (by omega)
  by_cases h44 : j < 753
  · exact wstaticRange_731.get (by omega) (by omega)
  by_cases h45 : j < 774
  · exact wstaticRange_753.get (by omega) (by omega)
  by_cases h46 : j < 796
  · exact wstaticRange_774.get (by omega) (by omega)
  by_cases h47 : j < 817
  · exact wstaticRange_796.get (by omega) (by omega)
  by_cases h48 : j < 839
  · exact wstaticRange_817.get (by omega) (by omega)
  by_cases h49 : j < 860
  · exact wstaticRange_839.get (by omega) (by omega)
  by_cases h50 : j < 881
  · exact wstaticRange_860.get (by omega) (by omega)
  by_cases h51 : j < 902
  · exact wstaticRange_881.get (by omega) (by omega)
  by_cases h52 : j < 923
  · exact wstaticRange_902.get (by omega) (by omega)
  by_cases h53 : j < 945
  · exact wstaticRange_923.get (by omega) (by omega)
  by_cases h54 : j < 966
  · exact wstaticRange_945.get (by omega) (by omega)
  by_cases h55 : j < 988
  · exact wstaticRange_966.get (by omega) (by omega)
  by_cases h56 : j < 1009
  · exact wstaticRange_988.get (by omega) (by omega)
  by_cases h57 : j < 1031
  · exact wstaticRange_1009.get (by omega) (by omega)
  by_cases h58 : j < 1055
  · exact wstaticRange_1031.get (by omega) (by omega)
  by_cases h59 : j < 1079
  · exact wstaticRange_1055.get (by omega) (by omega)
  by_cases h60 : j < 1100
  · exact wstaticRange_1079.get (by omega) (by omega)
  by_cases h61 : j < 1120
  · exact wstaticRange_1100.get (by omega) (by omega)
  by_cases h62 : j < 1142
  · exact wstaticRange_1120.get (by omega) (by omega)
  by_cases h63 : j < 1163
  · exact wstaticRange_1142.get (by omega) (by omega)
  by_cases h64 : j < 1184
  · exact wstaticRange_1163.get (by omega) (by omega)
  by_cases h65 : j < 1205
  · exact wstaticRange_1184.get (by omega) (by omega)
  by_cases h66 : j < 1226
  · exact wstaticRange_1205.get (by omega) (by omega)
  by_cases h67 : j < 1247
  · exact wstaticRange_1226.get (by omega) (by omega)
  by_cases h68 : j < 1268
  · exact wstaticRange_1247.get (by omega) (by omega)
  by_cases h69 : j < 1289
  · exact wstaticRange_1268.get (by omega) (by omega)
  by_cases h70 : j < 1308
  · exact wstaticRange_1289.get (by omega) (by omega)
  by_cases h71 : j < 1329
  · exact wstaticRange_1308.get (by omega) (by omega)
  by_cases h72 : j < 1350
  · exact wstaticRange_1329.get (by omega) (by omega)
  by_cases h73 : j < 1372
  · exact wstaticRange_1350.get (by omega) (by omega)
  by_cases h74 : j < 1393
  · exact wstaticRange_1372.get (by omega) (by omega)
  by_cases h75 : j < 1414
  · exact wstaticRange_1393.get (by omega) (by omega)
  by_cases h76 : j < 1435
  · exact wstaticRange_1414.get (by omega) (by omega)
  by_cases h77 : j < 1456
  · exact wstaticRange_1435.get (by omega) (by omega)
  by_cases h78 : j < 1477
  · exact wstaticRange_1456.get (by omega) (by omega)
  by_cases h79 : j < 1498
  · exact wstaticRange_1477.get (by omega) (by omega)
  by_cases h80 : j < 1518
  · exact wstaticRange_1498.get (by omega) (by omega)
  by_cases h81 : j < 1539
  · exact wstaticRange_1518.get (by omega) (by omega)
  by_cases h82 : j < 1560
  · exact wstaticRange_1539.get (by omega) (by omega)
  by_cases h83 : j < 1581
  · exact wstaticRange_1560.get (by omega) (by omega)
  by_cases h84 : j < 1602
  · exact wstaticRange_1581.get (by omega) (by omega)
  by_cases h85 : j < 1623
  · exact wstaticRange_1602.get (by omega) (by omega)
  by_cases h86 : j < 1643
  · exact wstaticRange_1623.get (by omega) (by omega)
  by_cases h87 : j < 1657
  · exact wstaticRange_1643.get (by omega) (by omega)
  by_cases h88 : j < 1671
  · exact wstaticRange_1657.get (by omega) (by omega)
  by_cases h89 : j < 1685
  · exact wstaticRange_1671.get (by omega) (by omega)
  by_cases h90 : j < 1699
  · exact wstaticRange_1685.get (by omega) (by omega)
  by_cases h91 : j < 1710
  · exact wstaticRange_1699.get (by omega) (by omega)
  by_cases h92 : j < 1722
  · exact wstaticRange_1710.get (by omega) (by omega)
  by_cases h93 : j < 1731
  · exact wstaticRange_1722.get (by omega) (by omega)
  by_cases h94 : j < 1742
  · exact wstaticRange_1731.get (by omega) (by omega)
  exact wstaticRange_1742.get (by omega) (by omega)

end
end LeanVM.Guest
