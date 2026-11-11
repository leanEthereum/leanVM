/-
  LeanVM.Guest.Memory.GuestCntVK.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVK.Part00
public import LeanVM.Guest.Memory.GuestCntVK.Part01
public import LeanVM.Guest.Memory.GuestCntVK.Part02
public import LeanVM.Guest.Memory.GuestCntVK.Part03
public import LeanVM.Guest.Memory.GuestCntVK.Part04
public import LeanVM.Guest.Memory.GuestCntVK.Part05
public import LeanVM.Guest.Memory.GuestCntVK.Part06
public import LeanVM.Guest.Memory.GuestCntVK.Part07
public import LeanVM.Guest.Memory.GuestCntVK.Part08
public import LeanVM.Guest.Memory.GuestCntVK.Part09
public import LeanVM.Guest.Memory.GuestCntVK.Part10
public import LeanVM.Guest.Memory.GuestCntVK.Part11
public import LeanVM.Guest.Memory.GuestCntVK.Part12
public import LeanVM.Guest.Memory.GuestCntVK.Part13
public import LeanVM.Guest.Memory.GuestCntVK.Part14
public import LeanVM.Guest.Memory.GuestCntVK.Part15

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkchkIdx_319 : kvkchkIdx 319 = true := by
  have hb : blockB (kvklookJ 319) (kvkomLookJ 319) false [] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨8268, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [← blockR_eq (Data.core319.body.drop 0), kvksplit_319_0]
  exact kvkchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_320 : kvkchkIdx 320 = true := by
  have hb : blockB (kvklookJ 320) (kvkomLookJ 320) false [] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨8398, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [← blockR_eq (Data.core320.body.drop 0), kvksplit_320_0]
  exact kvkchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_321 : kvkchkIdx 321 = true := by
  have hb : blockB (kvklookJ 321) (kvkomLookJ 321) false [] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨8746, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [← blockR_eq (Data.core321.body.drop 0), kvksplit_321_0]
  exact kvkchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_322 : kvkchkIdx 322 = true := by
  have hb : blockB (kvklookJ 322) (kvkomLookJ 322) false [] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨10591, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [← blockR_eq (Data.core322.body.drop 0), kvksplit_322_0]
  exact kvkchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvkchkIdx_all : ∀ j < 1752, kvkchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 319
  · subst h1000; exact kvkchkIdx_319
  by_cases h1001 : j = 320
  · subst h1001; exact kvkchkIdx_320
  by_cases h1002 : j = 321
  · subst h1002; exact kvkchkIdx_321
  by_cases h1003 : j = 322
  · subst h1003; exact kvkchkIdx_322
  by_cases h0 : j < 11
  · exact kvkstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvkstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvkstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvkstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvkstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvkstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvkstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvkstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvkstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvkstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvkstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 311
  · exact kvkstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 312
  · exact kvkstaticRange_311.get (by omega) (by omega)
  by_cases h13 : j < 313
  · exact kvkstaticRange_312.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kvkstaticRange_313.get (by omega) (by omega)
  by_cases h15 : j < 315
  · exact kvkstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 316
  · exact kvkstaticRange_315.get (by omega) (by omega)
  by_cases h17 : j < 317
  · exact kvkstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 318
  · exact kvkstaticRange_317.get (by omega) (by omega)
  by_cases h19 : j < 319
  · exact kvkstaticRange_318.get (by omega) (by omega)
  by_cases h20 : j < 344
  · exact kvkstaticRange_323.get (by omega) (by omega)
  by_cases h21 : j < 366
  · exact kvkstaticRange_344.get (by omega) (by omega)
  by_cases h22 : j < 389
  · exact kvkstaticRange_366.get (by omega) (by omega)
  by_cases h23 : j < 403
  · exact kvkstaticRange_389.get (by omega) (by omega)
  by_cases h24 : j < 433
  · exact kvkstaticRange_403.get (by omega) (by omega)
  by_cases h25 : j < 456
  · exact kvkstaticRange_433.get (by omega) (by omega)
  by_cases h26 : j < 478
  · exact kvkstaticRange_456.get (by omega) (by omega)
  by_cases h27 : j < 500
  · exact kvkstaticRange_478.get (by omega) (by omega)
  by_cases h28 : j < 522
  · exact kvkstaticRange_500.get (by omega) (by omega)
  by_cases h29 : j < 544
  · exact kvkstaticRange_522.get (by omega) (by omega)
  by_cases h30 : j < 566
  · exact kvkstaticRange_544.get (by omega) (by omega)
  by_cases h31 : j < 588
  · exact kvkstaticRange_566.get (by omega) (by omega)
  by_cases h32 : j < 610
  · exact kvkstaticRange_588.get (by omega) (by omega)
  by_cases h33 : j < 632
  · exact kvkstaticRange_610.get (by omega) (by omega)
  by_cases h34 : j < 653
  · exact kvkstaticRange_632.get (by omega) (by omega)
  by_cases h35 : j < 675
  · exact kvkstaticRange_653.get (by omega) (by omega)
  by_cases h36 : j < 696
  · exact kvkstaticRange_675.get (by omega) (by omega)
  by_cases h37 : j < 718
  · exact kvkstaticRange_696.get (by omega) (by omega)
  by_cases h38 : j < 739
  · exact kvkstaticRange_718.get (by omega) (by omega)
  by_cases h39 : j < 761
  · exact kvkstaticRange_739.get (by omega) (by omega)
  by_cases h40 : j < 782
  · exact kvkstaticRange_761.get (by omega) (by omega)
  by_cases h41 : j < 804
  · exact kvkstaticRange_782.get (by omega) (by omega)
  by_cases h42 : j < 825
  · exact kvkstaticRange_804.get (by omega) (by omega)
  by_cases h43 : j < 847
  · exact kvkstaticRange_825.get (by omega) (by omega)
  by_cases h44 : j < 868
  · exact kvkstaticRange_847.get (by omega) (by omega)
  by_cases h45 : j < 890
  · exact kvkstaticRange_868.get (by omega) (by omega)
  by_cases h46 : j < 911
  · exact kvkstaticRange_890.get (by omega) (by omega)
  by_cases h47 : j < 932
  · exact kvkstaticRange_911.get (by omega) (by omega)
  by_cases h48 : j < 953
  · exact kvkstaticRange_932.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvkstaticRange_953.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvkstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1016
  · exact kvkstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1039
  · exact kvkstaticRange_1016.get (by omega) (by omega)
  by_cases h53 : j < 1063
  · exact kvkstaticRange_1039.get (by omega) (by omega)
  by_cases h54 : j < 1086
  · exact kvkstaticRange_1063.get (by omega) (by omega)
  by_cases h55 : j < 1106
  · exact kvkstaticRange_1086.get (by omega) (by omega)
  by_cases h56 : j < 1127
  · exact kvkstaticRange_1106.get (by omega) (by omega)
  by_cases h57 : j < 1148
  · exact kvkstaticRange_1127.get (by omega) (by omega)
  by_cases h58 : j < 1169
  · exact kvkstaticRange_1148.get (by omega) (by omega)
  by_cases h59 : j < 1190
  · exact kvkstaticRange_1169.get (by omega) (by omega)
  by_cases h60 : j < 1211
  · exact kvkstaticRange_1190.get (by omega) (by omega)
  by_cases h61 : j < 1232
  · exact kvkstaticRange_1211.get (by omega) (by omega)
  by_cases h62 : j < 1254
  · exact kvkstaticRange_1232.get (by omega) (by omega)
  by_cases h63 : j < 1275
  · exact kvkstaticRange_1254.get (by omega) (by omega)
  by_cases h64 : j < 1296
  · exact kvkstaticRange_1275.get (by omega) (by omega)
  by_cases h65 : j < 1315
  · exact kvkstaticRange_1296.get (by omega) (by omega)
  by_cases h66 : j < 1336
  · exact kvkstaticRange_1315.get (by omega) (by omega)
  by_cases h67 : j < 1357
  · exact kvkstaticRange_1336.get (by omega) (by omega)
  by_cases h68 : j < 1378
  · exact kvkstaticRange_1357.get (by omega) (by omega)
  by_cases h69 : j < 1399
  · exact kvkstaticRange_1378.get (by omega) (by omega)
  by_cases h70 : j < 1420
  · exact kvkstaticRange_1399.get (by omega) (by omega)
  by_cases h71 : j < 1441
  · exact kvkstaticRange_1420.get (by omega) (by omega)
  by_cases h72 : j < 1461
  · exact kvkstaticRange_1441.get (by omega) (by omega)
  by_cases h73 : j < 1482
  · exact kvkstaticRange_1461.get (by omega) (by omega)
  by_cases h74 : j < 1503
  · exact kvkstaticRange_1482.get (by omega) (by omega)
  by_cases h75 : j < 1524
  · exact kvkstaticRange_1503.get (by omega) (by omega)
  by_cases h76 : j < 1545
  · exact kvkstaticRange_1524.get (by omega) (by omega)
  by_cases h77 : j < 1566
  · exact kvkstaticRange_1545.get (by omega) (by omega)
  by_cases h78 : j < 1587
  · exact kvkstaticRange_1566.get (by omega) (by omega)
  by_cases h79 : j < 1607
  · exact kvkstaticRange_1587.get (by omega) (by omega)
  by_cases h80 : j < 1628
  · exact kvkstaticRange_1607.get (by omega) (by omega)
  by_cases h81 : j < 1645
  · exact kvkstaticRange_1628.get (by omega) (by omega)
  by_cases h82 : j < 1661
  · exact kvkstaticRange_1645.get (by omega) (by omega)
  by_cases h83 : j < 1674
  · exact kvkstaticRange_1661.get (by omega) (by omega)
  by_cases h84 : j < 1687
  · exact kvkstaticRange_1674.get (by omega) (by omega)
  by_cases h85 : j < 1700
  · exact kvkstaticRange_1687.get (by omega) (by omega)
  by_cases h86 : j < 1712
  · exact kvkstaticRange_1700.get (by omega) (by omega)
  by_cases h87 : j < 1724
  · exact kvkstaticRange_1712.get (by omega) (by omega)
  by_cases h88 : j < 1733
  · exact kvkstaticRange_1724.get (by omega) (by omega)
  by_cases h89 : j < 1744
  · exact kvkstaticRange_1733.get (by omega) (by omega)
  exact kvkstaticRange_1744.get (by omega) (by omega)

end
end LeanVM.Guest
