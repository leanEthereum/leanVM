/-
  LeanVM.Guest.Memory.GuestCntVD.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVD.Part00
public import LeanVM.Guest.Memory.GuestCntVD.Part01
public import LeanVM.Guest.Memory.GuestCntVD.Part02
public import LeanVM.Guest.Memory.GuestCntVD.Part03
public import LeanVM.Guest.Memory.GuestCntVD.Part04
public import LeanVM.Guest.Memory.GuestCntVD.Part05
public import LeanVM.Guest.Memory.GuestCntVD.Part06
public import LeanVM.Guest.Memory.GuestCntVD.Part07
public import LeanVM.Guest.Memory.GuestCntVD.Part08
public import LeanVM.Guest.Memory.GuestCntVD.Part09
public import LeanVM.Guest.Memory.GuestCntVD.Part10
public import LeanVM.Guest.Memory.GuestCntVD.Part11
public import LeanVM.Guest.Memory.GuestCntVD.Part12
public import LeanVM.Guest.Memory.GuestCntVD.Part13
public import LeanVM.Guest.Memory.GuestCntVD.Part14
public import LeanVM.Guest.Memory.GuestCntVD.Part15

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdchkIdx_319 : kvdchkIdx 319 = true := by
  have hb : blockB (kvdlookJ 319) (kvdomLookJ 319) false [] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨23860, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [← blockR_eq (Data.core319.body.drop 0), kvdsplit_319_0]
  exact kvdchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_320 : kvdchkIdx 320 = true := by
  have hb : blockB (kvdlookJ 320) (kvdomLookJ 320) false [] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨25077, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [← blockR_eq (Data.core320.body.drop 0), kvdsplit_320_0]
  exact kvdchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_321 : kvdchkIdx 321 = true := by
  have hb : blockB (kvdlookJ 321) (kvdomLookJ 321) false [] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨26985, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [← blockR_eq (Data.core321.body.drop 0), kvdsplit_321_0]
  exact kvdchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_322 : kvdchkIdx 322 = true := by
  have hb : blockB (kvdlookJ 322) (kvdomLookJ 322) false [] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨28229, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [← blockR_eq (Data.core322.body.drop 0), kvdsplit_322_0]
  exact kvdchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvdchkIdx_all : ∀ j < 1752, kvdchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 319
  · subst h1000; exact kvdchkIdx_319
  by_cases h1001 : j = 320
  · subst h1001; exact kvdchkIdx_320
  by_cases h1002 : j = 321
  · subst h1002; exact kvdchkIdx_321
  by_cases h1003 : j = 322
  · subst h1003; exact kvdchkIdx_322
  by_cases h0 : j < 11
  · exact kvdstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvdstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvdstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvdstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvdstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvdstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvdstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvdstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvdstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvdstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvdstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 311
  · exact kvdstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 312
  · exact kvdstaticRange_311.get (by omega) (by omega)
  by_cases h13 : j < 313
  · exact kvdstaticRange_312.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kvdstaticRange_313.get (by omega) (by omega)
  by_cases h15 : j < 315
  · exact kvdstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 316
  · exact kvdstaticRange_315.get (by omega) (by omega)
  by_cases h17 : j < 317
  · exact kvdstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 318
  · exact kvdstaticRange_317.get (by omega) (by omega)
  by_cases h19 : j < 319
  · exact kvdstaticRange_318.get (by omega) (by omega)
  by_cases h20 : j < 344
  · exact kvdstaticRange_323.get (by omega) (by omega)
  by_cases h21 : j < 366
  · exact kvdstaticRange_344.get (by omega) (by omega)
  by_cases h22 : j < 389
  · exact kvdstaticRange_366.get (by omega) (by omega)
  by_cases h23 : j < 403
  · exact kvdstaticRange_389.get (by omega) (by omega)
  by_cases h24 : j < 433
  · exact kvdstaticRange_403.get (by omega) (by omega)
  by_cases h25 : j < 456
  · exact kvdstaticRange_433.get (by omega) (by omega)
  by_cases h26 : j < 478
  · exact kvdstaticRange_456.get (by omega) (by omega)
  by_cases h27 : j < 500
  · exact kvdstaticRange_478.get (by omega) (by omega)
  by_cases h28 : j < 522
  · exact kvdstaticRange_500.get (by omega) (by omega)
  by_cases h29 : j < 544
  · exact kvdstaticRange_522.get (by omega) (by omega)
  by_cases h30 : j < 566
  · exact kvdstaticRange_544.get (by omega) (by omega)
  by_cases h31 : j < 588
  · exact kvdstaticRange_566.get (by omega) (by omega)
  by_cases h32 : j < 610
  · exact kvdstaticRange_588.get (by omega) (by omega)
  by_cases h33 : j < 632
  · exact kvdstaticRange_610.get (by omega) (by omega)
  by_cases h34 : j < 653
  · exact kvdstaticRange_632.get (by omega) (by omega)
  by_cases h35 : j < 675
  · exact kvdstaticRange_653.get (by omega) (by omega)
  by_cases h36 : j < 696
  · exact kvdstaticRange_675.get (by omega) (by omega)
  by_cases h37 : j < 718
  · exact kvdstaticRange_696.get (by omega) (by omega)
  by_cases h38 : j < 739
  · exact kvdstaticRange_718.get (by omega) (by omega)
  by_cases h39 : j < 761
  · exact kvdstaticRange_739.get (by omega) (by omega)
  by_cases h40 : j < 782
  · exact kvdstaticRange_761.get (by omega) (by omega)
  by_cases h41 : j < 804
  · exact kvdstaticRange_782.get (by omega) (by omega)
  by_cases h42 : j < 825
  · exact kvdstaticRange_804.get (by omega) (by omega)
  by_cases h43 : j < 847
  · exact kvdstaticRange_825.get (by omega) (by omega)
  by_cases h44 : j < 868
  · exact kvdstaticRange_847.get (by omega) (by omega)
  by_cases h45 : j < 890
  · exact kvdstaticRange_868.get (by omega) (by omega)
  by_cases h46 : j < 911
  · exact kvdstaticRange_890.get (by omega) (by omega)
  by_cases h47 : j < 932
  · exact kvdstaticRange_911.get (by omega) (by omega)
  by_cases h48 : j < 953
  · exact kvdstaticRange_932.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvdstaticRange_953.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvdstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1016
  · exact kvdstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1039
  · exact kvdstaticRange_1016.get (by omega) (by omega)
  by_cases h53 : j < 1063
  · exact kvdstaticRange_1039.get (by omega) (by omega)
  by_cases h54 : j < 1086
  · exact kvdstaticRange_1063.get (by omega) (by omega)
  by_cases h55 : j < 1106
  · exact kvdstaticRange_1086.get (by omega) (by omega)
  by_cases h56 : j < 1127
  · exact kvdstaticRange_1106.get (by omega) (by omega)
  by_cases h57 : j < 1148
  · exact kvdstaticRange_1127.get (by omega) (by omega)
  by_cases h58 : j < 1169
  · exact kvdstaticRange_1148.get (by omega) (by omega)
  by_cases h59 : j < 1190
  · exact kvdstaticRange_1169.get (by omega) (by omega)
  by_cases h60 : j < 1211
  · exact kvdstaticRange_1190.get (by omega) (by omega)
  by_cases h61 : j < 1232
  · exact kvdstaticRange_1211.get (by omega) (by omega)
  by_cases h62 : j < 1254
  · exact kvdstaticRange_1232.get (by omega) (by omega)
  by_cases h63 : j < 1275
  · exact kvdstaticRange_1254.get (by omega) (by omega)
  by_cases h64 : j < 1296
  · exact kvdstaticRange_1275.get (by omega) (by omega)
  by_cases h65 : j < 1315
  · exact kvdstaticRange_1296.get (by omega) (by omega)
  by_cases h66 : j < 1336
  · exact kvdstaticRange_1315.get (by omega) (by omega)
  by_cases h67 : j < 1357
  · exact kvdstaticRange_1336.get (by omega) (by omega)
  by_cases h68 : j < 1378
  · exact kvdstaticRange_1357.get (by omega) (by omega)
  by_cases h69 : j < 1399
  · exact kvdstaticRange_1378.get (by omega) (by omega)
  by_cases h70 : j < 1420
  · exact kvdstaticRange_1399.get (by omega) (by omega)
  by_cases h71 : j < 1441
  · exact kvdstaticRange_1420.get (by omega) (by omega)
  by_cases h72 : j < 1461
  · exact kvdstaticRange_1441.get (by omega) (by omega)
  by_cases h73 : j < 1482
  · exact kvdstaticRange_1461.get (by omega) (by omega)
  by_cases h74 : j < 1503
  · exact kvdstaticRange_1482.get (by omega) (by omega)
  by_cases h75 : j < 1524
  · exact kvdstaticRange_1503.get (by omega) (by omega)
  by_cases h76 : j < 1545
  · exact kvdstaticRange_1524.get (by omega) (by omega)
  by_cases h77 : j < 1566
  · exact kvdstaticRange_1545.get (by omega) (by omega)
  by_cases h78 : j < 1587
  · exact kvdstaticRange_1566.get (by omega) (by omega)
  by_cases h79 : j < 1607
  · exact kvdstaticRange_1587.get (by omega) (by omega)
  by_cases h80 : j < 1628
  · exact kvdstaticRange_1607.get (by omega) (by omega)
  by_cases h81 : j < 1645
  · exact kvdstaticRange_1628.get (by omega) (by omega)
  by_cases h82 : j < 1661
  · exact kvdstaticRange_1645.get (by omega) (by omega)
  by_cases h83 : j < 1674
  · exact kvdstaticRange_1661.get (by omega) (by omega)
  by_cases h84 : j < 1687
  · exact kvdstaticRange_1674.get (by omega) (by omega)
  by_cases h85 : j < 1700
  · exact kvdstaticRange_1687.get (by omega) (by omega)
  by_cases h86 : j < 1712
  · exact kvdstaticRange_1700.get (by omega) (by omega)
  by_cases h87 : j < 1724
  · exact kvdstaticRange_1712.get (by omega) (by omega)
  by_cases h88 : j < 1733
  · exact kvdstaticRange_1724.get (by omega) (by omega)
  by_cases h89 : j < 1744
  · exact kvdstaticRange_1733.get (by omega) (by omega)
  exact kvdstaticRange_1744.get (by omega) (by omega)

end
end LeanVM.Guest
