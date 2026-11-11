/-
  LeanVM.Guest.Memory.GuestCntVJ.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVJ.Part00
public import LeanVM.Guest.Memory.GuestCntVJ.Part01
public import LeanVM.Guest.Memory.GuestCntVJ.Part02
public import LeanVM.Guest.Memory.GuestCntVJ.Part03
public import LeanVM.Guest.Memory.GuestCntVJ.Part04
public import LeanVM.Guest.Memory.GuestCntVJ.Part05
public import LeanVM.Guest.Memory.GuestCntVJ.Part06
public import LeanVM.Guest.Memory.GuestCntVJ.Part07
public import LeanVM.Guest.Memory.GuestCntVJ.Part08
public import LeanVM.Guest.Memory.GuestCntVJ.Part09
public import LeanVM.Guest.Memory.GuestCntVJ.Part10
public import LeanVM.Guest.Memory.GuestCntVJ.Part11
public import LeanVM.Guest.Memory.GuestCntVJ.Part12
public import LeanVM.Guest.Memory.GuestCntVJ.Part13
public import LeanVM.Guest.Memory.GuestCntVJ.Part14
public import LeanVM.Guest.Memory.GuestCntVJ.Part15

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjchkIdx_319 : kvjchkIdx 319 = true := by
  have hb : blockB (kvjlookJ 319) (kvjomLookJ 319) false [] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨15304, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [← blockR_eq (Data.core319.body.drop 0), kvjsplit_319_0]
  exact kvjchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_320 : kvjchkIdx 320 = true := by
  have hb : blockB (kvjlookJ 320) (kvjomLookJ 320) false [] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨15490, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [← blockR_eq (Data.core320.body.drop 0), kvjsplit_320_0]
  exact kvjchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_321 : kvjchkIdx 321 = true := by
  have hb : blockB (kvjlookJ 321) (kvjomLookJ 321) false [] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨16210, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [← blockR_eq (Data.core321.body.drop 0), kvjsplit_321_0]
  exact kvjchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_322 : kvjchkIdx 322 = true := by
  have hb : blockB (kvjlookJ 322) (kvjomLookJ 322) false [] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨16979, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [← blockR_eq (Data.core322.body.drop 0), kvjsplit_322_0]
  exact kvjchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvjchkIdx_all : ∀ j < 1752, kvjchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 319
  · subst h1000; exact kvjchkIdx_319
  by_cases h1001 : j = 320
  · subst h1001; exact kvjchkIdx_320
  by_cases h1002 : j = 321
  · subst h1002; exact kvjchkIdx_321
  by_cases h1003 : j = 322
  · subst h1003; exact kvjchkIdx_322
  by_cases h0 : j < 11
  · exact kvjstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvjstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvjstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvjstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvjstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvjstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvjstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvjstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvjstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvjstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvjstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 311
  · exact kvjstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 312
  · exact kvjstaticRange_311.get (by omega) (by omega)
  by_cases h13 : j < 313
  · exact kvjstaticRange_312.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kvjstaticRange_313.get (by omega) (by omega)
  by_cases h15 : j < 315
  · exact kvjstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 316
  · exact kvjstaticRange_315.get (by omega) (by omega)
  by_cases h17 : j < 317
  · exact kvjstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 318
  · exact kvjstaticRange_317.get (by omega) (by omega)
  by_cases h19 : j < 319
  · exact kvjstaticRange_318.get (by omega) (by omega)
  by_cases h20 : j < 344
  · exact kvjstaticRange_323.get (by omega) (by omega)
  by_cases h21 : j < 366
  · exact kvjstaticRange_344.get (by omega) (by omega)
  by_cases h22 : j < 389
  · exact kvjstaticRange_366.get (by omega) (by omega)
  by_cases h23 : j < 403
  · exact kvjstaticRange_389.get (by omega) (by omega)
  by_cases h24 : j < 433
  · exact kvjstaticRange_403.get (by omega) (by omega)
  by_cases h25 : j < 456
  · exact kvjstaticRange_433.get (by omega) (by omega)
  by_cases h26 : j < 478
  · exact kvjstaticRange_456.get (by omega) (by omega)
  by_cases h27 : j < 500
  · exact kvjstaticRange_478.get (by omega) (by omega)
  by_cases h28 : j < 522
  · exact kvjstaticRange_500.get (by omega) (by omega)
  by_cases h29 : j < 544
  · exact kvjstaticRange_522.get (by omega) (by omega)
  by_cases h30 : j < 566
  · exact kvjstaticRange_544.get (by omega) (by omega)
  by_cases h31 : j < 588
  · exact kvjstaticRange_566.get (by omega) (by omega)
  by_cases h32 : j < 610
  · exact kvjstaticRange_588.get (by omega) (by omega)
  by_cases h33 : j < 632
  · exact kvjstaticRange_610.get (by omega) (by omega)
  by_cases h34 : j < 653
  · exact kvjstaticRange_632.get (by omega) (by omega)
  by_cases h35 : j < 675
  · exact kvjstaticRange_653.get (by omega) (by omega)
  by_cases h36 : j < 696
  · exact kvjstaticRange_675.get (by omega) (by omega)
  by_cases h37 : j < 718
  · exact kvjstaticRange_696.get (by omega) (by omega)
  by_cases h38 : j < 739
  · exact kvjstaticRange_718.get (by omega) (by omega)
  by_cases h39 : j < 761
  · exact kvjstaticRange_739.get (by omega) (by omega)
  by_cases h40 : j < 782
  · exact kvjstaticRange_761.get (by omega) (by omega)
  by_cases h41 : j < 804
  · exact kvjstaticRange_782.get (by omega) (by omega)
  by_cases h42 : j < 825
  · exact kvjstaticRange_804.get (by omega) (by omega)
  by_cases h43 : j < 847
  · exact kvjstaticRange_825.get (by omega) (by omega)
  by_cases h44 : j < 868
  · exact kvjstaticRange_847.get (by omega) (by omega)
  by_cases h45 : j < 890
  · exact kvjstaticRange_868.get (by omega) (by omega)
  by_cases h46 : j < 911
  · exact kvjstaticRange_890.get (by omega) (by omega)
  by_cases h47 : j < 932
  · exact kvjstaticRange_911.get (by omega) (by omega)
  by_cases h48 : j < 953
  · exact kvjstaticRange_932.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvjstaticRange_953.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvjstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1016
  · exact kvjstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1039
  · exact kvjstaticRange_1016.get (by omega) (by omega)
  by_cases h53 : j < 1063
  · exact kvjstaticRange_1039.get (by omega) (by omega)
  by_cases h54 : j < 1086
  · exact kvjstaticRange_1063.get (by omega) (by omega)
  by_cases h55 : j < 1106
  · exact kvjstaticRange_1086.get (by omega) (by omega)
  by_cases h56 : j < 1127
  · exact kvjstaticRange_1106.get (by omega) (by omega)
  by_cases h57 : j < 1148
  · exact kvjstaticRange_1127.get (by omega) (by omega)
  by_cases h58 : j < 1169
  · exact kvjstaticRange_1148.get (by omega) (by omega)
  by_cases h59 : j < 1190
  · exact kvjstaticRange_1169.get (by omega) (by omega)
  by_cases h60 : j < 1211
  · exact kvjstaticRange_1190.get (by omega) (by omega)
  by_cases h61 : j < 1232
  · exact kvjstaticRange_1211.get (by omega) (by omega)
  by_cases h62 : j < 1254
  · exact kvjstaticRange_1232.get (by omega) (by omega)
  by_cases h63 : j < 1275
  · exact kvjstaticRange_1254.get (by omega) (by omega)
  by_cases h64 : j < 1296
  · exact kvjstaticRange_1275.get (by omega) (by omega)
  by_cases h65 : j < 1315
  · exact kvjstaticRange_1296.get (by omega) (by omega)
  by_cases h66 : j < 1336
  · exact kvjstaticRange_1315.get (by omega) (by omega)
  by_cases h67 : j < 1357
  · exact kvjstaticRange_1336.get (by omega) (by omega)
  by_cases h68 : j < 1378
  · exact kvjstaticRange_1357.get (by omega) (by omega)
  by_cases h69 : j < 1399
  · exact kvjstaticRange_1378.get (by omega) (by omega)
  by_cases h70 : j < 1420
  · exact kvjstaticRange_1399.get (by omega) (by omega)
  by_cases h71 : j < 1441
  · exact kvjstaticRange_1420.get (by omega) (by omega)
  by_cases h72 : j < 1461
  · exact kvjstaticRange_1441.get (by omega) (by omega)
  by_cases h73 : j < 1482
  · exact kvjstaticRange_1461.get (by omega) (by omega)
  by_cases h74 : j < 1503
  · exact kvjstaticRange_1482.get (by omega) (by omega)
  by_cases h75 : j < 1524
  · exact kvjstaticRange_1503.get (by omega) (by omega)
  by_cases h76 : j < 1545
  · exact kvjstaticRange_1524.get (by omega) (by omega)
  by_cases h77 : j < 1566
  · exact kvjstaticRange_1545.get (by omega) (by omega)
  by_cases h78 : j < 1587
  · exact kvjstaticRange_1566.get (by omega) (by omega)
  by_cases h79 : j < 1607
  · exact kvjstaticRange_1587.get (by omega) (by omega)
  by_cases h80 : j < 1628
  · exact kvjstaticRange_1607.get (by omega) (by omega)
  by_cases h81 : j < 1645
  · exact kvjstaticRange_1628.get (by omega) (by omega)
  by_cases h82 : j < 1661
  · exact kvjstaticRange_1645.get (by omega) (by omega)
  by_cases h83 : j < 1674
  · exact kvjstaticRange_1661.get (by omega) (by omega)
  by_cases h84 : j < 1687
  · exact kvjstaticRange_1674.get (by omega) (by omega)
  by_cases h85 : j < 1700
  · exact kvjstaticRange_1687.get (by omega) (by omega)
  by_cases h86 : j < 1712
  · exact kvjstaticRange_1700.get (by omega) (by omega)
  by_cases h87 : j < 1724
  · exact kvjstaticRange_1712.get (by omega) (by omega)
  by_cases h88 : j < 1733
  · exact kvjstaticRange_1724.get (by omega) (by omega)
  by_cases h89 : j < 1744
  · exact kvjstaticRange_1733.get (by omega) (by omega)
  exact kvjstaticRange_1744.get (by omega) (by omega)

end
end LeanVM.Guest
