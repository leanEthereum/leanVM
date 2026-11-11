/-
  LeanVM.Guest.Memory.GuestCntVX.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVX.Part00
public import LeanVM.Guest.Memory.GuestCntVX.Part01
public import LeanVM.Guest.Memory.GuestCntVX.Part02
public import LeanVM.Guest.Memory.GuestCntVX.Part03
public import LeanVM.Guest.Memory.GuestCntVX.Part04
public import LeanVM.Guest.Memory.GuestCntVX.Part05
public import LeanVM.Guest.Memory.GuestCntVX.Part06
public import LeanVM.Guest.Memory.GuestCntVX.Part07
public import LeanVM.Guest.Memory.GuestCntVX.Part08
public import LeanVM.Guest.Memory.GuestCntVX.Part09
public import LeanVM.Guest.Memory.GuestCntVX.Part10
public import LeanVM.Guest.Memory.GuestCntVX.Part11
public import LeanVM.Guest.Memory.GuestCntVX.Part12
public import LeanVM.Guest.Memory.GuestCntVX.Part13
public import LeanVM.Guest.Memory.GuestCntVX.Part14
public import LeanVM.Guest.Memory.GuestCntVX.Part15

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxchkIdx_319 : kvxchkIdx 319 = true := by
  have hb : blockB (kvxlookJ 319) (kvxomLookJ 319) false [] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨55819, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [← blockR_eq (Data.core319.body.drop 0), kvxsplit_319_0]
  exact kvxchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_320 : kvxchkIdx 320 = true := by
  have hb : blockB (kvxlookJ 320) (kvxomLookJ 320) false [] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨56909, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [← blockR_eq (Data.core320.body.drop 0), kvxsplit_320_0]
  exact kvxchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_321 : kvxchkIdx 321 = true := by
  have hb : blockB (kvxlookJ 321) (kvxomLookJ 321) false [] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨57766, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [← blockR_eq (Data.core321.body.drop 0), kvxsplit_321_0]
  exact kvxchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_322 : kvxchkIdx 322 = true := by
  have hb : blockB (kvxlookJ 322) (kvxomLookJ 322) false [] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨60292, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [← blockR_eq (Data.core322.body.drop 0), kvxsplit_322_0]
  exact kvxchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvxchkIdx_all : ∀ j < 1752, kvxchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 319
  · subst h1000; exact kvxchkIdx_319
  by_cases h1001 : j = 320
  · subst h1001; exact kvxchkIdx_320
  by_cases h1002 : j = 321
  · subst h1002; exact kvxchkIdx_321
  by_cases h1003 : j = 322
  · subst h1003; exact kvxchkIdx_322
  by_cases h0 : j < 11
  · exact kvxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvxstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvxstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvxstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvxstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvxstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvxstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvxstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvxstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvxstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvxstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 311
  · exact kvxstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 312
  · exact kvxstaticRange_311.get (by omega) (by omega)
  by_cases h13 : j < 313
  · exact kvxstaticRange_312.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kvxstaticRange_313.get (by omega) (by omega)
  by_cases h15 : j < 315
  · exact kvxstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 316
  · exact kvxstaticRange_315.get (by omega) (by omega)
  by_cases h17 : j < 317
  · exact kvxstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 318
  · exact kvxstaticRange_317.get (by omega) (by omega)
  by_cases h19 : j < 319
  · exact kvxstaticRange_318.get (by omega) (by omega)
  by_cases h20 : j < 344
  · exact kvxstaticRange_323.get (by omega) (by omega)
  by_cases h21 : j < 366
  · exact kvxstaticRange_344.get (by omega) (by omega)
  by_cases h22 : j < 389
  · exact kvxstaticRange_366.get (by omega) (by omega)
  by_cases h23 : j < 403
  · exact kvxstaticRange_389.get (by omega) (by omega)
  by_cases h24 : j < 433
  · exact kvxstaticRange_403.get (by omega) (by omega)
  by_cases h25 : j < 456
  · exact kvxstaticRange_433.get (by omega) (by omega)
  by_cases h26 : j < 478
  · exact kvxstaticRange_456.get (by omega) (by omega)
  by_cases h27 : j < 500
  · exact kvxstaticRange_478.get (by omega) (by omega)
  by_cases h28 : j < 522
  · exact kvxstaticRange_500.get (by omega) (by omega)
  by_cases h29 : j < 544
  · exact kvxstaticRange_522.get (by omega) (by omega)
  by_cases h30 : j < 566
  · exact kvxstaticRange_544.get (by omega) (by omega)
  by_cases h31 : j < 588
  · exact kvxstaticRange_566.get (by omega) (by omega)
  by_cases h32 : j < 610
  · exact kvxstaticRange_588.get (by omega) (by omega)
  by_cases h33 : j < 632
  · exact kvxstaticRange_610.get (by omega) (by omega)
  by_cases h34 : j < 653
  · exact kvxstaticRange_632.get (by omega) (by omega)
  by_cases h35 : j < 675
  · exact kvxstaticRange_653.get (by omega) (by omega)
  by_cases h36 : j < 696
  · exact kvxstaticRange_675.get (by omega) (by omega)
  by_cases h37 : j < 718
  · exact kvxstaticRange_696.get (by omega) (by omega)
  by_cases h38 : j < 739
  · exact kvxstaticRange_718.get (by omega) (by omega)
  by_cases h39 : j < 761
  · exact kvxstaticRange_739.get (by omega) (by omega)
  by_cases h40 : j < 782
  · exact kvxstaticRange_761.get (by omega) (by omega)
  by_cases h41 : j < 804
  · exact kvxstaticRange_782.get (by omega) (by omega)
  by_cases h42 : j < 825
  · exact kvxstaticRange_804.get (by omega) (by omega)
  by_cases h43 : j < 847
  · exact kvxstaticRange_825.get (by omega) (by omega)
  by_cases h44 : j < 868
  · exact kvxstaticRange_847.get (by omega) (by omega)
  by_cases h45 : j < 890
  · exact kvxstaticRange_868.get (by omega) (by omega)
  by_cases h46 : j < 911
  · exact kvxstaticRange_890.get (by omega) (by omega)
  by_cases h47 : j < 932
  · exact kvxstaticRange_911.get (by omega) (by omega)
  by_cases h48 : j < 953
  · exact kvxstaticRange_932.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvxstaticRange_953.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvxstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1016
  · exact kvxstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1039
  · exact kvxstaticRange_1016.get (by omega) (by omega)
  by_cases h53 : j < 1063
  · exact kvxstaticRange_1039.get (by omega) (by omega)
  by_cases h54 : j < 1086
  · exact kvxstaticRange_1063.get (by omega) (by omega)
  by_cases h55 : j < 1106
  · exact kvxstaticRange_1086.get (by omega) (by omega)
  by_cases h56 : j < 1127
  · exact kvxstaticRange_1106.get (by omega) (by omega)
  by_cases h57 : j < 1148
  · exact kvxstaticRange_1127.get (by omega) (by omega)
  by_cases h58 : j < 1169
  · exact kvxstaticRange_1148.get (by omega) (by omega)
  by_cases h59 : j < 1190
  · exact kvxstaticRange_1169.get (by omega) (by omega)
  by_cases h60 : j < 1211
  · exact kvxstaticRange_1190.get (by omega) (by omega)
  by_cases h61 : j < 1232
  · exact kvxstaticRange_1211.get (by omega) (by omega)
  by_cases h62 : j < 1254
  · exact kvxstaticRange_1232.get (by omega) (by omega)
  by_cases h63 : j < 1275
  · exact kvxstaticRange_1254.get (by omega) (by omega)
  by_cases h64 : j < 1296
  · exact kvxstaticRange_1275.get (by omega) (by omega)
  by_cases h65 : j < 1315
  · exact kvxstaticRange_1296.get (by omega) (by omega)
  by_cases h66 : j < 1336
  · exact kvxstaticRange_1315.get (by omega) (by omega)
  by_cases h67 : j < 1357
  · exact kvxstaticRange_1336.get (by omega) (by omega)
  by_cases h68 : j < 1378
  · exact kvxstaticRange_1357.get (by omega) (by omega)
  by_cases h69 : j < 1399
  · exact kvxstaticRange_1378.get (by omega) (by omega)
  by_cases h70 : j < 1420
  · exact kvxstaticRange_1399.get (by omega) (by omega)
  by_cases h71 : j < 1441
  · exact kvxstaticRange_1420.get (by omega) (by omega)
  by_cases h72 : j < 1461
  · exact kvxstaticRange_1441.get (by omega) (by omega)
  by_cases h73 : j < 1482
  · exact kvxstaticRange_1461.get (by omega) (by omega)
  by_cases h74 : j < 1503
  · exact kvxstaticRange_1482.get (by omega) (by omega)
  by_cases h75 : j < 1524
  · exact kvxstaticRange_1503.get (by omega) (by omega)
  by_cases h76 : j < 1545
  · exact kvxstaticRange_1524.get (by omega) (by omega)
  by_cases h77 : j < 1566
  · exact kvxstaticRange_1545.get (by omega) (by omega)
  by_cases h78 : j < 1587
  · exact kvxstaticRange_1566.get (by omega) (by omega)
  by_cases h79 : j < 1607
  · exact kvxstaticRange_1587.get (by omega) (by omega)
  by_cases h80 : j < 1628
  · exact kvxstaticRange_1607.get (by omega) (by omega)
  by_cases h81 : j < 1645
  · exact kvxstaticRange_1628.get (by omega) (by omega)
  by_cases h82 : j < 1661
  · exact kvxstaticRange_1645.get (by omega) (by omega)
  by_cases h83 : j < 1674
  · exact kvxstaticRange_1661.get (by omega) (by omega)
  by_cases h84 : j < 1687
  · exact kvxstaticRange_1674.get (by omega) (by omega)
  by_cases h85 : j < 1700
  · exact kvxstaticRange_1687.get (by omega) (by omega)
  by_cases h86 : j < 1712
  · exact kvxstaticRange_1700.get (by omega) (by omega)
  by_cases h87 : j < 1724
  · exact kvxstaticRange_1712.get (by omega) (by omega)
  by_cases h88 : j < 1733
  · exact kvxstaticRange_1724.get (by omega) (by omega)
  by_cases h89 : j < 1744
  · exact kvxstaticRange_1733.get (by omega) (by omega)
  exact kvxstaticRange_1744.get (by omega) (by omega)

end
end LeanVM.Guest
