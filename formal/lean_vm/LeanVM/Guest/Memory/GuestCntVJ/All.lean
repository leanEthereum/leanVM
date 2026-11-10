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
public import LeanVM.Guest.Memory.GuestCntVJ.Part16

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjchkIdx_320 : kvjchkIdx 320 = true := by
  have hb : blockB (kvjlookJ 320) (kvjomLookJ 320) false [] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨15304, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [← blockR_eq (Data.core320.body.drop 0), kvjsplit_320_0]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_321 : kvjchkIdx 321 = true := by
  have hb : blockB (kvjlookJ 321) (kvjomLookJ 321) false [] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨15490, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [← blockR_eq (Data.core321.body.drop 0), kvjsplit_321_0]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_322 : kvjchkIdx 322 = true := by
  have hb : blockB (kvjlookJ 322) (kvjomLookJ 322) false [] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨16210, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [← blockR_eq (Data.core322.body.drop 0), kvjsplit_322_0]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_323 : kvjchkIdx 323 = true := by
  have hb : blockB (kvjlookJ 323) (kvjomLookJ 323) false [] Data.core323.params Data.core323.name ([], []) Data.core323.body = some (⟨16979, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core323.body)]
    rw [← blockR_eq (Data.core323.body.drop 0), kvjsplit_323_0]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core323) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvjchkIdx_all : ∀ j < 1803, kvjchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 320
  · subst h1000; exact kvjchkIdx_320
  by_cases h1001 : j = 321
  · subst h1001; exact kvjchkIdx_321
  by_cases h1002 : j = 322
  · subst h1002; exact kvjchkIdx_322
  by_cases h1003 : j = 323
  · subst h1003; exact kvjchkIdx_323
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
  by_cases h20 : j < 320
  · exact kvjstaticRange_319.get (by omega) (by omega)
  by_cases h21 : j < 345
  · exact kvjstaticRange_324.get (by omega) (by omega)
  by_cases h22 : j < 367
  · exact kvjstaticRange_345.get (by omega) (by omega)
  by_cases h23 : j < 390
  · exact kvjstaticRange_367.get (by omega) (by omega)
  by_cases h24 : j < 404
  · exact kvjstaticRange_390.get (by omega) (by omega)
  by_cases h25 : j < 434
  · exact kvjstaticRange_404.get (by omega) (by omega)
  by_cases h26 : j < 456
  · exact kvjstaticRange_434.get (by omega) (by omega)
  by_cases h27 : j < 478
  · exact kvjstaticRange_456.get (by omega) (by omega)
  by_cases h28 : j < 500
  · exact kvjstaticRange_478.get (by omega) (by omega)
  by_cases h29 : j < 522
  · exact kvjstaticRange_500.get (by omega) (by omega)
  by_cases h30 : j < 544
  · exact kvjstaticRange_522.get (by omega) (by omega)
  by_cases h31 : j < 566
  · exact kvjstaticRange_544.get (by omega) (by omega)
  by_cases h32 : j < 588
  · exact kvjstaticRange_566.get (by omega) (by omega)
  by_cases h33 : j < 610
  · exact kvjstaticRange_588.get (by omega) (by omega)
  by_cases h34 : j < 632
  · exact kvjstaticRange_610.get (by omega) (by omega)
  by_cases h35 : j < 654
  · exact kvjstaticRange_632.get (by omega) (by omega)
  by_cases h36 : j < 675
  · exact kvjstaticRange_654.get (by omega) (by omega)
  by_cases h37 : j < 697
  · exact kvjstaticRange_675.get (by omega) (by omega)
  by_cases h38 : j < 718
  · exact kvjstaticRange_697.get (by omega) (by omega)
  by_cases h39 : j < 740
  · exact kvjstaticRange_718.get (by omega) (by omega)
  by_cases h40 : j < 761
  · exact kvjstaticRange_740.get (by omega) (by omega)
  by_cases h41 : j < 783
  · exact kvjstaticRange_761.get (by omega) (by omega)
  by_cases h42 : j < 804
  · exact kvjstaticRange_783.get (by omega) (by omega)
  by_cases h43 : j < 826
  · exact kvjstaticRange_804.get (by omega) (by omega)
  by_cases h44 : j < 847
  · exact kvjstaticRange_826.get (by omega) (by omega)
  by_cases h45 : j < 869
  · exact kvjstaticRange_847.get (by omega) (by omega)
  by_cases h46 : j < 890
  · exact kvjstaticRange_869.get (by omega) (by omega)
  by_cases h47 : j < 912
  · exact kvjstaticRange_890.get (by omega) (by omega)
  by_cases h48 : j < 933
  · exact kvjstaticRange_912.get (by omega) (by omega)
  by_cases h49 : j < 954
  · exact kvjstaticRange_933.get (by omega) (by omega)
  by_cases h50 : j < 975
  · exact kvjstaticRange_954.get (by omega) (by omega)
  by_cases h51 : j < 996
  · exact kvjstaticRange_975.get (by omega) (by omega)
  by_cases h52 : j < 1018
  · exact kvjstaticRange_996.get (by omega) (by omega)
  by_cases h53 : j < 1039
  · exact kvjstaticRange_1018.get (by omega) (by omega)
  by_cases h54 : j < 1061
  · exact kvjstaticRange_1039.get (by omega) (by omega)
  by_cases h55 : j < 1085
  · exact kvjstaticRange_1061.get (by omega) (by omega)
  by_cases h56 : j < 1108
  · exact kvjstaticRange_1085.get (by omega) (by omega)
  by_cases h57 : j < 1127
  · exact kvjstaticRange_1108.get (by omega) (by omega)
  by_cases h58 : j < 1148
  · exact kvjstaticRange_1127.get (by omega) (by omega)
  by_cases h59 : j < 1168
  · exact kvjstaticRange_1148.get (by omega) (by omega)
  by_cases h60 : j < 1190
  · exact kvjstaticRange_1168.get (by omega) (by omega)
  by_cases h61 : j < 1211
  · exact kvjstaticRange_1190.get (by omega) (by omega)
  by_cases h62 : j < 1233
  · exact kvjstaticRange_1211.get (by omega) (by omega)
  by_cases h63 : j < 1254
  · exact kvjstaticRange_1233.get (by omega) (by omega)
  by_cases h64 : j < 1275
  · exact kvjstaticRange_1254.get (by omega) (by omega)
  by_cases h65 : j < 1296
  · exact kvjstaticRange_1275.get (by omega) (by omega)
  by_cases h66 : j < 1317
  · exact kvjstaticRange_1296.get (by omega) (by omega)
  by_cases h67 : j < 1339
  · exact kvjstaticRange_1317.get (by omega) (by omega)
  by_cases h68 : j < 1360
  · exact kvjstaticRange_1339.get (by omega) (by omega)
  by_cases h69 : j < 1381
  · exact kvjstaticRange_1360.get (by omega) (by omega)
  by_cases h70 : j < 1402
  · exact kvjstaticRange_1381.get (by omega) (by omega)
  by_cases h71 : j < 1423
  · exact kvjstaticRange_1402.get (by omega) (by omega)
  by_cases h72 : j < 1444
  · exact kvjstaticRange_1423.get (by omega) (by omega)
  by_cases h73 : j < 1465
  · exact kvjstaticRange_1444.get (by omega) (by omega)
  by_cases h74 : j < 1486
  · exact kvjstaticRange_1465.get (by omega) (by omega)
  by_cases h75 : j < 1507
  · exact kvjstaticRange_1486.get (by omega) (by omega)
  by_cases h76 : j < 1528
  · exact kvjstaticRange_1507.get (by omega) (by omega)
  by_cases h77 : j < 1549
  · exact kvjstaticRange_1528.get (by omega) (by omega)
  by_cases h78 : j < 1570
  · exact kvjstaticRange_1549.get (by omega) (by omega)
  by_cases h79 : j < 1591
  · exact kvjstaticRange_1570.get (by omega) (by omega)
  by_cases h80 : j < 1612
  · exact kvjstaticRange_1591.get (by omega) (by omega)
  by_cases h81 : j < 1633
  · exact kvjstaticRange_1612.get (by omega) (by omega)
  by_cases h82 : j < 1653
  · exact kvjstaticRange_1633.get (by omega) (by omega)
  by_cases h83 : j < 1674
  · exact kvjstaticRange_1653.get (by omega) (by omega)
  by_cases h84 : j < 1692
  · exact kvjstaticRange_1674.get (by omega) (by omega)
  by_cases h85 : j < 1707
  · exact kvjstaticRange_1692.get (by omega) (by omega)
  by_cases h86 : j < 1720
  · exact kvjstaticRange_1707.get (by omega) (by omega)
  by_cases h87 : j < 1735
  · exact kvjstaticRange_1720.get (by omega) (by omega)
  by_cases h88 : j < 1747
  · exact kvjstaticRange_1735.get (by omega) (by omega)
  by_cases h89 : j < 1759
  · exact kvjstaticRange_1747.get (by omega) (by omega)
  by_cases h90 : j < 1771
  · exact kvjstaticRange_1759.get (by omega) (by omega)
  by_cases h91 : j < 1782
  · exact kvjstaticRange_1771.get (by omega) (by omega)
  by_cases h92 : j < 1793
  · exact kvjstaticRange_1782.get (by omega) (by omega)
  exact kvjstaticRange_1793.get (by omega) (by omega)

end
end LeanVM.Guest
