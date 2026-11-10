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
public import LeanVM.Guest.Memory.GuestCntVX.Part16

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxchkIdx_320 : kvxchkIdx 320 = true := by
  have hb : blockB (kvxlookJ 320) (kvxomLookJ 320) false [] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨55819, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [← blockR_eq (Data.core320.body.drop 0), kvxsplit_320_0]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_321 : kvxchkIdx 321 = true := by
  have hb : blockB (kvxlookJ 321) (kvxomLookJ 321) false [] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨56909, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [← blockR_eq (Data.core321.body.drop 0), kvxsplit_321_0]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_322 : kvxchkIdx 322 = true := by
  have hb : blockB (kvxlookJ 322) (kvxomLookJ 322) false [] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨57766, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [← blockR_eq (Data.core322.body.drop 0), kvxsplit_322_0]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_323 : kvxchkIdx 323 = true := by
  have hb : blockB (kvxlookJ 323) (kvxomLookJ 323) false [] Data.core323.params Data.core323.name ([], []) Data.core323.body = some (⟨60292, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core323.body)]
    rw [← blockR_eq (Data.core323.body.drop 0), kvxsplit_323_0]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core323) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvxchkIdx_all : ∀ j < 1803, kvxchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 320
  · subst h1000; exact kvxchkIdx_320
  by_cases h1001 : j = 321
  · subst h1001; exact kvxchkIdx_321
  by_cases h1002 : j = 322
  · subst h1002; exact kvxchkIdx_322
  by_cases h1003 : j = 323
  · subst h1003; exact kvxchkIdx_323
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
  by_cases h20 : j < 320
  · exact kvxstaticRange_319.get (by omega) (by omega)
  by_cases h21 : j < 345
  · exact kvxstaticRange_324.get (by omega) (by omega)
  by_cases h22 : j < 367
  · exact kvxstaticRange_345.get (by omega) (by omega)
  by_cases h23 : j < 390
  · exact kvxstaticRange_367.get (by omega) (by omega)
  by_cases h24 : j < 404
  · exact kvxstaticRange_390.get (by omega) (by omega)
  by_cases h25 : j < 434
  · exact kvxstaticRange_404.get (by omega) (by omega)
  by_cases h26 : j < 456
  · exact kvxstaticRange_434.get (by omega) (by omega)
  by_cases h27 : j < 478
  · exact kvxstaticRange_456.get (by omega) (by omega)
  by_cases h28 : j < 500
  · exact kvxstaticRange_478.get (by omega) (by omega)
  by_cases h29 : j < 522
  · exact kvxstaticRange_500.get (by omega) (by omega)
  by_cases h30 : j < 544
  · exact kvxstaticRange_522.get (by omega) (by omega)
  by_cases h31 : j < 566
  · exact kvxstaticRange_544.get (by omega) (by omega)
  by_cases h32 : j < 588
  · exact kvxstaticRange_566.get (by omega) (by omega)
  by_cases h33 : j < 610
  · exact kvxstaticRange_588.get (by omega) (by omega)
  by_cases h34 : j < 632
  · exact kvxstaticRange_610.get (by omega) (by omega)
  by_cases h35 : j < 654
  · exact kvxstaticRange_632.get (by omega) (by omega)
  by_cases h36 : j < 675
  · exact kvxstaticRange_654.get (by omega) (by omega)
  by_cases h37 : j < 697
  · exact kvxstaticRange_675.get (by omega) (by omega)
  by_cases h38 : j < 718
  · exact kvxstaticRange_697.get (by omega) (by omega)
  by_cases h39 : j < 740
  · exact kvxstaticRange_718.get (by omega) (by omega)
  by_cases h40 : j < 761
  · exact kvxstaticRange_740.get (by omega) (by omega)
  by_cases h41 : j < 783
  · exact kvxstaticRange_761.get (by omega) (by omega)
  by_cases h42 : j < 804
  · exact kvxstaticRange_783.get (by omega) (by omega)
  by_cases h43 : j < 826
  · exact kvxstaticRange_804.get (by omega) (by omega)
  by_cases h44 : j < 847
  · exact kvxstaticRange_826.get (by omega) (by omega)
  by_cases h45 : j < 869
  · exact kvxstaticRange_847.get (by omega) (by omega)
  by_cases h46 : j < 890
  · exact kvxstaticRange_869.get (by omega) (by omega)
  by_cases h47 : j < 912
  · exact kvxstaticRange_890.get (by omega) (by omega)
  by_cases h48 : j < 933
  · exact kvxstaticRange_912.get (by omega) (by omega)
  by_cases h49 : j < 954
  · exact kvxstaticRange_933.get (by omega) (by omega)
  by_cases h50 : j < 975
  · exact kvxstaticRange_954.get (by omega) (by omega)
  by_cases h51 : j < 996
  · exact kvxstaticRange_975.get (by omega) (by omega)
  by_cases h52 : j < 1018
  · exact kvxstaticRange_996.get (by omega) (by omega)
  by_cases h53 : j < 1039
  · exact kvxstaticRange_1018.get (by omega) (by omega)
  by_cases h54 : j < 1061
  · exact kvxstaticRange_1039.get (by omega) (by omega)
  by_cases h55 : j < 1085
  · exact kvxstaticRange_1061.get (by omega) (by omega)
  by_cases h56 : j < 1108
  · exact kvxstaticRange_1085.get (by omega) (by omega)
  by_cases h57 : j < 1127
  · exact kvxstaticRange_1108.get (by omega) (by omega)
  by_cases h58 : j < 1148
  · exact kvxstaticRange_1127.get (by omega) (by omega)
  by_cases h59 : j < 1168
  · exact kvxstaticRange_1148.get (by omega) (by omega)
  by_cases h60 : j < 1190
  · exact kvxstaticRange_1168.get (by omega) (by omega)
  by_cases h61 : j < 1211
  · exact kvxstaticRange_1190.get (by omega) (by omega)
  by_cases h62 : j < 1233
  · exact kvxstaticRange_1211.get (by omega) (by omega)
  by_cases h63 : j < 1254
  · exact kvxstaticRange_1233.get (by omega) (by omega)
  by_cases h64 : j < 1275
  · exact kvxstaticRange_1254.get (by omega) (by omega)
  by_cases h65 : j < 1296
  · exact kvxstaticRange_1275.get (by omega) (by omega)
  by_cases h66 : j < 1317
  · exact kvxstaticRange_1296.get (by omega) (by omega)
  by_cases h67 : j < 1339
  · exact kvxstaticRange_1317.get (by omega) (by omega)
  by_cases h68 : j < 1360
  · exact kvxstaticRange_1339.get (by omega) (by omega)
  by_cases h69 : j < 1381
  · exact kvxstaticRange_1360.get (by omega) (by omega)
  by_cases h70 : j < 1402
  · exact kvxstaticRange_1381.get (by omega) (by omega)
  by_cases h71 : j < 1423
  · exact kvxstaticRange_1402.get (by omega) (by omega)
  by_cases h72 : j < 1444
  · exact kvxstaticRange_1423.get (by omega) (by omega)
  by_cases h73 : j < 1465
  · exact kvxstaticRange_1444.get (by omega) (by omega)
  by_cases h74 : j < 1486
  · exact kvxstaticRange_1465.get (by omega) (by omega)
  by_cases h75 : j < 1507
  · exact kvxstaticRange_1486.get (by omega) (by omega)
  by_cases h76 : j < 1528
  · exact kvxstaticRange_1507.get (by omega) (by omega)
  by_cases h77 : j < 1549
  · exact kvxstaticRange_1528.get (by omega) (by omega)
  by_cases h78 : j < 1570
  · exact kvxstaticRange_1549.get (by omega) (by omega)
  by_cases h79 : j < 1591
  · exact kvxstaticRange_1570.get (by omega) (by omega)
  by_cases h80 : j < 1612
  · exact kvxstaticRange_1591.get (by omega) (by omega)
  by_cases h81 : j < 1633
  · exact kvxstaticRange_1612.get (by omega) (by omega)
  by_cases h82 : j < 1653
  · exact kvxstaticRange_1633.get (by omega) (by omega)
  by_cases h83 : j < 1674
  · exact kvxstaticRange_1653.get (by omega) (by omega)
  by_cases h84 : j < 1692
  · exact kvxstaticRange_1674.get (by omega) (by omega)
  by_cases h85 : j < 1707
  · exact kvxstaticRange_1692.get (by omega) (by omega)
  by_cases h86 : j < 1720
  · exact kvxstaticRange_1707.get (by omega) (by omega)
  by_cases h87 : j < 1735
  · exact kvxstaticRange_1720.get (by omega) (by omega)
  by_cases h88 : j < 1747
  · exact kvxstaticRange_1735.get (by omega) (by omega)
  by_cases h89 : j < 1759
  · exact kvxstaticRange_1747.get (by omega) (by omega)
  by_cases h90 : j < 1771
  · exact kvxstaticRange_1759.get (by omega) (by omega)
  by_cases h91 : j < 1782
  · exact kvxstaticRange_1771.get (by omega) (by omega)
  by_cases h92 : j < 1793
  · exact kvxstaticRange_1782.get (by omega) (by omega)
  exact kvxstaticRange_1793.get (by omega) (by omega)

end
end LeanVM.Guest
