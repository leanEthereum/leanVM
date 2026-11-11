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
public import LeanVM.Guest.Memory.GuestWords.Part23
public import LeanVM.Guest.Memory.GuestWords.Part24
public import LeanVM.Guest.Memory.GuestWords.Part25
public import LeanVM.Guest.Memory.GuestWords.Part26
public import LeanVM.Guest.Memory.GuestWords.Part27
public import LeanVM.Guest.Memory.GuestWords.Part28
public import LeanVM.Guest.Memory.GuestWords.Part29
public import LeanVM.Guest.Memory.GuestWords.Part30

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

theorem wchkIdx_all : ∀ j < 1601, wchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact wchkIdx_19
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
  by_cases h14 : j < 286
  · exact wstaticRange_265.get (by omega) (by omega)
  by_cases h15 : j < 313
  · exact wstaticRange_286.get (by omega) (by omega)
  by_cases h16 : j < 335
  · exact wstaticRange_313.get (by omega) (by omega)
  by_cases h17 : j < 336
  · exact wstaticRange_335.get (by omega) (by omega)
  by_cases h18 : j < 337
  · exact wstaticRange_336.get (by omega) (by omega)
  by_cases h19 : j < 338
  · exact wstaticRange_337.get (by omega) (by omega)
  by_cases h20 : j < 339
  · exact wstaticRange_338.get (by omega) (by omega)
  by_cases h21 : j < 340
  · exact wstaticRange_339.get (by omega) (by omega)
  by_cases h22 : j < 341
  · exact wstaticRange_340.get (by omega) (by omega)
  by_cases h23 : j < 342
  · exact wstaticRange_341.get (by omega) (by omega)
  by_cases h24 : j < 343
  · exact wstaticRange_342.get (by omega) (by omega)
  by_cases h25 : j < 344
  · exact wstaticRange_343.get (by omega) (by omega)
  by_cases h26 : j < 345
  · exact wstaticRange_344.get (by omega) (by omega)
  by_cases h27 : j < 346
  · exact wstaticRange_345.get (by omega) (by omega)
  by_cases h28 : j < 367
  · exact wstaticRange_346.get (by omega) (by omega)
  by_cases h29 : j < 389
  · exact wstaticRange_367.get (by omega) (by omega)
  by_cases h30 : j < 412
  · exact wstaticRange_389.get (by omega) (by omega)
  by_cases h31 : j < 426
  · exact wstaticRange_412.get (by omega) (by omega)
  by_cases h32 : j < 448
  · exact wstaticRange_426.get (by omega) (by omega)
  by_cases h33 : j < 473
  · exact wstaticRange_448.get (by omega) (by omega)
  by_cases h34 : j < 494
  · exact wstaticRange_473.get (by omega) (by omega)
  by_cases h35 : j < 515
  · exact wstaticRange_494.get (by omega) (by omega)
  by_cases h36 : j < 536
  · exact wstaticRange_515.get (by omega) (by omega)
  by_cases h37 : j < 557
  · exact wstaticRange_536.get (by omega) (by omega)
  by_cases h38 : j < 578
  · exact wstaticRange_557.get (by omega) (by omega)
  by_cases h39 : j < 599
  · exact wstaticRange_578.get (by omega) (by omega)
  by_cases h40 : j < 620
  · exact wstaticRange_599.get (by omega) (by omega)
  by_cases h41 : j < 641
  · exact wstaticRange_620.get (by omega) (by omega)
  by_cases h42 : j < 661
  · exact wstaticRange_641.get (by omega) (by omega)
  by_cases h43 : j < 682
  · exact wstaticRange_661.get (by omega) (by omega)
  by_cases h44 : j < 703
  · exact wstaticRange_682.get (by omega) (by omega)
  by_cases h45 : j < 724
  · exact wstaticRange_703.get (by omega) (by omega)
  by_cases h46 : j < 744
  · exact wstaticRange_724.get (by omega) (by omega)
  by_cases h47 : j < 765
  · exact wstaticRange_744.get (by omega) (by omega)
  by_cases h48 : j < 785
  · exact wstaticRange_765.get (by omega) (by omega)
  by_cases h49 : j < 806
  · exact wstaticRange_785.get (by omega) (by omega)
  by_cases h50 : j < 826
  · exact wstaticRange_806.get (by omega) (by omega)
  by_cases h51 : j < 847
  · exact wstaticRange_826.get (by omega) (by omega)
  by_cases h52 : j < 868
  · exact wstaticRange_847.get (by omega) (by omega)
  by_cases h53 : j < 888
  · exact wstaticRange_868.get (by omega) (by omega)
  by_cases h54 : j < 909
  · exact wstaticRange_888.get (by omega) (by omega)
  by_cases h55 : j < 930
  · exact wstaticRange_909.get (by omega) (by omega)
  by_cases h56 : j < 952
  · exact wstaticRange_930.get (by omega) (by omega)
  by_cases h57 : j < 976
  · exact wstaticRange_952.get (by omega) (by omega)
  by_cases h58 : j < 1000
  · exact wstaticRange_976.get (by omega) (by omega)
  by_cases h59 : j < 1020
  · exact wstaticRange_1000.get (by omega) (by omega)
  by_cases h60 : j < 1041
  · exact wstaticRange_1020.get (by omega) (by omega)
  by_cases h61 : j < 1054
  · exact wstaticRange_1041.get (by omega) (by omega)
  by_cases h62 : j < 1073
  · exact wstaticRange_1054.get (by omega) (by omega)
  by_cases h63 : j < 1091
  · exact wstaticRange_1073.get (by omega) (by omega)
  by_cases h64 : j < 1109
  · exact wstaticRange_1091.get (by omega) (by omega)
  by_cases h65 : j < 1128
  · exact wstaticRange_1109.get (by omega) (by omega)
  by_cases h66 : j < 1141
  · exact wstaticRange_1128.get (by omega) (by omega)
  by_cases h67 : j < 1162
  · exact wstaticRange_1141.get (by omega) (by omega)
  by_cases h68 : j < 1173
  · exact wstaticRange_1162.get (by omega) (by omega)
  by_cases h69 : j < 1191
  · exact wstaticRange_1173.get (by omega) (by omega)
  by_cases h70 : j < 1209
  · exact wstaticRange_1191.get (by omega) (by omega)
  by_cases h71 : j < 1223
  · exact wstaticRange_1209.get (by omega) (by omega)
  by_cases h72 : j < 1241
  · exact wstaticRange_1223.get (by omega) (by omega)
  by_cases h73 : j < 1256
  · exact wstaticRange_1241.get (by omega) (by omega)
  by_cases h74 : j < 1268
  · exact wstaticRange_1256.get (by omega) (by omega)
  by_cases h75 : j < 1288
  · exact wstaticRange_1268.get (by omega) (by omega)
  by_cases h76 : j < 1300
  · exact wstaticRange_1288.get (by omega) (by omega)
  by_cases h77 : j < 1311
  · exact wstaticRange_1300.get (by omega) (by omega)
  by_cases h78 : j < 1331
  · exact wstaticRange_1311.get (by omega) (by omega)
  by_cases h79 : j < 1343
  · exact wstaticRange_1331.get (by omega) (by omega)
  by_cases h80 : j < 1354
  · exact wstaticRange_1343.get (by omega) (by omega)
  by_cases h81 : j < 1373
  · exact wstaticRange_1354.get (by omega) (by omega)
  by_cases h82 : j < 1387
  · exact wstaticRange_1373.get (by omega) (by omega)
  by_cases h83 : j < 1397
  · exact wstaticRange_1387.get (by omega) (by omega)
  by_cases h84 : j < 1415
  · exact wstaticRange_1397.get (by omega) (by omega)
  by_cases h85 : j < 1433
  · exact wstaticRange_1415.get (by omega) (by omega)
  by_cases h86 : j < 1441
  · exact wstaticRange_1433.get (by omega) (by omega)
  by_cases h87 : j < 1452
  · exact wstaticRange_1441.get (by omega) (by omega)
  by_cases h88 : j < 1471
  · exact wstaticRange_1452.get (by omega) (by omega)
  by_cases h89 : j < 1483
  · exact wstaticRange_1471.get (by omega) (by omega)
  by_cases h90 : j < 1491
  · exact wstaticRange_1483.get (by omega) (by omega)
  by_cases h91 : j < 1502
  · exact wstaticRange_1491.get (by omega) (by omega)
  by_cases h92 : j < 1514
  · exact wstaticRange_1502.get (by omega) (by omega)
  by_cases h93 : j < 1530
  · exact wstaticRange_1514.get (by omega) (by omega)
  by_cases h94 : j < 1543
  · exact wstaticRange_1530.get (by omega) (by omega)
  by_cases h95 : j < 1556
  · exact wstaticRange_1543.get (by omega) (by omega)
  by_cases h96 : j < 1569
  · exact wstaticRange_1556.get (by omega) (by omega)
  by_cases h97 : j < 1581
  · exact wstaticRange_1569.get (by omega) (by omega)
  by_cases h98 : j < 1593
  · exact wstaticRange_1581.get (by omega) (by omega)
  exact wstaticRange_1593.get (by omega) (by omega)

end
end LeanVM.Guest
