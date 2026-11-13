/-
  LeanVM.Guest.B1.Tables.VtC.Stores

  The stores of `verify_tables`' evaluation list (generated: scripts/b1c-vt/genstores.py).

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Flat

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The 114 stores of `vtEvL`, in order. -/
def vtSL : List Atom := [
  .load (.n 38) (.n 33) 0,
  .load (.n 40) (.n 34) 0,
  .load (.n 44) (.n 33) 1,
  .load (.n 46) (.n 34) 1,
  .load (.n 52) (.n 33) 2,
  .load (.n 54) (.n 34) 2,
  .load (.n 58) (.n 33) 3,
  .load (.n 63) (.n 34) 3,
  .load (.n 67) (.n 33) 4,
  .load (.n 72) (.n 34) 4,
  .load (.n 76) (.n 33) 5,
  .load (.n 80) (.n 34) 5,
  .load (.n 84) (.n 33) 6,
  .load (.n 89) (.n 34) 6,
  .load (.n 93) (.n 33) 7,
  .load (.n 98) (.n 34) 7,
  .load (.n 102) (.n 33) 8,
  .load (.n 110) (.n 34) 8,
  .load (.n 116) (.n 117) 212,
  .load (.n 120) (.n 121) 0,
  .load (.n 129) (.n 130) 212,
  .load (.n 123) (.n 140) 0,
  .load (.n 149) (.n 150) 212,
  .load (.n 143) (.n 160) 0,
  .load (.n 169) (.n 170) 212,
  .load (.n 163) (.n 180) 0,
  .load (.n 189) (.n 190) 212,
  .load (.n 183) (.n 200) 0,
  .load (.n 209) (.n 210) 212,
  .load (.n 203) (.n 220) 0,
  .load (.n 229) (.n 230) 212,
  .load (.n 223) (.n 240) 0,
  .load (.n 249) (.n 250) 212,
  .load (.n 243) (.n 260) 0,
  .load (.n 269) (.n 270) 212,
  .load (.n 263) (.n 280) 0,
  .load (.n 359) (.n 33) 18,
  .load (.n 363) (.n 34) 18,
  .load (.n 367) (.n 33) 19,
  .load (.n 371) (.n 34) 19,
  .load (.n 375) (.n 33) 20,
  .load (.n 378) (.n 34) 20,
  .load (.n 382) (.n 33) 21,
  .load (.n 386) (.n 34) 21,
  .load (.n 390) (.n 33) 22,
  .load (.n 394) (.n 34) 22,
  .load (.n 398) (.n 33) 23,
  .load (.n 407) (.n 34) 23,
  .load (.n 413) (.n 414) 212,
  .load (.n 417) (.n 418) 0,
  .load (.n 426) (.n 427) 212,
  .load (.n 420) (.n 437) 0,
  .load (.n 446) (.n 447) 212,
  .load (.n 440) (.n 457) 0,
  .load (.n 466) (.n 467) 212,
  .load (.n 460) (.n 477) 0,
  .load (.n 486) (.n 487) 212,
  .load (.n 480) (.n 497) 0,
  .load (.n 506) (.n 507) 212,
  .load (.n 500) (.n 517) 0,
  .load (.n 665) (.n 664) 0,
  .load (.n 666) (.n 664) 1,
  .load (.n 667) (.n 664) 2,
  .load (.n 668) (.n 664) 3,
  .load (.n 669) (.n 664) 4,
  .load (.n 670) (.n 664) 5,
  .load (.n 671) (.n 664) 6,
  .load (.n 672) (.n 664) 7,
  .load (.n 673) (.n 664) 8,
  .load (.n 674) (.n 664) 9,
  .load (.n 675) (.n 664) 10,
  .load (.n 676) (.n 664) 11,
  .load (.n 677) (.n 664) 12,
  .load (.n 678) (.n 664) 13,
  .load (.n 679) (.n 664) 14,
  .load (.n 680) (.n 664) 15,
  .load (.n 681) (.n 664) 16,
  .load (.n 682) (.n 664) 17,
  .load (.n 683) (.n 664) 18,
  .load (.n 684) (.n 664) 19,
  .load (.n 685) (.n 664) 20,
  .load (.n 686) (.n 664) 21,
  .load (.n 687) (.n 664) 22,
  .load (.n 688) (.n 664) 23,
  .load (.n 689) (.n 664) 24,
  .load (.n 690) (.n 664) 25,
  .load (.n 691) (.n 664) 26,
  .load (.n 692) (.n 664) 27,
  .load (.n 693) (.n 664) 28,
  .load (.n 694) (.n 664) 29,
  .load (.n 695) (.n 664) 30,
  .load (.n 696) (.n 664) 31,
  .load (.n 697) (.n 664) 32,
  .load (.n 698) (.n 664) 33,
  .load (.n 809) (.n 777) 1,
  .load (.n 812) (.n 15) 0,
  .load (.n 816) (.n 15) 1,
  .load (.n 837) (.n 777) 2,
  .load (.n 1302) (.n 15) 2,
  .load (.n 1316) (.n 15) 3,
  .load (.n 1867) (.n 19) 0,
  .load (.n 1883) (.n 19) 1,
  .load (.n 1891) (.n 19) 2,
  .load (.n 1899) (.n 19) 3,
  .load (.n 2605) (.n 2627) 0,
  .load (.n 2606) (.n 2627) 1,
  .load (.n 2607) (.n 2627) 2,
  .load (.n 2608) (.n 2627) 3,
  .load (.n 2609) (.n 2627) 4,
  .load (.n 2632) (.n 2627) 5,
  .load (.n 2620) (.n 2627) 6,
  .load (.n 2633) (.n 2630) 0,
  .load (.n 5974) (.n 15) 157,
  .load (.n 5977) (.n 15) 158]

set_option maxRecDepth 100000 in
/-- The counter `storesOf` carries stays unevaluated over long runs without loads: the kernel's
recursion goes deep (as `CoreNames`' checks). -/
theorem vt_stores : storesOf 20 vtEvL = vtSL := by decide +kernel

end
end LeanVM.Guest.B1.Tables
