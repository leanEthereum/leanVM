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
  .load (.n 39) (.n 34) 0,
  .load (.n 41) (.n 35) 0,
  .load (.n 45) (.n 34) 1,
  .load (.n 47) (.n 35) 1,
  .load (.n 53) (.n 34) 2,
  .load (.n 55) (.n 35) 2,
  .load (.n 59) (.n 34) 3,
  .load (.n 64) (.n 35) 3,
  .load (.n 68) (.n 34) 4,
  .load (.n 73) (.n 35) 4,
  .load (.n 77) (.n 34) 5,
  .load (.n 81) (.n 35) 5,
  .load (.n 85) (.n 34) 6,
  .load (.n 90) (.n 35) 6,
  .load (.n 94) (.n 34) 7,
  .load (.n 99) (.n 35) 7,
  .load (.n 103) (.n 34) 8,
  .load (.n 111) (.n 35) 8,
  .load (.n 117) (.n 118) 212,
  .load (.n 121) (.n 122) 0,
  .load (.n 130) (.n 131) 212,
  .load (.n 124) (.n 141) 0,
  .load (.n 150) (.n 151) 212,
  .load (.n 144) (.n 161) 0,
  .load (.n 170) (.n 171) 212,
  .load (.n 164) (.n 181) 0,
  .load (.n 190) (.n 191) 212,
  .load (.n 184) (.n 201) 0,
  .load (.n 210) (.n 211) 212,
  .load (.n 204) (.n 221) 0,
  .load (.n 230) (.n 231) 212,
  .load (.n 224) (.n 241) 0,
  .load (.n 250) (.n 251) 212,
  .load (.n 244) (.n 261) 0,
  .load (.n 270) (.n 271) 212,
  .load (.n 264) (.n 281) 0,
  .load (.n 360) (.n 34) 18,
  .load (.n 364) (.n 35) 18,
  .load (.n 368) (.n 34) 19,
  .load (.n 372) (.n 35) 19,
  .load (.n 376) (.n 34) 20,
  .load (.n 379) (.n 35) 20,
  .load (.n 383) (.n 34) 21,
  .load (.n 387) (.n 35) 21,
  .load (.n 391) (.n 34) 22,
  .load (.n 395) (.n 35) 22,
  .load (.n 399) (.n 34) 23,
  .load (.n 408) (.n 35) 23,
  .load (.n 414) (.n 415) 212,
  .load (.n 418) (.n 419) 0,
  .load (.n 427) (.n 428) 212,
  .load (.n 421) (.n 438) 0,
  .load (.n 447) (.n 448) 212,
  .load (.n 441) (.n 458) 0,
  .load (.n 467) (.n 468) 212,
  .load (.n 461) (.n 478) 0,
  .load (.n 487) (.n 488) 212,
  .load (.n 481) (.n 498) 0,
  .load (.n 507) (.n 508) 212,
  .load (.n 501) (.n 518) 0,
  .load (.n 666) (.n 665) 0,
  .load (.n 667) (.n 665) 1,
  .load (.n 668) (.n 665) 2,
  .load (.n 669) (.n 665) 3,
  .load (.n 670) (.n 665) 4,
  .load (.n 671) (.n 665) 5,
  .load (.n 672) (.n 665) 6,
  .load (.n 673) (.n 665) 7,
  .load (.n 674) (.n 665) 8,
  .load (.n 675) (.n 665) 9,
  .load (.n 676) (.n 665) 10,
  .load (.n 677) (.n 665) 11,
  .load (.n 678) (.n 665) 12,
  .load (.n 679) (.n 665) 13,
  .load (.n 680) (.n 665) 14,
  .load (.n 681) (.n 665) 15,
  .load (.n 682) (.n 665) 16,
  .load (.n 683) (.n 665) 17,
  .load (.n 684) (.n 665) 18,
  .load (.n 685) (.n 665) 19,
  .load (.n 686) (.n 665) 20,
  .load (.n 687) (.n 665) 21,
  .load (.n 688) (.n 665) 22,
  .load (.n 689) (.n 665) 23,
  .load (.n 690) (.n 665) 24,
  .load (.n 691) (.n 665) 25,
  .load (.n 692) (.n 665) 26,
  .load (.n 693) (.n 665) 27,
  .load (.n 694) (.n 665) 28,
  .load (.n 695) (.n 665) 29,
  .load (.n 696) (.n 665) 30,
  .load (.n 697) (.n 665) 31,
  .load (.n 698) (.n 665) 32,
  .load (.n 699) (.n 665) 33,
  .load (.n 810) (.n 778) 1,
  .load (.n 813) (.n 15) 0,
  .load (.n 817) (.n 15) 1,
  .load (.n 838) (.n 778) 2,
  .load (.n 1303) (.n 15) 2,
  .load (.n 1317) (.n 15) 3,
  .load (.n 1868) (.n 19) 0,
  .load (.n 1884) (.n 19) 1,
  .load (.n 1892) (.n 19) 2,
  .load (.n 1900) (.n 19) 3,
  .load (.n 2606) (.n 2628) 0,
  .load (.n 2607) (.n 2628) 1,
  .load (.n 2608) (.n 2628) 2,
  .load (.n 2609) (.n 2628) 3,
  .load (.n 2610) (.n 2628) 4,
  .load (.n 2633) (.n 2628) 5,
  .load (.n 2621) (.n 2628) 6,
  .load (.n 2634) (.n 2631) 0,
  .load (.n 5979) (.n 15) 157,
  .load (.n 5982) (.n 15) 158]

set_option maxRecDepth 100000 in
/-- The counter `storesOf` carries stays unevaluated over long runs without loads: the kernel's
recursion goes deep (as `CoreNames`' checks). -/
theorem vt_stores : storesOf 21 vtEvL = vtSL := by decide +kernel

end
end LeanVM.Guest.B1.Tables
