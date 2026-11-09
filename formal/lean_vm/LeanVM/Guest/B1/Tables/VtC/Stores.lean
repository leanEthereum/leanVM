/-
  LeanVM.Guest.B1.Tables.VtC.Stores

  The stores of `verify_tables`' evaluation list (generated: scripts/b1c-vt/genstores.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Flat

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The 112 stores of `vtEvL`, in order. -/
def vtSL : List Atom := [
  .load (.n 41) (.n 36) 0,
  .load (.n 43) (.n 37) 0,
  .load (.n 47) (.n 36) 1,
  .load (.n 49) (.n 37) 1,
  .load (.n 55) (.n 36) 2,
  .load (.n 57) (.n 37) 2,
  .load (.n 61) (.n 36) 3,
  .load (.n 66) (.n 37) 3,
  .load (.n 70) (.n 36) 4,
  .load (.n 75) (.n 37) 4,
  .load (.n 79) (.n 36) 5,
  .load (.n 83) (.n 37) 5,
  .load (.n 87) (.n 36) 6,
  .load (.n 92) (.n 37) 6,
  .load (.n 96) (.n 36) 7,
  .load (.n 101) (.n 37) 7,
  .load (.n 105) (.n 36) 8,
  .load (.n 113) (.n 37) 8,
  .load (.n 119) (.n 120) 212,
  .load (.n 123) (.n 124) 0,
  .load (.n 132) (.n 133) 212,
  .load (.n 126) (.n 143) 0,
  .load (.n 152) (.n 153) 212,
  .load (.n 146) (.n 163) 0,
  .load (.n 172) (.n 173) 212,
  .load (.n 166) (.n 183) 0,
  .load (.n 192) (.n 193) 212,
  .load (.n 186) (.n 203) 0,
  .load (.n 212) (.n 213) 212,
  .load (.n 206) (.n 223) 0,
  .load (.n 232) (.n 233) 212,
  .load (.n 226) (.n 243) 0,
  .load (.n 252) (.n 253) 212,
  .load (.n 246) (.n 263) 0,
  .load (.n 272) (.n 273) 212,
  .load (.n 266) (.n 283) 0,
  .load (.n 362) (.n 36) 18,
  .load (.n 366) (.n 37) 18,
  .load (.n 370) (.n 36) 19,
  .load (.n 374) (.n 37) 19,
  .load (.n 378) (.n 36) 20,
  .load (.n 381) (.n 37) 20,
  .load (.n 385) (.n 36) 21,
  .load (.n 389) (.n 37) 21,
  .load (.n 393) (.n 36) 22,
  .load (.n 397) (.n 37) 22,
  .load (.n 401) (.n 36) 23,
  .load (.n 410) (.n 37) 23,
  .load (.n 416) (.n 417) 212,
  .load (.n 420) (.n 421) 0,
  .load (.n 429) (.n 430) 212,
  .load (.n 423) (.n 440) 0,
  .load (.n 449) (.n 450) 212,
  .load (.n 443) (.n 460) 0,
  .load (.n 469) (.n 470) 212,
  .load (.n 463) (.n 480) 0,
  .load (.n 489) (.n 490) 212,
  .load (.n 483) (.n 500) 0,
  .load (.n 509) (.n 510) 212,
  .load (.n 503) (.n 520) 0,
  .load (.n 669) (.n 668) 0,
  .load (.n 670) (.n 668) 1,
  .load (.n 671) (.n 668) 2,
  .load (.n 672) (.n 668) 3,
  .load (.n 673) (.n 668) 4,
  .load (.n 674) (.n 668) 5,
  .load (.n 675) (.n 668) 6,
  .load (.n 676) (.n 668) 7,
  .load (.n 677) (.n 668) 8,
  .load (.n 678) (.n 668) 9,
  .load (.n 679) (.n 668) 10,
  .load (.n 680) (.n 668) 11,
  .load (.n 681) (.n 668) 12,
  .load (.n 682) (.n 668) 13,
  .load (.n 683) (.n 668) 14,
  .load (.n 684) (.n 668) 15,
  .load (.n 685) (.n 668) 16,
  .load (.n 686) (.n 668) 17,
  .load (.n 687) (.n 668) 18,
  .load (.n 688) (.n 668) 19,
  .load (.n 689) (.n 668) 20,
  .load (.n 690) (.n 668) 21,
  .load (.n 691) (.n 668) 22,
  .load (.n 692) (.n 668) 23,
  .load (.n 693) (.n 668) 24,
  .load (.n 694) (.n 668) 25,
  .load (.n 695) (.n 668) 26,
  .load (.n 696) (.n 668) 27,
  .load (.n 697) (.n 668) 28,
  .load (.n 698) (.n 668) 29,
  .load (.n 699) (.n 668) 30,
  .load (.n 700) (.n 668) 31,
  .load (.n 701) (.n 668) 32,
  .load (.n 702) (.n 668) 33,
  .load (.n 824) (.n 781) 1,
  .load (.n 830) (.n 15) 0,
  .load (.n 843) (.n 15) 1,
  .load (.n 856) (.n 15) 2,
  .load (.n 894) (.n 781) 2,
  .load (.n 1843) (.n 15) 3,
  .load (.n 1898) (.n 15) 4,
  .load (.n 2577) (.n 2605) 0,
  .load (.n 2578) (.n 2605) 1,
  .load (.n 2579) (.n 2605) 2,
  .load (.n 2580) (.n 2605) 3,
  .load (.n 2581) (.n 2605) 4,
  .load (.n 2610) (.n 2605) 5,
  .load (.n 2598) (.n 2605) 6,
  .load (.n 2611) (.n 2608) 0,
  .load (.n 6956) (.n 15) 164,
  .load (.n 6959) (.n 15) 165,
  .load (.n 6960) (.n 15) 166]

set_option maxRecDepth 100000 in
/-- The counter `storesOf` carries stays unevaluated over long runs without loads: the kernel's
recursion goes deep (as `CoreNames`' checks). -/
theorem vt_stores : storesOf 20 vtEvL = vtSL := by decide +kernel

end
end LeanVM.Guest.B1.Tables
