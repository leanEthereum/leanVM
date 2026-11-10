/-
  LeanVM.Guest.B1.Bits.QueryWindowsData

  The 43 specializations of `decode_query_windows` are their template, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsT
public import LeanVM.Guest.CoreData

/-!
# `decode_query_windows`' specializations

`queryWindowsShapes`: the deployed `(name, depth, cap depth)`; `queryWindows_data`: each is found
in the core IR with the parameters `0 .. 3` and the body `qwBody d cd` (`stmtsEqb_sound`, one
kernel evaluation each).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem qw_L14_L5 : QwIs "decode_query_windows__L14_L5" (qwBody 14 5) :=
  ⟨Data.core497, Program.find?_of_indexOf? (j := 497) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L15_L5 : QwIs "decode_query_windows__L15_L5" (qwBody 15 5) :=
  ⟨Data.core492, Program.find?_of_indexOf? (j := 492) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L16_L5 : QwIs "decode_query_windows__L16_L5" (qwBody 16 5) :=
  ⟨Data.core516, Program.find?_of_indexOf? (j := 516) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L16_L6 : QwIs "decode_query_windows__L16_L6" (qwBody 16 6) :=
  ⟨Data.core486, Program.find?_of_indexOf? (j := 486) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L5 : QwIs "decode_query_windows__L17_L5" (qwBody 17 5) :=
  ⟨Data.core538, Program.find?_of_indexOf? (j := 538) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L6 : QwIs "decode_query_windows__L17_L6" (qwBody 17 6) :=
  ⟨Data.core511, Program.find?_of_indexOf? (j := 511) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L8 : QwIs "decode_query_windows__L17_L8" (qwBody 17 8) :=
  ⟨Data.core479, Program.find?_of_indexOf? (j := 479) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L4 : QwIs "decode_query_windows__L18_L4" (qwBody 18 4) :=
  ⟨Data.core626, Program.find?_of_indexOf? (j := 626) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L5 : QwIs "decode_query_windows__L18_L5" (qwBody 18 5) :=
  ⟨Data.core564, Program.find?_of_indexOf? (j := 564) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L6 : QwIs "decode_query_windows__L18_L6" (qwBody 18 6) :=
  ⟨Data.core533, Program.find?_of_indexOf? (j := 533) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L7 : QwIs "decode_query_windows__L18_L7" (qwBody 18 7) :=
  ⟨Data.core635, Program.find?_of_indexOf? (j := 635) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L8 : QwIs "decode_query_windows__L18_L8" (qwBody 18 8) :=
  ⟨Data.core506, Program.find?_of_indexOf? (j := 506) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L4 : QwIs "decode_query_windows__L19_L4" (qwBody 19 4) :=
  ⟨Data.core717, Program.find?_of_indexOf? (j := 717) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L5 : QwIs "decode_query_windows__L19_L5" (qwBody 19 5) :=
  ⟨Data.core586, Program.find?_of_indexOf? (j := 586) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L6 : QwIs "decode_query_windows__L19_L6" (qwBody 19 6) :=
  ⟨Data.core559, Program.find?_of_indexOf? (j := 559) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L7 : QwIs "decode_query_windows__L19_L7" (qwBody 19 7) :=
  ⟨Data.core646, Program.find?_of_indexOf? (j := 646) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L8 : QwIs "decode_query_windows__L19_L8" (qwBody 19 8) :=
  ⟨Data.core528, Program.find?_of_indexOf? (j := 528) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L4 : QwIs "decode_query_windows__L20_L4" (qwBody 20 4) :=
  ⟨Data.core714, Program.find?_of_indexOf? (j := 714) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L5 : QwIs "decode_query_windows__L20_L5" (qwBody 20 5) :=
  ⟨Data.core604, Program.find?_of_indexOf? (j := 604) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L6 : QwIs "decode_query_windows__L20_L6" (qwBody 20 6) :=
  ⟨Data.core583, Program.find?_of_indexOf? (j := 583) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L7 : QwIs "decode_query_windows__L20_L7" (qwBody 20 7) :=
  ⟨Data.core656, Program.find?_of_indexOf? (j := 656) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L8 : QwIs "decode_query_windows__L20_L8" (qwBody 20 8) :=
  ⟨Data.core554, Program.find?_of_indexOf? (j := 554) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L4 : QwIs "decode_query_windows__L21_L4" (qwBody 21 4) :=
  ⟨Data.core791, Program.find?_of_indexOf? (j := 791) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L5 : QwIs "decode_query_windows__L21_L5" (qwBody 21 5) :=
  ⟨Data.core621, Program.find?_of_indexOf? (j := 621) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L6 : QwIs "decode_query_windows__L21_L6" (qwBody 21 6) :=
  ⟨Data.core601, Program.find?_of_indexOf? (j := 601) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L7 : QwIs "decode_query_windows__L21_L7" (qwBody 21 7) :=
  ⟨Data.core668, Program.find?_of_indexOf? (j := 668) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L8 : QwIs "decode_query_windows__L21_L8" (qwBody 21 8) :=
  ⟨Data.core580, Program.find?_of_indexOf? (j := 580) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L4 : QwIs "decode_query_windows__L22_L4" (qwBody 22 4) :=
  ⟨Data.core874, Program.find?_of_indexOf? (j := 874) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L5 : QwIs "decode_query_windows__L22_L5" (qwBody 22 5) :=
  ⟨Data.core710, Program.find?_of_indexOf? (j := 710) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L6 : QwIs "decode_query_windows__L22_L6" (qwBody 22 6) :=
  ⟨Data.core618, Program.find?_of_indexOf? (j := 618) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L7 : QwIs "decode_query_windows__L22_L7" (qwBody 22 7) :=
  ⟨Data.core680, Program.find?_of_indexOf? (j := 680) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L8 : QwIs "decode_query_windows__L22_L8" (qwBody 22 8) :=
  ⟨Data.core598, Program.find?_of_indexOf? (j := 598) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L5 : QwIs "decode_query_windows__L23_L5" (qwBody 23 5) :=
  ⟨Data.core787, Program.find?_of_indexOf? (j := 787) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L6 : QwIs "decode_query_windows__L23_L6" (qwBody 23 6) :=
  ⟨Data.core707, Program.find?_of_indexOf? (j := 707) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L7 : QwIs "decode_query_windows__L23_L7" (qwBody 23 7) :=
  ⟨Data.core692, Program.find?_of_indexOf? (j := 692) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L8 : QwIs "decode_query_windows__L23_L8" (qwBody 23 8) :=
  ⟨Data.core615, Program.find?_of_indexOf? (j := 615) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L5 : QwIs "decode_query_windows__L24_L5" (qwBody 24 5) :=
  ⟨Data.core855, Program.find?_of_indexOf? (j := 855) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L6 : QwIs "decode_query_windows__L24_L6" (qwBody 24 6) :=
  ⟨Data.core784, Program.find?_of_indexOf? (j := 784) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L7 : QwIs "decode_query_windows__L24_L7" (qwBody 24 7) :=
  ⟨Data.core704, Program.find?_of_indexOf? (j := 704) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L5 : QwIs "decode_query_windows__L25_L5" (qwBody 25 5) :=
  ⟨Data.core869, Program.find?_of_indexOf? (j := 869) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L6 : QwIs "decode_query_windows__L25_L6" (qwBody 25 6) :=
  ⟨Data.core852, Program.find?_of_indexOf? (j := 852) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L7 : QwIs "decode_query_windows__L25_L7" (qwBody 25 7) :=
  ⟨Data.core781, Program.find?_of_indexOf? (j := 781) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L26_L6 : QwIs "decode_query_windows__L26_L6" (qwBody 26 6) :=
  ⟨Data.core866, Program.find?_of_indexOf? (j := 866) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

/-- **Every deployed specialization is its template.** -/
theorem queryWindows_data : ∀ p ∈ queryWindowsShapes, QwIs p.1 (qwBody p.2.1 p.2.2) := by
  intro p hp
  simp only [queryWindowsShapes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [qw_L14_L5, qw_L15_L5, qw_L16_L5, qw_L16_L6, qw_L17_L5, qw_L17_L6, qw_L17_L8, qw_L18_L4, qw_L18_L5, qw_L18_L6, qw_L18_L7, qw_L18_L8, qw_L19_L4, qw_L19_L5, qw_L19_L6, qw_L19_L7, qw_L19_L8, qw_L20_L4, qw_L20_L5, qw_L20_L6, qw_L20_L7, qw_L20_L8, qw_L21_L4, qw_L21_L5, qw_L21_L6, qw_L21_L7, qw_L21_L8, qw_L22_L4, qw_L22_L5, qw_L22_L6, qw_L22_L7, qw_L22_L8, qw_L23_L5, qw_L23_L6, qw_L23_L7, qw_L23_L8, qw_L24_L5, qw_L24_L6, qw_L24_L7, qw_L25_L5, qw_L25_L6, qw_L25_L7, qw_L26_L6]

end
end LeanVM.Guest.B1
