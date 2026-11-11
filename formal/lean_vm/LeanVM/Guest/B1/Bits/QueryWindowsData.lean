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
  ⟨Data.core494, Program.find?_of_indexOf? (j := 494) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L15_L5 : QwIs "decode_query_windows__L15_L5" (qwBody 15 5) :=
  ⟨Data.core489, Program.find?_of_indexOf? (j := 489) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L16_L5 : QwIs "decode_query_windows__L16_L5" (qwBody 16 5) :=
  ⟨Data.core510, Program.find?_of_indexOf? (j := 510) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L16_L6 : QwIs "decode_query_windows__L16_L6" (qwBody 16 6) :=
  ⟨Data.core484, Program.find?_of_indexOf? (j := 484) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L5 : QwIs "decode_query_windows__L17_L5" (qwBody 17 5) :=
  ⟨Data.core529, Program.find?_of_indexOf? (j := 529) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L6 : QwIs "decode_query_windows__L17_L6" (qwBody 17 6) :=
  ⟨Data.core506, Program.find?_of_indexOf? (j := 506) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L8 : QwIs "decode_query_windows__L17_L8" (qwBody 17 8) :=
  ⟨Data.core478, Program.find?_of_indexOf? (j := 478) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L4 : QwIs "decode_query_windows__L18_L4" (qwBody 18 4) :=
  ⟨Data.core608, Program.find?_of_indexOf? (j := 608) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L5 : QwIs "decode_query_windows__L18_L5" (qwBody 18 5) :=
  ⟨Data.core550, Program.find?_of_indexOf? (j := 550) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L6 : QwIs "decode_query_windows__L18_L6" (qwBody 18 6) :=
  ⟨Data.core525, Program.find?_of_indexOf? (j := 525) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L7 : QwIs "decode_query_windows__L18_L7" (qwBody 18 7) :=
  ⟨Data.core617, Program.find?_of_indexOf? (j := 617) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L8 : QwIs "decode_query_windows__L18_L8" (qwBody 18 8) :=
  ⟨Data.core502, Program.find?_of_indexOf? (j := 502) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L4 : QwIs "decode_query_windows__L19_L4" (qwBody 19 4) :=
  ⟨Data.core699, Program.find?_of_indexOf? (j := 699) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L5 : QwIs "decode_query_windows__L19_L5" (qwBody 19 5) :=
  ⟨Data.core570, Program.find?_of_indexOf? (j := 570) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L6 : QwIs "decode_query_windows__L19_L6" (qwBody 19 6) :=
  ⟨Data.core546, Program.find?_of_indexOf? (j := 546) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L7 : QwIs "decode_query_windows__L19_L7" (qwBody 19 7) :=
  ⟨Data.core628, Program.find?_of_indexOf? (j := 628) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L8 : QwIs "decode_query_windows__L19_L8" (qwBody 19 8) :=
  ⟨Data.core521, Program.find?_of_indexOf? (j := 521) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L4 : QwIs "decode_query_windows__L20_L4" (qwBody 20 4) :=
  ⟨Data.core696, Program.find?_of_indexOf? (j := 696) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L5 : QwIs "decode_query_windows__L20_L5" (qwBody 20 5) :=
  ⟨Data.core587, Program.find?_of_indexOf? (j := 587) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L6 : QwIs "decode_query_windows__L20_L6" (qwBody 20 6) :=
  ⟨Data.core567, Program.find?_of_indexOf? (j := 567) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L7 : QwIs "decode_query_windows__L20_L7" (qwBody 20 7) :=
  ⟨Data.core638, Program.find?_of_indexOf? (j := 638) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L8 : QwIs "decode_query_windows__L20_L8" (qwBody 20 8) :=
  ⟨Data.core542, Program.find?_of_indexOf? (j := 542) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L4 : QwIs "decode_query_windows__L21_L4" (qwBody 21 4) :=
  ⟨Data.core773, Program.find?_of_indexOf? (j := 773) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L5 : QwIs "decode_query_windows__L21_L5" (qwBody 21 5) :=
  ⟨Data.core603, Program.find?_of_indexOf? (j := 603) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L6 : QwIs "decode_query_windows__L21_L6" (qwBody 21 6) :=
  ⟨Data.core584, Program.find?_of_indexOf? (j := 584) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L7 : QwIs "decode_query_windows__L21_L7" (qwBody 21 7) :=
  ⟨Data.core650, Program.find?_of_indexOf? (j := 650) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L8 : QwIs "decode_query_windows__L21_L8" (qwBody 21 8) :=
  ⟨Data.core564, Program.find?_of_indexOf? (j := 564) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L4 : QwIs "decode_query_windows__L22_L4" (qwBody 22 4) :=
  ⟨Data.core856, Program.find?_of_indexOf? (j := 856) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L5 : QwIs "decode_query_windows__L22_L5" (qwBody 22 5) :=
  ⟨Data.core692, Program.find?_of_indexOf? (j := 692) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L6 : QwIs "decode_query_windows__L22_L6" (qwBody 22 6) :=
  ⟨Data.core600, Program.find?_of_indexOf? (j := 600) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L7 : QwIs "decode_query_windows__L22_L7" (qwBody 22 7) :=
  ⟨Data.core662, Program.find?_of_indexOf? (j := 662) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L8 : QwIs "decode_query_windows__L22_L8" (qwBody 22 8) :=
  ⟨Data.core581, Program.find?_of_indexOf? (j := 581) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L5 : QwIs "decode_query_windows__L23_L5" (qwBody 23 5) :=
  ⟨Data.core769, Program.find?_of_indexOf? (j := 769) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L6 : QwIs "decode_query_windows__L23_L6" (qwBody 23 6) :=
  ⟨Data.core689, Program.find?_of_indexOf? (j := 689) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L7 : QwIs "decode_query_windows__L23_L7" (qwBody 23 7) :=
  ⟨Data.core674, Program.find?_of_indexOf? (j := 674) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L8 : QwIs "decode_query_windows__L23_L8" (qwBody 23 8) :=
  ⟨Data.core597, Program.find?_of_indexOf? (j := 597) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L5 : QwIs "decode_query_windows__L24_L5" (qwBody 24 5) :=
  ⟨Data.core837, Program.find?_of_indexOf? (j := 837) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L6 : QwIs "decode_query_windows__L24_L6" (qwBody 24 6) :=
  ⟨Data.core766, Program.find?_of_indexOf? (j := 766) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L7 : QwIs "decode_query_windows__L24_L7" (qwBody 24 7) :=
  ⟨Data.core686, Program.find?_of_indexOf? (j := 686) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L5 : QwIs "decode_query_windows__L25_L5" (qwBody 25 5) :=
  ⟨Data.core851, Program.find?_of_indexOf? (j := 851) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L6 : QwIs "decode_query_windows__L25_L6" (qwBody 25 6) :=
  ⟨Data.core834, Program.find?_of_indexOf? (j := 834) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L7 : QwIs "decode_query_windows__L25_L7" (qwBody 25 7) :=
  ⟨Data.core763, Program.find?_of_indexOf? (j := 763) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L26_L6 : QwIs "decode_query_windows__L26_L6" (qwBody 26 6) :=
  ⟨Data.core848, Program.find?_of_indexOf? (j := 848) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

/-- **Every deployed specialization is its template.** -/
theorem queryWindows_data : ∀ p ∈ queryWindowsShapes, QwIs p.1 (qwBody p.2.1 p.2.2) := by
  intro p hp
  simp only [queryWindowsShapes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [qw_L14_L5, qw_L15_L5, qw_L16_L5, qw_L16_L6, qw_L17_L5, qw_L17_L6, qw_L17_L8, qw_L18_L4, qw_L18_L5, qw_L18_L6, qw_L18_L7, qw_L18_L8, qw_L19_L4, qw_L19_L5, qw_L19_L6, qw_L19_L7, qw_L19_L8, qw_L20_L4, qw_L20_L5, qw_L20_L6, qw_L20_L7, qw_L20_L8, qw_L21_L4, qw_L21_L5, qw_L21_L6, qw_L21_L7, qw_L21_L8, qw_L22_L4, qw_L22_L5, qw_L22_L6, qw_L22_L7, qw_L22_L8, qw_L23_L5, qw_L23_L6, qw_L23_L7, qw_L23_L8, qw_L24_L5, qw_L24_L6, qw_L24_L7, qw_L25_L5, qw_L25_L6, qw_L25_L7, qw_L26_L6]

end
end LeanVM.Guest.B1
