/-
  LeanVM.Guest.B1.Bits.QueryWindowsData

  The 45 specializations of `decode_query_windows` are their template, by kernel evaluation.
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
  ⟨Data.core851, Program.find?_of_indexOf? (j := 851) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L15_L5 : QwIs "decode_query_windows__L15_L5" (qwBody 15 5) :=
  ⟨Data.core849, Program.find?_of_indexOf? (j := 849) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L16_L4 : QwIs "decode_query_windows__L16_L4" (qwBody 16 4) :=
  ⟨Data.core899, Program.find?_of_indexOf? (j := 899) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L16_L5 : QwIs "decode_query_windows__L16_L5" (qwBody 16 5) :=
  ⟨Data.core857, Program.find?_of_indexOf? (j := 857) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L16_L6 : QwIs "decode_query_windows__L16_L6" (qwBody 16 6) :=
  ⟨Data.core847, Program.find?_of_indexOf? (j := 847) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L4 : QwIs "decode_query_windows__L17_L4" (qwBody 17 4) :=
  ⟨Data.core903, Program.find?_of_indexOf? (j := 903) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L5 : QwIs "decode_query_windows__L17_L5" (qwBody 17 5) :=
  ⟨Data.core863, Program.find?_of_indexOf? (j := 863) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L6 : QwIs "decode_query_windows__L17_L6" (qwBody 17 6) :=
  ⟨Data.core855, Program.find?_of_indexOf? (j := 855) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L8 : QwIs "decode_query_windows__L17_L8" (qwBody 17 8) :=
  ⟨Data.core845, Program.find?_of_indexOf? (j := 845) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L4 : QwIs "decode_query_windows__L18_L4" (qwBody 18 4) :=
  ⟨Data.core891, Program.find?_of_indexOf? (j := 891) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L5 : QwIs "decode_query_windows__L18_L5" (qwBody 18 5) :=
  ⟨Data.core869, Program.find?_of_indexOf? (j := 869) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L6 : QwIs "decode_query_windows__L18_L6" (qwBody 18 6) :=
  ⟨Data.core861, Program.find?_of_indexOf? (j := 861) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L7 : QwIs "decode_query_windows__L18_L7" (qwBody 18 7) :=
  ⟨Data.core893, Program.find?_of_indexOf? (j := 893) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L8 : QwIs "decode_query_windows__L18_L8" (qwBody 18 8) :=
  ⟨Data.core853, Program.find?_of_indexOf? (j := 853) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L4 : QwIs "decode_query_windows__L19_L4" (qwBody 19 4) :=
  ⟨Data.core909, Program.find?_of_indexOf? (j := 909) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L5 : QwIs "decode_query_windows__L19_L5" (qwBody 19 5) :=
  ⟨Data.core875, Program.find?_of_indexOf? (j := 875) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L6 : QwIs "decode_query_windows__L19_L6" (qwBody 19 6) :=
  ⟨Data.core867, Program.find?_of_indexOf? (j := 867) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L7 : QwIs "decode_query_windows__L19_L7" (qwBody 19 7) :=
  ⟨Data.core895, Program.find?_of_indexOf? (j := 895) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L8 : QwIs "decode_query_windows__L19_L8" (qwBody 19 8) :=
  ⟨Data.core859, Program.find?_of_indexOf? (j := 859) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L4 : QwIs "decode_query_windows__L20_L4" (qwBody 20 4) :=
  ⟨Data.core917, Program.find?_of_indexOf? (j := 917) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L5 : QwIs "decode_query_windows__L20_L5" (qwBody 20 5) :=
  ⟨Data.core882, Program.find?_of_indexOf? (j := 882) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L6 : QwIs "decode_query_windows__L20_L6" (qwBody 20 6) :=
  ⟨Data.core873, Program.find?_of_indexOf? (j := 873) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L7 : QwIs "decode_query_windows__L20_L7" (qwBody 20 7) :=
  ⟨Data.core897, Program.find?_of_indexOf? (j := 897) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L8 : QwIs "decode_query_windows__L20_L8" (qwBody 20 8) :=
  ⟨Data.core865, Program.find?_of_indexOf? (j := 865) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L4 : QwIs "decode_query_windows__L21_L4" (qwBody 21 4) :=
  ⟨Data.core938, Program.find?_of_indexOf? (j := 938) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L5 : QwIs "decode_query_windows__L21_L5" (qwBody 21 5) :=
  ⟨Data.core889, Program.find?_of_indexOf? (j := 889) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L6 : QwIs "decode_query_windows__L21_L6" (qwBody 21 6) :=
  ⟨Data.core880, Program.find?_of_indexOf? (j := 880) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L7 : QwIs "decode_query_windows__L21_L7" (qwBody 21 7) :=
  ⟨Data.core901, Program.find?_of_indexOf? (j := 901) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L8 : QwIs "decode_query_windows__L21_L8" (qwBody 21 8) :=
  ⟨Data.core871, Program.find?_of_indexOf? (j := 871) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L4 : QwIs "decode_query_windows__L22_L4" (qwBody 22 4) :=
  ⟨Data.core1179, Program.find?_of_indexOf? (j := 1179) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L5 : QwIs "decode_query_windows__L22_L5" (qwBody 22 5) :=
  ⟨Data.core915, Program.find?_of_indexOf? (j := 915) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L6 : QwIs "decode_query_windows__L22_L6" (qwBody 22 6) :=
  ⟨Data.core887, Program.find?_of_indexOf? (j := 887) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L7 : QwIs "decode_query_windows__L22_L7" (qwBody 22 7) :=
  ⟨Data.core905, Program.find?_of_indexOf? (j := 905) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L8 : QwIs "decode_query_windows__L22_L8" (qwBody 22 8) :=
  ⟨Data.core877, Program.find?_of_indexOf? (j := 877) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L5 : QwIs "decode_query_windows__L23_L5" (qwBody 23 5) :=
  ⟨Data.core936, Program.find?_of_indexOf? (j := 936) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L6 : QwIs "decode_query_windows__L23_L6" (qwBody 23 6) :=
  ⟨Data.core913, Program.find?_of_indexOf? (j := 913) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L7 : QwIs "decode_query_windows__L23_L7" (qwBody 23 7) :=
  ⟨Data.core907, Program.find?_of_indexOf? (j := 907) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L8 : QwIs "decode_query_windows__L23_L8" (qwBody 23 8) :=
  ⟨Data.core884, Program.find?_of_indexOf? (j := 884) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L5 : QwIs "decode_query_windows__L24_L5" (qwBody 24 5) :=
  ⟨Data.core947, Program.find?_of_indexOf? (j := 947) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L6 : QwIs "decode_query_windows__L24_L6" (qwBody 24 6) :=
  ⟨Data.core934, Program.find?_of_indexOf? (j := 934) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L7 : QwIs "decode_query_windows__L24_L7" (qwBody 24 7) :=
  ⟨Data.core911, Program.find?_of_indexOf? (j := 911) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L5 : QwIs "decode_query_windows__L25_L5" (qwBody 25 5) :=
  ⟨Data.core951, Program.find?_of_indexOf? (j := 951) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L6 : QwIs "decode_query_windows__L25_L6" (qwBody 25 6) :=
  ⟨Data.core945, Program.find?_of_indexOf? (j := 945) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L7 : QwIs "decode_query_windows__L25_L7" (qwBody 25 7) :=
  ⟨Data.core931, Program.find?_of_indexOf? (j := 931) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L26_L6 : QwIs "decode_query_windows__L26_L6" (qwBody 26 6) :=
  ⟨Data.core949, Program.find?_of_indexOf? (j := 949) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

/-- **Every deployed specialization is its template.** -/
theorem queryWindows_data : ∀ p ∈ queryWindowsShapes, QwIs p.1 (qwBody p.2.1 p.2.2) := by
  intro p hp
  simp only [queryWindowsShapes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [qw_L14_L5, qw_L15_L5, qw_L16_L4, qw_L16_L5, qw_L16_L6, qw_L17_L4, qw_L17_L5, qw_L17_L6, qw_L17_L8, qw_L18_L4, qw_L18_L5, qw_L18_L6, qw_L18_L7, qw_L18_L8, qw_L19_L4, qw_L19_L5, qw_L19_L6, qw_L19_L7, qw_L19_L8, qw_L20_L4, qw_L20_L5, qw_L20_L6, qw_L20_L7, qw_L20_L8, qw_L21_L4, qw_L21_L5, qw_L21_L6, qw_L21_L7, qw_L21_L8, qw_L22_L4, qw_L22_L5, qw_L22_L6, qw_L22_L7, qw_L22_L8, qw_L23_L5, qw_L23_L6, qw_L23_L7, qw_L23_L8, qw_L24_L5, qw_L24_L6, qw_L24_L7, qw_L25_L5, qw_L25_L6, qw_L25_L7, qw_L26_L6]

end
end LeanVM.Guest.B1
