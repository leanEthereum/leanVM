/-
  LeanVM.Guest.B1.Bits.QueryWindowsData

  The 21 specializations of `decode_query_windows` are their template, by kernel evaluation.
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
theorem qw_L12_L6 : QwIs "decode_query_windows__L12_L6" (qwBody 12 6) :=
  ⟨Data.core1655, Program.find?_of_indexOf? (j := 1655) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L13_L7 : QwIs "decode_query_windows__L13_L7" (qwBody 13 7) :=
  ⟨Data.core1653, Program.find?_of_indexOf? (j := 1653) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L14_L2 : QwIs "decode_query_windows__L14_L2" (qwBody 14 2) :=
  ⟨Data.core1648, Program.find?_of_indexOf? (j := 1648) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L15_L3 : QwIs "decode_query_windows__L15_L3" (qwBody 15 3) :=
  ⟨Data.core1638, Program.find?_of_indexOf? (j := 1638) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L16_L4 : QwIs "decode_query_windows__L16_L4" (qwBody 16 4) :=
  ⟨Data.core1639, Program.find?_of_indexOf? (j := 1639) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L5 : QwIs "decode_query_windows__L17_L5" (qwBody 17 5) :=
  ⟨Data.core1640, Program.find?_of_indexOf? (j := 1640) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L6 : QwIs "decode_query_windows__L18_L6" (qwBody 18 6) :=
  ⟨Data.core1641, Program.find?_of_indexOf? (j := 1641) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L7 : QwIs "decode_query_windows__L19_L7" (qwBody 19 7) :=
  ⟨Data.core1661, Program.find?_of_indexOf? (j := 1661) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L2 : QwIs "decode_query_windows__L20_L2" (qwBody 20 2) :=
  ⟨Data.core1673, Program.find?_of_indexOf? (j := 1673) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L8 : QwIs "decode_query_windows__L20_L8" (qwBody 20 8) :=
  ⟨Data.core1697, Program.find?_of_indexOf? (j := 1697) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L3 : QwIs "decode_query_windows__L21_L3" (qwBody 21 3) :=
  ⟨Data.core1682, Program.find?_of_indexOf? (j := 1682) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L4 : QwIs "decode_query_windows__L22_L4" (qwBody 22 4) :=
  ⟨Data.core1691, Program.find?_of_indexOf? (j := 1691) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L5 : QwIs "decode_query_windows__L23_L5" (qwBody 23 5) :=
  ⟨Data.core1698, Program.find?_of_indexOf? (j := 1698) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L6 : QwIs "decode_query_windows__L24_L6" (qwBody 24 6) :=
  ⟨Data.core1705, Program.find?_of_indexOf? (j := 1705) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L7 : QwIs "decode_query_windows__L25_L7" (qwBody 25 7) :=
  ⟨Data.core1711, Program.find?_of_indexOf? (j := 1711) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L26_L2 : QwIs "decode_query_windows__L26_L2" (qwBody 26 2) :=
  ⟨Data.core1717, Program.find?_of_indexOf? (j := 1717) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L26_L8 : QwIs "decode_query_windows__L26_L8" (qwBody 26 8) :=
  ⟨Data.core1735, Program.find?_of_indexOf? (j := 1735) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L27_L3 : QwIs "decode_query_windows__L27_L3" (qwBody 27 3) :=
  ⟨Data.core1723, Program.find?_of_indexOf? (j := 1723) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L28_L4 : QwIs "decode_query_windows__L28_L4" (qwBody 28 4) :=
  ⟨Data.core1730, Program.find?_of_indexOf? (j := 1730) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L29_L5 : QwIs "decode_query_windows__L29_L5" (qwBody 29 5) :=
  ⟨Data.core1736, Program.find?_of_indexOf? (j := 1736) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L30_L6 : QwIs "decode_query_windows__L30_L6" (qwBody 30 6) :=
  ⟨Data.core1742, Program.find?_of_indexOf? (j := 1742) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

/-- **Every deployed specialization is its template.** -/
theorem queryWindows_data : ∀ p ∈ queryWindowsShapes, QwIs p.1 (qwBody p.2.1 p.2.2) := by
  intro p hp
  simp only [queryWindowsShapes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [qw_L12_L6, qw_L13_L7, qw_L14_L2, qw_L15_L3, qw_L16_L4, qw_L17_L5, qw_L18_L6, qw_L19_L7, qw_L20_L2, qw_L20_L8, qw_L21_L3, qw_L22_L4, qw_L23_L5, qw_L24_L6, qw_L25_L7, qw_L26_L2, qw_L26_L8, qw_L27_L3, qw_L28_L4, qw_L29_L5, qw_L30_L6]

end
end LeanVM.Guest.B1
