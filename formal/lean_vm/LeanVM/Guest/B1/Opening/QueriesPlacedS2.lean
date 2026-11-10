/-
  LeanVM.Guest.B1.Opening.QueriesPlacedS2

  A quarter of `opening_queries`' specializations, `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody2
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L16_L4` is `CompleteAtB`. -/
theorem oqD_1113 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L16_L4" "__loop622" ⟨1, 64, 12, 4⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 12, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1692
    (Program.find?_of_indexOf? (j := 1113) (by decide +kernel) rfl) rfl oqBody_1113
    (Program.find?_of_indexOf? (j := 1693) (by decide +kernel) rfl) rfl oqBody_1693

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L3` is `CompleteAtB`. -/
theorem oqD_1124 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L15_L3" "__loop626" ⟨0, 16, 12, 3⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 12, 3⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1707
    (Program.find?_of_indexOf? (j := 1124) (by decide +kernel) rfl) rfl oqBody_1124
    (Program.find?_of_indexOf? (j := 1699) (by decide +kernel) rfl) rfl oqBody_1699

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L16_L4` is `CompleteAtB`. -/
theorem oqD_1156 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L16_L4" "__loop630" ⟨1, 64, 12, 4⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 12, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1692
    (Program.find?_of_indexOf? (j := 1156) (by decide +kernel) rfl) rfl oqBody_1156
    (Program.find?_of_indexOf? (j := 1709) (by decide +kernel) rfl) rfl oqBody_1709

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L18_L6` is `CompleteAtB`. -/
theorem oqD_1198 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L18_L6" "__loop634" ⟨1, 64, 12, 6⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 12, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1719
    (Program.find?_of_indexOf? (j := 1198) (by decide +kernel) rfl) rfl oqBody_1198
    (Program.find?_of_indexOf? (j := 1720) (by decide +kernel) rfl) rfl oqBody_1720

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L2` is `CompleteAtB`. -/
theorem oqD_1236 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L20_L2" "__loop638" ⟨1, 64, 18, 2⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1737
    (Program.find?_of_indexOf? (j := 1236) (by decide +kernel) rfl) rfl oqBody_1236
    (Program.find?_of_indexOf? (j := 1730) (by decide +kernel) rfl) rfl oqBody_1730

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L2` is `CompleteAtB`. -/
theorem oqD_1277 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L20_L2" "__loop642" ⟨0, 16, 18, 2⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 18, 2⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1737
    (Program.find?_of_indexOf? (j := 1277) (by decide +kernel) rfl) rfl oqBody_1277
    (Program.find?_of_indexOf? (j := 1740) (by decide +kernel) rfl) rfl oqBody_1740

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8` is `CompleteAtB`. -/
theorem oqD_1345 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L20_L8" "__loop646" ⟨1, 64, 12, 8⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 12, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1801
    (Program.find?_of_indexOf? (j := 1345) (by decide +kernel) rfl) rfl oqBody_1345
    (Program.find?_of_indexOf? (j := 1750) (by decide +kernel) rfl) rfl oqBody_1750

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L5` is `CompleteAtB`. -/
theorem oqD_1384 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L23_L5" "__loop650" ⟨1, 64, 18, 5⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1757
    (Program.find?_of_indexOf? (j := 1384) (by decide +kernel) rfl) rfl oqBody_1384
    (Program.find?_of_indexOf? (j := 1758) (by decide +kernel) rfl) rfl oqBody_1758

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L7` is `CompleteAtB`. -/
theorem oqD_1423 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L25_L7" "__loop654" ⟨1, 64, 18, 7⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1769
    (Program.find?_of_indexOf? (j := 1423) (by decide +kernel) rfl) rfl oqBody_1423
    (Program.find?_of_indexOf? (j := 1765) (by decide +kernel) rfl) rfl oqBody_1765

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L7` is `CompleteAtB`. -/
theorem oqD_1464 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L25_L7" "__loop658" ⟨0, 16, 18, 7⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 18, 7⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1769
    (Program.find?_of_indexOf? (j := 1464) (by decide +kernel) rfl) rfl oqBody_1464
    (Program.find?_of_indexOf? (j := 1772) (by decide +kernel) rfl) rfl oqBody_1772

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L28_L4` is `CompleteAtB`. -/
theorem oqD_1545 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L28_L4" "__loop662" ⟨1, 64, 24, 4⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 24, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1782
    (Program.find?_of_indexOf? (j := 1545) (by decide +kernel) rfl) rfl oqBody_1545
    (Program.find?_of_indexOf? (j := 1783) (by decide +kernel) rfl) rfl oqBody_1783

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L28_L4` is `CompleteAtB`. -/
theorem oqD_1597 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L28_L4" "__loop666" ⟨0, 16, 24, 4⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 24, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1782
    (Program.find?_of_indexOf? (j := 1597) (by decide +kernel) rfl) rfl oqBody_1597
    (Program.find?_of_indexOf? (j := 1791) (by decide +kernel) rfl) rfl oqBody_1791

end
end LeanVM.Guest.B1
