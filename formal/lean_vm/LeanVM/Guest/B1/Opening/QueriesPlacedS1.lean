/-
  LeanVM.Guest.B1.Opening.QueriesPlacedS1

  A quarter of `opening_queries`' specializations, `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody1
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L15_L3` is `CompleteAtB`. -/
theorem oqD_1111 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L15_L3" "__loop621" ⟨1, 64, 12, 3⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 12, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1707
    (Program.find?_of_indexOf? (j := 1111) (by decide +kernel) rfl) rfl oqBody_1111
    (Program.find?_of_indexOf? (j := 1691) (by decide +kernel) rfl) rfl oqBody_1691

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L2` is `CompleteAtB`. -/
theorem oqD_1123 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L14_L2" "__loop625" ⟨0, 16, 12, 2⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 12, 2⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1799
    (Program.find?_of_indexOf? (j := 1123) (by decide +kernel) rfl) rfl oqBody_1123
    (Program.find?_of_indexOf? (j := 1698) (by decide +kernel) rfl) rfl oqBody_1698

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L15_L3` is `CompleteAtB`. -/
theorem oqD_1155 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L15_L3" "__loop629" ⟨1, 64, 12, 3⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 12, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1707
    (Program.find?_of_indexOf? (j := 1155) (by decide +kernel) rfl) rfl oqBody_1155
    (Program.find?_of_indexOf? (j := 1708) (by decide +kernel) rfl) rfl oqBody_1708

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5` is `CompleteAtB`. -/
theorem oqD_1162 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L17_L5" "__loop633" ⟨0, 16, 12, 5⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 12, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1710
    (Program.find?_of_indexOf? (j := 1162) (by decide +kernel) rfl) rfl oqBody_1162
    (Program.find?_of_indexOf? (j := 1713) (by decide +kernel) rfl) rfl oqBody_1713

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7` is `CompleteAtB`. -/
theorem oqD_1235 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L19_L7" "__loop637" ⟨1, 64, 12, 7⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1728
    (Program.find?_of_indexOf? (j := 1235) (by decide +kernel) rfl) rfl oqBody_1235
    (Program.find?_of_indexOf? (j := 1729) (by decide +kernel) rfl) rfl oqBody_1729

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L3` is `CompleteAtB`. -/
theorem oqD_1274 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L21_L3" "__loop641" ⟨1, 64, 18, 3⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1743
    (Program.find?_of_indexOf? (j := 1274) (by decide +kernel) rfl) rfl oqBody_1274
    (Program.find?_of_indexOf? (j := 1739) (by decide +kernel) rfl) rfl oqBody_1739

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L3` is `CompleteAtB`. -/
theorem oqD_1311 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L21_L3" "__loop645" ⟨0, 16, 18, 3⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 18, 3⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1743
    (Program.find?_of_indexOf? (j := 1311) (by decide +kernel) rfl) rfl oqBody_1311
    (Program.find?_of_indexOf? (j := 1746) (by decide +kernel) rfl) rfl oqBody_1746

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4` is `CompleteAtB`. -/
theorem oqD_1350 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L22_L4" "__loop649" ⟨0, 16, 18, 4⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 18, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1751
    (Program.find?_of_indexOf? (j := 1350) (by decide +kernel) rfl) rfl oqBody_1350
    (Program.find?_of_indexOf? (j := 1754) (by decide +kernel) rfl) rfl oqBody_1754

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L6` is `CompleteAtB`. -/
theorem oqD_1422 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L24_L6" "__loop653" ⟨1, 64, 18, 6⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1763
    (Program.find?_of_indexOf? (j := 1422) (by decide +kernel) rfl) rfl oqBody_1422
    (Program.find?_of_indexOf? (j := 1764) (by decide +kernel) rfl) rfl oqBody_1764

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L2` is `CompleteAtB`. -/
theorem oqD_1460 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L26_L2" "__loop657" ⟨1, 64, 24, 2⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 24, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1775
    (Program.find?_of_indexOf? (j := 1460) (by decide +kernel) rfl) rfl oqBody_1460
    (Program.find?_of_indexOf? (j := 1771) (by decide +kernel) rfl) rfl oqBody_1771

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L26_L2` is `CompleteAtB`. -/
theorem oqD_1506 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L26_L2" "__loop661" ⟨0, 16, 24, 2⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 24, 2⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1775
    (Program.find?_of_indexOf? (j := 1506) (by decide +kernel) rfl) rfl oqBody_1506
    (Program.find?_of_indexOf? (j := 1779) (by decide +kernel) rfl) rfl oqBody_1779

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L29_L5` is `CompleteAtB`. -/
theorem oqD_1593 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L29_L5" "__loop665" ⟨1, 64, 24, 5⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 24, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1789
    (Program.find?_of_indexOf? (j := 1593) (by decide +kernel) rfl) rfl oqBody_1593
    (Program.find?_of_indexOf? (j := 1790) (by decide +kernel) rfl) rfl oqBody_1790

end
end LeanVM.Guest.B1
