/-
  LeanVM.Guest.B1.Opening.QueriesPlacedS3

  A quarter of `opening_queries`' specializations, `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody3
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L2` is `CompleteAtB`. -/
theorem oqD_1413 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L26_L2" "__loop544" ⟨1, 64, 24, 2⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 24, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1724
    (Program.find?_of_indexOf? (j := 1306) (by decide +kernel) rfl) rfl oqBody_1413
    (Program.find?_of_indexOf? (j := 1516) (by decide +kernel) rfl) rfl oqBody_1720

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L7` is `CompleteAtB`. -/
theorem oqD_1417 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L25_L7" "__loop545" ⟨0, 16, 18, 7⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 18, 7⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1718
    (Program.find?_of_indexOf? (j := 1310) (by decide +kernel) rfl) rfl oqBody_1417
    (Program.find?_of_indexOf? (j := 1517) (by decide +kernel) rfl) rfl oqBody_1721

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L26_L2` is `CompleteAtB`. -/
theorem oqD_1454 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L26_L2" "__loop546" ⟨1, 64, 24, 2⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 24, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1724
    (Program.find?_of_indexOf? (j := 1347) (by decide +kernel) rfl) rfl oqBody_1454
    (Program.find?_of_indexOf? (j := 1521) (by decide +kernel) rfl) rfl oqBody_1725

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L27_L3` is `CompleteAtB`. -/
theorem oqD_1455 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L27_L3" "__loop547" ⟨1, 64, 24, 3⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 24, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1726
    (Program.find?_of_indexOf? (j := 1348) (by decide +kernel) rfl) rfl oqBody_1455
    (Program.find?_of_indexOf? (j := 1523) (by decide +kernel) rfl) rfl oqBody_1727

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L26_L2` is `CompleteAtB`. -/
theorem oqD_1459 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L26_L2" "__loop548" ⟨0, 16, 24, 2⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 24, 2⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1724
    (Program.find?_of_indexOf? (j := 1352) (by decide +kernel) rfl) rfl oqBody_1459
    (Program.find?_of_indexOf? (j := 1524) (by decide +kernel) rfl) rfl oqBody_1728

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L28_L4` is `CompleteAtB`. -/
theorem oqD_1498 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L28_L4" "__loop549" ⟨1, 64, 24, 4⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 24, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1731
    (Program.find?_of_indexOf? (j := 1391) (by decide +kernel) rfl) rfl oqBody_1498
    (Program.find?_of_indexOf? (j := 1528) (by decide +kernel) rfl) rfl oqBody_1732

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L27_L3` is `CompleteAtB`. -/
theorem oqD_1502 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L27_L3" "__loop550" ⟨0, 16, 24, 3⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 24, 3⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1726
    (Program.find?_of_indexOf? (j := 1395) (by decide +kernel) rfl) rfl oqBody_1502
    (Program.find?_of_indexOf? (j := 1529) (by decide +kernel) rfl) rfl oqBody_1733

end
end LeanVM.Guest.B1
