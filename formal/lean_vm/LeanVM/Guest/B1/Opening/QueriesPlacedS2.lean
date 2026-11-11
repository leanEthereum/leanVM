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
/-- `opening_queries__L0_L0_L16_L24_L21_L3` is `CompleteAtB`. -/
theorem oqD_1263 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L21_L3" "__loop532" ⟨0, 16, 18, 3⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 18, 3⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1692
    (Program.find?_of_indexOf? (j := 1156) (by decide +kernel) rfl) rfl oqBody_1263
    (Program.find?_of_indexOf? (j := 1491) (by decide +kernel) rfl) rfl oqBody_1695

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8` is `CompleteAtB`. -/
theorem oqD_1298 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L20_L8" "__loop533" ⟨1, 64, 12, 8⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 12, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1750
    (Program.find?_of_indexOf? (j := 1191) (by decide +kernel) rfl) rfl oqBody_1298
    (Program.find?_of_indexOf? (j := 1495) (by decide +kernel) rfl) rfl oqBody_1699

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L4` is `CompleteAtB`. -/
theorem oqD_1299 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L22_L4" "__loop534" ⟨1, 64, 18, 4⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1700
    (Program.find?_of_indexOf? (j := 1192) (by decide +kernel) rfl) rfl oqBody_1299
    (Program.find?_of_indexOf? (j := 1497) (by decide +kernel) rfl) rfl oqBody_1701

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L5` is `CompleteAtB`. -/
theorem oqD_1300 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L23_L5" "__loop535" ⟨1, 64, 18, 5⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1706
    (Program.find?_of_indexOf? (j := 1193) (by decide +kernel) rfl) rfl oqBody_1300
    (Program.find?_of_indexOf? (j := 1498) (by decide +kernel) rfl) rfl oqBody_1702

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4` is `CompleteAtB`. -/
theorem oqD_1303 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L22_L4" "__loop536" ⟨0, 16, 18, 4⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 18, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1700
    (Program.find?_of_indexOf? (j := 1196) (by decide +kernel) rfl) rfl oqBody_1303
    (Program.find?_of_indexOf? (j := 1499) (by decide +kernel) rfl) rfl oqBody_1703

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L5` is `CompleteAtB`. -/
theorem oqD_1337 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L23_L5" "__loop537" ⟨1, 64, 18, 5⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1706
    (Program.find?_of_indexOf? (j := 1230) (by decide +kernel) rfl) rfl oqBody_1337
    (Program.find?_of_indexOf? (j := 1503) (by decide +kernel) rfl) rfl oqBody_1707

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6` is `CompleteAtB`. -/
theorem oqD_1338 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L24_L6" "__loop538" ⟨1, 64, 18, 6⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1712
    (Program.find?_of_indexOf? (j := 1231) (by decide +kernel) rfl) rfl oqBody_1338
    (Program.find?_of_indexOf? (j := 1504) (by decide +kernel) rfl) rfl oqBody_1708

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5` is `CompleteAtB`. -/
theorem oqD_1341 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L23_L5" "__loop539" ⟨0, 16, 18, 5⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 18, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1706
    (Program.find?_of_indexOf? (j := 1234) (by decide +kernel) rfl) rfl oqBody_1341
    (Program.find?_of_indexOf? (j := 1505) (by decide +kernel) rfl) rfl oqBody_1709

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L6` is `CompleteAtB`. -/
theorem oqD_1375 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L24_L6" "__loop540" ⟨1, 64, 18, 6⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1712
    (Program.find?_of_indexOf? (j := 1268) (by decide +kernel) rfl) rfl oqBody_1375
    (Program.find?_of_indexOf? (j := 1509) (by decide +kernel) rfl) rfl oqBody_1713

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L7` is `CompleteAtB`. -/
theorem oqD_1376 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L25_L7" "__loop541" ⟨1, 64, 18, 7⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_1718
    (Program.find?_of_indexOf? (j := 1269) (by decide +kernel) rfl) rfl oqBody_1376
    (Program.find?_of_indexOf? (j := 1510) (by decide +kernel) rfl) rfl oqBody_1714

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6` is `CompleteAtB`. -/
theorem oqD_1380 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L24_L6" "__loop542" ⟨0, 16, 18, 6⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 18, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_1712
    (Program.find?_of_indexOf? (j := 1273) (by decide +kernel) rfl) rfl oqBody_1380
    (Program.find?_of_indexOf? (j := 1511) (by decide +kernel) rfl) rfl oqBody_1715

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7` is `CompleteAtB`. -/
theorem oqD_1412 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L25_L7" "__loop543" ⟨1, 64, 18, 7⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 18, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_1718
    (Program.find?_of_indexOf? (j := 1305) (by decide +kernel) rfl) rfl oqBody_1412
    (Program.find?_of_indexOf? (j := 1515) (by decide +kernel) rfl) rfl oqBody_1719

end
end LeanVM.Guest.B1
