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
/-- `opening_queries__L0_L1_L64_L32_L18_L7` is `CompleteAtB`. -/
theorem oqD_533 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L18_L7" "__loop391" ⟨1, 64, 11, 7⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 11, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_976
    (Program.find?_of_indexOf? (j := 554) (by decide +kernel) rfl) rfl oqBody_533
    (Program.find?_of_indexOf? (j := 894) (by decide +kernel) rfl) rfl oqBody_859

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L6` is `CompleteAtB`. -/
theorem oqD_692 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L20_L6" "__loop109" ⟨1, 64, 14, 6⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 14, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_969
    (Program.find?_of_indexOf? (j := 713) (by decide +kernel) rfl) rfl oqBody_692
    (Program.find?_of_indexOf? (j := 933) (by decide +kernel) rfl) rfl oqBody_884

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L7` is `CompleteAtB`. -/
theorem oqD_563 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L21_L7" "__loop395" ⟨1, 64, 14, 7⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 14, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_923
    (Program.find?_of_indexOf? (j := 584) (by decide +kernel) rfl) rfl oqBody_563
    (Program.find?_of_indexOf? (j := 902) (by decide +kernel) rfl) rfl oqBody_863

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L6` is `CompleteAtB`. -/
theorem oqD_721 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L23_L6" "__loop112" ⟨1, 64, 17, 6⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 17, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_980
    (Program.find?_of_indexOf? (j := 742) (by decide +kernel) rfl) rfl oqBody_721
    (Program.find?_of_indexOf? (j := 936) (by decide +kernel) rfl) rfl oqBody_887

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L6` is `CompleteAtB`. -/
theorem oqD_743 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L64_L32_L25_L6" "__loop114" ⟨1, 64, 19, 6⟩ 0 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 19, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 0 ≤ 1) (by decide +kernel) wpFn_986
    (Program.find?_of_indexOf? (j := 764) (by decide +kernel) rfl) rfl oqBody_743
    (Program.find?_of_indexOf? (j := 938) (by decide +kernel) rfl) rfl oqBody_889

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L7` is `CompleteAtB`. -/
theorem oqD_632 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L21_L7" "__loop406" ⟨1, 64, 14, 7⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 14, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_923
    (Program.find?_of_indexOf? (j := 653) (by decide +kernel) rfl) rfl oqBody_632
    (Program.find?_of_indexOf? (j := 924) (by decide +kernel) rfl) rfl oqBody_875

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L8` is `CompleteAtB`. -/
theorem oqD_515 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L64_L32_L23_L8" "__loop387" ⟨1, 64, 15, 8⟩ 1 :=
  oqCompleteDB1 fs cert (s := ⟨1, 64, 15, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide : 1 ≤ 1) (by decide +kernel) wpFn_885
    (Program.find?_of_indexOf? (j := 536) (by decide +kernel) rfl) rfl oqBody_515
    (Program.find?_of_indexOf? (j := 886) (by decide +kernel) rfl) rfl oqBody_855

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L5` is `CompleteAtB`. -/
theorem oqD_422 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L15_L5" "__loop105" ⟨0, 16, 10, 5⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 10, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_957
    (Program.find?_of_indexOf? (j := 443) (by decide +kernel) rfl) rfl oqBody_422
    (Program.find?_of_indexOf? (j := 927) (by decide +kernel) rfl) rfl oqBody_831

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L4` is `CompleteAtB`. -/
theorem oqD_568 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L17_L4" "__loop396" ⟨0, 16, 13, 4⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 13, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_978
    (Program.find?_of_indexOf? (j := 589) (by decide +kernel) rfl) rfl oqBody_568
    (Program.find?_of_indexOf? (j := 904) (by decide +kernel) rfl) rfl oqBody_864

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L5` is `CompleteAtB`. -/
theorem oqD_474 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L18_L5" "__loop380" ⟨0, 16, 13, 5⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 13, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_967
    (Program.find?_of_indexOf? (j := 495) (by decide +kernel) rfl) rfl oqBody_474
    (Program.find?_of_indexOf? (j := 870) (by decide +kernel) rfl) rfl oqBody_845

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L6` is `CompleteAtB`. -/
theorem oqD_471 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L19_L6" "__loop379" ⟨0, 16, 13, 6⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 13, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_966
    (Program.find?_of_indexOf? (j := 492) (by decide +kernel) rfl) rfl oqBody_471
    (Program.find?_of_indexOf? (j := 868) (by decide +kernel) rfl) rfl oqBody_844

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L4` is `CompleteAtB`. -/
theorem oqD_683 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L21_L4" "__loop108" ⟨0, 16, 17, 4⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 17, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_985
    (Program.find?_of_indexOf? (j := 704) (by decide +kernel) rfl) rfl oqBody_683
    (Program.find?_of_indexOf? (j := 932) (by decide +kernel) rfl) rfl oqBody_883

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L5` is `CompleteAtB`. -/
theorem oqD_602 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L22_L5" "__loop402" ⟨0, 16, 17, 5⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 17, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_981
    (Program.find?_of_indexOf? (j := 623) (by decide +kernel) rfl) rfl oqBody_602
    (Program.find?_of_indexOf? (j := 916) (by decide +kernel) rfl) rfl oqBody_871

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L5` is `CompleteAtB`. -/
theorem oqD_745 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L16_L24_L24_L5" "__loop115" ⟨0, 16, 19, 5⟩ 0 :=
  oqCompleteDB0 fs cert (s := ⟨0, 16, 19, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide)
    (by decide +kernel) wpFn_987
    (Program.find?_of_indexOf? (j := 766) (by decide +kernel) rfl) rfl oqBody_745
    (Program.find?_of_indexOf? (j := 939) (by decide +kernel) rfl) rfl oqBody_890

end
end LeanVM.Guest.B1
