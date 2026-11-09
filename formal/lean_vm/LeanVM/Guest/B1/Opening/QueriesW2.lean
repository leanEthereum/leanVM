/-
  LeanVM.Guest.B1.Opening.QueriesW2

  A quarter of `opening_queries`' specializations, sound with their queries named.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody2
public import LeanVM.Guest.B1.Opening.QueriesMainW
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L8` is sound with its queries named. -/
theorem oqSpecW_433 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L18_L8" "__loop372" ⟨1, 64, 10, 8⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 10, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_959)
    (Program.find?_of_indexOf? (j := 454) (by decide +kernel) rfl) rfl oqBody_433
    (Program.find?_of_indexOf? (j := 854) (by decide +kernel) rfl) rfl oqBody_835

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L7` is sound with its queries named. -/
theorem oqSpecW_551 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L20_L7" "__loop393" ⟨1, 64, 13, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 13, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_921)
    (Program.find?_of_indexOf? (j := 572) (by decide +kernel) rfl) rfl oqBody_551
    (Program.find?_of_indexOf? (j := 898) (by decide +kernel) rfl) rfl oqBody_861

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L8` is sound with its queries named. -/
theorem oqSpecW_487 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L21_L8" "__loop381" ⟨1, 64, 13, 8⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 13, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_968)
    (Program.find?_of_indexOf? (j := 508) (by decide +kernel) rfl) rfl oqBody_487
    (Program.find?_of_indexOf? (j := 872) (by decide +kernel) rfl) rfl oqBody_847

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L7` is sound with its queries named. -/
theorem oqSpecW_586 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L23_L7" "__loop398" ⟨1, 64, 16, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 16, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_927)
    (Program.find?_of_indexOf? (j := 607) (by decide +kernel) rfl) rfl oqBody_586
    (Program.find?_of_indexOf? (j := 908) (by decide +kernel) rfl) rfl oqBody_866

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L6` is sound with its queries named. -/
theorem oqSpecW_755 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L26_L6" "__loop421" ⟨1, 64, 20, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 20, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_988)
    (Program.find?_of_indexOf? (j := 776) (by decide +kernel) rfl) rfl oqBody_755
    (Program.find?_of_indexOf? (j := 950) (by decide +kernel) rfl) rfl oqBody_892

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L7` is sound with its queries named. -/
theorem oqSpecW_643 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L22_L7" "__loop407" ⟨1, 64, 15, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 15, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_925)
    (Program.find?_of_indexOf? (j := 664) (by decide +kernel) rfl) rfl oqBody_643
    (Program.find?_of_indexOf? (j := 926) (by decide +kernel) rfl) rfl oqBody_876

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L7` is sound with its queries named. -/
theorem oqSpecW_665 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L24_L7" "__loop409" ⟨1, 64, 17, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 17, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_929)
    (Program.find?_of_indexOf? (j := 686) (by decide +kernel) rfl) rfl oqBody_665
    (Program.find?_of_indexOf? (j := 930) (by decide +kernel) rfl) rfl oqBody_878

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L4` is sound with its queries named. -/
theorem oqSpecW_556 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L16_L4" "__loop394" ⟨0, 16, 12, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_977)
    (Program.find?_of_indexOf? (j := 577) (by decide +kernel) rfl) rfl oqBody_556
    (Program.find?_of_indexOf? (j := 900) (by decide +kernel) rfl) rfl oqBody_862

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5` is sound with its queries named. -/
theorem oqSpecW_455 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L17_L5" "__loop377" ⟨0, 16, 12, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_964)
    (Program.find?_of_indexOf? (j := 476) (by decide +kernel) rfl) rfl oqBody_455
    (Program.find?_of_indexOf? (j := 864) (by decide +kernel) rfl) rfl oqBody_841

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6` is sound with its queries named. -/
theorem oqSpecW_452 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L18_L6" "__loop376" ⟨0, 16, 12, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_963)
    (Program.find?_of_indexOf? (j := 473) (by decide +kernel) rfl) rfl oqBody_452
    (Program.find?_of_indexOf? (j := 862) (by decide +kernel) rfl) rfl oqBody_840

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L4` is sound with its queries named. -/
theorem oqSpecW_605 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L20_L4" "__loop403" ⟨0, 16, 16, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 16, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_982)
    (Program.find?_of_indexOf? (j := 626) (by decide +kernel) rfl) rfl oqBody_605
    (Program.find?_of_indexOf? (j := 918) (by decide +kernel) rfl) rfl oqBody_872

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L5` is sound with its queries named. -/
theorem oqSpecW_519 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L21_L5" "__loop389" ⟨0, 16, 16, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 16, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_974)
    (Program.find?_of_indexOf? (j := 540) (by decide +kernel) rfl) rfl oqBody_519
    (Program.find?_of_indexOf? (j := 890) (by decide +kernel) rfl) rfl oqBody_857

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L6` is sound with its queries named. -/
theorem oqSpecW_517 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L22_L6" "__loop388" ⟨0, 16, 16, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 16, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_973)
    (Program.find?_of_indexOf? (j := 538) (by decide +kernel) rfl) rfl oqBody_517
    (Program.find?_of_indexOf? (j := 888) (by decide +kernel) rfl) rfl oqBody_856

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6` is sound with its queries named. -/
theorem oqSpecW_678 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L24_L6" "__loop411" ⟨0, 16, 18, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_983)
    (Program.find?_of_indexOf? (j := 699) (by decide +kernel) rfl) rfl oqBody_678
    (Program.find?_of_indexOf? (j := 935) (by decide +kernel) rfl) rfl oqBody_881

end
end LeanVM.Guest.B1
