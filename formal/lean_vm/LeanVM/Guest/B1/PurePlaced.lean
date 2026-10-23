/-
  LeanVM.Guest.B1.PurePlaced

  Group 1's pure functions placed: `CompleteMem` through their meanings.
-/

module

public import LeanVM.Guest.B1.FiatShamir
public import LeanVM.Guest.B1.Opening
public import LeanVM.Guest.B1.RowWeights
public import LeanVM.Guest.B1.FoldFinal
public import LeanVM.Guest.B1.Sumcheck
public import LeanVM.Guest.B1.Loops
public import LeanVM.Guest.B1.G1Placed

/-!
# Group 1's pure functions, placed

`opening_fold`, `assert_canonical`, `sumcheck_round4`, `sumcheck_round5`,
`opening_final_message__L{4,8,16,32}`, `opening_row_weights__L4_L0`, `__L6_L1`,
`fold_final_msg__L{2..5}`, `batch_sumcheck__L22`, `__L28`, `eq_prefix_chain` (with `__loop7`) and
`rs_eq_run` (with `__loop8`) allocate nothing and name no frame run, so each is `CompleteMem` on its
meaning (`completeMem_of_iff`). `assert_canonical`'s meaning reads no memory and `opening_fold`'s
reads only words its returns pin, so those two are also `CompleteRel` (`completeRel_of_lift`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)

set_option maxRecDepth 100000 in
theorem opening_fold_completeMem : CompleteMem fs cert k "opening_fold" MeaningOpeningFold :=
  completeMem_of_iff (g1_pure_one find_opening_fold (by decide +kernel)) (by simp) opening_fold_iff k

set_option maxRecDepth 100000 in
theorem opening_fold_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "opening_fold" B) :
    CompleteMemB fs cert k "opening_fold" MeaningOpeningFold B :=
  completeMem_of_iffB (g1_pure_one find_opening_fold (by decide +kernel)) (by simp) opening_fold_iff k hB

set_option maxRecDepth 100000 in
theorem opening_fold_completeMemD : CompleteMemD fs cert k "opening_fold" MeaningOpeningFold :=
  completeMem_of_iffD (g1_pure_one find_opening_fold (by decide +kernel)) (by simp) opening_fold_iff k

set_option maxRecDepth 100000 in
theorem sumcheck_round4_completeMem : CompleteMem fs cert k "sumcheck_round4" MeaningSumcheckRound4 :=
  completeMem_of_iff (g1_pure_one find_sumcheck_round4 (by decide +kernel)) (by simp) sumcheck_round4_iff k

set_option maxRecDepth 100000 in
theorem sumcheck_round4_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "sumcheck_round4" B) :
    CompleteMemB fs cert k "sumcheck_round4" MeaningSumcheckRound4 B :=
  completeMem_of_iffB (g1_pure_one find_sumcheck_round4 (by decide +kernel)) (by simp) sumcheck_round4_iff k hB

set_option maxRecDepth 100000 in
theorem sumcheck_round4_completeMemD : CompleteMemD fs cert k "sumcheck_round4" MeaningSumcheckRound4 :=
  completeMem_of_iffD (g1_pure_one find_sumcheck_round4 (by decide +kernel)) (by simp) sumcheck_round4_iff k

set_option maxRecDepth 100000 in
theorem sumcheck_round5_completeMem : CompleteMem fs cert k "sumcheck_round5" MeaningSumcheckRound5 :=
  completeMem_of_iff (g1_pure_one find_sumcheck_round5 (by decide +kernel)) (by simp) sumcheck_round5_iff k

set_option maxRecDepth 100000 in
theorem sumcheck_round5_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "sumcheck_round5" B) :
    CompleteMemB fs cert k "sumcheck_round5" MeaningSumcheckRound5 B :=
  completeMem_of_iffB (g1_pure_one find_sumcheck_round5 (by decide +kernel)) (by simp) sumcheck_round5_iff k hB

set_option maxRecDepth 100000 in
theorem sumcheck_round5_completeMemD : CompleteMemD fs cert k "sumcheck_round5" MeaningSumcheckRound5 :=
  completeMem_of_iffD (g1_pure_one find_sumcheck_round5 (by decide +kernel)) (by simp) sumcheck_round5_iff k

set_option maxRecDepth 100000 in
theorem ofm_L4_completeMem : CompleteMem fs cert k "opening_final_message__L4" (MeaningOpeningFinalMessage 4) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L4") (j := 616) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L4_iff k

set_option maxRecDepth 100000 in
theorem ofm_L4_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "opening_final_message__L4" B) :
    CompleteMemB fs cert k "opening_final_message__L4" (MeaningOpeningFinalMessage 4) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L4") (j := 616) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L4_iff k hB

set_option maxRecDepth 100000 in
theorem ofm_L4_completeMemD : CompleteMemD fs cert k "opening_final_message__L4" (MeaningOpeningFinalMessage 4) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L4") (j := 616) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L4_iff k

set_option maxRecDepth 100000 in
theorem ofm_L8_completeMem : CompleteMem fs cert k "opening_final_message__L8" (MeaningOpeningFinalMessage 8) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L8") (j := 631) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L8_iff k

set_option maxRecDepth 100000 in
theorem ofm_L8_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "opening_final_message__L8" B) :
    CompleteMemB fs cert k "opening_final_message__L8" (MeaningOpeningFinalMessage 8) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L8") (j := 631) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L8_iff k hB

set_option maxRecDepth 100000 in
theorem ofm_L8_completeMemD : CompleteMemD fs cert k "opening_final_message__L8" (MeaningOpeningFinalMessage 8) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L8") (j := 631) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L8_iff k

set_option maxRecDepth 100000 in
theorem ofm_L16_completeMem : CompleteMem fs cert k "opening_final_message__L16" (MeaningOpeningFinalMessage 16) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L16") (j := 588) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L16_iff k

set_option maxRecDepth 100000 in
theorem ofm_L16_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "opening_final_message__L16" B) :
    CompleteMemB fs cert k "opening_final_message__L16" (MeaningOpeningFinalMessage 16) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L16") (j := 588) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L16_iff k hB

set_option maxRecDepth 100000 in
theorem ofm_L16_completeMemD : CompleteMemD fs cert k "opening_final_message__L16" (MeaningOpeningFinalMessage 16) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L16") (j := 588) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L16_iff k

set_option maxRecDepth 100000 in
theorem ofm_L32_completeMem : CompleteMem fs cert k "opening_final_message__L32" (MeaningOpeningFinalMessage 32) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L32") (j := 602) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L32_iff k

set_option maxRecDepth 100000 in
theorem ofm_L32_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "opening_final_message__L32" B) :
    CompleteMemB fs cert k "opening_final_message__L32" (MeaningOpeningFinalMessage 32) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L32") (j := 602) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L32_iff k hB

set_option maxRecDepth 100000 in
theorem ofm_L32_completeMemD : CompleteMemD fs cert k "opening_final_message__L32" (MeaningOpeningFinalMessage 32) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L32") (j := 602) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_final_message_L32_iff k

set_option maxRecDepth 100000 in
theorem orw_L4_L0_completeMem : CompleteMem fs cert k "opening_row_weights__L4_L0" (MeaningOpeningRowWeights 4 0) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "opening_row_weights__L4_L0") (j := 582) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_row_weights_L4_L0_iff k

set_option maxRecDepth 100000 in
theorem orw_L4_L0_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "opening_row_weights__L4_L0" B) :
    CompleteMemB fs cert k "opening_row_weights__L4_L0" (MeaningOpeningRowWeights 4 0) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "opening_row_weights__L4_L0") (j := 582) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_row_weights_L4_L0_iff k hB

set_option maxRecDepth 100000 in
theorem orw_L4_L0_completeMemD : CompleteMemD fs cert k "opening_row_weights__L4_L0" (MeaningOpeningRowWeights 4 0) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "opening_row_weights__L4_L0") (j := 582) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_row_weights_L4_L0_iff k

set_option maxRecDepth 100000 in
theorem orw_L6_L1_completeMem : CompleteMem fs cert k "opening_row_weights__L6_L1" (MeaningOpeningRowWeights 6 1) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "opening_row_weights__L6_L1") (j := 578) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_row_weights_L6_L1_iff k

set_option maxRecDepth 100000 in
theorem orw_L6_L1_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "opening_row_weights__L6_L1" B) :
    CompleteMemB fs cert k "opening_row_weights__L6_L1" (MeaningOpeningRowWeights 6 1) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "opening_row_weights__L6_L1") (j := 578) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_row_weights_L6_L1_iff k hB

set_option maxRecDepth 100000 in
theorem orw_L6_L1_completeMemD : CompleteMemD fs cert k "opening_row_weights__L6_L1" (MeaningOpeningRowWeights 6 1) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "opening_row_weights__L6_L1") (j := 578) (by decide +kernel) rfl) (by decide +kernel)) (by simp) opening_row_weights_L6_L1_iff k

set_option maxRecDepth 100000 in
theorem ffm_L2_completeMem : CompleteMem fs cert k "fold_final_msg__L2" (MeaningFoldFinalMsg 2) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L2") (j := 618) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L2_iff k

set_option maxRecDepth 100000 in
theorem ffm_L2_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "fold_final_msg__L2" B) :
    CompleteMemB fs cert k "fold_final_msg__L2" (MeaningFoldFinalMsg 2) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L2") (j := 618) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L2_iff k hB

set_option maxRecDepth 100000 in
theorem ffm_L2_completeMemD : CompleteMemD fs cert k "fold_final_msg__L2" (MeaningFoldFinalMsg 2) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L2") (j := 618) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L2_iff k

set_option maxRecDepth 100000 in
theorem ffm_L3_completeMem : CompleteMem fs cert k "fold_final_msg__L3" (MeaningFoldFinalMsg 3) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L3") (j := 633) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L3_iff k

set_option maxRecDepth 100000 in
theorem ffm_L3_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "fold_final_msg__L3" B) :
    CompleteMemB fs cert k "fold_final_msg__L3" (MeaningFoldFinalMsg 3) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L3") (j := 633) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L3_iff k hB

set_option maxRecDepth 100000 in
theorem ffm_L3_completeMemD : CompleteMemD fs cert k "fold_final_msg__L3" (MeaningFoldFinalMsg 3) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L3") (j := 633) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L3_iff k

set_option maxRecDepth 100000 in
theorem ffm_L4_completeMem : CompleteMem fs cert k "fold_final_msg__L4" (MeaningFoldFinalMsg 4) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L4") (j := 591) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L4_iff k

set_option maxRecDepth 100000 in
theorem ffm_L4_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "fold_final_msg__L4" B) :
    CompleteMemB fs cert k "fold_final_msg__L4" (MeaningFoldFinalMsg 4) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L4") (j := 591) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L4_iff k hB

set_option maxRecDepth 100000 in
theorem ffm_L4_completeMemD : CompleteMemD fs cert k "fold_final_msg__L4" (MeaningFoldFinalMsg 4) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L4") (j := 591) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L4_iff k

set_option maxRecDepth 100000 in
theorem ffm_L5_completeMem : CompleteMem fs cert k "fold_final_msg__L5" (MeaningFoldFinalMsg 5) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L5") (j := 604) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L5_iff k

set_option maxRecDepth 100000 in
theorem ffm_L5_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "fold_final_msg__L5" B) :
    CompleteMemB fs cert k "fold_final_msg__L5" (MeaningFoldFinalMsg 5) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L5") (j := 604) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L5_iff k hB

set_option maxRecDepth 100000 in
theorem ffm_L5_completeMemD : CompleteMemD fs cert k "fold_final_msg__L5" (MeaningFoldFinalMsg 5) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "fold_final_msg__L5") (j := 604) (by decide +kernel) rfl) (by decide +kernel)) (by simp) fold_final_msg_L5_iff k

set_option maxRecDepth 100000 in
theorem bs_L22_completeMem : CompleteMem fs cert k "batch_sumcheck__L22" (MeaningBatchSumcheck 22) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "batch_sumcheck__L22") (j := 568) (by decide +kernel) rfl) (by decide +kernel)) (by simp) batch_sumcheck_L22_iff k

set_option maxRecDepth 100000 in
theorem bs_L22_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "batch_sumcheck__L22" B) :
    CompleteMemB fs cert k "batch_sumcheck__L22" (MeaningBatchSumcheck 22) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "batch_sumcheck__L22") (j := 568) (by decide +kernel) rfl) (by decide +kernel)) (by simp) batch_sumcheck_L22_iff k hB

set_option maxRecDepth 100000 in
theorem bs_L22_completeMemD : CompleteMemD fs cert k "batch_sumcheck__L22" (MeaningBatchSumcheck 22) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "batch_sumcheck__L22") (j := 568) (by decide +kernel) rfl) (by decide +kernel)) (by simp) batch_sumcheck_L22_iff k

set_option maxRecDepth 100000 in
theorem bs_L28_completeMem : CompleteMem fs cert k "batch_sumcheck__L28" (MeaningBatchSumcheck 28) :=
  completeMem_of_iff (g1_pure_one (Program.find?_of_indexOf? (n := "batch_sumcheck__L28") (j := 571) (by decide +kernel) rfl) (by decide +kernel)) (by simp) batch_sumcheck_L28_iff k

set_option maxRecDepth 100000 in
theorem bs_L28_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "batch_sumcheck__L28" B) :
    CompleteMemB fs cert k "batch_sumcheck__L28" (MeaningBatchSumcheck 28) B :=
  completeMem_of_iffB (g1_pure_one (Program.find?_of_indexOf? (n := "batch_sumcheck__L28") (j := 571) (by decide +kernel) rfl) (by decide +kernel)) (by simp) batch_sumcheck_L28_iff k hB

set_option maxRecDepth 100000 in
theorem bs_L28_completeMemD : CompleteMemD fs cert k "batch_sumcheck__L28" (MeaningBatchSumcheck 28) :=
  completeMem_of_iffD (g1_pure_one (Program.find?_of_indexOf? (n := "batch_sumcheck__L28") (j := 571) (by decide +kernel) rfl) (by decide +kernel)) (by simp) batch_sumcheck_L28_iff k

set_option maxRecDepth 100000 in
theorem eq_prefix_chain_completeMem : CompleteMem fs cert k "eq_prefix_chain" MeaningEqPrefixChain :=
  completeMem_of_iff (g1_pure_two find_eq_prefix_chain find_loop7 (by decide +kernel) (by decide +kernel)) (by simp) eq_prefix_chain_iff k

set_option maxRecDepth 100000 in
theorem eq_prefix_chain_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "eq_prefix_chain" B) :
    CompleteMemB fs cert k "eq_prefix_chain" MeaningEqPrefixChain B :=
  completeMem_of_iffB (g1_pure_two find_eq_prefix_chain find_loop7 (by decide +kernel) (by decide +kernel)) (by simp) eq_prefix_chain_iff k hB

set_option maxRecDepth 100000 in
theorem eq_prefix_chain_completeMemD : CompleteMemD fs cert k "eq_prefix_chain" MeaningEqPrefixChain :=
  completeMem_of_iffD (g1_pure_two find_eq_prefix_chain find_loop7 (by decide +kernel) (by decide +kernel)) (by simp) eq_prefix_chain_iff k

set_option maxRecDepth 100000 in
theorem rs_eq_run_completeMem : CompleteMem fs cert k "rs_eq_run" MeaningRsEqRun :=
  completeMem_of_iff (g1_pure_two find_rs_eq_run find_loop8 (by decide +kernel) (by decide +kernel)) (by simp) rs_eq_run_iff k

set_option maxRecDepth 100000 in
theorem rs_eq_run_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "rs_eq_run" B) :
    CompleteMemB fs cert k "rs_eq_run" MeaningRsEqRun B :=
  completeMem_of_iffB (g1_pure_two find_rs_eq_run find_loop8 (by decide +kernel) (by decide +kernel)) (by simp) rs_eq_run_iff k hB

set_option maxRecDepth 100000 in
theorem rs_eq_run_completeMemD : CompleteMemD fs cert k "rs_eq_run" MeaningRsEqRun :=
  completeMem_of_iffD (g1_pure_two find_rs_eq_run find_loop8 (by decide +kernel) (by decide +kernel)) (by simp) rs_eq_run_iff k

set_option maxRecDepth 100000 in
theorem assert_canonical_completeMem :
    CompleteMem fs cert k "assert_canonical" fun _ args rets => MeaningAssertCanonical args rets :=
  completeMem_of_iff (g1_pure_one find_assert_canonical (by decide +kernel)) (by simp)
    assert_canonical_iff k

set_option maxRecDepth 100000 in
theorem assert_canonical_completeMemB (B : List E → ℕ) (hB : TotalLe coreProgram fs "assert_canonical" B) :
    CompleteMemB fs cert k "assert_canonical" (fun _ args rets => MeaningAssertCanonical args rets) B :=
  completeMem_of_iffB (g1_pure_one find_assert_canonical (by decide +kernel)) (by simp)
    assert_canonical_iff k hB

set_option maxRecDepth 100000 in
theorem assert_canonical_completeMemD :
    CompleteMemD fs cert k "assert_canonical" fun _ args rets => MeaningAssertCanonical args rets :=
  completeMem_of_iffD (g1_pure_one find_assert_canonical (by decide +kernel)) (by simp)
    assert_canonical_iff k

/-- **`assert_canonical`, placed**, in the `CompleteRel` form: its meaning reads no memory. -/
theorem assert_canonical_completeRel :
    CompleteRel fs cert k "assert_canonical" fun _ args rets => MeaningAssertCanonical args rets :=
  completeRel_of_const (assert_canonical_completeMem fs cert k)

/-- **`assert_canonical`, placed**, in the `CompleteRelD` form: its meaning reads no memory. -/
theorem assert_canonical_completeRelD :
    CompleteRelD fs cert k "assert_canonical" fun _ args rets => MeaningAssertCanonical args rets :=
  completeRel_of_constD (assert_canonical_completeMemD fs cert k)

/-- **`opening_fold`, placed**, in the `CompleteRel` form: the two words it reads are returned. -/
theorem opening_fold_completeRel : CompleteRel fs cert k "opening_fold" MeaningOpeningFold := by
  refine completeRel_of_lift (opening_fold_completeMem fs cert k) fun args rets Lin rd1 hl1 hL1 hpre => ?_
  obtain ⟨s0, s1, cur, c0, c1, c2, rfl⟩ : ∃ s0 s1 cur c0 c1 c2, args = [s0, s1, cur, c0, c1, c2] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  have hr : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd cur [rets.getD 4 0, rets.getD 5 0] := by
    intro rd hl hL
    obtain ⟨_, _, _, _, _, _, _, -, hR, -, rfl⟩ := hpre rd hl hL
    exact hR
  have hr' := (readsAt_lift hl1 hL1 hr).2
  intro rd hL
  obtain ⟨cv, d0, d2, r, t, q, cv', hcv, -, hrun, rfl⟩ := hpre rd1 hl1 hL1
  exact ⟨cv, d0, d2, r, t, q, cv', hcv, hr' rd hL, hrun, rfl⟩

/-- **`opening_fold`, placed**, in the `CompleteRelD` form: the two words it reads are returned. -/
theorem opening_fold_completeRelD : CompleteRelD fs cert k "opening_fold" MeaningOpeningFold := by
  refine completeRel_of_liftD (opening_fold_completeMemD fs cert k) fun args rets Lin rd1 hl1 hL1 hpre => ?_
  obtain ⟨s0, s1, cur, c0, c1, c2, rfl⟩ : ∃ s0 s1 cur c0 c1 c2, args = [s0, s1, cur, c0, c1, c2] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  have hr : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd cur [rets.getD 4 0, rets.getD 5 0] := by
    intro rd hl hL
    obtain ⟨_, _, _, _, _, _, _, -, hR, -, rfl⟩ := hpre rd hl hL
    exact hR
  have hr' := (readsAt_lift hl1 hL1 hr).2
  intro rd hL
  obtain ⟨cv, d0, d2, r, t, q, cv', hcv, -, hrun, rfl⟩ := hpre rd1 hl1 hL1
  exact ⟨cv, d0, d2, r, t, q, cv', hcv, hr' rd hL, hrun, rfl⟩


/-- **`assert_canonical`, placed**, bounded: its meaning reads no memory. -/
theorem assert_canonical_completeRelB (B : List E → ℕ) (hB : TotalLe coreProgram fs "assert_canonical" B) :
    ∀ (args rets : List E) (Lin : Main.Layout),
      (∀ rd, LowDef k rd → MemL rd Lin → MeaningAssertCanonical args rets) →
        CompleteAtB fs cert k "assert_canonical" Lin args (Returns rets) (B args) :=
  completeRel_of_constB (assert_canonical_completeMemB fs cert k B hB)

/-- **`opening_fold`, placed**, in the `CompleteRelD` form: the two words it reads are returned. -/
theorem opening_fold_completeRelB (B : List E → ℕ) (hB : TotalLe coreProgram fs "opening_fold" B) :
    ∀ (args rets : List E) (Lin : Main.Layout),
      (∀ rd, LowDef k rd → MemL rd Lin → MeaningOpeningFold rd args rets) →
        CompleteAtB fs cert k "opening_fold" Lin args (Returns rets) (B args) := by
  intro args rets Lin hpre
  refine completeRel_of_liftB (opening_fold_completeMemB fs cert k B hB) (fun args rets Lin rd1 hl1 hL1 hpre => ?_) args rets Lin hpre
  obtain ⟨s0, s1, cur, c0, c1, c2, rfl⟩ : ∃ s0 s1 cur c0 c1 c2, args = [s0, s1, cur, c0, c1, c2] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  have hr : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd cur [rets.getD 4 0, rets.getD 5 0] := by
    intro rd hl hL
    obtain ⟨_, _, _, _, _, _, _, -, hR, -, rfl⟩ := hpre rd hl hL
    exact hR
  have hr' := (readsAt_lift hl1 hL1 hr).2
  intro rd hL
  obtain ⟨cv, d0, d2, r, t, q, cv', hcv, -, hrun, rfl⟩ := hpre rd1 hl1 hL1
  exact ⟨cv, d0, d2, r, t, q, cv', hcv, hr' rd hL, hrun, rfl⟩

end
end LeanVM.Guest.B1
