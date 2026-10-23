/-
  LeanVM.Guest.B1.Whir.StackedInst2

  `open_stacked__L14` to `open_stacked__L20` are sound: their configurations' facts by
  kernel evaluation, their callees' meanings.
-/

module

public import LeanVM.Guest.B1.Whir.StackedSound
public import LeanVM.Guest.B1.Whir.StackedData2
public import LeanVM.Guest.B1.Whir.QueriesSpec

/-!
# `open_stacked__L14` to `open_stacked__L20`

For each candidate `m = (μ - 22) + 7·(r - 1)`: `OsCfgOk` of its configuration against
`deriveConfig μ r` (decided), `OsCallees` (the specialized callees' theorems and the loop
bodies' kernel checks), and `open_stacked_sound` at them.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.B1.VerifySub

@[expose] public section


set_option maxRecDepth 100000 in
theorem osCfgOk_14 : OsCfgOk osCfg14 22 3 ((deriveConfig 22 3).getD []) where
  config := by decide +kernel
  len := by decide +kernel
  len2 := by decide +kernel
  spec := by decide +kernel
  lane := by decide +kernel
  off0 := by decide +kernel
  shape := by decide +kernel
  yr2 := by decide +kernel
  yr5 := by decide +kernel
  yrLevel := by decide +kernel
  nFolds := by decide +kernel
  total := by decide +kernel
  laneLe := by decide +kernel
  pt42 := by decide +kernel
  ood := by decide +kernel
  lvs := by decide +kernel

theorem osCallees_14 (rd : Reader) : OsCallees rd osCfg14 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L19_L7_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core764, os_sq_find_14_0, rfl, os_sq_body_14_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L6_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core765, os_sq_find_14_1, rfl, os_sq_body_14_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core766, os_sq_find_14_2, rfl, os_sq_body_14_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_sound hn hq h, fun a r h => (decode_query_bits_L16_iff rd a r).mp h,
        ⟨Data.core767, os_sq_find_14_3, rfl, os_sq_body_14_3⟩⟩
  fin := fun a r h => (opening_final_message_L16_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L4_iff rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core768, os_res_find_14_0, rfl, os_res_body_14_0⟩, ⟨Data.core769, os_res_find_14_1, rfl, os_res_body_14_1⟩, ⟨Data.core770, os_res_find_14_2, rfl, os_res_body_14_2⟩, ⟨Data.core771, os_res_find_14_3, rfl, os_res_body_14_3⟩]

/-- **`open_stacked__L14`** (`μ = 22`, `r = 3`) is sound. -/
theorem open_stacked_L14_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L14" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 22 3 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_14 os_find_14 rfl os_body_14 (osCallees_14 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_15 : OsCfgOk osCfg15 23 3 ((deriveConfig 23 3).getD []) where
  config := by decide +kernel
  len := by decide +kernel
  len2 := by decide +kernel
  spec := by decide +kernel
  lane := by decide +kernel
  off0 := by decide +kernel
  shape := by decide +kernel
  yr2 := by decide +kernel
  yr5 := by decide +kernel
  yrLevel := by decide +kernel
  nFolds := by decide +kernel
  total := by decide +kernel
  laneLe := by decide +kernel
  pt42 := by decide +kernel
  ood := by decide +kernel
  lvs := by decide +kernel

theorem osCallees_15 (rd : Reader) : OsCallees rd osCfg15 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L20_L7_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core772, os_sq_find_15_0, rfl, os_sq_body_15_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L6_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core773, os_sq_find_15_1, rfl, os_sq_body_15_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core774, os_sq_find_15_2, rfl, os_sq_body_15_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core775, os_sq_find_15_3, rfl, os_sq_body_15_3⟩⟩
  fin := fun a r h => (opening_final_message_L32_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L5_iff rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core776, os_res_find_15_0, rfl, os_res_body_15_0⟩, ⟨Data.core777, os_res_find_15_1, rfl, os_res_body_15_1⟩, ⟨Data.core778, os_res_find_15_2, rfl, os_res_body_15_2⟩, ⟨Data.core779, os_res_find_15_3, rfl, os_res_body_15_3⟩]

/-- **`open_stacked__L15`** (`μ = 23`, `r = 3`) is sound. -/
theorem open_stacked_L15_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L15" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 23 3 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_15 os_find_15 rfl os_body_15 (osCallees_15 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_16 : OsCfgOk osCfg16 24 3 ((deriveConfig 24 3).getD []) where
  config := by decide +kernel
  len := by decide +kernel
  len2 := by decide +kernel
  spec := by decide +kernel
  lane := by decide +kernel
  off0 := by decide +kernel
  shape := by decide +kernel
  yr2 := by decide +kernel
  yr5 := by decide +kernel
  yrLevel := by decide +kernel
  nFolds := by decide +kernel
  total := by decide +kernel
  laneLe := by decide +kernel
  pt42 := by decide +kernel
  ood := by decide +kernel
  lvs := by decide +kernel

theorem osCallees_16 (rd : Reader) : OsCallees rd osCfg16 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L21_L7_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core780, os_sq_find_16_0, rfl, os_sq_body_16_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L6_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core781, os_sq_find_16_1, rfl, os_sq_body_16_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core782, os_sq_find_16_2, rfl, os_sq_body_16_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core783, os_sq_find_16_3, rfl, os_sq_body_16_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L4_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core784, os_sq_find_16_4, rfl, os_sq_body_16_4⟩⟩
  fin := fun a r h => (opening_final_message_L4_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L2_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core785, os_res_find_16_0, rfl, os_res_body_16_0⟩, ⟨Data.core786, os_res_find_16_1, rfl, os_res_body_16_1⟩, ⟨Data.core787, os_res_find_16_2, rfl, os_res_body_16_2⟩, ⟨Data.core788, os_res_find_16_3, rfl, os_res_body_16_3⟩, ⟨Data.core789, os_res_find_16_4, rfl, os_res_body_16_4⟩]

/-- **`open_stacked__L16`** (`μ = 24`, `r = 3`) is sound. -/
theorem open_stacked_L16_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L16" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 24 3 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_16 os_find_16 rfl os_body_16 (osCallees_16 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_17 : OsCfgOk osCfg17 25 3 ((deriveConfig 25 3).getD []) where
  config := by decide +kernel
  len := by decide +kernel
  len2 := by decide +kernel
  spec := by decide +kernel
  lane := by decide +kernel
  off0 := by decide +kernel
  shape := by decide +kernel
  yr2 := by decide +kernel
  yr5 := by decide +kernel
  yrLevel := by decide +kernel
  nFolds := by decide +kernel
  total := by decide +kernel
  laneLe := by decide +kernel
  pt42 := by decide +kernel
  ood := by decide +kernel
  lvs := by decide +kernel

theorem osCallees_17 (rd : Reader) : OsCallees rd osCfg17 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L22_L7_sound hn hq h, fun a r h => (decode_query_bits_L22_iff rd a r).mp h,
        ⟨Data.core790, os_sq_find_17_0, rfl, os_sq_body_17_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L6_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core791, os_sq_find_17_1, rfl, os_sq_body_17_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core792, os_sq_find_17_2, rfl, os_sq_body_17_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core793, os_sq_find_17_3, rfl, os_sq_body_17_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L4_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core794, os_sq_find_17_4, rfl, os_sq_body_17_4⟩⟩
  fin := fun a r h => (opening_final_message_L8_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L3_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core795, os_res_find_17_0, rfl, os_res_body_17_0⟩, ⟨Data.core796, os_res_find_17_1, rfl, os_res_body_17_1⟩, ⟨Data.core797, os_res_find_17_2, rfl, os_res_body_17_2⟩, ⟨Data.core798, os_res_find_17_3, rfl, os_res_body_17_3⟩, ⟨Data.core799, os_res_find_17_4, rfl, os_res_body_17_4⟩]

/-- **`open_stacked__L17`** (`μ = 25`, `r = 3`) is sound. -/
theorem open_stacked_L17_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L17" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 25 3 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_17 os_find_17 rfl os_body_17 (osCallees_17 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_18 : OsCfgOk osCfg18 26 3 ((deriveConfig 26 3).getD []) where
  config := by decide +kernel
  len := by decide +kernel
  len2 := by decide +kernel
  spec := by decide +kernel
  lane := by decide +kernel
  off0 := by decide +kernel
  shape := by decide +kernel
  yr2 := by decide +kernel
  yr5 := by decide +kernel
  yrLevel := by decide +kernel
  nFolds := by decide +kernel
  total := by decide +kernel
  laneLe := by decide +kernel
  pt42 := by decide +kernel
  ood := by decide +kernel
  lvs := by decide +kernel

theorem osCallees_18 (rd : Reader) : OsCallees rd osCfg18 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L23_L7_sound hn hq h, fun a r h => (decode_query_bits_L23_iff rd a r).mp h,
        ⟨Data.core800, os_sq_find_18_0, rfl, os_sq_body_18_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L6_sound hn hq h, fun a r h => (decode_query_bits_L22_iff rd a r).mp h,
        ⟨Data.core801, os_sq_find_18_1, rfl, os_sq_body_18_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core802, os_sq_find_18_2, rfl, os_sq_body_18_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core803, os_sq_find_18_3, rfl, os_sq_body_18_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L4_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core804, os_sq_find_18_4, rfl, os_sq_body_18_4⟩⟩
  fin := fun a r h => (opening_final_message_L16_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L4_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core805, os_res_find_18_0, rfl, os_res_body_18_0⟩, ⟨Data.core806, os_res_find_18_1, rfl, os_res_body_18_1⟩, ⟨Data.core807, os_res_find_18_2, rfl, os_res_body_18_2⟩, ⟨Data.core808, os_res_find_18_3, rfl, os_res_body_18_3⟩, ⟨Data.core809, os_res_find_18_4, rfl, os_res_body_18_4⟩]

/-- **`open_stacked__L18`** (`μ = 26`, `r = 3`) is sound. -/
theorem open_stacked_L18_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L18" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 26 3 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_18 os_find_18 rfl os_body_18 (osCallees_18 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_19 : OsCfgOk osCfg19 27 3 ((deriveConfig 27 3).getD []) where
  config := by decide +kernel
  len := by decide +kernel
  len2 := by decide +kernel
  spec := by decide +kernel
  lane := by decide +kernel
  off0 := by decide +kernel
  shape := by decide +kernel
  yr2 := by decide +kernel
  yr5 := by decide +kernel
  yrLevel := by decide +kernel
  nFolds := by decide +kernel
  total := by decide +kernel
  laneLe := by decide +kernel
  pt42 := by decide +kernel
  ood := by decide +kernel
  lvs := by decide +kernel

theorem osCallees_19 (rd : Reader) : OsCallees rd osCfg19 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L24_L7_sound hn hq h, fun a r h => (decode_query_bits_L24_iff rd a r).mp h,
        ⟨Data.core810, os_sq_find_19_0, rfl, os_sq_body_19_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L23_L6_sound hn hq h, fun a r h => (decode_query_bits_L23_iff rd a r).mp h,
        ⟨Data.core811, os_sq_find_19_1, rfl, os_sq_body_19_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L5_sound hn hq h, fun a r h => (decode_query_bits_L22_iff rd a r).mp h,
        ⟨Data.core812, os_sq_find_19_2, rfl, os_sq_body_19_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core813, os_sq_find_19_3, rfl, os_sq_body_19_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L4_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core814, os_sq_find_19_4, rfl, os_sq_body_19_4⟩⟩
  fin := fun a r h => (opening_final_message_L32_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L5_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core815, os_res_find_19_0, rfl, os_res_body_19_0⟩, ⟨Data.core816, os_res_find_19_1, rfl, os_res_body_19_1⟩, ⟨Data.core817, os_res_find_19_2, rfl, os_res_body_19_2⟩, ⟨Data.core818, os_res_find_19_3, rfl, os_res_body_19_3⟩, ⟨Data.core819, os_res_find_19_4, rfl, os_res_body_19_4⟩]

/-- **`open_stacked__L19`** (`μ = 27`, `r = 3`) is sound. -/
theorem open_stacked_L19_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L19" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 27 3 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_19 os_find_19 rfl os_body_19 (osCallees_19 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_20 : OsCfgOk osCfg20 28 3 ((deriveConfig 28 3).getD []) where
  config := by decide +kernel
  len := by decide +kernel
  len2 := by decide +kernel
  spec := by decide +kernel
  lane := by decide +kernel
  off0 := by decide +kernel
  shape := by decide +kernel
  yr2 := by decide +kernel
  yr5 := by decide +kernel
  yrLevel := by decide +kernel
  nFolds := by decide +kernel
  total := by decide +kernel
  laneLe := by decide +kernel
  pt42 := by decide +kernel
  ood := by decide +kernel
  lvs := by decide +kernel

theorem osCallees_20 (rd : Reader) : OsCallees rd osCfg20 where
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L25_L7_sound hn hq h, fun a r h => (decode_query_bits_L25_iff rd a r).mp h,
        ⟨Data.core820, os_sq_find_20_0, rfl, os_sq_body_20_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L24_L6_sound hn hq h, fun a r h => (decode_query_bits_L24_iff rd a r).mp h,
        ⟨Data.core822, os_sq_find_20_1, rfl, os_sq_body_20_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L23_L5_sound hn hq h, fun a r h => (decode_query_bits_L23_iff rd a r).mp h,
        ⟨Data.core824, os_sq_find_20_2, rfl, os_sq_body_20_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L5_sound hn hq h, fun a r h => (decode_query_bits_L22_iff rd a r).mp h,
        ⟨Data.core826, os_sq_find_20_3, rfl, os_sq_body_20_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L4_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core827, os_sq_find_20_4, rfl, os_sq_body_20_4⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L4_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core829, os_sq_find_20_5, rfl, os_sq_body_20_5⟩⟩
  fin := fun a r h => (opening_final_message_L4_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L2_iff rd a r).mp h
  res := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    exacts [⟨Data.core830, os_res_find_20_0, rfl, os_res_body_20_0⟩, ⟨Data.core831, os_res_find_20_1, rfl, os_res_body_20_1⟩, ⟨Data.core832, os_res_find_20_2, rfl, os_res_body_20_2⟩, ⟨Data.core833, os_res_find_20_3, rfl, os_res_body_20_3⟩, ⟨Data.core834, os_res_find_20_4, rfl, os_res_body_20_4⟩, ⟨Data.core835, os_res_find_20_5, rfl, os_res_body_20_5⟩]

/-- **`open_stacked__L20`** (`μ = 28`, `r = 3`) is sound. -/
theorem open_stacked_L20_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L20" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 28 3 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_20 os_find_20 rfl os_body_20 (osCallees_20 rd) hroot h

end
end LeanVM.Guest.B1
