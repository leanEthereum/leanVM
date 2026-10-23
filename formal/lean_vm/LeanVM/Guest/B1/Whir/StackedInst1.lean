/-
  LeanVM.Guest.B1.Whir.StackedInst1

  `open_stacked__L7` to `open_stacked__L13` are sound: their configurations' facts by
  kernel evaluation, their callees' meanings.
-/

module

public import LeanVM.Guest.B1.Whir.StackedSound
public import LeanVM.Guest.B1.Whir.StackedData1
public import LeanVM.Guest.B1.Whir.QueriesSpec

/-!
# `open_stacked__L7` to `open_stacked__L13`

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
theorem osCfgOk_7 : OsCfgOk osCfg7 22 2 ((deriveConfig 22 2).getD []) where
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

theorem osCallees_7 (rd : Reader) : OsCallees rd osCfg7 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L18_L7_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core682, os_sq_find_7_0, rfl, os_sq_body_7_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L6_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core685, os_sq_find_7_1, rfl, os_sq_body_7_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_sound hn hq h, fun a r h => (decode_query_bits_L16_iff rd a r).mp h,
        ⟨Data.core686, os_sq_find_7_2, rfl, os_sq_body_7_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L15_L5_sound hn hq h, fun a r h => (decode_query_bits_L15_iff rd a r).mp h,
        ⟨Data.core687, os_sq_find_7_3, rfl, os_sq_body_7_3⟩⟩
  fin := fun a r h => (opening_final_message_L16_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L4_iff rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core688, os_res_find_7_0, rfl, os_res_body_7_0⟩, ⟨Data.core689, os_res_find_7_1, rfl, os_res_body_7_1⟩, ⟨Data.core690, os_res_find_7_2, rfl, os_res_body_7_2⟩, ⟨Data.core691, os_res_find_7_3, rfl, os_res_body_7_3⟩]

/-- **`open_stacked__L7`** (`μ = 22`, `r = 2`) is sound. -/
theorem open_stacked_L7_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L7" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 22 2 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_7 os_find_7 rfl os_body_7 (osCallees_7 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_8 : OsCfgOk osCfg8 23 2 ((deriveConfig 23 2).getD []) where
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

theorem osCallees_8 (rd : Reader) : OsCallees rd osCfg8 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L19_L7_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core692, os_sq_find_8_0, rfl, os_sq_body_8_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L6_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core694, os_sq_find_8_1, rfl, os_sq_body_8_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core695, os_sq_find_8_2, rfl, os_sq_body_8_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_sound hn hq h, fun a r h => (decode_query_bits_L16_iff rd a r).mp h,
        ⟨Data.core696, os_sq_find_8_3, rfl, os_sq_body_8_3⟩⟩
  fin := fun a r h => (opening_final_message_L32_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L5_iff rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core697, os_res_find_8_0, rfl, os_res_body_8_0⟩, ⟨Data.core698, os_res_find_8_1, rfl, os_res_body_8_1⟩, ⟨Data.core699, os_res_find_8_2, rfl, os_res_body_8_2⟩, ⟨Data.core700, os_res_find_8_3, rfl, os_res_body_8_3⟩]

/-- **`open_stacked__L8`** (`μ = 23`, `r = 2`) is sound. -/
theorem open_stacked_L8_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L8" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 23 2 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_8 os_find_8 rfl os_body_8 (osCallees_8 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_9 : OsCfgOk osCfg9 24 2 ((deriveConfig 24 2).getD []) where
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

theorem osCallees_9 (rd : Reader) : OsCallees rd osCfg9 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L20_L7_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core701, os_sq_find_9_0, rfl, os_sq_body_9_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L6_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core703, os_sq_find_9_1, rfl, os_sq_body_9_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core704, os_sq_find_9_2, rfl, os_sq_body_9_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core705, os_sq_find_9_3, rfl, os_sq_body_9_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L4_sound hn hq h, fun a r h => (decode_query_bits_L16_iff rd a r).mp h,
        ⟨Data.core706, os_sq_find_9_4, rfl, os_sq_body_9_4⟩⟩
  fin := fun a r h => (opening_final_message_L4_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L2_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core708, os_res_find_9_0, rfl, os_res_body_9_0⟩, ⟨Data.core709, os_res_find_9_1, rfl, os_res_body_9_1⟩, ⟨Data.core710, os_res_find_9_2, rfl, os_res_body_9_2⟩, ⟨Data.core711, os_res_find_9_3, rfl, os_res_body_9_3⟩, ⟨Data.core712, os_res_find_9_4, rfl, os_res_body_9_4⟩]

/-- **`open_stacked__L9`** (`μ = 24`, `r = 2`) is sound. -/
theorem open_stacked_L9_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L9" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 24 2 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_9 os_find_9 rfl os_body_9 (osCallees_9 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_10 : OsCfgOk osCfg10 25 2 ((deriveConfig 25 2).getD []) where
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

theorem osCallees_10 (rd : Reader) : OsCallees rd osCfg10 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L21_L7_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core713, os_sq_find_10_0, rfl, os_sq_body_10_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L6_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core715, os_sq_find_10_1, rfl, os_sq_body_10_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core716, os_sq_find_10_2, rfl, os_sq_body_10_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core717, os_sq_find_10_3, rfl, os_sq_body_10_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L4_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core718, os_sq_find_10_4, rfl, os_sq_body_10_4⟩⟩
  fin := fun a r h => (opening_final_message_L8_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L3_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core720, os_res_find_10_0, rfl, os_res_body_10_0⟩, ⟨Data.core721, os_res_find_10_1, rfl, os_res_body_10_1⟩, ⟨Data.core722, os_res_find_10_2, rfl, os_res_body_10_2⟩, ⟨Data.core723, os_res_find_10_3, rfl, os_res_body_10_3⟩, ⟨Data.core724, os_res_find_10_4, rfl, os_res_body_10_4⟩]

/-- **`open_stacked__L10`** (`μ = 25`, `r = 2`) is sound. -/
theorem open_stacked_L10_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L10" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 25 2 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_10 os_find_10 rfl os_body_10 (osCallees_10 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_11 : OsCfgOk osCfg11 26 2 ((deriveConfig 26 2).getD []) where
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

theorem osCallees_11 (rd : Reader) : OsCallees rd osCfg11 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L22_L7_sound hn hq h, fun a r h => (decode_query_bits_L22_iff rd a r).mp h,
        ⟨Data.core725, os_sq_find_11_0, rfl, os_sq_body_11_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L6_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core727, os_sq_find_11_1, rfl, os_sq_body_11_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core728, os_sq_find_11_2, rfl, os_sq_body_11_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core729, os_sq_find_11_3, rfl, os_sq_body_11_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L4_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core730, os_sq_find_11_4, rfl, os_sq_body_11_4⟩⟩
  fin := fun a r h => (opening_final_message_L16_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L4_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core731, os_res_find_11_0, rfl, os_res_body_11_0⟩, ⟨Data.core732, os_res_find_11_1, rfl, os_res_body_11_1⟩, ⟨Data.core733, os_res_find_11_2, rfl, os_res_body_11_2⟩, ⟨Data.core734, os_res_find_11_3, rfl, os_res_body_11_3⟩, ⟨Data.core735, os_res_find_11_4, rfl, os_res_body_11_4⟩]

/-- **`open_stacked__L11`** (`μ = 26`, `r = 2`) is sound. -/
theorem open_stacked_L11_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L11" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 26 2 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_11 os_find_11 rfl os_body_11 (osCallees_11 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_12 : OsCfgOk osCfg12 27 2 ((deriveConfig 27 2).getD []) where
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

theorem osCallees_12 (rd : Reader) : OsCallees rd osCfg12 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L23_L7_sound hn hq h, fun a r h => (decode_query_bits_L23_iff rd a r).mp h,
        ⟨Data.core736, os_sq_find_12_0, rfl, os_sq_body_12_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L6_sound hn hq h, fun a r h => (decode_query_bits_L22_iff rd a r).mp h,
        ⟨Data.core738, os_sq_find_12_1, rfl, os_sq_body_12_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core739, os_sq_find_12_2, rfl, os_sq_body_12_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core740, os_sq_find_12_3, rfl, os_sq_body_12_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L4_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core741, os_sq_find_12_4, rfl, os_sq_body_12_4⟩⟩
  fin := fun a r h => (opening_final_message_L32_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L5_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core743, os_res_find_12_0, rfl, os_res_body_12_0⟩, ⟨Data.core744, os_res_find_12_1, rfl, os_res_body_12_1⟩, ⟨Data.core745, os_res_find_12_2, rfl, os_res_body_12_2⟩, ⟨Data.core746, os_res_find_12_3, rfl, os_res_body_12_3⟩, ⟨Data.core747, os_res_find_12_4, rfl, os_res_body_12_4⟩]

/-- **`open_stacked__L12`** (`μ = 27`, `r = 2`) is sound. -/
theorem open_stacked_L12_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L12" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 27 2 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_12 os_find_12 rfl os_body_12 (osCallees_12 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_13 : OsCfgOk osCfg13 28 2 ((deriveConfig 28 2).getD []) where
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

theorem osCallees_13 (rd : Reader) : OsCallees rd osCfg13 where
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L7_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L24_L7_sound hn hq h, fun a r h => (decode_query_bits_L24_iff rd a r).mp h,
        ⟨Data.core748, os_sq_find_13_0, rfl, os_sq_body_13_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L23_L6_sound hn hq h, fun a r h => (decode_query_bits_L23_iff rd a r).mp h,
        ⟨Data.core750, os_sq_find_13_1, rfl, os_sq_body_13_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L5_sound hn hq h, fun a r h => (decode_query_bits_L22_iff rd a r).mp h,
        ⟨Data.core752, os_sq_find_13_2, rfl, os_sq_body_13_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core754, os_sq_find_13_3, rfl, os_sq_body_13_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L4_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core755, os_sq_find_13_4, rfl, os_sq_body_13_4⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L4_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core757, os_sq_find_13_5, rfl, os_sq_body_13_5⟩⟩
  fin := fun a r h => (opening_final_message_L4_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L2_iff rd a r).mp h
  res := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    exacts [⟨Data.core758, os_res_find_13_0, rfl, os_res_body_13_0⟩, ⟨Data.core759, os_res_find_13_1, rfl, os_res_body_13_1⟩, ⟨Data.core760, os_res_find_13_2, rfl, os_res_body_13_2⟩, ⟨Data.core761, os_res_find_13_3, rfl, os_res_body_13_3⟩, ⟨Data.core762, os_res_find_13_4, rfl, os_res_body_13_4⟩, ⟨Data.core763, os_res_find_13_5, rfl, os_res_body_13_5⟩]

/-- **`open_stacked__L13`** (`μ = 28`, `r = 2`) is sound. -/
theorem open_stacked_L13_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L13" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 28 2 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_13 os_find_13 rfl os_body_13 (osCallees_13 rd) hroot h

end
end LeanVM.Guest.B1
