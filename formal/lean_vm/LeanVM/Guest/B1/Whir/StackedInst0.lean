/-
  LeanVM.Guest.B1.Whir.StackedInst0

  `open_stacked__L0` to `open_stacked__L6` are sound: their configurations' facts by
  kernel evaluation, their callees' meanings.
-/

module

public import LeanVM.Guest.B1.Whir.StackedSound
public import LeanVM.Guest.B1.Whir.StackedData0
public import LeanVM.Guest.B1.Whir.QueriesSpec

/-!
# `open_stacked__L0` to `open_stacked__L6`

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
theorem osCfgOk_0 : OsCfgOk osCfg0 22 1 ((deriveConfig 22 1).getD []) where
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

theorem osCallees_0 (rd : Reader) : OsCallees rd osCfg0 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L8_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L17_L8_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core577, os_sq_find_0_0, rfl, os_sq_body_0_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L6_sound hn hq h, fun a r h => (decode_query_bits_L16_iff rd a r).mp h,
        ⟨Data.core581, os_sq_find_0_1, rfl, os_sq_body_0_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L15_L5_sound hn hq h, fun a r h => (decode_query_bits_L15_iff rd a r).mp h,
        ⟨Data.core585, os_sq_find_0_2, rfl, os_sq_body_0_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L14_L5_sound hn hq h, fun a r h => (decode_query_bits_L14_iff rd a r).mp h,
        ⟨Data.core589, os_sq_find_0_3, rfl, os_sq_body_0_3⟩⟩
  fin := fun a r h => (opening_final_message_L16_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L4_iff rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core592, os_res_find_0_0, rfl, os_res_body_0_0⟩, ⟨Data.core593, os_res_find_0_1, rfl, os_res_body_0_1⟩, ⟨Data.core594, os_res_find_0_2, rfl, os_res_body_0_2⟩, ⟨Data.core595, os_res_find_0_3, rfl, os_res_body_0_3⟩]

/-- **`open_stacked__L0`** (`μ = 22`, `r = 1`) is sound. -/
theorem open_stacked_L0_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L0" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 22 1 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_0 os_find_0 rfl os_body_0 (osCallees_0 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_1 : OsCfgOk osCfg1 23 1 ((deriveConfig 23 1).getD []) where
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

theorem osCallees_1 (rd : Reader) : OsCallees rd osCfg1 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L8_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L18_L8_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core596, os_sq_find_1_0, rfl, os_sq_body_1_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L6_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core598, os_sq_find_1_1, rfl, os_sq_body_1_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_sound hn hq h, fun a r h => (decode_query_bits_L16_iff rd a r).mp h,
        ⟨Data.core600, os_sq_find_1_2, rfl, os_sq_body_1_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L15_L5_sound hn hq h, fun a r h => (decode_query_bits_L15_iff rd a r).mp h,
        ⟨Data.core603, os_sq_find_1_3, rfl, os_sq_body_1_3⟩⟩
  fin := fun a r h => (opening_final_message_L32_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L5_iff rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core605, os_res_find_1_0, rfl, os_res_body_1_0⟩, ⟨Data.core606, os_res_find_1_1, rfl, os_res_body_1_1⟩, ⟨Data.core607, os_res_find_1_2, rfl, os_res_body_1_2⟩, ⟨Data.core608, os_res_find_1_3, rfl, os_res_body_1_3⟩]

/-- **`open_stacked__L1`** (`μ = 23`, `r = 1`) is sound. -/
theorem open_stacked_L1_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L1" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 23 1 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_1 os_find_1 rfl os_body_1 (osCallees_1 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_2 : OsCfgOk osCfg2 24 1 ((deriveConfig 24 1).getD []) where
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

theorem osCallees_2 (rd : Reader) : OsCallees rd osCfg2 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L8_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L19_L8_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core609, os_sq_find_2_0, rfl, os_sq_body_2_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L6_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core611, os_sq_find_2_1, rfl, os_sq_body_2_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core613, os_sq_find_2_2, rfl, os_sq_body_2_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_sound hn hq h, fun a r h => (decode_query_bits_L16_iff rd a r).mp h,
        ⟨Data.core615, os_sq_find_2_3, rfl, os_sq_body_2_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L15_L5_sound hn hq h, fun a r h => (decode_query_bits_L15_iff rd a r).mp h,
        ⟨Data.core617, os_sq_find_2_4, rfl, os_sq_body_2_4⟩⟩
  fin := fun a r h => (opening_final_message_L4_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L2_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core619, os_res_find_2_0, rfl, os_res_body_2_0⟩, ⟨Data.core620, os_res_find_2_1, rfl, os_res_body_2_1⟩, ⟨Data.core621, os_res_find_2_2, rfl, os_res_body_2_2⟩, ⟨Data.core622, os_res_find_2_3, rfl, os_res_body_2_3⟩, ⟨Data.core623, os_res_find_2_4, rfl, os_res_body_2_4⟩]

/-- **`open_stacked__L2`** (`μ = 24`, `r = 1`) is sound. -/
theorem open_stacked_L2_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L2" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 24 1 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_2 os_find_2 rfl os_body_2 (osCallees_2 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_3 : OsCfgOk osCfg3 25 1 ((deriveConfig 25 1).getD []) where
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

theorem osCallees_3 (rd : Reader) : OsCallees rd osCfg3 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L8_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L20_L8_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core624, os_sq_find_3_0, rfl, os_sq_body_3_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L6_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core626, os_sq_find_3_1, rfl, os_sq_body_3_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core628, os_sq_find_3_2, rfl, os_sq_body_3_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core630, os_sq_find_3_3, rfl, os_sq_body_3_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_sound hn hq h, fun a r h => (decode_query_bits_L16_iff rd a r).mp h,
        ⟨Data.core632, os_sq_find_3_4, rfl, os_sq_body_3_4⟩⟩
  fin := fun a r h => (opening_final_message_L8_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L3_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core634, os_res_find_3_0, rfl, os_res_body_3_0⟩, ⟨Data.core635, os_res_find_3_1, rfl, os_res_body_3_1⟩, ⟨Data.core636, os_res_find_3_2, rfl, os_res_body_3_2⟩, ⟨Data.core637, os_res_find_3_3, rfl, os_res_body_3_3⟩, ⟨Data.core638, os_res_find_3_4, rfl, os_res_body_3_4⟩]

/-- **`open_stacked__L3`** (`μ = 25`, `r = 1`) is sound. -/
theorem open_stacked_L3_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L3" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 25 1 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_3 os_find_3 rfl os_body_3 (osCallees_3 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_4 : OsCfgOk osCfg4 26 1 ((deriveConfig 26 1).getD []) where
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

theorem osCallees_4 (rd : Reader) : OsCallees rd osCfg4 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L8_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L21_L8_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core639, os_sq_find_4_0, rfl, os_sq_body_4_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L6_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core641, os_sq_find_4_1, rfl, os_sq_body_4_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core643, os_sq_find_4_2, rfl, os_sq_body_4_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core645, os_sq_find_4_3, rfl, os_sq_body_4_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_sound hn hq h, fun a r h => (decode_query_bits_L17_iff rd a r).mp h,
        ⟨Data.core646, os_sq_find_4_4, rfl, os_sq_body_4_4⟩⟩
  fin := fun a r h => (opening_final_message_L16_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L4_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core647, os_res_find_4_0, rfl, os_res_body_4_0⟩, ⟨Data.core648, os_res_find_4_1, rfl, os_res_body_4_1⟩, ⟨Data.core649, os_res_find_4_2, rfl, os_res_body_4_2⟩, ⟨Data.core650, os_res_find_4_3, rfl, os_res_body_4_3⟩, ⟨Data.core651, os_res_find_4_4, rfl, os_res_body_4_4⟩]

/-- **`open_stacked__L4`** (`μ = 26`, `r = 1`) is sound. -/
theorem open_stacked_L4_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L4" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 26 1 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_4 os_find_4 rfl os_body_4 (osCallees_4 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_5 : OsCfgOk osCfg5 27 1 ((deriveConfig 27 1).getD []) where
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

theorem osCallees_5 (rd : Reader) : OsCallees rd osCfg5 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L8_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L22_L8_sound hn hq h, fun a r h => (decode_query_bits_L22_iff rd a r).mp h,
        ⟨Data.core652, os_sq_find_5_0, rfl, os_sq_body_5_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L6_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core654, os_sq_find_5_1, rfl, os_sq_body_5_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core656, os_sq_find_5_2, rfl, os_sq_body_5_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core658, os_sq_find_5_3, rfl, os_sq_body_5_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core659, os_sq_find_5_4, rfl, os_sq_body_5_4⟩⟩
  fin := fun a r h => (opening_final_message_L32_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L5_iff rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core660, os_res_find_5_0, rfl, os_res_body_5_0⟩, ⟨Data.core661, os_res_find_5_1, rfl, os_res_body_5_1⟩, ⟨Data.core662, os_res_find_5_2, rfl, os_res_body_5_2⟩, ⟨Data.core663, os_res_find_5_3, rfl, os_res_body_5_3⟩, ⟨Data.core664, os_res_find_5_4, rfl, os_res_body_5_4⟩]

/-- **`open_stacked__L5`** (`μ = 27`, `r = 1`) is sound. -/
theorem open_stacked_L5_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L5" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 27 1 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_5 os_find_5 rfl os_body_5 (osCallees_5 rd) hroot h

set_option maxRecDepth 100000 in
theorem osCfgOk_6 : OsCfgOk osCfg6 28 1 ((deriveConfig 28 1).getD []) where
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

theorem osCallees_6 (rd : Reader) : OsCallees rd osCfg6 where
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L8_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L23_L8_sound hn hq h, fun a r h => (decode_query_bits_L23_iff rd a r).mp h,
        ⟨Data.core665, os_sq_find_6_0, rfl, os_sq_body_6_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L6_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L6_sound hn hq h, fun a r h => (decode_query_bits_L22_iff rd a r).mp h,
        ⟨Data.core667, os_sq_find_6_1, rfl, os_sq_body_6_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_sound hn hq h, fun a r h => (decode_query_bits_L21_iff rd a r).mp h,
        ⟨Data.core669, os_sq_find_6_2, rfl, os_sq_body_6_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_sound hn hq h, fun a r h => (decode_query_bits_L20_iff rd a r).mp h,
        ⟨Data.core671, os_sq_find_6_3, rfl, os_sq_body_6_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L5_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_sound hn hq h, fun a r h => (decode_query_bits_L19_iff rd a r).mp h,
        ⟨Data.core672, os_sq_find_6_4, rfl, os_sq_body_6_4⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iff rd a r).mp h, fun a r h => (verify_merkle_cap_L4_iff rd a r).mp h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L4_sound hn hq h, fun a r h => (decode_query_bits_L18_iff rd a r).mp h,
        ⟨Data.core673, os_sq_find_6_5, rfl, os_sq_body_6_5⟩⟩
  fin := fun a r h => (opening_final_message_L4_iff rd a r).mp h
  ff := fun a r h => (fold_final_msg_L2_iff rd a r).mp h
  res := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    exacts [⟨Data.core676, os_res_find_6_0, rfl, os_res_body_6_0⟩, ⟨Data.core677, os_res_find_6_1, rfl, os_res_body_6_1⟩, ⟨Data.core678, os_res_find_6_2, rfl, os_res_body_6_2⟩, ⟨Data.core679, os_res_find_6_3, rfl, os_res_body_6_3⟩, ⟨Data.core680, os_res_find_6_4, rfl, os_res_body_6_4⟩, ⟨Data.core681, os_res_find_6_5, rfl, os_res_body_6_5⟩]

/-- **`open_stacked__L6`** (`μ = 28`, `r = 1`) is sound. -/
theorem open_stacked_L6_sound {rd : Reader} {root : Digest} {fs0 fs1 target root0 root1 cur : E}
    {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd "open_stacked__L6" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd 28 1 root fs0 fs1 target cur rets :=
  open_stacked_sound osCfgOk_6 os_find_6 rfl os_body_6 (osCallees_6 rd) hroot h

end
end LeanVM.Guest.B1
