/-
  LeanVM.Guest.B1.Whir.OsInst1

  `open_stacked__L7` to `open_stacked__L13`: their callees, placed.
-/

module

public import LeanVM.Guest.B1.Whir.OsInstBase

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-!
# `open_stacked__L7` to `open_stacked__L13`, their callees

For each configuration, `OsKidsAt`: group 1's callees at its names (`OsCalleesAtD`), its levels'
caps and queries (`vmc_completeAt_*`, `oq_completeAt_*`), its loops' bodies and checks.
-/

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

set_option maxRecDepth 100000 in
theorem osKidsAt_7 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg7 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg16
  foldFinal := h1.foldFinal4
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L18_L7 fs cert κ hq.f457)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_7_0 rfl os_sq_body_7_0
        (by show coreProgram.loop "__loop170" = true; rw [Program.loop_of_find? os_sq_find_7_0]; decide +kernel)
        os_res_find_7_0 rfl os_res_body_7_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L6 fs cert κ hq.f437)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_7_1 rfl os_sq_body_7_1
        (by show coreProgram.loop "__loop171" = true; rw [Program.loop_of_find? os_sq_find_7_1]; decide +kernel)
        os_res_find_7_1 rfl os_res_body_7_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L16_L5 fs cert κ hq.f438)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_7_2 rfl os_sq_body_7_2
        (by show coreProgram.loop "__loop172" = true; rw [Program.loop_of_find? os_sq_find_7_2]; decide +kernel)
        os_res_find_7_2 rfl os_res_body_7_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L15_L5 fs cert κ hq.f434)
        (h1.decode (15, "decode_query_bits__L15") (by decide)) (by decide +kernel) os_sq_find_7_3 rfl os_sq_body_7_3
        (by show coreProgram.loop "__loop173" = true; rw [Program.loop_of_find? os_sq_find_7_3]; decide +kernel)
        os_res_find_7_3 rfl os_res_body_7_3
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_8 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg8 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg32
  foldFinal := h1.foldFinal5
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L19_L7 fs cert κ hq.f458)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_8_0 rfl os_sq_body_8_0
        (by show coreProgram.loop "__loop178" = true; rw [Program.loop_of_find? os_sq_find_8_0]; decide +kernel)
        os_res_find_8_0 rfl os_res_body_8_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L6 fs cert κ hq.f440)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_8_1 rfl os_sq_body_8_1
        (by show coreProgram.loop "__loop179" = true; rw [Program.loop_of_find? os_sq_find_8_1]; decide +kernel)
        os_res_find_8_1 rfl os_res_body_8_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L5 fs cert κ hq.f441)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_8_2 rfl os_sq_body_8_2
        (by show coreProgram.loop "__loop180" = true; rw [Program.loop_of_find? os_sq_find_8_2]; decide +kernel)
        os_res_find_8_2 rfl os_res_body_8_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L16_L5 fs cert κ hq.f438)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_8_3 rfl os_sq_body_8_3
        (by show coreProgram.loop "__loop181" = true; rw [Program.loop_of_find? os_sq_find_8_3]; decide +kernel)
        os_res_find_8_3 rfl os_res_body_8_3
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_9 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg9 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg4
  foldFinal := h1.foldFinal2
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L20_L7 fs cert κ hq.f459)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_9_0 rfl os_sq_body_9_0
        (by show coreProgram.loop "__loop186" = true; rw [Program.loop_of_find? os_sq_find_9_0]; decide +kernel)
        os_res_find_9_0 rfl os_res_body_9_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L6 fs cert κ hq.f443)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_9_1 rfl os_sq_body_9_1
        (by show coreProgram.loop "__loop187" = true; rw [Program.loop_of_find? os_sq_find_9_1]; decide +kernel)
        os_res_find_9_1 rfl os_res_body_9_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L5 fs cert κ hq.f444)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_9_2 rfl os_sq_body_9_2
        (by show coreProgram.loop "__loop188" = true; rw [Program.loop_of_find? os_sq_find_9_2]; decide +kernel)
        os_res_find_9_2 rfl os_res_body_9_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L5 fs cert κ hq.f441)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_9_3 rfl os_sq_body_9_3
        (by show coreProgram.loop "__loop189" = true; rw [Program.loop_of_find? os_sq_find_9_3]; decide +kernel)
        os_res_find_9_3 rfl os_res_body_9_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L16_L4 fs cert κ hq.f460)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_9_4 rfl os_sq_body_9_4
        (by show coreProgram.loop "__loop190" = true; rw [Program.loop_of_find? os_sq_find_9_4]; decide +kernel)
        os_res_find_9_4 rfl os_res_body_9_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_10 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg10 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg8
  foldFinal := h1.foldFinal3
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L21_L7 fs cert κ hq.f461)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_10_0 rfl os_sq_body_10_0
        (by show coreProgram.loop "__loop196" = true; rw [Program.loop_of_find? os_sq_find_10_0]; decide +kernel)
        os_res_find_10_0 rfl os_res_body_10_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L6 fs cert κ hq.f446)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_10_1 rfl os_sq_body_10_1
        (by show coreProgram.loop "__loop197" = true; rw [Program.loop_of_find? os_sq_find_10_1]; decide +kernel)
        os_res_find_10_1 rfl os_res_body_10_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L5 fs cert κ hq.f447)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_10_2 rfl os_sq_body_10_2
        (by show coreProgram.loop "__loop198" = true; rw [Program.loop_of_find? os_sq_find_10_2]; decide +kernel)
        os_res_find_10_2 rfl os_res_body_10_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L5 fs cert κ hq.f444)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_10_3 rfl os_sq_body_10_3
        (by show coreProgram.loop "__loop199" = true; rw [Program.loop_of_find? os_sq_find_10_3]; decide +kernel)
        os_res_find_10_3 rfl os_res_body_10_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L4 fs cert κ hq.f462)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_10_4 rfl os_sq_body_10_4
        (by show coreProgram.loop "__loop200" = true; rw [Program.loop_of_find? os_sq_find_10_4]; decide +kernel)
        os_res_find_10_4 rfl os_res_body_10_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_11 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg11 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg16
  foldFinal := h1.foldFinal4
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L22_L7 fs cert κ hq.f463)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_11_0 rfl os_sq_body_11_0
        (by show coreProgram.loop "__loop206" = true; rw [Program.loop_of_find? os_sq_find_11_0]; decide +kernel)
        os_res_find_11_0 rfl os_res_body_11_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L6 fs cert κ hq.f449)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_11_1 rfl os_sq_body_11_1
        (by show coreProgram.loop "__loop207" = true; rw [Program.loop_of_find? os_sq_find_11_1]; decide +kernel)
        os_res_find_11_1 rfl os_res_body_11_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L5 fs cert κ hq.f450)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_11_2 rfl os_sq_body_11_2
        (by show coreProgram.loop "__loop208" = true; rw [Program.loop_of_find? os_sq_find_11_2]; decide +kernel)
        os_res_find_11_2 rfl os_res_body_11_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L5 fs cert κ hq.f447)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_11_3 rfl os_sq_body_11_3
        (by show coreProgram.loop "__loop209" = true; rw [Program.loop_of_find? os_sq_find_11_3]; decide +kernel)
        os_res_find_11_3 rfl os_res_body_11_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L4 fs cert κ hq.f455)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_11_4 rfl os_sq_body_11_4
        (by show coreProgram.loop "__loop210" = true; rw [Program.loop_of_find? os_sq_find_11_4]; decide +kernel)
        os_res_find_11_4 rfl os_res_body_11_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_12 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg12 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg32
  foldFinal := h1.foldFinal5
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L23_L7 fs cert κ hq.f464)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_12_0 rfl os_sq_body_12_0
        (by show coreProgram.loop "__loop216" = true; rw [Program.loop_of_find? os_sq_find_12_0]; decide +kernel)
        os_res_find_12_0 rfl os_res_body_12_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L22_L6 fs cert κ hq.f452)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_12_1 rfl os_sq_body_12_1
        (by show coreProgram.loop "__loop217" = true; rw [Program.loop_of_find? os_sq_find_12_1]; decide +kernel)
        os_res_find_12_1 rfl os_res_body_12_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L5 fs cert κ hq.f453)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_12_2 rfl os_sq_body_12_2
        (by show coreProgram.loop "__loop218" = true; rw [Program.loop_of_find? os_sq_find_12_2]; decide +kernel)
        os_res_find_12_2 rfl os_res_body_12_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L5 fs cert κ hq.f450)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_12_3 rfl os_sq_body_12_3
        (by show coreProgram.loop "__loop219" = true; rw [Program.loop_of_find? os_sq_find_12_3]; decide +kernel)
        os_res_find_12_3 rfl os_res_body_12_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L4 fs cert κ hq.f465)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_12_4 rfl os_sq_body_12_4
        (by show coreProgram.loop "__loop220" = true; rw [Program.loop_of_find? os_sq_find_12_4]; decide +kernel)
        os_res_find_12_4 rfl os_res_body_12_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_13 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg13 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg4
  foldFinal := h1.foldFinal2
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L24_L7 fs cert κ hq.f466)
        (h1.decode (24, "decode_query_bits__L24") (by decide)) (by decide +kernel) os_sq_find_13_0 rfl os_sq_body_13_0
        (by show coreProgram.loop "__loop226" = true; rw [Program.loop_of_find? os_sq_find_13_0]; decide +kernel)
        os_res_find_13_0 rfl os_res_body_13_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L23_L6 fs cert κ hq.f467)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_13_1 rfl os_sq_body_13_1
        (by show coreProgram.loop "__loop227" = true; rw [Program.loop_of_find? os_sq_find_13_1]; decide +kernel)
        os_res_find_13_1 rfl os_res_body_13_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L22_L5 fs cert κ hq.f468)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_13_2 rfl os_sq_body_13_2
        (by show coreProgram.loop "__loop228" = true; rw [Program.loop_of_find? os_sq_find_13_2]; decide +kernel)
        os_res_find_13_2 rfl os_res_body_13_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L5 fs cert κ hq.f453)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_13_3 rfl os_sq_body_13_3
        (by show coreProgram.loop "__loop229" = true; rw [Program.loop_of_find? os_sq_find_13_3]; decide +kernel)
        os_res_find_13_3 rfl os_res_body_13_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L4 fs cert κ hq.f469)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_13_4 rfl os_sq_body_13_4
        (by show coreProgram.loop "__loop230" = true; rw [Program.loop_of_find? os_sq_find_13_4]; decide +kernel)
        os_res_find_13_4 rfl os_res_body_13_4
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L4 fs cert κ hq.f465)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_13_5 rfl os_sq_body_13_5
        (by show coreProgram.loop "__loop231" = true; rw [Program.loop_of_find? os_sq_find_13_5]; decide +kernel)
        os_res_find_13_5 rfl os_res_body_13_5
        (by decide +kernel)

end
end LeanVM.Guest.B1
