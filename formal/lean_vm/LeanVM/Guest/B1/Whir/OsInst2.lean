/-
  LeanVM.Guest.B1.Whir.OsInst2

  `open_stacked__L14` to `open_stacked__L20`: their callees, placed.
-/

module

public import LeanVM.Guest.B1.Whir.OsInstBase

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-!
# `open_stacked__L14` to `open_stacked__L20`, their callees

For each configuration, `OsKidsAt`: group 1's callees at its names (`OsCalleesAtD`), its levels'
caps and queries (`vmc_completeAt_*`, `oq_completeAt_*`), its loops' bodies and checks.
-/

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

set_option maxRecDepth 100000 in
theorem osKidsAt_14 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg14 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg16
  foldFinal := h1.foldFinal4
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L19_L7 fs cert κ hq.f458)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_14_0 rfl os_sq_body_14_0
        (by show coreProgram.loop "__loop238" = true; rw [Program.loop_of_find? os_sq_find_14_0]; decide +kernel)
        os_res_find_14_0 rfl os_res_body_14_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L6 fs cert κ hq.f440)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_14_1 rfl os_sq_body_14_1
        (by show coreProgram.loop "__loop239" = true; rw [Program.loop_of_find? os_sq_find_14_1]; decide +kernel)
        os_res_find_14_1 rfl os_res_body_14_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L5 fs cert κ hq.f441)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_14_2 rfl os_sq_body_14_2
        (by show coreProgram.loop "__loop240" = true; rw [Program.loop_of_find? os_sq_find_14_2]; decide +kernel)
        os_res_find_14_2 rfl os_res_body_14_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L16_L5 fs cert κ hq.f438)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_14_3 rfl os_sq_body_14_3
        (by show coreProgram.loop "__loop241" = true; rw [Program.loop_of_find? os_sq_find_14_3]; decide +kernel)
        os_res_find_14_3 rfl os_res_body_14_3
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_15 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg15 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg32
  foldFinal := h1.foldFinal5
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L20_L7 fs cert κ hq.f459)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_15_0 rfl os_sq_body_15_0
        (by show coreProgram.loop "__loop246" = true; rw [Program.loop_of_find? os_sq_find_15_0]; decide +kernel)
        os_res_find_15_0 rfl os_res_body_15_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L6 fs cert κ hq.f443)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_15_1 rfl os_sq_body_15_1
        (by show coreProgram.loop "__loop247" = true; rw [Program.loop_of_find? os_sq_find_15_1]; decide +kernel)
        os_res_find_15_1 rfl os_res_body_15_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L5 fs cert κ hq.f444)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_15_2 rfl os_sq_body_15_2
        (by show coreProgram.loop "__loop248" = true; rw [Program.loop_of_find? os_sq_find_15_2]; decide +kernel)
        os_res_find_15_2 rfl os_res_body_15_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L5 fs cert κ hq.f441)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_15_3 rfl os_sq_body_15_3
        (by show coreProgram.loop "__loop249" = true; rw [Program.loop_of_find? os_sq_find_15_3]; decide +kernel)
        os_res_find_15_3 rfl os_res_body_15_3
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_16 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg16 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg4
  foldFinal := h1.foldFinal2
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L21_L7 fs cert κ hq.f461)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_16_0 rfl os_sq_body_16_0
        (by show coreProgram.loop "__loop254" = true; rw [Program.loop_of_find? os_sq_find_16_0]; decide +kernel)
        os_res_find_16_0 rfl os_res_body_16_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L6 fs cert κ hq.f446)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_16_1 rfl os_sq_body_16_1
        (by show coreProgram.loop "__loop255" = true; rw [Program.loop_of_find? os_sq_find_16_1]; decide +kernel)
        os_res_find_16_1 rfl os_res_body_16_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L5 fs cert κ hq.f447)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_16_2 rfl os_sq_body_16_2
        (by show coreProgram.loop "__loop256" = true; rw [Program.loop_of_find? os_sq_find_16_2]; decide +kernel)
        os_res_find_16_2 rfl os_res_body_16_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L5 fs cert κ hq.f444)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_16_3 rfl os_sq_body_16_3
        (by show coreProgram.loop "__loop257" = true; rw [Program.loop_of_find? os_sq_find_16_3]; decide +kernel)
        os_res_find_16_3 rfl os_res_body_16_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L4 fs cert κ hq.f462)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_16_4 rfl os_sq_body_16_4
        (by show coreProgram.loop "__loop258" = true; rw [Program.loop_of_find? os_sq_find_16_4]; decide +kernel)
        os_res_find_16_4 rfl os_res_body_16_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_17 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg17 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg8
  foldFinal := h1.foldFinal3
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L22_L7 fs cert κ hq.f463)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_17_0 rfl os_sq_body_17_0
        (by show coreProgram.loop "__loop264" = true; rw [Program.loop_of_find? os_sq_find_17_0]; decide +kernel)
        os_res_find_17_0 rfl os_res_body_17_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L6 fs cert κ hq.f449)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_17_1 rfl os_sq_body_17_1
        (by show coreProgram.loop "__loop265" = true; rw [Program.loop_of_find? os_sq_find_17_1]; decide +kernel)
        os_res_find_17_1 rfl os_res_body_17_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L5 fs cert κ hq.f450)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_17_2 rfl os_sq_body_17_2
        (by show coreProgram.loop "__loop266" = true; rw [Program.loop_of_find? os_sq_find_17_2]; decide +kernel)
        os_res_find_17_2 rfl os_res_body_17_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L5 fs cert κ hq.f447)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_17_3 rfl os_sq_body_17_3
        (by show coreProgram.loop "__loop267" = true; rw [Program.loop_of_find? os_sq_find_17_3]; decide +kernel)
        os_res_find_17_3 rfl os_res_body_17_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L4 fs cert κ hq.f455)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_17_4 rfl os_sq_body_17_4
        (by show coreProgram.loop "__loop268" = true; rw [Program.loop_of_find? os_sq_find_17_4]; decide +kernel)
        os_res_find_17_4 rfl os_res_body_17_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_18 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg18 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg16
  foldFinal := h1.foldFinal4
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L23_L7 fs cert κ hq.f464)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_18_0 rfl os_sq_body_18_0
        (by show coreProgram.loop "__loop274" = true; rw [Program.loop_of_find? os_sq_find_18_0]; decide +kernel)
        os_res_find_18_0 rfl os_res_body_18_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L22_L6 fs cert κ hq.f452)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_18_1 rfl os_sq_body_18_1
        (by show coreProgram.loop "__loop275" = true; rw [Program.loop_of_find? os_sq_find_18_1]; decide +kernel)
        os_res_find_18_1 rfl os_res_body_18_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L5 fs cert κ hq.f453)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_18_2 rfl os_sq_body_18_2
        (by show coreProgram.loop "__loop276" = true; rw [Program.loop_of_find? os_sq_find_18_2]; decide +kernel)
        os_res_find_18_2 rfl os_res_body_18_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L5 fs cert κ hq.f450)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_18_3 rfl os_sq_body_18_3
        (by show coreProgram.loop "__loop277" = true; rw [Program.loop_of_find? os_sq_find_18_3]; decide +kernel)
        os_res_find_18_3 rfl os_res_body_18_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L4 fs cert κ hq.f465)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_18_4 rfl os_sq_body_18_4
        (by show coreProgram.loop "__loop278" = true; rw [Program.loop_of_find? os_sq_find_18_4]; decide +kernel)
        os_res_find_18_4 rfl os_res_body_18_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_19 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg19 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg32
  foldFinal := h1.foldFinal5
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L24_L7 fs cert κ hq.f466)
        (h1.decode (24, "decode_query_bits__L24") (by decide)) (by decide +kernel) os_sq_find_19_0 rfl os_sq_body_19_0
        (by show coreProgram.loop "__loop284" = true; rw [Program.loop_of_find? os_sq_find_19_0]; decide +kernel)
        os_res_find_19_0 rfl os_res_body_19_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L23_L6 fs cert κ hq.f467)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_19_1 rfl os_sq_body_19_1
        (by show coreProgram.loop "__loop285" = true; rw [Program.loop_of_find? os_sq_find_19_1]; decide +kernel)
        os_res_find_19_1 rfl os_res_body_19_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L22_L5 fs cert κ hq.f468)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_19_2 rfl os_sq_body_19_2
        (by show coreProgram.loop "__loop286" = true; rw [Program.loop_of_find? os_sq_find_19_2]; decide +kernel)
        os_res_find_19_2 rfl os_res_body_19_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L5 fs cert κ hq.f453)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_19_3 rfl os_sq_body_19_3
        (by show coreProgram.loop "__loop287" = true; rw [Program.loop_of_find? os_sq_find_19_3]; decide +kernel)
        os_res_find_19_3 rfl os_res_body_19_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L4 fs cert κ hq.f469)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_19_4 rfl os_sq_body_19_4
        (by show coreProgram.loop "__loop288" = true; rw [Program.loop_of_find? os_sq_find_19_4]; decide +kernel)
        os_res_find_19_4 rfl os_res_body_19_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_20 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg20 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg4
  foldFinal := h1.foldFinal2
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L7 fs cert κ) (oq_completeAt_L1_L64_L8_L25_L7 fs cert κ hq.f470)
        (h1.decode (25, "decode_query_bits__L25") (by decide)) (by decide +kernel) os_sq_find_20_0 rfl os_sq_body_20_0
        (by show coreProgram.loop "__loop294" = true; rw [Program.loop_of_find? os_sq_find_20_0]; decide +kernel)
        os_res_find_20_0 rfl os_res_body_20_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L24_L6 fs cert κ hq.f471)
        (h1.decode (24, "decode_query_bits__L24") (by decide)) (by decide +kernel) os_sq_find_20_1 rfl os_sq_body_20_1
        (by show coreProgram.loop "__loop295" = true; rw [Program.loop_of_find? os_sq_find_20_1]; decide +kernel)
        os_res_find_20_1 rfl os_res_body_20_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L23_L5 fs cert κ hq.f472)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_20_2 rfl os_sq_body_20_2
        (by show coreProgram.loop "__loop296" = true; rw [Program.loop_of_find? os_sq_find_20_2]; decide +kernel)
        os_res_find_20_2 rfl os_res_body_20_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L22_L5 fs cert κ hq.f468)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_20_3 rfl os_sq_body_20_3
        (by show coreProgram.loop "__loop297" = true; rw [Program.loop_of_find? os_sq_find_20_3]; decide +kernel)
        os_res_find_20_3 rfl os_res_body_20_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L4 fs cert κ hq.f473)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_20_4 rfl os_sq_body_20_4
        (by show coreProgram.loop "__loop298" = true; rw [Program.loop_of_find? os_sq_find_20_4]; decide +kernel)
        os_res_find_20_4 rfl os_res_body_20_4
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L4 fs cert κ hq.f469)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_20_5 rfl os_sq_body_20_5
        (by show coreProgram.loop "__loop299" = true; rw [Program.loop_of_find? os_sq_find_20_5]; decide +kernel)
        os_res_find_20_5 rfl os_res_body_20_5
        (by decide +kernel)

end
end LeanVM.Guest.B1
