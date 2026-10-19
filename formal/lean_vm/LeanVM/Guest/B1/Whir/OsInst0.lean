/-
  LeanVM.Guest.B1.Whir.OsInst0

  `open_stacked__L0` to `open_stacked__L6`: their callees, placed.
-/

module

public import LeanVM.Guest.B1.Whir.OsInstBase

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-!
# `open_stacked__L0` to `open_stacked__L6`, their callees

For each configuration, `OsKidsAt`: group 1's callees at its names (`OsCalleesAtD`), its levels'
caps and queries (`vmc_completeAt_*`, `oq_completeAt_*`), its loops' bodies and checks.
-/

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

set_option maxRecDepth 100000 in
theorem osKidsAt_0 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg0 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg16
  foldFinal := h1.foldFinal4
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L8 fs cert κ) (oq_completeAt_L1_L64_L8_L17_L8 fs cert κ hq.f430)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_0_0 rfl os_sq_body_0_0
        (by show coreProgram.loop "__loop102" = true; rw [Program.loop_of_find? os_sq_find_0_0]; decide +kernel)
        os_res_find_0_0 rfl os_res_body_0_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L16_L6 fs cert κ hq.f432)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_0_1 rfl os_sq_body_0_1
        (by show coreProgram.loop "__loop103" = true; rw [Program.loop_of_find? os_sq_find_0_1]; decide +kernel)
        os_res_find_0_1 rfl os_res_body_0_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L15_L5 fs cert κ hq.f434)
        (h1.decode (15, "decode_query_bits__L15") (by decide)) (by decide +kernel) os_sq_find_0_2 rfl os_sq_body_0_2
        (by show coreProgram.loop "__loop104" = true; rw [Program.loop_of_find? os_sq_find_0_2]; decide +kernel)
        os_res_find_0_2 rfl os_res_body_0_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L14_L5 fs cert κ hq.f435)
        (h1.decode (14, "decode_query_bits__L14") (by decide)) (by decide +kernel) os_sq_find_0_3 rfl os_sq_body_0_3
        (by show coreProgram.loop "__loop105" = true; rw [Program.loop_of_find? os_sq_find_0_3]; decide +kernel)
        os_res_find_0_3 rfl os_res_body_0_3
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_1 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg1 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg32
  foldFinal := h1.foldFinal5
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L8 fs cert κ) (oq_completeAt_L1_L64_L8_L18_L8 fs cert κ hq.f436)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_1_0 rfl os_sq_body_1_0
        (by show coreProgram.loop "__loop110" = true; rw [Program.loop_of_find? os_sq_find_1_0]; decide +kernel)
        os_res_find_1_0 rfl os_res_body_1_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L6 fs cert κ hq.f437)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_1_1 rfl os_sq_body_1_1
        (by show coreProgram.loop "__loop111" = true; rw [Program.loop_of_find? os_sq_find_1_1]; decide +kernel)
        os_res_find_1_1 rfl os_res_body_1_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L16_L5 fs cert κ hq.f438)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_1_2 rfl os_sq_body_1_2
        (by show coreProgram.loop "__loop112" = true; rw [Program.loop_of_find? os_sq_find_1_2]; decide +kernel)
        os_res_find_1_2 rfl os_res_body_1_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L15_L5 fs cert κ hq.f434)
        (h1.decode (15, "decode_query_bits__L15") (by decide)) (by decide +kernel) os_sq_find_1_3 rfl os_sq_body_1_3
        (by show coreProgram.loop "__loop113" = true; rw [Program.loop_of_find? os_sq_find_1_3]; decide +kernel)
        os_res_find_1_3 rfl os_res_body_1_3
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_2 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg2 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg4
  foldFinal := h1.foldFinal2
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L8 fs cert κ) (oq_completeAt_L1_L64_L8_L19_L8 fs cert κ hq.f439)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_2_0 rfl os_sq_body_2_0
        (by show coreProgram.loop "__loop118" = true; rw [Program.loop_of_find? os_sq_find_2_0]; decide +kernel)
        os_res_find_2_0 rfl os_res_body_2_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L6 fs cert κ hq.f440)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_2_1 rfl os_sq_body_2_1
        (by show coreProgram.loop "__loop119" = true; rw [Program.loop_of_find? os_sq_find_2_1]; decide +kernel)
        os_res_find_2_1 rfl os_res_body_2_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L5 fs cert κ hq.f441)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_2_2 rfl os_sq_body_2_2
        (by show coreProgram.loop "__loop120" = true; rw [Program.loop_of_find? os_sq_find_2_2]; decide +kernel)
        os_res_find_2_2 rfl os_res_body_2_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L16_L5 fs cert κ hq.f438)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_2_3 rfl os_sq_body_2_3
        (by show coreProgram.loop "__loop121" = true; rw [Program.loop_of_find? os_sq_find_2_3]; decide +kernel)
        os_res_find_2_3 rfl os_res_body_2_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L15_L5 fs cert κ hq.f434)
        (h1.decode (15, "decode_query_bits__L15") (by decide)) (by decide +kernel) os_sq_find_2_4 rfl os_sq_body_2_4
        (by show coreProgram.loop "__loop122" = true; rw [Program.loop_of_find? os_sq_find_2_4]; decide +kernel)
        os_res_find_2_4 rfl os_res_body_2_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_3 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg3 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg8
  foldFinal := h1.foldFinal3
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L8 fs cert κ) (oq_completeAt_L1_L64_L8_L20_L8 fs cert κ hq.f442)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_3_0 rfl os_sq_body_3_0
        (by show coreProgram.loop "__loop128" = true; rw [Program.loop_of_find? os_sq_find_3_0]; decide +kernel)
        os_res_find_3_0 rfl os_res_body_3_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L6 fs cert κ hq.f443)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_3_1 rfl os_sq_body_3_1
        (by show coreProgram.loop "__loop129" = true; rw [Program.loop_of_find? os_sq_find_3_1]; decide +kernel)
        os_res_find_3_1 rfl os_res_body_3_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L5 fs cert κ hq.f444)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_3_2 rfl os_sq_body_3_2
        (by show coreProgram.loop "__loop130" = true; rw [Program.loop_of_find? os_sq_find_3_2]; decide +kernel)
        os_res_find_3_2 rfl os_res_body_3_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L5 fs cert κ hq.f441)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_3_3 rfl os_sq_body_3_3
        (by show coreProgram.loop "__loop131" = true; rw [Program.loop_of_find? os_sq_find_3_3]; decide +kernel)
        os_res_find_3_3 rfl os_res_body_3_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L16_L5 fs cert κ hq.f438)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_3_4 rfl os_sq_body_3_4
        (by show coreProgram.loop "__loop132" = true; rw [Program.loop_of_find? os_sq_find_3_4]; decide +kernel)
        os_res_find_3_4 rfl os_res_body_3_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_4 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg4 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg16
  foldFinal := h1.foldFinal4
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L8 fs cert κ) (oq_completeAt_L1_L64_L8_L21_L8 fs cert κ hq.f445)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_4_0 rfl os_sq_body_4_0
        (by show coreProgram.loop "__loop138" = true; rw [Program.loop_of_find? os_sq_find_4_0]; decide +kernel)
        os_res_find_4_0 rfl os_res_body_4_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L6 fs cert κ hq.f446)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_4_1 rfl os_sq_body_4_1
        (by show coreProgram.loop "__loop139" = true; rw [Program.loop_of_find? os_sq_find_4_1]; decide +kernel)
        os_res_find_4_1 rfl os_res_body_4_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L5 fs cert κ hq.f447)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_4_2 rfl os_sq_body_4_2
        (by show coreProgram.loop "__loop140" = true; rw [Program.loop_of_find? os_sq_find_4_2]; decide +kernel)
        os_res_find_4_2 rfl os_res_body_4_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L5 fs cert κ hq.f444)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_4_3 rfl os_sq_body_4_3
        (by show coreProgram.loop "__loop141" = true; rw [Program.loop_of_find? os_sq_find_4_3]; decide +kernel)
        os_res_find_4_3 rfl os_res_body_4_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L5 fs cert κ hq.f441)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_4_4 rfl os_sq_body_4_4
        (by show coreProgram.loop "__loop142" = true; rw [Program.loop_of_find? os_sq_find_4_4]; decide +kernel)
        os_res_find_4_4 rfl os_res_body_4_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_5 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg5 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg32
  foldFinal := h1.foldFinal5
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L8 fs cert κ) (oq_completeAt_L1_L64_L8_L22_L8 fs cert κ hq.f448)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_5_0 rfl os_sq_body_5_0
        (by show coreProgram.loop "__loop148" = true; rw [Program.loop_of_find? os_sq_find_5_0]; decide +kernel)
        os_res_find_5_0 rfl os_res_body_5_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L6 fs cert κ hq.f449)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_5_1 rfl os_sq_body_5_1
        (by show coreProgram.loop "__loop149" = true; rw [Program.loop_of_find? os_sq_find_5_1]; decide +kernel)
        os_res_find_5_1 rfl os_res_body_5_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L5 fs cert κ hq.f450)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_5_2 rfl os_sq_body_5_2
        (by show coreProgram.loop "__loop150" = true; rw [Program.loop_of_find? os_sq_find_5_2]; decide +kernel)
        os_res_find_5_2 rfl os_res_body_5_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L5 fs cert κ hq.f447)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_5_3 rfl os_sq_body_5_3
        (by show coreProgram.loop "__loop151" = true; rw [Program.loop_of_find? os_sq_find_5_3]; decide +kernel)
        os_res_find_5_3 rfl os_res_body_5_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L5 fs cert κ hq.f444)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_5_4 rfl os_sq_body_5_4
        (by show coreProgram.loop "__loop152" = true; rw [Program.loop_of_find? os_sq_find_5_4]; decide +kernel)
        os_res_find_5_4 rfl os_res_body_5_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_6 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg6 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg4
  foldFinal := h1.foldFinal2
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L8 fs cert κ) (oq_completeAt_L1_L64_L8_L23_L8 fs cert κ hq.f451)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_6_0 rfl os_sq_body_6_0
        (by show coreProgram.loop "__loop158" = true; rw [Program.loop_of_find? os_sq_find_6_0]; decide +kernel)
        os_res_find_6_0 rfl os_res_body_6_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L0_L16_L6_L22_L6 fs cert κ hq.f452)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_6_1 rfl os_sq_body_6_1
        (by show coreProgram.loop "__loop159" = true; rw [Program.loop_of_find? os_sq_find_6_1]; decide +kernel)
        os_res_find_6_1 rfl os_res_body_6_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L5 fs cert κ hq.f453)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_6_2 rfl os_sq_body_6_2
        (by show coreProgram.loop "__loop160" = true; rw [Program.loop_of_find? os_sq_find_6_2]; decide +kernel)
        os_res_find_6_2 rfl os_res_body_6_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L5 fs cert κ hq.f450)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_6_3 rfl os_sq_body_6_3
        (by show coreProgram.loop "__loop161" = true; rw [Program.loop_of_find? os_sq_find_6_3]; decide +kernel)
        os_res_find_6_3 rfl os_res_body_6_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L5 fs cert κ hq.f447)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_6_4 rfl os_sq_body_6_4
        (by show coreProgram.loop "__loop162" = true; rw [Program.loop_of_find? os_sq_find_6_4]; decide +kernel)
        os_res_find_6_4 rfl os_res_body_6_4
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L4 fs cert κ hq.f455)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_6_5 rfl os_sq_body_6_5
        (by show coreProgram.loop "__loop163" = true; rw [Program.loop_of_find? os_sq_find_6_5]; decide +kernel)
        os_res_find_6_5 rfl os_res_body_6_5
        (by decide +kernel)

end
end LeanVM.Guest.B1
