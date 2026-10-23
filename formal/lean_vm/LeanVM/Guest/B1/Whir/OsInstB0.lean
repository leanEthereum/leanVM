/-
  LeanVM.Guest.B1.Whir.OsInstB0

  `open_stacked__L0` to `open_stacked__L6`: their callees, placed, by bounded trees.
-/

module

public import LeanVM.Guest.B1.Whir.OsInstBaseB

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-!
# `open_stacked__L0` to `open_stacked__L6`, their callees by bounded trees

For each configuration, `OsKidsAtB` at `osBd`: group 1's callees at its names (`osKB_*`), its
levels' caps and queries (`vmc_completeAtB_*`, `oq_completeAtB_*`), its loops' bodies and checks.
-/

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

set_option maxRecDepth 100000 in
theorem osKidsAtB_0 (h1 : OsCalleesAtB fs cert κ) (hm : OsCalleesMax h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizes fs) : OsKidsAtB fs cert κ osCfg0 (osBd fs hm hp osCfg0) where
  fold := osKB_fold hm hp _
  canonical := osKB_canonical hm hp _
  ood := osKB_ood hm hp _
  grind := osKB_grind hm hp _
  finalMsg := osKB_finalMsg16 hm hp _
  foldFinal := osKB_foldFinal4 hm hp _
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAtB_mk hi (osKB_rowWeights6 hm hp _) (by decide +kernel) (vmc_completeAtB_L8 fs cert κ)
        (oq_completeAtB_L1_L64_L8_L17_L8 fs cert κ hq.f430) (by decide +kernel)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_0_0 rfl os_sq_body_0_0
        (by show coreProgram.loop "__loop102" = true; rw [Program.loop_of_find? os_sq_find_0_0]; decide +kernel)
        os_res_find_0_0 rfl os_res_body_0_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L6 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L16_L6 fs cert κ hq.f432) (by decide +kernel)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_0_1 rfl os_sq_body_0_1
        (by show coreProgram.loop "__loop103" = true; rw [Program.loop_of_find? os_sq_find_0_1]; decide +kernel)
        os_res_find_0_1 rfl os_res_body_0_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L15_L5 fs cert κ hq.f434) (by decide +kernel)
        (h1.decode (15, "decode_query_bits__L15") (by decide)) (by decide +kernel) os_sq_find_0_2 rfl os_sq_body_0_2
        (by show coreProgram.loop "__loop104" = true; rw [Program.loop_of_find? os_sq_find_0_2]; decide +kernel)
        os_res_find_0_2 rfl os_res_body_0_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L14_L5 fs cert κ hq.f435) (by decide +kernel)
        (h1.decode (14, "decode_query_bits__L14") (by decide)) (by decide +kernel) os_sq_find_0_3 rfl os_sq_body_0_3
        (by show coreProgram.loop "__loop105" = true; rw [Program.loop_of_find? os_sq_find_0_3]; decide +kernel)
        os_res_find_0_3 rfl os_res_body_0_3
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_1 (h1 : OsCalleesAtB fs cert κ) (hm : OsCalleesMax h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizes fs) : OsKidsAtB fs cert κ osCfg1 (osBd fs hm hp osCfg1) where
  fold := osKB_fold hm hp _
  canonical := osKB_canonical hm hp _
  ood := osKB_ood hm hp _
  grind := osKB_grind hm hp _
  finalMsg := osKB_finalMsg32 hm hp _
  foldFinal := osKB_foldFinal5 hm hp _
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAtB_mk hi (osKB_rowWeights6 hm hp _) (by decide +kernel) (vmc_completeAtB_L8 fs cert κ)
        (oq_completeAtB_L1_L64_L8_L18_L8 fs cert κ hq.f436) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_1_0 rfl os_sq_body_1_0
        (by show coreProgram.loop "__loop110" = true; rw [Program.loop_of_find? os_sq_find_1_0]; decide +kernel)
        os_res_find_1_0 rfl os_res_body_1_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L6 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L17_L6 fs cert κ hq.f437) (by decide +kernel)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_1_1 rfl os_sq_body_1_1
        (by show coreProgram.loop "__loop111" = true; rw [Program.loop_of_find? os_sq_find_1_1]; decide +kernel)
        os_res_find_1_1 rfl os_res_body_1_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L16_L5 fs cert κ hq.f438) (by decide +kernel)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_1_2 rfl os_sq_body_1_2
        (by show coreProgram.loop "__loop112" = true; rw [Program.loop_of_find? os_sq_find_1_2]; decide +kernel)
        os_res_find_1_2 rfl os_res_body_1_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L15_L5 fs cert κ hq.f434) (by decide +kernel)
        (h1.decode (15, "decode_query_bits__L15") (by decide)) (by decide +kernel) os_sq_find_1_3 rfl os_sq_body_1_3
        (by show coreProgram.loop "__loop113" = true; rw [Program.loop_of_find? os_sq_find_1_3]; decide +kernel)
        os_res_find_1_3 rfl os_res_body_1_3
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_2 (h1 : OsCalleesAtB fs cert κ) (hm : OsCalleesMax h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizes fs) : OsKidsAtB fs cert κ osCfg2 (osBd fs hm hp osCfg2) where
  fold := osKB_fold hm hp _
  canonical := osKB_canonical hm hp _
  ood := osKB_ood hm hp _
  grind := osKB_grind hm hp _
  finalMsg := osKB_finalMsg4 hm hp _
  foldFinal := osKB_foldFinal2 hm hp _
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAtB_mk hi (osKB_rowWeights6 hm hp _) (by decide +kernel) (vmc_completeAtB_L8 fs cert κ)
        (oq_completeAtB_L1_L64_L8_L19_L8 fs cert κ hq.f439) (by decide +kernel)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_2_0 rfl os_sq_body_2_0
        (by show coreProgram.loop "__loop118" = true; rw [Program.loop_of_find? os_sq_find_2_0]; decide +kernel)
        os_res_find_2_0 rfl os_res_body_2_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L6 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L18_L6 fs cert κ hq.f440) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_2_1 rfl os_sq_body_2_1
        (by show coreProgram.loop "__loop119" = true; rw [Program.loop_of_find? os_sq_find_2_1]; decide +kernel)
        os_res_find_2_1 rfl os_res_body_2_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L17_L5 fs cert κ hq.f441) (by decide +kernel)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_2_2 rfl os_sq_body_2_2
        (by show coreProgram.loop "__loop120" = true; rw [Program.loop_of_find? os_sq_find_2_2]; decide +kernel)
        os_res_find_2_2 rfl os_res_body_2_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L16_L5 fs cert κ hq.f438) (by decide +kernel)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_2_3 rfl os_sq_body_2_3
        (by show coreProgram.loop "__loop121" = true; rw [Program.loop_of_find? os_sq_find_2_3]; decide +kernel)
        os_res_find_2_3 rfl os_res_body_2_3
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L15_L5 fs cert κ hq.f434) (by decide +kernel)
        (h1.decode (15, "decode_query_bits__L15") (by decide)) (by decide +kernel) os_sq_find_2_4 rfl os_sq_body_2_4
        (by show coreProgram.loop "__loop122" = true; rw [Program.loop_of_find? os_sq_find_2_4]; decide +kernel)
        os_res_find_2_4 rfl os_res_body_2_4
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_3 (h1 : OsCalleesAtB fs cert κ) (hm : OsCalleesMax h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizes fs) : OsKidsAtB fs cert κ osCfg3 (osBd fs hm hp osCfg3) where
  fold := osKB_fold hm hp _
  canonical := osKB_canonical hm hp _
  ood := osKB_ood hm hp _
  grind := osKB_grind hm hp _
  finalMsg := osKB_finalMsg8 hm hp _
  foldFinal := osKB_foldFinal3 hm hp _
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAtB_mk hi (osKB_rowWeights6 hm hp _) (by decide +kernel) (vmc_completeAtB_L8 fs cert κ)
        (oq_completeAtB_L1_L64_L8_L20_L8 fs cert κ hq.f442) (by decide +kernel)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_3_0 rfl os_sq_body_3_0
        (by show coreProgram.loop "__loop128" = true; rw [Program.loop_of_find? os_sq_find_3_0]; decide +kernel)
        os_res_find_3_0 rfl os_res_body_3_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L6 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L19_L6 fs cert κ hq.f443) (by decide +kernel)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_3_1 rfl os_sq_body_3_1
        (by show coreProgram.loop "__loop129" = true; rw [Program.loop_of_find? os_sq_find_3_1]; decide +kernel)
        os_res_find_3_1 rfl os_res_body_3_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L18_L5 fs cert κ hq.f444) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_3_2 rfl os_sq_body_3_2
        (by show coreProgram.loop "__loop130" = true; rw [Program.loop_of_find? os_sq_find_3_2]; decide +kernel)
        os_res_find_3_2 rfl os_res_body_3_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L17_L5 fs cert κ hq.f441) (by decide +kernel)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_3_3 rfl os_sq_body_3_3
        (by show coreProgram.loop "__loop131" = true; rw [Program.loop_of_find? os_sq_find_3_3]; decide +kernel)
        os_res_find_3_3 rfl os_res_body_3_3
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L16_L5 fs cert κ hq.f438) (by decide +kernel)
        (h1.decode (16, "decode_query_bits__L16") (by decide)) (by decide +kernel) os_sq_find_3_4 rfl os_sq_body_3_4
        (by show coreProgram.loop "__loop132" = true; rw [Program.loop_of_find? os_sq_find_3_4]; decide +kernel)
        os_res_find_3_4 rfl os_res_body_3_4
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_4 (h1 : OsCalleesAtB fs cert κ) (hm : OsCalleesMax h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizes fs) : OsKidsAtB fs cert κ osCfg4 (osBd fs hm hp osCfg4) where
  fold := osKB_fold hm hp _
  canonical := osKB_canonical hm hp _
  ood := osKB_ood hm hp _
  grind := osKB_grind hm hp _
  finalMsg := osKB_finalMsg16 hm hp _
  foldFinal := osKB_foldFinal4 hm hp _
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAtB_mk hi (osKB_rowWeights6 hm hp _) (by decide +kernel) (vmc_completeAtB_L8 fs cert κ)
        (oq_completeAtB_L1_L64_L8_L21_L8 fs cert κ hq.f445) (by decide +kernel)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_4_0 rfl os_sq_body_4_0
        (by show coreProgram.loop "__loop138" = true; rw [Program.loop_of_find? os_sq_find_4_0]; decide +kernel)
        os_res_find_4_0 rfl os_res_body_4_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L6 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L20_L6 fs cert κ hq.f446) (by decide +kernel)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_4_1 rfl os_sq_body_4_1
        (by show coreProgram.loop "__loop139" = true; rw [Program.loop_of_find? os_sq_find_4_1]; decide +kernel)
        os_res_find_4_1 rfl os_res_body_4_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L19_L5 fs cert κ hq.f447) (by decide +kernel)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_4_2 rfl os_sq_body_4_2
        (by show coreProgram.loop "__loop140" = true; rw [Program.loop_of_find? os_sq_find_4_2]; decide +kernel)
        os_res_find_4_2 rfl os_res_body_4_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L18_L5 fs cert κ hq.f444) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_4_3 rfl os_sq_body_4_3
        (by show coreProgram.loop "__loop141" = true; rw [Program.loop_of_find? os_sq_find_4_3]; decide +kernel)
        os_res_find_4_3 rfl os_res_body_4_3
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L17_L5 fs cert κ hq.f441) (by decide +kernel)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_4_4 rfl os_sq_body_4_4
        (by show coreProgram.loop "__loop142" = true; rw [Program.loop_of_find? os_sq_find_4_4]; decide +kernel)
        os_res_find_4_4 rfl os_res_body_4_4
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_5 (h1 : OsCalleesAtB fs cert κ) (hm : OsCalleesMax h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizes fs) : OsKidsAtB fs cert κ osCfg5 (osBd fs hm hp osCfg5) where
  fold := osKB_fold hm hp _
  canonical := osKB_canonical hm hp _
  ood := osKB_ood hm hp _
  grind := osKB_grind hm hp _
  finalMsg := osKB_finalMsg32 hm hp _
  foldFinal := osKB_foldFinal5 hm hp _
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAtB_mk hi (osKB_rowWeights6 hm hp _) (by decide +kernel) (vmc_completeAtB_L8 fs cert κ)
        (oq_completeAtB_L1_L64_L8_L22_L8 fs cert κ hq.f448) (by decide +kernel)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_5_0 rfl os_sq_body_5_0
        (by show coreProgram.loop "__loop148" = true; rw [Program.loop_of_find? os_sq_find_5_0]; decide +kernel)
        os_res_find_5_0 rfl os_res_body_5_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L6 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L21_L6 fs cert κ hq.f449) (by decide +kernel)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_5_1 rfl os_sq_body_5_1
        (by show coreProgram.loop "__loop149" = true; rw [Program.loop_of_find? os_sq_find_5_1]; decide +kernel)
        os_res_find_5_1 rfl os_res_body_5_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L20_L5 fs cert κ hq.f450) (by decide +kernel)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_5_2 rfl os_sq_body_5_2
        (by show coreProgram.loop "__loop150" = true; rw [Program.loop_of_find? os_sq_find_5_2]; decide +kernel)
        os_res_find_5_2 rfl os_res_body_5_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L19_L5 fs cert κ hq.f447) (by decide +kernel)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_5_3 rfl os_sq_body_5_3
        (by show coreProgram.loop "__loop151" = true; rw [Program.loop_of_find? os_sq_find_5_3]; decide +kernel)
        os_res_find_5_3 rfl os_res_body_5_3
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L18_L5 fs cert κ hq.f444) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_5_4 rfl os_sq_body_5_4
        (by show coreProgram.loop "__loop152" = true; rw [Program.loop_of_find? os_sq_find_5_4]; decide +kernel)
        os_res_find_5_4 rfl os_res_body_5_4
        (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAtB_6 (h1 : OsCalleesAtB fs cert κ) (hm : OsCalleesMax h1) (hq : OsOqFits fs cert)
    (hp : OsPureSizes fs) : OsKidsAtB fs cert κ osCfg6 (osBd fs hm hp osCfg6) where
  fold := osKB_fold hm hp _
  canonical := osKB_canonical hm hp _
  ood := osKB_ood hm hp _
  grind := osKB_grind hm hp _
  finalMsg := osKB_finalMsg4 hm hp _
  foldFinal := osKB_foldFinal2 hm hp _
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact osLvKidsAtB_mk hi (osKB_rowWeights6 hm hp _) (by decide +kernel) (vmc_completeAtB_L8 fs cert κ)
        (oq_completeAtB_L1_L64_L8_L23_L8 fs cert κ hq.f451) (by decide +kernel)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_6_0 rfl os_sq_body_6_0
        (by show coreProgram.loop "__loop158" = true; rw [Program.loop_of_find? os_sq_find_6_0]; decide +kernel)
        os_res_find_6_0 rfl os_res_body_6_0
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L6 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L22_L6 fs cert κ hq.f452) (by decide +kernel)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_6_1 rfl os_sq_body_6_1
        (by show coreProgram.loop "__loop159" = true; rw [Program.loop_of_find? os_sq_find_6_1]; decide +kernel)
        os_res_find_6_1 rfl os_res_body_6_1
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L21_L5 fs cert κ hq.f453) (by decide +kernel)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_6_2 rfl os_sq_body_6_2
        (by show coreProgram.loop "__loop160" = true; rw [Program.loop_of_find? os_sq_find_6_2]; decide +kernel)
        os_res_find_6_2 rfl os_res_body_6_2
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L20_L5 fs cert κ hq.f450) (by decide +kernel)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_6_3 rfl os_sq_body_6_3
        (by show coreProgram.loop "__loop161" = true; rw [Program.loop_of_find? os_sq_find_6_3]; decide +kernel)
        os_res_find_6_3 rfl os_res_body_6_3
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L5 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L19_L5 fs cert κ hq.f447) (by decide +kernel)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_6_4 rfl os_sq_body_6_4
        (by show coreProgram.loop "__loop162" = true; rw [Program.loop_of_find? os_sq_find_6_4]; decide +kernel)
        os_res_find_6_4 rfl os_res_body_6_4
        (by decide +kernel) (by decide +kernel)
    · exact osLvKidsAtB_mk hi (osKB_rowWeights4 hm hp _) (by decide +kernel) (vmc_completeAtB_L4 fs cert κ)
        (oq_completeAtB_L0_L16_L6_L18_L4 fs cert κ hq.f455) (by decide +kernel)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_6_5 rfl os_sq_body_6_5
        (by show coreProgram.loop "__loop163" = true; rw [Program.loop_of_find? os_sq_find_6_5]; decide +kernel)
        os_res_find_6_5 rfl os_res_body_6_5
        (by decide +kernel) (by decide +kernel)

end
end LeanVM.Guest.B1
