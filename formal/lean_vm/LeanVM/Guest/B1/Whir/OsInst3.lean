/-
  LeanVM.Guest.B1.Whir.OsInst3

  `open_stacked__L21` to `open_stacked__L27`: their callees, placed.
-/

module

public import LeanVM.Guest.B1.Whir.OsInstBase

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-!
# `open_stacked__L21` to `open_stacked__L27`, their callees

For each configuration, `OsKidsAt`: group 1's callees at its names (`OsCalleesAtD`), its levels'
caps and queries (`vmc_completeAt_*`, `oq_completeAt_*`), its loops' bodies and checks.
-/

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

set_option maxRecDepth 100000 in
theorem osKidsAt_21 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg21 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg16
  foldFinal := h1.foldFinal4
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L1_L64_L8_L20_L6 fs cert κ hq.f474)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_21_0 rfl os_sq_body_21_0
        (by show coreProgram.loop "__loop306" = true; rw [Program.loop_of_find? os_sq_find_21_0]; decide +kernel)
        os_res_find_21_0 rfl os_res_body_21_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L5 fs cert κ hq.f447)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_21_1 rfl os_sq_body_21_1
        (by show coreProgram.loop "__loop307" = true; rw [Program.loop_of_find? os_sq_find_21_1]; decide +kernel)
        os_res_find_21_1 rfl os_res_body_21_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L5 fs cert κ hq.f444)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_21_2 rfl os_sq_body_21_2
        (by show coreProgram.loop "__loop308" = true; rw [Program.loop_of_find? os_sq_find_21_2]; decide +kernel)
        os_res_find_21_2 rfl os_res_body_21_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L17_L5 fs cert κ hq.f441)
        (h1.decode (17, "decode_query_bits__L17") (by decide)) (by decide +kernel) os_sq_find_21_3 rfl os_sq_body_21_3
        (by show coreProgram.loop "__loop309" = true; rw [Program.loop_of_find? os_sq_find_21_3]; decide +kernel)
        os_res_find_21_3 rfl os_res_body_21_3
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_22 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg22 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg32
  foldFinal := h1.foldFinal5
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L1_L64_L8_L21_L6 fs cert κ hq.f475)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_22_0 rfl os_sq_body_22_0
        (by show coreProgram.loop "__loop314" = true; rw [Program.loop_of_find? os_sq_find_22_0]; decide +kernel)
        os_res_find_22_0 rfl os_res_body_22_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L5 fs cert κ hq.f450)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_22_1 rfl os_sq_body_22_1
        (by show coreProgram.loop "__loop315" = true; rw [Program.loop_of_find? os_sq_find_22_1]; decide +kernel)
        os_res_find_22_1 rfl os_res_body_22_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L5 fs cert κ hq.f447)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_22_2 rfl os_sq_body_22_2
        (by show coreProgram.loop "__loop316" = true; rw [Program.loop_of_find? os_sq_find_22_2]; decide +kernel)
        os_res_find_22_2 rfl os_res_body_22_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L5 fs cert κ hq.f444)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_22_3 rfl os_sq_body_22_3
        (by show coreProgram.loop "__loop317" = true; rw [Program.loop_of_find? os_sq_find_22_3]; decide +kernel)
        os_res_find_22_3 rfl os_res_body_22_3
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_23 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg23 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg4
  foldFinal := h1.foldFinal2
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L1_L64_L8_L22_L6 fs cert κ hq.f476)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_23_0 rfl os_sq_body_23_0
        (by show coreProgram.loop "__loop322" = true; rw [Program.loop_of_find? os_sq_find_23_0]; decide +kernel)
        os_res_find_23_0 rfl os_res_body_23_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L5 fs cert κ hq.f453)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_23_1 rfl os_sq_body_23_1
        (by show coreProgram.loop "__loop323" = true; rw [Program.loop_of_find? os_sq_find_23_1]; decide +kernel)
        os_res_find_23_1 rfl os_res_body_23_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L5 fs cert κ hq.f450)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_23_2 rfl os_sq_body_23_2
        (by show coreProgram.loop "__loop324" = true; rw [Program.loop_of_find? os_sq_find_23_2]; decide +kernel)
        os_res_find_23_2 rfl os_res_body_23_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L5 fs cert κ hq.f447)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_23_3 rfl os_sq_body_23_3
        (by show coreProgram.loop "__loop325" = true; rw [Program.loop_of_find? os_sq_find_23_3]; decide +kernel)
        os_res_find_23_3 rfl os_res_body_23_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L18_L4 fs cert κ hq.f455)
        (h1.decode (18, "decode_query_bits__L18") (by decide)) (by decide +kernel) os_sq_find_23_4 rfl os_sq_body_23_4
        (by show coreProgram.loop "__loop326" = true; rw [Program.loop_of_find? os_sq_find_23_4]; decide +kernel)
        os_res_find_23_4 rfl os_res_body_23_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_24 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg24 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg8
  foldFinal := h1.foldFinal3
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L1_L64_L8_L23_L6 fs cert κ hq.f477)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_24_0 rfl os_sq_body_24_0
        (by show coreProgram.loop "__loop332" = true; rw [Program.loop_of_find? os_sq_find_24_0]; decide +kernel)
        os_res_find_24_0 rfl os_res_body_24_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L22_L5 fs cert κ hq.f468)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_24_1 rfl os_sq_body_24_1
        (by show coreProgram.loop "__loop333" = true; rw [Program.loop_of_find? os_sq_find_24_1]; decide +kernel)
        os_res_find_24_1 rfl os_res_body_24_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L5 fs cert κ hq.f453)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_24_2 rfl os_sq_body_24_2
        (by show coreProgram.loop "__loop334" = true; rw [Program.loop_of_find? os_sq_find_24_2]; decide +kernel)
        os_res_find_24_2 rfl os_res_body_24_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L5 fs cert κ hq.f450)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_24_3 rfl os_sq_body_24_3
        (by show coreProgram.loop "__loop335" = true; rw [Program.loop_of_find? os_sq_find_24_3]; decide +kernel)
        os_res_find_24_3 rfl os_res_body_24_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L19_L4 fs cert κ hq.f465)
        (h1.decode (19, "decode_query_bits__L19") (by decide)) (by decide +kernel) os_sq_find_24_4 rfl os_sq_body_24_4
        (by show coreProgram.loop "__loop336" = true; rw [Program.loop_of_find? os_sq_find_24_4]; decide +kernel)
        os_res_find_24_4 rfl os_res_body_24_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_25 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg25 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg16
  foldFinal := h1.foldFinal4
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L1_L64_L8_L24_L6 fs cert κ hq.f478)
        (h1.decode (24, "decode_query_bits__L24") (by decide)) (by decide +kernel) os_sq_find_25_0 rfl os_sq_body_25_0
        (by show coreProgram.loop "__loop342" = true; rw [Program.loop_of_find? os_sq_find_25_0]; decide +kernel)
        os_res_find_25_0 rfl os_res_body_25_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L23_L5 fs cert κ hq.f472)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_25_1 rfl os_sq_body_25_1
        (by show coreProgram.loop "__loop343" = true; rw [Program.loop_of_find? os_sq_find_25_1]; decide +kernel)
        os_res_find_25_1 rfl os_res_body_25_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L22_L5 fs cert κ hq.f468)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_25_2 rfl os_sq_body_25_2
        (by show coreProgram.loop "__loop344" = true; rw [Program.loop_of_find? os_sq_find_25_2]; decide +kernel)
        os_res_find_25_2 rfl os_res_body_25_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L5 fs cert κ hq.f453)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_25_3 rfl os_sq_body_25_3
        (by show coreProgram.loop "__loop345" = true; rw [Program.loop_of_find? os_sq_find_25_3]; decide +kernel)
        os_res_find_25_3 rfl os_res_body_25_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L20_L4 fs cert κ hq.f469)
        (h1.decode (20, "decode_query_bits__L20") (by decide)) (by decide +kernel) os_sq_find_25_4 rfl os_sq_body_25_4
        (by show coreProgram.loop "__loop346" = true; rw [Program.loop_of_find? os_sq_find_25_4]; decide +kernel)
        os_res_find_25_4 rfl os_res_body_25_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_26 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg26 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg32
  foldFinal := h1.foldFinal5
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L1_L64_L8_L25_L6 fs cert κ hq.f479)
        (h1.decode (25, "decode_query_bits__L25") (by decide)) (by decide +kernel) os_sq_find_26_0 rfl os_sq_body_26_0
        (by show coreProgram.loop "__loop352" = true; rw [Program.loop_of_find? os_sq_find_26_0]; decide +kernel)
        os_res_find_26_0 rfl os_res_body_26_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L24_L5 fs cert κ hq.f480)
        (h1.decode (24, "decode_query_bits__L24") (by decide)) (by decide +kernel) os_sq_find_26_1 rfl os_sq_body_26_1
        (by show coreProgram.loop "__loop353" = true; rw [Program.loop_of_find? os_sq_find_26_1]; decide +kernel)
        os_res_find_26_1 rfl os_res_body_26_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L23_L5 fs cert κ hq.f472)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_26_2 rfl os_sq_body_26_2
        (by show coreProgram.loop "__loop354" = true; rw [Program.loop_of_find? os_sq_find_26_2]; decide +kernel)
        os_res_find_26_2 rfl os_res_body_26_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L22_L5 fs cert κ hq.f468)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_26_3 rfl os_sq_body_26_3
        (by show coreProgram.loop "__loop355" = true; rw [Program.loop_of_find? os_sq_find_26_3]; decide +kernel)
        os_res_find_26_3 rfl os_res_body_26_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L4 fs cert κ hq.f473)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_26_4 rfl os_sq_body_26_4
        (by show coreProgram.loop "__loop356" = true; rw [Program.loop_of_find? os_sq_find_26_4]; decide +kernel)
        os_res_find_26_4 rfl os_res_body_26_4
        (by decide +kernel)

set_option maxRecDepth 100000 in
theorem osKidsAt_27 (h1 : OsCalleesAtD fs cert κ) (hq : OsOqFits fs cert) : OsKidsAt fs cert κ osCfg27 where
  fold := h1.fold
  canonical := h1.canonical
  ood := h1.ood
  grind := h1.grind
  finalMsg := h1.finalMsg4
  foldFinal := h1.foldFinal2
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact osLvKidsAt_mk h1.rowWeights6 (vmc_completeAt_L6 fs cert κ) (oq_completeAt_L1_L64_L8_L26_L6 fs cert κ hq.f481)
        (h1.decode (26, "decode_query_bits__L26") (by decide)) (by decide +kernel) os_sq_find_27_0 rfl os_sq_body_27_0
        (by show coreProgram.loop "__loop362" = true; rw [Program.loop_of_find? os_sq_find_27_0]; decide +kernel)
        os_res_find_27_0 rfl os_res_body_27_0
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L25_L5 fs cert κ hq.f482)
        (h1.decode (25, "decode_query_bits__L25") (by decide)) (by decide +kernel) os_sq_find_27_1 rfl os_sq_body_27_1
        (by show coreProgram.loop "__loop363" = true; rw [Program.loop_of_find? os_sq_find_27_1]; decide +kernel)
        os_res_find_27_1 rfl os_res_body_27_1
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L24_L5 fs cert κ hq.f480)
        (h1.decode (24, "decode_query_bits__L24") (by decide)) (by decide +kernel) os_sq_find_27_2 rfl os_sq_body_27_2
        (by show coreProgram.loop "__loop364" = true; rw [Program.loop_of_find? os_sq_find_27_2]; decide +kernel)
        os_res_find_27_2 rfl os_res_body_27_2
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L5 fs cert κ) (oq_completeAt_L0_L16_L6_L23_L5 fs cert κ hq.f472)
        (h1.decode (23, "decode_query_bits__L23") (by decide)) (by decide +kernel) os_sq_find_27_3 rfl os_sq_body_27_3
        (by show coreProgram.loop "__loop365" = true; rw [Program.loop_of_find? os_sq_find_27_3]; decide +kernel)
        os_res_find_27_3 rfl os_res_body_27_3
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L22_L4 fs cert κ hq.f483)
        (h1.decode (22, "decode_query_bits__L22") (by decide)) (by decide +kernel) os_sq_find_27_4 rfl os_sq_body_27_4
        (by show coreProgram.loop "__loop366" = true; rw [Program.loop_of_find? os_sq_find_27_4]; decide +kernel)
        os_res_find_27_4 rfl os_res_body_27_4
        (by decide +kernel)
    · exact osLvKidsAt_mk h1.rowWeights4 (vmc_completeAt_L4 fs cert κ) (oq_completeAt_L0_L16_L6_L21_L4 fs cert κ hq.f473)
        (h1.decode (21, "decode_query_bits__L21") (by decide)) (by decide +kernel) os_sq_find_27_5 rfl os_sq_body_27_5
        (by show coreProgram.loop "__loop367" = true; rw [Program.loop_of_find? os_sq_find_27_5]; decide +kernel)
        os_res_find_27_5 rfl os_res_body_27_5
        (by decide +kernel)

end
end LeanVM.Guest.B1
