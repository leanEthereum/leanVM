/-
  LeanVM.Guest.B1.Whir.OsInstAll

  `open_stacked` complete, placed, at every candidate: `CompleteOpenAt` with `CapAgrees`.
-/

module

public import LeanVM.Guest.B1.Whir.OsInst0
public import LeanVM.Guest.B1.Whir.OsInst1
public import LeanVM.Guest.B1.Whir.OsInst2
public import LeanVM.Guest.B1.Whir.OsInst3
public import LeanVM.Guest.B1.Whir.StackedInst0
public import LeanVM.Guest.B1.Whir.StackedInst1
public import LeanVM.Guest.B1.Whir.StackedInst2
public import LeanVM.Guest.B1.Whir.StackedInst3
public import LeanVM.Guest.B1.VerifySub.CompleteIface

/-!
# `open_stacked`, placed, at every candidate (TRIAGE #36)

`open_stacked_completeAt`: from the 28 configurations' body facts (`OsAllBodyFacts`, decided per
configuration), group 1's callees (`OsCalleesAtD`) and the queries loops' certificate facts
(`OsOqFits`), `CompleteOpenAt fs cert k CapAgrees`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The 28 configurations' body facts. -/
structure OsAllBodyFacts : Prop where
  b0 : OsBodyFacts osCfg0
  b1 : OsBodyFacts osCfg1
  b2 : OsBodyFacts osCfg2
  b3 : OsBodyFacts osCfg3
  b4 : OsBodyFacts osCfg4
  b5 : OsBodyFacts osCfg5
  b6 : OsBodyFacts osCfg6
  b7 : OsBodyFacts osCfg7
  b8 : OsBodyFacts osCfg8
  b9 : OsBodyFacts osCfg9
  b10 : OsBodyFacts osCfg10
  b11 : OsBodyFacts osCfg11
  b12 : OsBodyFacts osCfg12
  b13 : OsBodyFacts osCfg13
  b14 : OsBodyFacts osCfg14
  b15 : OsBodyFacts osCfg15
  b16 : OsBodyFacts osCfg16
  b17 : OsBodyFacts osCfg17
  b18 : OsBodyFacts osCfg18
  b19 : OsBodyFacts osCfg19
  b20 : OsBodyFacts osCfg20
  b21 : OsBodyFacts osCfg21
  b22 : OsBodyFacts osCfg22
  b23 : OsBodyFacts osCfg23
  b24 : OsBodyFacts osCfg24
  b25 : OsBodyFacts osCfg25
  b26 : OsBodyFacts osCfg26
  b27 : OsBodyFacts osCfg27

set_option maxRecDepth 100000 in
/-- **`open_stacked` is complete, placed, at every candidate.** -/
theorem open_stacked_completeAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (hbf : OsAllBodyFacts)
    (h1 : OsCalleesAtD fs cert k) (hq : OsOqFits fs cert) : CompleteOpenAt fs cert k CapAgrees := by
  intro μ r hμ1 hμ2 hr1 hr2
  interval_cases μ <;> interval_cases r
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_0 hbf.b0 (osKidsAt_0 h1 hq)
      osCallees_0 os_find_0 rfl os_body_0 (by rw [Program.loop_of_find? os_find_0]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_7 hbf.b7 (osKidsAt_7 h1 hq)
      osCallees_7 os_find_7 rfl os_body_7 (by rw [Program.loop_of_find? os_find_7]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_14 hbf.b14 (osKidsAt_14 h1 hq)
      osCallees_14 os_find_14 rfl os_body_14 (by rw [Program.loop_of_find? os_find_14]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_21 hbf.b21 (osKidsAt_21 h1 hq)
      osCallees_21 os_find_21 rfl os_body_21 (by rw [Program.loop_of_find? os_find_21]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_1 hbf.b1 (osKidsAt_1 h1 hq)
      osCallees_1 os_find_1 rfl os_body_1 (by rw [Program.loop_of_find? os_find_1]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_8 hbf.b8 (osKidsAt_8 h1 hq)
      osCallees_8 os_find_8 rfl os_body_8 (by rw [Program.loop_of_find? os_find_8]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_15 hbf.b15 (osKidsAt_15 h1 hq)
      osCallees_15 os_find_15 rfl os_body_15 (by rw [Program.loop_of_find? os_find_15]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_22 hbf.b22 (osKidsAt_22 h1 hq)
      osCallees_22 os_find_22 rfl os_body_22 (by rw [Program.loop_of_find? os_find_22]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_2 hbf.b2 (osKidsAt_2 h1 hq)
      osCallees_2 os_find_2 rfl os_body_2 (by rw [Program.loop_of_find? os_find_2]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_9 hbf.b9 (osKidsAt_9 h1 hq)
      osCallees_9 os_find_9 rfl os_body_9 (by rw [Program.loop_of_find? os_find_9]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_16 hbf.b16 (osKidsAt_16 h1 hq)
      osCallees_16 os_find_16 rfl os_body_16 (by rw [Program.loop_of_find? os_find_16]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_23 hbf.b23 (osKidsAt_23 h1 hq)
      osCallees_23 os_find_23 rfl os_body_23 (by rw [Program.loop_of_find? os_find_23]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_3 hbf.b3 (osKidsAt_3 h1 hq)
      osCallees_3 os_find_3 rfl os_body_3 (by rw [Program.loop_of_find? os_find_3]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_10 hbf.b10 (osKidsAt_10 h1 hq)
      osCallees_10 os_find_10 rfl os_body_10 (by rw [Program.loop_of_find? os_find_10]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_17 hbf.b17 (osKidsAt_17 h1 hq)
      osCallees_17 os_find_17 rfl os_body_17 (by rw [Program.loop_of_find? os_find_17]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_24 hbf.b24 (osKidsAt_24 h1 hq)
      osCallees_24 os_find_24 rfl os_body_24 (by rw [Program.loop_of_find? os_find_24]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_4 hbf.b4 (osKidsAt_4 h1 hq)
      osCallees_4 os_find_4 rfl os_body_4 (by rw [Program.loop_of_find? os_find_4]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_11 hbf.b11 (osKidsAt_11 h1 hq)
      osCallees_11 os_find_11 rfl os_body_11 (by rw [Program.loop_of_find? os_find_11]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_18 hbf.b18 (osKidsAt_18 h1 hq)
      osCallees_18 os_find_18 rfl os_body_18 (by rw [Program.loop_of_find? os_find_18]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_25 hbf.b25 (osKidsAt_25 h1 hq)
      osCallees_25 os_find_25 rfl os_body_25 (by rw [Program.loop_of_find? os_find_25]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_5 hbf.b5 (osKidsAt_5 h1 hq)
      osCallees_5 os_find_5 rfl os_body_5 (by rw [Program.loop_of_find? os_find_5]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_12 hbf.b12 (osKidsAt_12 h1 hq)
      osCallees_12 os_find_12 rfl os_body_12 (by rw [Program.loop_of_find? os_find_12]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_19 hbf.b19 (osKidsAt_19 h1 hq)
      osCallees_19 os_find_19 rfl os_body_19 (by rw [Program.loop_of_find? os_find_19]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_26 hbf.b26 (osKidsAt_26 h1 hq)
      osCallees_26 os_find_26 rfl os_body_26 (by rw [Program.loop_of_find? os_find_26]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_6 hbf.b6 (osKidsAt_6 h1 hq)
      osCallees_6 os_find_6 rfl os_body_6 (by rw [Program.loop_of_find? os_find_6]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_13 hbf.b13 (osKidsAt_13 h1 hq)
      osCallees_13 os_find_13 rfl os_body_13 (by rw [Program.loop_of_find? os_find_13]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_20 hbf.b20 (osKidsAt_20 h1 hq)
      osCallees_20 os_find_20 rfl os_body_20 (by rw [Program.loop_of_find? os_find_20]; decide +kernel) hrun hcap hLin
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => os_completeOpenAt osCfgOk_27 hbf.b27 (osKidsAt_27 h1 hq)
      osCallees_27 os_find_27 rfl os_body_27 (by rw [Program.loop_of_find? os_find_27]; decide +kernel) hrun hcap hLin

end
end LeanVM.Guest.B1
