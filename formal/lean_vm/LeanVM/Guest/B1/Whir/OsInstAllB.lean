/-
  LeanVM.Guest.B1.Whir.OsInstAllB

  `open_stacked` complete, placed, at every candidate, by bounded trees: `CompleteOpenAtB`.
-/

module

public import LeanVM.Guest.B1.Whir.OsInstB0
public import LeanVM.Guest.B1.Whir.OsInstB1
public import LeanVM.Guest.B1.Whir.OsInstB2
public import LeanVM.Guest.B1.Whir.OsInstB3
public import LeanVM.Guest.B1.Whir.OsInstFacts

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-!
# `open_stacked`, placed, at every candidate, bounded (TRIAGE #36)

`open_stacked_completeAtB`: from group 1's callees by bounded trees (`OsCalleesAtB`) with their
maxima (`OsCalleesMax`), the queries loops' certificate facts (`OsOqFits`) and the pure callees'
sizes (`OsPureSizes`), `CompleteOpenAtB fs cert k CapAgrees (osBop fs hm hp)`: `osBop` the largest
over the 28 configurations of the frame, the buffers and the calls' bounds (`osCfgBound`).
-/

/-- A configuration's bound: its frame, its buffers, its calls at their bounds. -/
def osCfgBound (fs : String → ℕ) {cert : String → V → ℕ} {k : ℕ} {h1 : OsCalleesAtB fs cert k} (hm : OsCalleesMax h1)
    (hp : OsPureSizes fs) (cfg : OsCfg) (name : String) : ℕ :=
  fs name + (osSizes cfg).sum + osCallsMax fs (osBd fs hm hp cfg) cfg

/-- **`open_stacked`'s bound**: the largest configuration's. -/
def osBop (fs : String → ℕ) {cert : String → V → ℕ} {k : ℕ} {h1 : OsCalleesAtB fs cert k} (hm : OsCalleesMax h1)
    (hp : OsPureSizes fs) : ℕ :=
  max (osCfgBound fs hm hp osCfg0 (openName 22 1))
    (max (osCfgBound fs hm hp osCfg1 (openName 23 1))
    (max (osCfgBound fs hm hp osCfg2 (openName 24 1))
    (max (osCfgBound fs hm hp osCfg3 (openName 25 1))
    (max (osCfgBound fs hm hp osCfg4 (openName 26 1))
    (max (osCfgBound fs hm hp osCfg5 (openName 27 1))
    (max (osCfgBound fs hm hp osCfg6 (openName 28 1))
    (max (osCfgBound fs hm hp osCfg7 (openName 22 2))
    (max (osCfgBound fs hm hp osCfg8 (openName 23 2))
    (max (osCfgBound fs hm hp osCfg9 (openName 24 2))
    (max (osCfgBound fs hm hp osCfg10 (openName 25 2))
    (max (osCfgBound fs hm hp osCfg11 (openName 26 2))
    (max (osCfgBound fs hm hp osCfg12 (openName 27 2))
    (max (osCfgBound fs hm hp osCfg13 (openName 28 2))
    (max (osCfgBound fs hm hp osCfg14 (openName 22 3))
    (max (osCfgBound fs hm hp osCfg15 (openName 23 3))
    (max (osCfgBound fs hm hp osCfg16 (openName 24 3))
    (max (osCfgBound fs hm hp osCfg17 (openName 25 3))
    (max (osCfgBound fs hm hp osCfg18 (openName 26 3))
    (max (osCfgBound fs hm hp osCfg19 (openName 27 3))
    (max (osCfgBound fs hm hp osCfg20 (openName 28 3))
    (max (osCfgBound fs hm hp osCfg21 (openName 22 4))
    (max (osCfgBound fs hm hp osCfg22 (openName 23 4))
    (max (osCfgBound fs hm hp osCfg23 (openName 24 4))
    (max (osCfgBound fs hm hp osCfg24 (openName 25 4))
    (max (osCfgBound fs hm hp osCfg25 (openName 26 4))
    (max (osCfgBound fs hm hp osCfg26 (openName 27 4))
    (osCfgBound fs hm hp osCfg27 (openName 28 4))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
/-- **`open_stacked` is complete, placed, at every candidate, by trees of at most `osBop` words.** -/
theorem open_stacked_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (h1 : OsCalleesAtB fs cert k)
    (hm : OsCalleesMax h1) (hq : OsOqFits fs cert) (hp : OsPureSizes fs) :
    CompleteOpenAtB fs cert k CapAgrees (osBop fs hm hp) := by
  intro μ r hμ1 hμ2 hr1 hr2
  interval_cases μ <;> interval_cases r
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_0 osAllBodyFacts.b0
      (osKidsAtB_0 h1 hm hq hp) osCallees_0 os_find_0 rfl os_body_0
      (by rw [Program.loop_of_find? os_find_0]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_left _ _)
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_7 osAllBodyFacts.b7
      (osKidsAtB_7 h1 hm hq hp) osCallees_7 os_find_7 rfl os_body_7
      (by rw [Program.loop_of_find? os_find_7]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_14 osAllBodyFacts.b14
      (osKidsAtB_14 h1 hm hq hp) osCallees_14 os_find_14 rfl os_body_14
      (by rw [Program.loop_of_find? os_find_14]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_21 osAllBodyFacts.b21
      (osKidsAtB_21 h1 hm hq hp) osCallees_21 os_find_21 rfl os_body_21
      (by rw [Program.loop_of_find? os_find_21]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_1 osAllBodyFacts.b1
      (osKidsAtB_1 h1 hm hq hp) osCallees_1 os_find_1 rfl os_body_1
      (by rw [Program.loop_of_find? os_find_1]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_left _ _))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_8 osAllBodyFacts.b8
      (osKidsAtB_8 h1 hm hq hp) osCallees_8 os_find_8 rfl os_body_8
      (by rw [Program.loop_of_find? os_find_8]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_15 osAllBodyFacts.b15
      (osKidsAtB_15 h1 hm hq hp) osCallees_15 os_find_15 rfl os_body_15
      (by rw [Program.loop_of_find? os_find_15]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_22 osAllBodyFacts.b22
      (osKidsAtB_22 h1 hm hq hp) osCallees_22 os_find_22 rfl os_body_22
      (by rw [Program.loop_of_find? os_find_22]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_2 osAllBodyFacts.b2
      (osKidsAtB_2 h1 hm hq hp) osCallees_2 os_find_2 rfl os_body_2
      (by rw [Program.loop_of_find? os_find_2]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_9 osAllBodyFacts.b9
      (osKidsAtB_9 h1 hm hq hp) osCallees_9 os_find_9 rfl os_body_9
      (by rw [Program.loop_of_find? os_find_9]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_16 osAllBodyFacts.b16
      (osKidsAtB_16 h1 hm hq hp) osCallees_16 os_find_16 rfl os_body_16
      (by rw [Program.loop_of_find? os_find_16]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_23 osAllBodyFacts.b23
      (osKidsAtB_23 h1 hm hq hp) osCallees_23 os_find_23 rfl os_body_23
      (by rw [Program.loop_of_find? os_find_23]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_3 osAllBodyFacts.b3
      (osKidsAtB_3 h1 hm hq hp) osCallees_3 os_find_3 rfl os_body_3
      (by rw [Program.loop_of_find? os_find_3]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_10 osAllBodyFacts.b10
      (osKidsAtB_10 h1 hm hq hp) osCallees_10 os_find_10 rfl os_body_10
      (by rw [Program.loop_of_find? os_find_10]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_17 osAllBodyFacts.b17
      (osKidsAtB_17 h1 hm hq hp) osCallees_17 os_find_17 rfl os_body_17
      (by rw [Program.loop_of_find? os_find_17]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_24 osAllBodyFacts.b24
      (osKidsAtB_24 h1 hm hq hp) osCallees_24 os_find_24 rfl os_body_24
      (by rw [Program.loop_of_find? os_find_24]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_4 osAllBodyFacts.b4
      (osKidsAtB_4 h1 hm hq hp) osCallees_4 os_find_4 rfl os_body_4
      (by rw [Program.loop_of_find? os_find_4]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_11 osAllBodyFacts.b11
      (osKidsAtB_11 h1 hm hq hp) osCallees_11 os_find_11 rfl os_body_11
      (by rw [Program.loop_of_find? os_find_11]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_18 osAllBodyFacts.b18
      (osKidsAtB_18 h1 hm hq hp) osCallees_18 os_find_18 rfl os_body_18
      (by rw [Program.loop_of_find? os_find_18]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_25 osAllBodyFacts.b25
      (osKidsAtB_25 h1 hm hq hp) osCallees_25 os_find_25 rfl os_body_25
      (by rw [Program.loop_of_find? os_find_25]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_5 osAllBodyFacts.b5
      (osKidsAtB_5 h1 hm hq hp) osCallees_5 os_find_5 rfl os_body_5
      (by rw [Program.loop_of_find? os_find_5]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_12 osAllBodyFacts.b12
      (osKidsAtB_12 h1 hm hq hp) osCallees_12 os_find_12 rfl os_body_12
      (by rw [Program.loop_of_find? os_find_12]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_19 osAllBodyFacts.b19
      (osKidsAtB_19 h1 hm hq hp) osCallees_19 os_find_19 rfl os_body_19
      (by rw [Program.loop_of_find? os_find_19]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_26 osAllBodyFacts.b26
      (osKidsAtB_26 h1 hm hq hp) osCallees_26 os_find_26 rfl os_body_26
      (by rw [Program.loop_of_find? os_find_26]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_6 osAllBodyFacts.b6
      (osKidsAtB_6 h1 hm hq hp) osCallees_6 os_find_6 rfl os_body_6
      (by rw [Program.loop_of_find? os_find_6]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_13 osAllBodyFacts.b13
      (osKidsAtB_13 h1 hm hq hp) osCallees_13 os_find_13 rfl os_body_13
      (by rw [Program.loop_of_find? os_find_13]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_20 osAllBodyFacts.b20
      (osKidsAtB_20 h1 hm hq hp) osCallees_20 os_find_20 rfl os_body_20
      (by rw [Program.loop_of_find? os_find_20]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => CompleteAtB.mono (os_completeOpenAtB osCfgOk_27 osAllBodyFacts.b27
      (osKidsAtB_27 h1 hm hq hp) osCallees_27 os_find_27 rfl os_body_27
      (by rw [Program.loop_of_find? os_find_27]; decide +kernel) hrun hcap hLin) le_rfl
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))))))))))))))))))))))))

end
end LeanVM.Guest.B1
