/-
  LeanVM.Guest.Count.VsWB

  `verify_tables`' and the terminal's weight bounds at the deployed instance (`B1.VerifySub.vtWB`,
  `termWB` at `Count.vsWords`), by the kernel, through the search tree's lookups: `kcVtW`,
  `kcTermW` (`Count/VsCountData`).
-/

module

public import LeanVM.Guest.Count.VsWords
public import LeanVM.Guest.Count.Fast
public import LeanVM.Guest.Count.StaticV
public import LeanVM.Guest.Count.VsCountData

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- `kuSB`, by the tree where it has the name. -/
noncomputable def kuSBFast (op : Opcode) (f : String) : ℕ :=
  match wNameIdx f with
  | some j => kuSBJ op j
  | none => kuSB op f

/-- `kuSK`, by the tree where it has the name. -/
noncomputable def kuSKFast (op : Opcode) (f : String) : ℕ :=
  match wNameIdx f with
  | some j => kuSKJ op j
  | none => kuSK op f

theorem kuSBFast_eq : kuSBFast = kuSB := by
  funext op f
  unfold kuSBFast
  rcases h : wNameIdx f with _ | j
  · rfl
  · dsimp only; rw [kuSB_idx (wNameIdx_spec h)]

theorem kuSKFast_eq : kuSKFast = kuSK := by
  funext op f
  unfold kuSKFast
  rcases h : wNameIdx f with _ | j
  · rfl
  · dsimp only; rw [kuSK_idx (wNameIdx_spec h)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **`verify_tables`' weight bound at the deployed instance.** -/
theorem vtWB_eq (op : Opcode) : B1.VerifySub.vtWB vsWords op = kcVtW op := by
  show B2C.ωArm B2C.xmssArmC op "verify_tables" + (B1.Tables.vtBs (kuSB op)
    (B2C.ωArm B2C.xmssArmC op "shared_selector_tables" + 15 * kuSK op "__loop8" + kSpW op)
    (28 * kuSK op "__loop9")).sum = kcVtW op
  rw [ωArm_idx (j := 11) (by decide +kernel) (by decide),
    ωArm_idx (j := 10) (by decide +kernel) (by decide)]
  unfold kSpW
  rw [← kuSBFast_eq, ← kuSKFast_eq]
  cases op <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The terminal's weight bound at the deployed instance.** -/
theorem termWB_eq (op : Opcode) : B1.VerifySub.termWB vsWords op = kcTermW op := by
  show B2C.ωArm B2C.xmssArmC op "check_opening_terminal" +
    (B1.VerifySub.termWs (fun op => kuSB op "eq_prefix_chain")
      (fun op => krVl15A op * max (B2C.fs "__loop14") (32 * 38) / 1000)
      (fun op => kuSB op "selector_tables") kCsW
      (fun op => krVrswA op * (B2C.fs "ring_switch_weight" + 2240 + 16433) / 1000) op).sum =
    kcTermW op
  rw [ωArm_idx (j := 17) (by decide +kernel) (by decide)]
  unfold kCsW
  rw [← kuSBFast_eq, ← fsFast_eq]
  cases op <;> decide +kernel

end
end LeanVM.Guest.Count
