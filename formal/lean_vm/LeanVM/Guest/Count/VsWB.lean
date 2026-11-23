/-
  LeanVM.Guest.Count.VsWB

  `verify_tables`' and the terminal's weight bounds at the deployed instance (`B1.VerifySub.vtWB`,
  `termWB` at `Count.vsWords`), by the kernel, through the search tree's lookups: `kcVtW`,
  `kcTermW` (`Count/VsCountData`).
-/

module

public import LeanVM.Guest.CoreRef
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

/-- The xmss arm's frame weights, by the tree where the frame has the name (`main_loop2` aside). -/
noncomputable def ωArmFast (op : Opcode) (f : String) : ℕ :=
  match wNameIdx f with
  | some j => if f = name% main_loop2 then B2C.ωArm B2C.xmssArmC op f
      else (B2C.plumbOf (j + 1)).pmax.getD (B2C.opIdx op) 0
  | none => B2C.ωArm B2C.xmssArmC op f

theorem ωArmFast_eq : ωArmFast = B2C.ωArm B2C.xmssArmC := by
  funext op f
  unfold ωArmFast
  rcases h : wNameIdx f with _ | j
  · rfl
  · dsimp only
    split_ifs with hx
    · rfl
    · rw [ωArm_idx (wNameIdx_spec h) hx]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **`verify_tables`' weight bound at the deployed instance**: its closed form (`vtWeightB_form`) at the
search tree's lookups. -/
theorem vtWB_eq (op : Opcode) : B1.VerifySub.vtWB vsWords op = kcVtW op := by
  refine (vtWeightB_form op).trans ?_
  rw [← ωArmFast_eq, ← kuSBFast_eq, ← kuSKFast_eq]
  cases op <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The terminal's weight bound at the deployed instance**: its closed form (`termW_form`) at the search
tree's lookups. -/
theorem termWB_eq (op : Opcode) : B1.VerifySub.termWB vsWords op = kcTermW op := by
  refine (termW_form op).trans ?_
  rw [← ωArmFast_eq, ← kuSBFast_eq, ← fsFast_eq]
  cases op <;> decide +kernel

end
end LeanVM.Guest.Count
