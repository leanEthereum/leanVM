/-
  LeanVM.Guest.B1.Place.LqVmc

  `verify_merkle_cap`, placed within its frame.
-/

module

public import LeanVM.Guest.B1.Place.LqTable
public import LeanVM.Guest.B1.Place.LqMem
public import LeanVM.Guest.Lift.OsCallees

/-!
# `verify_merkle_cap`, placed within its frame

Each `verify_merkle_cap__L{D}` of `merkleCapNames` is a leaf placing nothing (`vmc_unplaced`,
decided by the kernel), so its valid trees are its frame alone (`leaf_total`), and on every
memory where its relation holds it is complete placed within its frame (`vmc_completeAtB`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- A leaf placing nothing, as a check. -/
noncomputable def leafUnplB (f : String) : Bool :=
  match coreProgram.find? f with
  | some fn => Lift.Stmt.leafOkList atomUnplaced fn.body
  | none => false

theorem leafUnplB_of {f : String} {fn : Fn} (h : leafUnplB f = true)
    (hf : coreProgram.find? f = some fn) : Lift.Stmt.leafOkList atomUnplaced fn.body = true := by
  unfold leafUnplB at h
  rw [hf] at h
  exact h

set_option maxRecDepth 100000 in
theorem vmc_unplacedB : (merkleCapNames.all fun p ↦ leafUnplB p.1) = true := by
  decide +kernel

/-- **`verify_merkle_cap__L{cd}` is complete placed within its frame** on every memory where its
relation holds. -/
theorem vmc_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {cd : ℕ}
    (hm : (vmcName cd, cd) ∈ merkleCapNames) {Lin : Layout} {args rets : List E}
    (h : ∀ rd, MemL rd Lin → coreProgram.Rel rd (vmcName cd) args rets) :
    CompleteAtB fs cert κ (vmcName cd) Lin args (Returns rets) (fs (vmcName cd)) := by
  obtain ⟨fn, hf, -, hleaf⟩ := leafSpecOk_all merkleCap_leafSpec _ hm
  have hu := leafUnplB_of (List.all_eq_true.mp vmc_unplacedB _ hm) hf
  exact completeAt_of_rel_pureBat (Lift.pureIn_of_leafOk hf hleaf) (List.mem_singleton_self _) h κ
    fun rd t hn hv hb ↦ leaf_total hf hu rd t args rets hn hv hb

/-- **A valid tree of `verify_merkle_cap__L{cd}` is its frame.** -/
theorem vmc_total {fs : String → ℕ} {cd : ℕ} (hm : (vmcName cd, cd) ∈ merkleCapNames) :
    TotalLe coreProgram fs (vmcName cd) (fun _ ↦ fs (vmcName cd)) := by
  obtain ⟨fn, hf, -, -⟩ := leafSpecOk_all merkleCap_leafSpec _ hm
  have hu := leafUnplB_of (List.all_eq_true.mp vmc_unplacedB _ hm) hf
  exact leaf_total hf hu

end
end LeanVM.Guest.B1
