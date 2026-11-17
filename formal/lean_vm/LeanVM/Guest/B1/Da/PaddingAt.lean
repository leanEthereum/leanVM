/-
  LeanVM.Guest.B1.Da.PaddingAt

  `da_padding` in the uniform placed form: it reads no memory, its range check the memory below
  `2^16`.
-/

module

public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Da.PaddingComplete
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# `da_padding`, placed

`da_padding` is atoms and a return, with no load; its range check reads the memory below `2^16`
(`LowDef 16`), which is no load. `padding_completeAt`: it is `CompleteAtD` with its return.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (LowDef CompleteAtD Returns disj_nil)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- `da_padding`'s atoms. -/
def padAs : List Atom := [
    .const (.n 1) (word 1 0), .add (.n 2) (.n 0) (.n 1), .hint (.inverse (.n 2) (.n 3)),
    .assertNe (.n 2) (.n 3) (.n 4), .const (.n 5) (word (2 ^ guest_const% DA_MAX_ROWS) 0),
    .rangeCheck (.n 0) (.n 6) (.n 7) (.n 8) (.n 5), .const (.n 9) (word (2 ^ guest_const% DA_MAX_ROWS) 0),
    .mul (.n 9) (.n 10) (.n 0), .copy (.n 11) (.n 10)]

theorem pad_split : Fn.body fn% «da_padding» = padAs.map Stmt.atom ++ [.ret [.n 11]] := by
  rw [da_padding_body]; rfl

theorem pad_loop : coreProgram.loop "da_padding" = false := by
  rw [Program.loop_of_find? find_da_padding]; decide +kernel

/-- **`da_padding` is complete, placed**: it reads no memory. -/
theorem padding_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : r ≤ LeanDa.maxRows) :
    CompleteAtD fs cert 16 "da_padding" [] [gen ^ r] (Returns [gen ^ (LeanDa.maxRows - r)]) := by
  intro fp
  refine ⟨fs "da_padding", [], _, [], ⟨rfl, rfl⟩, fun q hq => by simp at hq, disj_nil,
    fun rd hlow _ => ?_⟩
  have hrel := da_padding_complete rd hlow r hr1 hr
  obtain ⟨σ, hp, hh⟩ := (rel_iff_sem find_da_padding _ _).mp hrel
  rw [pad_split, holdsList_atoms_ret] at hh
  obtain ⟨hat, hr⟩ := hh
  have hpar : (fn% «da_padding»).params = [.n 0] := rfl
  rw [hpar] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  refine relAtIn_atoms find_da_padding pad_split pad_loop (by decide) (by rw [hpar]; simp [hp])
    hat hr (fun q hq => by
      rw [show padAs.filterMap atomAddr? = [] by decide] at hq; exact absurd hq List.not_mem_nil)
    (fun q hq => by
      rw [show padAs.filterMap atomLoad? = [] by decide] at hq; exact absurd hq List.not_mem_nil)
    (fun i hi => ?_)
  · obtain ⟨q, hq, -⟩ := hi; simp at hq

end
end LeanVM.Guest.B1.Da
