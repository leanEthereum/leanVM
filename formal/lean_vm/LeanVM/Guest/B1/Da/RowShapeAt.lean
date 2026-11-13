/-
  LeanVM.Guest.B1.Da.RowShapeAt

  `da_row_shape` in the uniform placed form: it reads `g_squares[L]` in its caller's words, its
  range checks the memory below `2^16`.
-/

module

public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Da.RowShapeComplete
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# `da_row_shape`, placed

`da_row_shape` is atoms and a return, with one load, `g_squares·g^L`; its range checks read the
memory below `2^16` (`LowDef 16`), which is no load. `row_shape_completeAt`: with
`g_squares = g^s` and the word `g^(2^L)` at `g^(s + L)` among the caller's words, it is
`CompleteAtD` with the shape's returns.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (LowDef CompleteAtD Returns disj_nil)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- `da_row_shape`'s atoms. -/
def rsAs : List Atom := [
    .const (.n 3) (word 1 0), .add (.n 4) (.n 0) (.n 3), .hint (.inverse (.n 4) (.n 5)),
    .assertNe (.n 4) (.n 5) (.n 6), .const (.n 7) (word (2 ^ guest_const% DA_MAX_ROWS) 0),
    .rangeCheck (.n 0) (.n 8) (.n 9) (.n 10) (.n 7), .const (.n 11) (word (2 ^ guest_const% DA_LOG_MAX_ROWS) 0),
    .rangeCheck (.n 1) (.n 12) (.n 13) (.n 14) (.n 11), .mul (.n 15) (.n 2) (.n 1),
    .load (.n 16) (.n 15) 0, .mul (.n 16) (.n 17) (.n 0),
    .const (.n 18) (word (2 ^ guest_const% DA_MAX_ROWS) 0), .rangeCheck (.n 17) (.n 19) (.n 20) (.n 21) (.n 18),
    .const (.n 22) (word (2 ^ (guest_const% DA_MAX_ROWS - 1)) 0), .mul (.n 23) (.n 0) (.n 0),
    .const (.n 24) (word 2 0), .mul (.n 25) (.n 16) (.n 24), .mul (.n 23) (.n 26) (.n 25),
    .rangeCheck (.n 26) (.n 27) (.n 28) (.n 29) (.n 22), .copy (.n 30) (.n 16),
    .copy (.n 31) (.n 17)]

theorem rs_split : Fn.body fn% «da_row_shape» = rsAs.map Stmt.atom ++ [.ret [.n 30, .n 31]] := by
  rw [da_row_shape_body]; rfl

theorem rs_loop : coreProgram.loop "da_row_shape" = false := by
  rw [Program.loop_of_find? find_da_row_shape]; decide +kernel

/-- **`da_row_shape` is complete, placed**, reading `g_squares[L]` among the caller's words. -/
theorem row_shape_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {s r L : ℕ} (hr1 : 1 ≤ r)
    (hr : r ≤ LeanDa.maxRows) (hL : 2 ^ L = LeanDa.paddedRowCount r) :
    CompleteAtD fs cert 16 "da_row_shape" [(s + L, [gen ^ 2 ^ L])] [gen ^ r, gen ^ L, gen ^ s]
      (Returns [gen ^ 2 ^ L, gen ^ (2 ^ L - r)]) := by
  intro fp
  refine ⟨fs "da_row_shape", [], _, [], ⟨rfl, rfl⟩, fun q hq => by simp at hq, disj_nil,
    fun rd hlow hm => ?_⟩
  simp only [List.append_nil, List.nil_append] at hm
  have hq := reads_of_memL hm List.mem_cons_self
  have hsq : LoadHolds rd (gen ^ s) L (gen ^ 2 ^ L) := by
    have := hq 0 (by simp)
    rw [← Nat.add_zero L, ← loadHolds_mul_gen_pow, ← pow_add]
    simpa using this
  have hrel := da_row_shape_complete' rd hlow (gen ^ s) r L hsq hr1 hr hL
  obtain ⟨σ, hp, hh⟩ := (rel_iff_sem find_da_row_shape _ _).mp hrel
  rw [rs_split, holdsList_atoms_ret] at hh
  obtain ⟨hat, hr⟩ := hh
  have hpar : (fn% «da_row_shape»).params = [.n 0, .n 1, .n 2] := rfl
  rw [hpar] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  have h15 : σ (.n 15) = gen ^ s * gen ^ L := by
    have := hat (.mul (.n 15) (.n 2) (.n 1)) (by simp [rsAs])
    simp only [Atom.Holds] at this
    rw [this, hp.2.2, hp.2.1]
  refine relAtIn_atoms find_da_row_shape rs_split rs_loop (by decide) (by rw [hpar]; simp [hp])
    hat hr (fun q hq => by
      rw [show rsAs.filterMap atomAddr? = [] by decide] at hq; exact absurd hq List.not_mem_nil) (fun q hq => ?_) (fun i hi => ?_)
  · have e : rsAs.filterMap atomLoad? = [(.n 15, 0)] := by decide
    rw [e, List.mem_singleton] at hq
    subst hq
    refine ⟨s + L, by rw [h15, ← pow_add, limb0_gen_pow_mul]; rfl, Or.inl ?_⟩
    simpa using regionL_of_mem (L := [(s + L, [gen ^ 2 ^ L])]) List.mem_cons_self
      (k := 0) (by simp)
  · obtain ⟨q, hq, -⟩ := hi; simp at hq

end
end LeanVM.Guest.B1.Da
