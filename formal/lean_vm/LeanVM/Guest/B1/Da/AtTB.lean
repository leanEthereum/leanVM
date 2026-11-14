/-
  LeanVM.Guest.B1.Da.AtTB

  Helpers for `da_verify`'s bounded honest shapes (`CompleteAtDTB`, the words bounded before the
  memory): the pure callees within their static bounds, `da_row_shape` within its frame, and the
  static bounds `da_verify` rests on (`DvStaticB`).

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.AtT
public import LeanVM.Guest.B1.Da.RowShapeAt
public import LeanVM.Guest.B1.Da.PureAt
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.B1.Da.Offsets
public import LeanVM.Guest.B1.Main.IterK
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# Bounded helpers

`pureB_static`, `pureB_loop`: a pure callee complete within the words its static bound gives
(`TotalLe`; for a loop helper from `1` to `g^m`, `TotalLeOn … LoopPre` of `m` iterations and its
run's phantom frame). `DvStaticB fs SB SK`: the static bounds `da_verify`'s completeness rests on,
`SB g` the words of `g`, `SK g` a loop helper's words per iteration with its run's phantom frame,
which a run charges once (`iterK fs SK g` per iteration and `fs g`). `row_shape_completeAtB`:
`row_shape_completeAt` (same proof) within its frame.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (LowDef CompleteAtD CompleteAtDT CompleteAtDTB Returns disj_nil
  completeAt_of_rel_pureBat)
open LeanVM.Guest.B1.Main (Layout MemL RegionL iterK)

@[expose] public section

/-- **The static bounds `da_verify` rests on**: its loop helpers' runs, `iterK fs SK g` words per
iteration and the run's phantom frame `fs g` once (`TotalLeOn … LoopPre`: the regions' bases, the
blobs' trees, the padding, a column's cells, the column offsets' doublings), the DA levels' words
(`TotalLe`), and the statically bounded callees `da_vector` and `da_expand__L6_L7` within their
static words (`vecB`, a frame). -/
structure DvStaticB (fs : String → ℕ) (SB SK : String → ℕ) : Prop where
  l17 : TotalLeOn coreProgram fs name% «da_verify_loop0» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «da_verify_loop0» + fs name% «da_verify_loop0»)
  l19 : TotalLeOn coreProgram fs name% «da_verify_loop2» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «da_verify_loop2» + fs name% «da_verify_loop2»)
  l20 : TotalLeOn coreProgram fs name% «da_verify_loop3» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «da_verify_loop3» + fs name% «da_verify_loop3»)
  l21 : TotalLeOn coreProgram fs name% «da_verify_column_loop0» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «da_verify_column_loop0» + fs
        name% «da_verify_column_loop0»)
  off : ∀ b < 7, TotalLeOn coreProgram fs (offLoopName b) LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK (offLoopName b) + fs (offLoopName b))
  dl : ∀ j ≤ guest_const% DA_LOG_MAX_ROWS, TotalLe coreProgram fs dlNames[j]! (fun _ => SB dlNames[j]!)
  vec : fs "da_vector" + 28 + (fs "da_factors__L13_L7_L0" + 128 + (fs "da_expand__L13_L7" +
    (fs "da_factors__L6_L7_L128" + 128 + (fs "da_column_offsets" + 945 +
      ((List.range 7).map fun b => 2 ^ b * iterK fs SK (offLoopName b) + fs (offLoopName b)).sum +
        0)))) ≤ SB "da_vector"
  exp : fs "da_expand__L6_L7" ≤ SB "da_expand__L6_L7"

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A pure callee within its static bound.** -/
theorem pureB_static {S : List String} (hS : coreProgram.PureIn S) {g : String} (hg : g ∈ S)
    {κ : ℕ} {Lin : Layout} {args rets : List E} {B : List E → ℕ}
    (h : ∀ rd, MemL rd Lin → coreProgram.Rel rd g args rets) (hT : TotalLe coreProgram fs g B) :
    CompleteAtDTB fs cert κ g Lin args (Returns rets) (fun _ => True) (B args) :=
  (completeAt_of_rel_pureBat hS hg h κ fun rd t hn hv hb => hT rd t args rets hn hv hb).toDTB

/-- **A pure loop helper from `1` to `g^m` within `m` iterations** and a constant (its run's
phantom frame). -/
theorem pureB_loop {S : List String} (hS : coreProgram.PureIn S) {g : String} (hg : g ∈ S)
    {κ : ℕ} {Lin : Layout} {m K F : ℕ} {rest rets : List E}
    (h : ∀ rd, MemL rd Lin → coreProgram.Rel rd g (1 :: gen ^ m :: rest) rets)
    (hT : TotalLeOn coreProgram fs g LoopPre (fun a => logG (a.getD 1 0) * K + F)) (h0 : 0 < m)
    (hm : m < 2 ^ 64 - 1) :
    CompleteAtDTB fs cert κ g Lin (1 :: gen ^ m :: rest) (Returns rets) (fun _ => True)
      (m * K + F) :=
  (completeAt_of_rel_pureBat hS hg h κ fun rd t hn hv hb => by
    have := hT rd t _ rets hn (loopPre_gen h0 hm rest) hv hb
    simpa [logG_gen_pow hm] using this).toDTB

/-- **`da_row_shape` is complete, placed, within its frame.** -/
theorem row_shape_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {s r L : ℕ} (hr1 : 1 ≤ r)
    (hr : r ≤ LeanDa.maxRows) (hL : 2 ^ L = LeanDa.paddedRowCount r) :
    CompleteAtDTB fs cert 16 "da_row_shape" [(s + L, [gen ^ 2 ^ L])] [gen ^ r, gen ^ L, gen ^ s]
      (Returns [gen ^ 2 ^ L, gen ^ (2 ^ L - r)]) (fun _ => True) (fs "da_row_shape") := by
  intro fp
  refine ⟨fs "da_row_shape", [], _, [], le_rfl, ⟨rfl, rfl⟩, fun q hq => by simp at hq, disj_nil,
    fun rd hlow hm => RelAtIn.relAtInT ?_⟩
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
