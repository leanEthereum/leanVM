/-
  LeanVM.Guest.B1.Da.AtTB

  Helpers for `da_verify`'s bounded honest shapes (`CompleteAtDTB`, the words bounded before the
  memory): the pure callees within their static bounds, `da_padding` within its frame, and the
  static bounds `da_verify` rests on (`DvStaticB`).

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.AtT
public import LeanVM.Guest.B1.Da.PaddingAt
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
which a run charges once (`iterK fs SK g` per iteration and `fs g`). `padding_completeAtB`:
`padding_completeAt` (same proof) within its frame.
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
  dl : TotalLe coreProgram fs dlTop (fun _ => SB dlTop)
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

/-- **`da_padding` is complete, placed, within its frame.** -/
theorem padding_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : r ≤ LeanDa.maxRows) :
    CompleteAtDTB fs cert 16 "da_padding" [] [gen ^ r] (Returns [gen ^ (LeanDa.maxRows - r)])
      (fun _ => True) (fs "da_padding") := by
  intro fp
  refine ⟨fs "da_padding", [], _, [], le_rfl, ⟨rfl, rfl⟩, fun q hq => by simp at hq, disj_nil,
    fun rd hlow _ => RelAtIn.relAtInT ?_⟩
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
