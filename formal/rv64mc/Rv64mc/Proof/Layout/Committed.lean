/-
  Rv64mc.Proof.Layout.Committed

  `Layout::committed` keeps its contract (`Spec.Layout.Committed.spec`): a bounds check, the element's tag, and
  `Ok` with its two words or `Err(CommittedSize)` stored at `sret`. `rv_auto` steps the three paths; the stores into
  `sret` are closed by `Proof.Layout.Out`.
-/

import Rv64mc.Spec.Layout.Committed
import Rv64mc.Proof.Layout.Out
import Rv64mc.Gen.Tmpl.Verifier.Layout.Layout.Committed
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Layout.Committed

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Committed
open Rv64mc.Gen.Verifier.Layout.Layout.Committed (Link tmpl)

theorem ne8 (a : Word) : a + 8#64 ≠ a := Tactic.add_ne (by decide)
theorem ne16 (a : Word) : a + 16#64 ≠ a := Tactic.add_ne (by decide)
theorem ne8_16 (a : Word) : a + 8#64 ≠ a + 16#64 := Tactic.add_ne_add (by decide)

/-- `Err(CommittedSize)` as the code stores it. -/
theorem post_err (m : MachineState) (a : Word) :
    ResultPlacementAt ((m.setMem (a + 8#64) 28#64).setMem a 1#64) a none := by
  simp only [ResultPlacementAt, Layouts.ResultPlacement.tagOffset, Layouts.ResultPlacement.Err.tag,
    Layouts.ResultPlacement.Err.f0, Layouts.VerifierError.CommittedSize.tag, BitVec.add_zero]
  exact ⟨MachineState.getMem_setMem_eq,
    by rw [MachineState.getMem_setMem_ne (ne8 a), MachineState.getMem_setMem_eq]⟩

/-- `Ok(placement)` as the code stores it. -/
theorem post_ok (m : MachineState) (a v w : Word) (p : Model.PlacementRust) (hv : v = BitVec.ofNat 64 p.variableCount)
    (hw : w = p.index) :
    ResultPlacementAt (((m.setMem (a + 8#64) v).setMem (a + 16#64) w).setMem a 0#64) a (some p) := by
  simp only [ResultPlacementAt, Layouts.ResultPlacement.tagOffset, Layouts.ResultPlacement.Ok.tag,
    Layouts.ResultPlacement.Ok.f0, Layouts.Placement.variables, Layouts.Placement.index,
    BitVec.add_zero]
  refine ⟨MachineState.getMem_setMem_eq, ?_, ?_⟩
  · rw [MachineState.getMem_setMem_ne (ne8 a), MachineState.getMem_setMem_ne (ne8_16 a),
      MachineState.getMem_setMem_eq, hv]
  · rw [MachineState.getMem_setMem_ne (ne16 a), MachineState.getMem_setMem_eq, hw]

/-- The element's address as the code computes it. -/
theorem elem_addr (q x : Word) : q + (x <<< 4 + x <<< 3) = q + BitVec.ofNat 64 (24 * x.toNat) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem index_lt {ps : List (Option Model.PlacementRust)} {x : Word} {q : Word}
    (hb : q.toNat + 24 * ps.length < 2 ^ 64) (h : x < BitVec.ofNat 64 ps.length) : x.toNat < ps.length := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat] at h; omega

theorem index_ge {ps : List (Option Model.PlacementRust)} {x : Word} {q : Word}
    (hb : q.toNat + 24 * ps.length < 2 ^ 64) (h : BitVec.ofNat 64 ps.length ≤ x) : ps.length ≤ x.toNat := by
  rw [BitVec.le_def, BitVec.toNat_ofNat] at h; omega

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) :
    spec env p i := by
  intro ps
  rv_auto hp
  all_goals
    have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
    rw [hpre_2] at hpre_9
    have hown : env.Owned m top (regs .x10) Layouts.ResultPlacement.byteSize := ⟨hpre_9, hpre_10⟩
    have s0 := owned_slot0 hown hpre_5 hlim (by decide)
    have s8 := owned_slot (k := 8) hown hpre_5 hlim (by decide)
    have s16 := owned_slot (k := 16) hown hpre_5 hlim (by decide)
  all_goals try first
    | exact frame_setMem_out (frame_setMem_out (frame_setMem_out (Env.Frame.refl hpre_5) s8.1 s8.2.1) s16.1
        s16.2.1) s0.1 s0.2.1
    | exact frame_setMem_out (frame_setMem_out (Env.Frame.refl hpre_5) s8.1 s8.2.1) s0.1 s0.2.1
    | exact Env.static_setMem (Env.static_setMem (Env.static_setMem hpre_4 s8.2.2) s16.2.2) s0.2.2
    | exact Env.static_setMem (Env.static_setMem hpre_4 s8.2.2) s0.2.2
  -- out of range
  · rw [List.getD_eq_default _ _ (index_ge hpre_7 hc)]
    exact post_err m _
  -- not `Some`
  · have hk := index_lt hpre_7 hc_1
    have he := hpre_8 _ hk
    rw [elem_addr] at hc
    rw [List.getD_eq_getElem _ _ hk]
    generalize ps[(regs .x13).toNat] = o at he ⊢
    cases o with
    | none => exact post_err m _
    | some pl =>
      simp only [OptPlacementAt, Layouts.OptionPlacement.tagOffset, Layouts.OptionPlacement.Some.tag,
        Layouts.OptionPlacement.byteSize, BitVec.add_zero] at he
      exact absurd he.1 hc
  -- the element's tag is `Some`
  · have hk := index_lt hpre_7 hc_1
    have he := hpre_8 _ hk
    rw [elem_addr] at hc ⊢
    rw [List.getD_eq_getElem _ _ hk]
    generalize ps[(regs .x13).toNat] = o at he ⊢
    cases o with
    | none =>
      simp only [OptPlacementAt, Layouts.OptionPlacement.tagOffset, Layouts.OptionPlacement.None.tag,
        Layouts.OptionPlacement.byteSize, BitVec.add_zero] at he
      rw [he] at hc; exact absurd hc (by decide)
    | some pl =>
      simp only [OptPlacementAt, Layouts.OptionPlacement.tagOffset, Layouts.OptionPlacement.Some.tag,
        Layouts.OptionPlacement.Some.f0, Layouts.Placement.variables, Layouts.Placement.index,
        Layouts.OptionPlacement.byteSize, BitVec.add_zero] at he
      exact post_ok m _ _ _ pl he.2.1 he.2.2

end Rv64mc.Proof.Layout.Committed
