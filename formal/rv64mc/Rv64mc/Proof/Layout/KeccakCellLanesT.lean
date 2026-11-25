/-
  Rv64mc.Proof.Layout.KeccakCellLanesT

  `verifier::layout::keccak_cell_lanes(sret, flag)` is total (`CellLanesSafeT`): it fills the `13` entries of `32`
  bytes it returns through `sret`, 8-byte aligned in a window apart from the static data and `NEXT`, and returns,
  writing nothing else. The entries' values are not stated: no caller's safety reads them as addresses. Its loop over
  the entries after the first is `Total.loop` with the entries left as the measure.

  ## Main definitions

  * `cellBytes`, `CellPreT`, `CellOut`, `CellLanesSafeT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Tactic.SymT
import Rv64mc.Gen.Tmpl.Verifier.Layout.KeccakCellLanes

namespace Rv64mc.Proof.Layout.KeccakCellLanesT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Proof.Runtime.MemsetT (InWin Kept)
open Rv64mc.Gen.Verifier.Layout.KeccakCellLanes (Link tmpl)

/-- The returned array's size in bytes: `13` entries of `32`. -/
abbrev cellBytes : Nat := 13 * 32

/-- The total precondition: `sret`'s bytes 8-byte aligned, in the heap window up to the heap's end or in the stack
    window. -/
def CellPreT (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧
    ((0x10000000 ≤ (regs .x10).toNat ∧ (regs .x10).toNat + cellBytes ≤ env.heapEnd.toNat) ∨
      (env.stackLimit.toNat ≤ (regs .x10).toNat ∧ (regs .x10).toNat + cellBytes ≤ 0xc0000000))

/-- What it writes: the doublewords of the returned array. -/
def CellOut (regs : Reg → Word) (_m : MachineState) : Word → Prop := Spec.Runtime.DwordsOf (regs .x10) cellBytes

/-- **The total contract of `keccak_cell_lanes`**: it returns, writing at most the array it returns. -/
def CellLanesSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (CellPreT env) (fun _ _ _ _ => True) CellOut

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link}

variable {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}

/-- The continuation the parts are proved against. -/
abbrev Cont (env : Env) (p : Lprog (Op Reg) Reg) (Q : State rvIsa → Prop) (ret top : Word) (rest : List Frame)
    (regs : Reg → Word) (m : MachineState) : Prop :=
  ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) CellOut ret top regs m r' m' →
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩

/-- The loop at its head (the four stores of an entry), `t` entries after the first done. -/
def KInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  r .x1 = ret ∧ AbiRegs top regs r ∧ Kept env top (regs .x10) cellBytes m M ∧ k ≤ 11 ∧
    (r .x10).toNat = (regs .x10).toNat + 0x38 + 32 * (11 - k) ∧ (r .x13).toNat = 3 + 2 * (11 - k) ∧
    r .x14 = 27#64 ∧ r .x15 = 17#64 ∧ (r .x16).toNat = 1 + (11 - k) ∧ r .x12 = 1#64

/-- `AbiRegs` through writes of registers it does not read. -/
macro "abi_ok " h:term : tactic =>
  `(tactic| ((repeat rw [AbiRegs.updReg_iff (by decide)]) <;> exact $h))

/-- The entries after the first, `k` of them left after this one. -/
theorem loop_ok (hp : p[i]? = some (tmpl L)) (hk : Cont env p Q ret top rest regs m)
    (hpre : CellPreT env regs m) (hW : Windows env top m) :
    ∀ k r M, KInv env ret top regs m k r M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) (KInv env ret top regs m)
    fun k r M ⟨h1, ha, hK, hk11, h10, h13, h14, h15, h16, h12⟩ ih => ?_
  obtain ⟨hal, hw⟩ := hpre
  have hw' : InWin env (regs .x10) cellBytes := hw
  have hcode := hK.2.2
  have h416 : cellBytes = 416 := rfl
  unfold InWin at hw'
  have hb := (regs .x10).isLt
  have hl := hW.heapEnd_le
  have e24 : (r .x10 + 0xffffffffffffffe8#64).toNat = (r .x10).toNat - 24 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have e16 : (r .x10 + 0xfffffffffffffff0#64).toNat = (r .x10).toNat - 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have e8 : (r .x10 + 0xfffffffffffffff8#64).toNat = (r .x10).toNat - 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have e32 : (r .x10 + 32#64).toNat = (r .x10).toNat + 32 := toNat_add_ofNat (by omega)
  have e2 : (r .x13 + 2#64).toNat = (r .x13).toNat + 2 := toNat_add_ofNat (by omega)
  have e1 : (r .x16 + 1#64).toNat = (r .x16).toNat + 1 := toNat_add_ofNat (by omega)
  have hK4 := fun (v1 v2 v3 v4 : Word) =>
    (((hK.setMem (x := r .x10 + 0xffffffffffffffe8#64) hw' (by omega) (by omega) (by omega) v1).setMem
      (x := r .x10 + 0xfffffffffffffff0#64) hw' (by omega) (by omega) (by omega) v2).setMem
      (x := r .x10 + 0xfffffffffffffff8#64) hw' (by omega) (by omega) (by omega) v3).setMem
      (x := r .x10) hw' (by omega) (by omega) (by omega) v4
  have h27 : (r .x14).toNat = 27 := by rw [h14]; rfl
  have hne : ¬ (r .x13 + 2#64) = r .x14 → k ≠ 0 := fun h hk0 =>
    h (BitVec.eq_of_toNat_eq (by rw [e2, h27, h13]; omega))
  have back := fun (h : k ≠ 0) {r' : Reg → Word} {M' : MachineState}
      (hr : r' .x1 = ret ∧ AbiRegs top regs r' ∧ (r' .x10).toNat = (r .x10).toNat + 32 ∧
        (r' .x13).toNat = (r .x13).toNat + 2 ∧ r' .x14 = r .x14 ∧ r' .x15 = r .x15 ∧
        (r' .x16).toNat = (r .x16).toNat + 1 ∧ r' .x12 = r .x12)
      (hM : Kept env top (regs .x10) cellBytes m M') =>
    ih (k - 1) r' M' (by omega) ⟨hr.1, hr.2.1, hM, by omega, by omega, by omega, hr.2.2.2.2.1.trans h14,
      hr.2.2.2.2.2.1.trans h15, by omega, hr.2.2.2.2.2.2.2.trans h12⟩
  rv_symT hp stop [72, 78]
  · exact ha.1
  · obtain ⟨hF, hs, hc'⟩ := hK4 _ _ _ _
    exact hk _ _ ⟨⟨by abi_ok ha, hF, hs, trivial⟩, hc'⟩
  · rv_symT hp stop [78]
    exact back (hne hc_1) ⟨by tnorm; exact h1, by abi_ok ha, by tnorm; exact e32, by tnorm; exact e2, by tnorm,
      by tnorm, by tnorm; exact e1, by tnorm⟩ (hK4 _ _ _ _)
  · exact back (hne hc_1) ⟨by tnorm; exact h1, by abi_ok ha, by tnorm; exact e32, by tnorm; exact e2, by tnorm,
      by tnorm, by tnorm; exact e1, by tnorm⟩ (hK4 _ _ _ _)
  · exact back (hne hc_1) ⟨by tnorm; exact h1, by abi_ok ha, by tnorm; exact e32, by tnorm; exact e2, by tnorm,
      by tnorm, by tnorm; exact e1, by tnorm⟩ (hK4 _ _ _ _)

set_option rv_sym.heap true in
/-- **`keccak_cell_lanes` is total**, with no stack. -/
theorem total (hp : p[i]? = some (tmpl L)) : CellLanesSafeT env p i 0 := by
  rv_autoT hp stop [72, 78]
  all_goals
    have hw' : InWin env (regs .x10) cellBytes := hpre_7
    have h416 : cellBytes = 416 := rfl
    have hl := hpre_9.heapEnd_le
    have hK0 : Kept env top (regs .x10) cellBytes m m := ⟨Env.Frame.refl hpre_5, hpre_4, rfl⟩
    unfold InWin at hw'
  · rv_symT hp stop [78]
    refine loop_ok hp hk ⟨hpre_6, hpre_7⟩ hpre_9 11 _ _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl⟩, ?_, le_rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · repeat (refine Proof.Runtime.MemsetT.Kept.setMem ?_ hw' ?_ ?_ ?_ _)
      all_goals first | exact hK0 | (rw [toNat_add_ofNat (by omega)]; omega) | omega
    · dsimp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]
  · refine loop_ok hp hk ⟨hpre_6, hpre_7⟩ hpre_9 11 _ _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl⟩, ?_, le_rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · repeat (refine Proof.Runtime.MemsetT.Kept.setMem ?_ hw' ?_ ?_ ?_ _)
      all_goals first | exact hK0 | (rw [toNat_add_ofNat (by omega)]; omega) | omega
    · dsimp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]

end Rv64mc.Proof.Layout.KeccakCellLanesT

/-- info: 'Rv64mc.Proof.Layout.KeccakCellLanesT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.KeccakCellLanesT.total
