/-
  Rv64mc.Proof.Field.ESumU16T

  `E::sum` over `at.iter().map(|&i| low_weights[i as usize])` (`Bytecode::evaluate`'s inner sum) is total
  (`SumSafeT`): passed the iterator by reference (the slice's pointer and end, then the closure's reference to the
  `Vec<E>` of weights), it returns without writing memory, or ends the run with `a0 = 2` on an index past the
  weights (`panic_bounds_check`). The precondition (`SumPreT`): the iterator's three words and the weights' header
  in windows and 8-byte aligned; the `u16`s between pointer and end, an even number of bytes, 2-byte aligned and in
  a window unless there are none; the weights a `TabW`. The sum is not stated: no caller's safety reads it. The loop
  is `Total.loop` with the `u16`s left as the measure.

  ## Main definitions

  * `SumPreT`, `SumSafeT`

  ## Main results

  * `loop_ok`, `total`
-/

import Rv64mc.Proof.Field.ESumWinT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Core.AbortStop
import Rv64mc.Tactic.SymT
import Rv64mc.Tactic.TStep
import Rv64mc.Gen.Tmpl.Verifier.Field.E.SumMapIterU16EvaluateCloH33077ef9

namespace Rv64mc.Proof.Field.ESumU16T

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Field.ESumWinT
open Rv64mc.Gen.Verifier.Field.E.SumMapIterU16EvaluateCloH33077ef9 (Link tmpl)

/-- The total precondition: the iterator at `x10` (pointer, end, the closure's reference to the weights' header) and
    the header in windows and 8-byte aligned, the `u16`s from pointer to end as above, the weights a `TabW`. -/
def SumPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧ InWin env (regs .x10) 24 ∧
    (m.getMem (regs .x10)).toNat ≤ (m.getMem (regs .x10 + 8#64)).toNat ∧
    ((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) % 2 = 0 ∧
    (m.getMem (regs .x10)).toNat % 2 = 0 ∧
    (m.getMem (regs .x10 + 8#64) = m.getMem (regs .x10) ∨
      InWin env (m.getMem (regs .x10)) ((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat)) ∧
    (m.getMem (regs .x10 + 16#64)).toNat % 8 = 0 ∧ InWin env (m.getMem (regs .x10 + 16#64)) 24 ∧
    TabW env (m.getMem (m.getMem (regs .x10 + 16#64) + 8#64)) (m.getMem (m.getMem (regs .x10 + 16#64) + 16#64))

/-- **The total contract**: it returns, writing nothing, or ends the run with `a0 = 2`. It does not state the sum. -/
def SumSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (SumPreT env) (fun _ _ _ _ => True) (Stop := AbortStop)

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {Q : State rvIsa → Prop} {ret top : Word}
  {rest : List Frame} {regs : Reg → Word} {m : MachineState}

/-- `AbiRegs` through writes of registers it does not read. -/
local macro "abi_ok " h:term : tactic =>
  `(tactic| ((repeat rw [AbiRegs.updReg_iff (by decide)]) <;> exact $h))

/-- A nonzero counter decremented, as a number. -/
theorem dec_toNat {x : Word} (h : 0 < x.toNat) : (x + 18446744073709551615#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- Half the bytes from `q` to `e`, as a number. -/
theorem half_sub {e q : Word} (h : q.toNat ≤ e.toNat) : ((e - q) >>> 1).toNat = (e.toNat - q.toNat) / 2 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]; omega

/-- The return after the loop. -/
theorem ret_ok (hp : p[i]? = some (tmpl L)) (hk : Cont env p Q ret top rest regs m) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) {r : Reg → Word} (h1 : r .x1 = ret) (ha : AbiRegs top regs r) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 44, ret, top⟩ :: rest, r, m⟩ := by
  have hx2 := ha.1
  rv_symT hp with [h1, hx2]
  exact hk _ _ ⟨⟨ha, Env.Frame.refl hnx, hst, trivial⟩, rfl⟩

/-- The loop from its head with `k` `u16`s left (`x16`), the next at `x14`. -/
theorem loop_ok (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need : Nat}
    (hpanic : Aborts env p L.panicBoundsCheck.idx need) (hk : Cont env p Q ret top rest regs m)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hst : env.Static m) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {ptr lw : Word} (ht : TabW env ptr lw) :
    ∀ k r M, (M = m ∧ r .x1 = ret ∧ r .x2 = top ∧ AbiRegs top regs r ∧ (r .x16).toNat = k ∧ 0 < k ∧
      (r .x14).toNat % 2 = 0 ∧ InWin env (r .x14) (2 * k) ∧ r .x12 = lw ∧ r .x15 = ptr) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 22, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) _ fun k r M ⟨hM, h1, h2, ha, h16, hk0, h14a, hw, h12, h15⟩ ih => ?_
  subst hM
  have hx14 : (r .x14 + 2#64).toNat = (r .x14).toNat + 2 := toNat_add_ofNat (by unfold InWin at hw; omega)
  rv_symT hp stop [22, 44] with [hL, h1, h2, h12, h15] using [hpanic]
  · rw [h2]; omega
  · rw [h2]; omega
  · rw [h15]; exact (ht.entry hW (h12 ▸ hc)).1.1
  · rw [h15]; exact (ht.entry hW (h12 ▸ hc)).1.2
  · rw [h15]; exact (ht.entry hW (h12 ▸ hc)).2.1
  · rw [h15]; exact (ht.entry hW (h12 ▸ hc)).2.2
  · have hne : (r .x16 + 18446744073709551615#64).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    rw [dec_toNat (by omega)] at hne
    refine ih (k - 1) _ _ (by omega) ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · tnorm; exact h1
    · tnorm; exact h2
    · abi_ok ha
    · tnorm; rw [dec_toNat (by omega)]; omega
    · omega
    · tnorm; omega
    · unfold InWin at hw ⊢; tnorm; omega
    · tnorm; exact h12
    · tnorm; exact h15
  · exact ret_ok hp hk hst hnx (by tnorm; exact h1) (by abi_ok ha)

/-- **`E::sum` over the `u16` indices is total**, with no stack. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need : Nat} (hpanic : Aborts env p L.panicBoundsCheck.idx need) : SumSafeT env p i need := by
  rv_autoT hp with [hL] using [hpanic]
  refine loop_ok hp hL hpanic hk hstop hpre_4 hpre_5 hpre_3 hpre_15 hpre_16 hpre_14 _ _ _
    ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_, ?_, rfl, rfl⟩
  all_goals dsimp only [Tactic.rf]
  · rw [half_sub hpre_8]
    have : (m.getMem (regs .x10)).toNat ≠ (m.getMem (regs .x10 + 8#64)).toNat := fun h => hc (BitVec.eq_of_toNat_eq h)
    omega
  · exact hpre_10
  · rw [half_sub hpre_8, show 2 * (((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) / 2) =
      (m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat by omega]
    exact hpre_11.resolve_left (Ne.symm hc)

end Rv64mc.Proof.Field.ESumU16T

/-- info: 'Rv64mc.Proof.Field.ESumU16T.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ESumU16T.total
