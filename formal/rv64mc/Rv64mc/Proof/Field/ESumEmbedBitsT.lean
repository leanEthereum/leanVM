/-
  Rv64mc.Proof.Field.ESumEmbedBitsT

  `E::sum` over `(0..EMBED_BITS).filter(|b| e >> b & 1 == 1).map(|b| powers[b])` (`instance_weights`'s sum) is
  total (`SumSafeT`): passed the iterator by reference (the closure's reference to `e`, a `u32`, the range, the
  closure's reference to `powers`, an array of `24` `E`s), it returns without writing memory, or ends the run with
  `a0 = 2` on an index past the array (`panic_bounds_check`). The precondition (`SumPreT`): the iterator's four
  words in a window and 8-byte aligned, `e` in a window and 4-byte aligned, the array a `TabW` of `24` entries. The
  sum is not stated: no caller's safety reads it. The loop is `Total.loop` with the indices left as the measure.

  ## Main definitions

  * `SumPreT`, `SumSafeT`, `Cont`

  ## Main results

  * `loop_ok`, `total`
-/

import Rv64mc.Proof.Field.ESumWinT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Core.AbortStop
import Rv64mc.Tactic.SymT
import Rv64mc.Tactic.TStep
import Rv64mc.Gen.Tmpl.Verifier.Field.E.SumMapFilterRangeUsizeInHbf23f0ea

namespace Rv64mc.Proof.Field.ESumEmbedBitsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Field.ESumWinT
open Rv64mc.Gen.Verifier.Field.E.SumMapFilterRangeUsizeInHbf23f0ea (Link tmpl)

/-- The total precondition: the iterator at `x10` (the reference to `e`, the range's start and end, the reference
    to `powers`) in a window and 8-byte aligned, `e` in a window and 4-byte aligned, `powers` a `TabW` of `24`
    entries. -/
def SumPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧ InWin env (regs .x10) 32 ∧
    (m.getMem (regs .x10)).toNat % 4 = 0 ∧ InWin env (m.getMem (regs .x10)) 4 ∧
    TabW env (m.getMem (regs .x10 + 24#64)) 24#64

/-- **The total contract**: it returns, writing nothing, or ends the run with `a0 = 2`. It does not state the sum. -/
def SumSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (SumPreT env) (fun _ _ _ _ => True) (Stop := AbortStop)

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {Q : State rvIsa → Prop} {ret top : Word}
  {rest : List Frame} {regs : Reg → Word} {m : MachineState}

/-- `AbiRegs` through writes of registers it does not read. -/
local macro "abi_ok " h:term : tactic =>
  `(tactic| ((repeat rw [AbiRegs.updReg_iff (by decide)]) <;> exact $h))

/-- The continuation the parts are proved against. -/
abbrev Cont (env : Env) (p : Lprog (Op Reg) Reg) (Q : State rvIsa → Prop) (ret top : Word) (rest : List Frame)
    (regs : Reg → Word) (m : MachineState) : Prop :=
  ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩

/-- The next element's offset, from the pointer kept 8 bytes into the current one. -/
theorem succ_shl (c q : Word) : c <<< 4 + q + 8#64 + 8#64 = (c + 1#64) <<< 4 + q := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]; omega

/-- The next element's second doubleword, from the pointer kept 8 bytes into the current one. -/
theorem succ_shl8 (c q : Word) : c <<< 4 + q + 8#64 + 16#64 = (c + 1#64) <<< 4 + q + 8#64 := by
  rw [← succ_shl, BitVec.add_assoc (c <<< 4 + q + 8#64)]; rfl

/-- The return after the loop. -/
theorem ret_ok (hp : p[i]? = some (tmpl L)) (hk : Cont env p Q ret top rest regs m) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) {r : Reg → Word} (h1 : r .x1 = ret) (ha : AbiRegs top regs r) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 64, ret, top⟩ :: rest, r, m⟩ := by
  have hx2 := ha.1
  rv_symT hp with [h1, hx2]
  exact hk _ _ ⟨⟨ha, Env.Frame.refl hnx, hst, trivial⟩, rfl⟩

/-- The loop from its head after index `x10`, below the end `e`, `k` indices left after the next. -/
theorem loop_ok (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need : Nat}
    (hpanic : Aborts env p L.panicBoundsCheck.idx need) (hk : Cont env p Q ret top rest regs m)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hst : env.Static m) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {ptr lw e : Word} (ht : TabW env ptr lw) :
    ∀ k r M, (M = m ∧ r .x1 = ret ∧ r .x2 = top ∧ AbiRegs top regs r ∧ r .x14 = e ∧ r .x16 = lw ∧
      (r .x10).toNat < e.toNat ∧ e.toNat - (r .x10).toNat - 1 = k ∧ r .x15 = r .x10 <<< 4 + ptr + 8#64) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 30, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) _ fun k r M ⟨hM, h1, h2, ha, h14, h16, hlt, hk', h15⟩ ih => ?_
  subst hM
  have hx10 : (r .x10 + 1#64).toNat = (r .x10).toNat + 1 := toNat_add_ofNat (by omega)
  rv_symT hp stop [30, 64] with [hL, h1, h2, h16, h14] using [hpanic]
  · exact ret_ok hp hk hst hnx (by tnorm; exact h1) (by abi_ok ha)
  · have hne : (r .x10 + 1#64).toNat ≠ e.toNat := fun h => hc_1 (by rw [h14]; exact BitVec.eq_of_toNat_eq h.symm)
    refine ih (k - 1) _ _ (by omega) ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · tnorm; exact h1
    · tnorm; exact h2
    · abi_ok ha
    · tnorm; exact h14
    · tnorm; exact h16
    · tnorm; omega
    · tnorm; omega
    · tnorm; rw [h15, ← succ_shl8]
  · rw [h2]; omega
  · rw [h2]; omega
  · rw [h15, succ_shl]; exact (ht.entry' hW (h16 ▸ hc)).1.1
  · rw [h15, succ_shl]; exact (ht.entry' hW (h16 ▸ hc)).1.2
  · rw [h15, succ_shl8]; exact (ht.entry' hW (h16 ▸ hc)).2.1
  · rw [h15, succ_shl8]; exact (ht.entry' hW (h16 ▸ hc)).2.2
  · have hne : (r .x10 + 1#64).toNat ≠ e.toNat := fun h => by
      have : r .x14 = r .x10 + 1#64 := by rw [h14]; exact BitVec.eq_of_toNat_eq h.symm
      exact hc_1 this
    refine ih (k - 1) _ _ (by omega) ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · tnorm; exact h1
    · tnorm; exact h2
    · abi_ok ha
    · tnorm; exact h14
    · tnorm; exact h16
    · tnorm; omega
    · tnorm; omega
    · tnorm; rw [h15, ← succ_shl8]

/-- **`E::sum` over the embedding's bits is total**, with no stack. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need : Nat} (hpanic : Aborts env p L.panicBoundsCheck.idx need) : SumSafeT env p i need := by
  rv_autoT hp with [hL] using [hpanic]
  any_goals first
    | exact (TabW.entry' hpre_10 hpre_12 hc).1.1
    | exact (TabW.entry' hpre_10 hpre_12 hc).1.2
    | exact (TabW.entry' hpre_10 hpre_12 hc).2.1
    | exact (TabW.entry' hpre_10 hpre_12 hc).2.2
  all_goals
    refine loop_ok (e := m.getMem (regs .x10 + 16#64)) hp hL hpanic hk hstop hpre_4 hpre_5 hpre_3 hpre_11 hpre_12
      hpre_10 ((m.getMem (regs .x10 + 16#64)).toNat - (m.getMem (regs .x10 + 8#64)).toNat - 1) _ _ ?_
    exact ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hc_1, rfl, rfl⟩

end Rv64mc.Proof.Field.ESumEmbedBitsT

/-- info: 'Rv64mc.Proof.Field.ESumEmbedBitsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ESumEmbedBitsT.total
