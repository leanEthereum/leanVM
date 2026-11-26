/-
  Rv64mc.Proof.Field.ScaledMulT

  `Scaled::mul` is total: it returns `Scaled.MulPost`'s product (`Spec.Field.Scaled`), or ends the run with `a0 = 2`
  when a window's index is past the table (`panic_bounds_check`), over any program holding its template. The partial
  proof (`ScaledMul.lean`) ported by `rv_autoT`: its loop over the second limb's windows, there an induction on the
  windows left, is `Total.loop` at instruction 238 with them as the measure (`LoopInv`). The precondition (`MulPreT`)
  adds that a nonempty table lies in a window (`InWin`) and is 8-byte aligned; each of the 22 entries read is in it
  after the bounds check before it (`tab_ok`).

  ## Main definitions

  * `MulPreT`, `mulSpecT`, `LoopInv`

  ## Main results

  * `tab_ok`, `len_lt60`, `total`
-/

import Rv64mc.Proof.Field.ScaledMul
import Rv64mc.Proof.Field.ESumWinT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Core.AbortStop
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Field.ScaledMulT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field.Scaled Rv64mc.Spec.Field
open Rv64mc.Proof.Field.ScaledMul
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Field.Scaled.Mul (Link tmpl)

/-- The total precondition: `MulPre`, and a nonempty table in a window and 8-byte aligned. -/
def MulPreT (env : Env) (tabs : List Model.Limbs) (regs : Reg → Word) (m : MachineState) : Prop :=
  MulPre env tabs regs m ∧
    (tabs.length = 0 ∨ (InWin env (regs .x10) (16 * tabs.length) ∧ (regs .x10).toNat % 8 = 0))

/-- **The total contract of `Scaled::mul`**: `Scaled.mulSpec`'s, as a `HoldsT`, from `MulPreT`, ending the run with
    `a0 = 2` on an index past the table. -/
def mulSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ tabs, HoldsT env p i need (MulPreT env tabs) (MulPost tabs) (Stop := AbortStop)

/-- An entry the code reads after checking its index `x` against the table's length: both its doublewords are in a
    window and aligned. -/
theorem tab_ok {env : Env} {q x top : Word} {len : Nat} {m : MachineState}
    (hd : len = 0 ∨ (InWin env q (16 * len) ∧ q.toNat % 8 = 0)) (hW : Windows env top m)
    (hx : x < BitVec.ofNat 64 len) (hl : len < 2 ^ 60) :
    (inWindow (q + x <<< 4) 8 = true ∧ (q + x <<< 4).toNat % 8 = 0) ∧
      (inWindow (q + x <<< 4 + 8#64) 8 = true ∧ (q + x <<< 4 + 8#64).toNat % 8 = 0) := by
  have hn : (BitVec.ofNat 64 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega
  exact ESumWinT.TabW.entry (by unfold ESumWinT.TabW; rw [hn]; exact hd) hW hx

/-- A live table has fewer than `2 ^ 60` entries. -/
theorem len_lt60 {env : Env} {m : MachineState} {q : Word} {tabs : List Model.Limbs}
    (hl : env.Live m q (Layouts.E.byteSize * tabs.length)) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    tabs.length < 2 ^ 60 := by
  have := env.layout; have := env.stackLimit.isLt; unfold Env.Live at hl; simp only [Layouts.E.byteSize] at hl; omega

/-- The loop's head with `k` windows of the second limb left after this one: `Inv` after the others, their
    indices in the table, and the code map kept since the entry. -/
def LoopInv (env : Env) (tabs : List Model.Limbs) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  k < 11 ∧ (∀ w < 10 - k, idx 1 w (regs .x13) < tabs.length) ∧ Inv env tabs ret top regs m (10 - k) R M ∧
    M.code = m.code

set_option hygiene false in
/-- A table entry's window and alignment goal after its bounds check (`tab_ok`), from `rv_autoT`'s names. -/
local macro "tab_goal" : tactic => `(tactic| first
    | (with_reducible refine (tab_ok hpre_9 hpre_11 ?_ hl60).1.1); with_reducible assumption
    | (with_reducible refine (tab_ok hpre_9 hpre_11 ?_ hl60).1.2); with_reducible assumption
    | (with_reducible refine (tab_ok hpre_9 hpre_11 ?_ hl60).2.1); with_reducible assumption
    | (with_reducible refine (tab_ok hpre_9 hpre_11 ?_ hl60).2.2); with_reducible assumption)

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needP : Nat} (hnP : 80 + needP ≤ need) (hpanic : Aborts env p L.panicBoundsCheck.idx needP) :
    mulSpecT env p i need := by
  intro tabs
  rv_autoT hp with [hL] using [hpanic]
  all_goals have hl60 := len_lt60 hpre_8 hpre_5
  any_goals tab_goal
  have hlen := len_lt hpre_8 hpre_5
  have w1 := win (regs .x12) 1 52 64 (by decide) rfl rfl
  have w2 := win (regs .x12) 2 46 128 (by decide) rfl rfl
  have w3 := win (regs .x12) 3 40 192 (by decide) rfl rfl
  have w4 := win (regs .x12) 4 34 256 (by decide) rfl rfl
  have w5 := win (regs .x12) 5 28 320 (by decide) rfl rfl
  have w6 := win (regs .x12) 6 22 384 (by decide) rfl rfl
  have w7 := win (regs .x12) 7 16 448 (by decide) rfl rfl
  have w8 := win (regs .x12) 8 10 512 (by decide) rfl rfl
  have w9 := win (regs .x12) 9 4 576 (by decide) rfl rfl
  have b : ∀ w, w < 11 → BitVec.ofNat 64 (idx 0 w (regs .x12)) < BitVec.ofNat 64 tabs.length →
      idx 0 w (regs .x12) < tabs.length := fun w hw h =>
    lt_of_ofNat (by have := idx_lt 0 w (regs .x12) (by decide) hw; omega) hlen h
  rw [win0] at hc_1
  rw [w1] at hc_2; rw [w2] at hc_3; rw [w3] at hc_4; rw [w4] at hc_5; rw [w5] at hc_6; rw [w6] at hc_7
  rw [w7] at hc_8; rw [w8] at hc_9; rw [w9] at hc_10; rw [win10] at hc
  have hb0 : ∀ w < 11, idx 0 w (regs .x12) < tabs.length := by
    intro w hw
    interval_cases w <;> exact b _ (by decide) ‹_›
  clear hc_1 hc_2 hc_3 hc_4 hc_5 hc_6 hc_7 hc_8 hc_9 hc_10 hc
  refine Total.loop (LoopInv env tabs ret top regs m) ?_ 10 _ _ ?_
  · intro k R M hI ih
    obtain ⟨hk11, hb1, hinv, hcode⟩ := hI
    obtain ⟨j, hj⟩ : ∃ j, j + k = 10 := ⟨10 - k, by omega⟩
    rw [show 10 - k = j by omega] at hb1 hinv
    rv_introT hinv
    rv_symT hp with [hL] using [hpanic]
    any_goals tab_goal
    all_goals have hbj := bound_j hlen (by omega) hc_1
    all_goals have hb : ∀ w < j + 1, idx 1 w (regs .x13) < tabs.length := fun w hw =>
      if h : w < j then hb1 w h else (show w = j by omega) ▸ hbj
    · cases k with
      | zero => exact absurd ((end17 (by omega)).2 (by omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨by omega, by rw [show 10 - k = j + 1 by omega]; exact hb, ?_, hcode⟩
        rw [show 10 - k = j + 1 by omega]
        rv_closeT
        · exact step16 j
        · exact step17 j
        · rw [← body_val M _ _ _ j (by omega)]
        · rw [← body_val M _ _ _ j (by omega)]
    all_goals have hj10 : j = 10 := (end17 (by omega)).1 hc
    all_goals subst hj10
    all_goals rw [sum_eq hinv_13 hpre_5 hpre_7 hpre_8 hb0 hb, ← body_val M _ _ _ 10 (by decide)]
  · refine ⟨by omega, fun w hw => absurd hw (by omega), ?_, by rv_closeT⟩
    rv_closeT
    all_goals simp only [win0, w1, w2, w3, w4, w5, w6, w7, w8, w9, win10, shl_idx, part_succ, part_zero, rd,
      Model.eAdd, Model.eZero, BitVec.zero_xor, Nat.reduceLT]
    all_goals exact xor11 _ _ _ _ _ _ _ _ _ _ _

end Rv64mc.Proof.Field.ScaledMulT

/-- info: 'Rv64mc.Proof.Field.ScaledMulT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ScaledMulT.total
