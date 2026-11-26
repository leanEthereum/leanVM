/-
  Rv64mc.Proof.Whir.FoldRowT

  `verifier::whir::fold_row` is total (`specT`): from the row's `Vec<E>` header (`a0`, the caller's copy, in its
  frame) a vector (`VecT`), and the rounds (`a2`, `a3` of them) in a window and 8-byte aligned unless there are none,
  it returns, writing at most the row's elements (`Spec.Whir.FoldRow.Out`) besides its stack, or ends the run with
  `a0 = 2` (`assert_eq!` on one value left, or a bounds check). Safety only: the partial specification
  (`Spec/Whir/FoldRow.lean`, class C) has no proof. Two loops: over the rounds (`outer`, the rounds left as the
  measure) and, in each round, over the pairs folded in place (`inner`, the pairs left as the measure).

  ## Main definitions

  * `PreT`, `specT`, `ExitInv`, `OInv`, `BInv`, `LInv`

  ## Main results

  * `exit_ok`, `inner`, `body`, `outer`, `total`
-/

import Rv64mc.Core.AbortStop
import Rv64mc.Proof.Field.BaseMulT
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.VecReprT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Spec.Whir.FoldRow
import Rv64mc.Tactic.SymT
import Rv64mc.Gen.Tmpl.Verifier.Whir.FoldRow

namespace Rv64mc.Proof.Whir.FoldRowT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Gen.Verifier.Whir.FoldRow (Link tmpl)

/-- The total precondition: the row's header a vector of 16-byte elements (`VecT`) in the caller's frame (at or
    above the stack pointer), the rounds (`a3` of 32 bytes from `a2`), unless there are none, in a window and 8-byte
    aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  VecT env m (regs .x10) 16 ∧ (regs .x2).toNat ≤ (regs .x10).toNat ∧
    ((regs .x13).toNat = 0 ∨ (InWin env (regs .x12) (32 * (regs .x13).toNat) ∧ (regs .x12).toNat % 8 = 0))

/-- **The total contract of `fold_row`**: it returns, writing at most the row's elements, or ends the run with
    `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True) Spec.Whir.FoldRow.Out (Stop := AbortStop)

/-- The row's buffer, unless its length is `0`: from the input and heap window's start, allocated before `m`, 8-byte
    aligned. -/
def BufR (env : Env) (m : MachineState) (ptr len : Word) : Prop :=
  len.toNat = 0 ∨ (0x10000000 ≤ ptr.toNat ∧ ptr.toNat + 16 * len.toNat ≤ (env.next m).toNat ∧ ptr.toNat % 8 = 0)

/-- The precondition the steps use: the header's words read as the code reads them. -/
def PreR (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x2).toNat ≤ (regs .x10).toNat ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
    BufR env m (m.getMem (regs .x10 + 8#64)) (m.getMem (regs .x10 + 16#64)) ∧
    ((regs .x13).toNat = 0 ∨ (InWin env (regs .x12) (32 * (regs .x13).toNat) ∧ (regs .x12).toNat % 8 = 0))

theorem preR_of_preT {env : Env} {regs : Reg → Word} {m : MachineState} (h : PreT env regs m) : PreR env regs m := by
  obtain ⟨⟨hw, ⟨-, ha, hb, -⟩, hlc⟩, htop, hr⟩ := h
  refine ⟨htop, hw, ha, ?_, hr⟩
  simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero] at hlc
  simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero] at hb
  rcases hb with h0 | ⟨h1, h2, h3⟩
  · exact .inl (by omega)
  · refine .inr ⟨h1, ?_, h3⟩
    unfold Env.Live at h2
    change (m.getMem (regs .x10 + 16#64)).toNat ≤ (m.getMem (regs .x10)).toNat at hlc
    change (m.getMem (regs .x10 + 8#64)).toNat + (m.getMem (regs .x10)).toNat * 16 ≤ _ at h2
    omega

/-- The state at the final check (instruction 72): the count left `x8` at most the row's length, the stack
    pointer, the frame, the code, the static data, the header's address and the saved registers' slots. -/
def ExitInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ (R .x8).toNat ≤ (m.getMem (regs .x10 + 16#64)).toNat ∧
    env.Frame top (Spec.Whir.FoldRow.Out regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551472#64) = regs .x10 ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26 ∧
    M.getMem (top + 18446744073709551512#64) = regs .x27

set_option rv_sym.heap true in
/-- From the final check: `assert_eq!(values.len(), 1)`, the first element read, the return. -/
theorem exit_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA : Nat} (hnA : 144 + needA ≤ need)
    (haf : Aborts env p L.assertFailedUsizeUsize.idx needA) {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) Spec.Whir.FoldRow.Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (htop : top.toNat ≤ (regs .x10).toNat) (hw : InWin env (regs .x10) 24) (ha : (regs .x10).toNat % 8 = 0)
    (hb : BufR env m (m.getMem (regs .x10 + 8#64)) (m.getMem (regs .x10 + 16#64))) :
    ∀ R M, ExitInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 144, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have := hW.top_le
  have hlay := env.layout
  have hl := hw.lt
  unfold InWin at hw
  rv_introT hinv
  have hge := hW.next_ge
  have hhe := hW.heapEnd_le
  have hnx := hinv_3.2.1
  have hnm := hinv_3.1
  have hP : M.getMem (regs .x10 + 8#64) = m.getMem (regs .x10 + 8#64) := by
    refine hinv_3.getMem_above (by omega) (by rw [toNat_add_ofNat (by omega)]; omega) ?_
    simp only [Spec.Whir.FoldRow.Out, InRange, vecPtr, vecLen, Layouts.Vec.ptr, Layouts.Vec.len, Layouts.E.byteSize,
      toNat_add_ofNat (show (regs .x10).toNat + 8 < 2 ^ 64 by omega)]
    rcases hb with h0 | ⟨-, h1, -⟩
    · omega
    · omega
  rv_symT hp with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)] using [haf]
  all_goals
    rw [hc, show (1#64 : Word).toNat = 1 from rfl] at hinv_2
    obtain ⟨hp0, hpl, hpa⟩ := hb.resolve_left (by omega)
    have hp8 : (m.getMem (regs .x10 + 8#64) + 8#64).toNat = (m.getMem (regs .x10 + 8#64)).toNat + 8 :=
      toNat_add_ofNat (by have := env.heapEnd.isLt; omega)
    rw [hinv_6, hP]
    first | (rw [Rv64mc.inWindow_iff]; (try rw [hp8]); omega) | (simp only [hp8]; omega) | omega

/-- The hypotheses the loops share: the stack, the windows, the header in the caller's frame, the rounds (at least
    one) in a window, the buffer's bounds. -/
structure Ctx (env : Env) (top : Word) (regs : Reg → Word) (m : MachineState) : Prop where
  hstk : env.stackLimit.toNat + 144 ≤ top.toNat
  hal : top.toNat % 16 = 0
  hW : Windows env top m
  htop : top.toNat ≤ (regs .x10).toNat
  hw : InWin env (regs .x10) 24
  ha : (regs .x10).toNat % 8 = 0
  hb : BufR env m (m.getMem (regs .x10 + 8#64)) (m.getMem (regs .x10 + 16#64))
  hrn : 1 ≤ (regs .x13).toNat
  hrw : InWin env (regs .x12) (32 * (regs .x13).toNat)
  hra : (regs .x12).toNat % 8 = 0

/-- The inner loop's head (instruction 52) in round `rn - (k + 1)`, with `c` values left of which `h` pairs are
    folded and `ki + 1` pairs to go: the cursors (`x20` the odd index read, `x27` its element, `x24` the second half
    of the element written), the counter, the frame, the saved registers' slots and the locals. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k c h ki : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧
    R .x9 = regs .x12 + BitVec.ofNat 64 (32 * ((regs .x13).toNat - (k + 1))) ∧ R .x18 = regs .x11 ∧
    (R .x19).toNat = c ∧ (R .x8).toNat = h ∧ R .x26 = BitVec.ofNat 64 (ki + 1) ∧
    (R .x20).toNat = 2 * (h - (ki + 1)) + 1 ∧
    (R .x27).toNat = (m.getMem (regs .x10 + 8#64)).toNat + 16 * (2 * (h - (ki + 1)) + 1) ∧
    (R .x24).toNat = (m.getMem (regs .x10 + 8#64)).toNat + 16 * (h - (ki + 1)) + 8 ∧
    ki + 1 ≤ h ∧ 2 * h ≤ c ∧ c ≤ (m.getMem (regs .x10 + 16#64)).toNat ∧ k + 1 ≤ (regs .x13).toNat ∧
    env.Frame top (Spec.Whir.FoldRow.Out regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551472#64) = regs .x10 ∧
    M.getMem (top + 18446744073709551480#64) = m.getMem (regs .x10 + 8#64) + 16#64 ∧
    M.getMem (top + 18446744073709551488#64) = m.getMem (regs .x10 + 8#64) + 8#64 ∧
    M.getMem (top + 18446744073709551496#64) = regs .x12 + regs .x13 <<< 5 ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26 ∧
    M.getMem (top + 18446744073709551512#64) = regs .x27

/-- The outer loop's head (instruction 28) after round `rn - (k + 1)`: the round's address, the values left `x8` at
    most the row's length, the frame, the saved registers' slots and the locals. -/
def OInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧
    R .x9 = regs .x12 + BitVec.ofNat 64 (32 * ((regs .x13).toNat - (k + 1))) ∧ R .x18 = regs .x11 ∧
    (R .x8).toNat ≤ (m.getMem (regs .x10 + 16#64)).toNat ∧ k + 1 ≤ (regs .x13).toNat ∧
    env.Frame top (Spec.Whir.FoldRow.Out regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551472#64) = regs .x10 ∧
    M.getMem (top + 18446744073709551480#64) = m.getMem (regs .x10 + 8#64) + 16#64 ∧
    M.getMem (top + 18446744073709551488#64) = m.getMem (regs .x10 + 8#64) + 8#64 ∧
    M.getMem (top + 18446744073709551496#64) = regs .x12 + regs .x13 <<< 5 ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26 ∧
    M.getMem (top + 18446744073709551512#64) = regs .x27

theorem cnt_dec (k : Nat) : BitVec.ofNat 64 (k + 1) + 18446744073709551615#64 = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add, BitVec.add_assoc,
    show (BitVec.ofNat 64 1 + 18446744073709551615#64 : Word) = 0#64 from by decide, BitVec.add_zero]

set_option rv_sym.heap true in
/-- **The inner loop**, from its head: a pair folded into one value, then back to the head or to the outer loop's. -/
theorem inner (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needB : Nat} (hnM : 144 + needM ≤ need) (hnB : 144 + needB ≤ need)
    (hmu : Field.EMulT.specT env p L.mul.idx needM) (hpb : Aborts env p L.panicBoundsCheck.idx needB)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hC : Ctx env top regs m) {k c h : Nat}
    (hp0 : 0x10000000 ≤ (m.getMem (regs .x10 + 8#64)).toNat)
    (hpl : (m.getMem (regs .x10 + 8#64)).toNat + 16 * (m.getMem (regs .x10 + 16#64)).toNat ≤ (env.next m).toNat)
    (hpa : (m.getMem (regs .x10 + 8#64)).toNat % 8 = 0)
    (hout : ∀ R M, OInv env ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 56, ret, top⟩ :: rest, R, M⟩) :
    ∀ ki R M, LInv env ret top regs m k c h ki R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 104, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m k c h) fun ki R M hI ih => ?_
  obtain ⟨hstk', hal, hW, htop, hw, ha, -, hrn, hrw, hra⟩ := hC
  have hlay := env.layout
  have := hW.top_le
  have hge := hW.next_ge
  have hhe := hW.heapEnd_le
  obtain ⟨-, -, -, -, -, -, -, -, -, hkh, h2c, hcl, -, hF, -⟩ := id hI
  have hnm := hF.1
  have hnx := hF.2.1
  rv_introT hI
  have hsp : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hx24 : (R .x24 + 18446744073709551608#64).toNat = (R .x24).toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hlt : (m.getMem (regs .x10 + 8#64)).toNat + 16 * (m.getMem (regs .x10 + 16#64)).toNat < 2 ^ 64 := by
    have := env.heapEnd.isLt; omega
  have hF2 : ∀ (X : MachineState) (v0 v8 : Word), env.Frame (top + 18446744073709551472#64) Tactic.F M X →
      env.Frame top (Spec.Whir.FoldRow.Out regs m) m
        ((X.setMem (R .x24 + 18446744073709551608#64) v0).setMem (R .x24) v8) := by
    intro X v0 v8 hX
    have hFX := Tactic.frame_callF hI_14 hX (by omega)
    have hnX := hFX.2.1
    refine Tactic.frame_out (Tactic.frame_out hFX ?_ ?_) ?_ ?_
    · simp only [Spec.Whir.FoldRow.Out, vecPtr, vecLen, Layouts.Vec.ptr, Layouts.Vec.len, Layouts.E.byteSize,
        InRange, hx24]
      omega
    · intro he; have := congrArg BitVec.toNat he; rw [hx24] at this; omega
    · simp only [Spec.Whir.FoldRow.Out, vecPtr, vecLen, Layouts.Vec.ptr, Layouts.Vec.len, Layouts.E.byteSize,
        InRange]
      omega
    · intro he; have := congrArg BitVec.toNat he; omega
  rv_symT hp stop [56, 104] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)] using [hmu, hpb]
  · -- back to the head
    have hk0 : ki ≠ 0 := fun h0 => hc (by rw [h0]; decide)
    clear hc
    refine ih (ki - 1) _ _ (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_6 => rw [cnt_dec, Nat.sub_add_cancel (by omega)]
    case refine_7 => rw [toNat_add_ofNat (by omega)]; omega
    case refine_8 => rw [toNat_add_ofNat (by omega)]; omega
    case refine_9 => rw [toNat_add_ofNat (by omega)]; omega
    case refine_14 => exact hF2 _ _ _ hret2_14
    all_goals try omega
    all_goals rv_closeT
  · -- the last pair: to the outer loop's head
    clear hc
    refine hout _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_4 => omega
    case refine_6 => exact hF2 _ _ _ hret2_14
    all_goals try omega
    all_goals rv_closeT

/-- A round's head (instruction 32), round `rn - (k + 1)`: its address, the values left `x19` at most the row's
    length, the frame, the saved registers' slots and the locals. -/
def BInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧
    R .x9 = regs .x12 + BitVec.ofNat 64 (32 * ((regs .x13).toNat - (k + 1))) ∧ R .x18 = regs .x11 ∧
    (R .x19).toNat ≤ (m.getMem (regs .x10 + 16#64)).toNat ∧ k + 1 ≤ (regs .x13).toNat ∧
    env.Frame top (Spec.Whir.FoldRow.Out regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551472#64) = regs .x10 ∧
    M.getMem (top + 18446744073709551480#64) = m.getMem (regs .x10 + 8#64) + 16#64 ∧
    M.getMem (top + 18446744073709551488#64) = m.getMem (regs .x10 + 8#64) + 8#64 ∧
    M.getMem (top + 18446744073709551496#64) = regs .x12 + regs .x13 <<< 5 ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26 ∧
    M.getMem (top + 18446744073709551512#64) = regs .x27

theorem ushr1 (x : Word) : (x >>> 1).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

set_option rv_sym.heap true in
/-- **A round**, from its head: `beta * x` by two `base_mul`s, the count halved; to the outer loop's head if no pair
    is left, else into the inner loop. -/
theorem body (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needB needK : Nat} (hnM : 144 + needM ≤ need) (hnB : 144 + needB ≤ need)
    (hnK : 144 + needK ≤ need) (hmu : Field.EMulT.specT env p L.mul.idx needM)
    (hpb : Aborts env p L.panicBoundsCheck.idx needB) (hbm : Field.BaseMulT.specT env p L.baseMul.idx needK)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hC : Ctx env top regs m) {k : Nat}
    (hout : ∀ R M, OInv env ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 56, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, BInv env ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 64, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hC' := hC
  obtain ⟨hstk', hal, hW, htop, hw, ha, hb, hrn, hrw, hra⟩ := hC'
  have hlay := env.layout
  have := hW.top_le
  have hge := hW.next_ge
  have hhe := hW.heapEnd_le
  have hrl := hrw.lt
  unfold InWin at hrw
  obtain ⟨-, -, -, hcl, hkr, hF, -⟩ := id hI
  have hnm := hF.1
  have hnx := hF.2.1
  have hj : (regs .x12 + BitVec.ofNat 64 (32 * ((regs .x13).toNat - (k + 1)))).toNat =
      (regs .x12).toNat + 32 * ((regs .x13).toNat - (k + 1)) := toNat_add_ofNat (by omega)
  have hsp : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rv_introT hI
  rv_symT hp stop [56, 104] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)] using [hbm, hmu, hpb]
  all_goals have hF2 := Tactic.frame_callF (Tactic.frame_callF hF hret1_14 (by omega)) hret2_14 (by omega)
  all_goals have hh := ushr1 (R .x19)
  · -- no pair: to the outer loop's head
    refine hout _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_4 => omega
    case refine_6 => exact hF2
    all_goals try omega
    all_goals rv_closeT
  · -- into the inner loop
    have hh0 : 1 ≤ (R .x19).toNat / 2 := by
      rcases Nat.eq_zero_or_pos ((R .x19).toNat / 2) with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [hh, h0]; rfl)) hc
      · exact h0
    obtain ⟨hp0, hpl, hpa⟩ := hb.resolve_left (by omega)
    clear hc
    refine inner env p i L hp hL hnM hnB hmu hpb hstop hstk hC (c := (R .x19).toNat) (h := (R .x19).toNat / 2)
      hp0 hpl hpa hout ((R .x19).toNat / 2 - 1) _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_6 =>
      apply BitVec.eq_of_toNat_eq
      rw [hh, Nat.sub_add_cancel hh0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case refine_7 => rw [show (1#64 : Word).toNat = 1 from rfl]; omega
    case refine_8 => rw [hI_10, toNat_add_ofNat (by have := env.heapEnd.isLt; omega)]; omega
    case refine_9 => rw [hI_11, toNat_add_ofNat (by have := env.heapEnd.isLt; omega)]; omega
    case refine_14 => exact hF2
    all_goals try omega
    all_goals rv_closeT

theorem cur_step (q : Word) (j : Nat) :
    q + BitVec.ofNat 64 (32 * j) + 32#64 = q + BitVec.ofNat 64 (32 * (j + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * j + 32 = 32 * (j + 1) by omega]

theorem shl5 (x : Word) : x <<< 5 = BitVec.ofNat 64 (32 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm]

set_option rv_sym.heap true in
/-- **The outer loop**, from its head: the next round's address; to the final check after the last round, else a
    round (`body`), which comes back here. -/
theorem outer (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needB needK needA : Nat} (hnM : 144 + needM ≤ need) (hnB : 144 + needB ≤ need)
    (hnK : 144 + needK ≤ need) (hnA : 144 + needA ≤ need) (hmu : Field.EMulT.specT env p L.mul.idx needM)
    (hpb : Aborts env p L.panicBoundsCheck.idx needB) (hbm : Field.BaseMulT.specT env p L.baseMul.idx needK)
    (haf : Aborts env p L.assertFailedUsizeUsize.idx needA)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) Spec.Whir.FoldRow.Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hC : Ctx env top regs m) :
    ∀ k R M, OInv env ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 56, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInv env ret top regs m) fun k R M hI ih => ?_
  have hC' := hC
  obtain ⟨hstk', hal, hW, htop, hw, ha, hb, hrn, hrw, hra⟩ := hC'
  have hlay := env.layout
  have := hW.top_le
  have hrl := hrw.lt
  obtain ⟨-, -, -, hcl, hkr, hF, -⟩ := id hI
  have hsh := shl5 (regs .x13)
  rv_introT hI
  rv_symT hp stop [64, 144] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)]
  · -- the last round done: to the final check
    clear hc
    refine exit_ok env p i L hp hL hnA haf hstop hk hstk hal hW htop hw ha hb _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    all_goals omega
  · -- a round
    have hk0 : k ≠ 0 := by
      intro h0
      apply hc
      rw [cur_step, hI_12, hsh, h0, show (regs .x13).toNat - (0 + 1) + 1 = (regs .x13).toNat by omega]
    clear hc
    refine body env p i L hp hL hnM hnB hnK hmu hpb hbm hstop hstk hC (k := k - 1) (ih (k - 1) · · (by omega)) _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_2 => rw [cur_step, show (regs .x13).toNat - (k - 1 + 1) = (regs .x13).toNat - (k + 1) + 1 by omega]
    all_goals omega

set_option rv_sym.heap true in
/-- The steps from the entry, over `PreR`. -/
theorem total_raw (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needB needK needA : Nat} (hnM : 144 + needM ≤ need) (hnB : 144 + needB ≤ need)
    (hnK : 144 + needK ≤ need) (hnA : 144 + needA ≤ need) (hmu : Field.EMulT.specT env p L.mul.idx needM)
    (hpb : Aborts env p L.panicBoundsCheck.idx needB) (hbm : Field.BaseMulT.specT env p L.baseMul.idx needK)
    (haf : Aborts env p L.assertFailedUsizeUsize.idx needA) :
    HoldsT env p i need (PreR env) (fun _ _ _ _ => True) Spec.Whir.FoldRow.Out (Stop := AbortStop) := by
  rv_autoT hp stop [64, 144] with [hL] using [hbm, hmu, hpb, haf]
  all_goals have htop : top.toNat ≤ (regs .x10).toNat := hpre_2 ▸ hpre_6
  · -- no rounds: to the final check
    refine exit_ok env p i L hp hL hnA haf hstop hk hpre_3 hpre_11 hpre_12 htop hpre_7 hpre_8 hpre_9 _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_2 => exact Nat.le_refl _
    all_goals rv_closeT
  · -- the first round
    have hrn : 1 ≤ (regs .x13).toNat := by
      rcases Nat.eq_zero_or_pos (regs .x13).toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hc
      · exact h0
    obtain ⟨hrw, hra⟩ := hpre_10.resolve_left (by omega)
    have hC : Ctx env top regs m := ⟨by omega, hpre_11, hpre_12, htop, hpre_7, hpre_8, hpre_9, hrn, hrw, hra⟩
    clear hc
    refine body env p i L hp hL hnM hnB hnK hmu hpb hbm hstop hpre_3 hC (k := (regs .x13).toNat - 1)
      (outer env p i L hp hL hnM hnB hnK hnA hmu hpb hbm haf hstop hk hpre_3 hC _) _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_2 => rw [show (regs .x13).toNat - ((regs .x13).toNat - 1 + 1) = 0 by omega]; simp
    case refine_4 => exact Nat.le_refl _
    all_goals try omega
    all_goals rv_closeT

/-- **`fold_row` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needB needK needA : Nat} (hnM : 144 + needM ≤ need) (hnB : 144 + needB ≤ need)
    (hnK : 144 + needK ≤ need) (hnA : 144 + needA ≤ need) (hmu : Field.EMulT.specT env p L.mul.idx needM)
    (hpb : Aborts env p L.panicBoundsCheck.idx needB) (hbm : Field.BaseMulT.specT env p L.baseMul.idx needK)
    (haf : Aborts env p L.assertFailedUsizeUsize.idx needA) : specT env p i need :=
  Isa.TContract.mono (total_raw env p i L hp hL hnM hnB hnK hnA hmu hpb hbm haf)
    (fun _ _ _ _ ⟨⟨h1, h2, h3, h4, hP, h5⟩, hw⟩ => ⟨⟨h1, h2, h3, h4, preR_of_preT hP, h5⟩, hw⟩)
    (fun _ _ _ _ _ _ _ h => h) fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Whir.FoldRowT

/-- info: 'Rv64mc.Proof.Whir.FoldRowT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.FoldRowT.total
