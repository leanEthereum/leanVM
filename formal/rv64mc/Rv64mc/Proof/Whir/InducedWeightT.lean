/-
  Rv64mc.Proof.Whir.InducedWeightT

  `verifier::whir::induced_weight(message_log, queries, query_weights, point) -> Result<E, VerifierError>` is total
  (`specT`): from a result's slot of `24` bytes owned, in a window, 8-byte aligned, and the three slices (`a2`..`a7`)
  each none or in a window and 8-byte aligned (`SliceN`), it returns, writing at most the slot besides what it
  allocates (`SretOut`, the partial contract's), or the run ends with `a0 = 2` where `Subspace::new` or
  `Subspace::at` does. Safety only: the partial contract's value (`Spec/Whir/InducedWeight.lean`'s `spec`,
  `Model.inducedWeightRust`) is owed (class C).

  Cut at `Subspace::new`'s call (instruction 48, `new_ok`: its frame carried by `MemOk.call_at`, the subspace's two
  vectors from its `PostT`), at the outer loop's head (84, `outer`: `Total.loop` with the queries left; `Subspace::at`
  into `what`'s slot), at the inner loop's head (130, `inner`: `Total.loop` with the pairs left, each pass
  `inner_a`, the two `base_mul`s, and `inner_b`, `E::mul` and the cursors) and at the exit (192, `fin_ok`). Each part
  keeps `Mem` (`SavedT.MemOk`, the thirteen saved registers' slots) and `Frm` (the frame's words and the subspace's
  vectors), carried across a call by `keep_call`.

  ## Main definitions

  * `SliceN`, `PreT`, `specT`, `Mem`, `Frm`, `FinInv`, `IInv`, `OInv`, `NRegs`, `NWords`

  ## Main results

  * `slots`, `fin_ok`, `vecT_keep`, `keep_call`, `inner_a`, `inner_b`, `inner`, `outer`, `frm_init`, `new_ok`, `total`
-/

import Rv64mc.Proof.Whir.SubspaceNewT
import Rv64mc.Proof.Whir.SubspaceAtT
import Rv64mc.Proof.Field.BaseMulT
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Spec.Whir.InducedWeight
import Rv64mc.Gen.Tmpl.Verifier.Whir.InducedWeight

namespace Rv64mc.Proof.Whir.InducedWeightT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Whir
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Transcript (getMem_setMem_off)
open Rv64mc.Gen.Verifier.Whir.InducedWeight (Link tmpl)

/-- `n` elements of `w` bytes at `a`: none, or in a window and 8-byte aligned. -/
def SliceN (env : Env) (a n : Word) (w : Nat) : Prop :=
  n.toNat = 0 ∨ InWin env a (w * n.toNat) ∧ a.toNat % 8 = 0

/-- The total precondition: the result's slot (`24` bytes) in a window, 8-byte aligned, owned; `queries` (`a2`,
    `a3`), `query_weights` (`a4`, `a5`) and `point` (`a6`, `a7`) `SliceN`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 24 ∧
    SliceN env (regs .x12) (regs .x13) 8 ∧ SliceN env (regs .x14) (regs .x15) 16 ∧
    SliceN env (regs .x16) (regs .x17) 16

/-- **The total contract of `induced_weight`**: from `PreT` it returns, writing at most the slot (`SretOut`), or
    ends the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True) (SretOut Layouts.ResultE.byteSize) (Stop := AbortStop)

/-- What every part keeps of memory: `SavedT.MemOk` with the thirteen saved registers' slots, from `top - 8` (the
    return address) down to `top - 104` (`s11`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (SretOut Layouts.ResultE.byteSize regs m)
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64, 18446744073709551536#64, 18446744073709551528#64, 18446744073709551520#64,
      18446744073709551512#64]
    [ret, regs .x8, regs .x9, regs .x18, regs .x19, regs .x20, regs .x21, regs .x22, regs .x23, regs .x24,
      regs .x25, regs .x26, regs .x27] m M

/-- The saved slots lie in the `104` bytes below `top`. -/
theorem slots : SlotsIn 104
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64, 18446744073709551536#64, 18446744073709551528#64, 18446744073709551520#64,
      18446744073709551512#64] := slots_le

/-- The frame's words: the slot's address (`sp + 8`), `point + 8` (`sp + 0x10`), `point.len` (`sp + 0x18`),
    `queries` (`sp + 0x20`), `query_weights` (`sp + 0x28`); the subspace's `roots` and `inverses` vectors at
    `sp + 0x30` and `sp + 0x48`. -/
def Frm (env : Env) (top : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  M.getMem (top + 18446744073709551400#64) = regs .x10 ∧ M.getMem (top + 18446744073709551408#64) = regs .x16 + 8#64 ∧
    M.getMem (top + 18446744073709551416#64) = regs .x17 ∧ M.getMem (top + 18446744073709551424#64) = regs .x12 ∧
    M.getMem (top + 18446744073709551432#64) = regs .x14 ∧ VecT env M (top + 18446744073709551440#64) 8 ∧
    VecT env M (top + 18446744073709551464#64) 8

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- The exit (instruction 192): the stack pointer, `Mem`, the slot's address at `sp + 8`. -/
def FinInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551392#64 ∧ Mem env ret top regs m M ∧
    M.getMem (top + 18446744073709551400#64) = regs .x10

set_option rv_sym.heap true in
/-- **The exit**: `Ok(total)` into the slot, the epilogue, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (SretOut Layouts.ResultE.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 224 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hwS : InWin env (regs .x10) 24) (haS : (regs .x10).toNat % 8 = 0)
    (hoS : env.Owned m top (regs .x10) 24) :
    ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 192, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hF := hinv.2.1.1
  have hlS := hwS.lt
  rv_introT hinv
  rv_symT hp with [(by omega : env.stackLimit.toNat + 224 ≤ top.toNat)]
  rw [hinv_18]
  have o : ∀ k : Nat, k < 24 → SretOut Layouts.ResultE.byteSize regs m (regs .x10 + BitVec.ofNat 64 k) :=
    fun k hk => ⟨by rw [toNat_add_ofNat (by omega)]; omega,
      by rw [toNat_add_ofNat (by omega)]; simp only [Layouts.ResultE.byteSize]; omega⟩
  exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF (by simpa using o 0 (by omega))
    (hwS.ne_next (Nat.le_refl _) (by omega))) (o 8 (by omega)) (hwS.ne_next_add (o := 8) (by omega)))
    (o 16 (by omega)) (hwS.ne_next_add (o := 16) (by omega))

/-- **A vector's header kept** by a memory agreeing on its three words, `NEXT` not lowered. -/
theorem vecT_keep {env : Env} {M X : MachineState} {a : Word} {s : Nat} (h : VecT env M a s)
    (h0 : X.getMem a = M.getMem a) (h8 : X.getMem (a + 8#64) = M.getMem (a + 8#64))
    (h16 : X.getMem (a + 16#64) = M.getMem (a + 16#64)) (hn : (env.next M).toNat ≤ (env.next X).toNat) :
    VecT env X a s := by
  have e0 : rvCapAt a = a := by simp only [rvCapAt, Layouts.RawVecInner.cap]; exact BitVec.add_zero _
  have e8 : rvPtrAt a = a + 8#64 := by simp only [rvPtrAt, Layouts.RawVecInner.ptr]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2.keep (by rw [e0]; exact h0) (by rw [e8]; exact h8) hn, ?_⟩
  simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero] at h3 ⊢
  rw [show a + BitVec.ofNat 64 16 = a + 16#64 from rfl, h16, h0]
  exact h3

/-- **`Mem` and `Frm` across a call** from `sp` (`top - 224`) writing of the caller's at most words of `what`'s slot
    (`top - 128` to `top - 104`); every other word of the frame read as before. -/
theorem keep_call {env : Env} {ret top : Word} {regs : Reg → Word} {m M X : MachineState} {out' : Word → Prop}
    (hM : Mem env ret top regs m M) (hF : Frm env top regs M) (hlim : env.stackLimit.toNat + 224 ≤ top.toNat)
    (hf : env.Frame (top + 18446744073709551392#64) out' M X)
    (hout : ∀ a, out' a → top.toNat - 128 ≤ a.toNat ∧ a.toNat + 104 < top.toNat)
    (hk : ∀ a : Word, top + 18446744073709551392#64 ≤ a → ¬ out' a → X.getMem a = M.getMem a)
    (hc : X.code = M.code) (hs : env.Static X) :
    Mem env ret top regs m X ∧ Frm env top regs X ∧
      ∀ a : Word, top.toNat - 224 ≤ a.toNat → ¬ out' a → X.getMem a = M.getMem a := by
  obtain ⟨h1, rd⟩ := hM.call_at slots (by omega) hlim (by tn) hf (fun a ha => by have := hout a ha; omega) hk hc hs
  have r : ∀ c : Word, ∀ d, c.toNat + d = 2 ^ 64 → 128 < d → d ≤ 224 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c d hc' hd hd' => rd _ (by rw [BitVec.toNat_add]; omega) fun h => by
      have := hout _ h; rw [BitVec.toNat_add] at this; omega
  have r' : ∀ c : Word, ∀ d, c.toNat + d = 2 ^ 64 → 144 < d → d ≤ 224 → ∀ k : Word, k.toNat ≤ 16 →
      X.getMem (top + c + k) = M.getMem (top + c + k) := fun c d hc' hd hd' k hk => by
    rw [BitVec.add_assoc]
    exact rd _ (by rw [BitVec.toNat_add, BitVec.toNat_add]; omega) fun h => by
      have := hout _ h; rw [BitVec.toNat_add, BitVec.toNat_add] at this; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hF
  have hn := hf.1
  refine ⟨h1, ⟨(r _ 216 rfl (by omega) (by omega)).trans f1, (r _ 208 rfl (by omega) (by omega)).trans f2,
    (r _ 200 rfl (by omega) (by omega)).trans f3, (r _ 192 rfl (by omega) (by omega)).trans f4,
    (r _ 184 rfl (by omega) (by omega)).trans f5, vecT_keep f6 (r _ 176 rfl (by omega) (by omega))
      (r' _ 176 rfl (by omega) (by omega) _ (by decide)) (r' _ 176 rfl (by omega) (by omega) _ (by decide)) hn,
    vecT_keep f7 (r _ 152 rfl (by omega) (by omega)) (r' _ 152 rfl (by omega) (by omega) _ (by decide))
      (r' _ 152 rfl (by omega) (by omega) _ (by decide)) hn⟩, rd⟩

/-- The inner loop's head (instruction 130), query `c - d` of `c`, `e` of the `n` pairs left: the stack pointer, the
    query's index in `s0`, `c` in `s1`, `what`'s cursor `s2` and end `s4` in its buffer `W`, the point's cursor `s3`;
    `W`'s `n` words in a window, 8-byte aligned; `Mem`, `Frm`. -/
def IInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (c d n : Nat) (W : Word) (e : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551392#64 ∧ R .x8 = BitVec.ofNat 64 (c - d) ∧ (R .x9).toNat = c ∧
    (R .x18).toNat + 8 * e = W.toNat + 8 * n ∧ (R .x20).toNat = W.toNat + 8 * n ∧
    (R .x19).toNat + 16 * e = (regs .x16).toNat + 8 + 16 * n ∧ 1 ≤ e ∧ e ≤ n ∧ n ≤ (regs .x17).toNat ∧
    InWin env W (8 * n) ∧ W.toNat % 8 = 0 ∧ 1 ≤ d ∧ d ≤ c ∧ c ≤ (regs .x13).toNat ∧ c ≤ (regs .x15).toNat ∧
    Mem env ret top regs m M ∧ Frm env top regs M

/-- The outer loop's head (instruction 84), `d` of the `c` queries left: the stack pointer, the query's index in
    `s0`, `c` in `s2`, the point's length in `s1`; `Mem`, `Frm`. -/
def OInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (c d : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551392#64 ∧ R .x8 = BitVec.ofNat 64 (c - d) ∧ (R .x18).toNat = c ∧
    R .x9 = regs .x17 ∧ 1 ≤ d ∧ d ≤ c ∧ c ≤ (regs .x13).toNat ∧ c ≤ (regs .x15).toNat ∧
    Mem env ret top regs m M ∧ Frm env top regs M

set_option rv_sym.heap true in
/-- The inner loop's first half (instruction 130 to 154): the pair's value and challenge read, the two `base_mul`s of
    `challenge * (1 + value)`. -/
theorem inner_a (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needB : Nat} (hnB : 224 + needB ≤ need) (hbm : Field.BaseMulT.specT env p L.baseMul.idx needB)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hsp : SliceN env (regs .x16) (regs .x17) 16)
    {c d n : Nat} {W : Word} {e : Nat}
    (hnext : ∀ R M, IInv env ret top regs m c d n W e R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 154, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, IInv env ret top regs m c d n W e R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨-, -, h9, h18, h20, h19, he1, hen, hnp, hwW, hWa, hd1, hdc, hcq, hcw, hM, hF⟩ := id hI
  obtain ⟨hwp, hpa⟩ := hsp.resolve_left (by omega)
  have hlay := env.layout
  have hc0 := hM.2.1
  have hn0 := hM.1.1
  have hs0 := hM.2.2.1
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 224 ≤ top.toNat := by omega
  have hwl := hwW.lt
  have hpl := hwp.lt
  obtain ⟨dW, dWa⟩ := hwW.dword hW hWa (x := R .x18) (o := 8 * (n - e)) (by omega) (by omega) (by omega)
  obtain ⟨dP0, dP0a⟩ := hwp.dword hW hpa (x := R .x19 + 18446744073709551608#64) (o := 16 * (n - e))
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by omega) (by omega)
  obtain ⟨dP8, dP8a⟩ := hwp.dword hW hpa (x := R .x19) (o := 16 * (n - e) + 8) (by omega) (by omega) (by omega)
  have hR : R .x2 = top + 18446744073709551392#64 ∧ R .x8 = BitVec.ofNat 64 (c - d) := ⟨hI.1, hI.2.1⟩
  have hX := PLift.up (And.intro hI (And.intro hM hF))
  clear hM hF hwW hwp hI
  rv_introT hR
  rv_symT hp stop [154] with [hL, hlim] using [hbm]
  · exact dW
  obtain ⟨hI, hM, hF⟩ := hX.down
  obtain ⟨hM1, hF1, -⟩ := keep_call hM hF hlim hret1_14 (fun _ h => h.elim) (fun a h _ => keep1_1 a h) hret1_17
    hret1_15
  obtain ⟨hM2, hF2, -⟩ := keep_call hM1 hF1 hlim hret2_14 (fun _ h => h.elim) (fun a h _ => keep2_1 a h) hret2_17
    hret2_15
  refine hnext _ _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, he1, hen, hnp, hI.2.2.2.2.2.2.2.2.2.1, hWa, hd1, hdc, hcq, hcw, hM2, hF2⟩
  all_goals simp only [Tactic.rf]
  · exact h9
  · exact h18
  · exact h20
  · exact h19

set_option rv_sym.heap true in
/-- The inner loop's second half (instruction 154): the factor multiplied into the product (`E::mul`), the cursors
    advanced, then back to the head, or the product added to the total and on to the next query or the exit. -/
theorem inner_b (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needU : Nat} (hnU : 224 + needU ≤ need) (hmul : Field.EMulT.specT env p L.mul.idx needU)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hsp : SliceN env (regs .x16) (regs .x17) 16) {c d n : Nat} {W : Word} {e : Nat}
    (ih : ∀ e', e' < e → ∀ R M, IInv env ret top regs m c d n W e' R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩)
    (hfin : ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 192, ret, top⟩ :: rest, R, M⟩)
    (hnext : ∀ R M, 2 ≤ d → OInv env ret top regs m c (d - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 84, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, IInv env ret top regs m c d n W e R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 154, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨-, -, h9, h18, h20, h19, he1, hen, hnp, hwW, hWa, hd1, hdc, hcq, hcw, hM, hF⟩ := id hI
  obtain ⟨hwp, -⟩ := hsp.resolve_left (by omega)
  have hlay := env.layout
  have hc0 := hM.2.1
  have hn0 := hM.1.1
  have hs0 := hM.2.2.1
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 224 ≤ top.toNat := by omega
  have hwl := hwW.lt
  have hpl := hwp.lt
  have hR : R .x2 = top + 18446744073709551392#64 ∧ R .x8 = BitVec.ofNat 64 (c - d) := ⟨hI.1, hI.2.1⟩
  have hX := PLift.up (And.intro hI (And.intro hM hF))
  clear hM hF hwW hI hwp hsp
  rv_introT hR
  rv_symT hp stop [130, 84, 192] through [72] with [hL, hlim] using [hmul]
  all_goals
    obtain ⟨hI, hM, hF⟩ := hX.down
    obtain ⟨hM1, hF1, -⟩ := keep_call hM hF hlim hret1_14 (fun _ h => h.elim) (fun a h _ => keep1_1 a h) hret1_18
      hret1_15
    have hc9 : (R .x9).toNat < 2 ^ 64 := (R .x9).isLt
  -- back to the head
  · have e8 : (R .x18 + 8#64).toNat = (R .x18).toNat + 8 := toNat_add_ofNat (by omega)
    have hn20 : 2 ≤ e := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by rw [e8]; omega))
    refine ih (e - 1) (by omega) _ _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, by omega, by omega, hnp, hI.2.2.2.2.2.2.2.2.2.1, hWa,
      hd1, hdc, hcq, hcw, hM1, hF1⟩
    all_goals simp only [Tactic.rf]
    · exact h9
    · rw [e8]; omega
    · exact h20
    · rw [toNat_add_ofNat (by omega)]; omega
  -- the last query: the exit
  · exact hfin _ _ ⟨rfl, hM1, hF1.1⟩
  -- the next query
  · have hd2 : 2 ≤ d := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h9]; omega))
    refine hnext _ _ hd2 ⟨rfl, ?_, ?_, ?_, by omega, by omega, hcq, hcw, hM1, hF1⟩
    all_goals simp only [Tactic.rf]
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    · exact h9
    · exact hF.2.2.1

/-- **The inner loop**, from its head: `inner_a` then `inner_b`, one pair fewer left each pass. -/
theorem inner (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needB needU : Nat} (hnB : 224 + needB ≤ need) (hnU : 224 + needU ≤ need)
    (hbm : Field.BaseMulT.specT env p L.baseMul.idx needB) (hmul : Field.EMulT.specT env p L.mul.idx needU)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hsp : SliceN env (regs .x16) (regs .x17) 16)
    {c d n : Nat} {W : Word}
    (hfin : ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 192, ret, top⟩ :: rest, R, M⟩)
    (hnext : ∀ R M, 2 ≤ d → OInv env ret top regs m c (d - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 84, ret, top⟩ :: rest, R, M⟩) :
    ∀ e R M, IInv env ret top regs m c d n W e R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩ :=
  Total.loop (I := rvIsa) (IInv env ret top regs m c d n W) fun _ R M hI ih =>
    inner_a env p i L hp hL hnB hbm hstk hal hW hsp
      (inner_b env p i L hp hL hnU hmul hstk hal hW hsp (fun e' h R' M' hI' => ih e' R' M' h hI') hfin hnext) R M hI

set_option rv_sym.heap true in
/-- **The outer loop**, from its head: query `c - d`'s weight and position read, `Subspace::at` into `what`'s slot,
    then the inner loop over `min(point.len, what.len)` pairs, or for none the next query or the exit; one query
    fewer left. -/
theorem outer (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA : Nat} (hnA : 224 + needA ≤ need) (hat : SubspaceAtT.specT env p L.«at».idx needA)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hsq : SliceN env (regs .x12) (regs .x13) 8) (hsw : SliceN env (regs .x14) (regs .x15) 16)
    (hsp : SliceN env (regs .x16) (regs .x17) 16) {c : Nat}
    (hfin : ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 192, ret, top⟩ :: rest, R, M⟩)
    (hin : ∀ d, (∀ R M, 2 ≤ d → OInv env ret top regs m c (d - 1) R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 84, ret, top⟩ :: rest, R, M⟩) →
      ∀ n W e R M, IInv env ret top regs m c d n W e R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩) :
    ∀ d R M, OInv env ret top regs m c d R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 84, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInv env ret top regs m c) fun d R M hI ih => ?_
  obtain ⟨-, -, h18, h9, hd1, hdc, hcq, hcw, hM, hF⟩ := id hI
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := id hF
  have hlay := env.layout
  have hc0 := hM.2.1
  have hn0 := hM.1.1
  have hs0 := hM.2.2.1
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 224 ≤ top.toNat := by omega
  obtain ⟨hwq, hqa⟩ := hsq.resolve_left (by omega)
  obtain ⟨hww, hwa⟩ := hsw.resolve_left (by omega)
  have hql := hwq.lt
  have hwl := hww.lt
  have e3 : (regs .x12 + BitVec.ofNat 64 (c - d) <<< 3).toNat = (regs .x12).toNat + 8 * (c - d) := by
    rw [Runtime.WinT.elem_toNat (s := 3) (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; rfl
  have e4 : (regs .x14 + BitVec.ofNat 64 (c - d) <<< 4).toNat = (regs .x14).toNat + 16 * (c - d) := by
    rw [Runtime.WinT.elem_toNat (s := 4) (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; rfl
  obtain ⟨dq, dqa⟩ := hwq.dword hW hqa e3 (by omega) (by omega)
  obtain ⟨dw0, dw0a⟩ := hww.dword hW hwa e4 (by omega) (by omega)
  obtain ⟨dw8, dw8a⟩ := hww.dword_add (k := 8) hW hwa e4 (by omega) (by omega)
  have hV2 : VecT env M (top + 18446744073709551440#64 + 24#64) 8 := by
    rw [BitVec.add_assoc]; exact f7
  have hR : R .x2 = top + 18446744073709551392#64 ∧ R .x8 = BitVec.ofNat 64 (c - d) := ⟨hI.1, hI.2.1⟩
  have hX := PLift.up (And.intro hI (And.intro hM hF))
  clear hM hF hI hwq hww hsq hsw f7
  rv_introT hR
  rv_symT hp stop [84, 130, 192] through [72] with [hL, hlim] using [hat]
  · rw [f5]; exact dw0
  · rw [f5]; exact dw0a
  · rw [f5]; exact dw8
  · rw [f5]; exact dw8a
  · rw [f4]; exact dq
  · rw [f4]; exact dqa
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; exact f6.2.2
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; exact hV2.2.2
  all_goals
    obtain ⟨hI, hM, hF⟩ := hX.down
    have e128 : (top + 18446744073709551488#64).toNat = top.toNat - 128 := by tn
    obtain ⟨hM1, hF1, rd1⟩ := keep_call hM hF hlim hret1_14 (fun a ha => by
      simp only [SretOut, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, e128,
        Layouts.Vec.byteSize] at ha
      omega) keep1_1 hret1_24 hret1_15
    have hc9 : (R .x9).toNat < 2 ^ 64 := (R .x9).isLt
    obtain ⟨bc, bp, -, -, bL⟩ := Runtime.SavedT.hdr_at top 18446744073709551488#64 m1
    simp only [BitVec.reduceAdd] at bp bL
    rw [bc, bp] at hret1_19
    rw [bc] at hret1_20
    have hcl := hret1_21
    simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero] at hcl
    rw [show top + 18446744073709551488#64 + BitVec.ofNat 64 16 = top + 18446744073709551504#64 by
      rw [BitVec.add_assoc]; rfl] at hcl
    have hnm1 := hM1.1.2.1
    have hpl := hsp
  -- no pair, the last query: the exit
  · exact hfin _ _ ⟨rfl, hM1, hF1.1⟩
  -- no pair: the next query
  · have hd2 : 2 ≤ d := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h18]; omega))
    refine ih (d - 1) _ _ (by omega) ⟨rfl, ?_, ?_, ?_, by omega, by omega, hcq, hcw, hM1, hF1⟩
    all_goals simp only [Tactic.rf]
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    · exact h18
    · exact hF.2.2.1
  -- the inner loop over `point.len` pairs
  · have hn0 : (regs .x17).toNat ≠ 0 := fun h => hc (by rw [h9]; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    obtain ⟨hwp, hpa⟩ := hpl.resolve_left hn0
    have hpl' := hwp.lt
    have hlt : (regs .x17).toNat < (m1.getMem (top + 18446744073709551504#64)).toNat := by
      rw [← h9]; exact hc_1
    obtain ⟨hW1, hW2, hW3⟩ := hret1_19.resolve_left (by omega)
    unfold Env.Live at hW2
    refine hin d (fun R' M' h hO => ih (d - 1) R' M' (by omega) hO) (regs .x17).toNat
      (m1.getMem (top + 18446744073709551496#64)) (regs .x17).toNat _ _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, by omega,
      Nat.le_refl _, Nat.le_refl _, .inl ⟨hW1, by omega⟩, hW3, hd1, hdc, hcq, hcw, hM1, hF1⟩
    all_goals simp only [Tactic.rf]
    · exact h18
    · rw [h9, Runtime.WinT.elem_toNat (s := 3) (by omega)]; rfl
    · rw [f2, toNat_add_ofNat (by omega)]
  -- no pair, the last query: the exit
  · exact hfin _ _ ⟨rfl, hM1, hF1.1⟩
  -- no pair: the next query
  · have hd2 : 2 ≤ d := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h18]; omega))
    refine ih (d - 1) _ _ (by omega) ⟨rfl, ?_, ?_, ?_, by omega, by omega, hcq, hcw, hM1, hF1⟩
    all_goals simp only [Tactic.rf]
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    · exact h18
    · exact hF.2.2.1
  -- the inner loop over `what.len` pairs
  · have hn0 : (m1.getMem (top + 18446744073709551504#64)).toNat ≠ 0 := fun h =>
      hc (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have hle : (m1.getMem (top + 18446744073709551504#64)).toNat ≤ (regs .x17).toNat := by
      rw [← h9]; exact hc_1
    obtain ⟨hwp, hpa⟩ := hpl.resolve_left (by omega)
    have hpl' := hwp.lt
    obtain ⟨hW1, hW2, hW3⟩ := hret1_19.resolve_left (by omega)
    unfold Env.Live at hW2
    refine hin d (fun R' M' h hO => ih (d - 1) R' M' (by omega) hO) (m1.getMem (top + 18446744073709551504#64)).toNat
      (m1.getMem (top + 18446744073709551496#64)) (m1.getMem (top + 18446744073709551504#64)).toNat _ _
      ⟨rfl, rfl, ?_, ?_, ?_, ?_, by omega, Nat.le_refl _, hle, .inl ⟨hW1, by omega⟩, hW3, hd1, hdc, hcq, hcw, hM1,
        hF1⟩
    all_goals simp only [Tactic.rf]
    · exact h18
    · rw [Runtime.WinT.elem_toNat (s := 3) (by omega)]; rfl
    · rw [f2, toNat_add_ofNat (by omega)]

/-- The registers at `Subspace::new`'s call (instruction 48): the stack pointer, `point.len` in `s1`,
    `query_weights.len` in `s2`, `point` in `s5`, `queries.len` in `s6`, the slot's address in `a0`, the
    callee-saved registers the function has not written. -/
def NRegs (top : Word) (regs : Reg → Word) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551392#64 ∧ R .x9 = regs .x17 ∧ R .x18 = regs .x15 ∧ R .x22 = regs .x13 ∧
    R .x21 = regs .x16 ∧ R .x10 = top + 18446744073709551440#64 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧
    R .x23 = regs .x23 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25

/-- The frame's three words stored before `Subspace::new`'s call: the slot's address, `queries`, `query_weights`. -/
def NWords (top : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  M.getMem (top + 18446744073709551400#64) = regs .x10 ∧ M.getMem (top + 18446744073709551424#64) = regs .x12 ∧
    M.getMem (top + 18446744073709551432#64) = regs .x14

/-- **`Frm` from the subspace's two vectors and the frame's words**, after the stores of `point + 8` and
    `point.len` at `sp + 0x10` and `sp + 0x18`. -/
theorem frm_init {env : Env} {top : Word} {regs : Reg → Word} {M : MachineState}
    (hlim : env.stackLimit.toNat + 224 ≤ top.toNat) (hV1 : VecT env M (top + 18446744073709551440#64) 8)
    (hV2 : VecT env M (top + 18446744073709551464#64) 8) (w1 : M.getMem (top + 18446744073709551400#64) = regs .x10)
    (w4 : M.getMem (top + 18446744073709551424#64) = regs .x12)
    (w5 : M.getMem (top + 18446744073709551432#64) = regs .x14) :
    Frm env top regs ((M.setMem (top + 18446744073709551408#64) (regs .x16 + 8#64)).setMem
      (top + 18446744073709551416#64) (regs .x17)) := by
  have hlay := env.layout
  have n : ∀ c : Word, 2 ^ 64 - 224 ≤ c.toNat → top + c ≠ env.nextAddr := fun c hc =>
    Tactic.ne_of_toNat (by rw [BitVec.toNat_add]; omega)
  have hn : env.next ((M.setMem (top + 18446744073709551408#64) (regs .x16 + 8#64)).setMem
      (top + 18446744073709551416#64) (regs .x17)) = env.next M := by
    rw [Tactic.next_setMem (n _ (by decide)), Tactic.next_setMem (n _ (by decide))]
  refine ⟨?_, ?_, ?_, ?_, ?_, vecT_keep hV1 ?_ ?_ ?_ (by rw [hn]), vecT_keep hV2 ?_ ?_ ?_ (by rw [hn])⟩
  all_goals simp (disch := decide) only [BitVec.add_assoc, BitVec.reduceAdd, getMem_setMem_off,
    MachineState.getMem_setMem_eq]
  · exact w1
  · exact w4
  · exact w5

set_option rv_sym.heap true in
/-- `Subspace::new(message_log)` into the frame (instruction 48), the count `min(query_weights.len, queries.len)`,
    then the exit for none or the outer loop's head. -/
theorem new_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needN : Nat} (hnN : 224 + needN ≤ need) (hnw : SubspaceNewT.specT env p L.new.idx needN)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hfin : ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 192, ret, top⟩ :: rest, R, M⟩)
    (hout : ∀ c d R M, OInv env ret top regs m c d R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 84, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, NRegs top regs R ∧ Mem env ret top regs m M ∧ NWords top regs M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 48, ret, top⟩ :: rest, R, M⟩ := by
  intro R M ⟨hR, hM, hw⟩
  have hc0 := hM.2.1
  have hn0 := hM.1.1
  have hs0 := hM.2.2.1
  have hnM := hM.1.2.1
  have hlay := env.layout
  have hlim : env.stackLimit.toNat + 224 ≤ top.toNat := by omega
  have hX := PLift.up (And.intro hM hw)
  clear hM hw
  rv_introT hR
  rv_symT hp stop [84, 192] with [hL, hlim] using [hnw]
  all_goals
    obtain ⟨hM, w1, w2, w3⟩ := hX.down
    have hV1 : VecT env m1 (top + 18446744073709551440#64) 8 :=
      ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩
    have hV2 : VecT env m1 (top + 18446744073709551464#64) 8 := by
      have h : VecT env m1 (top + 18446744073709551440#64 + 24#64) 8 :=
        ⟨hret1_24, ⟨hret1_25, hret1_26, hret1_27, hret1_28⟩, hret1_29⟩
      rwa [BitVec.add_assoc] at h
    have e176 : (top + 18446744073709551440#64).toNat = top.toNat - 176 := by tn
    obtain ⟨hM1, rd⟩ := hM.call_at slots (by omega) hlim (by tn) hret1_14 (fun a ha => by
      simp only [SretOut, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, e176,
        Layouts.Subspace.byteSize] at ha
      omega) keep1_1 hret1_32 hret1_15
    have rw : ∀ c : Word, ∀ d, c.toNat + d = 2 ^ 64 → 176 < d → d ≤ 224 → m1.getMem (top + c) = M.getMem (top + c) :=
      fun c d hc' hd hd' => rd _ (by rw [BitVec.toNat_add]; omega) fun h => by
        simp only [SretOut, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, e176,
          Layouts.Subspace.byteSize] at h
        rw [BitVec.toNat_add] at h; omega
    have v1 := (rw _ 216 rfl (by omega) (by omega)).trans w1
    have hF := fun (hsl : env.stackLimit.toNat + 224 ≤ top.toNat) => frm_init (regs := regs) hsl hV1 hV2 v1
      ((rw _ 192 rfl (by omega) (by omega)).trans w2) ((rw _ 184 rfl (by omega) (by omega)).trans w3)
    obtain ⟨hM2, -⟩ := hM1.slot (a := top + 18446744073709551408#64) (v := regs .x16 + 8#64) slots (F := 224) hlim
      (by tn) (by tn)
    obtain ⟨hM3, -⟩ := hM2.slot (a := top + 18446744073709551416#64) (v := regs .x17) slots (F := 224) hlim
      (by tn) (by tn)
  -- no query: the exit
  · exact hfin _ _ ⟨rfl, hM1, v1⟩
  -- `query_weights.len` queries
  · refine hout (regs .x15).toNat (regs .x15).toNat _ _ ⟨rfl, ?_, rfl, rfl, ?_, Nat.le_refl _, ?_, Nat.le_refl _, hM3,
      hF hlim⟩
    · simp only [Tactic.rf, Nat.sub_self]
    · exact Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact Nat.le_of_lt (BitVec.lt_def.1 hc_1)
  · exact hfin _ _ ⟨rfl, hM1, v1⟩
  -- `queries.len` queries
  · refine hout (regs .x13).toNat (regs .x13).toNat _ _ ⟨rfl, ?_, rfl, rfl, ?_, Nat.le_refl _, Nat.le_refl _, ?_, hM3,
      hF hlim⟩
    · simp only [Tactic.rf, Nat.sub_self]
    · exact Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact BitVec.le_def.1 hc_1

set_option rv_sym.heap true in
/-- **`induced_weight` is total**: the prologue, `Err` when `point.len ≠ message_log`, else the parts. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needN needA needB needU : Nat} (hnN : 224 + needN ≤ need) (hnA : 224 + needA ≤ need)
    (hnB : 224 + needB ≤ need) (hnU : 224 + needU ≤ need) (hnw : SubspaceNewT.specT env p L.new.idx needN)
    (hat : SubspaceAtT.specT env p L.«at».idx needA) (hbm : Field.BaseMulT.specT env p L.baseMul.idx needB)
    (hmul : Field.EMulT.specT env p L.mul.idx needU) : specT env p i need := by
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 224 ≤ top.toNat)]
  have hfin := fin_ok env p i L hp hk hpre_3 (by omega) hpre_13 hpre_14 hpre_6 hpre_7 (hpre_2 ▸ ⟨hpre_8, hpre_9⟩)
  have hnew := new_ok env p i L hp hL hnN hnw hstop hpre_3 hpre_13 hpre_14 hfin
    fun c => outer env p i L hp hL hnA hat hstop hpre_3 hpre_13 hpre_14 hpre_10 hpre_11 hpre_12 (c := c) hfin
      fun _ hl _ _ => inner env p i L hp hL hnB hnU hbm hmul hpre_3 hpre_13 hpre_14 hpre_12 hfin hl
  clear hpre_10 hpre_11 hpre_12 hfin
  rv_symT hp stop [48] with [hL, (by omega : env.stackLimit.toNat + 224 ≤ top.toNat)]
  refine hnew _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  iterate 3 rv_closeT

end Rv64mc.Proof.Whir.InducedWeightT

/-- info: 'Rv64mc.Proof.Whir.InducedWeightT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.InducedWeightT.total
