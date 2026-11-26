/-
  Rv64mc.Proof.Whir.RingWeightT

  `verifier::ring_switch::ring_weight` is total (`specT`): from `r` (`a0`, `a1` elements), unless empty, allocated
  before (`Live`, the partial `RingWeight.Pre`'s `ESlice`) and in a window, and `r_prime` (`a2`, `a3`) and the
  coefficients (`a4`, `a5`), unless empty, in windows and 8-byte aligned, it returns, writing nothing of its
  caller's besides its stack and the copy of `r` it allocates, or ends the run with `a0 = 2` (`assert_eq!` on the
  lengths, the allocator out of heap). Safety only: the partial specification (`Spec/Whir/RingWeight.lean`, class C)
  has no proof. `rv_autoT` steps from the entry to the loops' set-up (instruction 32, `head`); two loops: over the
  coefficients (`outer`, from the step to the next one at instruction 42, the coefficients left as the measure) and
  over the copy's elements (`inner`, the elements left as the measure).

  ## Main definitions

  * `PreT`, `specT`, `Saved`, `Ctx`, `BufF`, `OInvA`, `LInv`, `PInv`

  ## Main results

  * `inner`, `outer`, `head`, `total`
-/

import Rv64mc.Core.AbortStop
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Field.ESquareT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Proof.Multilinear.Heap
import Rv64mc.Proof.Whir.Arith
import Rv64mc.Tactic.SymT
import Rv64mc.Gen.Tmpl.Verifier.RingSwitch.RingWeight

namespace Rv64mc.Proof.Whir.RingWeightT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.RingSwitch.RingWeight (Link tmpl)

/-- The total precondition: `r` (`a0`, `a1` elements), unless empty, allocated before and in a window; `r_prime`
    (`a2`, `a3`) and the coefficients (`a4`, `a5`), unless empty, in windows and 8-byte aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  ((regs .x11).toNat = 0 ∨
    (env.Live m (regs .x10) (16 * (regs .x11).toNat) ∧ InWin env (regs .x10) (16 * (regs .x11).toNat))) ∧
  ((regs .x13).toNat = 0 ∨ (InWin env (regs .x12) (16 * (regs .x13).toNat) ∧ (regs .x12).toNat % 8 = 0)) ∧
  ((regs .x15).toNat = 0 ∨ (InWin env (regs .x14) (16 * (regs .x15).toNat) ∧ (regs .x14).toNat % 8 = 0))

/-- **The total contract of `ring_weight`**: it returns, writing nothing of its caller's, or ends the run with
    `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True) (Stop := AbortStop)

/-- The saved registers' slots, from `top - 8` (the return address) down to `top - 104` (`s11`), as the prologue
    wrote them. -/
abbrev Saved (ret top : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26 ∧
    M.getMem (top + 18446744073709551512#64) = regs .x27

/-- The hypotheses the loops share: the stack, the windows, `r_prime` as long as `r`, its elements and the
    coefficients' in windows and aligned unless none, the byte count `16 n` without wrapping. -/
structure Ctx (env : Env) (top : Word) (regs : Reg → Word) (m : MachineState) : Prop where
  hstk : env.stackLimit.toNat + 144 ≤ top.toNat
  hal : top.toNat % 16 = 0
  hW : Windows env top m
  hnx : (env.next m).toNat ≤ env.heapEnd.toNat
  hn : 16 * (regs .x11).toNat < 2 ^ 63
  hrp : (regs .x11).toNat = 0 ∨ (InWin env (regs .x12) (16 * (regs .x11).toNat) ∧ (regs .x12).toNat % 8 = 0)
  hcs : (regs .x15).toNat = 0 ∨ (InWin env (regs .x14) (16 * (regs .x15).toNat) ∧ (regs .x14).toNat % 8 = 0)

/-- The copy of `r`, unless empty: a block allocated since the entry, 8-byte aligned. -/
def BufF (env : Env) (m M : MachineState) (n b : Word) : Prop :=
  n.toNat = 0 ∨ ((env.next m).toNat ≤ b.toNat ∧ b.toNat + 16 * n.toNat ≤ (env.next M).toNat ∧ b.toNat % 8 = 0)

/-- The step to the next coefficient (instruction 42) with `k` coefficients left after it: the coefficient's cursor
    one back, the cursors' bases (`r_prime`'s and the copy's, past their first halves), `r_prime`'s end, the frame, the
    copy, the slots (`n` and the coefficients' end besides the saved registers). -/
def OInvA (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (b : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧
    R .x8 = regs .x14 + BitVec.ofNat 64 (16 * ((regs .x15).toNat - (k + 1))) ∧ k + 1 ≤ (regs .x15).toNat ∧
    R .x24 = regs .x12 + 8#64 ∧ R .x9 = b + 8#64 ∧ R .x27 = regs .x12 + 8#64 + regs .x11 <<< 4 ∧
    env.Frame top Tactic.F m M ∧ M.code = m.code ∧ env.Static M ∧ BufF env m M (regs .x11) b ∧
    M.getMem (top + 18446744073709551480#64) = regs .x14 + regs .x15 <<< 4 ∧
    M.getMem (top + 18446744073709551488#64) = regs .x11 ∧ Saved ret top regs M

/-- The inner loop's head (instruction 53) with `k` coefficients left counting this one and `kk + 1` elements to
    go: `OInvA`'s facts with the cursor on this coefficient, and the cursors into `r_prime` (`x25`) and the copy
    (`x26`). -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (b : Word) (k kk : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧
    R .x8 = regs .x14 + BitVec.ofNat 64 (16 * ((regs .x15).toNat - k)) ∧ 1 ≤ k ∧ k ≤ (regs .x15).toNat ∧
    R .x24 = regs .x12 + 8#64 ∧ R .x9 = b + 8#64 ∧ R .x27 = regs .x12 + 8#64 + regs .x11 <<< 4 ∧
    (R .x25).toNat = (regs .x12).toNat + 8 + 16 * ((regs .x11).toNat - (kk + 1)) ∧
    (R .x26).toNat = b.toNat + 8 + 16 * ((regs .x11).toNat - (kk + 1)) ∧ kk + 1 ≤ (regs .x11).toNat ∧
    env.Frame top Tactic.F m M ∧ M.code = m.code ∧ env.Static M ∧ BufF env m M (regs .x11) b ∧
    M.getMem (top + 18446744073709551480#64) = regs .x14 + regs .x15 <<< 4 ∧
    M.getMem (top + 18446744073709551488#64) = regs .x11 ∧ Saved ret top regs M

theorem shl4 (x : Word) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm]

/- Each pass goes through `E::mul` and `E::square`, whose results stay in the register file: the default heartbeats
   do not cover the two paths. -/
set_option maxHeartbeats 400000 in
set_option rv_sym.heap true in
/-- **The inner loop**, from its head: an element of the copy squared after its product with the coefficient is
    accumulated; back to the head, or to the outer loop's head with the next coefficient. -/
theorem inner (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needS : Nat} (hnM : 144 + needM ≤ need) (hnS : 144 + needS ≤ need)
    (hmu : Field.EMulT.specT env p L.mul.idx needM) (hsq : Field.ESquareT.specT env p L.square.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hC : Ctx env top regs m) {b : Word} {k : Nat}
    (hout : ∀ R M, OInvA env ret top regs m b (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 84, ret, top⟩ :: rest, R, M⟩) :
    ∀ kk R M, LInv env ret top regs m b k kk R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 106, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m b k) fun kk R M hI ih => ?_
  obtain ⟨hstk', hal, hW, hnx0, hn, hrp, -⟩ := hC
  have hlay := env.layout
  have := hW.top_le
  have hge := hW.next_ge
  have hhe := hW.heapEnd_le
  obtain ⟨-, -, -, -, -, -, -, -, -, hkn, hF, -, -, hB, -⟩ := id hI
  obtain ⟨hrw, hra⟩ := hrp.resolve_left (by omega)
  obtain ⟨hb0, hbn, hba⟩ := hB.resolve_left (by omega)
  have hrl := hrw.lt
  unfold InWin at hrw
  have hnm := hF.1
  have hnx := hF.2.1
  rv_introT hI
  have hsp : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hx26 : (R .x26 + 18446744073709551608#64).toNat = (R .x26).toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hend : (regs .x12 + 8#64 + regs .x11 <<< 4).toNat = (regs .x12).toNat + 8 + 16 * (regs .x11).toNat := by
    rw [shl4, toNat_add_ofNat (by rw [toNat_add_ofNat (by omega)]; omega), toNat_add_ofNat (by omega)]
  have hF2 : ∀ (X1 X2 : MachineState) (v0 v8 : Word), env.Frame (top + 18446744073709551472#64) Tactic.F M X1 →
      env.Frame (top + 18446744073709551472#64) Tactic.F X1 X2 →
      env.Frame top Tactic.F m ((X2.setMem (R .x26 + 18446744073709551608#64) v0).setMem (R .x26) v8) ∧
        BufF env m ((X2.setMem (R .x26 + 18446744073709551608#64) v0).setMem (R .x26) v8) (regs .x11) b := by
    intro X1 X2 v0 v8 h1 h2
    have hFX := Tactic.frame_callF (Tactic.frame_callF hI_11 h1 (by omega)) h2 (by omega)
    have hn1 := h1.1
    have hn2 := h2.1
    have hN0 := Multilinear.next_store_heap (env := env) (N := X2) (a := R .x26 + 18446744073709551608#64) (v := v0)
      (by rw [hx26]; omega)
    have hN1 := Multilinear.next_store_heap (env := env) (N := X2.setMem (R .x26 + 18446744073709551608#64) v0)
      (a := R .x26) (v := v8) (by omega)
    refine ⟨Multilinear.frame_store_heap (Multilinear.frame_store_heap hFX ?_ ?_) ?_ ?_, Or.inr ⟨hb0, ?_, hba⟩⟩
    · rw [hx26]; omega
    · rw [hx26]; omega
    · omega
    · rw [hN0]; omega
    · rw [hN1, hN0]; omega
  rv_symT hp stop [84, 106] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)] using [hmu, hsq]
  · -- back to the head
    have hk0 : kk ≠ 0 := by
      intro h0
      apply hc
      apply BitVec.eq_of_toNat_eq
      rw [hend, toNat_add_ofNat (by omega)]
      omega
    clear hc
    obtain ⟨hF', hB'⟩ := hF2 _ _ _ _ hret1_14 hret2_14
    refine ih (kk - 1) _ _ (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hF', ?_, ?_, hB', ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_8 => rw [toNat_add_ofNat (by omega)]; omega
    case refine_9 => rw [toNat_add_ofNat (by omega)]; omega
    case refine_3 => omega
    case refine_4 => omega
    case refine_10 => omega
    all_goals rv_closeT
  · -- the last element: to the next coefficient
    clear hc
    obtain ⟨hF', hB'⟩ := hF2 _ _ _ _ hret1_14 hret2_14
    refine hout _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, hF', ?_, ?_, hB', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_2 => rw [show (regs .x15).toNat - (k - 1 + 1) = (regs .x15).toNat - k by omega]
    case refine_3 => omega
    all_goals rv_closeT

/-- The cursor after the step to the next coefficient, `k` of `n` left before it, `k - 1` after. -/
theorem cur_back (q : Word) {k n : Nat} (hk : k ≠ 0) (hkn : k + 1 ≤ n) :
    q + BitVec.ofNat 64 (16 * (n - (k + 1))) + 16#64 = q + BitVec.ofNat 64 (16 * (n - (k - 1 + 1))) := by
  rw [ptr_step, show n - (k + 1) + 1 = n - (k - 1 + 1) by omega]

set_option rv_sym.heap true in
/-- **The outer loop**, from the step to the next coefficient: the cursor moved, the return after the last one,
    else the coefficient read and the inner loop entered (or skipped when `r` is empty). -/
theorem outer (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needS : Nat} (hnM : 144 + needM ≤ need) (hnS : 144 + needS ≤ need)
    (hmu : Field.EMulT.specT env p L.mul.idx needM) (hsq : Field.ESquareT.specT env p L.square.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hC : Ctx env top regs m) {b : Word} :
    ∀ k R M, OInvA env ret top regs m b k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 84, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInvA env ret top regs m b) fun k R M hI ih => ?_
  have hC' := hC
  obtain ⟨hstk', hal, hW, hnx0, hn, hrp, hcs⟩ := hC'
  have hlay := env.layout
  have := hW.top_le
  have hge := hW.next_ge
  have hhe := hW.heapEnd_le
  obtain ⟨-, -, hkc, -, -, -, hF, -⟩ := id hI
  obtain ⟨hcw, hca⟩ := hcs.resolve_left (by omega)
  have hcl := hcw.lt
  unfold InWin at hcw
  have hnm := hF.1
  have hnx := hF.2.1
  have hsh := shl4 (regs .x15)
  rv_introT hI
  have hna := hW.nextAddr_ge
  have hj : (regs .x14 + BitVec.ofNat 64 (16 * ((regs .x15).toNat - (k + 1)))).toNat =
      (regs .x14).toNat + 16 * ((regs .x15).toNat - (k + 1)) := toNat_add_ofNat (by omega)
  rv_symT hp stop [84, 106] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)] using [hmu, hsq]
  all_goals try rw [hI_11, ptr_step, hsh] at hc
  all_goals try rw [hI_11, ptr_step, hsh] at hc_1
  all_goals try have hk0 : k ≠ 0 := fun h0 => hc (by
    rw [h0, show (regs .x15).toNat - (0 + 1) + 1 = (regs .x15).toNat by omega])
  all_goals try have hk0 : k ≠ 0 := fun h0 => hc_1 (by
    rw [h0, show (regs .x15).toNat - (0 + 1) + 1 = (regs .x15).toNat by omega])
  all_goals try (try rw [Rv64mc.inWindow_iff]); rw [toNat_add_ofNat (by rw [hj]; omega), hj]; omega
  all_goals have hx8 := cur_back (regs .x14) (n := (regs .x15).toNat) hk0 hI_3
  · -- `r` empty: the next coefficient
    clear hc hc_1
    refine ih (k - 1) _ _ (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_2 => exact hx8
    case refine_3 => omega
    all_goals rv_closeT
  · -- into the inner loop
    rw [hI_12] at hc
    have hn0 : 1 ≤ (regs .x11).toNat := by
      rcases Nat.eq_zero_or_pos (regs .x11).toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hc
      · exact h0
    clear hc hc_1
    obtain ⟨hb0, hbn, hba⟩ := hI_10.resolve_left (by omega)
    have hrl := (hrp.resolve_left (by omega)).1.lt
    refine inner env p i L hp hL hnM hnS hmu hsq hstk hC (k := k) (b := b)
      (fun R M h => ih (k - 1) R M (by omega) h) ((regs .x11).toNat - 1) _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_2 => rw [ptr_step, show (regs .x15).toNat - (k + 1) + 1 = (regs .x15).toNat - k by omega]
    case refine_3 => omega
    case refine_4 => omega
    case refine_8 => rw [toNat_add_ofNat (by omega)]; omega
    case refine_9 => rw [toNat_add_ofNat (by omega)]; omega
    case refine_10 => omega
    all_goals rv_closeT

/-- The loops' set-up (instruction 32), with at least one coefficient: the arguments in place, the copy of `r` in
    `x23`, the frame, the saved registers' slots. -/
def PInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x8 = regs .x14 ∧ R .x9 = regs .x11 ∧ R .x20 = regs .x15 ∧
    R .x21 = regs .x12 ∧ R .x22 = regs .x11 <<< 4 ∧ 1 ≤ (regs .x15).toNat ∧
    env.Frame top Tactic.F m M ∧ M.code = m.code ∧ env.Static M ∧ BufF env m M (regs .x11) (R .x23) ∧
    Saved ret top regs M

set_option rv_sym.heap true in
/-- **The set-up**: the slots of `n` and the coefficients' end, the cursors; into the outer loop's first pass. -/
theorem head (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needS : Nat} (hnM : 144 + needM ≤ need) (hnS : 144 + needS ≤ need)
    (hmu : Field.EMulT.specT env p L.mul.idx needM) (hsq : Field.ESquareT.specT env p L.square.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hC : Ctx env top regs m) :
    ∀ R M, PInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 64, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hC' := hC
  obtain ⟨hstk', hal, hW, hnx0, hn, hrp, hcs⟩ := hC'
  have hlay := env.layout
  have := hW.top_le
  have hge := hW.next_ge
  have hhe := hW.heapEnd_le
  have hna := hW.nextAddr_ge
  obtain ⟨-, -, -, -, -, -, hc1, hF, -, -, hB, -⟩ := id hI
  obtain ⟨hcw, hca⟩ := hcs.resolve_left (by omega)
  have hcl := hcw.lt
  unfold InWin at hcw
  have hnm := hF.1
  have hnx := hF.2.1
  have hsh := shl4 (regs .x15)
  rv_introT hI
  have h128 : (top + 18446744073709551488#64).toNat = top.toNat - 128 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h136 : (top + 18446744073709551480#64).toNat = top.toNat - 136 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hN : ∀ v0 v8 : Word, env.next ((M.setMem (top + 18446744073709551488#64) v0).setMem
      (top + 18446744073709551480#64) v8) = env.next M := fun v0 v8 => by
    rw [Tactic.next_setMem (fun h => by have := congrArg BitVec.toNat h; rw [h136] at this; omega),
      Tactic.next_setMem (fun h => by have := congrArg BitVec.toNat h; rw [h128] at this; omega)]
  rv_symT hp stop [84, 106] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)] using [hmu, hsq]
  · -- `r` empty: the next coefficient
    clear hc
    refine outer env p i L hp hL hnM hnS hmu hsq hk hstk hC (b := R .x23) ((regs .x15).toNat - 1) _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_2 => rw [show (regs .x15).toNat - ((regs .x15).toNat - 1 + 1) = 0 by omega]; simp
    case refine_3 => omega
    case refine_10 =>
      refine hB.imp id fun ⟨h1, h2, h3⟩ => ⟨h1, ?_, h3⟩
      rw [hN]; exact h2
    all_goals rv_closeT
  · -- into the inner loop
    have hn0 : 1 ≤ (regs .x11).toNat := by
      rcases Nat.eq_zero_or_pos (regs .x11).toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hc
      · exact h0
    clear hc
    obtain ⟨hb0, hbn, hba⟩ := hB.resolve_left (by omega)
    have hrl := (hrp.resolve_left (by omega)).1.lt
    refine inner env p i L hp hL hnM hnS hmu hsq hstk hC (k := (regs .x15).toNat) (b := R .x23)
      (outer env p i L hp hL hnM hnS hmu hsq hk hstk hC (b := R .x23) _) ((regs .x11).toNat - 1) _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_2 => rw [Nat.sub_self]; simp
    case refine_3 => omega
    case refine_4 => omega
    case refine_8 => rw [toNat_add_ofNat (by omega)]; omega
    case refine_9 => rw [toNat_add_ofNat (by omega)]; omega
    case refine_10 => omega
    case refine_14 => exact .inr ⟨hb0, by rw [hN]; exact hbn, hba⟩
    all_goals rv_closeT

set_option rv_sym.heap true in
/-- **`ring_weight` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needH needC needM needS needF : Nat} (hnA : 144 + needA ≤ need)
    (hnH : 144 + needH ≤ need) (hnC : 144 + needC ≤ need) (hnM : 144 + needM ≤ need) (hnS : 144 + needS ≤ need)
    (hnF : 144 + needF ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hhe : Aborts env p L.handleError.idx needH)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needC) (hmu : Field.EMulT.specT env p L.mul.idx needM)
    (hsq : Field.ESquareT.specT env p L.square.idx needS)
    (haf : Aborts env p L.assertFailedUsizeUsize.idx needF) : specT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [64] with [hL] using [hal', hhe, hcp, hmu, hsq, haf]
  all_goals
    have hhe' := hpre_10.heapEnd_le
    have hge := hpre_10.next_ge
    have hlay := env.layout
    have h16 : 16 * (regs .x11).toNat ≤ 0xc0000000 := by
      rcases hpre_6 with h | ⟨-, h⟩
      · omega
      · unfold InWin at h; omega
    have hshT : (regs .x11 <<< 4).toNat = 16 * (regs .x11).toNat := by
      rw [shl4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hC : Ctx env top regs m := ⟨by omega, hpre_9, hpre_10, hpre_5, by omega, by rw [hc_1]; exact hpre_7, hpre_8⟩
  · -- `r` empty
    refine head env p i L hp hL hnM hnS hmu hsq hk hpre_3 hC _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_7 =>
      rcases Nat.eq_zero_or_pos (regs .x15).toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hc
      · exact h0
    case refine_11 => exact .inl (by rw [hc_2]; rfl)
    all_goals rv_closeT
  all_goals
    have hn0 : (regs .x11).toNat ≠ 0 := by
      first
        | exact fun h => hc_2 (BitVec.eq_of_toNat_eq h)
        | exact fun h => hc (BitVec.eq_of_toNat_eq h)
    obtain ⟨hlv, hwn⟩ := hpre_6.resolve_left hn0
    have hrl := hwn.lt
    unfold Env.Live at hlv
  · rw [hshT]; omega
  · rw [hshT]; omega
  · intro _ b h1 h2
    simp only [InRange, hshT] at h1 h2
    omega
  · have hn2 := hret2_14.2.1
    rw [hshT]
    refine .inr ⟨.inl ⟨by omega, by omega⟩, .inl (by omega), hwn.inWindow hpre_10, .inl (by unfold InWin at hwn; omega)⟩
  · -- `r` copied
    refine head env p i L hp hL hnM hnS hmu hsq hk hpre_3 hC _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_7 =>
      rcases Nat.eq_zero_or_pos (regs .x15).toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hc
      · exact h0
    case refine_11 =>
      have := hret4_14.1
      exact .inr ⟨hret2_16, by omega, hret2_17⟩
    all_goals rv_closeT

end Rv64mc.Proof.Whir.RingWeightT

/-- info: 'Rv64mc.Proof.Whir.RingWeightT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.RingWeightT.total
