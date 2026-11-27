/-
  Rv64mc.Proof.Field.ESumBlockT

  `E::sum` over `block.iter().map(|(word, at)| E::sum(at.iter().map(|&i| low_weights[i as usize])) * *word)`
  (`Bytecode::evaluate`'s block value, index 24) is total (`SumSafeT`): passed the iterator by reference (the
  block's pointer and end, the closure's reference to `low_weights`' header), it returns, writing nothing of its
  caller's, or ends the run with `a0 = 2` where the inner sum does (`ESumU16T`, an index past the weights). The
  precondition (`SumPreT`): the iterator's three words 8-byte aligned, in a window and the caller's (`Owned`); the
  block whole `32`-byte elements (a `K`, then a `Vec<u16>`: capacity, pointer, length), unless none in a window,
  8-byte aligned and the caller's; each element's `u16`s 2-byte aligned and, unless none, in a window (`U16sW`); the
  weights' header 8-byte aligned, in a window and the caller's, the weights a `TabW`. The sum is not stated: no
  caller's safety reads it.

  The loop is `Total.loop` with the elements left as the measure. Each pass stores the inner sum's iterator (the
  `u16`s' pointer and end, the weights' reference) in the frame below the saved registers (`MemOk.slot`), calls
  the inner sum (`ESumU16T`, whose precondition the stored words and `kept` give) and `base_mul` twice (its
  postcondition dropped). The nine saved registers' slots are `SavedT.MemOk`.

  ## Main definitions

  * `U16sW`, `SumPreT`, `SumSafeT`, `Mem`, `LInv`

  ## Main results

  * `call_back`, `loop_ok`, `total`
-/

import Rv64mc.Proof.Field.ESumFormT
import Rv64mc.Proof.Field.ESumU16T
import Rv64mc.Proof.Field.BaseMulT
import Rv64mc.Gen.Tmpl.Verifier.Field.E.SumMapIterTKVecU16EEvaluH09540813
import Mathlib.Tactic.IntervalCases

namespace Rv64mc.Proof.Field.ESumBlockT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Field.ESumWinT (TabW)
open Rv64mc.Proof.Field.KInvT (dropPost)
open Rv64mc.Proof.Field.ESumFormT (kept)
open Rv64mc.Gen.Verifier.Field.E.SumMapIterTKVecU16EEvaluH09540813 (Link tmpl)

/-- The `n` elements (`32` bytes: a `K`, then the `Vec<u16>`'s capacity, pointer and length) from `q`: each one's
    `u16`s 2-byte aligned and, unless none, in a window. -/
def U16sW (env : Env) (m : MachineState) (q : Word) (n : Nat) : Prop :=
  ∀ j, j < n → (m.getMem (q + BitVec.ofNat 64 (32 * j) + 16#64)).toNat % 2 = 0 ∧
    ((m.getMem (q + BitVec.ofNat 64 (32 * j) + 24#64)).toNat = 0 ∨
      InWin env (m.getMem (q + BitVec.ofNat 64 (32 * j) + 16#64))
        (2 * (m.getMem (q + BitVec.ofNat 64 (32 * j) + 24#64)).toNat))

/-- The total precondition: the iterator at `x10` (`24` bytes) 8-byte aligned, in a window and the caller's; the
    block from `+ 0` to `+ 8` whole `32`-byte elements, unless none in a window, 8-byte aligned and the caller's,
    each a `U16sW`; the weights' header (at `+ 16`) 8-byte aligned, in a window and the caller's, the weights a
    `TabW`. -/
def SumPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧ InWin env (regs .x10) 24 ∧ env.Owned m (regs .x2) (regs .x10) 24 ∧
    (m.getMem (regs .x10)).toNat ≤ (m.getMem (regs .x10 + 8#64)).toNat ∧
    ((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) % 32 = 0 ∧
    (m.getMem (regs .x10 + 8#64) = m.getMem (regs .x10) ∨
      InWin env (m.getMem (regs .x10)) ((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) ∧
      (m.getMem (regs .x10)).toNat % 8 = 0 ∧
      env.Owned m (regs .x2) (m.getMem (regs .x10))
        ((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat)) ∧
    U16sW env m (m.getMem (regs .x10))
      (((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) / 32) ∧
    (m.getMem (regs .x10 + 16#64)).toNat % 8 = 0 ∧ InWin env (m.getMem (regs .x10 + 16#64)) 24 ∧
    env.Owned m (regs .x2) (m.getMem (regs .x10 + 16#64)) 24 ∧
    TabW env (m.getMem (m.getMem (regs .x10 + 16#64) + 8#64)) (m.getMem (m.getMem (regs .x10 + 16#64) + 16#64))

/-- **The total contract**: it returns, writing nothing of its caller's, or ends the run with `a0 = 2`. It does not
    state the sum. -/
def SumSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (SumPreT env) (fun _ _ _ _ => True) (Stop := AbortStop)

/-- What the loop keeps of memory: `SavedT.MemOk` with the nine saved registers' slots, from `top - 8` (the return
    address) down to `top - 72` (`s7`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (fun _ => False)
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64]
    [ret, regs .x8, regs .x9, regs .x18, regs .x19, regs .x20, regs .x21, regs .x22, regs .x23] m M

/-- The saved slots lie in the `72` bytes below `top`. -/
theorem slots : SlotsIn 72
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64] :=
  slots_le

/-- **`Mem` across a callee** writing nothing of the caller's, from the stack pointer `top - 96`. -/
theorem call_back {env : Env} {ret top : Word} {regs : Reg → Word} {m M X : MachineState}
    (hf : env.Frame (top + 18446744073709551520#64) (fun _ => False) M X)
    (hk : ∀ a : Word, top + 18446744073709551520#64 ≤ a → X.getMem a = M.getMem a) (hc : X.code = M.code)
    (hs : env.Static X) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hM : Mem env ret top regs m M) :
    Mem env ret top regs m X :=
  (hM.call_below slots (by omega) hlim (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) hf hk hc hs).1

/-- **`Mem` across the three stores** of the inner sum's iterator at `top - 96`, `top - 88`, `top - 80`. -/
theorem iter_ok {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hM : Mem env ret top regs m M) (a b c : Word) :
    Mem env ret top regs m (((M.setMem (top + 18446744073709551520#64) a).setMem (top + 18446744073709551528#64)
      b).setMem (top + 18446744073709551536#64) c) := by
  have e0 : (top + 18446744073709551520#64).toNat = top.toNat - 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e1 : (top + 18446744073709551528#64).toNat = top.toNat - 88 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h1 := (hM.slot (F := 96) (a := top + 18446744073709551520#64) slots hlim (by omega) (by omega) (v := a)).1
  have h2 := (h1.slot (F := 96) (a := top + 18446744073709551528#64) slots hlim (by omega) (by omega) (v := b)).1
  exact (h2.slot (F := 96) (a := top + 18446744073709551536#64) slots hlim (by omega) (by omega) (v := c)).1

/-- A word apart from the inner sum's iterator, read through its three stores. -/
theorem rd3 {M : MachineState} {top a x y z : Word} (htop : 96 ≤ top.toNat)
    (ha : a.toNat + 8 ≤ top.toNat - 96 ∨ top.toNat - 72 ≤ a.toNat) :
    (((M.setMem (top + 18446744073709551520#64) x).setMem (top + 18446744073709551528#64) y).setMem
      (top + 18446744073709551536#64) z).getMem a = M.getMem a := by
  have e0 : (top + 18446744073709551520#64).toNat = top.toNat - 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e1 : (top + 18446744073709551528#64).toNat = top.toNat - 88 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega)),
    MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega)),
    MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))]

/-- The weights' reference, read back from the inner sum's iterator. -/
theorem rd3_ref {M : MachineState} {top x y z : Word} :
    (((M.setMem (top + 18446744073709551520#64) x).setMem (top + 18446744073709551528#64) y).setMem
      (top + 18446744073709551536#64) z).getMem (top + 18446744073709551520#64 + 16#64) = z := by
  rw [BitVec.add_assoc]; exact MachineState.getMem_setMem_eq

/-- A multiple of `32` is its own multiple of `32` rounded down (the code's `& !31`). -/
theorem and_mask32 (x : Word) (h : x.toNat % 32 = 0) : x &&& 0xffffffffffffffe0#64 = x := by
  have : (0xffffffffffffffe0#64 : Word) = BitVec.allOnes 64 <<< 5 := by decide
  rw [this]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
  by_cases h5 : i < 5
  · have : x.getLsbD i = false := by
      rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
      simp only [decide_eq_false_iff_not]
      interval_cases i <;> omega
    simp [h5, this]
  · simp [h5, hi]; omega

/-- The loop's head (instruction 20), `d` of the `n` elements from `q` left: the stack pointer, `s8` to `s11` as at
    the entry, the weights' reference `x21`, the element's cursor `x22` (`24` past it) and its end `x23`, `Mem`. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q h : Word) (n d : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551520#64 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧
    R .x27 = regs .x27 ∧ R .x21 = h ∧ (R .x22).toNat = q.toNat + 24 + 32 * (n - d) ∧
    (R .x23).toNat = q.toNat + 24 + 32 * n ∧ 1 ≤ d ∧ d ≤ n ∧ Mem env ret top regs m M

/-- **The element's `u16`s** (element `n - d`, its last word at `x`), read through `Mem`: its pointer and length the
    entry's, their end as a number, and `U16sW`'s facts. -/
theorem elem_ok {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {q x : Word} {n d : Nat}
    (hM : Mem env ret top regs m M) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hwq : InWin env q (32 * n))
    (hoq : env.Owned m top q (32 * n)) (hus : U16sW env m q n) (hd1 : 1 ≤ d) (hdn : d ≤ n)
    (hx : x.toNat = q.toNat + 24 + 32 * (n - d)) :
    M.getMem (x + 18446744073709551608#64) = m.getMem (q + BitVec.ofNat 64 (32 * (n - d)) + 16#64) ∧
      M.getMem x = m.getMem (q + BitVec.ofNat 64 (32 * (n - d)) + 24#64) ∧
      (m.getMem (q + BitVec.ofNat 64 (32 * (n - d)) + 16#64) +
        m.getMem (q + BitVec.ofNat 64 (32 * (n - d)) + 24#64) <<< 1).toNat =
        (m.getMem (q + BitVec.ofNat 64 (32 * (n - d)) + 16#64)).toNat +
          2 * (m.getMem (q + BitVec.ofNat 64 (32 * (n - d)) + 24#64)).toNat ∧
      (m.getMem (q + BitVec.ofNat 64 (32 * (n - d)) + 16#64)).toNat % 2 = 0 ∧
      ((m.getMem (q + BitVec.ofNat 64 (32 * (n - d)) + 24#64)).toNat = 0 ∨
        InWin env (m.getMem (q + BitVec.ofNat 64 (32 * (n - d)) + 16#64))
          (2 * (m.getMem (q + BitVec.ofNat 64 (32 * (n - d)) + 24#64)).toNat)) := by
  have hwl := hwq.lt
  have hlay := env.layout
  have ej : (q + BitVec.ofNat 64 (32 * (n - d))).toNat = q.toNat + 32 * (n - d) := toNat_add_ofNat (by omega)
  have a16 : x + 18446744073709551608#64 = q + BitVec.ofNat 64 (32 * (n - d)) + 16#64 :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, BitVec.toNat_add, ej, hx]; simp only [BitVec.toNat_ofNat]; omega)
  have a24 : x = q + BitVec.ofNat 64 (32 * (n - d)) + 24#64 :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, ej, hx]; simp only [BitVec.toNat_ofNat]; omega)
  obtain ⟨hp2, hlen⟩ := hus (n - d) (by omega)
  refine ⟨?_, ?_, ?_, hp2, hlen⟩
  · rw [a16]; exact kept hM (by omega) (by rw [toNat_add_ofNat (by omega), ej]; rcases hoq.1 with h | h <;> omega)
  · rw [a24]; exact kept hM (by omega) (by rw [toNat_add_ofNat (by omega), ej]; rcases hoq.1 with h | h <;> omega)
  · rcases hlen with h0 | hw
    · have : m.getMem (q + BitVec.ofNat 64 (32 * (n - d)) + 24#64) = 0#64 := BitVec.eq_of_toNat_eq h0
      rw [this]; simp
    · have := hw.lt
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

set_option rv_sym.heap true in
/-- **The loop**, from its head: the element's `u16`s' pointer and end, the inner sum over them, the element's
    word times its two coordinates (`base_mul`), then back to the head (one element fewer) or the return. -/
theorem loop_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS needM : Nat} (hnS : 96 + needS ≤ need) (hnM : 96 + needM ≤ need)
    (hsum : ESumU16T.SumSafeT env p L.sumMapIterU16EvaluateCloH33077ef9.idx needS)
    (hbm : BaseMulT.specT env p L.baseMul.idx needM)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {q h : Word} {n : Nat} (hwq : InWin env q (32 * n)) (haq : q.toNat % 8 = 0) (hoq : env.Owned m top q (32 * n))
    (hus : U16sW env m q n) (hah : h.toNat % 8 = 0) (hwh : InWin env h 24) (hoh : env.Owned m top h 24)
    (htab : TabW env (m.getMem (h + 8#64)) (m.getMem (h + 16#64))) :
    ∀ d R M, LInv env ret top regs m q h n d R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 40, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m q h n) fun d R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, -, -, -, h21, h22, h23, hd1, hdn, hM⟩ := id hI
  have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
  have hwl := hwq.lt
  rv_introT hI
  rv_symT hp stop [40] with [hL, hlim] using [hsum, dropPost hbm, dropPost hbm]
  all_goals
    obtain ⟨k16, k24, hE, hp2, hlen⟩ := elem_ok hM hlim hwq hoq hus hd1 hdn h22
    have h8 := kept hM (by omega) (a := h + 8#64)
      (by have := hwh.lt; rw [toNat_add_ofNat (by omega)]; rcases hoh.1 with h | h <;> omega)
    have h16 := kept hM (by omega) (a := h + 16#64)
      (by have := hwh.lt; rw [toNat_add_ofNat (by omega)]; rcases hoh.1 with h | h <;> omega)
  -- the inner sum's precondition
  · rw [k16, k24, hE]; omega
  · rw [k16, k24, hE]; omega
  · rw [k16]; exact hp2
  · rw [k16, k24]
    rcases hlen with h0 | hw
    · exact .inl (by rw [BitVec.eq_of_toNat_eq (h0.trans (by rfl) : _ = (0#64).toNat)]; simp)
    · exact .inr (by rw [hE]; simpa using hw)
  · have hph : h.toNat + 24 ≤ top.toNat - 96 ∨ top.toNat - 72 ≤ h.toNat := by
      have := hM.1.1; have := hM.1.2.1
      rcases hoh.1 with hh | hh <;> omega
    have := hwh.lt
    rw [rd3_ref, rd3 (by omega) (by rw [toNat_add_ofNat (by omega)]; omega),
      rd3 (by omega) (by rw [toNat_add_ofNat (by omega)]; omega), h8, h16]
    exact htab
  all_goals
    clear k16 k24 hE hp2 hlen h8 h16
    have hM1 := call_back hret1_14 keep1_1 hret1_16 hret1_15 hlim (iter_ok hlim hM _ _ _)
    have hM2 := call_back hret2_14 keep2_1 hret2_16 hret2_15 hlim hM1
    have hM3 := call_back hret3_14 keep3_1 hret3_16 hret3_15 hlim hM2
  -- back to the head, one element fewer
  · have hd2 : 2 ≤ d := Nat.le_of_not_lt fun h' => hc (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_add, h22, h23]; simp only [BitVec.toNat_ofNat]; omega))
    refine ih (d - 1) _ _ (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, h23, by omega, by omega, hM3⟩
    simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]; omega
  -- the return
  · obtain ⟨-, -, -, s1, s2, s3, s4, s5, s6, s7, s8, s9, -⟩ := hM
    refine ⟨?_, hM3.1, hM3.2.2.1, trivial⟩
    simp only [AbiRegs, Tactic.rf]
    exact ⟨trivial, s2, s3, s4, s5, s6, s7, s8, s9, trivial, trivial, trivial, trivial⟩

set_option rv_sym.heap true in
/-- **`Bytecode::evaluate`'s block value is total**: none for an empty block, else the loop from its first
    element. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS needM : Nat} (hnS : 96 + needS ≤ need) (hnM : 96 + needM ≤ need)
    (hsum : ESumU16T.SumSafeT env p L.sumMapIterU16EvaluateCloH33077ef9.idx needS)
    (hbm : BaseMulT.specT env p L.baseMul.idx needM) :
    SumSafeT env p i need := by
  rv_autoT hp stop [40] with [hL]
  have hne : (m.getMem (regs .x10)).toNat ≠ (m.getMem (regs .x10 + 8#64)).toNat :=
    fun h => hc (BitVec.eq_of_toNat_eq h)
  have hsub : (m.getMem (regs .x10 + 8#64) - m.getMem (regs .x10)).toNat =
      (m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat := by
    rw [BitVec.toNat_sub]; omega
  have hmask := and_mask32 (m.getMem (regs .x10 + 8#64) - m.getMem (regs .x10)) (by rw [hsub]; exact hpre_11)
  obtain ⟨hwq, haq, hoq⟩ := hpre_12.resolve_left (Ne.symm hc)
  have e32 : (m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat =
      32 * (((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) / 32) := by omega
  have hwl := hwq.lt
  rw [e32] at hwq hoq
  rw [hpre_2] at hoq hpre_16
  refine loop_ok env p i L hp hL hnS hnM hsum hbm hk hstop hpre_3 hpre_19 hpre_20 hwq haq hoq hpre_13 hpre_14 hpre_15
    ⟨hpre_16, hpre_17⟩ hpre_18 (((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) / 32) _ _
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, by omega, le_rfl, ?_⟩
  · simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]; omega
  · have := hwq; unfold InWin at this
    have := hpre_20.heapEnd_le
    simp only [Tactic.rf]; rw [hmask, BitVec.toNat_add, toNat_add_ofNat (by omega), hsub]; omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> rv_closeT

end Rv64mc.Proof.Field.ESumBlockT

/-- info: 'Rv64mc.Proof.Field.ESumBlockT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ESumBlockT.total
