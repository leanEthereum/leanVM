/-
  Rv64mc.Proof.Field.ESumNovelT

  `E::sum` over `values.iter().zip(basis).map(|(v, b)| v.base_mul(b))` (`novel_eval`'s sum, index 18) is total
  (`SumSafeT`): passed the zip by reference (the `E` slice's pointer and end, the `Vec<K>`'s `IntoIter` with its cursor
  at `+ 24` and end at `+ 40`, the zip's index at `+ 48`), it returns, writing nothing of its caller's. The
  precondition (`SumPreT`): the zip's seven words in a window, 8-byte aligned and the caller's (`Owned` at the stack
  pointer), its index `0` (as `novel_eval` builds it), and each side a slice (`SliceW`): its end not below its
  pointer and, unless empty, its bytes in a window and 8-byte aligned. The sum is not stated: no caller's safety reads
  it. The loop is `Total.loop` with the pairs left (the shorter side's length) as the measure; `base_mul` is stepped
  through its total contract with its postcondition dropped (`KInvT.dropPost`), and the nine saved registers' slots
  are `SavedT.MemOk`.

  ## Main definitions

  * `SliceW`, `SumPreT`, `SumSafeT`, `Mem`, `LInv`

  ## Main results

  * `SliceW.win`, `call_back`, `loop_ok`, `total`
-/

import Rv64mc.Proof.Field.ESumWinT
import Rv64mc.Proof.Field.KInvT
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Gen.Tmpl.Verifier.Field.E.SumMapZipIterEIntoIterKNovelEvalClosure0

namespace Rv64mc.Proof.Field.ESumNovelT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Field.KInvT (dropPost)
open Rv64mc.Gen.Verifier.Field.E.SumMapZipIterEIntoIterKNovelEvalClosure0 (Link tmpl)

/-- A slice from `b` to `e`: `e` not below `b`, and unless empty its bytes in a window and `b` 8-byte aligned. -/
def SliceW (env : Env) (b e : Word) : Prop :=
  b.toNat ≤ e.toNat ∧ (e = b ∨ InWin env b (e.toNat - b.toNat) ∧ b.toNat % 8 = 0)

/-- The total precondition: the zip at `x10` (`56` bytes) 8-byte aligned, in a window and the caller's, its index
    `0`, the `E`s from `+ 0` to `+ 8` and the `K`s from `+ 24` to `+ 40` slices. -/
def SumPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧ InWin env (regs .x10) 56 ∧ env.Owned m (regs .x2) (regs .x10) 56 ∧
    m.getMem (regs .x10 + 48#64) = 0#64 ∧ SliceW env (m.getMem (regs .x10)) (m.getMem (regs .x10 + 8#64)) ∧
    SliceW env (m.getMem (regs .x10 + 24#64)) (m.getMem (regs .x10 + 40#64))

/-- **The total contract**: it returns, writing nothing of its caller's. It does not state the sum. -/
def SumSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (SumPreT env) (fun _ _ _ _ => True)

/-- `n` elements of `2 ^ s` bytes, at least one, within a slice: in a window, aligned. -/
theorem SliceW.win {env : Env} {b e : Word} {n s : Nat} (h : SliceW env b e) (hn : 1 ≤ n)
    (hle : 2 ^ s * n ≤ e.toNat - b.toNat) (hs : 1 ≤ 2 ^ s) : InWin env b (2 ^ s * n) ∧ b.toNat % 8 = 0 := by
  rcases h.2 with he | ⟨hw, ha⟩
  · subst he; have : 2 ^ s * n ≥ 1 := Nat.le_trans hs (Nat.le_mul_of_pos_right _ hn); omega
  · exact ⟨hw.sub le_rfl (by omega), ha⟩

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

/-- **`Mem` across `base_mul`**, from the stack pointer `top - 80`. -/
theorem call_back {env : Env} {ret top : Word} {regs : Reg → Word} {m M X : MachineState}
    (hf : env.Frame (top + 18446744073709551536#64) (fun _ => False) M X)
    (hk : ∀ a : Word, top + 18446744073709551536#64 ≤ a → X.getMem a = M.getMem a) (hc : X.code = M.code)
    (hs : env.Static X) (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hM : Mem env ret top regs m M) :
    Mem env ret top regs m X :=
  (hM.call_below slots (by omega) hlim (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) hf hk hc hs).1

/-- The loop's head (instruction 29), `k` pairs of `n` left: the stack pointer, `s8` to `s11` as at the entry, the
    `K`s' cursor `x22` and the `E`s' `x23` (`8` past the next element), `Mem`. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (qa qk : Word) (n k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧
    R .x27 = regs .x27 ∧ (R .x21).toNat = k ∧ 1 ≤ k ∧ k ≤ n ∧ (R .x22).toNat = qk.toNat + 8 * (n - k) ∧
    (R .x23).toNat = qa.toNat + 16 * (n - k) + 8 ∧ Mem env ret top regs m M

/-- The elements of `2 ^ s` bytes from `b` to `e`, as a number. -/
theorem shr_sub {b e : Word} {s : Nat} (h : b.toNat ≤ e.toNat) :
    ((e - b) >>> s).toNat = (e.toNat - b.toNat) / 2 ^ s := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]; congr 1; omega

set_option rv_sym.heap true in
/-- **The loop**, from its head: the next `K` and `E` read, two `base_mul`s, then back to the head (one pair fewer)
    or the return. -/
theorem loop_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM : Nat} (hnM : 80 + needM ≤ need) (hbm : BaseMulT.specT env p L.baseMul.idx needM)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {qa qk : Word} {n : Nat} (hwa : InWin env qa (16 * n)) (haa : qa.toNat % 8 = 0) (hwk : InWin env qk (8 * n))
    (hak : qk.toNat % 8 = 0) :
    ∀ k R M, LInv env ret top regs m qa qk n k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 58, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m qa qk n) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, -, -, -, h21, hk1, hkn, h22, h23, hM⟩ := id hI
  have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
  have hla := hwa.lt
  have hlk := hwk.lt
  have hdk := hwk.dword (x := R .x22) (o := 8 * (n - k)) hW hak h22 (by omega) (by omega)
  have hea : (R .x23 + 18446744073709551608#64).toNat = qa.toNat + 16 * (n - k) := by
    rw [BitVec.toNat_add, h23, BitVec.toNat_ofNat]; omega
  have hd0 := hwa.dword hW haa hea (by omega) (by omega)
  have hd8 := hwa.dword (x := R .x23) (o := 16 * (n - k) + 8) hW haa (by omega) (by omega) (by omega)
  rv_introT hI
  rv_symT hp stop [58] with [hL, hlim] using [dropPost hbm]
  all_goals
    have hM1 := call_back hret1_14 keep1_1 hret1_16 hret1_15 hlim hM
    have hM2 := call_back hret2_14 keep2_1 hret2_16 hret2_15 hlim hM1
  -- back to the head, one pair fewer
  · have hk2 : 2 ≤ k := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega))
    refine ih (k - 1) _ _ (by omega) ⟨rfl, rfl, rfl, rfl, rfl, ?_, by omega, by omega, ?_, ?_, hM2⟩
    all_goals simp only [Tactic.rf]
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
  -- the return
  · obtain ⟨-, -, -, s1, s2, s3, s4, s5, s6, s7, s8, s9, -⟩ := hM
    refine ⟨?_, hM2.1, hM2.2.2.1, trivial⟩
    simp only [AbiRegs, Tactic.rf]
    exact ⟨trivial, s2, s3, s4, s5, s6, s7, s8, s9, trivial, trivial, trivial, trivial⟩

set_option rv_sym.heap true in
/-- **`novel_eval`'s sum is total**: the shorter side's length, then nothing more for none, or the loop from the
    zip's first pair. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM : Nat} (hnM : 80 + needM ≤ need) (hbm : BaseMulT.specT env p L.baseMul.idx needM) :
    SumSafeT env p i need := by
  rv_autoT hp stop [58] with [hL]
  all_goals
    have hlay := env.layout
    have hsa : SliceW env (m.getMem (regs .x10)) (m.getMem (regs .x10 + 8#64)) := ⟨hpre_11, hpre_12⟩
    have hsk : SliceW env (m.getMem (regs .x10 + 24#64)) (m.getMem (regs .x10 + 40#64)) := ⟨hpre_13, hpre_14⟩
    have ea := shr_sub (s := 4) hpre_11
    have ek := shr_sub (s := 3) hpre_13
    simp only [hpre_10, BitVec.zero_shiftLeft, BitVec.zero_add, BitVec.add_zero]
  -- the `E`s the shorter side
  · have h0 : ((m.getMem (regs .x10 + 8#64) - m.getMem (regs .x10)) >>> 4).toNat ≠ 0 :=
      fun h => hc (BitVec.eq_of_toNat_eq h)
    have hlt : ((m.getMem (regs .x10 + 8#64) - m.getMem (regs .x10)) >>> 4).toNat <
      ((m.getMem (regs .x10 + 40#64) - m.getMem (regs .x10 + 24#64)) >>> 3).toNat := hc_1
    obtain ⟨hwa, haa⟩ := hsa.win (s := 4) (n := ((m.getMem (regs .x10 + 8#64) - m.getMem (regs .x10)) >>> 4).toNat)
      (by omega) (by omega) (by decide)
    obtain ⟨hwk, hak⟩ := hsk.win (s := 3) (n := ((m.getMem (regs .x10 + 8#64) - m.getMem (regs .x10)) >>> 4).toNat)
      (by omega) (by omega) (by decide)
    have := hwa.lt
    refine loop_ok env p i L hp hL hnM hbm hk hpre_3 hpre_15 hpre_16 hwa haa hwk hak _ _ _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp only [Tactic.rf]; omega, le_rfl, by simp only [Tactic.rf]; omega,
        by simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]; omega, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> rv_closeT
  -- the `K`s the shorter side
  · have h0 : ((m.getMem (regs .x10 + 40#64) - m.getMem (regs .x10 + 24#64)) >>> 3).toNat ≠ 0 :=
      fun h => hc (BitVec.eq_of_toNat_eq h)
    have hle : ((m.getMem (regs .x10 + 40#64) - m.getMem (regs .x10 + 24#64)) >>> 3).toNat ≤
      ((m.getMem (regs .x10 + 8#64) - m.getMem (regs .x10)) >>> 4).toNat := hc_1
    obtain ⟨hwa, haa⟩ := hsa.win (s := 4)
      (n := ((m.getMem (regs .x10 + 40#64) - m.getMem (regs .x10 + 24#64)) >>> 3).toNat) (by omega) (by omega)
      (by decide)
    obtain ⟨hwk, hak⟩ := hsk.win (s := 3)
      (n := ((m.getMem (regs .x10 + 40#64) - m.getMem (regs .x10 + 24#64)) >>> 3).toNat) (by omega) (by omega)
      (by decide)
    have := hwa.lt
    refine loop_ok env p i L hp hL hnM hbm hk hpre_3 hpre_15 hpre_16 hwa haa hwk hak _ _ _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp only [Tactic.rf]; omega, le_rfl, by simp only [Tactic.rf]; omega,
        by simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]; omega, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> rv_closeT

end Rv64mc.Proof.Field.ESumNovelT

/-- info: 'Rv64mc.Proof.Field.ESumNovelT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ESumNovelT.total
