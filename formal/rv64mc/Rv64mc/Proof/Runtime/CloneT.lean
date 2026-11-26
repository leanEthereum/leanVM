/-
  Rv64mc.Proof.Runtime.CloneT

  `<Vec<T> as Clone>::clone` is total for `T` of 8 bytes (`usize`) and 16 bytes (`E`): called with the result's
  slot (`a0`) and the source's buffer and length (`a1`, `a2`), it checks that `len * size` fits an `isize` (else
  `handle_error`), allocates the new buffer (`alloc`, none when there are no bytes), writes the header and copies the
  bytes (`memcpy`). Its result is a vector's (`VecReprT.VecT`) of the source's length, its buffer fresh; the run ends
  with the guest's abort (`AbortStop`) where `alloc` or `handle_error` does. The precondition: the result's slot
  `Spec/Runtime/Vec`'s `SretPre` (a caller's object), in a window and 8-byte aligned; the source a vector's buffer
  holding `len` elements (`BufT` with the length for the capacity). It does not state the bytes copied.

  The two templates differ only in the shifts by `T`'s size, so both proofs are one script over the shift
  (`clone_close`).

  ## Main definitions

  * `ClonePreT`, `ClonePostT`, `CloneSpecT`

  ## Main results

  * `usize_total`, `e_total`
-/

import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.FinishGrow
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.VecReprT
import Rv64mc.Spec.Runtime.Vec
import Rv64mc.Core.AbortStop
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecUsize.AsClone.Clone
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecE.AsClone.Clone
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Runtime.CloneT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)

/-- `clone`'s total precondition, for `T` of `size` bytes: the result's slot a caller's, in a window and 8-byte
    aligned; the source `len` elements of a vector's buffer. -/
def ClonePreT (env : Env) (size : Nat) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) Layouts.Vec.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    BufT env m (regs .x12) (regs .x11) size

/-- `clone`'s total postcondition: the result a vector's of the source's length, its buffer fresh unless empty. -/
def ClonePostT (env : Env) (size : Nat) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) size ∧ vecLen m' (regs .x10) = regs .x12 ∧
    ((regs .x12).toNat = 0 ∨ env.Fresh m m' (vecPtr m' (regs .x10)) ((regs .x12).toNat * size))

/-- **The total contract of `<Vec<T> as Clone>::clone`**, `T` of `size` bytes. -/
def CloneSpecT (env : Env) (size : Nat) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (ClonePreT env size) (ClonePostT env size) SretVecOut AbortStop

/-- The size check's two tests passed: `x << s` exact and at most `c`. -/
theorem shl_ok {x c : Word} {s : Nat} (hs : s < 64)
    (h : (BinOp.ult.eval 0#64 (x >>> (64 - s)) ||| BinOp.ult.eval c (x <<< s)) = 0#64) :
    (x <<< s).toNat = x.toNat * 2 ^ s ∧ x.toNat * 2 ^ s ≤ c.toNat := by
  obtain ⟨h1, h2⟩ := FinishGrow.ult_or_zero h
  rw [BitVec.toNat_ushiftRight, show (0#64 : Word).toNat = 0 from rfl, Nat.le_zero, Nat.shiftRight_eq_div_pow,
    Nat.div_eq_zero_iff] at h1
  have hlt : x.toNat * 2 ^ s < 2 ^ 64 := by
    rcases h1 with h1 | h1
    · exact absurd h1 (Nat.two_pow_pos _).ne'
    · calc x.toNat * 2 ^ s < 2 ^ (64 - s) * 2 ^ s := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
        _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  have he : (x <<< s).toNat = x.toNat * 2 ^ s := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt]
  exact ⟨he, he ▸ h2⟩

/-- A doubleword wholly below an aligned destination, or at or after its end, is not one it may write. -/
theorem not_dwordsOf {dst a : Word} {n : Nat} (hd : dst.toNat % 8 = 0)
    (h : a.toNat + 8 ≤ dst.toNat ∨ dst.toNat + n ≤ a.toNat) : ¬ DwordsOf dst n a := by
  unfold DwordsOf InRange
  rw [toNat_alignToDword]
  omega


set_option hygiene false in
/-- What is left after `rv_autoT` of either template, for `T` of `2 ^ s` bytes. -/
local macro "clone_close " s:num : tactic => `(tactic| (
    all_goals try simp only [rvCapAt, rvPtrAt, vecLen, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr,
      Layouts.Vec.len] at *
    all_goals try rv_closeT
    all_goals
      obtain ⟨hsh, hle⟩ := shl_ok (s := $s) (by decide) hc_1
      simp only [show (9223372036854775800#64 : Word).toNat = 9223372036854775800 from rfl, Nat.reducePow] at hsh hle
      have hl := env.layout
      have hEnd := hpre_12.heapEnd_le
      have ho : (regs .x10).toNat + 24 < 2 ^ 64 := hpre_7
    -- `len * size = 0` with `len ≠ 0`: not reached, `len` is below `2 ^ 61`
    all_goals try
      have h0 : (regs .x12 <<< $s).toNat = 0 := by rw [hc_2]; rfl
      exact absurd (BitVec.eq_of_toNat_eq (by rw [show (0#64 : Word).toNat = 0 from rfl]; omega)) hc
    -- the copy's source: the old buffer, below `NEXT`
    all_goals
      have hn0 : (regs .x12).toNat ≠ 0 := by
        intro h
        have h3 : regs .x12 <<< $s = 0#64 := BitVec.eq_of_toNat_eq (by rw [hsh, h]; rfl)
        first | exact hc_2 h3 | exact hc h3
    -- `len = 0` with `len * size ≠ 0`: not reached
    all_goals try exact absurd (congrArg BitVec.toNat hc) hn0
    all_goals
      obtain ⟨hq1, hq2, hq3⟩ := hpre_10.resolve_left hn0
      unfold Env.Live at hq2
    · omega
    · omega
    · intro _ b h1 h2
      unfold InRange at h1 h2
      omega
    · have hn2 := hret2_14.2.1
      rw [hsh]
      exact .inr ⟨.inl ⟨by omega, by omega⟩, by unfold OffStack; omega, inWindow_iff.2 (.inl ⟨by omega, by omega⟩),
        by unfold OffStack; omega⟩
    -- after the copy: the header's words, in the caller's object, kept by `memcpy`
    all_goals
      have hW : InWin env (regs .x10) 24 := hpre_8
      have hnP : env.next (((m2.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64) (r2 .x10)).setMem
          (regs .x10 + 16#64) 0#64) = env.next m2 := by
        unfold Env.next
        rw [MachineState.getMem_setMem_ne (Ne.symm (hW.ne_next_add (o := 16) (by decide))),
          MachineState.getMem_setMem_ne (Ne.symm (hW.ne_next_add (o := 8) (by decide))),
          MachineState.getMem_setMem_ne (Ne.symm (by simpa using hW.ne_next_add (o := 0) (by decide)))]
      simp only [CopyOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, hnP] at keep3_2
      have h8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
      have h48 : (top + 0xffffffffffffffd0#64).toNat = top.toNat - 48 := by
        rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
      have hown : (regs .x10).toNat + 24 ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x10).toNat := by
        rw [← hpre_2]; exact hpre_6
      have hn2 := hret2_14.2.1
      have hc3 : m3.getMem (regs .x10) = regs .x12 := by
        rw [keep3_2 _ (by omega) (not_dwordsOf hret2_17 (by omega)),
          MachineState.getMem_setMem_ne (FinishGrow.ne16 ho).symm,
          MachineState.getMem_setMem_ne (FinishGrow.ne8 ho).symm,
          MachineState.getMem_setMem_eq]
      have hp3 : m3.getMem (regs .x10 + 8#64) = r2 .x10 := by
        rw [keep3_2 _ (by omega) (not_dwordsOf hret2_17 (by omega)),
          MachineState.getMem_setMem_ne (FinishGrow.ne816 ho), MachineState.getMem_setMem_eq]
      have hnF : env.next (m3.setMem (regs .x10 + 16#64) (regs .x12)) = env.next m3 := by
        unfold Env.next
        rw [MachineState.getMem_setMem_ne (Ne.symm (hW.ne_next_add (o := 16) (by decide)))]
      have hn3 := hret3_14.1
      rw [hnP] at hn3
      rw [hsh] at hret2_18
    · rw [hc3, hp3]
      refine .inr ⟨by omega, ?_, hret2_17⟩
      unfold Env.Live
      rw [hnF]
      omega
    · rw [hc3]; omega
    · rw [hc3]
    · exact .inr ⟨by rw [hp3]; omega, by rw [hp3, hnF]; omega⟩))

set_option rv_sym.heap true in
/-- **`<Vec<usize> as Clone>::clone` is total**, with 48 bytes of stack beyond its callees'. -/
theorem usize_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Alloc.Vec.VecUsize.AsClone.Clone.Link)
    (hp : p[i]? = some (Gen.Alloc.Vec.VecUsize.AsClone.Clone.tmpl L)) (hL : L.WF p)
    {need needA needM needH : Nat} (hnA : 48 + needA ≤ need) (hnM : 48 + needM ≤ need) (hnH : 48 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hcp : MemcpySpecT env p L.memcpy.idx needM)
    (hhe : Aborts env p L.handleError.idx needH) : CloneSpecT env 8 p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal', hcp, hhe]
  clone_close 3

set_option rv_sym.heap true in
/-- **`<Vec<E> as Clone>::clone` is total**, with 48 bytes of stack beyond its callees'. -/
theorem e_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Alloc.Vec.VecE.AsClone.Clone.Link)
    (hp : p[i]? = some (Gen.Alloc.Vec.VecE.AsClone.Clone.tmpl L)) (hL : L.WF p)
    {need needA needM needH : Nat} (hnA : 48 + needA ≤ need) (hnM : 48 + needM ≤ need) (hnH : 48 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hcp : MemcpySpecT env p L.memcpy.idx needM)
    (hhe : Aborts env p L.handleError.idx needH) : CloneSpecT env 16 p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal', hcp, hhe]
  clone_close 4

end Rv64mc.Proof.Runtime.CloneT

/-- info: 'Rv64mc.Proof.Runtime.CloneT.usize_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.CloneT.usize_total

/-- info: 'Rv64mc.Proof.Runtime.CloneT.e_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.CloneT.e_total
