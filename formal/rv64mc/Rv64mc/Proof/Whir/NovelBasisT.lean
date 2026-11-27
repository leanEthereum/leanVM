/-
  Rv64mc.Proof.Whir.NovelBasisT

  `verifier::whir::novel_basis(what: &[K], count) -> Vec<K>` is total (`specT`): from a result's slot of `24` bytes
  owned, in a window, 8-byte aligned, and `what` (`a1`, `a2`) none or in a window and 8-byte aligned (`SliceK`), it
  returns with the slot a vector of `K`s (`VecT`) of `count` elements, its buffer allocated since the entry, writing
  at most the slot besides what it allocates (`SretOut`, the partial contract's), or the run ends with `a0 = 2` where
  `alloc` (through `panic_nounwind_fmt` or `handle_error`), `reserve` or the `assert!` (`panic_fmt`) does. Safety
  only: the partial contract's values (`Spec/Whir/Subspace.lean`'s `basisSpec`, `Model.novelBasisRust`) are owed. It
  has no partial proof (class C).

  The basis starts as `[1]` and doubles per value of `what` until it has `count` elements: each pass allocates the
  products' buffer of the basis's length `n` (`reserve(n)` on it finds the room), stores the `n` products
  (`base_mul`), `reserve`s `n` more in the basis (which may grow it into a block allocated after the products') and
  copies the products after its elements (`memcpy`, the two blocks apart). Cut at the outer loop's head (instruction
  34, `outer`, `Total.loop` with `what`'s values left as the measure), the products' loop head (59, `inner`, the
  products left), after the products (67, `app`) and at the exit (81, `fin_ok`).

  ## Main definitions

  * `SliceK`, `PreT`, `PostT`, `specT`, `Saved`, `MemOk`, `BV`, `FinInv`, `Base`, `OInv`, `Tmp`, `AInv`, `IInv`

  ## Main results

  * `entry_bv`, `after_tmp`, `prod_step`, `after_basis`, `copy_ok`, `fin_ok`, `inner`, `app`, `outer`, `total`
-/

import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.VecHdrT
import Rv64mc.Proof.Field.BaseMulT
import Rv64mc.Core.AbortStop
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Proof.Whir.VecWordT
import Rv64mc.Spec.Whir.Subspace
import Rv64mc.Gen.Tmpl.Verifier.Whir.NovelBasis

namespace Rv64mc.Proof.Whir.NovelBasisT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Whir
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Whir.VecWordT (vecT_stores shl3)
open Rv64mc.Gen.Verifier.Whir.NovelBasis (Link tmpl)

/-- `len` words at `ptr`: none, or in a window and 8-byte aligned. -/
def SliceK (env : Env) (ptr len : Word) : Prop :=
  len.toNat = 0 ∨ (InWin env ptr (8 * len.toNat) ∧ ptr.toNat % 8 = 0)

/-- The total precondition: the result's slot (`24` bytes) in a window, 8-byte aligned, owned; `what` `SliceK`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 24 ∧
    SliceK env (regs .x11) (regs .x12)

/-- The total postcondition: the slot a vector of `K`s of `count` elements, its buffer allocated since the entry unless
    it has no capacity. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 8 ∧ vecLen m' (regs .x10) = regs .x13 ∧
    (vecCap m' (regs .x10) = 0#64 ∨ (env.next m).toNat ≤ (vecPtr m' (regs .x10)).toNat)

/-- **The total contract of `novel_basis`**: `PreT` to `PostT`, writing at most the slot (`SretOut`, the partial
    contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (SretOut Layouts.Vec.byteSize) (Stop := AbortStop)

/-- The saved registers' eleven slots, from `top - 8` (the return address) down to `top - 88` (`s9`). -/
def Saved (ret top : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25

/-- What every part keeps of memory: the frame, the code, the static data, the saved registers' slots. -/
def MemOk (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  env.Frame top (SretOut Layouts.Vec.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧ Saved ret top regs M

/-- The basis's header at `top - 136` (capacity, pointer, length): its length at least `1` and at most its capacity,
    its buffer of fewer than `2^63` bytes, allocated since the entry, 8-byte aligned. -/
def BV (env : Env) (m : MachineState) (top : Word) (M : MachineState) : Prop :=
  1 ≤ (M.getMem (top + 18446744073709551496#64)).toNat ∧
    (M.getMem (top + 18446744073709551496#64)).toNat ≤ (M.getMem (top + 18446744073709551480#64)).toNat ∧
    (M.getMem (top + 18446744073709551480#64)).toNat * 8 < 2 ^ 63 ∧
    (env.next m).toNat ≤ (M.getMem (top + 18446744073709551488#64)).toNat ∧
    0x10000000 ≤ (M.getMem (top + 18446744073709551488#64)).toNat ∧
    (M.getMem (top + 18446744073709551488#64)).toNat + 8 * (M.getMem (top + 18446744073709551480#64)).toNat ≤
      (env.next M).toNat ∧
    (M.getMem (top + 18446744073709551488#64)).toNat % 8 = 0

/-- The exit (instruction 81): the stack pointer, `count` in `x8`, the slot's address in `x9`, the basis's length in
    `x19`; `MemOk`, `BV`. -/
def FinInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x8 = regs .x13 ∧ R .x9 = regs .x10 ∧
    R .x19 = M.getMem (top + 18446744073709551496#64) ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    MemOk env ret top regs m M ∧ BV env m top M

/-- What the passes over `what` share, `k` values left: the stack pointer, `count`, the slot, `what`'s cursor `x18`
    and end `x24`, `what` in a window and 8-byte aligned; `MemOk`, `BV`. -/
def Base (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x8 = regs .x13 ∧ R .x9 = regs .x10 ∧
    (R .x18).toNat + 8 * k = (regs .x11).toNat + 8 * (regs .x12).toNat ∧
    (R .x24).toNat = (regs .x11).toNat + 8 * (regs .x12).toNat ∧ 1 ≤ k ∧ k ≤ (regs .x12).toNat ∧
    InWin env (regs .x11) (8 * (regs .x12).toNat) ∧ (regs .x11).toNat % 8 = 0 ∧ R .x26 = regs .x26 ∧
    R .x27 = regs .x27 ∧ MemOk env ret top regs m M ∧ BV env m top M

/-- The outer loop's head (instruction 34), `k` values left: `Base`, the basis's length in `x19`. -/
def OInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Base env ret top regs m k R M ∧ R .x19 = M.getMem (top + 18446744073709551496#64)

/-- The products' buffer at `q`, as many words as the basis has: past the basis's buffer, allocated, 8-byte
    aligned. -/
def Tmp (env : Env) (top q : Word) (M : MachineState) : Prop :=
  (M.getMem (top + 18446744073709551488#64)).toNat + 8 * (M.getMem (top + 18446744073709551480#64)).toNat ≤
      q.toNat ∧
    q.toNat + 8 * (M.getMem (top + 18446744073709551496#64)).toNat ≤ (env.next M).toNat ∧ q.toNat % 8 = 0

/-- After the products (instruction 67): `Base`, the basis's length in `x21`, the products' buffer `x22`. -/
def AInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Base env ret top regs m k R M ∧ R .x21 = M.getMem (top + 18446744073709551496#64) ∧ Tmp env top (R .x22) M

/-- The products' loop head (instruction 59), `j` left: `AInv`, the basis's cursor `x25` and end `x23`, the
    products' cursor `x19`. -/
def IInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k j : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  AInv env ret top regs m k R M ∧ 1 ≤ j ∧ j ≤ (M.getMem (top + 18446744073709551496#64)).toNat ∧
    (R .x25).toNat + 8 * j = (M.getMem (top + 18446744073709551488#64)).toNat +
      8 * (M.getMem (top + 18446744073709551496#64)).toNat ∧
    (R .x23).toNat = (M.getMem (top + 18446744073709551488#64)).toNat +
      8 * (M.getMem (top + 18446744073709551496#64)).toNat ∧
    (R .x19).toNat + 8 * j = (R .x22).toNat + 8 * (M.getMem (top + 18446744073709551496#64)).toNat

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- The saved registers' slots, kept by a memory that agrees from `top - 88` up to `top`. -/
theorem Saved.keep {ret top : Word} {regs : Reg → Word} {M X : MachineState} (hlim : 88 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 88 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (h : Saved ret top regs M) : Saved ret top regs X := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := h
  exact ⟨(hk _ (by tn) (by tn)).trans s1, (hk _ (by tn) (by tn)).trans s2, (hk _ (by tn) (by tn)).trans s3,
    (hk _ (by tn) (by tn)).trans s4, (hk _ (by tn) (by tn)).trans s5, (hk _ (by tn) (by tn)).trans s6,
    (hk _ (by tn) (by tn)).trans s7, (hk _ (by tn) (by tn)).trans s8, (hk _ (by tn) (by tn)).trans s9,
    (hk _ (by tn) (by tn)).trans s10, (hk _ (by tn) (by tn)).trans s11⟩

/-- **`MemOk` across a callee**, from a stack top no higher, each word of its `out` one the function may write,
    the slots kept. -/
theorem MemOk.call {env : Env} {ret top top' : Word} {regs : Reg → Word} {m M X : MachineState}
    {out : Word → Prop} (h : MemOk env ret top regs m M) (hlim : 88 ≤ top.toNat) (ht : top'.toNat ≤ top.toNat)
    (hf : env.Frame top' out M X) (hc : X.code = M.code) (hs : env.Static X)
    (hout : ∀ a, out a → env.MayWrite top (SretOut Layouts.Vec.byteSize regs m) m X a)
    (hk : ∀ a : Word, top.toNat - 88 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a) :
    MemOk env ret top regs m X :=
  ⟨Tactic.frame_trans h.1 hf ht hout, hc.trans h.2.1, hs, h.2.2.2.keep hlim hk⟩

/-- **`MemOk` across a store into what the function allocated**, `NEXT` kept. -/
theorem MemOk.fresh {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M : MachineState}
    (h : MemOk env ret top regs m M) (hlim : env.stackLimit.toNat + 144 ≤ top.toNat)
    (hlo : (env.next m).toNat ≤ a.toNat) (hhi : a.toNat + 8 ≤ (env.next M).toNat) :
    MemOk env ret top regs m (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  have hnM := h.1.2.1
  have hna : a ≠ env.nextAddr := Tactic.ne_of_toNat (by omega)
  have hn : env.next (M.setMem a v) = env.next M := Tactic.next_setMem hna
  refine ⟨⟨Tactic.frame_fresh h.1 hn.symm hlo (by rw [hn]; omega), by rw [MachineState.code_setMem]; exact h.2.1,
    Tactic.static_store h.2.2.1 (by omega), h.2.2.2.keep (by omega) fun x h1 h2 => ?_⟩, hn⟩
  exact MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))

/-- **`BV` kept** by a memory agreeing on the header's three words, `NEXT` not lowered. -/
theorem BV.keep {env : Env} {m M X : MachineState} {top : Word} (h : BV env m top M)
    (hn : (env.next M).toNat ≤ (env.next X).toNat) (hlim : 144 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 136 ≤ a.toNat → a.toNat < top.toNat - 112 → X.getMem a = M.getMem a) :
    BV env m top X := by
  unfold BV at h ⊢
  rw [hk _ (by tn) (by tn), hk _ (by tn) (by tn), hk _ (by tn) (by tn)]
  omega

set_option hygiene false in
/-- A length of at least `1` that a branch says is `0`. -/
local macro "zlen" h:ident : tactic =>
  `(tactic| (have h0 := congrArg BitVec.toNat $h; rw [BitVec.toNat_ofNat] at h0; omega))

/-- **`BV` after the entry**: the basis `[1]`, its header `(1, q, 1)` stored at `top - 136`, its word at `q` freshly
    allocated. -/
theorem entry_bv {env : Env} {m m1 : MachineState} {top q : Word} (hlim : env.stackLimit.toNat + 144 ≤ top.toNat)
    (hq : (env.next m).toNat ≤ q.toNat) (hq0 : 0x10000000 ≤ q.toNat) (hq8 : q.toNat % 8 = 0)
    (hqn : q.toNat + 8 = (env.next m1).toNat) (hn1 : (env.next m1).toNat ≤ env.heapEnd.toNat) :
    BV env m top ((((m1.setMem (top + 18446744073709551488#64) q).setMem (top + 18446744073709551480#64)
      1#64).setMem (top + 18446744073709551496#64) 1#64).setMem q 1#64) := by
  have hlay := env.layout
  have e1 : (top + 18446744073709551488#64).toNat = top.toNat - 128 := by tn
  have e2 : (top + 18446744073709551480#64).toNat = top.toNat - 136 := by tn
  have e3 : (top + 18446744073709551496#64).toNat = top.toNat - 120 := by tn
  have hn : env.next ((((m1.setMem (top + 18446744073709551488#64) q).setMem (top + 18446744073709551480#64)
      1#64).setMem (top + 18446744073709551496#64) 1#64).setMem q 1#64) = env.next m1 := by
    rw [Tactic.next_setMem (Tactic.ne_of_toNat (by omega)), Tactic.next_setMem (Tactic.ne_of_toNat (by omega)),
      Tactic.next_setMem (Tactic.ne_of_toNat (by omega)), Tactic.next_setMem (Tactic.ne_of_toNat (by omega))]
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b h => Tactic.ne_of_toNat h
  have r1 : ((((m1.setMem (top + 18446744073709551488#64) q).setMem (top + 18446744073709551480#64) 1#64).setMem
      (top + 18446744073709551496#64) 1#64).setMem q 1#64).getMem (top + 18446744073709551488#64) = q := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have r2 : ((((m1.setMem (top + 18446744073709551488#64) q).setMem (top + 18446744073709551480#64) 1#64).setMem
      (top + 18446744073709551496#64) 1#64).setMem q 1#64).getMem (top + 18446744073709551480#64) = 1#64 := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r3 : ((((m1.setMem (top + 18446744073709551488#64) q).setMem (top + 18446744073709551480#64) 1#64).setMem
      (top + 18446744073709551496#64) 1#64).setMem q 1#64).getMem (top + 18446744073709551496#64) = 1#64 := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  unfold BV
  rw [hn, r1, r2, r3]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The two headers' words, the products' at `top - 112` and the basis's at `top - 136`, as `rvCapAt`, `rvPtrAt`,
    `vecCap`, `vecPtr` and `vecLen` name them. -/
theorem hdr_eq (top : Word) (M : MachineState) :
    rvCapAt (top + 18446744073709551504#64) = top + 18446744073709551504#64 ∧
      rvPtrAt (top + 18446744073709551504#64) = top + 18446744073709551512#64 ∧
      vecCap M (top + 18446744073709551504#64) = M.getMem (top + 18446744073709551504#64) ∧
      vecPtr M (top + 18446744073709551504#64) = M.getMem (top + 18446744073709551512#64) ∧
      vecLen M (top + 18446744073709551504#64) = M.getMem (top + 18446744073709551520#64) ∧
      rvCapAt (top + 18446744073709551480#64) = top + 18446744073709551480#64 ∧
      rvPtrAt (top + 18446744073709551480#64) = top + 18446744073709551488#64 ∧
      vecCap M (top + 18446744073709551480#64) = M.getMem (top + 18446744073709551480#64) ∧
      vecPtr M (top + 18446744073709551480#64) = M.getMem (top + 18446744073709551488#64) ∧
      vecLen M (top + 18446744073709551480#64) = M.getMem (top + 18446744073709551496#64) := by
  refine ⟨Runtime.GrowOne.rvCapAt_eq _, ?_, Runtime.VecHdrT.vecCap_eq _ _, ?_, ?_, Runtime.GrowOne.rvCapAt_eq _, ?_,
    Runtime.VecHdrT.vecCap_eq _ _, ?_, ?_⟩
  · unfold rvPtrAt; rw [BitVec.add_assoc]; rfl
  · unfold vecPtr; rw [BitVec.add_assoc]; rfl
  · unfold vecLen; rw [BitVec.add_assoc]; rfl
  · unfold rvPtrAt; rw [BitVec.add_assoc]; rfl
  · unfold vecPtr; rw [BitVec.add_assoc]; rfl
  · unfold vecLen; rw [BitVec.add_assoc]; rfl

/-- The products' header `(c, q, 0)` stored at `top - 112`, read back as `reserve` reads it, `NEXT` kept. -/
theorem tmp_reads {env : Env} {top c q : Word} {X : MachineState} (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) :
    (((X.setMem (top + 18446744073709551504#64) c).setMem (top + 18446744073709551512#64) q).setMem
        (top + 18446744073709551520#64) 0#64).getMem (rvCapAt (top + 18446744073709551504#64)) = c ∧
      (((X.setMem (top + 18446744073709551504#64) c).setMem (top + 18446744073709551512#64) q).setMem
        (top + 18446744073709551520#64) 0#64).getMem (rvPtrAt (top + 18446744073709551504#64)) = q ∧
      env.next (((X.setMem (top + 18446744073709551504#64) c).setMem (top + 18446744073709551512#64) q).setMem
        (top + 18446744073709551520#64) 0#64) = env.next X := by
  have hlay := env.layout
  have e504 : (top + 18446744073709551504#64).toNat = top.toNat - 112 := by tn
  have e512 : (top + 18446744073709551512#64).toNat = top.toNat - 104 := by tn
  have e520 : (top + 18446744073709551520#64).toNat = top.toNat - 96 := by tn
  obtain ⟨c0, p0, -⟩ := hdr_eq top X
  rw [c0, p0]
  refine ⟨?_, ?_, ?_⟩
  · rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega)), MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega)), MachineState.getMem_setMem_eq]
  · rw [Tactic.next_setMem (Tactic.ne_of_toNat (by omega)), Tactic.next_setMem (Tactic.ne_of_toNat (by omega)),
      Tactic.next_setMem (Tactic.ne_of_toNat (by omega))]

/-- **`MemOk` across a store into the frame** below the saved registers' slots, `NEXT` kept. -/
theorem MemOk.slot {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M : MachineState}
    (h : MemOk env ret top regs m M) (hlim : env.stackLimit.toNat + 144 ≤ top.toNat)
    (hlo : top.toNat - 144 ≤ a.toNat) (hhi : a.toNat + 96 ≤ top.toNat) :
    MemOk env ret top regs m (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  have hn : env.next (M.setMem a v) = env.next M := Tactic.next_setMem (Tactic.ne_of_toNat (by omega))
  refine ⟨⟨Tactic.frame_slot h.1 (by omega) (by omega), by rw [MachineState.code_setMem]; exact h.2.1,
    Tactic.static_store h.2.2.1 (by omega), h.2.2.2.keep (by omega) fun x h1 h2 => ?_⟩, hn⟩
  exact MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))

/-- **After the products' buffer `q` is allocated** (`m2`), its header `(n, q, 0)` stored at `top - 112` and
    `reserve(n)`d (`m3`, the room there): `MemOk`, `BV`, the basis's header kept, the products' pointer `q` and length
    `0` kept, `Tmp`. -/
theorem after_tmp {env : Env} {ret top q : Word} {regs : Reg → Word} {m M m2 m3 : MachineState}
    {out : Word → Prop} (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hM : MemOk env ret top regs m M)
    (hB : BV env m top M)
    (hf2 : env.Frame (top + 18446744073709551472#64) (fun _ => False) M m2)
    (hk2 : ∀ a : Word, top + 18446744073709551472#64 ≤ a → m2.getMem a = M.getMem a)
    (hc2 : m2.code = M.code) (hs2 : env.Static m2) (hq : (env.next M).toNat ≤ q.toNat) (hq8 : q.toNat % 8 = 0)
    (hqn : q.toNat + 8 * (M.getMem (top + 18446744073709551496#64)).toNat = (env.next m2).toNat)
    (hf3 : env.Frame (top + 18446744073709551472#64) out (((m2.setMem (top + 18446744073709551504#64)
      (M.getMem (top + 18446744073709551496#64))).setMem (top + 18446744073709551512#64) q).setMem
        (top + 18446744073709551520#64) 0#64) m3)
    (hout : ∀ a, out a → a = top + 18446744073709551504#64 ∨ a = top + 18446744073709551512#64)
    (hk3 : ∀ a : Word, top + 18446744073709551472#64 ≤ a → ¬ out a →
      m3.getMem a = (((m2.setMem (top + 18446744073709551504#64) (M.getMem (top + 18446744073709551496#64))).setMem
        (top + 18446744073709551512#64) q).setMem (top + 18446744073709551520#64) 0#64).getMem a)
    (hc3 : m3.code = (((m2.setMem (top + 18446744073709551504#64) (M.getMem (top + 18446744073709551496#64))).setMem
        (top + 18446744073709551512#64) q).setMem (top + 18446744073709551520#64) 0#64).code)
    (hs3 : env.Static m3)
    (hlen : vecLen m3 (top + 18446744073709551504#64) = vecLen (((m2.setMem (top + 18446744073709551504#64)
      (M.getMem (top + 18446744073709551496#64))).setMem (top + 18446744073709551512#64) q).setMem
        (top + 18446744073709551520#64) 0#64) (top + 18446744073709551504#64))
    (hroom : (M.getMem (top + 18446744073709551496#64)).toNat ≤
      (vecCap (((m2.setMem (top + 18446744073709551504#64) (M.getMem (top + 18446744073709551496#64))).setMem
        (top + 18446744073709551512#64) q).setMem (top + 18446744073709551520#64) 0#64)
          (top + 18446744073709551504#64)).toNat -
      (vecLen (((m2.setMem (top + 18446744073709551504#64) (M.getMem (top + 18446744073709551496#64))).setMem
        (top + 18446744073709551512#64) q).setMem (top + 18446744073709551520#64) 0#64)
          (top + 18446744073709551504#64)).toNat →
      vecCap m3 (top + 18446744073709551504#64) =
          vecCap (((m2.setMem (top + 18446744073709551504#64) (M.getMem (top + 18446744073709551496#64))).setMem
            (top + 18446744073709551512#64) q).setMem (top + 18446744073709551520#64) 0#64)
              (top + 18446744073709551504#64) ∧
        vecPtr m3 (top + 18446744073709551504#64) =
          vecPtr (((m2.setMem (top + 18446744073709551504#64) (M.getMem (top + 18446744073709551496#64))).setMem
            (top + 18446744073709551512#64) q).setMem (top + 18446744073709551520#64) 0#64)
              (top + 18446744073709551504#64)) :
    MemOk env ret top regs m m3 ∧ BV env m top m3 ∧
      m3.getMem (top + 18446744073709551496#64) = M.getMem (top + 18446744073709551496#64) ∧
      m3.getMem (top + 18446744073709551488#64) = M.getMem (top + 18446744073709551488#64) ∧
      m3.getMem (top + 18446744073709551512#64) = q ∧ m3.getMem (top + 18446744073709551520#64) = 0#64 ∧
      Tmp env top q m3 := by
  have hlay := env.layout
  have e472 : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
  have e504 : (top + 18446744073709551504#64).toNat = top.toNat - 112 := by tn
  have e512 : (top + 18446744073709551512#64).toNat = top.toNat - 104 := by tn
  have e520 : (top + 18446744073709551520#64).toNat = top.toNat - 96 := by tn
  have hM2 : MemOk env ret top regs m m2 := hM.call (by omega) (by omega) hf2 hc2 hs2 (fun _ h => h.elim)
    fun a h1 h2 => hk2 a (Tactic.le_of_toNat (by omega))
  obtain ⟨hT1, n1⟩ := hM2.slot (a := top + 18446744073709551504#64) (v := M.getMem (top + 18446744073709551496#64))
    hlim (by omega) (by omega)
  obtain ⟨hT2, n2⟩ := hT1.slot (a := top + 18446744073709551512#64) (v := q) hlim (by omega) (by omega)
  obtain ⟨hT3, n3⟩ := hT2.slot (a := top + 18446744073709551520#64) (v := 0#64) hlim (by omega) (by omega)
  have hout' : ∀ a, out a → a.toNat = top.toNat - 112 ∨ a.toNat = top.toNat - 104 := fun a ha => by
    rcases hout a ha with h | h <;> rw [h] <;> omega
  have hk : ∀ a : Word, top.toNat - 144 ≤ a.toNat → a.toNat < top.toNat → a.toNat ≠ top.toNat - 112 →
      a.toNat ≠ top.toNat - 104 → a.toNat ≠ top.toNat - 96 → m3.getMem a = M.getMem a := fun a h1 h2 h3 h4 h5 => by
    rw [hk3 a (Tactic.le_of_toNat (by omega)) fun ho => by rcases hout' a ho with h | h <;> omega,
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))]
    exact hk2 a (Tactic.le_of_toNat (by omega))
  have hM3 : MemOk env ret top regs m m3 := hT3.call (by omega) (by omega) hf3 hc3 hs3
    (fun a ha => Tactic.mw_stack (by rcases hout' a ha with h | h <;> omega)) fun a h1 h2 =>
      hk3 a (Tactic.le_of_toNat (by omega)) fun ho => by rcases hout' a ho with h | h <;> omega
  have hn3 : (env.next M).toNat ≤ (env.next m3).toNat := by
    have := hf2.1; have := hf3.1; rw [n3, n2, n1] at this; omega
  have g496 := hk (top + 18446744073709551496#64) (by tn) (by tn) (by tn) (by tn) (by tn)
  have g488 := hk (top + 18446744073709551488#64) (by tn) (by tn) (by tn) (by tn) (by tn)
  have g480 := hk (top + 18446744073709551480#64) (by tn) (by tn) (by tn) (by tn) (by tn)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b h => Tactic.ne_of_toNat h
  have t504 : (((m2.setMem (top + 18446744073709551504#64) (M.getMem (top + 18446744073709551496#64))).setMem
      (top + 18446744073709551512#64) q).setMem (top + 18446744073709551520#64) 0#64).getMem
        (top + 18446744073709551504#64) = M.getMem (top + 18446744073709551496#64) := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have t512 : (((m2.setMem (top + 18446744073709551504#64) (M.getMem (top + 18446744073709551496#64))).setMem
      (top + 18446744073709551512#64) q).setMem (top + 18446744073709551520#64) 0#64).getMem
        (top + 18446744073709551512#64) = q := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have t520 : (((m2.setMem (top + 18446744073709551504#64) (M.getMem (top + 18446744073709551496#64))).setMem
      (top + 18446744073709551512#64) q).setMem (top + 18446744073709551520#64) 0#64).getMem
        (top + 18446744073709551520#64) = 0#64 := MachineState.getMem_setMem_eq
  obtain ⟨-, -, c504, p504, l504, -⟩ := hdr_eq top m3
  obtain ⟨-, -, c504', p504', l504', -⟩ := hdr_eq top (((m2.setMem (top + 18446744073709551504#64)
    (M.getMem (top + 18446744073709551496#64))).setMem (top + 18446744073709551512#64) q).setMem
      (top + 18446744073709551520#64) 0#64)
  rw [c504', l504', t504, t520] at hroom
  rw [l504, l504', t520] at hlen
  obtain ⟨-, hp⟩ := hroom (by simp)
  rw [p504, p504', t512] at hp
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hB
  refine ⟨hM3, ?_, g496, g488, hp, hlen, ?_⟩
  · unfold BV; rw [g496, g488, g480]; omega
  · unfold Tmp; rw [g496, g488, g480]
    have := hf3.1; rw [n3, n2, n1] at this; omega

set_option rv_sym.heap true in
/-- **The exit**: the `assert!` (`panic_fmt` when the basis is shorter than `count`), then the basis's header copied
    into the slot with the length `count`, the epilogue, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needQ : Nat} (hnQ : 144 + needQ ≤ need) (hpf : Aborts env p L.panicFmt.idx needQ)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', HoldsT.post env (PostT env) (SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hwS : InWin env (regs .x10) 24) (haS : (regs .x10).toNat % 8 = 0)
    (hoS : env.Owned m top (regs .x10) 24) :
    ∀ R M, FinInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 162, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, -, -, -, -, ⟨hF, -, -, -⟩, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := id hinv
  have hlS := hwS.lt
  rv_introT hinv
  rv_symT hp with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)] using [hpf]
  · have o : ∀ k : Nat, k < 24 → SretOut Layouts.Vec.byteSize regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      ⟨by rw [toNat_add_ofNat (by omega)]; omega,
        by rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Vec.byteSize]; omega⟩
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF (by simpa using o 0 (by omega))
      (hwS.ne_next (Nat.le_refl _) (by omega))) (o 8 (by omega)) (hwS.ne_next_add (o := 8) (by omega)))
      (o 16 (by omega)) (hwS.ne_next_add (o := 16) (by omega))
  all_goals
    have hB : BufT env M (M.getMem (top + 18446744073709551480#64)) (M.getMem (top + 18446744073709551488#64)) 8 :=
      .inr ⟨hb5, by unfold Env.Live; omega, hb7⟩
    have hl : (regs .x13).toNat ≤ (M.getMem (top + 18446744073709551480#64)).toNat := by
      have := BitVec.le_def.1 hc; omega
  · exact (vecT_stores hwS haS hB hb3 hl).1.2.1.2.2.1
  · exact (vecT_stores hwS haS hB hb3 hl).1.2.1.2.2.2
  · exact .inr hb4

/-- **A product stored**: across `base_mul` (`m1`) and the store at `a` in the products' buffer `q`: `MemOk`, `BV`
    and `Tmp` kept, the basis's length and pointer read as before. -/
theorem prod_step {env : Env} {ret top q a v : Word} {regs : Reg → Word} {m M m1 : MachineState}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hM : MemOk env ret top regs m M) (hB : BV env m top M)
    (hT : Tmp env top q M) (hf : env.Frame (top + 18446744073709551472#64) (fun _ => False) M m1)
    (hk : ∀ a : Word, top + 18446744073709551472#64 ≤ a → m1.getMem a = M.getMem a) (hc : m1.code = M.code)
    (hs : env.Static m1) (ha1 : q.toNat ≤ a.toNat)
    (ha2 : a.toNat + 8 ≤ q.toNat + 8 * (M.getMem (top + 18446744073709551496#64)).toNat) :
    MemOk env ret top regs m (m1.setMem a v) ∧ BV env m top (m1.setMem a v) ∧ Tmp env top q (m1.setMem a v) ∧
      (m1.setMem a v).getMem (top + 18446744073709551496#64) = M.getMem (top + 18446744073709551496#64) ∧
      (m1.setMem a v).getMem (top + 18446744073709551488#64) = M.getMem (top + 18446744073709551488#64) := by
  have hlay := env.layout
  have e472 : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
  have hM1 : MemOk env ret top regs m m1 := hM.call (by omega) (by omega) hf hc hs (fun _ h => h.elim)
    fun a h1 h2 => hk a (Tactic.le_of_toNat (by omega))
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hB
  obtain ⟨ht1, ht2, ht3⟩ := hT
  have hnM := hM.1.2.1
  have hn1 := hf.1
  obtain ⟨hM2, hn⟩ := hM1.fresh (a := a) (v := v) hlim (by omega) (by omega)
  have rd : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 144 →
      (m1.setMem a v).getMem (top + c) = M.getMem (top + c) := fun c k hc' hk' => by
    have e : (top + c).toNat = top.toNat - k := by rw [BitVec.toNat_add]; omega
    rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))]
    exact hk _ (Tactic.le_of_toNat (by omega))
  have r496 := rd 18446744073709551496#64 120 rfl (by omega)
  have r488 := rd 18446744073709551488#64 128 rfl (by omega)
  have r480 := rd 18446744073709551480#64 136 rfl (by omega)
  refine ⟨hM2, ?_, ?_, r496, r488⟩
  · unfold BV; rw [r496, r488, r480, hn]; omega
  · unfold Tmp; rw [r496, r488, r480, hn]; omega

set_option rv_sym.heap true in
/-- **The products' loop**, from its head: a basis element times `what`'s value (`base_mul`) stored into the
    products' buffer, then back to the head or on to `app`; one product fewer left. -/
theorem inner (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needB : Nat} (hnB : 144 + needB ≤ need) (hbm : Field.BaseMulT.specT env p L.baseMul.idx needB)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m) {k : Nat}
    (happ : ∀ R M, AInv env ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 134, ret, top⟩ :: rest, R, M⟩) :
    ∀ j R M, IInv env ret top regs m k j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (IInv env ret top regs m k) fun j R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨hBase, h21, hT⟩, hj1, hjn, h25, h23, h19⟩ := id hI
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hM, hB⟩ := id hBase
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := id hB
  obtain ⟨ht1, ht2, ht3⟩ := id hT
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  rv_introT hI
  obtain ⟨-, -, -, h18, h24, hk1, hkw, hw, hwa, -, -, -, -⟩ := id hBase
  rv_symT hp stop [118, 134] with [hL, hlim] using [hbm]
  all_goals
    obtain ⟨hM1, hB1, hT1, g496, g488⟩ := prod_step (a := R .x19)
      (v := Model.baseMul (M.getMem (R .x25)) (R .x20)) hlim hM hB hT hret1_14 keep1_1 hret1_17 hret1_15
      (by omega) (by omega)
  -- back to the head
  · have hj2 : 2 ≤ j := by
      refine Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq ?_)
      rw [toNat_add_ofNat (by omega)]; omega
    refine ih (j - 1) _ _ (by omega) ⟨⟨⟨rfl, rfl, rfl, h18, h24, hk1, hkw, hw, hwa, rfl, rfl, hM1, hB1⟩, ?_, hT1⟩,
      by omega, by rw [g496]; omega, ?_, ?_, ?_⟩
    all_goals simp only [Tactic.rf]
    · exact g496.symm
    · rw [g496, g488, toNat_add_ofNat (by omega)]; omega
    · rw [g496, g488]; exact h23
    · rw [g496, toNat_add_ofNat (by omega)]; omega
  -- the last product: on to `app`
  · exact happ _ _ ⟨⟨rfl, rfl, rfl, h18, h24, hk1, hkw, hw, hwa, rfl, rfl, hM1, hB1⟩, g496.symm, hT1⟩

/-- **After `reserve(n)` of the basis** (`n` its length): `MemOk`, the length kept, room for `2 n` elements, the
    buffer allocated since the entry, 8-byte aligned, and apart from the products' buffer `q` (kept where it was, or
    grown into a block allocated after `q`'s). -/
theorem after_basis {env : Env} {ret top q : Word} {regs : Reg → Word} {m M m1 : MachineState} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hM : MemOk env ret top regs m M) (hB : BV env m top M)
    (hT : Tmp env top q M) (hf : env.Frame (top + 18446744073709551472#64) out M m1)
    (hout : ∀ a, out a → a = top + 18446744073709551480#64 ∨ a = top + 18446744073709551488#64)
    (hk : ∀ a : Word, top + 18446744073709551472#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a)
    (hc : m1.code = M.code) (hs : env.Static m1)
    (hlen : vecLen m1 (top + 18446744073709551480#64) = vecLen M (top + 18446744073709551480#64))
    (hroom : (M.getMem (top + 18446744073709551496#64)).toNat ≤
      (vecCap M (top + 18446744073709551480#64)).toNat - (vecLen M (top + 18446744073709551480#64)).toNat →
      vecCap m1 (top + 18446744073709551480#64) = vecCap M (top + 18446744073709551480#64) ∧
        vecPtr m1 (top + 18446744073709551480#64) = vecPtr M (top + 18446744073709551480#64))
    (hgrow : ¬ (M.getMem (top + 18446744073709551496#64)).toNat ≤
      (vecCap M (top + 18446744073709551480#64)).toNat - (vecLen M (top + 18446744073709551480#64)).toNat →
      Grown env M m1 (top + 18446744073709551480#64)
        ((vecLen M (top + 18446744073709551480#64)).toNat + (M.getMem (top + 18446744073709551496#64)).toNat) 8)
    (hbuf : (m1.getMem (rvCapAt (top + 18446744073709551480#64))).toNat = 0 ∨
      0x10000000 ≤ (m1.getMem (rvPtrAt (top + 18446744073709551480#64))).toNat ∧
        env.Live m1 (m1.getMem (rvPtrAt (top + 18446744073709551480#64)))
          ((m1.getMem (rvCapAt (top + 18446744073709551480#64))).toNat * 8) ∧
        (m1.getMem (rvPtrAt (top + 18446744073709551480#64))).toNat % 8 = 0)
    (hcap : (m1.getMem (rvCapAt (top + 18446744073709551480#64))).toNat * 8 < 2 ^ 63) :
    MemOk env ret top regs m m1 ∧
      m1.getMem (top + 18446744073709551496#64) = M.getMem (top + 18446744073709551496#64) ∧
      2 * (M.getMem (top + 18446744073709551496#64)).toNat ≤ (m1.getMem (top + 18446744073709551480#64)).toNat ∧
      (m1.getMem (top + 18446744073709551480#64)).toNat * 8 < 2 ^ 63 ∧
      (env.next m).toNat ≤ (m1.getMem (top + 18446744073709551488#64)).toNat ∧
      0x10000000 ≤ (m1.getMem (top + 18446744073709551488#64)).toNat ∧
      (m1.getMem (top + 18446744073709551488#64)).toNat + 8 * (m1.getMem (top + 18446744073709551480#64)).toNat ≤
        (env.next m1).toNat ∧
      (m1.getMem (top + 18446744073709551488#64)).toNat % 8 = 0 ∧
      ((m1.getMem (top + 18446744073709551488#64)).toNat + 8 * (m1.getMem (top + 18446744073709551480#64)).toNat ≤
          q.toNat ∨
        q.toNat + 8 * (M.getMem (top + 18446744073709551496#64)).toNat ≤
          (m1.getMem (top + 18446744073709551488#64)).toNat) ∧
      q.toNat + 8 * (M.getMem (top + 18446744073709551496#64)).toNat ≤ (env.next m1).toNat := by
  have hlay := env.layout
  have e472 : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
  have e480 : (top + 18446744073709551480#64).toNat = top.toNat - 136 := by tn
  have e488 : (top + 18446744073709551488#64).toNat = top.toNat - 128 := by tn
  have hout' : ∀ a, out a → a.toNat = top.toNat - 136 ∨ a.toNat = top.toNat - 128 := fun a ha => by
    rcases hout a ha with h | h <;> rw [h] <;> omega
  have hM1 : MemOk env ret top regs m m1 := hM.call (by omega) (by omega) hf hc hs
    (fun a ha => Tactic.mw_stack (by rcases hout' a ha with h | h <;> omega)) fun a h1 h2 =>
      hk a (Tactic.le_of_toNat (by omega)) fun ho => by rcases hout' a ho with h | h <;> omega
  obtain ⟨-, -, -, -, -, bc, bp, bC, bP, bL⟩ := hdr_eq top m1
  obtain ⟨-, -, -, -, -, -, -, bC', bP', bL'⟩ := hdr_eq top M
  rw [bL, bL'] at hlen
  rw [bC', bL', bC, bP, bP'] at hroom
  rw [bC', bL'] at hgrow
  rw [bc, bp] at hbuf
  rw [bc] at hcap
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hB
  obtain ⟨ht1, ht2, ht3⟩ := hT
  have hn1 := hf.1
  refine ⟨hM1, hlen, ?_⟩
  by_cases hr : (M.getMem (top + 18446744073709551496#64)).toNat ≤
    (M.getMem (top + 18446744073709551480#64)).toNat - (M.getMem (top + 18446744073709551496#64)).toNat
  · obtain ⟨c1, p1⟩ := hroom hr
    rw [c1, p1]
    exact ⟨by omega, hb3, hb4, hb5, by omega, hb7, .inl ht1, by omega⟩
  · obtain ⟨g1, ⟨g2, g3⟩, -⟩ := hgrow hr
    rw [Runtime.GrowOne.rvCapAt_eq] at g1 g3
    rw [Runtime.GrowOne.rvPtrAt_eq] at g2 g3
    rw [show top + 18446744073709551480#64 + 8#64 = top + 18446744073709551488#64 by
      rw [BitVec.add_assoc]; rfl] at g2 g3
    obtain ⟨p0, -, p8⟩ := hbuf.resolve_left (by omega)
    exact ⟨by omega, hcap, by omega, p0, by omega, p8, .inr (by omega), by omega⟩

/-- **After the products' copy and the length's store**: `memcpy` (`m2`) writing only past the basis's `n` elements
    within its buffer, then the length `v = 2 n` stored: `MemOk`, `BV`. -/
theorem copy_ok {env : Env} {ret top v : Word} {regs : Reg → Word} {m m1 m2 : MachineState} {out : Word → Prop}
    {n : Nat} (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hM1 : MemOk env ret top regs m m1) (hn1 : 1 ≤ n)
    (hc1 : 2 * n ≤ (m1.getMem (top + 18446744073709551480#64)).toNat)
    (hc2 : (m1.getMem (top + 18446744073709551480#64)).toNat * 8 < 2 ^ 63)
    (hp1 : (env.next m).toNat ≤ (m1.getMem (top + 18446744073709551488#64)).toNat)
    (hp2 : 0x10000000 ≤ (m1.getMem (top + 18446744073709551488#64)).toNat)
    (hp3 : (m1.getMem (top + 18446744073709551488#64)).toNat + 8 * (m1.getMem (top + 18446744073709551480#64)).toNat ≤
      (env.next m1).toNat)
    (hp4 : (m1.getMem (top + 18446744073709551488#64)).toNat % 8 = 0)
    (hf : env.Frame (top + 18446744073709551472#64) out m1 m2)
    (hout : ∀ a, out a → (m1.getMem (top + 18446744073709551488#64)).toNat + 8 * n ≤ a.toNat ∧
      a.toNat < (m1.getMem (top + 18446744073709551488#64)).toNat + 16 * n)
    (hk : ∀ a : Word, top + 18446744073709551472#64 ≤ a → ¬ out a → m2.getMem a = m1.getMem a)
    (hc : m2.code = m1.code) (hs : env.Static m2) (hv : v.toNat = 2 * n) :
    MemOk env ret top regs m (m2.setMem (top + 18446744073709551496#64) v) ∧
      BV env m top (m2.setMem (top + 18446744073709551496#64) v) := by
  have hlay := env.layout
  have e472 : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
  have hnm1 := hM1.1.2.1
  have hn2 := hf.1
  have hM2 : MemOk env ret top regs m m2 := hM1.call (by omega) (by omega) hf hc hs
    (fun a ha => Tactic.mw_fresh (by have := hout a ha; omega)) fun a h1 h2 =>
      hk a (Tactic.le_of_toNat (by omega)) fun ho => by have := hout a ho; omega
  obtain ⟨hM3, hn3⟩ := hM2.slot (a := top + 18446744073709551496#64) (v := v) hlim (by tn) (by tn)
  have rd : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 144 → k ≠ 120 →
      (m2.setMem (top + 18446744073709551496#64) v).getMem (top + c) = m1.getMem (top + c) := fun c k hc' hk' h1 => by
    have e : (top + c).toNat = top.toNat - k := by rw [BitVec.toNat_add]; omega
    rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e]; tn))]
    exact hk _ (Tactic.le_of_toNat (by omega)) fun ho => by have := hout _ ho; omega
  refine ⟨hM3, ?_⟩
  unfold BV
  rw [rd 18446744073709551480#64 136 rfl (by omega) (by omega), rd 18446744073709551488#64 128 rfl (by omega)
    (by omega), MachineState.getMem_setMem_eq, hn3, hv]
  omega

set_option rv_sym.heap true in
/-- **The products appended** (instruction 67): the basis `reserve`d for them, `memcpy` of the products after its
    elements, its length doubled, `what`'s cursor advanced; then the outer loop's head, one value fewer, or the
    exit. -/
theorem app (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR needM : Nat} (hnR : 144 + needR ≤ need) (hnM : 144 + needM ≤ need)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 8 p L.reserve.idx needR)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needM)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m) {k : Nat}
    (hfin : ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 162, ret, top⟩ :: rest, R, M⟩)
    (hloop : ∀ R M, 2 ≤ k → OInv env ret top regs m (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 68, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, AInv env ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 134, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hlay := env.layout
  obtain ⟨hBase, h21, hT⟩ := id hI
  obtain ⟨-, -, -, h18, h24, hk1, hkw, hw, hwa, -, -, hM, hB⟩ := id hBase
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := id hB
  obtain ⟨ht1, ht2, ht3⟩ := id hT
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  rv_introT hI
  have hwl := hw.lt
  have hhe := hW.heapEnd_le
  obtain ⟨-, -, -, -, -, bc, bp, -, -, -⟩ := hdr_eq top M
  rv_symT hp stop [68, 162] through [60] with [hL, hlim] using [hres, hcp]
  -- `reserve`'s precondition
  · rw [bc, bp]; exact .inr (by unfold Env.Live; omega)
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [bc]; exact hb3
  · rw [bc, bp]; exact .inr ⟨hb5, by unfold Env.Live; omega, hb7⟩
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [bc]; exact hb3
  -- no products: never, the basis has an element
  · exfalso; zlen hc_1
  · exfalso; zlen hc_1
  all_goals
    obtain ⟨hM1, g496, gc1, gc2, gp1, gp2, gp3, gp4, gdis, gq⟩ := after_basis hlim hM hB hT hret1_14
      (fun a ha => by
        simp only [GrowOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, bc, bp] at ha
        exact ha) keep1_1 hret1_25 hret1_15 hret1_16 hret1_17 hret1_18 hret1_22 hret1_23
    have hs3 : (M.getMem (top + 18446744073709551496#64) <<< 3).toNat =
        8 * (M.getMem (top + 18446744073709551496#64)).toNat := shl3 (by omega)
    have hd : (m1.getMem (top + 18446744073709551488#64) + m1.getMem (top + 18446744073709551496#64) <<< 3).toNat =
        (m1.getMem (top + 18446744073709551488#64)).toNat + 8 * (M.getMem (top + 18446744073709551496#64)).toNat := by
      rw [g496, BitVec.toNat_add, hs3]; omega
    have hn1 := hM1.1.2.1
  -- `memcpy`'s precondition
  · rw [hd, hs3]; omega
  · rw [hs3]; omega
  · intro _ b h1 h2
    unfold InRange at h1 h2
    rw [hd, hs3] at h1
    rw [hs3] at h2
    omega
  · rw [hs3, hd]
    refine .inr ⟨.inl ⟨by omega, by omega⟩, .inl (by omega), ?_, .inl (by omega)⟩
    rw [inWindow_iff]; exact .inl ⟨by omega, by omega⟩
  all_goals
    have hcopy := copy_ok (n := (M.getMem (top + 18446744073709551496#64)).toNat)
      (v := m1.getMem (top + 18446744073709551496#64) + M.getMem (top + 18446744073709551496#64)) hlim hM1 hb1 gc1
      gc2 gp1 gp2 gp3 gp4 hret2_14 (fun a ha => by
        simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte] at ha
        rw [toNat_alignToDword, hd, hs3] at ha
        omega) keep2_1 hret2_19 hret2_15 (by rw [g496, BitVec.toNat_add]; omega)
  -- the last value: the exit
  · exact hfin _ _ ⟨rfl, rfl, rfl, MachineState.getMem_setMem_eq.symm, rfl, rfl, hcopy.1, hcopy.2⟩
  -- the outer loop's head
  · have hk2 : 2 ≤ k := by
      refine Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq ?_)
      rw [toNat_add_ofNat (by omega)]; omega
    refine hloop _ _ hk2 ⟨⟨rfl, rfl, rfl, ?_, h24, by omega, by omega, hw, hwa, rfl, rfl, hcopy.1, hcopy.2⟩,
      MachineState.getMem_setMem_eq.symm⟩
    simp only [Tactic.rf]
    rw [toNat_add_ofNat (by omega)]; omega

set_option rv_sym.heap true in
/-- **The outer loop**, from its head: the exit when the basis is long enough, else `what`'s next value read, the
    products' buffer allocated and `reserve`d, then the products' loop; one value fewer left. -/
theorem outer (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR needA needH : Nat} (hnR : 144 + needR ≤ need) (hnA : 144 + needA ≤ need)
    (hnH : 144 + needH ≤ need) (hres : Runtime.ReserveT.ReserveSpecT env 8 8 p L.reserve.idx needR)
    (hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop))
    (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hfin : ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 162, ret, top⟩ :: rest, R, M⟩)
    (hin : ∀ k, (∀ R M, 2 ≤ k → OInv env ret top regs m (k - 1) R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 68, ret, top⟩ :: rest, R, M⟩) →
      ∀ j R M, IInv env ret top regs m k j R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, OInv env ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 68, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInv env ret top regs m) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨-, -, -, h18, h24, hk1, hkw, hw, hwa, -, -, hM, hB⟩, -⟩ := id hI
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := id hB
  have hwl := hw.lt
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  rv_introT hI
  rv_symT hp stop [118, 134, 162] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)]
    using [hac, hhe, hres]
  · exact hfin _ _ ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, hM, hB⟩
  -- the basis empty: never
  · exfalso; zlen hc
  · exfalso; zlen hc
  · exfalso; zlen hc
  · exfalso; zlen hc_2
  · rw [shl3 (by omega)]; omega
  all_goals
    have hq : (r2 .x10).toNat + 8 * (M.getMem (top + 18446744073709551496#64)).toNat = (env.next m2).toNat := by
      have := hret2_18; rw [shl3 (by omega)] at this; exact this
    have hn2 := hret2_14.1
    have hge := hW.next_ge
    have hnm := hM.1.1
    obtain ⟨tc, tp, tnx⟩ := tmp_reads (top := top) (c := M.getMem (top + 18446744073709551496#64)) (q := r2 .x10)
      (X := m2) hlim
  all_goals try simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
  · rw [tc, tp]; exact .inr (by unfold Env.Live; rw [tnx]; omega)
  · rw [tc]; omega
  · rw [tc, tp]; exact .inr ⟨by omega, by unfold Env.Live; rw [tnx]; omega, hret2_17⟩
  · rw [tc]; omega
  · exfalso; zlen hc
  · obtain ⟨hM3, hB3, g496, g488, g512, g520, hT3⟩ := after_tmp (q := r2 .x10) hlim hM hB hret2_14 keep2_1
      hret2_19 hret2_15 hret2_16 hret2_17 hq hret3_14 (fun a ha => by
        simp only [GrowOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, (hdr_eq top m3).1,
          (hdr_eq top m3).2.1] at ha
        exact ha) keep3_1 hret3_25 hret3_15 hret3_16 hret3_17
    refine hin k (fun R' M' h2 h' => ih (k - 1) R' M' (by omega) h')
      (m3.getMem (top + 18446744073709551496#64)).toNat _ _ ⟨⟨⟨rfl, rfl, rfl, h18, h24, hk1, hkw, hw, hwa, rfl, rfl,
        hM3, hB3⟩, ?_, ?_⟩, by rw [g496]; exact hB.1, Nat.le_refl _, ?_, ?_, ?_⟩
    all_goals simp only [Tactic.rf]
    · rw [g520, g496, BitVec.add_zero]
    · rw [g512]; exact hT3
    · rw [g488]
    · rw [g488, g496, BitVec.toNat_add, shl3 (by omega)]; omega
    · rw [g520, g512]; simp

set_option rv_sym.heap true in
/-- **`novel_basis` is total**: the basis `[1]` allocated (`panic_nounwind_fmt` when `alloc` fails), then the outer
    loop or the exit. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR needA needH needB needM needP needQ : Nat} (hnR : 144 + needR ≤ need) (hnA : 144 + needA ≤ need)
    (hnH : 144 + needH ≤ need) (hnB : 144 + needB ≤ need) (hnM : 144 + needM ≤ need) (hnP : 144 + needP ≤ need)
    (hnQ : 144 + needQ ≤ need)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 8 p L.reserve.idx needR)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hhe : Aborts env p L.handleError.idx needH) (hbm : Field.BaseMulT.specT env p L.baseMul.idx needB)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needM)
    (hpn : Aborts env p L.panicNounwindFmt.idx needP) (hpf : Aborts env p L.panicFmt.idx needQ) :
    specT env p i need := by
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)]
  have hfin := fin_ok env p i L hp hL hnQ hpf hstop hk hpre_3 hpre_11 hpre_12 hpre_6 hpre_7
    (hpre_2 ▸ ⟨hpre_8, hpre_9⟩)
  have hout := outer env p i L hp hL hnR hnA hnH hres hac hhe hstop hpre_3 hpre_11 hpre_12 hfin
    fun k hl => inner env p i L hp hL hnB hbm hpre_3 hpre_11 hpre_12
      (app env p i L hp hL hnR hnM hres hcp hstop hpre_3 hpre_11 hpre_12 hfin hl)
  rv_symT hp stop [68, 162] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)] using [hac, hpn]
  all_goals
    have hlay := env.layout
    have hn1 := hret1_14.2.1
    have hn0 := hret1_14.1
  all_goals
    have hB := entry_bv (by omega) hret1_16 (by have := hpre_12.next_ge; omega) hret1_17 hret1_18 hn1
  · refine hfin _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, hB⟩
    all_goals rv_closeT
  · have hw0 : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
    obtain ⟨hw, ha⟩ := hpre_10.resolve_left hw0
    have hwl := hw.lt
    refine hout (regs .x12).toNat _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, hB⟩, ?_⟩
    all_goals rv_closeT
    rw [BitVec.toNat_add, shl3 (by omega)]; omega

end Rv64mc.Proof.Whir.NovelBasisT

/-- info: 'Rv64mc.Proof.Whir.NovelBasisT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.NovelBasisT.total
