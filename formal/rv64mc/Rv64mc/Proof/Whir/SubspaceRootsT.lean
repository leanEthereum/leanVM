/-
  Rv64mc.Proof.Whir.SubspaceRootsT

  `verifier::whir::subspace_roots(log_n) -> Vec<K>` is total (`specT`): from a result's slot of `24` bytes owned, in a
  window, 8-byte aligned (`log_n` anything), it returns with the slot a vector of `K`s (`VecT`) of `log_n + 1`
  elements, its buffer allocated since the entry, writing at most the slot besides what it allocates (`SretOut`, the
  partial contract's), or the run ends with `a0 = 2` where `alloc` (through `panic_nounwind_fmt` or `handle_error`),
  `log_n`'s size check (`handle_error`) or `grow_one` does. Safety only: the partial contract's values
  (`Spec/Whir/Subspace.lean`'s `rootsSpec`, `Model.subspaceRootsRust`) are owed. It has no partial proof (class C).

  `roots` starts as `[1]` (its header at `sp + 0x28`), `layer` as `log_n` words (`1 << i`, its buffer `p`). Each of
  the `log_n` passes rewrites every word of `layer` (`spread`, `reduce`, `base_mul`), takes its first word
  (`memmove` of the rest down one word, the layer's length kept in a register) and pushes it on `roots`
  (`grow_one` when full). `remove`'s `assert!` is never reached: pass `t` starts with `log_n - t ≥ 1` words. Cut
  after the allocations (instruction 54, `mid`), at the fill loop's head (67, `fill`, `Total.loop`), the passes'
  head (92, `outer`, `Total.loop` with the layer's length as the measure), the layer's loop head (104, `inner`,
  the words left), after it (120, `rem`), at the push (84, `push`, where the paths with and without `grow_one` meet)
  and at the exit (139, `fin_ok`). Each part's memory facts are carried across its calls and stores by lemmas
  (`mv_ok`, `grow_ok`, `res_ok`, `call_ok`, `heap_ok`, `slots3`, `push_ok`), every other word of the frame read
  through them as before.

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `Saved`, `MemOk`, `RV`, `Lay`, `FinInv`, `MInv`, `FInv`, `OInv`, `RInv`, `IInv`,
    `PInv`

  ## Main results

  * `MemOk.call`, `MemOk.fresh`, `MemOk.slot`, `RV.keep`, `Lay.mono`, `mv_ok`, `grow_ok`, `res_ok`, `call_ok`,
    `heap_ok`, `slots3`, `push_ok`
  * `fin_ok`, `push`, `rem`, `inner`, `outer`, `fill`, `mid`, `total`
-/

import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.GrowOneT
import Rv64mc.Proof.Runtime.MemmoveT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.VecHdrT
import Rv64mc.Proof.Field.BaseMulT
import Rv64mc.Proof.Field.ReduceT
import Rv64mc.Proof.Field.SpreadT
import Rv64mc.Core.AbortStop
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Proof.Whir.VecWordT
import Rv64mc.Spec.Whir.Subspace
import Rv64mc.Gen.Tmpl.Verifier.Whir.SubspaceRoots

namespace Rv64mc.Proof.Whir.SubspaceRootsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Whir
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Runtime.GrowOneT (GrowOneSpecT)
open Rv64mc.Proof.Runtime.MemmoveT (MemmoveSpecT)
open Rv64mc.Proof.Whir.VecWordT (vecT_stores shl3 ovf)
open Rv64mc.Proof.Transcript (getMem_setMem_off)
open Rv64mc.Gen.Verifier.Whir.SubspaceRoots (Link tmpl)

/-- The total precondition: the result's slot (`24` bytes) in a window, 8-byte aligned, owned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 24

/-- The total postcondition: the slot a vector of `K`s of `log_n + 1` elements, its buffer allocated since the entry
    unless it has no capacity. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 8 ∧ (vecLen m' (regs .x10)).toNat = (regs .x11).toNat + 1 ∧
    (vecCap m' (regs .x10) = 0#64 ∨ (env.next m).toNat ≤ (vecPtr m' (regs .x10)).toNat)

/-- **The total contract of `subspace_roots`**: `PreT` to `PostT`, writing at most the slot (`SretOut`, the partial
    contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (SretOut Layouts.Vec.byteSize) (Stop := AbortStop)

/-- The saved registers' thirteen slots, from `top - 8` (the return address) down to `top - 104` (`s11`). -/
def Saved (ret top : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26 ∧
    M.getMem (top + 18446744073709551512#64) = regs .x27

/-- What every part keeps of memory: the frame, the code, the static data, the saved registers' slots. -/
def MemOk (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  env.Frame top (SretOut Layouts.Vec.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧ Saved ret top regs M

/-- `roots`' header at `top - 152` (capacity, pointer at `top - 144`, length at `top - 136`): its length at least `1`
    and at most its capacity, its buffer of fewer than `2^63` bytes, allocated since the entry, 8-byte aligned. -/
def RV (env : Env) (m : MachineState) (top : Word) (M : MachineState) : Prop :=
  1 ≤ (M.getMem (top + 18446744073709551480#64)).toNat ∧
    (M.getMem (top + 18446744073709551480#64)).toNat ≤ (M.getMem (top + 18446744073709551464#64)).toNat ∧
    (M.getMem (top + 18446744073709551464#64)).toNat * 8 < 2 ^ 63 ∧
    (env.next m).toNat ≤ (M.getMem (top + 18446744073709551472#64)).toNat ∧
    0x10000000 ≤ (M.getMem (top + 18446744073709551472#64)).toNat ∧
    (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat ≤
      (env.next M).toNat ∧
    (M.getMem (top + 18446744073709551472#64)).toNat % 8 = 0

/-- `layer`'s buffer `p` of `n` words: allocated since the entry, 8-byte aligned. -/
def Lay (env : Env) (m : MachineState) (n : Nat) (p : Word) (M : MachineState) : Prop :=
  (env.next m).toNat ≤ p.toNat ∧ 0x10000000 ≤ p.toNat ∧ p.toNat + 8 * n ≤ (env.next M).toNat ∧ p.toNat % 8 = 0

/-- The exit (instruction 139): the stack pointer, the slot's address at `sp`, `roots` of `log_n + 1` elements;
    `MemOk`, `RV`. -/
def FinInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ M.getMem (top + 18446744073709551424#64) = regs .x10 ∧
    (M.getMem (top + 18446744073709551480#64)).toNat = (regs .x11).toNat + 1 ∧ MemOk env ret top regs m M ∧
    RV env m top M

/-- After the allocations (instruction 54): the stack pointer, `log_n` in `x18`, the layer's header's address
    (`sp + 0x40`) in `x10`, `roots`' pointer in `x20`; the slot's address at `sp`, `roots` of length `1`, the layer's
    header `(log_n, p, 0)`, its buffer `Lay` unless `log_n = 0`; `MemOk`, `RV`. -/
def MInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x18 = regs .x11 ∧ R .x10 = top + 18446744073709551488#64 ∧
    R .x20 = M.getMem (top + 18446744073709551472#64) ∧ M.getMem (top + 18446744073709551424#64) = regs .x10 ∧
    M.getMem (top + 18446744073709551488#64) = regs .x11 ∧ M.getMem (top + 18446744073709551504#64) = 0#64 ∧
    M.getMem (top + 18446744073709551480#64) = 1#64 ∧ (regs .x11).toNat * 8 < 2 ^ 63 ∧
    ((regs .x11).toNat = 0 ∨ Lay env m (regs .x11).toNat (M.getMem (top + 18446744073709551496#64)) M) ∧
    MemOk env ret top regs m M ∧ RV env m top M

/-- The fill loop's head (instruction 67), `j` words of the layer left to write: the stack pointer, `log_n` in `x18`,
    `1` in `x10`, `roots`' pointer in `x20`, the layer's buffer `p` in `x22`, the next exponent `i` in `x12` (`i + j =
    log_n`), the cursor `p + 8 (i - 1)` in `x11`, `log_n - 1` in `x26`; `roots` of length `1`, the slot's address at
    `sp`; `Lay`, `MemOk`, `RV`. -/
def FInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (p : Word) (j : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x18 = regs .x11 ∧ R .x10 = 1#64 ∧
    R .x20 = M.getMem (top + 18446744073709551472#64) ∧ R .x22 = p ∧ (R .x12).toNat + j = (regs .x11).toNat ∧
    1 ≤ (R .x12).toNat ∧ 1 ≤ j ∧ (R .x11).toNat + 8 = p.toNat + 8 * (R .x12).toNat ∧
    (R .x26).toNat + 1 = (regs .x11).toNat ∧ M.getMem (top + 18446744073709551480#64) = 1#64 ∧
    M.getMem (top + 18446744073709551424#64) = regs .x10 ∧ (regs .x11).toNat * 8 < 2 ^ 63 ∧
    Lay env m (regs .x11).toNat p M ∧ MemOk env ret top regs m M ∧ RV env m top M

/-- The passes' head (instruction 92), `k` words left in the layer at its buffer `p`: the stack pointer, `log_n` in
    `x18`, `roots`' pointer in `x20` and length in `x25`, `p` in `x22`, `k` in `x26`, `8 k` in `x27`, the passes done
    in `x12`, `p + 8` at `sp + 8`, the slot's address at `sp`; `log_n * 8` below `2^63`, `Lay`, `MemOk`, `RV`. -/
def OInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (p : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x18 = regs .x11 ∧ R .x20 = M.getMem (top + 18446744073709551472#64) ∧
    R .x22 = p ∧ R .x25 = M.getMem (top + 18446744073709551480#64) ∧ (R .x26).toNat = k ∧ (R .x27).toNat = 8 * k ∧
    (R .x12).toNat + k = (regs .x11).toNat ∧
    (M.getMem (top + 18446744073709551480#64)).toNat + k = (regs .x11).toNat + 1 ∧ 1 ≤ k ∧
    M.getMem (top + 18446744073709551432#64) = p + 8#64 ∧ M.getMem (top + 18446744073709551424#64) = regs .x10 ∧
    (regs .x11).toNat * 8 < 2 ^ 63 ∧ Lay env m (regs .x11).toNat p M ∧ MemOk env ret top regs m M ∧ RV env m top M

/-- After the layer's loop (instruction 120), `k` words in it: the stack pointer, `log_n` in `x18`, `p` in `x20`,
    `roots`' length in `x25`, eight times it in `x8`, `k` in `x26`, `8 k` in `x27`; `roots`' pointer at `sp + 0x20`,
    the passes done (this one included) at `sp + 0x18`, `8 k` at `sp + 0x10`, `p + 8` at `sp + 8`, the slot's address
    at `sp`; `Lay`, `MemOk`, `RV`. -/
def RInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (p : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x18 = regs .x11 ∧ R .x20 = p ∧
    R .x25 = M.getMem (top + 18446744073709551480#64) ∧ (R .x26).toNat = k ∧ (R .x27).toNat = 8 * k ∧
    (R .x8).toNat = 8 * (M.getMem (top + 18446744073709551480#64)).toNat ∧
    (M.getMem (top + 18446744073709551480#64)).toNat + k = (regs .x11).toNat + 1 ∧ 1 ≤ k ∧
    M.getMem (top + 18446744073709551456#64) = M.getMem (top + 18446744073709551472#64) ∧
    (M.getMem (top + 18446744073709551448#64)).toNat + k = (regs .x11).toNat + 1 ∧
    (M.getMem (top + 18446744073709551440#64)).toNat = 8 * k ∧
    M.getMem (top + 18446744073709551432#64) = p + 8#64 ∧ M.getMem (top + 18446744073709551424#64) = regs .x10 ∧
    (regs .x11).toNat * 8 < 2 ^ 63 ∧ Lay env m (regs .x11).toNat p M ∧ MemOk env ret top regs m M ∧ RV env m top M

/-- The layer's loop head (instruction 104), `j` of its `k` words left: `RInv`, the cursor `x9`, the end `x19`. -/
def IInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (p : Word) (k j : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  RInv env ret top regs m p k R M ∧ (R .x9).toNat + 8 * j = p.toNat + 8 * k ∧ (R .x19).toNat = p.toNat + 8 * k ∧
    1 ≤ j ∧ j ≤ k

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

set_option hygiene false in
/-- A length of at least `1` that a branch says is `0`. -/
local macro "zlen" h:ident : tactic =>
  `(tactic| (have h0 := congrArg BitVec.toNat $h; rw [BitVec.toNat_ofNat] at h0; omega))

/-- The saved registers' slots, kept by a memory that agrees from `top - 104` up to `top`. -/
theorem Saved.keep {ret top : Word} {regs : Reg → Word} {M X : MachineState} (hlim : 104 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 104 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (h : Saved ret top regs M) : Saved ret top regs X := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := h
  exact ⟨(hk _ (by tn) (by tn)).trans s1, (hk _ (by tn) (by tn)).trans s2, (hk _ (by tn) (by tn)).trans s3,
    (hk _ (by tn) (by tn)).trans s4, (hk _ (by tn) (by tn)).trans s5, (hk _ (by tn) (by tn)).trans s6,
    (hk _ (by tn) (by tn)).trans s7, (hk _ (by tn) (by tn)).trans s8, (hk _ (by tn) (by tn)).trans s9,
    (hk _ (by tn) (by tn)).trans s10, (hk _ (by tn) (by tn)).trans s11, (hk _ (by tn) (by tn)).trans s12,
    (hk _ (by tn) (by tn)).trans s13⟩

/-- **`MemOk` across a callee**, from a stack top no higher, each word of its `out` one the function may write,
    the slots kept. -/
theorem MemOk.call {env : Env} {ret top top' : Word} {regs : Reg → Word} {m M X : MachineState}
    {out : Word → Prop} (h : MemOk env ret top regs m M) (hlim : 104 ≤ top.toNat) (ht : top'.toNat ≤ top.toNat)
    (hf : env.Frame top' out M X) (hc : X.code = M.code) (hs : env.Static X)
    (hout : ∀ a, out a → env.MayWrite top (SretOut Layouts.Vec.byteSize regs m) m X a)
    (hk : ∀ a : Word, top.toNat - 104 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a) :
    MemOk env ret top regs m X :=
  ⟨Tactic.frame_trans h.1 hf ht hout, hc.trans h.2.1, hs, h.2.2.2.keep hlim hk⟩

/-- **`MemOk` across a store into what the function allocated**, `NEXT` kept. -/
theorem MemOk.fresh {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M : MachineState}
    (h : MemOk env ret top regs m M) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (hlo : (env.next m).toNat ≤ a.toNat) (hhi : a.toNat + 8 ≤ (env.next M).toNat) :
    MemOk env ret top regs m (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  have hnM := h.1.2.1
  have hna : a ≠ env.nextAddr := Tactic.ne_of_toNat (by omega)
  have hn : env.next (M.setMem a v) = env.next M := Tactic.next_setMem hna
  refine ⟨⟨Tactic.frame_fresh h.1 hn.symm hlo (by rw [hn]; omega), by rw [MachineState.code_setMem]; exact h.2.1,
    Tactic.static_store h.2.2.1 (by omega), h.2.2.2.keep (by omega) fun x h1 h2 => ?_⟩, hn⟩
  exact MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))

/-- **`MemOk` across a store into the frame** below the saved registers' slots, `NEXT` kept. -/
theorem MemOk.slot {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M : MachineState}
    (h : MemOk env ret top regs m M) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (hlo : top.toNat - 192 ≤ a.toNat) (hhi : a.toNat + 112 ≤ top.toNat) :
    MemOk env ret top regs m (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  have hn : env.next (M.setMem a v) = env.next M := Tactic.next_setMem (Tactic.ne_of_toNat (by omega))
  refine ⟨⟨Tactic.frame_slot h.1 (by omega) (by omega), by rw [MachineState.code_setMem]; exact h.2.1,
    Tactic.static_store h.2.2.1 (by omega), h.2.2.2.keep (by omega) fun x h1 h2 => ?_⟩, hn⟩
  exact MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))

/-- **`RV` kept** by a memory agreeing on the header's three words, `NEXT` not lowered. -/
theorem RV.keep {env : Env} {m M X : MachineState} {top : Word} (h : RV env m top M)
    (hn : (env.next M).toNat ≤ (env.next X).toNat) (hlim : 192 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 152 ≤ a.toNat → a.toNat < top.toNat - 128 → X.getMem a = M.getMem a) :
    RV env m top X := by
  unfold RV at h ⊢
  rw [hk _ (by tn) (by tn), hk _ (by tn) (by tn), hk _ (by tn) (by tn)]
  omega

/-- `Lay` kept, `NEXT` not lowered. -/
theorem Lay.mono {env : Env} {m M X : MachineState} {n : Nat} {p : Word} (h : Lay env m n p M)
    (hn : (env.next M).toNat ≤ (env.next X).toNat) : Lay env m n p X :=
  ⟨h.1, h.2.1, by have := h.2.2.1; omega, h.2.2.2⟩

/-- `roots`' header words as `rvCapAt`, `rvPtrAt` name them. -/
theorem hdr (top : Word) : rvCapAt (top + 18446744073709551464#64) = top + 18446744073709551464#64 ∧
    rvPtrAt (top + 18446744073709551464#64) = top + 18446744073709551472#64 := by
  simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_assoc]
  exact ⟨rfl, rfl⟩

/-- **Across `memmove` within the layer** (`m1`): `MemOk`, `RV`, `Lay` kept, every word of the frame read as
    before. -/
theorem mv_ok {env : Env} {ret top lp : Word} {regs : Reg → Word} {m M m1 : MachineState} {out : Word → Prop}
    {n : Nat} (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hM : MemOk env ret top regs m M)
    (hB : RV env m top M) (hL : Lay env m n lp M) (hf : env.Frame (top + 18446744073709551424#64) out M m1)
    (hout : ∀ a, out a → (env.next m).toNat ≤ a.toNat ∧ a.toNat < lp.toNat + 8 * n)
    (hk : ∀ a : Word, top + 18446744073709551424#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a)
    (hc : m1.code = M.code) (hs : env.Static m1) :
    MemOk env ret top regs m m1 ∧ RV env m top m1 ∧ Lay env m n lp m1 ∧
      ∀ c : Word, top.toNat - 192 ≤ (top + c).toNat → m1.getMem (top + c) = M.getMem (top + c) := by
  have hlay := env.layout
  have e424 : (top + 18446744073709551424#64).toNat = top.toNat - 192 := by tn
  have hnM := hM.1.2.1
  have hl3 := hL.2.2.1
  have hn1 := hf.1
  have rd : ∀ a : Word, top.toNat - 192 ≤ a.toNat → m1.getMem a = M.getMem a := fun a h =>
    hk a (Tactic.le_of_toNat (by omega)) fun ho => by have := hout a ho; omega
  refine ⟨hM.call (by omega) (by omega) hf hc hs (fun a ha => Tactic.mw_fresh (by have := hout a ha; omega))
    fun a h1 _ => rd a (by omega), hB.keep hn1 (by omega) fun a h1 _ => rd a (by omega), hL.mono hn1,
    fun c h => rd _ h⟩

/-- **Across `grow_one` of `roots`** (full, `m1`): `MemOk` kept, `RV` with room for one more, every other word of
    the frame read as before. -/
theorem grow_ok {env : Env} {ret top : Word} {regs r : Reg → Word} {m M m1 : MachineState}
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hM : MemOk env ret top regs m M) (hB : RV env m top M)
    (hr : r .x10 = top + 18446744073709551464#64)
    (hf : env.Frame (top + 18446744073709551424#64) (GrowOut r M) M m1)
    (hk : ∀ a : Word, top + 18446744073709551424#64 ≤ a → ¬ GrowOut r M a → m1.getMem a = M.getMem a)
    (hc : m1.code = M.code) (hs : env.Static m1)
    (h16 : (M.getMem (rvCapAt (top + 18446744073709551464#64))).toNat + 1 ≤
      (m1.getMem (rvCapAt (top + 18446744073709551464#64))).toNat)
    (h17 : env.Fresh M m1 (m1.getMem (rvPtrAt (top + 18446744073709551464#64)))
      ((m1.getMem (rvCapAt (top + 18446744073709551464#64))).toNat * 8))
    (h21 : (m1.getMem (rvCapAt (top + 18446744073709551464#64))).toNat = 0 ∨
      268435456 ≤ (m1.getMem (rvPtrAt (top + 18446744073709551464#64))).toNat ∧
        env.Live m1 (m1.getMem (rvPtrAt (top + 18446744073709551464#64)))
          ((m1.getMem (rvCapAt (top + 18446744073709551464#64))).toNat * 8) ∧
        (m1.getMem (rvPtrAt (top + 18446744073709551464#64))).toNat % 8 = 0)
    (h22 : (m1.getMem (rvCapAt (top + 18446744073709551464#64))).toNat * 8 < 2 ^ 63) :
    MemOk env ret top regs m m1 ∧ RV env m top m1 ∧
      (m1.getMem (top + 18446744073709551480#64)).toNat < (m1.getMem (top + 18446744073709551464#64)).toNat ∧
      (env.next M).toNat ≤ (env.next m1).toNat ∧
      ∀ c : Word, top.toNat - 192 ≤ (top + c).toNat → (top + c).toNat ≠ top.toNat - 152 →
        (top + c).toNat ≠ top.toNat - 144 → m1.getMem (top + c) = M.getMem (top + c) := by
  have hlay := env.layout
  have e424 : (top + 18446744073709551424#64).toNat = top.toNat - 192 := by tn
  have e464 : (top + 18446744073709551464#64).toNat = top.toNat - 152 := by tn
  have e472 : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
  obtain ⟨c0, p0⟩ := hdr top
  rw [c0] at h16 h22
  rw [c0, p0] at h17 h21
  have ho : ∀ a, GrowOut r M a → a.toNat = top.toNat - 152 ∨ a.toNat = top.toNat - 144 := fun a ha => by
    simp only [GrowOut, hr, c0, p0] at ha
    rcases ha with rfl | rfl
    · exact .inl e464
    · exact .inr e472
  have rd : ∀ a : Word, top.toNat - 192 ≤ a.toNat → a.toNat ≠ top.toNat - 152 → a.toNat ≠ top.toNat - 144 →
      m1.getMem a = M.getMem a := fun a h1 h2 h3 =>
    hk a (Tactic.le_of_toNat (by omega)) fun h => by rcases ho a h with h | h <;> omega
  have hnM := hM.1.2.1
  have hn1 := hf.1
  have hM1 : MemOk env ret top regs m m1 := hM.call (by omega) (by omega) hf hc hs
    (fun a ha => Tactic.mw_stack (by rcases ho a ha with h | h <;> omega)) fun a h1 h2 => rd a (by omega)
      (by omega) (by omega)
  have g480 := rd (top + 18446744073709551480#64) (by tn) (by tn) (by tn)
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hB
  obtain ⟨hp0, -, hpa⟩ := h21.resolve_left (by omega)
  have hf1 := h17.1
  have hf2 := h17.2
  refine ⟨hM1, ?_, by rw [g480]; omega, hn1, fun c h1 h2 h3 => rd _ h1 h2 h3⟩
  unfold RV
  rw [g480]
  omega

/-- **Across a callee writing nothing of the caller's** (`m1`, from the stack pointer `top - 192`): `MemOk`, `RV`,
    `Lay` kept, every word of the frame read as before. -/
theorem call_ok {env : Env} {ret top lp : Word} {regs : Reg → Word} {m M m1 : MachineState} {n : Nat}
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hM : MemOk env ret top regs m M) (hB : RV env m top M)
    (hL : Lay env m n lp M) (hf : env.Frame (top + 18446744073709551424#64) (fun _ => False) M m1)
    (hk : ∀ a : Word, top + 18446744073709551424#64 ≤ a → m1.getMem a = M.getMem a) (hc : m1.code = M.code)
    (hs : env.Static m1) :
    MemOk env ret top regs m m1 ∧ RV env m top m1 ∧ Lay env m n lp m1 ∧
      ∀ c : Word, top.toNat - 192 ≤ (top + c).toNat → m1.getMem (top + c) = M.getMem (top + c) := by
  have e424 : (top + 18446744073709551424#64).toNat = top.toNat - 192 := by tn
  have rd : ∀ a : Word, top.toNat - 192 ≤ a.toNat → m1.getMem a = M.getMem a := fun a h =>
    hk a (Tactic.le_of_toNat (by omega))
  exact ⟨hM.call (by omega) (by omega) hf hc hs (fun _ h => h.elim) fun a h1 _ => rd a (by omega),
    hB.keep hf.1 (by omega) fun a h1 _ => rd a (by omega), hL.mono hf.1, fun c h => rd _ h⟩

/-- **A store into what the function allocated**: `MemOk`, `RV` kept, `NEXT` kept, every word of the stack read as
    before. -/
theorem heap_ok {env : Env} {ret top a : Word} {regs : Reg → Word} {m M : MachineState}
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hM : MemOk env ret top regs m M) (hB : RV env m top M)
    (hlo : (env.next m).toNat ≤ a.toNat) (hhi : a.toNat + 8 ≤ (env.next M).toNat) (v : Word) :
    MemOk env ret top regs m (M.setMem a v) ∧ RV env m top (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      ∀ c : Word, env.stackLimit.toNat ≤ (top + c).toNat → (M.setMem a v).getMem (top + c) = M.getMem (top + c) := by
  have hlay := env.layout
  have hnM := hM.1.2.1
  obtain ⟨h1, n1⟩ := hM.fresh (v := v) hlim hlo hhi
  have rd : ∀ x : Word, env.stackLimit.toNat ≤ x.toNat → (M.setMem a v).getMem x = M.getMem x := fun x h =>
    MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))
  exact ⟨h1, hB.keep (by rw [n1]) (by omega) fun x h1 _ => rd x (by omega), n1, fun c h => rd _ h⟩

/-- The layer's header words (at `top - 128`) as `rvCapAt`, `rvPtrAt`, `vecCap`, `vecPtr`, `vecLen` name them. -/
theorem hdrL (top : Word) (M : MachineState) :
    rvCapAt (top + 18446744073709551488#64) = top + 18446744073709551488#64 ∧
      rvPtrAt (top + 18446744073709551488#64) = top + 18446744073709551496#64 ∧
      vecCap M (top + 18446744073709551488#64) = M.getMem (top + 18446744073709551488#64) ∧
      vecPtr M (top + 18446744073709551488#64) = M.getMem (top + 18446744073709551496#64) ∧
      vecLen M (top + 18446744073709551488#64) = M.getMem (top + 18446744073709551504#64) := by
  refine ⟨Runtime.GrowOne.rvCapAt_eq _, ?_, Runtime.VecHdrT.vecCap_eq _ _, ?_, ?_⟩
  · unfold rvPtrAt; rw [BitVec.add_assoc]; rfl
  · unfold vecPtr; rw [BitVec.add_assoc]; rfl
  · unfold vecLen; rw [BitVec.add_assoc]; rfl

/-- **Across `reserve` of the layer** (`m1`) writing at most its header's capacity and pointer: `MemOk`, `RV` kept,
    `NEXT` not lowered, every other word of the frame read as before. -/
theorem res_ok {env : Env} {ret top : Word} {regs : Reg → Word} {m M m1 : MachineState} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hM : MemOk env ret top regs m M) (hB : RV env m top M)
    (hf : env.Frame (top + 18446744073709551424#64) out M m1)
    (hout : ∀ a, out a → a = top + 18446744073709551488#64 ∨ a = top + 18446744073709551496#64)
    (hk : ∀ a : Word, top + 18446744073709551424#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a)
    (hc : m1.code = M.code) (hs : env.Static m1) :
    MemOk env ret top regs m m1 ∧ RV env m top m1 ∧ (env.next M).toNat ≤ (env.next m1).toNat ∧
      ∀ c : Word, top.toNat - 192 ≤ (top + c).toNat → (top + c).toNat ≠ top.toNat - 128 →
        (top + c).toNat ≠ top.toNat - 120 → m1.getMem (top + c) = M.getMem (top + c) := by
  have hlay := env.layout
  have e424 : (top + 18446744073709551424#64).toNat = top.toNat - 192 := by tn
  have ho : ∀ a, out a → a.toNat = top.toNat - 128 ∨ a.toNat = top.toNat - 120 := fun a ha => by
    rcases hout a ha with rfl | rfl
    · exact .inl (by tn)
    · exact .inr (by tn)
  have rd : ∀ a : Word, top.toNat - 192 ≤ a.toNat → a.toNat ≠ top.toNat - 128 → a.toNat ≠ top.toNat - 120 →
      m1.getMem a = M.getMem a := fun a h1 h2 h3 =>
    hk a (Tactic.le_of_toNat (by omega)) fun h => by rcases ho a h with h | h <;> omega
  exact ⟨hM.call (by omega) (by omega) hf hc hs (fun a ha => Tactic.mw_stack (by rcases ho a ha with h | h <;> omega))
    fun a h1 h2 => rd a (by omega) (by omega) (by omega), hB.keep hf.1 (by omega) fun a h1 h2 =>
      rd a (by omega) (by omega) (by omega), hf.1, fun c h1 h2 h3 => rd _ h1 h2 h3⟩

/-- A store into the frame keeps `NEXT`. -/
theorem next_stk {env : Env} {top c v : Word} {M : MachineState} (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (hc : 2 ^ 64 - 192 ≤ c.toNat) : env.next (M.setMem (top + c) v) = env.next M :=
  Env.next_setMem_stack (by rw [BitVec.toNat_add]; have := c.isLt; omega)

/-- Two offsets from one base. -/
theorem ne_off {t c d : Word} (h : c ≠ d) : t + c ≠ t + d := fun e => h ((BitVec.add_right_inj t).1 e)

/-- **The pass's three words saved** (`sp + 0x20`, `0x18`, `0x10`): `MemOk`, `RV` kept, `NEXT` kept, every other word
    of the frame read as before. -/
theorem slots3 {env : Env} {ret top v1 v2 v3 : Word} {regs : Reg → Word} {m M : MachineState}
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hM : MemOk env ret top regs m M) (hB : RV env m top M) :
    MemOk env ret top regs m (((M.setMem (top + 18446744073709551456#64) v1).setMem (top + 18446744073709551448#64)
      v2).setMem (top + 18446744073709551440#64) v3) ∧
    RV env m top (((M.setMem (top + 18446744073709551456#64) v1).setMem (top + 18446744073709551448#64)
      v2).setMem (top + 18446744073709551440#64) v3) ∧
    env.next (((M.setMem (top + 18446744073709551456#64) v1).setMem (top + 18446744073709551448#64)
      v2).setMem (top + 18446744073709551440#64) v3) = env.next M ∧
    ∀ c : Word, c ≠ 18446744073709551456#64 → c ≠ 18446744073709551448#64 → c ≠ 18446744073709551440#64 →
      (((M.setMem (top + 18446744073709551456#64) v1).setMem (top + 18446744073709551448#64)
        v2).setMem (top + 18446744073709551440#64) v3).getMem (top + c) = M.getMem (top + c) := by
  obtain ⟨h1, n1⟩ := hM.slot (a := top + 18446744073709551456#64) (v := v1) hlim (by tn) (by tn)
  obtain ⟨h2, n2⟩ := h1.slot (a := top + 18446744073709551448#64) (v := v2) hlim (by tn) (by tn)
  obtain ⟨h3, n3⟩ := h2.slot (a := top + 18446744073709551440#64) (v := v3) hlim (by tn) (by tn)
  have rd : ∀ c : Word, c ≠ 18446744073709551456#64 → c ≠ 18446744073709551448#64 → c ≠ 18446744073709551440#64 →
      (((M.setMem (top + 18446744073709551456#64) v1).setMem (top + 18446744073709551448#64)
        v2).setMem (top + 18446744073709551440#64) v3).getMem (top + c) = M.getMem (top + c) := fun c c1 c2 c3 => by
    rw [MachineState.getMem_setMem_ne (ne_off c3), MachineState.getMem_setMem_ne (ne_off c2),
      MachineState.getMem_setMem_ne (ne_off c1)]
  refine ⟨h3, ?_, by rw [n3, n2, n1], rd⟩
  unfold RV
  rw [rd _ (by decide) (by decide) (by decide), rd _ (by decide) (by decide) (by decide),
    rd _ (by decide) (by decide) (by decide), n3, n2, n1]
  exact hB

/-- **An element pushed on `roots`**: a word stored at `a`, its slot `len` (below the capacity), then the length `w =
    len + 1` stored: `MemOk`, `RV` kept, `NEXT` kept, every other word of the frame read as before. -/
theorem push_ok {env : Env} {ret top a v w : Word} {regs : Reg → Word} {m X : MachineState}
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hM : MemOk env ret top regs m X) (hB : RV env m top X)
    (hlt : (X.getMem (top + 18446744073709551480#64)).toNat < (X.getMem (top + 18446744073709551464#64)).toNat)
    (ha : a.toNat = (X.getMem (top + 18446744073709551472#64)).toNat +
      8 * (X.getMem (top + 18446744073709551480#64)).toNat)
    (hw : w.toNat = (X.getMem (top + 18446744073709551480#64)).toNat + 1) :
    MemOk env ret top regs m ((X.setMem a v).setMem (top + 18446744073709551480#64) w) ∧
      RV env m top ((X.setMem a v).setMem (top + 18446744073709551480#64) w) ∧
      env.next ((X.setMem a v).setMem (top + 18446744073709551480#64) w) = env.next X ∧
      ∀ c : Word, env.stackLimit.toNat ≤ (top + c).toNat → (X.setMem a v).getMem (top + c) = X.getMem (top + c) := by
  have hlay := env.layout
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hB
  have hnM := hM.1.2.1
  obtain ⟨hM1, hn1⟩ := hM.fresh (a := a) (v := v) hlim (by omega) (by omega)
  obtain ⟨hM2, hn2⟩ := hM1.slot (a := top + 18446744073709551480#64) (v := w) hlim (by tn) (by tn)
  have rd1 : ∀ c : Word, env.stackLimit.toNat ≤ (top + c).toNat → (X.setMem a v).getMem (top + c) =
      X.getMem (top + c) := fun c h => MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))
  have rd : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 192 → k ≠ 136 →
      ((X.setMem a v).setMem (top + 18446744073709551480#64) w).getMem (top + c) = X.getMem (top + c) :=
    fun c k hc' hk' h1 => by
      have e : (top + c).toNat = top.toNat - k := by rw [BitVec.toNat_add]; omega
      rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e]; tn))]
      exact rd1 c (by omega)
  refine ⟨hM2, ?_, by rw [hn2, hn1], rd1⟩
  unfold RV
  rw [rd 18446744073709551464#64 152 rfl (by omega) (by omega), rd 18446744073709551472#64 144 rfl (by omega)
    (by omega), MachineState.getMem_setMem_eq, hn2, hn1, hw]
  omega

set_option rv_sym.heap true in
/-- **The exit**: `roots`' header copied into the slot, the epilogue, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 192 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hwS : InWin env (regs .x10) 24) (haS : (regs .x10).toNat % 8 = 0)
    (hoS : env.Owned m top (regs .x10) 24) :
    ∀ R M, FinInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 278, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, hlen, ⟨hF, -, -, -⟩, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := id hinv
  have hlS := hwS.lt
  rv_introT hinv
  rv_symT hp with [(by omega : env.stackLimit.toNat + 192 ≤ top.toNat)]
  all_goals rw [hinv_2]
  · have o : ∀ k : Nat, k < 24 → SretOut Layouts.Vec.byteSize regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      ⟨by rw [toNat_add_ofNat (by omega)]; omega,
        by rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Vec.byteSize]; omega⟩
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF (by simpa using o 0 (by omega))
      (hwS.ne_next (Nat.le_refl _) (by omega))) (o 8 (by omega)) (hwS.ne_next_add (o := 8) (by omega)))
      (o 16 (by omega)) (hwS.ne_next_add (o := 16) (by omega))
  all_goals
    have hB : BufT env M (M.getMem (top + 18446744073709551464#64)) (M.getMem (top + 18446744073709551472#64)) 8 :=
      .inr ⟨hb5, by unfold Env.Live; omega, hb7⟩
  · exact (vecT_stores hwS haS hB hb3 hb2).1.2.1.2.2.1
  · exact (vecT_stores hwS haS hB hb3 hb2).1.2.1.2.2.2
  · rw [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_eq]; exact hb2
  · rw [(vecT_stores hwS haS hB hb3 hb2).2]; exact hlen
  · exact .inr (by rw [MachineState.getMem_setMem_eq]; exact hb4)


/-- Before the push (instruction 84), `k` words in the layer at `p`: `RInv`'s registers, `roots`' pointer in `x20`
    and room in it; the passes done at `sp + 0x18`, `p + 8` at `sp + 8`, the slot's address at `sp`. -/
def PInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (p : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x18 = regs .x11 ∧ R .x20 = M.getMem (top + 18446744073709551472#64) ∧
    R .x22 = p ∧ R .x25 = M.getMem (top + 18446744073709551480#64) ∧ (R .x26).toNat = k ∧ (R .x27).toNat = 8 * k ∧
    (R .x8).toNat = 8 * (M.getMem (top + 18446744073709551480#64)).toNat ∧
    (M.getMem (top + 18446744073709551480#64)).toNat + k = (regs .x11).toNat + 1 ∧ 1 ≤ k ∧
    (M.getMem (top + 18446744073709551480#64)).toNat < (M.getMem (top + 18446744073709551464#64)).toNat ∧
    (M.getMem (top + 18446744073709551448#64)).toNat + k = (regs .x11).toNat + 1 ∧
    M.getMem (top + 18446744073709551432#64) = p + 8#64 ∧ M.getMem (top + 18446744073709551424#64) = regs .x10 ∧
    (regs .x11).toNat * 8 < 2 ^ 63 ∧ Lay env m (regs .x11).toNat p M ∧ MemOk env ret top regs m M ∧ RV env m top M

set_option rv_sym.heap true in
/-- **The push** (instruction 84): the layer's first word stored after `roots`' elements, its length raised; then
    the passes' head, one word fewer, or the exit. -/
theorem push (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 192 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {lp : Word} {k : Nat}
    (hfin : ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 278, ret, top⟩ :: rest, R, M⟩)
    (hloop : ∀ R M, 2 ≤ k → OInv env ret top regs m lp (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 184, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, PInv env ret top regs m lp k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 168, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hlay := env.layout
  obtain ⟨-, -, -, -, -, h26, h27, h8, hlk, hk1, hlt, h448, h432, h424, hn63, hLay, hM, hB⟩ := id hI
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := id hB
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  have hA : (M.getMem (top + 18446744073709551472#64) + R .x8).toNat =
      (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551480#64)).toNat := by
    rw [BitVec.toNat_add, h8]; omega
  have hw : (M.getMem (top + 18446744073709551480#64) + 1#64).toNat =
      (M.getMem (top + 18446744073709551480#64)).toNat + 1 := toNat_add_ofNat (by omega)
  rv_introT hI
  rv_symT hp stop [184, 278] with [hlim]
  all_goals
    obtain ⟨hM2, hB2, hnx, rdh⟩ := push_ok (v := R .x9) hlim hM hB hlt hA hw
  · refine hfin _ _ ⟨rfl, ?_, ?_, hM2, hB2⟩
    · rw [MachineState.getMem_setMem_ne (ne_off (by decide)), rdh 18446744073709551424#64 (by tn)]
      exact h424
    · have h48 := congrArg BitVec.toNat hc
      rw [MachineState.getMem_setMem_eq, hw]; omega
  · have hk2 : 2 ≤ k := by
      refine Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq ?_)
      omega
    refine hloop _ _ hk2 ⟨rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, hn63,
      hLay.mono (by rw [hnx]), hM2, hB2⟩
    all_goals try simp only [Tactic.rf]
    · rw [MachineState.getMem_setMem_ne (ne_off (by decide)), rdh 18446744073709551472#64 (by tn)]
    · rw [MachineState.getMem_setMem_eq]
    · rw [BitVec.toNat_add, h26, BitVec.toNat_ofNat]; omega
    · rw [BitVec.toNat_add, h27, BitVec.toNat_ofNat]; omega
    · omega
    · rw [MachineState.getMem_setMem_eq, hw]; omega
    · rw [MachineState.getMem_setMem_ne (ne_off (by decide)), rdh 18446744073709551432#64 (by tn)]
      exact h432
    · rw [MachineState.getMem_setMem_ne (ne_off (by decide)), rdh 18446744073709551424#64 (by tn)]
      exact h424

set_option rv_sym.heap true in
/-- **A pass's end** (instruction 120): the layer's first word read, the rest moved down one word (`memmove`),
    `roots` grown if full (`grow_one`); then the push. -/
theorem rem (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM needG : Nat} (hnM : 192 + needM ≤ need) (hnG : 192 + needG ≤ need)
    (hmm : MemmoveSpecT env p L.memmove.idx needM) (hgo : GrowOneSpecT env 8 8 p L.growOne.idx needG)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {lp : Word} {k : Nat}
    (hpush : ∀ R M, PInv env ret top regs m lp k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 168, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, RInv env ret top regs m lp k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 240, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hlay := env.layout
  obtain ⟨-, -, -, -, h26, h27, h8, hlk, hk1, h456, h448, h440, h432, h424, hn63, hLay, hM, hB⟩ := id hI
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := id hB
  obtain ⟨hl1, hl2, hl3, hl4⟩ := id hLay
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  have hhe := hW.heapEnd_le
  have hn8 : (M.getMem (top + 18446744073709551440#64) + 18446744073709551608#64).toNat = 8 * k - 8 := by
    rw [BitVec.toNat_add, h440, BitVec.toNat_ofNat]; omega
  have e8 : (lp + 8#64).toNat = lp.toNat + 8 := toNat_add_ofNat (by omega)
  rv_introT hI
  rv_symT hp stop [168] with [hL, hlim] using [hmm, hgo]
  -- `memmove`'s precondition: the layer's words after the first, down one word
  · intro h; exact absurd h (by decide)
  · rw [hn8, h432]
    refine .inr ⟨.inl ⟨hl2, by omega⟩, .inl (by omega), ?_, .inl (by rw [e8]; omega)⟩
    rw [inWindow_iff, e8]; exact .inl ⟨by omega, by omega⟩
  all_goals
    obtain ⟨hM1, hB1, hL1, rd1⟩ := mv_ok (n := (regs .x11).toNat) hlim hM hB hLay hret1_14 (fun a ha => by
      simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte] at ha
      rw [toNat_alignToDword, hn8] at ha
      omega) keep1_1 hret1_19 hret1_15
  -- room
  · have r : ∀ c : Word, ∀ q, c.toNat + q = 2 ^ 64 → q ≤ 192 → m1.getMem (top + c) = M.getMem (top + c) :=
      fun c q hc' hq => rd1 c (by rw [BitVec.toNat_add]; omega)
    refine hpush _ _ ⟨rfl, rfl, ?_, rfl, ?_, h26, h27, ?_, ?_, hk1, ?_, ?_, ?_, ?_, hn63, hL1, hM1, hB1⟩
    all_goals try simp only [Tactic.rf]
    · rw [r 18446744073709551472#64 144 rfl (by omega)]; exact h456
    · rw [r 18446744073709551480#64 136 rfl (by omega)]
    · rw [r 18446744073709551480#64 136 rfl (by omega)]; exact h8
    · rw [r 18446744073709551480#64 136 rfl (by omega)]; exact hlk
    · rw [r 18446744073709551480#64 136 rfl (by omega), r 18446744073709551464#64 152 rfl (by omega)]
      exact Nat.lt_of_le_of_ne hb2 fun h => hc (BitVec.eq_of_toNat_eq h)
    · rw [r 18446744073709551448#64 168 rfl (by omega)]; exact h448
    · rw [r 18446744073709551432#64 184 rfl (by omega)]; exact h432
    · rw [r 18446744073709551424#64 192 rfl (by omega)]; exact h424
  -- full: `grow_one`'s precondition
  all_goals try simp only [(hdr top).1, (hdr top).2]
  · obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hB1
    exact .inr (by unfold Env.Live; omega)
  · exact hB1.2.2.1
  · obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hB1
    exact .inr ⟨c5, by unfold Env.Live; omega, c7⟩
  · exact hB1.2.2.1
  -- grown
  · obtain ⟨hM2, hB2, hlt2, hn12, rd2⟩ := grow_ok hlim hM1 hB1 rfl hret2_14 keep2_1 hret2_23 hret2_15 hret2_16
      hret2_17 hret2_21 hret2_22
    have r : ∀ c : Word, ∀ q, c.toNat + q = 2 ^ 64 → q ≤ 192 → q ≠ 152 → q ≠ 144 →
        m2.getMem (top + c) = M.getMem (top + c) := fun c q hc' hq h1 h2 => by
      have e : (top + c).toNat = top.toNat - q := by rw [BitVec.toNat_add]; omega
      rw [rd2 c (by omega) (by omega) (by omega), rd1 c (by omega)]
    refine hpush _ _ ⟨rfl, rfl, rfl, rfl, ?_, h26, h27, ?_, ?_, hk1, hlt2, ?_, ?_, ?_, hn63, hL1.mono hn12, hM2,
      hB2⟩
    all_goals try simp only [Tactic.rf]
    · rw [r 18446744073709551480#64 136 rfl (by omega) (by omega) (by omega)]
    · rw [r 18446744073709551480#64 136 rfl (by omega) (by omega) (by omega)]; exact h8
    · rw [r 18446744073709551480#64 136 rfl (by omega) (by omega) (by omega)]; exact hlk
    · rw [r 18446744073709551448#64 168 rfl (by omega) (by omega) (by omega)]; exact h448
    · rw [r 18446744073709551432#64 184 rfl (by omega) (by omega) (by omega)]; exact h432
    · rw [r 18446744073709551424#64 192 rfl (by omega) (by omega) (by omega)]; exact h424

set_option rv_sym.heap true in
/-- **The layer's loop**, from its head: a word `v` of the layer replaced by `v^2 + root * v` (`spread`, `reduce`,
    `base_mul`), then back to the head or on to `rem`; one word fewer left. -/
theorem inner (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needB needS needR : Nat} (hnB : 192 + needB ≤ need) (hnS : 192 + needS ≤ need)
    (hnR : 192 + needR ≤ need) (hbm : Field.BaseMulT.specT env p L.baseMul.idx needB)
    (hsp : Field.SpreadT.specT env p L.spread.idx needS) (hrd : Field.ReduceT.specT env p L.reduce.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {lp : Word} {k : Nat}
    (hrem : ∀ R M, RInv env ret top regs m lp k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 240, ret, top⟩ :: rest, R, M⟩) :
    ∀ j R M, IInv env ret top regs m lp k j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 208, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (IInv env ret top regs m lp k) fun j R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨-, -, -, -, h26, h27, h8, hlk, hk1, h456, h448, h440, h432, h424, hn63, hLay, hM, hB⟩, h9, h19, hj1,
    hjk⟩ := id hI
  obtain ⟨hl1, hl2, hl3, hl4⟩ := id hLay
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  rv_introT hI
  rv_symT hp stop [208, 240] with [hL, hlim] using [hbm, hsp, hrd]
  all_goals
    obtain ⟨hM1, hB1, hL1, rd1⟩ := call_ok hlim hM hB hLay hret1_14 keep1_1 hret1_18 hret1_15
    obtain ⟨hM2, hB2, hL2, rd2⟩ := call_ok hlim hM1 hB1 hL1 hret2_14 keep2_1 hret2_17 hret2_15
    obtain ⟨hM3, hB3, hL3, rd3⟩ := call_ok hlim hM2 hB2 hL2 hret3_14 keep3_1 hret3_17 hret3_15
    have hkn : k ≤ (regs .x11).toNat := by have := hB.1; omega
    have hL3' := hL3.2.2.1
    have hM4 := fun v => hM3.fresh (a := R .x9) (v := v) hlim (by omega) (by omega)
    have rd4 : ∀ v, ∀ c : Word, ∀ q, c.toNat + q = 2 ^ 64 → q ≤ 192 →
        (m3.setMem (R .x9) v).getMem (top + c) = M.getMem (top + c) := fun v c q hc' hq => by
      have e : (top + c).toNat = top.toNat - q := by rw [BitVec.toNat_add]; omega
      rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by have := hM3.1.2.1; omega)), rd3 c (by omega),
        rd2 c (by omega), rd1 c (by omega)]
    have hB4 := fun v => hB3.keep (X := m3.setMem (R .x9) v) (by rw [(hM4 v).2]) (by omega) fun a h1 h2 =>
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by have := hM3.1.2.1; omega))
    have hL4 := fun v => hL3.mono (X := m3.setMem (R .x9) v) (by rw [(hM4 v).2])
  -- back to the head
  · have hj2 : 2 ≤ j := by
      refine Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq ?_)
      rw [toNat_add_ofNat (by omega)]; omega
    refine ih (j - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, ?_, h26, h27, ?_, ?_, hk1, ?_, ?_, ?_, ?_, ?_, hn63, hL4 _,
      (hM4 _).1, hB4 _⟩, ?_, h19, by omega, by omega⟩
    all_goals try simp only [Tactic.rf]
    · rw [rd4 _ 18446744073709551480#64 136 rfl (by omega)]
    · rw [rd4 _ 18446744073709551480#64 136 rfl (by omega)]; exact h8
    · rw [rd4 _ 18446744073709551480#64 136 rfl (by omega)]; exact hlk
    · rw [rd4 _ 18446744073709551456#64 160 rfl (by omega), rd4 _ 18446744073709551472#64 144 rfl (by omega)]
      exact h456
    · rw [rd4 _ 18446744073709551448#64 168 rfl (by omega)]; exact h448
    · rw [rd4 _ 18446744073709551440#64 176 rfl (by omega)]; exact h440
    · rw [rd4 _ 18446744073709551432#64 184 rfl (by omega)]; exact h432
    · rw [rd4 _ 18446744073709551424#64 192 rfl (by omega)]; exact h424
    · rw [toNat_add_ofNat (by omega)]; omega
  -- the layer's last word: on to `rem`
  · refine hrem _ _ ⟨rfl, rfl, rfl, ?_, h26, h27, ?_, ?_, hk1, ?_, ?_, ?_, ?_, ?_, hn63, hL4 _, (hM4 _).1, hB4 _⟩
    all_goals try simp only [Tactic.rf]
    · rw [rd4 _ 18446744073709551480#64 136 rfl (by omega)]
    · rw [rd4 _ 18446744073709551480#64 136 rfl (by omega)]; exact h8
    · rw [rd4 _ 18446744073709551480#64 136 rfl (by omega)]; exact hlk
    · rw [rd4 _ 18446744073709551456#64 160 rfl (by omega), rd4 _ 18446744073709551472#64 144 rfl (by omega)]
      exact h456
    · rw [rd4 _ 18446744073709551448#64 168 rfl (by omega)]; exact h448
    · rw [rd4 _ 18446744073709551440#64 176 rfl (by omega)]; exact h440
    · rw [rd4 _ 18446744073709551432#64 184 rfl (by omega)]; exact h432
    · rw [rd4 _ 18446744073709551424#64 192 rfl (by omega)]; exact h424

set_option rv_sym.heap true in
/-- **The passes**, from their head: `roots`' last element read, the passes' count and the layer's size saved, then
    the layer's loop; `remove`'s `assert!` (an empty layer) never fails. One word fewer left after each pass. -/
theorem outer (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 192 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {lp : Word}
    (hin : ∀ k, (∀ R M, 2 ≤ k → OInv env ret top regs m lp (k - 1) R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 184, ret, top⟩ :: rest, R, M⟩) →
      ∀ j R M, IInv env ret top regs m lp k j R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 208, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, OInv env ret top regs m lp k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 184, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInv env ret top regs m lp) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, -, -, -, h26, h27, h12, hlk, hk1, h432, h424, hn63, hLay, hM, hB⟩ := id hI
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := id hB
  obtain ⟨hl1, hl2, hl3, hl4⟩ := id hLay
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  have hs3 : (M.getMem (top + 18446744073709551480#64) <<< 3).toNat =
      8 * (M.getMem (top + 18446744073709551480#64)).toNat := shl3 (by omega)
  have hA : (M.getMem (top + 18446744073709551472#64) + M.getMem (top + 18446744073709551480#64) <<< 3 +
      18446744073709551608#64).toNat = (M.getMem (top + 18446744073709551472#64)).toNat +
        8 * (M.getMem (top + 18446744073709551480#64)).toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hs3, BitVec.toNat_ofNat]; omega
  rv_introT hI
  rv_symT hp stop [208, 326] with [hlim]
  -- `remove(0)` of an empty layer: never
  · exfalso; zlen hc
  · obtain ⟨hM1, hB1, hn1, rd⟩ := slots3 (v1 := M.getMem (top + 18446744073709551472#64)) (v2 := R .x12 + 1#64)
      (v3 := R .x26 <<< 3) hlim hM hB
    have hkn : k ≤ (regs .x11).toNat := by omega
    refine hin k (fun R' M' h2 h' => ih (k - 1) R' M' (by omega) h') k _ _ ⟨⟨rfl, rfl, rfl, ?_, h26, h27, ?_, ?_,
      hk1, ?_, ?_, ?_, ?_, ?_, hn63, hLay.mono (by rw [hn1]), hM1, hB1⟩, ?_, ?_, hk1, Nat.le_refl _⟩
    all_goals try simp only [Tactic.rf]
    · rw [rd _ (by decide) (by decide) (by decide)]
    · rw [rd _ (by decide) (by decide) (by decide)]; exact hs3
    · rw [rd _ (by decide) (by decide) (by decide)]; exact hlk
    · rw [rd 18446744073709551472#64 (by decide) (by decide) (by decide),
        MachineState.getMem_setMem_ne (ne_off (by decide)), MachineState.getMem_setMem_ne (ne_off (by decide)),
        MachineState.getMem_setMem_eq]
    · rw [MachineState.getMem_setMem_ne (ne_off (by decide)), MachineState.getMem_setMem_eq,
        toNat_add_ofNat (by omega)]
      omega
    · rw [MachineState.getMem_setMem_eq, shl3 (by omega), h26]
    · rw [rd _ (by decide) (by decide) (by decide)]; exact h432
    · rw [rd _ (by decide) (by decide) (by decide)]; exact h424
    · rw [BitVec.toNat_add, h27]; omega

set_option rv_sym.heap true in
/-- **The fill loop**, from its head: `1 << i` stored at the cursor, then back to the head, or the last word
    `1 << log_n` stored and on to the passes' head (`log_n` words left); one word fewer left. -/
theorem fill (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 192 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {lp : Word}
    (hout : ∀ R M, OInv env ret top regs m lp (regs .x11).toNat R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 184, ret, top⟩ :: rest, R, M⟩) :
    ∀ j R M, FInv env ret top regs m lp j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 134, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (FInv env ret top regs m lp) fun j R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, -, -, -, h12, h12a, hj1, h11, h26, h480, h424, hn63, hLay, hM, hB⟩ := id hI
  obtain ⟨hl1, hl2, hl3, hl4⟩ := id hLay
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  have hs26 : (R .x26 <<< 3).toNat = 8 * (R .x26).toNat := shl3 (by omega)
  have hA26 : (lp + R .x26 <<< 3).toNat = lp.toNat + 8 * (R .x26).toNat := by
    rw [BitVec.toNat_add, hs26]; omega
  rv_introT hI
  rv_symT hp stop [134, 184] with [hlim]
  all_goals
    obtain ⟨hM1, hB1, hn1, rd1⟩ := heap_ok hlim hM hB (a := R .x11) (by omega) (by omega)
      (1#64 <<< (R .x12 &&& 63#64).toNat)
  -- back to the head
  · have hj2 : 2 ≤ j := by
      refine Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq ?_)
      rw [toNat_add_ofNat (by omega)]; omega
    refine ih (j - 1) _ _ (by omega) ⟨rfl, rfl, rfl, ?_, rfl, ?_, ?_, by omega, ?_, h26, ?_, ?_, hn63,
      hLay.mono (by rw [hn1]), hM1, hB1⟩
    all_goals try simp only [Tactic.rf]
    · rw [rd1 18446744073709551472#64 (by tn)]
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]; omega
    · rw [rd1 18446744073709551480#64 (by tn)]; exact h480
    · rw [rd1 18446744073709551424#64 (by tn)]; exact h424
  -- the last word `1 << log_n`: on to the passes' head
  · have hn12 := congrArg BitVec.toNat hc
    rw [toNat_add_ofNat (by omega)] at hn12
    obtain ⟨hM2, hB2, hn2, rd2⟩ := heap_ok hlim hM1 hB1 (a := lp + R .x26 <<< 3) (by rw [hA26]; omega)
      (by rw [hA26, hn1]; omega) (1#64 <<< (regs .x11 &&& 63#64).toNat)
    obtain ⟨hM3, hn3⟩ := hM2.slot (a := top + 18446744073709551432#64) (v := lp + 8#64) hlim (by tn) (by tn)
    have e432 : (top + 18446744073709551432#64).toNat = top.toNat - 184 := by tn
    have hB3 := hB2.keep (X := ((MachineState.setMem M (R .x11) (1#64 <<< (R .x12 &&& 63#64).toNat)).setMem
      (lp + R .x26 <<< 3) (1#64 <<< (regs .x11 &&& 63#64).toNat)).setMem (top + 18446744073709551432#64) (lp + 8#64))
      (by rw [hn3]) (by omega) fun a h1 h2 => MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))
    refine hout _ _ ⟨rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, hn63,
      hLay.mono (by rw [hn3, hn2, hn1]), hM3, hB3⟩
    all_goals try simp only [Tactic.rf]
    · rw [MachineState.getMem_setMem_ne (ne_off (by decide)), rd2 18446744073709551472#64 (by tn),
        rd1 18446744073709551472#64 (by tn)]
    · rw [MachineState.getMem_setMem_ne (ne_off (by decide)), rd2 18446744073709551480#64 (by tn),
        rd1 18446744073709551480#64 (by tn), h480]
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by rw [hs26]; omega), hs26]; omega
    · simp
    · rw [MachineState.getMem_setMem_ne (ne_off (by decide)), rd2 18446744073709551480#64 (by tn),
        rd1 18446744073709551480#64 (by tn), h480]
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [MachineState.getMem_setMem_eq]
    · rw [MachineState.getMem_setMem_ne (ne_off (by decide)), rd2 18446744073709551424#64 (by tn),
        rd1 18446744073709551424#64 (by tn), h424]

set_option hygiene false in
/-- One of `reserve`'s preconditions on the layer's header (`log_n` words at `p`, `Lay` unless none). -/
local macro "rpre" : tactic => `(tactic| (
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, bc, bp, h488]
    first
      | exact hn63
      | rcases hLay with h0 | ⟨l1, l2, l3, l4⟩
        · exact .inl h0
        · first
            | exact .inr (by unfold Env.Live; omega)
            | exact .inr ⟨l2, by unfold Env.Live; omega, l4⟩))

set_option rv_sym.heap true in
/-- **After the allocations** (instruction 54): `reserve(log_n)` of the layer (it has the room), then the fill loop, or
    for `log_n = 1` the passes' head, or for `log_n = 0` the exit. -/
theorem mid (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR : Nat} (hnR : 192 + needR ≤ need) (hres : Runtime.ReserveT.ReserveSpecT env 8 8 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hfin : ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 278, ret, top⟩ :: rest, R, M⟩)
    (hfill : ∀ lp j R M, FInv env ret top regs m lp j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 134, ret, top⟩ :: rest, R, M⟩)
    (hout : ∀ lp R M, OInv env ret top regs m lp (regs .x11).toNat R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 184, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, MInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 108, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hlay := env.layout
  obtain ⟨-, -, -, -, h424, h488, h504, h480, hn63, hLay, hM, hB⟩ := id hI
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := id hB
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  obtain ⟨bc, bp, bC, bP, bL⟩ := hdrL top M
  rv_introT hI
  rv_symT hp stop [134, 184, 278] with [hL, hlim] using [hres]
  -- `reserve(0)`'s precondition (the layer's header, empty)
  iterate 4 rpre
  -- `log_n = 0`: the exit
  · have h0 : (regs .x11).toNat = 0 := by have := congrArg BitVec.toNat hc; simpa using this
    obtain ⟨hM1, hB1, -, rd1⟩ := res_ok hlim hM hB hret1_14 (fun a ha => by
      simp only [GrowOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, bc, bp] at ha
      exact ha) keep1_1 hret1_25 hret1_15
    refine hfin _ _ ⟨rfl, ?_, ?_, hM1, hB1⟩
    · rw [rd1 18446744073709551424#64 (by tn) (by tn) (by tn)]; exact h424
    · rw [rd1 18446744073709551480#64 (by tn) (by tn) (by tn), h480, h0]; rfl
  -- `reserve(log_n)`'s precondition
  iterate 4 rpre
  all_goals
    obtain ⟨hM2, hB2, hn2, rd2⟩ := res_ok hlim hM hB hret2_14 (fun a ha => by
      simp only [GrowOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, bc, bp] at ha
      exact ha) keep2_1 hret2_25 hret2_15
    have hn0 : (regs .x11).toNat ≠ 0 := fun h => hc_1 (BitVec.eq_of_toNat_eq (by simpa using h))
    obtain ⟨l1, l2, l3, l4⟩ := hLay.resolve_left hn0
    have h496 : m2.getMem (top + 18446744073709551496#64) = M.getMem (top + 18446744073709551496#64) := by
      have := (hret2_17 (by rw [bC, bL, h488, h504]; simp)).2
      rwa [(hdrL top m2).2.2.2.1, bP] at this
    have g504 : m2.getMem (top + 18446744073709551504#64) = 0#64 := by
      rw [rd2 18446744073709551504#64 (by tn) (by tn) (by tn)]; exact h504
    have hnm2 := hM2.1.2.1
    have hL2 : Lay env m (regs .x11).toNat (m2.getMem (top + 18446744073709551496#64)) m2 :=
      ⟨by rw [h496]; exact l1, by rw [h496]; exact l2, by rw [h496]; omega, by rw [h496]; exact l4⟩
  -- `log_n = 1`: the last word `1 << 1` stored, on to the passes' head
  · rw [h496, g504, BitVec.zero_shiftLeft, BitVec.add_zero]; exact hW.heapObj l2 (by omega)
  · rw [h496, g504, BitVec.zero_shiftLeft, BitVec.add_zero]; exact l4
  · have h1 : (regs .x11).toNat = 1 := by have := congrArg BitVec.toNat hc; simpa using this
    have hlp : (m2.getMem (top + 18446744073709551496#64) + m2.getMem (top + 18446744073709551504#64) <<< 3) =
        m2.getMem (top + 18446744073709551496#64) := by rw [g504, BitVec.zero_shiftLeft, BitVec.add_zero]
    rw [hlp]
    obtain ⟨hM3, hB3, hn3, rd3⟩ := heap_ok hlim hM2 hB2 (a := m2.getMem (top + 18446744073709551496#64))
      (by rw [h496]; omega) (by rw [h496]; omega) (1#64 <<< (regs .x11 &&& 63#64).toNat)
    obtain ⟨hM4, hn4⟩ := hM3.slot (a := top + 18446744073709551432#64)
      (v := m2.getMem (top + 18446744073709551496#64) + 8#64) hlim (by tn) (by tn)
    have e432 : (top + 18446744073709551432#64).toNat = top.toNat - 184 := by tn
    have hB4 := hB3.keep (X := (m2.setMem (m2.getMem (top + 18446744073709551496#64))
      (1#64 <<< (regs .x11 &&& 63#64).toNat)).setMem (top + 18446744073709551432#64)
        (m2.getMem (top + 18446744073709551496#64) + 8#64)) (by rw [hn4]) (by omega) fun a h1 h2 =>
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))
    have rd : ∀ c : Word, c ≠ 18446744073709551432#64 → ∀ q, c.toNat + q = 2 ^ 64 → q ≤ 192 → q ≠ 128 →
        q ≠ 120 → ((m2.setMem (m2.getMem (top + 18446744073709551496#64))
          (1#64 <<< (regs .x11 &&& 63#64).toNat)).setMem (top + 18446744073709551432#64)
            (m2.getMem (top + 18446744073709551496#64) + 8#64)).getMem (top + c) = M.getMem (top + c) :=
      fun c hc' q hq hq1 hq2 hq3 => by
        have e : (top + c).toNat = top.toNat - q := by rw [BitVec.toNat_add]; omega
        rw [MachineState.getMem_setMem_ne (ne_off hc'), rd3 c (by omega), rd2 c (by omega) (by omega) (by omega)]
    refine hout (m2.getMem (top + 18446744073709551496#64)) _ _ ⟨rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, by omega, ?_,
      ?_, hn63, hL2.mono (by rw [hn4, hn3]), hM4, hB4⟩
    all_goals try simp only [Tactic.rf]
    · rw [rd _ (by decide) 144 rfl (by omega) (by omega) (by omega)]
    · rw [rd _ (by decide) 136 rfl (by omega) (by omega) (by omega), h480]
    · rw [g504, h1]; rfl
    · rw [g504, h1]; rfl
    · rw [h1]; rfl
    · rw [rd _ (by decide) 136 rfl (by omega) (by omega) (by omega), h480, h1]; rfl
    · rw [MachineState.getMem_setMem_eq]
    · rw [rd _ (by decide) 192 rfl (by omega) (by omega) (by omega)]; exact h424
  -- `log_n ≥ 2`: the fill loop
  · have h1 : (regs .x11).toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
    refine hfill (m2.getMem (top + 18446744073709551496#64)) ((regs .x11).toNat - 1) _ _ ⟨rfl, rfl, rfl, ?_, rfl, ?_,
      ?_, by omega, ?_, ?_, ?_, ?_, hn63, hL2, hM2, hB2⟩
    all_goals try simp only [Tactic.rf]
    · rw [rd2 18446744073709551472#64 (by tn) (by tn) (by tn)]
    · simp only [BitVec.toNat_ofNat]; omega
    · simp only [BitVec.toNat_ofNat]; omega
    · rw [g504, BitVec.zero_shiftLeft, BitVec.add_zero]; simp only [BitVec.toNat_ofNat]
    · rw [g504, BitVec.zero_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · rw [rd2 18446744073709551480#64 (by tn) (by tn) (by tn)]; exact h480
    · rw [rd2 18446744073709551424#64 (by tn) (by tn) (by tn)]; exact h424

set_option rv_sym.heap true in
/-- **`subspace_roots` is total**: `roots = [1]` allocated (`panic_nounwind_fmt` when `alloc` fails), `log_n`'s size
    checked (`handle_error`), the layer allocated (`handle_error` when `alloc` fails), then `mid`. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR needA needH needB needS needD needM needG needP : Nat} (hnR : 192 + needR ≤ need)
    (hnA : 192 + needA ≤ need) (hnH : 192 + needH ≤ need) (hnB : 192 + needB ≤ need) (hnS : 192 + needS ≤ need)
    (hnD : 192 + needD ≤ need) (hnM : 192 + needM ≤ need) (hnG : 192 + needG ≤ need) (hnP : 192 + needP ≤ need)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 8 p L.reserve.idx needR)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hhe : Aborts env p L.handleError.idx needH) (hbm : Field.BaseMulT.specT env p L.baseMul.idx needB)
    (hsp : Field.SpreadT.specT env p L.spread.idx needS) (hrd : Field.ReduceT.specT env p L.reduce.idx needD)
    (hmm : MemmoveSpecT env p L.memmove.idx needM) (hgo : GrowOneSpecT env 8 8 p L.growOne.idx needG)
    (hpn : Aborts env p L.panicNounwindFmt.idx needP) :
    specT env p i need := by
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 192 ≤ top.toNat)]
  have hfin := fin_ok env p i L hp (by omega) hk hpre_3 hpre_10 hpre_11 hpre_6 hpre_7 (hpre_2 ▸ ⟨hpre_8, hpre_9⟩)
  have hout := fun lp => outer env p i L hp (by omega) hpre_3 hpre_10 hpre_11 (lp := lp) fun k hl =>
    inner env p i L hp hL hnB hnS hnD hbm hsp hrd hpre_3 hpre_10 hpre_11
      (rem env p i L hp hL hnM hnG hmm hgo hstop hpre_3 hpre_10 hpre_11
        (push env p i L hp (by omega) hpre_3 hpre_10 hpre_11 hfin hl))
  have hmid := mid env p i L hp hL hnR hres hstop hpre_3 hpre_10 hpre_11 hfin
    (fun lp => fill env p i L hp (by omega) hpre_3 hpre_10 hpre_11 (hout lp _)) fun lp => hout lp _
  clear hout
  clear hfin
  rv_symT hp stop [108] with [hL, (by omega : env.stackLimit.toNat + 192 ≤ top.toNat)] using [hac, hhe, hpn]
  all_goals
    have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
    have hov := ovf hc_2
    have e8 := shl3 (x := regs .x11) (by omega)
    have hn1 := hret1_14.1
    have hn1' := hret1_14.2.1
    have hge := hpre_11.next_ge
    have hlay := env.layout
  -- `log_n = 0`
  · have h0 : (regs .x11).toNat = 0 := by have := congrArg BitVec.toNat hc; rw [e8] at this; simpa using this
    refine hmid _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, .inl h0, ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rv_closeT
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq, next_stk hlim]
    have h18 := hret1_18
    simp only [BitVec.toNat_ofNat] at h18
    rw [Tactic.next_setMem (Tactic.ne_of_toNat (by omega))]
    simp only [BitVec.toNat_ofNat]; omega
  · rw [e8]; omega
  -- `log_n > 0`: the layer allocated
  · have hn3 := hret3_14.1
    have hn3' := hret3_14.2.1
    have hs3 := hret3_18
    rw [e8] at hs3
    refine hmid _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, .inr ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rv_closeT
    have le : ∀ c : Word, 2 ^ 64 - 192 ≤ c.toNat → top + 18446744073709551424#64 ≤ top + c := fun c hc =>
      Tactic.le_of_toNat (by rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; have := c.isLt; omega)
    simp (disch := decide) only [getMem_setMem_off, next_stk hlim]
    rw [keep3_1 (top + 18446744073709551472#64) (le _ (by decide)),
      keep3_1 (top + 18446744073709551464#64) (le _ (by decide))]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
    have h18 := hret1_18
    simp only [BitVec.toNat_ofNat] at h18 ⊢
    omega

end Rv64mc.Proof.Whir.SubspaceRootsT

/-- info: 'Rv64mc.Proof.Whir.SubspaceRootsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.SubspaceRootsT.total
