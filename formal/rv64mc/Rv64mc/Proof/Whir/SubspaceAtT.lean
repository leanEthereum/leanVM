/-
  Rv64mc.Proof.Whir.SubspaceAtT

  `<verifier::whir::Subspace>::at(&self, x)` is total (`specT`): from a result's slot of `24` bytes owned, in a window,
  8-byte aligned, and a `Subspace` owned, in a window, 8-byte aligned, whose two vectors (`roots` at `0`, `inverses`
  at `24`) are `VecReprT.VecT` (`PreT`), it returns with the slot a vector of words (`VecT`) whose length is the
  shorter of the two (`min`, the `zip` the code walks), its buffer allocated since the entry unless it has no
  capacity, writing at most the slot besides what it allocates (`SretOut`, the partial contract's), or the run ends
  with `a0 = 2` where `alloc` or its `handle_error` does. Safety only: the partial contract's values
  (`Spec/Whir/Subspace.lean`'s `atSpec`, `Model.SubspaceRust.at`) are owed. It has no partial proof (class C).

  The vector is allocated with capacity `roots.len()`, at least the zip's length, so `RawVec<K>::grow_one` is never
  reached: its call is refuted, not stepped. Cut after the allocation (instruction 62, `mid_ok`, `MInv`), at the
  loop's head (instruction 122, `loop`: `Total.loop` with the elements left as the measure) and at the exit
  (instruction 152, `fin_ok`). The memory facts the parts keep
  (`Inv`: the header, the frame, the saved registers' slots) are carried across each call of `base_mul`, `spread`
  and `reduce` (`Inv.call`) and across the element's two stores (`Inv.push`) by lemmas.

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `Saved`, `Inv`, `Src`, `LInv`, `FinInv`, `MInv`

  ## Main results

  * `Inv.call`, `Inv.push`, `fin_ok`, `loop`, `src_of`, `mid_ok`, `total`
-/

import Rv64mc.Proof.Field.BaseMulT
import Rv64mc.Proof.Field.ReduceT
import Rv64mc.Proof.Field.SpreadT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Core.AbortStop
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Proof.Whir.VecWordT
import Rv64mc.Spec.Whir.Subspace
import Rv64mc.Gen.Tmpl.Verifier.Whir.Subspace.At

namespace Rv64mc.Proof.Whir.SubspaceAtT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Whir
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Whir.VecWordT (vecT_stores shl3)
open Rv64mc.Proof.Transcript (getMem_setMem_off)
open Rv64mc.Gen.Verifier.Whir.Subspace.At (Link tmpl)

/-- The total precondition: the result's slot (`24` bytes) in a window, 8-byte aligned, owned; the `Subspace` at
    `a1` in a window, 8-byte aligned, owned, its `roots` and `inverses` vectors of words. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 24 ∧
    InWin env (regs .x11) 48 ∧ (regs .x11).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x11) 48 ∧
    VecT env m (regs .x11) 8 ∧ VecT env m (regs .x11 + 24#64) 8

/-- The total postcondition: the slot a vector of words as long as the shorter of `roots` and `inverses`, its buffer
    allocated since the entry unless it has no capacity. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 8 ∧
    (vecLen m' (regs .x10)).toNat = min (m.getMem (regs .x11 + 16#64)).toNat (m.getMem (regs .x11 + 40#64)).toNat ∧
    (vecCap m' (regs .x10) = 0#64 ∨ (env.next m).toNat ≤ (vecPtr m' (regs .x10)).toNat)

/-- **The total contract of `Subspace::at`**: `PreT` to `PostT`, writing at most the slot (`SretOut`, the partial
    contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (SretOut Layouts.Vec.byteSize) (Stop := AbortStop)

/-- The saved registers' twelve slots. -/
def Saved (ret top : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26

/-- What every part keeps of the memory: the frame, the code, the static data, the saved registers' slots, and the
    vector's header (`sp + 8`: capacity, pointer, length): its buffer `BufT`, of fewer than `2^63` bytes, allocated
    since the entry, its capacity at least `n`, its length `len`. -/
def Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (n : Nat) (len : Word)
    (M : MachineState) : Prop :=
  env.Frame top (SretOut Layouts.Vec.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧ Saved ret top regs M ∧
    BufT env M (M.getMem (top + 18446744073709551496#64)) (M.getMem (top + 18446744073709551504#64)) 8 ∧
    (M.getMem (top + 18446744073709551496#64)).toNat * 8 < 2 ^ 63 ∧
    n ≤ (M.getMem (top + 18446744073709551496#64)).toNat ∧
    (M.getMem (top + 18446744073709551496#64) = 0#64 ∨
      (env.next m).toNat ≤ (M.getMem (top + 18446744073709551504#64)).toNat) ∧
    M.getMem (top + 18446744073709551512#64) = len

/-- The two buffers the loop reads, `n` words each, allocated before the entry, 8-byte aligned. -/
def Src (env : Env) (m : MachineState) (n : Nat) (rp ip : Word) : Prop :=
  0x10000000 ≤ rp.toNat ∧ rp.toNat % 8 = 0 ∧ rp.toNat + 8 * n ≤ (env.next m).toNat ∧
    0x10000000 ≤ ip.toNat ∧ ip.toNat % 8 = 0 ∧ ip.toNat + 8 * n ≤ (env.next m).toNat

/-- The loop's head (instruction 122), `k` elements left, at least one: the stack pointer, the slot's address, the
    buffer and capacity in `x18`, `x21`, the length in `x23`, its offset in `x22`, `8 n` in `x26`, the two read
    buffers in `x24`, `x25`, `x27` (not saved). -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (n : Nat) (rp ip : Word) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551488#64 ∧ R .x8 = regs .x10 ∧
    R .x18 = M.getMem (top + 18446744073709551504#64) ∧ R .x21 = M.getMem (top + 18446744073709551496#64) ∧
    R .x24 = rp ∧ R .x25 = ip ∧ R .x27 = regs .x27 ∧ (R .x22).toNat = 8 * (R .x23).toNat ∧ (R .x26).toNat = 8 * n ∧
    (R .x23).toNat + k = n ∧ 1 ≤ k ∧ Inv env ret top regs m n (R .x23) M ∧ Src env m n rp ip

/-- The exit (instruction 152): the stack pointer, the slot's address, `x27` (not saved), `Inv` at the length
    `n`. -/
def FinInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (n : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551488#64 ∧ R .x8 = regs .x10 ∧ R .x27 = regs .x27 ∧ n < 2 ^ 64 ∧
    Inv env ret top regs m n (BitVec.ofNat 64 n) M

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- The saved registers' slots, in a memory that keeps the words `top - c` for `8 ≤ c ≤ 96`. -/
theorem Saved.keep {ret top : Word} {regs : Reg → Word} {M M' : MachineState} (h : Saved ret top regs M)
    (e : ∀ c : Nat, 8 ≤ c → c ≤ 96 → M'.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) =
      M.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c))) : Saved ret top regs M' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨(e 8 (by omega) (by omega)).trans h1, (e 16 (by omega) (by omega)).trans h2,
    (e 24 (by omega) (by omega)).trans h3, (e 32 (by omega) (by omega)).trans h4,
    (e 40 (by omega) (by omega)).trans h5, (e 48 (by omega) (by omega)).trans h6,
    (e 56 (by omega) (by omega)).trans h7, (e 64 (by omega) (by omega)).trans h8,
    (e 72 (by omega) (by omega)).trans h9, (e 80 (by omega) (by omega)).trans h10,
    (e 88 (by omega) (by omega)).trans h11, (e 96 (by omega) (by omega)).trans h12⟩

/-- **`Inv` across a call that writes nothing outside its stack and its allocations**, from a stack top at or below
    the frame's. -/
theorem Inv.call {env : Env} {ret top top' : Word} {regs : Reg → Word} {m M m1 : MachineState} {n : Nat}
    {len : Word} (h : Inv env ret top regs m n len M) (hlim : env.stackLimit.toNat ≤ top'.toNat)
    (htop : top'.toNat + 128 ≤ top.toNat) (hf : env.Frame top' Tactic.F M m1) (hc : m1.code = M.code)
    (hs : env.Static m1) : Inv env ret top regs m n len m1 := by
  obtain ⟨hF, hcM, -, hSv, hb, hcap, hn, hfr, hl⟩ := h
  have e : ∀ a : Word, top.toNat - 128 ≤ a.toNat → m1.getMem a = M.getMem a := fun a ha =>
    hf.getMem_above hlim (by omega) id
  have e120 := e (top + 18446744073709551496#64) (by tn)
  have e112 := e (top + 18446744073709551504#64) (by tn)
  refine ⟨Env.Frame.trans hF hf (by omega) fun _ h => h.elim, hc.trans hcM, hs,
    hSv.keep fun c hc0 hc1 => e _ (by tn), ?_, ?_, ?_, ?_, ?_⟩
  · rw [e120, e112]; exact hb.mono hf.1
  · rw [e120]; exact hcap
  · rw [e120]; exact hn
  · rw [e120, e112]; exact hfr
  · rw [e _ (by tn)]; exact hl

/-- **`Inv` after one element pushed**: a word stored at the buffer's slot `len` (the buffer's address `q`), below
    `n`, then the length `len + 1` stored. -/
theorem Inv.push {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {n : Nat}
    {len v off q : Word} (h : Inv env ret top regs m n len M) (hlim : env.stackLimit.toNat + 128 ≤ top.toNat)
    (hq : M.getMem (top + 18446744073709551504#64) = q) (hlt : len.toNat < n) (hoff : off.toNat = 8 * len.toNat) :
    Inv env ret top regs m n (len + 1#64) ((M.setMem (q + off) v).setMem (top + 18446744073709551512#64)
      (len + 1#64)) := by
  subst hq
  obtain ⟨hF, hcM, hs, hSv, hb, hcap, hn, hfr, hl⟩ := h
  have hlay := env.layout
  have hnM := hF.2.1
  have hcap0 : (M.getMem (top + 18446744073709551496#64)).toNat ≠ 0 := by omega
  obtain ⟨hp0, hpl, hpa⟩ := hb.resolve_left hcap0
  have hfr' := hfr.resolve_left fun h0 => hcap0 (by rw [h0]; rfl)
  unfold Env.Live at hpl
  have hA : (M.getMem (top + 18446744073709551504#64) + off).toNat =
      (M.getMem (top + 18446744073709551504#64)).toNat + 8 * len.toNat := by
    rw [BitVec.toNat_add, hoff]; omega
  have hna : M.getMem (top + 18446744073709551504#64) + off ≠ env.nextAddr := Tactic.ne_of_toNat (by omega)
  have hns : top + 18446744073709551512#64 ≠ env.nextAddr := Tactic.ne_of_toNat (by tn)
  have rd : ∀ c : Word, c ≠ 18446744073709551512#64 → env.stackLimit.toNat ≤ (top + c).toNat →
      ((M.setMem (M.getMem (top + 18446744073709551504#64) + off) v).setMem
        (top + 18446744073709551512#64) (len + 1#64)).getMem (top + c) = M.getMem (top + c) := fun c hc h1 => by
    rw [MachineState.getMem_setMem_ne (fun he => hc ((BitVec.add_right_inj top).1 he)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))]
  have hn' : env.next ((M.setMem (M.getMem (top + 18446744073709551504#64) + off) v).setMem
      (top + 18446744073709551512#64) (len + 1#64)) = env.next M := by
    rw [Tactic.next_setMem hns, Tactic.next_setMem hna]
  have r120 := rd 18446744073709551496#64 (by decide) (by tn)
  have r112 := rd 18446744073709551504#64 (by decide) (by tn)
  refine ⟨?_, by simp only [MachineState.code_setMem]; exact hcM, ?_, hSv.keep fun c hc0 hc1 => rd _ (fun he => by
      have := congrArg BitVec.toNat he; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega) (by tn),
    by rw [r120, r112]; exact hb.mono (by rw [hn']), by rw [r120]; exact hcap, by rw [r120]; exact hn,
    by rw [r120, r112]; exact hfr, MachineState.getMem_setMem_eq⟩
  · exact Tactic.frame_slot (Tactic.frame_fresh hF rfl (by omega) (by omega)) (by tn) (by tn)
  · exact Tactic.static_store (Tactic.static_store hs (by omega)) (by tn)

/-- A word of the frame read through an element's store into the heap and the length's store. -/
theorem rd_push {env : Env} {M : MachineState} {top b x v w : Word} (hb : b.toNat < env.heapEnd.toNat)
    (hx : env.stackLimit.toNat ≤ x.toNat) (hne : x ≠ top + 18446744073709551512#64) :
    ((M.setMem b v).setMem (top + 18446744073709551512#64) w).getMem x = M.getMem x := by
  have := env.layout
  rw [MachineState.getMem_setMem_ne hne, MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))]

set_option rv_sym.heap true in
/-- **The exit**: the vector's header copied into the slot, the epilogue, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 128 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hwS : InWin env (regs .x10) 24) (haS : (regs .x10).toNat % 8 = 0)
    (hoS : env.Owned m top (regs .x10) 24)
    {n' : Nat} (hmin : min (m.getMem (regs .x11 + 16#64)).toNat (m.getMem (regs .x11 + 40#64)).toNat = n') :
    ∀ R M, FinInv env ret top regs m n' R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 152, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, -, hn64, hF, -, -, -, hb, hcap, hncap, hfr, hl⟩ := id hinv
  have hlS := hwS.lt
  have hlc : (M.getMem (top + 18446744073709551512#64)).toNat ≤ (M.getMem (top + 18446744073709551496#64)).toNat := by
    rw [hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]; exact hncap
  rv_introT hinv
  rv_symT hp stop [158] with [(by omega : env.stackLimit.toNat + 128 ≤ top.toNat)]
  clear hinv_20 hinv_23
  rv_symT hp with [(by omega : env.stackLimit.toNat + 128 ≤ top.toNat)]
  · have o : ∀ k : Nat, k < 24 → SretOut Layouts.Vec.byteSize regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      ⟨by rw [toNat_add_ofNat (by omega)]; omega,
        by rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Vec.byteSize]; omega⟩
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF (by simpa using o 0 (by omega))
      (hwS.ne_next (Nat.le_refl _) (by omega))) (o 8 (by omega)) (hwS.ne_next_add (o := 8) (by omega)))
      (o 16 (by omega)) (hwS.ne_next_add (o := 16) (by omega))
  · exact (vecT_stores hwS haS hb hcap hlc).1.2.1.2.2.1
  · exact (vecT_stores hwS haS hb hcap hlc).1.2.1.2.2.2
  · rw [hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]; exact hmin.symm

set_option hygiene false in
/-- `Inv` after a pass: across `base_mul`, the element's push, `spread`, `reduce` and `base_mul`. -/
local macro "inv4" : tactic => `(tactic| (
  have hI4 : Inv env ret top regs m n (R .x23 + 1#64) m4 :=
    ((((hInv.call (by rw [hsp]; omega) (by rw [hsp]; omega) hret1_14 hret1_17 hret1_15).push hlim
      (keep1_1 _ (le _ (by tn))) (by omega) h22).call (by rw [hsp]; omega) (by rw [hsp]; omega) hret2_14 hret2_18
      hret2_15).call (by rw [hsp]; omega) (by rw [hsp]; omega) hret3_14 hret3_17 hret3_15).call (by rw [hsp]; omega)
      (by rw [hsp]; omega) hret4_14 hret4_17 hret4_15))

set_option rv_sym.heap true in
/-- **The loop**, from its head: `inverses[i]` times the basis pushed (the buffer has room: its capacity is at least
    `n`), the basis advanced by `spread`, `reduce` and `base_mul`, then back to the head or to the exit; one element
    fewer left. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needB needS needR : Nat} (hnB : 128 + needB ≤ need) (hnS : 128 + needS ≤ need)
    (hnR : 128 + needR ≤ need) (hbm : Field.BaseMulT.specT env p L.baseMul.idx needB)
    (hsp : Field.SpreadT.specT env p L.spread.idx needS) (hrd : Field.ReduceT.specT env p L.reduce.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {n : Nat} {rp ip : Word} (hn : n < 2 ^ 61)
    (hfin : ∀ R M, FinInv env ret top regs m n R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 152, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv env ret top regs m n rp ip k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 122, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m n rp ip) fun k R M hI ih => ?_
  obtain ⟨-, -, -, -, -, -, -, h22, h26, hlk, hk1, hInv, r0, ra, rl, i0, ia, il⟩ := id hI
  have hnM := hInv.1.1
  have hA : (rp + R .x22).toNat = rp.toNat + 8 * (R .x23).toNat := by rw [BitVec.toNat_add, h22]; omega
  have hB : (ip + R .x22).toNat = ip.toNat + 8 * (R .x23).toNat := by rw [BitVec.toNat_add, h22]; omega
  obtain ⟨-, -, -, -, hb, hcap, hncap, hfr, -⟩ := id hInv
  have hcap0 : (M.getMem (top + 18446744073709551496#64)).toNat ≠ 0 := by omega
  obtain ⟨hp0, hpl, hpa⟩ := hb.resolve_left hcap0
  unfold Env.Live at hpl
  have hP : (M.getMem (top + 18446744073709551504#64) + R .x22).toNat =
      (M.getMem (top + 18446744073709551504#64)).toNat + 8 * (R .x23).toNat := by rw [BitVec.toNat_add, h22]; omega
  rv_introT hI
  clear hI_27 hI_30
  rv_symT hp stop [122, 140, 152] through [88] with [hL, (by omega : env.stackLimit.toNat + 128 ≤ top.toNat)]
    using [hbm, hsp, hrd]
  all_goals
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 128 ≤ top.toNat := by omega
    have hsp : (top + 18446744073709551488#64).toNat = top.toNat - 128 := by tn
    have le : ∀ c : Word, top.toNat - 128 ≤ (top + c).toNat → top + 18446744073709551488#64 ≤ top + c :=
      fun c h => BitVec.le_def.2 (by rw [hsp]; exact h)
    have hnMe := hInv.1.2.1
  -- the exit: `n` elements pushed
  · inv4
    have hn' : R .x23 + 1#64 = BitVec.ofNat 64 n := by
      have := congrArg BitVec.toNat hc
      rw [h26, BitVec.toNat_add, h22] at this
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp at this ⊢; omega
    exact hfin _ _ ⟨by rv_closeT, by rv_closeT, by rv_closeT, by omega, hn' ▸ hI4⟩
  -- back to the head
  · inv4
    have hb1 : (M.getMem (top + 18446744073709551504#64) + R .x22).toNat < env.heapEnd.toNat := by omega
    have ek : ∀ c : Word, top.toNat - 128 ≤ (top + c).toNat → c ≠ 18446744073709551512#64 →
        m4.getMem (top + c) = M.getMem (top + c) := fun c h1 h2 =>
      (keep4_1 _ (le c h1)).trans ((keep3_1 _ (le c h1)).trans ((keep2_1 _ (le c h1)).trans
        ((rd_push hb1 (by omega) fun he => h2 ((BitVec.add_right_inj top).1 he)).trans (keep1_1 _ (le c h1)))))
    have hk2 : 2 ≤ k := by
      refine Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq ?_)
      rw [h26, toNat_add_ofNat (by omega), h22]; omega
    refine ih (k - 1) _ _ (by omega) ⟨by rv_closeT, by rv_closeT, ?_, ?_, by rv_closeT, by rv_closeT, by rv_closeT,
      ?_, ?_, ?_, by omega, hI4, r0, ra, rl, i0, ia, il⟩
    all_goals simp only [Tactic.rf]
    · exact (ek _ (by tn) (by decide)).symm
    · exact (ek _ (by tn) (by decide)).symm
    · rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega), h22]; omega
    · exact h26
    · rw [toNat_add_ofNat (by omega)]; omega
  -- `grow_one`, never reached: the length is below `n`, at most the capacity
  · exfalso; have := congrArg BitVec.toNat hc; omega

/-- **What `Subspace::at` reads of its two vectors**: the zip's length below `2^60`, and, when it is not `0`, both
    buffers `Src`. -/
theorem src_of {env : Env} {m : MachineState} {a : Word} (hv1 : VecT env m a 8) (hv2 : VecT env m (a + 24#64) 8) :
    (m.getMem (a + 16#64)).toNat < 2 ^ 60 ∧ (m.getMem (a + 40#64)).toNat < 2 ^ 60 ∧
      (0 < min (m.getMem (a + 16#64)).toNat (m.getMem (a + 40#64)).toNat →
        Src env m (min (m.getMem (a + 16#64)).toNat (m.getMem (a + 40#64)).toNat) (m.getMem (a + 8#64))
          (m.getMem (a + 32#64))) := by
  obtain ⟨-, ⟨-, -, hb1, hc1⟩, hl1⟩ := hv1
  obtain ⟨-, ⟨-, -, hb2, hc2⟩, hl2⟩ := hv2
  simp only [rvCapAt, rvPtrAt, vecLen, vecCap, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, Layouts.Vec.len,
    Layouts.Vec.cap, BitVec.add_assoc] at hb1 hc1 hl1 hb2 hc2 hl2
  simp only [BitVec.add_zero, show (24#64 : Word) + 0#64 = 24#64 from rfl,
    show (24#64 : Word) + 8#64 = 32#64 from rfl, show (24#64 : Word) + 16#64 = 40#64 from rfl]
    at hb1 hc1 hl1 hb2 hc2 hl2
  refine ⟨by omega, by omega, fun hpos => ?_⟩
  obtain ⟨r0, rl, ra⟩ := hb1.resolve_left (by omega)
  obtain ⟨i0, il, ia⟩ := hb2.resolve_left (by omega)
  unfold Env.Live at rl il
  exact ⟨r0, ra, by omega, i0, ia, by omega⟩

/-- The zip's length, `min a b`, is not `0` when the shorter is not. -/
theorem min_pos {a b : Word} (h : a ≠ 0#64 ∧ a < b ∨ b ≠ 0#64 ∧ b ≤ a) : 0 < min a.toNat b.toNat := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := BitVec.lt_def.1 h2; have : a.toNat ≠ 0 := fun h => h1 (BitVec.eq_of_toNat_eq h); omega
  · have := BitVec.le_def.1 h2; have : b.toNat ≠ 0 := fun h => h1 (BitVec.eq_of_toNat_eq h); omega

/-- After the allocation (instruction 62): the stack pointer, the slot's and the `Subspace`'s addresses, `roots.len()`
    in `x26`, the buffer `BufT` in `x18` with its capacity, at least `roots.len()`, in `x21`, allocated since the
    entry unless it has no capacity; the frame, the code, the static data, the saved registers' slots, and the
    `Subspace`'s words the rest reads kept. -/
def MInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551488#64 ∧ R .x8 = regs .x10 ∧ R .x19 = regs .x11 ∧
    R .x26 = m.getMem (regs .x11 + 16#64) ∧ R .x27 = regs .x27 ∧
    BufT env M (R .x21) (R .x18) 8 ∧ (R .x21).toNat * 8 < 2 ^ 63 ∧
    (m.getMem (regs .x11 + 16#64)).toNat ≤ (R .x21).toNat ∧ (R .x21 = 0#64 ∨ (env.next m).toNat ≤ (R .x18).toNat) ∧
    env.Frame top (SretOut Layouts.Vec.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    Saved ret top regs M ∧ M.getMem (regs .x11 + 8#64) = m.getMem (regs .x11 + 8#64) ∧
    M.getMem (regs .x11 + 32#64) = m.getMem (regs .x11 + 32#64) ∧
    M.getMem (regs .x11 + 40#64) = m.getMem (regs .x11 + 40#64)

set_option hygiene false in
/-- The frame across the header's three stores. -/
local macro "hdr_frame" : tactic => `(tactic| exact Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot hF
  (by tn) (by tn)) (by tn) (by tn)) (by tn) (by tn))

set_option rv_sym.heap true in
/-- **From the allocation**: the header stored, the zip's length, then the loop or the exit. -/
theorem mid_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 128 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) (hw11 : InWin env (regs .x11) 48)
    (ha11 : (regs .x11).toNat % 8 = 0) (ho11 : env.Owned m top (regs .x11) 48)
    (hr60 : (m.getMem (regs .x11 + 16#64)).toNat < 2 ^ 60) (hi60 : (m.getMem (regs .x11 + 40#64)).toNat < 2 ^ 60)
    (hsrc : 0 < min (m.getMem (regs .x11 + 16#64)).toNat (m.getMem (regs .x11 + 40#64)).toNat →
      Src env m (min (m.getMem (regs .x11 + 16#64)).toNat (m.getMem (regs .x11 + 40#64)).toNat)
        (m.getMem (regs .x11 + 8#64)) (m.getMem (regs .x11 + 32#64)))
    (hfin : ∀ R M, FinInv env ret top regs m
        (min (m.getMem (regs .x11 + 16#64)).toNat (m.getMem (regs .x11 + 40#64)).toNat) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 152, ret, top⟩ :: rest, R, M⟩)
    (hloop : ∀ k R M, LInv env ret top regs m
        (min (m.getMem (regs .x11 + 16#64)).toNat (m.getMem (regs .x11 + 40#64)).toNat)
        (m.getMem (regs .x11 + 8#64)) (m.getMem (regs .x11 + 32#64)) k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 122, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, MInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 62, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, -, -, -, hb, hcap, hrc, hfr, hF, -, -, -, h8, h32, h40⟩ := id hinv
  have hl11 := hw11.lt
  have e8 : (regs .x11 + 8#64).toNat = (regs .x11).toNat + 8 := toNat_add_ofNat (by omega)
  have e32 : (regs .x11 + 32#64).toNat = (regs .x11).toNat + 32 := toNat_add_ofNat (by omega)
  have e40 : (regs .x11 + 40#64).toNat = (regs .x11).toNat + 40 := toNat_add_ofNat (by omega)
  rv_introT hinv
  clear hinv_6 hinv_9
  rv_symT hp stop [122, 152] with [(by omega : env.stackLimit.toNat + 128 ≤ top.toNat)]
  all_goals (try rw [h40] at hc); rw [h40] at hc_1
  · refine hfin _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rv_closeT
    · hdr_frame
    · rw [hc]; simp
  · refine hloop (min (m.getMem (regs .x11 + 16#64)).toNat (m.getMem (regs .x11 + 40#64)).toNat) _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsrc (min_pos (.inl ⟨hc, hc_1⟩))⟩
    all_goals try rv_closeT
    · rw [shl3 (by omega), Nat.min_eq_left (Nat.le_of_lt (BitVec.lt_def.1 hc_1))]
    · exact min_pos (.inl ⟨hc, hc_1⟩)
    · hdr_frame
  · refine hfin _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rv_closeT
    · hdr_frame
    · rw [hc]; simp
  · refine hloop (min (m.getMem (regs .x11 + 16#64)).toNat (m.getMem (regs .x11 + 40#64)).toNat) _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsrc (min_pos (.inr ⟨hc, hc_1⟩))⟩
    all_goals try rv_closeT
    · rw [h40, shl3 (by omega), Nat.min_eq_right (BitVec.le_def.1 hc_1)]
    · exact min_pos (.inr ⟨hc, hc_1⟩)
    · hdr_frame

set_option rv_sym.heap true in
/-- **`Subspace::at` is total**: the allocation of `roots.len()` words, the zip's length, then the loop or the
    exit. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needB needS needR needA needH : Nat} (hnB : 128 + needB ≤ need) (hnS : 128 + needS ≤ need)
    (hnR : 128 + needR ≤ need) (hnA : 128 + needA ≤ need) (hnH : 128 + needH ≤ need)
    (hbm : Field.BaseMulT.specT env p L.baseMul.idx needB) (hsp : Field.SpreadT.specT env p L.spread.idx needS)
    (hrd : Field.ReduceT.specT env p L.reduce.idx needR) (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hhe : Aborts env p L.handleError.idx needH) : specT env p i need := by
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 128 ≤ top.toNat)]
  have hv1 : VecT env m (regs .x11) 8 := ⟨hpre_14, ⟨hpre_15, hpre_16, hpre_17, hpre_18⟩, hpre_19⟩
  have hv2 : VecT env m (regs .x11 + 24#64) 8 := ⟨hpre_20, ⟨hpre_21, hpre_22, hpre_23, hpre_24⟩, hpre_25⟩
  clear hpre_14 hpre_15 hpre_16 hpre_17 hpre_18 hpre_19 hpre_20 hpre_21 hpre_22 hpre_23 hpre_24 hpre_25
  obtain ⟨hr60, hi60, hsrc⟩ := src_of hv1 hv2
  have hfin := fin_ok env p i L hp hk hpre_3 (by omega) hpre_26 hpre_27 hpre_6 hpre_7 (hpre_2 ▸ ⟨hpre_8, hpre_9⟩) rfl
  have hmid := mid_ok env p i L hp hpre_3 (by omega) hpre_26 hpre_27 hpre_10 hpre_11 (hpre_2 ▸ ⟨hpre_12, hpre_13⟩)
    hr60 hi60 hsrc hfin
    (loop env p i L hp hL hnB hnS hnR hbm hsp hrd hpre_3 hpre_26 hpre_27 (by omega) hfin)
  clear hfin
  rv_symT hp stop [62] with [hL, (by omega : env.stackLimit.toNat + 128 ≤ top.toNat)] using [hac, hhe]
  · refine hmid _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals rv_closeT
    exact .inl rfl
  · rw [shl3 (by omega)]; omega
  · refine hmid _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals rv_closeT
    · refine .inr ⟨by have := hpre_27.next_ge; omega, ?_, hret1_17⟩
      unfold Env.Live
      rw [shl3 (by omega)] at hret1_18; omega
    · exact .inr hret1_16

end Rv64mc.Proof.Whir.SubspaceAtT

/-- info: 'Rv64mc.Proof.Whir.SubspaceAtT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.SubspaceAtT.total
