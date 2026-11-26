/-
  Rv64mc.Proof.Runtime.FromIterOptT

  `<Vec<Option<E>> as SpecFromIterNested>::from_iter` over `xs.iter().map(|x| Some(*x))` (the slice's ends in `a1`
  and `a2`) is total: it checks the slice's bytes against `isize::MAX / 24 * 16` (a word of the static data,
  `d_c8_131d94e1`; else `handle_error`), allocates `24 n` bytes for its `n` elements (`alloc`, the dangling pointer `8`
  for none), builds the header in its frame at `sp + 8`, calls `Vec::reserve` for `n` (which keeps the header),
  stores `Some(x)` for each element and copies the header to `sret`. Its result is a vector's (`VecReprT.VecT`) of
  `n` elements, its buffer fresh unless empty; the run ends with the guest's abort (`AbortStop`) where `alloc` or
  `handle_error` does. The source is whole 16-byte elements in a window (`SrcT`): the loop stops on its count only
  when the slice's bytes are a multiple of 16.

  The proof is `FromElemT`'s for this frame: `rv_autoT` up to `reserve`'s return (instruction 80), `hdr_kept`, `tail`,
  `loop` (`Total.loop`, the elements left as the measure, `LInv`).

  ## Main definitions

  * `SrcT`, `FromIterPreT`, `FromIterPostT`, `FromIterSpecT`, `LInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.FromElemT
import Rv64mc.Proof.Field.ESumCopied
import Rv64mc.Gen.Tmpl.Alloc.Vec.SpecFromIterNested.VecOptionE.AsSpecFromIterNestedOptiH0c7a0891.FromIter

namespace Rv64mc.Proof.Runtime.FromIterOptT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT)
open Rv64mc.Proof.Runtime.FromElemT (keep_store)
open Rv64mc.Gen.Alloc.Vec.SpecFromIterNested.VecOptionE.AsSpecFromIterNestedOptiH0c7a0891.FromIter
  (Link tmpl d_c8_131d94e1_words)

/-- The source `[a1, a2)`: whole elements of 16 bytes, in a window and 8-byte aligned unless empty. -/
def SrcT (env : Env) (b e : Word) : Prop :=
  b.toNat ≤ e.toNat ∧ (e.toNat - b.toNat) % 16 = 0 ∧
    (b = e ∨ InWin env b (e.toNat - b.toNat) ∧ b.toNat % 8 = 0)

/-- The total precondition: the result's slot a caller's (`SretPre`), in a window and 8-byte aligned; the source
    `SrcT`. -/
def FromIterPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) Layouts.Vec.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    SrcT env (regs .x11) (regs .x12)

/-- The total postcondition: the result a vector's (`VecT`) of the source's length, its buffer fresh unless
    empty. -/
def FromIterPostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  VecT env m' (regs .x10) 24 ∧ 16 * (vecLen m' (regs .x10)).toNat = (regs .x12).toNat - (regs .x11).toNat ∧
    ((vecLen m' (regs .x10)).toNat = 0 ∨
      env.Fresh m m' (vecPtr m' (regs .x10)) ((vecLen m' (regs .x10)).toNat * 24))

/-- **The total contract of `Vec<Option<E>>`'s `spec_from_iter_nested`** over `xs.iter().map(Some)`, or the guest's
    abort. -/
def FromIterSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (FromIterPreT env) (FromIterPostT env) SretVecOut AbortStop

/-- The capacity check passed: the count `n` and `24 n` as the code computes them, below `2 ^ 63`. -/
theorem ovf2 {b e : Word} (hle : b.toNat ≤ e.toNat) (h16 : (e.toNat - b.toNat) % 16 = 0)
    (h : e - b ≤ 6148914691236517200#64) :
    ((e - b) >>> 4).toNat = (e.toNat - b.toNat) / 16 ∧
    (((e - b) &&& 18446744073709551600#64) + (e - b) >>> 4 <<< 3).toNat = 24 * ((e.toNat - b.toNat) / 16) ∧
    24 * ((e.toNat - b.toNat) / 16) < 2 ^ 63 := by
  have hd : (e - b).toNat = e.toNat - b.toNat := by rw [BitVec.toNat_sub]; omega
  have hsr : ((e - b) >>> 4).toNat = (e.toNat - b.toNat) / 16 := by
    rw [BitVec.toNat_ushiftRight, hd, Nat.shiftRight_eq_div_pow]
  have hback : (e - b) >>> 4 <<< 4 = e - b := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft, hsr, Nat.shiftLeft_eq, hd]; omega
  have hand : (e - b) &&& 18446744073709551600#64 = e - b := by
    rw [← hback]; exact Rv64mc.Proof.Field.ESumCopied.shl4_and _
  rw [BitVec.le_def, hd] at h
  have h' : e.toNat - b.toNat ≤ 6148914691236517200 := h
  refine ⟨hsr, ?_, by omega⟩
  rw [hand, BitVec.toNat_add, hd, BitVec.toNat_shiftLeft, hsr, Nat.shiftLeft_eq]
  omega

/-- The prologue's six saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  (((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)

/-- The header in the frame, at `sp + 8`: capacity `c`, pointer `q`, length `0`. -/
def hdr (N : MachineState) (top c q : Word) : MachineState :=
  ((N.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64) q).setMem
    (top + 18446744073709551560#64) 0#64

/-- The header's pointer and length, from its address. -/
theorem at8 (t : Word) : t + 18446744073709551544#64 + BitVec.ofNat 64 8 = t + 18446744073709551552#64 := by
  rw [BitVec.add_assoc]; rfl
theorem at16 (t : Word) : t + 18446744073709551544#64 + BitVec.ofNat 64 16 = t + 18446744073709551560#64 := by
  rw [BitVec.add_assoc]; rfl

/-- The header's words, read back. -/
theorem hdr_reads (N : MachineState) (t c q : Word) :
    (hdr N t c q).getMem (t + 18446744073709551544#64) = c ∧ (hdr N t c q).getMem (t + 18446744073709551552#64) = q ∧
      (hdr N t c q).getMem (t + 18446744073709551560#64) = 0#64 := by
  simp only [hdr]
  refine ⟨?_, ?_, MachineState.getMem_setMem_eq⟩
  · rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)),
      MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]

/-- **The header's words after `reserve`**, at and above the frame's start: `FromElemT.hdr_kept` for this frame. -/
theorem hdr_kept {N N0 m1 m' : MachineState} {top c q : Word} {R : Reg → Word}
    (hR : R .x10 = top + 18446744073709551544#64)
    (hN : ∀ a, top + 18446744073709551536#64 ≤ a → N.getMem a = N0.getMem a)
    (k1 : ∀ a, top + 18446744073709551536#64 ≤ a → ¬ GrowOut R m' a → m1.getMem a = (hdr N top c q).getMem a)
    (hc : vecCap m1 (top + 18446744073709551544#64) = vecCap (hdr N top c q) (top + 18446744073709551544#64))
    (hq : vecPtr m1 (top + 18446744073709551544#64) = vecPtr (hdr N top c q) (top + 18446744073709551544#64)) :
    ∀ a, top + 18446744073709551536#64 ≤ a → m1.getMem a = (hdr N0 top c q).getMem a := by
  have r := hdr_reads
  simp only [vecCap, vecPtr, Layouts.Vec.cap, Layouts.Vec.ptr, BitVec.add_zero, at8] at hc hq
  intro a ha
  by_cases e1 : a = top + 18446744073709551544#64
  · subst e1; rw [hc]; exact (r N _ _ _).1.trans (r N0 _ _ _).1.symm
  by_cases e2 : a = top + 18446744073709551552#64
  · subst e2; rw [hq]; exact (r N _ _ _).2.1.trans (r N0 _ _ _).2.1.symm
  rw [k1 a ha (by
    simp only [GrowOut, rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero, hR, at8]
    exact fun h => h.elim e1 e2)]
  simp only [hdr]
  by_cases e3 : a = top + 18446744073709551560#64
  · subst e3; rw [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne e3, MachineState.getMem_setMem_ne e2, MachineState.getMem_setMem_ne e1,
      MachineState.getMem_setMem_ne e3, MachineState.getMem_setMem_ne e2, MachineState.getMem_setMem_ne e1, hN a ha]

/-- The header the code stored has room for `n ≤ c` elements past its length `0`. -/
theorem hdr_spare (N : MachineState) (top c q : Word) {n : Nat} (h : n ≤ c.toNat) :
    n ≤ (vecCap (hdr N top c q) (top + 18446744073709551544#64)).toNat -
      (vecLen (hdr N top c q) (top + 18446744073709551544#64)).toNat := by
  simp only [vecCap, vecLen, Layouts.Vec.cap, Layouts.Vec.len, BitVec.add_zero, at16]
  rw [(hdr_reads N top c q).1, (hdr_reads N top c q).2.2]
  simpa using h

/-- The prologue's and the header's stores stay in the frame. -/
theorem saved_frame {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    env.Frame top Tactic.F m (saved m top ret regs) := by
  have := top.isLt
  refine Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
    (Tactic.frame_store (Tactic.frame_refl hnx) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_ <;>
    (rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega)

theorem hdr_frame {env : Env} {m N : MachineState} {top c q : Word} (hlim : env.stackLimit.toNat + 80 ≤ top.toNat)
    (hF : env.Frame top Tactic.F m N) : env.Frame top Tactic.F m (hdr N top c q) := by
  have := top.isLt
  refine Tactic.frame_store (Tactic.frame_store (Tactic.frame_store hF ?_ ?_) ?_ ?_) ?_ ?_ <;>
    (rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega)

/-- `reserve`'s `out`, the header's two words, lies in the frame. -/
theorem grow_stack {env : Env} {top b : Word} {R : Reg → Word} {M : MachineState}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hx : R .x10 = top + 18446744073709551544#64)
    (hb : GrowOut R M b) : env.stackLimit.toNat ≤ b.toNat ∧ b.toNat < top.toNat := by
  have s72 : (top + 18446744073709551544#64).toNat = top.toNat - 72 :=
    Multilinear.slot_toNat (by decide) (by omega) (by decide)
  have := Multilinear.SelectorPoint.grow_in hx (by omega) hb
  unfold InRange at this
  omega

/-- The loop's head with `k + 1` passes left: the source cursor `x9` 8 bytes into an element, `x12` 8 bytes into the
    one past the last; the destination cursor `x11` 16 bytes into an element of the block `q`. -/
def LInv (env : Env) (m M0 : MachineState) (top ret q : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ R .x10 = (regs .x12 - regs .x11) >>> 4 ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧
    R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    k + 1 ≤ ((regs .x12).toNat - (regs .x11).toNat) / 16 ∧
    (R .x9).toNat + 16 * (k + 1) = (R .x12).toNat ∧ (R .x9).toNat % 8 = 0 ∧
    (R .x12).toNat = (regs .x12).toNat + 8 ∧
    (R .x11).toNat + 24 * (k + 1) = q.toNat + 16 + 24 * (((regs .x12).toNat - (regs .x11).toNat) / 16) ∧
    (R .x11).toNat % 8 = 0 ∧
    (∀ a, top + 18446744073709551536#64 ≤ a →
      M.getMem a = (hdr (saved m top ret regs) top ((regs .x12 - regs .x11) >>> 4) q).getMem a) ∧
    env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code ∧ env.next M = env.next M0

set_option rv_sym.heap true in
/-- **The loop**, from its head; past its last pass the header is copied to `sret`. -/
theorem loop {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 80 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m M0 : MachineState} {q : Word}
    (hk : ∀ r' m', HoldsT.post env (FromIterPostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hwin : InWin env (regs .x10) Layouts.Vec.byteSize)
    (hal : (regs .x10).toNat % 8 = 0)
    (hs1 : (regs .x11).toNat ≤ (regs .x12).toNat) (hs2 : ((regs .x12).toNat - (regs .x11).toNat) % 16 = 0)
    (hsw : InWin env (regs .x11) ((regs .x12).toNat - (regs .x11).toNat)) (hs8 : (regs .x11).toNat % 8 = 0)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hge : 0x10000000 ≤ (env.next m).toNat)
    (hnw : ((regs .x12 - regs .x11) >>> 4).toNat = ((regs .x12).toNat - (regs .x11).toNat) / 16)
    (h63 : 24 * (((regs .x12).toNat - (regs .x11).toNat) / 16) < 2 ^ 63)
    (hpos : 0 < ((regs .x12).toNat - (regs .x11).toNat) / 16)
    (hfr : env.Fresh m M0 q (24 * (((regs .x12).toNat - (regs .x11).toNat) / 16))) (hq8 : q.toNat % 8 = 0)
    (hF0 : (env.next M0).toNat ≤ env.heapEnd.toNat) :
    ∀ k R M, LInv env m M0 top ret q regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 106, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env m M0 top ret q regs) fun k R M hI ih => ?_
  have hlay := env.layout
  have hfr1 := hfr.1
  have hfr2 := hfr.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hk1, hq1, hq2, hq3, hq4, hq5, hK, hF, hS, hcode, hnM⟩ := id hI
  clear hK
  rv_introT hI
  simp only [hdr, saved] at hI_17
  have hd16 : (regs .x12).toNat - (regs .x11).toNat = 16 * (((regs .x12).toNat - (regs .x11).toNat) / 16) := by
    omega
  generalize ((regs .x12).toNat - (regs .x11).toNat) / 16 = n at *
  have hx16 : (R .x9 + 16#64).toNat = (R .x9).toNat + 16 := toNat_add_ofNat (by have := env.heapEnd.isLt; omega)
  have hy24 : (R .x11 + 24#64).toNat = (R .x11).toNat + 24 := toNat_add_ofNat (by have := env.heapEnd.isLt; omega)
  rv_symT hp stop [122]
  · -- back to the head
    have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [hx16]; subst h0; omega))
    clear hc
    have hlo : (env.next m).toNat + 16 ≤ (R .x11).toNat := by omega
    have hhi : (R .x11).toNat + 8 ≤ (env.next M).toNat := by rw [hnM]; omega
    refine ih (k - 1) _ _ (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    all_goals try simp only [Tactic.rf]
    all_goals try rv_closeT
    have ht80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 :=
      Multilinear.slot_toNat (by decide) (by omega) (by decide)
    have := hnM ▸ hF0
    have e16 : (R .x11 + 18446744073709551600#64).toNat = (R .x11).toNat - 16 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    have e8 : (R .x11 + 18446744073709551608#64).toNat = (R .x11).toNat - 8 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    exact keep_store (keep_store (keep_store hI_17 (by rw [e16]; omega)) (by rw [e8]; omega)) (by omega)
  · -- past the last pass
    have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; rw [hx16] at this; omega
    clear hc
    subst hk0
    clear hsw hs8 hk1 hq1
    rv_symT hp
    all_goals simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
    all_goals rv_closeT

/-- The registers at `reserve`'s return. -/
def TailRegs (top : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧ R .x19 = regs .x12 ∧
    R .x18 = (regs .x12 - regs .x11) >>> 4 ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧
    R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

set_option rv_sym.heap true in
/-- **From `reserve`'s return**: an empty source straight to the copy, else into the loop. -/
theorem tail {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 80 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (FromIterPostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hwin : InWin env (regs .x10) Layouts.Vec.byteSize)
    (hal : (regs .x10).toNat % 8 = 0) (hsrc : SrcT env (regs .x11) (regs .x12))
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hge : 0x10000000 ≤ (env.next m).toNat) (hend : env.heapEnd.toNat ≤ 0x78000000)
    (hnw : ((regs .x12 - regs .x11) >>> 4).toNat = ((regs .x12).toNat - (regs .x11).toNat) / 16)
    (h63 : 24 * (((regs .x12).toNat - (regs .x11).toNat) / 16) < 2 ^ 63)
    (R : Reg → Word) (M : MachineState) (hR : TailRegs top regs R) (c q : Word)
    (hK : ∀ a, top + 18446744073709551536#64 ≤ a → M.getMem a = (hdr (saved m top ret regs) top c q).getMem a)
    (hF : env.Frame top Tactic.F m M) (hS : env.Static M) (hcode : M.code = m.code)
    (hcq : (((regs .x12).toNat - (regs .x11).toNat) / 16 = 0 ∧ c = 0#64) ∨
      (c = (regs .x12 - regs .x11) >>> 4 ∧ 0 < ((regs .x12).toNat - (regs .x11).toNat) / 16 ∧
        env.Fresh m M q (24 * (((regs .x12).toNat - (regs .x11).toNat) / 16)) ∧ q.toNat % 8 = 0)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 80, ret, top⟩ :: rest, R, M⟩ := by
  have hK' := hK
  simp only [hdr, saved] at hK
  rv_introT hR
  obtain ⟨hs1, hs2, hs3⟩ := hsrc
  rcases hcq with ⟨hn0, rfl⟩ | ⟨rfl, hpos, hfr, hq8⟩
  · rv_symT hp stop [106]
    all_goals try (exfalso; exact hc (BitVec.eq_of_toNat_eq (by omega)))
    all_goals simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
    all_goals rv_closeT
  · have hfr1 := hfr.1
    have hfr2 := hfr.2
    have hFn := hF.2.1
    rv_symT hp stop [106]
    all_goals try (exfalso; have := congrArg BitVec.toNat hc; omega)
    have hsw := hs3.resolve_left hc
    have hsw' := hsw.1
    unfold InWin at hsw'
    have hb8 : (regs .x11 + 8#64).toNat = (regs .x11).toNat + 8 := toNat_add_ofNat (by omega)
    have hsh : ((regs .x12 - regs .x11) >>> 4 <<< 4).toNat = (regs .x12).toNat - (regs .x11).toNat := by
      rw [BitVec.toNat_shiftLeft, hnw, Nat.shiftLeft_eq]; omega
    have he8 : (regs .x11 + 8#64 + (regs .x12 - regs .x11) >>> 4 <<< 4).toNat = (regs .x12).toNat + 8 := by
      rw [BitVec.toNat_add, hb8, hsh]; omega
    have hq16 : (q + 16#64).toNat = q.toNat + 16 := toNat_add_ofNat (by omega)
    refine loop hp hn hk hstk hnx hown hwin hal hs1 hs2 hsw.1 hsw.2 hW h16 hge hnw h63 hpos hfr hq8 hFn
      (((regs .x12).toNat - (regs .x11).toNat) / 16 - 1) _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hK', hF, hS, hcode, rfl⟩
    all_goals try simp only [Tactic.rf]
    all_goals rv_closeT

set_option rv_sym.heap true in
/-- **`spec_from_iter_nested` for `Vec<Option<E>>` is total**, with 80 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hdata : DataRef.InData env [(L.d_c8_131d94e1, d_c8_131d94e1_words)])
    {need needA needR needH : Nat} (hnA : 80 + needA ≤ need) (hnR : 80 + needR ≤ need) (hnH : 80 + needH ≤ need)
    (hal : AllocT.AllocSpecT env p L.alloc.idx needA) (hres : ReserveT.ReserveSpecT env 8 24 p L.reserve.idx needR)
    (hhe : Aborts env p L.handleError.idx needH) : FromIterSpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hw := hdata.words (List.mem_singleton_self _)
  rv_autoT hp stop [80] with [hL, hw] using [hal', hres, hhe]
  all_goals
    have hd0 : inWindow (L.d_c8_131d94e1.hi + L.d_c8_131d94e1.lo) 8 = true ∧
        (L.d_c8_131d94e1.hi + L.d_c8_131d94e1.lo).toNat % 8 = 0 := by
      have h0 := hpre_14.data_ok _ (hdata _ (List.mem_singleton_self _) 0 Nat.one_pos)
      have e : L.d_c8_131d94e1.hi + L.d_c8_131d94e1.lo + BitVec.ofNat 64 (8 * 0) =
          L.d_c8_131d94e1.hi + L.d_c8_131d94e1.lo := BitVec.add_zero _
      dsimp only at h0
      rwa [e] at h0
  · exact hd0.1
  · exact hd0.2
  all_goals have hov := ovf2 hpre_10 hpre_11 hc_1
  on_goal 11 =>
    refine tail hp (by omega) hk hpre_3 hpre_5 ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩ hpre_8 hpre_9
      ⟨hpre_10, hpre_11, hpre_12⟩ hpre_14 hpre_13 hpre_14.next_ge hpre_14.heapEnd_le hov.1 hov.2.2 _ _
      ?_ ((regs .x12 - regs .x11) >>> 4) (r2 .x10)
      (hdr_kept rfl keep2_1 keep3_1 ?_ ?_) ?_ hret3_15 (hret3_25.trans hret2_19) ?_
  on_goal 5 =>
    refine tail hp (by omega) hk hpre_3 hpre_5 ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩ hpre_8 hpre_9
      ⟨hpre_10, hpre_11, hpre_12⟩ hpre_14 hpre_13 hpre_14.next_ge hpre_14.heapEnd_le hov.1 hov.2.2 _ _
      ?_ ((regs .x12 - regs .x11 &&& 18446744073709551600#64) + (regs .x12 - regs .x11) >>> 4 <<< 3) 8#64
      (hdr_kept rfl (fun _ _ => rfl) keep1_1 ?_ ?_) ?_ hret1_15 hret1_25 ?_
  all_goals try exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals try simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero,
    Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
  all_goals try rv_closeT
  all_goals
    have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
    have hF0 : env.Frame top Tactic.F m (saved m top ret regs) := saved_frame hlim hpre_5
    have h24 := hov.2.1
  -- no bytes: the dangling pointer
  · have h0 := congrArg BitVec.toNat hc
    exact (hret1_17 (hdr_spare _ _ _ _ (by rw [hov.1]; omega))).1
  · have h0 := congrArg BitVec.toNat hc
    exact (hret1_17 (hdr_spare _ _ _ _ (by rw [hov.1]; omega))).2
  · have s80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 :=
      Multilinear.slot_toNat (by decide) (by omega) (by decide)
    exact Multilinear.frame_call_own (hdr_frame hlim hF0) hret1_14 (by omega) fun b hb => grow_stack hlim rfl hb
  · have h0 := congrArg BitVec.toNat hc
    exact Or.inl ⟨by simp only [BitVec.toNat_ofNat] at h0; omega, hc⟩
  -- a block from `alloc`
  · exact (hret3_17 (hdr_spare _ _ _ _ le_rfl)).1
  · exact (hret3_17 (hdr_spare _ _ _ _ le_rfl)).2
  · have s80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 :=
      Multilinear.slot_toNat (by decide) (by omega) (by decide)
    exact Multilinear.frame_call_own (hdr_frame hlim (Tactic.frame_call hF0 hret2_14 (by omega))) hret3_14
      (by omega) fun b hb => grow_stack hlim rfl hb
  · have hpos : 0 < ((regs .x12).toNat - (regs .x11).toNat) / 16 := by
      rcases Nat.eq_zero_or_pos (((regs .x12).toNat - (regs .x11).toNat) / 16) with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h24, h]; rfl)) hc_2
      · exact h
    have hn3 := hret3_14.1
    have s56 : (top + 18446744073709551560#64).toNat = top.toNat - 56 :=
      Multilinear.slot_toNat (by decide) (by omega) (by decide)
    have s64 : (top + 18446744073709551552#64).toNat = top.toNat - 64 :=
      Multilinear.slot_toNat (by decide) (by omega) (by decide)
    have s72 : (top + 18446744073709551544#64).toNat = top.toNat - 72 :=
      Multilinear.slot_toNat (by decide) (by omega) (by decide)
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
      at hn3
    refine Or.inr ⟨trivial, hpos, ⟨hret2_16, ?_⟩, hret2_17⟩
    rw [h24] at hret2_18
    omega

end Rv64mc.Proof.Runtime.FromIterOptT

/-- info: 'Rv64mc.Proof.Runtime.FromIterOptT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.FromIterOptT.total
