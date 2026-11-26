/-
  Rv64mc.Proof.Runtime.FromElemT

  `<E as SpecFromElem>::from_elem` (`vec![E::new(c0, 0); n]`, the element's low limb in `a1`, the count in `a2`)
  is total: it checks that `16 n` fits an `isize` (else `handle_error`), allocates the buffer (`alloc`, the dangling
  pointer `8` for none), builds the header in its frame (capacity, pointer, length `0`), calls `Vec::reserve` for
  `n` (which keeps the header: the capacity is `n`), stores the `n` elements and copies the header to `sret`. Its
  result is a vector's (`VecReprT.VecT`) of length `n`, its buffer fresh unless empty: `CloneT`'s `ClonePostT`.
  The run ends with the guest's abort (`AbortStop`) where `alloc` or `handle_error` does. It does not state the
  elements stored.

  The prologue and the header are `selector_point`'s (`Proof/Multilinear/SelectorPoint`), whose lemmas it reuses.
  `rv_autoT` steps up to `reserve`'s return (instruction 80); `hdr_kept` turns `reserve`'s frame and
  postcondition into the frame's words at and above its start, the form the executor reads loads through, and
  `tail` steps the rest: `n < 2` straight to the copy, else the loop (`loop`, `Total.loop` with the elements left
  as the measure, `LInv`).

  ## Main definitions

  * `FromElemPreT`, `FromElemSpecT`, `LInv`

  ## Main results

  * `e_total`
  * `hdr_kept`: the frame's words after `reserve`
-/

import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.CloneT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Multilinear.SelectorPoint
import Rv64mc.Gen.Tmpl.Alloc.Vec.SpecFromElem.E.AsSpecFromElem.FromElemGlobal
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Runtime.FromElemT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT)
open Rv64mc.Gen.Alloc.Vec.SpecFromElem.E.AsSpecFromElem.FromElemGlobal (Link tmpl)

/-- `from_elem`'s total precondition: the result's slot a caller's (`SretPre`), in a window and 8-byte aligned. -/
def FromElemPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) Layouts.Vec.byteSize ∧ (regs .x10).toNat % 8 = 0

/-- **The total contract of `from_elem::<E>`** (`vec![E::new(c0, 0); n]`): its result a vector's (`VecT`) of
    length `n`, its buffer fresh unless empty (`CloneT.ClonePostT`), or the guest's abort. -/
def FromElemSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (FromElemPreT env) (ClonePostT env 16) SretVecOut AbortStop

/-- The prologue's five saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)

/-- The header in the frame: capacity `c`, pointer `q`, length `0`. -/
def hdr (N : MachineState) (top c q : Word) : MachineState :=
  ((N.setMem (top + 18446744073709551552#64) c).setMem (top + 18446744073709551560#64) q).setMem
    (top + 18446744073709551568#64) 0#64

/-- The registers at `reserve`'s return. -/
def TailRegs (top : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧ R .x18 = regs .x12 ∧
    R .x19 = regs .x12 <<< 4 ∧
    R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧
    R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- The loop's head with `k + 1` passes left: the cursor `x11` at an element of the block `q`, `x12` at the last. -/
def LInv (env : Env) (m M0 : MachineState) (top ret q : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧ R .x10 = 0#64 ∧
    R .x18 = regs .x12 ∧
    R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧
    R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    q.toNat ≤ (R .x11).toNat ∧ (R .x11).toNat % 8 = 0 ∧ (R .x11).toNat + 16 * (k + 1) = (R .x12).toNat ∧
    (R .x12).toNat + 16 = q.toNat + 16 * (regs .x12).toNat ∧
    (∀ a, top + 18446744073709551552#64 ≤ a → M.getMem a = (hdr (saved m top ret regs) top (regs .x12) q).getMem a) ∧
    env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code ∧ env.next M = env.next M0

/-- A store below the stack keeps what the frame's slots hold. -/
theorem keep_store {M : MachineState} {S : MachineState} {t x v : Word} (h : ∀ a, t ≤ a → M.getMem a = S.getMem a)
    (hx : x.toNat < t.toNat) : ∀ a, t ≤ a → (M.setMem x v).getMem a = S.getMem a := fun a ha => by
  rw [MachineState.getMem_setMem_ne (fun e => by rw [e, BitVec.le_def] at ha; omega), h a ha]

set_option rv_sym.heap true in
/-- **The loop**, from its head; its last pass stores the last element and copies the header to `sret`. -/
theorem loop {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 64 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m M0 : MachineState} {q : Word}
    (hk : ∀ r' m', HoldsT.post env (ClonePostT env 16) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hwin : InWin env (regs .x10) Layouts.Vec.byteSize)
    (hal : (regs .x10).toNat % 8 = 0) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hge : 0x10000000 ≤ (env.next m).toNat) (hend : env.heapEnd.toNat ≤ 0x78000000)
    (hov : (regs .x12 <<< 4).toNat = 16 * (regs .x12).toNat ∧ 16 * (regs .x12).toNat < 2 ^ 63)
    (hpos : 0 < (regs .x12).toNat) (hfr : env.Fresh m M0 q (16 * (regs .x12).toNat)) (hq8 : q.toNat % 8 = 0)
    (hF0 : (env.next M0).toNat ≤ env.heapEnd.toNat) :
    ∀ k R M, LInv env m M0 top ret q regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 98, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env m M0 top ret q regs) fun k R M hI ih => ?_
  have hlay := env.layout
  have hfr1 := hfr.1
  have hfr2 := hfr.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hq1, hq2, hq3, hq4, hK, hF, hS, hcode, hnM⟩ := id hI
  clear hK
  rv_introT hI
  simp only [hdr, saved] at hI_18
  have hx16 : (R .x11 + 16#64).toNat = (R .x11).toNat + 16 := toNat_add_ofNat (by have := env.heapEnd.isLt; omega)
  have hx8 : (R .x11 + 8#64).toNat = (R .x11).toNat + 8 := toNat_add_ofNat (by have := env.heapEnd.isLt; omega)
  rv_symT hp stop [106]
  · -- back to the head
    have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [hx16]; subst h0; omega))
    clear hc
    have hlo : (env.next m).toNat ≤ (R .x11).toNat := by omega
    have hhi : (R .x11).toNat + 16 ≤ (env.next M).toNat := by rw [hnM]; omega
    refine ih (k - 1) _ _ (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    all_goals try rv_closeT
    have ht64 : (top + 18446744073709551552#64).toNat = top.toNat - 64 :=
      Multilinear.slot_toNat (by decide) (by omega) (by decide)
    have := hnM ▸ hF0
    exact keep_store (keep_store hI_18 (by omega)) (by rw [hx8]; omega)
  · have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; rw [hx16] at this; omega
    clear hc
    subst hk0
    rv_symT hp
    all_goals simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
    all_goals rv_closeT

set_option rv_sym.heap true in
theorem tail {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 64 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (ClonePostT env 16) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hwin : InWin env (regs .x10) Layouts.Vec.byteSize)
    (hal : (regs .x10).toNat % 8 = 0) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hge : 0x10000000 ≤ (env.next m).toNat) (hend : env.heapEnd.toNat ≤ 0x78000000)
    (hov : (regs .x12 <<< 4).toNat = 16 * (regs .x12).toNat ∧ 16 * (regs .x12).toNat < 2 ^ 63)
    (R : Reg → Word) (M : MachineState) (hR : TailRegs top regs R) (c q : Word)
    (hK : ∀ a, top + 18446744073709551552#64 ≤ a → M.getMem a = (hdr (saved m top ret regs) top c q).getMem a)
    (hF : env.Frame top Tactic.F m M) (hS : env.Static M) (hcode : M.code = m.code)
    (hcq : ((regs .x12).toNat = 0 ∧ c = 0#64) ∨
      (c = regs .x12 ∧ 0 < (regs .x12).toNat ∧ env.Fresh m M q (16 * (regs .x12).toNat) ∧ q.toNat % 8 = 0)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 80, ret, top⟩ :: rest, R, M⟩ := by
  have hK' := hK
  simp only [hdr, saved] at hK
  rv_introT hR
  rcases hcq with ⟨hn0, rfl⟩ | ⟨rfl, hpos, hfr, hq8⟩
  · rv_symT hp stop [98]
    all_goals try simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
    all_goals try rv_closeT
    all_goals exfalso
    all_goals first
      | exact hc (BitVec.eq_of_toNat_eq hn0)
      | (rw [BitVec.le_def] at hc; have : (2#64 : Word).toNat = 2 := rfl; omega)
  · have hfr1 := hfr.1
    have hfr2 := hfr.2
    have hFn := hF.2.1
    rv_symT hp stop [98]
    all_goals try simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
    all_goals rv_closeT
    have h2 : 2 ≤ (regs .x12).toNat := by rw [BitVec.le_def] at hc; exact hc
    have hx12 : (regs .x12 <<< 4 + q + 18446744073709551600#64).toNat = q.toNat + 16 * (regs .x12).toNat - 16 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, hov.1]; have := env.heapEnd.isLt; simp only [BitVec.toNat_ofNat]; omega
    refine loop hp hn hk hstk hnx hown hwin hal hW h16 hge hend hov hpos hfr hq8 hFn ((regs .x12).toNat - 2) _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hK', hF, hS, hcode, rfl⟩
    all_goals simp only [Tactic.rf]
    all_goals try rv_closeT
    rw [hx12]; omega

/-- **The header's words after `reserve`**, at and above the frame's start: what the code stored over `N`, which
    agrees there with `N0`, where `reserve` (`out` the header's capacity and pointer) kept the capacity and pointer. -/
theorem hdr_kept {N N0 m1 m' : MachineState} {top c q : Word} {R : Reg → Word}
    (hR : R .x10 = top + 18446744073709551552#64)
    (hN : ∀ a, top + 18446744073709551552#64 ≤ a → N.getMem a = N0.getMem a)
    (k1 : ∀ a, top + 18446744073709551552#64 ≤ a → ¬ GrowOut R m' a → m1.getMem a = (hdr N top c q).getMem a)
    (hc : vecCap m1 (top + 18446744073709551552#64) = vecCap (hdr N top c q) (top + 18446744073709551552#64))
    (hq : vecPtr m1 (top + 18446744073709551552#64) = vecPtr (hdr N top c q) (top + 18446744073709551552#64)) :
    ∀ a, top + 18446744073709551552#64 ≤ a → m1.getMem a = (hdr N0 top c q).getMem a := by
  have r := Multilinear.SelectorPoint.hdr_reads
  simp only [vecCap, vecPtr, Layouts.Vec.cap, Layouts.Vec.ptr, BitVec.add_zero, Multilinear.SelectorPoint.at64_8]
    at hc hq
  intro a ha
  by_cases e1 : a = top + 18446744073709551552#64
  · subst e1; rw [hc]; exact (r N _ _ _).1.trans (r N0 _ _ _).1.symm
  by_cases e2 : a = top + 18446744073709551560#64
  · subst e2; rw [hq]; exact (r N _ _ _).2.1.trans (r N0 _ _ _).2.1.symm
  rw [k1 a ha (by
    simp only [GrowOut, rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero, hR,
      Multilinear.SelectorPoint.at64_8]
    exact fun h => h.elim e1 e2)]
  simp only [hdr]
  by_cases e3 : a = top + 18446744073709551568#64
  · subst e3; rw [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne e3, MachineState.getMem_setMem_ne e2, MachineState.getMem_setMem_ne e1,
      MachineState.getMem_setMem_ne e3, MachineState.getMem_setMem_ne e2, MachineState.getMem_setMem_ne e1, hN a ha]

/-- The header the code stored has room for `n ≤ c` elements past its length `0`. -/
theorem hdr_spare (N : MachineState) (top c q : Word) {n : Nat} (h : n ≤ c.toNat) :
    n ≤ (vecCap (hdr N top c q) (top + 18446744073709551552#64)).toNat -
      (vecLen (hdr N top c q) (top + 18446744073709551552#64)).toNat := by
  simp only [vecCap, vecLen, Layouts.Vec.cap, Layouts.Vec.len, BitVec.add_zero, Multilinear.SelectorPoint.at64_16,
    hdr]
  rw [(Multilinear.SelectorPoint.hdr_reads N top c q).1, (Multilinear.SelectorPoint.hdr_reads N top c q).2.2]
  simpa using h

set_option rv_sym.heap true in
/-- **`from_elem::<E>` is total**, with 64 bytes of stack beyond its callees'. -/
theorem e_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needR needH : Nat} (hnA : 64 + needA ≤ need) (hnR : 64 + needR ≤ need) (hnH : 64 + needH ≤ need)
    (hal : AllocT.AllocSpecT env p L.alloc.idx needA) (hres : ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hhe : Aborts env p L.handleError.idx needH) : FromElemSpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [80] with [hL] using [hal', hres, hhe]
  all_goals have hov := Multilinear.SelectorPoint.ovf hc_1
  all_goals try
    first
    | refine tail hp (by omega) hk hpre_3 hpre_5 ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩ hpre_8 hpre_9
        hpre_11 hpre_10 hpre_11.next_ge hpre_11.heapEnd_le hov _ _
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ 0#64 8#64
        (hdr_kept rfl (fun _ _ => rfl) keep1_1 ?_ ?_) ?_ hret1_15 hret1_25 ?_
    | refine tail hp (by omega) hk hpre_3 hpre_5 ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩ hpre_8 hpre_9
        hpre_11 hpre_10 hpre_11.next_ge hpre_11.heapEnd_le hov _ _
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (regs .x12) (r2 .x10)
        (hdr_kept rfl keep2_1 keep3_1 ?_ ?_) ?_ hret3_15 (hret3_25.trans hret2_19) ?_
  all_goals try simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero,
    Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
  all_goals try rv_closeT
  all_goals
    have hlim : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
    obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64⟩ := Multilinear.SelectorPoint.slots hlim
    obtain ⟨hF0, -⟩ := Multilinear.SelectorPoint.prologue (ret := ret) (regs := regs) hlim hpre_5
    have hgo : ∀ {R : Reg → Word} {M : MachineState} {b : Word}, R .x10 = top + 18446744073709551552#64 →
        GrowOut R M b → env.stackLimit.toNat ≤ b.toNat ∧ b.toNat < top.toNat := fun hx hb => by
      have := Multilinear.SelectorPoint.grow_in hx (by omega) hb; unfold InRange at this; omega
  -- no bytes: the dangling pointer
  · have h0 : (regs .x12).toNat = 0 := by have := hov.1; rw [hc] at this; simp at this; omega
    exact (hret1_17 (hdr_spare _ _ _ _ (by omega))).1
  · have h0 : (regs .x12).toNat = 0 := by have := hov.1; rw [hc] at this; simp at this; omega
    exact (hret1_17 (hdr_spare _ _ _ _ (by omega))).2
  · exact Multilinear.frame_call_own (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store hF0
      (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)) hret1_14 (by omega) fun b hb => hgo rfl hb
  · have := hov.1; rw [hc] at this; simp at this
    exact Or.inl ⟨by omega, trivial⟩
  -- a block from `alloc`
  · exact (hret3_17 (hdr_spare _ _ _ _ le_rfl)).1
  · exact (hret3_17 (hdr_spare _ _ _ _ le_rfl)).2
  · exact Multilinear.frame_call_own (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
      (Tactic.frame_call hF0 hret2_14 (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega)
      (by omega)) hret3_14 (by omega) fun b hb => hgo rfl hb
  · have hpos : 0 < (regs .x12).toNat := by
      rcases Nat.eq_zero_or_pos (regs .x12).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [hov.1, h]; rfl)) hc_2
      · exact h
    have hn3 := hret3_14.1
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
      at hn3
    refine Or.inr ⟨trivial, hpos, ⟨hret2_16, ?_⟩, hret2_17⟩
    rw [hov.1] at hret2_18
    omega

end Rv64mc.Proof.Runtime.FromElemT

/-- info: 'Rv64mc.Proof.Runtime.FromElemT.e_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.FromElemT.e_total
