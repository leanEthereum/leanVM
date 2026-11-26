/-
  Rv64mc.Proof.Runtime.FromIterET

  `<Vec<E> as SpecFromIterNested>::from_iter` over `verify_layer`'s `(s..e).map(|i| a[i / 64] * v[i % 64])` (the
  iterator at `a1`: the array's pointer, the vector's, `s`, `e`) is total: it counts the range (`0` when `s > e`),
  checks `16 n` fits an `isize` (else `handle_error`), allocates the buffer (`alloc`, the dangling pointer `8` for
  none), builds the header in its frame at `sp`, calls `Vec::reserve` for `n` (which keeps the header), and for each
  index checks `i < 25 * 64` and `i % 64` against the vector's length (else `panic_bounds_check`), multiplies the two
  elements (`E::mul`) and stores the product; then it copies the header to `sret`. Its result is a vector's
  (`VecReprT.VecT`) of `n` elements, its buffer fresh unless empty; the run ends with the guest's abort
  (`AbortStop`) where `alloc`, `handle_error` or a bounds check does. It does not state the products.

  The precondition: the result's slot as `FromIterOptT`'s; the iterator a caller's object in a window, the array of
  25 elements in a window, the vector a vector's (`VecT`) and a caller's object (`IterT`). At the image's one call
  site (`verify_layer`, template step 385) all three lie in the caller's frame.

  The proof is `FromIterOptT`'s for this frame: `rv_autoT` up to `reserve`'s return (instruction 104), `hdr_kept`,
  `tail`, `loop` (`Total.loop` at instruction 124, the indices left as the measure, `LInv`). In the loop the vector's
  header is read through the frame (`hKeep`); the two loads' windows are `arr_ok` and `vec_ok`.

  ## Main definitions

  * `count`, `IterT`, `PreT`, `PostT`, `SpecT`, `LInv`, `TailRegs`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.FromElemT
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Runtime.SpecExtendT
import Rv64mc.Gen.Tmpl.Alloc.Vec.SpecFromIterNested.VecE.AsSpecFromIterNestedEMapH4a41f075.FromIter

namespace Rv64mc.Proof.Runtime.FromIterET

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.FromElemT (keep_store)
open Rv64mc.Gen.Alloc.Vec.SpecFromIterNested.VecE.AsSpecFromIterNestedEMapH4a41f075.FromIter (Link tmpl)

/-- The number of elements of the range `[s, e)`. -/
def count (s e : Word) : Nat := e.toNat - s.toNat

/-- The iterator at `it`: its 32 bytes (the array's pointer, the vector's, the range's ends) a caller's in a window,
    8-byte aligned; the array of 25 elements in a window, 8-byte aligned; the vector a vector's and a caller's. -/
def IterT (env : Env) (m : MachineState) (sp it : Word) : Prop :=
  InWin env it 32 ∧ it.toNat % 8 = 0 ∧ env.Owned m sp it 32 ∧
    InWin env (m.getMem it) 400 ∧ (m.getMem it).toNat % 8 = 0 ∧
    VecT env m (m.getMem (it + 8#64)) 16 ∧ env.Owned m sp (m.getMem (it + 8#64)) 24

/-- The total precondition: the result's slot a caller's (`SretPre`), in a window and 8-byte aligned; the iterator
    `IterT`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) Layouts.Vec.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    IterT env m (regs .x2) (regs .x11)

/-- The total postcondition: the result a vector's (`VecT`) of the range's length, its buffer fresh unless empty. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧
    (vecLen m' (regs .x10)).toNat = count (m.getMem (regs .x11 + 16#64)) (m.getMem (regs .x11 + 24#64)) ∧
    ((vecLen m' (regs .x10)).toNat = 0 ∨
      env.Fresh m m' (vecPtr m' (regs .x10)) ((vecLen m' (regs .x10)).toNat * 16))

/-- **The total contract of `Vec<E>`'s `spec_from_iter_nested` over `verify_layer`'s products**, or the guest's
    abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) SretVecOut AbortStop

/-- The prologue's nine saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)

/-- The header in the frame, at `sp`: capacity `c`, pointer `q`, length `0`. -/
def hdr (N : MachineState) (top c q : Word) : MachineState :=
  ((N.setMem (top + 18446744073709551520#64) c).setMem (top + 18446744073709551528#64) q).setMem
    (top + 18446744073709551536#64) 0#64

/-- The loop's head with `k + 1` passes left: the index `x19` from `s` below `e`, the count `x9` of elements
    stored, the cursor `x23` 8 bytes into the next one of the block `q`; `x22` the bound the index is checked
    against (`1600`, or `s` past it). -/
def LInv (env : Env) (m M0 : MachineState) (top ret c q A V s e X : Word) (regs : Reg → Word) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551520#64 ∧ R .x8 = regs .x10 ∧ R .x18 = A ∧ R .x20 = e ∧ R .x21 = V ∧
    R .x22 = X ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    (R .x19).toNat + (k + 1) = e.toNat ∧ s.toNat ≤ (R .x19).toNat ∧ (R .x9).toNat = (R .x19).toNat - s.toNat ∧
    (R .x23).toNat = q.toNat + 16 * (R .x9).toNat + 8 ∧
    ((X.toNat = 1600 ∧ (R .x19).toNat ≤ 1600) ∨ X = R .x19) ∧
    (∀ a, top + 18446744073709551520#64 ≤ a → M.getMem a = (hdr (saved m top ret regs) top c q).getMem a) ∧
    env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code ∧ (env.next M0).toNat ≤ (env.next M).toNat

/-- The count the code computes, `e - s` masked to `0` when `s > e`. -/
theorem cnt_toNat (s e : Word) :
    ((BinOp.ult.eval e (e - s) + 18446744073709551615#64) &&& (e - s)).toNat = e.toNat - s.toNat := by
  simp only [BinOp.eval, BitVec.ult]
  by_cases h : s.toNat ≤ e.toNat
  · have hd : (e - s).toNat = e.toNat - s.toNat := by rw [BitVec.toNat_sub]; omega
    have hlt : ¬ (e.toNat < (e - s).toNat) := by omega
    simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [show (0 : Word) + 18446744073709551615#64 = BitVec.allOnes 64 by decide, BitVec.allOnes_and, hd]
  · have hd : (e - s).toNat = 2 ^ 64 - s.toNat + e.toNat := by rw [BitVec.toNat_sub]; have := s.isLt; omega
    have hlt : e.toNat < (e - s).toNat := by have := s.isLt; omega
    simp only [hlt, decide_true, ↓reduceIte]
    rw [show (1 : Word) + 18446744073709551615#64 = 0#64 by decide, BitVec.zero_and]
    simp only [BitVec.toNat_ofNat]
    omega

/-- The header's pointer, from its address. -/
theorem at8 (t : Word) : t + 18446744073709551520#64 + BitVec.ofNat 64 8 = t + 18446744073709551528#64 := by
  rw [BitVec.add_assoc]; rfl

/-- The header's length, from its address. -/
theorem at16 (t : Word) : t + 18446744073709551520#64 + BitVec.ofNat 64 16 = t + 18446744073709551536#64 := by
  rw [BitVec.add_assoc]; rfl

/-- The header's words, read back. -/
theorem hdr_reads (N : MachineState) (t c q : Word) :
    (hdr N t c q).getMem (t + 18446744073709551520#64) = c ∧ (hdr N t c q).getMem (t + 18446744073709551528#64) = q ∧
      (hdr N t c q).getMem (t + 18446744073709551536#64) = 0#64 := by
  simp only [hdr]
  refine ⟨?_, ?_, MachineState.getMem_setMem_eq⟩
  · rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)),
      MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]

/-- **The header's words after `reserve`**, at and above the frame's start: `FromElemT.hdr_kept` for this frame. -/
theorem hdr_kept {N N0 m1 m' : MachineState} {top c q : Word} {R : Reg → Word}
    (hR : R .x10 = top + 18446744073709551520#64)
    (hN : ∀ a, top + 18446744073709551520#64 ≤ a → N.getMem a = N0.getMem a)
    (k1 : ∀ a, top + 18446744073709551520#64 ≤ a → ¬ GrowOut R m' a → m1.getMem a = (hdr N top c q).getMem a)
    (hc : vecCap m1 (top + 18446744073709551520#64) = vecCap (hdr N top c q) (top + 18446744073709551520#64))
    (hq : vecPtr m1 (top + 18446744073709551520#64) = vecPtr (hdr N top c q) (top + 18446744073709551520#64)) :
    ∀ a, top + 18446744073709551520#64 ≤ a → m1.getMem a = (hdr N0 top c q).getMem a := by
  have r := hdr_reads
  simp only [vecCap, vecPtr, Layouts.Vec.cap, Layouts.Vec.ptr, BitVec.add_zero, at8] at hc hq
  intro a ha
  by_cases e1 : a = top + 18446744073709551520#64
  · subst e1; rw [hc]; exact (r N _ _ _).1.trans (r N0 _ _ _).1.symm
  by_cases e2 : a = top + 18446744073709551528#64
  · subst e2; rw [hq]; exact (r N _ _ _).2.1.trans (r N0 _ _ _).2.1.symm
  rw [k1 a ha (by
    simp only [GrowOut, rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero, hR, at8]
    exact fun h => h.elim e1 e2)]
  simp only [hdr]
  by_cases e3 : a = top + 18446744073709551536#64
  · subst e3; rw [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne e3, MachineState.getMem_setMem_ne e2, MachineState.getMem_setMem_ne e1,
      MachineState.getMem_setMem_ne e3, MachineState.getMem_setMem_ne e2, MachineState.getMem_setMem_ne e1, hN a ha]

/-- The header the code stored has room for `n ≤ c` elements past its length `0`. -/
theorem hdr_spare (N : MachineState) (top c q : Word) {n : Nat} (h : n ≤ c.toNat) :
    n ≤ (vecCap (hdr N top c q) (top + 18446744073709551520#64)).toNat -
      (vecLen (hdr N top c q) (top + 18446744073709551520#64)).toNat := by
  simp only [vecCap, vecLen, Layouts.Vec.cap, Layouts.Vec.len, BitVec.add_zero, at16]
  rw [(hdr_reads N top c q).1, (hdr_reads N top c q).2.2]
  simpa using h

/-- The prologue's stores stay in the frame. -/
theorem saved_frame {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    env.Frame top Tactic.F m (saved m top ret regs) := by
  have := top.isLt
  simp only [saved]
  repeat (first | exact Tactic.frame_refl hnx | refine Tactic.frame_store ?_ ?_ ?_)
  all_goals (rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega)

/-- The header's stores stay in the frame. -/
theorem hdr_frame {env : Env} {m N : MachineState} {top c q : Word} (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hF : env.Frame top Tactic.F m N) : env.Frame top Tactic.F m (hdr N top c q) := by
  have := top.isLt
  refine Tactic.frame_store (Tactic.frame_store (Tactic.frame_store hF ?_ ?_) ?_ ?_) ?_ ?_ <;>
    (rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega)

/-- `reserve`'s `out`, the header's two words, lies in the frame. -/
theorem grow_stack {env : Env} {top b : Word} {R : Reg → Word} {M : MachineState}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hx : R .x10 = top + 18446744073709551520#64)
    (hb : GrowOut R M b) : env.stackLimit.toNat ≤ b.toNat ∧ b.toNat < top.toNat := by
  have s96 : (top + 18446744073709551520#64).toNat = top.toNat - 96 :=
    Multilinear.slot_toNat (by decide) (by omega) (by decide)
  have := SpecExtendT.grow_in hx (by omega) hb
  unfold InRange at this
  omega

/-- The index below `1600` past the check against the bound. -/
theorem idx_lt {X i : Word} (hX : (X.toNat = 1600 ∧ i.toNat ≤ 1600) ∨ X = i) (hne : ¬ X = i) : i.toNat < 1600 := by
  rcases hX with ⟨h1, h2⟩ | h
  · refine Nat.lt_of_le_of_ne h2 fun h => hne (BitVec.eq_of_toNat_eq (by omega))
  · exact absurd h hne

/-- The array's element `i / 64`, as the code addresses it, in a window and aligned. -/
theorem arr_ok {env : Env} {top : Word} {m : MachineState} {A i : Word} (hW : Windows env top m)
    (hA : InWin env A 400) (hA8 : A.toNat % 8 = 0) (hi : i.toNat < 1600) :
    (inWindow (A + i >>> 6 <<< 4) 8 = true ∧ (A + i >>> 6 <<< 4).toNat % 8 = 0) ∧
      (inWindow (A + i >>> 6 <<< 4 + 8#64) 8 = true ∧ (A + i >>> 6 <<< 4 + 8#64).toNat % 8 = 0) := by
  have hq : (i >>> 6).toNat = i.toNat / 64 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt := hA.lt
  have hx : (A + i >>> 6 <<< 4).toNat = A.toNat + 16 * (i.toNat / 64) := by
    rw [WinT.elem_toNat (by rw [hq]; omega), hq]; rfl
  refine ⟨hA.dword hW hA8 hx (by omega) (by omega), hA.dword hW hA8 (o := 16 * (i.toNat / 64) + 8) ?_ (by omega)
    (by omega)⟩
  rw [toNat_add_ofNat (by omega), hx]; omega

/-- The vector's element `i % 64`, below its length, as the code addresses it, in a window and aligned. -/
theorem vec_ok {env : Env} {top : Word} {m : MachineState} {C P Lw i : Word} (hW : Windows env top m)
    (hb : BufT env m C P 16) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hl : Lw.toNat ≤ C.toNat)
    (hi : i &&& 63#64 < Lw) :
    (inWindow (P + (i &&& 63#64) <<< 4) 8 = true ∧ (P + (i &&& 63#64) <<< 4).toNat % 8 = 0) ∧
      (inWindow (P + (i &&& 63#64) <<< 4 + 8#64) 8 = true ∧
        (P + (i &&& 63#64) <<< 4 + 8#64).toNat % 8 = 0) := by
  have hi' := BitVec.lt_def.1 hi
  rcases hb with h0 | ⟨hge, hlive, hal⟩
  · omega
  have hw : InWin env P (C.toNat * 16) := .inl ⟨hge, by unfold Env.Live at hlive; omega⟩
  have hlt := hw.lt
  have hx : (P + (i &&& 63#64) <<< 4).toNat = P.toNat + 16 * (i &&& 63#64).toNat := by
    rw [WinT.elem_toNat (by omega)]; rfl
  refine ⟨hw.dword hW hal hx (by omega) (by omega), hw.dword hW hal (o := 16 * (i &&& 63#64).toNat + 8) ?_
    (by omega) (by omega)⟩
  rw [toNat_add_ofNat (by omega), hx]; omega

set_option maxHeartbeats 2000000 in
set_option rv_sym.heap true in
/-- **The loop**, from its head; past its last pass the header is copied to `sret`. -/
theorem loop {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needP : Nat} (hn : 96 ≤ need) (hnM : 96 + needM ≤ need) (hnP : 96 + needP ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needM) (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m M0 : MachineState}
    {c q A V s e X : Word}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hwin : InWin env (regs .x10) Layouts.Vec.byteSize)
    (hal : (regs .x10).toNat % 8 = 0) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hge : 0x10000000 ≤ (env.next m).toNat)
    (hAw : InWin env A 400) (hA8 : A.toNat % 8 = 0) (hVw : InWin env V 24) (hV8 : V.toNat % 8 = 0)
    (hVo : V.toNat + 24 ≤ (env.next m).toNat ∨ top.toNat ≤ V.toNat)
    (hVb : BufT env m (m.getMem V) (m.getMem (V + 8#64)) 16)
    (hVl : (m.getMem (V + 16#64)).toNat ≤ (m.getMem V).toNat)
    (hs : m.getMem (regs .x11 + 16#64) = s) (he : m.getMem (regs .x11 + 24#64) = e)
    (hc : c.toNat = e.toNat - s.toNat) (hlt : s.toNat < e.toNat) (h63 : 16 * c.toNat < 2 ^ 63)
    (hfr : env.Fresh m M0 q (c.toNat * 16)) (hq8 : q.toNat % 8 = 0)
    (hF0 : (env.next M0).toNat ≤ env.heapEnd.toNat) :
    ∀ k R M, LInv env m M0 top ret c q A V s e X regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 124, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env m M0 top ret c q A V s e X regs) fun k R M hI ih => ?_
  have hlay := env.layout
  have hfr1 := hfr.1
  have hfr2 := hfr.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hk1, hi1, hj1, hx23, hX, hK, hF, hS, hcode, hnM⟩ := id hI
  clear hK
  have hKeep := SpecExtendT.keep_of_frame hF (by omega)
  have hnmM := hF.1
  rv_introT hI
  simp only [hdr, saved] at hI_16
  rv_symT hp stop [124] with [hL, hKeep] using [hmul, hpb]
  all_goals try
    have hi := idx_lt hI_15 hc_2
    first
    | exact (arr_ok hW hAw hA8 hi).1.1
    | exact (arr_ok hW hAw hA8 hi).1.2
    | exact (arr_ok hW hAw hA8 hi).2.1
    | exact (arr_ok hW hAw hA8 hi).2.2
    | exact (vec_ok hW hVb hnx hVl hc).1.1
    | exact (vec_ok hW hVb hnx hVl hc).1.2
    | exact (vec_ok hW hVb hnx hVl hc).2.1
    | exact (vec_ok hW hVb hnx hVl hc).2.2
  · -- back to the head
    have hi1 : (R .x19 + 1#64).toNat = (R .x19).toNat + 1 := toNat_add_ofNat (by have := e.isLt; omega)
    have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [hi1]; subst h0; omega))
    clear hc
    refine ih (k - 1) _ _ (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    all_goals try rv_closeT
    · have hi := idx_lt hI_15 hc_2
      refine Or.inl ⟨?_, by rw [hi1]; omega⟩
      rcases hI_15 with h | h
      · exact h.1
      · exact absurd h hc_2
    · have ht96 : (top + 18446744073709551520#64).toNat = top.toNat - 96 :=
        Multilinear.slot_toNat (by decide) (by omega) (by decide)
      have hj : (R .x9).toNat < c.toNat := by omega
      have h23 : (R .x23).toNat < (top + 18446744073709551520#64).toNat := by
        have := hF.2.1; omega
      have h23' : (R .x23 + 18446744073709551608#64).toNat < (top + 18446744073709551520#64).toNat := by
        rw [CloneT.toNat_add_neg (k := 8) rfl (by omega)]; omega
      exact keep_store (keep_store (fun a ha => (keep3_1 a ha).trans (hI_16 a ha)) h23') h23
  all_goals try simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
  all_goals try rv_closeT
  · have hi1 : (R .x19 + 1#64).toNat = (R .x19).toNat + 1 := toNat_add_ofNat (by have := e.isLt; omega)
    have hx9 : (R .x9 + 1#64).toNat = (R .x9).toNat + 1 := toNat_add_ofNat (by have := e.isLt; omega)
    rw [hs, he, hx9, hI_13]
    unfold count
    rw [hc, hi1]
    omega

/-- The registers at `reserve`'s return. -/
def TailRegs (top A V s e nw : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551520#64 ∧ R .x8 = regs .x10 ∧ R .x9 = nw ∧ R .x18 = A ∧ R .x19 = s ∧ R .x20 = e ∧
    R .x21 = V ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

set_option maxHeartbeats 1000000 in
set_option rv_sym.heap true in
/-- **From `reserve`'s return**: an empty range straight to the copy, else into the loop. -/
theorem tail {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needP : Nat} (hn : 96 ≤ need) (hnM : 96 + needM ≤ need) (hnP : 96 + needP ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needM) (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    {A V s e nw : Word}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hwin : InWin env (regs .x10) Layouts.Vec.byteSize)
    (hal : (regs .x10).toNat % 8 = 0) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hge : 0x10000000 ≤ (env.next m).toNat)
    (hAw : InWin env A 400) (hA8 : A.toNat % 8 = 0) (hVw : InWin env V 24) (hV8 : V.toNat % 8 = 0)
    (hVo : V.toNat + 24 ≤ (env.next m).toNat ∨ top.toNat ≤ V.toNat)
    (hVb : BufT env m (m.getMem V) (m.getMem (V + 8#64)) 16)
    (hVl : (m.getMem (V + 16#64)).toNat ≤ (m.getMem V).toNat)
    (hs : m.getMem (regs .x11 + 16#64) = s) (he : m.getMem (regs .x11 + 24#64) = e)
    (hnw : nw.toNat = e.toNat - s.toNat) (h63 : 16 * nw.toNat < 2 ^ 63)
    (R : Reg → Word) (M : MachineState) (hR : TailRegs top A V s e nw regs R) (c q : Word)
    (hK : ∀ a, top + 18446744073709551520#64 ≤ a → M.getMem a = (hdr (saved m top ret regs) top c q).getMem a)
    (hF : env.Frame top Tactic.F m M) (hS : env.Static M) (hcode : M.code = m.code)
    (hcq : (nw.toNat = 0 ∧ c = 0#64) ∨
      (c = nw ∧ 0 < nw.toNat ∧ env.Fresh m M q (c.toNat * 16) ∧ q.toNat % 8 = 0)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 104, ret, top⟩ :: rest, R, M⟩ := by
  have hK' := hK
  simp only [hdr, saved] at hK
  rv_introT hR
  rcases hcq with ⟨hn0, rfl⟩ | ⟨rfl, hpos, hfr, hq8⟩
  · rv_symT hp stop [124] with [hL] using [hmul, hpb]
    all_goals try (exfalso; have := BitVec.lt_def.1 hc_1; omega)
    all_goals try simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
    all_goals try rv_closeT
    rw [hs, he]
    unfold count
    rw [← hnw, hn0]
    rfl
  · have hfr1 := hfr.1
    have hfr2 := hfr.2
    have hFn := hF.2.1
    rv_symT hp stop [124] with [hL] using [hmul, hpb]
    all_goals
      have hlt : s.toNat < e.toNat := by omega
      have hq8' : (q + 8#64).toNat = q.toNat + 8 := toNat_add_ofNat (by omega)
    all_goals try (exfalso; have := BitVec.le_def.1 hc; omega)
    · refine loop (X := s) hp hL hn hnM hnP hmul hpb hk hstop hstk hnx hown hwin hal hW h16 hge hAw hA8 hVw hV8 hVo
        hVb hVl hs he hnw hlt h63 hfr hq8 hFn (e.toNat - s.toNat - 1) _ _ ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hK', hF, hS, hcode, Nat.le_refl _⟩
      all_goals simp only [Tactic.rf]
      all_goals try rv_closeT
      exact Or.inr trivial
    · refine loop (X := 1600#64) hp hL hn hnM hnP hmul hpb hk hstop hstk hnx hown hwin hal hW h16 hge hAw hA8 hVw
        hV8 hVo hVb hVl hs he hnw hlt h63 hfr hq8 hFn (e.toNat - s.toNat - 1) _ _ ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hK', hF, hS, hcode, Nat.le_refl _⟩
      all_goals simp only [Tactic.rf]
      all_goals try rv_closeT
      exact Or.inl ⟨rfl, BitVec.le_def.1 hc⟩

set_option maxHeartbeats 2000000 in
set_option rv_sym.heap true in
/-- **`spec_from_iter_nested` for `verify_layer`'s `Vec<E>` is total**, with 96 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needR needH needM needP : Nat} (hnA : 96 + needA ≤ need) (hnR : 96 + needR ≤ need)
    (hnH : 96 + needH ≤ need) (hnM : 96 + needM ≤ need) (hnP : 96 + needP ≤ need)
    (hal : AllocT.AllocSpecT env p L.alloc.idx needA) (hres : ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hhe : Aborts env p L.handleError.idx needH) (hmul : Field.EMulT.specT env p L.mul.idx needM)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [104] with [hL] using [hal', hres, hhe]
  all_goals
    have hov := Multilinear.SelectorPoint.ovf hc_1
    have hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
    have hVo : (m.getMem (regs .x11 + 8#64)).toNat + 24 ≤ (env.next m).toNat ∨
        top.toNat ≤ (m.getMem (regs .x11 + 8#64)).toNat := by rw [← hpre_2]; exact hpre_22
    have hVb : BufT env m (m.getMem (m.getMem (regs .x11 + 8#64)))
        (m.getMem (m.getMem (regs .x11 + 8#64) + 8#64)) 16 := by
      simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero] at hpre_19
      exact hpre_19
    have hVl : (m.getMem (m.getMem (regs .x11 + 8#64) + 16#64)).toNat ≤
        (m.getMem (m.getMem (regs .x11 + 8#64))).toNat := by
      rwa [ReserveT.vecLen_eq, ReserveT.vecCap_eq] at hpre_21
  on_goal 11 =>
    refine tail hp hL (by omega) hnM hnP hmul hpb hk hstop hpre_3 hpre_5 hown hpre_8 hpre_9 hpre_25 hpre_24
      hpre_25.next_ge hpre_14 hpre_15 hpre_16 hpre_18 hVo hVb hVl rfl rfl (cnt_toNat _ _) hov.2 _ _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ _ (r2 .x10)
      (hdr_kept rfl keep2_1 keep3_1 ?_ ?_) ?_ hret3_15 (hret3_25.trans hret2_19) ?_
  on_goal 5 =>
    refine tail hp hL (by omega) hnM hnP hmul hpb hk hstop hpre_3 hpre_5 hown hpre_8 hpre_9 hpre_25 hpre_24
      hpre_25.next_ge hpre_14 hpre_15 hpre_16 hpre_18 hVo hVb hVl rfl rfl (cnt_toNat _ _) hov.2 _ _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ 0#64 8#64
      (hdr_kept rfl (fun _ _ => rfl) keep1_1 ?_ ?_) ?_ hret1_15 hret1_25 ?_
  all_goals try simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero,
    Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
  all_goals try rv_closeT
  all_goals
    have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
    have hF0 : env.Frame top Tactic.F m (saved m top ret regs) := saved_frame hlim hpre_5
    have s96 : (top + 18446744073709551520#64).toNat = top.toNat - 96 :=
      Multilinear.slot_toNat (by decide) (by omega) (by decide)
  -- no bytes: the dangling pointer
  · have h0 := hov.1; rw [hc] at h0; simp only [BitVec.toNat_ofNat] at h0
    exact (hret1_17 (hdr_spare _ _ _ _ (by simp only [BitVec.toNat_ofNat]; omega))).1
  · have h0 := hov.1; rw [hc] at h0; simp only [BitVec.toNat_ofNat] at h0
    exact (hret1_17 (hdr_spare _ _ _ _ (by simp only [BitVec.toNat_ofNat]; omega))).2
  · exact Multilinear.frame_call_own (hdr_frame hlim hF0) hret1_14 (by omega) fun b hb => grow_stack hlim rfl hb
  · have h0 := hov.1; rw [hc] at h0; simp only [BitVec.toNat_ofNat] at h0
    exact Or.inl ⟨by omega, trivial⟩
  -- a block from `alloc`
  · exact (hret3_17 (hdr_spare _ _ _ _ le_rfl)).1
  · exact (hret3_17 (hdr_spare _ _ _ _ le_rfl)).2
  · exact Multilinear.frame_call_own (hdr_frame hlim (Tactic.frame_call hF0 hret2_14 (by omega))) hret3_14
      (by omega) fun b hb => grow_stack hlim rfl hb
  · have hpos := hc_2
    rw [← BitVec.toNat_inj, hov.1] at hpos
    have hn3 := hret3_14.1
    have s80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 :=
      Multilinear.slot_toNat (by decide) (by omega) (by decide)
    have s88 : (top + 18446744073709551528#64).toNat = top.toNat - 88 :=
      Multilinear.slot_toNat (by decide) (by omega) (by decide)
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
      at hn3
    refine Or.inr ⟨trivial, by simp only [BitVec.toNat_ofNat] at hpos; omega, ⟨hret2_16, ?_⟩, hret2_17⟩
    rw [hov.1] at hret2_18
    omega

end Rv64mc.Proof.Runtime.FromIterET

/-- info: 'Rv64mc.Proof.Runtime.FromIterET.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.FromIterET.total
