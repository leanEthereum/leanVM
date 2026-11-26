/-
  Rv64mc.Proof.Keccak.LinearTransposeT

  `linear_transpose::<E>`'s partial proof (`LinearTranspose.lean`) ported to `HoldsT`, loop by loop: each loop of
  the partial proof, there an induction on the positions left with a continuation, is `Total.loop` here with them as
  the measure, the partial invariant and the code map kept.

  ## Main definitions

  * `LInv2`

  ## Main results

  * `loop2`: the column sums
-/

import Rv64mc.Proof.Keccak.LinearTranspose
import Rv64mc.Proof.Keccak.TryFromFnT
import Rv64mc.Proof.Runtime.MemsetBytesT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Keccak.LinearTransposeT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters
open Rv64mc.Spec.Keccak.LinearTranspose Rv64mc.Proof.Keccak.LinearTranspose
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT)
open Rv64mc.Gen.Verifier.Keccak.LinearTransposeE (Link tmpl)
open Rv64mc.Proof.Multilinear (step_ptr)

/-- The total precondition: `Pre`, the result's slot in a window and 8-byte aligned, the slice in a window and
    8-byte aligned unless empty (`TryFromFnT.SliceT`). -/
def PreT (env : Env) (ws : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env ws regs m ∧ InWin env (regs .x10) Layouts.Vec.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    TryFromFnT.SliceT env (regs .x11) (regs .x12).toNat

/-- The total postcondition: `Post`, and the result a vector's (`VecT`). -/
def PostT (env : Env) (ws : List E) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  Post env ws regs m r' m' ∧ VecT env m' (regs .x10) 16

/-- **The total contract of `linear_transpose::<E>`**: `LinearTranspose.spec`'s, as a `HoldsT` from `PreT`, with
    `VecT` of the result, or the guest's abort (`assert_eq!` on a slice of another length, `alloc`, `handle_error`). -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ ws, HoldsT env p i need (PreT env ws) (PostT env ws) Out AbortStop

/-- The column loop's head with `k + 1` positions left: `Inv2` after the others, and the code map kept. -/
def LInv2 (env : Env) (ws : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  ∃ j, j + k + 1 = 1600 ∧ Inv2 env ws ret top regs m j R M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **The column sums**, from the loop's head to its exit (instruction 190). -/
theorem loop2 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {ws : List E}
    (hp : p[i]? = some (tmpl L)) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} (htop : env.stackLimit.toNat + 30816 ≤ top.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hnext : ∀ R M, Exit2 env ws ret top regs m R M → M.code = m.code →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 190, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv2 env ws ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 154, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv2 env ws ret top regs m) fun k R M hI ih => ?_
  obtain ⟨j, hj, hI, hcode⟩ := hI
  have hjl : j < 1600 := by omega
  have := top.isLt
  have hgb := gBase_toNat (top := top) (by omega)
  have hcb := colsBase_toNat (top := top) (by omega)
  have g0 : (top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * j)).toNat = top.toNat - 30792 + 16 * j := by
    rw [toNat_elem (by omega), hgb]
  have g8 : (top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * j) + 8#64).toNat =
      top.toNat - 30792 + 16 * j + 8 := by
    rw [toNat_elem8 (by omega), hgb]
  obtain ⟨c0, c8⟩ := cols_elem (top := top) (by omega) (Nat.mod_lt j (show 320 > 0 by decide))
  rv_introT hI
  rv_symT hp stop [168]
  rw [cols_addr _ hjl, cols_addr8 _ hjl]
  rv_symT hp stop [154, 190]
  all_goals simp only [(hI_23 _ (Nat.mod_lt _ (show 320 > 0 by decide))).1,
    (hI_23 _ (Nat.mod_lt _ (show 320 > 0 by decide))).2, (hI_22 _ hjl).1, (hI_22 _ hjl).2]
  all_goals obtain ⟨f1, f2, f3, f4⟩ := loop2_mem htop hjl hI_13 hI_14 hI_22 hI_23
  · -- back to the head
    have hk0 : k ≠ 0 := fun h0 => hc (by rw [succ_ofNat, show j + 1 = 1600 by omega])
    clear hc
    refine ih (k - 1) _ _ (by omega) ⟨j + 1, by omega, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, f1, f2⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, f3, f4⟩, hcode⟩
    all_goals rv_closeT
    · exact step16 _ _
    · exact succ_ofNat _
    · exact step_ptr _ _
    · exact step_ptr _ _
  · have hj1 : j + 1 = 1600 := by
      rw [succ_ofNat] at hc; exact (ofNat_inj (by omega) (by decide)).1 hc
    clear hc
    refine hnext _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, f1, f2⟩, f3, by rw [← hj1]; exact f4⟩ hcode
    all_goals rv_closeT

/-- An element of the column sums' rows, at offset `o`, as a number. -/
theorem cols_toNat {env : Env} {top : Word} (htop : env.stackLimit.toNat + 30816 ≤ top.toNat) {o : Nat}
    (ho : o + 16 ≤ 5120) (h16 : o % 16 = 0) :
    (top + 18446744073709546424#64 + BitVec.ofNat 64 o).toNat = top.toNat - 5192 + o ∧
      (top + 18446744073709546424#64 + BitVec.ofNat 64 o + 8#64).toNat = top.toNat - 5192 + o + 8 := by
  have hcb := colsBase_toNat (top := top) (by omega)
  have := top.isLt
  have e : (top + 18446744073709546424#64 + BitVec.ofNat 64 o).toNat = top.toNat - 5192 + o := by
    rw [BitVec.toNat_add, hcb, BitVec.toNat_ofNat]; omega
  refine ⟨e, ?_⟩
  rw [BitVec.toNat_add, e]; simp only [BitVec.toNat_ofNat]; omega

/-- The result's loop's head with `k + 1` positions left: `Inv3` after the others, and the code map kept. -/
def LInv3 (env : Env) (ws : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (P : Word) (cap k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  ∃ j, j + k + 1 = 1600 ∧ Inv3 env ws ret top regs m P cap j R M ∧ M.code = m.code

set_option hygiene false in
/-- One pass of the result's loop after its last stop: the column reads and `g`'s read, the stores made the next
    position's (`loop3_mem`), and the head (`ih`) or the exit (`hfin`). -/
macro "lt3_close" : tactic => `(tactic| (
  simp (disch := omega) only [PairsAt.get0 hI_25, PairsAt.get1 hI_25, (hI_24 _ hjl).1, (hI_24 _ hjl).2]
  rw [(outE_limbs ws (by omega) (by omega)).1, (outE_limbs ws (by omega) (by omega)).2]
  have hm := loop3_mem htop hjl ⟨hI_22, hI_23, hI_24, hI_25, hI_26, hI_27, hI_28, hI_29, hI_30, hI_31, hI_32⟩
  first
  | (have hk0 : k ≠ 0 := fun h0 => hc (by rw [succ_ofNat, show j + 1 = 1600 by omega])
     clear hc
     have m1 := hm.1
     have m2 := hm.2.1
     refine ih (k - 1) _ _ (by omega) ⟨j + 1, by omega, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, m1, m2⟩,
       ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm⟩, hcode⟩
     all_goals rv_closeT
     all_goals first | exact succ_ofNat _ | exact step_ptr _ _)
  | (have e : j + 1 = 1600 := (ofNat_inj (by omega) (by omega)).1 ((succ_ofNat j).symm.trans hc)
     rw [e] at hm
     have m1 := hm.1
     have m2 := hm.2.1
     refine hfin _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, m1, m2⟩, ?_, ?_, hm⟩ hcode
     all_goals rv_closeT
     all_goals exact hc)))

set_option maxHeartbeats 1000000 in
set_option rv_sym.heap true in
/-- **The result's loop**, from its head to its exit (instruction 332). -/
theorem loop3 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {ws : List E}
    (hp : p[i]? = some (tmpl L)) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} {P : Word} {cap : Nat}
    (htop : env.stackLimit.toNat + 30816 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (_hge : 0x10000000 ≤ (env.next m).toNat) (hP8 : P.toNat % 8 = 0)
    (hfin : ∀ R M, Exit3 env ws ret top regs m P cap R M → M.code = m.code →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 332, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv3 env ws ret top regs m P cap k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 314, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv3 env ws ret top regs m P cap) fun k R M hI ih => ?_
  obtain ⟨j, hj, hI, hcode⟩ := hI
  have hjl : j < 1600 := by omega
  have := top.isLt
  have hgb := gBase_toNat (top := top) (by omega)
  have hcb := colsBase_toNat (top := top) (by omega)
  have g0 : (top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * j)).toNat = top.toNat - 30792 + 16 * j := by
    rw [toNat_elem (by omega), hgb]
  have g8 : (top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * j) + 8#64).toNat =
      top.toNat - 30792 + 16 * j + 8 := by
    rw [toNat_elem8 (by omega), hgb]
  obtain ⟨-, -, -, -, -, -, -, -, hF3, -, -, -, -, -, -, hP1, hP2, hc1, hc2⟩ := id hI
  have hFn := hF3.2.1
  have e0 : (P + BitVec.ofNat 64 (16 * j)).toNat = P.toNat + 16 * j := toNat_elem (by omega)
  have e8 : (P + BitVec.ofNat 64 (16 * j) + 8#64).toNat = P.toNat + 16 * j + 8 := toNat_elem8 (by omega)
  rv_introT hI
  rv_symT hp stop [248, 250, 286, 314, 332]
  · rw [xval hjl] at hc ⊢
    have hx : j / 64 % 5 = 0 := by rw [ofNat_inj (by omega) (by decide)] at hc; exact hc
    rw [hx]
    clear hc
    rv_symT hp stop [286, 314, 332]
    rv_symT hp stop [286, 314, 332]
    rw [maskA0, colA_eq, colB0_eq]
    obtain ⟨a0, a8⟩ := cols_toNat htop (o := 16 * (j % 64) + 1024) (by omega) (by omega)
    obtain ⟨b0, b8⟩ := cols_toNat htop (o := 4096 + 16 * ((j + 1) % 64)) (by omega) (by omega)
    rv_symT hp stop [314, 332]
    all_goals lt3_close
  · rw [xval hjl] at hc ⊢
    have hx : j / 64 % 5 = 1 ∨ j / 64 % 5 = 2 ∨ j / 64 % 5 = 3 ∨ j / 64 % 5 = 4 := by
      rw [ofNat_inj (by omega) (by decide)] at hc; omega
    clear hc
    rcases hx with hx | hx | hx | hx
    · rw [hx]
      rv_symT hp stop [286, 314, 332]
      rw [maskA1, rowB1, colA_eq, colB_eq]
      obtain ⟨a0, a8⟩ := cols_toNat htop (o := 16 * (j % 64) + 2048) (by omega) (by omega)
      obtain ⟨b0, b8⟩ := cols_toNat htop (o := 0 + 16 * ((j + 1) % 64)) (by omega) (by omega)
      rv_symT hp stop [314, 332]
      all_goals lt3_close
    · rw [hx]
      rv_symT hp stop [286, 314, 332]
      rw [maskA2, rowB2, colA_eq, colB_eq]
      obtain ⟨a0, a8⟩ := cols_toNat htop (o := 16 * (j % 64) + 3072) (by omega) (by omega)
      obtain ⟨b0, b8⟩ := cols_toNat htop (o := 1024 + 16 * ((j + 1) % 64)) (by omega) (by omega)
      rv_symT hp stop [314, 332]
      all_goals lt3_close
    · rw [hx]
      rv_symT hp stop [286, 314, 332]
      rw [maskA3, rowB3, colA_eq, colB_eq]
      obtain ⟨a0, a8⟩ := cols_toNat htop (o := 16 * (j % 64) + 4096) (by omega) (by omega)
      obtain ⟨b0, b8⟩ := cols_toNat htop (o := 2048 + 16 * ((j + 1) % 64)) (by omega) (by omega)
      rv_symT hp stop [314, 332]
      all_goals lt3_close
    · rw [hx]
      rv_symT hp stop [286, 314, 332]
      rw [maskA4, rowB4, colA_eq, colB_eq]
      obtain ⟨a0, a8⟩ := cols_toNat htop (o := 16 * (j % 64) + 0) (by omega) (by omega)
      obtain ⟨b0, b8⟩ := cols_toNat htop (o := 3072 + 16 * ((j + 1) % 64)) (by omega) (by omega)
      rv_symT hp stop [314, 332]
      all_goals lt3_close

set_option rv_sym.heap true in
/-- **The return**: the header into the result's slot, the saved registers back. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {ws : List E}
    (hp : p[i]? = some (tmpl L)) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} {P : Word} {cap : Nat}
    (htop : env.stackLimit.toNat + 30816 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (_hge : 0x10000000 ≤ (env.next m).toNat) (hP8 : P.toNat % 8 = 0) (hc16 : cap * 16 < 2 ^ 63)
    (hst : env.Static m) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (ho : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hwin : InWin env (regs .x10) 24)
    (hal : (regs .x10).toNat % 8 = 0) (hlen : ws.length = 1600)
    (hk : ∀ r' m', HoldsT.post env (PostT env ws) Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) :
    ∀ R M, Exit3 env ws ret top regs m P cap R M → M.code = m.code →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 332, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv hcode
  rv_introT hinv
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
    slot3 ho hnx (by omega) hinv_13 (BitVec.ofNat 64 cap) P 1600#64
  have hs := savedBase_toNat (top := top) (by omega)
  have hsv : ∀ x : Word, top + 18446744073709551568#64 ≤ x → x.toNat < top.toNat → _ := fun x h1 h2 =>
    (k1 x (by rw [BitVec.le_def] at h1; omega) h2).trans (hinv_14 x h1)
  have := top.isLt
  have e72 := toNat_below (t := top) (c := 18446744073709551544) (d := 72) (by decide) (by omega)
  have e64 := toNat_below (t := top) (c := 18446744073709551552) (d := 64) (by decide) (by omega)
  have e56 := toNat_below (t := top) (c := 18446744073709551560) (d := 56) (by decide) (by omega)
  rv_symT hp
  all_goals simp only [hinv_22, hinv_23]
  · exact k4 hst
  · intro v hv
    have hvl : v.length = 1600 := by
      rw [Model.linearTransposeRust_some hlen, Option.some.injEq] at hv; subst hv; simp
    have hlay := env.layout
    have hfe := hinv_17.2.1
    refine ⟨P, cap, ⟨?_, ?_, ?_, ?_, hinv_27, ?_⟩, hinv_24, by rw [k5]; exact hinv_25⟩
    · exact k7
    · simp [vecCap, Layouts.Vec.cap, k6]
    · simp [vecLen, Layouts.Vec.len, hvl, k8]
    · simp only [List.length_map, hvl]; exact hinv_26
    · exact result_elems hlen hinv_21 (by omega) (fun x h1 h2 => k2 x (by omega) (by omega)) v hv
  all_goals try simp only [Spec.Runtime.rvCapAt, Spec.Runtime.rvPtrAt, Layouts.RawVecInner.cap,
    Layouts.RawVecInner.ptr, BitVec.add_zero]
  all_goals have hfe := hinv_17.2.1
  all_goals have hcv : (BitVec.ofNat 64 cap).toNat = cap := by rw [BitVec.toNat_ofNat]; omega
  all_goals try simp only [hcv]
  all_goals rv_closeT

set_option rv_sym.heap true in
/-- **From the column sums to the result's loop**: the buffer allocated, its header stored, `reserve`, and the
    loop's registers. -/
theorem mid {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {ws : List E}
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need nAl nRes nHe : Nat} (hnAl : 30816 + nAl ≤ need)
    (hnRes : 30816 + nRes ≤ need) (hnHe : 30816 + nHe ≤ need)
    (hal : HoldsT env p L.alloc.idx nAl Spec.Runtime.AllocPre (Spec.Runtime.AllocPost env) (Stop := AbortStop))
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx nRes)
    (hhe : Runtime.Aborts env p L.handleError.idx nHe)
    (hd : DataRef.InData env [(L.d_c8_e5d50e4a, Gen.Verifier.Keccak.LinearTransposeE.d_c8_e5d50e4a_words)])
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ (fr : Frame) (st : List Frame) (r' : rvIsa.Reg → Word) (m' : rvIsa.M), AbortStop regs m r' m' →
      rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (h16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (_hge : 0x10000000 ≤ (env.next m).toNat)
    (hl3 : ∀ P, P.toNat % 8 = 0 → ∀ k R M, LInv3 env ws ret top regs m P 1600 k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 314, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Exit2 env ws ret top regs m R M → M.code = m.code →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 190, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv hcode
  have htop : env.stackLimit.toNat + 30816 ≤ top.toNat := by omega
  have := top.isLt
  have hlay := env.layout
  have esp := toNat_top (t := top) (c := 18446744073709520800) (by decide) (by omega)
  have eH := toNat_top (t := top) (c := 18446744073709551544) (by decide) (by omega)
  obtain ⟨hd0, hd1⟩ := Runtime.FromElemT.data0 hW hd (by decide)
  rv_introT hinv
  rv_symT hp stop [314] with [hL] using [hal, hres, hhe]
  rotate_right
  · -- the loop's head
    simp (disch := first | exact Tactic.add_ne_add (by decide) | fail) only [vecLen, vecCap, vecPtr, Layouts.Vec.cap,
      Layouts.Vec.ptr, Layouts.Vec.len, add_ofNat2, Nat.reduceAdd, MachineState.getMem_setMem_ne,
      MachineState.getMem_setMem_eq] at hret3_16 hret3_17
    obtain ⟨hcap, hptr⟩ := hret3_17 (by decide)
    have hmg : m3.getMem (L.d_c8_e5d50e4a.hi + L.d_c8_e5d50e4a.lo) = 0x3333333333333334#64 :=
      DataRef.Words.get0 (hd.words (List.mem_singleton_self _)) hret3_15 (by decide)
    rw [hret3_16, hptr, hmg]
    obtain ⟨h3, -⟩ := mid_mem htop hinv_13 hinv_14 hinv_15 hinv_16 hret1_14 hret1_16 (by simpa using hret1_18)
      hret3_14 (fun b hb => by
        simp only [Spec.Runtime.GrowOut, Spec.Runtime.rvCapAt, Spec.Runtime.rvPtrAt, Layouts.RawVecInner.cap,
          Layouts.RawVecInner.ptr, Lprog.updReg_apply, Tactic.rf] at hb
        rcases hb with h | h
        · left; simpa using h
        · right; exact h) hcap hptr
    refine hl3 (r1 .x10) hret1_17 1599 _ _ ⟨0, by omega, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h3.1,
      h3.2.1⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h3⟩, hret3_25.trans (hret1_19.trans hcode)⟩
    all_goals rv_closeT
    all_goals simp only [Tactic.rf]
    · simp
    · rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  all_goals try exact hd0
  all_goals simp only [Spec.Runtime.rvCapAt, Spec.Runtime.rvPtrAt, Layouts.RawVecInner.cap,
    Layouts.RawVecInner.ptr, BitVec.add_zero]
  all_goals have hMn := hinv_13.1
  all_goals rv_closeT

/-- **A part of a constant table's word**: `w` bytes (`4` or `8`) at offset `j` of word `k` of a table in
    `env.data`, in a window and aligned. -/
theorem table_win {env : Env} {top : Word} {m : MachineState} (hW : Windows env top m) {d : DataRef}
    {ws : List Word} (hd : DataRef.InData env [(d, ws)]) {k : Nat} (hk : k < ws.length) {j w : Nat}
    (hjw : j + w ≤ 8) (hw : w = 4 ∨ w = 8) (hj : j % w = 0) :
    inWindow (d.hi + d.lo + BitVec.ofNat 64 (8 * k + j)) w = true ∧
      (d.hi + d.lo + BitVec.ofNat 64 (8 * k + j)).toNat % w = 0 := by
  obtain ⟨hwin, h8⟩ := hW.data_ok _ (hd _ (List.mem_singleton_self _) k hk)
  simp only at hwin h8
  rw [inWindow_iff] at hwin ⊢
  have e : d.hi + d.lo + BitVec.ofNat 64 (8 * k + j) = d.hi + d.lo + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j := by
    rw [BitVec.add_assoc (d.hi + d.lo), BitVec.ofNat_add_ofNat]
  have e2 : (d.hi + d.lo + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j).toNat =
      (d.hi + d.lo + BitVec.ofNat 64 (8 * k)).toNat + j := toNat_add_ofNat (by omega)
  rw [e, e2]
  rcases hw with rfl | rfl <;> omega

/-- `g`'s fill's inner head with `k + 1` positions left: `Inv1` at lane `lane`, bit `z`, and the code map kept. -/
def LInv1 (env : Env) (ws : List E) (L : Link) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  ∃ lane z, 64 * lane + z + k + 1 = 1600 ∧ z < 64 ∧ Inv1 env ws L ret top regs m lane z R M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **`g`'s fill**, from its inner head to the column sums' head (154), through `memset` of the column sums. -/
theorem loop1 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {ws : List E}
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need nMs nPb : Nat} (hnMs : 30816 + nMs ≤ need)
    (hnPb : 30816 + nPb ≤ need)
    (hms : Runtime.MemsetBytesT.MemsetSpecT env p L.memset.idx nMs)
    (hpb : Runtime.Aborts env p L.panicBoundsCheck.idx nPb)
    (hpi : DataRef.InData env [(L.d_c200_f4afdee4, Gen.Verifier.Keccak.LinearTransposeE.d_c200_f4afdee4_words)])
    (hrhoD : DataRef.InData env [(L.d_c100_179d68cc, Gen.Verifier.Keccak.LinearTransposeE.d_c100_179d68cc_words)])
    (hrho : RhoAt env L.d_c100_179d68cc)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ (fr : Frame) (st : List Frame) (r' : rvIsa.Reg → Word) (m' : rvIsa.M), AbortStop regs m r' m' →
      rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (h16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (hx : EListAt m (regs .x11) (ws.map Model.limbs)) (hl : env.Live m (regs .x11) (Layouts.E.byteSize * ws.length))
    (hlen : ws.length = 1600) (hsl : InWin env (regs .x11) (16 * 1600)) (hw8 : (regs .x11).toNat % 8 = 0)
    (hl2 : ∀ R M, Inv2 env ws ret top regs m 0 R M → M.code = m.code →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 154, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv1 env ws L ret top regs m k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := by
  have htop : env.stackLimit.toNat + 30816 ≤ top.toNat := by omega
  have hcal : (top + 18446744073709546424#64).toNat % 8 = 0 := by
    rw [colsBase_toNat (by omega)]; omega
  refine Total.loop (I := rvIsa) (LInv1 env ws L ret top regs m) fun k R M hI ih => ?_
  obtain ⟨lane, z, hk, hz, hinv, hcode⟩ := hI
  have hlane : lane < 25 := by omega
  have hkn : 64 * lane + z < 1600 := by omega
  have := top.isLt
  have hgb := gBase_toNat (top := top) (by omega)
  have hJ : 64 * Model.keccakPiRust.getD lane 0 + (z + Model.keccakRhoRust.getD lane 0) % 64 < 1600 := by
    have := pi_lt lane hlane; have := Nat.mod_lt (z + Model.keccakRhoRust.getD lane 0) (show 64 > 0 by decide)
    omega
  have hw0 : (regs .x11 + BitVec.ofNat 64 (16 * (64 * Model.keccakPiRust.getD lane 0 +
      (z + Model.keccakRhoRust.getD lane 0) % 64))).toNat = (regs .x11).toNat + 16 * (64 *
      Model.keccakPiRust.getD lane 0 + (z + Model.keccakRhoRust.getD lane 0) % 64) :=
    toNat_add_ofNat (by unfold InWin at hsl; omega)
  have g0 : (top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * (64 * lane + z))).toNat =
      top.toNat - 30792 + 16 * (64 * lane + z) := by rw [toNat_elem (by omega), hgb]
  have g8 : (top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * (64 * lane + z)) + 8#64).toNat =
      top.toNat - 30792 + 16 * (64 * lane + z) + 8 := by rw [toNat_elem8 (by omega), hgb]
  rv_introT hinv
  obtain ⟨f1, f2, f3, f4, f5⟩ := loop1_mem htop hkn hst hinv_13 hinv_14 hinv_24
  have hg := load_g hinv_13 hnx hx hl hlen hlane hz
  rv_symT hp stop [64, 68, 88, 154] with [hL] using [hms, hpb]
  clear hc
  rw [idx_eq (pi_lt lane hlane)]
  rv_symT hp stop [58, 64, 68, 78, 154] with [hL] using [hms, hpb]
  all_goals rw [hg.1, hg.2] at *
  · -- the next bit
    have hz1 : z + 1 < 64 := by rw [dec_ofNat hz, ofNat_inj (by omega) (by omega)] at hc; omega
    clear hc
    refine ih (k - 1) _ _ (by omega) ⟨lane, z + 1, by omega, hz1, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      f1, f2⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [← Nat.add_assoc]; exact f3⟩, hcode⟩
    all_goals rv_closeT
    all_goals simp only [Tactic.rf]
    all_goals first | rw [succ_ofNat2] | rw [dec_ofNat hz] | rw [step_ptr2]
  · -- the next lane
    have hl1 : lane + 1 < 25 := by rw [ofNat_inj (by omega) (by omega)] at hc; omega
    have hz63 : z = 63 := by rw [dec_ofNat hz, ofNat_inj (by omega) (by omega)] at hc_1; omega
    clear hc hc_1
    have hp8 : 2 ^ 3 * (lane + 1) = 8 * (lane + 1) + 0 := by omega
    have hr4 : 2 ^ 2 * (lane + 1) = 8 * ((lane + 1) / 2) + 4 * ((lane + 1) % 2) := by omega
    have tp := table_win hW hpi (k := lane + 1) (j := 0) (w := 8) (by change lane + 1 < 25; omega) (by omega)
      (Or.inr rfl) rfl
    have tr := table_win hW hrhoD (k := (lane + 1) / 2) (j := 4 * ((lane + 1) % 2)) (w := 4)
      (by change (lane + 1) / 2 < 13; omega) (by omega) (Or.inl rfl) (by omega)
    rv_symT hp stop [78] with [hL] using [hms, hpb]
    · rw [shl_ofNat, hp8]; exact tp.1
    · rw [shl_ofNat, hp8]; exact tp.2
    · rw [shl_ofNat, hr4]; exact tr.1
    · rw [shl_ofNat, hr4]; exact tr.2
    rw [pi_load (hpi.words (List.mem_singleton_self _)) f4 hl1, rho_load hrho f4 hl1]
    refine ih (k - 1) _ _ (by omega) ⟨lane + 1, 0, by omega, by omega, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, f1, f2⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by rw [show 64 * (lane + 1) + 0 = 64 * lane + z + 1 by omega]; exact f3⟩, hcode⟩
    all_goals rv_closeT
    all_goals simp only [Tactic.rf]
    all_goals first | rw [succ_ofNat] | rw [lane_ptr'] | rfl
    rfl
  · exact f4
  · -- the last bit: `memset` of the column sums, then the column loop's head
    have hl24 : lane = 24 := by rw [ofNat_inj (by omega) (by omega)] at hc; omega
    have hz63 : z = 63 := by rw [dec_ofNat hz, ofNat_inj (by omega) (by omega)] at hc_1; omega
    clear hc hc_1
    obtain ⟨g1, g2, g3, g4⟩ := memset_cols (ws := ws) htop (by omega) f1 f2
      (by rw [show (1600 : Nat) = 64 * lane + z + 1 by omega]; exact f3) hret1_14
      (fun b hb => by
        simp only [Spec.Runtime.CopyOut, Spec.Runtime.DwordsOf, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
          ite_false] at hb
        rw [alignToDword_self hcal, hcal] at hb
        exact hb)
      (fun k hk => (hret1_17 k (by simpa using hk)).trans (by decide))
    refine hl2 _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, g1, g2⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, g3, g4⟩
      (hret1_19.trans hcode)
    all_goals rv_closeT
    · exact start_ofs top 18446744073709546424
    · exact start_ofs8 top 18446744073709546424
    · exact start_ofs8 top 18446744073709520824

end Rv64mc.Proof.Keccak.LinearTransposeT
