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

end Rv64mc.Proof.Keccak.LinearTransposeT
