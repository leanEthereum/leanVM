/-
  Rv64mc.Proof.Multilinear.SelectorPointT

  `selector_point` is total: it returns `SelectorPoint.Post`'s vector (`Spec.Multilinear.SelectorPoint`), which is
  also a vector's (`VecReprT.VecT`) of the length asked for, its buffer fresh unless empty (`CloneT.ClonePostT`), or
  the run ends with the guest's abort (`AbortStop`) where `alloc` or `handle_error` does. Over any program holding
  its template, from the total contracts of `alloc`, `Vec::reserve` and `handle_error`.

  The partial proof (`SelectorPoint.lean`) ported by `rv_autoT`: up to `reserve`'s return (instruction 78) as there,
  its `After` from `after_of`; `tail` from there; its loop, there an induction on the elements left, is `Total.loop`
  at instruction 94 with them as the measure (`LInv`: the partial `Inv` and the code map kept). The precondition
  (`PreT`) adds that the result's slot lies in a window and is 8-byte aligned (`from_elem`'s `FromElemPreT`).

  ## Main definitions

  * `PreT`, `PostT`, `SpecT`, `LInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.FromElemT
import Rv64mc.Proof.Multilinear.SelectorPoint
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Multilinear.SelectorPointT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime Rv64mc.Proof.Multilinear
open Rv64mc.Proof.Multilinear.SelectorPoint (After Inv MemInv TailInv mem_step exit_fin fin after_of slots ovf
  prologue grow_in hdr_reads cnt_iff cnt_step)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT)
open Rv64mc.Gen.Verifier.Multilinear.SelectorPoint (Link tmpl)

/-- The total precondition: `Pre`, and the result's slot in a window and 8-byte aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  Spec.Multilinear.SelectorPoint.Pre env regs m ∧ InWin env (regs .x10) Layouts.Vec.byteSize ∧
    (regs .x10).toNat % 8 = 0

/-- The total postcondition: `Post`, and the result a vector's of length `n`, its buffer fresh unless empty. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  Spec.Multilinear.SelectorPoint.Post env regs m r' m' ∧ ClonePostT env 16 regs m r' m'

/-- **The total contract of `selector_point`**: `SelectorPoint.spec`'s, as a `HoldsT` from `PreT`, with `VecT` of the
    result, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (Spec.Whir.SretOut Layouts.Vec.byteSize) AbortStop

/-- The loop's head with `k + 1` elements left: `Inv` after the others, and the code map kept since the entry. -/
def LInv (env : Env) (m M0 : MachineState) (top q : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  ∃ j, j + k + 1 = (regs .x12).toNat ∧ Inv env m M0 top q regs j R M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **The loop**, from its head; its last pass copies the header to `sret`. -/
theorem loop {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 64 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m M0 : MachineState} {q : Word}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (Spec.Whir.SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hwin : InWin env (regs .x10) Layouts.Vec.byteSize)
    (hal : (regs .x10).toNat % 8 = 0) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hge : 0x10000000 ≤ (env.next m).toNat) (hend : env.heapEnd.toNat ≤ 0x78000000)
    (hA : After env m top ret regs M0) (hq : q = M0.getMem (top + 18446744073709551560#64))
    (hpos : 0 < (regs .x12).toNat) (hq8 : q.toNat % 8 = 0) :
    ∀ k R M, LInv env m M0 top q regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 94, ret, top⟩ :: rest, R, M⟩ := by
  have hlim : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
  have hlay := env.layout
  have hc' : M0.getMem (top + 18446744073709551552#64) = regs .x12 ∧
      env.Fresh m M0 q (16 * (regs .x12).toNat) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := hA
    rcases h with h | h
    · omega
    · rw [hq]; exact h
  have hfr1 := hc'.2.1
  have hfr2 := hc'.2.2
  have hF0 := hA.1.2.1
  refine Total.loop (I := rvIsa) (LInv env m M0 top q regs) fun k R M hI ih => ?_
  obtain ⟨j, hj, hI, hcode⟩ := hI
  have e0 : (q + BitVec.ofNat 64 (16 * j)).toNat = q.toNat + 16 * j := toNat_add_ofNat (by omega)
  have e8 : (q + BitVec.ofNat 64 (16 * j) + 8#64).toNat = q.toNat + 16 * j + 8 := by
    rw [toNat_add_ofNat (k := 8) (by omega), e0]
  have hMI := hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hnM := hMI.2.2.1
  rv_introT hI
  rv_symT hp stop [110]
  · -- back to the head
    have hk0 : k ≠ 0 := fun h0 => hc ((cnt_iff (by have := (regs .x12).isLt; omega)).2 (by omega))
    clear hc
    have mi := mem_step (len := (regs .x12).toNat) hfr1 hfr2 hF0 (by omega) ⟨hI_16, hI_17, hI_18, hI_19, hI_20⟩
    refine ih (k - 1) _ _ (by omega) ⟨j + 1, by omega, ?_, ?_⟩
    · rv_closeT
      all_goals first
        | exact step_ptr _ _
        | exact cnt_step j
        | exact mi.2.2.2.2
    · rv_closeT
  · have hj1 : j + 1 = (regs .x12).toNat := ((cnt_iff (by have := (regs .x12).isLt; omega)).1 hc).symm
    clear hc
    have fn := exit_fin hnx hlim hown hA hq hj1 ⟨hI_16, hI_17, hI_18, hI_19, hI_20⟩
    have mi := mem_step (len := (regs .x12).toNat) hfr1 hfr2 hF0 (by omega) ⟨hI_16, hI_17, hI_18, hI_19, hI_20⟩
    obtain ⟨-, -, -, -, -, -, e56, e64⟩ := slots hlim
    set_option rv_sym.heap false in rv_symT hp
    · exact fn.1
    · exact fn.2.1
    · exact fn.2.2.1
    · exact fn.2.2.2.1
    · exact fn.2.2.2.2.1
    · exact fn.2.2.2.2.2.1
    · exact fn.2.2.2.2.2.2.1
    · exact fn.2.2.2.2.2.2.2
    all_goals try rw [mi.2.2.2.1 (top + 18446744073709551552#64) (by omega), hc'.1]
    all_goals try rw [mi.2.2.2.1 (top + 18446744073709551560#64) (by omega), ← hq]
    all_goals try rw [hA.2.2.2.2.2.2.2.1, BitVec.zero_add]
    all_goals try simp only [Layouts.Vec.byteSize, Layouts.RawVecInner.byteSize, rvCapAt, rvPtrAt,
      Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
    have hb := hA.2.2.2.2.2.2.2.2.1
    all_goals rv_closeT

set_option rv_sym.heap true in
/-- **From `reserve`'s return** (the partial `TailInv`, the code map kept, the buffer's pointer 8-byte aligned): the
    loop, or the empty header copied. -/
theorem tail {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 64 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (Spec.Whir.SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hwin : InWin env (regs .x10) Layouts.Vec.byteSize)
    (hal : (regs .x10).toNat % 8 = 0) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hge : 0x10000000 ≤ (env.next m).toNat) (hend : env.heapEnd.toNat ≤ 0x78000000)
    (R : Reg → Word) (M : MachineState) (hinv : TailInv env m top ret regs R M) (hcode : M.code = m.code)
    (hq8 : (M.getMem (top + 18446744073709551560#64)).toNat % 8 = 0) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := by
  have hlim : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
  have hA : After env m top ret regs M := hinv.2.2.2.2.2.2.2.2.2.2.2.2
  rv_introT hinv
  rv_symT hp stop [94, 110]
  · -- no elements: the empty header copied
    have hx0 : (regs .x12).toNat = 0 := by rw [hc]; rfl
    clear hc
    have hcap0 : M.getMem (top + 18446744073709551552#64) = 0#64 := by
      rcases hinv_22 with h | h
      · exact h.2
      · rw [h.1]; exact BitVec.eq_of_toNat_eq hx0
    have fn := fin (M := M) (L := M.getMem (top + 18446744073709551568#64))
      (xs := (Model.selectorPointRust (regs .x11) (regs .x12).toNat).map Model.limbs) hown hnx hlim hinv_13 hinv_14
      hinv_15 hinv_16 hinv_17 hinv_18 hinv_19
      (by rw [hx0]; exact ⟨by simpa [Model.selectorPointRust] using BitVec.isLt _,
        fun k hk => by simp [Model.selectorPointRust] at hk⟩)
      (by rw [hinv_20, hx0]; rfl) (by simp [hx0, Model.selectorPointRust]) (by rw [hcap0]; decide)
      (Or.inl (by rw [hcap0]; rfl))
    set_option rv_sym.heap false in rv_symT hp
    · exact fn.1
    · exact fn.2.1
    · exact fn.2.2.1
    · exact fn.2.2.2.1
    · exact fn.2.2.2.2.1
    · exact fn.2.2.2.2.2.1
    · exact fn.2.2.2.2.2.2.1
    · exact fn.2.2.2.2.2.2.2
    all_goals try rw [hcap0]
    all_goals try rw [hinv_20]
    all_goals try simp only [Layouts.Vec.byteSize, Layouts.RawVecInner.byteSize, rvCapAt, rvPtrAt,
      Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
    all_goals rv_closeT
  · -- the loop
    have hpos : 0 < (regs .x12).toNat := Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq h)
    clear hc
    have hq : M.getMem (top + 18446744073709551568#64) <<< 4 + M.getMem (top + 18446744073709551560#64) =
        M.getMem (top + 18446744073709551560#64) := by rw [hinv_20]; simp
    refine loop hp hn hk hstk hnx hown hwin hal hW h16 hge hend hA rfl hpos hq8 ((regs .x12).toNat - 1) _ _
      ⟨0, by omega, ?_, hcode⟩
    rv_closeT
    rw [hq]; exact start_ptr _

/-- The header's pointer after `reserve`, which kept it. -/
theorem ptr_kept {m1 N : MachineState} {top c q : Word}
    (h : vecPtr m1 (top + 18446744073709551552#64) = vecPtr (((N.setMem (top + 18446744073709551552#64) c).setMem
      (top + 18446744073709551560#64) q).setMem (top + 18446744073709551568#64) 0#64) (top + 18446744073709551552#64)) :
    m1.getMem (top + 18446744073709551560#64) = q := by
  simp only [vecPtr, Layouts.Vec.ptr, SelectorPoint.at64_8] at h
  rw [h, (hdr_reads _ _ _ _).2.1]

set_option rv_sym.heap true in
/-- **`selector_point` is total**, with 64 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needR needH : Nat} (hnA : 64 + needA ≤ need) (hnR : 64 + needR ≤ need) (hnH : 64 + needH ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hhe : Runtime.Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [78] with [hL] using [hal', hres, hhe]
  all_goals have hlim : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
  all_goals have hov := ovf hc_1
  all_goals obtain ⟨hF0, hn0, p8, p16, p24, p32, p40⟩ := prologue (ret := ret) (regs := regs) hlim hpre_5
  all_goals have hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
  all_goals obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64⟩ := slots hlim
  on_goal 11 =>
    have hF2 := Tactic.frame_call hF0 hret2_14 (by omega)
    have k2 : ∀ a : Word, top.toNat - 64 ≤ a.toNat → m2.getMem a = _ := fun a ha =>
      keep2_1 a (by rw [BitVec.le_def]; omega)
    refine tail hp (by omega) hk hpre_3 hpre_5 hown hpre_8 hpre_9 hpre_11 hpre_10 hpre_11.next_ge
      hpre_11.heapEnd_le _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        after_of hlim hF2 (by rw [k2 _ (by omega), p8]) (by rw [k2 _ (by omega), p16])
          (by rw [k2 _ (by omega), p24]) (by rw [k2 _ (by omega), p32]) (by rw [k2 _ (by omega), p40]) hret3_14
          (fun b h => grow_in rfl (by omega) h) hret3_15 hret3_16 hret3_17 (by omega)
          (Or.inr ⟨rfl, hret2_16, by rw [hov.1] at hret2_18; omega⟩)⟩
      (hret3_25.trans hret2_19) ?_
    rw [ptr_kept (hret3_17 (Runtime.FromElemT.hdr_spare _ _ _ _ le_rfl)).2]; exact hret2_17
  on_goal 5 =>
    refine tail hp (by omega) hk hpre_3 hpre_5 hown hpre_8 hpre_9 hpre_11 hpre_10 hpre_11.next_ge
      hpre_11.heapEnd_le _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        after_of hlim hF0 p8 p16 p24 p32 p40 hret1_14 (fun b h => grow_in rfl (by omega) h) hret1_15 hret1_16
          hret1_17 (by omega) (Or.inl ⟨?_, hc⟩)⟩ hret1_25 ?_
    · have := hov.1; rw [hc] at this; simp at this; omega
    · rw [ptr_kept (hret1_17 (Runtime.FromElemT.hdr_spare _ _ _ _ (by omega))).2]; rfl
  all_goals try simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero,
    Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
  all_goals rv_closeT

end Rv64mc.Proof.Multilinear.SelectorPointT
