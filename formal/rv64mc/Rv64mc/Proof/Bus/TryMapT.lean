/-
  Rv64mc.Proof.Bus.TryMapT

  `<[usize; 2]>::try_map` with `verify_bus_balance`'s closure `|j| ColumnClaim { point: point.to_vec(), column: j,
  value: values[j] }` is total: called with the result's slot (`a0`, the two claims' 96 bytes) and the closure (`a1`:
  the point's buffer and length at `+ 8`, `+ 16`, the values' `Vec<E>` at `+ 24`), it checks the point's bytes fit an
  `isize` (else `handle_error`), and for `j = 0, 1` checks `j` against the values' length (else
  `panic_bounds_check`), clones the point (`alloc`, none for an empty point, then `memcpy`) and reads `values[j]`;
  then it writes the two claims. Each result's point is a vector's (`VecReprT.VecT`) of the point's length, its
  buffer fresh unless empty, and its column `j`; the run ends with the guest's abort (`AbortStop`) where `alloc`,
  `handle_error` or a bounds check does. It does not state the copied bytes or the values.

  The precondition (`ClosureT`): the slot a caller's object in a window, aligned; the closure a caller's object in a
  window; the point `n` elements of a vector's buffer (`BufT`); the values a vector's (`VecT`) and a caller's object.
  At the image's one call site (`verify_bus_balance`, template step 177) the closure is at `sp + 0x3d0` in the
  caller's frame, the point a vector's buffer and the values the vector at `sp + 0x1e0`.

  The executor stops at the joins the two clones' empty cases reach by backward jumps (instructions 86, 96, 124,
  134): `fin` steps the stores from `134`, `mid` the second clone from `96`, each over a clone's buffer `CloneBufT`.

  ## Main definitions

  * `ClosureT`, `PreT`, `ClaimT`, `PostT`, `SpecT`, `CloneBufT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Bus.ColumnClaimT
import Rv64mc.Proof.Runtime.SpecExtendT
import Rv64mc.Proof.Multilinear.SelectorPoint
import Rv64mc.Gen.Tmpl.Core.Array.ArrUsizeN2.TryMapNeverShortCircuitCH2be087e3

namespace Rv64mc.Proof.Bus.TryMapT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Gen.Core.Array.ArrUsizeN2.TryMapNeverShortCircuitCH2be087e3 (Link tmpl)

/-- The closure at `f`: its 32 bytes a caller's in a window, 8-byte aligned; the point (`f + 8`, `f + 16`) `n`
    elements of a vector's buffer; the values (`f + 24`) a vector's and a caller's object. -/
def ClosureT (env : Env) (m : MachineState) (sp f : Word) : Prop :=
  InWin env f 32 ∧ f.toNat % 8 = 0 ∧ env.Owned m sp f 32 ∧
    BufT env m (m.getMem (f + 16#64)) (m.getMem (f + 8#64)) 16 ∧
    VecT env m (m.getMem (f + 24#64)) 16 ∧ env.Owned m sp (m.getMem (f + 24#64)) 24

/-- The total precondition: the result's slot a caller's object in a window, 8-byte aligned; the closure
    `ClosureT`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) (2 * Layouts.ColumnClaim.byteSize) ∧
    InWin env (regs .x10) (2 * Layouts.ColumnClaim.byteSize) ∧ (regs .x10).toNat % 8 = 0 ∧
    ClosureT env m (regs .x2) (regs .x11)

/-- Claim `j`'s point a vector's of the point's length, fresh unless empty, and its column `j`. -/
def ClaimT (env : Env) (m m' : MachineState) (a n : Word) (j : Nat) : Prop :=
  VecT env m' a 16 ∧ vecLen m' a = n ∧ (n.toNat = 0 ∨ env.Fresh m m' (vecPtr m' a) (n.toNat * 16)) ∧
    m'.getMem (a + BitVec.ofNat 64 Layouts.ColumnClaim.column) = BitVec.ofNat 64 j

/-- The total postcondition: both claims `ClaimT`, at `sret` and the next `ColumnClaim`. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  ClaimT env m m' (regs .x10) (m.getMem (regs .x11 + 16#64)) 0 ∧
    ClaimT env m m' (regs .x10 + BitVec.ofNat 64 Layouts.ColumnClaim.byteSize) (m.getMem (regs .x11 + 16#64)) 1

/-- **The total contract of `<[usize; 2]>::try_map` with `verify_bus_balance`'s claim closure**, writing the two
    claims. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (fun regs _ => InRange (regs .x10) (2 * Layouts.ColumnClaim.byteSize))
    AbortStop

/-- The prologue's thirteen saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)).setMem (top + 18446744073709551536#64) (regs .x24)).setMem
    (top + 18446744073709551528#64) (regs .x25)).setMem (top + 18446744073709551520#64) (regs .x26)).setMem
    (top + 18446744073709551512#64) (regs .x27)

/-- The prologue's stores stay in the frame, keep `env.Static` and the code. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hs : env.Static m) :
    env.Frame top Tactic.F m (saved m top ret regs) ∧ env.Static (saved m top ret regs) ∧
      (saved m top ret regs).code = m.code := by
  have := top.isLt
  simp only [saved]
  refine ⟨?_, ?_, rfl⟩
  · repeat (first | refine Tactic.frame_store ?_ ?_ ?_ | exact Tactic.frame_refl hnx)
    all_goals (rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega)
  · repeat (first | refine Env.static_setMem_stack ?_ ?_ | exact hs)
    all_goals (rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega)

/-- The values' elements `0` and `1` words, past the check that there is one, in a window and aligned. -/
theorem val0_ok {env : Env} {top : Word} {m : MachineState} {C P Lw : Word} (hW : Windows env top m)
    (hb : BufT env m C P 16) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hl : Lw.toNat ≤ C.toNat)
    (hi : ¬ Lw = 0#64) :
    (inWindow P 8 = true ∧ P.toNat % 8 = 0) ∧ (inWindow (P + 8#64) 8 = true ∧ (P + 8#64).toNat % 8 = 0) := by
  have hi' : 1 ≤ Lw.toNat := Nat.pos_of_ne_zero fun h => hi (BitVec.eq_of_toNat_eq (by simpa using h))
  rcases hb with h0 | ⟨hge, hlive, hal⟩
  · omega
  have hw : InWin env P (C.toNat * 16) := .inl ⟨hge, by unfold Env.Live at hlive; omega⟩
  have hlt := hw.lt
  exact ⟨hw.dword hW hal (o := 0) (by simp) (by omega) (by omega),
    hw.dword hW hal (o := 8) (toNat_add_ofNat (by omega)) (by omega) (by omega)⟩

/-- A clone's buffer: none (capacity `0`) for an empty point, else `n` elements allocated since the entry. -/
def CloneBufT (env : Env) (m M : MachineState) (n c q : Word) : Prop :=
  (n.toNat = 0 ∧ c.toNat = 0) ∨
    (c.toNat = n.toNat ∧ 0x10000000 ≤ q.toNat ∧ env.Fresh m M q (n.toNat * 16) ∧ q.toNat % 8 = 0)

set_option maxHeartbeats 1000000 in
set_option rv_sym.heap true in
/-- **The end**, from the clones made: the two claims stored into `sret`, and the return. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 112 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} {n c1 q1 c2 q2 : Word}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (fun regs _ => InRange (regs .x10) 96) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) 96) (hwin : InWin env (regs .x10) 96) (hal : (regs .x10).toNat % 8 = 0)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hn63 : 16 * n.toNat < 2 ^ 63)
    (hnm : m.getMem (regs .x11 + 16#64) = n)
    (R : Reg → Word) (M : MachineState)
    (hR : R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x10 ∧ R .x19 = q1 ∧ R .x24 = c1 ∧ R .x20 = q2 ∧
      R .x27 = c2 ∧ R .x21 = n)
    (hK : ∀ a, top + 18446744073709551504#64 ≤ a → M.getMem a = (saved m top ret regs).getMem a)
    (hF : env.Frame top Tactic.F m M) (hS : env.Static M) (hcode : M.code = m.code)
    (h1 : CloneBufT env m M n c1 q1) (h2 : CloneBufT env m M n c2 q2) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 134, ret, top⟩ :: rest, R, M⟩ := by
  have hFn := hF.2.1
  simp only [saved] at hK
  rv_introT hR
  rv_symT hp
  all_goals simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
  all_goals rv_closeT

set_option maxHeartbeats 2000000 in
set_option rv_sym.heap true in
/-- **From the first clone made**: the second, then `fin`. -/
theorem mid {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needM needH needP : Nat} (hn : 112 ≤ need) (hnA : 112 + needA ≤ need) (hnM : 112 + needM ≤ need)
    (hnH : 112 + needH ≤ need) (hnP : 112 + needP ≤ need)
    (hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop))
    (hcp : MemcpySpecT env p L.memcpy.idx needM)
    (hhe : Aborts env p L.handleError.idx needH) (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    {n B S V c1 q1 : Word}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (fun regs _ => InRange (regs .x10) 96) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) 96) (hwin : InWin env (regs .x10) 96) (hal : (regs .x10).toNat % 8 = 0)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hn63 : 16 * n.toNat < 2 ^ 63)
    (hnm : m.getMem (regs .x11 + 16#64) = n) (hB : B.toNat = 16 * n.toNat)
    (hVw : InWin env V 24) (hV8 : V.toNat % 8 = 0)
    (hVo : V.toNat + 24 ≤ (env.next m).toNat ∨ top.toNat ≤ V.toNat)
    (hVb : BufT env m (m.getMem V) (m.getMem (V + 8#64)) 16)
    (hVl : (m.getMem (V + 16#64)).toNat ≤ (m.getMem V).toNat) (hSb : BufT env m n S 16)
    (R : Reg → Word) (M : MachineState)
    (hR : R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x10 ∧ R .x9 = B ∧ R .x18 = S ∧ R .x19 = q1 ∧
      R .x20 = V ∧ R .x21 = n ∧ R .x24 = c1)
    (hK : ∀ a, top + 18446744073709551504#64 ≤ a → M.getMem a = (saved m top ret regs).getMem a)
    (hF : env.Frame top Tactic.F m M) (hS : env.Static M) (hcode : M.code = m.code)
    (h1 : CloneBufT env m M n c1 q1) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 96, ret, top⟩ :: rest, R, M⟩ := by
  have hlay := env.layout
  have hKeep := SpecExtendT.keep_of_frame hF (by omega)
  have hnmM := hF.1
  have hFn := hF.2.1
  have hK' := hK
  simp only [saved] at hK
  rv_introT hR
  rv_symT hp stop [124, 134] with [hL, hKeep] using [hal', hcp, hhe, hpb]
  -- no bytes but a point, or bytes but no point: not reached
  · exfalso; apply hc; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat hc_2; rw [hB] at this; simp only [BitVec.toNat_ofNat] at this ⊢; omega
  · refine fin (c1 := c1) (q1 := q1) hp hn hk hstk hnx hown hwin hal hW h16 hn63 hnm _ _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hK' hF hS hcode h1 (Or.inl ⟨?_, rfl⟩)
    rw [hc]; rfl
  · exfalso; apply hc_2; apply BitVec.eq_of_toNat_eq
    rw [hB, hc]; rfl
  · have hn0 : n.toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
    obtain ⟨hS1, hS2, -⟩ := hSb.resolve_left hn0
    unfold Env.Live at hS2
    have hE := hW.heapEnd_le
    have hq2 : (env.next m).toNat ≤ (r2 .x10).toNat := Nat.le_trans hnmM hret2_16
    have hn2 := hret2_14.2.1
    have hB16 : B.toNat = n.toNat * 16 := by rw [hB]; ring
    rv_symT hp stop [134] with [hL] using [hcp]
    · refine Or.inr ⟨Or.inl ⟨by omega, by omega⟩, Or.inl (by omega), inWindow_iff.2 (Or.inl ⟨by omega, by omega⟩),
        Or.inl (by omega)⟩
    · have hnx1 := hret1_14.1
      have hHS : env.heapEnd.toNat ≤ env.stackLimit.toNat := by omega
      have hD : (r2 .x10).toNat = (r2 .x10).toNat + 16 * 0 := rfl
      have t112 : (top + 18446744073709551504#64).toNat = top.toNat - 112 :=
        CloneT.toNat_add_neg (k := 112) rfl (by omega)
      refine fin (c1 := c1) (q1 := q1) (c2 := n) (q2 := r2 .x10) hp hn hk hstk hnx hown hwin hal hW h16 hn63 hnm _ m1
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ hret1_15 (hret1_19.trans (hret2_19.trans hcode)) ?_ ?_
      · intro a ha
        have hlo : env.stackLimit.toNat ≤ a.toNat := by rw [BitVec.le_def, t112] at ha; omega
        rw [keep1_1 a ha fun hb => SpecExtendT.not_slot (SpecExtendT.dwords_in (n := B.toNat) hret2_17 hD hb)
          (by omega) hHS hlo,
          keep2_1 a ha]
        exact hK' a ha
      · refine (Tactic.frame_call hF hret2_14 (by omega)).trans hret1_14 (by omega) fun b hb => ?_
        obtain ⟨hb1, hb2⟩ := SpecExtendT.dwords_in (n := B.toNat) hret2_17 hD hb
        rw [Nat.mul_zero, Nat.add_zero] at hb1 hb2
        rw [hret2_18] at hb2
        exact Or.inr (Or.inl ⟨Nat.le_trans hq2 hb1, Nat.lt_of_lt_of_le hb2 hnx1⟩)
      · rcases h1 with h | ⟨h1, h2, ⟨h3, h4⟩, h5⟩
        · exact .inl h
        · have := hret2_14.1
          exact .inr ⟨h1, h2, ⟨h3, by omega⟩, h5⟩
      · have := hW.next_ge
        refine .inr ⟨rfl, by omega, ⟨hq2, ?_⟩, hret2_17⟩
        rw [← hnm] at hB
        omega

set_option maxHeartbeats 2000000 in
set_option rv_sym.heap true in
/-- **`try_map` is total**, with 112 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needM needH needP : Nat} (hnA : 112 + needA ≤ need) (hnM : 112 + needM ≤ need)
    (hnH : 112 + needH ≤ need) (hnP : 112 + needP ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hcp : MemcpySpecT env p L.memcpy.idx needM)
    (hhe : Aborts env p L.handleError.idx needH) (hpb : Aborts env p L.panicBoundsCheck.idx needP) :
    SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [86, 96] with [hL] using [hal', hcp, hhe, hpb]
  all_goals
    first
    | have hov := Multilinear.SelectorPoint.ovf hc_2
    | have hov := Multilinear.SelectorPoint.ovf hc
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
    have hVb : BufT env m (m.getMem (m.getMem (regs .x11 + 24#64)))
        (m.getMem (m.getMem (regs .x11 + 24#64) + 8#64)) 16 := by
      simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero] at hpre_18
      exact hpre_18
    have hVl : (m.getMem (m.getMem (regs .x11 + 24#64) + 16#64)).toNat ≤
        (m.getMem (m.getMem (regs .x11 + 24#64))).toNat := by
      rwa [ReserveT.vecLen_eq, ReserveT.vecCap_eq] at hpre_20
    have hVo : (m.getMem (regs .x11 + 24#64)).toNat + 24 ≤ (env.next m).toNat ∨
        top.toNat ≤ (m.getMem (regs .x11 + 24#64)).toNat := by rw [← hpre_2]; exact hpre_21
    have hsv := saved_ok (ret := ret) (regs := regs) hlim hpre_5 hpre_4
    have hown : env.Owned m top (regs .x10) 96 := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
  -- the first value's words
  · exact (val0_ok hpre_24 hVb hpre_5 hVl hc_1).1.1
  · exact (val0_ok hpre_24 hVb hpre_5 hVl hc_1).1.2
  · exact (val0_ok hpre_24 hVb hpre_5 hVl hc_1).2.1
  · exact (val0_ok hpre_24 hVb hpre_5 hVl hc_1).2.2
  -- no bytes but a point: not reached
  · exfalso; apply hc; apply BitVec.eq_of_toNat_eq
    have := hov.1; rw [hc_3] at this; simp only [BitVec.toNat_ofNat] at this ⊢; omega
  -- no point: the first clone empty
  · refine mid (c1 := 0#64) (q1 := 8#64) hp hL (by omega) hnA hnM hnH hnP hal' hcp hhe hpb hk hstop hpre_3 hpre_5
      hown hpre_8 hpre_9 hpre_24 hpre_23 hov.2 rfl hov.1 hpre_15 hpre_17 hVo hVb hVl hpre_14 _ _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ _ => rfl) hsv.1 hsv.2.1 hsv.2.2 (Or.inl ⟨?_, rfl⟩)
    rw [hc]; rfl
  · rw [hov.1]; exact hov.2
  -- bytes but no point: not reached
  · exfalso; apply hc_3; apply BitVec.eq_of_toNat_eq
    rw [hov.1, hc]; rfl
  -- the first clone's copy
  · have hn0 : (m.getMem (regs .x11 + 16#64)).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
    obtain ⟨hS1, hS2, -⟩ := hpre_14.resolve_left hn0
    unfold Env.Live at hS2
    have hE := hpre_24.heapEnd_le
    have hq2 := hret2_16
    have hn2 := hret2_14.2.1
    have hB16 := hov.1
    rv_symT hp stop [96] with [hL] using [hcp]
    · refine Or.inr ⟨Or.inl ⟨by have := hpre_24.next_ge; omega, by omega⟩, Or.inl (by omega),
        inWindow_iff.2 (Or.inl ⟨by omega, by omega⟩), Or.inl (by omega)⟩
    · have hnx1 := hret1_14.1
      have hHS : env.heapEnd.toNat ≤ env.stackLimit.toNat := by omega
      have hD : (r2 .x10).toNat = (r2 .x10).toNat + 16 * 0 := rfl
      have t112 : (top + 18446744073709551504#64).toNat = top.toNat - 112 :=
        CloneT.toNat_add_neg (k := 112) rfl (by omega)
      refine mid (c1 := m.getMem (regs .x11 + 16#64)) (q1 := r2 .x10) hp hL (by omega) hnA hnM hnH hnP hal' hcp hhe
        hpb hk hstop hpre_3 hpre_5 hown hpre_8 hpre_9 hpre_24 hpre_23 hov.2 rfl hov.1 hpre_15 hpre_17 hVo hVb hVl
        hpre_14 _ m1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ hret1_15 (hret1_19.trans (hret2_19.trans hsv.2.2))
        ?_
      · intro a ha
        have hlo : env.stackLimit.toNat ≤ a.toNat := by rw [BitVec.le_def, t112] at ha; omega
        rw [keep1_1 a ha fun hb => SpecExtendT.not_slot
          (SpecExtendT.dwords_in (n := (m.getMem (regs .x11 + 16#64) <<< 4).toNat) hret2_17 hD hb) (by omega) hHS hlo,
          keep2_1 a ha]
        rfl
      · refine (Tactic.frame_call hsv.1 hret2_14 (by omega)).trans hret1_14 (by omega) fun b hb => ?_
        obtain ⟨hb1, hb2⟩ :=
          SpecExtendT.dwords_in (n := (m.getMem (regs .x11 + 16#64) <<< 4).toNat) hret2_17 hD hb
        rw [Nat.mul_zero, Nat.add_zero] at hb1 hb2
        rw [hret2_18] at hb2
        exact Or.inr (Or.inl ⟨Nat.le_trans hq2 hb1, Nat.lt_of_lt_of_le hb2 hnx1⟩)
      · have := hpre_24.next_ge
        refine .inr ⟨rfl, by omega, ⟨hq2, ?_⟩, hret2_17⟩
        rw [hB16] at hret2_18
        omega

end Rv64mc.Proof.Bus.TryMapT

/-- info: 'Rv64mc.Proof.Bus.TryMapT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Bus.TryMapT.total
