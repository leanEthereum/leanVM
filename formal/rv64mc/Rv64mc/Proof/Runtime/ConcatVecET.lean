/-
  Rv64mc.Proof.Runtime.ConcatVecET

  `<[Vec<E>] as Concat<E>>::concat` over a slice of two vectors (the length the image's code fixes) is total:
  called with the result's slot (`a0`) and the two vectors' headers at `a1` and `a1 + 24`, it checks the total
  length's bytes against `isize::MAX` (`handle_error` above), allocates the result's block (none when empty), builds
  the header `(n, block, 0)` in its frame, extends it by each vector's elements (`Vec<E>::spec_extend`, `SpecExtendT`)
  and copies the header to `sret`. Its result is a vector's (`VecT`) of both lengths, its buffer allocated since the
  entry unless empty; the run ends with the guest's abort (`AbortStop`) where `alloc`, `spec_extend` or
  `handle_error` does. A safety-only contract (class D); it does not state the elements copied.

  The precondition: the result's slot a caller's (`SretPre`), in a window and 8-byte aligned; the two headers a
  caller's 48 bytes (`Owned`), 8-byte aligned, each a vector's (`VecT`). At its call sites (`sumcheck_round_poly`,
  twice, and `verify_gkr_grand_products`) both are slots of the caller's frame and the headers its frame's copies of
  vectors.

  The body is cut at the join after `alloc` (instruction 72, `Inv72`), after the first `spec_extend` (90, `Inv90`)
  and after the second (102, `fin`): `rv_symT` over the whole body runs out of heartbeats on the callee's
  precondition.

  ## Main definitions

  * `PreT`, `PostT`, `SpecT`, `Slots`, `Saved`, `Inv72`, `Inv90`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.SpecExtendT
import Rv64mc.Proof.Layout.CloneFormsT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Gen.Tmpl.Alloc.Slice.SliceVecE.AsConcatE.Concat

namespace Rv64mc.Proof.Runtime.ConcatVecET

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Layout.FormReprT (vecT_buf vecT_lt)
open Rv64mc.Proof.Layout.CloneFormsT (vecT_copy)
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Gen.Alloc.Slice.SliceVecE.AsConcatE.Concat (Link tmpl)

/-- The total precondition: the result's slot a caller's, in a window and aligned; the two vectors at `a1` and
    `a1 + 24` a caller's objects, vectors of `E`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
    env.Owned m (regs .x2) (regs .x11) 48 ∧ (regs .x11).toNat % 8 = 0 ∧
    VecT env m (regs .x11) 16 ∧ VecT env m (regs .x11 + 24#64) 16

/-- The total postcondition: the result a vector's of both lengths, its buffer fresh unless empty. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧
    (vecLen m' (regs .x10)).toNat = (vecLen m (regs .x11)).toNat + (vecLen m (regs .x11 + 24#64)).toNat ∧
    ((vecLen m' (regs .x10)).toNat = 0 ∨
      env.Fresh m m' (vecPtr m' (regs .x10)) ((vecLen m' (regs .x10)).toNat * 16))

/-- **The total contract of `<[Vec<E>] as Concat<E>>::concat`** over two vectors. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) SretVecOut AbortStop

/-- The prologue's seven saved words in `M`, at `top - 8` down to `top - 56`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21

/-- The six saved registers the function does not save, the entry's. -/
def Saved (regs R : Reg → Word) : Prop :=
  R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧
    R .x27 = regs .x27

/-- The state at instruction 72: the result's block `B` of `n` elements (none when `n = 0`, its pointer then `8`),
    allocated since the entry. -/
def Inv72 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧
    R .x18 = m.getMem (regs .x11 + 40#64) ∧ R .x19 = m.getMem (regs .x11 + 16#64) ∧
    (R .x20).toNat = (m.getMem (regs .x11 + 16#64)).toNat + (m.getMem (regs .x11 + 40#64)).toNat ∧
    ((R .x20).toNat = 0 ∨ (env.Fresh m M (R .x10) ((R .x20).toNat * 16) ∧ (R .x10).toNat % 8 = 0)) ∧
    Saved regs R ∧ Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

/-- The header `(n, B, 0)` stored in the frame at `top - 80`. -/
abbrev hdr (M : MachineState) (top n B : Word) : MachineState :=
  ((M.setMem (top + 18446744073709551536#64) n).setMem (top + 18446744073709551544#64) B).setMem
    (top + 18446744073709551552#64) 0#64

/-- The header's words read back. -/
theorem hdr_reads {M : MachineState} {top n B : Word} (h80 : 80 ≤ top.toNat) :
    (hdr M top n B).getMem (rvCapAt (top + 18446744073709551536#64)) = n ∧
      (hdr M top n B).getMem (rvPtrAt (top + 18446744073709551536#64)) = B ∧
      vecLen (hdr M top n B) (top + 18446744073709551536#64) = 0#64 := by
  have e : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 80 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => CloneT.toNat_add_neg hc (by omega)
  have e80 := e 18446744073709551536#64 80 rfl (by omega)
  have e72 := e 18446744073709551544#64 72 rfl (by omega)
  have e64 := e 18446744073709551552#64 64 rfl (by omega)
  have p8 : rvPtrAt (top + 18446744073709551536#64) = top + 18446744073709551544#64 := by
    rw [rvPtrAt_eq, BitVec.add_assoc]; rfl
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  refine ⟨?_, ?_, ?_⟩
  · rw [rvCapAt_eq, MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne
      (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · rw [p8, MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · rw [vecLen_eq, BitVec.add_assoc]; exact MachineState.getMem_setMem_eq

/-- `NEXT` after the header's stores. -/
theorem hdr_next {env : Env} {M : MachineState} {top n B : Word} (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) :
    env.next (hdr M top n B) = env.next M := by
  have e : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 80 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => CloneT.toNat_add_neg hc (by omega)
  simp only [hdr]
  rw [Env.next_setMem_stack (by rw [e _ 64 rfl (by omega)]; omega),
    Env.next_setMem_stack (by rw [e _ 72 rfl (by omega)]; omega),
    Env.next_setMem_stack (by rw [e _ 80 rfl (by omega)]; omega)]

/-- **The result's header copied** to `sret` from the frame's vector at `s`: the postcondition, the frame and the
    static data. -/
theorem fin_post {env : Env} {m M : MachineState} {top s : Word} {regs : Reg → Word} (h2 : regs .x2 = top)
    (hpre : PreT env regs m) (hW : Windows env top m) (hs8 : s + 8#64 = top + 18446744073709551544#64)
    (hs16 : s + 16#64 = top + 18446744073709551552#64)
    (hF : env.Frame top Tactic.F m M) (hS : env.Static M) (hV : VecT env M s 16)
    (hlen : (vecLen M s).toNat = (vecLen m (regs .x11)).toNat + (vecLen m (regs .x11 + 24#64)).toNat)
    (hfr : (vecLen M s).toNat = 0 ∨ env.Fresh m M (vecPtr M s) ((vecLen M s).toNat * 16)) {r : Reg → Word} :
    let M3 := ((M.setMem (regs .x10) (M.getMem s)).setMem (regs .x10 + 8#64)
      (M.getMem (top + 18446744073709551544#64))).setMem (regs .x10 + 16#64) (M.getMem (top + 18446744073709551552#64))
    PostT env regs m r M3 ∧ env.Frame top (SretVecOut regs m) m M3 ∧ env.Static M3 := by
  intro M3
  have hlay := env.layout
  obtain ⟨hown, hwin, hal, -⟩ := hpre
  have hown' : env.Owned m top (regs .x10) 24 := by rw [← h2]; exact hown
  have h24 := hown'.2
  have hnM := hF.2.1
  have hnm := hF.1
  have := hW.nextAddr_ge
  have e8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hwin' := hwin
  unfold InWin at hwin'
  have hnx : ∀ k, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k → b ≠ env.nextAddr := fun k hk b hb e => by
    rw [e] at hb; rcases hwin' with h | h <;> omega
  have hout : ∀ k, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k → SretVecOut regs m b := fun k hk b hb => by
    show InRange (regs .x10) Layouts.Vec.byteSize b; unfold InRange Layouts.Vec.byteSize; omega
  have hst : ∀ k, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k →
      b.toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ b.toNat := fun k hk b hb => by
    rcases hwin' with h | h <;> omega
  have n1 := Tactic.next_setMem (N := M) (v := M.getMem s) (hnx 0 (by omega) _ rfl)
  have n2 := Tactic.next_setMem (N := M.setMem (regs .x10) (M.getMem s))
    (v := M.getMem (top + 18446744073709551544#64)) (hnx 8 (by omega) _ e8)
  have n3 := Tactic.next_setMem (N := (M.setMem (regs .x10) (M.getMem s)).setMem (regs .x10 + 8#64)
    (M.getMem (top + 18446744073709551544#64))) (v := M.getMem (top + 18446744073709551552#64)) (hnx 16 (by omega) _ e16)
  have hN : env.next M3 = env.next M := by simp only [M3]; rw [n3, n2, n1]
  have r0 : M3.getMem (regs .x10) = M.getMem s := by
    simp only [M3]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r8 : M3.getMem (regs .x10 + 8#64) = M.getMem (s + 8#64) := by
    simp only [M3]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq, hs8]
  have r16 : M3.getMem (regs .x10 + 16#64) = M.getMem (s + 16#64) := by
    simp only [M3]; rw [MachineState.getMem_setMem_eq, hs16]
  have hv := vecT_copy hV hwin hal (by rw [hN]) r0 r8 r16
  have hl3 : vecLen M3 (regs .x10) = vecLen M s := by rw [vecLen_eq, vecLen_eq, r16]
  have hp3 : vecPtr M3 (regs .x10) = vecPtr M s := by rw [vecPtr_eq, vecPtr_eq, r8]
  refine ⟨⟨hv, by rw [hl3, hlen], by rw [hl3, hp3]; unfold Env.Fresh at hfr ⊢; rw [hN]; exact hfr⟩, ?_, ?_⟩
  · simp only [M3]
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_weaken hF) (hout 0 (by omega) _ rfl)
      (hnx 0 (by omega) _ rfl)) (hout 8 (by omega) _ e8) (hnx 8 (by omega) _ e8)) (hout 16 (by omega) _ e16)
      (hnx 16 (by omega) _ e16)
  · simp only [M3]
    exact Tactic.static_store (Tactic.static_store (Tactic.static_store hS (hst 0 (by omega) _ rfl))
      (hst 8 (by omega) _ e8)) (hst 16 (by omega) _ e16)

set_option rv_sym.heap true in
/-- **The return**, from instruction 102: the result's header copied to `sret`, the saved registers. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hW : Windows env top m) (h2 : regs .x2 = top) (hpre : PreT env regs m)
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) :
    ∀ R M, (R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ Saved regs R) → Slots M top ret regs →
      env.Frame top Tactic.F m M → env.Static M → M.code = m.code → VecT env M (top + 18446744073709551536#64) 16 →
      (vecLen M (top + 18446744073709551536#64)).toNat =
        (vecLen m (regs .x11)).toNat + (vecLen m (regs .x11 + 24#64)).toNat →
      ((vecLen M (top + 18446744073709551536#64)).toNat = 0 ∨ env.Fresh m M (vecPtr M (top + 18446744073709551536#64))
        ((vecLen M (top + 18446744073709551536#64)).toNat * 16)) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 102, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hsl hF hS hc hV hlen hfr
  have hlay := env.layout
  have := hW.nextAddr_ge
  have e80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := CloneT.toNat_add_neg (k := 80) rfl (by omega)
  have hs8 : top + 18446744073709551536#64 + 8#64 = top + 18446744073709551544#64 := by rw [BitVec.add_assoc]; rfl
  have hs16 : top + 18446744073709551536#64 + 16#64 = top + 18446744073709551552#64 := by
    rw [BitVec.add_assoc]; rfl
  obtain ⟨hPost, hF', hS'⟩ := fin_post (r := fun _ => 0#64) h2 hpre hW hs8 hs16 hF hS hV hlen hfr
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := hsl
  obtain ⟨-, -, -, -, -, -⟩ := hR.2.2
  obtain ⟨hown, hwin, hal, -⟩ := hpre
  have hwin' := hwin
  unfold InWin at hwin'
  have := hown.2
  have hW1 := hW.heapEnd_le
  have w0 : inWindow (regs .x10) 8 = true := by rw [inWindow_iff]; omega
  have w8 : inWindow (regs .x10 + 8#64) 8 = true := by rw [inWindow_iff, toNat_add_ofNat (by omega)]; omega
  have w16 : inWindow (regs .x10 + 16#64) 8 = true := by rw [inWindow_iff, toNat_add_ofNat (by omega)]; omega
  rv_introT hR
  rv_symT hp with [_hL]
  exact ⟨⟨rfl, t2, t3, t4, t5, t6, t7, rfl, rfl, rfl, rfl, rfl, rfl⟩, hF', hS', hPost⟩

/-- The state at instruction 90, after the first `spec_extend`: the header at `top - 80` a vector's of the first
    length, its buffer none or allocated since the entry. -/
def Inv90 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧
    R .x18 = m.getMem (regs .x11 + 40#64) ∧
    VecT env M (top + 18446744073709551536#64) 16 ∧
    (vecLen M (top + 18446744073709551536#64)).toNat = (m.getMem (regs .x11 + 16#64)).toNat ∧
    ((vecCap M (top + 18446744073709551536#64)).toNat = 0 ∨
      (env.next m).toNat ≤ (vecPtr M (top + 18446744073709551536#64)).toNat) ∧
    Saved regs R ∧ Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **From instruction 90**: the second `spec_extend`, then the return. -/
theorem tail2 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 80 + needS ≤ need) (hse : SpecExtendT.SpecT env p L.specExtend.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hpre : PreT env regs m) :
    ∀ R M, Inv90 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 90, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hR18, hV, hlen, hcap, hsv, hsl, hF, hS, hc⟩ := hI
  have hlay := env.layout
  obtain ⟨hsret, hwin0, hal0, hown1, hal1, hV0, hV1⟩ := id hpre
  have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hnm := hF.1
  have hnM := hF.2.1
  have kM := SpecExtendT.keep_of_frame hF (by omega)
  have ha1 : (regs .x11).toNat + 48 ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x11).toNat := by
    rw [← h2]; exact hown1.1
  have ha1' := hown1.2
  have e32 : (regs .x11 + 32#64).toNat = (regs .x11).toNat + 32 := toNat_add_ofNat (by omega)
  have e24 : (regs .x11 + 24#64).toNat = (regs .x11).toNat + 24 := toNat_add_ofNat (by omega)
  have p1 : M.getMem (regs .x11 + 32#64) = m.getMem (regs .x11 + 32#64) := kM _ (by omega)
  have l1 : vecLen m (regs .x11 + 24#64) = m.getMem (regs .x11 + 40#64) := by
    rw [vecLen_eq, BitVec.add_assoc]; rfl
  have l1p : vecPtr m (regs .x11 + 24#64) = m.getMem (regs .x11 + 32#64) := by
    rw [vecPtr_eq, BitVec.add_assoc]; rfl
  obtain ⟨hb1, -, -⟩ := vecT_buf hV1
  rw [l1, l1p] at hb1
  have s1 : (m.getMem (regs .x11 + 40#64)).toNat = 0 ∨ (0x10000000 ≤ (m.getMem (regs .x11 + 32#64)).toNat ∧
      (m.getMem (regs .x11 + 32#64)).toNat + (m.getMem (regs .x11 + 40#64)).toNat * 16 ≤ (env.next m).toNat ∧
      (m.getMem (regs .x11 + 32#64)).toNat % 8 = 0) := hb1.imp id fun ⟨h1, h3, h4⟩ => ⟨h1, h3, h4⟩
  have w1 := hV1.1
  unfold InWin at w1
  simp only [Layouts.Vec.byteSize, e24] at w1
  have w32 : inWindow (regs .x11 + 32#64) 8 = true := by rw [inWindow_iff, e32]; omega
  have q1 : (m.getMem (regs .x11 + 32#64) + m.getMem (regs .x11 + 40#64) <<< 4).toNat =
      (m.getMem (regs .x11 + 32#64)).toNat + 16 * (m.getMem (regs .x11 + 40#64)).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have := (m.getMem (regs .x11 + 32#64)).isLt
    rcases s1 with h | ⟨-, h, -⟩
    · rw [h]; omega
    · omega
  clear hb1 hV0 hV1 hown1
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR18 hsv)))
  have hle := hV.2.2
  have e80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := CloneT.toNat_add_neg (k := 80) rfl (by omega)
  have hha := SpecExtendT.HdrApart.of_stack hV.2.1 hnM (by rw [e80]; omega)
  rv_introT hR
  rv_symT hp stop [102] with [hL] using [hse]
  · exact hle
  · exact hha
  · rw [q1]
    rcases s1 with h | ⟨h1, h3, h4⟩
    · exact .inl (by omega)
    · have e80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := CloneT.toNat_add_neg (k := 80) rfl (by omega)
      refine .inr ⟨by rw [inWindow_iff]; omega, by unfold OffStack; rw [e80]; omega, .inl (by omega), ?_⟩
      have hp8 : vecPtr M (top + 18446744073709551536#64) = M.getMem (top + 18446744073709551544#64) := by
        rw [vecPtr_eq, BitVec.add_assoc]; rfl
      rw [vecCap_eq, hp8] at hcap
      exact hcap.imp_right fun h => .inl (by omega)
  · have e8' : (top + 18446744073709551536#64).toNat + 24 ≤ top.toNat - 56 := by rw [e80]; omega
    have hcap' : (vecCap M (top + 18446744073709551536#64)).toNat = 0 ∨
        (env.next m).toNat ≤ (vecPtr M (top + 18446744073709551536#64)).toNat := hcap
    have hbM := (vecT_buf hV).1
    obtain ⟨-, ⟨-, -, hbM', -⟩, -⟩ := hV
    rw [rvCapAt_eq, rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq] at hbM'
    have hnotOut : ∀ r' : Reg → Word, r' .x10 = top + 18446744073709551536#64 → ∀ b : Word,
        top.toNat - 56 ≤ b.toNat → b.toNat < top.toNat → ¬ SpecExtendT.OutT r' M b := fun r' hr b h1 h3 ho => by
      unfold SpecExtendT.OutT at ho
      rw [hr] at ho
      rcases ho with ho | ho
      · unfold InRange at ho; simp only [Layouts.Vec.byteSize] at ho; omega
      · unfold InRange at ho
        rcases hbM' with h0 | ⟨-, h5, -⟩
        · rw [h0] at ho; omega
        · unfold Env.Live at h5; omega
    have hmay : ∀ r' : Reg → Word, r' .x10 = top + 18446744073709551536#64 → ∀ b : Word,
        SpecExtendT.OutT r' M b → env.MayWrite top Tactic.F m m1 b := fun r' hr b ho => by
      unfold SpecExtendT.OutT at ho
      rw [hr] at ho
      rcases ho with ho | ho
      · unfold InRange at ho; simp only [Layouts.Vec.byteSize] at ho; exact .inl ⟨by omega, by omega⟩
      · unfold InRange at ho
        have := hret1_14.1
        rcases hbM' with h0 | ⟨-, h5, -⟩
        · rw [h0] at ho; omega
        · unfold Env.Live at h5
          rcases hcap' with h6 | h6
          · rw [h6] at ho; omega
          · exact .inr (.inl ⟨by omega, by omega⟩)
    have hF1 : env.Frame top Tactic.F m m1 := hF.trans hret1_14 (by rw [e80]; omega) (hmay _ rfl)
    obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := hsl
    have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 56 →
        m1.getMem (top + c) = M.getMem (top + c) := fun c k hc h0 hk' => by
      have e := CloneT.toNat_add_neg (t := top) hc (by omega)
      exact keep1_1 _ (by rw [BitVec.le_def, e, e80]; omega) (hnotOut _ rfl _ (by rw [e]; omega) (by rw [e]; omega))
    have hsl1 : Slots m1 top ret regs := ⟨(g _ 8 rfl (by omega) (by omega)).trans t1,
      (g _ 16 rfl (by omega) (by omega)).trans t2, (g _ 24 rfl (by omega) (by omega)).trans t3,
      (g _ 32 rfl (by omega) (by omega)).trans t4, (g _ 40 rfl (by omega) (by omega)).trans t5,
      (g _ 48 rfl (by omega) (by omega)).trans t6, (g _ 56 rfl (by omega) (by omega)).trans t7⟩
    have hV1 : VecT env m1 (top + 18446744073709551536#64) 16 :=
      ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩
    have hlen1 : (vecLen m1 (top + 18446744073709551536#64)).toNat =
        (vecLen m (regs .x11)).toNat + (vecLen m (regs .x11 + 24#64)).toNat := by
      rw [hret1_22, hlen, q1, l1]
      show _ = (m.getMem (regs .x11 + 16#64)).toNat + _
      omega
    have hb1 := (vecT_buf hV1).1
    have hl1 := hV1.2.2
    have hfr1 : (vecLen m1 (top + 18446744073709551536#64)).toNat = 0 ∨
        env.Fresh m m1 (vecPtr m1 (top + 18446744073709551536#64))
          ((vecLen m1 (top + 18446744073709551536#64)).toNat * 16) := by
      obtain ⟨-, ⟨-, -, hb2, -⟩, -⟩ := hV1
      rw [rvCapAt_eq, rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq] at hb2
      rcases hb2 with h0 | ⟨-, h5, -⟩
      · exact .inl (by omega)
      · unfold Env.Live at h5
        rcases hret1_23 with ⟨hc1, hp1⟩ | ⟨h7, h8⟩
        · rw [hc1] at h5 hl1; rw [hp1] at h5 ⊢
          rcases hcap' with h6 | h6
          · exact .inl (by omega)
          · exact .inr ⟨h6, by omega⟩
        · exact .inr ⟨by have := hF.1; omega, by omega⟩
    exact fin hp hL hk hW h2 hpre hlim _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsl1 hF1 hret1_15
      (hret1_24.trans hc) hV1 hlen1 hfr1

set_option rv_sym.heap true in
/-- **From instruction 72**: the header built, the first `spec_extend`, then the rest. -/
theorem tail {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 80 + needS ≤ need) (hse : SpecExtendT.SpecT env p L.specExtend.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hpre : PreT env regs m) :
    ∀ R M, Inv72 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 72, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hR18, hR19, h20, hB, hsv, hsl, hF, hS, hc⟩ := hI
  have hlay := env.layout
  have ht2 := tail2 hp hL hnS hse hk hstop hneed hW h16 h2 hpre
  obtain ⟨hsret, hwin0, hal0, hown1, hal1, hV0, hV1⟩ := hpre
  have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hnm := hF.1
  have hnM := hF.2.1
  have kM := SpecExtendT.keep_of_frame hF (by omega)
  obtain ⟨hb0, hl0, hc0⟩ := vecT_buf hV0
  obtain ⟨hb1, hl1, hc1⟩ := vecT_buf hV1
  have ha1 : (regs .x11).toNat + 48 ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x11).toNat := by
    rw [← h2]; exact hown1.1
  have ha1' := hown1.2
  have e8 : (regs .x11 + 8#64).toNat = (regs .x11).toNat + 8 := toNat_add_ofNat (by omega)
  have e32 : (regs .x11 + 32#64).toNat = (regs .x11).toNat + 32 := toNat_add_ofNat (by omega)
  have e24 : (regs .x11 + 24#64).toNat = (regs .x11).toNat + 24 := toNat_add_ofNat (by omega)
  have p0 : M.getMem (regs .x11 + 8#64) = vecPtr m (regs .x11) := kM _ (by omega)
  have l1 : vecLen m (regs .x11 + 24#64) = m.getMem (regs .x11 + 40#64) := by
    rw [vecLen_eq, BitVec.add_assoc]; rfl
  have l1p : vecPtr m (regs .x11 + 24#64) = m.getMem (regs .x11 + 32#64) := by
    rw [vecPtr_eq, BitVec.add_assoc]; rfl
  have p1 : M.getMem (regs .x11 + 32#64) = m.getMem (regs .x11 + 32#64) := kM _ (by omega)
  rw [l1, l1p] at hb1
  -- the two sources' numbers
  have s0 : (m.getMem (regs .x11 + 16#64)).toNat = 0 ∨ (0x10000000 ≤ (m.getMem (regs .x11 + 8#64)).toNat ∧
      (m.getMem (regs .x11 + 8#64)).toNat + (m.getMem (regs .x11 + 16#64)).toNat * 16 ≤ (env.next m).toNat ∧
      (m.getMem (regs .x11 + 8#64)).toNat % 8 = 0) := hb0.imp id fun ⟨h1, h3, h4⟩ => ⟨h1, h3, h4⟩
  have s1 : (m.getMem (regs .x11 + 40#64)).toNat = 0 ∨ (0x10000000 ≤ (m.getMem (regs .x11 + 32#64)).toNat ∧
      (m.getMem (regs .x11 + 32#64)).toNat + (m.getMem (regs .x11 + 40#64)).toNat * 16 ≤ (env.next m).toNat ∧
      (m.getMem (regs .x11 + 32#64)).toNat % 8 = 0) := hb1.imp id fun ⟨h1, h3, h4⟩ => ⟨h1, h3, h4⟩
  have n0 : (m.getMem (regs .x11 + 16#64)).toNat * 16 ≤ 0x78000000 := by rcases s0 with h | ⟨-, h, -⟩ <;> omega
  have n1 : (m.getMem (regs .x11 + 40#64)).toNat * 16 ≤ 0x78000000 := by rcases s1 with h | ⟨-, h, -⟩ <;> omega
  have w0 := hV0.1
  have w1 := hV1.1
  unfold InWin at w0 w1
  simp only [Layouts.Vec.byteSize, e24] at w0 w1
  have w8 : inWindow (regs .x11 + 8#64) 8 = true := by rw [inWindow_iff, e8]; omega
  have w32 : inWindow (regs .x11 + 32#64) 8 = true := by rw [inWindow_iff, e32]; omega
  have q0' : (m.getMem (regs .x11 + 8#64) + m.getMem (regs .x11 + 16#64) <<< 4).toNat =
      (m.getMem (regs .x11 + 8#64)).toNat + 16 * (m.getMem (regs .x11 + 16#64)).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have := (m.getMem (regs .x11 + 8#64)).isLt
    rcases s0 with h | ⟨-, h, -⟩
    · rw [h]; omega
    · omega
  have q0 : (m.getMem (regs .x11 + 8#64) + vecLen m (regs .x11) <<< 4).toNat =
      (m.getMem (regs .x11 + 8#64)).toNat + 16 * (vecLen m (regs .x11)).toNat := q0'
  have hn16 : (R .x20).toNat * 16 < 2 ^ 63 := by omega
  have hBn : (R .x20).toNat = 0 ∨ (0x10000000 ≤ (R .x10).toNat ∧ (R .x10).toNat + (R .x20).toNat * 16 ≤
      (env.next M).toNat ∧ (R .x10).toNat % 8 = 0) := by
    rcases hB with h | ⟨⟨h1, h3⟩, h4⟩
    · exact .inl h
    · have := hW.next_ge; exact .inr ⟨by omega, by omega, h4⟩
  clear hb0 hb1 hV0 hV1 hown1
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR18 (And.intro hR19 hsv))))
  rv_introT hR
  obtain ⟨r0, r8, r16⟩ := hdr_reads (M := M) (n := R .x20) (B := R .x10) (top := top) (by omega)
  have hnx := hdr_next (env := env) (M := M) (n := R .x20) (B := R .x10) hlim
  rv_symT hp stop [90] with [hL] using [hse]
  · show BufT env (hdr M top (R .x20) (R .x10))
      ((hdr M top (R .x20) (R .x10)).getMem (rvCapAt (top + 18446744073709551536#64)))
      ((hdr M top (R .x20) (R .x10)).getMem (rvPtrAt (top + 18446744073709551536#64))) 16
    rw [r0, r8]
    exact hBn.imp_right fun ⟨h1, h3, h4⟩ => ⟨h1, by unfold Env.Live; rw [hnx]; omega, h4⟩
  · show ((hdr M top (R .x20) (R .x10)).getMem (rvCapAt (top + 18446744073709551536#64))).toNat * 16 < 2 ^ 63
    rw [r0]; exact hn16
  · rw [q0']
    rcases s0 with h | ⟨h1, h3, h4⟩
    · exact .inl (by omega)
    · refine .inr ⟨by rw [inWindow_iff]; omega, by unfold OffStack; rw [CloneT.toNat_add_neg (k := 80) rfl (by omega)]; omega,
        .inl (by omega), ?_⟩
      exact hB.imp_right fun ⟨⟨h5, _⟩, _⟩ => .inl (by omega)
  · have e80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := CloneT.toNat_add_neg (k := 80) rfl (by omega)
    rw [rvCapAt_eq] at r0
    rw [rvPtrAt_eq] at r8
    have e72 : (top + 18446744073709551544#64).toNat = top.toNat - 72 := CloneT.toNat_add_neg (k := 72) rfl (by omega)
    have e64 : (top + 18446744073709551552#64).toNat = top.toNat - 64 := CloneT.toNat_add_neg (k := 64) rfl (by omega)
    have hFc : env.Frame top Tactic.F m (hdr M top (R .x20) (R .x10)) :=
      Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot hF (by omega) (by omega)) (by omega) (by omega))
        (by omega) (by omega)
    have hbufc : (R .x20).toNat = 0 ∨ ((env.next m).toNat ≤ (R .x10).toNat ∧
        (R .x10).toNat + (R .x20).toNat * 16 ≤ (env.next M).toNat) :=
      hB.imp_right fun ⟨⟨h5, h6⟩, _⟩ => ⟨h5, by omega⟩
    have hmay : ∀ r' : Reg → Word, r' .x10 = top + 18446744073709551536#64 → ∀ b : Word,
        SpecExtendT.OutT r' (hdr M top (R .x20) (R .x10)) b → env.MayWrite top Tactic.F m m1 b := fun r' hr b ho => by
      unfold SpecExtendT.OutT at ho
      rw [hr, vecPtr_eq, vecCap_eq, r0, r8] at ho
      have := hret1_14.1
      rw [hnx] at this
      rcases ho with ho | ho
      · unfold InRange at ho; simp only [Layouts.Vec.byteSize] at ho; exact .inl ⟨by omega, by omega⟩
      · unfold InRange at ho
        rcases hbufc with h6 | h6
        · rw [h6] at ho; omega
        · exact .inr (.inl ⟨by omega, by omega⟩)
    have hF1 : env.Frame top Tactic.F m m1 := hFc.trans hret1_14 (by rw [e80]; omega) (hmay _ rfl)
    have hnotOut : ∀ r' : Reg → Word, r' .x10 = top + 18446744073709551536#64 → ∀ b : Word,
        top.toNat - 56 ≤ b.toNat → b.toNat < top.toNat → ¬ SpecExtendT.OutT r' (hdr M top (R .x20) (R .x10)) b :=
      fun r' hr b h1 h3 ho => by
        unfold SpecExtendT.OutT at ho
        rw [hr, vecPtr_eq, vecCap_eq, r0, r8] at ho
        rcases ho with ho | ho
        · unfold InRange at ho; simp only [Layouts.Vec.byteSize] at ho; omega
        · unfold InRange at ho
          rcases hbufc with h6 | h6
          · rw [h6] at ho; omega
          · omega
    obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := hsl
    have gM : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 56 →
        (hdr M top (R .x20) (R .x10)).getMem (top + c) = M.getMem (top + c) := fun c k hc h0 hk' => by
      have e := CloneT.toNat_add_neg (t := top) hc (by omega)
      have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
      simp only [hdr]
      rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        MachineState.getMem_setMem_ne (ne _ _ (by omega))]
    have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 56 →
        m1.getMem (top + c) = M.getMem (top + c) := fun c k hc h0 hk' => by
      have e := CloneT.toNat_add_neg (t := top) hc (by omega)
      rw [← gM c k hc h0 hk']
      exact keep1_1 _ (by rw [BitVec.le_def, e, e80]; omega) (hnotOut _ rfl _ (by rw [e]; omega) (by rw [e]; omega))
    have hsl1 : Slots m1 top ret regs := ⟨(g _ 8 rfl (by omega) (by omega)).trans t1,
      (g _ 16 rfl (by omega) (by omega)).trans t2, (g _ 24 rfl (by omega) (by omega)).trans t3,
      (g _ 32 rfl (by omega) (by omega)).trans t4, (g _ 40 rfl (by omega) (by omega)).trans t5,
      (g _ 48 rfl (by omega) (by omega)).trans t6, (g _ 56 rfl (by omega) (by omega)).trans t7⟩
    have hV1 : VecT env m1 (top + 18446744073709551536#64) 16 :=
      ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩
    have hlen1 : (vecLen m1 (top + 18446744073709551536#64)).toNat = (m.getMem (regs .x11 + 16#64)).toNat := by
      rw [hret1_22, r16, q0']
      show 0 + _ = _
      omega
    have hcap1 : (vecCap m1 (top + 18446744073709551536#64)).toNat = 0 ∨
        (env.next m).toNat ≤ (vecPtr m1 (top + 18446744073709551536#64)).toNat := by
      rcases hret1_23 with ⟨hc1, hp1⟩ | ⟨h7, -⟩
      · rw [hc1, hp1, vecPtr_eq, vecCap_eq, r0, r8]
        exact hbufc.imp_right And.left
      · exact .inr (by rw [hnx] at h7; omega)
    exact ht2 _ _ ⟨rfl, rfl, rfl, rfl, hV1, hlen1, hcap1, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hsl1, hF1, hret1_15,
      hret1_24.trans (by simp only [MachineState.code_setMem]; exact hc)⟩

/-- The prologue's seven saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)

/-- The prologue's stores: the slots, the frame, the static data and the code. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) :
    Slots (saved m top ret regs) top ret regs ∧ env.Frame top Tactic.F m (saved m top ret regs) ∧
      env.Static (saved m top ret regs) ∧ (saved m top ret regs).code = m.code := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 80 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => CloneT.toNat_add_neg hc (by omega)
  have e1 := g 18446744073709551608#64 8 rfl (by omega)
  have e2 := g 18446744073709551600#64 16 rfl (by omega)
  have e3 := g 18446744073709551592#64 24 rfl (by omega)
  have e4 := g 18446744073709551584#64 32 rfl (by omega)
  have e5 := g 18446744073709551576#64 40 rfl (by omega)
  have e6 := g 18446744073709551568#64 48 rfl (by omega)
  have e7 := g 18446744073709551560#64 56 rfl (by omega)
  refine ⟨?_, ?_, ?_, by simp only [saved, MachineState.code_setMem]⟩
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6, e7] at h'; omega)])
  · simp only [saved]
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Env.Frame.refl hnx)
  · simp only [saved]
    repeat (first | refine Env.static_setMem_stack ?_ (by omega) | exact hS)

set_option rv_sym.heap true in
/-- **`<[Vec<E>] as Concat<E>>::concat` is total**, with 80 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needS needH : Nat} (hnA : 80 + needA ≤ need) (hnS : 80 + needS ≤ need) (hnH : 80 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hse : SpecExtendT.SpecT env p L.specExtend.idx needS)
    (hhe : Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [72] with [hL] using [hal', hhe]
  all_goals
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
    obtain ⟨hsl0, hF0, hS0, hc0⟩ := saved_ok (ret := ret) (regs := regs) hlim hpre_5 hpre_4
    simp only [saved] at hsl0 hF0 hS0 hc0
    have hpre : PreT env regs m := ⟨⟨hpre_6, hpre_7⟩, hpre_8, hpre_9, ⟨hpre_10, hpre_11⟩, hpre_12,
      ⟨hpre_13, ⟨hpre_14, hpre_15, hpre_16, hpre_17⟩, hpre_18⟩, ⟨hpre_19, ⟨hpre_20, hpre_21, hpre_22, hpre_23⟩, hpre_24⟩⟩
    have ht := tail hp hL hnS hse hk hstop hpre_3 hpre_26 hpre_25 hpre_2 hpre
    have hW1 := hpre_26.heapEnd_le
    have hl1 : vecLen m (regs .x11 + 24#64) = m.getMem (regs .x11 + 40#64) := by
      rw [vecLen_eq, BitVec.add_assoc]; rfl
    obtain ⟨hb0, hle0, -⟩ := vecT_buf (env := env) (m := m) (a := regs .x11) (s := 16)
      ⟨hpre_13, ⟨hpre_14, hpre_15, hpre_16, hpre_17⟩, hpre_18⟩
    obtain ⟨hb1, hle1, -⟩ := vecT_buf (env := env) (m := m) (a := regs .x11 + 24#64) (s := 16)
      ⟨hpre_19, ⟨hpre_20, hpre_21, hpre_22, hpre_23⟩, hpre_24⟩
    rw [hl1] at hb1
    have n0 : (m.getMem (regs .x11 + 16#64)).toNat * 16 ≤ 0x78000000 := by
      rcases hb0 with h | ⟨-, h, -⟩
      · show (vecLen m (regs .x11)).toNat * 16 ≤ _; rw [h]; omega
      · unfold Env.Live at h; show (vecLen m (regs .x11)).toNat * 16 ≤ _; omega
    have n1 : (m.getMem (regs .x11 + 40#64)).toNat * 16 ≤ 0x78000000 := by
      rcases hb1 with h | ⟨-, h, -⟩
      · rw [h]; omega
      · unfold Env.Live at h; omega
    have hsum : (m.getMem (regs .x11 + 40#64) + m.getMem (regs .x11 + 16#64)).toNat =
        (m.getMem (regs .x11 + 40#64)).toNat + (m.getMem (regs .x11 + 16#64)).toNat := by
      rw [BitVec.toNat_add]; omega
    have hsh : ((m.getMem (regs .x11 + 40#64) + m.getMem (regs .x11 + 16#64)) <<< 4).toNat =
        16 * ((m.getMem (regs .x11 + 40#64)).toNat + (m.getMem (regs .x11 + 16#64)).toNat) := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hsum]; omega
  · -- no elements: the empty vector
    have h0 : (m.getMem (regs .x11 + 40#64)).toNat + (m.getMem (regs .x11 + 16#64)).toNat = 0 := by
      have := congrArg BitVec.toNat hc; rw [hsh] at this; simp only [BitVec.toNat_ofNat] at this; omega
    exact ht _ _ ⟨rfl, rfl, rfl, rfl, rfl, by simp only [Tactic.rf, BitVec.toNat_ofNat]; omega, .inl rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hsl0, hF0, hS0, hc0⟩
  · rw [hsh]; omega
  · -- the block `alloc` returned
    have e80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := CloneT.toNat_add_neg (k := 80) rfl (by omega)
    obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := hsl0
    have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 56 →
        m1.getMem (top + c) = (((((((m.setMem (top + 18446744073709551608#64) ret).setMem
          (top + 18446744073709551600#64) (regs .x8)).setMem (top + 18446744073709551592#64) (regs .x9)).setMem
          (top + 18446744073709551584#64) (regs .x18)).setMem (top + 18446744073709551576#64) (regs .x19)).setMem
          (top + 18446744073709551568#64) (regs .x20)).setMem (top + 18446744073709551560#64) (regs .x21)).getMem
          (top + c) := fun c k hc' h0 hk' => by
      have e := CloneT.toNat_add_neg (t := top) hc' (by omega)
      exact keep1_1 _ (by rw [BitVec.le_def, e, e80]; omega)
    rw [hsh] at hret1_18
    exact ht _ _ ⟨rfl, rfl, rfl, rfl, rfl, by simp only [Tactic.rf]; omega,
      .inr ⟨⟨hret1_16, by simp only [Tactic.rf]; rw [hsum]; omega⟩, hret1_17⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨(g _ 8 rfl (by omega) (by omega)).trans t1, (g _ 16 rfl (by omega) (by omega)).trans t2,
        (g _ 24 rfl (by omega) (by omega)).trans t3, (g _ 32 rfl (by omega) (by omega)).trans t4,
        (g _ 40 rfl (by omega) (by omega)).trans t5, (g _ 48 rfl (by omega) (by omega)).trans t6,
        (g _ 56 rfl (by omega) (by omega)).trans t7⟩,
      hF0.trans hret1_14 (by rw [e80]; omega) (fun b hb => hb.elim), hret1_15, hret1_19.trans hc0⟩

end Rv64mc.Proof.Runtime.ConcatVecET

/-- info: 'Rv64mc.Proof.Runtime.ConcatVecET.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.ConcatVecET.total
