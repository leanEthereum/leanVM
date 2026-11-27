/-
  Rv64mc.Proof.Runtime.ConcatSliceET

  `<[&[E]] as Concat<E>>::concat` is total: called with the result's slot (`a0`) and `n > 0` slices of `E` (`a1`,
  `n` in `a2`), each a pointer and a length (16 bytes), it sums the lengths (the first loop), checks the total's
  bytes against `isize::MAX` (`handle_error` above), allocates the result's block (none when empty), builds the
  header `(total, block, 0)` in its frame, extends it by each slice's elements (the second loop, `Vec<E>::spec_extend`,
  `SpecExtendT`) and copies the header to `sret`. Its result is a vector's (`VecT`) of the lengths' sum, its buffer
  allocated since the entry unless empty; the run ends with the guest's abort (`AbortStop`) where `alloc`,
  `spec_extend` or `handle_error` does. A safety-only contract (class D); it does not state the elements copied.

  The precondition: the result's slot a caller's (`SretPre`), in a window and 8-byte aligned; at least one slice (both
  loops test at their end); the slices' array a caller's (`Owned`), in a window, 8-byte aligned; each slice, unless
  empty, in a window, apart from the stack below the stack pointer, below `NEXT` or from the heap's end (`SliceT`).
  At its seven call sites (`verify_keccak` three times, `verify_bus_balance`, `Placement::stack_point`, the WHIR
  stacked opening's closure twice) the array is in the caller's frame with two or three slices; `sret` is a frame
  slot, except at `verify_keccak`'s step 557, where it is `verify_keccak`'s own `a0`.

  The body is cut at the loops' heads (24, `L1`; 90, `L2`), at the sum (32, `Inv32`), at the join after `alloc` (82,
  `Inv82`), after each `spec_extend` (108, `Mid`, `after_call` composing the callee's frame) and at the copy to `sret`
  (112, `fin`): each part is its own declaration, under the default heartbeats.

  ## Main definitions

  * `sptr`, `slen`, `lenSum`, `SliceT`, `PreT`, `PostT`, `SpecT`
  * `L1`, `Inv32`, `Inv82`, `L2`, `Mid`: the states at the cuts

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.ConcatVecET
import Rv64mc.Gen.Tmpl.Alloc.Slice.SliceRefSliceE.AsConcatE.Concat

namespace Rv64mc.Proof.Runtime.ConcatSliceET

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Layout.FormReprT (vecT_buf)
open Rv64mc.Proof.Layout.CloneFormsT (vecT_copy)
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Gen.Alloc.Slice.SliceRefSliceE.AsConcatE.Concat (Link tmpl)

/-- The `k`-th slice's pointer in the array at `a`. -/
abbrev sptr (m : MachineState) (a : Word) (k : Nat) : Word := m.getMem (a + BitVec.ofNat 64 (16 * k))

/-- The `k`-th slice's length in the array at `a`. -/
abbrev slen (m : MachineState) (a : Word) (k : Nat) : Word := m.getMem (a + BitVec.ofNat 64 (16 * k + 8))

/-- The first `k` slices' lengths' sum. -/
def lenSum (m : MachineState) (a : Word) : Nat → Nat
  | 0 => 0
  | k + 1 => lenSum m a k + (slen m a k).toNat

/-- Each length at most `B`: the first `k` sum to at most `k * B`. -/
theorem lenSum_le {m : MachineState} {a : Word} {B : Nat} :
    ∀ k, (∀ j, j < k → (slen m a j).toNat ≤ B) → lenSum m a k ≤ k * B
  | 0, _ => by simp [lenSum]
  | k + 1, h => by
    have := lenSum_le k fun j hj => h j (by omega)
    have := h k (by omega)
    simp only [lenSum]
    rw [Nat.succ_mul]
    omega

/-- A slice of `n` elements at `q`: unless empty, in a window, apart from the stack below `sp`, below `NEXT` or from
    the heap's end. -/
def SliceT (env : Env) (m : MachineState) (sp q n : Word) : Prop :=
  n.toNat = 0 ∨ (inWindow q (16 * n.toNat) = true ∧ OffStack env sp q (16 * n.toNat) ∧
    (q.toNat + 16 * n.toNat ≤ (env.next m).toNat ∨ env.heapEnd.toNat ≤ q.toNat))

/-- The total precondition: the result's slot a caller's, in a window and aligned; at least one slice; the slices'
    array a caller's, in a window and aligned; each slice `SliceT`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ 0 < (regs .x12).toNat ∧
    env.Owned m (regs .x2) (regs .x11) (16 * (regs .x12).toNat) ∧ InWin env (regs .x11) (16 * (regs .x12).toNat) ∧
    (regs .x11).toNat % 8 = 0 ∧
    ∀ k, k < (regs .x12).toNat → SliceT env m (regs .x2) (sptr m (regs .x11) k) (slen m (regs .x11) k)

/-- The total postcondition: the result a vector's of the lengths' sum, its buffer fresh unless empty. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ (vecLen m' (regs .x10)).toNat = lenSum m (regs .x11) (regs .x12).toNat ∧
    ((vecLen m' (regs .x10)).toNat = 0 ∨
      env.Fresh m m' (vecPtr m' (regs .x10)) ((vecLen m' (regs .x10)).toNat * 16))

/-- **The total contract of `<[&[E]] as Concat<E>>::concat`.** -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) SretVecOut AbortStop

/-- The prologue's six saved words in `M`, at `top - 8` down to `top - 48`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20

/-- The seven saved registers the function does not save, the entry's. -/
def Saved (regs R : Reg → Word) : Prop :=
  R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- **The result's header copied** to `sret` from the frame's vector: the postcondition, the frame and the static
    data. -/
theorem fin_post {env : Env} {m M : MachineState} {top : Word} {regs : Reg → Word} (h2 : regs .x2 = top)
    (hsret : SretPre env regs m) (hwin : InWin env (regs .x10) 24) (hal : (regs .x10).toNat % 8 = 0)
    (hW : Windows env top m) (hF : env.Frame top Tactic.F m M) (hS : env.Static M) (hV : VecT env M (top + 18446744073709551544#64) 16)
    (hlen : (vecLen M (top + 18446744073709551544#64)).toNat = lenSum m (regs .x11) (regs .x12).toNat)
    (hfr : (vecLen M (top + 18446744073709551544#64)).toNat = 0 ∨ env.Fresh m M (vecPtr M (top + 18446744073709551544#64)) ((vecLen M (top + 18446744073709551544#64)).toNat * 16))
    {r : Reg → Word} :
    let M3 := ((M.setMem (regs .x10) (M.getMem (top + 18446744073709551544#64))).setMem (regs .x10 + 8#64)
      (M.getMem (top + 18446744073709551552#64))).setMem (regs .x10 + 16#64) (M.getMem (top + 18446744073709551560#64))
    PostT env regs m r M3 ∧ env.Frame top (SretVecOut regs m) m M3 ∧ env.Static M3 := by
  intro M3
  have hlay := env.layout
  have hown' : env.Owned m top (regs .x10) 24 := by rw [← h2]; exact hsret
  have h24 := hown'.2
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
  have n1 := Tactic.next_setMem (N := M) (v := M.getMem (top + 18446744073709551544#64)) (hnx 0 (by omega) _ rfl)
  have n2 := Tactic.next_setMem (N := M.setMem (regs .x10) (M.getMem (top + 18446744073709551544#64)))
    (v := M.getMem (top + 18446744073709551552#64)) (hnx 8 (by omega) _ e8)
  have n3 := Tactic.next_setMem (N := (M.setMem (regs .x10) (M.getMem (top + 18446744073709551544#64))).setMem (regs .x10 + 8#64)
    (M.getMem (top + 18446744073709551552#64))) (v := M.getMem (top + 18446744073709551560#64)) (hnx 16 (by omega) _ e16)
  have hN : env.next M3 = env.next M := by simp only [M3]; rw [n3, n2, n1]
  have hs8 : top + 18446744073709551544#64 + 8#64 = top + 18446744073709551552#64 := by rw [BitVec.add_assoc]; rfl
  have hs16 : top + 18446744073709551544#64 + 16#64 = top + 18446744073709551560#64 := by rw [BitVec.add_assoc]; rfl
  have r0 : M3.getMem (regs .x10) = M.getMem (top + 18446744073709551544#64) := by
    simp only [M3]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r8 : M3.getMem (regs .x10 + 8#64) = M.getMem (top + 18446744073709551544#64 + 8#64) := by
    simp only [M3]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq, hs8]
  have r16 : M3.getMem (regs .x10 + 16#64) = M.getMem (top + 18446744073709551544#64 + 16#64) := by
    simp only [M3]; rw [MachineState.getMem_setMem_eq, hs16]
  have hv := vecT_copy hV hwin hal (by rw [hN]) r0 r8 r16
  have hl3 : vecLen M3 (regs .x10) = vecLen M (top + 18446744073709551544#64) := by rw [vecLen_eq, vecLen_eq, r16]
  have hp3 : vecPtr M3 (regs .x10) = vecPtr M (top + 18446744073709551544#64) := by rw [vecPtr_eq, vecPtr_eq, r8]
  refine ⟨⟨hv, by rw [hl3, hlen], by rw [hl3, hp3]; unfold Env.Fresh at hfr ⊢; rw [hN]; exact hfr⟩, ?_, ?_⟩
  · simp only [M3]
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_weaken hF) (hout 0 (by omega) _ rfl)
      (hnx 0 (by omega) _ rfl)) (hout 8 (by omega) _ e8) (hnx 8 (by omega) _ e8)) (hout 16 (by omega) _ e16)
      (hnx 16 (by omega) _ e16)
  · simp only [M3]
    exact Tactic.static_store (Tactic.static_store (Tactic.static_store hS (hst 0 (by omega) _ rfl))
      (hst 8 (by omega) _ e8)) (hst 16 (by omega) _ e16)

set_option rv_sym.heap true in
/-- **The return**, from instruction 112: the result's header copied to `sret`, the saved registers. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hW : Windows env top m) (h2 : regs .x2 = top) (hpre : PreT env regs m)
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (h16 : top.toNat % 16 = 0) :
    ∀ R M, (R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ Saved regs R) → Slots M top ret regs →
      env.Frame top Tactic.F m M → env.Static M → M.code = m.code → VecT env M (top + 18446744073709551544#64) 16 →
      (vecLen M (top + 18446744073709551544#64)).toNat = lenSum m (regs .x11) (regs .x12).toNat →
      ((vecLen M (top + 18446744073709551544#64)).toNat = 0 ∨ env.Fresh m M (vecPtr M (top + 18446744073709551544#64)) ((vecLen M (top + 18446744073709551544#64)).toNat * 16)) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 112, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hsl hF hS hcd hV hlen hfr
  have hlay := env.layout
  have := hW.nextAddr_ge
  obtain ⟨hsret, hwin, hal, -⟩ := hpre
  obtain ⟨hPost, hF', hS'⟩ := fin_post (r := fun _ => 0#64) h2 hsret hwin hal hW hF hS hV hlen hfr
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hsl
  obtain ⟨-, -, -, -, -, -, -⟩ := hR.2.2
  have hwin' := hwin
  unfold InWin at hwin'
  have := hsret.2
  have hW1 := hW.heapEnd_le
  have w0 : inWindow (regs .x10) 8 = true := by rw [inWindow_iff]; omega
  have w8 : inWindow (regs .x10 + 8#64) 8 = true := by rw [inWindow_iff, toNat_add_ofNat (by omega)]; omega
  have w16 : inWindow (regs .x10 + 16#64) 8 = true := by rw [inWindow_iff, toNat_add_ofNat (by omega)]; omega
  rv_introT hR
  rv_symT hp with [_hL]
  exact ⟨⟨rfl, t2, t3, t4, t5, t6, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hF', hS', hPost⟩

/-- The second loop's head with `k + 1` slices left: the cursor `x11` at the next slice, `x19` past the last; the
    header at `sp + 8` a vector's of the lengths before the cursor, its buffer none or allocated since the entry. -/
def L2 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ Saved regs R ∧ k < (regs .x12).toNat ∧
    (R .x11).toNat = (regs .x11).toNat + 16 * ((regs .x12).toNat - 1 - k) ∧
    (R .x19).toNat = (regs .x11).toNat + 16 * (regs .x12).toNat ∧
    VecT env M (top + 18446744073709551544#64) 16 ∧ (vecLen M (top + 18446744073709551544#64)).toNat = lenSum m (regs .x11) ((regs .x12).toNat - 1 - k) ∧
    ((vecCap M (top + 18446744073709551544#64)).toNat = 0 ∨ (env.next m).toNat ≤ (vecPtr M (top + 18446744073709551544#64)).toNat) ∧
    Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

/-- The state after a slice's `spec_extend` (instruction 108) with `k + 1` slices left before it: the cursor `x9`
    past that slice, the header a vector's of the lengths before the cursor. -/
def Mid (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ Saved regs R ∧
    (R .x9).toNat = (regs .x11).toNat + 16 * ((regs .x12).toNat - k) ∧
    (R .x19).toNat = (regs .x11).toNat + 16 * (regs .x12).toNat ∧
    VecT env M (top + 18446744073709551544#64) 16 ∧
    (vecLen M (top + 18446744073709551544#64)).toNat = lenSum m (regs .x11) ((regs .x12).toNat - k) ∧
    ((vecCap M (top + 18446744073709551544#64)).toNat = 0 ∨
      (env.next m).toNat ≤ (vecPtr M (top + 18446744073709551544#64)).toNat) ∧
    Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **After a slice's `spec_extend`**: back to the loop's head, or the return after the last slice. -/
theorem back {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hfin : ∀ R M, (R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ Saved regs R) →
      Slots M top ret regs → env.Frame top Tactic.F m M → env.Static M → M.code = m.code →
      VecT env M (top + 18446744073709551544#64) 16 →
      (vecLen M (top + 18446744073709551544#64)).toNat = lenSum m (regs .x11) (regs .x12).toNat →
      ((vecLen M (top + 18446744073709551544#64)).toNat = 0 ∨ env.Fresh m M
        (vecPtr M (top + 18446744073709551544#64)) ((vecLen M (top + 18446744073709551544#64)).toNat * 16)) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 112, ret, top⟩ :: rest, R, M⟩) :
    ∀ k, k < (regs .x12).toNat →
      (∀ k' R M, k' < k → L2 env m top ret regs k' R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 90, ret, top⟩ :: rest, R, M⟩) →
      ∀ R M, Mid env m top ret regs k R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 108, ret, top⟩ :: rest, R, M⟩ := by
  intro k hkn ih R M hI
  obtain ⟨hR2, hR8, hsv, h9, h19, hV, hlen, hcap, hsl, hF, hS, hcd⟩ := hI
  have hR := And.intro hR2 (And.intro hR8 hsv)
  rv_introT hR
  rv_symT hp stop [90, 112] with [_hL]
  · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h9, h19]; subst h0; omega))
    clear hc
    exact ih (k - 1) _ _ (by omega) ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by omega,
      by simp only [Tactic.rf]; rw [h9]; omega, h19, hV, by rw [hlen]; congr 1; omega, hcap, hsl, hF, hS, hcd⟩
  · have hk0 : k = 0 := by
      have := congrArg BitVec.toNat hc; rw [h9, h19] at this; omega
    clear hc
    subst hk0
    rw [Nat.sub_zero] at hlen
    have hfr : (vecLen M (top + 18446744073709551544#64)).toNat = 0 ∨ env.Fresh m M
        (vecPtr M (top + 18446744073709551544#64)) ((vecLen M (top + 18446744073709551544#64)).toNat * 16) := by
      have hl := hV.2.2
      obtain ⟨-, ⟨-, -, hb2, -⟩, -⟩ := id hV
      rw [rvCapAt_eq, rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq] at hb2
      rcases hb2 with h0 | ⟨-, h5, -⟩
      · exact .inl (by omega)
      · unfold Env.Live at h5
        rcases hcap with h6 | h6
        · exact .inl (by omega)
        · exact .inr ⟨h6, by omega⟩
    exact hfin _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ hsl hF hS hcd hV hlen hfr

/-- **After a slice's `spec_extend`** on the header at `sp + 8`: the frame, the slots and the buffer's place, from
    the callee's frame and what it keeps. -/
theorem after_call {env : Env} {m M m1 : MachineState} {top ret : Word} {regs r' : Reg → Word}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hF : env.Frame top Tactic.F m M) (hsl : Slots M top ret regs) (hV : VecT env M (top + 18446744073709551544#64) 16)
    (hcap : (vecCap M (top + 18446744073709551544#64)).toNat = 0 ∨
      (env.next m).toNat ≤ (vecPtr M (top + 18446744073709551544#64)).toNat)
    (h14 : env.Frame (top + 18446744073709551536#64) (SpecExtendT.OutT r' M) M m1)
    (keep : ∀ a : Word, top + 18446744073709551536#64 ≤ a → ¬ SpecExtendT.OutT r' M a → m1.getMem a = M.getMem a)
    (h23 : vecCap m1 (top + 18446744073709551544#64) = vecCap M (top + 18446744073709551544#64) ∧
        vecPtr m1 (top + 18446744073709551544#64) = vecPtr M (top + 18446744073709551544#64) ∨
      env.Fresh M m1 (vecPtr m1 (top + 18446744073709551544#64))
        ((vecCap m1 (top + 18446744073709551544#64)).toNat * 16))
    (hr : r' .x10 = top + 18446744073709551544#64) :
    env.Frame top Tactic.F m m1 ∧ Slots m1 top ret regs ∧
      ((vecCap m1 (top + 18446744073709551544#64)).toNat = 0 ∨
        (env.next m).toNat ≤ (vecPtr m1 (top + 18446744073709551544#64)).toNat) := by
  have hlay := env.layout
  have hnM := hF.2.1
  have hn1 := h14.1
  have e80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 :=
    CloneT.toNat_add_neg (k := 80) rfl (by omega)
  have e72 : (top + 18446744073709551544#64).toNat = top.toNat - 72 :=
    CloneT.toNat_add_neg (k := 72) rfl (by omega)
  have hbM := hV.2.1.2.2.1
  rw [rvCapAt_eq, rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq] at hbM
  have hout : ∀ b : Word, SpecExtendT.OutT r' M b →
      (top.toNat - 72 ≤ b.toNat ∧ b.toNat < top.toNat - 48) ∨
        ((vecCap M (top + 18446744073709551544#64)).toNat ≠ 0 ∧ (env.next m).toNat ≤ b.toNat ∧
          b.toNat < (env.next M).toNat) := fun b ho => by
    unfold SpecExtendT.OutT at ho
    rw [hr] at ho
    rcases ho with ho | ho
    · unfold InRange at ho; simp only [Layouts.Vec.byteSize] at ho; exact .inl ⟨by omega, by omega⟩
    · unfold InRange at ho
      rcases hbM with h0 | ⟨-, h5, -⟩
      · rw [h0] at ho; omega
      · unfold Env.Live at h5
        rcases hcap with h6 | h6
        · rw [h6] at ho; omega
        · exact .inr ⟨by omega, by omega, by omega⟩
  have hF1 : env.Frame top Tactic.F m m1 := hF.trans h14 (by rw [e80]; omega) fun b ho => by
    exact (hout b ho).imp (fun ⟨h1, h3⟩ => ⟨by omega, by omega⟩) fun ⟨_, h1, h3⟩ => .inl ⟨h1, by omega⟩
  refine ⟨hF1, ?_, ?_⟩
  · obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hsl
    have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 48 →
        m1.getMem (top + c) = M.getMem (top + c) := fun c k hc h0 hk' => by
      have e := CloneT.toNat_add_neg (t := top) hc (by omega)
      refine keep _ (by rw [BitVec.le_def, e, e80]; omega) fun ho => ?_
      rcases hout _ ho with ⟨h1, h3⟩ | ⟨-, h1, h3⟩ <;> rw [e] at h1 h3 <;> omega
    exact ⟨(g _ 8 rfl (by omega) (by omega)).trans t1, (g _ 16 rfl (by omega) (by omega)).trans t2,
      (g _ 24 rfl (by omega) (by omega)).trans t3, (g _ 32 rfl (by omega) (by omega)).trans t4,
      (g _ 40 rfl (by omega) (by omega)).trans t5, (g _ 48 rfl (by omega) (by omega)).trans t6⟩
  · rcases h23 with ⟨hc1, hp1⟩ | ⟨h7, -⟩
    · rw [hc1, hp1]; exact hcap
    · exact .inr (by have := hF.1; omega)

set_option rv_sym.heap true in
/-- **The second loop**, from its head: each slice's `spec_extend`, then the return. -/
theorem loop2 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 80 + needS ≤ need) (hse : SpecExtendT.SpecT env p L.specExtend.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hpre : PreT env regs m) :
    ∀ k R M, L2 env m top ret regs k R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 90, ret, top⟩ :: rest, R, M⟩ := by
  have hback := back hp hL (fin hp hL hk hW h2 hpre (by omega) h16)
  refine Total.loop (I := rvIsa) (L2 env m top ret regs) fun k R M hI ih => ?_
  obtain ⟨hR2, hR8, hsv, hkn, h11, h19, hV, hlen, hcap, hsl, hF, hS, hc⟩ := hI
  have hlay := env.layout
  obtain ⟨hsret, hwin0, hal0, hn0, hown1, hwin1, hal1, hsrc⟩ := hpre
  have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hnm := hF.1
  have hnM := hF.2.1
  have kM := SpecExtendT.keep_of_frame hF (by omega)
  have hw1 := hwin1
  unfold InWin at hw1
  have ha1 : (regs .x11).toNat + 16 * (regs .x12).toNat ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x11).toNat := by
    rw [← h2]; exact hown1.1
  have hj : (regs .x12).toNat - 1 - k < (regs .x12).toNat := by omega
  have e0 : R .x11 = regs .x11 + BitVec.ofNat 64 (16 * ((regs .x12).toNat - 1 - k)) :=
    BitVec.eq_of_toNat_eq (by rw [h11, toNat_add_ofNat (by omega)])
  have e8 : R .x11 + 8#64 = regs .x11 + BitVec.ofNat 64 (16 * ((regs .x12).toNat - 1 - k) + 8) :=
    BitVec.eq_of_toNat_eq (by rw [toNat_add_ofNat (by omega), h11, toNat_add_ofNat (by omega)]; omega)
  have hs : SliceT env m (regs .x2) (m.getMem (R .x11)) (m.getMem (R .x11 + 8#64)) := by
    rw [e8, e0]; exact hsrc _ hj
  clear e0 e8
  have hs'' := hs
  unfold SliceT OffStack at hs''
  rw [h2] at hs''
  have q1 : (m.getMem (R .x11) + m.getMem (R .x11 + 8#64) <<< 4).toNat =
      (m.getMem (R .x11)).toNat + 16 * (m.getMem (R .x11 + 8#64)).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have := (m.getMem (R .x11)).isLt
    rcases hs'' with h | ⟨h, -, -⟩
    · rw [h]; omega
    · rw [inWindow_iff] at h; omega
  clear hs''
  have hle := hV.2.2
  have e72 : (top + 18446744073709551544#64).toNat = top.toNat - 72 :=
    CloneT.toNat_add_neg (k := 72) rfl (by omega)
  have e80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 :=
    CloneT.toNat_add_neg (k := 80) rfl (by omega)
  have hha := SpecExtendT.HdrApart.of_stack hV.2.1 hnM (by rw [e72]; omega)
  have p8 : top + 18446744073709551544#64 + 8#64 = top + 18446744073709551552#64 := by rw [BitVec.add_assoc]; rfl
  have hR := And.intro hR2 (And.intro hR8 hsv)
  rv_introT hR
  rv_symT hp stop [108] with [hL] using [hse]
  · exact hle
  · exact hha
  · have hbM := hV.2.1.2.2.1
    rw [rvCapAt_eq, rvPtrAt_eq, p8] at hbM
    rw [vecCap_eq, vecPtr_eq, p8] at hcap
    rw [q1, Nat.add_sub_cancel_left]
    unfold SliceT OffStack at hs
    rw [h2] at hs
    rcases hs with h | ⟨h1, h3, h4⟩
    · exact .inl (by omega)
    · refine .inr ⟨h1, by unfold OffStack; rw [e80]; omega, h4.imp (fun h => by omega) id, ?_⟩
      rcases hbM with h0 | ⟨-, h5, -⟩
      · exact .inl h0
      · unfold Env.Live at h5
        exact hcap.imp_right fun h6 => h4.imp (fun h => by omega) fun h => by omega
  · obtain ⟨hF1, hsl1, hcap1⟩ := after_call hlim hF hsl hV hcap hret1_14 keep1_1 hret1_23 rfl
    have hV1 : VecT env m1 (top + 18446744073709551544#64) 16 :=
      ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩
    have hc1 : m1.code = m.code := hret1_24.trans hc
    have hS1 := hret1_15
    have h22 := hret1_22
    clear keep1_1 keep1_2 hret1_14 hret1_16 hret1_17 hret1_18 hret1_19 hret1_20 hret1_21 hret1_22 hret1_23 hret1_24
      hret1_15 hV hcap hha hle hs kM hF hS hc hsl hw1 ha1 hsrc hown1 hwin1 hsret hwin0
    have e8 : R .x11 + 8#64 = regs .x11 + BitVec.ofNat 64 (16 * ((regs .x12).toNat - 1 - k) + 8) :=
      BitVec.eq_of_toNat_eq (by rw [toNat_add_ofNat (by omega), h11, toNat_add_ofNat (by omega)]; omega)
    have hl8 : (slen m (regs .x11) ((regs .x12).toNat - 1 - k)).toNat = (m.getMem (R .x11 + 8#64)).toNat := by
      rw [e8]
    have hlen1 : (vecLen m1 (top + 18446744073709551544#64)).toNat = lenSum m (regs .x11) ((regs .x12).toNat - k) := by
      have e1 : (regs .x12).toNat - k = (regs .x12).toNat - 1 - k + 1 := by omega
      rw [h22, hlen, q1, e1]
      simp only [lenSum]
      omega
    have x16 : (R .x11 + 16#64).toNat = (regs .x11).toNat + 16 * ((regs .x12).toNat - k) := by
      rw [toNat_add_ofNat (by omega), h11]; omega
    exact hback k hkn ih _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, x16, h19, hV1, hlen1, hcap1, hsl1, hF1,
      hS1, hc1⟩

/-- The header `(c, B, 0)` stored at `sp + 8`. -/
abbrev hdr (M : MachineState) (top c B : Word) : MachineState :=
  ((M.setMem (top + 18446744073709551544#64) c).setMem (top + 18446744073709551552#64) B).setMem
    (top + 18446744073709551560#64) 0#64

/-- **The header built**: a vector's with no elements, over the block `B` of `c` elements (none when `c = 0`)
    allocated since the entry; the slots, the frame and the static data kept. -/
theorem hdr_ok {env : Env} {m M : MachineState} {top ret c B : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (h16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (hsl : Slots M top ret regs) (hF : env.Frame top Tactic.F m M) (hS : env.Static M) (hc58 : c.toNat < 2 ^ 58)
    (hB : c.toNat = 0 ∨ (env.Fresh m M B (c.toNat * 16) ∧ B.toNat % 8 = 0)) :
    VecT env (hdr M top c B) (top + 18446744073709551544#64) 16 ∧
      (vecLen (hdr M top c B) (top + 18446744073709551544#64)).toNat = 0 ∧
      ((vecCap (hdr M top c B) (top + 18446744073709551544#64)).toNat = 0 ∨
        (env.next m).toNat ≤ (vecPtr (hdr M top c B) (top + 18446744073709551544#64)).toNat) ∧
      Slots (hdr M top c B) top ret regs ∧ env.Frame top Tactic.F m (hdr M top c B) ∧
      env.Static (hdr M top c B) := by
  have hlay := env.layout
  have := hW.top_le
  have := hW.next_ge
  have hnM := hF.2.1
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 80 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => CloneT.toNat_add_neg hc (by omega)
  have e72 := g 18446744073709551544#64 72 rfl (by omega)
  have e64 := g 18446744073709551552#64 64 rfl (by omega)
  have e56 := g 18446744073709551560#64 56 rfl (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have rd : ∀ (b : Word), (top.toNat ≤ b.toNat + 48 → b.toNat < top.toNat → (hdr M top c B).getMem b = M.getMem b) :=
    fun b h1 h2 => by
      simp only [hdr]
      rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        MachineState.getMem_setMem_ne (ne _ _ (by omega))]
  have r0 : (hdr M top c B).getMem (top + 18446744073709551544#64) = c := by
    simp only [hdr]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r8 : (hdr M top c B).getMem (top + 18446744073709551544#64 + 8#64) = B := by
    have : top + 18446744073709551544#64 + 8#64 = top + 18446744073709551552#64 := by rw [BitVec.add_assoc]; rfl
    simp only [hdr]
    rw [this, MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have r16 : (hdr M top c B).getMem (top + 18446744073709551544#64 + 16#64) = 0#64 := by
    have : top + 18446744073709551544#64 + 16#64 = top + 18446744073709551560#64 := by rw [BitVec.add_assoc]; rfl
    simp only [hdr]
    rw [this, MachineState.getMem_setMem_eq]
  have hN : env.next (hdr M top c B) = env.next M := by
    simp only [hdr]
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
  have hcap : vecCap (hdr M top c B) (top + 18446744073709551544#64) = c := by rw [vecCap_eq, r0]
  have hptr : vecPtr (hdr M top c B) (top + 18446744073709551544#64) = B := by rw [vecPtr_eq, r8]
  have hlen : vecLen (hdr M top c B) (top + 18446744073709551544#64) = 0#64 := by rw [vecLen_eq, r16]
  have hw : InWin env (top + 18446744073709551544#64) 24 := .inr ⟨by omega, by omega⟩
  refine ⟨⟨hw, ⟨.inr ⟨by omega, by simp only [Layouts.RawVecInner.byteSize]; omega⟩, by omega, ?_, ?_⟩, ?_⟩,
    by rw [hlen]; rfl, ?_, ?_, ?_, ?_⟩
  · rw [rvCapAt_eq, rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq, hcap, hptr]
    exact hB.imp_right fun ⟨⟨h1, h2⟩, h3⟩ => ⟨by omega, by unfold Env.Live; rw [hN]; omega, h3⟩
  · rw [rvCapAt_eq, ← vecCap_eq, hcap]; omega
  · rw [hlen, hcap]; simp
  · rw [hcap, hptr]; exact hB.imp_right fun ⟨⟨h1, _⟩, _⟩ => h1
  · obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hsl
    have q : ∀ d : Word, ∀ k, d.toNat + k = 2 ^ 64 → 0 < k → k ≤ 48 →
        (hdr M top c B).getMem (top + d) = M.getMem (top + d) := fun d k hc hk0 hk => by
      have e := CloneT.toNat_add_neg (t := top) hc (by omega)
      exact rd _ (by omega) (by omega)
    exact ⟨(q _ 8 rfl (by omega) (by omega)).trans t1, (q _ 16 rfl (by omega) (by omega)).trans t2,
      (q _ 24 rfl (by omega) (by omega)).trans t3, (q _ 32 rfl (by omega) (by omega)).trans t4,
      (q _ 40 rfl (by omega) (by omega)).trans t5, (q _ 48 rfl (by omega) (by omega)).trans t6⟩
  · exact Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot hF (by omega) (by omega)) (by omega) (by omega))
      (by omega) (by omega)
  · exact Env.static_setMem_stack (Env.static_setMem_stack (Env.static_setMem_stack hS (by omega)) (by omega))
      (by omega)

/-- The state at instruction 82, after `alloc`: `x18` the lengths' sum, the block `x10` of that many elements
    allocated since the entry (none when the sum is `0`). -/
def Inv82 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ Saved regs R ∧ R .x11 = regs .x11 ∧
    R .x19 = regs .x12 <<< 4 ∧ (R .x18).toNat = lenSum m (regs .x11) (regs .x12).toNat ∧
    ((R .x18).toNat = 0 ∨ (env.Fresh m M (R .x10) ((R .x18).toNat * 16) ∧ (R .x10).toNat % 8 = 0)) ∧
    Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

/-- The lengths' sum is below `2 ^ 58`. -/
theorem lenSum_lt {env : Env} {m : MachineState} {regs : Reg → Word} (hpre : PreT env regs m)
    (hend : env.heapEnd.toNat ≤ 0x78000000) :
    ∀ k, k ≤ (regs .x12).toNat → lenSum m (regs .x11) k < 2 ^ 58 := by
  obtain ⟨-, -, -, -, -, hwin1, -, hsrc⟩ := hpre
  have hlay := env.layout
  have hn : 16 * (regs .x12).toNat ≤ 0xc0000000 := by unfold InWin at hwin1; omega
  intro k hk
  have hb : ∀ j, j < k → (slen m (regs .x11) j).toNat ≤ 0xc000000 := fun j hj => by
    rcases hsrc j (by omega) with h | ⟨h, -, -⟩
    · omega
    · rw [inWindow_iff] at h; omega
  have := lenSum_le k hb
  have : k * 0xc000000 ≤ 0xc000000 * 0xc000000 := Nat.mul_le_mul_right _ (by omega)
  omega

set_option rv_sym.heap true in
/-- **From instruction 82**: the header built, then the second loop. -/
theorem at82 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 80 + needS ≤ need) (hse : SpecExtendT.SpecT env p L.specExtend.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hpre : PreT env regs m) :
    ∀ R M, Inv82 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 82, ret, top⟩ :: rest, R, M⟩ := by
  have hl2 := loop2 hp hL hnS hse hk hstop hneed hW h16 h2 hpre
  have hlt := lenSum_lt hpre hW.heapEnd_le (regs .x12).toNat le_rfl
  have hW1 := hW.heapEnd_le
  obtain ⟨-, -, -, hn0, -, hwin1, -, -⟩ := hpre
  intro R M hI
  obtain ⟨hR2, hR8, hsv, hR11, hR19, h18, hB, hsl, hF, hS, hc⟩ := hI
  have hlay := env.layout
  have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
  have hn : 16 * (regs .x12).toNat ≤ 0xc0000000 := by unfold InWin at hwin1; omega
  have hw1 := hwin1
  unfold InWin at hw1
  obtain ⟨hV, hlen, hcap, hsl1, hF1, hS1⟩ := hdr_ok (ret := ret) (regs := regs) hlim h16 hW hsl hF hS
    (by omega) hB
  have hc1 : (hdr M top (R .x18) (R .x10)).code = m.code := by simp only [hdr, MachineState.code_setMem]; exact hc
  have h19 : (regs .x11 + regs .x12 <<< 4).toNat = (regs .x11).toNat + 16 * (regs .x12).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  clear hB hsl hF hS hw1
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR11 (And.intro hR19 hsv)))
  rv_introT hR
  rv_symT hp stop [90] with [hL]
  have e0 : (regs .x12).toNat - 1 - ((regs .x12).toNat - 1) = 0 := by omega
  refine hl2 ((regs .x12).toNat - 1) _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by omega, ?_, h19, hV, ?_,
    hcap, hsl1, hF1, hS1, hc1⟩
  · show (regs .x11).toNat = _
    rw [e0]; rfl
  · rw [hlen, e0]; rfl

/-- The state at instruction 32, after the first loop: `x18` the lengths' sum. -/
def Inv32 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ Saved regs R ∧ R .x11 = regs .x11 ∧
    R .x19 = regs .x12 <<< 4 ∧ (R .x18).toNat = lenSum m (regs .x11) (regs .x12).toNat ∧
    Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **From instruction 32**: the size check, `alloc` (none when the sum is `0`), to the join at 82. -/
theorem at32 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needA needH : Nat}
    (hal : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop))
    (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hnA : env.stackLimit.toNat + 80 + needA ≤ top.toNat) (hnH : env.stackLimit.toNat + 80 + needH ≤ top.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hpre : PreT env regs m)
    (h82 : ∀ R M, Inv82 env m top ret regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 82, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv32 env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 32, ret, top⟩ :: rest, R, M⟩ := by
  have hlt := lenSum_lt hpre hW.heapEnd_le (regs .x12).toNat le_rfl
  clear hpre
  intro R M hI
  obtain ⟨hR2, hR8, hsv, hR11, hR19, h18, hsl, hF, hS, hc⟩ := hI
  have hlay := env.layout
  have hsh : (R .x18 <<< 4).toNat = 16 * (R .x18).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR11 (And.intro hR19 hsv)))
  rv_introT hR
  rv_symT hp stop [82] with [hL] using [hal, hhe]
  · have h0 : (R .x18).toNat = 0 := by have := congrArg BitVec.toNat hc; rw [hsh] at this; simp at this; omega
    exact h82 _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp only [Tactic.rf]; simp; omega,
      .inl rfl, hsl, hF, hS, hc_1⟩
  · have e80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 :=
      CloneT.toNat_add_neg (k := 80) rfl (by omega)
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hsl
    have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 48 →
        m1.getMem (top + c) = M.getMem (top + c) := fun c k hc' h0 hk' => by
      have e := CloneT.toNat_add_neg (t := top) hc' (by omega)
      have := hret1_14.2.1
      have := hW.nextAddr_ge
      refine hret1_14.2.2 _ fun hw => ?_
      rcases hw with hw | hw | hw | hw
      · rw [e80, e] at hw; omega
      · rw [e] at hw; omega
      · rw [hw] at e; omega
      · exact hw
    have := hF.1
    rw [hsh] at hret1_18
    exact h82 _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, h18,
      .inr ⟨⟨by simp only [Tactic.rf]; omega, by simp only [Tactic.rf]; omega⟩, by simp only [Tactic.rf]; exact hret1_17⟩,
      ⟨(g _ 8 rfl (by omega) (by omega)).trans t1, (g _ 16 rfl (by omega) (by omega)).trans t2,
        (g _ 24 rfl (by omega) (by omega)).trans t3, (g _ 32 rfl (by omega) (by omega)).trans t4,
        (g _ 40 rfl (by omega) (by omega)).trans t5, (g _ 48 rfl (by omega) (by omega)).trans t6⟩,
      hF.trans hret1_14 (by rw [e80]; omega) (fun b hb => hb.elim), hret1_15, hret1_19.trans hc_1⟩

/-- The first loop's head with `k + 1` slices left: the cursor `x10` at the next slice's length, `x12` past the last
    one's, `x18` the lengths before the cursor. -/
def L1 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x10 ∧ Saved regs R ∧ R .x11 = regs .x11 ∧
    R .x19 = regs .x12 <<< 4 ∧ k < (regs .x12).toNat ∧
    (R .x10).toNat = (regs .x11).toNat + 8 + 16 * ((regs .x12).toNat - 1 - k) ∧
    (R .x12).toNat = (regs .x11).toNat + 8 + 16 * (regs .x12).toNat ∧
    (R .x18).toNat = lenSum m (regs .x11) ((regs .x12).toNat - 1 - k) ∧
    Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **The first loop**, from its head: the lengths summed, then instruction 32. -/
theorem loop1 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hW : Windows env top m) (hlim : env.stackLimit.toNat + 80 ≤ top.toNat)
    (h2 : regs .x2 = top) (hpre : PreT env regs m)
    (h32 : ∀ R M, Inv32 env m top ret regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 32, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, L1 env m top ret regs k R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 24, ret, top⟩ :: rest, R, M⟩ := by
  have hlt := lenSum_lt hpre hW.heapEnd_le
  obtain ⟨-, -, -, hn0, hown1, hwin1, hal1, -⟩ := hpre
  refine Total.loop (I := rvIsa) (L1 env m top ret regs) fun k R M hI ih => ?_
  obtain ⟨hR2, hR8, hsv, hR11, hR19, hkn, h10, h12, h18, hsl, hF, hS, hc⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hnm := hF.1
  have hnM := hF.2.1
  have kM := SpecExtendT.keep_of_frame hF (by omega)
  have hw1 := hwin1
  unfold InWin at hw1
  have ha1 : (regs .x11).toNat + 16 * (regs .x12).toNat ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x11).toNat := by
    rw [← h2]; exact hown1.1
  have e10 : R .x10 = regs .x11 + BitVec.ofNat 64 (16 * ((regs .x12).toNat - 1 - k) + 8) :=
    BitVec.eq_of_toNat_eq (by rw [h10, toNat_add_ofNat (by omega)]; omega)
  have hsum : (m.getMem (R .x10) + R .x18).toNat = lenSum m (regs .x11) ((regs .x12).toNat - 1 - k + 1) := by
    have := hlt ((regs .x12).toNat - 1 - k + 1) (by omega)
    simp only [lenSum, slen] at this ⊢
    rw [BitVec.toNat_add, e10, h18]
    omega
  clear e10
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR11 (And.intro hR19 hsv)))
  rv_introT hR
  have x16 : (R .x10 + 16#64).toNat = (R .x10).toNat + 16 := toNat_add_ofNat (by omega)
  rv_symT hp stop [24, 32] with [_hL]
  · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [x16, h10, h12]; subst h0; omega))
    clear hc
    have e : (regs .x12).toNat - 1 - k + 1 = (regs .x12).toNat - 1 - (k - 1) := by omega
    rw [e] at hsum
    exact ih (k - 1) _ _ (by omega) ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by omega,
      by simp only [Tactic.rf]; rw [x16, h10]; omega, h12, hsum, hsl, hF, hS, hc_1⟩
  · have hk0 : k = 0 := by
      have := congrArg BitVec.toNat hc; rw [x16, h10, h12] at this; omega
    clear hc
    subst hk0
    have e : (regs .x12).toNat - 1 - 0 + 1 = (regs .x12).toNat := by omega
    rw [e] at hsum
    exact h32 _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hsum, hsl, hF, hS, hc_1⟩

/-- The prologue's six saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  (((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)

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
  refine ⟨?_, ?_, ?_, by simp only [saved, MachineState.code_setMem]⟩
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6] at h'; omega)])
  · simp only [saved]
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Env.Frame.refl hnx)
  · simp only [saved]
    repeat (first | refine Env.static_setMem_stack ?_ (by omega) | exact hS)

set_option rv_sym.heap true in
/-- **`<[&[E]] as Concat<E>>::concat` is total**, with 80 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needS needH : Nat} (hnA : 80 + needA ≤ need) (hnS : 80 + needS ≤ need) (hnH : 80 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hse : SpecExtendT.SpecT env p L.specExtend.idx needS)
    (hhe : Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal', hhe, hse]
  have hlay := env.layout
  have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
  have hpre : PreT env regs m :=
    ⟨⟨hpre_6, hpre_7⟩, hpre_8, hpre_9, hpre_10, ⟨hpre_11, hpre_12⟩, hpre_13, hpre_14, hpre_15⟩
  have h82 := at82 hp hL hnS hse hk hstop hpre_3 hpre_17 hpre_16 hpre_2 hpre
  have h32 := at32 hp hL hal' hhe hstop (by omega) (by omega) hpre_17 hpre_16 hpre h82
  obtain ⟨hsl0, hF0, hS0, hc0⟩ := saved_ok (ret := ret) (regs := regs) hlim hpre_5 hpre_4
  simp only [saved] at hsl0 hF0 hS0 hc0
  have hW1 := hpre_17.heapEnd_le
  have e0 : (regs .x12).toNat - 1 - ((regs .x12).toNat - 1) = 0 := by omega
  refine loop1 hp hL hpre_17 hlim hpre_2 hpre h32 ((regs .x12).toNat - 1) _ _
    ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by omega, ?_, ?_, ?_, hsl0, hF0, hS0, hc0⟩
  · show (regs .x11 + 8#64).toNat = _
    rw [toNat_add_ofNat (by omega), e0]
  · show (regs .x11 + 8#64 + regs .x12 <<< 4).toNat = _
    rw [BitVec.toNat_add, toNat_add_ofNat (by omega), BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  · show (0#64).toNat = _
    rw [e0]; rfl

end Rv64mc.Proof.Runtime.ConcatSliceET

/-- info: 'Rv64mc.Proof.Runtime.ConcatSliceET.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.ConcatSliceET.total
