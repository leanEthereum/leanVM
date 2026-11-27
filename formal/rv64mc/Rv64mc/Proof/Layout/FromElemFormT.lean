/-
  Rv64mc.Proof.Layout.FromElemFormT

  `<Form as SpecFromElem>::from_elem` (`vec![form; 3]`, the count `3` folded into the code; `sret` in `a0`, the
  element `Form`'s header at `a1`) is total for an empty element: it allocates three `Form` headers (`alloc(72)`),
  builds the vector's header in its frame and calls `Vec::reserve` for `3` (which keeps it: the capacity is `3`),
  checks the element's length against `isize::MAX / 40` (a word of the static data), clones the element twice
  (no terms: each clone is the empty `Form`, `(0, 8, 0)`), moves the element into the third slot and copies the
  header to `sret`. Its result is a vector of three `Form`s (`FormReprT.FormsT`), its buffer fresh, the first two
  of capacity `0` and the third of the element's (so all three empty at the one call site); the run ends with
  the guest's abort (`AbortStop`) where `alloc` or `handle_error` does. A safety-only contract (the function is
  class D: no spec).

  The precondition asks the element empty (`vecLen = 0`): the image's one call site (`verify_bus_balance`, template
  label 421) passes the `Form` it built at `sp + 0x3d0` as `(0, 8, 0)` just before (labels 415 to 417). With it the
  two term loops (labels 69 and 114) are never entered: the branch at label 47 (`40 len = 0`) goes straight to the
  join (label 143), and the path into them is refuted (`tail`'s second case).

  The body is cut at `reserve`'s return (instruction 56, `tail`), the join (286, `fin`) and the epilogue (316,
  `exit`). `fin_mem` gives the frame and the postcondition after the last nine stores.

  ## Main definitions

  * `PreT`, `PostT`, `SpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.CloneFormsT
import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.FromElemT
import Rv64mc.Proof.Multilinear.SelectorPoint
import Rv64mc.Gen.Tmpl.Alloc.Vec.SpecFromElem.Form.AsSpecFromElem.FromElemGlobal

namespace Rv64mc.Proof.Layout.FromElemFormT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Layout.FormReprT
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Gen.Alloc.Vec.SpecFromElem.Form.AsSpecFromElem.FromElemGlobal (Link tmpl d_c8_51ab739d_words)

/-- The total precondition: the result's slot a caller's (`SretPre`), in a window and 8-byte aligned; the element
    (`a1`) an empty `Form` its caller owns. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
    env.Owned m (regs .x2) (regs .x11) 24 ∧ VecT env m (regs .x11) 40 ∧ vecLen m (regs .x11) = 0#64

/-- The total postcondition: the result a vector of three `Form`s, its buffer fresh, the first two of capacity `0`
    and the third of the element's. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 24 ∧ vecLen m' (regs .x10) = 3#64 ∧
    env.Fresh m m' (vecPtr m' (regs .x10)) 72 ∧ FormsT env m' (vecPtr m' (regs .x10)) 3 ∧
    vecCap m' (vecPtr m' (regs .x10)) = 0#64 ∧ vecCap m' (vecPtr m' (regs .x10) + 24#64) = 0#64 ∧
    vecCap m' (vecPtr m' (regs .x10) + 48#64) = vecCap m (regs .x11)

/-- **The total contract of `<Form as SpecFromElem>::from_elem`** for `vec![form; 3]`. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) SretVecOut AbortStop


/-- The header in the frame at `top - 168`: capacity `3`, pointer `q`, length `0`. -/
def hdr (N : MachineState) (top q : Word) : MachineState :=
  ((N.setMem (top + 18446744073709551448#64) 3#64).setMem (top + 18446744073709551456#64) q).setMem
    (top + 18446744073709551464#64) 0#64

/-- The registers at `reserve`'s return the rest reads. -/
def TRegs (top : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x9 = regs .x11 ∧ R .x24 = regs .x10

/-- The six stores of the second and third `Form`s' headers, from `q + 24`, over `M`. -/
def heap6 (M : MachineState) (q e0 e1 e2 : Word) : MachineState :=
  (((((M.setMem (q + 24#64) 0#64).setMem (q + 32#64) 8#64).setMem (q + 40#64) 0#64).setMem (q + 48#64) e0).setMem
    (q + 56#64) e1).setMem (q + 64#64) e2

/-- **The last stores**: the second `Form`'s header (empty) and the third's (`e0`, `e1`, `e2`, the element's
    words) after the first's at `q`, then the result's header `(c, P, 3)` at `sret`: `MemOk` and the
    postcondition. -/
theorem fin_mem {env : Env} {m M : MachineState} {top ret q c P e0 e1 e2 : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hW : Windows env top m) (hpre : PreT env regs m)
    (h2 : regs .x2 = top) (hM : CloneFormsT.MemOk env m top ret regs Tactic.F M)
    (hq1 : (env.next m).toNat ≤ q.toNat) (hq2 : q.toNat + 72 ≤ (env.next M).toNat) (hq8 : q.toNat % 8 = 0)
    (f0 : M.getMem q = 0#64) (f8 : M.getMem (q + 8#64) = 8#64) (f16 : M.getMem (q + 16#64) = 0#64)
    (hc : c = 3#64) (hP : P = q) (he0 : e0 = m.getMem (regs .x11)) (he1 : e1 = m.getMem (regs .x11 + 8#64))
    (he2 : e2 = m.getMem (regs .x11 + 16#64)) :
    CloneFormsT.MemOk env m top ret regs (SretVecOut regs m)
        ((((heap6 M q e0 e1 e2).setMem (regs .x10) c).setMem (regs .x10 + 8#64) P).setMem (regs .x10 + 16#64) 3#64) ∧
      ∀ r, PostT env regs m r
        ((((heap6 M q e0 e1 e2).setMem (regs .x10) c).setMem (regs .x10 + 8#64) P).setMem (regs .x10 + 16#64)
          3#64) := by
  subst c P
  obtain ⟨hown0, hwin, hal, -, hv, hlen⟩ := hpre
  have hown : env.Owned m top (regs .x10) 24 := by rw [← h2]; exact hown0
  have hlay := env.layout
  have hge := hW.next_ge
  have hW1 := hW.heapEnd_le
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have hlt : q.toNat + 72 < 2 ^ 64 := by omega
  have e : ∀ k : Nat, k ≤ 72 → (q + BitVec.ofNat 64 k).toNat = q.toNat + k := fun k hk => toNat_add_ofNat (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have e8 := e 8 (by omega)
  have e16 := e 16 (by omega)
  have e24 := e 24 (by omega)
  have e32 := e 32 (by omega)
  have e40 := e 40 (by omega)
  have e48 := e 48 (by omega)
  have e56 := e 56 (by omega)
  have e64 := e 64 (by omega)
  obtain ⟨m1, n1, k1⟩ := CloneFormsT.heap_store (a := q + 24#64) (v := 0#64) (by omega) hM (by omega) (by omega)
  obtain ⟨m2, n2, k2⟩ := CloneFormsT.heap_store (a := q + 32#64) (v := 8#64) (by omega) m1 (by omega)
    (by rw [n1]; omega)
  obtain ⟨m3, n3, k3⟩ := CloneFormsT.heap_store (a := q + 40#64) (v := 0#64) (by omega) m2 (by omega)
    (by rw [n2, n1]; omega)
  obtain ⟨m4, n4, k4⟩ := CloneFormsT.heap_store (a := q + 48#64) (v := e0) (by omega) m3 (by omega)
    (by rw [n3, n2, n1]; omega)
  obtain ⟨m5, n5, k5⟩ := CloneFormsT.heap_store (a := q + 56#64) (v := e1) (by omega) m4 (by omega)
    (by rw [n4, n3, n2, n1]; omega)
  obtain ⟨m6, n6, k6⟩ := CloneFormsT.heap_store (a := q + 64#64) (v := e2) (by omega) m5 (by omega)
    (by rw [n5, n4, n3, n2, n1]; omega)
  have hN6 : env.next (heap6 M q e0 e1 e2) = env.next M := by rw [heap6, n6, n5, n4, n3, n2, n1]
  have hM6 : CloneFormsT.MemOk env m top ret regs (SretVecOut regs m) (heap6 M q e0 e1 e2) := by
    obtain ⟨a1, a2, a3, a4⟩ := m6
    exact ⟨a1, Tactic.frame_weaken a2, a3, a4⟩
  obtain ⟨hM9, hn9, r0, r8, r16, rk⟩ := CloneFormsT.hdr3 (v0 := 3#64) (v1 := q) (v2 := 3#64) (by omega) hown hwin hM6
  refine ⟨hM9, fun r => ?_⟩
  have hsep : ∀ b : Word, q.toNat ≤ b.toNat → b.toNat < q.toNat + 72 →
      b.toNat < (regs .x10).toNat ∨ (regs .x10).toNat + 24 ≤ b.toNat := fun b h1 h2 => by
    have := hown.2; rcases hown.1 with h | h <;> omega
  have kq : ∀ b : Word, (b.toNat < q.toNat + 24 ∨ q.toNat + 72 ≤ b.toNat) →
      (heap6 M q e0 e1 e2).getMem b = M.getMem b := fun b hb => by
    simp only [heap6]
    rw [k6 b (ne _ _ (by omega)), k5 b (ne _ _ (by omega)), k4 b (ne _ _ (by omega)), k3 b (ne _ _ (by omega)),
      k2 b (ne _ _ (by omega)), k1 b (ne _ _ (by omega))]
  have g : ∀ b : Word, ∀ k, k + 8 ≤ 72 → b = q + BitVec.ofNat 64 k →
      ((((heap6 M q e0 e1 e2).setMem (regs .x10) 3#64).setMem (regs .x10 + 8#64) q).setMem (regs .x10 + 16#64)
        3#64).getMem b = (heap6 M q e0 e1 e2).getMem b := fun b k hk hb => by
    have := e k (by omega); rw [← hb] at this; exact rk b (hsep b (by omega) (by omega))
  have h6 : ∀ k v, k ≤ 64 → 24 ≤ k → (heap6 M q e0 e1 e2).getMem (q + BitVec.ofNat 64 k) = v →
      ((((heap6 M q e0 e1 e2).setMem (regs .x10) 3#64).setMem (regs .x10 + 8#64) q).setMem (regs .x10 + 16#64)
        3#64).getMem (q + BitVec.ofNat 64 k) = v := fun k v hk hk' h => by rw [g _ k (by omega) rfl, h]
  have hq0 : q + BitVec.ofNat 64 0 = q := BitVec.eq_of_toNat_eq (by rw [e 0 (by omega)]; omega)
  have r0' : ((((heap6 M q e0 e1 e2).setMem (regs .x10) 3#64).setMem (regs .x10 + 8#64) q).setMem (regs .x10 + 16#64)
      3#64).getMem q = 0#64 := by
    rw [g q 0 (by omega) hq0.symm, kq q (by omega), f0]
  have r8' := g (q + 8#64) 8 (by omega) rfl
  have r16' := g (q + 16#64) 16 (by omega) rfl
  rw [kq _ (by omega), f8] at r8'
  rw [kq _ (by omega), f16] at r16'
  have w24 : (heap6 M q e0 e1 e2).getMem (q + 24#64) = 0#64 := by
    simp only [heap6]
    rw [k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), k3 _ (ne _ _ (by omega)),
      k2 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have w32 : (heap6 M q e0 e1 e2).getMem (q + 32#64) = 8#64 := by
    simp only [heap6]
    rw [k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), k3 _ (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have w40 : (heap6 M q e0 e1 e2).getMem (q + 40#64) = 0#64 := by
    simp only [heap6]
    rw [k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have w48 : (heap6 M q e0 e1 e2).getMem (q + 48#64) = e0 := by
    simp only [heap6]
    rw [k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have w56 : (heap6 M q e0 e1 e2).getMem (q + 56#64) = e1 := by
    simp only [heap6]
    rw [k6 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have w64 : (heap6 M q e0 e1 e2).getMem (q + 64#64) = e2 := by
    simp only [heap6]; exact MachineState.getMem_setMem_eq
  have a24 : ∀ k : Word, q + 24#64 + k = q + (24#64 + k) := fun k => BitVec.add_assoc ..
  have a48 : ∀ k : Word, q + 48#64 + k = q + (48#64 + k) := fun k => BitVec.add_assoc ..
  have hN9 : env.next ((((heap6 M q e0 e1 e2).setMem (regs .x10) 3#64).setMem (regs .x10 + 8#64) q).setMem
      (regs .x10 + 16#64) 3#64) = env.next M := by rw [hn9, hN6]
  have hwq : ∀ k, k + 24 ≤ 72 → InWin env (q + BitVec.ofNat 64 k) 24 := fun k hk => .inl ⟨by rw [e k (by omega)]; omega,
    by rw [e k (by omega)]; omega⟩
  have F0 : FormT env ((((heap6 M q e0 e1 e2).setMem (regs .x10) 3#64).setMem (regs .x10 + 8#64) q).setMem
      (regs .x10 + 16#64) 3#64) q :=
    CloneFormsT.new_form (c := 0#64) (P := 8#64) (L := 0#64) (hq0 ▸ hwq 0 (by omega)) hq8 r0' r8' r16'
      (by decide) (.inl ⟨rfl, rfl⟩)
  have F1 : FormT env ((((heap6 M q e0 e1 e2).setMem (regs .x10) 3#64).setMem (regs .x10 + 8#64) q).setMem
      (regs .x10 + 16#64) 3#64) (q + 24#64) := by
    refine CloneFormsT.new_form (c := 0#64) (P := 8#64) (L := 0#64) (hwq 24 (by omega)) (by rw [e24]; omega)
      (h6 24 _ (by omega) (by omega) w24)
      ?_ ?_ (by decide) (.inl ⟨rfl, rfl⟩)
    · rw [a24]; exact h6 32 _ (by omega) (by omega) w32
    · rw [a24]; exact h6 40 _ (by omega) (by omega) w40
  have F2 : FormT env ((((heap6 M q e0 e1 e2).setMem (regs .x10) 3#64).setMem (regs .x10 + 8#64) q).setMem
      (regs .x10 + 16#64) 3#64) (q + 48#64) := by
    have h48 := h6 48 _ (by omega) (by omega) w48
    have h56 := h6 56 _ (by omega) (by omega) w56
    have h64 := h6 64 _ (by omega) (by omega) w64
    refine ⟨CloneFormsT.vecT_copy hv (hwq 48 (by omega)) (by rw [e48]; omega) (by rw [hN9]; have := hM.2.1.1; omega)
      (by rw [h48, he0]) (by rw [a48]; exact h56.trans he1) (by rw [a48]; exact h64.trans he2), ?_⟩
    intro t ht
    rw [vecLen_eq, a48] at ht
    have : (48#64 + 16#64 : Word) = 64#64 := rfl
    rw [this, h64, he2, ← vecLen_eq, hlen] at ht
    exact absurd ht (Nat.not_lt_zero _)
  refine ⟨?_, by rw [vecLen_eq, r16], ⟨?_, ?_⟩, ?_, ?_⟩
  · refine ⟨hwin, ⟨Runtime.MemsetT.InWin.sub hwin (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega),
      hal, ?_, ?_⟩, ?_⟩
    · rw [rvCapAt_eq, rvPtrAt_eq, r0, r8]
      have := congrArg BitVec.toNat hN9
      exact .inr ⟨by omega, by unfold Env.Live; simp only [BitVec.toNat_ofNat]; omega, hq8⟩
    · rw [rvCapAt_eq, r0]; decide
    · rw [vecLen_eq, vecCap_eq, r0, r16]
  · rw [vecPtr_eq, r8]; exact hq1
  · have := congrArg BitVec.toNat hN9
    rw [vecPtr_eq, r8]; omega
  · rw [vecPtr_eq, r8]
    intro j hj
    rcases j with _ | _ | _ | j
    · rw [hq0]; exact F0
    · exact F1
    · exact F2
    · omega
  · rw [vecPtr_eq, r8, vecCap_eq, vecCap_eq, vecCap_eq, vecCap_eq]
    exact ⟨r0', h6 24 _ (by omega) (by omega) w24, (h6 48 _ (by omega) (by omega) w48).trans he0⟩

/-- The registers at the join (instruction 286). -/
def XRegs (top q : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x9 = regs .x11 ∧ R .x10 = 0#64 ∧ R .x19 = 8#64 ∧ R .x21 = 0#64 ∧
    R .x23 = q ∧ R .x24 = regs .x10 ∧ R .x26 = 0#64

set_option rv_sym.heap true in
/-- **The return**, from instruction 316: the saved registers reloaded. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (R : Reg → Word) (M : MachineState) (hR : R .x2 = top + 18446744073709551424#64)
    (hM : CloneFormsT.MemOk env m top ret regs (SretVecOut regs m) M) (hPost : ∀ r, PostT env regs m r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 316, ret, top⟩ :: rest, R, M⟩ := by
  obtain ⟨⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13⟩, hF, hS, hc⟩ := hM
  rv_introT hR
  rv_symT hp with [_hL]
  exact ⟨⟨rfl, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13⟩, hF, hS, hPost _⟩

set_option rv_sym.heap true in
/-- **The join** (instruction 286, the first `Form`'s header stored at `q`): the other two headers, the result's,
    the return. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hpre : PreT env regs m) (h2 : regs .x2 = top)
    (R : Reg → Word) (M : MachineState) (q : Word) (hR : XRegs top q regs R)
    (hM : CloneFormsT.MemOk env m top ret regs Tactic.F M)
    (s168 : M.getMem (top + 18446744073709551448#64) = 3#64) (s160 : M.getMem (top + 18446744073709551456#64) = q)
    (hq1 : (env.next m).toNat ≤ q.toNat) (hq2 : q.toNat + 72 ≤ (env.next M).toNat) (hq8 : q.toNat % 8 = 0)
    (f0 : M.getMem q = 0#64) (f8 : M.getMem (q + 8#64) = 8#64) (f16 : M.getMem (q + 16#64) = 0#64)
    (he : ∀ b : Word, (regs .x11).toNat ≤ b.toNat → b.toNat < (regs .x11).toNat + 24 → M.getMem b = m.getMem b) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 286, ret, top⟩ :: rest, R, M⟩ := by
  obtain ⟨hMf, hPost⟩ := fin_mem (c := M.getMem (top + 18446744073709551448#64))
    (P := M.getMem (top + 18446744073709551456#64)) (e0 := m.getMem (regs .x11))
    (e1 := m.getMem (regs .x11 + 8#64)) (e2 := m.getMem (regs .x11 + 16#64)) hlim hW hpre h2 hM hq1 hq2 hq8 f0 f8 f16
    s168 s160 rfl rfl rfl
  simp only [heap6] at hMf hPost
  obtain ⟨hsl, hF, hS, hc⟩ := hMf
  have hcM : M.code = m.code := hM.2.2.2
  obtain ⟨hown, hwin, hal, -, hv, -⟩ := hpre
  have h24 : (regs .x10).toNat + 24 < 2 ^ 64 := hown.2
  have hW1 := hW.heapEnd_le
  have hW2 := hW.top_le
  have hlay := env.layout
  have hW3 := hW.nextAddr_ge
  have w0 : inWindow (regs .x10) 8 = true := (hwin.dword (x := regs .x10) (o := 0) hW hal rfl (by omega) rfl).1
  have w8 := hwin.dword_add (x := regs .x10) (o := 0) (k := 8) hW hal rfl (by omega) rfl
  have w16 := hwin.dword_add (x := regs .x10) (o := 0) (k := 16) hW hal rfl (by omega) rfl
  have hex := exit hp hL hk hlim hW h16
  rv_introT hR
  rv_symT hp stop [316] with [hL]
  exact hex _ _ rfl ⟨hsl, hF, hS, hc⟩ hPost

/-- **The frame at `reserve`'s return**: the words at and above the stack pointer are the header's over the saved
    registers, which gives `MemOk` and the header's capacity and pointer. -/
theorem memOk_of {env : Env} {m M : MachineState} {top ret q : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hSm : env.Static m)
    (hK : ∀ a, top + 18446744073709551424#64 ≤ a → M.getMem a = (hdr (CloneFormsT.saved m top ret regs) top q).getMem a)
    (hF : env.Frame top Tactic.F m M) (hS : env.Static M) (hcode : M.code = m.code) :
    CloneFormsT.MemOk env m top ret regs Tactic.F M ∧ M.getMem (top + 18446744073709551448#64) = 3#64 ∧
      M.getMem (top + 18446744073709551456#64) = q := by
  have hlay := env.layout
  have e : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 192 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => CloneFormsT.es hc (by omega)
  have e192 := e 18446744073709551424#64 192 rfl (by omega)
  have e168 := e 18446744073709551448#64 168 rfl (by omega)
  have e160 := e 18446744073709551456#64 160 rfl (by omega)
  have e152 := e 18446744073709551464#64 152 rfl (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hK2 : ∀ a : Word, top.toNat - 192 ≤ a.toNat →
      M.getMem a = (hdr (CloneFormsT.saved m top ret regs) top q).getMem a :=
    fun a ha => hK a (by rw [BitVec.le_def, e192]; exact ha)
  have hsl := (CloneFormsT.saved_ok (top := top) (ret := ret) (regs := regs) (by omega) hnx hSm).1
  refine ⟨⟨CloneFormsT.slots_keep (top := top) (X := M) (by omega) (fun a h1 h2 => ?_) hsl, hF, hS, hcode⟩, ?_, ?_⟩
  · rw [hK2 a (by omega), hdr, MachineState.getMem_setMem_ne (ne a (top + 18446744073709551464#64) (by omega)),
      MachineState.getMem_setMem_ne (ne a (top + 18446744073709551456#64) (by omega)),
      MachineState.getMem_setMem_ne (ne a (top + 18446744073709551448#64) (by omega))]
  · rw [hK2 (top + 18446744073709551448#64) (by omega), hdr,
      MachineState.getMem_setMem_ne (ne (top + 18446744073709551448#64) (top + 18446744073709551464#64) (by omega)),
      MachineState.getMem_setMem_ne (ne (top + 18446744073709551448#64) (top + 18446744073709551456#64) (by omega)),
      MachineState.getMem_setMem_eq]
  · rw [hK2 (top + 18446744073709551456#64) (by omega), hdr,
      MachineState.getMem_setMem_ne (ne (top + 18446744073709551456#64) (top + 18446744073709551464#64) (by omega)),
      MachineState.getMem_setMem_eq]

set_option rv_sym.heap true in
/-- **From `reserve`'s return** (instruction 56): the length check, then the join; a nonzero length is refuted. -/
theorem tail {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) (hd : DataRef.InData env [(L.d_c8_51ab739d, d_c8_51ab739d_words)])
    {need needH : Nat} (hnH : 192 + needH ≤ need) (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hpre : PreT env regs m) (h2 : regs .x2 = top)
    (R : Reg → Word) (M : MachineState) (q : Word) (hR : TRegs top regs R)
    (hK : ∀ a, top + 18446744073709551424#64 ≤ a → M.getMem a = (hdr (CloneFormsT.saved m top ret regs) top q).getMem a)
    (hF : env.Frame top Tactic.F m M) (hS : env.Static M) (hcode : M.code = m.code) (hSm : env.Static m)
    (hq1 : (env.next m).toNat ≤ q.toNat) (hq2 : q.toNat + 72 ≤ (env.next M).toNat) (hq8 : q.toNat % 8 = 0)
    (he : ∀ b : Word, (regs .x11).toNat ≤ b.toNat → b.toNat < (regs .x11).toNat + 24 → M.getMem b = m.getMem b) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 56, ret, top⟩ :: rest, R, M⟩ := by
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  obtain ⟨hM, s168, s160⟩ := memOk_of hlim (hF.1.trans hF.2.1) hSm hK hF hS hcode
  have hfin := fin hp hL hk hlim hW h16 hpre h2
  simp only [hdr, CloneFormsT.saved] at hK
  obtain ⟨hown, hwin, hal, hown1, hv, hlen⟩ := hpre
  have hw1 := hd.words (List.mem_singleton_self _)
  have hdw := Runtime.FromElemT.data0 hW hd (by decide)
  have h0 : m.getMem (regs .x11 + 16#64) = 0#64 := by rw [← vecLen_eq]; exact hlen
  rv_introT hR
  rv_symT hp stop [96] with [hL, hw1, h0] using [hhe]
  all_goals try exact hdw.1
  · -- the first `Form`'s header stored at `q`: to the join
    have hlay := env.layout
    have hnM := hF.2.1
    have h24 : (regs .x11).toNat + 24 < 2 ^ 64 := hown1.2
    have hq24 : q.toNat + 24 < 2 ^ 64 := by omega
    have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
    have e8 : (q + 8#64).toNat = q.toNat + 8 := toNat_add_ofNat (by omega)
    have e16 : (q + 16#64).toNat = q.toNat + 16 := toNat_add_ofNat (by omega)
    obtain ⟨m1, n1, k1⟩ := CloneFormsT.heap_store (a := q) (v := 0#64) (by omega) hM (by omega) (by omega)
    obtain ⟨m2, n2, k2⟩ := CloneFormsT.heap_store (a := q + 8#64) (v := 8#64) (by omega) m1 (by omega)
      (by rw [n1]; omega)
    obtain ⟨m3, n3, k3⟩ := CloneFormsT.heap_store (a := q + 16#64) (v := m.getMem (regs .x11 + 16#64)) (by omega) m2
      (by omega) (by rw [n2, n1]; omega)
    have hk3 : ∀ b : Word, (b.toNat < q.toNat ∨ q.toNat + 24 ≤ b.toNat) →
        (((M.setMem q 0#64).setMem (q + 8#64) 8#64).setMem (q + 16#64) (m.getMem (regs .x11 + 16#64))).getMem b =
          M.getMem b := fun b hb => by
      rw [k3 b (ne _ _ (by omega)), k2 b (ne _ _ (by omega)), k1 b (ne _ _ (by omega))]
    have hsep : ∀ b : Word, (regs .x11).toNat ≤ b.toNat → b.toNat < (regs .x11).toNat + 24 →
        b.toNat < q.toNat ∨ q.toNat + 24 ≤ b.toNat := fun b hb1 hb2 => by
      have := hown1.1; rw [h2] at this; rcases this with h | h <;> omega
    refine hfin _ _ q ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩ m3 ?_ ?_ hq1 (by rw [n3, n2, n1]; exact hq2) hq8 ?_ ?_ ?_
      fun b h1 h2 => (hk3 b (hsep b h1 h2)).trans (he b h1 h2)
    · show m.getMem (regs .x11 + 16#64) = 0#64
      exact h0
    · rw [hk3 _ (by rw [CloneFormsT.es (k := 168) rfl (by omega)]; omega)]; exact s168
    · rw [hk3 _ (by rw [CloneFormsT.es (k := 160) rfl (by omega)]; omega)]; exact s160
    · rw [k3 _ (ne _ _ (by omega)), k2 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
    · rw [k3 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
    · rw [MachineState.getMem_setMem_eq, h0]
  · -- a nonzero length: not reached
    exact absurd (by rw [h0]; rfl) hc

/-- **The header's words after `reserve`**, at and above the stack pointer: what the code stored over `N`, which
    agrees there with `N0`, where `reserve` (`out` the header's capacity and pointer) kept the capacity and pointer. -/
theorem hdr_kept {N N0 m1 m' : MachineState} {top q : Word} {R : Reg → Word}
    (hR : R .x10 = top + 18446744073709551448#64)
    (hN : ∀ a, top + 18446744073709551424#64 ≤ a → N.getMem a = N0.getMem a)
    (k1 : ∀ a, top + 18446744073709551424#64 ≤ a → ¬ GrowOut R m' a → m1.getMem a = (hdr N top q).getMem a)
    (hc : vecCap m1 (top + 18446744073709551448#64) = vecCap (hdr N top q) (top + 18446744073709551448#64))
    (hq : vecPtr m1 (top + 18446744073709551448#64) = vecPtr (hdr N top q) (top + 18446744073709551448#64)) :
    ∀ a, top + 18446744073709551424#64 ≤ a → m1.getMem a = (hdr N0 top q).getMem a := by
  have a8 : top + 18446744073709551448#64 + BitVec.ofNat 64 8 = top + 18446744073709551456#64 := by
    rw [BitVec.add_assoc]; rfl
  have n1 : top + 18446744073709551456#64 ≠ top + 18446744073709551448#64 := Tactic.add_ne_add (by decide)
  have n2 : top + 18446744073709551464#64 ≠ top + 18446744073709551448#64 := Tactic.add_ne_add (by decide)
  have n3 : top + 18446744073709551464#64 ≠ top + 18446744073709551456#64 := Tactic.add_ne_add (by decide)
  have r : ∀ X : MachineState, (hdr X top q).getMem (top + 18446744073709551448#64) = 3#64 ∧
      (hdr X top q).getMem (top + 18446744073709551456#64) = q := fun X => by
    simp only [hdr]
    exact ⟨by rw [MachineState.getMem_setMem_ne n2.symm, MachineState.getMem_setMem_ne n1.symm,
      MachineState.getMem_setMem_eq], by rw [MachineState.getMem_setMem_ne n3.symm, MachineState.getMem_setMem_eq]⟩
  simp only [vecCap, vecPtr, Layouts.Vec.cap, Layouts.Vec.ptr, BitVec.add_zero, a8] at hc hq
  intro a ha
  by_cases e1 : a = top + 18446744073709551448#64
  · subst e1; rw [hc]; exact (r N).1.trans (r N0).1.symm
  by_cases e2 : a = top + 18446744073709551456#64
  · subst e2; rw [hq]; exact (r N).2.trans (r N0).2.symm
  rw [k1 a ha (by
    simp only [GrowOut, rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero, hR, a8]
    exact fun h => h.elim e1 e2)]
  simp only [hdr]
  by_cases e3 : a = top + 18446744073709551464#64
  · subst e3; rw [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne e3, MachineState.getMem_setMem_ne e2, MachineState.getMem_setMem_ne e1,
      MachineState.getMem_setMem_ne e3, MachineState.getMem_setMem_ne e2, MachineState.getMem_setMem_ne e1, hN a ha]

/-- The header the code stored has room for its three `Form`s past its length `0`. -/
theorem hdr_spare (N : MachineState) (top q : Word) :
    (3#64 : Word).toNat ≤ (vecCap (hdr N top q) (top + 18446744073709551448#64)).toNat -
      (vecLen (hdr N top q) (top + 18446744073709551448#64)).toNat := by
  have a16 : top + 18446744073709551448#64 + 16#64 = top + 18446744073709551464#64 := by rw [BitVec.add_assoc]; rfl
  have n2 : top + 18446744073709551464#64 ≠ top + 18446744073709551448#64 := Tactic.add_ne_add (by decide)
  have n1 : top + 18446744073709551456#64 ≠ top + 18446744073709551448#64 := Tactic.add_ne_add (by decide)
  rw [vecCap_eq, vecLen_eq, a16]
  simp only [hdr]
  rw [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne n2.symm, MachineState.getMem_setMem_ne n1.symm,
    MachineState.getMem_setMem_eq]
  decide

set_option rv_sym.heap true in
/-- **`<Form as SpecFromElem>::from_elem` is total** for an empty element, with 192 bytes of stack beyond its
    callees', given its bound's word in the static data. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hd : DataRef.InData env [(L.d_c8_51ab739d, d_c8_51ab739d_words)])
    {need needA needR needH : Nat} (hnA : 192 + needA ≤ need) (hnR : 192 + needR ≤ need)
    (hnH : 192 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hres : Runtime.ReserveT.ReserveSpecT env 8 24 p L.reserve.idx needR)
    (hhe : Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hw1 := hd.words (List.mem_singleton_self _)
  rv_autoT hp stop [56] with [hL, hw1] using [hal', hres, hhe]
  all_goals try (simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero,
    Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rv_closeT)
  have hlay := env.layout
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  obtain ⟨hsl0, hF0, -, -⟩ := CloneFormsT.saved_ok (top := top) (ret := ret) (regs := regs) (by omega) hpre_5 hpre_4
  have e : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 192 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => CloneFormsT.es hc (by omega)
  have e192 := e 18446744073709551424#64 192 rfl (by omega)
  have e168 := e 18446744073709551448#64 168 rfl (by omega)
  have e160 := e 18446744073709551456#64 160 rfl (by omega)
  have e152 := e 18446744073709551464#64 152 rfl (by omega)
  have hgo : ∀ {R : Reg → Word} {M : MachineState} {b : Word}, R .x10 = top + 18446744073709551448#64 →
      GrowOut R M b → env.stackLimit.toNat ≤ b.toNat ∧ b.toNat < top.toNat := fun hx hb => by
    have := Multilinear.SelectorPoint.grow_in hx (by omega) hb; unfold InRange at this; omega
  have hF3 : env.Frame top Tactic.F m m3 :=
    Multilinear.frame_call_own (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
      (Tactic.frame_call hF0 hret1_14 (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega)
      (by omega)) hret3_14 (by omega) fun b hb => hgo rfl hb
  have hn3 := hret3_14.1
  rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)] at hn3
  have hown1 : env.Owned m top (regs .x11) 24 := by rw [← hpre_2]; exact ⟨hpre_10, hpre_11⟩
  refine tail hp hL hd hnH hhe hk hstop hpre_3 hpre_20 hpre_19
    ⟨⟨hpre_6, hpre_7⟩, hpre_8, hpre_9, ⟨hpre_10, hpre_11⟩, ⟨hpre_12, ⟨hpre_13, hpre_14, hpre_15, hpre_16⟩, hpre_17⟩,
      hpre_18⟩ hpre_2 _ _ (r1 .x10) ⟨rfl, rfl, rfl⟩ (hdr_kept rfl keep1_1 keep3_1 ?_ ?_) hF3 hret3_15 ?_ hpre_4
    hret1_16 (by simp only [BitVec.toNat_ofNat] at hret1_18; omega) hret1_17 fun b h1 h2 =>
      Runtime.ReserveT.getMem_owned hF3 hown1 hpre_5 (by omega) ⟨h1, h2⟩ id
  · exact (hret3_17 (hdr_spare _ _ _)).1
  · exact (hret3_17 (hdr_spare _ _ _)).2
  · rw [hret3_25]; simp only [MachineState.code_setMem]; rw [hret1_19]; simp only [MachineState.code_setMem]

end Rv64mc.Proof.Layout.FromElemFormT

/-- info: 'Rv64mc.Proof.Layout.FromElemFormT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.FromElemFormT.total
