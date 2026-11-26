/-
  Rv64mc.Proof.Layout.ColumnKappasT

  `verifier::layout::column_kappas(tables, log_memory, log_bytecode, table_log_heights)` is total: called with the
  result's slot (`a0`), the tables (`a1`, `a2`, 80-byte elements), the two logs (`a3`, `a4`) and the heights (`a5`,
  `a6`, words), it returns the kappas a vector's (`VecT`), its buffer fresh, or the run ends with the guest's abort
  (`AbortStop`) where `keccak_shape`, `alloc`, `try_allocate_in`, `reserve`, a bounds check, `handle_error` or
  `panic_nounwind_fmt` does. A safety-only contract (the function is class D: no spec).

  The widths come from `TABLE_WIDTHS` in the static data, `[13, 13, 7, 14, 14, 92]`, which the proof takes as an
  environment fact (`DataRef.InData`, as `Table::count_columns` takes `COUNT_COLUMNS`): the code's fill loop for
  `vec![h; w]` is a do-while that is only safe for `w ≥ 2`, which the compiler derived from those values.

  The body is cut at the outer loop's head (instruction 98, one table a pass, measure the tables left), at 138
  (`vec![0; w]`, `try_allocate_in`), at 164 (`vec![h; w]`'s block from `alloc`, its header stored and `reserve`d), at
  the fill loop's head (192, measure the words left), at 202 (the result `reserve`d), at 210 (`memcpy` and the length's
  store) and at the return (236). Every part keeps `MemOk` (the thirteen slots, the frame, the static data, the code)
  and `RV` (the result's header at `top - 152`: length at most capacity, buffer fresh since the entry).

  ## Main definitions

  * `PreT`, `PostT`, `SpecT`, `Slots`, `MemOk`, `RV`, `OBase`, `Args`, `Src`, `CInv`, `FInv`, `OInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Multilinear.StackOffsetsT
import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Layout.KeccakShapeT
import Rv64mc.Gen.Tmpl.Verifier.Layout.ColumnKappas

namespace Rv64mc.Proof.Layout.ColumnKappasT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Runtime.TryAllocateInT (TryAllocSpecT)
open Rv64mc.Proof.Runtime.ReserveT (ReserveSpecT)
open Rv64mc.Gen.Verifier.Layout.ColumnKappas (Link tmpl d_c48_a47cc263_words)

/-- The words of a slice of `n` words at `a`, as numbers. -/
def wordsOf (m : MachineState) (a : Word) (n : Nat) : List Nat :=
  (List.range n).map fun k => (m.getMem (a + BitVec.ofNat 64 (8 * k))).toNat

/-- The heights read from memory satisfy `keccak_shape`'s partial precondition. -/
theorem wordsOf_pre {m : MachineState} {regs : Reg → Word} (h : (regs .x10).toNat + 8 * (regs .x11).toNat < 2 ^ 64) :
    Spec.Layout.KeccakShape.Pre (wordsOf m (regs .x10) (regs .x11).toNat) regs m := by
  refine ⟨by simp [wordsOf], by simpa [wordsOf] using h, fun k hk => ?_⟩
  simp [wordsOf]

/-- `keccak_shape`'s total contract for the heights memory holds: any slice in a window, nothing of its result. -/
theorem ks_any {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (hks : KeccakShapeT.specT env p i need) :
    HoldsT env p i need
      (fun regs m => KeccakShapeT.SliceWin env regs m ∧ (regs .x10).toNat + 8 * (regs .x11).toNat < 2 ^ 64)
      (fun _ _ _ _ => True) (Stop := AbortStop) := by
  intro Q ret top rest regs m hpre hstop hk
  obtain ⟨⟨hE, hs, hst, hnx, ⟨hw, hb⟩, h16⟩, hW⟩ := hpre
  exact hks (wordsOf m (regs .x10) (regs .x11).toNat) Q ret top rest regs m
    ⟨⟨hE, hs, hst, hnx, ⟨wordsOf_pre hb, hw⟩, h16⟩, hW⟩ hstop
    fun r' m' h => hk r' m' ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, trivial⟩, h.2⟩

/-- The total precondition: the result's slot a caller's, in a window and 8-byte aligned; the tables (`a1`, `a2`,
    80-byte elements) and the heights (`a5`, `a6`, words) blocks allocated before (`BufT`). -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
    BufT env m (regs .x12) (regs .x11) 80 ∧ BufT env m (regs .x16) (regs .x15) 8

/-- The total postcondition: the result a vector's, its buffer fresh unless it has no capacity. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 8 ∧
    ((vecCap m' (regs .x10)).toNat = 0 ∨ env.Fresh m m' (vecPtr m' (regs .x10)) ((vecCap m' (regs .x10)).toNat * 8))

/-- **The total contract of `column_kappas`**: the kappas a vector's, its buffer fresh. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) SretVecOut AbortStop

/-- The prologue's thirteen saved words in `M`, at `top - 8` down to `top - 104`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26 ∧
    M.getMem (top + 18446744073709551512#64) = regs .x27

/-- What every part keeps of memory: the slots, the frame, the static data, the code. -/
def MemOk (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  Slots M top ret regs ∧ env.Frame top (SretVecOut regs m) m M ∧ env.Static M ∧ M.code = m.code

/-- The result's header at `top - 152` (capacity, pointer, length): the length at most the capacity, the buffer
    fresh since the entry. -/
def RV (env : Env) (m : MachineState) (top : Word) (M : MachineState) : Prop :=
  (M.getMem (top + 18446744073709551480#64)).toNat ≤ (M.getMem (top + 18446744073709551464#64)).toNat ∧
    (M.getMem (top + 18446744073709551464#64)).toNat * 8 < 2 ^ 63 ∧
    0x10000000 ≤ (M.getMem (top + 18446744073709551472#64)).toNat ∧
    (env.next m).toNat ≤ (M.getMem (top + 18446744073709551472#64)).toNat ∧
    (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat ≤
      (env.next M).toNat ∧ (M.getMem (top + 18446744073709551472#64)).toNat % 8 = 0

/-- The slots kept by a memory that agrees from `top - 104` up to `top`. -/
theorem slots_keep {M X : MachineState} {top ret : Word} {regs : Reg → Word} (hlim : 160 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 104 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (hsl : Slots M top ret regs) : Slots X top ret regs := by
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 104 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := Runtime.CloneT.toNat_add_neg (t := top) hc (by omega)
      exact hk _ (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := hsl
  exact ⟨(es _ 8 rfl (by omega) (by omega)).trans s1, (es _ 16 rfl (by omega) (by omega)).trans s2,
    (es _ 24 rfl (by omega) (by omega)).trans s3, (es _ 32 rfl (by omega) (by omega)).trans s4,
    (es _ 40 rfl (by omega) (by omega)).trans s5, (es _ 48 rfl (by omega) (by omega)).trans s6,
    (es _ 56 rfl (by omega) (by omega)).trans s7, (es _ 64 rfl (by omega) (by omega)).trans s8,
    (es _ 72 rfl (by omega) (by omega)).trans s9, (es _ 80 rfl (by omega) (by omega)).trans s10,
    (es _ 88 rfl (by omega) (by omega)).trans s11, (es _ 96 rfl (by omega) (by omega)).trans s12,
    (es _ 104 rfl (by omega) (by omega)).trans s13⟩

/-- **One store into the frame's `out`**, a word apart from the slots and in a window: `MemOk` and `NEXT` kept. -/
theorem out_store {env : Env} {m M : MachineState} {top ret b v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hb : SretVecOut regs m b) (hwin : InWin env b 8)
    (hsep : b.toNat + 8 ≤ top.toNat - 104 ∨ top.toNat ≤ b.toNat) (hM : MemOk env m top ret regs M) :
    MemOk env m top ret regs (M.setMem b v) ∧ env.next (M.setMem b v) = env.next M := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hn : b ≠ env.nextAddr := fun e => by rw [e] at hwin; unfold InWin at hwin; omega
  exact ⟨⟨slots_keep (by omega) (fun a h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_out hF hb hn, Tactic.static_store hS (by unfold InWin at hwin; omega),
    by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hn⟩

/-- **The result's three stores** at `sret`, a caller's 24 bytes in a window: `MemOk` and `NEXT` kept, the three
    words read back. -/
theorem hdr3 {env : Env} {m M : MachineState} {top ret v0 v1 v2 : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hown : env.Owned m top (regs .x10) 24)
    (hwin : InWin env (regs .x10) 24) (hM : MemOk env m top ret regs M) :
    MemOk env m top ret regs (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v1).setMem (regs .x10 + 16#64) v2) ∧
      env.next (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v1).setMem (regs .x10 + 16#64) v2) =
        env.next M ∧
      (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v1).setMem (regs .x10 + 16#64) v2).getMem (regs .x10) =
        v0 ∧
      (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v1).setMem (regs .x10 + 16#64) v2).getMem
        (regs .x10 + 8#64) = v1 ∧
      (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v1).setMem (regs .x10 + 16#64) v2).getMem
        (regs .x10 + 16#64) = v2 := by
  have hlay := env.layout
  have hnm := hM.2.1.1
  have hnM := hM.2.1.2.1
  have h24 := hown.2
  have e8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have hsep : ∀ k, k ≤ 16 → (regs .x10).toNat + k + 8 ≤ top.toNat - 104 ∨ top.toNat ≤ (regs .x10).toNat + k :=
    fun k hk => by rcases hown.1 with h1 | h1 <;> omega
  have hout : ∀ k : Nat, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k → SretVecOut regs m b :=
    fun k hk b hb => by show InRange (regs .x10) Layouts.Vec.byteSize b; unfold InRange Layouts.Vec.byteSize; omega
  have hw : ∀ k : Nat, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k → InWin env b 8 :=
    fun k hk b hb => Runtime.MemsetT.InWin.sub hwin (by omega) (by omega)
  obtain ⟨m1, n1⟩ := out_store (v := v0) hlim (hout 0 (by omega) _ rfl) (hw 0 (by omega) _ rfl) (hsep 0 (by omega)) hM
  obtain ⟨m2, n2⟩ := out_store (v := v1) hlim (hout 8 (by omega) _ e8) (hw 8 (by omega) _ e8)
    (by rw [e8]; exact hsep 8 (by omega)) m1
  obtain ⟨m3, n3⟩ := out_store (v := v2) hlim (hout 16 (by omega) _ e16) (hw 16 (by omega) _ e16)
    (by rw [e16]; exact hsep 16 (by omega)) m2
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  refine ⟨m3, by rw [n3, n2, n1], ?_, ?_, MachineState.getMem_setMem_eq⟩
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]

/-- **The result from its header's words**: capacity `C`, pointer `P`, length `n`, the buffer fresh since `m`. -/
theorem post_ok {env : Env} {regs : Reg → Word} {m M : MachineState} {C P n : Word}
    (hwin : InWin env (regs .x10) 24) (hal : (regs .x10).toNat % 8 = 0)
    (h0 : M.getMem (regs .x10) = C) (h8 : M.getMem (regs .x10 + 8#64) = P) (h16 : M.getMem (regs .x10 + 16#64) = n)
    (hnC : n.toNat ≤ C.toNat) (hC : C.toNat * 8 < 2 ^ 63) (hP1 : 0x10000000 ≤ P.toNat)
    (hP2 : (env.next m).toNat ≤ P.toNat) (hP3 : P.toNat + 8 * C.toNat ≤ (env.next M).toNat) (hP8 : P.toNat % 8 = 0)
    {r : Reg → Word} : PostT env regs m r M := by
  have hc : vecCap M (regs .x10) = C := by rw [Runtime.ReserveT.vecCap_eq, h0]
  have hc' : M.getMem (rvCapAt (regs .x10)) = C := by
    rw [show rvCapAt (regs .x10) = regs .x10 from Runtime.GrowOne.rvCapAt_eq _, h0]
  have hp : vecPtr M (regs .x10) = P := h8
  have hp' : M.getMem (rvPtrAt (regs .x10)) = P := h8
  refine ⟨⟨hwin, ⟨Runtime.MemsetT.InWin.sub hwin (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega),
    hal, ?_, by rw [hc']; exact hC⟩, by rw [Runtime.ReserveT.vecLen_eq, h16, hc]; exact hnC⟩, ?_⟩
  · rw [hc', hp']; exact .inr ⟨hP1, by unfold Env.Live; omega, hP8⟩
  · rw [hc, hp]; exact .inr ⟨hP2, by omega⟩

set_option rv_sym.heap true in
/-- **The return**, from instruction 236: the result's header copied to `sret`, then the saved registers. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + 160 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hown : env.Owned m top (regs .x10) 24) (hwin : InWin env (regs .x10) 24) (hal : (regs .x10).toNat % 8 = 0) :
    ∀ R M, (R .x2 = top + 18446744073709551456#64 ∧ R .x8 = regs .x10) → MemOk env m top ret regs M →
      RV env m top M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 236, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hM hV
  have hlay := env.layout
  obtain ⟨hM', hn', r0, r8, r16⟩ := hdr3 (v0 := M.getMem (top + 18446744073709551464#64))
    (v1 := M.getMem (top + 18446744073709551472#64)) (v2 := M.getMem (top + 18446744073709551480#64)) (by omega)
    hown hwin hM
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩, hF, hS, hc⟩ := hM'
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  have hPost := fun r => post_ok (r := r) hwin hal r0 r8 r16 v1 v2 v3 v4 (by rw [hn']; exact v5) v6
  obtain ⟨⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13⟩, -, -, hc0⟩ := hM
  have h24 := hown.2
  have := hW.heapEnd_le
  have := hW.nextAddr_ge
  have hw : ∀ k : Nat, k ≤ 16 → inWindow (regs .x10 + BitVec.ofNat 64 k) 8 = true := fun k hk => by
    have e : (regs .x10 + BitVec.ofNat 64 k).toNat = (regs .x10).toNat + k := toNat_add_ofNat (by omega)
    rw [inWindow_iff, e]; unfold InWin at hwin; omega
  have w0 : inWindow (regs .x10) 8 = true := by simpa using hw 0 (by omega)
  have w8 := hw 8 (by omega)
  have w16 := hw 16 (by omega)
  rv_introT hR
  rv_symT hp with [_hL]
  all_goals first | exact (hPost (fun _ => 0#64)).1.2.1.2.2.1 | exact (hPost (fun _ => 0#64)).1.2.1.2.2.2

/-- The outer loop's fixed registers and memory, at table `j`: the result's slot, the heights, the tables' end and
    cursor, the widths table, `isize`'s bound; `MemOk` and the result's header `RV`. -/
def OBase (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (D : DataRef) (j : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551456#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x16 ∧ R .x18 = regs .x15 ∧
    R .x25 = regs .x11 + (regs .x12 <<< 6 + regs .x12 <<< 4) ∧ R .x26 = D.hi + D.lo ∧
    R .x27 = 9223372036854775800#64 ∧ (R .x19).toNat = (regs .x11).toNat + 80 * j ∧
    MemOk env m top ret regs M ∧ RV env m top M

/-- The facts of the precondition the parts read. -/
def Args (env : Env) (m : MachineState) (top : Word) (regs : Reg → Word) : Prop :=
  env.stackLimit.toNat + 160 ≤ top.toNat ∧ Windows env top m ∧ top.toNat % 16 = 0 ∧
    env.Owned m top (regs .x10) 24 ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
    BufT env m (regs .x12) (regs .x11) 80 ∧ BufT env m (regs .x16) (regs .x15) 8 ∧
    (regs .x11).toNat + 80 * (regs .x12).toNat < 2 ^ 64

theorem cap_at (top : Word) : rvCapAt (top + 18446744073709551464#64) = top + 18446744073709551464#64 :=
  Runtime.GrowOne.rvCapAt_eq _

theorem ptr_at (top : Word) : rvPtrAt (top + 18446744073709551464#64) = top + 18446744073709551472#64 := by
  unfold rvPtrAt; rw [BitVec.add_assoc]; rfl

theorem len_at (m : MachineState) (top : Word) :
    vecLen m (top + 18446744073709551464#64) = m.getMem (top + 18446744073709551480#64) := by
  unfold vecLen; rw [BitVec.add_assoc]; rfl

theorem vcap_at (m : MachineState) (top : Word) :
    vecCap m (top + 18446744073709551464#64) = m.getMem (top + 18446744073709551464#64) :=
  Runtime.ReserveT.vecCap_eq _ _

theorem vptr_at (m : MachineState) (top : Word) :
    vecPtr m (top + 18446744073709551464#64) = m.getMem (top + 18446744073709551472#64) := by
  unfold vecPtr; rw [BitVec.add_assoc]; rfl

/-- The source of a table's words, `n` of them at `s`: in the heap, allocated before `M`'s `NEXT`, aligned. -/
def Src (env : Env) (s : Word) (n : Nat) (M : MachineState) : Prop :=
  0x10000000 ≤ s.toNat ∧ s.toNat + 8 * n ≤ (env.next M).toNat ∧ s.toNat % 8 = 0

/-- At instruction 210, the result reserved: room for the `n` words, its buffer apart from the source. -/
def CInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (D : DataRef) (j : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  OBase env m top ret regs D j R M ∧ 7 ≤ (R .x21).toNat ∧ (R .x21).toNat ≤ 92 ∧
    Src env (R .x22) (R .x21).toNat M ∧
    (M.getMem (top + 18446744073709551480#64)).toNat + (R .x21).toNat ≤
      (M.getMem (top + 18446744073709551464#64)).toNat ∧
    ((M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat ≤
      (R .x22).toNat ∨ (R .x22).toNat + 8 * (R .x21).toNat ≤ (M.getMem (top + 18446744073709551472#64)).toNat)

/-- **What `reserve` of the result leaves**: `MemOk`, `RV`, the source, room for its `n` words, the result's buffer
    apart from it. -/
theorem after_resv {env : Env} {m M m1 : MachineState} {top ret s : Word} {regs : Reg → Word} {n : Nat}
    {out : Word → Prop} (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (hV : RV env m top M) (hS : Src env s n M)
    (hsep : (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat ≤
      s.toNat)
    (hF : env.Frame (top + 18446744073709551456#64) out M m1)
    (hout : ∀ b, out b → b = rvCapAt (top + 18446744073709551464#64) ∨ b = rvPtrAt (top + 18446744073709551464#64))
    (hSt : env.Static m1) (hc : m1.code = M.code)
    (hkeep : ∀ a, top + 18446744073709551456#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a)
    (h16 : vecLen m1 (top + 18446744073709551464#64) = vecLen M (top + 18446744073709551464#64))
    (h17 : n ≤ (vecCap M (top + 18446744073709551464#64)).toNat - (vecLen M (top + 18446744073709551464#64)).toNat →
      vecCap m1 (top + 18446744073709551464#64) = vecCap M (top + 18446744073709551464#64) ∧
        vecPtr m1 (top + 18446744073709551464#64) = vecPtr M (top + 18446744073709551464#64))
    (h18 : ¬ n ≤ (vecCap M (top + 18446744073709551464#64)).toNat - (vecLen M (top + 18446744073709551464#64)).toNat →
      Grown env M m1 (top + 18446744073709551464#64) ((vecLen M (top + 18446744073709551464#64)).toNat + n) 8)
    (h22 : (m1.getMem (rvCapAt (top + 18446744073709551464#64))).toNat = 0 ∨
      0x10000000 ≤ (m1.getMem (rvPtrAt (top + 18446744073709551464#64))).toNat ∧
        env.Live m1 (m1.getMem (rvPtrAt (top + 18446744073709551464#64)))
          ((m1.getMem (rvCapAt (top + 18446744073709551464#64))).toNat * 8) ∧
        (m1.getMem (rvPtrAt (top + 18446744073709551464#64))).toNat % 8 = 0)
    (h23 : (m1.getMem (rvCapAt (top + 18446744073709551464#64))).toNat * 8 < 2 ^ 63)
    (h24 : (vecLen m1 (top + 18446744073709551464#64)).toNat ≤ (vecCap m1 (top + 18446744073709551464#64)).toNat) :
    MemOk env m top ret regs m1 ∧ RV env m top m1 ∧ Src env s n m1 ∧
      (m1.getMem (top + 18446744073709551480#64)).toNat + n ≤ (m1.getMem (top + 18446744073709551464#64)).toNat ∧
      ((m1.getMem (top + 18446744073709551472#64)).toNat + 8 * (m1.getMem (top + 18446744073709551464#64)).toNat ≤
        s.toNat ∨ s.toNat + 8 * n ≤ (m1.getMem (top + 18446744073709551472#64)).toNat) := by
  have hlay := env.layout
  obtain ⟨hsl, hF0, -, hc0⟩ := hM
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  obtain ⟨s1, s2, s3⟩ := hS
  have hnM := hF.1
  have hnm := hF0.1
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e152 := es 18446744073709551464#64 152 rfl (by omega)
  have e144 := es 18446744073709551472#64 144 rfl (by omega)
  have e160 := es 18446744073709551456#64 160 rfl (by omega)
  have hout' : ∀ b, out b → b.toNat = top.toNat - 152 ∨ b.toNat = top.toNat - 144 := fun b hb => by
    rcases hout b hb with h | h
    · rw [h, cap_at]; exact .inl e152
    · rw [h, ptr_at]; exact .inr e144
  rw [len_at, len_at] at h16
  rw [vcap_at, vcap_at, len_at, vptr_at, vptr_at] at h17
  rw [vcap_at, len_at] at h18
  rw [cap_at, ptr_at] at h22
  rw [cap_at] at h23
  rw [len_at, vcap_at] at h24
  refine ⟨⟨slots_keep (by omega) (fun a h1 h2 => hkeep a (BitVec.le_def.2 (by rw [e160]; omega)) fun ha => by
      rcases hout' a ha with h | h <;> omega) hsl,
    hF0.trans hF (by rw [e160]; omega) fun b hb => Or.inl (by rcases hout' b hb with h | h <;> omega), hSt,
    hc.trans hc0⟩, ?_⟩
  simp only [RV, Src]
  rw [h16]
  by_cases hr : n ≤ (M.getMem (top + 18446744073709551464#64)).toNat - (M.getMem (top + 18446744073709551480#64)).toNat
  · obtain ⟨c1, c2⟩ := h17 hr
    rw [c1, c2]
    exact ⟨⟨v1, v2, v3, v4, by omega, v6⟩, ⟨s1, by omega, s3⟩, by omega, .inl hsep⟩
  · obtain ⟨g1, ⟨g2, g3⟩, -⟩ := h18 hr
    simp only [cap_at, ptr_at] at g1 g2 g3
    obtain ⟨p1, -, p3⟩ := h22.resolve_left (by omega)
    rw [h16] at h24
    exact ⟨⟨h24, h23, p1, by omega, by omega, p3⟩, ⟨s1, by omega, s3⟩, by omega, .inr (by omega)⟩

set_option rv_sym.heap true in
/-- **From instruction 202** to 210: the result reserved for a table's `n` words at `x22`. -/
theorem resv {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needR : Nat} (hnR : 160 + needR ≤ need)
    (hres : ReserveSpecT env 8 8 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) {j : Nat}
    (hk : ∀ R M, CInv env m top ret regs L.d_c48_a47cc263 j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 210, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, OBase env m top ret regs L.d_c48_a47cc263 j R M → 7 ≤ (R .x21).toNat → (R .x21).toNat ≤ 92 →
      Src env (R .x22) (R .x21).toNat M →
      (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat ≤
        (R .x22).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 202, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI hw1 hw2 hS hsep
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, hown, hwin, hal, hB1, hB2, hov⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, hM, hV⟩ := id hI
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  rv_introT hI
  rv_symT hp stop [210] with [hL] using [hres]
  · rw [cap_at, ptr_at]; exact .inr (by unfold Env.Live; omega)
  · change (M.getMem (rvCapAt (top + 18446744073709551464#64))).toNat * 8 < 2 ^ 63
    rw [cap_at]; exact v2
  · rw [cap_at, ptr_at]; exact .inr ⟨v3, by unfold Env.Live; omega, v6⟩
  · change (M.getMem (rvCapAt (top + 18446744073709551464#64))).toNat * 8 < 2 ^ 63
    rw [cap_at]; exact v2
  obtain ⟨hM1, hV1, hS1, hr1, hs1⟩ := after_resv (by omega) hM ⟨v1, v2, v3, v4, v5, v6⟩ hS hsep hret1_14
    (fun b hb => hb) hret1_15 hret1_25 keep1_1 hret1_16 hret1_17 hret1_18 hret1_22 hret1_23 hret1_24
  exact hk _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hI_8, hM1, hV1⟩, hw1, hw2, hS1, hr1, hs1⟩

/-- **What `memcpy` into the result's spare room and the length's store leave**: `MemOk` and `RV`, the length
    `v`. -/
theorem after_copy {env : Env} {m M m1 : MachineState} {top ret v : Word} {regs : Reg → Word} {n : Nat}
    {out : Word → Prop} (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (hV : RV env m top M)
    (hr : (M.getMem (top + 18446744073709551480#64)).toNat + n ≤ (M.getMem (top + 18446744073709551464#64)).toNat)
    (hv : v.toNat = (M.getMem (top + 18446744073709551480#64)).toNat + n)
    (hF : env.Frame (top + 18446744073709551456#64) out M m1)
    (hout : ∀ b, out b → (M.getMem (top + 18446744073709551472#64)).toNat ≤ b.toNat ∧
      b.toNat < (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat)
    (hSt : env.Static m1) (hc : m1.code = M.code)
    (hkeep : ∀ a, top + 18446744073709551456#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a) :
    MemOk env m top ret regs (m1.setMem (top + 18446744073709551480#64) v) ∧
      RV env m top (m1.setMem (top + 18446744073709551480#64) v) := by
  have hlay := env.layout
  obtain ⟨hsl, hF0, -, hc0⟩ := hM
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  have hnM := hF.1
  have hnm := hF0.1
  have hnE := hF0.2.1
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e136 := es 18446744073709551480#64 136 rfl (by omega)
  have e144 := es 18446744073709551472#64 144 rfl (by omega)
  have e152 := es 18446744073709551464#64 152 rfl (by omega)
  have e160 := es 18446744073709551456#64 160 rfl (by omega)
  have hk1 : ∀ a : Word, top.toNat - 160 ≤ a.toNat → m1.getMem a = M.getMem a := fun a ha =>
    hkeep a (BitVec.le_def.2 (by rw [e160]; omega)) fun hb => by have := hout a hb; omega
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hF1 : env.Frame top (SretVecOut regs m) m m1 :=
    hF0.trans hF (by rw [e160]; omega) fun b hb => Or.inr (Or.inl (by have := hout b hb; omega))
  have hn1 : env.next (m1.setMem (top + 18446744073709551480#64) v) = env.next m1 :=
    Env.next_setMem_stack (by omega)
  refine ⟨⟨slots_keep (by omega) (fun a h1 h2 => by
      rw [MachineState.getMem_setMem_ne (ne _ _ (by omega))]; exact hk1 a (by omega)) hsl,
    Tactic.frame_slot hF1 (by omega) (by omega), Env.static_setMem_stack hSt (by omega),
    by rw [MachineState.code_setMem, hc, hc0]⟩, ?_⟩
  have g152 : (m1.setMem (top + 18446744073709551480#64) v).getMem (top + 18446744073709551464#64) =
      M.getMem (top + 18446744073709551464#64) := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega))]; exact hk1 _ (by omega)
  have g144 : (m1.setMem (top + 18446744073709551480#64) v).getMem (top + 18446744073709551472#64) =
      M.getMem (top + 18446744073709551472#64) := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega))]; exact hk1 _ (by omega)
  unfold RV
  rw [g152, g144, MachineState.getMem_setMem_eq, hn1, hv]
  exact ⟨hr, v2, v3, v4, by omega, v6⟩

set_option rv_sym.heap true in
/-- **From instruction 210**: the table's words appended (`memcpy`), then the next table or the return. -/
theorem copy {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM : Nat} (hnM : 160 + needM ≤ need) (hcp : MemcpySpecT env p L.memcpy.idx needM)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) {j k : Nat}
    (hj : j + k + 1 = (regs .x12).toNat)
    (hk98 : ∀ R M, j + 1 < (regs .x12).toNat → OBase env m top ret regs L.d_c48_a47cc263 (j + 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 98, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, CInv env m top ret regs L.d_c48_a47cc263 j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 210, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, hown, hwin, hal, hB1, hB2, hov⟩ := hA
  obtain ⟨⟨-, -, -, -, -, -, -, hx19, hM, hV⟩, hw1, hw2, hS, hr, hsep⟩ := id hI
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  obtain ⟨s1, s2, s3⟩ := hS
  have hnm := hM.2.1.1
  have hnM := hM.2.1.2.1
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hs : (R .x21 <<< 3).toNat = 8 * (R .x21).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hl3 : (M.getMem (top + 18446744073709551480#64) <<< 3).toNat =
      8 * (M.getMem (top + 18446744073709551480#64)).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have eD : (M.getMem (top + 18446744073709551472#64) + M.getMem (top + 18446744073709551480#64) <<< 3).toNat =
      (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551480#64)).toNat := by
    rw [BitVec.toNat_add, hl3]; omega
  have h6 : (regs .x12 <<< 6).toNat = 64 * (regs .x12).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have h4 : (regs .x12 <<< 4).toNat = 16 * (regs .x12).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e25 : (regs .x11 + (regs .x12 <<< 6 + regs .x12 <<< 4)).toNat = (regs .x11).toNat + 80 * (regs .x12).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, h6, h4]; omega
  have e19 : (R .x19 + 80#64).toNat = (regs .x11).toNat + 80 * (j + 1) := by
    rw [toNat_add_ofNat (by omega)]; omega
  rv_introT hI
  rv_symT hp stop [98, 236] with [hL] using [hcp]
  any_goals first
    | exact absurd (congrArg BitVec.toNat hc_1) (by simp; omega)
    | (rw [eD, hs]; omega)
    | (rw [hs]; omega)
    | (rw [hs, eD]
       refine .inr ⟨.inl ⟨by omega, by omega⟩, .inl (by omega), ?_, .inl (by omega)⟩
       rw [inWindow_iff]; omega)
  all_goals
    obtain ⟨hM1, hV1⟩ := after_copy (v := M.getMem (top + 18446744073709551480#64) + R .x21) (n := (R .x21).toNat)
      (by omega) hM ⟨v1, v2, v3, v4, v5, v6⟩ hr (Runtime.Alloc.toNat_add_ofNat' (by omega)) hret1_14
      (fun b hb => by
        have := Runtime.VecHdrT.copyOut_in
          (P := M.getMem (top + 18446744073709551472#64) + M.getMem (top + 18446744073709551480#64) <<< 3)
          (by exact rfl) (by exact hs) (by rw [eD]; omega) hb
        rw [eD] at this; omega) hret1_15 hret1_19 keep1_1
  · have hlt : j + 1 < (regs .x12).toNat := by
      have : j + 1 ≠ (regs .x12).toNat := fun h => hc (BitVec.eq_of_toNat_eq (by rw [e19, e25, h]))
      omega
    exact hk98 _ _ hlt ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, e19, hM1, hV1⟩
  · exact exit hp hL hk (by omega) hW h16 hown hwin hal _ _ ⟨rfl, rfl⟩ hM1 hV1

/-- The widths table: entry `op` below `6` in a window, aligned, between `7` and `92`. -/
theorem width_ok {env : Env} {top : Word} {m M : MachineState} {D : DataRef}
    (hdata : DataRef.InData env [(D, d_c48_a47cc263_words)]) (hS : env.Static M) (hW : Windows env top m)
    {op : Word} (hop : op.toNat < 6) :
    inWindow (D.hi + D.lo + op <<< 3) 8 = true ∧ (D.hi + D.lo + op <<< 3).toNat % 8 = 0 ∧
      7 ≤ (M.getMem (D.hi + D.lo + op <<< 3)).toNat ∧ (M.getMem (D.hi + D.lo + op <<< 3)).toNat ≤ 92 := by
  have e : op <<< 3 = BitVec.ofNat 64 (8 * op.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]; omega
  have hl : d_c48_a47cc263_words.length = 6 := rfl
  rw [e]
  have hd := hW.data_ok _ (hdata _ (List.mem_singleton_self _) op.toNat (by rw [hl]; omega))
  rw [(hdata.words (List.mem_singleton_self _)).get hS op.toNat (by rw [hl]; omega)]
  refine ⟨hd.1, hd.2, ?_⟩
  rcases (by omega : op.toNat = 0 ∨ op.toNat = 1 ∨ op.toNat = 2 ∨ op.toNat = 3 ∨ op.toNat = 4 ∨ op.toNat = 5) with
    h | h | h | h | h | h <;> simp [h, d_c48_a47cc263_words]

/-- **A store into a block allocated since the entry**: `MemOk`, `RV`, `NEXT` and the result's header kept. -/
theorem heap_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hM : MemOk env m top ret regs M) (hV : RV env m top M)
    (ha1 : (env.next m).toNat ≤ a.toNat) (ha2 : a.toNat + 8 ≤ (env.next M).toNat) :
    MemOk env m top ret regs (M.setMem a v) ∧ RV env m top (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      (M.setMem a v).getMem (top + 18446744073709551464#64) = M.getMem (top + 18446744073709551464#64) ∧
      (M.setMem a v).getMem (top + 18446744073709551472#64) = M.getMem (top + 18446744073709551472#64) := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hnM := hF.2.1
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at ha2; omega
  have hn : env.next (M.setMem a v) = env.next M := Tactic.next_setMem hne
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (M.setMem a v).getMem (top + c) = M.getMem (top + c) :=
    fun c k hc hk => MachineState.getMem_setMem_ne fun h => by
      have := congrArg BitVec.toNat h; rw [es c k hc hk] at this; omega
  refine ⟨⟨slots_keep (by omega) (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_fresh hF rfl ha1 (by omega), Tactic.static_store hS (.inl (by omega)),
    by rw [MachineState.code_setMem, hc]⟩, ?_, hn, g 18446744073709551464#64 152 rfl (by omega),
    g 18446744073709551472#64 144 rfl (by omega)⟩
  unfold RV
  rw [g 18446744073709551464#64 152 rfl (by omega), g 18446744073709551472#64 144 rfl (by omega),
    g 18446744073709551480#64 136 rfl (by omega), hn]
  exact hV

/-- **A store between the result's header and the slots** (`top - 128` to `top - 104`): `MemOk`, `RV` and `NEXT`
    kept. -/
theorem mid_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hM : MemOk env m top ret regs M) (hV : RV env m top M)
    (ha1 : top.toNat - 128 ≤ a.toNat) (ha2 : a.toNat + 8 ≤ top.toNat - 104) :
    MemOk env m top ret regs (M.setMem a v) ∧ RV env m top (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      (M.setMem a v).getMem (top + 18446744073709551464#64) = M.getMem (top + 18446744073709551464#64) ∧
      (M.setMem a v).getMem (top + 18446744073709551472#64) = M.getMem (top + 18446744073709551472#64) := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hn : env.next (M.setMem a v) = env.next M := Env.next_setMem_stack (by omega)
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 136 ≤ k → k ≤ 160 →
      (M.setMem a v).getMem (top + c) = M.getMem (top + c) :=
    fun c k hc hk hk' => MachineState.getMem_setMem_ne fun h => by
      have := congrArg BitVec.toNat h; rw [es c k hc hk'] at this; omega
  refine ⟨⟨slots_keep (by omega) (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_slot hF (by omega) (by omega), Env.static_setMem_stack hS (by omega),
    by rw [MachineState.code_setMem, hc]⟩, ?_, hn, g 18446744073709551464#64 152 rfl (by omega) (by omega),
    g 18446744073709551472#64 144 rfl (by omega) (by omega)⟩
  unfold RV
  rw [g 18446744073709551464#64 152 rfl (by omega) (by omega), g 18446744073709551472#64 144 rfl (by omega) (by omega),
    g 18446744073709551480#64 136 rfl (by omega) (by omega), hn]
  exact hV

/-- **A call that writes at most between the result's header and the slots**: `MemOk` and `RV` kept. -/
theorem keep_mid {env : Env} {m M M' : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hM : MemOk env m top ret regs M) (hV : RV env m top M)
    (hF : env.Frame (top + 18446744073709551456#64) out M M')
    (hout : ∀ b, out b → top.toNat - 128 ≤ b.toNat ∧ b.toNat < top.toNat - 104)
    (hSt : env.Static M') (hc : M'.code = M.code)
    (hkeep : ∀ a, top + 18446744073709551456#64 ≤ a → ¬ out a → M'.getMem a = M.getMem a) :
    MemOk env m top ret regs M' ∧ RV env m top M' ∧
      M'.getMem (top + 18446744073709551464#64) = M.getMem (top + 18446744073709551464#64) ∧
      M'.getMem (top + 18446744073709551472#64) = M.getMem (top + 18446744073709551472#64) := by
  have hlay := env.layout
  obtain ⟨hsl, hF0, -, hc0⟩ := hM
  have hnM := hF.1
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e160 := es 18446744073709551456#64 160 rfl (by omega)
  have hk1 : ∀ a : Word, top.toNat - 160 ≤ a.toNat → (a.toNat < top.toNat - 128 ∨ top.toNat - 104 ≤ a.toNat) →
      M'.getMem a = M.getMem a := fun a ha hb =>
    hkeep a (BitVec.le_def.2 (by rw [e160]; omega)) fun h => by have := hout a h; omega
  refine ⟨⟨slots_keep (by omega) (fun a h1 h2 => hk1 a (by omega) (.inr h1)) hsl,
    hF0.trans hF (by rw [e160]; omega) fun b hb => Or.inl (by have := hout b hb; omega), hSt, hc.trans hc0⟩, ?_⟩
  have e152 := es 18446744073709551464#64 152 rfl (by omega)
  have e144 := es 18446744073709551472#64 144 rfl (by omega)
  have e136 := es 18446744073709551480#64 136 rfl (by omega)
  unfold RV
  rw [hk1 (top + 18446744073709551464#64) (by omega) (.inl (by omega)),
    hk1 (top + 18446744073709551472#64) (by omega) (.inl (by omega)),
    hk1 (top + 18446744073709551480#64) (by omega) (.inl (by omega))]
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  exact ⟨⟨v1, v2, v3, v4, by omega, v6⟩, rfl, rfl⟩

/-- The fill loop's head (instruction 192) for a table of width `w` at `Pt`, with `k + 2` words left to write: `x11`
    at word `i`, `x12` at the last. -/
def FInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (D : DataRef) (j : Nat) (w Pt : Word)
    (k : Nat) (R : Reg → Word) (M : MachineState) : Prop :=
  OBase env m top ret regs D j R M ∧ R .x21 = w ∧ R .x22 = Pt ∧ (R .x10).toNat = 0 ∧ Src env Pt w.toNat M ∧
    (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat ≤
      Pt.toNat ∧
    (R .x12).toNat + 8 = Pt.toNat + 8 * w.toNat ∧ ∃ i, i + k + 2 = w.toNat ∧ (R .x11).toNat = Pt.toNat + 8 * i

set_option rv_sym.heap true in
/-- **The fill loop** (`vec![h; w]`'s clones, then its last word), from its head to instruction 202. -/
theorem fill {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} {j : Nat} {w Pt : Word} (hlim : env.stackLimit.toNat + 160 ≤ top.toNat)
    (hW : Windows env top m) (hw1 : 7 ≤ w.toNat) (hw2 : w.toNat ≤ 92)
    (h202 : ∀ R M, OBase env m top ret regs L.d_c48_a47cc263 j R M → 7 ≤ (R .x21).toNat → (R .x21).toNat ≤ 92 →
      Src env (R .x22) (R .x21).toNat M →
      (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat ≤
        (R .x22).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 202, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, FInv env m top ret regs L.d_c48_a47cc263 j w Pt k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 192, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (FInv env m top ret regs L.d_c48_a47cc263 j w Pt) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨-, -, -, -, -, -, -, hx19, hM, hV⟩, hx21, hx22, hx10, hS, hsep, hx12, i, hi, hx11⟩ := id hI
  obtain ⟨s1, s2, s3⟩ := hS
  have hnM := hM.2.1.2.1
  have hW1 := hW.heapEnd_le
  have v4 := hV.2.2.2.1
  have w11 : inWindow (R .x11) 8 = true := by rw [inWindow_iff, hx11]; omega
  have a11 : (R .x11).toNat % 8 = 0 := by rw [hx11]; omega
  have e11 : (R .x11 + 8#64).toNat = Pt.toNat + 8 * (i + 1) := by rw [toNat_add_ofNat (by omega)]; omega
  have w11' : inWindow (R .x11 + 8#64) 8 = true := by rw [inWindow_iff, e11]; omega
  have a11' : (R .x11 + 8#64).toNat % 8 = 0 := by rw [e11]; omega
  obtain ⟨hM1, hV1, hn1, g1, g2⟩ := heap_store (a := R .x11) (v := R .x24) hlim hM hV (by omega) (by omega)
  rv_introT hI
  rv_symT hp stop [192, 202] with [_hL]
  · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [e11]; omega))
    exact ih (k - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx19, hM1, hV1⟩, rfl, rfl, hx10,
      ⟨s1, by rw [hn1]; omega, s3⟩, by rw [g1, g2]; exact hsep, hx12, i + 1, by omega, e11⟩
  · have he := congrArg BitVec.toNat hc
    rw [e11] at he
    obtain ⟨hM2, hV2, hn2, g3, g4⟩ := heap_store (a := R .x11 + 8#64) (v := R .x24) hlim hM1 hV1 (by omega)
      (by rw [hn1]; omega)
    have ew : (w + R .x10).toNat = w.toNat := by rw [BitVec.toNat_add, hx10]; omega
    exact h202 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx19, hM2, hV2⟩ (by simp only [Tactic.rf]; omega)
      (by simp only [Tactic.rf]; omega) ⟨s1, by simp only [Tactic.rf]; rw [ew, hn2, hn1]; omega, s3⟩
      (by simp only [Tactic.rf]; rw [g3, g4, g1, g2]; exact hsep)

theorem tcap_at (top : Word) : rvCapAt (top + 18446744073709551488#64) = top + 18446744073709551488#64 :=
  Runtime.GrowOne.rvCapAt_eq _

theorem tptr_at (top : Word) : rvPtrAt (top + 18446744073709551488#64) = top + 18446744073709551496#64 := by
  unfold rvPtrAt; rw [BitVec.add_assoc]; rfl

/-- The scratch vector's header stored at `top - 128`: capacity `w`, pointer `P`, length `0`. -/
def tmp3 (M7 : MachineState) (top w P : Word) : MachineState :=
  ((M7.setMem (top + 18446744073709551488#64) w).setMem (top + 18446744073709551496#64) P).setMem
    (top + 18446744073709551504#64) 0#64

/-- The scratch vector's header, as `reserve` asks it. -/
theorem tmp_pre {env : Env} {M7 : MachineState} {top w P : Word} (hlim : env.stackLimit.toNat + 160 ≤ top.toNat)
    (hw : w.toNat ≤ 92) (hP1 : 0x10000000 ≤ P.toNat) (hP2 : P.toNat + 8 * w.toNat ≤ (env.next M7).toNat)
    (hP8 : P.toNat % 8 = 0) :
    (((tmp3 M7 top w P).getMem (rvCapAt (top + 18446744073709551488#64))).toNat = 0 ∨
      env.Live (tmp3 M7 top w P) ((tmp3 M7 top w P).getMem (rvPtrAt (top + 18446744073709551488#64)))
        (((tmp3 M7 top w P).getMem (rvCapAt (top + 18446744073709551488#64))).toNat * 8)) ∧
      ((tmp3 M7 top w P).getMem (rvCapAt (top + 18446744073709551488#64))).toNat * 8 < 2 ^ 63 ∧
      BufT env (tmp3 M7 top w P) ((tmp3 M7 top w P).getMem (rvCapAt (top + 18446744073709551488#64)))
        ((tmp3 M7 top w P).getMem (rvPtrAt (top + 18446744073709551488#64))) 8 ∧
      (tmp3 M7 top w P).getMem (top + 18446744073709551488#64) = w ∧
      (tmp3 M7 top w P).getMem (top + 18446744073709551496#64) = P ∧
      (tmp3 M7 top w P).getMem (top + 18446744073709551504#64) = 0#64 ∧
      env.next (tmp3 M7 top w P) = env.next M7 := by
  have hlay := env.layout
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e128 := es 18446744073709551488#64 128 rfl (by omega)
  have e120 := es 18446744073709551496#64 120 rfl (by omega)
  have e112 := es 18446744073709551504#64 112 rfl (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have r0 : (tmp3 M7 top w P).getMem (top + 18446744073709551488#64) = w := by
    unfold tmp3
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r8 : (tmp3 M7 top w P).getMem (top + 18446744073709551496#64) = P := by
    unfold tmp3
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have r16 : (tmp3 M7 top w P).getMem (top + 18446744073709551504#64) = 0#64 := by
    unfold tmp3; rw [MachineState.getMem_setMem_eq]
  have hn : env.next (tmp3 M7 top w P) = env.next M7 := by
    unfold tmp3
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
  rw [tcap_at, tptr_at, r0, r8]
  exact ⟨.inr (by unfold Env.Live; rw [hn]; omega), by omega, .inr ⟨hP1, by unfold Env.Live; rw [hn]; omega, hP8⟩,
    rfl, rfl, r16, hn⟩

/-- **What `reserve` of the scratch vector leaves**: it had room, so its length `0` and pointer `P` are kept. -/
theorem after_tmp_resv {M7 m9 : MachineState} {top w P : Word} {n : Nat} (hn : n ≤ w.toNat)
    (hc0 : M7.getMem (top + 18446744073709551488#64) = w) (hp0 : M7.getMem (top + 18446744073709551496#64) = P)
    (hl0 : M7.getMem (top + 18446744073709551504#64) = 0#64)
    (h16 : vecLen m9 (top + 18446744073709551488#64) = vecLen M7 (top + 18446744073709551488#64))
    (h17 : n ≤ (vecCap M7 (top + 18446744073709551488#64)).toNat -
        (vecLen M7 (top + 18446744073709551488#64)).toNat →
      vecCap m9 (top + 18446744073709551488#64) = vecCap M7 (top + 18446744073709551488#64) ∧
        vecPtr m9 (top + 18446744073709551488#64) = vecPtr M7 (top + 18446744073709551488#64)) :
    m9.getMem (top + 18446744073709551504#64) = 0#64 ∧ m9.getMem (top + 18446744073709551496#64) = P := by
  have el : ∀ X : MachineState, vecLen X (top + 18446744073709551488#64) = X.getMem (top + 18446744073709551504#64) :=
    fun X => by unfold vecLen; rw [BitVec.add_assoc]; rfl
  have ep : ∀ X : MachineState, vecPtr X (top + 18446744073709551488#64) = X.getMem (top + 18446744073709551496#64) :=
    fun X => by unfold vecPtr; rw [BitVec.add_assoc]; rfl
  rw [el, el, hl0] at h16
  rw [Runtime.ReserveT.vecCap_eq, Runtime.ReserveT.vecCap_eq, el, ep, ep, hc0, hl0, hp0] at h17
  exact ⟨h16, (h17 (by simp; omega)).2⟩

set_option rv_sym.heap true in
/-- **`vec![0; w]`**, from instruction 138: `try_allocate_in`'s zeroed block, to instruction 202. -/
theorem zpath {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needT needH : Nat} (hnT : 160 + needT ≤ need) (hnH : 160 + needH ≤ need)
    (hta : TryAllocSpecT env p L.tryAllocateInInVerifier.idx needT) (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState} {j : Nat}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs)
    (h202 : ∀ R M, OBase env m top ret regs L.d_c48_a47cc263 j R M → 7 ≤ (R .x21).toNat → (R .x21).toNat ≤ 92 →
      Src env (R .x22) (R .x21).toNat M →
      (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat ≤
        (R .x22).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 202, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, OBase env m top ret regs L.d_c48_a47cc263 j R M → 7 ≤ (R .x21).toNat → (R .x21).toNat ≤ 92 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 138, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hB hw1 hw2
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, hown, hwin, hal, hB1, hB2, hov⟩ := hA
  have hlim : env.stackLimit.toNat + 160 ≤ top.toNat := hstk
  obtain ⟨-, -, -, -, -, -, -, hx19, hM, hV⟩ := id hB
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  have hnm := hM.2.1.1
  have hge := hW.next_ge
  have e128 := Runtime.CloneT.toNat_add_neg (t := top) (c := 18446744073709551488#64) (k := 128) rfl (by omega)
  rv_introT hB
  rv_symT hp stop [202] with [hL] using [hta, hhe]
  obtain ⟨hM3, hV3, q1, q2⟩ := keep_mid hlim hM ⟨v1, v2, v3, v4, v5, v6⟩ hret1_14 (fun b hb => by
      change InRange (top + 18446744073709551488#64) tryAllocBytes b at hb
      unfold InRange tryAllocBytes at hb; rw [e128] at hb; omega) hret1_15 hret1_18 keep1_1
  obtain ⟨-, hok⟩ := hret1_16 hc
  have tp : taPtrAt (top + 18446744073709551488#64) = top + 18446744073709551504#64 := by
    unfold taPtrAt; rw [BitVec.add_assoc]; rfl
  rw [tp, show (8#64 : Word).toNat = 8 from rfl] at hok
  rcases hok with ⟨h0, -⟩ | ⟨-, -, hfr, h8⟩
  · omega
  · unfold Env.Fresh at hfr
    exact h202 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx19, hM3, hV3⟩ hw1 hw2
      ⟨by simp only [Tactic.rf]; omega, by simp only [Tactic.rf]; omega, h8⟩
      (by simp only [Tactic.rf]; rw [q1, q2]; omega)

set_option rv_sym.heap true in
/-- **`vec![h; w]`**, from instruction 164, `alloc`'s block at `x20`: the scratch header stored and `reserve`d, to
    the fill loop's head. -/
theorem apath {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needR : Nat} (hnR : 160 + needR ≤ need) (hres : ReserveSpecT env 8 8 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState} {j : Nat}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs)
    (hfill : ∀ {w Pt : Word}, 7 ≤ w.toNat → w.toNat ≤ 92 →
      (∀ R M, OBase env m top ret regs L.d_c48_a47cc263 j R M → 7 ≤ (R .x21).toNat → (R .x21).toNat ≤ 92 →
        Src env (R .x22) (R .x21).toNat M →
        (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat ≤
          (R .x22).toNat →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 202, ret, top⟩ :: rest, R, M⟩) →
      ∀ k R M, FInv env m top ret regs L.d_c48_a47cc263 j w Pt k R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 192, ret, top⟩ :: rest, R, M⟩)
    (h202 : ∀ R M, OBase env m top ret regs L.d_c48_a47cc263 j R M → 7 ≤ (R .x21).toNat → (R .x21).toNat ≤ 92 →
      Src env (R .x22) (R .x21).toNat M →
      (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat ≤
        (R .x22).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 202, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, OBase env m top ret regs L.d_c48_a47cc263 j R M → 7 ≤ (R .x21).toNat → (R .x21).toNat ≤ 92 →
      R .x10 = R .x21 → R .x23 = R .x21 <<< 3 → Src env (R .x20) (R .x21).toNat M →
      (M.getMem (top + 18446744073709551472#64)).toNat + 8 * (M.getMem (top + 18446744073709551464#64)).toNat ≤
        (R .x20).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 164, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hB hw1 hw2 h10 h23 hS hsep
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, hown, hwin, hal, hB1, hB2, hov⟩ := hA
  have hlim : env.stackLimit.toNat + 160 ≤ top.toNat := hstk
  obtain ⟨-, -, -, -, -, -, -, hx19, hM, hV⟩ := id hB
  obtain ⟨s1, s2, s3⟩ := hS
  rw [← h10] at hw1 hw2 s2
  have tq := tmp_pre (M7 := M) (top := top) (w := R .x10) (P := R .x20) hlim hw2 s1 s2 s3
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e128 := es 18446744073709551488#64 128 rfl (by omega)
  have e120 := es 18446744073709551496#64 120 rfl (by omega)
  have e112 := es 18446744073709551504#64 112 rfl (by omega)
  rv_introT hB
  rv_symT hp stop [192] with [hL] using [hres]
  · exact tq.1
  · exact tq.2.1
  · exact tq.2.2.1
  · exact tq.2.1
  obtain ⟨-, -, -, tq4, tq5, tq6, tq7⟩ := tq
  unfold tmp3 at tq4 tq5 tq6 tq7
  obtain ⟨a1, b1, -, c1, d1⟩ := mid_store (a := top + 18446744073709551488#64) (v := R .x10) hlim hM hV
    (by omega) (by omega)
  obtain ⟨a2, b2, -, c2, d2⟩ := mid_store (a := top + 18446744073709551496#64) (v := R .x20) hlim a1 b1
    (by omega) (by omega)
  obtain ⟨a3, b3, -, c3, d3⟩ := mid_store (a := top + 18446744073709551504#64) (v := 0#64) hlim a2 b2
    (by omega) (by omega)
  obtain ⟨hM9, hV9, q3, q4⟩ := keep_mid hlim a3 b3 hret1_14 (fun b hb => by
      have hb' : b = rvCapAt (top + 18446744073709551488#64) ∨ b = rvPtrAt (top + 18446744073709551488#64) := hb
      rcases hb' with h | h
      · rw [h, tcap_at]; omega
      · rw [h, tptr_at]; omega) hret1_15 hret1_25 keep1_1
  obtain ⟨l9, p9⟩ := after_tmp_resv (n := (R .x21).toNat) (by rw [h10]) tq4 tq5 tq6 hret1_16 hret1_17
  have hn9 := hret1_14.1
  have hz : (0#64 : Word) <<< 3 = 0#64 := rfl
  have hs : (R .x21 <<< 3).toNat = 8 * (R .x21).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ← h10]; omega
  have eP : (R .x20 + R .x21 <<< 3).toNat = (R .x20).toNat + 8 * (R .x21).toNat := by
    rw [BitVec.toNat_add, hs, ← h10]; omega
  rw [h10] at hw1 hw2
  have e12 : (R .x20 + R .x21 <<< 3 + 18446744073709551608#64).toNat + 8 = (R .x20).toNat + 8 * (R .x21).toNat := by
    rw [Runtime.CloneT.toNat_add_neg (c := 18446744073709551608#64) (k := 8) rfl (by rw [eP]; omega), eP]; omega
  refine hfill hw1 hw2 h202 ((R .x21).toNat - 2) _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx19, hM9, hV9⟩, rfl, rfl,
    ?_, ?_, ?_, ?_, 0, by omega, ?_⟩ <;> simp only [Tactic.rf]
  · rw [l9]; rfl
  · rw [p9]; refine ⟨s1, ?_, s3⟩
    rw [tq7] at hn9; rw [← h10]; omega
  · rw [p9, q3, q4, c3, c2, c1, d3, d2, d1]; exact hsep
  · simp only [l9, p9, h23, hz, BitVec.add_zero]; exact e12
  · simp only [l9, p9, hz, BitVec.add_zero]; omega

/-- The outer loop's head (instruction 98) with `k + 1` tables left. -/
def OInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (D : DataRef) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  ∃ j, j + k + 1 = (regs .x12).toNat ∧ OBase env m top ret regs D j R M

set_option rv_sym.heap true in
/-- **The outer loop**, one table a pass, from its head to the return. -/
theorem outer {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) (hdata : DataRef.InData env [(L.d_c48_a47cc263, d_c48_a47cc263_words)])
    {need needA needT needR needM needH needP : Nat}
    (hnA : 160 + needA ≤ need) (hnT : 160 + needT ≤ need) (hnR : 160 + needR ≤ need) (hnM : 160 + needM ≤ need)
    (hnH : 160 + needH ≤ need) (hnP : 160 + needP ≤ need)
    (hal : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop))
    (hta : TryAllocSpecT env p L.tryAllocateInInVerifier.idx needT)
    (hres : ReserveSpecT env 8 8 p L.reserve.idx needR) (hcp : MemcpySpecT env p L.memcpy.idx needM)
    (hhe : Aborts env p L.handleError.idx needH) (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) :
    ∀ k R M, OInv env m top ret regs L.d_c48_a47cc263 k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 98, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInv env m top ret regs L.d_c48_a47cc263) fun k R M hI ih => ?_
  obtain ⟨j, hj, hB⟩ := hI
  have hk98 : ∀ R M, j + 1 < (regs .x12).toNat → OBase env m top ret regs L.d_c48_a47cc263 (j + 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 98, ret, top⟩ :: rest, R, M⟩ := fun R M hlt hB' =>
    ih (k - 1) R M (by omega) ⟨j + 1, by omega, hB'⟩
  have h210 := copy hp hL hnM hcp hk hneed hA hj hk98
  have h202 := resv hp hL hnR hres hstop hneed hA h210
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, hown, hwin, hal8, hB1, hB2, hov⟩ := id hA
  obtain ⟨-, -, -, -, -, -, -, hx19, hM, hV⟩ := id hB
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  have hlim : env.stackLimit.toNat + 160 ≤ top.toNat := hstk
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  obtain ⟨t1, t2, t3⟩ : 0x10000000 ≤ (regs .x11).toNat ∧
      (regs .x11).toNat + 80 * (regs .x12).toNat ≤ (env.next m).toNat ∧ (regs .x11).toNat % 8 = 0 := by
    rcases hB1 with h | ⟨h1, h2, h3⟩
    · omega
    · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
  have e72 : (R .x19 + 72#64).toNat = (regs .x11).toNat + 80 * j + 72 := by rw [toNat_add_ofNat (by omega)]; omega
  have hT : inWindow (R .x19 + 72#64) 8 = true ∧ (R .x19 + 72#64).toNat % 8 = 0 := by
    rw [inWindow_iff, e72]; omega
  have hH : ∀ op : Word, op < regs .x16 →
      inWindow (regs .x15 + op <<< 3) 8 = true ∧ (regs .x15 + op <<< 3).toNat % 8 = 0 := fun op h => by
    have h' := BitVec.lt_def.1 h
    obtain ⟨u1, u2, u3⟩ : 0x10000000 ≤ (regs .x15).toNat ∧
        (regs .x15).toNat + 8 * (regs .x16).toNat ≤ (env.next m).toNat ∧ (regs .x15).toNat % 8 = 0 := by
      rcases hB2 with h | ⟨h1, h2, h3⟩
      · omega
      · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
    have hs : (op <<< 3).toNat = 8 * op.toNat := by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have e : (regs .x15 + op <<< 3).toNat = (regs .x15).toNat + 8 * op.toNat := by rw [BitVec.toNat_add, hs]; omega
    rw [inWindow_iff, e]; omega
  have hD : ∀ op : Word, op < 6#64 →
      inWindow (L.d_c48_a47cc263.hi + L.d_c48_a47cc263.lo + op <<< 3) 8 = true ∧
        (L.d_c48_a47cc263.hi + L.d_c48_a47cc263.lo + op <<< 3).toNat % 8 = 0 ∧
        7 ≤ (M.getMem (L.d_c48_a47cc263.hi + L.d_c48_a47cc263.lo + op <<< 3)).toNat ∧
        (M.getMem (L.d_c48_a47cc263.hi + L.d_c48_a47cc263.lo + op <<< 3)).toNat ≤ 92 := fun op h =>
    width_ok hdata hM.2.2.1 hW (by have := BitVec.lt_def.1 h; simpa using this)
  have hW0 : ∀ op : Word, op < 6#64 →
      ¬ (M.getMem (L.d_c48_a47cc263.hi + L.d_c48_a47cc263.lo + op <<< 3) <<< 3 = 0#64) := fun op h e => by
    obtain ⟨-, -, h1, h2⟩ := hD op h
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e128 := es 18446744073709551488#64 128 rfl (by omega)
  have e120 := es 18446744073709551496#64 120 rfl (by omega)
  have e112 := es 18446744073709551504#64 112 rfl (by omega)
  have hZ := zpath (j := j) hp hL hnT hnH hta hhe hstop hneed hA h202
  have hAp := apath (j := j) hp hL hnR hres hstop hneed hA (fun hw1 hw2 h => fill (j := j) hp hL hlim hW hw1 hw2 h)
    h202
  rv_introT hB
  rv_symT hp stop [138, 160, 164] with [hL] using [hal, hhe, hpb]
  · exact (hH _ hc_1).1
  · exact (hH _ hc_1).2
  · exact (hD _ hc).1
  · exact (hD _ hc).2.1
  · obtain ⟨-, -, hw1, hw2⟩ := hD _ hc_2
    exact hZ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx19, hM, v1, v2, v3, v4, v5, v6⟩ hw1 hw2
  · exact absurd hc (hW0 _ hc_2)
  · obtain ⟨-, -, hw1, hw2⟩ := hD _ hc_2
    obtain ⟨hM7, hV7, q1, q2⟩ := keep_mid (out := fun _ => False) hlim hM ⟨v1, v2, v3, v4, v5, v6⟩ hret4_14
      (fun b hb => hb.elim) hret4_15 hret4_19 (fun a h _ => keep4_1 a h)
    have hx7 := hret4_18
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at hx7
    have hp7 := hret4_16
    have hn7 := hret4_14.1
    exact hAp _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx19, hM7, hV7⟩ hw1 hw2 rfl rfl
      ⟨by simp only [Tactic.rf]; omega, by simp only [Tactic.rf]; omega, hret4_17⟩
      (by simp only [Tactic.rf]; rw [q1, q2]; omega)

/-- The prologue's thirteen saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)).setMem (top + 18446744073709551536#64) (regs .x24)).setMem
    (top + 18446744073709551528#64) (regs .x25)).setMem (top + 18446744073709551520#64) (regs .x26)).setMem
    (top + 18446744073709551512#64) (regs .x27)

/-- The prologue's stores: in the frame, `env.Static`, `NEXT` and the code kept, the slots holding the saved
    words. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) :
    env.Frame top out m (saved m top ret regs) ∧ env.Static (saved m top ret regs) ∧
      env.next (saved m top ret regs) = env.next m ∧ Slots (saved m top ret regs) top ret regs ∧
      (saved m top ret regs).code = m.code := by
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e1 := es 18446744073709551608#64 8 rfl (by omega)
  have e2 := es 18446744073709551600#64 16 rfl (by omega)
  have e3 := es 18446744073709551592#64 24 rfl (by omega)
  have e4 := es 18446744073709551584#64 32 rfl (by omega)
  have e5 := es 18446744073709551576#64 40 rfl (by omega)
  have e6 := es 18446744073709551568#64 48 rfl (by omega)
  have e7 := es 18446744073709551560#64 56 rfl (by omega)
  have e8 := es 18446744073709551552#64 64 rfl (by omega)
  have e9 := es 18446744073709551544#64 72 rfl (by omega)
  have e10 := es 18446744073709551536#64 80 rfl (by omega)
  have e11 := es 18446744073709551528#64 88 rfl (by omega)
  have e12 := es 18446744073709551520#64 96 rfl (by omega)
  have e13 := es 18446744073709551512#64 104 rfl (by omega)
  refine ⟨?_, ?_, ?_, ?_, by simp only [saved, MachineState.code_setMem]⟩
  · simp only [saved]
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Env.Frame.refl hnx)
  · simp only [saved]
    repeat (first | refine Env.static_setMem_stack ?_ (by omega) | exact hS)
  · simp only [saved]
    repeat rw [Env.next_setMem_stack (by omega)]
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13] at h'; omega)])

/-- **The result's first block** (five words at `P`, from `alloc`) and its header at `top - 152` (capacity and length
    `5`): `MemOk` and `RV`. -/
theorem init_ok {env : Env} {m M : MachineState} {top ret P v0 v1 v2 : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (hge : 0x10000000 ≤ (env.next m).toNat) (hP1 : (env.next m).toNat ≤ P.toNat)
    (hP2 : P.toNat + 40 = (env.next M).toNat) (hP8 : P.toNat % 8 = 0) :
    MemOk env m top ret regs ((((((((M.setMem P v0).setMem (P + 8#64) v0).setMem (P + 16#64) v0).setMem (P + 24#64) v1).setMem
      (P + 32#64) v2).setMem (top + 18446744073709551464#64) 5#64).setMem (top + 18446744073709551472#64) P).setMem
      (top + 18446744073709551480#64) 5#64) ∧
    RV env m top ((((((((M.setMem P v0).setMem (P + 8#64) v0).setMem (P + 16#64) v0).setMem (P + 24#64) v1).setMem
      (P + 32#64) v2).setMem (top + 18446744073709551464#64) 5#64).setMem (top + 18446744073709551472#64) P).setMem
      (top + 18446744073709551480#64) 5#64) := by
  have hlay := env.layout
  have hnM := hM.2.1.2.1
  have hst : ∀ {X : MachineState} {a v : Word}, MemOk env m top ret regs X → (env.next m).toNat ≤ a.toNat →
      a.toNat + 8 ≤ (env.next X).toNat →
      MemOk env m top ret regs (X.setMem a v) ∧ env.next (X.setMem a v) = env.next X := fun {X a v} hX ha1 ha2 => by
    obtain ⟨hsl, hF, hS, hc⟩ := hX
    have hnX := hF.2.1
    have hne : a ≠ env.nextAddr := fun e => by rw [e] at ha2; omega
    exact ⟨⟨slots_keep (by omega) (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega)
      hsl, Tactic.frame_fresh hF rfl ha1 (by omega), Tactic.static_store hS (.inl (by omega)),
      by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hne⟩
  have ek : ∀ k : Nat, k ≤ 32 → (P + BitVec.ofNat 64 k).toNat = P.toNat + k := fun k hk =>
    toNat_add_ofNat (by omega)
  obtain ⟨a1, n1⟩ := hst (a := P) (v := v0) hM hP1 (by omega)
  obtain ⟨a2, n2⟩ := hst (a := P + 8#64) (v := v0) a1 (by rw [ek 8 (by omega)]; omega)
    (by rw [ek 8 (by omega), n1]; omega)
  obtain ⟨a3, n3⟩ := hst (a := P + 16#64) (v := v0) a2 (by rw [ek 16 (by omega)]; omega)
    (by rw [ek 16 (by omega), n2, n1]; omega)
  obtain ⟨a4, n4⟩ := hst (a := P + 24#64) (v := v1) a3 (by rw [ek 24 (by omega)]; omega)
    (by rw [ek 24 (by omega), n3, n2, n1]; omega)
  obtain ⟨a5, n5⟩ := hst (a := P + 32#64) (v := v2) a4 (by rw [ek 32 (by omega)]; omega)
    (by rw [ek 32 (by omega), n4, n3, n2, n1]; omega)
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e152 := es 18446744073709551464#64 152 rfl (by omega)
  have e144 := es 18446744073709551472#64 144 rfl (by omega)
  have e136 := es 18446744073709551480#64 136 rfl (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hS : ∀ {X : MachineState} {a v : Word}, MemOk env m top ret regs X → top.toNat - 152 ≤ a.toNat →
      a.toNat + 8 ≤ top.toNat - 104 →
      MemOk env m top ret regs (X.setMem a v) ∧ env.next (X.setMem a v) = env.next X := fun {X a v} hX ha1 ha2 => by
    obtain ⟨hsl, hF, hSt, hc⟩ := hX
    exact ⟨⟨slots_keep (by omega) (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega)
      hsl, Tactic.frame_slot hF (by omega) (by omega), Env.static_setMem_stack hSt (by omega),
      by rw [MachineState.code_setMem, hc]⟩, Env.next_setMem_stack (by omega)⟩
  obtain ⟨b1, m1⟩ := hS (a := top + 18446744073709551464#64) (v := 5#64) a5 (by omega) (by omega)
  obtain ⟨b2, m2⟩ := hS (a := top + 18446744073709551472#64) (v := P) b1 (by omega) (by omega)
  obtain ⟨b3, m3⟩ := hS (a := top + 18446744073709551480#64) (v := 5#64) b2 (by omega) (by omega)
  refine ⟨b3, ?_⟩
  have r136 : ∀ X : MachineState, (X.setMem (top + 18446744073709551480#64) 5#64).getMem
      (top + 18446744073709551480#64) = 5#64 := fun X => MachineState.getMem_setMem_eq
  have r144 : ∀ X : MachineState, ((X.setMem (top + 18446744073709551472#64) P).setMem (top + 18446744073709551480#64)
      5#64).getMem (top + 18446744073709551472#64) = P := fun X => by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have r152 : ∀ X : MachineState, (((X.setMem (top + 18446744073709551464#64) 5#64).setMem
      (top + 18446744073709551472#64) P).setMem (top + 18446744073709551480#64) 5#64).getMem
      (top + 18446744073709551464#64) = 5#64 := fun X => by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  unfold RV
  rw [r136, r144, r152, m3, m2, m1, n5, n4, n3, n2, n1]
  simp only [BitVec.toNat_ofNat]
  omega

set_option rv_sym.heap true in
/-- **`column_kappas` is total**, with 160 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hdata : DataRef.InData env [(L.d_c48_a47cc263, d_c48_a47cc263_words)])
    {need needK needA needT needR needM needH needF needP : Nat} (hnK : 160 + needK ≤ need)
    (hnA : 160 + needA ≤ need) (hnT : 160 + needT ≤ need) (hnR : 160 + needR ≤ need) (hnM : 160 + needM ≤ need)
    (hnH : 160 + needH ≤ need) (hnF : 160 + needF ≤ need) (hnP : 160 + needP ≤ need)
    (hks : KeccakShapeT.specT env p L.keccakShape.idx needK) (hal : AllocSpecT env p L.alloc.idx needA)
    (hta : TryAllocSpecT env p L.tryAllocateInInVerifier.idx needT)
    (hres : ReserveSpecT env 8 8 p L.reserve.idx needR) (hcp : MemcpySpecT env p L.memcpy.idx needM)
    (hhe : Aborts env p L.handleError.idx needH) (hpf : Aborts env p L.panicNounwindFmt.idx needF)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hks' := ks_any hks
  rv_autoT hp stop [98, 236] with [hL] using [hks', hal', hhe, hpf]
  all_goals
    have hlay := env.layout
    rw [hpre_2] at hpre_6
    have hlim : env.stackLimit.toNat + 160 ≤ top.toNat := by omega
    obtain ⟨hF0, hS0, hn0, hsl0, hc0⟩ := saved_ok (out := SretVecOut regs m) (ret := ret) (regs := regs) hlim hpre_5
      hpre_4
    simp only [saved] at hF0 hS0 hn0 hsl0 hc0
    have t160 := Runtime.CloneT.toNat_add_neg (t := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
    have hF2 := Tactic.frame_callF (Tactic.frame_callF hF0 hret1_14 (by rw [t160]; omega)) hret2_14
      (by rw [t160]; omega)
    have hsl2 : Slots m2 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => (keep2_1 a (BitVec.le_def.2 (by rw [t160]; omega))).trans
        (keep1_1 a (BitVec.le_def.2 (by rw [t160]; omega)))) hsl0
    have hM2 : MemOk env m top ret regs m2 := ⟨hsl2, hF2, hret2_15, hret2_19.trans (hret1_16.trans hc0)⟩
    have hge := hpre_13.next_ge
    have hn1 := hret1_14.1
    rw [hn0] at hn1
    obtain ⟨hMi, hVi⟩ := init_ok (v0 := regs .x13) (v1 := regs .x14) (v2 := r1 .x10 + 6#64) hlim hM2 hge
      (by omega) (by have := hret2_18; simp only [BitVec.toNat_ofNat] at this; omega) hret2_17
    have hA : Args env m top regs := ⟨hlim, hpre_13, hpre_12, ⟨hpre_6, hpre_7⟩, hpre_8, hpre_9, hpre_10, hpre_11, ?_⟩
  · exact exit hp hL hk hlim hpre_13 hpre_12 ⟨hpre_6, hpre_7⟩ hpre_8 hpre_9 _ _ ⟨rfl, rfl⟩ hMi hVi
  · rcases hpre_10 with h | ⟨h1, h2, -⟩
    · omega
    · unfold Env.Live at h2; omega
  · have hn0' : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    exact outer hp hL hdata hnA hnT hnR hnM hnH hnP hal' hta hres hcp hhe hpb hk hstop hpre_3 hA
      ((regs .x12).toNat - 1) _ _ ⟨0, by omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp only [Tactic.rf]; omega,
        hMi, hVi⟩
  · rcases hpre_10 with h | ⟨h1, h2, -⟩
    · omega
    · unfold Env.Live at h2; omega

end Rv64mc.Proof.Layout.ColumnKappasT

/-- info: 'Rv64mc.Proof.Layout.ColumnKappasT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.ColumnKappasT.total
