/-
  Rv64mc.Proof.Layout.StackedBlocksT

  `verifier::layout::stacked_blocks(columns)` is total: called with the result's slot (`a0`) and a column count
  (`a1`), it returns the columns with a block of their own (`qkeccak_slot` none, not an output lane) as a vector
  (`ColumnKappasT.PostT`: `VecT`, its buffer fresh unless it has no capacity), or the run ends with the guest's abort
  (`AbortStop`) where `alloc`, `reserve` or `handle_error` does. A safety-only contract (the function is class D: no
  spec); nothing is asked of the count.

  The body is cut at the first loop's head (instruction 34, before any block, measure the columns left), at 30 (a
  column skipped), at the push loop's head (86, the vector built in the frame at `top - 88`), at 82 and 78 (the next
  column), at 118 (the push, room made by `reserve(1)` where the vector was full), and at the two returns (130 with
  the vector, 144 with none). Every part keeps `MemOk` (the eight slots, the frame, the static data, the code); the
  push loop also `RV` (the header: length at most capacity, buffer fresh since the entry, length in `x22`, pointer in
  `x18`).

  ## Main definitions

  * `PreT`, `SpecT`, `Slots`, `MemOk`, `RV`, `Saved`, `Args`, `PBase`, `PInv`, `FInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.ColumnKappasT
import Rv64mc.Proof.Layout.QkeccakSlotT
import Rv64mc.Proof.Layout.IsOutputLaneT
import Rv64mc.Gen.Tmpl.Verifier.Layout.StackedBlocks

namespace Rv64mc.Proof.Layout.StackedBlocksT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.ReserveT (ReserveSpecT)
open Rv64mc.Proof.Layout.ColumnKappasT (PostT)
open Rv64mc.Gen.Verifier.Layout.StackedBlocks (Link tmpl)

/-- The total precondition: the result's slot a caller's, in a window and 8-byte aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0

/-- **The total contract of `stacked_blocks`**: the blocks a vector's, its buffer fresh unless it has no capacity. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) SretVecOut AbortStop

/-- The prologue's eight saved words in `M`, at `top - 8` down to `top - 64`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22

/-- What every part keeps of memory: the slots, the frame, the static data, the code. -/
def MemOk (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  Slots M top ret regs ∧ env.Frame top (SretVecOut regs m) m M ∧ env.Static M ∧ M.code = m.code

/-- The blocks' header at `top - 88` (capacity, pointer, length): the length at most the capacity, the buffer fresh
    since the entry. -/
def RV (env : Env) (m : MachineState) (top : Word) (M : MachineState) : Prop :=
  (M.getMem (top + 18446744073709551544#64)).toNat ≤ (M.getMem (top + 18446744073709551528#64)).toNat ∧
    (M.getMem (top + 18446744073709551528#64)).toNat * 8 < 2 ^ 63 ∧
    0x10000000 ≤ (M.getMem (top + 18446744073709551536#64)).toNat ∧
    (env.next m).toNat ≤ (M.getMem (top + 18446744073709551536#64)).toNat ∧
    (M.getMem (top + 18446744073709551536#64)).toNat + 8 * (M.getMem (top + 18446744073709551528#64)).toNat ≤
      (env.next M).toNat ∧ (M.getMem (top + 18446744073709551536#64)).toNat % 8 = 0

theorem slots_keep {M X : MachineState} {top ret : Word} {regs : Reg → Word} (hlim : 96 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 64 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (hsl : Slots M top ret regs) : Slots X top ret regs := by
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 64 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := Runtime.CloneT.toNat_add_neg (t := top) hc (by omega)
      exact hk _ (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hsl
  exact ⟨(es _ 8 rfl (by omega) (by omega)).trans s1, (es _ 16 rfl (by omega) (by omega)).trans s2,
    (es _ 24 rfl (by omega) (by omega)).trans s3, (es _ 32 rfl (by omega) (by omega)).trans s4,
    (es _ 40 rfl (by omega) (by omega)).trans s5, (es _ 48 rfl (by omega) (by omega)).trans s6,
    (es _ 56 rfl (by omega) (by omega)).trans s7, (es _ 64 rfl (by omega) (by omega)).trans s8⟩

/-- **One store into the frame's `out`**, a word apart from the slots and in a window. -/
theorem out_store {env : Env} {m M : MachineState} {top ret b v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hb : SretVecOut regs m b) (hwin : InWin env b 8)
    (hsep : b.toNat + 8 ≤ top.toNat - 64 ∨ top.toNat ≤ b.toNat) (hM : MemOk env m top ret regs M) :
    MemOk env m top ret regs (M.setMem b v) ∧ env.next (M.setMem b v) = env.next M := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hn : b ≠ env.nextAddr := fun e => by rw [e] at hwin; unfold InWin at hwin; omega
  exact ⟨⟨slots_keep (by omega) (fun a h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_out hF hb hn, Tactic.static_store hS (by unfold InWin at hwin; omega),
    by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hn⟩

/-- **The result's three stores** at `sret`: `MemOk` and `NEXT` kept, the three words read back. -/
theorem hdr3 {env : Env} {m M : MachineState} {top ret v0 v1 v2 : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hown : env.Owned m top (regs .x10) 24)
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
  have hsep : ∀ k, k ≤ 16 → (regs .x10).toNat + k + 8 ≤ top.toNat - 64 ∨ top.toNat ≤ (regs .x10).toNat + k :=
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

/-- The registers the return needs: the stack pointer, `sret`, the callee-saved registers never written. -/
def Saved (top : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551520#64 ∧ R .x8 = regs .x10 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧
    R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- The facts of the precondition the parts read. -/
def Args (env : Env) (m : MachineState) (top : Word) (regs : Reg → Word) : Prop :=
  env.stackLimit.toNat + 96 ≤ top.toNat ∧ Windows env top m ∧ top.toNat % 16 = 0 ∧
    env.Owned m top (regs .x10) 24 ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0

set_option rv_sym.heap true in
/-- **The return with the blocks**, from instruction 130: their header copied to `sret`, the saved registers. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) :
    ∀ R M, Saved top regs R → MemOk env m top ret regs M →
      RV env m top M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hM hV
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, hown, hwin, hal⟩ := hA
  obtain ⟨hM', hn', r0, r8, r16⟩ := hdr3 (v0 := M.getMem (top + 18446744073709551528#64))
    (v1 := M.getMem (top + 18446744073709551536#64)) (v2 := M.getMem (top + 18446744073709551544#64)) hstk
    hown hwin hM
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7, s8⟩, hF, hS, hc⟩ := hM'
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  have hPost := fun r => ColumnKappasT.post_ok (r := r) hwin hal r0 r8 r16 v1 v2 v3 v4 (by rw [hn']; exact v5) v6
  obtain ⟨⟨t1, t2, t3, t4, t5, t6, t7, t8⟩, -, -, hc0⟩ := hM
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

set_option rv_sym.heap true in
/-- **The return with no blocks**, from instruction 144: the empty vector at `sret`. -/
theorem empty {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) :
    ∀ R M, Saved top regs R → MemOk env m top ret regs M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 144, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hM
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, hown, hwin, hal⟩ := hA
  obtain ⟨hM', hn', r0, r8, r16⟩ := hdr3 (v0 := 0#64) (v1 := 8#64) (v2 := 0#64) hstk hown hwin hM
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7, s8⟩, hF, hS, hc⟩ := hM'
  have rc : (((M.setMem (regs .x10) 0#64).setMem (regs .x10 + 8#64) 8#64).setMem (regs .x10 + 16#64) 0#64).getMem
      (rvCapAt (regs .x10)) = 0#64 := by rw [Runtime.GrowOne.rvCapAt_eq]; exact r0
  have hPost : ∀ r, PostT env regs m r
      (((M.setMem (regs .x10) 0#64).setMem (regs .x10 + 8#64) 8#64).setMem (regs .x10 + 16#64) 0#64) := fun r =>
    ⟨⟨hwin, ⟨Runtime.MemsetT.InWin.sub hwin (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega), hal,
      .inl (by rw [rc]; rfl), by rw [rc]; decide⟩,
      by rw [Runtime.ReserveT.vecLen_eq, r16, Runtime.ReserveT.vecCap_eq, r0]⟩,
      .inl (by rw [Runtime.ReserveT.vecCap_eq, r0]; rfl)⟩
  obtain ⟨⟨t1, t2, t3, t4, t5, t6, t7, t8⟩, -, -, hc0⟩ := hM
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

/-- `RV` kept by a memory that agrees on the header and has `NEXT` no lower. -/
theorem rv_keep {env : Env} {m M M' : MachineState} {top : Word} (hV : RV env m top M)
    (h1 : M'.getMem (top + 18446744073709551528#64) = M.getMem (top + 18446744073709551528#64))
    (h2 : M'.getMem (top + 18446744073709551536#64) = M.getMem (top + 18446744073709551536#64))
    (h3 : M'.getMem (top + 18446744073709551544#64) = M.getMem (top + 18446744073709551544#64))
    (hn : (env.next M).toNat ≤ (env.next M').toNat) : RV env m top M' := by
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  unfold RV; rw [h1, h2, h3]
  exact ⟨v1, v2, v3, v4, by omega, v6⟩

/-- **A call that writes nothing of the caller's** (`qkeccak_slot`, `is_output_lane`, `alloc`): `MemOk` kept, every
    word at or above its stack pointer kept. -/
theorem keep_none {env : Env} {m M M' : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (hF : env.Frame (top + 18446744073709551520#64) (fun _ => False) M M') (hSt : env.Static M')
    (hc : M'.code = M.code) (hkeep : ∀ a, top + 18446744073709551520#64 ≤ a → M'.getMem a = M.getMem a) :
    MemOk env m top ret regs M' ∧ (∀ a : Word, top.toNat - 96 ≤ a.toNat → M'.getMem a = M.getMem a) ∧
      (env.next M).toNat ≤ (env.next M').toNat := by
  obtain ⟨hsl, hF0, -, hc0⟩ := hM
  have e96 := Runtime.CloneT.toNat_add_neg (t := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have hk : ∀ a : Word, top.toNat - 96 ≤ a.toNat → M'.getMem a = M.getMem a := fun a ha =>
    hkeep a (BitVec.le_def.2 (by rw [e96]; omega))
  exact ⟨⟨slots_keep (by omega) (fun a h1 _ => hk a (by omega)) hsl, Tactic.frame_callF hF0 hF (by rw [e96]; omega),
    hSt, hc.trans hc0⟩, hk, hF.1⟩

/-- **A store into a block allocated since the entry**: `MemOk`, `NEXT` and the stack kept. -/
theorem heap_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (ha1 : (env.next m).toNat ≤ a.toNat) (ha2 : a.toNat + 8 ≤ (env.next M).toNat) :
    MemOk env m top ret regs (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      ∀ b : Word, top.toNat - 96 ≤ b.toNat → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hnM := hF.2.1
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at ha2; omega
  have hk : ∀ b : Word, top.toNat - 96 ≤ b.toNat → (M.setMem a v).getMem b = M.getMem b := fun b hb =>
    MachineState.getMem_setMem_ne fun e => by rw [e] at hb; omega
  exact ⟨⟨slots_keep (by omega) (fun b h1 _ => hk b (by omega)) hsl, Tactic.frame_fresh hF rfl ha1 (by omega),
    Tactic.static_store hS (.inl (by omega)), by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hne, hk⟩

/-- **A store into the frame below the slots** (`top - 96` to `top - 64`): `MemOk`, `NEXT` and every other word
    kept. -/
theorem frame_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (ha1 : top.toNat - 96 ≤ a.toNat) (ha2 : a.toNat + 8 ≤ top.toNat - 64) :
    MemOk env m top ret regs (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      ∀ b : Word, b ≠ a → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  exact ⟨⟨slots_keep (by omega) (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_slot hF (by omega) (by omega), Env.static_setMem_stack hS (by omega),
    by rw [MachineState.code_setMem, hc]⟩, Env.next_setMem_stack (by omega),
    fun b hb => MachineState.getMem_setMem_ne hb⟩

theorem cap_at (top : Word) : rvCapAt (top + 18446744073709551528#64) = top + 18446744073709551528#64 :=
  Runtime.GrowOne.rvCapAt_eq _

theorem ptr_at (top : Word) : rvPtrAt (top + 18446744073709551528#64) = top + 18446744073709551536#64 := by
  unfold rvPtrAt; rw [BitVec.add_assoc]; rfl

theorem len_at (m : MachineState) (top : Word) :
    vecLen m (top + 18446744073709551528#64) = m.getMem (top + 18446744073709551544#64) := by
  unfold vecLen; rw [BitVec.add_assoc]; rfl

theorem vptr_at (m : MachineState) (top : Word) :
    vecPtr m (top + 18446744073709551528#64) = m.getMem (top + 18446744073709551536#64) := by
  unfold vecPtr; rw [BitVec.add_assoc]; rfl

/-- **What `reserve(1)` of the full blocks' vector leaves**: `MemOk`, `RV`, the length kept and below the
    capacity. -/
theorem after_resv1 {env : Env} {m M m1 : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hM : MemOk env m top ret regs M) (hV : RV env m top M)
    (hF : env.Frame (top + 18446744073709551520#64) out M m1)
    (hout : ∀ b, out b → b = rvCapAt (top + 18446744073709551528#64) ∨ b = rvPtrAt (top + 18446744073709551528#64))
    (hSt : env.Static m1) (hc : m1.code = M.code)
    (hkeep : ∀ a, top + 18446744073709551520#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a)
    (h16 : vecLen m1 (top + 18446744073709551528#64) = vecLen M (top + 18446744073709551528#64))
    (h17 : 1 ≤ (vecCap M (top + 18446744073709551528#64)).toNat - (vecLen M (top + 18446744073709551528#64)).toNat →
      vecCap m1 (top + 18446744073709551528#64) = vecCap M (top + 18446744073709551528#64) ∧
        vecPtr m1 (top + 18446744073709551528#64) = vecPtr M (top + 18446744073709551528#64))
    (h18 : ¬ 1 ≤ (vecCap M (top + 18446744073709551528#64)).toNat - (vecLen M (top + 18446744073709551528#64)).toNat →
      Grown env M m1 (top + 18446744073709551528#64) ((vecLen M (top + 18446744073709551528#64)).toNat + 1) 8)
    (h22 : (m1.getMem (rvCapAt (top + 18446744073709551528#64))).toNat = 0 ∨
      0x10000000 ≤ (m1.getMem (rvPtrAt (top + 18446744073709551528#64))).toNat ∧
        env.Live m1 (m1.getMem (rvPtrAt (top + 18446744073709551528#64)))
          ((m1.getMem (rvCapAt (top + 18446744073709551528#64))).toNat * 8) ∧
        (m1.getMem (rvPtrAt (top + 18446744073709551528#64))).toNat % 8 = 0)
    (h23 : (m1.getMem (rvCapAt (top + 18446744073709551528#64))).toNat * 8 < 2 ^ 63)
    (h24 : (vecLen m1 (top + 18446744073709551528#64)).toNat ≤ (vecCap m1 (top + 18446744073709551528#64)).toNat) :
    MemOk env m top ret regs m1 ∧ RV env m top m1 ∧
      m1.getMem (top + 18446744073709551544#64) = M.getMem (top + 18446744073709551544#64) ∧
      (m1.getMem (top + 18446744073709551544#64)).toNat + 1 ≤ (m1.getMem (top + 18446744073709551528#64)).toNat := by
  have hlay := env.layout
  obtain ⟨hsl, hF0, -, hc0⟩ := hM
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  have hnM := hF.1
  have hnm := hF0.1
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 96 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e88 := es 18446744073709551528#64 88 rfl (by omega)
  have e80 := es 18446744073709551536#64 80 rfl (by omega)
  have e96 := es 18446744073709551520#64 96 rfl (by omega)
  have hout' : ∀ b, out b → b.toNat = top.toNat - 88 ∨ b.toNat = top.toNat - 80 := fun b hb => by
    rcases hout b hb with h | h
    · rw [h, cap_at]; exact .inl e88
    · rw [h, ptr_at]; exact .inr e80
  rw [len_at, len_at] at h16
  rw [Runtime.ReserveT.vecCap_eq, Runtime.ReserveT.vecCap_eq, len_at, vptr_at, vptr_at] at h17
  rw [Runtime.ReserveT.vecCap_eq, len_at] at h18
  rw [cap_at, ptr_at] at h22
  rw [cap_at] at h23
  rw [len_at, Runtime.ReserveT.vecCap_eq] at h24
  refine ⟨⟨slots_keep (by omega) (fun a h1 h2 => hkeep a (BitVec.le_def.2 (by rw [e96]; omega)) fun ha => by
      rcases hout' a ha with h | h <;> omega) hsl,
    hF0.trans hF (by rw [e96]; omega) fun b hb => Or.inl (by rcases hout' b hb with h | h <;> omega), hSt,
    hc.trans hc0⟩, ?_, h16, ?_⟩
  · simp only [RV]
    rw [h16]
    by_cases hr : 1 ≤ (M.getMem (top + 18446744073709551528#64)).toNat - (M.getMem (top + 18446744073709551544#64)).toNat
    · obtain ⟨c1, c2⟩ := h17 hr
      rw [c1, c2]
      exact ⟨v1, v2, v3, v4, by omega, v6⟩
    · obtain ⟨g1, ⟨g2, g3⟩, -⟩ := h18 hr
      simp only [cap_at, ptr_at] at g1 g2 g3
      obtain ⟨p1, -, p3⟩ := h22.resolve_left (by omega)
      rw [h16] at h24
      exact ⟨h24, h23, p1, by omega, by omega, p3⟩
  · rw [h16]
    by_cases hr : 1 ≤ (M.getMem (top + 18446744073709551528#64)).toNat - (M.getMem (top + 18446744073709551544#64)).toNat
    · rw [(h17 hr).1]; omega
    · obtain ⟨g1, -, -⟩ := h18 hr
      simp only [cap_at] at g1
      omega

/-- The push loop's fixed registers and memory: `Saved`, the count, `MemOk`, the header `RV` with its length in
    `x22` and pointer in `x18`. -/
def PBase (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Saved top regs R ∧ R .x9 = regs .x11 ∧ R .x21 = 1#64 ∧ MemOk env m top ret regs M ∧ RV env m top M ∧
    R .x22 = M.getMem (top + 18446744073709551544#64) ∧ R .x18 = M.getMem (top + 18446744073709551536#64)

/-- The push loop's head (instruction 86) with `k + 1` columns left, from `c` in `x19`. -/
def PInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  PBase env m top ret regs R M ∧ ∃ c, c + k + 1 = (regs .x11).toNat ∧ (R .x19).toNat = c

/-- **The push's two stores**, the column into the buffer's next word and the length counted: `MemOk`, `RV`, the
    pointer kept, the length one more. -/
theorem push_mem {env : Env} {m M : MachineState} {top ret v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hM : MemOk env m top ret regs M) (hV : RV env m top M)
    (hroom : (M.getMem (top + 18446744073709551544#64)).toNat + 1 ≤ (M.getMem (top + 18446744073709551528#64)).toNat)
    (eA : (M.getMem (top + 18446744073709551536#64) + M.getMem (top + 18446744073709551544#64) <<< 3).toNat =
      (M.getMem (top + 18446744073709551536#64)).toNat + 8 * (M.getMem (top + 18446744073709551544#64)).toNat) :
    MemOk env m top ret regs ((M.setMem (M.getMem (top + 18446744073709551536#64) +
        M.getMem (top + 18446744073709551544#64) <<< 3) v).setMem (top + 18446744073709551544#64)
        (M.getMem (top + 18446744073709551544#64) + 1#64)) ∧
      RV env m top ((M.setMem (M.getMem (top + 18446744073709551536#64) +
        M.getMem (top + 18446744073709551544#64) <<< 3) v).setMem (top + 18446744073709551544#64)
        (M.getMem (top + 18446744073709551544#64) + 1#64)) ∧
      ((M.setMem (M.getMem (top + 18446744073709551536#64) + M.getMem (top + 18446744073709551544#64) <<< 3) v).setMem
        (top + 18446744073709551544#64) (M.getMem (top + 18446744073709551544#64) + 1#64)).getMem
        (top + 18446744073709551536#64) = M.getMem (top + 18446744073709551536#64) := by
  have hlay := env.layout
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hV
  have hnM := hM.2.1.2.1
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 96 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e88 := es 18446744073709551528#64 88 rfl (by omega)
  have e80 := es 18446744073709551536#64 80 rfl (by omega)
  have e72 := es 18446744073709551544#64 72 rfl (by omega)
  obtain ⟨a1, n1, k1⟩ := heap_store (v := v) hlim hM (by rw [eA]; omega) (by rw [eA]; omega)
  obtain ⟨a2, n2, k2⟩ := frame_store (a := top + 18446744073709551544#64)
    (v := M.getMem (top + 18446744073709551544#64) + 1#64) hlim a1 (by omega) (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have g88 := (k2 (top + 18446744073709551528#64) (ne _ _ (by omega))).trans (k1 _ (by omega))
  have g80 := (k2 (top + 18446744073709551536#64) (ne _ _ (by omega))).trans (k1 _ (by omega))
  refine ⟨a2, ?_, g80⟩
  unfold RV
  rw [g88, g80, MachineState.getMem_setMem_eq, n2, n1, toNat_add_ofNat (by omega)]
  exact ⟨by omega, v2, v3, v4, v5, v6⟩

set_option rv_sym.heap true in
/-- **The push itself**, from instruction 118 (room for one more): the column stored, the length counted, then the
    next column (78) or the return. -/
theorem store1 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {c : Nat}
    (h78 : ∀ R M, PBase env m top ret regs R M → (R .x20).toNat = c + 1 → c + 1 < (regs .x11).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, PBase env m top ret regs R M → (R .x20).toNat = c + 1 →
      (M.getMem (top + 18446744073709551544#64)).toNat + 1 ≤ (M.getMem (top + 18446744073709551528#64)).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hB h20 hroom
  have hlay := env.layout
  have hex := exit hp hL hk hA
  obtain ⟨hstk, hW, h16, hown, hwin, hal⟩ := hA
  obtain ⟨hS, -, -, hM, hV, h22, h18⟩ := id hB
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := id hV
  have hnM := hM.2.1.2.1
  have hW1 := hW.heapEnd_le
  have hs : (M.getMem (top + 18446744073709551544#64) <<< 3).toNat =
      8 * (M.getMem (top + 18446744073709551544#64)).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have eA : (M.getMem (top + 18446744073709551536#64) + M.getMem (top + 18446744073709551544#64) <<< 3).toNat =
      (M.getMem (top + 18446744073709551536#64)).toNat + 8 * (M.getMem (top + 18446744073709551544#64)).toNat := by
    rw [BitVec.toNat_add, hs]; omega
  have wA := Multilinear.StackOffsetsT.elem_ok (j := (M.getMem (top + 18446744073709551544#64)).toNat)
    (c := (M.getMem (top + 18446744073709551528#64)).toNat) v3 v5 v6 hnM hW1 eA (by omega)
  obtain ⟨a2, b2, c2⟩ := push_mem (v := R .x19) hstk hM hV hroom eA
  rv_introT hB
  rv_symT hp stop [78, 130] with [hL]
  · exact h78 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, a2, b2, by simp only [Tactic.rf, MachineState.getMem_setMem_eq],
      c2.symm⟩ h20 (by have := BitVec.lt_def.1 hc; omega)
  · exact hex _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ a2 b2

set_option rv_sym.heap true in
/-- **The push loop**, from its head to the return. -/
theorem push {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needQ needO needR : Nat} (hnQ : 96 + needQ ≤ need) (hnO : 96 + needO ≤ need)
    (hnR : 96 + needR ≤ need)
    (hq : QkeccakSlotT.specT env p L.qkeccakSlot.idx needQ) (ho : IsOutputLaneT.specT env p L.isOutputLane.idx needO)
    (hres : ReserveSpecT env 8 8 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) :
    ∀ k R M, PInv env m top ret regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 86, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (PInv env m top ret regs) fun k R M hI ih => ?_
  have hlay := env.layout
  have hex := exit hp hL hk hA
  obtain ⟨hB, c, hck, hx19⟩ := hI
  have h78 : ∀ R' M', PBase env m top ret regs R' M' → (R' .x20).toNat = c + 1 → c + 1 < (regs .x11).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R', M'⟩ := by
    intro R' M' hB' h20 hlt
    obtain ⟨-, -, -, hM', hV', -, -⟩ := id hB'
    rv_introT hB'
    rv_symT hp stop [86] with [hL]
    exact ih (k - 1) _ _ (by omega) ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hM', hV', rfl, rfl⟩, c + 1,
      by omega, h20⟩
  have h82 : ∀ R' M', PBase env m top ret regs R' M' → (R' .x20).toNat = c + 1 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 82, ret, top⟩ :: rest, R', M'⟩ := by
    intro R' M' hB' h20
    obtain ⟨-, -, -, hM', hV', -, -⟩ := id hB'
    rv_introT hB'
    rv_symT hp stop [86, 130] with [hL]
    · exact hex _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hM' hV'
    · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h20]; omega))
      exact ih (k - 1) _ _ (by omega) ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hM', hV', rfl, rfl⟩, c + 1,
        by omega, h20⟩
  have h118 := store1 hp hL hk hA (c := c) h78
  obtain ⟨hstk, hW, h16, hown, hwin, hal⟩ := hA
  obtain ⟨hS, -, -, hM, hV, h22, h18⟩ := id hB
  have e20 : (R .x19 + 1#64).toNat = c + 1 := by rw [toNat_add_ofNat (by omega)]; omega
  rv_introT hB
  rv_symT hp stop [82, 118] with [hL] using [hq, ho, hres]
  all_goals
    obtain ⟨hM1, hk1, hn1⟩ := keep_none hstk hM hret1_14 hret1_15 hret1_17 keep1_1
    have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 96 → (top + c).toNat = top.toNat - k :=
      fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
    have e88 := es 18446744073709551528#64 88 rfl (by omega)
    have e80 := es 18446744073709551536#64 80 rfl (by omega)
    have e72 := es 18446744073709551544#64 72 rfl (by omega)
    have q1 := hk1 (top + 18446744073709551528#64) (by omega)
    have q2 := hk1 (top + 18446744073709551536#64) (by omega)
    have q3 := hk1 (top + 18446744073709551544#64) (by omega)
    have hV1 := rv_keep hV q1 q2 q3 hn1
  · exact h82 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hM1, hV1, q3.symm, q2.symm⟩ e20
  all_goals
    obtain ⟨hM2, hk2, hn2⟩ := keep_none hstk hM1 hret2_14 hret2_15 hret2_17 keep2_1
    have q1' := (hk2 (top + 18446744073709551528#64) (by omega)).trans q1
    have q2' := (hk2 (top + 18446744073709551536#64) (by omega)).trans q2
    have q3' := (hk2 (top + 18446744073709551544#64) (by omega)).trans q3
    have hV2 := rv_keep hV q1' q2' q3' (by omega)
  · exact h82 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hM2, hV2, q3'.symm, q2'.symm⟩ e20
  · -- room left: no `reserve`
    obtain ⟨v1, -, -, -, -, -⟩ := hV
    have hne : (M.getMem (top + 18446744073709551544#64)).toNat ≠ (M.getMem (top + 18446744073709551528#64)).toNat :=
      fun h => hc (BitVec.eq_of_toNat_eq h)
    exact h118 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hM2, hV2, q3'.symm, q2'.symm⟩ e20
      (by rw [q3', q1']; omega)
  all_goals
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hV2
  · rw [cap_at, ptr_at]; exact .inr (by unfold Env.Live; omega)
  · rw [cap_at]; exact w2
  · rw [cap_at, ptr_at]; exact .inr ⟨w3, by unfold Env.Live; omega, w6⟩
  · rw [cap_at]; exact w2
  · -- full: `reserve(1)`, then the pointer reloaded
    obtain ⟨hM3, hV3, l3, hr3⟩ := after_resv1 hstk hM2 ⟨w1, w2, w3, w4, w5, w6⟩ hret3_14 (fun b hb => hb) hret3_15
      hret3_25 keep3_1 hret3_16 hret3_17 hret3_18 hret3_22 hret3_23 hret3_24
    exact h118 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hM3, hV3, by simp only [Tactic.rf]; rw [l3, q3'], rfl⟩ e20 hr3

/-- **The first block** (from `alloc`, its first word written) and its header at `top - 88` (capacity `4`, length
    `1`): `MemOk`, `RV`, the length and pointer read back. -/
theorem init1 {env : Env} {m M : MachineState} {top ret P v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (hge : 0x10000000 ≤ (env.next m).toNat) (hP1 : (env.next m).toNat ≤ P.toNat)
    (hP2 : P.toNat + 32 = (env.next M).toNat) (hP8 : P.toNat % 8 = 0) :
    MemOk env m top ret regs ((((M.setMem P v).setMem (top + 18446744073709551528#64) 4#64).setMem
      (top + 18446744073709551536#64) P).setMem (top + 18446744073709551544#64) 1#64) ∧
    RV env m top ((((M.setMem P v).setMem (top + 18446744073709551528#64) 4#64).setMem
      (top + 18446744073709551536#64) P).setMem (top + 18446744073709551544#64) 1#64) ∧
    ((((M.setMem P v).setMem (top + 18446744073709551528#64) 4#64).setMem
      (top + 18446744073709551536#64) P).setMem (top + 18446744073709551544#64) 1#64).getMem
      (top + 18446744073709551544#64) = 1#64 ∧
    ((((M.setMem P v).setMem (top + 18446744073709551528#64) 4#64).setMem
      (top + 18446744073709551536#64) P).setMem (top + 18446744073709551544#64) 1#64).getMem
      (top + 18446744073709551536#64) = P := by
  have hlay := env.layout
  have hnM := hM.2.1.2.1
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 96 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e88 := es 18446744073709551528#64 88 rfl (by omega)
  have e80 := es 18446744073709551536#64 80 rfl (by omega)
  have e72 := es 18446744073709551544#64 72 rfl (by omega)
  obtain ⟨a1, n1, -⟩ := heap_store (v := v) hlim hM hP1 (by omega)
  obtain ⟨a2, n2, -⟩ := frame_store (a := top + 18446744073709551528#64) (v := 4#64) hlim a1 (by omega) (by omega)
  obtain ⟨a3, n3, -⟩ := frame_store (a := top + 18446744073709551536#64) (v := P) hlim a2 (by omega) (by omega)
  obtain ⟨a4, n4, -⟩ := frame_store (a := top + 18446744073709551544#64) (v := 1#64) hlim a3 (by omega) (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have r72 : ((((M.setMem P v).setMem (top + 18446744073709551528#64) 4#64).setMem
      (top + 18446744073709551536#64) P).setMem (top + 18446744073709551544#64) 1#64).getMem
      (top + 18446744073709551544#64) = 1#64 := MachineState.getMem_setMem_eq
  have r80 : ((((M.setMem P v).setMem (top + 18446744073709551528#64) 4#64).setMem
      (top + 18446744073709551536#64) P).setMem (top + 18446744073709551544#64) 1#64).getMem
      (top + 18446744073709551536#64) = P := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have r88 : ((((M.setMem P v).setMem (top + 18446744073709551528#64) 4#64).setMem
      (top + 18446744073709551536#64) P).setMem (top + 18446744073709551544#64) 1#64).getMem
      (top + 18446744073709551528#64) = 4#64 := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  refine ⟨a4, ?_, r72, r80⟩
  unfold RV
  rw [r72, r80, r88, n4, n3, n2, n1]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The first loop's head (instruction 34) with `k + 1` columns left from `c` (`x19`), no block found yet. -/
def FInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Saved top regs R ∧ R .x9 = regs .x11 ∧ R .x18 = 1#64 ∧ MemOk env m top ret regs M ∧
    ∃ c, c + k + 1 = (regs .x11).toNat ∧ (R .x19).toNat = c

set_option rv_sym.heap true in
/-- **The first loop**, to the first column with a block of its own (then the push loop) or the empty result. -/
theorem first {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needQ needO needA needR needH : Nat} (hnQ : 96 + needQ ≤ need) (hnO : 96 + needO ≤ need)
    (hnA : 96 + needA ≤ need) (hnR : 96 + needR ≤ need) (hnH : 96 + needH ≤ need)
    (hq : QkeccakSlotT.specT env p L.qkeccakSlot.idx needQ) (ho : IsOutputLaneT.specT env p L.isOutputLane.idx needO)
    (hal : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop))
    (hres : ReserveSpecT env 8 8 p L.reserve.idx needR) (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) :
    ∀ k R M, FInv env m top ret regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 34, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (FInv env m top ret regs) fun k R M hI ih => ?_
  have hlay := env.layout
  have hex := exit hp hL hk hA
  have hem := empty hp hL hk hA
  have hpush := push hp hL hnQ hnO hnR hq ho hres hk hstop hneed hA
  obtain ⟨hS, -, -, hM, c, hck, hx19⟩ := id hI
  have h30 : ∀ R' M', (Saved top regs R' ∧ R' .x9 = regs .x11 ∧ R' .x18 = 1#64) → MemOk env m top ret regs M' →
      (R' .x20).toNat = c + 1 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 30, ret, top⟩ :: rest, R', M'⟩ := by
    intro R' M' hB' hM' h20
    rv_introT hB'
    rv_symT hp stop [34, 144] with [hL]
    · exact hem _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hM'
    · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h20]; omega))
      exact ih (k - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hM', c + 1, by omega, h20⟩
  obtain ⟨hstk, hW, h16, hown, hwin, hal8⟩ := id hA
  have e20 : (R .x19 + 1#64).toNat = c + 1 := by rw [toNat_add_ofNat (by omega)]; omega
  rv_introT hI
  rv_symT hp stop [30, 130, 86] with [hL] using [hq, ho, hal, hhe]
  all_goals
    obtain ⟨hM1, -, -⟩ := keep_none hstk hM hret1_14 hret1_15 hret1_17 keep1_1
  · exact h30 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩ hM1 e20
  all_goals
    obtain ⟨hM2, -, -⟩ := keep_none hstk hM1 hret2_14 hret2_15 hret2_17 keep2_1
  · exact h30 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩ hM2 e20
  all_goals
    obtain ⟨hM3, -, hn3⟩ := keep_none hstk hM2 hret3_14 hret3_15 hret3_19 keep3_1
    have hge := hW.next_ge
    have hnm := hM.2.1.1
    have hn1 := hret1_14.1
    have hn2 := hret2_14.1
    obtain ⟨a4, b4, r72, r80⟩ := init1 (v := R .x19) hstk hM3 hge (by omega)
      (by have := hret3_18; simp only [BitVec.toNat_ofNat] at this; omega) hret3_17
  · exact hex _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ a4 b4
  · rv_symT hp stop [86] with [hL]
    exact hpush (k - 1) _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, a4, b4, r72.symm, r80.symm⟩, c + 1,
      by have := BitVec.lt_def.1 hc; omega, e20⟩

/-- The prologue's eight saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  (((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)

/-- The prologue's stores: `MemOk` at the entry's frame. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) : MemOk env m top ret regs (saved m top ret regs) := by
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 96 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e1 := es 18446744073709551608#64 8 rfl (by omega)
  have e2 := es 18446744073709551600#64 16 rfl (by omega)
  have e3 := es 18446744073709551592#64 24 rfl (by omega)
  have e4 := es 18446744073709551584#64 32 rfl (by omega)
  have e5 := es 18446744073709551576#64 40 rfl (by omega)
  have e6 := es 18446744073709551568#64 48 rfl (by omega)
  have e7 := es 18446744073709551560#64 56 rfl (by omega)
  have e8 := es 18446744073709551552#64 64 rfl (by omega)
  refine ⟨?_, ?_, ?_, by simp only [saved, MachineState.code_setMem]⟩
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6, e7, e8] at h'; omega)])
  · simp only [saved]
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Env.Frame.refl hnx)
  · simp only [saved]
    repeat (first | refine Env.static_setMem_stack ?_ (by omega) | exact hS)

set_option rv_sym.heap true in
/-- **`stacked_blocks` is total**, with 96 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needQ needO needA needR needH : Nat} (hnQ : 96 + needQ ≤ need) (hnO : 96 + needO ≤ need)
    (hnA : 96 + needA ≤ need) (hnR : 96 + needR ≤ need) (hnH : 96 + needH ≤ need)
    (hq : QkeccakSlotT.specT env p L.qkeccakSlot.idx needQ) (ho : IsOutputLaneT.specT env p L.isOutputLane.idx needO)
    (hal : AllocSpecT env p L.alloc.idx needA) (hres : ReserveSpecT env 8 8 p L.reserve.idx needR)
    (hhe : Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [34, 144] with [hL]
  all_goals
    have hlay := env.layout
    rw [hpre_2] at hpre_6
    have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
    have hM0 := saved_ok (ret := ret) (regs := regs) hlim hpre_5 hpre_4
    simp only [saved] at hM0
    have hA : Args env m top regs := ⟨hlim, hpre_11, hpre_10, ⟨hpre_6, hpre_7⟩, hpre_8, hpre_9⟩
  · exact empty hp hL hk hA _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hM0
  · have hn0 : (regs .x11).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    exact first hp hL hnQ hnO hnA hnR hnH hq ho hal' hres hhe hk hstop hpre_3 hA ((regs .x11).toNat - 1) _ _
      ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hM0, 0, by omega, rfl⟩

end Rv64mc.Proof.Layout.StackedBlocksT

/-- info: 'Rv64mc.Proof.Layout.StackedBlocksT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.StackedBlocksT.total
