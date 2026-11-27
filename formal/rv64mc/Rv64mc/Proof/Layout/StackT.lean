/-
  Rv64mc.Proof.Layout.StackT

  `verifier::layout::stack(kappas)` is total: called with the result's slot (`a0`, 32 bytes: the offsets'
  `Vec<Option<u64>>` header, then the `usize` log) and the kappas (`a1`, `a2`, words), it computes the blocks
  (`stacked_blocks`), their kappas (a vector of the blocks' count, `reserve`d, filled by a loop reading
  `kappas[block]`, each index checked), their offsets (`stack_offsets`), the zeroed `vec![None; kappas.len()]`
  (`try_allocate_in`), sets `offsets[block] = Some(offset)` for each block (a second loop, each index checked), and
  returns the offsets a vector of the kappas' length (`CloneT.ClonePostT` of 16-byte elements: `VecT`, its buffer
  fresh unless empty) and the log at least `MIN_STACKED_LOG = 16`, writing only the result's 32 bytes; or the run
  ends with the guest's abort (`AbortStop`) where a callee or a bounds check does. A safety-only contract (class D):
  the offsets' values are not stated.

  The precondition asks the result's slot a caller's (`Owned`), in a window and 8-byte aligned, and the kappas a
  block allocated before (`BufT`); at its one call site (`build_layout`) the slot is in the caller's frame and the
  kappas are `column_kappas`' vector.

  The body is cut at the join after `alloc` (instruction 86, `Inv86`), at the first loop's head (114, `L1`), before
  `stack_offsets` (136, `Inv136`), before `try_allocate_in` (142, `Inv142`), at the second loop's head (176, `L2`) and
  at the result's stores (202, `Fin`), each part its own declaration under the default heartbeats. The loops' stores
  go to blocks allocated since the entry (`store_ok`); their loads need only windows, so no part tracks the
  contents of the blocks, kappas or offsets.

  ## Main definitions

  * `PreT`, `PostT`, `SpecT`, `Slots`, `Saved`
  * `Inv86`, `L1`, `Inv136`, `Inv142`, `L2`, `Fin`: the states at the cuts

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.StackedBlocksT
import Rv64mc.Proof.Multilinear.StackOffsetsT
import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Stack

namespace Rv64mc.Proof.Layout.StackT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.ReserveT (ReserveSpecT)
open Rv64mc.Proof.Runtime.TryAllocateInT (TryAllocSpecT)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT)
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Gen.Verifier.Layout.Stack (Link tmpl)

/-- The total precondition: the result's 32 bytes a caller's, in a window and 8-byte aligned; the kappas (`a1`,
    `a2`) a block allocated before (`BufT`). -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) 32 ∧ InWin env (regs .x10) 32 ∧ (regs .x10).toNat % 8 = 0 ∧
    BufT env m (regs .x12) (regs .x11) 8

/-- The total postcondition: the offsets a vector of the kappas' length, its buffer fresh unless empty; the log at
    least `16`. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  ClonePostT env 16 regs m r' m' ∧ 16 ≤ (m'.getMem (regs .x10 + 24#64)).toNat

/-- **The total contract of `stack`**: it writes only the result's 32 bytes. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (Spec.Whir.SretOut 32) AbortStop

/-- The prologue's nine saved words in `M`, at `top - 8` down to `top - 72`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23

/-- The four saved registers the function does not save, the entry's. -/
def Saved (regs R : Reg → Word) : Prop :=
  R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- The slots kept by a memory that agrees from `top - 72` up to `top`. -/
theorem slots_keep {M X : MachineState} {top ret : Word} {regs : Reg → Word} (hlim : 128 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 72 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (hsl : Slots M top ret regs) : Slots X top ret regs := by
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 72 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := Runtime.CloneT.toNat_add_neg (t := top) hc (by omega)
      exact hk _ (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hsl
  exact ⟨(es _ 8 rfl (by omega) (by omega)).trans s1, (es _ 16 rfl (by omega) (by omega)).trans s2,
    (es _ 24 rfl (by omega) (by omega)).trans s3, (es _ 32 rfl (by omega) (by omega)).trans s4,
    (es _ 40 rfl (by omega) (by omega)).trans s5, (es _ 48 rfl (by omega) (by omega)).trans s6,
    (es _ 56 rfl (by omega) (by omega)).trans s7, (es _ 64 rfl (by omega) (by omega)).trans s8,
    (es _ 72 rfl (by omega) (by omega)).trans s9⟩

/-- The state at instruction 202, after the second loop: the offsets' block `P` of `x8` (the kappas' length)
    16-byte elements, fresh since the entry unless empty, its capacity `x10`, the log in `x20`. -/
def Fin (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551488#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x10 = regs .x12 ∧
    Saved regs R ∧ (regs .x12).toNat * 16 < 2 ^ 63 ∧
    ((regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x12).toNat ∧ (env.next m).toNat ≤ (R .x12).toNat ∧
      (R .x12).toNat + (regs .x12).toNat * 16 ≤ (env.next M).toNat ∧ (R .x12).toNat % 8 = 0)) ∧
    Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

/-- **The result's four stores** at `h`, a caller's 32 bytes in a window: the slots, the frame with the result as
    its `out`, the static data, the code and `NEXT` kept; the header's three words read back. -/
theorem hdr4 {env : Env} {m M : MachineState} {top ret h v0 v1 v2 v3 : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 128 ≤ top.toNat) (hh : regs .x10 = h) (hown : env.Owned m top h 32)
    (hwin : InWin env h 32) (hsl : Slots M top ret regs) (hF : env.Frame top Tactic.F m M) (hS : env.Static M)
    (hc : M.code = m.code) :
    let X := (((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2).setMem (h + 24#64) v3
    Slots X top ret regs ∧ env.Frame top (Spec.Whir.SretOut 32 regs m) m X ∧ env.Static X ∧ X.code = m.code ∧
      env.next X = env.next M ∧ X.getMem h = v0 ∧ X.getMem (h + 8#64) = v1 ∧ X.getMem (h + 16#64) = v2 ∧
      X.getMem (h + 24#64) = v3 := by
  intro X
  have hlay := env.layout
  have h32 := hown.2
  have hnm := hF.1
  have hnM := hF.2.1
  have hwin' := hwin
  unfold InWin at hwin'
  have e8 : (h + 8#64).toNat = h.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (h + 16#64).toNat = h.toNat + 16 := toNat_add_ofNat (by omega)
  have e24 : (h + 24#64).toNat = h.toNat + 24 := toNat_add_ofNat (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hnx : ∀ k, k ≤ 24 → ∀ b : Word, b.toNat = h.toNat + k → b ≠ env.nextAddr := fun k hk b hb e => by
    rw [e] at hb; rcases hwin' with h1 | h1 <;> omega
  have hout : ∀ k, k ≤ 24 → ∀ b : Word, b.toNat = h.toNat + k → Spec.Whir.SretOut 32 regs m b :=
    fun k hk b hb => by show InRange (regs .x10) 32 b; unfold InRange; rw [hh]; omega
  have hst : ∀ k, k ≤ 24 → ∀ b : Word, b.toNat = h.toNat + k →
      b.toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ b.toNat := fun k hk b hb => by
    rcases hwin' with h1 | h1 <;> omega
  refine ⟨slots_keep (by omega) (fun a h1 h2 => ?_) hsl, ?_, ?_, by simp only [X, MachineState.code_setMem]; exact hc,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hsep : h.toNat + 32 ≤ top.toNat - 72 ∨ top.toNat ≤ h.toNat := by rcases hown.1 with h3 | h3 <;> omega
    simp only [X]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega))]
  · simp only [X]
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_weaken hF)
      (hout 0 (by omega) _ rfl) (hnx 0 (by omega) _ rfl)) (hout 8 (by omega) _ e8) (hnx 8 (by omega) _ e8))
      (hout 16 (by omega) _ e16) (hnx 16 (by omega) _ e16)) (hout 24 (by omega) _ e24) (hnx 24 (by omega) _ e24)
  · simp only [X]
    exact Tactic.static_store (Tactic.static_store (Tactic.static_store (Tactic.static_store hS
      (hst 0 (by omega) _ rfl)) (hst 8 (by omega) _ e8)) (hst 16 (by omega) _ e16)) (hst 24 (by omega) _ e24)
  · simp only [X]
    rw [Tactic.next_setMem (hnx 24 (by omega) _ e24), Tactic.next_setMem (hnx 16 (by omega) _ e16),
      Tactic.next_setMem (hnx 8 (by omega) _ e8), Tactic.next_setMem (hnx 0 (by omega) _ rfl)]
  · simp only [X]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · simp only [X]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · simp only [X]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · simp only [X]
    rw [MachineState.getMem_setMem_eq]

set_option rv_sym.heap true in
/-- **The return**, from instruction 202: the log floored at `16`, the result's four words, the saved registers. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (Spec.Whir.SretOut 32) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hlim : env.stackLimit.toNat + 128 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hpre : PreT env regs m) :
    ∀ R M, Fin env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 202, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hR10, hsv, hn16, hP, hsl, hF, hS, hc⟩ := hI
  obtain ⟨hown, hwin, hal, -⟩ := hpre
  rw [h2] at hown
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hwin' := hwin
  unfold InWin at hwin'
  have := hown.2
  have hq : ∀ v : Word,
      env.Frame top (Spec.Whir.SretOut 32 regs m) m ((((M.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64)
        (R .x12)).setMem (regs .x10 + 16#64) (regs .x12)).setMem (regs .x10 + 24#64) v) ∧
      env.Static ((((M.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64) (R .x12)).setMem (regs .x10 + 16#64)
        (regs .x12)).setMem (regs .x10 + 24#64) v) ∧
      env.next ((((M.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64) (R .x12)).setMem (regs .x10 + 16#64)
        (regs .x12)).setMem (regs .x10 + 24#64) v) = env.next M ∧
      ClonePostT env 16 regs m (fun _ => 0#64) ((((M.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64)
        (R .x12)).setMem (regs .x10 + 16#64) (regs .x12)).setMem (regs .x10 + 24#64) v) := fun v => by
    obtain ⟨-, f, t, -, n, r0, r8, r16, -⟩ := hdr4 (v0 := regs .x12) (v1 := R .x12) (v2 := regs .x12) (v3 := v)
      hlim rfl hown hwin hsl hF hS hc
    refine ⟨f, t, n, Runtime.VecHdrT.post_ok (Runtime.MemsetT.InWin.sub hwin (Nat.le_refl _) (by omega)) hal r0
      r8 r16 ?_ hn16⟩
    exact hP.imp_right fun ⟨h1, h3, h4, h5⟩ => ⟨h1, h3, by rw [n]; omega, h5⟩
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR10 hsv)))
  have hnm := hF.1
  have hnM := hF.2.1
  have hsep : (regs .x10).toNat + 32 ≤ top.toNat - 72 ∨ top.toNat ≤ (regs .x10).toNat := by
    rcases hown.1 with h3 | h3 <;> omega
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hsl
  clear hF hS
  rv_introT hR
  rv_symT hp with [_hL]
  all_goals first
    | exact (hq _).1
    | exact (hq _).2.1
    | exact (hq _).2.2.2.1.2.1.2.2.1
    | exact (hq _).2.2.2.1.2.1.2.2.2

/-- One store into a block allocated since the entry keeps the slots, the frame, the static data, the code and
    `NEXT`. -/
theorem store_ok {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 128 ≤ top.toNat) (hsl : Slots M top ret regs) (hF : env.Frame top Tactic.F m M)
    (hS : env.Static M) (hc : M.code = m.code) (ha1 : (env.next m).toNat ≤ a.toNat)
    (ha2 : a.toNat + 8 ≤ (env.next M).toNat) :
    Slots (M.setMem a v) top ret regs ∧ env.Frame top Tactic.F m (M.setMem a v) ∧ env.Static (M.setMem a v) ∧
      (M.setMem a v).code = m.code ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  have hnM := hF.2.1
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at ha2; omega
  exact ⟨slots_keep (by omega) (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_fresh hF rfl ha1 (by omega), Tactic.static_store hS (.inl (by omega)),
    by rw [MachineState.code_setMem, hc], Tactic.next_setMem hne⟩

/-- The second loop's head (instruction 176) with `k + 1` blocks left: `x21` at the next block's column in the
    blocks' buffer `B`, `x22` at its offset in the offsets' buffer `O`, `x18` and `x13` the bytes left of each; the
    result's block `x12` as in `Fin`. -/
def L2 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (B O : Word) (nb k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551488#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x10 = regs .x12 ∧
    R .x14 = 1#64 ∧ Saved regs R ∧ (regs .x12).toNat * 16 < 2 ^ 63 ∧
    ((regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x12).toNat ∧ (env.next m).toNat ≤ (R .x12).toNat ∧
      (R .x12).toNat + (regs .x12).toNat * 16 ≤ (env.next M).toNat ∧ (R .x12).toNat % 8 = 0)) ∧
    k < nb ∧ 0x10000000 ≤ B.toNat ∧ B.toNat % 8 = 0 ∧ B.toNat + 8 * nb ≤ (env.next M).toNat ∧
    0x10000000 ≤ O.toNat ∧ O.toNat % 8 = 0 ∧ O.toNat + 8 * nb ≤ (env.next M).toNat ∧
    (R .x21).toNat = B.toNat + 8 * (nb - 1 - k) ∧ (R .x22).toNat = O.toNat + 8 * (nb - 1 - k) ∧
    (R .x18).toNat = 8 * (k + 1) ∧ (R .x13).toNat = 8 * (k + 1) ∧
    Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **The second loop**, from its head: `offsets[block] = Some(offset)` for each block, then `fin`. -/
theorem loop2 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needP : Nat} (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top B O : Word} {nb : Nat} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hnP : env.stackLimit.toNat + 128 + needP ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hfin : ∀ R M, Fin env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 202, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, L2 env m top ret regs B O nb k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 176, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (L2 env m top ret regs B O nb) fun k R M hI ih => ?_
  obtain ⟨hR2, hR8, hR9, hR10, hR14, hsv, hn16, hP, hk, hB1, hB8, hB2, hO1, hO8, hO2, h21, h22, h18, h13, hsl, hF, hS,
    hc⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hnm := hF.1
  have hnM := hF.2.1
  have hlim : env.stackLimit.toNat + 128 ≤ top.toNat := by omega
  have h8 := Runtime.CloneT.toNat_add_neg (t := R .x18) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have h8' := Runtime.CloneT.toNat_add_neg (t := R .x13) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR10 (And.intro hR14 hsv))))
  rv_introT hR
  rv_symT hp stop [182, 202] with [hL] using [hpb]
  · exact hfin _ _ ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, hn16, hP, hsl, hF, hS, hc_1⟩
  · have hb : (M.getMem (R .x21)).toNat < (regs .x12).toNat := by rw [BitVec.lt_def] at hc; exact hc
    clear hc
    obtain ⟨hP1, hP2, hP3, hP4⟩ := hP.resolve_left (by omega)
    have hsh : (M.getMem (R .x21) <<< 4).toNat = 16 * (M.getMem (R .x21)).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have hA : (R .x12 + M.getMem (R .x21) <<< 4).toNat = (R .x12).toNat + 16 * (M.getMem (R .x21)).toNat := by
      rw [BitVec.toNat_add, hsh]; omega
    have hA8 : (R .x12 + M.getMem (R .x21) <<< 4 + 8#64).toNat =
        (R .x12).toNat + 16 * (M.getMem (R .x21)).toNat + 8 := by
      rw [toNat_add_ofNat (by omega), hA]
    obtain ⟨s1, f1, t1, c1, n1⟩ := store_ok (a := R .x12 + M.getMem (R .x21) <<< 4) (v := 1#64) hlim hsl hF hS hc_1
      (by omega) (by omega)
    obtain ⟨s2, f2, t2, c2, n2⟩ := store_ok (a := R .x12 + M.getMem (R .x21) <<< 4 + 8#64)
      (v := M.getMem (R .x22)) hlim s1 f1 t1 c1 (by rw [hA8]; omega) (by rw [hA8, n1]; omega)
    have hP' : (regs .x12).toNat = 0 ∨ (0x10000000 ≤ (R .x12).toNat ∧ (env.next m).toNat ≤ (R .x12).toNat ∧
        (R .x12).toNat + (regs .x12).toNat * 16 ≤ (env.next (((M.setMem (R .x12 + M.getMem (R .x21) <<< 4) 1#64).setMem
          (R .x12 + M.getMem (R .x21) <<< 4 + 8#64) (M.getMem (R .x22))))).toNat ∧ (R .x12).toNat % 8 = 0) :=
      .inr ⟨hP1, hP2, by rw [n2, n1]; exact hP3, hP4⟩
    clear hsl hF hS s1 f1 t1 c1
    rv_symT hp stop [176, 202] with [hL]
    · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h8]; simp; omega))
      refine ih (k - 1) _ _ (by omega) ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, hn16, hP', by omega, hB1, hB8,
        by rw [n2, n1]; exact hB2, hO1, hO8, by rw [n2, n1]; exact hO2, ?_, ?_, ?_, ?_, s2, f2, t2, c2⟩ <;>
        simp only [Tactic.rf]
      · rw [toNat_add_ofNat (by omega)]; omega
      · rw [toNat_add_ofNat (by omega)]; omega
      · rw [h8]; omega
      · rw [h8']; omega
    · exact hfin _ _ ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, hn16, hP', s2, f2, t2, c2⟩

/-- `try_allocate_in`'s capacity word in the result at `sp + 0x18`. -/
theorem cap_slot (top : Word) : taCapAt (top + 18446744073709551512#64) = top + 18446744073709551520#64 := by
  unfold taCapAt; rw [BitVec.add_assoc]; rfl

/-- `try_allocate_in`'s pointer word in the result at `sp + 0x18`. -/
theorem ptr_slot (top : Word) : taPtrAt (top + 18446744073709551512#64) = top + 18446744073709551528#64 := by
  unfold taPtrAt; rw [BitVec.add_assoc]; rfl

/-- The state at instruction 142, after `stack_offsets`: its result at `sp + 0x18` a vector of `nb` (the blocks'
    count, `x19`) words, the blocks' buffer `B` in `x21`. -/
def Inv142 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (B : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551488#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x21 = B ∧
    R .x18 = R .x19 <<< 3 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ Saved regs R ∧ (R .x19).toNat * 8 < 2 ^ 63 ∧
    ((R .x19).toNat = 0 ∨ (0x10000000 ≤ B.toNat ∧ B.toNat % 8 = 0 ∧ B.toNat + 8 * (R .x19).toNat ≤ (env.next M).toNat)) ∧
    VecT env M (top + 18446744073709551512#64) 8 ∧ vecLen M (top + 18446744073709551512#64) = R .x19 ∧
    Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **From instruction 142**: `vec![None; kappas.len()]` (`try_allocate_in`), then the second loop or `fin`. -/
theorem at142 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needT needH : Nat} (hta : TryAllocSpecT env p L.tryAllocateInInVerifier.idx needT)
    (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top B : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hnT : env.stackLimit.toNat + 128 + needT ≤ top.toNat) (hnH : env.stackLimit.toNat + 128 + needH ≤ top.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hfin : ∀ R M, Fin env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 202, ret, top⟩ :: rest, R, M⟩)
    (hl2 : ∀ O nb k R M, L2 env m top ret regs B O nb k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 176, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv142 env m top ret regs B R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 142, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hR21, hR18, hR22, hR23, hsv, hn8, hB, hV, hlen, hsl, hF, hS, hc⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hnm := hF.1
  have hnM := hF.2.1
  have hlim : env.stackLimit.toNat + 128 ≤ top.toNat := by omega
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 128 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e128 := g 18446744073709551488#64 128 rfl (by omega)
  have e104 := g 18446744073709551512#64 104 rfl (by omega)
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR21 (And.intro hR18 (And.intro hR22
    (And.intro hR23 hsv))))))
  rv_introT hR
  rv_symT hp stop [176, 202] with [hL] using [hta, hhe]
  all_goals
    obtain ⟨hn16, hok⟩ := hret1_16 hc_2
    rw [show (16#64 : Word).toNat = 16 from rfl, cap_slot, ptr_slot] at hok
    rw [show (16#64 : Word).toNat = 16 from rfl] at hn16
    have hcap : m1.getMem (top + 18446744073709551520#64) = regs .x12 := by
      rcases hok with ⟨h0, h1⟩ | ⟨-, h1, -⟩
      · rw [h1]; exact (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega) : (0#64 : Word) = regs .x12)
      · exact h1
    have hP : (regs .x12).toNat = 0 ∨ (0x10000000 ≤ (m1.getMem (top + 18446744073709551528#64)).toNat ∧
        (env.next m).toNat ≤ (m1.getMem (top + 18446744073709551528#64)).toNat ∧
        (m1.getMem (top + 18446744073709551528#64)).toNat + (regs .x12).toNat * 16 ≤ (env.next m1).toNat ∧
        (m1.getMem (top + 18446744073709551528#64)).toNat % 8 = 0) := by
      rcases hok with ⟨h0, -⟩ | ⟨-, -, hfr, h8⟩
      · exact .inl (by omega)
      · unfold Env.Fresh at hfr; exact .inr ⟨by omega, by omega, by omega, h8⟩
    have hF1 : env.Frame top Tactic.F m m1 := hF.trans hret1_14 (by rw [e128]; omega) fun b hb => Or.inl (by
      change InRange (top + 18446744073709551512#64) tryAllocBytes b at hb
      unfold InRange tryAllocBytes at hb; rw [e104] at hb; omega)
    have hsl1 : Slots m1 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep1_1 a (BitVec.le_def.2 (by rw [e128]; omega)) fun hb => by
        change InRange (top + 18446744073709551512#64) tryAllocBytes a at hb
        unfold InRange tryAllocBytes at hb; rw [e104] at hb; omega) hsl
    have hc1 := hret1_18.trans hc_1
    have hnm1 := hret1_14.1
  · exact hfin _ _ ⟨rfl, rfl, rfl, hcap, ⟨rfl, rfl, rfl, rfl⟩, hn16, hP, hsl1, hF1, hret1_15, hc1⟩
  · have hnb : (R .x19).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    obtain ⟨hB1, hB8, hB2⟩ := hB.resolve_left hnb
    have hb := hV.2.1.2.2.1
    have hl := hV.2.2
    rw [hlen] at hl
    rw [vecCap_eq] at hl
    have hp8 : top + 18446744073709551512#64 + 8#64 = top + 18446744073709551520#64 := by rw [BitVec.add_assoc]; rfl
    have hp16 : top + 18446744073709551512#64 + 16#64 = top + 18446744073709551528#64 := by
      rw [BitVec.add_assoc]; rfl
    rw [rvCapAt_eq, rvPtrAt_eq, hp8] at hb
    rw [vecLen_eq, hp16] at hlen
    obtain ⟨hO1, hO2, hO8⟩ : 0x10000000 ≤ (M.getMem (top + 18446744073709551520#64)).toNat ∧
        (M.getMem (top + 18446744073709551520#64)).toNat + 8 * (R .x19).toNat ≤ (env.next M).toNat ∧
        (M.getMem (top + 18446744073709551520#64)).toNat % 8 = 0 := by
      rcases hb with h0 | ⟨h1, h2, h3⟩
      · omega
      · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
    have hx3 : (R .x19 <<< 3).toNat = 8 * (R .x19).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    refine hl2 (M.getMem (top + 18446744073709551520#64)) (R .x19).toNat ((R .x19).toNat - 1) _ _
      ⟨rfl, rfl, rfl, hcap, rfl, ⟨rfl, rfl, rfl, rfl⟩, hn16, hP, by omega, hB1, hB8, by omega, hO1, hO8, by omega,
        ?_, ?_, ?_, ?_, hsl1, hF1, hret1_15, hc1⟩ <;> simp only [Tactic.rf]
    · omega
    · omega
    · rw [hx3]; omega
    · rw [hlen, hx3]; omega

/-- The state at instruction 136, after the first loop: the blocks' kappas a buffer `x11` of `nb` (the blocks' count,
    `x19`, also in `x12`) words. -/
def Inv136 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (B : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551488#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x21 = B ∧
    R .x18 = R .x19 <<< 3 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x12 = R .x19 ∧ Saved regs R ∧
    (R .x19).toNat * 8 < 2 ^ 63 ∧
    ((R .x19).toNat = 0 ∨ (0x10000000 ≤ B.toNat ∧ B.toNat % 8 = 0 ∧ B.toNat + 8 * (R .x19).toNat ≤ (env.next M).toNat)) ∧
    BufT env M (R .x19) (R .x11) 8 ∧ Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧
    M.code = m.code

set_option rv_sym.heap true in
/-- **From instruction 136**: the blocks' offsets (`stack_offsets`), then `at142`. -/
theorem at136 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needO : Nat} (hso : Multilinear.StackOffsetsT.SpecT env p L.stackOffsets.idx needO)
    {Q : State rvIsa → Prop} {ret top B : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hnO : env.stackLimit.toNat + 128 + needO ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h142 : ∀ R M, Inv142 env m top ret regs B R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 142, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv136 env m top ret regs B R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 136, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hR21, hR18, hR22, hR23, hR12, hsv, hn8, hB, hbuf, hsl, hF, hS, hc⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hnm := hF.1
  have hnM := hF.2.1
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 128 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e128 := g 18446744073709551488#64 128 rfl (by omega)
  have e104 := g 18446744073709551512#64 104 rfl (by omega)
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR21 (And.intro hR18 (And.intro hR22
    (And.intro hR23 (And.intro hR12 hsv)))))))
  rv_introT hR
  rv_symT hp stop [142] with [hL] using [hso]
  have hn1 := hret1_14.1
  have hF1 : env.Frame top Tactic.F m m1 := hF.trans hret1_14 (by rw [e128]; omega) fun b hb => Or.inl (by
    change InRange (top + 18446744073709551512#64) 32 b at hb
    unfold InRange at hb; rw [e104] at hb; omega)
  have hsl1 : Slots m1 top ret regs := slots_keep (by omega) (fun a h1 h2 => hret1_14.2.2 a fun hw => by
    rcases hw with hw | hw | hw | hw
    · rw [e128] at hw; omega
    · have := hret1_14.2.1; omega
    · rw [hw] at h1; omega
    · change InRange (top + 18446744073709551512#64) 32 a at hw
      unfold InRange at hw; rw [e104] at hw; omega) hsl
  have hB' : (R .x19).toNat = 0 ∨ (0x10000000 ≤ B.toNat ∧ B.toNat % 8 = 0 ∧
      B.toNat + 8 * (R .x19).toNat ≤ (env.next m1).toNat) := hB.imp id fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩
  exact h142 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, hn8, hB',
    ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩, hret1_22, hsl1, hF1, hret1_15, hret1_24.trans hc⟩

/-- The first loop's head (instruction 114) with `k + 1` blocks left: `x14` at the next block's column in the blocks'
    buffer `B`, `x13` at the next free word of the blocks' kappas' buffer `P` (`x11`), `x12` the words written,
    `x15` the blocks left. -/
def L1 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (B P : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551488#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x20 = regs .x11 ∧ R .x21 = B ∧
    R .x18 = R .x19 <<< 3 ∧ R .x11 = P ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ Saved regs R ∧
    (R .x19).toNat * 8 < 2 ^ 63 ∧ k < (R .x19).toNat ∧
    0x10000000 ≤ B.toNat ∧ B.toNat % 8 = 0 ∧ B.toNat + 8 * (R .x19).toNat ≤ (env.next M).toNat ∧
    (env.next m).toNat ≤ P.toNat ∧ P.toNat % 8 = 0 ∧ P.toNat + 8 * (R .x19).toNat ≤ (env.next M).toNat ∧
    (R .x12).toNat = (R .x19).toNat - 1 - k ∧ (R .x13).toNat = P.toNat + 8 * ((R .x19).toNat - 1 - k) ∧
    (R .x14).toNat = B.toNat + 8 * ((R .x19).toNat - 1 - k) ∧ (R .x15).toNat = k + 1 ∧
    Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **The first loop**, from its head: `block_kappas.push(kappas[block])` for each block, then `at136`. -/
theorem loop1 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needP : Nat} (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top B P : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hnP : env.stackLimit.toNat + 128 + needP ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hK : BufT env m (regs .x12) (regs .x11) 8)
    (h136 : ∀ R M, Inv136 env m top ret regs B R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 136, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, L1 env m top ret regs B P k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (L1 env m top ret regs B P) fun k R M hI ih => ?_
  obtain ⟨hR2, hR8, hR9, hR20, hR21, hR18, hR11, hR22, hR23, hsv, hn8, hk, hB1, hB8, hB2, hP1, hP8, hP2, h12, h13,
    h14, h15, hsl, hF, hS, hc⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hnm := hF.1
  have hnM := hF.2.1
  have hlim : env.stackLimit.toNat + 128 ≤ top.toNat := by omega
  have h1 := Runtime.CloneT.toNat_add_neg (t := R .x15) (c := 18446744073709551615#64) (k := 1) rfl (by omega)
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR20 (And.intro hR21 (And.intro hR18
    (And.intro hR11 (And.intro hR22 (And.intro hR23 hsv))))))))
  rv_introT hR
  rv_symT hp stop [118] with [hL] using [hpb]
  have hb : (M.getMem (R .x14)).toNat < (regs .x12).toNat := by
    rw [BitVec.lt_def] at hc; exact hc
  clear hc
  obtain ⟨hK1, hK2, hK8⟩ : 0x10000000 ≤ (regs .x11).toNat ∧
      (regs .x11).toNat + 8 * (regs .x12).toNat ≤ (env.next m).toNat ∧ (regs .x11).toNat % 8 = 0 := by
    rcases hK with h | ⟨h1, h2, h3⟩
    · omega
    · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
  have hsh : (M.getMem (R .x14) <<< 3).toNat = 8 * (M.getMem (R .x14)).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hA : (regs .x11 + M.getMem (R .x14) <<< 3).toNat = (regs .x11).toNat + 8 * (M.getMem (R .x14)).toNat := by
    rw [BitVec.toNat_add, hsh]; omega
  have hst := fun v => store_ok (a := R .x13) (v := v) hlim hsl hF hS hc_1 (by omega) (by omega)
  have x1 : (R .x12 + 1#64).toNat = (R .x12).toNat + 1 := toNat_add_ofNat (by omega)
  have x8 : (R .x13 + 8#64).toNat = (R .x13).toNat + 8 := toNat_add_ofNat (by omega)
  have x8' : (R .x14 + 8#64).toNat = (R .x14).toNat + 8 := toNat_add_ofNat (by omega)
  clear hsl hF hS
  rv_symT hp stop [114, 136] with [hL]
  · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h1]; simp; omega))
    refine ih (k - 1) _ _ (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_, hB1,
      hB8, ?_, hP1, hP8, ?_, ?_, ?_, ?_, ?_, (hst _).1, (hst _).2.1, (hst _).2.2.1, (hst _).2.2.2.1⟩ <;>
      simp only [Tactic.rf]
    all_goals first
      | exact hn8
      | (rw [(hst _).2.2.2.2]; omega)
      | (rw [x1]; omega)
      | (rw [x8]; omega)
      | (rw [x8']; omega)
      | (rw [h1]; omega)
      | omega
  · have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; rw [h1] at this; simp at this; omega
    subst hk0
    refine h136 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, (hst _).1, (hst _).2.1,
      (hst _).2.2.1, (hst _).2.2.2.1⟩ <;> simp only [Tactic.rf]
    · exact BitVec.eq_of_toNat_eq (by rw [x1]; omega)
    · exact hn8
    · exact .inr ⟨hB1, hB8, by rw [(hst _).2.2.2.2]; omega⟩
    · exact .inr ⟨by omega, by unfold Env.Live; rw [(hst _).2.2.2.2]; omega, hP8⟩

/-- The header `(c, P, 0)` stored at `sp + 0x18`. -/
abbrev hdr (M : MachineState) (top c P : Word) : MachineState :=
  ((M.setMem (top + 18446744073709551512#64) c).setMem (top + 18446744073709551520#64) P).setMem
    (top + 18446744073709551528#64) 0#64

/-- **The blocks' kappas' header built**: a vector's of words with no elements over `P` (none when `c = 0`), with
    `reserve`'s buffer condition; the slots, the frame, the static data, the code and `NEXT` kept. -/
theorem hdr_ok {env : Env} {m M : MachineState} {top ret c P : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 128 ≤ top.toNat) (h16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (hsl : Slots M top ret regs) (hF : env.Frame top Tactic.F m M) (hS : env.Static M) (hc : M.code = m.code)
    (hc8 : c.toNat * 8 < 2 ^ 63)
    (hP : c.toNat = 0 ∨ ((env.next m).toNat ≤ P.toNat ∧ P.toNat % 8 = 0 ∧ P.toNat + 8 * c.toNat ≤ (env.next M).toNat)) :
    VecT env (hdr M top c P) (top + 18446744073709551512#64) 8 ∧
      (((hdr M top c P).getMem (rvCapAt (top + 18446744073709551512#64))).toNat = 0 ∨
        env.Live (hdr M top c P) ((hdr M top c P).getMem (rvPtrAt (top + 18446744073709551512#64)))
          (((hdr M top c P).getMem (rvCapAt (top + 18446744073709551512#64))).toNat * 8)) ∧
      vecCap (hdr M top c P) (top + 18446744073709551512#64) = c ∧
      vecPtr (hdr M top c P) (top + 18446744073709551512#64) = P ∧
      vecLen (hdr M top c P) (top + 18446744073709551512#64) = 0#64 ∧
      Slots (hdr M top c P) top ret regs ∧ env.Frame top Tactic.F m (hdr M top c P) ∧ env.Static (hdr M top c P) ∧
      (hdr M top c P).code = m.code ∧ env.next (hdr M top c P) = env.next M := by
  have hlay := env.layout
  have := hW.top_le
  have := hW.next_ge
  have hnM := hF.2.1
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 128 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e104 := g 18446744073709551512#64 104 rfl (by omega)
  have e96 := g 18446744073709551520#64 96 rfl (by omega)
  have e88 := g 18446744073709551528#64 88 rfl (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have p8 : top + 18446744073709551512#64 + 8#64 = top + 18446744073709551520#64 := by rw [BitVec.add_assoc]; rfl
  have p16 : top + 18446744073709551512#64 + 16#64 = top + 18446744073709551528#64 := by rw [BitVec.add_assoc]; rfl
  have r0 : (hdr M top c P).getMem (top + 18446744073709551512#64) = c := by
    simp only [hdr]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r8 : (hdr M top c P).getMem (top + 18446744073709551520#64) = P := by
    simp only [hdr]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have r16 : (hdr M top c P).getMem (top + 18446744073709551528#64) = 0#64 := by
    simp only [hdr]; rw [MachineState.getMem_setMem_eq]
  have hN : env.next (hdr M top c P) = env.next M := by
    simp only [hdr]
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
  have hcap : vecCap (hdr M top c P) (top + 18446744073709551512#64) = c := by rw [vecCap_eq, r0]
  have hptr : vecPtr (hdr M top c P) (top + 18446744073709551512#64) = P := by rw [vecPtr_eq, p8, r8]
  have hlen : vecLen (hdr M top c P) (top + 18446744073709551512#64) = 0#64 := by rw [vecLen_eq, p16, r16]
  have hrc : (hdr M top c P).getMem (rvCapAt (top + 18446744073709551512#64)) = c := by rw [rvCapAt_eq, r0]
  have hrp : (hdr M top c P).getMem (rvPtrAt (top + 18446744073709551512#64)) = P := by rw [rvPtrAt_eq, p8, r8]
  have hbuf : BufT env (hdr M top c P) c P 8 :=
    hP.imp_right fun ⟨h1, h2, h3⟩ => ⟨by omega, by unfold Env.Live; rw [hN]; omega, h2⟩
  refine ⟨⟨.inr ⟨by omega, by simp only [Layouts.Vec.byteSize]; omega⟩,
    ⟨.inr ⟨by omega, by simp only [Layouts.RawVecInner.byteSize]; omega⟩, by omega, by rw [hrc, hrp]; exact hbuf,
      by rw [hrc]; exact hc8⟩, by rw [hlen, hcap]; simp⟩, by rw [hrc, hrp]; exact hbuf.live, hcap, hptr, hlen,
    slots_keep (by omega) (fun a h1 h2 => by
      simp only [hdr]
      rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        MachineState.getMem_setMem_ne (ne _ _ (by omega))]) hsl, ?_, ?_, by simp only [hdr, MachineState.code_setMem]; exact hc, hN⟩
  · exact Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot hF (by omega) (by omega)) (by omega) (by omega))
      (by omega) (by omega)
  · exact Env.static_setMem_stack (Env.static_setMem_stack (Env.static_setMem_stack hS (by omega)) (by omega))
      (by omega)

/-- The state at instruction 86, after `alloc`: the blocks' buffer `B` (`x21`) of `nb` (`x19`) columns, the blocks'
    kappas' block `x10` of `nb` words (none when `nb = 0`), its capacity `x11`. -/
def Inv86 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (B : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551488#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x20 = regs .x11 ∧ R .x21 = B ∧
    R .x18 = R .x19 <<< 3 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ Saved regs R ∧
    (R .x19).toNat * 8 < 2 ^ 63 ∧ (R .x11).toNat = (R .x19).toNat ∧
    ((R .x19).toNat = 0 ∨ (0x10000000 ≤ B.toNat ∧ B.toNat % 8 = 0 ∧ B.toNat + 8 * (R .x19).toNat ≤ (env.next M).toNat ∧
      (env.next m).toNat ≤ (R .x10).toNat ∧ (R .x10).toNat % 8 = 0 ∧
      (R .x10).toNat + 8 * (R .x19).toNat ≤ (env.next M).toNat)) ∧
    Slots M top ret regs ∧ env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **From instruction 86**: the blocks' kappas' header built and `reserve`d, then the first loop or `at136`. -/
theorem at86 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needR : Nat} (hre : ReserveSpecT env 8 8 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top B : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hnR : env.stackLimit.toNat + 128 + needR ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h136 : ∀ R M, Inv136 env m top ret regs B R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 136, ret, top⟩ :: rest, R, M⟩)
    (hl1 : ∀ P k R M, L1 env m top ret regs B P k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv86 env m top ret regs B R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 86, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hR2, hR8, hR9, hR20, hR21, hR18, hR22, hR23, hsv, hn8, h11, hBP, hsl, hF, hS, hc⟩ := hI
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hnm := hF.1
  have hnM := hF.2.1
  have hlim : env.stackLimit.toNat + 128 ≤ top.toNat := by omega
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 128 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e128 := g 18446744073709551488#64 128 rfl (by omega)
  have e104 := g 18446744073709551512#64 104 rfl (by omega)
  have e96 := g 18446744073709551520#64 96 rfl (by omega)
  have e88 := g 18446744073709551528#64 88 rfl (by omega)
  have hR := And.intro hR2 (And.intro hR8 (And.intro hR9 (And.intro hR20 (And.intro hR21 (And.intro hR18
    (And.intro hR22 (And.intro hR23 hsv)))))))
  have hP0 : (R .x11).toNat = 0 ∨ ((env.next m).toNat ≤ (R .x10).toNat ∧ (R .x10).toNat % 8 = 0 ∧
      (R .x10).toNat + 8 * (R .x11).toNat ≤ (env.next M).toNat) := by
    rcases hBP with h0 | ⟨-, -, -, h1, h2, h3⟩
    · exact .inl (by omega)
    · exact .inr ⟨h1, h2, by omega⟩
  obtain ⟨hV3, hlv3, hcap3, hptr3, hlen3, hsl3, hF3, hS3, hc3, hN3⟩ :=
    hdr_ok (ret := ret) (regs := regs) hlim h16 hW hsl hF hS hc (by omega) hP0
  simp only [hdr] at hV3 hlv3 hcap3 hptr3 hlen3 hsl3 hF3 hS3 hc3 hN3
  clear hP0
  have hle3 := hV3.2.2
  rv_introT hR
  rv_symT hp stop [114, 136] with [hL] using [hre]
  all_goals
    have p8 : top + 18446744073709551512#64 + 8#64 = top + 18446744073709551520#64 := by rw [BitVec.add_assoc]; rfl
    have p16 : top + 18446744073709551512#64 + 16#64 = top + 18446744073709551528#64 := by
      rw [BitVec.add_assoc]; rfl
    obtain ⟨-, hp1⟩ := hret1_17 (by rw [hcap3, hlen3]; simp only [BitVec.toNat_ofNat]; omega)
    have p1 : m1.getMem (top + 18446744073709551520#64) = R .x10 := by rw [← p8, ← vecPtr_eq, hp1, hptr3]
    have l1 : m1.getMem (top + 18446744073709551528#64) = 0#64 := by rw [← p16, ← vecLen_eq, hret1_16, hlen3]
    have hgo' : ∀ b : Word, GrowOut (updReg (Tactic.rf (R .x0) L.s4.hi (top + 18446744073709551488#64) (R .x3) (R .x4)
        (R .x5) (R .x6) (R .x7) (regs .x12) (regs .x10) (top + 18446744073709551512#64) (R .x19) (R .x12) (R .x13)
        (R .x14) (R .x15) (R .x16) (R .x17) (R .x19 <<< 3) (R .x19) (regs .x11) B (regs .x22) (regs .x23) (regs .x24)
        (regs .x25) (regs .x26) (regs .x27) (R .x28) (R .x29) (R .x30) (R .x31)) .x1 (L.base + 200#64))
        (hdr M top (R .x11) (R .x10)) b → b.toNat = top.toNat - 104 ∨ b.toNat = top.toNat - 96 := fun b hb => by
      unfold GrowOut at hb
      rw [rvCapAt_eq, rvPtrAt_eq] at hb
      rcases hb with hb | hb
      · exact .inl (by rw [hb]; exact e104)
      · refine .inr (by rw [hb]; exact (congrArg BitVec.toNat p8).trans e96)
    have hF1 : env.Frame top Tactic.F m m1 := hF3.trans hret1_14 (by rw [e128]; omega) fun b hb => Or.inl (by
      rcases hgo' b hb with h | h <;> rw [h] <;> omega)
    have hsl1 : Slots m1 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep1_1 a (BitVec.le_def.2 (by rw [e128]; omega)) fun hb => by
        rcases hgo' a hb with h | h <;> omega) hsl3
    have hc1 := hret1_25.trans hc3
    have hn1 := hret1_14.1
    rw [hN3] at hn1
    have hS1 := hret1_15
    clear keep1_1 keep1_2 hret1_14 hret1_15 hret1_16 hret1_17 hret1_18 hret1_19 hret1_20 hret1_21 hret1_22 hret1_23
      hret1_24 hret1_25 hgo' hV3 hlv3 hle3 hsl3 hF3 hS3 hc3 hp1
  · refine h136 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ⟨rfl, rfl, rfl, rfl⟩, hn8, ?_, ?_, hsl1, hF1, hS1,
      hc1⟩ <;> simp only [Tactic.rf]
    · rw [l1, hc]
    · exact .inl (by rw [hc]; rfl)
    · exact .inl (by rw [hc]; rfl)
  · have hnb : (R .x19).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    obtain ⟨hB1, hB8, hB2, hP1, hP8, hP2⟩ := hBP.resolve_left hnb
    refine hl1 (m1.getMem (top + 18446744073709551520#64)) ((R .x19).toNat - 1) _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, hn8, ?_, hB1, hB8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsl1, hF1, hS1,
      hc1⟩ <;> try simp only [Tactic.rf]
    · omega
    · omega
    · rw [p1]; exact hP1
    · rw [p1]; exact hP8
    · rw [p1]; omega
    · rw [l1]; simp
    · rw [l1, p1]; simp
    · omega
    · omega

/-- The prologue's nine saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)

/-- The prologue's stores: the slots, the frame, the static data and the code. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 128 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) :
    Slots (saved m top ret regs) top ret regs ∧ env.Frame top Tactic.F m (saved m top ret regs) ∧
      env.Static (saved m top ret regs) ∧ (saved m top ret regs).code = m.code := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 128 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e1 := g 18446744073709551608#64 8 rfl (by omega)
  have e2 := g 18446744073709551600#64 16 rfl (by omega)
  have e3 := g 18446744073709551592#64 24 rfl (by omega)
  have e4 := g 18446744073709551584#64 32 rfl (by omega)
  have e5 := g 18446744073709551576#64 40 rfl (by omega)
  have e6 := g 18446744073709551568#64 48 rfl (by omega)
  have e7 := g 18446744073709551560#64 56 rfl (by omega)
  have e8 := g 18446744073709551552#64 64 rfl (by omega)
  have e9 := g 18446744073709551544#64 72 rfl (by omega)
  refine ⟨?_, ?_, ?_, by simp only [saved, MachineState.code_setMem]⟩
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9] at h'; omega)])
  · simp only [saved]
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Env.Frame.refl hnx)
  · simp only [saved]
    repeat (first | refine Env.static_setMem_stack ?_ (by omega) | exact hS)

set_option rv_sym.heap true in
/-- **`stack` is total**, with 128 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needB needH needA needR needO needT needP : Nat} (hnB : 128 + needB ≤ need) (hnH : 128 + needH ≤ need)
    (hnA : 128 + needA ≤ need) (hnR : 128 + needR ≤ need) (hnO : 128 + needO ≤ need) (hnT : 128 + needT ≤ need)
    (hnP : 128 + needP ≤ need)
    (hsb : StackedBlocksT.SpecT env p L.stackedBlocks.idx needB) (hhe : Aborts env p L.handleError.idx needH)
    (hal : AllocSpecT env p L.alloc.idx needA) (hre : ReserveSpecT env 8 8 p L.reserve.idx needR)
    (hso : Multilinear.StackOffsetsT.SpecT env p L.stackOffsets.idx needO)
    (hta : TryAllocSpecT env p L.tryAllocateInInVerifier.idx needT)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [86] with [hL] using [hsb, hhe, hal']
  all_goals
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 128 ≤ top.toNat := by omega
    have := hpre_12.nextAddr_ge
    have hW1 := hpre_12.heapEnd_le
    have hge := hpre_12.next_ge
    have hpre : PreT env regs m := ⟨⟨hpre_6, hpre_7⟩, hpre_8, hpre_9, hpre_10⟩
    obtain ⟨hsl0, hF0, hS0, hc0⟩ := saved_ok (ret := ret) (regs := regs) hlim hpre_5 hpre_4
    simp only [saved] at hsl0 hF0 hS0 hc0
    have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 128 → (top + c).toNat = top.toNat - k :=
      fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
    have e128 := g 18446744073709551488#64 128 rfl (by omega)
    have hF1 : env.Frame top Tactic.F m m1 := hF0.trans hret1_14 (by rw [e128]; omega) fun b hb => Or.inl (by
      change InRange (top + 18446744073709551488#64) Layouts.Vec.byteSize b at hb
      unfold InRange Layouts.Vec.byteSize at hb; rw [e128] at hb; omega)
    have hsl1 : Slots m1 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep1_1 a (BitVec.le_def.2 (by rw [e128]; omega)) fun hb => by
        change InRange (top + 18446744073709551488#64) Layouts.Vec.byteSize a at hb
        unfold InRange Layouts.Vec.byteSize at hb; rw [e128] at hb; omega) hsl0
    have p8 : top + 18446744073709551488#64 + 8#64 = top + 18446744073709551496#64 := by rw [BitVec.add_assoc]; rfl
    have p16 : top + 18446744073709551488#64 + 16#64 = top + 18446744073709551504#64 := by
      rw [BitVec.add_assoc]; rfl
    have hl := hret1_21
    rw [vecLen_eq, vecCap_eq, p16] at hl
    have hcb := hret1_20
    rw [rvCapAt_eq] at hcb
    have hb := hret1_19
    rw [rvCapAt_eq, rvPtrAt_eq, p8] at hb
    have hn8 : (m1.getMem (top + 18446744073709551504#64)).toNat * 8 < 2 ^ 63 := by omega
    have hB : (m1.getMem (top + 18446744073709551504#64)).toNat = 0 ∨
        (0x10000000 ≤ (m1.getMem (top + 18446744073709551496#64)).toNat ∧
          (m1.getMem (top + 18446744073709551496#64)).toNat % 8 = 0 ∧
          (m1.getMem (top + 18446744073709551496#64)).toNat + 8 * (m1.getMem (top + 18446744073709551504#64)).toNat ≤
            (env.next m1).toNat) := by
      rcases hb with h0 | ⟨h1, h2, h3⟩
      · exact .inl (by omega)
      · unfold Env.Live at h2; exact .inr ⟨h1, h3, by omega⟩
    have hsh : (m1.getMem (top + 18446744073709551504#64) <<< 3).toNat =
        8 * (m1.getMem (top + 18446744073709551504#64)).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have hnm1 := hret1_14.1
    have hnm0 := hF0.1
    have hc1 := hret1_23.trans hc0
    have hfin := fin hp hL hk hlim hpre_12 hpre_11 hpre_2 hpre
    have h86 := at86 (B := m1.getMem (top + 18446744073709551496#64)) hp hL hre hstop (by omega) hpre_12 hpre_11
      (at136 hp hL hso hstop (by omega) hpre_12 hpre_11
        (at142 hp hL hta hhe hstop (by omega) (by omega) hpre_12 hpre_11 hfin
          fun O nb k R M h => loop2 (B := m1.getMem (top + 18446744073709551496#64)) (O := O) (nb := nb) hp hL hpb
            hstop (by omega) hpre_12 hpre_11 hfin k R M h))
      fun P k R M h => loop1 (P := P) hp hL hpb hstop (by omega) hpre_12 hpre_11 hpre_10
        (at136 hp hL hso hstop (by omega) hpre_12 hpre_11
          (at142 hp hL hta hhe hstop (by omega) (by omega) hpre_12 hpre_11 hfin
            fun O nb k R M h => loop2 (O := O) (nb := nb) hp hL hpb hstop (by omega) hpre_12 hpre_11 hfin k R M h))
        k R M h
  · have h0 : (m1.getMem (top + 18446744073709551504#64)).toNat = 0 := by
      have := congrArg BitVec.toNat hc; rw [hsh] at this; simp at this; omega
    exact h86 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, hn8, by simp only [Tactic.rf]; simp; omega,
      .inl h0, hsl1, hF1, hret1_15, hc1⟩
  · rw [hsh]; omega
  · have hF2 : env.Frame top Tactic.F m m2 := hF1.trans hret2_14 (by rw [e128]; omega) fun b hb => hb.elim
    have hsl2 : Slots m2 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep2_1 a (BitVec.le_def.2 (by rw [e128]; omega))) hsl1
    have hnm2 := hret2_14.1
    rw [hsh] at hret2_18
    refine h86 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, hn8, rfl, ?_, hsl2, hF2, hret2_15,
      hret2_19.trans hc1⟩
    simp only [Tactic.rf]
    exact hB.imp_right fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega, by omega, hret2_17, by omega⟩

end Rv64mc.Proof.Layout.StackT

/-- info: 'Rv64mc.Proof.Layout.StackT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.StackT.total
