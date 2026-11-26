/-
  Rv64mc.Proof.Transcript.AbsorbT

  `Sponge::absorb` is total (`specT`): from a sponge `SpongeT` (`SpongeReprT`) its caller owns (`Owned`), it returns
  with the sponge `SpongeT` again, writing nothing outside it and its stack, or ends the run with `a0 = 2` on a
  waiting ground challenge (`panic_fmt`) or a count past three after the permutation (`panic_bounds_check`).
  Safety only, as `DuplexT`: the partial contract's sponge (`Absorb.lean`) is `duplex`'s permuted one. The body is
  cut where the slot's address is computed (instruction 25, its first store): the slot `a + 24 n` is then a word
  `s` with its value as a number (`hs`), so the three stores into it and the count's store are stepped with their
  addresses compared by `omega` on numbers.

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `TailInv`

  ## Main results

  * `slot_toNat`, `tail_ok`, `total`
-/

import Rv64mc.Proof.Transcript.DuplexT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Spec.Transcript.Absorb
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Sponge.Absorb

namespace Rv64mc.Proof.Transcript.AbsorbT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Transcript.SpongeReprT
open Rv64mc.Gen.Verifier.Transcript.Sponge.Absorb (Link tmpl)

/-- The total precondition: the sponge `SpongeT`, and owned by the caller. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SpongeT env m (regs .x10) ∧ env.Owned m (regs .x2) (regs .x10) Layouts.Sponge.byteSize

/-- The total postcondition: the sponge `SpongeT` again. -/
def PostT (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  SpongeT env m' (regs .x10)

/-- **The total contract of `Sponge::absorb`**: `PreT` to `PostT`, writing at most the sponge, or ending the run
    with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) Absorb.Out (Stop := AbortStop)

/-- The slot of waiting scalar `n`, as the code computes it: `24 n` bytes past the sponge. -/
theorem slot_toNat {a n : Word} (ha : a.toNat + 328 < 2 ^ 64) (hn : n ≤ 3#64) :
    (a + (n <<< 4 + n <<< 3)).toNat = a.toNat + 24 * n.toNat := by
  have h3 : n.toNat ≤ 3 := hn
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq]
  omega

/-- The state at instruction 25, the slot's address computed (`s`): the registers kept, the frame, the code, the
    static data, the saved registers' slots, the count `n` and the ground tag. -/
def TailInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (s n : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551568#64 ∧ R .x8 = regs .x13 ∧ R .x9 = regs .x10 ∧ R .x10 = s ∧
    R .x18 = regs .x12 ∧ R .x19 = regs .x11 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top (Absorb.Out regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (regs .x10 + 320#64) = n ∧
    (M.getMem (regs .x10) = 0#64 ∨ M.getMem (regs .x10) = 1#64)

set_option rv_sym.heap true in
/-- From the slot's address: the value, the zero and the tag stored into it, the count raised, the return. -/
theorem tail_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat}
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) Absorb.Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hn48 : 48 ≤ need) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (ha8 : (regs .x10).toNat % 8 = 0) (hw : InWin env (regs .x10) 328) (ho : env.Owned m top (regs .x10) 328)
    {s n : Word} (hn : n.toNat ≤ 3) (hs : s.toNat = (regs .x10).toNat + 24 * n.toNat) :
    ∀ R M, TailInv env ret top regs m s n R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 50, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have hlt := hw.lt
  have hne : regs .x10 ≠ env.nextAddr := hw.ne_next (Nat.le_refl _) (by omega)
  have hown := ho.1
  have := hW.top_le
  unfold InWin at hw
  rv_introT hinv
  rv_symT hp with [(by omega : env.stackLimit.toNat + 48 ≤ top.toNat)]

set_option rv_sym.heap true in
/-- **`Sponge::absorb` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needD needP needB : Nat} (hnD : 48 + needD ≤ need) (hnP : 48 + needP ≤ need) (hnB : 48 + needB ≤ need)
    (hdx : DuplexT.specT env p L.duplex.idx needD) (hpf : Aborts env p L.panicFmt.idx needP)
    (hpb : Aborts env p L.panicBoundsCheck.idx needB) : specT env p i need := by
  rv_autoT hp stop [50] with [hL, (by omega : env.stackLimit.toNat + 48 ≤ top.toNat), hpre_13.top_le]
    using [hdx, hpf, hpb]
  all_goals
    refine tail_ok env p i L hp hk hpre_3 hpre_5 (by omega) hpre_12 hpre_13 hpre_6 hpre_7
      (hpre_2 ▸ ⟨hpre_10, hpre_11⟩) (BitVec.le_def.1 hc) (slot_toNat (by omega) hc) _ _ ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try rv_closeT
  all_goals
    have hsp : (top + 18446744073709551568#64).toNat = top.toNat - 48 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h32 : (top + 18446744073709551584#64).toNat = top.toNat - 32 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have h40 : (top + 18446744073709551576#64).toNat = top.toNat - 40 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hown := hpre_2 ▸ hpre_10
    have := env.layout
    rw [keep3_1 _ (BitVec.le_def.2 (by omega)) (by
      simp only [Duplex.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, h8, h16, h24, h32,
        h40, Layouts.Sponge.byteSize]
      omega)]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]

end Rv64mc.Proof.Transcript.AbsorbT

/-- info: 'Rv64mc.Proof.Transcript.AbsorbT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Transcript.AbsorbT.total
