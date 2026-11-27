/-
  Rv64mc.Proof.Field.KInvT

  `K::inv` is total (`total`): it returns `Model.kInv a` (the partial contract's postcondition, `KInv.Post`),
  writing nothing of its caller's. Safety and termination are proved alone (`safe`, with `Post := True`) over the
  callees' total contracts with their postconditions dropped (`dropPost`), so the executor carries no value of the
  Itoh-Tsujii chain; `HoldsT.of_holds_post` then combines it with the partial proof (`Proof/Field/KInv.lean`, the
  hypothesis `hpart`). The body (`134` calls of `spread`, `reduce` and `base_mul`, unrolled, the last a tail call) is
  cut after the prologue (instruction 10) and before every twelfth call (`part1` to `part12`): one run of the executor
  costs more than linearly in its calls, and twelve stay well within the default budget. Each part keeps only
  `Inv`: the stack pointer, `s3` to `s11` as at the entry, and `SavedT.MemOk` with the four saved registers' slots,
  carried across each call by `call_back`.

  ## Main definitions

  * `specT`, `Mem`, `Keep`, `Inv`

  ## Main results

  * `dropPost`, `call_back`, `part1` to `part12`, `safe`, `total`
-/

import Rv64mc.Proof.Field.SpreadT
import Rv64mc.Proof.Field.ReduceT
import Rv64mc.Proof.Field.BaseMulT
import Rv64mc.Proof.Field.KInv
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Core.HoldsTOfHolds

namespace Rv64mc.Proof.Field.KInvT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Gen.Verifier.Field.K.Inv (Link tmpl)

/-- **The total contract of `K::inv`**: the partial contract's postcondition, writing nothing of the caller's. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) KInv.Post

/-- A total contract with its postcondition dropped. -/
theorem dropPost {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} {Pre : (Reg → Word) → MachineState → Prop}
    {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    (h : HoldsT env p i need Pre Post) : HoldsT env p i need Pre (fun _ _ _ _ => True) :=
  fun Q ret top rest regs m hpre hstop hk =>
    h Q ret top rest regs m hpre hstop fun r' m' ⟨⟨h1, h2, h3, _⟩, h5⟩ => hk r' m' ⟨⟨h1, h2, h3, trivial⟩, h5⟩

/-- What every part keeps of memory: `SavedT.MemOk` with the four saved registers' slots, from `top - 8` (the
    return address) down to `top - 32` (`s2`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (fun _ => False)
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64]
    [ret, regs .x8, regs .x9, regs .x18] m M

/-- The saved slots lie in the `32` bytes below `top`. -/
theorem slots : SlotsIn 32
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64] :=
  slots_le

/-- The callee-saved registers the function never saves (`s3` to `s11`), as at the entry. -/
def Keep (regs R : Reg → Word) : Prop :=
  R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- A cut: the stack pointer `top - 32`, `Keep`, `Mem`. -/
def Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551584#64 ∧ Keep regs R ∧ Mem env ret top regs m M

/-- **`Mem` across a callee** writing nothing of the caller's, from the stack pointer `top - 32`. -/
theorem call_back {env : Env} {ret top : Word} {regs : Reg → Word} {m M X : MachineState}
    (hf : env.Frame (top + 18446744073709551584#64) (fun _ => False) M X)
    (hk : ∀ a : Word, top + 18446744073709551584#64 ≤ a → X.getMem a = M.getMem a) (hc : X.code = M.code)
    (hs : env.Static X) (hlim : env.stackLimit.toNat + 32 ≤ top.toNat) (hM : Mem env ret top regs m M) :
    Mem env ret top regs m X := by
  have e : (top + 18446744073709551584#64).toNat = top.toNat - 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact hM.call slots (by omega) (by omega) hf hc hs (fun _ h => h.elim) fun a h1 _ =>
    hk a (Tactic.le_of_toNat (by omega))

set_option hygiene false in
/-- One part, from its cut to the cut `b` (where `hb` goes on), across `n` calls: `Inv` again from `Mem` carried
    across each call by `call_back`, the callee's facts found by `assumption`. -/
local macro "part_tac" b:num n:num : tactic => `(tactic| (
  intro R M hI
  obtain ⟨-, -, hM⟩ := id hI
  have hlim : env.stackLimit.toNat + 32 ≤ top.toNat := by omega
  rv_introT hI
  rv_symT hp stop [$b] with [hL, hlim] using [dropPost hsp, dropPost hrd, dropPost hbm]
  refine hb _ _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  iterate $n (refine call_back (by assumption) (by assumption) (by assumption) (by assumption) hlim ?_)
  exact hM))

section

variable (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
  {need needS needR needM : Nat} (hnS : 32 + needS ≤ need) (hnR : 32 + needR ≤ need) (hnM : 32 + needM ≤ need)
  (hsp : SpreadT.specT env p L.spread.idx needS) (hrd : ReduceT.specT env p L.reduce.idx needR)
  (hbm : BaseMulT.specT env p L.baseMul.idx needM)
  {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
  (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
include hp hL hnS hnR hnM hsp hrd hbm hstk hal hW
-- Every part takes every callee's contract, so that `safe` chains them uniformly; a part without a `base_mul`
-- call does not use `hbm`.
set_option linter.unusedSectionVars false

set_option rv_sym.heap true in
/-- Calls `s0` to `s11`, from instruction 10. -/
theorem part1 (hb : ∀ R M, Inv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 68, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 10, ret, top⟩ :: rest, R, M⟩ := by
  part_tac 68 12

set_option rv_sym.heap true in
/-- Calls `s12` to `s23`, from instruction 68. -/
theorem part2 (hb : ∀ R M, Inv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 68, ret, top⟩ :: rest, R, M⟩ := by
  part_tac 118 12

set_option rv_sym.heap true in
/-- Calls `s24` to `s35`, from instruction 118. -/
theorem part3 (hb : ∀ R M, Inv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 170, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩ := by
  part_tac 170 12

set_option rv_sym.heap true in
/-- Calls `s36` to `s47`, from instruction 170. -/
theorem part4 (hb : ∀ R M, Inv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 218, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 170, ret, top⟩ :: rest, R, M⟩ := by
  part_tac 218 12

set_option rv_sym.heap true in
/-- Calls `s48` to `s59`, from instruction 218. -/
theorem part5 (hb : ∀ R M, Inv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 270, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 218, ret, top⟩ :: rest, R, M⟩ := by
  part_tac 270 12

set_option rv_sym.heap true in
/-- Calls `s60` to `s71`, from instruction 270. -/
theorem part6 (hb : ∀ R M, Inv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 318, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 270, ret, top⟩ :: rest, R, M⟩ := by
  part_tac 318 12

set_option rv_sym.heap true in
/-- Calls `s72` to `s83`, from instruction 318. -/
theorem part7 (hb : ∀ R M, Inv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 366, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 318, ret, top⟩ :: rest, R, M⟩ := by
  part_tac 366 12

set_option rv_sym.heap true in
/-- Calls `s84` to `s95`, from instruction 366. -/
theorem part8 (hb : ∀ R M, Inv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 414, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 366, ret, top⟩ :: rest, R, M⟩ := by
  part_tac 414 12

set_option rv_sym.heap true in
/-- Calls `s96` to `s107`, from instruction 414. -/
theorem part9 (hb : ∀ R M, Inv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 464, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 414, ret, top⟩ :: rest, R, M⟩ := by
  part_tac 464 12

set_option rv_sym.heap true in
/-- Calls `s108` to `s119`, from instruction 464. -/
theorem part10 (hb : ∀ R M, Inv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 512, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 464, ret, top⟩ :: rest, R, M⟩ := by
  part_tac 512 12

set_option rv_sym.heap true in
/-- Calls `s120` to `s131`, from instruction 512. -/
theorem part11 (hb : ∀ R M, Inv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 564, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 512, ret, top⟩ :: rest, R, M⟩ := by
  part_tac 564 12

set_option rv_sym.heap true in
/-- Call `s132`, the epilogue and the tail call `s133`, from instruction 564: the saved registers restored from their
    slots, the frame across both calls. -/
theorem part12
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) :
    ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 564, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨-, -, hM⟩ := id hI
  have hlim : env.stackLimit.toNat + 32 ≤ top.toNat := by omega
  rv_introT hI
  rv_symT hp with [hL, hlim] using [dropPost hsp, dropPost hrd, dropPost hbm]
  have hM1 := call_back hret1_14 keep1_1 hret1_16 hret1_15 hlim hM
  refine ⟨?_, Tactic.frame_trans hM1.1 hret2_14 (Nat.le_refl _) (fun _ h => h.elim), hret2_15, trivial⟩
  simp only [AbiRegs, Tactic.rf, hI_15, hI_16, hI_17, and_self]

end

set_option hygiene false in
/-- `h' := t ... h`: the part `t` at the entry's facts, going on by `h`. -/
local macro "chain" t:ident h:ident h':ident : tactic => `(tactic|
  have $h' := $t env p i L hp hL hnS hnR hnM hsp hrd hbm hpre_3 hpre_6 hpre_7 $h)

set_option rv_sym.heap true in
/-- **`K::inv` is safe and terminates**: the prologue, then the twelve parts. -/
theorem safe (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS needR needM : Nat} (hnS : 32 + needS ≤ need) (hnR : 32 + needR ≤ need) (hnM : 32 + needM ≤ need)
    (hsp : SpreadT.specT env p L.spread.idx needS) (hrd : ReduceT.specT env p L.reduce.idx needR)
    (hbm : BaseMulT.specT env p L.baseMul.idx needM) :
    HoldsT env p i need (fun _ _ => True) (fun _ _ _ _ => True) := by
  rv_autoT hp stop [10] with [hL]
  chain part12 hk h12
  chain part11 h12 h11
  chain part10 h11 h10
  chain part9 h10 h9
  chain part8 h9 h8
  chain part7 h8 h7
  chain part6 h7 h6
  chain part5 h6 h5
  chain part4 h5 h4
  chain part3 h4 h3
  chain part2 h3 h2
  chain part1 h2 h1
  refine h1 _ _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> rv_closeT

/-- **`K::inv` is total**, with the partial contract's postcondition (`hpart`, `Proof.Field.KInv.ok` at the
    image). -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS needR needM : Nat} (hnS : 32 + needS ≤ need) (hnR : 32 + needR ≤ need) (hnM : 32 + needM ≤ need)
    (hsp : SpreadT.specT env p L.spread.idx needS) (hrd : ReduceT.specT env p L.reduce.idx needR)
    (hbm : BaseMulT.specT env p L.baseMul.idx needM) (hpart : KInv.spec env p i need) : specT env p i need :=
  (safe env p i L hp hL hnS hnR hnM hsp hrd hbm).of_holds_post hpart fun _ _ h => h

end Rv64mc.Proof.Field.KInvT

/-- info: 'Rv64mc.Proof.Field.KInvT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.KInvT.total
