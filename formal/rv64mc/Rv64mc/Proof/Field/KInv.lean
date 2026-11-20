/-
  Rv64mc.Proof.Field.KInv

  `K::inv` keeps its contract (`Spec.Field.KInv.spec`), over any program holding its template, from its callees'
  contracts: the 63 squarings of the Itoh-Tsujii chain, each `spread` then `reduce`, unrolled, and its 8 products
  by `base_mul`. Stepped in one run, the chain's values nest too deep for the tactic, so the body is cut where
  `t24` and `t48` are made (instructions 234 and 432): `seg2` and `seg3` start from those values as variables
  (`Inv`), each equal to its term (`t24 a`, `t48 a`), so that what the tactic carries stays small and the closer
  never compares a register's value with a term by unfolding.
-/

import Rv64mc.Spec.Field.KInv
import Rv64mc.Proof.Field.U128
import Rv64mc.Gen.Tmpl.Verifier.Field.K.Inv
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Field.KInv

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.K.Inv (Link tmpl)
open Model (kSq baseMul)

theorem kSq_zero (v : BitVec 64) : kSq v 0 = v := rfl

theorem kSq_succ (v : BitVec 64) (n : Nat) : kSq v (n + 1) = Model.kSquare (kSq v n) := by
  simp [kSq, List.range_succ, List.foldl_append]

theorem reduce_spread (a : BitVec 64) : Model.reduce (Model.spread a) = Model.kSquare a := rfl

/-! ## The chain's values, `Model.kInv`'s `let`s -/

def t3 (a : BitVec 64) : BitVec 64 := baseMul (kSq (baseMul (kSq a 1) a) 1) a
def t12 (a : BitVec 64) : BitVec 64 := baseMul (kSq (baseMul (kSq (t3 a) 3) (t3 a)) 6) (baseMul (kSq (t3 a) 3) (t3 a))
def t24 (a : BitVec 64) : BitVec 64 := baseMul (kSq (t12 a) 12) (t12 a)
def t48 (a : BitVec 64) : BitVec 64 := baseMul (kSq (t24 a) 24) (t24 a)

theorem kInv_eq (a : BitVec 64) :
    Model.kInv a = kSq (baseMul (kSq (baseMul (kSq (t48 a) 12) (t12 a)) 3) (t3 a)) 1 := rfl

/-! ## The cuts -/

/-- At a cut, after the prologue: `v8`, `v9` and `v18` (`t3`, `t12` and `t24`) in `s0`, `s1`, `s2`, the value
    `v` in `a0`, the saved registers, the frame of everything the function did, and the prologue's stores kept above
    its callees' frames. -/
def Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (v8 v9 v18 v : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 0xffffffffffffffe0#64 ∧ R .x8 = v8 ∧ R .x9 = v9 ∧ R .x18 = v18 ∧ R .x10 = v ∧
    R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧
    ∀ a, top + 0xffffffffffffffe0#64 ≤ a → M.getMem a =
      ((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
        (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).getMem a

section

variable (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
  {need needS needR needM : Nat} (hnS : 32 + needS ≤ need) (hnR : 32 + needR ≤ need) (hnM : 32 + needM ≤ need)
  (hsp : Spread.spec env p L.spread.idx needS) (hrd : Reduce.spec env p L.reduce.idx needR)
  (hbm : BaseMul.spec env p L.baseMul.idx needM)
  {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
  {regs : Reg → Word} {m : MachineState}
  (hk : ∀ r' m', Holds.post env KInv.Post (fun _ _ _ => False) ret top regs m r' m' →
    rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
  (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
  (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hal : top.toNat % 16 = 0)
include hp hL hnS hnR hnM hsp hrd hbm hk hstk hst hnx hal

/-- From `t48`: 12 squarings, times `t12`, 3 squarings, times `t3`, the last squaring. -/
theorem seg3 : ∀ v8 v9 v18 v R M, v8 = t3 (regs .x10) → v9 = t12 (regs .x10) → v = t48 (regs .x10) →
    Inv env ret top regs m v8 v9 v18 v R M → rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 432, ret, top⟩ :: rest, R, M⟩ := by
  intro v8 v9 v18 v R M h8 h9 hv hinv
  rv_intro hinv
  rv_sym hp with [hL] using [hsp, hrd, hbm]
  subst h8 h9 hv
  simp only [append_hi_lo, reduce_spread, kInv_eq, kSq_succ, kSq_zero]

/-- From `t24`: 24 squarings, times `t24`. -/
theorem seg2 : ∀ v8 v9 v18 v R M, v8 = t3 (regs .x10) → v9 = t12 (regs .x10) → v18 = t24 (regs .x10) →
    v = t24 (regs .x10) → Inv env ret top regs m v8 v9 v18 v R M →
    rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 234, ret, top⟩ :: rest, R, M⟩ := by
  intro v8 v9 v18 v R M h8 h9 h18 hv hinv
  rv_intro hinv
  rv_sym hp stop [432] with [hL] using [hsp, hrd, hbm]
  refine seg3 env p i L hp hL hnS hnR hnM hsp hrd hbm hk hstk hst hnx hal v8 v9 v18 ?v _ _ h8 h9 ?hv ?hinv
  case hinv => rv_close; rfl
  subst h18 hv
  simp only [append_hi_lo, reduce_spread, t48, kSq_succ, kSq_zero]

end

/-- **`K::inv` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS needR needM : Nat} (hnS : 32 + needS ≤ need) (hnR : 32 + needR ≤ need) (hnM : 32 + needM ≤ need)
    (hsp : Spread.spec env p L.spread.idx needS) (hrd : Reduce.spec env p L.reduce.idx needR)
    (hbm : BaseMul.spec env p L.baseMul.idx needM) : KInv.spec env p i need := by
  rv_auto hp stop [234] with [hL] using [hsp, hrd, hbm]
  refine seg2 env p i L hp hL hnS hnR hnM hsp hrd hbm hk hpre_3 hpre_4 hpre_5 (by assumption) ?v8 ?v9 ?v18 ?v _ _ ?h8 ?h9
    ?h18 ?hv
    ?hinv
  case hinv => rv_close; all_goals rfl
  all_goals simp only [append_hi_lo, reduce_spread, t3, t12, t24, kSq_succ, kSq_zero]

end Rv64mc.Proof.Field.KInv
