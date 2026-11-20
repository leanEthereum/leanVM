/-
  Rv64mc.Proof.Field.EPow

  `GEN.pow` keeps its contract (`Spec.Field.EPow.spec`), over any program holding its template, from the contracts
  of `E::square` and `E::mul`. The loop's head is instruction 28, where the base is squared; there the product of
  the bits seen so far is done, so what is left is `Model.ePowLoop` from the squared base and the shifted exponent
  (`loop`, by induction on the exponent's bits).
-/

import Rv64mc.Spec.Field.EPow
import Rv64mc.Gen.Tmpl.Verifier.Field.E.Pow
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Field.EPow

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.E.Pow (Link tmpl)
open Model (ePowLoop eSquare eMul)

/-! ## The Model's loop -/

theorem ePowLoop_zero (b o : Model.Limbs) : ePowLoop b o 0#64 = o := by
  rw [ePowLoop]; exact ite_eq_left rfl

theorem ePowLoop_step (b o : Model.Limbs) {n : Word} (h : ¬ n = 0#64) :
    ePowLoop b o n = ePowLoop (eSquare b) (if n &&& 1#64 = 1#64 then eMul o b else o) (n >>> 1) := by
  rw [ePowLoop]; exact ite_eq_right h

theorem bit_ne {n : Word} (h : ¬ n &&& 1#64 = 0#64) : n &&& 1#64 = 1#64 := by
  have hl : (n &&& 1#64).toNat ≤ 1 := by rw [BitVec.toNat_and]; exact Nat.and_le_right
  have h' : (n &&& 1#64).toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq (by simpa using h0))
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]; omega

theorem bit_eq {n : Word} (h : n &&& 1#64 = 0#64) : ¬ n &&& 1#64 = 1#64 := by
  rw [h]; decide

theorem half_lt {N : Word} {k : Nat} (h : (N >>> 1).toNat < 2 ^ (k + 1)) : (N >>> 1 >>> 1).toNat < 2 ^ k := by
  have e : (N >>> 1 >>> 1).toNat = (N >>> 1).toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, pow_one]
  rw [e]; rw [pow_succ] at h; omega

theorem half_zero {N : Word} (h : (N >>> 1).toNat < 2 ^ 0) : N >>> 1 = 0#64 :=
  BitVec.eq_of_toNat_eq (by simp only [pow_zero] at h; simp only [BitVec.toNat_ofNat]; omega)

/-! ## The loop -/

/-- The loop's head: the base `b` (in `s4`, `s3`), the product `o` (in `s2`, `s0`), the exponent `N` (in `s1`), the
    saved registers, the frame of everything the function did, and the prologue's stores. -/
def Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (b o : Model.Limbs) (N : Word)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 0xffffffffffffffd0#64 ∧ R .x20 = b.1 ∧ R .x19 = b.2 ∧ R .x18 = o.1 ∧ R .x8 = o.2 ∧ R .x9 = N ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧
    ∀ a, top + 0xffffffffffffffd0#64 ≤ a → M.getMem a =
      ((((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
        (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).setMem
          (top + 0xffffffffffffffd8#64) (regs .x19)).setMem (top + 0xffffffffffffffd0#64) (regs .x20)).getMem a

/-- **The loop**, from its head with the shifted exponent below `2^k`. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS needM : Nat} (hnS : 48 + needS ≤ need) (hnM : 48 + needM ≤ need)
    (hsq : ESquare.spec env p L.square.idx needS) (hmul : EMul.spec env p L.mul.idx needM)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env EPow.Post (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    ∀ k (b o : Model.Limbs) (N : Word) R M, (N >>> 1).toNat < 2 ^ k →
      Model.ePow Model.eGen (regs .x10) = ePowLoop (eSquare b) o (N >>> 1) →
      Inv env ret top regs m b o N R M → rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 28, ret, top⟩ :: rest, R, M⟩ := by
  intro k
  induction k with
  | zero =>
    intro b o N R M hb ht hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hsq, hmul]
    · rw [ht, hc, ePowLoop_zero]
    · rw [ht, hc, ePowLoop_zero]
    · exact absurd (half_zero hb) hc_1
    · exact absurd (half_zero hb) hc_1
  | succ k ih =>
    intro b o N R M hb ht hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hsq, hmul]
    · rw [ht, hc, ePowLoop_zero]
    · rw [ht, hc, ePowLoop_zero]
    · refine ih (eSquare b) o (N >>> 1) _ _ (half_lt hb) ?_ ?_
      · rw [ht, ePowLoop_step _ _ hc_1, ite_eq_right (bit_eq hc)]
      · rv_close
    · refine ih (eSquare b) (eMul o (eSquare b)) (N >>> 1) _ _ (half_lt hb) ?_ ?_
      · rw [ht, ePowLoop_step _ _ hc_1, ite_eq_left (bit_ne hc)]
      · rv_close

/-- **`GEN.pow` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS needM : Nat} (hnS : 48 + needS ≤ need) (hnM : 48 + needM ≤ need)
    (hsq : ESquare.spec env p L.square.idx needS) (hmul : EMul.spec env p L.mul.idx needM) :
    EPow.spec env p i need := by
  rv_auto hp with [hL] using [hsq, hmul]
  · rw [hc, Model.ePow, ePowLoop_zero]; rfl
  · rw [hc, Model.ePow, ePowLoop_zero]; rfl
  · refine loop env p i L hp hL hnS hnM hsq hmul hk hpre_3 hpre_4 hpre_5 64 Model.eGen Model.eOne (regs .x10) _ _
      (BitVec.isLt _) ?_ ?_
    · rw [Model.ePow, ePowLoop_step _ _ hc_1, ite_eq_right (bit_eq hc)]
    · rv_close
      all_goals rfl
  · refine loop env p i L hp hL hnS hnM hsq hmul hk hpre_3 hpre_4 hpre_5 64 Model.eGen
      (eMul Model.eOne Model.eGen) (regs .x10) _ _ (BitVec.isLt _) ?_ ?_
    · rw [Model.ePow, ePowLoop_step _ _ hc_1, ite_eq_left (bit_ne hc)]
    · rv_close
      all_goals rfl

end Rv64mc.Proof.Field.EPow
