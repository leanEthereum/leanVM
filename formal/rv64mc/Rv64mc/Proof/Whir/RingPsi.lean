/-
  Rv64mc.Proof.Whir.RingPsi

  `ring_psi` keeps its contract (`Spec.Whir.RingPsi.spec`), over any program holding its template, from the
  contracts of `E::mul` and `E::square`. An empty `g` returns `ZERO`; otherwise the loop (`loop`, head at
  instruction 32) keeps `psi` in `s2`, `s0` and `power` in `s3`, `s4`, its invariant the fold of
  `Model.ringPsiRust` over the first `j` elements.
-/

import Rv64mc.Spec.Whir.RingPsi
import Rv64mc.Core.ReprLemmas
import Rv64mc.Proof.Whir.Arith
import Rv64mc.Gen.Tmpl.Verifier.RingSwitch.RingPsi
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Whir.RingPsi

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Whir.RingPsi Rv64mc.Proof.Whir
open Rv64mc.Gen.Verifier.RingSwitch.RingPsi (Link tmpl)

/-! ## The fold -/

/-- One element of the loop: `psi += g_b * power; power = power.square()`. -/
def step (acc : E × E) (gB : E) : E × E := (acc.1 + gB * acc.2, Model.squareE acc.2)

/-- `(psi, power)` after the first `j` elements. -/
def acc (v : E) (gs : List E) (j : Nat) : E × E := (gs.take j).foldl step (0, v)

theorem acc_succ {v : E} {gs : List E} {j : Nat} (hj : j < gs.length) :
    acc v gs (j + 1) = step (acc v gs j) gs[j] := by
  rw [acc, List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hj]; rfl

theorem ringPsiRust_acc (v : E) (gs : List E) : Model.ringPsiRust v gs = (acc v gs gs.length).1 := by
  rw [acc, List.take_length]; rfl

theorem psi_limbs (psi g pw : E) :
    Model.limbs (psi + g * pw) =
      ((Model.eMul (Model.limbs g) (Model.limbs pw)).1 ^^^ (Model.limbs psi).1,
        (Model.eMul (Model.limbs g) (Model.limbs pw)).2 ^^^ (Model.limbs psi).2) := by
  rw [Model.eMul_eq, ← Model.eAdd_eq, Model.eAdd, BitVec.xor_comm, BitVec.xor_comm (Model.limbs psi).2]

theorem power_limbs (pw : E) :
    Model.limbs (Model.squareE pw) = Model.eSquare ((Model.limbs pw).1, (Model.limbs pw).2) := by
  rw [Model.squareE_eq, pow_two, ← Model.eSquare_eq]

/-! ## The loop -/

/-- The loop's invariant at its head after `j` elements: the pointer and the end, `psi` and `power`, the saved
    registers, the frame, and the prologue's stores. -/
def Inv (env : Env) (v : E) (gs : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 0xffffffffffffffc0#64 ∧ R .x9 = regs .x12 + BitVec.ofNat 64 (16 * j) ∧
    R .x21 = regs .x12 + BitVec.ofNat 64 (List.map Model.limbs gs).length <<< 4 ∧
    R .x18 = (Model.limbs (acc v gs j).1).1 ∧ R .x8 = (Model.limbs (acc v gs j).1).2 ∧
    R .x19 = (Model.limbs (acc v gs j).2).1 ∧ R .x20 = (Model.limbs (acc v gs j).2).2 ∧
    R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧
    R .x27 = regs .x27 ∧ env.Frame top Tactic.F m M ∧
    ∀ a, top + 0xffffffffffffffc0#64 ≤ a → M.getMem a =
      ((((((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
        (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).setMem
        (top + 0xffffffffffffffd8#64) (regs .x19)).setMem (top + 0xffffffffffffffd0#64) (regs .x20)).setMem
        (top + 0xffffffffffffffc8#64) (regs .x21))).getMem a

/-- What one pass computes of `psi`, from the element the loop loads through the frame. -/
theorem body_psi {env : Env} {top : Word} {m M : MachineState} {v : E} {gs : List E} {q : Word} {j : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hg : EListAt m q (gs.map Model.limbs)) (hl : env.Live m q (Layouts.E.byteSize * gs.length))
    (hj : j < gs.length) :
    ((Model.eMul (M.getMem (q + BitVec.ofNat 64 (16 * j)), M.getMem (q + BitVec.ofNat 64 (16 * j) + 8#64))
        ((Model.limbs (acc v gs j).2).1, (Model.limbs (acc v gs j).2).2)).1 ^^^ (Model.limbs (acc v gs j).1).1,
      (Model.eMul (M.getMem (q + BitVec.ofNat 64 (16 * j)), M.getMem (q + BitVec.ofNat 64 (16 * j) + 8#64))
        ((Model.limbs (acc v gs j).2).1, (Model.limbs (acc v gs j).2).2)).2 ^^^ (Model.limbs (acc v gs j).1).2) =
      Model.limbs (acc v gs (j + 1)).1 := by
  have e := EListAt.load (j := j) hf hnx hg (by simpa using hl) (by simpa using hj)
  simp only [List.getElem_map] at e
  rw [e.1, e.2, acc_succ hj, step, psi_limbs]

/-- **The loop**, from its head with `k + 1` elements to go. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (v : E) (gs : List E)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need needM needS : Nat} (hnM : 64 + needM ≤ need)
    (hnS : 64 + needS ≤ need) (hmul : Spec.Field.EMul.spec env p L.mul.idx needM)
    (hsq : Spec.Field.ESquare.spec env p L.square.idx needS)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (Post v gs) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩) (hal : top.toNat % 16 = 0)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hg : EListAt m (regs .x12) (gs.map Model.limbs))
    (hl : env.Live m (regs .x12) (Layouts.E.byteSize * gs.length)) :
    ∀ k j R M, j + k + 1 = gs.length → Inv env v gs ret top regs m j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 32, ret, top⟩ :: rest, R, M⟩ := by
  have hq : (regs .x12).toNat + 16 * (List.map Model.limbs gs).length < 2 ^ 64 := by
    have := live_bound hl hnx; simp only [Layouts.E.byteSize, List.length_map] at this ⊢; omega
  intro k
  induction k with
  | zero =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hmul, hsq]
    · exact absurd ((end_iff hq (by simp; omega)).2 (by simp; omega)) hc
    all_goals rw [ringPsiRust_acc, show gs.length = j + 1 by omega,
      ← body_psi hinv_14 hnx hg hl (by omega)]
  | succ k ih =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hmul, hsq]
    · apply ih (j + 1) _ _ (by omega)
      rv_close
      · exact ptr_step _ _
      · rw [← body_psi hinv_14 hnx hg hl (by omega)]
      · rw [← body_psi hinv_14 hnx hg hl (by omega)]
      · rw [acc_succ (by omega), step, power_limbs]
      · rw [acc_succ (by omega), step, power_limbs]
    all_goals exact absurd ((end_iff hq (by simp; omega)).1 hc) (by simp; omega)

/-- **`ring_psi` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM needS : Nat} (hnM : 64 + needM ≤ need) (hnS : 64 + needS ≤ need)
    (hmul : Spec.Field.EMul.spec env p L.mul.idx needM)
    (hsq : Spec.Field.ESquare.spec env p L.square.idx needS) : spec env p i need := by
  intro v gs
  rv_auto hp with [hL] using [hmul, hsq]
  all_goals have hb := live_bound hpre_10 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hb
  · have h0 : gs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]; rfl
  · have h0 : gs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]; rfl
  have h0 : gs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  refine loop env p i L v gs hp hL hnM hnS hmul hsq hk (by assumption) hpre_3 hpre_4 hpre_5 hpre_9 hpre_10
    (gs.length - 1) 0 _ _ (by omega) ?_
  rv_close
  · exact ptr_start _
  all_goals rfl

end Rv64mc.Proof.Whir.RingPsi
