/-
  Rv64mc.Proof.Whir.Frobenius8

  `frobenius_8` keeps its contract (`Spec.Whir.Frobenius8.spec`), over any program holding its template, from
  `E::square`'s: `p = 0` returns `value`; otherwise the loop (`loop`, head at instruction 10) squares `8 p` times,
  counting down in `s0`.
-/

import Rv64mc.Spec.Whir.Frobenius8
import Rv64mc.Gen.Tmpl.Verifier.RingSwitch.Frobenius8
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Whir.Frobenius8

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Whir.Frobenius8
open Rv64mc.Gen.Verifier.RingSwitch.Frobenius8 (Link tmpl)

/-- `value` squared `j` times: the loop's value after `j` passes. -/
def sq (v : E) (j : Nat) : E := (List.range j).foldl (fun v _ => Model.squareE v) v

theorem sq_succ (v : E) (j : Nat) : sq v (j + 1) = Model.squareE (sq v j) := by
  simp [sq, List.range_succ, List.foldl_append]

theorem limbs_squareE (x : E) : Model.limbs (Model.squareE x) = Model.eSquare (Model.limbs x) := by
  rw [Model.squareE_eq, pow_two, Model.eSquare_eq]

theorem limbs_sq_succ (v : E) (j : Nat) :
    Model.limbs (sq v (j + 1)) = Model.eSquare ((Model.limbs (sq v j)).1, (Model.limbs (sq v j)).2) := by
  rw [sq_succ, limbs_squareE]

/-! ## The counter -/

theorem count_start {w : Word} (h : 8 * w.toNat < 2 ^ 64) : w <<< 3 = BitVec.ofNat 64 (8 * w.toNat - 0) := by
  have := h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.sub_zero]; omega

theorem count_step {N j : Nat} (_hN : N < 2 ^ 64) (hj : j < N) :
    BitVec.ofNat 64 (N - j) + 0xffffffffffffffff#64 = BitVec.ofNat 64 (N - (j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem count_zero {N j : Nat} (hN : N < 2 ^ 64) (hj : j < N) :
    BitVec.ofNat 64 (N - j) + 0xffffffffffffffff#64 = 0#64 ↔ j + 1 = N := by
  rw [count_step hN hj, ← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem p_zero {w : Word} (h : w = 0#64) : w.toNat = 0 := by rw [h]; rfl

theorem p_pos {w : Word} (h : ¬ w = 0#64) : 0 < w.toNat := by
  rcases Nat.eq_zero_or_pos w.toNat with h' | h'
  · exact absurd (BitVec.eq_of_toNat_eq (by rw [h']; rfl)) h
  · exact h'

/-! ## The loop -/

/-- The loop's invariant at its head after `j` squarings. -/
def Inv (env : Env) (v : E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 0xfffffffffffffff0#64 ∧ R .x8 = BitVec.ofNat 64 (8 * (regs .x12).toNat - j) ∧
    R .x10 = (Model.limbs (sq v j)).1 ∧ R .x11 = (Model.limbs (sq v j)).2 ∧
    R .x9 = regs .x9 ∧ R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧
    R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧
    R .x27 = regs .x27 ∧ env.Frame top Tactic.F m M ∧
    ∀ a, top + 0xfffffffffffffff0#64 ≤ a → M.getMem a =
      ((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).getMem a

theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (v : E)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need needS : Nat} (hnS : 16 + needS ≤ need)
    (hsq : Spec.Field.ESquare.spec env p L.square.idx needS) {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (Post v) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (h8 : 8 * (regs .x12).toNat < 2 ^ 64) :
    ∀ k j R M, j + k + 1 = 8 * (regs .x12).toNat → Inv env v ret top regs m j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 10, ret, top⟩ :: rest, R, M⟩ := by
  intro k
  induction k with
  | zero =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hsq]
    · exact absurd ((count_zero h8 (by omega)).2 (by omega)) hc
    all_goals rw [show Model.frobenius8Rust v (regs .x12).toNat = sq v (j + 1) by
      rw [show j + 1 = 8 * (regs .x12).toNat by omega]; rfl, limbs_sq_succ]
  | succ k ih =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hsq]
    · apply ih (j + 1) _ _ (by omega)
      rv_close
      · exact count_step h8 (by omega)
      · rw [limbs_sq_succ]
      · rw [limbs_sq_succ]
    all_goals exact absurd ((count_zero h8 (by omega)).1 hc) (by omega)

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS : Nat} (hnS : 16 + needS ≤ need) (hsq : Spec.Field.ESquare.spec env p L.square.idx needS) :
    spec env p i need := by
  intro v
  rv_auto hp with [hL] using [hsq]
  · rw [p_zero hc]; rfl
  · rw [p_zero hc]; rfl
  refine loop env p i L v hp hL hnS hsq hk hpre_3 hpre_4 hpre_5 hpre_8 (8 * (regs .x12).toNat - 1) 0 _ _
    (by have := p_pos hc; omega) ?_
  rv_close
  · exact count_start hpre_8
  all_goals rfl

end Rv64mc.Proof.Whir.Frobenius8
