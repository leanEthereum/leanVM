/-
  Rv64mc.Proof.Multilinear.EqEval

  `eq_eval` keeps its contract (`Spec.Multilinear.EqEval.spec`), over any program holding its template, from the
  contracts of `E::mul` and of `assert_failed` (which does not return). `rv_auto` runs the entry to the loop's head
  (instruction 28, the target of the back edge) and closes the length check's failure; the loop is `loop`, by
  induction on the elements left, its invariant `Inv` the fold of `Model.eqEvalRust` over the first `j` pairs.
-/

import Rv64mc.Spec.Multilinear.EqEval
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Core.ReprLemmas
import Rv64mc.Gen.Tmpl.Verifier.Multilinear.EqEval
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Multilinear.EqEval

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.EqEval
open Rv64mc.Gen.Verifier.Multilinear.EqEval (Link tmpl)

/-- The product over the first `j` pairs: `result` after `j` passes of the loop. -/
def acc (xs ys : List E) (j : Nat) : E := ((xs.zip ys).take j).foldl (fun r xy => r * (1 + xy.1 + xy.2)) 1

/-! ## The fold and the limbs -/

theorem acc_succ {xs ys : List E} {j : Nat} (hx : j < xs.length) (hy : j < ys.length) :
    acc xs ys (j + 1) = acc xs ys j * (1 + xs[j] + ys[j]) := by
  rw [acc, List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simp; omega)]
  simp [acc, List.getElem_zip]

theorem eqEvalRust_acc {xs ys : List E} (h : xs.length = ys.length) :
    Model.eqEvalRust xs ys = some (acc xs ys xs.length) := by
  rw [Model.eqEvalRust, ite_eq_left_of_eq_true _ _ (eq_true h), acc,
    List.take_of_length_le (by simp only [List.length_zip]; omega)]

/-- One pass of the body on limbs, as `E::mul` gets its operands: `result * (ONE + x + y)`. -/
theorem step_limbs (a x y : E) :
    Model.limbs (a * (1 + x + y)) = Model.eMul ((Model.limbs a).1, (Model.limbs a).2)
      ((Model.limbs x).1 ^^^ (Model.limbs y).1 ^^^ 1#64, (Model.limbs y).2 ^^^ (Model.limbs x).2) := by
  rw [← Model.eMul_eq, ← Model.eAdd_eq, ← Model.eAdd_eq, Model.limbs_one]
  congr 1
  simp only [Model.eAdd, Model.eOne, Prod.mk.injEq]
  constructor
  · ac_rfl
  · rw [BitVec.zero_xor, BitVec.xor_comm]

/-! ## The loop's arithmetic -/

theorem step_ptr (q : Word) (j : Nat) :
    q + BitVec.ofNat 64 (16 * j) + 24#64 = q + BitVec.ofNat 64 (16 * (j + 1)) + 8#64 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem start_ptr (q : Word) : q + 8#64 = q + BitVec.ofNat 64 (16 * 0) + 8#64 := by simp

/-- A live slice ends below the stack, with room for the end pointer. -/
theorem live_bound {env : Env} {m : MachineState} {q : Word} {n : Nat} (hl : env.Live m q n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) : q.toNat + n + 8 < 2 ^ 64 := by
  have := env.layout; have := env.stackLimit.isLt; unfold Env.Live at hl; omega

/-- The loop's exit test: past the last element. -/
theorem end_iff {q : Word} {j len : Nat} (hq : q.toNat + 16 * len + 8 < 2 ^ 64) (hj : j < len) :
    q + BitVec.ofNat 64 (16 * j) + 24#64 = q + 8#64 + BitVec.ofNat 64 len <<< 4 ↔ j + 1 = len := by
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_right_inj, ← BitVec.toNat_inj]
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem len_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) :
    a = b := by
  rw [← BitVec.toNat_inj] at h; simp at h; omega

theorem len_zero {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a = 0#64 ↔ a = 0 := by
  rw [← BitVec.toNat_inj]; simp; omega

/-! ## The loop -/

/-- The loop's invariant at its head after `j` elements: the two pointers, the end, the product so far, the saved
    registers, the frame of everything the function did, and the prologue's stores kept above `E::mul`'s frame. -/
def Inv (env : Env) (xs ys : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 0xffffffffffffffd0#64 ∧
    R .x8 = regs .x12 + BitVec.ofNat 64 (16 * j) + 8#64 ∧ R .x9 = regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64 ∧
    R .x18 = regs .x12 + 8#64 + BitVec.ofNat 64 (List.map Model.limbs xs).length <<< 4 ∧
    R .x10 = (Model.limbs (acc xs ys j)).1 ∧ R .x11 = (Model.limbs (acc xs ys j)).2 ∧
    R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧
    ∀ a, top + 0xffffffffffffffd0#64 ≤ a → M.getMem a =
      ((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
        (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).getMem a

/-- What one pass computes, from the elements the loop loads through the frame. -/
theorem body_val {env : Env} {top : Word} {m M : MachineState} {xs ys : List E} {regs : Reg → Word} {j : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hx : EListAt m (regs .x10) (xs.map Model.limbs)) (hy : EListAt m (regs .x12) (ys.map Model.limbs))
    (hlx : env.Live m (regs .x10) (Layouts.E.byteSize * xs.length))
    (hly : env.Live m (regs .x12) (Layouts.E.byteSize * ys.length)) (hjx : j < xs.length) (hjy : j < ys.length) :
    Model.eMul ((Model.limbs (acc xs ys j)).1, (Model.limbs (acc xs ys j)).2)
        (M.getMem (regs .x10 + BitVec.ofNat 64 (16 * j)) ^^^ M.getMem (regs .x12 + BitVec.ofNat 64 (16 * j)) ^^^ 1#64,
          M.getMem (regs .x12 + BitVec.ofNat 64 (16 * j) + 8#64) ^^^
            M.getMem (regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64)) =
      Model.limbs (acc xs ys (j + 1)) := by
  have ex := EListAt.load (j := j) hf hnx hx (by simpa using hlx) (by simpa using hjx)
  have ey := EListAt.load (j := j) hf hnx hy (by simpa using hly) (by simpa using hjy)
  simp only [List.getElem_map] at ex ey
  rw [ex.1, ex.2, ey.1, ey.2, acc_succ hjx hjy, step_limbs]

/-- **The loop**, from its head with `k + 1` elements to go. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (xs ys : List E)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need needM : Nat} (hnM : 48 + needM ≤ need)
    (hmul : Spec.Field.EMul.spec env p L.mul.idx needM)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (Post xs ys) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hal : top.toNat % 16 = 0)
    (hx : EListAt m (regs .x10) (xs.map Model.limbs)) (hy : EListAt m (regs .x12) (ys.map Model.limbs))
    (hlx : env.Live m (regs .x10) (Layouts.E.byteSize * xs.length))
    (hly : env.Live m (regs .x12) (Layouts.E.byteSize * ys.length)) (hlen : xs.length = ys.length) :
    ∀ k j R M, j + k + 1 = xs.length → Inv env xs ys ret top regs m j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 28, ret, top⟩ :: rest, R, M⟩ := by
  have hq : (regs .x12).toNat + 16 * (List.map Model.limbs xs).length + 8 < 2 ^ 64 := by
    simpa [hlen] using live_bound hly hnx
  intro k
  induction k with
  | zero =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hmul]
    · exact absurd ((end_iff hq (by simp; omega)).2 (by simp; omega)) hc
    intro v hv
    rw [eqEvalRust_acc hlen, Option.some.injEq] at hv
    subst hv
    rw [show xs.length = j + 1 by omega, ← body_val hinv_16 hnx hx hy hlx hly (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hmul]
    · apply ih (j + 1) _ _ (by omega)
      rv_close
      · exact step_ptr _ _
      · exact step_ptr _ _
      · rw [body_val hinv_16 hnx hx hy hlx hly (by omega) (by omega)]
      · rw [body_val hinv_16 hnx hx hy hlx hly (by omega) (by omega)]
    exact absurd ((end_iff hq (by simp; omega)).1 hc) (by simp; omega)

/-- **`eq_eval` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM needF : Nat} (hnM : 48 + needM ≤ need) (hnF : 48 + needF ≤ need)
    (hmul : Spec.Field.EMul.spec env p L.mul.idx needM)
    (hfail : Spec.Runtime.NoReturn env p L.assertFailedUsizeUsize.idx needF) : spec env p i need := by
  intro xs ys
  rv_auto hp with [hL] using [hmul, hfail]
  all_goals have hlx := live_bound hpre_10 hpre_5
  all_goals have hly := live_bound hpre_11 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hlx hly
  all_goals have hlen : xs.length = ys.length := by simpa using len_eq (by simp; omega) (by simp; omega) hc_1
  · intro v hv
    rw [eqEvalRust_acc hlen, Option.some.injEq] at hv
    subst hv
    have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    simp [acc, h0, Model.limbs_one, Model.eOne]
  have h0 : xs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  refine loop env p i L xs ys hp hL hnM hmul hk hpre_3 hpre_4 hpre_5 (by assumption) hpre_7 hpre_9 hpre_10 hpre_11 hlen
    (xs.length - 1) 0 _ _ (by omega) ?_
  rv_close
  all_goals first
    | exact start_ptr _
    | (rw [show acc xs ys 0 = 1 from rfl, Model.limbs_one]; rfl)

end Rv64mc.Proof.Multilinear.EqEval
