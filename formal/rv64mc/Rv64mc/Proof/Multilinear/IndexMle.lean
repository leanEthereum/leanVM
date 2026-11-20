/-
  Rv64mc.Proof.Multilinear.IndexMle

  `index_mle` keeps its contract (`Spec.Multilinear.IndexMle.spec`), over any program holding its template, from
  the contracts of `E::mul` and `E::square`. `rv_auto` runs the entry to the loop's head (instruction 32); the
  loop's invariant `Inv` is the fold of `Model.indexMleRust` over the first `j` coordinates (`st`): the product and
  the generator's power.
-/

import Rv64mc.Spec.Multilinear.IndexMle
import Rv64mc.Spec.Field.EMul
import Rv64mc.Spec.Field.ESquare
import Rv64mc.Core.ReprLemmas
import Rv64mc.Proof.Multilinear.SliceLoop
import Rv64mc.Gen.Tmpl.Verifier.Multilinear.IndexMle
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Multilinear.IndexMle

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.IndexMle Rv64mc.Proof.Multilinear
open Rv64mc.Gen.Verifier.Multilinear.IndexMle (Link tmpl)

/-- One coordinate of the loop: `result *= 1 + c (1 + g)`, `g = g.square()`. -/
def f (acc : E × E) (c : E) : E × E := (acc.1 * (1 + c * (1 + acc.2)), Model.squareE acc.2)

/-- The product and the generator's power after `j` coordinates. -/
def st (xs : List E) (j : Nat) : E × E := (xs.take j).foldl f (1, LeanVM.Protocol.Verifier.gen)

theorem st_succ {xs : List E} {j : Nat} (hj : j < xs.length) : st xs (j + 1) = f (st xs j) xs[j] := by
  rw [st, List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hj]; rfl

theorem indexMleRust_st (xs : List E) : Model.indexMleRust xs = (st xs xs.length).1 := by
  rw [st, List.take_of_length_le (Nat.le_refl _)]; rfl

theorem body_res {M : MachineState} {a : Word} {c : E} (acc : E × E)
    (h0 : M.getMem a = (Model.limbs c).1) (h8 : M.getMem (a + 8#64) = (Model.limbs c).2) :
    Model.eMul ((Model.limbs acc.1).1, (Model.limbs acc.1).2)
        ((Model.eMul (M.getMem a, M.getMem (a + 8#64)) ((Model.limbs acc.2).1 ^^^ 1#64, (Model.limbs acc.2).2)).1 ^^^
          1#64,
          (Model.eMul (M.getMem a, M.getMem (a + 8#64)) ((Model.limbs acc.2).1 ^^^ 1#64, (Model.limbs acc.2).2)).2) =
      Model.limbs (f acc c).1 := by
  rw [h0, h8, f, ← Model.eMul_eq, limbs_one_add, ← Model.eMul_eq, limbs_one_add]

theorem body_g (acc : E × E) (c : E) :
    Model.eSquare ((Model.limbs acc.2).1, (Model.limbs acc.2).2) = Model.limbs (f acc c).2 := by
  rw [f, Model.squareE, Model.eSquare_eq, Model.ofLimbsW_limbs]

/-- The loop's invariant at its head after `j` coordinates. -/
def Inv (env : Env) (xs : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 0xffffffffffffffc0#64 ∧ R .x9 = regs .x10 + BitVec.ofNat 64 (16 * j) ∧
    R .x21 = regs .x10 + BitVec.ofNat 64 (List.map Model.limbs xs).length <<< 4 ∧
    R .x18 = (Model.limbs (st xs j).1).1 ∧ R .x8 = (Model.limbs (st xs j).1).2 ∧
    R .x20 = (Model.limbs (st xs j).2).1 ∧ R .x19 = (Model.limbs (st xs j).2).2 ∧
    R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧
    ∀ a, top + 0xffffffffffffffc0#64 ≤ a → M.getMem a =
      (((((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
        (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).setMem
        (top + 0xffffffffffffffd8#64) (regs .x19)).setMem (top + 0xffffffffffffffd0#64) (regs .x20)).setMem
        (top + 0xffffffffffffffc8#64) (regs .x21)).getMem a

theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (xs : List E)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need needM needS : Nat} (hnM : 64 + needM ≤ need)
    (hnS : 64 + needS ≤ need) (hmul : Spec.Field.EMul.spec env p L.mul.idx needM)
    (hsq : Spec.Field.ESquare.spec env p L.square.idx needS)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (Post xs) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩) (hal : top.toNat % 16 = 0)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hx : EListAt m (regs .x10) (xs.map Model.limbs))
    (hlx : env.Live m (regs .x10) (Layouts.E.byteSize * xs.length)) :
    ∀ k j R M, j + k + 1 = xs.length → Inv env xs ret top regs m j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 32, ret, top⟩ :: rest, R, M⟩ := by
  have hq : (regs .x10).toNat + 16 * (List.map Model.limbs xs).length < 2 ^ 64 := by
    have := live_bound hlx hnx; simp only [Layouts.E.byteSize, List.length_map] at this ⊢; omega
  intro k
  induction k with
  | zero =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hmul, hsq]
    · exact absurd ((end_iff0 hq (by simp; omega)).2 (by simp; omega)) hc
    all_goals have ex := EListAt.load (j := j) hinv_14 hnx hx (by simpa using hlx) (by simpa using (by omega : j < xs.length))
    all_goals simp only [List.getElem_map] at ex
    all_goals have hs := st_succ (xs := xs) (j := j) (by omega)
    all_goals rw [show j + 1 = xs.length by omega] at hs
    · rw [body_res _ ex.1 ex.2, indexMleRust_st, hs]
    · rw [body_res _ ex.1 ex.2, indexMleRust_st, hs]
  | succ k ih =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hmul, hsq]
    · have ex := EListAt.load (j := j) hinv_14 hnx hx (by simpa using hlx) (by simpa using (by omega : j < xs.length))
      simp only [List.getElem_map] at ex
      apply ih (j + 1) _ _ (by omega)
      rv_close
      · exact step_ptr0 _ _
      · rw [body_res _ ex.1 ex.2, st_succ (by omega)]
      · rw [body_res _ ex.1 ex.2, st_succ (by omega)]
      · rw [body_g _ xs[j], st_succ (by omega)]
      · rw [body_g _ xs[j], st_succ (by omega)]
    all_goals exact absurd ((end_iff0 hq (by simp; omega)).1 hc) (by simp; omega)

/-- **`index_mle` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM needS : Nat} (hnM : 64 + needM ≤ need) (hnS : 64 + needS ≤ need)
    (hmul : Spec.Field.EMul.spec env p L.mul.idx needM) (hsq : Spec.Field.ESquare.spec env p L.square.idx needS) :
    spec env p i need := by
  intro xs
  rv_auto hp with [hL] using [hmul, hsq]
  all_goals have hlx := live_bound hpre_8 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hlx
  · have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]; rfl
  · have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]; rfl
  have h0 : xs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  refine loop env p i L xs hp hL hnM hnS hmul hsq hk (by assumption) hpre_3 hpre_4 hpre_5 hpre_7 hpre_8
    (xs.length - 1) 0 _ _ (by omega) ?_
  rv_close
  · exact start_ptr0 _
  · rw [show st xs 0 = (1, LeanVM.Protocol.Verifier.gen) from rfl, Model.limbs_one]; rfl
  · rw [show st xs 0 = (1, LeanVM.Protocol.Verifier.gen) from rfl, Model.limbs_one]; rfl
  · rw [show st xs 0 = (1, LeanVM.Protocol.Verifier.gen) from rfl, Model.limbs_gen]; rfl
  · rw [show st xs 0 = (1, LeanVM.Protocol.Verifier.gen) from rfl, Model.limbs_gen]; rfl

end Rv64mc.Proof.Multilinear.IndexMle
