/-
  Rv64mc.Proof.Multilinear.PolyEval

  `poly_eval` keeps its contract (`Spec.Multilinear.PolyEval.spec`), over any program holding its template, from
  `E::mul`'s. `rv_auto` runs the entry to the loop's head (instruction 36); the loop walks the coefficients from the
  last down, its invariant `Inv` Horner's value over the coefficients above the pointer (`hor`).
-/

import Rv64mc.Spec.Multilinear.PolyEval
import Rv64mc.Core.ReprLemmas
import Rv64mc.Proof.Multilinear.SliceLoop
import Rv64mc.Gen.Tmpl.Verifier.Multilinear.PolyEval
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Multilinear.PolyEval

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.PolyEval Rv64mc.Proof.Multilinear
open Rv64mc.Gen.Verifier.Multilinear.PolyEval (Link tmpl)

/-- Horner's value over the coefficients from `i` on: `acc` once the loop has passed them. -/
def hor (cs : List E) (pt : E) (i : Nat) : E := (cs.drop i).reverse.foldl (fun a c => a * pt + c) 0

theorem hor_step {cs : List E} {pt : E} {i : Nat} (hi : i < cs.length) :
    hor cs pt i = hor cs pt (i + 1) * pt + cs[i] := by
  rw [hor, List.drop_eq_getElem_cons hi, List.reverse_cons, List.foldl_append]; rfl

theorem hor_len (cs : List E) (pt : E) : hor cs pt cs.length = 0 := by simp [hor]

theorem hor_zero (cs : List E) (pt : E) : hor cs pt 0 = Model.polyEvalRust cs pt := by
  simp [hor, Model.polyEvalRust]

theorem step_limbs (a pt c : E) :
    Model.limbs (a * pt + c) = ((Model.eMul (Model.limbs a) (Model.limbs pt)).1 ^^^ (Model.limbs c).1,
      (Model.eMul (Model.limbs a) (Model.limbs pt)).2 ^^^ (Model.limbs c).2) := by
  rw [Model.eMul_eq, ← Model.eAdd_eq, Model.eAdd]

/-! ## The pointer, walking down -/

theorem back_ptr (q : Word) (i : Nat) :
    q + BitVec.ofNat 64 (16 * (i + 1)) + 0xfffffffffffffff8#64 = q + BitVec.ofNat 64 (16 * i) + 8#64 := by
  rw [show 16 * (i + 1) = 16 * i + 16 by omega, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_assoc,
    BitVec.add_assoc, show (BitVec.ofNat 64 16) + 0xfffffffffffffff8#64 = 8#64 by decide]

theorem exit_iff {q : Word} {i : Nat} (hi : 16 * i < 2 ^ 64) :
    q + BitVec.ofNat 64 (16 * i) + 0xfffffffffffffff8#64 = q + 0xfffffffffffffff8#64 ↔ i = 0 := by
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 _), ← BitVec.add_assoc]
  conv => lhs; rhs; rw [← BitVec.add_zero (q + 0xfffffffffffffff8#64)]
  rw [BitVec.add_right_inj, ← BitVec.toNat_inj]; simp; omega

theorem start_ptr {q : Word} {len : Nat} (h : 0 < len) (hl : 16 * len < 2 ^ 64) :
    q + 0xfffffffffffffff8#64 + BitVec.ofNat 64 len <<< 4 = q + BitVec.ofNat 64 (16 * (len - 1)) + 8#64 := by
  have h1 : BitVec.ofNat 64 len <<< 4 = BitVec.ofNat 64 (16 * (len - 1)) + 16#64 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add]; omega
  rw [h1, BitVec.add_comm _ 16#64, ← BitVec.add_assoc, BitVec.add_assoc q,
    show (0xfffffffffffffff8#64 : BitVec 64) + 16#64 = 8#64 by decide, BitVec.add_assoc, BitVec.add_assoc,
    BitVec.add_comm 8#64]

/-! ## The loop -/

/-- The loop's invariant at its head, about to read coefficient `i`. -/
def Inv (env : Env) (cs : List E) (pt : E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (i : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 0xffffffffffffffc0#64 ∧ R .x8 = (Model.limbs pt).2 ∧ R .x9 = (Model.limbs pt).1 ∧
    R .x18 = regs .x10 + 0xfffffffffffffff8#64 ∧ R .x19 = regs .x10 + BitVec.ofNat 64 (16 * i) + 8#64 ∧
    R .x10 = (Model.limbs (hor cs pt (i + 1))).1 ∧ R .x11 = (Model.limbs (hor cs pt (i + 1))).2 ∧
    R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧
    ∀ a, top + 0xffffffffffffffc0#64 ≤ a → M.getMem a =
      (((((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
        (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).setMem
        (top + 0xffffffffffffffd8#64) (regs .x19)).setMem (top + 0xffffffffffffffd0#64) (regs .x20)).setMem
        (top + 0xffffffffffffffc8#64) (regs .x21)).getMem a

theorem body_val {env : Env} {top : Word} {m M : MachineState} {cs : List E} {pt : E} {regs : Reg → Word} {i : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hx : EListAt m (regs .x10) (cs.map Model.limbs)) (hlx : env.Live m (regs .x10) (Layouts.E.byteSize * cs.length))
    (hi : i < cs.length) :
    ((Model.eMul ((Model.limbs (hor cs pt (i + 1))).1, (Model.limbs (hor cs pt (i + 1))).2)
        ((Model.limbs pt).1, (Model.limbs pt).2)).1 ^^^ M.getMem (regs .x10 + BitVec.ofNat 64 (16 * i)),
      (Model.eMul ((Model.limbs (hor cs pt (i + 1))).1, (Model.limbs (hor cs pt (i + 1))).2)
        ((Model.limbs pt).1, (Model.limbs pt).2)).2 ^^^ M.getMem (regs .x10 + BitVec.ofNat 64 (16 * i) + 8#64)) =
      Model.limbs (hor cs pt i) := by
  have ex := EListAt.load (j := i) hf hnx hx (by simpa using hlx) (by simpa using hi)
  simp only [List.getElem_map] at ex
  rw [ex.1, ex.2, hor_step hi, step_limbs]

theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (cs : List E) (pt : E)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need needM : Nat} (hnM : 64 + needM ≤ need)
    (hmul : Spec.Field.EMul.spec env p L.mul.idx needM)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (Post cs pt) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩) (hal : top.toNat % 16 = 0)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hx : EListAt m (regs .x10) (cs.map Model.limbs))
    (hlx : env.Live m (regs .x10) (Layouts.E.byteSize * cs.length)) :
    ∀ j R M, j < cs.length → Inv env cs pt ret top regs m j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 36, ret, top⟩ :: rest, R, M⟩ := by
  have hq := live_bound hlx hnx
  simp only [Layouts.E.byteSize] at hq
  intro j
  induction j with
  | zero =>
    intro R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hmul]
    · exact absurd ((exit_iff (by omega)).2 rfl) hc
    · rw [← hor_zero, ← body_val hinv_14 hnx hx hlx hj]
    · rw [← hor_zero, ← body_val hinv_14 hnx hx hlx hj]
  | succ j ih =>
    intro R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hmul]
    · apply ih _ _ (by omega)
      rv_close
      · exact back_ptr _ _
      · rw [← body_val hinv_14 hnx hx hlx hj]
      · rw [← body_val hinv_14 hnx hx hlx hj]
    all_goals exact absurd ((exit_iff (by omega)).1 hc) (by omega)

/-- **`poly_eval` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM : Nat} (hnM : 64 + needM ≤ need) (hmul : Spec.Field.EMul.spec env p L.mul.idx needM) :
    spec env p i need := by
  intro cs pt
  rv_auto hp with [hL] using [hmul]
  all_goals have hlx := live_bound hpre_8 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hlx
  · have h0 : cs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]
    simp [Model.polyEvalRust, Model.limbs_zero, Model.eZero]
  · have h0 : cs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]
    simp [Model.polyEvalRust, Model.limbs_zero, Model.eZero]
  have h0 : cs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  refine loop env p i L cs pt hp hL hnM hmul hk (by assumption) hpre_3 hpre_4 hpre_5 hpre_7 hpre_8
    (cs.length - 1) _ _ (by omega) ?_
  rv_close
  · rw [List.length_map]; exact start_ptr (by omega) (by omega)
  · rw [show cs.length - 1 + 1 = cs.length by omega, hor_len, Model.limbs_zero]; rfl
  · rw [show cs.length - 1 + 1 = cs.length by omega, hor_len, Model.limbs_zero]; rfl

end Rv64mc.Proof.Multilinear.PolyEval
