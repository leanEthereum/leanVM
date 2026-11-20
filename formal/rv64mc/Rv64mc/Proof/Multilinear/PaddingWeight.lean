/-
  Rv64mc.Proof.Multilinear.PaddingWeight

  `padding_weight` keeps its contract (`Spec.Multilinear.PaddingWeight.spec`), over any program holding its
  template, from `E::mul`'s. `rv_auto` runs the entry to the loop's head (instruction 40) and the empty point's
  path, which ends in a tail call of `E::mul`; the loop's invariant `Inv` is the fold of `Model.paddingWeightRust`
  over the first `j` coordinates (`low`). The code computes `ONE + bit(k)` as `!(n >> k) & 1` (`bit_limbs`).
-/

import Rv64mc.Spec.Multilinear.PaddingWeight
import Rv64mc.Spec.Field.EMul
import Rv64mc.Core.ReprLemmas
import Rv64mc.Proof.Multilinear.SliceLoop
import Rv64mc.Gen.Tmpl.Verifier.Multilinear.PaddingWeight
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Multilinear.PaddingWeight

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.PaddingWeight Rv64mc.Proof.Multilinear
open Rv64mc.Gen.Verifier.Multilinear.PaddingWeight (Link tmpl)

/-! ## `ONE + bit(k)` as the code computes it -/

theorem not_and_one (x : BitVec 64) : (x ^^^ 18446744073709551615#64) &&& 1#64 = (x &&& 1#64) ^^^ 1#64 := by
  ext i hi
  by_cases h0 : i = 0
  · subst h0; simp
  · simp [h0]

theorem shift_amt (k : Nat) : (BitVec.ofNat 64 k &&& 63#64).toNat = k % 64 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (63#64).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by norm_num)]

theorem bit_limbs (n : Word) (k : Nat) :
    Model.limbs (1 + Model.bitE n k) =
      ((n >>> (BitVec.ofNat 64 k &&& 63#64).toNat ^^^ 18446744073709551615#64) &&& 1#64, 0#64) := by
  rw [limbs_one_add, Model.bitE, Model.eNew, Model.limbs_ofK, BF64.toBitVec_ofBitVec, shift_amt, not_and_one]

/-! ## The fold -/

/-- One coordinate: `(ONE + bit(k)) * r + (ONE + bit(k) + r) * pad`. -/
def g (n : Word) (pad : E) (rk : E × Nat) : E := (1 + Model.bitE n rk.2) * rk.1 + (1 + Model.bitE n rk.2 + rk.1) * pad

/-- The fold over the first `j` coordinates. -/
def low (xs : List E) (n : Word) (j : Nat) : E := (xs.zipIdx.take j).foldl (g n) 1

theorem low_succ {xs : List E} {n : Word} {j : Nat} (hj : j < xs.length) :
    low xs n (j + 1) = g n (low xs n j) (xs[j], j) := by
  rw [low, List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simpa using hj)]
  simp [low, List.getElem_zipIdx]

theorem paddingWeightRust_low (xs : List E) (n : Word) :
    Model.paddingWeightRust xs n = (1 + Model.bitE n xs.length) * low xs n xs.length := by
  rw [Model.paddingWeightRust, low, List.take_of_length_le (by simp)]; rfl

theorem body_val {M : MachineState} {a n : Word} {c pad : E} {k : Nat}
    (h0 : M.getMem a = (Model.limbs c).1) (h8 : M.getMem (a + 8#64) = (Model.limbs c).2) :
    (Model.eMul (((n >>> (BitVec.ofNat 64 k &&& 63#64).toNat ^^^ 18446744073709551615#64) &&& 1#64) ^^^ M.getMem a,
          M.getMem (a + 8#64)) ((Model.limbs pad).1, (Model.limbs pad).2)).1 ^^^
        (Model.eMul ((n >>> (BitVec.ofNat 64 k &&& 63#64).toNat ^^^ 18446744073709551615#64) &&& 1#64, 0#64)
          (M.getMem a, M.getMem (a + 8#64))).1 = (Model.limbs (g n pad (c, k))).1 ∧
      (Model.eMul (((n >>> (BitVec.ofNat 64 k &&& 63#64).toNat ^^^ 18446744073709551615#64) &&& 1#64) ^^^ M.getMem a,
          M.getMem (a + 8#64)) ((Model.limbs pad).1, (Model.limbs pad).2)).2 ^^^
        (Model.eMul ((n >>> (BitVec.ofNat 64 k &&& 63#64).toNat ^^^ 18446744073709551615#64) &&& 1#64, 0#64)
          (M.getMem a, M.getMem (a + 8#64))).2 = (Model.limbs (g n pad (c, k))).2 := by
  have e1 : Model.limbs (1 + Model.bitE n k + c) =
      (((n >>> (BitVec.ofNat 64 k &&& 63#64).toNat ^^^ 18446744073709551615#64) &&& 1#64) ^^^ (Model.limbs c).1,
        (Model.limbs c).2) := by
    rw [← Model.eAdd_eq, bit_limbs, Model.eAdd, BitVec.zero_xor]
  rw [h0, h8, g, ← Model.eAdd_eq, ← Model.eMul_eq, ← Model.eMul_eq, e1, bit_limbs]
  exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩

/-! ## The counter -/

theorem cnt_step (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.ofNat_add]

theorem cnt_iff {j len : Nat} (hl : len < 2 ^ 64) (hj : j < len) :
    BitVec.ofNat 64 len = BitVec.ofNat 64 j + 1#64 ↔ j + 1 = len := by
  rw [cnt_step, ← BitVec.toNat_inj]; simp; omega

/-! ## The loop -/

/-- The loop's invariant at its head after `j` coordinates. -/
def Inv (env : Env) (xs : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 0xffffffffffffffa0#64 ∧ R .x8 = regs .x12 ∧
    R .x9 = BitVec.ofNat 64 (List.map Model.limbs xs).length ∧ R .x25 = BitVec.ofNat 64 j ∧
    R .x26 = regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64 ∧
    R .x19 = (Model.limbs (low xs (regs .x12) j)).1 ∧ R .x18 = (Model.limbs (low xs (regs .x12) j)).2 ∧
    R .x27 = regs .x27 ∧ env.Frame top Tactic.F m M ∧
    ∀ a, top + 0xffffffffffffffa0#64 ≤ a → M.getMem a =
      ((((((((((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
        (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).setMem
        (top + 0xffffffffffffffd8#64) (regs .x19)).setMem (top + 0xffffffffffffffd0#64) (regs .x20)).setMem
        (top + 0xffffffffffffffc8#64) (regs .x21)).setMem (top + 0xffffffffffffffc0#64) (regs .x22)).setMem
        (top + 0xffffffffffffffb8#64) (regs .x23)).setMem (top + 0xffffffffffffffb0#64) (regs .x24)).setMem
        (top + 0xffffffffffffffa8#64) (regs .x25)).setMem (top + 0xffffffffffffffa0#64) (regs .x26)).getMem a

theorem post_val (xs : List E) (n : Word) :
    Model.eMul ((n >>> (BitVec.ofNat 64 (List.map Model.limbs xs).length &&& 63#64).toNat ^^^
        18446744073709551615#64) &&& 1#64, 0#64)
      ((Model.limbs (low xs n xs.length)).1, (Model.limbs (low xs n xs.length)).2) =
      Model.limbs (Model.paddingWeightRust xs n) := by
  rw [paddingWeightRust_low, ← Model.eMul_eq, bit_limbs, List.length_map]

theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (xs : List E)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need needM : Nat} (hnM : 96 + needM ≤ need)
    (hmul : Spec.Field.EMul.spec env p L.mul.idx needM)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (Post xs) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hx : EListAt m (regs .x10) (xs.map Model.limbs))
    (hlx : env.Live m (regs .x10) (Layouts.E.byteSize * xs.length)) :
    ∀ k j R M, j + k + 1 = xs.length → Inv env xs ret top regs m j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 40, ret, top⟩ :: rest, R, M⟩ := by
  have hq := live_bound hlx hnx
  simp only [Layouts.E.byteSize] at hq
  intro k
  induction k with
  | zero =>
    intro j R M hj hinv
    rv_intro hinv
    have ex := EListAt.load (j := j) hinv_9 hnx hx (by simpa using hlx) (by simp; omega)
    simp only [List.getElem_map] at ex
    rv_sym hp with [hL] using [hmul]
    · exact absurd ((cnt_iff (by simp; omega) (by simp; omega)).2 (by simp; omega)) hc
    · rw [(body_val ex.1 ex.2).1, (body_val ex.1 ex.2).2, ← low_succ (by omega), show j + 1 = xs.length by omega,
        post_val]
    · rw [(body_val ex.1 ex.2).1, (body_val ex.1 ex.2).2, ← low_succ (by omega), show j + 1 = xs.length by omega,
        post_val]
  | succ k ih =>
    intro j R M hj hinv
    rv_intro hinv
    have ex := EListAt.load (j := j) hinv_9 hnx hx (by simpa using hlx) (by simp; omega)
    simp only [List.getElem_map] at ex
    rv_sym hp with [hL] using [hmul]
    · apply ih (j + 1) _ _ (by omega)
      rv_close
      · exact cnt_step j
      · exact step_ptr _ _
      · rw [(body_val ex.1 ex.2).1, ← low_succ (by omega)]
      · rw [(body_val ex.1 ex.2).2, ← low_succ (by omega)]
    all_goals exact absurd ((cnt_iff (by simp; omega) (by simp; omega)).1 hc) (by simp; omega)

/-- **`padding_weight` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM : Nat} (hnM : 96 + needM ≤ need) (hmul : Spec.Field.EMul.spec env p L.mul.idx needM) :
    spec env p i need := by
  intro xs
  rv_auto hp with [hL] using [hmul]
  all_goals have hlx := live_bound hpre_8 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hlx
  · have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [← post_val, h0]; rfl
  · have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [← post_val, h0]; rfl
  have h0 : xs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  refine loop env p i L xs hp hL hnM hmul hk hpre_3 hpre_4 hpre_5 hpre_7 hpre_8
    (xs.length - 1) 0 _ _ (by omega) ?_
  rv_close
  · exact start_ptr _
  · rw [show low xs (regs .x12) 0 = 1 from rfl, Model.limbs_one]; rfl
  · rw [show low xs (regs .x12) 0 = 1 from rfl, Model.limbs_one]; rfl

end Rv64mc.Proof.Multilinear.PaddingWeight
