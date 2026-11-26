/-
  Rv64mc.Proof.Field.ESumCopied

  `E::sum` over a copied slice iterator keeps its contract (`Spec.Field.ESumCopied.spec`), over any program holding
  its template. `rv_auto` runs the entry to the loop's head (instruction 18) and closes the empty slice; the loop is
  `loop`, by induction on the elements left, its invariant the sum of the first `j` elements.
-/

import Rv64mc.Spec.Field.ESum
import Rv64mc.Core.ReprLemmas
import Rv64mc.Proof.Multilinear.SliceLoop
import Rv64mc.Gen.Tmpl.Verifier.Field.E.SumCopiedIterE
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Field.ESumCopied

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field.ESumCopied Rv64mc.Proof.Multilinear

open Rv64mc.Gen.Verifier.Field.E.SumCopiedIterE (Link tmpl)

/-- The sum of the first `j` elements: `acc` after `j` passes of the loop. -/
def acc (es : List Model.Limbs) (j : Nat) : Model.Limbs := (es.take j).foldl Model.eAdd Model.eZero

theorem acc_succ {es : List Model.Limbs} {j : Nat} (hj : j < es.length) :
    acc es (j + 1) = Model.eAdd (acc es j) es[j] := by
  rw [acc, List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hj]; rfl

theorem acc_len (es : List Model.Limbs) : acc es es.length = Model.eSum es := by
  rw [acc, List.take_length]; rfl

theorem shl4_and (x : Word) : x <<< 4 &&& 0xfffffffffffffff0#64 = x <<< 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm := (by decide +kernel : ∀ k : Fin 64, (0xfffffffffffffff0#64).getLsbD k = decide (4 ≤ k.val)) ⟨i, hi⟩
  simp only at hm
  rw [BitVec.getLsbD_and, hm, BitVec.getLsbD_shiftLeft]
  by_cases h : i < 4 <;> simp [h, hi]; omega

/-- The end pointer as the code computes it, from the slice's two ends. -/
theorem end_eq {q : Word} {len : Nat} (_h : 16 * len < 2 ^ 64) :
    q + 8#64 + (q + BitVec.ofNat 64 (16 * len) - q &&& 0xfffffffffffffff0#64) =
      q + 8#64 + BitVec.ofNat 64 len <<< 4 := by
  have e : BitVec.ofNat 64 (16 * len) = BitVec.ofNat 64 len <<< 4 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  rw [show q + BitVec.ofNat 64 (16 * len) - q = BitVec.ofNat 64 (16 * len) by
    rw [BitVec.add_comm, BitVec.add_sub_cancel], e, shl4_and]

theorem len_zero_of {q : Word} {len : Nat} (h : 16 * len < 2 ^ 64) (he : q = q + BitVec.ofNat 64 (16 * len)) :
    len = 0 := by
  have e := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
  have := q.isLt
  omega

/-- The loop's invariant at its head after `j` elements. -/
def Inv (env : Env) (es : List Model.Limbs) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x1 = ret ∧ R .x2 = top ∧ R .x12 = regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64 ∧
    R .x13 = regs .x10 + 8#64 + BitVec.ofNat 64 es.length <<< 4 ∧
    R .x10 = (acc es j).1 ∧ R .x11 = (acc es j).2 ∧
    R .x8 = regs .x8 ∧ R .x9 = regs .x9 ∧ R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧ env.Frame top Tactic.F m M

/-- What one pass computes, from the element the loop loads through the frame. -/
theorem body_val {env : Env} {top : Word} {m M : MachineState} {es : List Model.Limbs} {q : Word} {j : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (he : EListAt m q es)
    (hl : env.Live m q (Layouts.E.byteSize * es.length)) (hj : j < es.length) :
    (M.getMem (q + BitVec.ofNat 64 (16 * j)) ^^^ (acc es j).1,
      M.getMem (q + BitVec.ofNat 64 (16 * j) + 8#64) ^^^ (acc es j).2) = acc es (j + 1) := by
  have ex := EListAt.load (j := j) hf hnx he hl hj
  rw [ex.1, ex.2, acc_succ hj, Model.eAdd, BitVec.xor_comm es[j].1, BitVec.xor_comm es[j].2]

/-- **The loop**, from its head with `k + 1` elements to go. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (es : List Model.Limbs)
    (hp : p[i]? = some (tmpl L))
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (Post es) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hst : env.Static m) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (he : EListAt m (regs .x10) es)
    (hl : env.Live m (regs .x10) (Layouts.E.byteSize * es.length)) :
    ∀ k j R M, j + k + 1 = es.length → Inv env es ret top regs m j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 18, ret, top⟩ :: rest, R, M⟩ := by
  have hq : (regs .x10).toNat + 16 * es.length + 8 < 2 ^ 64 := live_bound hl hnx
  intro k
  induction k with
  | zero =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp
    · exact absurd ((end_iff hq (by omega)).2 (by omega)) hc
    · exact Tactic.static_of_frame hst hinv_19
    · rw [← acc_len, show es.length = j + 1 by omega, ← body_val hinv_19 hnx he hl (by omega)]
    · rw [← acc_len, show es.length = j + 1 by omega, ← body_val hinv_19 hnx he hl (by omega)]
  | succ k ih =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp
    · apply ih (j + 1) _ _ (by omega)
      rv_close
      · exact step_ptr _ _
      · rw [← body_val (j := j) hinv_19 hnx he hl (by omega)]
      · rw [← body_val (j := j) hinv_19 hnx he hl (by omega)]
    all_goals exact absurd ((end_iff hq (by omega)).1 hc) (by omega)

/-- **`E::sum` over a copied slice iterator keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat) :
    spec env p i need := by
  intro es
  rv_auto hp
  all_goals have hq := live_bound hpre_8 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hq
  · obtain rfl := List.eq_nil_of_length_eq_zero (len_zero_of (by omega) hc); rfl
  · obtain rfl := List.eq_nil_of_length_eq_zero (len_zero_of (by omega) hc); rfl
  have h0 : es.length ≠ 0 := fun h => hc (by rw [h]; simp)
  refine loop env p i L es hp hk hpre_4 hpre_5 hpre_6 hpre_8 (es.length - 1) 0 _ _ (by omega) ?_
  rv_close
  · exact start_ptr _
  · exact end_eq (by omega)
  all_goals rfl

end Rv64mc.Proof.Field.ESumCopied
