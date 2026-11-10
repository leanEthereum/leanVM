import Rv64Verifier.Proofs.Bus.VbbTail46

/-!
# `verify_bus_balance`'s side loop: the block's coordinates, arithmetic

The block's form after `j` of its coordinates (`coFold`), the coordinates' loop's write set
(`CoW`), and the loop's bound in `s1` (`b8000798c_x9'`, `bound_eq`, `exit_iff`): the loop stops
after the last coordinate, or dies when the weights run out.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The block's form after `j` of its coordinates `cs`. -/
def coFold (w : List E) (beta : E) (cs : List Form) (j : Nat) : Form :=
  (cs.zipIdx.take j).foldl (fun f c ↦ addScaledRust f c.1 (w.getD c.2 0)) (Form.const beta)

theorem coFold_succ {w : List E} {beta : E} {cs : List Form} {j : Nat} (hj : j < cs.length) :
    coFold w beta cs (j + 1) = addScaledRust (coFold w beta cs j) cs[j] (w.getD j 0) := by
  simp only [coFold]
  rw [List.take_add_one, List.foldl_append,
    List.getElem?_eq_getElem (by simpa using hj)]
  simp [List.getElem_zipIdx]

theorem coFold_all (w : List E) (beta : E) (b : BusBlock) :
    coFold w beta b.coordinates b.coordinates.length = blockFormRust b w beta := by
  simp only [coFold, blockFormRust]
  rw [List.take_of_length_le (by simp)]

/-- What the coordinates' loop writes from `t₀`'s `NEXT` on. -/
def CoW (s t₀ t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 296) 24 ∨ Within a (s.getReg .x2 - 248) 24 ∨
    Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨
    (heapNext t₀ ≤ a.toNat ∧ a.toNat < heapNext t)

theorem CoW.mono {s t₀ t t' : MachineState} (h : heapNext t ≤ heapNext t') {a : Word}
    (ha : CoW s t₀ t a) : CoW s t₀ t' a := by
  rcases ha with ha | ha | ha | ha | ⟨a1, a2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, by omega⟩)))

theorem b8000798c_x9' {s t : MachineState} (h : b8000798c.Holds s t) :
    t.getReg .x9 = ((if BitVec.ult (s.getMem (s.getReg .x2 + 96))
        (s.getMem (s.getReg .x2 + 96) - (((s.getReg .x10 * 8) - 8) >>> 3)) then (1 : Word) else 0) +
      (0xffffffffffffffff : Word)) &&&
        (s.getMem (s.getReg .x2 + 96) - (((s.getReg .x10 * 8) - 8) >>> 3)) :=
  h.reg_eq .x9 rfl (by rv_eval [])

theorem shift_eq {c : Word} (h1 : 1 ≤ c.toNat) (h2 : c.toNat < 2 ^ 60) :
    ((c * 8) - 8) >>> 3 = BitVec.ofNat 64 (c.toNat - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (8 : Word).toNat = 8 from rfl, Nat.shiftRight_eq_div_pow]
  omega

/-- The loop's bound: `W - (c - 1)`, or zero if the weights are fewer. -/
def coBound (W : Word) (c : Nat) : Word := if c - 1 ≤ W.toNat then W - BitVec.ofNat 64 (c - 1) else 0

theorem bound_eq {W c : Word} (h1 : 1 ≤ c.toNat) (h2 : c.toNat < 2 ^ 60) :
    ((if BitVec.ult W (W - (((c * 8) - 8) >>> 3)) then (1 : Word) else 0) +
      (0xffffffffffffffff : Word)) &&&
      (W - (((c * 8) - 8) >>> 3)) = coBound W c.toNat := by
  rw [shift_eq h1 h2, coBound]
  by_cases hle : c.toNat - 1 ≤ W.toNat
  · have hu : BitVec.ult W (W - BitVec.ofNat 64 (c.toNat - 1)) = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    simp only [hu, Bool.false_eq_true, ite_false, hle, ite_true]
    rw [show (0 : Word) + 0xffffffffffffffff = BitVec.allOnes 64 by decide, BitVec.allOnes_and]
  · have hu : BitVec.ult W (W - BitVec.ofNat 64 (c.toNat - 1)) = true := by
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    simp only [hu, ite_true, hle, ite_false]
    rw [show (1 : Word) + 0xffffffffffffffff = 0 by decide]
    exact BitVec.zero_and

theorem exit_iff {wl : Word} {c j : Nat} (hj : j < c) (hjw : j < wl.toNat) (hc : c < 2 ^ 60) :
    wl + 1 - BitVec.ofNat 64 j - 1 = coBound wl c ↔ j + 1 = c := by
  have hwl := wl.isLt
  unfold coBound
  split_ifs with h
  · constructor
    · intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    · intro he
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
  · constructor
    · intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at this
      have h0 : (0 : Word).toNat = 0 := rfl
      omega
    · intro he; omega

theorem addTermRust_length (terms : List LayoutMirror.Term) (m : LayoutMirror.Monomial) (c : E) :
    terms.length ≤ (LayoutMirror.addTermRust terms m c).length := by
  unfold LayoutMirror.addTermRust
  split <;> simp

theorem addScaled_length (f g : LayoutMirror.FormRust) (w : E) :
    f.terms.length ≤ (f.addScaled g w).terms.length := by
  simp only [LayoutMirror.FormRust.addScaled]
  generalize f.terms = A
  induction g.terms generalizing A with
  | nil => exact le_refl _
  | cons t rest ih =>
    simp only [List.foldl_cons]
    exact le_trans (addTermRust_length A t.1 (w * t.2)) (ih _)

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
