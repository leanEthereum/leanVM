import Whir.Algebra
import Whir.Protocol
import Whir.ArrayLayout

/-! Refinement of the executable array arithmetic. Ring laws are hypotheses on
an arbitrary carrier, not axioms or instances for the concrete machine field.
The sum formulas retain truncation and default-valued indexing on malformed inputs. -/
namespace Whir.ArrayAlgebra
open Concrete Protocol
open scoped BigOperators

variable {R : Type*} [CommRing R] [Inhabited R]

omit [Inhabited R] in
theorem message_eval (m : Message R) (claim r : R) :
    m.eval claim r = compactRound claim m.u0 m.u2 r := by
  unfold Message.eval compactRound
  ring

theorem dot_eq_sum (f b : Array R) :
    dot f b = ∑ i ∈ Finset.range (min f.size b.size), f[i]! * b[i]! := by
  unfold dot
  rw [← Array.foldl_toList]
  simp only [tab, Array.toList_map]
  rw [← List.sum_eq_foldl, ← List.sum_toFinset _ List.nodup_range]
  congr 1
  ext i
  simp

omit [Inhabited R] in
private theorem message_loop (xs : List Nat) (a c : Nat → R) (m : Message R) :
    xs.foldl (fun m i => Message.mk (m.u0 + a i) (m.u2 + c i)) m =
      ⟨m.u0 + (xs.map a).sum, m.u2 + (xs.map c).sum⟩ := by
  induction xs generalizing m with
  | nil => cases m; simp
  | cons i xs ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

theorem roundMessage_eq_sum (f b : Array R) (block : Nat) :
    roundMessage f b block =
      ⟨∑ i ∈ Finset.range (f.size / 2),
          f[(i/block)*(2*block)+i%block]! * b[(i/block)*(2*block)+i%block]!,
       ∑ i ∈ Finset.range (f.size / 2),
          (f[(i/block)*(2*block)+i%block]! + f[(i/block)*(2*block)+i%block+block]!) *
          (b[(i/block)*(2*block)+i%block]! + b[(i/block)*(2*block)+i%block+block]!)⟩ := by
  unfold roundMessage
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, pure_bind]
  change (List.range (f.size / 2)).foldl _ _ = _
  rw [message_loop]
  simp only [zero_add]
  congr 1

@[simp] theorem size_weightGlue (b other : Array R) (s : R) :
    (weightGlue b other s).size = b.size := by simp [weightGlue]

theorem dot_weightGlue (f b other : Array R) (s : R)
    (hb : b.size = f.size) (ho : other.size = f.size) :
    dot f (weightGlue b other s) = dot f b + s * dot f other := by
  simp only [dot_eq_sum, size_weightGlue, hb, ho, min_self]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [weightGlue, ArrayLayout.getElem!_tab _ _ _ (by simpa [hb] using Finset.mem_range.mp hi)]
  ring

omit [Inhabited R] in
private theorem honest_pair [CharP R 2] (a a' b b' r : R) :
    a*b + r * (a*b + a'*b' + (a+a')*(b+b')) +
      (r*r)*((a+a')*(b+b')) =
      foldPair a a' r * foldPair b b' r := by
  have h : a*b + a'*b' + (a+a')*(b+b') = a*b' + a'*b := by
    linear_combination b * CharTwo.add_self_eq_zero a +
      b' * CharTwo.add_self_eq_zero a'
  rw [h]
  unfold foldPair
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- Full honest top-lane round. Alignment implies even length; equal lengths
ensure both folded arrays and every source pair have the same valid domain. -/
theorem honest_foldLane [CharP R 2] (f b : Array R) (block lanes : Nat)
    (hf : f.size = (lanes * 2) * block) (hb : b.size = f.size) (r : R) :
    (roundMessage f b block).eval (dot f b) r =
      dot (foldLane f block r) (foldLane b block r) := by
  have half : f.size / 2 = lanes * block := by
    rw [hf, show lanes * 2 * block = lanes * block * 2 by ring, Nat.mul_div_left _ (by decide : 0 < 2)]
  have pairs :
      (∑ j ∈ Finset.range ((lanes * 2) * block), f[j]! * b[j]!) =
      ∑ i ∈ Finset.range (lanes * block),
        (f[(i/block)*(2*block)+i%block]! * b[(i/block)*(2*block)+i%block]! +
         f[(i/block)*(2*block)+i%block+block]! * b[(i/block)*(2*block)+i%block+block]!) := by
    simpa only [Finset.sum_range] using
      ArrayLayout.sum_foldLane_pairs lanes block (fun j => f[j]! * b[j]!)
  rw [roundMessage_eq_sum, dot_eq_sum, hb, min_self, hf, pairs]
  simp only [Message.eval, ← hf, half]
  rw [dot_eq_sum]
  simp only [ArrayLayout.size_foldLane, hb, min_self, half]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < f.size / 2 := by simpa [half] using Finset.mem_range.mp hi
  rw [foldLane, foldLane, ArrayLayout.getElem!_tab _ _ _ hi',
    ArrayLayout.getElem!_tab _ _ _ (by simpa [hb] using hi')]
  exact honest_pair _ _ _ _ _

theorem honest_foldLow [CharP R 2] (f b : Array R) (pairs : Nat)
    (hf : f.size = pairs * 2) (hb : b.size = f.size) (r : R) :
    (roundMessage f b).eval (dot f b) r = dot (foldLow f r) (foldLow b r) := by
  simpa [ArrayLayout.foldLane_one] using
    honest_foldLane f b 1 pairs (by simpa using hf) hb r

/-- Batching the actual transmitted coefficients agrees with batching their
weight arrays. Alignment rules out any access to a truncated/default tail. -/
theorem roundMessage_weightGlue (f b other : Array R) (s : R) (block lanes : Nat)
    (hf : f.size = (lanes * 2) * block) (hb : b.size = f.size) :
    roundMessage f (weightGlue b other s) block =
      (roundMessage f b block).glue (roundMessage f other block) s := by
  have half : f.size / 2 = lanes * block := by
    rw [hf, show lanes * 2 * block = lanes * block * 2 by ring,
      Nat.mul_div_left _ (by decide : 0 < 2)]
  have bounds (i : Nat) (hi : i ∈ Finset.range (f.size / 2)) :
      (i/block)*(2*block)+i%block < b.size ∧
      (i/block)*(2*block)+i%block+block < b.size := by
    have hi' : i < lanes * block := by simpa [half] using Finset.mem_range.mp hi
    have hp : 0 < block := by
      by_contra h
      have : block = 0 := by omega
      simp [this] at hi'
    simpa [hb, hf, Nat.mul_comm lanes 2] using ArrayLayout.foldLane_indices hp hi'
  simp only [roundMessage_eq_sum, Message.glue]
  congr 1 <;> {
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have h := bounds i hi
    simp only [weightGlue, ArrayLayout.getElem!_tab _ _ _ h.1,
      ArrayLayout.getElem!_tab _ _ _ h.2]
    ring }

/-- Interpret an executable pairing as a Boolean first coordinate. The remaining
coordinates are supplied explicitly, so this view covers both low and top lanes. -/
def pairTable {n : Nat} (a : Array R) (block : Nat) (index : Cube n → Nat) :
    Cube (n + 1) → R := fun u =>
  let i := index (fun j => u j.succ)
  a[(i/block)*(2*block)+i%block + if u 0 then block else 0]!

theorem roundMessage_cube {n : Nat} (f b : Array R) (block : Nat)
    (index : Cube n ≃ Fin (f.size / 2)) :
    roundMessage f b block =
      ⟨roundConstant (pairTable b block (fun u => (index u).val))
          (pairTable f block (fun u => (index u).val)),
       roundQuadratic (pairTable b block (fun u => (index u).val))
          (pairTable f block (fun u => (index u).val))⟩ := by
  rw [roundMessage_eq_sum]
  simp only [Finset.sum_range, roundConstant, roundQuadratic, pairTable,
    Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  congr 1 <;> rw [← Equiv.sum_comp index] <;>
    apply Finset.sum_congr rfl <;> intro u _ <;> ring

theorem foldLane_cube [CharP R 2] {n : Nat} (a : Array R) (block : Nat)
    (index : Cube n ≃ Fin (a.size / 2)) (r : R) :
    (fun u => (foldLane a block r)[(index u).val]!) =
      foldFirst (pairTable a block (fun u => (index u).val)) r := by
  funext u
  rw [foldFirst_charTwo]
  simp only [foldLane, ArrayLayout.getElem!_tab _ _ _ (index u).isLt,
    pairTable, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero, foldPair]

/-- The actual message evaluator specializes the pre-existing checked honest
round theorem once its pair layout is interpreted on a Boolean cube. -/
theorem honest_round_cube [CharP R 2] {n : Nat} (f b : Array R) (block : Nat)
    (index : Cube n ≃ Fin (f.size / 2)) (r : R) :
    (roundMessage f b block).eval
        (innerProduct (pairTable b block (fun u => (index u).val))
          (pairTable f block (fun u => (index u).val))) r =
      innerProduct
        (foldFirst (pairTable b block (fun u => (index u).val)) r)
        (foldFirst (pairTable f block (fun u => (index u).val)) r) := by
  rw [message_eval, roundMessage_cube f b block index]
  exact honest_round _ _ _

end Whir.ArrayAlgebra
