import Whir.AnchoredPhysicalAnchor
import Whir.CommitmentAnchor

/-! Refinement of the source occupied-prefix loop. The executable recurrence is `AnchoredPhysicalAnchor.prefixStep`; all sums here are proof specifications only. -/
namespace Whir.AnchorPrefixRefinement
open Concrete Protocol ExecutableOOD SuccinctPointWeight
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 3200000

/-- Dense occupied-prefix equality weight on the lower `j` Boolean lane bits. -/
noncomputable def occupiedPrefix (j count : Nat) (r x : Nat → E) : E :=
  ∑ u : Cube j, if cubeIndex u < count then
    Whir.eqWeight (fun i => r i.val) u * Whir.eqWeight (fun i => x i.val) u else 0

noncomputable def full (j : Nat) (r x : Nat → E) : E :=
  ∏ i : Fin j, (1+r i.val+x i.val)

lemma prefix_zero (j : Nat) (r x : Nat → E) : occupiedPrefix j 0 r x = 0 := by
  simp [occupiedPrefix]

lemma prefix_full (j : Nat) (r x : Nat → E) : occupiedPrefix j (2^j) r x = full j r x := by
  simp only [occupiedPrefix, cubeIndex_lt, ↓reduceIte]
  rw [show (∑ u : Cube j, Whir.eqWeight (fun i => r i.val) u *
      Whir.eqWeight (fun i => x i.val) u) =
      Whir.mle (Whir.eqWeight (fun i : Fin j => r i.val)) (fun i => x i.val) by
    unfold Whir.mle innerProduct
    apply Finset.sum_congr rfl
    intro u _
    ring]
  exact mle_eqWeight _ _

lemma full_zero (r x : Nat → E) : full 0 r x = 1 := by simp [full]
lemma full_succ (j : Nat) (r x : Nat → E) :
    full (j+1) r x = full j r x * (1+r j+x j) := by
  simp [full, Fin.prod_univ_castSucc]

lemma prefix_base (count : Nat) (r x : Nat → E) :
    occupiedPrefix 0 count r x = if 0 < count then 1 else 0 := by
  simp [occupiedPrefix, cubeIndex, Whir.eqWeight]

lemma eqWeight_nat_split (d k : Nat) (r : Nat → E) (a : Cube d) (b : Cube k) :
    Whir.eqWeight (fun i : Fin (d+k) => r i.val) (Fin.addCases a b) =
      Whir.eqWeight (fun i : Fin d => r i.val) a *
        Whir.eqWeight (fun i : Fin k => r (d+i.val)) b := by
  simp [Whir.eqWeight, Fin.prod_univ_add]

lemma prefix_split (j count : Nat) (r x : Nat → E) :
    occupiedPrefix (j+1) count r x =
      (1+r j)*(1+x j)*occupiedPrefix j count r x +
      (r j*x j)*occupiedPrefix j (count-2^j) r x := by
  unfold occupiedPrefix
  rw [← Equiv.sum_comp (cubeAppendEquiv j 1)]
  simp only [Fintype.sum_prod_type, cubeAppendEquiv, Equiv.coe_fn_mk,
    cubeIndex_append, eqWeight_nat_split]
  rw [Finset.sum_comm, sum_cube_succ]
  simp only [Fin.cons_zero, Bool.false_eq_true, ↓reduceIte, cubeIndex,
    Nat.mul_zero, Nat.add_zero]
  simp only [Whir.eqWeight, Fintype.sum_unique]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, ↓reduceIte, Fin.val_zero, Nat.zero_add, Nat.add_zero,
    CharTwo.sub_eq_add, mul_one]
  simp only [show ∀ a : Cube j, cubeIndex a + 2^j < count ↔
      cubeIndex a < count-2^j by intro a; omega, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro a _
  all_goals split_ifs <;> first | omega | ring

lemma prefix_of_ge (j count : Nat) (r x : Nat → E) (h : 2^j ≤ count) :
    occupiedPrefix j count r x = full j r x := by
  rw [← prefix_full]
  unfold occupiedPrefix
  apply Finset.sum_congr rfl
  intro u _
  simp only [cubeIndex_lt, ↓reduceIte,
    show cubeIndex u < count from lt_of_lt_of_le (cubeIndex_lt u) h]

lemma remainder_succ (n j : Nat) :
    n % 2^(j+1) = n % 2^j + 2^j*(n.testBit j).toNat := by
  have h := Nat.mod_add_div (n % (2^j*2)) (2^j)
  simpa only [pow_succ, Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self,
    Nat.toNat_testBit] using h.symm

lemma prefix_remainder_succ (n j : Nat) (r x : Nat → E) :
    occupiedPrefix (j+1) (n % 2^(j+1)) r x =
      if n.testBit j then
        (1+r j)*(1+x j)*full j r x +
          (r j*x j)*occupiedPrefix j (n % 2^j) r x
      else (1+r j)*(1+x j)*occupiedPrefix j (n % 2^j) r x := by
  rw [prefix_split, remainder_succ]
  have hlt := Nat.mod_lt n (Nat.two_pow_pos j)
  cases hb : n.testBit j
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt), prefix_zero, mul_zero, add_zero]
  · simp only [Bool.toNat_true, Nat.mul_one, ↓reduceIte]
    rw [prefix_of_ge j _ r x (by omega)]
    simp only [Nat.add_sub_cancel]

lemma coordinate_lo (r x : E) : (1+r)*(1+x) = (1+r+x)+r*x := by ring

open AnchoredPhysicalAnchor AnchoredHeaderCodec
open AnchorPrefixRefinementArith

def laneCoordinates (shape : Shape) (r : Array E) (j : Nat) : E :=
  r[shape.logN-shape.logBatch+j]!

/-- Before the first occupied count bit, `partial = 1` is a sentinel, never a claimed empty-prefix sum. The full cube is required only while unprocessed count bits can consume it. -/
structure Invariant (shape : Shape) (r x : Array E) (j : Nat) (s : PrefixState) : Prop where
  started : s.started = decide (shape.lanes % 2^j ≠ 0)
  «partial» : s.partial = if shape.lanes % 2^j = 0 then 1 else
    occupiedPrefix j (shape.lanes % 2^j) (laneCoordinates shape r) (laneCoordinates shape x)
  full : shape.lanes >>> j ≠ 0 →
    s.full = full j (laneCoordinates shape r) (laneCoordinates shape x)

lemma initial_invariant (shape : Shape) (r x : Array E) :
    Invariant shape r x 0 {} := by
  constructor <;> simp [Nat.mod_one, full_zero]

lemma step_invariant (shape : Shape) (r x : Array E) (j : Nat) (s : PrefixState)
    (h : Invariant shape r x j s) :
    Invariant shape r x (j+1) (prefixStep shape r x j s) := by
  have hm := Nat.mod_lt shape.lanes (Nat.two_pow_pos j)
  have hp := prefix_remainder_succ shape.lanes j (laneCoordinates shape r) (laneCoordinates shape x)
  have hr := remainder_succ shape.lanes j
  have hc : shape.lanes >>> (j+1) ≠ 0 → shape.lanes >>> j ≠ 0 := by
    simp only [Nat.shiftRight_eq_div_pow, pow_succ]
    intro hn hz
    rw [← Nat.div_div_eq_div_mul, hz] at hn
    simp at hn
  have hbfull : shape.lanes.testBit j = true → shape.lanes >>> j ≠ 0 := by
    simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, Nat.shiftRight_eq_div_pow]
    intro hb hz
    simp [hz] at hb
  have startedStep : (prefixStep shape r x j s).started = (shape.lanes.testBit j || s.started) := by
    cases hb : shape.lanes.testBit j <;> cases hs : s.started <;>
      by_cases hn : shape.lanes >>> (j+1) ≠ 0 <;>
      simp [prefixStep, prefixStepWith, native, native_factor, hb, hs, hn]
  have partialStep : (prefixStep shape r x j s).partial =
      if shape.lanes.testBit j then
        (if s.started then laneCoordinates shape r j*laneCoordinates shape x j*s.partial else 0) +
          (1+laneCoordinates shape r j+laneCoordinates shape x j+
            laneCoordinates shape r j*laneCoordinates shape x j) *
          (if j = 0 then 1 else s.full)
      else if s.started then
        (1+laneCoordinates shape r j+laneCoordinates shape x j+
          laneCoordinates shape r j*laneCoordinates shape x j)*s.partial
      else s.partial := by
    cases hb : shape.lanes.testBit j <;> cases hs : s.started <;>
      by_cases hn : shape.lanes >>> (j+1) ≠ 0
    all_goals
      simp only [prefixStep, prefixStepWith, native, native_factor, hb, hs, hn,
        Bool.or_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte, laneCoordinates]
      all_goals try (by_cases hj : j = 0 <;> simp [hj])
    all_goals first | rfl | (split <;> rfl)
  have fullStep : (prefixStep shape r x j s).full =
      if shape.lanes >>> (j+1) ≠ 0 then
        (if j = 0 then 1+laneCoordinates shape r j+laneCoordinates shape x j
          else s.full*(1+laneCoordinates shape r j+laneCoordinates shape x j))
      else s.full := by
    cases hb : shape.lanes.testBit j <;> cases hs : s.started <;>
      by_cases hn : shape.lanes >>> (j+1) ≠ 0 <;>
      simp [prefixStep, prefixStepWith, native, native_factor, hb, hs, hn, laneCoordinates]
    all_goals rfl
  constructor
  · rw [startedStep, h.started, hr]
    cases hb : shape.lanes.testBit j <;> simp [Bool.toNat_false, Bool.toNat_true]
  · rw [partialStep, h.started, h.partial]
    cases hb : shape.lanes.testBit j
    · simp only [hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Bool.false_eq_true,
        ↓reduceIte] at hr hp ⊢
      rw [hr]
      by_cases hz : shape.lanes % 2^j = 0
      · simp [hz]
      · rw [hr] at hp
        simp [hz]
        rw [hp, coordinate_lo]
    · have hf := h.full (hbfull hb)
      have hn : shape.lanes % 2^(j+1) ≠ 0 := by
        rw [hr]; simp only [hb, Bool.toNat_true, Nat.mul_one]
        have ht := Nat.two_pow_pos j
        omega
      simp only [hb, Bool.toNat_true, Nat.mul_one, ↓reduceIte] at hr hp ⊢
      rw [ite_eq_right hn, hp]
      have lower : (if j = 0 then (1 : E) else s.full) =
          full j (laneCoordinates shape r) (laneCoordinates shape x) := by
        split_ifs with hj
        · subst j; simp [full_zero]
        · exact hf
      rw [lower, ← coordinate_lo]
      by_cases hz : shape.lanes % 2^j = 0
      · simp [hz, prefix_zero]
      · simp [hz]; ring
  · intro hn
    rw [fullStep, ite_eq_left hn]
    have hf := h.full (hc hn)
    split_ifs with hj
    · subst j; simp [full_succ, full_zero]
    · rw [hf, full_succ]

lemma loop_invariant (shape : Shape) (r x : Array E) (j : Nat) :
    Invariant shape r x j
      ((List.range j).foldl (fun s i => prefixStep shape r x i s) {}) := by
  induction j with
  | zero => exact initial_invariant shape r x
  | succ j ih =>
    rw [List.range_succ, List.foldl_append]
    exact step_invariant shape r x j _ ih

lemma eqTable_cube {n : Nat} (r : Fin n → E) (u : Cube n) :
    (Concrete.eqTable (Array.ofFn r))[cubeIndex u]! = Whir.eqWeight r u := by
  induction n with
  | zero => simp [cubeIndex, Whir.eqWeight, Array.ofFn_zero]
  | succ n ih =>
    rw [Array.ofFn_succ']
    have hh := TerminalRefinement.eqTable_cons_get (r 0)
      (Array.ofFn (fun i => r i.succ)) (cubeIndex (fun i => u i.succ))
      (by simpa using cubeIndex_lt (fun i => u i.succ))
    have hu : u = Fin.cons (u 0) (fun i => u i.succ) := by
      ext i; exact Fin.cases rfl (fun _ => rfl) i
    rw [hu]
    cases hb : u 0
    · simpa [cubeIndex_cons, ← hu, Whir.eqWeight, Fin.prod_univ_succ, hb, ih,
        CharTwo.sub_eq_add, mul_comm] using hh.1
    · simpa [cubeIndex_cons, ← hu, Whir.eqWeight, Fin.prod_univ_succ, hb, ih,
        mul_comm] using hh.2

lemma occupied_cube_mle (d k lanes : Nat) (r x : Nat → E) :
    Whir.mle (fun u : Cube (d+k) =>
      if cubeIndex u < lanes*2^d then
        Whir.eqWeight (fun i => r i.val) u else 0) (fun i => x i.val) =
      full d r x * occupiedPrefix k lanes (fun j => r (d+j)) (fun j => x (d+j)) := by
  unfold Whir.mle innerProduct
  rw [← Equiv.sum_comp (cubeAppendEquiv d k)]
  simp only [Fintype.sum_prod_type, cubeAppendEquiv, Equiv.coe_fn_mk,
    cubeIndex_append, eqWeight_nat_split]
  have bound (a : Cube d) (b : Cube k) :
      cubeIndex a + 2^d*cubeIndex b < lanes*2^d ↔ cubeIndex b < lanes := by
    have ha := cubeIndex_lt a
    have hd := Nat.two_pow_pos d
    constructor
    · intro h
      by_contra hn
      have hb : lanes ≤ cubeIndex b := by omega
      have hm := Nat.mul_le_mul_left (2^d) hb
      rw [Nat.mul_comm lanes] at h
      omega
    · intro h
      have hm := Nat.mul_le_mul_left (2^d) (show cubeIndex b+1 ≤ lanes by omega)
      rw [Nat.mul_add] at hm
      rw [Nat.mul_comm lanes]
      simp only [Nat.mul_one] at hm
      omega
  simp_rw [bound]
  rw [Finset.sum_comm]
  have term (b : Cube k) :
      (∑ a : Cube d,
        (Whir.eqWeight (fun i : Fin d => x i.val) a *
          Whir.eqWeight (fun i : Fin k => x (d+i.val)) b) *
        if cubeIndex b < lanes then
          Whir.eqWeight (fun i : Fin d => r i.val) a *
            Whir.eqWeight (fun i : Fin k => r (d+i.val)) b else 0) =
      full d r x * (if cubeIndex b < lanes then
        Whir.eqWeight (fun i : Fin k => r (d+i.val)) b *
          Whir.eqWeight (fun i : Fin k => x (d+i.val)) b else 0) := by
    rw [← prefix_full]
    unfold occupiedPrefix
    simp only [cubeIndex_lt, ↓reduceIte, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  simp_rw [term]
  rw [← Finset.mul_sum]
  rfl

lemma ofFn_bang (a : Array E) :
    Array.ofFn (fun i : Fin a.size => a[i.val]!) = a := by
  convert Array.ofFn_getElem (xs := a) using 1
  apply congrArg Array.ofFn
  funext i
  exact getElem!_pos a i.val i.isLt

lemma occupied_cube_mle_dim (n d k lanes : Nat) (hd : d+k = n) (r x : Nat → E) :
    Whir.mle (fun u : Cube n =>
      if cubeIndex u < lanes*2^d then Whir.eqWeight (fun i => r i.val) u else 0)
      (fun i => x i.val) =
      full d r x * occupiedPrefix k lanes (fun j => r (d+j)) (fun j => x (d+j)) := by
  subst n
  exact occupied_cube_mle d k lanes r x

lemma full_split_dim (n d k : Nat) (hd : d+k = n) (r x : Nat → E) :
    full n r x = full d r x * full k (fun j => r (d+j)) (fun j => x (d+j)) := by
  subst n
  simp [full, Fin.prod_univ_add]

lemma dense_weight (c : Config) (lanes : Nat) (r x : Array E)
    (hr : r.size = c.logN) (hx : x.size = c.logN)
    (hk : c.folds[0]! ≤ c.logN) :
    Concrete.mle (CommitmentAnchor.weight c lanes r) x =
      full (c.logN-c.folds[0]!) (fun j => r[j]!) (fun j => x[j]!) *
        occupiedPrefix c.folds[0]! lanes
          (fun j => r[c.logN-c.folds[0]!+j]!)
          (fun j => x[c.logN-c.folds[0]!+j]!) := by
  have hs : c.logN-c.folds[0]!+c.folds[0]! = c.logN := by omega
  have rx : Array.ofFn (fun i : Fin c.logN => x[i.val]!) = x := by
    apply Array.ext
    · simp [hx]
    · intro i hi hj
      simp only [Array.getElem_ofFn]
      exact getElem!_pos x i hj
  have rr : Array.ofFn (fun i : Fin c.logN => r[i.val]!) = r := by
    apply Array.ext
    · simp [hr]
    · intro i hi hj
      simp only [Array.getElem_ofFn]
      exact getElem!_pos r i hj
  have er (u : Cube c.logN) :
      (Concrete.eqTable r)[cubeIndex u]! = Whir.eqWeight (fun i => r[i.val]!) u := by
    have h := eqTable_cube (fun i : Fin c.logN => r[i.val]!) u
    rwa [rr] at h
  conv_lhs => rw [← rx]
  rw [ExecutableOOD.mle_eq_cube _ _ (by simp [CommitmentAnchor.weight])]
  have hd : ExecutableOOD.decode c.logN (CommitmentAnchor.weight c lanes r) =
      fun u => if cubeIndex u < lanes*2^(c.logN-c.folds[0]!) then
        Whir.eqWeight (fun i => r[i.val]!) u else 0 := by
    funext u
    simp only [ExecutableOOD.decode, CommitmentAnchor.weight,
      ArrayLayout.getElem!_tab _ _ _ (cubeIndex_lt u)]
    rw [er]
    simp only [← FieldModel.E_zero_def]
  rw [hd]
  exact occupied_cube_mle_dim c.logN (c.logN-c.folds[0]!) c.folds[0]! lanes hs
    (fun j => r[j]!) (fun j => x[j]!)

lemma low_fold (n : Nat) (r x : Nat → E) :
    (List.range n).foldl (fun acc j => acc*(1+r j+x j)) 1 = full n r x := by
  induction n with
  | zero => simp [full_zero]
  | succ n ih => simp only [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ih, full_succ]

lemma partial_terminal (shape : Shape) (r x : Array E)
    (hn : 0 < shape.lanes) (hlt : shape.lanes < 2^shape.logBatch) :
    ((List.range shape.logBatch).foldl (fun s i => prefixStep shape r x i s) {}).partial =
      occupiedPrefix shape.logBatch shape.lanes (laneCoordinates shape r) (laneCoordinates shape x) := by
  have hp := (loop_invariant shape r x shape.logBatch).partial
  simpa only [Nat.mod_eq_of_lt hlt, Nat.ne_of_gt hn, ↓reduceIte] using hp

/-- Source terminal evaluation equals the actual dense occupied-prefix claim. No lane-count power-of-two or selector-alignment restriction is imposed. -/
theorem anchorAt_dense (c : Config) (shape : Shape) (r x : Array E)
    (hN : shape.logN = c.logN) (hB : shape.logBatch = c.folds[0]!)
    (occupied : 0 < shape.lanes ∧ shape.lanes ≤ 2^shape.logBatch)
    (dimensions : shape.logBatch < shape.logN)
    (hr : r.size = shape.logN) (hx : x.size = shape.logN) :
    anchorAt shape r x = Concrete.mle (CommitmentAnchor.weight c shape.lanes r) x := by
  rw [dense_weight c shape.lanes r x (hr.trans hN) (hx.trans hN) (by omega)]
  by_cases hc : shape.lanes = 2^shape.logBatch
  · simp only [anchorAt_unfold, hc, ↓reduceIte]
    rw [low_fold, ← hB, prefix_full]
    exact full_split_dim r.size (c.logN-shape.logBatch) shape.logBatch
      (by omega) (fun j => r[j]!) (fun j => x[j]!)
  · simp only [anchorAt_unfold, hc, ↓reduceIte]
    rw [partial_terminal shape r x occupied.1 (by omega), low_fold]
    have coords (a : Array E) : laneCoordinates shape a =
        fun j => a[c.logN-c.folds[0]!+j]! := by
      funext j
      simp [laneCoordinates, hN, hB]
    rw [coords r, coords x]
    simp only [hN, hB]

#print axioms step_invariant
#print axioms dense_weight
#print axioms anchorAt_dense

end Whir.AnchorPrefixRefinement
