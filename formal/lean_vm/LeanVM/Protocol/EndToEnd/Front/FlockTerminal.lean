/-
  LeanVM.Protocol.EndToEnd.Front.FlockTerminal

  The program's lincheck terminal value equals ArkLib's `linTerminal`, given that the program's
  forward walk of the BLAKE2s circuit computes the R1CS's left and right products.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.RingMultilinear

/-!
# The lincheck's terminal

`progTerminal` (`verifier.py:1152-1176, 1179-1294` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) against ArkLib's `linTerminal`
(`ToArkLib/Flock/Tables.lean`):

* the skip weights `lagrange_weights(64, z_skip)` are ArkLib's `skipWeights` over the skip domain
  `φ_8(0), …, φ_8(63)`, an `F_2`-subspace (`lagrangeWeights_skip`);
* `eq_kernel(point)` is CompPoly's `lagrangeBasis`, the first coordinate the lowest bit
  (`eqKernel_getD`);
* the row and column weights, built with `flatMap` over the equality kernel of the block's
  coordinates and the 64 skip positions, are ArkLib's `eRow` and `wCol` at `cubeIndex`
  (`flatMap_getD`);
* `eq_eval(χ_in, χ'_in)` is `eqTilde` in characteristic two;
* the forward walk `blake2s_row_values` is the R1CS's `rows`: this is `WalkFaithful`, the one
  hypothesis of this module, a statement about the deployed circuit and the program's walk alone.

`terminalFaithful`: `WalkFaithful F → TerminalFaithful F`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval
open scoped ENNReal NNReal

@[expose] public section

/-! ## The skip domain's Lagrange weights -/

/-- **The skip domain's denominators are the window's**: the nodes `φ_8(0), …, φ_8(2^b - 1)` are an
`F_2`-subspace. -/
theorem prod_sub_nodes_pow (b : ℕ) (i : Fin (2 ^ b)) :
    ∏ j ∈ Finset.univ.erase i, (ofK (Flock.phi8 i) - ofK (Flock.phi8 j)) =
      ∏ k ∈ Finset.range (2 ^ b - 1), phi (k + 1) := by
  have hsub : ∀ j : Fin (2 ^ b), ofK (Flock.phi8 i) - ofK (Flock.phi8 j) =
      ofK (Flock.phi8 (i.val ^^^ j.val)) := fun j ↦ by
    rw [phi8_xor, ofK_add, CharTwo.sub_eq_add]
  simp only [hsub]
  have hlt : ∀ j : Fin (2 ^ b), i.val ^^^ j.val < 2 ^ b := fun j ↦
    Nat.xor_lt_two_pow i.isLt j.isLt
  refine Finset.prod_bij' (fun j _ ↦ (i.val ^^^ j.val) - 1)
    (fun k hk ↦ ⟨i.val ^^^ (k + 1), Nat.xor_lt_two_pow i.isLt
      (by simp at hk; omega)⟩) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hne : i.val ^^^ j.val ≠ 0 := fun h ↦
      (Finset.mem_erase.mp hj).1 (Fin.ext (eq_of_xor_eq_zero h).symm)
    have := hlt j
    simp
    omega
  · intro k hk
    have hk' : k + 1 < 2 ^ b := by simp at hk; omega
    refine Finset.mem_erase.mpr ⟨fun h ↦ ?_, Finset.mem_univ _⟩
    have h' := congrArg Fin.val h
    simp only at h'
    have := xor_xor_cancel i.val (k + 1)
    rw [h', Nat.xor_self] at this
    omega
  · intro j hj
    have hne : i.val ^^^ j.val ≠ 0 := fun h ↦
      (Finset.mem_erase.mp hj).1 (Fin.ext (eq_of_xor_eq_zero h).symm)
    apply Fin.ext
    simp only
    rw [Nat.sub_add_cancel (by omega), xor_xor_cancel]
  · intro k hk
    simp only
    rw [xor_xor_cancel]
    exact Nat.add_sub_cancel k 1
  · intro j hj
    have hne : i.val ^^^ j.val ≠ 0 := fun h ↦
      (Finset.mem_erase.mp hj).1 (Fin.ext (eq_of_xor_eq_zero h).symm)
    rw [Nat.sub_add_cancel (by omega)]
    rfl

/-- The skip nodes of the deployed domain are `φ_8(0), …, φ_8(63)`. -/
theorem skipNodes_getElem (j : Fin (2 ^ Flock.kSkip)) :
    (Flock.skipNodes flockSkipDomain.pts)[j] = ofK (Flock.phi8 j) := by
  show (Flock.skipNodes flockNodes)[j] = _
  simp only [Flock.skipNodes, flockNodes, Fin.getElem_fin, Vector.getElem_ofFn]
  rfl

/-- **The program's skip weights are ArkLib's** over the skip domain. -/
theorem lagrangeWeights_skip (Y : E) (i : Fin (2 ^ Flock.kSkip)) :
    (lagrangeWeights 64 Y).getD i 0 = (Flock.skipWeights flockSkipDomain Y)[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [length_lagrangeWeights]; exact i.isLt), Option.getD_some,
    lagrangeWeights_getElem 64 Y i i.isLt, Flock.skipWeights_getElem, lagrangeWeight]
  simp only [skipNodes_getElem]
  have hd := prod_sub_nodes_pow Flock.kSkip i
  rw [show (2 : ℕ) ^ Flock.kSkip - 1 = 64 - 1 from rfl] at hd
  rw [windowDenominator_eq, ← hd]
  congr 1
  symm
  have h64 : (2 : ℕ) ^ Flock.kSkip = 64 := rfl
  refine Finset.prod_bij' (fun j _ ↦ j.val) (fun k hk ↦ ⟨k, by
    have := (Finset.mem_erase.mp hk).2; rw [h64]; simpa using this⟩) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_erase.mp hj).1 (Fin.ext h), by
      have : j.val < 64 := h64 ▸ j.isLt
      simpa using this⟩
  · intro k hk
    exact Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_erase.mp hk).1 (congrArg Fin.val h),
      Finset.mem_univ _⟩
  · intro j _
    rfl
  · intro k _
    rfl
  · intro j _
    rw [CharTwo.sub_eq_add]
    rfl

/-! ## The equality kernel -/

/-- One more coordinate doubles the kernel: the old weights times `1 + r`, then times `r`. -/
theorem eqKernel_append (l : List E) (r : E) :
    eqKernel (l ++ [r]) = (eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r) := by
  simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The kernel has `2^n` weights. -/
theorem length_eqKernel (l : List E) : (eqKernel l).length = 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l r ih =>
    rw [eqKernel_append, List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ, mul_two]

/-- **The kernel's weight at `x`**: `Π_j (r_j if bit j of x else 1 + r_j)`, the first coordinate the
lowest bit. -/
theorem eqKernel_getElem (l : List E) (x : ℕ) (hx : x < (eqKernel l).length) :
    (eqKernel l)[x] =
      ∏ j ∈ Finset.range l.length, (if x.testBit j then l.getD j 0 else 1 + l.getD j 0) := by
  induction l using List.reverseRecOn generalizing x with
  | nil =>
    have : x = 0 := by simpa [eqKernel] using hx
    subst this
    rfl
  | append_singleton l r ih =>
    have hlen := length_eqKernel l
    have hgetD : ∀ j < l.length, (l ++ [r]).getD j 0 = l.getD j 0 := fun j hj ↦ by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have hlast : (l ++ [r]).getD l.length 0 = r := by simp [List.getD_eq_getElem?_getD]
    simp only [eqKernel_append]
    rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
    by_cases hlo : x < 2 ^ l.length
    · rw [List.getElem_append_left (by simp [hlen, hlo]), List.getElem_map,
        ih x (by rw [hlen]; exact hlo), Nat.testBit_lt_two_pow hlo, hlast]
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by rw [hgetD j (Finset.mem_range.mp hj)]
    · have hx' : x < 2 ^ l.length + 2 ^ l.length := by
        simp [eqKernel_append, hlen] at hx
        omega
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ l.length + y := ⟨x - 2 ^ l.length, by omega⟩
      have hy : y < 2 ^ l.length := by omega
      rw [List.getElem_append_right (by simp [hlen]), List.getElem_map]
      simp only [List.length_map, hlen, Nat.add_sub_cancel_left]
      rw [ih y (by rw [hlen]; exact hy), Nat.testBit_two_pow_add_eq,
        Nat.testBit_lt_two_pow hy, hlast]
      simp only [Bool.not_false, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by
        rw [hgetD j (Finset.mem_range.mp hj),
          Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hj)]

/-- **The program's kernel is CompPoly's `lagrangeBasis`**, the first coordinate the lowest bit,
in characteristic two. -/
theorem lagrangeBasis_toVec {n : ℕ} {l : List E} (hl : l.length = n) (x : Fin (2 ^ n)) :
    (lagrangeBasis (toVec n l))[x] = (eqKernel l)[x.val]'(by
      rw [length_eqKernel, hl]; exact x.isLt) := by
  rw [lagrangeBasis_getElem, eqKernel_getElem, hl,
    ← Fin.prod_univ_eq_prod_range (fun j ↦ if x.val.testBit j then l.getD j 0 else 1 + l.getD j 0)]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [BitVec.getLsb_eq_getElem, BitVec.getElem_ofFin, toVec, Fin.getElem_fin,
    Vector.getElem_ofFn, CharTwo.sub_eq_add]

/-! ## Tensor products as `flatMap` -/

/-- The length of a tensor product built with `flatMap`. -/
theorem length_flatMap_map (A B : List E) (f : E → E → E) :
    (A.flatMap fun a ↦ B.map (f a)).length = A.length * B.length := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons]
    ring

/-- **Entry `j · |B| + i` of a tensor product** is `f A_j B_i`. -/
theorem flatMap_map_getD (A B : List E) (f : E → E → E) {j i : ℕ} (hj : j < A.length)
    (hi : i < B.length) :
    (A.flatMap fun a ↦ B.map (f a)).getD (j * B.length + i) 0 = f (A.getD j 0) (B.getD i 0) := by
  induction A generalizing j with
  | nil => simp at hj
  | cons a A ih =>
    rw [List.flatMap_cons]
    cases j with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by simpa using hi)]
      simp [List.getD_eq_getElem?_getD, hi]
    | succ j =>
      rw [List.getD_append_right _ _ _ _ (by simp; rw [Nat.succ_mul]; omega)]
      have e : (j + 1) * B.length + i - (B.map (f a)).length = j * B.length + i := by
        simp [Nat.succ_mul]; omega
      rw [e, ih (by simpa using hj)]
      simp

/-- **The program's column weights are ArkLib's `wCol`**: the slices times the equality kernel of
the block's coordinates, the slice index low. -/
theorem toVec_wCol {s m : ℕ} {sv l : List E} (hsv : sv.length = 2 ^ s) (hl : l.length = m) :
    toVec (2 ^ (s + m)) ((eqKernel l).flatMap fun w ↦ sv.map (· * w)) =
      Flock.wCol (toVec (2 ^ s) sv) (toVec m l) := by
  apply Vector.ext
  intro k hk
  obtain ⟨⟨i, jin⟩, hij⟩ := (cubeSplit s m).surjective ⟨k, hk⟩
  rw [cubeSplit_apply] at hij
  have hk' : k = jin.val * sv.length + i.val := by
    have := congrArg Fin.val hij
    simp only [cubeIndex] at this
    rw [hsv]
    linarith [this]
  have hw := Flock.wCol_cubeIndex (toVec (2 ^ s) sv) (toVec m l) i jin
  simp only [Fin.getElem_fin] at hw
  have hkc : k = (cubeIndex i jin).val := by rw [hij]
  subst hkc
  have hlb : (lagrangeBasis (toVec m l))[jin.val] = (eqKernel l)[jin.val]'(by
      rw [length_eqKernel, hl]; exact jin.isLt) := by
    have := lagrangeBasis_toVec hl jin
    simpa only [Fin.getElem_fin] using this
  rw [hw, hlb]
  simp only [toVec, Vector.getElem_ofFn]
  have hjin : jin.val < (eqKernel l).length := by rw [length_eqKernel, hl]; exact jin.isLt
  rw [hk', flatMap_map_getD _ _ _ hjin (by rw [hsv]; exact i.isLt), mul_comm]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjin, mul_comm]

/-- **The program's row weights are ArkLib's `eRow`**: the equality kernel of the block's
coordinates times the skip weights, the skip index low. -/
theorem toVec_eRow {s m : ℕ} (nodes : Flock.SkipDomain E s) (Y : E) {skipW l : List E}
    (hW : skipW.length = 2 ^ s)
    (hWv : ∀ i : Fin (2 ^ s), skipW.getD i 0 = (Flock.skipWeights nodes Y)[i])
    (hl : l.length = m) :
    toVec (2 ^ (s + m)) ((eqKernel l).flatMap fun w ↦ skipW.map (w * ·)) =
      Flock.eRow nodes Y (toVec m l) := by
  apply Vector.ext
  intro k hk
  obtain ⟨⟨i, jin⟩, hij⟩ := (cubeSplit s m).surjective ⟨k, hk⟩
  rw [cubeSplit_apply] at hij
  have hk' : k = jin.val * skipW.length + i.val := by
    have := congrArg Fin.val hij
    simp only [cubeIndex] at this
    rw [hW]
    linarith [this]
  have hw := Flock.eRow_cubeIndex nodes Y (toVec m l) i jin
  simp only [Fin.getElem_fin] at hw
  have hkc : k = (cubeIndex i jin).val := by rw [hij]
  subst hkc
  have hlb : (lagrangeBasis (toVec m l))[jin.val] = (eqKernel l)[jin.val]'(by
      rw [length_eqKernel, hl]; exact jin.isLt) := by
    have := lagrangeBasis_toVec hl jin
    simpa only [Fin.getElem_fin] using this
  have hsw := hWv i
  rw [Flock.skipWeights_getElem] at hsw
  rw [hw, hlb, ← hsw]
  simp only [toVec, Vector.getElem_ofFn]
  have hjin : jin.val < (eqKernel l).length := by rw [length_eqKernel, hl]; exact jin.isLt
  rw [hk', flatMap_map_getD _ _ _ hjin (by rw [hW]; exact i.isLt)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjin, mul_comm]

/-! ## The terminal -/

/-- The first `m` coordinates of a point read off a list are the list's first `m` entries. -/
theorem toVec_take {m κ : ℕ} (l : List E) : toVec m (l.take m) = lowVec (toVec (m + κ) l) := by
  apply Vector.ext
  intro i hi
  simp [toVec, lowVec, List.getD_eq_getElem?_getD]

/-- Reversing commutes with reading a list of the right length. -/
theorem toVec_reverse {m : ℕ} {l : List E} (hl : l.length = m) :
    toVec m l.reverse = (toVec m l).reverse := by
  apply Vector.ext
  intro i hi
  simp only [toVec, Vector.getElem_ofFn, Vector.getElem_reverse]
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega), List.getD_eq_getElem?_getD]
  congr 2
  omega

/-- **What the lincheck's terminal needs of the program's walk**: the forward walk of the BLAKE2s
circuit (`blake2s_row_values`) computes the R1CS's left and right products `(A w, B w)` of the
region's R1CS. A statement about the deployed circuit and the program alone. -/
def WalkFaithful (F : FlockSpec) : Prop :=
  ∀ w : List E, w.length = 2 ^ (Flock.kSkip + Flock.kIn) →
    (blake2sRowValues w).1.toList =
        List.ofFn (fun k : Fin (2 ^ (Flock.kSkip + Flock.kIn)) ↦
          (F.r1cs.rows (toVec _ w)).1[k]) ∧
      (blake2sRowValues w).2.toList =
        List.ofFn (fun k : Fin (2 ^ (Flock.kSkip + Flock.kIn)) ↦ (F.r1cs.rows (toVec _ w)).2[k])

/-- `dot` against a vector read off a list of the right length. -/
theorem dot_ofFn {n : ℕ} {l : List E} (hl : l.length = n) (f : Fin n → E) :
    dot l (List.ofFn f) = ∑ k : Fin n, (toVec n l)[k] * f k := by
  rw [dot_eq_sum hl (by simp)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk : k.val < l.length := by rw [hl]; exact k.isLt
  simp [toVec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

section Terminal

variable (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes)

/-- **The terminal's fidelity**, from the walk's. -/
theorem terminalFaithful (hwalk : WalkFaithful F) : TerminalFaithful F prog s := by
  intro zc alpha rc sv hchi hrc hsv
  have hm : (fP F prog s).m = 8 := rfl
  have hk8 : flockNumLincheckRounds = (fP F prog s).m := by rw [hm]; decide
  have hkB : kBits = 64 := rfl
  -- The row weights.
  have hE : toVec (2 ^ ((fP F prog s).s + (fP F prog s).m))
      ((eqKernel (zc.chi.take flockNumLincheckRounds)).flatMap fun weight ↦
        (lagrangeWeights kBits zc.zSkip).map (weight * ·)) =
      Flock.eRow (fP F prog s).nodes zc.zSkip
        (lowVec (toVec ((fP F prog s).m + (fP F prog s).κ) zc.chi)) := by
    rw [← toVec_take, hk8]
    exact toVec_eRow _ _ (by rw [length_lagrangeWeights]; rfl)
      (fun i ↦ by rw [hkB]; exact lagrangeWeights_skip zc.zSkip i)
      (by rw [List.length_take, hchi]; omega)
  -- The column weights.
  have hW : toVec (2 ^ ((fP F prog s).s + (fP F prog s).m))
      ((eqKernel rc.reverse).flatMap fun weight ↦ sv.map (· * weight)) =
      Flock.wCol (toVec (2 ^ (fP F prog s).s) sv) (toVec (fP F prog s).m rc).reverse := by
    rw [← toVec_reverse hrc]
    exact toVec_wCol (by rw [hsv]; rfl) (by rw [List.length_reverse, hrc])
  unfold progTerminal Flock.linTerminal blake2sBilinear
  dsimp only
  rw [← hE, ← hW]
  have hlenW : ((eqKernel rc.reverse).flatMap fun weight ↦ sv.map (· * weight)).length =
      2 ^ (Flock.kSkip + Flock.kIn) := by
    rw [length_flatMap_map, length_eqKernel, List.length_reverse, hrc, hsv, hm]
    norm_num [Flock.kSkip, Flock.kIn]
  have hlenE : ((eqKernel (zc.chi.take flockNumLincheckRounds)).flatMap fun weight ↦
      (lagrangeWeights kBits zc.zSkip).map (weight * ·)).length =
      2 ^ (Flock.kSkip + Flock.kIn) := by
    rw [length_flatMap_map, length_eqKernel, length_lagrangeWeights, List.length_take, hchi,
      hk8, hkB]
    rw [show min (fP F prog s).m ((fP F prog s).m + (fP F prog s).κ) = (fP F prog s).m by omega,
      hm]
    norm_num [Flock.kSkip, Flock.kIn]
  obtain ⟨hw1, hw2⟩ := hwalk _ hlenW
  have hw1' : (blake2sRowValues
      ((eqKernel rc.reverse).flatMap fun weight ↦ sv.map (· * weight))).1.toList =
      List.ofFn (fun k : Fin (2 ^ ((fP F prog s).s + (fP F prog s).m)) ↦
        ((fC F prog s).rows (toVec _
          ((eqKernel rc.reverse).flatMap fun weight ↦ sv.map (· * weight)))).1[k]) := hw1
  have hw2' : (blake2sRowValues
      ((eqKernel rc.reverse).flatMap fun weight ↦ sv.map (· * weight))).2.toList =
      List.ofFn (fun k : Fin (2 ^ ((fP F prog s).s + (fP F prog s).m)) ↦
        ((fC F prog s).rows (toVec _
          ((eqKernel rc.reverse).flatMap fun weight ↦ sv.map (· * weight)))).2[k]) := hw2
  have hlenE' : ((eqKernel (zc.chi.take flockNumLincheckRounds)).flatMap fun weight ↦
      (lagrangeWeights kBits zc.zSkip).map (weight * ·)).length =
      2 ^ ((fP F prog s).s + (fP F prog s).m) := hlenE
  rw [hw1', hw2', dot_ofFn hlenE', dot_ofFn hlenE']
  -- The equality kernel of the two points.
  have hq : eqEval (zc.chi.take flockNumLincheckRounds) rc.reverse =
      eqTilde (lowVec (toVec ((fP F prog s).m + (fP F prog s).κ) zc.chi))
        (toVec (fP F prog s).m rc).reverse := by
    rw [eqTilde_eq_prod, eqEval_eq_prod, List.length_take, List.length_reverse, hrc, hchi, hk8,
      show min (min (fP F prog s).m ((fP F prog s).m + (fP F prog s).κ)) (fP F prog s).m =
        (fP F prog s).m by omega, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← toVec_reverse hrc]
    simp only [lowVec, toVec, Vector.getElem_ofFn, Fin.getElem_fin, CharTwo.sub_eq_add]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, i.isLt, ↓reduceIte]
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    linear_combination (-(zc.chi[(i : ℕ)]?.getD 0 * rc.reverse[(i : ℕ)]?.getD 0)) * h2
  -- The skip weights against the slices.
  have hd : dot (lagrangeWeights kBits zc.zSkip) sv =
      ∑ i : Fin (2 ^ (fP F prog s).s),
        (Flock.skipWeights (fP F prog s).nodes zc.zSkip)[i] *
          (toVec (2 ^ (fP F prog s).s) sv)[i] := by
    have h64 : (2 : ℕ) ^ (fP F prog s).s = 64 := rfl
    rw [dot_eq_sum (n := 2 ^ (fP F prog s).s) (by rw [length_lagrangeWeights, hkB, h64])
      (by rw [hsv, h64])]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hw := lagrangeWeights_skip zc.zSkip i
    rw [← hkB] at hw
    have hi : (i : ℕ) < (lagrangeWeights kBits zc.zSkip).length := by
      rw [length_lagrangeWeights]; exact i.isLt
    have hi' : (i : ℕ) < sv.length := by rw [hsv]; exact i.isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hw
    simp only [Fin.getElem_fin] at hw ⊢
    rw [hw]
    simp only [toVec, Vector.getElem_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rfl
  -- The constant position.
  have hc : ((eqKernel rc.reverse).flatMap fun weight ↦ sv.map (· * weight)).getD
      blake2sConstantColumn 0 =
      (toVec (2 ^ ((fP F prog s).s + (fP F prog s).m))
        ((eqKernel rc.reverse).flatMap fun weight ↦ sv.map (· * weight)))[(fP F prog s).cpos] := by
    simp [toVec]
    rfl
  rw [hq, hd, hc]
  ring

end Terminal

end
end LeanVM.Protocol.EndToEnd.Front
