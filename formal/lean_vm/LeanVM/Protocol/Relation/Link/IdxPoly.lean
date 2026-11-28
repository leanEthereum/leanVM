/-
  LeanVM.Protocol.Relation.Link.IdxPoly

  Degrees in one coordinate of the index point: folds, sums and products of lists whose entries are
  polynomials in that coordinate, windows of a point, and the verifier's functions of the index
  point (`belowAt`, `rowMle`, `indexMle`, `eqEval`, `linkShiftEq`, `eqKernel`).
-/

module

public import LeanVM.Protocol.Relation.Link.Cube
public import LeanVM.Protocol.Relation.Link.Fold
public import LeanVM.Facts.Hotwire
public import LeanVM.Protocol.Relation.Link.GroupPoly

/-!
# Degrees in one coordinate of the index point

The index point is `pre ++ c :: rest`, the coordinate `c` free. Every function here is a
polynomial in `c` (`PolyIn`):

* lists: `foldl_inv` carries a property of `c ↦ acc` through a fold whose step depends on `c`;
  `polyIn_sumE` and `polyIn_prodE_one` bound a sum, and a product with at most one entry depending
  on `c`;
* windows: `((pre ++ c :: rest).drop a).take b` is constant in `c` when `c` lies outside it
  (`window_const`) and `u ++ c :: v` inside (`window_split`);
* the index point's functions: `eqAt`, `eqKernel`'s entries, `rowMle`, `indexMle`, `eqEval`,
  `linkShiftEq` are affine in `c`, and so is a product of `1 + r_h` over a window.
-/

namespace LeanVM.Protocol.Relation.IdxPoly

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

public section

/-! ## Constants, folds, sums and products -/

theorem polyIn_of_const {g : E → E} (h : ∀ c, g c = g 0) (d : ℕ) : PolyIn g d :=
  ((PolyIn.const (g 0)).mono (Nat.zero_le d)).congr fun c ↦ (h c).symm

theorem polyIn_cmul {f : E → E} {d : ℕ} (a : E) (h : PolyIn f d) : PolyIn (fun c ↦ a * f c) d :=
  ((PolyIn.const a).mul h).mono (by omega)

theorem polyIn_mulc {f : E → E} {d : ℕ} (a : E) (h : PolyIn f d) : PolyIn (fun c ↦ f c * a) d :=
  (h.mul (PolyIn.const a)).mono (by omega)

theorem polyIn_ite (p : Prop) [Decidable p] {f g : E → E} {d : ℕ} (hf : p → PolyIn f d)
    (hg : ¬ p → PolyIn g d) : PolyIn (fun c ↦ if p then f c else g c) d := by
  by_cases h : p
  · exact (hf h).congr fun c ↦ by simp [h]
  · exact (hg h).congr fun c ↦ by simp [h]

theorem polyIn_zero (d : ℕ) : PolyIn (fun _ ↦ (0 : E)) d := (PolyIn.const 0).mono (Nat.zero_le d)

/-- A property of `c ↦ acc` that each step keeps holds after the fold. -/
theorem foldl_inv {α β : Type} (P : (E → α) → Prop) (step : E → α → β → α) :
    ∀ (l : List β) (A : E → α), P A → (∀ x ∈ l, ∀ B, P B → P fun c ↦ step c (B c) x) →
      P fun c ↦ l.foldl (step c) (A c)
  | [], _, hA, _ => hA
  | x :: l, A, hA, h => by
    simpa only [List.foldl_cons] using
      foldl_inv P step l _ (h x (by simp) A hA) fun y hy ↦ h y (by simp [hy])

theorem foldl_mul_acc (l : List E) (a : E) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

theorem foldl_add_acc (l : List E) (a : E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem prodE_eq (l : List E) : prodE l = l.prod := by rw [prodE, foldl_mul_acc, one_mul]

theorem sumE_eq (l : List E) : sumE l = l.sum := by rw [sumE, foldl_add_acc, zero_add]

theorem list_sum_range (l : List E) : l.sum = ∑ j ∈ range l.length, l.getD j 0 := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.sum_cons, ih, List.length_cons, sum_range_succ']; simp [add_comm]

theorem list_prod_range (l : List E) : l.prod = ∏ j ∈ range l.length, l.getD j 0 := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.prod_cons, ih, List.length_cons, prod_range_succ']; simp [mul_comm]

/-- A sum of entries of degree `d`, the list's length constant. -/
theorem polyIn_sumE {L : E → List E} {d : ℕ} (hl : ∀ c, (L c).length = (L 0).length)
    (h : ∀ j < (L 0).length, PolyIn (fun c ↦ (L c).getD j 0) d) :
    PolyIn (fun c ↦ sumE (L c)) d :=
  (PolyIn.finsetSum (range (L 0).length) fun j hj ↦ h j (mem_range.mp hj)).congr fun c ↦ by
    rw [sumE_eq, list_sum_range, hl c]

/-- A product over a range whose factors but `j0` are constant. -/
theorem polyIn_prod_one {n d : ℕ} {f : ℕ → E → E} (j0 : ℕ)
    (hc : ∀ j < n, j ≠ j0 → ∀ c, f j c = f j 0) (h0 : j0 < n → PolyIn (f j0) d) :
    PolyIn (fun c ↦ ∏ j ∈ range n, f j c) d := by
  by_cases hj : j0 < n
  · have hmem : j0 ∈ range n := mem_range.mpr hj
    refine (((h0 hj).mul (PolyIn.const (∏ j ∈ (range n).erase j0, f j 0))).mono
      (by omega)).congr fun c ↦ ?_
    rw [← mul_prod_erase _ _ hmem]
    congr 1
    exact (prod_congr rfl fun j hj' ↦ hc j (mem_range.mp (mem_of_mem_erase hj'))
      (ne_of_mem_erase hj') c).symm
  · refine polyIn_of_const (fun c ↦ prod_congr rfl fun j hj' ↦ hc j (mem_range.mp hj')
      (by rintro rfl; exact hj (mem_range.mp hj')) c) d

/-- A product of entries all constant but entry `j0`, of degree `d`, the list's length constant. -/
theorem polyIn_prodE_one {L : E → List E} {d : ℕ} (j0 : ℕ) (hl : ∀ c, (L c).length = (L 0).length)
    (hc : ∀ j < (L 0).length, j ≠ j0 → ∀ c, (L c).getD j 0 = (L 0).getD j 0)
    (h0 : j0 < (L 0).length → PolyIn (fun c ↦ (L c).getD j0 0) d) :
    PolyIn (fun c ↦ prodE (L c)) d :=
  (polyIn_prod_one (f := fun j c ↦ (L c).getD j 0) j0 hc h0).congr fun c ↦ by
    rw [prodE_eq, list_prod_range, hl c]

/-! ## Entries of lists -/

theorem getD_map_range {α : Type} (n : ℕ) (f : ℕ → α) (d : α) (j : ℕ) :
    ((List.range n).map f).getD j d = if j < n then f j else d := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem getD_map_of_lt {α : Type} (l : List α) (f : α → E) {j : ℕ} (hj : j < l.length) (d : α) :
    (l.map f).getD j 0 = f (l.getD j d) := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem getD_zipWith_of_lt (f : E → E → E) (a b : List E) {j : ℕ} (hj : j < a.length)
    (hj' : j < b.length) : (List.zipWith f a b).getD j 0 = f (a.getD j 0) (b.getD j 0) := by
  simp [List.getD_eq_getElem?_getD, hj, hj']

theorem getD_addAtSlot (w : List E) (s j : ℕ) (v : E) :
    (addAtSlot w s v).getD j 0 = if j = s ∧ s < w.length then w.getD j 0 + v else w.getD j 0 := by
  unfold addAtSlot
  by_cases hs : s < w.length
  · by_cases hj : j = s
    · subst hj
      simp [List.getD_eq_getElem?_getD, hs]
    · simp [List.getD_eq_getElem?_getD, Ne.symm hj, hj]
  · rw [List.set_eq_of_length_le (by omega)]
    simp [hs]

theorem length_addAtSlot (w : List E) (s : ℕ) (v : E) : (addAtSlot w s v).length = w.length := by
  simp [addAtSlot]

/-! ## Windows of the point -/

theorem getElem?_split_ne {pre rest : List E} {m : ℕ} (hm : m ≠ pre.length) (c c' : E) :
    (pre ++ c :: rest)[m]? = (pre ++ c' :: rest)[m]? := by
  rcases lt_or_gt_of_ne hm with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · rw [List.getElem?_append_right h.le, List.getElem?_append_right h.le]
    obtain ⟨t, ht⟩ : ∃ t, m - pre.length = t + 1 := ⟨m - pre.length - 1, by omega⟩
    rw [ht, List.getElem?_cons_succ, List.getElem?_cons_succ]

/-- A window that misses the free coordinate is constant. -/
theorem window_const {pre rest : List E} {a b : ℕ} (h : ¬ (a ≤ pre.length ∧ pre.length < a + b))
    (c c' : E) : ((pre ++ c :: rest).drop a).take b = ((pre ++ c' :: rest).drop a).take b := by
  refine List.ext_getElem? fun i ↦ ?_
  simp only [List.getElem?_take, List.getElem?_drop]
  split_ifs with hi
  · exact getElem?_split_ne (by omega) c c'
  · rfl

/-- A window that holds the free coordinate. -/
theorem window_split {pre rest : List E} {a b : ℕ} (h1 : a ≤ pre.length)
    (h2 : pre.length < a + b) (c : E) :
    ((pre ++ c :: rest).drop a).take b =
      pre.drop a ++ c :: rest.take (b - (pre.length - a) - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, b - (pre.length - a) = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (show 0 < b - (pre.length - a) by omega)).symm⟩
  rw [List.drop_append_of_le_length h1, List.take_append, List.take_of_length_le (by simp; omega),
    List.length_drop, hm, List.take_succ_cons, Nat.add_sub_cancel]

/-- A function of a window: affine-like in `c` at every split point gives it in the window, and
constant when the window misses the coordinate. -/
theorem polyIn_window (pre rest : List E) (a b : ℕ) {F : List E → E} {e : ℕ}
    (hF : ∀ u v : List E, PolyIn (fun c ↦ F (u ++ c :: v)) e) :
    PolyIn (fun c ↦ F (((pre ++ c :: rest).drop a).take b)) e := by
  by_cases h : a ≤ pre.length ∧ pre.length < a + b
  · exact (hF _ _).congr fun c ↦ by rw [window_split h.1 h.2]
  · exact polyIn_of_const (fun c ↦ by rw [window_const h c 0]) e

theorem window_fn_const {pre rest : List E} {a b : ℕ} (F : List E → E)
    (h : ¬ (a ≤ pre.length ∧ pre.length < a + b)) (c : E) :
    F (((pre ++ c :: rest).drop a).take b) = F (((pre ++ (0 : E) :: rest).drop a).take b) := by
  rw [window_const h c 0]

/-- A point with its coordinate `k` set apart. -/
theorem split_coord {L : List E} {k : ℕ} (hk : k < L.length) :
    L = L.take k ++ L.getD k 0 :: L.drop (k + 1) := by
  rw [List.getD_eq_getElem _ _ hk, ← List.drop_eq_getElem_cons hk, List.take_append_drop]

theorem take_eq_window (l : List E) (h : ℕ) : l.take h = (l.drop 0).take h := by simp

theorem drop_eq_window (l : List E) (a : ℕ) : l.drop a = (l.drop a).take l.length :=
  (List.take_of_length_le (by simp)).symm

/-! ## Functions of a point with a free coordinate -/

theorem polyIn_eqAt (u v : List E) (j : ℕ) : PolyIn (fun c ↦ eqAt (u ++ c :: v) j) 1 := by
  have h : ∀ c, eqAt (u ++ c :: v) j =
      eqAt u j * eqAt v (j / 2 ^ u.length / 2) * (if j / 2 ^ u.length % 2 = 1 then c else 1 - c) := by
    intro c
    rw [eqAt_append, eqAt_cons]
    ring
  refine PolyIn.congr ?_ fun c ↦ (h c).symm
  refine ((PolyIn.const (eqAt u j * eqAt v (j / 2 ^ u.length / 2))).mul (e := 1) ?_).mono
    (by omega)
  split_ifs
  · exact PolyIn.var
  · exact ((PolyIn.const 1).sub PolyIn.var).mono (by simp)

theorem polyIn_eqKernel (u v : List E) (j : ℕ) :
    PolyIn (fun c ↦ (eqKernel (u ++ c :: v)).getD j 0) 1 := by
  have hl : ∀ c : E, (u ++ c :: v).length = u.length + 1 + v.length := fun c ↦ by simp; omega
  by_cases hj : j < 2 ^ (u.length + 1 + v.length)
  · exact (polyIn_eqAt u v j).congr fun c ↦ by rw [eqKernel_getD, hl]; simp [hj]
  · exact polyIn_of_const (fun c ↦ by rw [eqKernel_getD, eqKernel_getD, hl, hl]; simp [hj]) 1

theorem length_eqKernel_split (u v : List E) (c : E) :
    (eqKernel (u ++ c :: v)).length = 2 ^ (u.length + 1 + v.length) := by
  rw [eqKernel_length]; simp; ring_nf

theorem polyIn_rowMle (u v : List E) (f : ℕ → E) : PolyIn (fun c ↦ rowMle (u ++ c :: v) f) 1 := by
  have hl : ∀ c : E, (u ++ c :: v).length = u.length + 1 + v.length := fun c ↦ by simp; omega
  refine (PolyIn.finsetSum (range (2 ^ (u.length + 1 + v.length)))
    (f := fun w c ↦ eqAt (u ++ c :: v) w * f w) fun w _ ↦
      ((polyIn_eqAt u v w).mul (PolyIn.const (f w))).mono (by omega)).congr fun c ↦ ?_
  rw [rowMle_eq_mle, mle, hl]

theorem polyIn_prodE_map (u v : List E) {g : E → E} {e : ℕ} (hg : PolyIn g e) :
    PolyIn (fun c ↦ prodE ((u ++ c :: v).map g)) e :=
  ((PolyIn.const (u.map g).prod).mul (hg.mul (PolyIn.const (v.map g).prod))).mono (by omega)
    |>.congr fun c ↦ by
      rw [prodE_eq, List.map_append, List.map_cons, List.prod_append, List.prod_cons]

/-! ## The index point's functions -/

section Point

variable (pre rest : List E)

theorem polyIn_rowMle_take (h : ℕ) (f : ℕ → E) :
    PolyIn (fun c ↦ rowMle ((pre ++ c :: rest).take h) f) 1 :=
  (polyIn_window pre rest 0 h (F := fun p ↦ rowMle p f) fun u v ↦ polyIn_rowMle u v f).congr
    fun c ↦ by rw [← take_eq_window]

theorem rowMle_take_const {h : ℕ} (hk : h ≤ pre.length) (f : ℕ → E) (c : E) :
    rowMle ((pre ++ c :: rest).take h) f = rowMle ((pre ++ (0 : E) :: rest).take h) f := by
  rw [take_eq_window, take_eq_window (pre ++ (0 : E) :: rest)]
  exact window_fn_const (fun p ↦ rowMle p f) (by omega) c

theorem polyIn_belowAt (chunks : Chunks) (m : ℕ) :
    PolyIn (fun c ↦ belowAt chunks (pre ++ c :: rest) m) 1 :=
  (polyIn_window pre rest (min m chunks.width) (pre.length + 1 + rest.length)
    (F := fun p ↦ prodE (p.map (1 + ·))) fun u v ↦
      polyIn_prodE_map u v ((PolyIn.const 1).add PolyIn.var)).congr fun c ↦ by
    rw [belowAt, List.take_of_length_le (by simp; omega)]

theorem belowAt_const (chunks : Chunks) {m : ℕ} (hk : pre.length < min m chunks.width) (c : E) :
    belowAt chunks (pre ++ c :: rest) m = belowAt chunks (pre ++ (0 : E) :: rest) m := by
  have := window_fn_const (pre := pre) (rest := rest) (a := min m chunks.width)
    (b := pre.length + 1 + rest.length) (fun p ↦ prodE (p.map (1 + ·))) (by omega) c
  rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)] at this
  exact this

theorem indexMleFrom_acc : ∀ (g : E) (l : List E) (acc : E),
    indexMleFrom g l acc = acc * indexMleFrom g l 1
  | _, [], _ => by simp [indexMleFrom]
  | g, x :: l, acc => by
    simp only [indexMleFrom]
    rw [indexMleFrom_acc _ l, indexMleFrom_acc _ l (1 * _)]
    ring

theorem indexMleFrom_append : ∀ (g : E) (l₁ l₂ : List E) (acc : E),
    indexMleFrom g (l₁ ++ l₂) acc = indexMleFrom (g ^ 2 ^ l₁.length) l₂ (indexMleFrom g l₁ acc)
  | _, [], _, _ => by simp [indexMleFrom]
  | g, x :: l₁, l₂, acc => by
    simp only [List.cons_append, indexMleFrom, List.length_cons]
    rw [indexMleFrom_append, ← pow_mul, ← pow_succ']

theorem polyIn_indexMle : PolyIn (fun c ↦ indexMle (pre ++ c :: rest)) 1 := by
  set g' : E := gen ^ 2 ^ pre.length
  set a : E := indexMleFrom gen pre 1
  set b : E := indexMleFrom (g' ^ 2) rest 1
  refine (((PolyIn.const a).mul ((PolyIn.const 1).add ((PolyIn.var).mul
    (PolyIn.const (1 + g'))))).mul (PolyIn.const b)).mono (by omega) |>.congr fun c ↦ ?_
  rw [indexMle, indexMleFrom_append]
  simp only [indexMleFrom]
  rw [indexMleFrom_acc]

theorem polyIn_eqEval (zeta : List E) : PolyIn (fun c ↦ eqEval zeta (pre ++ c :: rest)) 1 := by
  by_cases hz : pre.length < zeta.length
  · have hs := split_coord hz
    refine ((PolyIn.const (eqEval (zeta.take pre.length) pre)).mul
      ((((PolyIn.const (1 + zeta.getD pre.length 0)).add PolyIn.var).mul
        (PolyIn.const (eqEval (zeta.drop (pre.length + 1)) rest))))).mono (by omega)
      |>.congr fun c ↦ ?_
    conv_rhs => rw [hs]
    rw [Tables.eqEval_append _ _ _ _ (by simp; omega), Tables.eqEval_cons]
  · refine polyIn_of_const (fun c ↦ ?_) 1
    simp only [eqEval]
    congr 1
    refine List.ext_getElem? fun i ↦ ?_
    simp only [List.getElem?_zipWith]
    by_cases hi : i < zeta.length
    · rw [getElem?_split_ne (by omega) c 0]
    · simp [List.getElem?_eq_none (show zeta.length ≤ i by omega)]

/-- `shift_eq`'s step. -/
def shiftStep (acc : E × E) (zx : E × E) : E × E :=
  (acc.1 * (1 + zx.1 + zx.2) + acc.2 * (1 + zx.2) * zx.1, acc.2 * (zx.2 * (1 + zx.1)))

theorem polyIn_linkShiftEq (zeta : List E) :
    PolyIn (fun c ↦ linkShiftEq zeta (pre ++ c :: rest)) 1 := by
  have hdef : ∀ r, linkShiftEq zeta r = ((zeta.zip r).foldl shiftStep (0, 1)).1 := fun _ ↦ rfl
  by_cases hz : pre.length < zeta.length
  · have hs := split_coord hz
    set z1 := zeta.take pre.length
    set z := zeta.getD pre.length 0
    set z2 := zeta.drop (pre.length + 1)
    have hzip : ∀ c, zeta.zip (pre ++ c :: rest) = z1.zip pre ++ (z, c) :: z2.zip rest := by
      intro c
      conv_lhs => rw [hs]
      rw [List.zip_append (by simp [z1]; omega), List.zip_cons_cons]
    set a0 := (z1.zip pre).foldl shiftStep (0, 1)
    let P : (E → E × E) → Prop := fun G ↦ PolyIn (fun c ↦ (G c).1) 1 ∧ PolyIn (fun c ↦ (G c).2) 1
    have hstart : P fun c ↦ shiftStep a0 (z, c) := by
      refine ⟨?_, ?_⟩
      · exact (((PolyIn.const a0.1).mul ((PolyIn.const (1 + z)).add PolyIn.var)).add
          (((PolyIn.const a0.2).mul ((PolyIn.const 1).add PolyIn.var)).mul (PolyIn.const z))).mono
          (by omega) |>.congr fun c ↦ by simp only [shiftStep]
      · exact ((PolyIn.const a0.2).mul (PolyIn.var.mul ((PolyIn.const (1 + z))))).mono (by omega)
          |>.congr fun c ↦ rfl
    have hfold := foldl_inv P (fun _ acc zx ↦ shiftStep acc zx) (z2.zip rest) _ hstart
      fun x _ B hB ↦ ⟨(((hB.1.mul (PolyIn.const (1 + x.1 + x.2))).add
        ((hB.2.mul (PolyIn.const (1 + x.2))).mul (PolyIn.const x.1))).mono (by omega)).congr
          fun c ↦ by simp only [shiftStep],
        ((hB.2.mul (PolyIn.const (x.2 * (1 + x.1)))).mono (by omega)).congr
          fun c ↦ by simp only [shiftStep]⟩
    refine hfold.1.congr fun c ↦ ?_
    rw [hdef, hzip, List.foldl_append, List.foldl_cons]
  · refine polyIn_of_const (fun c ↦ ?_) 1
    rw [hdef, hdef]
    congr 2
    refine List.ext_getElem? fun i ↦ ?_
    simp only [List.zip, List.getElem?_zipWith]
    by_cases hi : i < zeta.length
    · rw [getElem?_split_ne (by omega) c 0]
    · simp [List.getElem?_eq_none (show zeta.length ≤ i by omega)]

end Point

end

end LeanVM.Protocol.Relation.IdxPoly
