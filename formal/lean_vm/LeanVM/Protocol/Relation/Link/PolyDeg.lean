/-
  LeanVM.Protocol.Relation.Link.PolyDeg

  Degrees in one variable of the link's multilinear pieces: `eq_eval`, `eq_kernel`'s entries, a
  row's extension, `less_than`, `omega_at`, a corner product; lists whose entries are of bounded
  degree; forms.
-/

module

public import LeanVM.Protocol.Relation.Link.Cube
public import LeanVM.Protocol.Relation.Link.Facts
import LeanVM.Facts.Hotwire
import Mathlib.Tactic.Ring

/-!
# Degrees in one variable

`PolyIn` (`Link/Cube.lean`) with the closure lemmas the row side's summand needs:

* `MLin g`: `g` is of degree at most one in each coordinate (`mlin_eqEval`, `mlin_eqKernel_getD`,
  `mlin_rowMle`, `mlin_lessThan`, `mlin_omegaAt`, `mlin_prodE_one_add`), stated at
  `pre ++ z :: rest` with no hypothesis on the lengths;
* `Ent v d`: a list of constant length whose entries are of degree at most `d`, with `sumE`, `prodE`,
  `zipWith`, `drop`, `take`, `map` and `addAtSlot`;
* `polyIn_foldl`, `foldl_pred`: a fold whose step keeps a degree, or a predicate;
* `Form.deg`, `polyIn_evaluate`: a form at columns of degree `dc` is of degree `deg·dc`.
-/

namespace LeanVM.Protocol.Relation.RowPoly

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Relation Finset

@[expose] public section

/-! ## Closure -/

theorem polyIn_of_const {f : E → E} (h : ∀ c, f c = f 0) (d : ℕ) : PolyIn f d :=
  ((PolyIn.const (f 0)).congr fun c ↦ (h c).symm).mono (Nat.zero_le d)

theorem polyIn_finsetProd {ι : Type} (s : Finset ι) {f : ι → E → E} {d : ι → ℕ}
    (h : ∀ i ∈ s, PolyIn (f i) (d i)) : PolyIn (fun c ↦ ∏ i ∈ s, f i c) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ((PolyIn.const 1).congr fun c ↦ by simp).mono (by simp)
  | insert a s ha ih =>
    exact (((h a (mem_insert_self a s)).mul (ih fun i hi ↦ h i (mem_insert_of_mem hi))).congr
      fun c ↦ by rw [prod_insert ha]).mono (by rw [sum_insert ha])

/-- A fold whose step keeps a degree. -/
theorem polyIn_foldl {β : Type} {d : ℕ} (step : E → E → β → E) :
    ∀ (R : List β), (∀ x ∈ R, ∀ f : E → E, PolyIn f d → PolyIn (fun c ↦ step c (f c) x) d) →
      ∀ f : E → E, PolyIn f d → PolyIn (fun c ↦ R.foldl (step c) (f c)) d
  | [], _, _, hf => hf
  | x :: R, hs, f, hf =>
    polyIn_foldl step R (fun y hy ↦ hs y (by simp [hy])) _ (hs x (by simp) f hf)

/-- A fold whose step keeps a predicate of the accumulator, as a function of the variable. -/
theorem foldl_pred {α β : Type} (P : (E → α) → Prop) (step : E → α → β → α) :
    ∀ (R : List β), (∀ x ∈ R, ∀ A : E → α, P A → P fun c ↦ step c (A c) x) →
      ∀ A : E → α, P A → P fun c ↦ R.foldl (step c) (A c)
  | [], _, _, hA => hA
  | x :: R, hs, A, hA =>
    foldl_pred P step R (fun y hy ↦ hs y (by simp [hy])) _ (hs x (by simp) A hA)

/-! ## Sums and products of lists -/

theorem foldl_mul_eq (l : List E) (a : E) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

theorem foldl_add_eq' (l : List E) (a : E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem prodE_eq (l : List E) : prodE l = l.prod := by rw [prodE, foldl_mul_eq, one_mul]

theorem sumE_eq (l : List E) : sumE l = l.sum := by rw [sumE, foldl_add_eq', zero_add]

theorem list_sum_range (l : List E) : l.sum = ∑ i ∈ range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.sum_cons, List.length_cons, sum_range_succ', ih]; simp [add_comm]

theorem list_prod_range (l : List E) : l.prod = ∏ i ∈ range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.prod_cons, List.length_cons, prod_range_succ', ih]; simp [mul_comm]

/-! ## Lists of entries of bounded degree -/

/-- `v c` has a length independent of `c`, and each entry is of degree at most `d`. -/
def Ent (v : E → List E) (d : ℕ) : Prop :=
  (∀ c, (v c).length = (v 0).length) ∧ ∀ i, PolyIn (fun c ↦ (v c).getD i 0) d

theorem Ent.mono {v : E → List E} {d e : ℕ} (h : Ent v d) (hde : d ≤ e) : Ent v e :=
  ⟨h.1, fun i ↦ (h.2 i).mono hde⟩

theorem ent_const {v : E → List E} (h : ∀ c, v c = v 0) (d : ℕ) : Ent v d :=
  ⟨fun c ↦ by rw [h c], fun i ↦ polyIn_of_const (fun c ↦ by rw [h c]) d⟩

theorem polyIn_sumE {v : E → List E} {d : ℕ} (h : Ent v d) : PolyIn (fun c ↦ sumE (v c)) d :=
  (PolyIn.finsetSum (range (v 0).length) fun i _ ↦ h.2 i).congr fun c ↦ by
    rw [sumE_eq, list_sum_range, h.1 c]

theorem polyIn_prodE {v : E → List E} {d : ℕ} (h : Ent v d) :
    PolyIn (fun c ↦ prodE (v c)) ((v 0).length * d) :=
  ((polyIn_finsetProd (range (v 0).length) fun i _ ↦ h.2 i).congr fun c ↦ by
    rw [prodE_eq, list_prod_range, h.1 c]).mono (by simp)

theorem getD_map_list {β : Type} (L : List β) (F : β → E) (i : ℕ) :
    (L.map F).getD i 0 = if h : i < L.length then F L[i] else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · simp [List.getElem?_eq_getElem h]
  · rw [List.getElem?_eq_none (by omega : L.length ≤ i)]
    rfl

/-- A fixed list mapped by functions of degree at most `d`. -/
theorem ent_map {β : Type} (L : List β) {F : β → E → E} {d : ℕ}
    (h : ∀ x ∈ L, PolyIn (F x) d) : Ent (fun c ↦ L.map fun x ↦ F x c) d := by
  refine ⟨fun c ↦ by simp, fun i ↦ ?_⟩
  by_cases hi : i < L.length
  · exact (h L[i] (List.getElem_mem hi)).congr fun c ↦ by rw [getD_map_list, dite_eq_left hi]
  · exact polyIn_of_const (fun c ↦ by rw [getD_map_list, getD_map_list, dite_eq_right hi, dite_eq_right hi]) d

theorem polyIn_listSum_map {β : Type} (L : List β) {F : β → E → E} {d : ℕ}
    (h : ∀ x ∈ L, PolyIn (F x) d) : PolyIn (fun c ↦ sumE (L.map fun x ↦ F x c)) d :=
  polyIn_sumE (ent_map L h)

theorem getD_zipWith (f : E → E → E) : ∀ (a b : List E) (i : ℕ),
    (List.zipWith f a b).getD i 0 =
      if i < a.length ∧ i < b.length then f (a.getD i 0) (b.getD i 0) else 0
  | [], _, i => by simp
  | _ :: _, [], i => by simp
  | x :: a, y :: b, 0 => by simp
  | x :: a, y :: b, i + 1 => by
    simp only [List.zipWith_cons_cons, List.getD_cons_succ, List.length_cons,
      Nat.add_lt_add_iff_right, getD_zipWith f a b i]

theorem ent_zipWith_mul {a b : E → List E} {da db : ℕ} (ha : Ent a da) (hb : Ent b db) :
    Ent (fun c ↦ List.zipWith (· * ·) (a c) (b c)) (da + db) := by
  refine ⟨fun c ↦ by simp [ha.1 c, hb.1 c], fun i ↦ ?_⟩
  by_cases hi : i < (a 0).length ∧ i < (b 0).length
  · exact ((ha.2 i).mul (hb.2 i)).congr fun c ↦ by
      rw [getD_zipWith, ite_eq_left (by rw [ha.1 c, hb.1 c]; exact hi)]
  · exact polyIn_of_const (fun c ↦ by
      rw [getD_zipWith, getD_zipWith, ite_eq_right (by rw [ha.1 c, hb.1 c]; exact hi), ite_eq_right hi]) _

theorem ent_drop {v : E → List E} {d : ℕ} (h : Ent v d) (n : ℕ) : Ent (fun c ↦ (v c).drop n) d := by
  refine ⟨fun c ↦ by simp [h.1 c], fun i ↦ (h.2 (n + i)).congr fun c ↦ ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_take (l : List E) (n i : ℕ) : (l.take n).getD i 0 = if i < n then l.getD i 0 else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take]
  split_ifs <;> simp [List.getD_eq_getElem?_getD]

theorem ent_take {v : E → List E} {d : ℕ} (h : Ent v d) (n : ℕ) : Ent (fun c ↦ (v c).take n) d := by
  refine ⟨fun c ↦ by simp [h.1 c], fun i ↦ ?_⟩
  by_cases hi : i < n
  · exact (h.2 i).congr fun c ↦ by rw [getD_take, ite_eq_left hi]
  · exact polyIn_of_const (fun c ↦ by rw [getD_take, getD_take, ite_eq_right hi, ite_eq_right hi]) d

theorem getD_set (l : List E) (s i : ℕ) (x : E) :
    (l.set s x).getD i 0 = if i = s ∧ s < l.length then x else l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : s = i
  · subst h1
    by_cases h2 : s < l.length
    · simp [h2]
    · simp [h2]
  · simp [h1, Ne.symm h1]

theorem ent_addAtSlot {w : E → List E} {v : E → E} {d : ℕ} (hw : Ent w d) (hv : PolyIn v d)
    (s : ℕ) : Ent (fun c ↦ addAtSlot (w c) s (v c)) d := by
  refine ⟨fun c ↦ by beta_reduce; rw [addAtSlot, addAtSlot, List.length_set, List.length_set, hw.1 c], fun i ↦ ?_⟩
  by_cases hi : i = s ∧ s < (w 0).length
  · exact ((hw.2 s).add_le hv).congr fun c ↦ by
      beta_reduce
      rw [addAtSlot, getD_set, ite_eq_left (by rw [hw.1 c]; exact hi)]
  · exact (hw.2 i).congr fun c ↦ by beta_reduce; rw [addAtSlot, getD_set, ite_eq_right (by rw [hw.1 c]; exact hi)]

/-! ## Multilinear in each coordinate -/

/-- `g` is of degree at most one in each coordinate. -/
def MLin (g : List E → E) : Prop := ∀ pre rest : List E, PolyIn (fun z ↦ g (pre ++ z :: rest)) 1

theorem getD_line (pre rest : List E) (z : E) (i : ℕ) :
    (pre ++ z :: rest).getD i 0 = if i = pre.length then z else (pre ++ (0 : E) :: rest).getD i 0 := by
  rcases lt_trichotomy i pre.length with h | rfl | h
  · rw [ite_eq_right h.ne, List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
  · rw [ite_eq_left rfl, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
  · rw [ite_eq_right h.ne', List.getD_append_right _ _ _ _ h.le, List.getD_append_right _ _ _ _ h.le]
    obtain ⟨j, hj⟩ : ∃ j, i - pre.length = j + 1 := ⟨i - pre.length - 1, by omega⟩
    rw [hj, List.getD_cons_succ, List.getD_cons_succ]

theorem take_line (pre rest : List E) (z : E) (h : ℕ) :
    (pre ++ z :: rest).take h =
      if pre.length < h then pre ++ z :: rest.take (h - pre.length - 1) else pre.take h := by
  split_ifs with hl
  · rw [List.take_append, List.take_of_length_le hl.le,
      show h - pre.length = (h - pre.length - 1) + 1 by omega, List.take_succ_cons,
      Nat.add_sub_cancel]
  · rw [List.take_append_of_le_length (by omega)]

theorem drop_line (pre rest : List E) (z : E) (h : ℕ) :
    (pre ++ z :: rest).drop h =
      if h ≤ pre.length then pre.drop h ++ z :: rest else rest.drop (h - pre.length - 1) := by
  split_ifs with hl
  · rw [List.drop_append_of_le_length hl]
  · rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show h - pre.length = (h - pre.length - 1) + 1 by omega, List.drop_succ_cons,
      Nat.add_sub_cancel]

theorem polyIn_eqPt : ∀ (pre τ rest : List E),
    PolyIn (fun z ↦ Hotwire.eqPt τ (pre ++ z :: rest)) 1
  | [], [], _ => polyIn_of_const (fun _ ↦ rfl) 1
  | [], t :: τ, rest =>
    ((((PolyIn.const (1 + t)).add PolyIn.var).mul (PolyIn.const (Hotwire.eqPt τ rest))).congr
      fun z ↦ by simp [Hotwire.eqPt_cons, Hotwire.eq1_E]).mono (by norm_num)
  | _ :: _, [], _ => polyIn_of_const (fun _ ↦ rfl) 1
  | x :: pre, t :: τ, rest =>
    (((PolyIn.const (Hotwire.eq1 t x)).mul (polyIn_eqPt pre τ rest)).congr
      fun z ↦ by simp [Hotwire.eqPt_cons]).mono (by norm_num)

theorem mlin_eqEval (τ : List E) : MLin fun p ↦ eqEval τ p := fun pre rest ↦
  (polyIn_eqPt pre τ rest).congr fun _ ↦ (Hotwire.eqEval_eq_eqPt τ _).symm

theorem mlin_eqKernel_getD (w : ℕ) : MLin fun p ↦ (eqKernel p).getD w 0 := by
  intro pre rest
  have hl : ∀ z : E, (pre ++ z :: rest).length = pre.length + 1 + rest.length := fun z ↦ by
    simp; omega
  by_cases hw : w < 2 ^ (pre.length + 1 + rest.length)
  · have key : ∀ z : E, (eqKernel (pre ++ z :: rest)).getD w 0 = Hotwire.eqAt pre w *
        ((if w / 2 ^ pre.length % 2 = 1 then z else 1 - z) *
          Hotwire.eqAt rest (w / 2 ^ pre.length / 2)) := fun z ↦ by
      rw [Hotwire.eqKernel_getD, ite_eq_left (by rw [hl]; exact hw), Hotwire.eqAt_append,
        Hotwire.eqAt_cons]
    by_cases hb : w / 2 ^ pre.length % 2 = 1
    · exact (((PolyIn.const (Hotwire.eqAt pre w)).mul (PolyIn.var.mul
        (PolyIn.const (Hotwire.eqAt rest (w / 2 ^ pre.length / 2))))).congr fun z ↦ by
        beta_reduce; rw [key z, ite_eq_left hb]).mono (by norm_num)
    · exact (((PolyIn.const (Hotwire.eqAt pre w)).mul (((PolyIn.const 1).sub PolyIn.var).mul
        (PolyIn.const (Hotwire.eqAt rest (w / 2 ^ pre.length / 2))))).congr
        fun z ↦ by beta_reduce; rw [key z, ite_eq_right hb]).mono (by norm_num)
  · exact polyIn_of_const (fun z ↦ by
      beta_reduce
      rw [Hotwire.eqKernel_getD, Hotwire.eqKernel_getD, ite_eq_right (by rw [hl]; exact hw),
        ite_eq_right (by rw [hl]; exact hw)]) 1

theorem mlin_rowMle (f : ℕ → E) : MLin fun p ↦ rowMle p f := by
  intro pre rest
  obtain ⟨p, hp, hv⟩ := perVarDeg_rowMle_take (pre.length + 1 + rest.length)
    (pre.length + 1 + rest.length) f pre rest rfl
  refine ⟨p, hp, fun c ↦ ?_⟩
  rw [hv]
  dsimp only
  rw [List.take_of_length_le (by simp only [List.length_append, List.length_cons]; omega)]

theorem mlin_prodE_one_add : MLin fun p ↦ prodE (p.map (1 + ·)) := fun pre rest ↦
  (((PolyIn.const (pre.map (1 + ·)).prod).mul (((PolyIn.const 1).add PolyIn.var).mul
    (PolyIn.const (rest.map (1 + ·)).prod))).congr fun z ↦ by
      beta_reduce
      rw [prodE_eq, List.map_append, List.map_cons, List.prod_append, List.prod_cons]).mono
    (by norm_num)

/-! ### `less_than` -/

/-- `padding_weight`'s step. -/
def padStep (n : ℕ) (pad : E) (x : E × ℕ) : E :=
  (1 + eOfNat ((n >>> x.2) % 2)) * x.1 + (1 + eOfNat ((n >>> x.2) % 2) + x.1) * pad

theorem paddingWeight_line (n : ℕ) (pre rest : List E) (z : E) :
    paddingWeight (pre ++ z :: rest) n =
      (1 + eOfNat ((n >>> (pre.length + 1 + rest.length)) % 2)) *
        (rest.zipIdx (pre.length + 1)).foldl (padStep n)
          (padStep n (pre.zipIdx.foldl (padStep n) 1) (z, pre.length)) := by
  have hl : (pre ++ z :: rest).length = pre.length + 1 + rest.length := by simp; omega
  unfold paddingWeight
  rw [hl, List.zipIdx_append, List.foldl_append, List.zipIdx_cons, List.foldl_cons, Nat.zero_add]
  rfl

theorem polyIn_padFold (n : ℕ) (R : List (E × ℕ)) {f : E → E} {d : ℕ} (hf : PolyIn f d) :
    PolyIn (fun c ↦ R.foldl (padStep n) (f c)) d :=
  polyIn_foldl (fun _ ↦ padStep n) R (fun x _ g hg ↦
    (((PolyIn.const ((1 + eOfNat ((n >>> x.2) % 2)) * x.1)).add
      ((PolyIn.const (1 + eOfNat ((n >>> x.2) % 2) + x.1)).mul hg)).congr fun c ↦ rfl).mono
      (by simp)) f hf

theorem mlin_lessThan (n : ℕ) : MLin fun p ↦ lessThan p n := by
  intro pre rest
  have h1 : PolyIn (fun z ↦ padStep n (pre.zipIdx.foldl (padStep n) 1) (z, pre.length)) 1 :=
    ((((PolyIn.const (1 + eOfNat ((n >>> pre.length) % 2))).mul PolyIn.var).add
      (((PolyIn.const (1 + eOfNat ((n >>> pre.length) % 2))).add PolyIn.var).mul
      (PolyIn.const (pre.zipIdx.foldl (padStep n) 1)))).congr fun z ↦ rfl).mono (by norm_num)
  exact (((PolyIn.const 1).add ((PolyIn.const (1 + eOfNat ((n >>> (pre.length + 1 +
    rest.length)) % 2))).mul (polyIn_padFold n (rest.zipIdx (pre.length + 1)) h1))).congr fun z ↦ by
    beta_reduce; rw [lessThan, paddingWeight_line]).mono (by norm_num)

/-! ### `omega_at` -/

/-- `prefix_sum`'s table of prefix products. -/
def fullList (low high : List E) (m : ℕ) : List E :=
  (List.range m).foldl (fun acc h ↦ acc ++ [acc.getD h 0 * (low.getD h 0 + high.getD h 0)]) [1]

/-- `prefix_sum`'s walk step. -/
def walkStep (n : ℕ) (low high full : List E) (acc : E × E) (h : ℕ) : E × E :=
  if n >>> h % 2 = 1 then (acc.1 + acc.2 * low.getD h 0 * full.getD h 0, acc.2 * high.getD h 0)
  else (acc.1, acc.2 * low.getD h 0)

theorem prefixSum_eq (low high : List E) (n : ℕ) :
    prefixSum low high n =
      if 2 ^ low.length ≤ n then (fullList low high low.length).getD low.length 0
      else ((List.range low.length).reverse.foldl
        (walkStep n low high (fullList low high low.length)) (0, 1)).1 := rfl

theorem fullList_spec (low high : List E) : ∀ m : ℕ, (fullList low high m).length = m + 1 ∧
    ∀ h ≤ m, (fullList low high m).getD h 0 = ∏ j ∈ range h, (low.getD j 0 + high.getD j 0)
  | 0 => ⟨rfl, fun h hh ↦ by
      obtain rfl : h = 0 := by omega
      rfl⟩
  | m + 1 => by
    obtain ⟨hl, hg⟩ := fullList_spec low high m
    have he : fullList low high (m + 1) = fullList low high m ++
        [(fullList low high m).getD m 0 * (low.getD m 0 + high.getD m 0)] := by
      rw [fullList, List.range_succ, List.foldl_append]
      rfl
    refine ⟨by rw [he, List.length_append, hl]; rfl, fun h hh ↦ ?_⟩
    rw [he]
    rcases Nat.lt_or_ge h (m + 1) with h1 | h1
    · rw [List.getD_append _ _ _ _ (by rw [hl]; exact h1), hg h (by omega)]
    · obtain rfl : h = m + 1 := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hl]), hl, Nat.sub_self, List.getD_cons_zero,
        hg m le_rfl, prod_range_succ]

/-- **`prefix_sum` is of degree at most one** in a variable that only its entries `k` hold. -/
theorem polyIn_prefixSum (lo hi : E → List E) (k n : ℕ)
    (hlen : ∀ c, (lo c).length = (lo 0).length)
    (hlo : ∀ i, PolyIn (fun c ↦ (lo c).getD i 0) (if i = k then 1 else 0))
    (hhi : ∀ i, PolyIn (fun c ↦ (hi c).getD i 0) (if i = k then 1 else 0)) :
    PolyIn (fun c ↦ prefixSum (lo c) (hi c) n) 1 := by
  set L := (lo 0).length
  have hs : ∀ j, PolyIn (fun c ↦ (lo c).getD j 0 + (hi c).getD j 0) (if j = k then 1 else 0) :=
    fun j ↦ (hlo j).add_le (hhi j)
  have hfull : ∀ h ≤ L, PolyIn (fun c ↦ (fullList (lo c) (hi c) L).getD h 0)
      (if k < h then 1 else 0) := fun h hh ↦
    ((polyIn_finsetProd (range h) fun j _ ↦ hs j).congr fun c ↦
      ((fullList_spec (lo c) (hi c) L).2 h hh).symm).mono (by
        rw [sum_ite_eq' (range h) k fun _ ↦ 1]; simp)
  -- the walk, from the top bit down
  have walk : ∀ m ≤ L, ∀ A : E → E × E, PolyIn (fun c ↦ (A c).1) 1 →
      PolyIn (fun c ↦ (A c).2) (if m ≤ k then 1 else 0) →
      PolyIn (fun c ↦ ((List.range m).foldr (fun h acc ↦
        walkStep n (lo c) (hi c) (fullList (lo c) (hi c) L) acc h) (A c)).1) 1 := by
    intro m
    induction m with
    | zero => intro _ A h1 _; exact h1
    | succ m ih =>
      intro hm A h1 h2
      have e : ∀ c, (List.range (m + 1)).foldr (fun h acc ↦
          walkStep n (lo c) (hi c) (fullList (lo c) (hi c) L) acc h) (A c) =
          (List.range m).foldr (fun h acc ↦
            walkStep n (lo c) (hi c) (fullList (lo c) (hi c) L) acc h)
            (walkStep n (lo c) (hi c) (fullList (lo c) (hi c) L) (A c) m) := fun c ↦ by
        rw [List.range_succ, List.foldr_append]
        rfl
      refine (ih (by omega) _ ?_ ?_).congr fun c ↦ (congrArg Prod.fst (e c)).symm
      · by_cases hb : n >>> m % 2 = 1
        · exact ((h1.add ((h2.mul (hlo m)).mul (hfull m (by omega)))).congr fun c ↦ by
            simp only [walkStep, ite_eq_left hb]).mono (by split_ifs <;> omega)
        · exact h1.congr fun c ↦ by simp only [walkStep, ite_eq_right hb]
      · by_cases hb : n >>> m % 2 = 1
        · exact ((h2.mul (hhi m)).congr fun c ↦ by
            simp only [walkStep, ite_eq_left hb]).mono (by split_ifs <;> omega)
        · exact ((h2.mul (hlo m)).congr fun c ↦ by
            simp only [walkStep, ite_eq_right hb]).mono (by split_ifs <;> omega)
  by_cases hn : 2 ^ L ≤ n
  · exact ((hfull L le_rfl).congr fun c ↦ by rw [prefixSum_eq, hlen c, ite_eq_left hn]).mono
      (by split_ifs <;> omega)
  · refine (walk L le_rfl (fun _ ↦ (0, 1)) (PolyIn.const 0 |>.mono (Nat.zero_le _))
      (PolyIn.const 1 |>.mono (Nat.zero_le _))).congr fun c ↦ ?_
    rw [prefixSum_eq, hlen c, ite_eq_right hn, List.foldl_reverse]

/-- An entry of `zipWith f τ (pre ++ z :: rest)`, `f` affine in its second argument. -/
theorem polyIn_zipWith_line (f : E → E → E) (hf : ∀ t, PolyIn (f t) 1) (τ pre rest : List E)
    (i : ℕ) : PolyIn (fun z ↦ (List.zipWith f τ (pre ++ z :: rest)).getD i 0)
      (if i = pre.length then 1 else 0) := by
  have hl : ∀ z : E, (pre ++ z :: rest).length = (pre ++ (0 : E) :: rest).length := fun z ↦ by simp
  by_cases hc : i < τ.length ∧ i < (pre ++ (0 : E) :: rest).length
  · by_cases hi : i = pre.length
    · exact ((hf (τ.getD i 0)).congr fun z ↦ by
        rw [getD_zipWith, ite_eq_left (by rw [hl]; exact hc), getD_line, ite_eq_left hi]).mono
        (by simp [hi])
    · exact polyIn_of_const (fun z ↦ by
        rw [getD_zipWith, getD_zipWith, ite_eq_left (by rw [hl]; exact hc), ite_eq_left (by rw [hl]; exact hc),
          getD_line, getD_line, ite_eq_right hi, ite_eq_right hi]) _
  · exact polyIn_of_const (fun z ↦ by
      rw [getD_zipWith, getD_zipWith, ite_eq_right (by rw [hl]; exact hc), ite_eq_right (by rw [hl]; exact hc)]) _

theorem mlin_omegaAt (θ : E) (τ : List E) (n : ℕ) : MLin fun p ↦ omegaAt θ τ p n := by
  intro pre rest
  have hp := polyIn_prefixSum
    (fun z ↦ List.zipWith (fun t x ↦ (1 + t) * (1 + x)) τ (pre ++ z :: rest))
    (fun z ↦ List.zipWith (fun t x ↦ t * x) τ (pre ++ z :: rest)) pre.length n
    (fun c ↦ by simp)
    (polyIn_zipWith_line _ (fun t ↦ ((PolyIn.const (1 + t)).mul ((PolyIn.const 1).add
      PolyIn.var)).mono (by norm_num)) τ pre rest)
    (polyIn_zipWith_line _ (fun t ↦ ((PolyIn.const t).mul PolyIn.var).mono (by norm_num)) τ pre rest)
  exact (((PolyIn.const θ).mul hp).congr fun z ↦ rfl).mono (by norm_num)

/-! ## Forms -/

/-- The largest monomial's length. -/
def Form.deg (f : Form) : ℕ := (f.terms.map (·.1.length)).foldl max 0

theorem le_foldl_max : ∀ (L : List ℕ) (a : ℕ), a ≤ L.foldl max a ∧ ∀ x ∈ L, x ≤ L.foldl max a
  | [], a => ⟨le_rfl, by simp⟩
  | y :: L, a => by
    obtain ⟨h1, h2⟩ := le_foldl_max L (max a y)
    refine ⟨(le_max_left a y).trans h1, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right a x).trans h1
    · exact h2 x hx

theorem polyIn_monomial (col : E → ℕ → E) (dc : ℕ) (hcol : ∀ i, PolyIn (fun c ↦ col c i) dc) :
    ∀ (m : List ℕ) (a : E → E) (da : ℕ), PolyIn a da →
      PolyIn (fun c ↦ m.foldl (fun acc i ↦ acc * col c i) (a c)) (da + m.length * dc)
  | [], _, _, ha => ha.mono (by simp)
  | i :: m, a, da, ha => (polyIn_monomial col dc hcol m _ _ (ha.mul (hcol i))).mono (by
      simp only [List.length_cons]; nlinarith)

/-- **A form at columns of degree at most `dc`** is of degree at most `deg·dc`. -/
theorem polyIn_evaluate (f : Form) (col : E → ℕ → E) (dc : ℕ)
    (hcol : ∀ i, PolyIn (fun c ↦ col c i) dc) :
    PolyIn (fun c ↦ f.evaluate (col c)) (Form.deg f * dc) :=
  polyIn_listSum_map f.terms fun t ht ↦
    (polyIn_monomial col dc hcol t.1 (fun _ ↦ t.2) 0 (PolyIn.const t.2)).mono (by
      rw [Nat.zero_add]
      exact Nat.mul_le_mul_right _ ((le_foldl_max _ 0).2 _ (List.mem_map_of_mem ht)))

end

end LeanVM.Protocol.Relation.RowPoly
