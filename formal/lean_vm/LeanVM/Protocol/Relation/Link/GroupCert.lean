/-
  LeanVM.Protocol.Relation.Link.GroupCert

  The certificate's weight `linkB … r 0` in closed form: the batched mirror certificate over the
  tables' executed rows and pointer columns.
-/

module

public import LeanVM.Protocol.Relation.Link.Summand
public import LeanVM.Protocol.Relation.Link.GroupFold
public import LeanVM.Protocol.Relation.Link.GroupCube

/-!
# The certificate's weight

`linkB … r 0` is what the certificate's coefficient adds to the row side's sum. At a stack `q`:

* `rowSummand_cert`: the row summand at the unit coefficient less the one at none is the
  certificate term `certTerm` (the row side's fold does not see a zero `JUMP` coefficient);
* `linkB_zero_eq`: `linkB … r 0` is the certificate term summed over the Boolean row and
  pointer-column points.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

theorem sumE_eq_sum' (l : List E) : sumE l = l.sum := by
  rw [sumE, List.sum_eq_foldl]

theorem sumE_zipWith_replicate_zero (k : ℕ) : ∀ l : List E, sumE (List.zipWith (· * ·) (List.replicate k 0) l) = 0 := by
  intro l
  rw [sumE_eq_sum']
  induction l generalizing k with
  | nil => simp
  | cons x l ih => cases k <;> simp [List.replicate_succ, ih]

theorem sumE_nil : sumE [] = 0 := rfl

theorem tableBaseOf_zero_jump (ch : LinkCh) (a : IdxAt) (k : ℕ) (point : List E) (height : ℕ)
    (omega : E) (table : Table) (t : ℕ) (values : List E) :
    tableBaseOf ch a (List.replicate k 0) point height omega table t values =
      tableBaseOf ch a [] point height omega table t values := by
  have h0 : ∀ ids : List E, sumE (List.zipWith (· * ·) (List.replicate k 0) ids) =
      sumE (List.zipWith (· * ·) ([] : List E) ids) := fun ids ↦ by
    rw [sumE_zipWith_replicate_zero, List.zipWith_nil_left, sumE_nil]
  unfold tableBaseOf
  dsimp only
  split_ifs
  · rw [h0]
  · rfl

theorem rowSideOf_zero_jump (layout : Layout) (ch : LinkCh) (a : IdxAt) (k : ℕ) (eqQ chi message : List E) :
    rowSideOf layout ch a (List.replicate k 0) eqQ chi message = rowSideOf layout ch a [] eqQ chi message := by
  have h : rowStep layout ch a (List.replicate k 0) eqQ chi = rowStep layout ch a [] eqQ chi := by
    funext acc p
    obtain ⟨table, t⟩ := p
    dsimp only [rowStep]
    rw [tableBaseOf_zero_jump]
  unfold rowSideOf
  rw [h]

theorem unitFresh_zero_drop : (unitFresh 0).drop 1 = List.replicate 4 0 := by
  simp [unitFresh, List.ofFn_succ]

theorem unitFresh_zero_head : (unitFresh 0).getD 0 0 = 1 := by
  simp [unitFresh, List.ofFn_succ]

theorem getD_map_of_zero (l : List E) (g : E → E) (hg : g 0 = 0) (i : ℕ) :
    (l.map g).getD i 0 = g (l.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hg]

theorem list_sum_map_sub {α : Type} (l : List α) (f g : α → E) :
    (l.map f).sum - (l.map g).sum = (l.map fun i ↦ f i - g i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ← ih]; ring

theorem functionals_d (chunks : Chunks) (r : List E) (ms : ℕ) : (Functionals.new chunks r ms).d = chunks.d := rfl

/-- The certificate's term at the final point `x = χ ++ q`: `Σ_i w·ν_i·(D_i(r)·D_i(1 + r) + π_i)` on
the stack's bit-slices, `w` the row side's certificate weight. -/
def certTerm (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E) (drawn r : List E)
    (x : List E) : E :=
  let chi := x.take (linkRows layout)
  let qPoint := x.drop (linkRows layout)
  let ch := linkCh layout chunks theta0 drawn
  let a := idxAt layout chunks ch r (honestM1 layout chunks q r) (linkSplit layout r)
  let rs := rowSideOf layout ch a [] (eqKernel qPoint) chi (honestMessage layout q chi qPoint)
  let f := Functionals.new chunks r (layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0)
  let values := f.values chunks ((honestMessage layout q chi qPoint).drop (nValuesOf layout))
  ((List.range chunks.d).map fun i ↦
    rs.certWeight * ch.nu.getD i 0 * (values.getD i 0 * values.getD (chunks.d + i) 0 + f.mirrors.getD i 0)).sum

/-- **The certificate's coefficient adds the certificate term.** -/
theorem rowSummand_cert (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r x : List E) :
    rowSummand layout chunks q theta0 drawn r (unitFresh 0) x - rowSummand layout chunks q theta0 drawn r [] x =
      certTerm layout chunks q theta0 drawn r x := by
  simp only [rowSummand, tailValuesF, lastOf, unitFresh_zero_drop, rowSideOf_zero_jump, unitFresh_zero_head,
    List.drop_nil, List.getD_nil, certTerm, Functionals.summand, sumE_eq_sum']
  rw [add_sub_add_right_eq_sub, add_sub_add_left_eq_sub, list_sum_map_sub, functionals_d]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  rw [getD_map_of_zero _ _ (by ring), getD_map_of_zero _ _ (by ring)]
  ring

theorem list_sum_range_map {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- **`linkB … r 0` over the cube**: the certificate term at the Boolean row and pointer-column
points. -/
theorem linkB_zero_eq (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r : List E) :
    linkB layout chunks q theta0 drawn r 0 = ∑ jx ∈ range (2 ^ linkRows layout),
      ∑ jq ∈ range (2 ^ linkQVars layout),
        certTerm layout chunks q theta0 drawn r (boolL (linkRows layout) jx ++ boolL (linkQVars layout) jq) := by
  simp only [linkB, linkIdxAt, linkRow, cube, List.length_nil, Nat.sub_zero, linkRowVars]
  rw [sumTail_split, sumTail_split, ← sum_sub_distrib]
  refine sum_congr rfl fun jx _ ↦ ?_
  rw [sumTail_eq_sum, sumTail_eq_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun jq _ ↦ ?_
  rw [List.nil_append, rowSummand_cert]

theorem list_sum_flatMap {α : Type} (l : List α) (f : α → List E) :
    (l.flatMap f).sum = (l.map fun a ↦ (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- The placement of table `t`'s pointer column `k`. -/
def placementAt (layout : Layout) (t k : ℕ) : Option Placement :=
  some ((layout.placements.getD (globalColumnBases.getD t 0 + (ptrsOf layout t).getD k 0) none).getD default)

theorem length_honestValues (layout : Layout) {μ : ℕ} (q : Column μ) (chi : List E) :
    (honestValues layout q chi).length = nValuesOf layout := by
  simp [honestValues, nValuesOf, List.length_flatten, Function.comp_def]

/-- **The bit-slices in closed form**: slice `b` sums each pointer column's bit `b` at its table's row
point, weighed by `eq(q, ·)` at its index. -/
theorem honestSlices_closed (layout : Layout) {μ : ℕ} (q : Column μ) (chi qPoint : List E) :
    (honestMessage layout q chi qPoint).drop (nValuesOf layout) = (List.range kBits).map fun b ↦
      ∑ t ∈ range layout.tables.length, ∑ k ∈ range (ptrsOf layout t).length,
        (eqKernel qPoint).getD (qBase layout t + k) 0 *
          rowMle (chi.take (heightOf layout t)) fun j ↦ bitOf (pieceRow q (placementAt layout t k) j) b := by
  rw [honestMessage, List.drop_append_of_le_length (by rw [length_honestValues]),
    ← length_honestValues layout q chi, List.drop_length, List.nil_append, honestSlices]
  refine List.map_congr_left fun b _ ↦ ?_
  have hp := (rowSideOf_closed layout ⟨[], [], [], [], [], 0, 0, [], [], [], []⟩ ⟨0, 0, 0, 0, 0, 0, 0⟩ []
    (eqKernel qPoint) chi []).2.2
  rw [piecesOf, hp, sumE_eq_sum', List.map_flatMap, list_sum_flatMap, list_sum_range_map]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [List.map_map, list_sum_range_map]
  rfl

/-- Table `t`'s pointer column `k` at row `u`, the word the ring claim reads. -/
def wordAt (layout : Layout) {μ : ℕ} (q : Column μ) (t k u : ℕ) : K := pieceRow q (placementAt layout t k) u

/-- Chunk `i`'s mirror certificate `D_i(r)·D_i(1 + r) + π_i` of a word, from its bits. -/
def certAt (layout : Layout) (chunks : Chunks) (r : List E) (w : K) (i : ℕ) : E :=
  let f := Functionals.new chunks r (layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0)
  let values := f.values chunks ((List.range kBits).map (bitOf w))
  values.getD i 0 * values.getD (chunks.d + i) 0 + f.mirrors.getD i 0

theorem qBase_mono (layout : Layout) {a b : ℕ} (h : a ≤ b) : qBase layout a ≤ qBase layout b :=
  sum_le_sum_of_subset (range_subset_range.mpr h)

/-- Distinct pointer columns have distinct indices. -/
theorem qBase_inj (layout : Layout) {t t' k k' : ℕ} (hk : k < (ptrsOf layout t).length)
    (hk' : k' < (ptrsOf layout t').length) (h : qBase layout t + k = qBase layout t' + k') :
    t = t' ∧ k = k' := by
  rcases lt_trichotomy t t' with hlt | rfl | hgt
  · have := qBase_mono layout (show t + 1 ≤ t' by omega)
    rw [qBase_succ] at this
    omega
  · exact ⟨rfl, by omega⟩
  · have := qBase_mono layout (show t' + 1 ≤ t by omega)
    rw [qBase_succ] at this
    omega

/-- The double sum over the pointer columns at one index. -/
theorem sum_ptr_single (layout : Layout) (T : ℕ) (X : ℕ → ℕ → E) {t k : ℕ} (ht : t < T)
    (hk : k < (ptrsOf layout t).length) :
    ∑ t' ∈ range T, ∑ k' ∈ range (ptrsOf layout t').length,
      (if qBase layout t' + k' = qBase layout t + k then 1 else 0) * X t' k' = X t k := by
  rw [sum_eq_single t, sum_eq_single k]
  · simp
  · intro k' hk' hne
    simp only [show ¬ (qBase layout t + k' = qBase layout t + k) from
      fun h ↦ hne (qBase_inj layout (mem_range.mp hk') hk h).2, ↓reduceIte, zero_mul]
  · intro h; exact absurd (mem_range.mpr hk) h
  · intro t' _ hne
    refine sum_eq_zero fun k' hk' ↦ ?_
    simp only [show ¬ (qBase layout t' + k' = qBase layout t + k) from
      fun h ↦ hne (qBase_inj layout (mem_range.mp hk') hk h).1, ↓reduceIte, zero_mul]
  · intro h; exact absurd (mem_range.mpr ht) h

/-- **The certificate term at a Boolean point** `(jx, jq)`: the pointer column at index `jq`, at
its table's row `jx mod 2^h`. -/
theorem certTerm_bool (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r : List E) {jx jq : ℕ} (hjq : jq < 2 ^ linkQVars layout)
    (hh : ∀ t, heightOf layout t ≤ linkRows layout) :
    certTerm layout chunks q theta0 drawn r (boolL (linkRows layout) jx ++ boolL (linkQVars layout) jq) =
      ∑ t ∈ range layout.tables.length, ∑ k ∈ range (ptrsOf layout t).length,
        (if qBase layout t + k = jq then 1 else 0) *
          (cornerAt layout (boolL (linkRows layout) jx) t *
            omegaOf layout (linkCh layout chunks theta0 drawn) (boolL (linkRows layout) jx) t *
            (linkCh layout chunks theta0 drawn).eps.getD (qBase layout t + k) 0) *
          ((List.range chunks.d).map fun i ↦ (linkCh layout chunks theta0 drawn).nu.getD i 0 *
            certAt layout chunks r (wordAt layout q t k (jx % 2 ^ heightOf layout t)) i).sum := by
  unfold certTerm
  simp only [List.take_left' (length_boolL _ _), List.drop_left' (length_boolL _ _)]
  rw [honestSlices_closed, (rowSideOf_closed _ _ _ _ _ _ _).2.1]
  set ch := linkCh layout chunks theta0 drawn
  set fs := Functionals.new chunks r (layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0)
  set S := (List.range kBits).map fun b ↦ ∑ t ∈ range layout.tables.length, ∑ k ∈ range (ptrsOf layout t).length,
    (eqKernel (boolL (linkQVars layout) jq)).getD (qBase layout t + k) 0 *
      rowMle ((boolL (linkRows layout) jx).take (heightOf layout t)) fun j ↦
        bitOf (pieceRow q (placementAt layout t k) j) b
  have hsum : ∀ (c : E), ((List.range chunks.d).map fun i ↦ c * ch.nu.getD i 0 *
      ((fs.values chunks S).getD i 0 * (fs.values chunks S).getD (chunks.d + i) 0 + fs.mirrors.getD i 0)).sum =
      c * ((List.range chunks.d).map fun i ↦ ch.nu.getD i 0 *
      ((fs.values chunks S).getD i 0 * (fs.values chunks S).getD (chunks.d + i) 0 + fs.mirrors.getD i 0)).sum := by
    intro c
    rw [list_sum_range_map, list_sum_range_map, mul_sum]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hsum, sum_mul]
  refine sum_congr rfl fun t ht ↦ ?_
  rw [sum_mul]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [eqKernel_boolL hjq]
  by_cases he : qBase layout t + k = jq
  · have hS : S = (List.range kBits).map (bitOf (wordAt layout q t k (jx % 2 ^ heightOf layout t))) := by
      refine List.map_congr_left fun b _ ↦ ?_
      simp only [eqKernel_boolL hjq]
      rw [← he, sum_ptr_single layout _ (fun t' k' ↦ rowMle ((boolL (linkRows layout) jx).take (heightOf layout t'))
        fun j ↦ bitOf (pieceRow q (placementAt layout t' k') j) b) (mem_range.mp ht) (mem_range.mp hk)]
      rw [take_boolL (hh t), rowMle_boolL (Nat.mod_lt _ (Nat.two_pow_pos _))]
      rfl
    simp only [he, ↓reduceIte, hS, certAt]
    ring
  · simp only [he, ↓reduceIte]
    ring

theorem sum_range_ite_lt {N n : ℕ} (h : n ≤ N) (f : ℕ → E) :
    ∑ x ∈ range N, (if x < n then f x else 0) = ∑ x ∈ range n, f x := by
  rw [← sum_filter]
  congr 1
  ext x
  simp only [mem_filter, mem_range]
  omega

/-- **The certificate's weight in closed form**: `Σ_t θ_t Σ_k ε_{qBase t + k} Σ_{u < rows_t}
eq(τ, u)·Σ_i ν_i·cert_i(r, word_{t,k}(u))`, the batched mirror certificate over the executed rows. -/
theorem linkB_zero_closed (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r : List E) (hq : qBase layout layout.tables.length ≤ 2 ^ linkQVars layout)
    (hh : ∀ t, heightOf layout t ≤ linkRows layout)
    (hrows : ∀ t < layout.tables.length, layout.tableRows.getD t 0 ≤ 2 ^ heightOf layout t)
    (hτ : (linkCh layout chunks theta0 drawn).tau.length = linkRows layout) :
    linkB layout chunks q theta0 drawn r 0 =
      ∑ t ∈ range layout.tables.length, ∑ k ∈ range (ptrsOf layout t).length,
        ∑ u ∈ range (layout.tableRows.getD t 0),
          (linkCh layout chunks theta0 drawn).theta.getD t 0 *
            eqAt ((linkCh layout chunks theta0 drawn).tau.take (heightOf layout t)) u *
            (linkCh layout chunks theta0 drawn).eps.getD (qBase layout t + k) 0 *
            ((List.range chunks.d).map fun i ↦ (linkCh layout chunks theta0 drawn).nu.getD i 0 *
              certAt layout chunks r (wordAt layout q t k u) i).sum := by
  set ch := linkCh layout chunks theta0 drawn
  set Φ : ℕ → ℕ → ℕ → E := fun t k u ↦ ((List.range chunks.d).map fun i ↦ ch.nu.getD i 0 *
    certAt layout chunks r (wordAt layout q t k u) i).sum
  rw [linkB_zero_eq]
  have hjq : ∀ jx, ∑ jq ∈ range (2 ^ linkQVars layout),
      certTerm layout chunks q theta0 drawn r (boolL (linkRows layout) jx ++ boolL (linkQVars layout) jq) =
      ∑ t ∈ range layout.tables.length, ∑ k ∈ range (ptrsOf layout t).length,
        cornerAt layout (boolL (linkRows layout) jx) t * omegaOf layout ch (boolL (linkRows layout) jx) t *
          ch.eps.getD (qBase layout t + k) 0 * Φ t k (jx % 2 ^ heightOf layout t) := by
    intro jx
    rw [sum_congr rfl fun jq hjq ↦ certTerm_bool layout chunks q theta0 drawn r (mem_range.mp hjq) hh,
      sum_comm]
    refine sum_congr rfl fun t ht ↦ ?_
    rw [sum_comm]
    refine sum_congr rfl fun k hk ↦ ?_
    have hlt : qBase layout t + k < 2 ^ linkQVars layout := by
      have h1 := qBase_mono layout (show t + 1 ≤ layout.tables.length from mem_range.mp ht)
      rw [qBase_succ] at h1
      have := mem_range.mp hk
      omega
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_range, hlt, ↓reduceIte]
    rfl
  rw [sum_congr rfl fun jx _ ↦ hjq jx, sum_comm]
  refine sum_congr rfl fun t ht ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  have hrt := hrows t (mem_range.mp ht)
  have hpow : 2 ^ heightOf layout t ≤ 2 ^ linkRows layout := Nat.pow_le_pow_right (by norm_num) (hh t)
  rw [← sum_range_ite_lt (hrt.trans hpow)]
  refine sum_congr rfl fun jx hjx ↦ ?_
  have hjx' := mem_range.mp hjx
  rw [cornerAt, prodE_drop_boolL (hh t) hjx']
  by_cases hlt : jx < 2 ^ heightOf layout t
  · have hτh : (ch.tau.take (heightOf layout t)).length = heightOf layout t := by
      rw [List.length_take, hτ]; exact min_eq_left (hh t)
    rw [omegaOf, take_boolL (hh t), Nat.mod_eq_of_lt hlt, omegaAt_boolL _ _ hτh hlt hrt]
    simp only [hlt, ↓reduceIte]
    split_ifs <;> ring
  · simp only [hlt, ↓reduceIte, zero_mul, show ¬ jx < layout.tableRows.getD t 0 by omega]

end

end LeanVM.Protocol.Relation
