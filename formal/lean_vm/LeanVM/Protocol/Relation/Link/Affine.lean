/-
  LeanVM.Protocol.Relation.Link.Affine

  The row summand is affine in the fresh coefficients, so the row side's full sum is the index
  summand plus the fresh coefficients' weights.
-/

module

public import LeanVM.Protocol.Relation.Link.Summand
public import LeanVM.Protocol.Relation.Link.TailEq
public import LeanVM.Protocol.Relation.Link.Shape
public import LeanVM.Protocol.Link.Sound

/-!
# The fresh coefficients enter linearly

`verify_link`'s five fresh coefficients are `cert` (the mirror certificates' weight, in `lastOf`)
and `jump` (`JUMP`'s identities, in `tableBaseOf`). The row side's fold reads `jump` only in its
`base` (`rowStep_base`, `rowStep_rest`), and a table has at most four identities
(`tables_constraints_length`), so `base` is affine in `jump` (`Aff4`, `rowSideOf_aff`); `lastOf` is
affine in `cert` and in `base` (`lastOf_split`). Hence `rowSummand_fresh`: the row summand at `fresh`
is its value at `[]` plus `Σ_i fresh_i` times what the unit vector `i` adds, and `row_total_of_summand`
(`LinkSummandFacts.row_total`) by summing over the cube.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link Finset

@[expose] public section

/-! ## Sums of lists -/

theorem zipWith_mul_sum : ∀ (a b : List E) (n : ℕ), b.length ≤ n →
    (List.zipWith (· * ·) a b).sum = ∑ j : Fin n, a.getD j 0 * b.getD j 0
  | [], b, n, _ => by simp
  | _ :: _, [], n, _ => by simp
  | x :: a, y :: b, n + 1, h => by
    rw [List.zipWith_cons_cons, List.sum_cons, Fin.sum_univ_succ,
      zipWith_mul_sum a b n (by simpa using h)]
    simp
  | _ :: _, _ :: _, 0, h => by simp at h

theorem getD_drop_one (l : List E) (j : ℕ) : (l.drop 1).getD j 0 = l.getD (j + 1) 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_map_mul (c w : E) : ∀ (l : List E) (i : ℕ),
    (l.map fun n ↦ c * w * n).getD i 0 = c * (w * l.getD i 0)
  | [], i => by simp
  | x :: l, 0 => by simp; ring
  | x :: l, i + 1 => by simpa using getD_map_mul c w l i

/-! ## Affine in four coordinates -/

/-- `g` is affine in the first four coordinates of its argument. -/
def Aff4 (g : List E → E) : Prop :=
  ∃ (A : E) (C : Fin 4 → E), ∀ jump, g jump = A + ∑ j : Fin 4, jump.getD (j : ℕ) 0 * C j

theorem Aff4.add {f g : List E → E} (hf : Aff4 f) (hg : Aff4 g) : Aff4 fun j ↦ f j + g j := by
  obtain ⟨A, C, h⟩ := hf
  obtain ⟨A', C', h'⟩ := hg
  refine ⟨A + A', fun j ↦ C j + C' j, fun jump ↦ ?_⟩
  dsimp only
  rw [h, h']
  simp only [mul_add, sum_add_distrib]
  ring

theorem Aff4.const_mul {f : List E → E} (c : E) (hf : Aff4 f) : Aff4 fun j ↦ c * f j := by
  obtain ⟨A, C, h⟩ := hf
  refine ⟨c * A, fun j ↦ c * C j, fun jump ↦ ?_⟩
  dsimp only
  rw [h, mul_add, mul_sum]
  exact congrArg (c * A + ·) (sum_congr rfl fun j _ ↦ by ring)

theorem Aff4.congr {f g : List E → E} (hf : Aff4 f) (h : ∀ j, f j = g j) : Aff4 g := by
  obtain ⟨A, C, hA⟩ := hf
  exact ⟨A, C, fun j ↦ (h j).symm.trans (hA j)⟩

theorem Aff4.const (a : E) : Aff4 fun _ ↦ a := ⟨a, 0, fun _ ↦ by simp⟩

/-! ## The tables' identities -/

theorem tables_constraints_length : ∀ table ∈ tables, ∀ values : List E,
    (table.constraints values).length ≤ 4 := by
  intro table ht values
  simp only [tables, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [jumpConstraints]

theorem tableBaseOf_aff (ch : LinkCh) (a : IdxAt) (point : List E) (height : ℕ) (omega : E)
    (table : Table) (t : ℕ) (values : List E) (hc : (table.constraints values).length ≤ 4) :
    Aff4 fun jump ↦ tableBaseOf ch a jump point height omega table t values := by
  unfold tableBaseOf
  dsimp only
  split_ifs
  · refine (Aff4.const _).add (Aff4.const_mul _ ⟨0, fun j ↦ (table.constraints values).getD j 0,
      fun jump ↦ ?_⟩)
    dsimp only
    rw [sumE_eq_sum, zipWith_mul_sum _ _ 4 hc, zero_add]
  · exact Aff4.const _

/-! ## The fold -/

/-- Everything the row side's fold carries but `base`. -/
def restOf (acc : LinkRowSide) :
    E × List E × E × List RingPiece × ℕ × List (List E × List (ℕ × E)) × List E :=
  (acc.coef, acc.shifts, acc.certWeight, acc.pieces, acc.q, acc.columns, acc.sent)

/-- What table `x` adds to `base`, from the values left before it. -/
def stepAdd (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump chi sent : List E) (x : Table × ℕ) :
    E :=
  let table := x.1
  let t := x.2
  let height := layout.tableLogHeights.getD t 0
  let point := chi.take height
  let corner := prodE ((chi.drop height).map (1 + ·))
  let columns := nonPointerOf layout t table
  let sentT := columns.zip (sent.take columns.length)
  let values := (List.range table.width).map fun c ↦ (sentT.lookup c).getD 0
  let omega := omegaAt (ch.theta.getD t 0) (ch.tau.take height) point (layout.tableRows.getD t 0)
  corner * tableBaseOf ch a jump point height omega table t values

/-- A pointer column's step, on a side with its `base` set to zero. -/
def zeroBase (acc : LinkRowSide) : LinkRowSide := { acc with base := 0 }

theorem ptrStep_rest (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : List E)
    (corner omega act sHat sNext : E) (table : Table) (t : ℕ) (col : ℕ → E) (acc : LinkRowSide)
    (y : ℕ × ℕ) :
    restOf (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc y) =
      restOf (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col
        (zeroBase acc) y) := by
  obtain ⟨p, k⟩ := y
  rfl

theorem foldl_ptrStep_rest (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : List E)
    (corner omega act sHat sNext : E) (table : Table) (t : ℕ) (col : ℕ → E) (l : List (ℕ × ℕ))
    (b b' : LinkRowSide) (h : restOf b = restOf b') :
    restOf (l.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) b) =
      restOf (l.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) b') := by
  have hg := fun b y ↦ ptrStep_rest layout ch a eqQ point corner omega act sHat sNext table t col b y
  let g := fun (r : E × List E × E × List RingPiece × ℕ × List (List E × List (ℕ × E)) × List E)
      (y : ℕ × ℕ) ↦
    restOf (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col
      ⟨r.1, r.2.1, r.2.2.1, 0, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2⟩ y)
  rw [foldl_proj restOf _ g (fun b y ↦ (hg b y).trans rfl) l b,
    foldl_proj restOf _ g (fun b y ↦ (hg b y).trans rfl) l b', h]

theorem foldl_ptrStep_base (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : List E)
    (corner omega act sHat sNext : E) (table : Table) (t : ℕ) (col : ℕ → E) (l : List (ℕ × ℕ))
    (b : LinkRowSide) :
    (l.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) b).base =
      b.base := by
  rw [foldl_proj LinkRowSide.base _ (fun s _ ↦ s) (fun b y ↦ by obtain ⟨p, k⟩ := y; rfl) l b,
    foldl_const_self]

/-- A table's pointer columns, folded from a start. -/
def ptrFold (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ chi sent : List E) (x : Table × ℕ)
    (S : LinkRowSide) : LinkRowSide :=
  let table := x.1
  let t := x.2
  let height := layout.tableLogHeights.getD t 0
  let tableRows := layout.tableRows.getD t 0
  let point := chi.take height
  let corner := prodE ((chi.drop height).map (1 + ·))
  let columns := nonPointerOf layout t table
  let sentT := columns.zip (sent.take columns.length)
  let values := (List.range table.width).map fun c ↦ (sentT.lookup c).getD 0
  let col := fun (c : ℕ) ↦ values.getD c 0
  let state := table.links.stateLink
  let omega := omegaAt (ch.theta.getD t 0) (ch.tau.take height) point tableRows
  let act := lessThan point tableRows
  let sHat := ch.stateGamma (col state.pc) (col state.fp)
  let sNext := ch.stateGamma (state.next.1.evaluate col) (state.next.2.evaluate col)
  ((layout.tables.map (·.links.pointers)).getD t []).zipIdx.foldl
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) S

/-- The column entry a table appends. -/
def rowCol (layout : Layout) (chi sent : List E) (x : Table × ℕ) : List E × List (ℕ × E) :=
  (chi.take (layout.tableLogHeights.getD x.2 0),
    (nonPointerOf layout x.2 x.1).zip (sent.take (nonPointerOf layout x.2 x.1).length))

theorem rowStep_def (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi : List E)
    (acc : LinkRowSide) (x : Table × ℕ) :
    rowStep layout ch a jump eqQ chi acc x =
      let S : LinkRowSide := { acc with
        base := acc.base + stepAdd layout ch a jump chi acc.sent x,
        sent := acc.sent.drop (nonPointerOf layout x.2 x.1).length }
      { ptrFold layout ch a eqQ chi acc.sent x S with
        columns := (ptrFold layout ch a eqQ chi acc.sent x S).columns ++
          [rowCol layout chi acc.sent x] } := by
  obtain ⟨table, t⟩ := x
  rfl

theorem ptrFold_rest (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ chi sent : List E)
    (x : Table × ℕ) {S S' : LinkRowSide} (h : restOf S = restOf S') :
    restOf (ptrFold layout ch a eqQ chi sent x S) = restOf (ptrFold layout ch a eqQ chi sent x S') :=
  foldl_ptrStep_rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

theorem restOf_ptrFold_cols (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ chi sent : List E)
    (x : Table × ℕ) {S S' : LinkRowSide} (h : restOf S = restOf S') (X : List (List E × List (ℕ × E))) :
    restOf { ptrFold layout ch a eqQ chi sent x S with
      columns := (ptrFold layout ch a eqQ chi sent x S).columns ++ X } =
    restOf { ptrFold layout ch a eqQ chi sent x S' with
      columns := (ptrFold layout ch a eqQ chi sent x S').columns ++ X } := by
  have k := ptrFold_rest layout ch a eqQ chi sent x h
  simp only [restOf, Prod.mk.injEq] at k ⊢
  exact ⟨k.1, k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2.1, by rw [k.2.2.2.2.2.1], k.2.2.2.2.2.2⟩

/-- **A table's step adds to `base`** what `stepAdd` says. -/
theorem rowStep_base (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi : List E)
    (acc : LinkRowSide) (x : Table × ℕ) :
    (rowStep layout ch a jump eqQ chi acc x).base = acc.base + stepAdd layout ch a jump chi acc.sent x := by
  rw [rowStep_def]
  exact foldl_ptrStep_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **A table's step carries the rest** independently of `jump` and `base`. -/
theorem rowStep_rest (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump jump' eqQ chi : List E)
    (acc acc' : LinkRowSide) (h : restOf acc = restOf acc') (x : Table × ℕ) :
    restOf (rowStep layout ch a jump eqQ chi acc x) =
      restOf (rowStep layout ch a jump' eqQ chi acc' x) := by
  have hs : acc.sent = acc'.sent := congrArg (·.2.2.2.2.2.2) h
  rw [rowStep_def, rowStep_def]
  dsimp only
  rw [hs]
  apply restOf_ptrFold_cols
  simp only [restOf, Prod.mk.injEq] at h ⊢
  simp only [h, and_self]


theorem stepAdd_aff (layout : Layout) (ch : LinkCh) (a : IdxAt) (chi sent : List E) (x : Table × ℕ)
    (hc : ∀ values : List E, (x.1.constraints values).length ≤ 4) :
    Aff4 fun jump ↦ stepAdd layout ch a jump chi sent x := by
  unfold stepAdd
  dsimp only
  exact Aff4.const_mul _ (tableBaseOf_aff _ _ _ _ _ _ _ _ (hc _))

/-- **The fold is affine in `jump`**: the rest is `jump`'s alone, `base` affine. -/
theorem fold_aff (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ chi : List E) :
    ∀ (L : List (Table × ℕ)), (∀ x ∈ L, ∀ values : List E, (x.1.constraints values).length ≤ 4) →
    ∀ (b : List E → LinkRowSide), (∀ j, restOf (b j) = restOf (b [])) → Aff4 (fun j ↦ (b j).base) →
    (∀ j, restOf (L.foldl (rowStep layout ch a j eqQ chi) (b j)) =
      restOf (L.foldl (rowStep layout ch a [] eqQ chi) (b []))) ∧
    Aff4 fun j ↦ (L.foldl (rowStep layout ch a j eqQ chi) (b j)).base
  | [], _, _, hr, ha => ⟨hr, ha⟩
  | x :: L, hL, b, hr, ha => by
    simp only [List.foldl_cons]
    refine fold_aff layout ch a eqQ chi L (fun y hy ↦ hL y (by simp [hy]))
      (fun j ↦ rowStep layout ch a j eqQ chi (b j) x)
      (fun j ↦ rowStep_rest _ _ _ _ _ _ _ _ _ (hr j) x) ?_
    have hs : ∀ j, (b j).sent = (b []).sent := fun j ↦ congrArg (·.2.2.2.2.2.2) (hr j)
    refine (ha.add (stepAdd_aff layout ch a chi (b []).sent x (hL x (by simp)))).congr fun j ↦ ?_
    rw [rowStep_base, hs j]

theorem rowSideOf_aff (layout : Layout) (hT : layout.tables = tables) (ch : LinkCh) (a : IdxAt)
    (eqQ chi message : List E) :
    (∀ j, restOf (rowSideOf layout ch a j eqQ chi message) =
      restOf (rowSideOf layout ch a [] eqQ chi message)) ∧
    Aff4 fun j ↦ (rowSideOf layout ch a j eqQ chi message).base :=
  fold_aff layout ch a eqQ chi layout.tables.zipIdx
    (fun x hx values ↦ tables_constraints_length x.1 (hT ▸ fst_mem_of_mem_zipIdx _ _ _ hx) values)
    (fun _ ↦ rowStart layout message) (fun _ ↦ rfl) (Aff4.const _)

/-! ## The summand at the final point -/

theorem lastOf_rest (layout : Layout) (chunks : Chunks) (ch : LinkCh) (r : List E) (cert : E)
    (qPoint slices : List E) {rs rs' : LinkRowSide} (h : restOf rs = restOf rs') :
    lastOf layout chunks ch r cert qPoint slices rs =
      lastOf layout chunks ch r cert qPoint slices rs' +
        prodE (qPoint.map (1 + ·)) * (rs.base - rs'.base) := by
  obtain ⟨c, s, w, b, p, q, cs, se⟩ := rs
  obtain ⟨c', s', w', b', p', q', cs', se'⟩ := rs'
  simp only [restOf, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  simp only [lastOf]
  ring

theorem lastOf_cert (layout : Layout) (chunks : Chunks) (ch : LinkCh) (r : List E) (cert : E)
    (qPoint slices : List E) (rs : LinkRowSide) :
    lastOf layout chunks ch r cert qPoint slices rs =
      lastOf layout chunks ch r 0 qPoint slices rs +
        cert * (lastOf layout chunks ch r 1 qPoint slices rs -
          lastOf layout chunks ch r 0 qPoint slices rs) := by
  simp only [lastOf, Functionals.summand, getD_map_mul, sumE_eq_sum]
  simp only [mul_assoc]
  simp only [List.sum_map_mul_left]
  ring

/-! ## The row summand -/

theorem aff5_unit (f : List E → E) (A : E) (D : Fin 5 → E)
    (h : ∀ fresh, f fresh = A + ∑ i : Fin 5, fresh.getD (i : ℕ) 0 * D i) (fresh : List E) :
    f fresh = f [] + ∑ i : Fin 5, fresh.getD (i : ℕ) 0 * (f (unitFresh i) - f []) := by
  have h0 : f [] = A := by simp [h]
  have hu : ∀ i, f (unitFresh i) - A = D i := by
    intro i
    rw [h (unitFresh i), unitFresh]
    simp only [getD_ofFn, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      add_sub_cancel_left]
  rw [h fresh, h0]
  exact congrArg (A + ·) (sum_congr rfl fun i _ ↦ by rw [hu i])

/-- **The row summand is affine in the fresh coefficients.** -/
theorem rowSummand_fresh (layout : Layout) (hT : layout.tables = tables) (chunks : Chunks)
    {μ : ℕ} (q : Column μ) (theta0 : E) (drawn r fresh x : List E) :
    rowSummand layout chunks q theta0 drawn r fresh x =
      rowSummand layout chunks q theta0 drawn r [] x + ∑ i : Fin 5, fresh.getD i 0 *
        (rowSummand layout chunks q theta0 drawn r (unitFresh i) x -
          rowSummand layout chunks q theta0 drawn r [] x) := by
  set ch := linkCh layout chunks theta0 drawn
  set a := idxAt layout chunks ch r (honestM1 layout chunks q r) (linkSplit layout r)
  set chi := x.take (linkRows layout)
  set qPoint := x.drop (linkRows layout)
  set msg := honestMessage layout q chi qPoint
  obtain ⟨hrest, A, C, hA⟩ := rowSideOf_aff layout hT ch a (eqKernel qPoint) chi msg
  beta_reduce at hA
  set rs0 := rowSideOf layout ch a [] (eqKernel qPoint) chi msg
  set L0 := lastOf layout chunks ch r 0 qPoint (msg.drop (nValuesOf layout)) rs0
  set L1 := lastOf layout chunks ch r 1 qPoint (msg.drop (nValuesOf layout)) rs0
  refine aff5_unit (fun fresh ↦ rowSummand layout chunks q theta0 drawn r fresh x) L0
    (Fin.cons (L1 - L0) fun j ↦ prodE (qPoint.map (1 + ·)) * C j) (fun fresh ↦ ?_) fresh
  have e : rowSummand layout chunks q theta0 drawn r fresh x =
      lastOf layout chunks ch r (fresh.getD 0 0) qPoint (msg.drop (nValuesOf layout))
        (rowSideOf layout ch a (fresh.drop 1) (eqKernel qPoint) chi msg) := rfl
  rw [e, lastOf_rest _ _ _ _ _ _ _ (hrest (fresh.drop 1)), lastOf_cert, hA (fresh.drop 1), hA [],
    Fin.sum_univ_succ (n := 4)]
  simp only [Fin.cons_zero, Fin.cons_succ, List.getD_nil, zero_mul, sum_const_zero, add_zero,
    getD_drop_one, Fin.val_succ, Fin.val_zero, add_sub_cancel_left]
  rw [mul_sum, add_assoc]
  refine congrArg (L0 + ·) (congrArg (_ + ·) (sum_congr rfl fun j _ ↦ ?_))
  ring

theorem sumTail_sub (f g : List E → E) : ∀ (k : ℕ) (p : List E),
    sumTail (fun x ↦ f x - g x) k p = sumTail f k p - sumTail g k p
  | 0, _ => rfl
  | k + 1, p => by simp only [sumTail, sumTail_sub f g k]; ring

/-- **The row side's full sum** is the index summand plus the fresh coefficients' weights
(`LinkSummandFacts.row_total`). -/
theorem row_total_of_summand (layout : Layout) (hT : layout.tables = tables) (chunks : Chunks)
    {μ : ℕ} (q : Column μ) : ∀ theta0 drawn r fresh,
    linkRow layout chunks q theta0 drawn r fresh [] =
      linkIdxAt layout chunks q theta0 drawn r +
        ∑ i : Fin 5, fresh.getD i 0 * linkB layout chunks q theta0 drawn r i := by
  intro theta0 drawn r fresh
  have hf : rowSummand layout chunks q theta0 drawn r fresh = fun x ↦
      rowSummand layout chunks q theta0 drawn r [] x + ∑ i : Fin 5, fresh.getD i 0 *
        (rowSummand layout chunks q theta0 drawn r (unitFresh i) x -
          rowSummand layout chunks q theta0 drawn r [] x) :=
    funext fun x ↦ rowSummand_fresh layout hT chunks q theta0 drawn r fresh x
  simp only [linkB, linkIdxAt, linkRow, cube]
  rw [hf, sumTail_add, sumTail_finsetSum]
  simp only [sumTail_smul, sumTail_sub]

end

end LeanVM.Protocol.Relation
