/-
  LeanVM.Protocol.Relation.Link.GroupLinksSummand

  The row summand at no fresh coefficient as the row side's shares (`GroupLinksFold.lean`), and the
  drawn challenges as functions of the draw: every coordinate of degree at most one.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupLinksFold
public import LeanVM.Protocol.Relation.Link.GroupCh
public import LeanVM.Facts.Hotwire

/-!
# The row summand and the challenges' coordinates

* `lk_rowSummand`: `rowSummand … r [] x` is `lkVal_rowSideOf`'s sum at the functional values the
  honest bit-slices give at `r` (the certificate's term is zero at no fresh coefficient);
* `Lin n f`: a list of the draw `v : Fin n → E` whose length does not depend on `v` and whose entries
  are of degree at most one; closed under `take`, `drop` and `cons` (`lin_take`, `lin_drop`,
  `lin_cons`), and `linkCh`'s slices are such lists (`linCh`);
* `eq(α, ·)`, `eq(ζ, r)` and `shift_eq(ζ, r)` of such lists are of degree at most their length
  (`polyFn_eqKernel_getD`, `polyFn_eqEval`, `polyFn_linkShiftEq`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

/-! ## The row summand at no fresh coefficient -/

/-- The functional values the honest bit-slices give at `r` and `x = χ ++ q`. -/
def lkFVals (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (r x : List E) : List E :=
  (Functionals.new chunks r (lkMaxShift layout)).values chunks
    ((honestMessage layout q (x.take (linkRows layout)) (x.drop (linkRows layout))).drop (nValuesOf layout))

/-- The index scalars at `r` on the stack. -/
def lkIdx (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (ch : LinkCh) (r : List E) : IdxAt :=
  idxAt layout chunks ch r (honestM1 layout chunks q r) (linkSplit layout r)

/-- **The row summand at no fresh coefficient**, table by table and pointer column by pointer
column. -/
theorem lk_rowSummand (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r x : List E) :
    rowSummand layout chunks q theta0 drawn r [] x =
      ∑ t ∈ range layout.tables.length, (prodE ((x.drop (linkRows layout)).map (1 + ·)) *
        cornerAt layout (x.take (linkRows layout)) t *
        lkBase layout (linkCh layout chunks theta0 drawn)
          (lkIdx layout chunks q (linkCh layout chunks theta0 drawn) r) [] (x.take (linkRows layout))
          (honestMessage layout q (x.take (linkRows layout)) (x.drop (linkRows layout))) t +
        ∑ k ∈ range (ptrsOf layout t).length, (eqKernel (x.drop (linkRows layout))).getD (qBase layout t + k) 0 *
          cornerAt layout (x.take (linkRows layout)) t * lkPtrAt layout (linkCh layout chunks theta0 drawn)
            (lkIdx layout chunks q (linkCh layout chunks theta0 drawn) r) (x.take (linkRows layout))
            (honestMessage layout q (x.take (linkRows layout)) (x.drop (linkRows layout)))
            ((lkFVals layout chunks q r x).getD 0 0)
            (prodE (((lkFVals layout chunks q r x).drop 1).take (chunks.d - 1)))
            ((lkFVals layout chunks q r x).drop (2 * chunks.d)) t k) := by
  rw [← lkVal_rowSideOf]
  have hc : ∀ (w : E) (nu : List E) (i : ℕ), (nu.map fun n ↦ (([] : List E).getD 0 0) * w * n).getD i 0 = 0 := by
    intro w nu i
    rw [getD_map_of_zero _ _ (by ring)]
    simp
  simp only [rowSummand, tailValuesF, lastOf, Functionals.summand, lkVal, lkZ, hc, zero_mul,
    List.drop_nil]
  simp only [sumE_eq_sum', List.map_const', List.sum_replicate, smul_zero, add_zero]
  rfl

/-! ## Lists of degree-one coordinates -/

/-- `f v` has a length independent of `v`, and each entry is of degree at most one in `v`. -/
def Lin (n : ℕ) (f : (Fin n → E) → List E) : Prop :=
  (∀ v w, (f v).length = (f w).length) ∧ ∀ j, PolyFn n 1 fun v ↦ (f v).getD j 0

namespace Lin

variable {n : ℕ}

theorem congr {f g : (Fin n → E) → List E} (h : Lin n f) (hfg : ∀ v, f v = g v) : Lin n g :=
  ⟨fun v w ↦ by rw [← hfg, ← hfg]; exact h.1 v w, fun j ↦ (h.2 j).congr fun v ↦ by rw [hfg]⟩

theorem ofFn : Lin n fun v ↦ List.ofFn v := by
  refine ⟨fun v w ↦ by simp, fun j ↦ ?_⟩
  by_cases hj : j < n
  · refine (PolyFn.var ⟨j, hj⟩).congr fun v ↦ ?_
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  · refine ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ ?_
    rw [List.getD_eq_default _ _ (by simpa using hj)]

theorem drop {f : (Fin n → E) → List E} (h : Lin n f) (k : ℕ) : Lin n fun v ↦ (f v).drop k := by
  refine ⟨fun v w ↦ by simp [h.1 v w], fun j ↦ (h.2 (k + j)).congr fun v ↦ ?_⟩
  simp [List.getD_eq_getElem?_getD]

theorem tail {f : (Fin n → E) → List E} (h : Lin n f) : Lin n fun v ↦ (f v).tail :=
  (h.drop 1).congr fun v ↦ by simp

theorem take {f : (Fin n → E) → List E} (h : Lin n f) (k : ℕ) : Lin n fun v ↦ (f v).take k := by
  refine ⟨fun v w ↦ by simp [h.1 v w], fun j ↦ ?_⟩
  by_cases hj : j < k
  · refine (h.2 j).congr fun v ↦ ?_
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
    simp [hj]
  · refine ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ ?_
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
    simp [hj]

theorem cons {g : (Fin n → E) → E} {f : (Fin n → E) → List E} (hg : PolyFn n 1 g) (h : Lin n f) :
    Lin n fun v ↦ g v :: f v := by
  refine ⟨fun v w ↦ by simp [h.1 v w], fun j ↦ ?_⟩
  rcases j with _ | j
  · exact hg.congr fun v ↦ by simp
  · exact (h.2 j).congr fun v ↦ by simp

theorem nil : Lin n fun _ ↦ [] :=
  ⟨fun _ _ ↦ rfl, fun j ↦ ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ by simp⟩

theorem getD {f : (Fin n → E) → List E} (h : Lin n f) (j : ℕ) : PolyFn n 1 fun v ↦ (f v).getD j 0 :=
  h.2 j

end Lin

/-- The `μ` slices: table `t`'s are its accesses' share of the draw. -/
theorem mu_fold_fst : ∀ (tables : List Table) (acc : List (List E)) (d : List E) (t : ℕ),
    ((tables.foldl (fun (acc : List (List E) × List E) t ↦
      (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) (acc, d)).1).getD
        (acc.length + t) [] =
      if t < tables.length then
        (d.drop ((tables.take t).map (·.links.memory.length)).sum).take
          (tables.getD t default).links.memory.length
      else []
  | [], acc, d, t => by simp
  | tb :: tables, acc, d, t => by
    rw [List.foldl_cons]
    rcases t with _ | t
    · have h := mu_fold_fst tables (acc ++ [d.take tb.links.memory.length]) (d.drop tb.links.memory.length)
      have hfold : ∀ (L : List Table) (a : List (List E)) (d' : List E) (i : ℕ), i < a.length →
          ((L.foldl (fun (acc : List (List E) × List E) t ↦
            (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) (a, d')).1).getD
              i [] = a.getD i [] := by
        intro L
        induction L with
        | nil => intro a d' i hi; rfl
        | cons x L ih =>
          intro a d' i hi
          rw [List.foldl_cons, ih _ _ _ (by simp; omega), List.getD_append _ _ _ _ hi]
      rw [hfold _ _ _ _ (by simp)]
      simp
    · have h := mu_fold_fst tables (acc ++ [d.take tb.links.memory.length]) (d.drop tb.links.memory.length) t
      simp only [List.length_append, List.length_singleton] at h
      rw [show acc.length + (t + 1) = acc.length + 1 + t by omega, h]
      simp [List.drop_drop]

/-! ## The challenges of a draw -/

section Ch

variable {layout : Layout} {chunks : Chunks} {n : ℕ} {th : (Fin n → E) → E} {D : (Fin n → E) → List E}

/-- `linkCh`'s slices of a draw are lists of degree-one coordinates. -/
structure LinCh (n : ℕ) (ch : (Fin n → E) → LinkCh) : Prop where
  theta : Lin n fun v ↦ (ch v).theta
  gammaState : Lin n fun v ↦ (ch v).gammaState
  gammaMem : Lin n fun v ↦ (ch v).gammaMem
  mu : ∀ t, Lin n fun v ↦ (ch v).mu.getD t []
  alpha : Lin n fun v ↦ (ch v).alpha
  etaMem : PolyFn n 1 fun v ↦ (ch v).etaMem
  etaBc : PolyFn n 1 fun v ↦ (ch v).etaBc
  eps : Lin n fun v ↦ (ch v).eps
  tau : Lin n fun v ↦ (ch v).tau
  zeta : Lin n fun v ↦ (ch v).zeta
  nu : Lin n fun v ↦ (ch v).nu

theorem linCh (hth : PolyFn n 1 th) (hD : Lin n D) :
    LinCh n fun v ↦ linkCh layout chunks (th v) (D v) := by
  set nA := (layout.tables.map (·.links.memory.length)).sum
  set nP := ((layout.tables.map (·.links.pointers)).map List.length).sum
  set nR := layout.tableLogHeights.foldl max 0
  have h3 : Lin n fun v ↦ (((D v).drop (nTables - 1)).drop 2).drop 3 :=
    ((hD.drop (nTables - 1)).drop 2).drop 3
  have hR : Lin n fun v ↦ (((((D v).drop (nTables - 1)).drop 2).drop 3).drop nA).drop bytecodeSlotBits :=
    (h3.drop nA).drop bytecodeSlotBits
  have hS : Lin n fun v ↦ ((((((D v).drop (nTables - 1)).drop 2).drop 3).drop nA).drop bytecodeSlotBits).drop 2 :=
    hR.drop 2
  refine ⟨?_, ?_, ?_, fun t ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Lin.cons hth (hD.take (nTables - 1))).congr fun v ↦ by simp only [linkCh]
  · exact ((hD.drop (nTables - 1)).take 2).congr fun v ↦ by simp only [linkCh]
  · have hg := ((hD.drop (nTables - 1)).drop 2).take 3
    refine (Lin.cons (hg.getD 0) (Lin.cons (hg.getD 1)
      (Lin.cons ((hg.getD 1).mul_le (PolyFn.const eY) (by omega)) (Lin.cons (hg.getD 2) Lin.nil)))).congr
      fun v ↦ ?_
    simp only [linkCh]
  · have hm := fun v ↦ mu_fold_fst layout.tables [] ((((D v).drop (nTables - 1)).drop 2).drop 3) t
    simp only [List.length_nil, Nat.zero_add] at hm
    by_cases ht : t < layout.tables.length
    · refine ((h3.drop (((layout.tables.take t).map (·.links.memory.length)).sum)).take
        (layout.tables.getD t default).links.memory.length).congr fun v ↦ ?_
      simp only [linkCh]
      rw [hm v]
      simp [ht]
    · refine Lin.nil.congr fun v ↦ ?_
      simp only [linkCh]
      rw [hm v]
      simp [ht]
  · exact ((h3.drop nA).take bytecodeSlotBits).congr fun v ↦ by simp only [linkCh, mu_fold_snd, nA]
  · exact (hR.getD 0).congr fun v ↦ by simp only [linkCh, mu_fold_snd, nA]
  · exact (hR.getD 1).congr fun v ↦ by simp only [linkCh, mu_fold_snd, nA]
  · exact (hS.take nP).congr fun v ↦ by simp only [linkCh, mu_fold_snd, nA, nP]
  · exact ((hS.drop nP).take nR).congr fun v ↦ by simp only [linkCh, mu_fold_snd, nA, nP, nR]
  · exact (((hS.drop nP).drop nR).take chunks.width).congr fun v ↦ by
      simp only [linkCh, mu_fold_snd, nA, nP, nR]
  · exact ((((hS.drop nP).drop nR).drop chunks.width).take chunks.d).congr fun v ↦ by
      simp only [linkCh, mu_fold_snd, nA, nP, nR]

end Ch

/-- The draw's own challenges, `θ_0` and the rest. -/
theorem linCh_draw (layout : Layout) (chunks : Chunks) {n : ℕ} :
    LinCh (n + 1) fun v ↦ linkCh layout chunks ((List.ofFn v).headD 0) (List.ofFn v).tail := by
  refine linCh ?_ Lin.ofFn.tail
  exact (PolyFn.var 0).congr fun v ↦ by simp [List.ofFn_succ]

/-! ## Equality weights of such lists -/

theorem Lin.length_eq {n : ℕ} {f : (Fin n → E) → List E} (h : Lin n f) (v : Fin n → E) :
    (f v).length = (f 0).length := h.1 v 0

/-- `eq(α, s)`, entry `s` of `eq_kernel(α)`, is of degree at most `|α|`. -/
theorem polyFn_eqKernel_getD {n : ℕ} {f : (Fin n → E) → List E} (h : Lin n f) (s : ℕ) :
    PolyFn n (f 0).length fun v ↦ (eqKernel (f v)).getD s 0 := by
  by_cases hs : s < 2 ^ (f 0).length
  · refine (polyFn_eqAt (f 0).length f h.length_eq (fun k _ ↦ h.getD k) s).congr fun v ↦ ?_
    rw [eqKernel_getD, h.length_eq v]
    simp [hs]
  · refine ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ ?_
    rw [eqKernel_getD, h.length_eq v]
    simp [hs]

/-- `eq(ζ, r)` is of degree at most `|ζ|`. -/
theorem polyFn_eqEval {n : ℕ} {f : (Fin n → E) → List E} (h : Lin n f) (r : List E)
    (hr : (f 0).length = r.length) : PolyFn n (f 0).length fun v ↦ eqEval (f v) r := by
  refine (PolyFn.finsetSum (range (2 ^ (f 0).length)) fun j _ ↦
    ((PolyFn.const (eqAt r j)).mul_le (polyFn_eqAt (f 0).length f h.length_eq
      (fun k _ ↦ h.getD k) j) (by omega))).congr fun v ↦ ?_
  rw [eqEval_eq_sum _ _ (by rw [h.length_eq v, hr]), h.length_eq v]

/-- `shift_eq(ζ, r)` is of degree at most `|ζ|`. -/
theorem polyFn_linkShiftEq {n : ℕ} {f : (Fin n → E) → List E} (h : Lin n f) (r : List E)
    (hr : (f 0).length = r.length) : PolyFn n (f 0).length fun v ↦ linkShiftEq (f v) r := by
  have key : ∀ j, PolyFn n (f 0).length fun v ↦
      if j + 1 < 2 ^ (f 0).length then eqAt r j * eqAt (f v) (j + 1) else 0 := by
    intro j
    split_ifs
    · exact (PolyFn.const (eqAt r j)).mul_le (polyFn_eqAt (f 0).length f h.length_eq
        (fun k _ ↦ h.getD k) (j + 1)) (by omega)
    · exact (PolyFn.const 0).mono (Nat.zero_le _)
  refine (PolyFn.finsetSum (range (2 ^ (f 0).length)) fun j _ ↦ key j).congr fun v ↦ ?_
  rw [linkShiftEq, linkShiftEq_eq_shiftSum _ _ (by rw [h.length_eq v, hr]), shiftSum, h.length_eq v]

end

end LeanVM.Protocol.Relation
