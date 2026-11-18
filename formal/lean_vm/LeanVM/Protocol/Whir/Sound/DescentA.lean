/-
  LeanVM.Protocol.Whir.Sound.DescentA

  The descent over arrays: one-error decoding and the descent within a level, on arrays of values.
-/

module

public import LeanVM.Protocol.Whir.Sound.NewtonV

/-!
# The descent over arrays

A tuple of `2^m` lanes on `n` columns is held as an array of columns, each the array of its lanes'
values (`toAV`); the level's word and its folds are read through `getD` (`Rep`). On these:
the fold of a column (`foldCA`), the agreement set's columns (`agreeA`), one-error decoding of a
tuple (`newtonDecA`), each equal to the function's (`foldsCA_getD`, `agreeA_eq`,
`newtonDecA_eq`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Polynomial
open Newton

@[expose] public section

/-- Values held column by column. -/
abbrev AV := Array (Array E)

/-- A tuple's values, column by column, lane `k` the tuple's `(bitsEquiv m).symm k`. -/
def toAV (n m : ℕ) (f : (Fin m → Bool) → Fin n → E) : AV :=
  Array.ofFn fun x : Fin n ↦ Array.ofFn fun k : Fin (2 ^ m) ↦ f ((bitsEquiv m).symm k) x

/-- The array `A` holds `Q`: lane `u` of column `x` is `A[x][⟨u⟩]`. -/
def Rep {n m : ℕ} (A : AV) (Q : (Fin m → Bool) → Fin n → E) : Prop :=
  ∀ u x, Q u x = (A.getD x #[]).getD (bitsToNat u) 0

theorem bitsEquiv_symm_bitsToNat {m : ℕ} (u : Fin m → Bool) (h : bitsToNat u < 2 ^ m) :
    (bitsEquiv m).symm ⟨bitsToNat u, h⟩ = u := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (bitsEquiv_val u).symm

theorem rep_toAV {n m : ℕ} (f : (Fin m → Bool) → Fin n → E) : Rep (toAV n m f) f := by
  intro u x
  simp only [toAV, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, Fin.is_lt, ↓reduceDIte,
    Option.getD_some, bitsToNat_lt u]
  rw [bitsEquiv_symm_bitsToNat]

/-! ## Folds -/

/-- One fold of a column's lanes at the domain point `y`. -/
def foldCA (y : E) (r : FoldRound) (o : Array E) : Array E :=
  let b := r.beta * y
  let c := r.alpha + b
  Array.ofFn fun k : Fin ((o.size + 1) / 2) ↦
    let g := o.getD (2 * k) 0
    let h := o.getD (2 * k + 1) 0
    let t := c * g
    h + t

/-- The folds of a column. -/
def foldsCA (y : E) (rounds : List FoldRound) (o : Array E) : Array E :=
  rounds.foldl (fun o r ↦ foldCA y r o) o

theorem foldCA_getD (y : E) (r : FoldRound) (o : Array E) (k : ℕ) :
    (foldCA y r o).getD k 0 = foldC y r (o.getD · 0) k := by
  unfold foldCA foldC
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split_ifs with hk
  · rfl
  · simp only [Option.getD_none]
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
    simp

theorem foldsCA_getD (y : E) : ∀ (rounds : List FoldRound) (o : Array E) (k : ℕ),
    (foldsCA y rounds o).getD k 0 = foldsC y rounds (o.getD · 0) k
  | [], o, k => rfl
  | r :: rounds, o, k => by
    unfold foldsCA foldsC
    rw [List.foldl_cons, List.foldl_cons]
    have := foldsCA_getD y rounds (foldCA y r o) k
    unfold foldsCA foldsC at this
    rw [this, show (fun x ↦ (foldCA y r o).getD x 0) = foldC y r (fun x ↦ o.getD x 0) from
      funext (foldCA_getD y r o)]

/-- The folds of every column. -/
def foldsAA {n : ℕ} (dom : Fin n ↪ E) (rounds : List FoldRound) (O : AV) : AV :=
  Array.ofFn fun x : Fin n ↦ foldsCA (dom x) rounds (O.getD x #[])

theorem rep_foldsAA {n m : ℕ} (dom : Fin n ↪ E) (rounds : List FoldRound) {O : AV}
    {Ofun : ℕ → Fin n → E} (hO : ∀ j x, Ofun j x = (O.getD x #[]).getD j 0) :
    Rep (m := m) (foldsAA dom rounds O) (rowsOf m (foldsA dom rounds Ofun)) := by
  intro u x
  simp only [rowsOf, foldsA, foldsAA, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, Fin.is_lt,
    ↓reduceDIte, Option.getD_some, Fin.eta]
  rw [← Array.getD_eq_getD_getElem?, foldsCA_getD]
  congr 1
  funext j
  rw [hO]
  simp [Array.getD_eq_getD_getElem?]

theorem bitsToNat_symm {m : ℕ} (k : Fin (2 ^ m)) : bitsToNat ((bitsEquiv m).symm k) = k := by
  rw [← bitsEquiv_val, Equiv.apply_symm_apply]

/-! ## The agreement set -/

/-- The columns where the tuple `VA` of `2^m` lanes agrees with the fold of the word `QA`. -/
def agreeA {n : ℕ} (dom : Fin n ↪ E) (m : ℕ) (r : FoldRound) (VA QA : AV) : List (Fin n) :=
  (List.finRange n).filter fun (x : Fin n) ↦ (List.finRange (2 ^ m)).all fun k ↦
    (VA.getD x #[]).getD k 0 == (foldCA (dom x) r (QA.getD x #[])).getD k 0

theorem foldQ_rep {n m : ℕ} (dom : Fin n ↪ E) (r : FoldRound) {QA : AV}
    {Q : (Fin (m + 1) → Bool) → Fin n → E} (hQ : Rep QA Q) (u : Fin m → Bool) (x : Fin n) :
    foldQ dom r.alpha r.beta Q u x = (foldCA (dom x) r (QA.getD x #[])).getD (bitsToNat u) 0 := by
  rw [foldCA_getD, foldQ, foldC, hQ, hQ, bitsToNat_cons, bitsToNat_cons]
  simp only [Bool.toNat_true, Bool.toNat_false]
  congr 2 <;> ring_nf

theorem agreeA_eq {n m : ℕ} (dom : Fin n ↪ E) (r : FoldRound) {VA QA : AV}
    {V : (Fin m → Bool) → Fin n → E} {Q : (Fin (m + 1) → Bool) → Fin n → E} (hV : Rep VA V)
    (hQ : Rep QA Q) : agreeA dom m r VA QA = colsOf (agreeV V (foldQ dom r.alpha r.beta Q)) := by
  unfold agreeA colsOf
  refine List.filter_congr fun x _ ↦ ?_
  simp only [agreeV, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
  constructor
  · intro h u
    have := h ⟨bitsToNat u, bitsToNat_lt u⟩ (List.mem_finRange _)
    rw [beq_iff_eq] at this
    rw [hV, foldQ_rep dom r hQ]
    exact this
  · intro h k _
    have := h ((bitsEquiv m).symm k)
    rw [hV, foldQ_rep dom r hQ, bitsToNat_symm] at this
    exact beq_iff_eq.mpr this

/-! ## One-error decoding over arrays -/

theorem getD_eq_get' {α : Type} (o : Option α) (h : o.isSome) (d : α) : o.getD d = o.get h := by
  cases o with
  | none => simp at h
  | some a => rfl

/-- Lane `k`'s points on the window, from the array. -/
def winPtsA {n : ℕ} (dom : Fin n ↪ E) (d : ℕ) (QA : AV) (cols : List (Fin n)) (k : ℕ) :
    List (E × E) :=
  (cols.take (d + 3)).map fun x ↦ (dom x, (QA.getD x #[]).getD k 0)

/-- **One-error decoding over arrays**, of a word `QA` of `2^(m+1)` lanes on the columns `cols`
of the agreement set. -/
def newtonDecA {n : ℕ} (dom : Fin n ↪ E) (d m : ℕ) (QA : AV) (cols : List (Fin n)) :
    Option AV :=
  if d + 3 ≤ cols.length then
    let fs := Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦ decode1 d (winPtsA dom d QA cols k)
    if fs.all (·.isSome) then
      let V := Array.ofFn fun x : Fin n ↦ Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦
        nEval ((fs.getD k none).getD ([], [])).1 ((fs.getD k none).getD ([], [])).2 (dom x)
      if (cols.filter fun (x : Fin n) ↦ (List.finRange (2 ^ (m + 1))).any fun k ↦
          (V.getD x #[]).getD k 0 != (QA.getD x #[]).getD k 0).length ≤ 1 then some V else none
    else none
  else none

theorem winPtsA_eq {n m : ℕ} (dom : Fin n ↪ E) (d : ℕ) {QA : AV}
    {Q : (Fin (m + 1) → Bool) → Fin n → E} (hQ : Rep QA Q) (S : Finset (Fin n))
    (v : Fin (m + 1) → Bool) : winPtsA dom d QA (colsOf S) (bitsToNat v) = winPts dom d Q S v := by
  unfold winPtsA winPts window
  refine List.map_congr_left fun x _ ↦ ?_
  rw [hQ]

theorem length_filter_colsOf {n : ℕ} (S : Finset (Fin n)) (p : Fin n → Prop) [DecidablePred p] :
    ((colsOf S).filter fun x ↦ decide (p x)).length = (S.filter p).card := by
  rw [← length_colsOf]
  unfold colsOf
  rw [List.filter_filter]
  congr 1
  refine List.filter_congr fun x _ ↦ ?_
  simp [and_comm]

theorem newtonDecA_eq {n m : ℕ} (dom : Fin n ↪ E) (d : ℕ) {QA : AV}
    {Q : (Fin (m + 1) → Bool) → Fin n → E} (hQ : Rep QA Q) (S : Finset (Fin n)) :
    newtonDecA dom d m QA (colsOf S) = (newtonDecV dom d Q S).map (toAV n (m + 1)) := by
  have hfs : ∀ k : Fin (2 ^ (m + 1)), decode1 d (winPtsA dom d QA (colsOf S) k) =
      decode1 d (winPts dom d Q S ((bitsEquiv (m + 1)).symm k)) := fun k ↦ by
    rw [← winPtsA_eq dom d hQ S, bitsToNat_symm]
  unfold newtonDecA newtonDecV
  rw [length_colsOf]
  by_cases hS : d + 3 ≤ S.card
  · rw [ite_eq_left hS, ite_eq_left hS]
    have hall : (Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦
        decode1 d (winPtsA dom d QA (colsOf S) k)).all (·.isSome) = true ↔
        ∀ v, (decode1 d (winPts dom d Q S v)).isSome := by
      rw [Array.all_eq_true]
      simp only [Array.size_ofFn, Array.getElem_ofFn]
      constructor
      · intro h v
        have := h (bitsToNat v) (bitsToNat_lt v)
        rwa [show bitsToNat v = ((⟨bitsToNat v, bitsToNat_lt v⟩ : Fin (2 ^ (m + 1))) : ℕ) from rfl,
          hfs, bitsEquiv_symm_bitsToNat] at this
      · intro h k hk
        rw [show k = ((⟨k, hk⟩ : Fin (2 ^ (m + 1))) : ℕ) from rfl, hfs]
        exact h _
    by_cases h : ∀ v, (decode1 d (winPts dom d Q S v)).isSome
    · rw [dite_eq_left h]
      simp only [hall.mpr h, ↓reduceIte]
      have hV : (Array.ofFn fun x : Fin n ↦ Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦
          nEval (((Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦
            decode1 d (winPtsA dom d QA (colsOf S) k)).getD k none).getD ([], [])).1
          (((Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦
            decode1 d (winPtsA dom d QA (colsOf S) k)).getD k none).getD ([], [])).2 (dom x)) =
          toAV n (m + 1) fun v x ↦ nEval ((decode1 d (winPts dom d Q S v)).get (h v)).1
            ((decode1 d (winPts dom d Q S v)).get (h v)).2 (dom x) := by
        unfold toAV
        congr 1
        funext x
        congr 1
        funext k
        have hk : ((Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦
            decode1 d (winPtsA dom d QA (colsOf S) k)).getD k none) =
            decode1 d (winPts dom d Q S ((bitsEquiv (m + 1)).symm k)) := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left k.isLt, Option.getD_some,
            hfs]
        rw [hk, getD_eq_get' _ (h ((bitsEquiv (m + 1)).symm k))]
      rw [hV]
      have hrepV := rep_toAV (fun v x ↦ nEval ((decode1 d (winPts dom d Q S v)).get (h v)).1
        ((decode1 d (winPts dom d Q S v)).get (h v)).2 (dom x))
      have hcnt : ((colsOf S).filter fun (x : Fin n) ↦ (List.finRange (2 ^ (m + 1))).any fun k ↦
          ((toAV n (m + 1) fun v x ↦ nEval ((decode1 d (winPts dom d Q S v)).get (h v)).1
            ((decode1 d (winPts dom d Q S v)).get (h v)).2 (dom x)).getD x #[]).getD k 0 !=
            (QA.getD x #[]).getD k 0).length =
          (S.filter fun x ↦ ∃ v, nEval ((decode1 d (winPts dom d Q S v)).get (h v)).1
            ((decode1 d (winPts dom d Q S v)).get (h v)).2 (dom x) ≠ Q v x).card := by
        refine (congrArg List.length (List.filter_congr fun x _ ↦ ?_)).trans
          (length_filter_colsOf S _)
        rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
        constructor
        · rintro ⟨k, -, hk⟩
          refine ⟨(bitsEquiv (m + 1)).symm k, fun he ↦ ?_⟩
          rw [bne_iff_ne, ne_eq] at hk
          apply hk
          have h1 := hrepV ((bitsEquiv (m + 1)).symm k) x
          have h2 := hQ ((bitsEquiv (m + 1)).symm k) x
          beta_reduce at h1
          rw [bitsToNat_symm] at h1 h2
          rw [← h1, ← h2]
          exact he
        · rintro ⟨v, hv⟩
          refine ⟨⟨bitsToNat v, bitsToNat_lt v⟩, List.mem_finRange _, ?_⟩
          rw [bne_iff_ne]
          intro he
          apply hv
          have h1 := hrepV v x
          beta_reduce at h1
          rw [h1, hQ v x]
          exact he
      rw [hcnt]
      split_ifs <;> rfl
    · rw [dite_eq_right h]
      simp only [show ¬ ((Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦
        decode1 d (winPtsA dom d QA (colsOf S) k)).all (·.isSome) = true) from fun h' ↦
          h (hall.mp h'), Bool.false_eq_true, ↓reduceIte, Option.map_none]
  · rw [ite_eq_right hS, ite_eq_right hS]
    rfl

/-! ## Within a level -/

/-- **The descent within a level, over arrays.** -/
def descendRoundsA {n : ℕ} (dom : Fin n ↪ E) (d : ℕ) (thr : ℕ → ℕ) (OA : AV)
    (rs : List FoldRound) (m : ℕ) (VA : AV) : Option (ℕ × AV) :=
  match _h : rs.getLast? with
  | none => some (m, VA)
  | some r =>
    let QA := foldsAA dom rs.dropLast OA
    let cols := agreeA dom m r VA QA
    if thr (rs.dropLast.length + 1) ≤ cols.length then
      (newtonDecA dom d m QA cols).bind fun TA ↦ descendRoundsA dom d thr OA rs.dropLast (m + 1) TA
    else none
termination_by rs.length
decreasing_by
  have : rs ≠ [] := fun h0 ↦ by simp [h0] at _h
  simp only [List.length_dropLast]
  have := List.length_pos_of_ne_nil this
  omega

theorem descendRoundsA_nil {n : ℕ} (dom : Fin n ↪ E) (d : ℕ) (thr : ℕ → ℕ) (OA : AV) (m : ℕ)
    (VA : AV) : descendRoundsA dom d thr OA [] m VA = some (m, VA) := by
  rw [descendRoundsA]; rfl

theorem descendRoundsA_concat {n : ℕ} (dom : Fin n ↪ E) (d : ℕ) (thr : ℕ → ℕ) (OA : AV)
    (rs : List FoldRound) (r : FoldRound) (m : ℕ) (VA : AV) :
    descendRoundsA dom d thr OA (rs ++ [r]) m VA =
      if thr (rs.length + 1) ≤ (agreeA dom m r VA (foldsAA dom rs OA)).length then
        (newtonDecA dom d m (foldsAA dom rs OA) (agreeA dom m r VA (foldsAA dom rs OA))).bind
          fun TA ↦ descendRoundsA dom d thr OA rs (m + 1) TA
      else none := by
  rw [descendRoundsA]
  split
  · rename_i h; simp at h
  · rename_i r' h
    simp only [List.getLast?_concat, Option.some.injEq] at h
    subst h
    simp only [List.dropLast_concat]

/-- A tuple's values as arrays, with its lane count. -/
def toAVS {n : ℕ} (T : Σ k, (Fin k → Bool) → Fin n → E) : ℕ × AV := (T.1, toAV n T.1 T.2)

/-- **The descent within a level over arrays is the descent over values**, with one-error
decoding. -/
theorem descendRoundsA_eq {n : ℕ} (dom : Fin n ↪ E) (d : ℕ) (thr : ℕ → ℕ) {OA : AV}
    {O : ℕ → Fin n → E} (hO : ∀ j x, O j x = (OA.getD x #[]).getD j 0) :
    ∀ (rs : List FoldRound) (m : ℕ) (V : (Fin m → Bool) → Fin n → E),
      descendRoundsA dom d thr OA rs m (toAV n m V) =
        (descendRoundsV newtonValsDecoder dom d thr O rs m V).map toAVS := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil =>
    intro m V
    rw [descendRoundsA_nil, descendRoundsV_nil]
    rfl
  | append_singleton rs r ih =>
    intro m V
    have hQ := rep_foldsAA (m := m + 1) dom rs hO
    rw [descendRoundsA_concat, descendRoundsV_concat, agreeA_eq dom r (rep_toAV V) hQ,
      length_colsOf]
    split_ifs
    · rw [newtonDecA_eq dom d hQ]
      show (Option.map _ (newtonDecV dom d _ _)).bind _ = Option.map toAVS ((newtonDecV dom d _ _).bind _)
      rcases newtonDecV dom d (rowsOf (m + 1) (foldsA dom rs O))
        (agreeV V (foldQ dom r.alpha r.beta (rowsOf (m + 1) (foldsA dom rs O)))) with _ | T
      · rfl
      · exact ih (m + 1) T
    · rfl

end
end LeanVM.Protocol.Whir.Sound
