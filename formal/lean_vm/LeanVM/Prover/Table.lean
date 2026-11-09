/-
  LeanVM.Prover.Table

  The executable table phase (`Statement/Prover/Table.lean`, `tableFast`) makes the moves of the
  specification's (`hTable`): its state's invariant along the rounds, its round messages the
  specification's, its final evaluations the specification's.
-/

module

public import LeanVM.Prover.TableSpec
public import LeanVM.Prover.Sumcheck

/-!
# The table phase, executable, against its specification

* `TInv pre st`: after the challenges `pre`, the state's weights are the products of the tables'
  weight factors at `pre` (`preWeight`), and each table's folded columns are the extensions of its
  columns with the coordinates above the free ones bound to `pre` (`foldHigh`).
* `tableRound_eq`: the round's message evaluates as the specification's running claim
  (`claimOf_snoc_split`, the active tables' rows as lines between the halves,
  `multilinearEval_line`).
* `corr_tableFast`: **the executable table phase makes the specification's moves**.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete Finset
open LeanVM.Protocol.EndToEnd (boolPoint)
open LeanVM.Protocol.EndToEnd.Complete (coeffsOf hSumcheck)
open LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

/-! ## A bounded stateful sumcheck -/

/-- **The stateful sumcheck makes the specification's moves**, for at most `N` rounds: as
`corr_sumcheckBy`, the invariant's round and fold facts needed only before the `N`-th
challenge; the challenges are as many as the rounds. -/
theorem corr_sumcheckBy_le {σ : Type} (count : ℕ) (hc : 1 ≤ count) (hc' : count ≤ 2 ^ 128)
    (claimOf : List E → E) (round : σ → List E) (fold : σ → E → σ) (Inv : List E → σ → Prop)
    (N : ℕ)
    (hround : ∀ pre st, Inv pre st → pre.length < N →
      (round st).length = count ∧ ∀ x, polyEval (round st) x = claimOf (pre ++ [x]))
    (hfold : ∀ pre st c, Inv pre st → pre.length < N → Inv (pre ++ [c]) (fold st c)) :
    ∀ (modes : List (Option E)) (pre : List E) (st : σ), Inv pre st →
      pre.length + modes.length ≤ N →
      Corr (fun a b ↦ a.1 = b.1 ∧ a.1.length = modes.length ∧ Inv (pre ++ a.1) a.2 ∧
          b.2 = claimOf (pre ++ b.1))
        (sumcheckBy round fold modes st) (hSumcheck count claimOf modes pre)
  | [], pre, st, h, _ => by
    show Corr _ (.ret ([], st)) (.ret ([], claimOf pre))
    exact ⟨rfl, rfl, by simpa using h, by simp⟩
  | mode :: modes, pre, st, h, hN => by
    have hlt : pre.length < N := by simp only [List.length_cons] at hN; omega
    obtain ⟨hlen, hev⟩ := hround pre st h hlt
    have hco : coeffsOf (count - 1) (fun x ↦ claimOf (pre ++ [x])) = round st :=
      coeffsOf_eq (by omega) (by omega) hev
    simp only [sumcheckBy, hSumcheck, hco, ← wire_eq, Script.bind_assoc', roundGrind_eq hlen]
    refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun c ↦ ?_
    refine Corr.bind (fun a b hab ↦ ?_) _ _
      (corr_sumcheckBy_le count hc hc' claimOf round fold Inv N hround hfold modes (pre ++ [c])
        (fold st c) (hfold pre st c h hlt)
        (by simp only [List.length_append, List.length_cons, List.length_nil] at hN ⊢
            omega))
    obtain ⟨h1, h2, h3, h4⟩ := hab
    simp only [Corr, List.append_assoc, List.singleton_append] at h3 h4 ⊢
    exact ⟨by rw [h1], by simp [h2], h3, h4⟩

/-! ## The state's invariant -/

variable (prog : LeanIsaProgram) (s : Sizes) (q : LeanVM.Protocol.Column (leanIsaμ prog s))

/-- **The state's invariant** after the challenges `pre`. -/
def TInv (bus : BusResult) (pre : List E) (st : TableState) : Prop :=
  pre.length ≤ nRounds s ∧ st.free = nRounds s - pre.length ∧
  ∀ t : Fin 6, st.weights.getD t 0 = preWeight s bus t pre ∧
    (st.cols.getD t #[]).size = width (opIdx t) ∧
    ∀ i : Fin (width (opIdx t)),
      ((st.cols.getD t #[]).getD i #[]).size = 2 ^ min (s.τ t) st.free ∧
      ∀ p : List E, p.length = min (s.τ t) st.free →
        multilinearEval ((st.cols.getD t #[]).getD i #[]).toList p =
          multilinearEval (tableColList prog s q t i)
            (p ++ (pre.drop (nRounds s - s.τ t)).reverse)

/-- The point's coordinates a table of log-height `τ` reads, `X` binding coordinate `m`. -/
theorem take_point (pre : List E) (m τ n x : ℕ) (X : E) (hm : m < τ) (hτ : τ ≤ n)
    (hk : pre.length = n - m - 1) (hn : m < n) :
    (boolPoint m x ++ X :: pre.reverse).take τ =
      boolPoint m x ++ [X] ++ (pre.drop (n - τ)).reverse := by
  have hb := LeanVM.Protocol.Whir.Complete.length_boolPoint m x
  rw [List.take_append, List.take_of_length_le (by omega), hb,
    show τ - m = (τ - m - 1) + 1 by omega, List.take_succ_cons, List.take_reverse,
    show pre.length - (τ - m - 1) = n - τ by omega, List.append_assoc, List.singleton_append]

/-- An array read in range. -/
theorem getElem_eq_getD {α : Type} (a : Array α) (i : ℕ) (h : i < a.size) (d : α) :
    a[i] = a.getD i d := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- An array's entries past its size are the default. -/
theorem getD_of_size_le {α : Type} (a : Array α) (i : ℕ) (d : α) (h : a.size ≤ i) :
    a.getD i d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

/-- An honest evaluation of table `t` past its width is `0`. -/
theorem getD_evalsAt_of_le (t : Fin 6) (r : List E) (i : ℕ) (hi : width (opIdx t) ≤ i) :
    (evalsAt prog s q t r).getD i 0 = 0 :=
  List.getD_eq_default _ _ (by simp [evalsAt, hi])

/-- An honest evaluation of table `t` within its width. -/
theorem getD_evalsAt (t : Fin 6) (r : List E) (i : ℕ) (hi : i < width (opIdx t)) :
    (evalsAt prog s q t r).getD i 0 = multilinearEval (tableColList prog s q t ⟨i, hi⟩)
      (r.take (s.τ t)) := by
  rw [List.getD_eq_getElem _ _ (by simp [evalsAt, hi])]
  simp [evalsAt]

/-! ## The round -/

variable {prog s q}

/-- **The round's message** evaluates as the specification's running claim. -/
theorem tableRound_eq {bus : BusResult} (hb : BusGood prog s q bus) (cp fp : List E)
    (hcp : 2 ≤ cp.length) (logs : List ℕ) (hlogs : logs = tableLogs s)
    (terms : Array (List (List ℕ × E)))
    (hterms : ∀ t : Fin 6, terms.getD t [] = rowTerms cp fp bus.forms t) (sigma : Array E)
    (hsigma : ∀ t : Fin 6, s.τ t < nRounds s → sigma.getD t 0 = waitSum prog s q cp fp bus t)
    (pre : List E) (st : TableState) (hI : TInv prog s q bus pre st)
    (hk : pre.length < nRounds s) (X : E) :
    polyEval (tableRound bus.point logs terms sigma st) X =
      claimOf prog s q cp fp bus (pre ++ [X]) := by
  rw [polyEval_tableRound, claimOf_snoc_split prog s q hb cp fp pre hk X, Finset.sum_range]
  refine sum_congr rfl fun t _ ↦ ?_
  obtain ⟨_, hfree, hI⟩ := hI
  obtain ⟨hw, hsize, hcol⟩ := hI t
  have hm : st.free - 1 = nRounds s - pre.length - 1 := by omega
  have hl : logs.getD t 0 = s.τ t := by rw [hlogs, getD_tableLogs]
  rw [hm, hl, hw, hterms t]
  by_cases hτ : s.τ t ≤ nRounds s - pre.length - 1
  · rw [ite_eq_left hτ, evalCubic_tableCubic_wait _ _ _ _ _ _ _ _ hτ, hsigma t (by omega)]
  · rw [ite_eq_right hτ, evalCubic_tableCubic_active _ _ _ _ _ _ _ _ (by omega), evalQuad_activeQuad]
    refine congrArg (_ * ·) (congrArg (_ * ·) (sum_congr rfl fun x hx ↦ ?_))
    have hx' := mem_range.mp hx
    generalize hmd : nRounds s - pre.length - 1 = m at hτ hx' ⊢
    have hmτ : m < s.τ t := by omega
    have hτn := τ_le_nRounds s t
    have hlen : (bus.point.take m).length = m := by
      have := hb.point_length t
      simp only [List.length_take]
      omega
    rw [eqTable_getD (bus.point.take m) x (by rw [hlen]; exact hx'), hlen, eqEval_comm,
      evalQuad_formQuad _ _ (rowTerms_deg cp fp bus.forms t hb.forms_deg), rowPart,
      ← evaluate_rowTerms cp fp hcp bus t]
    refine congrArg (_ * ·) (congrArg (Form.evaluate _) (funext fun i ↦ ?_))
    by_cases hi : i < width (opIdx t)
    · rw [getD_evalsAt prog s q t _ i hi,
        take_point pre m (s.τ t) (nRounds s) x X hmτ hτn (by omega) (by omega),
        ← (hcol ⟨i, hi⟩).2 (boolPoint m x ++ [X])
          (by simp only [List.length_append, LeanVM.Protocol.Whir.Complete.length_boolPoint,
            List.length_singleton]; omega)]
      have hsz : ((st.cols.getD t #[]).getD i #[]).size = 2 ^ (m + 1) := by
        rw [(hcol ⟨i, hi⟩).1]; congr 1; omega
      rw [multilinearEval_line _ m hsz x hx' X]
      simp only [rowLine]
      ring
    · rw [getD_evalsAt_of_le prog s q t _ i (by omega)]
      simp only [rowLine, getD_of_size_le (st.cols.getD t #[]) i #[] (by omega)]
      simp

/-! ## The fold -/

theorem getD_map_lt {α β : Type} (f : α → β) (a : Array α) (i : ℕ) (d : α) (d' : β)
    (h : i < a.size) : (a.map f).getD i d' = f (a.getD i d) := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- **The fold keeps the invariant.** -/
theorem tableFold_inv (bus : BusResult) (logs : List ℕ) (hlogs : logs = tableLogs s)
    (pre : List E) (st : TableState) (hI : TInv prog s q bus pre st)
    (hk : pre.length < nRounds s) (c : E) :
    TInv prog s q bus (pre ++ [c]) (tableFold bus.point logs st c) := by
  obtain ⟨_, hfree, hI⟩ := hI
  refine ⟨by simp only [List.length_append, List.length_singleton]; omega,
    by simp only [tableFold, List.length_append, List.length_singleton]; omega, fun t ↦ ?_⟩
  obtain ⟨hw, hsize, hcol⟩ := hI t
  have hl : logs.getD t 0 = s.τ t := by rw [hlogs, getD_tableLogs]
  have hcols : (tableFold bus.point logs st c).cols.getD t #[] =
      if st.free - 1 < s.τ t then (st.cols.getD t #[]).map (foldHigh c)
      else st.cols.getD t #[] := by
    simp only [tableFold]
    rw [ofFn_getD _ t t.isLt _]
    simp only [hl]
  have hws : (tableFold bus.point logs st c).weights.getD t 0 =
      st.weights.getD t 0 * tableFactor bus.point (s.τ t) (st.free - 1) c := by
    simp only [tableFold]
    rw [ofFn_getD _ t t.isLt _]
    simp only [hl]
  have hfree' : (tableFold bus.point logs st c).free = st.free - 1 := rfl
  have hτn := τ_le_nRounds s t
  refine ⟨?_, ?_, fun i ↦ ?_⟩
  · rw [hws, hw, preWeight, preWeight, List.length_append, List.length_singleton,
      prod_range_succ', List.reverse_append, List.reverse_singleton, List.singleton_append]
    have e1 : ∏ i ∈ range pre.length, weightFactor bus.point (s.τ t)
        (nRounds s - (pre.length + 1) + (i + 1)) ((c :: pre.reverse).getD (i + 1) 0) =
        ∏ i ∈ range pre.length, weightFactor bus.point (s.τ t) (nRounds s - pre.length + i)
          (pre.reverse.getD i 0) :=
      prod_congr rfl fun i _ ↦ by
        rw [List.getD_cons_succ, show nRounds s - (pre.length + 1) + (i + 1) =
          nRounds s - pre.length + i by omega]
    rw [e1, List.getD_cons_zero, show nRounds s - (pre.length + 1) + 0 = st.free - 1 by omega]
    rfl
  · rw [hcols]
    split
    · rw [Array.size_map, hsize]
    · exact hsize
  · have hci := hcol i
    rw [hfree', hcols]
    by_cases hact : st.free - 1 < s.τ t
    · rw [ite_eq_left hact, getD_map_lt (foldHigh c) (st.cols.getD t #[]) i #[] #[]
        (by rw [hsize]; exact i.isLt)]
      have hmin : min (s.τ t) st.free = st.free - 1 + 1 := by omega
      have hmin' : min (s.τ t) (st.free - 1) = st.free - 1 := by omega
      have hsz : ((st.cols.getD t #[]).getD i #[]).size = 2 ^ (st.free - 1 + 1) := by
        rw [hci.1, hmin]
      refine ⟨by rw [size_foldHigh, hsz, hmin', pow_succ]; omega, fun p hp ↦ ?_⟩
      rw [hmin'] at hp
      rw [multilinearEval_foldHigh c _ (st.free - 1) hsz p hp,
        hci.2 (p ++ [c]) (by simp only [List.length_append, List.length_singleton, hp]; omega),
        List.drop_append_of_le_length (l₁ := pre) (l₂ := [c]) (i := nRounds s - s.τ t)
          (by omega), List.reverse_append, List.reverse_singleton,
        List.append_assoc, List.singleton_append]
    · rw [ite_eq_right hact]
      have hmin : min (s.τ t) (st.free - 1) = min (s.τ t) st.free := by omega
      refine ⟨by rw [hmin]; exact hci.1, fun p hp ↦ ?_⟩
      rw [hmin] at hp
      rw [hci.2 p hp,
        List.drop_eq_nil_of_le (as := pre ++ [c]) (i := nRounds s - s.τ t)
          (by simp only [List.length_append, List.length_singleton]; omega),
        List.drop_eq_nil_of_le (as := pre) (i := nRounds s - s.τ t) (by omega)]

/-! ## The start and the end -/

/-- A table's column, lifted, read off the instance's columns. -/
theorem getD_tableInit (cols : Array (Array K))
    (hcols : ∀ c : Col, cols.getD (refCol c) #[] = ((inst prog s).column q c).values.toArray)
    (t : Fin 6) (i : Fin (width (opIdx t))) :
    ((tableInit cols).getD t #[]).getD i #[] =
      (((inst prog s).column q ⟨opIdx t, i⟩).values.toArray).map ofK := by
  have hwi : (i : ℕ) < (tables.getD t default).width := by rw [← width_opIdx]; exact i.isLt
  simp only [tableInit]
  rw [ofFn_getD _ t t.isLt _, ofFn_getD _ i hwi _]
  simp only
  rw [← refCol_opIdx t i, hcols]
  rfl

/-- A table's size, read off the instance's columns. -/
theorem size_tableInit (cols : Array (Array K)) (t : Fin 6) :
    ((tableInit cols).getD t #[]).size = width (opIdx t) := by
  simp only [tableInit]
  rw [ofFn_getD _ t t.isLt _, Array.size_ofFn, width_opIdx]

/-- **The start**: the tables' columns, lifted, weights one. -/
theorem tableInit_inv (cols : Array (Array K))
    (hcols : ∀ c : Col, cols.getD (refCol c) #[] = ((inst prog s).column q c).values.toArray)
    (bus : BusResult) :
    TInv prog s q bus [] ⟨tableInit cols, Array.replicate 6 1, nRounds s⟩ := by
  refine ⟨by simp, by simp, fun t ↦ ⟨?_, size_tableInit cols t, fun i ↦ ?_⟩⟩
  · simp [preWeight, Array.getD, t.isLt]
  · have hlist : (((inst prog s).column q ⟨opIdx t, i⟩).values.toArray.map ofK).toList =
        tableColList prog s q t i := by
      simp [tableColList, Vector.toList]
    have hmin : min (s.τ t) (nRounds s) = s.τ t := min_eq_left (τ_le_nRounds s t)
    try dsimp only
    rw [getD_tableInit cols hcols t i, hmin]
    refine ⟨?_, fun p _ ↦ ?_⟩
    · rw [← Array.length_toList, hlist, length_tableColList]
    · rw [hlist]
      simp

/-- **The end**: once every coordinate is bound, each table's evaluations are the honest ones at
the point. -/
theorem finalEvals_eq (bus : BusResult) (pre : List E) (st : TableState)
    (hI : TInv prog s q bus pre st) (hlen : pre.length = nRounds s) (t : Fin 6) :
    finalEvals (st.cols.getD t #[]) = evalsAt prog s q t pre.reverse := by
  obtain ⟨_, hfree, hI⟩ := hI
  obtain ⟨_, hsize, hcol⟩ := hI t
  have hf : st.free = 0 := by omega
  apply List.ext_getElem
    (by rw [finalEvals, List.length_map, Array.length_toList, hsize]; simp [evalsAt])
  intro i h1 h2
  have hi : i < width (opIdx t) := by simpa [evalsAt] using h2
  have hc := (hcol ⟨i, hi⟩).2 [] (by simp [hf])
  simp only [finalEvals, List.getElem_map, Array.getElem_toList]
  rw [(List.getD_eq_getElem (evalsAt prog s q t pre.reverse) 0 h2).symm,
    getD_evalsAt prog s q t _ i hi, List.take_reverse,
    hlen, ← List.nil_append ((pre.drop (nRounds s - s.τ t)).reverse), ← hc]
  rw [getElem_eq_getD _ i _ #[]]
  simp only [multilinearEval, List.foldl_nil, List.headD_eq_getD, toList_getD]

/-! ## The phase -/

/-- The constraint powers have the two `JUMP` needs. -/
theorem two_le_cpOf (xi : E) : 2 ≤ (cpOf xi).length := by
  simp only [cpOf, List.length_take, powers, length_powersFrom]
  have : (tables.map Table.nConstraints).sum = 2 := rfl
  omega

/-- The tables' batched polynomials. -/
theorem tableTermsOf_getD (xi : E) (bus : BusResult) (t : Fin 6) :
    (tableTermsOf xi bus).getD t [] = rowTerms (cpOf xi) (fpOf xi) bus.forms t := by
  rw [tableTermsOf, ofFn_getD _ t t.isLt _]
  rfl

/-- The waiting tables' sums. -/
theorem tableSigmas_getD (cols : Array (Array K))
    (hcols : ∀ c : Col, cols.getD (refCol c) #[] = ((inst prog s).column q c).values.toArray)
    {bus : BusResult} (hb : BusGood prog s q bus) (xi : E) (t : Fin 6) (ht : s.τ t < nRounds s) :
    (tableSigmas bus.point (tableLogs s) (tableTermsOf xi bus) (tableInit cols)).getD t 0 =
      waitSum prog s q (cpOf xi) (fpOf xi) bus t := by
  rw [tableSigmas, ofFn_getD _ t t.isLt _]
  simp only [getD_tableLogs, show (tableLogs s).foldl max 0 = nRounds s from rfl]
  rw [tableSigma, ite_eq_left ht]
  dsimp only
  rw [fold_add_eq_sum, waitSum, Finset.sum_range, tableTermsOf_getD xi bus t]
  have hlen : (bus.point.take (s.τ t)).length = s.τ t := by
    have := hb.point_length t
    simp only [List.length_take]
    omega
  refine sum_congr rfl fun y _ ↦ ?_
  rw [eqTable_getD (bus.point.take (s.τ t)) y (by rw [hlen]; exact y.isLt), hlen, eqEval_comm,
    rowPart, ← evaluate_rowTerms (cpOf xi) (fpOf xi) (two_le_cpOf xi) bus t]
  refine congrArg (_ * ·) (congrArg (Form.evaluate _) (funext fun i ↦ ?_))
  by_cases hi : i < width (opIdx t)
  · have hrow : (rowEvals prog s q t y).getD i 0 = ofK (rowCell prog s q t y ⟨i, hi⟩) := by
      unfold rowEvals
      rw [List.getD_eq_getElem _ _ (by simp [hi])]
      simp
    rw [getD_tableInit cols hcols t ⟨i, hi⟩,
      getD_map_lt ofK _ (↑y) 0 0 (by rw [Vector.size_toArray]; exact y.isLt), hrow, rowCell,
      ← getElem_eq_getD _ _ (by rw [Vector.size_toArray]; exact y.isLt)]
    rfl
  · rw [getD_of_size_le _ i #[] (by rw [size_tableInit]; omega)]
    have hrow : (rowEvals prog s q t y).getD i 0 = 0 := by
      unfold rowEvals
      exact List.getD_eq_default _ _ (by simp; omega)
    rw [hrow]
    simp

/-- The evaluations sent at the end are the specification's. -/
theorem tableEvals_eq (bus : BusResult) (pre : List E) (st : TableState)
    (hI : TInv prog s q bus pre st) (hlen : pre.length = nRounds s) :
    tableEvals st = (pairsAt prog s q bus pre.reverse).flatMap (·.2) := by
  have hfin : ∀ t (ht : t < 6), finalEvals (st.cols.getD t #[]) =
      evalsAt prog s q ⟨t, ht⟩ pre.reverse := fun t ht ↦
    finalEvals_eq bus pre st hI hlen ⟨t, ht⟩
  have hr : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  rw [tableEvals, hr]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [hfin 0 (by norm_num), hfin 1 (by norm_num), hfin 2 (by norm_num), hfin 3 (by norm_num),
    hfin 4 (by norm_num), hfin 5 (by norm_num)]
  rfl

/-- **The executable table phase makes the specification's moves**: from the instance's columns
(`cols`, by global column), the announced log-heights and a true bus result. -/
theorem corr_tableFast (cols : Array (Array K))
    (hcols : ∀ c : Col, cols.getD (refCol c) #[] = ((inst prog s).column q c).values.toArray)
    (logs : List ℕ) (hlogs : logs = tableLogs s) (bus : BusResult)
    (hb : BusGood prog s q bus) :
    Corr (fun _ _ ↦ True) (tableFast cols logs bus) (hTable prog s q bus) := by
  subst hlogs
  show Corr _ (Script.sampleE.bind fun xi ↦
      (sumcheckBy (tableRound bus.point (tableLogs s) (tableTermsOf xi bus)
          (tableSigmas bus.point (tableLogs s) (tableTermsOf xi bus) (tableInit cols)))
        (tableFold bus.point (tableLogs s)) (List.replicate (nRounds s) none)
        ⟨tableInit cols, Array.replicate 6 1, nRounds s⟩).bind fun r ↦
      Script.sendList (tableEvals r.2))
    (Script.sampleE.bind fun xi ↦
      (hSumcheck 4 (claimOf prog s q (cpOf xi) (fpOf xi) bus) (List.replicate (nRounds s) none)
        []).bind fun r ↦
      (Script.sendList ((pairsAt prog s q bus r.1.reverse).flatMap (·.2))).bind fun _ ↦
        .ret (bus.claims ++
          (termsPure (cpOf xi) (fpOf xi) r.1.reverse (pairsAt prog s q bus r.1.reverse) 0 0 []).2))
  have key : ∀ xi : E, Corr (fun _ _ ↦ True)
      ((sumcheckBy (tableRound bus.point (tableLogs s) (tableTermsOf xi bus)
          (tableSigmas bus.point (tableLogs s) (tableTermsOf xi bus) (tableInit cols)))
        (tableFold bus.point (tableLogs s)) (List.replicate (nRounds s) none)
        ⟨tableInit cols, Array.replicate 6 1, nRounds s⟩).bind fun r ↦
      Script.sendList (tableEvals r.2))
      ((hSumcheck 4 (claimOf prog s q (cpOf xi) (fpOf xi) bus) (List.replicate (nRounds s) none)
        []).bind fun r ↦
      (Script.sendList ((pairsAt prog s q bus r.1.reverse).flatMap (·.2))).bind fun _ ↦
        .ret (bus.claims ++
          (termsPure (cpOf xi) (fpOf xi) r.1.reverse (pairsAt prog s q bus r.1.reverse) 0 0
            []).2)) := by
    intro xi
    have h1 : (1 : ℕ) ≤ 4 := by norm_num
    have h2 : (4 : ℕ) ≤ 2 ^ 128 := by norm_num
    have hround : ∀ pre st, TInv prog s q bus pre st → pre.length < nRounds s →
        (tableRound bus.point (tableLogs s) (tableTermsOf xi bus)
          (tableSigmas bus.point (tableLogs s) (tableTermsOf xi bus) (tableInit cols)) st).length =
            4 ∧ ∀ x, polyEval (tableRound bus.point (tableLogs s) (tableTermsOf xi bus)
              (tableSigmas bus.point (tableLogs s) (tableTermsOf xi bus) (tableInit cols)) st) x =
                claimOf prog s q (cpOf xi) (fpOf xi) bus (pre ++ [x]) :=
      fun pre st hI hk ↦ ⟨length_tableRound _ _ _ _ _, fun x ↦ tableRound_eq hb (cpOf xi)
        (fpOf xi) (two_le_cpOf xi) (tableLogs s) rfl _ (tableTermsOf_getD xi bus) _
        (tableSigmas_getD cols hcols hb xi) pre st hI hk x⟩
    have hfold : ∀ pre st c, TInv prog s q bus pre st → pre.length < nRounds s →
        TInv prog s q bus (pre ++ [c]) (tableFold bus.point (tableLogs s) st c) :=
      fun pre st c hI hk ↦ tableFold_inv bus (tableLogs s) rfl pre st hI hk c
    have hinit := tableInit_inv cols hcols bus
    have hlen0 : ([] : List E).length + (List.replicate (nRounds s) (none : Option E)).length ≤
        nRounds s := by simp
    have hs := @corr_sumcheckBy_le TableState 4 h1 h2
      (claimOf prog s q (cpOf xi) (fpOf xi) bus)
      (tableRound bus.point (tableLogs s) (tableTermsOf xi bus)
        (tableSigmas bus.point (tableLogs s) (tableTermsOf xi bus) (tableInit cols)))
      (tableFold bus.point (tableLogs s)) (TInv prog s q bus) (nRounds s)
      hround hfold (List.replicate (nRounds s) none) []
      ⟨tableInit cols, Array.replicate 6 1, nRounds s⟩ hinit hlen0
    have hk : ∀ (a : List E × TableState) (b : List E × E),
        (a.1 = b.1 ∧ a.1.length = (List.replicate (nRounds s) (none : Option E)).length ∧
          TInv prog s q bus ([] ++ a.1) a.2 ∧
          b.2 = claimOf prog s q (cpOf xi) (fpOf xi) bus ([] ++ b.1)) →
        Corr (fun _ _ ↦ True)
          (Script.sendList (tableEvals a.2))
          ((Script.sendList ((pairsAt prog s q bus b.1.reverse).flatMap (·.2))).bind fun _ ↦
            .ret (bus.claims ++ (termsPure (cpOf xi) (fpOf xi) b.1.reverse
              (pairsAt prog s q bus b.1.reverse) 0 0 []).2)) := by
      intro a b hab
      obtain ⟨h1, h2, h3, -⟩ := hab
      rw [← h1]
      simp only [List.length_replicate] at h2
      simp only [List.nil_append] at h3
      have e : Script.sendList (tableEvals a.2) =
          (Script.sendList (tableEvals a.2)).bind Script.ret := (Script.bind_ret _).symm
      rw [e, tableEvals_eq bus a.1 a.2 h3 h2]
      exact Corr.bind_same _ fun _ ↦ trivial
    -- `nRounds s` made opaque: unifying the scripts must not evaluate the rounds' count
    generalize nRounds s = n at hs hk ⊢
    exact Corr.bind hk _ _ hs
  generalize nRounds s = n at key ⊢
  exact Corr.bind_same Script.sampleE key

end
end LeanVM.Prover
