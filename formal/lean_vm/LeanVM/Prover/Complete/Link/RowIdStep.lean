/-
  LeanVM.Prover.Complete.Link.RowIdStep

  `rowProds`' pointer-column step, as the tables it appends and the terms it adds.
-/

module

public import LeanVM.Prover.Complete.Link.RowIdChunk

/-!
# The pointer-column step, unfolded

`rowPointerStep_eq`: the step of `rowProds` for the pointer column `p` (the `k`-th of its table)
appends its tables (`stepTabs`: the coefficients on `ω` and `act`, the `2d` functionals `D_i`,
`D̄_i`, the shifted reads `T_s`) and adds its terms (`stepTerms`). A term's value at a row reads
its tables there (`termAt_eq`, `tv`), which appending more tables keeps (`tv_append_left`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover Finset

/-! ## Tables read at a row -/

/-- Table `f`'s entry at row `u`. -/
def tv (T : Array (Array E)) (u f : ℕ) : E := (T.getD f #[]).getD u 0

theorem termAt_eq (P : Prods) (u : ℕ) (cf : E × Array ℕ) :
    termAt P u cf = cf.1 * (cf.2.toList.map (tv P.tables u)).prod := by
  rw [termAt, ← Array.foldl_toList, foldl_mul_map]
  rfl

theorem termsAt_eq_sum (P : Prods) (u : ℕ) :
    termsAt P u = (P.terms.toList.map (termAt P u)).sum := by
  rw [termsAt_eq, foldl_add_map, zero_add]

theorem tv_append_left {A : Array (Array E)} (B : Array (Array E)) (u : ℕ) {f : ℕ}
    (h : f < A.size) : tv (A ++ B) u f = tv A u f := by
  simp [tv, Array.getD_eq_getD_getElem?, Array.getElem?_append_left h]

theorem tv_append_right (A B : Array (Array E)) (u j : ℕ) :
    tv (A ++ B) u (A.size + j) = tv B u j := by
  simp [tv, Array.getD_eq_getD_getElem?, Array.getElem?_append_right (Nat.le_add_right _ _)]

/-! ## Folds that push -/

theorem foldl_push_ite {α : Type} (f : Array (E × Array ℕ) → α → Array (E × Array ℕ))
    (c : α → Prop) [DecidablePred c] (g : α → E × Array ℕ)
    (hf : ∀ ts x, f ts x = if c x then ts else ts.push (g x)) :
    ∀ (l : List α) (ts : Array (E × Array ℕ)),
      (l.foldl f ts).toList = ts.toList ++ (l.filter (fun x ↦ !decide (c x))).map g
  | [], ts => by simp
  | x :: l, ts => by
    rw [List.foldl_cons, foldl_push_ite f c g hf l, hf]
    by_cases hc : c x
    · simp [hc]
    · simp [hc]

theorem foldl_push_two {α : Type} (f : Array (E × Array ℕ) → α → Array (E × Array ℕ))
    (a b : α → E × Array ℕ) (hf : ∀ ts x, f ts x = (ts.push (a x)).push (b x)) :
    ∀ (l : List α) (ts : Array (E × Array ℕ)),
      (l.foldl f ts).toList = ts.toList ++ l.flatMap (fun x ↦ [a x, b x])
  | [], ts => by simp
  | x :: l, ts => by
    rw [List.foldl_cons, foldl_push_two f a b hf l, hf]
    simp

/-! ## The step -/

section Step

variable (W : Witness) (inp : RowInputs) (t q₀ : ℕ)

/-- The tables the step of pointer column `p` appends. -/
def stepTabs (p k : ℕ) : Array (Array E) :=
  let chunks := W.chunks
  let d := chunks.d
  let links := (tables.getD t default).links
  let mu := inp.ch.mu.getD t []
  let h := W.layout.tableLogHeights.getD t 0
  let cols := W.tableCols t
  let fTabs := inp.functionals.tables
  let words := cols.getD p #[]
  let coefs := Array.ofFn (n := 2 ^ h) fun u ↦ rowCoefs inp links mu k p (rowValue cols u)
  let shifts := shiftsAt links mu p
  let ds := (List.range (2 * d)).map fun i ↦ functionalTable chunks words (fTabs.getD i (0, []))
  let ts := shifts.map fun s ↦ functionalTable chunks words (fTabs.getD (2 * d + s - 1) (0, []))
  #[coefs.map (·.1), coefs.map (·.2)] ++ ds.toArray ++ ts.toArray

/-- The factors `D_1 … D_{d-1}` of the step at `pos`. -/
def restAt (d pos : ℕ) : Array ℕ := ((List.range (d - 1)).map (pos + 2 + 1 + ·)).toArray

/-- A shifted access's term. -/
def shiftTerm (inp : RowInputs) (d pos : ℕ) (shifts : List ℕ) (am : Access × E) : E × Array ℕ :=
  (inp.ch.etaMem * inp.yMem * am.2, #[0] ++ (am.1.gate.map fun g ↦ #[3 + g]).getD #[] ++
    #[pos + 2 + 2 * d + shifts.idxOf am.1.shift] ++ restAt d pos)

/-- The terms the step of pointer column `p` at `pos` adds. -/
def stepTerms (pos p k : ℕ) : List (E × Array ℕ) :=
  let d := W.chunks.d
  let links := (tables.getD t default).links
  let mu := inp.ch.mu.getD t []
  let e := inp.cert * inp.ch.eps.getD (q₀ + k) 0
  [(1, #[0, pos, pos + 2] ++ restAt d pos), (1, #[1, pos + 1, pos + 2] ++ restAt d pos)] ++
    ((accessesAt links mu p).filter (fun am ↦ !decide (am.1.shift = 0))).map
      (shiftTerm inp d pos (shiftsAt links mu p)) ++
    (List.range d).flatMap fun i ↦
      [(e * inp.ch.nu.getD i 0, #[0, pos + 2 + i, pos + 2 + d + i]),
        (e * inp.ch.nu.getD i 0 * inp.functionals.mirrors.getD i 0, #[0])]

theorem size_stepTabs (p k : ℕ) :
    (stepTabs W inp t p k).size = 2 + 2 * W.chunks.d +
      (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) p).length := by
  simp [stepTabs]; omega

theorem rowPointerStep_eq (tabs : Array (Array E)) (terms : Array (E × Array ℕ)) (pos p k : ℕ) :
    rowPointerStep W inp t q₀ (tabs, terms, pos) (p, k) =
      (tabs ++ stepTabs W inp t p k, (terms.toList ++ stepTerms W inp t q₀ pos p k).toArray,
        pos + (stepTabs W inp t p k).size) := by
  rw [size_stepTabs]
  unfold rowPointerStep stepTabs
  dsimp only
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Array.append_assoc]
  · apply Array.toList_inj.mp
    rw [List.toList_toArray]
    rw [foldl_push_two _ _ _ (fun _ _ ↦ rfl)]
    rw [foldl_push_ite _ (fun am : Access × E ↦ am.1.shift = 0) _ (fun _ _ ↦ rfl)]
    simp [stepTerms, restAt, shiftTerm, Nat.add_assoc]
  · simp only
    omega

end Step

end LeanVM.Prover.Complete.RowId

end
