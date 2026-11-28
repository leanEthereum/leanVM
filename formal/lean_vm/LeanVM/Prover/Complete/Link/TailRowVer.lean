/-
  LeanVM.Prover.Complete.Link.TailRowVer

  The verifier's row side (`rowSideOf`) with its steps named, and what each step adds.
-/

module

public import LeanVM.Prover.Complete.Link.TailRowCols

/-!
# The verifier's row side, step by step

`rowSideOf_eq` (by `rfl`): `rowSideOf` is a fold of `vTableStep` over the tables, each table a fold
of `vPointerStep` over its pointers. `vPointerStep`'s effect (`vPointerStep_q`, `_certWeight`,
`_coef`, `_shifts`): one more pointer column, the certificate weight `eq_q·corner·ω·ε_q`, the
coefficient `eq_q·corner·vCoef`, and on a memory pointer the shifted reads' coefficients.
`foldl_vPointerStep`: a table's pointers, summed.
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier.Defers

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Prover

/-- `linkTail`'s step at one pointer column of table `t`. -/
def vPointerStep (layout : Layout) (ch : LinkChallenges) (eqQ : List E) (t : ℕ) (point : List E)
    (corner act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1 : E) (col : ℕ → E)
    (links : Links) (muT : List E) (acc : LinkRowSide) (pk : ℕ × ℕ) : LinkRowSide :=
  match pk with
  | (pointer, k) =>
  let gammaMem := ch.gammaMem
  let etaMem := ch.etaMem
  let eps := ch.eps
  let state := links.stateLink
  let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
  let e := eqQ.getD acc.q 0 * corner
  let (coef, shifts) :=
    match k with
    | 0 => (acc.coef + e * act * (eqZetaR * sHat + shiftZetaR * sNext), acc.shifts)
    | 1 => (acc.coef + e * omega * (xBc + col state.fp * pFp), acc.shifts)
    | _ =>
      let coef := (links.memory.zip muT).foldl (fun coef (access, m) ↦
        access.reads.foldl (fun coef read ↦
          match read with
          | .word p scale =>
            if p = pointer then
              coef + e * omega * etaMem * m * gammaMem.getD 1 0 * m1 * scale.evaluate col
            else coef
          | _ => coef) coef) acc.coef
      ((links.memory.zip muT).filter (·.1.pointer = pointer)).foldl
        (fun (cs : E × List E) (access, m) ↦
          let c := e * omega * gateOf access * etaMem * m * yMem
          match access.shift with
          | 0 => (cs.1 + c, cs.2)
          | s + 1 => (cs.1, addAtSlot cs.2 s c)) (coef, acc.shifts)
  let piece : RingPiece :=
    { placement :=
        some ((layout.placements.getD (globalColumnBases.getD t 0 + pointer) none).getD default)
      point := point
      scale := eqQ.getD acc.q 0 }
  { acc with
    coef := coef
    shifts := shifts
    certWeight := acc.certWeight + e * omega * eps.getD acc.q 0
    pieces := acc.pieces ++ [piece]
    q := acc.q + 1 }

/-- `linkTail`'s step at one table. -/
def vTableStep (layout : Layout) (ch : LinkChallenges) (chi jump : List E)
    (eqZetaR shiftZetaR xBc pFp yMem m1 eq0R : E) (eqQ : List E) (acc : LinkRowSide)
    (tt : Table × ℕ) : LinkRowSide :=
  match tt with
  | (table, t) =>
  let heights := layout.tableLogHeights
  let rows := layout.tableRows
  let pointers := layout.tables.map (·.links.pointers)
  let theta := ch.theta
  let gammaState := ch.gammaState
  let gammaMem := ch.gammaMem
  let mu := ch.mu
  let slot := ch.slot
  let etaMem := ch.etaMem
  let etaBc := ch.etaBc
  let tau := ch.tau
  let stateGamma := fun (pc fp : E) ↦ 1 + gammaState.getD 0 0 * pc + gammaState.getD 1 0 * fp
  let nonPointer := fun (t : ℕ) (table : Table) ↦
    (List.range table.width).filter fun c ↦ !(pointers.getD t []).contains c
  let height := heights.getD t 0
  let tableRows := rows.getD t 0
  let point := chi.take height
  let corner := prodE ((chi.drop height).map (1 + ·))
  let columns := nonPointer t table
  let sent := columns.zip (acc.sent.take columns.length)
  let values := (List.range table.width).map fun c ↦ (sent.lookup c).getD 0
  let col := fun (c : ℕ) ↦ values.getD c 0
  let links := table.links
  let muT := mu.getD t []
  let omega := omegaAt (theta.getD t 0) (tau.take height) point tableRows
  let act := lessThan point tableRows
  let state := links.stateLink
  let sHat := stateGamma (col state.pc) (col state.fp)
  let sNext := stateGamma (state.next.1.evaluate col) (state.next.2.evaluate col)
  let accessValue := fun (a : Access) ↦
    gammaMem.getD 0 0 * a.address.evaluate col + gammaMem.getD 3 0 +
      gammaMem.getD 1 0 * a.value.evaluate col
  let bc := links.bytecodeLink
  let rBc := slot.getD 1 0 * col bc.pc + slot.getD 2 0 + slot.getD 3 0 * gpow bc.opcode +
    sumE (bc.operands.map fun (slots, f) ↦ slot.getD (slots.headD 0) 0 * f.evaluate col)
  let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
  let memory := sumE ((links.memory.zip muT).map fun (a, m) ↦ m * gateOf a * accessValue a)
  let tableBase := omega * eq0R * (etaMem * memory + etaBc * rBc)
  let tableBase :=
    if 0 < table.nConstraints then
      let identities := table.constraints values
      let eqTau := eqEval (tau.take height) point
      tableBase + eqTau * sumE (List.zipWith (· * ·) jump identities)
    else tableBase
  let acc := (pointers.getD t []).zipIdx.foldl
    (vPointerStep layout ch eqQ t point corner act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem
      m1 col links muT)
    { acc with base := acc.base + corner * tableBase, sent := acc.sent.drop columns.length }
  { acc with columns := acc.columns ++ [(point, sent)] }

theorem rowSideOf_eq (layout : Layout) (ch : LinkChallenges) (chi jump : List E)
    (eqZetaR shiftZetaR xBc pFp yMem m1 eq0R : E) (eqQ : List E) (maxShift : ℕ) (sent0 : List E) :
    rowSideOf layout ch chi jump eqZetaR shiftZetaR xBc pFp yMem m1 eq0R eqQ maxShift sent0 =
      layout.tables.zipIdx.foldl
        (vTableStep layout ch chi jump eqZetaR shiftZetaR xBc pFp yMem m1 eq0R eqQ)
        ⟨0, List.replicate maxShift 0, 0, 0, [], 0, [], sent0⟩ :=
  rfl

/-! ## One pointer column's step -/

section Step

open LeanVM.Prover.Complete

theorem foldl_eq_add_sum {α : Type} (f : E → α → E) (δ : α → E) (hf : ∀ c a, f c a = c + δ a) :
    ∀ (L : List α) (c : E), L.foldl f c = c + (L.map δ).sum
  | [], c => by simp
  | a :: L, c => by
    rw [List.foldl_cons, foldl_eq_add_sum f δ hf L, hf, List.map_cons, List.sum_cons]
    ring

theorem tailRow_length_addAtSlot (l : List E) (s : ℕ) (v : E) : (addAtSlot l s v).length = l.length := by
  simp [addAtSlot]

theorem tailRow_getD_addAtSlot (l : List E) {s : ℕ} (hs : s < l.length) (v : E) (s' : ℕ) :
    (addAtSlot l s v).getD s' 0 = l.getD s' 0 + if s' = s then v else 0 := by
  unfold addAtSlot
  by_cases h : s' = s
  · subst h
    simp [List.getD_eq_getElem?_getD, hs]
  · simp [List.getD_eq_getElem?_getD, Ne.symm h, h]

/-- A fold adding to a coefficient and to the shifts' slots. -/
theorem foldl_pair {α : Type} (f : E × List E → α → E × List E) (δ : α → E) (δs : α → ℕ → E)
    (n : ℕ) (P : α → Prop) (hf1 : ∀ cs a, P a → (f cs a).1 = cs.1 + δ a)
    (hf2 : ∀ cs a, P a → cs.2.length = n → (f cs a).2.length = n ∧
      ∀ s < n, (f cs a).2.getD s 0 = cs.2.getD s 0 + δs a s) :
    ∀ (L : List α) (cs : E × List E), (∀ a ∈ L, P a) → cs.2.length = n →
      (L.foldl f cs).1 = cs.1 + (L.map δ).sum ∧ (L.foldl f cs).2.length = n ∧
        ∀ s < n, (L.foldl f cs).2.getD s 0 = cs.2.getD s 0 + (L.map fun a ↦ δs a s).sum
  | [], cs, _, hn => by simp [hn]
  | a :: L, cs, hP, hn => by
    have ha := hP a List.mem_cons_self
    obtain ⟨h2, h3⟩ := hf2 cs a ha hn
    obtain ⟨i1, i2, i3⟩ := foldl_pair f δ δs n P hf1 hf2 L (f cs a)
      (fun b hb ↦ hP b (List.mem_cons_of_mem _ hb)) h2
    rw [List.foldl_cons]
    refine ⟨?_, i2, fun s hs ↦ ?_⟩
    · rw [i1, hf1 cs a ha, List.map_cons, List.sum_cons]; ring
    · rw [i3 s hs, h3 s hs, List.map_cons, List.sum_cons]; ring

/-- The verifier's coefficient at `(pointer, k)`, over `eq_q·corner`. -/
def vCoef (ch : LinkChallenges) (act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1 : E)
    (col : ℕ → E) (links : Links) (muT : List E) (pointer : ℕ) : ℕ → E
  | 0 => act * (eqZetaR * sHat + shiftZetaR * sNext)
  | 1 => omega * (xBc + col links.stateLink.fp * pFp)
  | _ + 2 => omega * ch.etaMem * ch.gammaMem.getD 1 0 * m1 * readsAt links muT pointer col +
      omega * ch.etaMem * yMem * directAt links muT pointer col

/-- The verifier's coefficient of the shift `s + 1` at a memory pointer, over `eq_q·corner`. -/
def vShift (ch : LinkChallenges) (omega yMem : E) (col : ℕ → E) (links : Links) (muT : List E)
    (pointer s : ℕ) : E :=
  omega * ch.etaMem * yMem * ((accessesAt links muT pointer).map fun am ↦
    if am.1.shift = s + 1 then am.2 * (am.1.gate.map col).getD 1 else 0).sum

variable (layout : Layout) (ch : LinkChallenges) (eqQ : List E) (t : ℕ) (point : List E)
  (corner act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1 : E) (col : ℕ → E)
  (links : Links) (muT : List E)

theorem vPointerStep_q (acc : LinkRowSide) (pointer k : ℕ) :
    (vPointerStep layout ch eqQ t point corner act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1
      col links muT acc (pointer, k)).q = acc.q + 1 := by
  rcases k with _ | _ | k <;> rfl

theorem vPointerStep_certWeight (acc : LinkRowSide) (pointer k : ℕ) :
    (vPointerStep layout ch eqQ t point corner act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1
      col links muT acc (pointer, k)).certWeight =
      acc.certWeight + eqQ.getD acc.q 0 * corner * omega * ch.eps.getD acc.q 0 := by
  rcases k with _ | _ | k <;> rfl

theorem vPointerStep_rest (acc : LinkRowSide) (pointer k : ℕ) :
    (vPointerStep layout ch eqQ t point corner act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1
      col links muT acc (pointer, k)).base = acc.base ∧
    (vPointerStep layout ch eqQ t point corner act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1
      col links muT acc (pointer, k)).sent = acc.sent ∧
    (vPointerStep layout ch eqQ t point corner act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1
      col links muT acc (pointer, k)).columns = acc.columns := by
  rcases k with _ | _ | k <;> exact ⟨rfl, rfl, rfl⟩

/-- **A memory pointer's step**: its coefficient and its shifts' coefficients. -/
theorem vPointerStep_mem (acc : LinkRowSide) (pointer k : ℕ)
    (hS : ∀ am ∈ accessesAt links muT pointer, am.1.shift ≤ acc.shifts.length) :
    let r := vPointerStep layout ch eqQ t point corner act omega eqZetaR shiftZetaR sHat sNext xBc pFp
      yMem m1 col links muT acc (pointer, k + 2)
    r.coef = acc.coef + eqQ.getD acc.q 0 * corner *
        vCoef ch act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1 col links muT pointer (k + 2) ∧
      r.shifts.length = acc.shifts.length ∧
      ∀ s < acc.shifts.length, r.shifts.getD s 0 =
        acc.shifts.getD s 0 + eqQ.getD acc.q 0 * corner * vShift ch omega yMem col links muT pointer s := by
  intro r
  set e := eqQ.getD acc.q 0 * corner
  have hreads : ∀ c0 : E, (links.memory.zip muT).foldl (fun coef (am : Access × E) ↦
      am.1.reads.foldl (fun coef read ↦ match read with
        | .word p scale =>
          if p = pointer then
            coef + e * omega * ch.etaMem * am.2 * ch.gammaMem.getD 1 0 * m1 * scale.evaluate col
          else coef
        | _ => coef) coef) c0 =
      c0 + e * omega * ch.etaMem * ch.gammaMem.getD 1 0 * m1 * readsAt links muT pointer col := by
    intro c0
    rw [foldl_eq_add_sum _ (fun am ↦ e * omega * ch.etaMem * ch.gammaMem.getD 1 0 * m1 *
      (am.1.reads.map (wordAt pointer am.2 col)).sum) (fun c am ↦ ?_), readsAt, ← List.sum_map_mul_left]
    rw [foldl_eq_add_sum _ (fun rd ↦ e * omega * ch.etaMem * ch.gammaMem.getD 1 0 * m1 *
      wordAt pointer am.2 col rd) (fun c rd ↦ ?_), ← List.sum_map_mul_left]
    cases rd with
    | word p scale =>
      by_cases hp : p = pointer
      · simp only [hp, ↓reduceIte, wordAt]; ring
      · simp [hp, wordAt]
    | slot _ _ => simp [wordAt]
    | frame _ _ => simp [wordAt]
    | pc _ _ => simp [wordAt]
  set coefR := (links.memory.zip muT).foldl (fun coef (am : Access × E) ↦
      am.1.reads.foldl (fun coef read ↦ match read with
        | .word p scale =>
          if p = pointer then
            coef + e * omega * ch.etaMem * am.2 * ch.gammaMem.getD 1 0 * m1 * scale.evaluate col
          else coef
        | _ => coef) coef) acc.coef with hcoefR
  set cOf := fun (am : Access × E) ↦ e * omega * (am.1.gate.map col).getD 1 * ch.etaMem * am.2 * yMem
  set step := fun (cs : E × List E) (am : Access × E) ↦
      match am.1.shift with
      | 0 => (cs.1 + cOf am, cs.2)
      | s + 1 => (cs.1, addAtSlot cs.2 s (cOf am)) with hstep
  set X := (accessesAt links muT pointer).foldl step (coefR, acc.shifts) with hX
  have hr1 : r.coef = X.1 := rfl
  have hr2 : r.shifts = X.2 := rfl
  obtain ⟨x1, x2, x3⟩ := foldl_pair step (fun am ↦ if am.1.shift = 0 then cOf am else 0)
    (fun am s ↦ if am.1.shift = s + 1 then cOf am else 0) acc.shifts.length
    (fun am ↦ am.1.shift ≤ acc.shifts.length)
    (fun cs am _ ↦ by
      rcases h : am.1.shift with _ | s
      · simp only [hstep, h]; simp
      · simp only [hstep, h]; simp)
    (fun cs am hP hn ↦ by
      rcases h : am.1.shift with _ | s
      · simp only [hstep, h]; exact ⟨hn, fun s _ ↦ by simp⟩
      · simp only [hstep, h]
        rw [h] at hP
        refine ⟨by rw [tailRow_length_addAtSlot, hn], fun s' hs' ↦ ?_⟩
        rw [tailRow_getD_addAtSlot _ (by omega)]
        by_cases hs : s' = s
        · simp [hs]
        · simp [hs, Ne.symm hs])
    (accessesAt links muT pointer) (coefR, acc.shifts) hS rfl
  rw [← hX] at x1 x2 x3
  refine ⟨?_, by rw [hr2, x2], fun s hs ↦ ?_⟩
  · rw [hr1, x1, hcoefR, hreads]
    simp only [vCoef, directAt]
    have : ∀ am ∈ accessesAt links muT pointer, (if am.1.shift = 0 then cOf am else 0) =
        e * (omega * ch.etaMem * yMem * (if am.1.shift = 0 then am.2 * (am.1.gate.map col).getD 1
          else 0)) := by
      intro am _
      split_ifs <;> simp [cOf]; ring
    rw [List.map_congr_left this, List.sum_map_mul_left, List.sum_map_mul_left]
    ring
  · rw [hr2, x3 s hs, vShift, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun am _ ↦ ?_)
    split_ifs <;> simp [cOf]; ring

/-- **The cycle and the program pointers' step.** -/
theorem vPointerStep_low (acc : LinkRowSide) (pointer k : ℕ) (hk : k < 2) :
    let r := vPointerStep layout ch eqQ t point corner act omega eqZetaR shiftZetaR sHat sNext xBc pFp
      yMem m1 col links muT acc (pointer, k)
    r.coef = acc.coef + eqQ.getD acc.q 0 * corner *
        vCoef ch act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1 col links muT pointer k ∧
      r.shifts = acc.shifts := by
  match k, hk with
  | 0, _ =>
    intro r
    have h : r.coef = acc.coef + eqQ.getD acc.q 0 * corner * act *
      (eqZetaR * sHat + shiftZetaR * sNext) := rfl
    exact ⟨by rw [h]; simp only [vCoef]; ring, rfl⟩
  | 1, _ =>
    intro r
    have h : r.coef = acc.coef + eqQ.getD acc.q 0 * corner * omega *
      (xBc + col links.stateLink.fp * pFp) := rfl
    exact ⟨by rw [h]; simp only [vCoef]; ring, rfl⟩

theorem vShift_nil (pointer s : ℕ) (h : accessesAt links muT pointer = []) :
    vShift ch omega yMem col links muT pointer s = 0 := by
  simp [vShift, h]

/-- **A table's pointer columns, folded.** -/
theorem foldl_vPointerStep (q0 n : ℕ) : ∀ (l : List ℕ) (k0 : ℕ) (acc : LinkRowSide),
    acc.q = q0 + k0 → acc.shifts.length = n →
    (∀ pk ∈ l.zipIdx k0, ∀ am ∈ accessesAt links muT pk.1, am.1.shift ≤ n) →
    (∀ pk ∈ l.zipIdx k0, pk.2 < 2 → accessesAt links muT pk.1 = []) →
    let r := (l.zipIdx k0).foldl (vPointerStep layout ch eqQ t point corner act omega eqZetaR
      shiftZetaR sHat sNext xBc pFp yMem m1 col links muT) acc
    r.q = acc.q + l.length ∧ r.base = acc.base ∧ r.sent = acc.sent ∧ r.columns = acc.columns ∧
      r.coef = acc.coef + ((l.zipIdx k0).map fun pk ↦ eqQ.getD (q0 + pk.2) 0 * corner *
        vCoef ch act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1 col links muT pk.1 pk.2).sum ∧
      r.certWeight = acc.certWeight + ((l.zipIdx k0).map fun pk ↦
        eqQ.getD (q0 + pk.2) 0 * corner * omega * ch.eps.getD (q0 + pk.2) 0).sum ∧
      r.shifts.length = n ∧ ∀ s < n, r.shifts.getD s 0 = acc.shifts.getD s 0 +
        ((l.zipIdx k0).map fun pk ↦ eqQ.getD (q0 + pk.2) 0 * corner *
          vShift ch omega yMem col links muT pk.1 s).sum
  | [], _, acc, _, hn, _, _ => by simp [hn]
  | p :: l, k0, acc, hq, hn, hS, hlow => by
    intro r
    simp only [List.zipIdx_cons] at hS hlow
    set acc' := vPointerStep layout ch eqQ t point corner act omega eqZetaR shiftZetaR sHat sNext xBc
      pFp yMem m1 col links muT acc (p, k0) with hacc'
    have hq' : acc'.q = q0 + (k0 + 1) := by rw [hacc', vPointerStep_q, hq]; ring
    obtain ⟨hb, hs, hc⟩ := vPointerStep_rest layout ch eqQ t point corner act omega eqZetaR shiftZetaR
      sHat sNext xBc pFp yMem m1 col links muT acc p k0
    have hw := vPointerStep_certWeight layout ch eqQ t point corner act omega eqZetaR shiftZetaR
      sHat sNext xBc pFp yMem m1 col links muT acc p k0
    -- the step's coefficient and shifts
    have hstep : acc'.coef = acc.coef + eqQ.getD (q0 + k0) 0 * corner *
          vCoef ch act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1 col links muT p k0 ∧
        acc'.shifts.length = n ∧ ∀ s < n, acc'.shifts.getD s 0 = acc.shifts.getD s 0 +
          eqQ.getD (q0 + k0) 0 * corner * vShift ch omega yMem col links muT p s := by
      rw [← hq]
      by_cases hk : k0 < 2
      · obtain ⟨h1, h2⟩ := vPointerStep_low layout ch eqQ t point corner act omega eqZetaR shiftZetaR
          sHat sNext xBc pFp yMem m1 col links muT acc p k0 hk
        have h0 := vShift_nil ch omega yMem col links muT p
          (s := 0) (hlow (p, k0) List.mem_cons_self hk)
        refine ⟨h1, by rw [h2, hn], fun s _ ↦ ?_⟩
        rw [h2, vShift_nil ch omega yMem col links muT p s (hlow (p, k0) List.mem_cons_self hk)]
        ring
      · obtain ⟨j, rfl⟩ : ∃ j, k0 = j + 2 := ⟨k0 - 2, by omega⟩
        obtain ⟨h1, h2, h3⟩ := vPointerStep_mem layout ch eqQ t point corner act omega eqZetaR
          shiftZetaR sHat sNext xBc pFp yMem m1 col links muT acc p j
          (fun am ham ↦ hn ▸ hS (p, j + 2) List.mem_cons_self am ham)
        exact ⟨h1, by rw [h2, hn], fun s hs ↦ h3 s (by omega)⟩
    obtain ⟨s1, s2, s3⟩ := hstep
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := foldl_vPointerStep q0 n l (k0 + 1) acc' hq' s2
      (fun pk hpk ↦ hS pk (List.mem_cons_of_mem _ hpk))
      (fun pk hpk ↦ hlow pk (List.mem_cons_of_mem _ hpk))
    have hr : r = (l.zipIdx (k0 + 1)).foldl (vPointerStep layout ch eqQ t point corner act omega
      eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1 col links muT) acc' := rfl
    rw [hr]
    refine ⟨?_, by rw [i2, hb], by rw [i3, hs], by rw [i4, hc], ?_, ?_, i7, fun s hs' ↦ ?_⟩
    · rw [i1, hacc', vPointerStep_q, List.length_cons]; ring
    · rw [i5, s1, List.zipIdx_cons, List.map_cons, List.sum_cons]; ring
    · rw [i6, hw, hq, List.zipIdx_cons, List.map_cons, List.sum_cons]; ring
    · rw [i8 s hs', s3 s hs', List.zipIdx_cons, List.map_cons, List.sum_cons]; ring

end Step

end LeanVM.Protocol.Verifier.Defers

end
