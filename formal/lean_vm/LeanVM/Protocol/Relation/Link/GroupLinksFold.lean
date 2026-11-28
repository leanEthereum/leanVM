/-
  LeanVM.Protocol.Relation.Link.GroupLinksFold

  The row side's fold seen through the summand at fixed functional values: what each table and
  each pointer column adds to `last`, as a sum over the tables and their pointer columns.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupFold
public import LeanVM.Protocol.Relation.Link.GroupCert
public import LeanVM.Protocol.Relation.Link.TailEq

/-!
# The row side's fold through the summand

At fixed functional values (`D_0`, the window reads `T_s`, the product `rest` of the other chunks,
`eq(0, q)`), `last` is linear in the fold's coefficient, its shifts and its base (`lkVal`). Each
pointer column adds its share (`lkPtr`: the state at column `0`, the program at column `1`, the
word reads and the accesses through the pointer at the others), each table its base terms
(`lkVal_rowSideOf`), the tables' values read from the message as `verify_link` reads them
(`lkVals`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

/-- `Σ_i l_i·ts_i`. -/
def lkZ (l ts : List E) : E := sumE (List.zipWith (· * ·) l ts)

/-- `last` as a linear form of the fold's state, at fixed functional values. -/
def lkVal (d0 rest eq0Q : E) (ts : List E) (acc : LinkRowSide) : E :=
  (acc.coef * d0 + lkZ acc.shifts ts) * rest + eq0Q * acc.base

theorem lkZ_addAtSlot : ∀ (l ts : List E) (s : ℕ) (c : E),
    lkZ (addAtSlot l s c) ts = lkZ l ts + (if s < l.length then c * ts.getD s 0 else 0)
  | [], ts, s, c => by simp [lkZ, addAtSlot, sumE_eq_sum']
  | x :: l, [], s, c => by cases s <;> simp [lkZ, addAtSlot, sumE_eq_sum']
  | x :: l, y :: ts, 0, c => by simp [lkZ, addAtSlot, sumE_eq_sum']; ring
  | x :: l, y :: ts, s + 1, c => by
    have h := lkZ_addAtSlot l ts s c
    simp only [lkZ, addAtSlot, sumE_eq_sum'] at h
    simp only [lkZ, addAtSlot, sumE_eq_sum', List.set_cons_succ, List.getD_cons_succ,
      List.zipWith_cons_cons, List.sum_cons, List.length_cons, h]
    split_ifs <;> first | omega | ring

theorem length_addAtSlot (l : List E) (s : ℕ) (c : E) : (addAtSlot l s c).length = l.length := by
  simp [addAtSlot]

/-- One access through a pointer: shift `0` adds to the coefficient, shift `s + 1` to `c_{s+1}`. -/
def lkShiftStep (F : Access × E → E) (cs : E × List E) (x : Access × E) : E × List E :=
  match x.1.shift with
  | 0 => (cs.1 + F x, cs.2)
  | s + 1 => (cs.1, addAtSlot cs.2 s (F x))

/-- The accesses through a pointer, folded into the coefficient and the shifts. -/
theorem lk_shift_fold (F : Access × E → E) (d0 : E) (ts : List E) : ∀ (L : List (Access × E)) (cs : E × List E),
    (L.foldl (lkShiftStep F) cs).1 * d0 + lkZ (L.foldl (lkShiftStep F) cs).2 ts =
      cs.1 * d0 + lkZ cs.2 ts + (L.map fun x ↦ F x * match x.1.shift with
        | 0 => d0
        | s + 1 => if s < cs.2.length then ts.getD s 0 else 0).sum ∧
    (L.foldl (lkShiftStep F) cs).2.length = cs.2.length
  | [], cs => by simp
  | x :: L, cs => by
    rw [List.foldl_cons]
    rcases hs : x.1.shift with _ | s
    · have he : lkShiftStep F cs x = (cs.1 + F x, cs.2) := by simp [lkShiftStep, hs]
      obtain ⟨h1, h2⟩ := lk_shift_fold F d0 ts L (cs.1 + F x, cs.2)
      rw [he]
      refine ⟨?_, h2⟩
      rw [h1, List.map_cons, List.sum_cons]
      simp only [hs]
      ring
    · have he : lkShiftStep F cs x = (cs.1, addAtSlot cs.2 s (F x)) := by simp [lkShiftStep, hs]
      obtain ⟨h1, h2⟩ := lk_shift_fold F d0 ts L (cs.1, addAtSlot cs.2 s (F x))
      rw [he]
      refine ⟨?_, by rw [h2, length_addAtSlot]⟩
      rw [h1, List.map_cons, List.sum_cons, lkZ_addAtSlot, length_addAtSlot]
      simp only [hs]
      split_ifs <;> ring

/-- A read's share of the word reads through `pointer`. -/
def lkRead (pointer : ℕ) (G : E → Form → E) (m : E) : Read → E
  | .word p scale => if p = pointer then G m scale else 0
  | _ => 0

/-- One read folded into the coefficient. -/
def lkReadStep (pointer : ℕ) (G : E → Form → E) (m : E) (coef : E) (read : Read) : E :=
  match read with
  | .word p scale => if p = pointer then coef + G m scale else coef
  | _ => coef

/-- One access's reads folded into the coefficient. -/
def lkReadsStep (pointer : ℕ) (G : E → Form → E) (coef : E) (x : Access × E) : E :=
  x.1.reads.foldl (lkReadStep pointer G x.2) coef

theorem lk_read_fold (pointer : ℕ) (G : E → Form → E) (m : E) : ∀ (R : List Read) (c : E),
    R.foldl (lkReadStep pointer G m) c = c + (R.map (lkRead pointer G m)).sum
  | [], c => by simp
  | r :: R, c => by
    rw [List.foldl_cons, lk_read_fold pointer G m R, List.map_cons, List.sum_cons]
    cases r with
    | word p scale => simp only [lkReadStep, lkRead]; split_ifs <;> ring
    | slot s scale => simp [lkReadStep, lkRead]
    | frame s scale => simp [lkReadStep, lkRead]
    | pc s scale => simp [lkReadStep, lkRead]

/-- The word reads through a pointer, folded into the coefficient. -/
theorem lk_reads_fold (pointer : ℕ) (G : E → Form → E) : ∀ (L : List (Access × E)) (c0 : E),
    L.foldl (lkReadsStep pointer G) c0 =
      c0 + (L.map fun x ↦ (x.1.reads.map (lkRead pointer G x.2)).sum).sum
  | [], c0 => by simp
  | x :: L, c0 => by
    rw [List.foldl_cons, lk_reads_fold pointer G L, lkReadsStep, lk_read_fold, List.map_cons,
      List.sum_cons]
    ring

theorem lkRead_mul (pointer : ℕ) (G : E → Form → E) (e m : E) (r : Read) :
    lkRead pointer (fun m scale ↦ e * G m scale) m r = e * lkRead pointer G m r := by
  cases r <;> simp only [lkRead] <;> (try split_ifs) <;> ring

/-- An access's gate on the row's values, `1` for none. -/
def lkGate (col : ℕ → E) (a : Access) : E := (a.gate.map col).getD 1

/-- The share of pointer column `k`, named `pointer`, of table `t`, at fixed functional values:
`D_0`, the window reads `ts` (`T_{s+1}` at `s`), `rest`, over `N` shifts. -/
def lkPtr (ch : LinkCh) (a : IdxAt) (omega act sHat sNext : E) (table : Table) (t : ℕ)
    (col : ℕ → E) (d0 rest : E) (ts : List E) (N pointer k : ℕ) : E :=
  match k with
  | 0 => act * (a.eqZetaR * sHat + a.shiftZetaR * sNext) * d0 * rest
  | 1 => omega * (a.xBc + col table.links.stateLink.fp * a.pFp) * d0 * rest
  | _ + 2 =>
    (((table.links.memory.zip (ch.mu.getD t [])).map fun x ↦ (x.1.reads.map (lkRead pointer
        (fun m scale ↦ omega * ch.etaMem * m * ch.gammaMem.getD 1 0 * a.m1 * scale.evaluate col)
        x.2)).sum).sum * d0 +
      (((table.links.memory.zip (ch.mu.getD t [])).filter (·.1.pointer = pointer)).map fun x ↦
        omega * lkGate col x.1 * ch.etaMem * x.2 * a.yMem * match x.1.shift with
          | 0 => d0
          | s + 1 => if s < N then ts.getD s 0 else 0).sum) * rest

section Step

variable (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : List E)
  (corner omega act sHat sNext : E) (table : Table) (t : ℕ) (col : ℕ → E) (d0 rest eq0Q : E)
  (ts : List E)

set_option maxRecDepth 100000 in
/-- **One pointer column** adds its share, weighed by `eq(q, ·)` at its index and the corner. -/
theorem lk_ptrStep (acc : LinkRowSide) (pointer k : ℕ) :
    let acc' := ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (pointer, k)
    lkVal d0 rest eq0Q ts acc' = lkVal d0 rest eq0Q ts acc + eqQ.getD acc.q 0 * corner *
        lkPtr ch a omega act sHat sNext table t col d0 rest ts acc.shifts.length pointer k ∧
      acc'.q = acc.q + 1 ∧ acc'.shifts.length = acc.shifts.length ∧ acc'.base = acc.base := by
  intro acc'
  rcases k with _ | _ | k
  · refine ⟨?_, rfl, rfl, rfl⟩
    simp only [acc', ptrStep, lkVal, lkPtr]
    ring
  · refine ⟨?_, rfl, rfl, rfl⟩
    simp only [acc', ptrStep, lkVal, lkPtr]
    ring
  · set e := eqQ.getD acc.q 0 * corner
    set G : E → Form → E := fun m scale ↦ omega * ch.etaMem * m * ch.gammaMem.getD 1 0 * a.m1 *
      scale.evaluate col
    set F : Access × E → E := fun x ↦ omega * lkGate col x.1 * ch.etaMem * x.2 * a.yMem
    set L := table.links.memory.zip (ch.mu.getD t [])
    set Lf := L.filter (·.1.pointer = pointer)
    set c1 := L.foldl (lkReadsStep pointer fun m scale ↦
      e * omega * ch.etaMem * m * ch.gammaMem.getD 1 0 * a.m1 * scale.evaluate col) acc.coef
    have hc : acc'.coef = (Lf.foldl (lkShiftStep fun x ↦
        e * omega * lkGate col x.1 * ch.etaMem * x.2 * a.yMem) (c1, acc.shifts)).1 := rfl
    have hsh : acc'.shifts = (Lf.foldl (lkShiftStep fun x ↦
        e * omega * lkGate col x.1 * ch.etaMem * x.2 * a.yMem) (c1, acc.shifts)).2 := rfl
    have hF : (fun x : Access × E ↦ e * omega * lkGate col x.1 * ch.etaMem * x.2 * a.yMem) =
        fun x ↦ e * F x := by funext x; simp only [F]; ring
    have hG : (fun (m : E) (scale : Form) ↦
        e * omega * ch.etaMem * m * ch.gammaMem.getD 1 0 * a.m1 * scale.evaluate col) =
        fun m scale ↦ e * G m scale := by funext m scale; simp only [G]; ring
    rw [hF] at hc hsh
    obtain ⟨hs1, hs2⟩ := lk_shift_fold (fun x ↦ e * F x) d0 ts Lf (c1, acc.shifts)
    refine ⟨?_, rfl, by rw [hsh]; exact hs2, rfl⟩
    have hb : acc'.base = acc.base := rfl
    simp only [lkVal]
    rw [hc, hsh, hb]
    rw [hs1]
    have hc1 : c1 = L.foldl (lkReadsStep pointer fun m scale ↦ e * G m scale) acc.coef := by
      simp only [c1, hG]
    rw [hc1, lk_reads_fold, lkPtr]
    have hr : (L.map fun x ↦ (x.1.reads.map (lkRead pointer (fun m scale ↦ e * G m scale) x.2)).sum).sum =
        e * (L.map fun x ↦ (x.1.reads.map (lkRead pointer G x.2)).sum).sum := by
      rw [← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun x _ ↦ ?_)
      rw [← List.sum_map_mul_left]
      exact congrArg List.sum (List.map_congr_left fun r _ ↦ lkRead_mul pointer G e x.2 r)
    have hs : (Lf.map fun x ↦ e * F x * match x.1.shift with
          | 0 => d0
          | s + 1 => if s < acc.shifts.length then ts.getD s 0 else 0).sum =
        e * (Lf.map fun x ↦ F x * match x.1.shift with
          | 0 => d0
          | s + 1 => if s < acc.shifts.length then ts.getD s 0 else 0).sum := by
      rw [← List.sum_map_mul_left]
      exact congrArg List.sum (List.map_congr_left fun x _ ↦ by ring)
    rw [hr, hs]
    simp only [F, G, Lf, L]
    ring

/-- **A table's pointer columns** add their shares in order. -/
theorem lk_ptrFold : ∀ (L : List (ℕ × ℕ)) (acc : LinkRowSide),
    let acc' := L.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) acc
    lkVal d0 rest eq0Q ts acc' = lkVal d0 rest eq0Q ts acc + ∑ j ∈ range L.length,
        eqQ.getD (acc.q + j) 0 * corner * lkPtr ch a omega act sHat sNext table t col d0 rest ts
          acc.shifts.length (L.getD j (0, 0)).1 (L.getD j (0, 0)).2 ∧
      acc'.q = acc.q + L.length ∧ acc'.shifts.length = acc.shifts.length ∧ acc'.base = acc.base
  | [], acc => by simp
  | (p, k) :: L, acc => by
    intro acc'
    obtain ⟨h1, h2, h3, h4⟩ := lk_ptrStep layout ch a eqQ point corner omega act sHat sNext table t
      col d0 rest eq0Q ts acc p k
    obtain ⟨g1, g2, g3, g4⟩ := lk_ptrFold L
      (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (p, k))
    have ha : acc' = L.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col)
        (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (p, k)) := rfl
    rw [ha]
    refine ⟨?_, by rw [g2, h2, List.length_cons]; omega, by rw [g3, h3], by rw [g4, h4]⟩
    rw [g1, h1, h2, h3, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    have hs : ∑ j ∈ range L.length, eqQ.getD (acc.q + 1 + j) 0 * corner *
        lkPtr ch a omega act sHat sNext table t col d0 rest ts acc.shifts.length (L.getD j (0, 0)).1
          (L.getD j (0, 0)).2 = ∑ j ∈ range L.length, eqQ.getD (acc.q + (j + 1)) 0 * corner *
        lkPtr ch a omega act sHat sNext table t col d0 rest ts acc.shifts.length (L.getD j (0, 0)).1
          (L.getD j (0, 0)).2 :=
      sum_congr rfl fun j _ ↦ by rw [show acc.q + 1 + j = acc.q + (j + 1) by omega]
    rw [hs]
    ring

end Step

/-! ## The tables -/

/-- The values the tables before `t` take from the message. -/
def lkOff (layout : Layout) (t : ℕ) : ℕ :=
  ∑ t' ∈ range t, (nonPointerOf layout t' (layout.tables.getD t' default)).length

/-- Table `t`'s values as the row side reads them from the message. -/
def lkVals (layout : Layout) (message : List E) (t : ℕ) : List E :=
  let table := layout.tables.getD t default
  let columns := nonPointerOf layout t table
  let sent := columns.zip ((((rowStart layout message).sent).drop (lkOff layout t)).take
    columns.length)
  (List.range table.width).map fun c ↦ (sent.lookup c).getD 0

/-- The widest shift over the tables, the row side's shift count. -/
def lkMaxShift (layout : Layout) : ℕ := layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0

/-- Table `t`'s base terms. -/
def lkBase (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump chi message : List E) (t : ℕ) : E :=
  tableBaseOf ch a jump (chi.take (heightOf layout t)) (heightOf layout t) (omegaOf layout ch chi t)
    (layout.tables.getD t default) t (lkVals layout message t)

/-- Pointer column `k` of table `t`'s share. -/
def lkPtrAt (layout : Layout) (ch : LinkCh) (a : IdxAt) (chi message : List E) (d0 rest : E)
    (ts : List E) (t k : ℕ) : E :=
  let table := layout.tables.getD t default
  let col := fun (c : ℕ) ↦ (lkVals layout message t).getD c 0
  let state := table.links.stateLink
  lkPtr ch a (omegaOf layout ch chi t) (lessThan (chi.take (heightOf layout t)) (layout.tableRows.getD t 0))
    (ch.stateGamma (col state.pc) (col state.fp))
    (ch.stateGamma (state.next.1.evaluate col) (state.next.2.evaluate col)) table t col d0 rest ts
    (lkMaxShift layout) ((ptrsOf layout t).getD k 0) k

/-- The fold over the first `n` tables. -/
theorem lk_rowFold (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi message : List E) (d0 rest eq0Q : E)
    (ts : List E) : ∀ n : ℕ,
    let rs := ((List.range n).map fun t ↦ (layout.tables.getD t default, t)).foldl
      (rowStep layout ch a jump eqQ chi) (rowStart layout message)
    lkVal d0 rest eq0Q ts rs = ∑ t ∈ range n, (eq0Q * cornerAt layout chi t *
        lkBase layout ch a jump chi message t + ∑ k ∈ range (ptrsOf layout t).length,
          eqQ.getD (qBase layout t + k) 0 * cornerAt layout chi t *
            lkPtrAt layout ch a chi message d0 rest ts t k) ∧
      rs.q = qBase layout n ∧ rs.shifts.length = lkMaxShift layout ∧ rs.sent = (rowStart layout message).sent.drop (lkOff layout n)
  | 0 => by
    simp [rowStart, qBase, lkVal, lkZ, lkOff, lkMaxShift, sumE_zipWith_replicate_zero]
  | n + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := lk_rowFold layout ch a jump eqQ chi message d0 rest eq0Q ts n
    rw [List.range_succ, List.map_append, List.foldl_append, List.map_singleton, List.foldl_cons,
      List.foldl_nil]
    set rs := ((List.range n).map fun t ↦ (layout.tables.getD t default, t)).foldl
      (rowStep layout ch a jump eqQ chi) (rowStart layout message)
    set table := layout.tables.getD n default
    set h := layout.tableLogHeights.getD n 0
    set P := chi.take h
    set C := prodE ((chi.drop h).map (1 + ·))
    set len := (nonPointerOf layout n table).length
    set vals := (List.range table.width).map fun c ↦
      (((nonPointerOf layout n table).zip (rs.sent.take len)).lookup c).getD 0
    set col := fun (c : ℕ) ↦ vals.getD c 0
    set st := table.links.stateLink
    set O := omegaAt (ch.theta.getD n 0) (ch.tau.take h) P (layout.tableRows.getD n 0)
    set A := lessThan P (layout.tableRows.getD n 0)
    set SH := ch.stateGamma (col st.pc) (col st.fp)
    set SN := ch.stateGamma (st.next.1.evaluate col) (st.next.2.evaluate col)
    set TB := tableBaseOf ch a jump P h O table n vals
    set acc0 : LinkRowSide := { rs with base := rs.base + C * TB, sent := rs.sent.drop len }
    set acc1 := ((layout.tables.map (·.links.pointers)).getD n []).zipIdx.foldl
      (ptrStep layout ch a eqQ P C O A SH SN table n col) acc0
    have hstep : rowStep layout ch a jump eqQ chi rs (table, n) =
        { acc1 with columns := acc1.columns ++ [(P, (nonPointerOf layout n table).zip (rs.sent.take len))] } :=
      rfl
    obtain ⟨p1, p2, p3, p4⟩ := lk_ptrFold layout ch a eqQ P C O A SH SN table n col d0 rest eq0Q ts
      ((layout.tables.map (·.links.pointers)).getD n []).zipIdx acc0
    have hvals : vals = lkVals layout message n := by
      simp only [vals, lkVals, h4, len, table]
    have hcol : col = fun c ↦ (lkVals layout message n).getD c 0 := by simp only [col, hvals]
    have hsent1 : acc1.sent = rs.sent.drop len := by
      simp only [acc1, foldl_ptrStep_sent, acc0]
    rw [hstep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hv : lkVal d0 rest eq0Q ts { acc1 with columns := acc1.columns ++
          [(P, (nonPointerOf layout n table).zip (rs.sent.take len))] } = lkVal d0 rest eq0Q ts acc1 := rfl
      rw [hv, p1, zipIdx_ptrsOf, sum_range_succ, ← h1]
      have h0 : lkVal d0 rest eq0Q ts acc0 = lkVal d0 rest eq0Q ts rs + eq0Q * C * TB := by
        simp only [lkVal, acc0]; ring
      rw [h0]
      have hq : acc0.q = qBase layout n := h2
      have hN : acc0.shifts.length = lkMaxShift layout := h3
      rw [hq, hN]
      have hb : TB = lkBase layout ch a jump chi message n := by
        simp only [TB, lkBase, ← hvals, P, h, O, omegaOf, heightOf, table]
      have hc : C = cornerAt layout chi n := rfl
      rw [hb, ← hc, add_assoc]
      refine congrArg (fun z ↦ lkVal d0 rest eq0Q ts rs + (eq0Q * C * lkBase layout ch a jump chi message n + z))
        (sum_congr rfl fun k hk ↦ ?_)
      have hk' : k < (ptrsOf layout n).length := mem_range.mp hk
      rw [zipIdx_getD_fst _ (by simpa [ptrsOf] using hk')]
      have hsnd : (((layout.tables.map (·.links.pointers)).getD n []).zipIdx.getD k (0, 0)).2 = k := by
        rw [List.getD_eq_getElem _ _ (by simpa [ptrsOf] using hk'), List.getElem_zipIdx]
        simp
      rw [hsnd]
      simp only [lkPtrAt, O, A, SH, SN, hcol, st, P, h, omegaOf, heightOf, ptrsOf, table, lkMaxShift, C]
    · show acc1.q = _
      rw [p2, zipIdx_ptrsOf, qBase_succ]
      exact congrArg (· + _) h2
    · show acc1.shifts.length = _
      rw [p3]
      exact h3
    · show acc1.sent = _
      rw [hsent1, h4, List.drop_drop]
      simp only [lkOff, sum_range_succ, len, table]

/-- **`last` over the whole row side**: each table's base terms under `eq(0, q)` and its corner, and
each pointer column's share under `eq(q, ·)` at its index and the corner. -/
theorem lkVal_rowSideOf (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi message : List E) (d0 rest eq0Q : E)
    (ts : List E) :
    lkVal d0 rest eq0Q ts (rowSideOf layout ch a jump eqQ chi message) =
      ∑ t ∈ range layout.tables.length, (eq0Q * cornerAt layout chi t *
        lkBase layout ch a jump chi message t + ∑ k ∈ range (ptrsOf layout t).length,
          eqQ.getD (qBase layout t + k) 0 * cornerAt layout chi t *
            lkPtrAt layout ch a chi message d0 rest ts t k) := by
  have h := (lk_rowFold layout ch a jump eqQ chi message d0 rest eq0Q ts layout.tables.length).1
  rw [← zipIdx_eq_map] at h
  exact h

end

end LeanVM.Protocol.Relation
