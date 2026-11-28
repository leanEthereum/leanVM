/-
  LeanVM.Prover.Complete.Link.TailRowFold

  The verifier's row side on the honest message: table by table, its coefficient, shifts,
  certificate weight and base are the honest pointer columns' and base terms'.
-/

module

public import LeanVM.Prover.Complete.Link.TailRowTable

/-!
# The verifier's row side, table by table

`vTableStep_eq` (by `rfl`): one table's step is its pointers' fold from the table's values
(`vColFn`) and base. `rowSide_honest`: on the honest message's values, with the challenges and the
index side's values the honest prover's, the fold over the tables gives the coefficient, shifts and
certificate weight summed over the tables' pointer columns `Σ_t Σ_k eq(q*, q_t + k)·…` of
`colSpec`, and the base terms' total `linkBase`. It reads `ω` through `OmegaMle`, the extension
of `omegaTable` as `omegaAt` (proved with the index side's closed forms).
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

/-- **`ω`'s closed form is `omegaTable`'s extension** (`omega_at`, `link.rs`). -/
def OmegaMle : Prop :=
  ∀ (theta : E) (tau pt : List E) (n : ℕ), pt.length ≤ tau.length → n ≤ 2 ^ pt.length →
    mleA (omegaTable theta tau pt.length n) pt = omegaAt theta (tau.take pt.length) pt n

/-- The values the verifier reads for a table, from the values `sent` not yet read. -/
def vValuesOf (table : Table) (cols : List ℕ) (sent : List E) : List E :=
  (List.range table.width).map fun c ↦ ((cols.zip (sent.take cols.length)).lookup c).getD 0

/-- **One table's step**, its pointers' fold, its base `TB`. -/
theorem vTableStep_eq (layout : Layout) (ch : LinkChallenges) (chi jump : List E)
    (eqZetaR shiftZetaR xBc pFp yMem m1 eq0R : E) (eqQ : List E) (acc : LinkRowSide) (table : Table)
    (t : ℕ) (TB : E) :
    let h := layout.tableLogHeights.getD t 0
    let point := chi.take h
    let corner := prodE ((chi.drop h).map (1 + ·))
    let ptrs := (layout.tables.map (·.links.pointers)).getD t []
    let cols := (List.range table.width).filter fun c ↦ !ptrs.contains c
    let values := vValuesOf table cols acc.sent
    let col := fun c ↦ values.getD c 0
    let omega := omegaAt (ch.theta.getD t 0) (ch.tau.take h) point (layout.tableRows.getD t 0)
    let act := lessThan point (layout.tableRows.getD t 0)
    let sg := fun (a b : E) ↦ 1 + ch.gammaState.getD 0 0 * a + ch.gammaState.getD 1 0 * b
    let links := table.links
    let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
    let accessValue := fun (a : Access) ↦
      ch.gammaMem.getD 0 0 * a.address.evaluate col + ch.gammaMem.getD 3 0 +
        ch.gammaMem.getD 1 0 * a.value.evaluate col
    let memory := sumE ((links.memory.zip (ch.mu.getD t [])).map fun (a, m) ↦ m * gateOf a * accessValue a)
    let bc := links.bytecodeLink
    let rBc := ch.slot.getD 1 0 * col bc.pc + ch.slot.getD 2 0 + ch.slot.getD 3 0 * gpow bc.opcode +
      sumE (bc.operands.map fun (slots, f) ↦ ch.slot.getD (slots.headD 0) 0 * f.evaluate col)
    let tableBase := omega * eq0R * (ch.etaMem * memory + ch.etaBc * rBc)
    let tableBase :=
      if 0 < table.nConstraints then
        tableBase + eqEval (ch.tau.take h) point * sumE (List.zipWith (· * ·) jump (table.constraints values))
      else tableBase
    TB = tableBase →
    let r := ptrs.zipIdx.foldl (vPointerStep layout ch eqQ t point corner act omega eqZetaR shiftZetaR
      (sg (col links.stateLink.pc) (col links.stateLink.fp))
      (sg (links.stateLink.next.1.evaluate col) (links.stateLink.next.2.evaluate col)) xBc pFp yMem m1
      col links (ch.mu.getD t []))
      { acc with base := acc.base + corner * TB, sent := acc.sent.drop cols.length }
    vTableStep layout ch chi jump eqZetaR shiftZetaR xBc pFp yMem m1 eq0R eqQ acc (table, t) =
      { r with columns := r.columns ++ [(point, cols.zip (acc.sent.take cols.length))] } := by
  intro h point corner ptrs cols values col omega act sg links gateOf accessValue memory bc rBc
    tableBase0 tableBase hTB
  subst hTB
  rfl

theorem inline_base (ch : LinkChallenges) (links : Links) (muT : List E) (col : ℕ → E)
    (omega eq0R : E) :
    (let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
    let accessValue := fun (a : Access) ↦
      ch.gammaMem.getD 0 0 * a.address.evaluate col + ch.gammaMem.getD 3 0 +
        ch.gammaMem.getD 1 0 * a.value.evaluate col
    let memory := sumE ((links.memory.zip muT).map fun (a, m) ↦ m * gateOf a * accessValue a)
    let bc := links.bytecodeLink
    let rBc := ch.slot.getD 1 0 * col bc.pc + ch.slot.getD 2 0 + ch.slot.getD 3 0 * gpow bc.opcode +
      sumE (bc.operands.map fun (slots, f) ↦ ch.slot.getD (slots.headD 0) 0 * f.evaluate col)
    omega * eq0R * (ch.etaMem * memory + ch.etaBc * rBc)) =
      omega * eq0R * payloadAt ch links muT col := by
  unfold payloadAt
  dsimp only

/-! ## Helpers -/

theorem payloadAt_congr {t : ℕ} (hf : TableFacts t) (ch : LinkChallenges) (mu : List E)
    {col col' : ℕ → E} (h : ∀ c ∈ nonPtr t, col c = col' c) :
    payloadAt ch (tables.getD t default).links mu col = payloadAt ch (tables.getD t default).links mu col' := by
  unfold payloadAt
  have e1 : ((tables.getD t default).links.memory.zip mu).map (fun am ↦ am.2 * (am.1.gate.map col).getD 1 *
      (ch.gammaMem.getD 0 0 * am.1.address.evaluate col + ch.gammaMem.getD 3 0 +
        ch.gammaMem.getD 1 0 * am.1.value.evaluate col)) =
      ((tables.getD t default).links.memory.zip mu).map (fun am ↦ am.2 * (am.1.gate.map col').getD 1 *
      (ch.gammaMem.getD 0 0 * am.1.address.evaluate col' + ch.gammaMem.getD 3 0 +
        ch.gammaMem.getD 1 0 * am.1.value.evaluate col')) := by
    refine List.map_congr_left fun am ham ↦ ?_
    have ha := (List.of_mem_zip ham).1
    rw [evaluate_congr (fun m hm v hv ↦ h v (formIn_spec (hf.address _ ha) m hm v hv)),
      evaluate_congr (fun m hm v hv ↦ h v (formIn_spec (hf.value _ ha) m hm v hv))]
    rcases hg : am.1.gate with _ | g
    · rfl
    · simp [h g (hf.gate _ ha g hg)]
  have e2 : (tables.getD t default).links.bytecodeLink.operands.map (fun so ↦
      ch.slot.getD (so.1.headD 0) 0 * so.2.evaluate col) =
      (tables.getD t default).links.bytecodeLink.operands.map (fun so ↦
      ch.slot.getD (so.1.headD 0) 0 * so.2.evaluate col') := by
    refine List.map_congr_left fun so hso ↦ ?_
    rw [evaluate_congr (fun m hm v hv ↦ h v (formIn_spec (hf.operands _ hso) m hm v hv))]
  rw [e1, e2, h _ hf.bcPc]

theorem lookup_zip_map (f : ℕ → E) : ∀ (cols : List ℕ), cols.Nodup → ∀ c ∈ cols,
    (cols.zip (cols.map f)).lookup c = some (f c)
  | [], _, c, hc => absurd hc List.not_mem_nil
  | a :: cols, hnd, c, hc => by
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.zip_cons_cons, List.lookup]
    by_cases h : c = a
    · subst h; simp
    · have : (c == a) = false := by simpa using h
      rw [this]
      exact lookup_zip_map f cols hnd.2 c (by simpa [h] using hc)

theorem tailRow_take_drop_flatMap (F : ℕ → List E) {n k : ℕ} (hk : k < n) :
    ((((List.range n).flatMap F).drop ((List.range k).map fun t ↦ (F t).length).sum).take
      (F k).length) = F k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - k - 1, by omega⟩
  have hl : ((List.range k).flatMap F).length = ((List.range k).map fun t ↦ (F t).length).sum := by
    simp [List.length_flatMap]
  rw [List.range_add, List.range_succ, List.flatMap_append, List.flatMap_append, List.append_assoc,
    List.drop_left' hl]
  simp

/-! ## One table's step, its fields -/

/-- **One table's step, its fields**: its pointers summed (`foldl_vPointerStep`). -/
theorem vTableStep_fields (layout : Layout) (ch : LinkChallenges) (chi jump : List E)
    (eqZetaR shiftZetaR xBc pFp yMem m1 eq0R : E) (eqQ : List E) (acc : LinkRowSide) (table : Table)
    (t : ℕ)
    (hS : ∀ pk ∈ ((layout.tables.map (·.links.pointers)).getD t []).zipIdx,
      ∀ am ∈ accessesAt table.links (ch.mu.getD t []) pk.1, am.1.shift ≤ acc.shifts.length)
    (hlow : ∀ pk ∈ ((layout.tables.map (·.links.pointers)).getD t []).zipIdx, pk.2 < 2 →
      accessesAt table.links (ch.mu.getD t []) pk.1 = []) :
    let h := layout.tableLogHeights.getD t 0
    let point := chi.take h
    let corner := prodE ((chi.drop h).map (1 + ·))
    let ptrs := (layout.tables.map (·.links.pointers)).getD t []
    let cols := (List.range table.width).filter fun c ↦ !ptrs.contains c
    let values := vValuesOf table cols acc.sent
    let col := fun c ↦ values.getD c 0
    let omega := omegaAt (ch.theta.getD t 0) (ch.tau.take h) point (layout.tableRows.getD t 0)
    let act := lessThan point (layout.tableRows.getD t 0)
    let sg := fun (a b : E) ↦ 1 + ch.gammaState.getD 0 0 * a + ch.gammaState.getD 1 0 * b
    let links := table.links
    let sHat := sg (col links.stateLink.pc) (col links.stateLink.fp)
    let sNext := sg (links.stateLink.next.1.evaluate col) (links.stateLink.next.2.evaluate col)
    let tableBase :=
      if 0 < table.nConstraints then
        omega * eq0R * payloadAt ch links (ch.mu.getD t []) col +
          eqEval (ch.tau.take h) point * sumE (List.zipWith (· * ·) jump (table.constraints values))
      else omega * eq0R * payloadAt ch links (ch.mu.getD t []) col
    let R := vTableStep layout ch chi jump eqZetaR shiftZetaR xBc pFp yMem m1 eq0R eqQ acc (table, t)
    R.q = acc.q + ptrs.length ∧ R.sent = acc.sent.drop cols.length ∧
      R.coef = acc.coef + (ptrs.zipIdx.map fun pk ↦ eqQ.getD (acc.q + pk.2) 0 * corner *
        vCoef ch act omega eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1 col links
          (ch.mu.getD t []) pk.1 pk.2).sum ∧
      R.certWeight = acc.certWeight + (ptrs.zipIdx.map fun pk ↦
        eqQ.getD (acc.q + pk.2) 0 * corner * omega * ch.eps.getD (acc.q + pk.2) 0).sum ∧
      R.shifts.length = acc.shifts.length ∧
      (∀ s < acc.shifts.length, R.shifts.getD s 0 = acc.shifts.getD s 0 +
        (ptrs.zipIdx.map fun pk ↦ eqQ.getD (acc.q + pk.2) 0 * corner *
          vShift ch omega yMem col links (ch.mu.getD t []) pk.1 s).sum) ∧
      R.base = acc.base + corner * tableBase := by
  intro h point corner ptrs cols values col omega act sg links sHat sNext tableBase R
  have hbase : tableBase = (let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
      let accessValue := fun (a : Access) ↦
        ch.gammaMem.getD 0 0 * a.address.evaluate col + ch.gammaMem.getD 3 0 +
          ch.gammaMem.getD 1 0 * a.value.evaluate col
      let memory := sumE ((links.memory.zip (ch.mu.getD t [])).map fun (a, m) ↦ m * gateOf a * accessValue a)
      let bc := links.bytecodeLink
      let rBc := ch.slot.getD 1 0 * col bc.pc + ch.slot.getD 2 0 + ch.slot.getD 3 0 * gpow bc.opcode +
        sumE (bc.operands.map fun (slots, f) ↦ ch.slot.getD (slots.headD 0) 0 * f.evaluate col)
      let tableBase := omega * eq0R * (ch.etaMem * memory + ch.etaBc * rBc)
      if 0 < table.nConstraints then
        tableBase + eqEval (ch.tau.take h) point * sumE (List.zipWith (· * ·) jump (table.constraints values))
      else tableBase) := by
    simp only [tableBase, inline_base]
  set acc1 : LinkRowSide := { acc with base := acc.base + corner * tableBase, sent := acc.sent.drop cols.length }
  have e : R = { (ptrs.zipIdx.foldl (vPointerStep layout ch eqQ t point corner act omega eqZetaR
      shiftZetaR sHat sNext xBc pFp yMem m1 col links (ch.mu.getD t [])) acc1) with
      columns := (ptrs.zipIdx.foldl (vPointerStep layout ch eqQ t point corner act omega eqZetaR
        shiftZetaR sHat sNext xBc pFp yMem m1 col links (ch.mu.getD t [])) acc1).columns ++
          [(point, cols.zip (acc.sent.take cols.length))] } :=
    vTableStep_eq layout ch chi jump eqZetaR shiftZetaR xBc pFp yMem m1 eq0R eqQ acc table t tableBase hbase
  obtain ⟨i1, i2, i3, -, i5, i6, i7, i8⟩ := foldl_vPointerStep layout ch eqQ t point corner act omega
    eqZetaR shiftZetaR sHat sNext xBc pFp yMem m1 col links (ch.mu.getD t []) acc.q acc.shifts.length
    ptrs 0 acc1 (by simp [acc1]) rfl hS hlow
  rw [e]
  refine ⟨i1, i3, ?_, ?_, i7, fun s hs ↦ ?_, i2⟩
  · rw [i5]
  · rw [i6]
  · rw [i8 s hs]

end LeanVM.Prover.Complete

end
