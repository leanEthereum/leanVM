/-
  LeanVM.Protocol.Relation.Link.RowDeg

  The row summand's degree in each row and pointer-column variable: `LinkSummandFacts.row_deg`.
-/

module

public import LeanVM.Protocol.Relation.Link.Summand
public import LeanVM.Protocol.Relation.Link.PolyDeg

/-!
# The row summand's degrees

`row_deg_of_summand`: on any stack, `rowSummand` is of degree at most `max(d + 2, 4)` in each row
variable and `max(d + 1, 3)` in each pointer-column variable, the row side's round degrees
(`rowDegrees`, `roundCoefficients`).

Fix every coordinate of `x = χ ++ q_point` but one, `z`. Per table `t` of height `h`:

* `z` a row variable below `h`: the table's corner `Π_{j ≥ h} (1 + χ_j)` is constant, and its row
  point's functions (`ω`, `less_than`, `eq(τ, ·)`, the values `rowMle`) are of degree one;
* `z` a row variable at or past `h`: the corner is of degree one, the point constant;
* `z` a pointer-column variable: both constant, but `eq_kernel(q_point)`'s entries and `eq0Q` are of
  degree one.

So the row side's accumulators (`RSInv`) stay within `coef, shifts ≤ 2`, `certWeight ≤ 1`, `base ≤ 4`
for a row variable, and `coef, shifts, certWeight ≤ 1`, `base` constant for a pointer variable:
the table's forms are of degree at most two, its next and read scales linear, `JUMP`'s identities
quadratic (`tables_ok`, `tables_constraints`). The bit-slices are of degree one, so the values the
functionals read are, and `lastOf_deg` concludes.
-/

namespace LeanVM.Protocol.Relation.RowPoly

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Protocol.Relation Finset

@[expose] public section

/-! ## The deployed tables' degrees -/

/-- A read's scale is linear. -/
def readOk : Read → Bool
  | .word _ s => decide (Form.deg s ≤ 1)
  | _ => true

/-- An access's address and value are of degree at most two, its reads' scales linear. -/
def accessOk (acc : Access) : Bool :=
  decide (Form.deg acc.address ≤ 2) && decide (Form.deg acc.value ≤ 2) && acc.reads.all readOk

/-- A table's successor state is linear, its operand forms and accesses of degree at most two. -/
def tableOk (table : Table) : Bool :=
  decide (Form.deg table.links.stateLink.next.1 ≤ 1) &&
    decide (Form.deg table.links.stateLink.next.2 ≤ 1) &&
    table.links.bytecodeLink.operands.all (fun op ↦ decide (Form.deg op.2 ≤ 2)) &&
    table.links.memory.all accessOk

theorem tables_ok : tables.all tableOk = true := by decide +kernel

/-- What the row side's degrees need of a table. -/
structure TableFacts (table : Table) : Prop where
  next1 : Form.deg table.links.stateLink.next.1 ≤ 1
  next2 : Form.deg table.links.stateLink.next.2 ≤ 1
  operands : ∀ op ∈ table.links.bytecodeLink.operands, Form.deg op.2 ≤ 2
  address : ∀ acc ∈ table.links.memory, Form.deg acc.address ≤ 2
  value : ∀ acc ∈ table.links.memory, Form.deg acc.value ≤ 2
  reads : ∀ acc ∈ table.links.memory, ∀ p s, Read.word p s ∈ acc.reads → Form.deg s ≤ 1
  constraints : table.constraints = jumpConstraints ∨ table.constraints = fun _ ↦ []

theorem tables_constraints {table : Table} (h : table ∈ tables) :
    table.constraints = jumpConstraints ∨ table.constraints = fun _ ↦ [] := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  have hi6 : i < 6 := by rw [tables_length] at hi; exact hi
  interval_cases i <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem tableFacts_of_mem {table : Table} (h : table ∈ tables) : TableFacts table := by
  have hok := List.all_eq_true.mp tables_ok table h
  simp only [tableOk, accessOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hok
  refine ⟨h1, h2, h3, fun acc ha ↦ (h4 acc ha).1.1, fun acc ha ↦ (h4 acc ha).1.2,
    fun acc ha p s hr ↦ ?_, tables_constraints h⟩
  simpa [readOk] using (h4 acc ha).2 _ hr

/-! ## Small facts -/

theorem polyIn_ite (P : Prop) [Decidable P] {X Y : E → E} {d : ℕ} (hX : P → PolyIn X d)
    (hY : ¬P → PolyIn Y d) : PolyIn (fun c ↦ if P then X c else Y c) d := by
  by_cases h : P
  · exact (hX h).congr fun c ↦ by simp [h]
  · exact (hY h).congr fun c ↦ by simp [h]

theorem lookup_zip_map (g : ℕ → E) (x : ℕ) :
    ∀ l : List ℕ, List.lookup x (l.zip (l.map g)) = if x ∈ l then some (g x) else none
  | [] => by simp
  | y :: l => by
    rw [List.map_cons, List.zip_cons_cons, List.lookup_cons, lookup_zip_map g x l]
    by_cases h : x = y
    · subst h; simp
    · rw [beq_false_of_ne h]
      simp [h]

theorem height_le (layout : Layout) (t : ℕ) :
    layout.tableLogHeights.getD t 0 ≤ linkRows layout := by
  unfold linkRows
  rw [List.getD_eq_getElem?_getD]
  rcases h : layout.tableLogHeights[t]? with _ | x
  · exact Nat.zero_le _
  · exact (le_foldl_max _ 0).2 x (List.mem_of_getElem? h)

/-! ## The row side's accumulators -/

/-- The row side's accumulators within their degrees. -/
structure RSInv (A : E → LinkRowSide) (Bc Bw Bb : ℕ) : Prop where
  coef : PolyIn (fun c ↦ (A c).coef) Bc
  shifts : Ent (fun c ↦ (A c).shifts) Bc
  cw : PolyIn (fun c ↦ (A c).certWeight) Bw
  base : PolyIn (fun c ↦ (A c).base) Bb
  q : ∀ c, (A c).q = (A 0).q

theorem RSInv.of_eq {A B : E → LinkRowSide} {Bc Bw Bb : ℕ} (h : RSInv B Bc Bw Bb)
    (h1 : ∀ c, (A c).coef = (B c).coef) (h2 : ∀ c, (A c).shifts = (B c).shifts)
    (h3 : ∀ c, (A c).certWeight = (B c).certWeight) (h4 : ∀ c, (A c).base = (B c).base)
    (h5 : ∀ c, (A c).q = (B c).q) : RSInv A Bc Bw Bb where
  coef := h.coef.congr fun c ↦ (h1 c).symm
  shifts := ⟨fun c ↦ by beta_reduce; rw [h2, h2, h.shifts.1 c], fun i ↦ (h.shifts.2 i).congr fun c ↦ by
    beta_reduce; rw [h2]⟩
  cw := h.cw.congr fun c ↦ (h3 c).symm
  base := h.base.congr fun c ↦ (h4 c).symm
  q := fun c ↦ by rw [h5, h5, h.q c]

/-! ## One pointer column -/

/-- `ptrStep`'s reads of the word through `pointer`. -/
def readCoef (ch : LinkCh) (a : IdxAt) (e omega : E) (table : Table) (t pointer : ℕ)
    (col : ℕ → E) (coef : E) : E :=
  (table.links.memory.zip (ch.mu.getD t [])).foldl (fun coef (access, m) ↦
    access.reads.foldl (fun coef read ↦
      match read with
      | .word p scale =>
        if p = pointer then
          coef + e * omega * ch.etaMem * m * ch.gammaMem.getD 1 0 * a.m1 * scale.evaluate col
        else coef
      | _ => coef) coef) coef

/-- `ptrStep`'s accesses through `pointer`, at their shifts. -/
def memShifts (ch : LinkCh) (a : IdxAt) (e omega : E) (table : Table) (t pointer : ℕ)
    (col : ℕ → E) (cs : E × List E) : E × List E :=
  ((table.links.memory.zip (ch.mu.getD t [])).filter (·.1.pointer = pointer)).foldl
    (fun (cs : E × List E) (access, m) ↦
      let c := e * omega * (access.gate.map col).getD 1 * ch.etaMem * m * a.yMem
      match access.shift with
      | 0 => (cs.1 + c, cs.2)
      | s + 1 => (cs.1, addAtSlot cs.2 s c)) cs

section PtrStep

variable (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : List E)
  (corner omega act sHat sNext : E) (table : Table) (t : ℕ) (col : ℕ → E) (acc : LinkRowSide)
  (pointer : ℕ)

theorem ptrStep_zero :
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (pointer, 0)).coef =
        acc.coef + eqQ.getD acc.q 0 * corner * act * (a.eqZetaR * sHat + a.shiftZetaR * sNext) ∧
      (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc
        (pointer, 0)).shifts = acc.shifts := ⟨rfl, rfl⟩

theorem ptrStep_one :
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (pointer, 1)).coef =
        acc.coef + eqQ.getD acc.q 0 * corner * omega *
          (a.xBc + col table.links.stateLink.fp * a.pFp) ∧
      (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc
        (pointer, 1)).shifts = acc.shifts := ⟨rfl, rfl⟩

theorem ptrStep_two (kk : ℕ) :
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc
        (pointer, kk + 2)).coef =
        (memShifts ch a (eqQ.getD acc.q 0 * corner) omega table t pointer col
          (readCoef ch a (eqQ.getD acc.q 0 * corner) omega table t pointer col acc.coef,
            acc.shifts)).1 ∧
      (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc
        (pointer, kk + 2)).shifts =
        (memShifts ch a (eqQ.getD acc.q 0 * corner) omega table t pointer col
          (readCoef ch a (eqQ.getD acc.q 0 * corner) omega table t pointer col acc.coef,
            acc.shifts)).2 := ⟨rfl, rfl⟩

theorem ptrStep_rest (kk : ℕ) :
    let r := ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (pointer, kk)
    r.certWeight = acc.certWeight + eqQ.getD acc.q 0 * corner * omega * ch.eps.getD acc.q 0 ∧
      r.q = acc.q + 1 ∧ r.base = acc.base ∧ r.sent = acc.sent ∧
      r.pieces = acc.pieces ++ [⟨some ((layout.placements.getD
        (globalColumnBases.getD t 0 + pointer) none).getD default), point, eqQ.getD acc.q 0⟩] := by
  rcases kk with _ | _ | kk <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end PtrStep

theorem readCoef_deg (ch : LinkCh) (a : IdxAt) (e omega : E → E) (table : Table) (t pointer : ℕ)
    (col : E → ℕ → E) (coef : E → E) {Bc de dp : ℕ} (he : PolyIn e de)
    (homega : PolyIn omega dp) (hcol : ∀ i, PolyIn (fun c ↦ col c i) dp)
    (hreads : ∀ acc ∈ table.links.memory, ∀ p s, Read.word p s ∈ acc.reads → Form.deg s ≤ 1)
    (hc : de + 2 * dp ≤ Bc) (hcoef : PolyIn coef Bc) :
    PolyIn (fun c ↦ readCoef ch a (e c) (omega c) table t pointer (col c) (coef c)) Bc := by
  unfold readCoef
  refine polyIn_foldl _ _ (fun x hx f hf ↦ ?_) _ hcoef
  obtain ⟨acc, m⟩ := x
  have hacc : acc ∈ table.links.memory := (List.of_mem_zip hx).1
  dsimp only
  refine polyIn_foldl _ _ (fun rd hrd g hg ↦ ?_) _ hf
  cases rd with
  | word p s =>
    dsimp only
    refine polyIn_ite (p = pointer) (fun _ ↦ ?_) (fun _ ↦ hg)
    have hs := (polyIn_evaluate s col dp hcol).mono
      (Nat.mul_le_mul_right dp (hreads acc hacc p s hrd))
    exact hg.add_le ((((((((he.mul homega).mul (PolyIn.const ch.etaMem)).mul (PolyIn.const m)).mul
      (PolyIn.const (ch.gammaMem.getD 1 0))).mul (PolyIn.const a.m1)).mul hs)).mono (by omega))
  | slot => exact hg
  | frame => exact hg
  | pc => exact hg

theorem memShifts_deg (ch : LinkCh) (a : IdxAt) (e omega : E → E) (table : Table)
    (t pointer : ℕ) (col : E → ℕ → E) (cs : E → E × List E) {Bc de dp : ℕ} (he : PolyIn e de)
    (homega : PolyIn omega dp) (hcol : ∀ i, PolyIn (fun c ↦ col c i) dp)
    (hc : de + 2 * dp ≤ Bc) (h1 : PolyIn (fun c ↦ (cs c).1) Bc) (h2 : Ent (fun c ↦ (cs c).2) Bc) :
    PolyIn (fun c ↦ (memShifts ch a (e c) (omega c) table t pointer (col c) (cs c)).1) Bc ∧
      Ent (fun c ↦ (memShifts ch a (e c) (omega c) table t pointer (col c) (cs c)).2) Bc := by
  unfold memShifts
  refine foldl_pred (fun B : E → E × List E ↦ PolyIn (fun c ↦ (B c).1) Bc ∧
    Ent (fun c ↦ (B c).2) Bc) _ _ (fun x _ B hB ↦ ?_) _ ⟨h1, h2⟩
  obtain ⟨acc, m⟩ := x
  have hg : PolyIn (fun c ↦ (acc.gate.map (col c)).getD 1) dp := by
    cases acc.gate with
    | none => exact polyIn_of_const (fun _ ↦ rfl) dp
    | some g => exact hcol g
  have hcc : PolyIn (fun c ↦ e c * omega c * (acc.gate.map (col c)).getD 1 * ch.etaMem * m *
      a.yMem) Bc :=
    (((((he.mul homega).mul hg).mul (PolyIn.const ch.etaMem)).mul (PolyIn.const m)).mul
      (PolyIn.const a.yMem)).mono (by omega)
  dsimp only
  rcases hs : acc.shift with _ | s
  · exact ⟨hB.1.add_le hcc, hB.2⟩
  · exact ⟨hB.1, ent_addAtSlot hB.2 hcc s⟩

theorem ptrStep_inv (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : E → List E)
    (corner omega act sHat sNext : E → E) (table : Table) (t : ℕ) (col : E → ℕ → E)
    {Bc Bw Bb de dp : ℕ} (he : ∀ j, PolyIn (fun c ↦ (eqQ c).getD j 0 * corner c) de)
    (homega : PolyIn omega dp) (hact : PolyIn act dp) (hsHat : PolyIn sHat dp)
    (hsNext : PolyIn sNext dp) (hcol : ∀ i, PolyIn (fun c ↦ col c i) dp)
    (hreads : ∀ acc ∈ table.links.memory, ∀ p s, Read.word p s ∈ acc.reads → Form.deg s ≤ 1)
    (hc : de + 2 * dp ≤ Bc) (hw : de + dp ≤ Bw) (x : ℕ × ℕ) (A : E → LinkRowSide)
    (hA : RSInv A Bc Bw Bb) :
    RSInv (fun c ↦ ptrStep layout ch a (eqQ c) (point c) (corner c) (omega c) (act c) (sHat c)
      (sNext c) table t (col c) (A c) x) Bc Bw Bb := by
  obtain ⟨pointer, kk⟩ := x
  have hE : PolyIn (fun c ↦ (eqQ c).getD (A c).q 0 * corner c) de :=
    (he (A 0).q).congr fun c ↦ by rw [hA.q c]
  have hcs : PolyIn (fun c ↦ (ptrStep layout ch a (eqQ c) (point c) (corner c) (omega c) (act c)
      (sHat c) (sNext c) table t (col c) (A c) (pointer, kk)).coef) Bc ∧
      Ent (fun c ↦ (ptrStep layout ch a (eqQ c) (point c) (corner c) (omega c) (act c) (sHat c)
        (sNext c) table t (col c) (A c) (pointer, kk)).shifts) Bc := by
    rcases kk with _ | _ | kk
    · refine ⟨(hA.coef.add_le (((hE.mul hact).mul (((PolyIn.const a.eqZetaR).mul hsHat).add
        ((PolyIn.const a.shiftZetaR).mul hsNext))).mono (by omega))).congr fun c ↦
        (ptrStep_zero ..).1.symm, ?_⟩
      exact ⟨fun c ↦ by beta_reduce; rw [(ptrStep_zero ..).2, (ptrStep_zero ..).2, hA.shifts.1 c],
        fun i ↦ (hA.shifts.2 i).congr fun c ↦ by beta_reduce; rw [(ptrStep_zero ..).2]⟩
    · refine ⟨(hA.coef.add_le (((hE.mul homega).mul ((PolyIn.const a.xBc).add
        ((hcol table.links.stateLink.fp).mul (PolyIn.const a.pFp)))).mono (by omega))).congr
        fun c ↦ (ptrStep_one ..).1.symm, ?_⟩
      exact ⟨fun c ↦ by beta_reduce; rw [(ptrStep_one ..).2, (ptrStep_one ..).2, hA.shifts.1 c],
        fun i ↦ (hA.shifts.2 i).congr fun c ↦ by beta_reduce; rw [(ptrStep_one ..).2]⟩
    · have hr := readCoef_deg ch a _ omega table t pointer col (fun c ↦ (A c).coef) hE homega hcol
        hreads (by omega) hA.coef
      obtain ⟨m1, m2⟩ := memShifts_deg ch a _ omega table t pointer col
        (fun c ↦ (readCoef ch a ((eqQ c).getD (A c).q 0 * corner c) (omega c) table t pointer (col c)
          (A c).coef, (A c).shifts)) hE homega hcol (by omega) hr hA.shifts
      refine ⟨m1.congr fun c ↦ (ptrStep_two ..).1.symm, ?_⟩
      exact ⟨fun c ↦ by beta_reduce; rw [(ptrStep_two ..).2, (ptrStep_two ..).2, m2.1 c],
        fun i ↦ (m2.2 i).congr fun c ↦ by beta_reduce; rw [(ptrStep_two ..).2]⟩
  refine ⟨hcs.1, hcs.2, ?_, ?_, fun c ↦ ?_⟩
  · exact (hA.cw.add_le (((hE.mul homega).mul (PolyIn.const _)).mono (by omega))).congr fun c ↦ by
      rw [(ptrStep_rest ..).1, hA.q c]
  · exact hA.base.congr fun c ↦ (ptrStep_rest ..).2.2.1.symm
  · rw [(ptrStep_rest ..).2.1, (ptrStep_rest ..).2.1, hA.q c]

theorem ptrFold_inv (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : E → List E)
    (corner omega act sHat sNext : E → E) (table : Table) (t : ℕ) (col : E → ℕ → E)
    {Bc Bw Bb de dp : ℕ} (he : ∀ j, PolyIn (fun c ↦ (eqQ c).getD j 0 * corner c) de)
    (homega : PolyIn omega dp) (hact : PolyIn act dp) (hsHat : PolyIn sHat dp)
    (hsNext : PolyIn sNext dp) (hcol : ∀ i, PolyIn (fun c ↦ col c i) dp)
    (hreads : ∀ acc ∈ table.links.memory, ∀ p s, Read.word p s ∈ acc.reads → Form.deg s ≤ 1)
    (hc : de + 2 * dp ≤ Bc) (hw : de + dp ≤ Bw) (P : List (ℕ × ℕ)) (A : E → LinkRowSide)
    (hA : RSInv A Bc Bw Bb) :
    RSInv (fun c ↦ P.foldl (ptrStep layout ch a (eqQ c) (point c) (corner c) (omega c) (act c)
      (sHat c) (sNext c) table t (col c)) (A c)) Bc Bw Bb :=
  foldl_pred (fun B ↦ RSInv B Bc Bw Bb) _ P (fun x _ B hB ↦ ptrStep_inv layout ch a eqQ point
    corner omega act sHat sNext table t col he homega hact hsHat hsNext hcol hreads hc hw x B hB) A hA

theorem ptrFold_sent (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : List E)
    (corner omega act sHat sNext : E) (table : Table) (t : ℕ) (col : ℕ → E) :
    ∀ (P : List (ℕ × ℕ)) (acc : LinkRowSide), (P.foldl (ptrStep layout ch a eqQ point corner omega
      act sHat sNext table t col) acc).sent = acc.sent
  | [], _ => rfl
  | (p, k) :: P, acc => (ptrFold_sent layout ch a eqQ point corner omega act sHat sNext table t col
      P _).trans (ptrStep_rest layout ch a eqQ point corner omega act sHat sNext table t col acc p
        k).2.2.2.1

/-! ## One table -/

/-- `tableBaseOf`'s base term, the payload under `ω`. -/
def tableBaseCore (ch : LinkCh) (a : IdxAt) (omega : E) (table : Table) (t : ℕ)
    (values : List E) : E :=
  let col := fun (c : ℕ) ↦ values.getD c 0
  let links := table.links
  let muT := ch.mu.getD t []
  let slot := eqKernel ch.alpha
  let accessValue := fun (a : Access) ↦
    ch.gammaMem.getD 0 0 * a.address.evaluate col + ch.gammaMem.getD 3 0 +
      ch.gammaMem.getD 1 0 * a.value.evaluate col
  let bc := links.bytecodeLink
  let rBc := slot.getD 1 0 * col bc.pc + slot.getD 2 0 + slot.getD 3 0 * gpow bc.opcode +
    sumE (bc.operands.map fun (slots, f) ↦ slot.getD (slots.headD 0) 0 * f.evaluate col)
  let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
  let memory := sumE ((links.memory.zip muT).map fun (a, m) ↦ m * gateOf a * accessValue a)
  omega * a.eq0R * (ch.etaMem * memory + ch.etaBc * rBc)

theorem tableBaseOf_eq (ch : LinkCh) (a : IdxAt) (jump point : List E) (height : ℕ) (omega : E)
    (table : Table) (t : ℕ) (values : List E) :
    tableBaseOf ch a jump point height omega table t values =
      if 0 < table.nConstraints then
        tableBaseCore ch a omega table t values +
          eqEval (ch.tau.take height) point * sumE (List.zipWith (· * ·) jump (table.constraints values))
      else tableBaseCore ch a omega table t values := rfl

theorem tableBaseCore_deg (ch : LinkCh) (a : IdxAt) (omega : E → E) (table : Table) (t : ℕ)
    (values : E → List E) {dp : ℕ} (hf : TableFacts table) (homega : PolyIn omega dp)
    (hval : ∀ i, PolyIn (fun c ↦ (values c).getD i 0) dp) :
    PolyIn (fun c ↦ tableBaseCore ch a (omega c) table t (values c)) (4 * dp) := by
  have hgate : ∀ acc : Access,
      PolyIn (fun c ↦ (acc.gate.map fun i ↦ (values c).getD i 0).getD 1) dp := fun acc ↦ by
    cases acc.gate with
    | none => exact polyIn_of_const (fun _ ↦ rfl) dp
    | some g => exact hval g
  have hev : ∀ (f : Form) (k : ℕ), Form.deg f ≤ k →
      PolyIn (fun c ↦ f.evaluate fun i ↦ (values c).getD i 0) (k * dp) := fun f k hk ↦
    (polyIn_evaluate f (fun c i ↦ (values c).getD i 0) dp hval).mono (Nat.mul_le_mul_right dp hk)
  unfold tableBaseCore
  dsimp only
  refine PolyIn.mul_le (d := dp) (e := 3 * dp) ((homega.mul (PolyIn.const _)).mono (by omega))
    (PolyIn.add_le (PolyIn.mul_le (d := 0) (e := 3 * dp) (PolyIn.const _) ?_ (by omega))
      (PolyIn.mul_le (d := 0) (e := 3 * dp) (PolyIn.const _) ?_ (by omega))) (by omega)
  · refine polyIn_listSum_map _ fun x hx ↦ ?_
    obtain ⟨acc, m⟩ := x
    have hacc := (List.of_mem_zip hx).1
    dsimp only
    refine PolyIn.mul_le (d := dp) (e := 2 * dp)
      (PolyIn.mul_le (d := 0) (e := dp) (PolyIn.const _) (hgate acc) (by omega)) ?_ (by omega)
    refine PolyIn.add_le (PolyIn.add_le ?_ ((PolyIn.const _).mono (Nat.zero_le _))) ?_
    · exact (PolyIn.const _).mul_le (hev _ 2 (hf.address acc hacc)) (by omega)
    · exact (PolyIn.const _).mul_le (hev _ 2 (hf.value acc hacc)) (by omega)
  · refine PolyIn.add_le (PolyIn.add_le (PolyIn.add_le ?_ ?_) ?_) ?_
    · exact (PolyIn.const _).mul_le (hval _) (by omega)
    · exact (PolyIn.const _).mono (Nat.zero_le _)
    · exact (PolyIn.const _).mono (Nat.zero_le _)
    · refine polyIn_listSum_map _ fun x hx ↦ ?_
      obtain ⟨slots, f⟩ := x
      dsimp only
      exact (PolyIn.const _).mul_le (hev _ 2 (hf.operands _ hx)) (by omega)

theorem constraints_deg (table : Table) (hf : TableFacts table) (jump : List E)
    (values : E → List E) {dp : ℕ} (hval : ∀ i, PolyIn (fun c ↦ (values c).getD i 0) dp) :
    PolyIn (fun c ↦ sumE (List.zipWith (· * ·) jump (table.constraints (values c)))) (2 * dp) := by
  rcases hf.constraints with h | h
  · rw [h]
    have hv : ∀ name, PolyIn (fun c ↦ (values c).getD (colIndex jumpColumns name) 0) dp :=
      fun _ ↦ hval _
    have hb1 : PolyIn (fun c ↦ (values c).getD (colIndex jumpColumns "b") 0 + 1) dp :=
      ((hv "b").add (PolyIn.const 1)).mono (by omega)
    have hent : Ent (fun c ↦ jumpConstraints (values c)) (2 * dp) := by
      refine ⟨fun c ↦ by simp only [jumpConstraints, List.length_cons, List.length_nil],
        fun i ↦ ?_⟩
      match i with
      | 0 =>
        exact (((hv "b").mono (by omega)).add_le
          ((hv "v_cond").mul_le (hv "w") (by omega))).congr fun c ↦ rfl
      | 1 => exact ((hv "v_cond").mul_le hb1 (by omega)).congr fun c ↦ rfl
      | 2 =>
        exact ((((hv "pc_next").mono (by omega)).add_le ((hv "b").mul_le (hv "v_pc")
          (by omega))).add_le ((hb1.mul (PolyIn.const (gpow 1))).mul_le (hv "pc")
          (by omega))).congr fun c ↦ rfl
      | 3 =>
        exact ((((hv "fp_next").mono (by omega)).add_le ((hv "b").mul_le (hv "v_fp")
          (by omega))).add_le (hb1.mul_le (hv "fp") (by omega))).congr fun c ↦ rfl
      | i + 4 => exact polyIn_of_const (fun _ ↦ by simp [jumpConstraints]) _
    exact (polyIn_sumE (ent_zipWith_mul (ent_const (v := fun _ ↦ jump) (fun _ ↦ rfl) 0)
      hent)).mono (by omega)
  · rw [h]
    exact polyIn_of_const (fun _ ↦ rfl) _

/-- Table `t`'s values on the stack, its non-pointer columns' extensions at its row point. -/
def honestOf (layout : Layout) {μ : ℕ} (q : Column μ) (chi : List E) (table : Table) (t : ℕ) :
    List E :=
  (nonPointerOf layout t table).map fun c ↦
    rowMle (chi.take (layout.tableLogHeights.getD t 0))
      (columnValue layout q (globalColumnBases.getD t 0 + c))

/-- `rowStep` before it records the table's columns. -/
def rowStepFold (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi : List E)
    (acc : LinkRowSide) (table : Table) (t : ℕ) : LinkRowSide :=
  let height := layout.tableLogHeights.getD t 0
  let tableRows := layout.tableRows.getD t 0
  let point := chi.take height
  let corner := prodE ((chi.drop height).map (1 + ·))
  let columns := nonPointerOf layout t table
  let sent := columns.zip (acc.sent.take columns.length)
  let values := (List.range table.width).map fun c ↦ (sent.lookup c).getD 0
  let col := fun (c : ℕ) ↦ values.getD c 0
  let state := table.links.stateLink
  let omega := omegaAt (ch.theta.getD t 0) (ch.tau.take height) point tableRows
  let act := lessThan point tableRows
  let sHat := ch.stateGamma (col state.pc) (col state.fp)
  let sNext := ch.stateGamma (state.next.1.evaluate col) (state.next.2.evaluate col)
  let tableBase := tableBaseOf ch a jump point height omega table t values
  (((layout.tables.map (·.links.pointers)).getD t []).zipIdx.foldl
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col))
    { acc with base := acc.base + corner * tableBase, sent := acc.sent.drop columns.length }

theorem rowStep_fields (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi : List E)
    (acc : LinkRowSide) (table : Table) (t : ℕ) :
    let r := rowStep layout ch a jump eqQ chi acc (table, t)
    let f := rowStepFold layout ch a jump eqQ chi acc table t
    r.coef = f.coef ∧ r.shifts = f.shifts ∧ r.certWeight = f.certWeight ∧ r.base = f.base ∧
      r.q = f.q ∧ r.sent = f.sent ∧ r.pieces = f.pieces :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rowStepFold_inv (layout : Layout) {μ : ℕ} (q : Column μ) (ch : LinkCh) (a : IdxAt)
    (jump : List E) (eqQ chi : E → List E) (table : Table) (t : ℕ) (hf : TableFacts table)
    {Bc Bw Bb deq dp dk : ℕ} (hq : ∀ j, PolyIn (fun c ↦ (eqQ c).getD j 0) deq)
    (hpt : ∀ g, MLin g →
      PolyIn (fun c ↦ g ((chi c).take (layout.tableLogHeights.getD t 0))) dp)
    (hk : PolyIn (fun c ↦ prodE (((chi c).drop (layout.tableLogHeights.getD t 0)).map (1 + ·))) dk)
    (hc : deq + dk + 2 * dp ≤ Bc) (hw : deq + dk + dp ≤ Bw) (hb : dk + 4 * dp ≤ Bb)
    (A : E → LinkRowSide) (hA : RSInv A Bc Bw Bb) (R : E → List E)
    (hsent : ∀ c, (A c).sent = honestOf layout q (chi c) table t ++ R c) :
    RSInv (fun c ↦ rowStepFold layout ch a jump (eqQ c) (chi c) (A c) table t) Bc Bw Bb ∧
      ∀ c, (rowStepFold layout ch a jump (eqQ c) (chi c) (A c) table t).sent = R c := by
  have hlen : ∀ c, (honestOf layout q (chi c) table t).length = (nonPointerOf layout t table).length :=
    fun c ↦ by simp [honestOf]
  have htake : ∀ c, (A c).sent.take (nonPointerOf layout t table).length =
      honestOf layout q (chi c) table t := fun c ↦ by rw [hsent c, List.take_left' (hlen c)]
  -- the table's values
  have hval : ∀ i, PolyIn (fun c ↦ ((List.range table.width).map fun j ↦
      (((nonPointerOf layout t table).zip ((A c).sent.take
        (nonPointerOf layout t table).length)).lookup j).getD 0).getD i 0) dp := by
    intro i
    have hF : ∀ j ∈ List.range table.width, PolyIn (fun c ↦
        ((if j ∈ nonPointerOf layout t table then
          some (rowMle ((chi c).take (layout.tableLogHeights.getD t 0))
            (columnValue layout q (globalColumnBases.getD t 0 + j))) else none) : Option E).getD 0)
        dp := by
      intro j _
      by_cases hj : j ∈ nonPointerOf layout t table
      · exact (hpt _ (mlin_rowMle (columnValue layout q (globalColumnBases.getD t 0 + j)))).congr
          fun c ↦ by simp [hj]
      · exact polyIn_of_const (fun c ↦ by simp [hj]) dp
    refine ((ent_map _ hF).2 i).congr fun c ↦ ?_
    beta_reduce
    simp only [htake c, honestOf, lookup_zip_map]
  have homega := hpt _ (mlin_omegaAt (ch.theta.getD t 0)
    (ch.tau.take (layout.tableLogHeights.getD t 0)) (layout.tableRows.getD t 0))
  have hact := hpt _ (mlin_lessThan (layout.tableRows.getD t 0))
  have hev : ∀ f : Form, Form.deg f ≤ 1 → PolyIn (fun c ↦ f.evaluate fun i ↦
      ((List.range table.width).map fun j ↦ (((nonPointerOf layout t table).zip ((A c).sent.take
        (nonPointerOf layout t table).length)).lookup j).getD 0).getD i 0) dp := fun f hk ↦
    (polyIn_evaluate f _ dp hval).mono (by simpa using Nat.mul_le_mul_right dp hk)
  have hgam : ∀ x y : E → E, PolyIn x dp → PolyIn y dp →
      PolyIn (fun c ↦ ch.stateGamma (x c) (y c)) dp := fun x y hx hy ↦
    ((((PolyIn.const 1).add ((PolyIn.const (ch.gammaState.getD 0 0)).mul hx)).add
      ((PolyIn.const (ch.gammaState.getD 1 0)).mul hy)).congr fun c ↦ rfl).mono (by omega)
  have htb := tableBaseCore_deg ch a _ table t _ hf homega hval
  have hid := constraints_deg table hf jump _ hval
  have heqTau := hpt _ (mlin_eqEval (ch.tau.take (layout.tableLogHeights.getD t 0)))
  have hbase : PolyIn (fun c ↦ tableBaseOf ch a jump ((chi c).take (layout.tableLogHeights.getD t 0))
      (layout.tableLogHeights.getD t 0) (omegaAt (ch.theta.getD t 0)
        (ch.tau.take (layout.tableLogHeights.getD t 0))
        ((chi c).take (layout.tableLogHeights.getD t 0)) (layout.tableRows.getD t 0)) table t
      ((List.range table.width).map fun j ↦ (((nonPointerOf layout t table).zip ((A c).sent.take
        (nonPointerOf layout t table).length)).lookup j).getD 0)) (4 * dp) := by
    refine (polyIn_ite _ (fun _ ↦ htb.add_le (heqTau.mul_le hid (by omega))) (fun _ ↦ htb)).congr
      fun c ↦ (tableBaseOf_eq ..).symm
  have hpre : RSInv (fun c ↦ { A c with
      base := (A c).base + prodE (((chi c).drop (layout.tableLogHeights.getD t 0)).map (1 + ·)) *
        tableBaseOf ch a jump ((chi c).take (layout.tableLogHeights.getD t 0))
          (layout.tableLogHeights.getD t 0) (omegaAt (ch.theta.getD t 0)
            (ch.tau.take (layout.tableLogHeights.getD t 0))
            ((chi c).take (layout.tableLogHeights.getD t 0)) (layout.tableRows.getD t 0)) table t
          ((List.range table.width).map fun j ↦ (((nonPointerOf layout t table).zip ((A c).sent.take
            (nonPointerOf layout t table).length)).lookup j).getD 0)
      sent := (A c).sent.drop (nonPointerOf layout t table).length }) Bc Bw Bb :=
    ⟨hA.coef, hA.shifts, hA.cw, hA.base.add_le (hk.mul_le hbase (by omega)), hA.q⟩
  refine ⟨ptrFold_inv layout ch a eqQ _ _ _ _ _ _ table t _ (de := deq + dk) (dp := dp)
    (fun j ↦ (hq j).mul hk) homega hact (hgam _ _ (hval _) (hval _))
    (hgam _ _ (hev _ hf.next1) (hev _ hf.next2)) hval hf.reads (by omega) (by omega) _ _ hpre,
    fun c ↦ ?_⟩
  exact (ptrFold_sent ..).trans (by
    show (A c).sent.drop (nonPointerOf layout t table).length = R c
    rw [hsent c, List.drop_left' (hlen c)])

/-! ## Every table -/

theorem rowSide_inv (layout : Layout) (hT : layout.tables = tables) {μ : ℕ} (q : Column μ)
    (ch : LinkCh) (a : IdxAt) (jump : List E) (eqQ chi : E → List E) {Bc Bw Bb deq : ℕ}
    (dpH dkH : ℕ → ℕ) (hq : ∀ j, PolyIn (fun c ↦ (eqQ c).getD j 0) deq)
    (hpt : ∀ h ≤ linkRows layout, ∀ g, MLin g → PolyIn (fun c ↦ g ((chi c).take h)) (dpH h))
    (hk : ∀ h ≤ linkRows layout, PolyIn (fun c ↦ prodE (((chi c).drop h).map (1 + ·))) (dkH h))
    (hc : ∀ h ≤ linkRows layout, deq + dkH h + 2 * dpH h ≤ Bc)
    (hw : ∀ h ≤ linkRows layout, deq + dkH h + dpH h ≤ Bw)
    (hb : ∀ h ≤ linkRows layout, dkH h + 4 * dpH h ≤ Bb) :
    ∀ (S : List (Table × ℕ)), (∀ x ∈ S, x.1 ∈ layout.tables) → ∀ A : E → LinkRowSide,
      RSInv A Bc Bw Bb →
      (∀ c, (A c).sent = (S.map fun x ↦ honestOf layout q (chi c) x.1 x.2).flatten) →
      RSInv (fun c ↦ S.foldl (rowStep layout ch a jump (eqQ c) (chi c)) (A c)) Bc Bw Bb
  | [], _, _, hA, _ => hA
  | (table, t) :: S, hS, A, hA, hsent => by
    have hht := height_le layout t
    have hmem : table ∈ tables := hT ▸ hS (table, t) (by simp)
    obtain ⟨h1, h2⟩ := rowStepFold_inv layout q ch a jump eqQ chi table t (tableFacts_of_mem hmem)
      hq (hpt _ hht) (hk _ hht) (hc _ hht) (hw _ hht) (hb _ hht) A hA
      (fun c ↦ (S.map fun x ↦ honestOf layout q (chi c) x.1 x.2).flatten)
      (fun c ↦ by rw [hsent c, List.map_cons, List.flatten_cons])
    refine rowSide_inv layout hT q ch a jump eqQ chi dpH dkH hq hpt hk hc hw hb S
      (fun x hx ↦ hS x (by simp [hx])) _ (h1.of_eq (fun c ↦ (rowStep_fields ..).1)
        (fun c ↦ (rowStep_fields ..).2.1) (fun c ↦ (rowStep_fields ..).2.2.1)
        (fun c ↦ (rowStep_fields ..).2.2.2.1) (fun c ↦ (rowStep_fields ..).2.2.2.2.1))
      fun c ↦ (rowStep_fields ..).2.2.2.2.2.1.trans (h2 c)

/-! ## The ring pieces -/

/-- The pieces so far: each at a table's row point, scaled by an entry of `eq_kernel(q_point)`. -/
def PInv (N : ℕ) (eqQ chi : E → List E) (A : E → LinkRowSide) : Prop :=
  (∀ c, (A c).q = (A 0).q) ∧ ∃ P : List (Option Placement × ℕ × ℕ), (∀ x ∈ P, x.2.1 ≤ N) ∧
    ∀ c, (A c).pieces = P.map fun x ↦ ⟨x.1, (chi c).take x.2.1, (eqQ c).getD x.2.2 0⟩

theorem PInv.of_eq {N : ℕ} {eqQ chi : E → List E} {A B : E → LinkRowSide}
    (h1 : ∀ c, (A c).q = (B c).q) (h2 : ∀ c, (A c).pieces = (B c).pieces)
    (h : PInv N eqQ chi B) : PInv N eqQ chi A := by
  obtain ⟨hq, P, hP, hp⟩ := h
  exact ⟨fun c ↦ by rw [h1, h1, hq c], P, hP, fun c ↦ by rw [h2, hp c]⟩

theorem ptrFold_pieces (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ chi : E → List E)
    (table : Table) (t : ℕ) (corner omega act sHat sNext : E → E) (col : E → ℕ → E) :
    ∀ (P : List (ℕ × ℕ)) (B : E → LinkRowSide), PInv (linkRows layout) eqQ chi B →
      PInv (linkRows layout) eqQ chi fun c ↦ P.foldl (ptrStep layout ch a (eqQ c)
        ((chi c).take (layout.tableLogHeights.getD t 0)) (corner c) (omega c) (act c) (sHat c)
        (sNext c) table t (col c)) (B c)
  | [], _, h => h
  | (p, k) :: P, B, ⟨hq, Q, hQ, hp⟩ => by
    refine ptrFold_pieces layout ch a eqQ chi table t corner omega act sHat sNext col P _
      ⟨fun c ↦ ?_, Q ++ [(some ((layout.placements.getD (globalColumnBases.getD t 0 + p)
        none).getD default), layout.tableLogHeights.getD t 0, (B 0).q)], fun y hy ↦ ?_,
        fun c ↦ ?_⟩
    · rw [(ptrStep_rest ..).2.1, (ptrStep_rest ..).2.1, hq c]
    · rcases List.mem_append.mp hy with hy | hy
      · exact hQ y hy
      · rw [List.mem_singleton.mp hy]; exact height_le layout t
    · rw [(ptrStep_rest ..).2.2.2.2, hp c, hq c, List.map_append]
      rfl

theorem pieces_inv (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump : List E)
    (eqQ chi : E → List E) :
    ∀ (S : List (Table × ℕ)) (A : E → LinkRowSide), PInv (linkRows layout) eqQ chi A →
      PInv (linkRows layout) eqQ chi
        (fun c ↦ S.foldl (rowStep layout ch a jump (eqQ c) (chi c)) (A c))
  | [], _, hA => hA
  | (table, t) :: S, A, hA => by
    refine pieces_inv layout ch a jump eqQ chi S _ (PInv.of_eq
      (fun c ↦ (rowStep_fields ..).2.2.2.2.1) (fun c ↦ (rowStep_fields ..).2.2.2.2.2.2) ?_)
    refine ptrFold_pieces layout ch a eqQ chi table t _ _ _ _ _ _ _ _ ?_
    exact hA

/-- **The bit-slices are of degree at most one.** -/
theorem slices_deg (layout : Layout) {μ : ℕ} (q : Column μ) (qP chi : E → List E) {deq : ℕ}
    (dpH : ℕ → ℕ) (hq : ∀ j, PolyIn (fun c ↦ (eqKernel (qP c)).getD j 0) deq)
    (hpt : ∀ h ≤ linkRows layout, ∀ g, MLin g → PolyIn (fun c ↦ g ((chi c).take h)) (dpH h))
    (hs : ∀ h ≤ linkRows layout, deq + dpH h ≤ 1) :
    Ent (fun c ↦ honestSlices layout q (chi c) (qP c)) 1 := by
  obtain ⟨-, P, hP, hp⟩ := pieces_inv layout ⟨[], [], [], [], [], 0, 0, [], [], [], []⟩
    ⟨0, 0, 0, 0, 0, 0, 0⟩ [] (fun c ↦ eqKernel (qP c)) chi layout.tables.zipIdx
    (fun _ ↦ rowStart layout []) ⟨fun _ ↦ rfl, [], by simp, fun _ ↦ rfl⟩
  unfold honestSlices
  refine ent_map _ fun b _ ↦ ?_
  refine (polyIn_listSum_map P (F := fun x c ↦ (eqKernel (qP c)).getD x.2.2 0 *
    rowMle ((chi c).take x.2.1) fun j ↦ bitOf (pieceRow q x.1 j) b) fun x hx ↦
      (hq x.2.2).mul_le (hpt _ (hP x hx) _ (mlin_rowMle _)) (hs _ (hP x hx))).congr fun c ↦ ?_
  rw [show piecesOf layout (chi c) (qP c) = P.map (fun x ↦ (⟨x.1, (chi c).take x.2.1,
    (eqKernel (qP c)).getD x.2.2 0⟩ : RingPiece)) from hp c, List.map_map]
  rfl

/-! ## The summand at the final point -/

theorem ent_values (f : Functionals) (chunks : Chunks) (slices : E → List E) (h : Ent slices 1) :
    Ent (fun c ↦ f.values chunks (slices c)) 1 := by
  unfold Functionals.values
  refine ent_map _ fun x _ ↦ ?_
  obtain ⟨i, table⟩ := x
  dsimp only
  exact (polyIn_sumE (ent_zipWith_mul (ent_const (v := fun _ ↦ table) (fun _ ↦ rfl) 0)
    (ent_drop h _))).mono (by omega)

/-- **`lastOf`'s degree** from the accumulators', the slices' and `eq0Q`'s. -/
theorem lastOf_deg (layout : Layout) (chunks : Chunks) (ch : LinkCh) (r : List E) (cert : E)
    (qP slices : E → List E) (rs : E → LinkRowSide) {Bc Bw Bb deq : ℕ}
    (hrs : RSInv rs Bc Bw Bb) (hsl : Ent slices 1)
    (heq0 : PolyIn (fun c ↦ prodE ((qP c).map (1 + ·))) deq) :
    PolyIn (fun c ↦ lastOf layout chunks ch r cert (qP c) (slices c) (rs c))
      (max (max (Bc + 1 + (chunks.d - 1)) (Bw + 2)) (deq + Bb)) := by
  set F := Functionals.new chunks r (layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0)
  have hd : F.d = chunks.d := rfl
  have hV := ent_values F chunks slices hsl
  have hrest : PolyIn (fun c ↦ prodE (((F.values chunks (slices c)).drop 1).take (F.d - 1)))
      (chunks.d - 1) :=
    (polyIn_prodE (ent_take (ent_drop hV 1) (F.d - 1))).mono (by
      rw [← hd]; simp only [List.length_take, Nat.mul_one]; exact min_le_left _ _)
  have hlow : PolyIn (fun c ↦ (rs c).coef * (F.values chunks (slices c)).getD 0 0 +
      sumE (List.zipWith (· * ·) (rs c).shifts ((F.values chunks (slices c)).drop (2 * F.d))))
      (Bc + 1) :=
    (hrs.coef.mul (hV.2 0)).add_le (polyIn_sumE (ent_zipWith_mul hrs.shifts (ent_drop hV _)))
  have hcerts : Ent (fun c ↦ ch.nu.map fun n ↦ cert * (rs c).certWeight * n) Bw :=
    ent_map ch.nu fun n _ ↦ (((PolyIn.const cert).mul hrs.cw).mul (PolyIn.const n)).mono (by omega)
  have hcert : PolyIn (fun c ↦ sumE ((List.range F.d).map fun i ↦
      (ch.nu.map fun n ↦ cert * (rs c).certWeight * n).getD i 0 *
        ((F.values chunks (slices c)).getD i 0 * (F.values chunks (slices c)).getD (F.d + i) 0 +
          F.mirrors.getD i 0))) (Bw + 2) :=
    polyIn_listSum_map _ fun i _ ↦ (hcerts.2 i).mul_le
      (((hV.2 i).mul (hV.2 (F.d + i))).add (PolyIn.const _)) (by omega)
  exact ((((hlow.mul hrest).add hcert).add (heq0.mul hrs.base)).congr fun c ↦ rfl).mono
    (by omega)

/-! ## The row summand -/

theorem tailValuesF_fst (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh : List E) (split : Split) (chi qPoint message : List E) :
    (tailValuesF layout chunks theta0 drawn r m1 fresh split chi qPoint message).1 =
      lastOf layout chunks (linkCh layout chunks theta0 drawn) r (fresh.getD 0 0) qPoint
        (message.drop (nValuesOf layout))
        (rowSideOf layout (linkCh layout chunks theta0 drawn)
          (idxAt layout chunks (linkCh layout chunks theta0 drawn) r m1 split) (fresh.drop 1)
          (eqKernel qPoint) chi message) := rfl

theorem honestValues_eq (layout : Layout) {μ : ℕ} (q : Column μ) (chi : List E) :
    honestValues layout q chi =
      (layout.tables.zipIdx.map fun x ↦ honestOf layout q chi x.1 x.2).flatten := rfl

theorem honestValues_length (layout : Layout) {μ : ℕ} (q : Column μ) (chi : List E) :
    (honestValues layout q chi).length = nValuesOf layout := by
  rw [honestValues_eq, List.length_flatten, List.map_map, nValuesOf]
  congr 1
  refine List.map_congr_left ?_
  rintro ⟨table, t⟩ _
  simp [honestOf]

theorem rowSummand_eq (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r fresh x : List E) :
    rowSummand layout chunks q theta0 drawn r fresh x =
      lastOf layout chunks (linkCh layout chunks theta0 drawn) r (fresh.getD 0 0)
        (x.drop (linkRows layout))
        (honestSlices layout q (x.take (linkRows layout)) (x.drop (linkRows layout)))
        (layout.tables.zipIdx.foldl (rowStep layout (linkCh layout chunks theta0 drawn)
          (idxAt layout chunks (linkCh layout chunks theta0 drawn) r (honestM1 layout chunks q r)
            (linkSplit layout r)) (fresh.drop 1) (eqKernel (x.drop (linkRows layout)))
          (x.take (linkRows layout)))
          (rowStart layout (honestMessage layout q (x.take (linkRows layout))
            (x.drop (linkRows layout))))) := by
  have h := tailValuesF_fst layout chunks theta0 drawn r (honestM1 layout chunks q r) fresh
    (linkSplit layout r) (x.take (linkRows layout)) (x.drop (linkRows layout))
    (honestMessage layout q (x.take (linkRows layout)) (x.drop (linkRows layout)))
  have hd : (honestMessage layout q (x.take (linkRows layout)) (x.drop (linkRows layout))).drop
      (nValuesOf layout) = honestSlices layout q (x.take (linkRows layout)) (x.drop (linkRows layout)) :=
    List.drop_left' (honestValues_length ..)
  rw [hd] at h
  exact h

theorem rowStart_fields (layout : Layout) (m : List E) :
    (rowStart layout m).coef = 0 ∧
      (rowStart layout m).shifts =
        List.replicate (layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0) 0 ∧
      (rowStart layout m).certWeight = 0 ∧ (rowStart layout m).base = 0 ∧
      (rowStart layout m).q = 0 ∧ (rowStart layout m).sent = m.take (nValuesOf layout) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rsInv_rowStart (layout : Layout) (msg : E → List E) (Bc Bw Bb : ℕ) :
    RSInv (fun c ↦ rowStart layout (msg c)) Bc Bw Bb where
  coef := polyIn_of_const (fun c ↦ by rw [(rowStart_fields ..).1, (rowStart_fields ..).1]) _
  shifts := ent_const (fun c ↦ by rw [(rowStart_fields ..).2.1, (rowStart_fields ..).2.1]) _
  cw := polyIn_of_const (fun c ↦ by rw [(rowStart_fields ..).2.2.1, (rowStart_fields ..).2.2.1]) _
  base := polyIn_of_const (fun c ↦ by
    rw [(rowStart_fields ..).2.2.2.1, (rowStart_fields ..).2.2.2.1]) _
  q := fun c ↦ by rw [(rowStart_fields ..).2.2.2.2.1, (rowStart_fields ..).2.2.2.2.1]

/-- **The row summand's degree** in a variable, from its pieces' degrees. -/
theorem summand_deg (layout : Layout) (hT : layout.tables = tables) (chunks : Chunks) {μ : ℕ}
    (q : Column μ) (theta0 : E) (drawn r fresh : List E) (X : E → List E) {deq Bc Bw Bb : ℕ}
    (dpH dkH : ℕ → ℕ)
    (hq : ∀ j, PolyIn (fun c ↦ (eqKernel ((X c).drop (linkRows layout))).getD j 0) deq)
    (heq0 : PolyIn (fun c ↦ prodE (((X c).drop (linkRows layout)).map (1 + ·))) deq)
    (hpt : ∀ h ≤ linkRows layout, ∀ g, MLin g →
      PolyIn (fun c ↦ g (((X c).take (linkRows layout)).take h)) (dpH h))
    (hk : ∀ h ≤ linkRows layout,
      PolyIn (fun c ↦ prodE ((((X c).take (linkRows layout)).drop h).map (1 + ·))) (dkH h))
    (hc : ∀ h ≤ linkRows layout, deq + dkH h + 2 * dpH h ≤ Bc)
    (hw : ∀ h ≤ linkRows layout, deq + dkH h + dpH h ≤ Bw)
    (hb : ∀ h ≤ linkRows layout, dkH h + 4 * dpH h ≤ Bb)
    (hs : ∀ h ≤ linkRows layout, deq + dpH h ≤ 1) :
    PolyIn (fun c ↦ rowSummand layout chunks q theta0 drawn r fresh (X c))
      (max (max (Bc + 1 + (chunks.d - 1)) (Bw + 2)) (deq + Bb)) := by
  have hsl := slices_deg layout q (fun c ↦ (X c).drop (linkRows layout))
    (fun c ↦ (X c).take (linkRows layout)) dpH hq hpt hs
  have hstart : ∀ c, (rowStart layout (honestMessage layout q ((X c).take (linkRows layout))
      ((X c).drop (linkRows layout)))).sent = (layout.tables.zipIdx.map fun x ↦
        honestOf layout q ((X c).take (linkRows layout)) x.1 x.2).flatten := fun c ↦ by
    rw [(rowStart_fields ..).2.2.2.2.2, honestMessage, List.take_left' (honestValues_length ..), honestValues_eq]
  have hrs := rowSide_inv layout hT q (linkCh layout chunks theta0 drawn)
    (idxAt layout chunks (linkCh layout chunks theta0 drawn) r (honestM1 layout chunks q r)
      (linkSplit layout r)) (fresh.drop 1) (fun c ↦ eqKernel ((X c).drop (linkRows layout)))
    (fun c ↦ (X c).take (linkRows layout)) dpH dkH hq hpt hk hc hw hb layout.tables.zipIdx
    (fun x hx ↦ fst_mem_of_mem_zipIdx _ _ x hx)
    (fun c ↦ rowStart layout (honestMessage layout q ((X c).take (linkRows layout))
      ((X c).drop (linkRows layout))))
    (rsInv_rowStart ..) hstart
  refine (lastOf_deg layout chunks (linkCh layout chunks theta0 drawn) r (fresh.getD 0 0) _ _ _ hrs
    hsl heq0).congr fun c ↦ (rowSummand_eq ..).symm

end

end LeanVM.Protocol.Relation.RowPoly

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link RowPoly

public section

/-- **The row summand is of the row side's round degrees** in each variable, on any stack:
`max(d + 2, 4)` in a row variable, `max(d + 1, 3)` in a pointer-column variable. -/
theorem row_deg_of_summand {layout : Layout} (hT : layout.tables = tables) (chunks : Chunks)
    {μ : ℕ} (q : Column μ) (theta0 : E) (drawn r fresh : List E) :
    PerVarDegAt (rowSummand layout chunks q theta0 drawn r fresh) (linkRowVars layout)
      (rowDegrees (linkRows layout) (roundCoefficients chunks.d).1
        (roundCoefficients chunks.d).2) := by
  intro pre rest _
  rcases Nat.lt_or_ge pre.length (linkRows layout) with hk | hk
  · -- a row variable
    have hX : ∀ c : E, (pre ++ c :: rest).take (linkRows layout) =
        pre ++ c :: rest.take (linkRows layout - pre.length - 1) := fun c ↦ by
      rw [take_line, ite_eq_left hk]
    have hQ : ∀ c : E, (pre ++ c :: rest).drop (linkRows layout) =
        rest.drop (linkRows layout - pre.length - 1) := fun c ↦ by
      rw [drop_line, ite_eq_right (by omega)]
    refine (summand_deg layout hT chunks q theta0 drawn r fresh (fun c ↦ pre ++ c :: rest)
      (deq := 0) (Bc := 2) (Bw := 1) (Bb := 4)
      (fun h ↦ if pre.length < h then 1 else 0) (fun h ↦ if h ≤ pre.length then 1 else 0)
      (fun j ↦ polyIn_of_const (fun c ↦ by simp only [hQ]) 0)
      (polyIn_of_const (fun c ↦ by simp only [hQ]) 0)
      (fun h _ g hg ↦ ?_) (fun h _ ↦ ?_) (fun h _ ↦ by split_ifs <;> omega)
      (fun h _ ↦ by split_ifs <;> omega) (fun h _ ↦ by split_ifs <;> omega)
      (fun h _ ↦ by split_ifs <;> omega)).mono ?_
    · by_cases hh : pre.length < h
      · exact ((hg pre ((rest.take (linkRows layout - pre.length - 1)).take
          (h - pre.length - 1))).congr fun c ↦ by
            rw [hX, take_line, ite_eq_left hh]).mono (by simp [hh])
      · exact polyIn_of_const (fun c ↦ by simp only [hX, take_line, hh, ↓reduceIte]) _
    · by_cases hh : h ≤ pre.length
      · exact ((mlin_prodE_one_add (pre.drop h) (rest.take (linkRows layout - pre.length - 1))).congr
          fun c ↦ by beta_reduce; rw [hX, drop_line, ite_eq_left hh]).mono (by simp [hh])
      · exact polyIn_of_const (fun c ↦ by simp only [hX, drop_line, hh, ↓reduceIte]) _
    · unfold rowDegrees roundCoefficients
      dsimp only
      rw [ite_eq_left hk]
      omega
  · -- a pointer-column variable
    have hX : ∀ c : E, (pre ++ c :: rest).take (linkRows layout) = pre.take (linkRows layout) :=
      fun c ↦ by rw [take_line, ite_eq_right (by omega)]
    have hQ : ∀ c : E, (pre ++ c :: rest).drop (linkRows layout) =
        pre.drop (linkRows layout) ++ c :: rest := fun c ↦ by rw [drop_line, ite_eq_left hk]
    refine (summand_deg layout hT chunks q theta0 drawn r fresh (fun c ↦ pre ++ c :: rest)
      (deq := 1) (Bc := 1) (Bw := 1) (Bb := 0) (fun _ ↦ 0) (fun _ ↦ 0)
      (fun j ↦ (mlin_eqKernel_getD j (pre.drop (linkRows layout)) rest).congr fun c ↦ by
        beta_reduce; rw [hQ])
      ((mlin_prodE_one_add (pre.drop (linkRows layout)) rest).congr fun c ↦ by
        beta_reduce; rw [hQ])
      (fun h _ g _ ↦ polyIn_of_const (fun c ↦ by simp only [hX]) 0)
      (fun h _ ↦ polyIn_of_const (fun c ↦ by simp only [hX]) 0)
      (fun _ _ ↦ by omega) (fun _ _ ↦ by omega) (fun _ _ ↦ by omega) (fun _ _ ↦ by omega)).mono ?_
    unfold rowDegrees roundCoefficients
    dsimp only
    rw [ite_eq_right (by omega)]
    omega

end

end LeanVM.Protocol.Relation
