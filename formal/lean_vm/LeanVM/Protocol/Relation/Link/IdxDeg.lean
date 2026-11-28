/-
  LeanVM.Protocol.Relation.Link.IdxDeg

  The index summand and the fresh coefficients' weights are of degree at most two in each index
  variable: `LinkSummandFacts`'s `idx_deg` and `B_deg`.
-/

module

public import LeanVM.Protocol.Relation.Link.Summand
public import LeanVM.Protocol.Relation.Link.IdxPoly

/-!
# The index side's degrees

Fix every index variable but one, `r = pre ++ c :: rest`. The row summand (`rowSummand`) is a
polynomial of degree at most two in `c`:

* the index side's scalars (`idxAt`) are affine in `c` (`idxIn_idxAt`): `eq(0, r)`, `eq(ζ, r)`, the
  shift, `index_mle`, the memory term (`below_mem` and the memory's extension read disjoint
  coordinates) and `X_bc`, `P_fp` (`below_bc` and the program's split read disjoint coordinates);
* the row side's fold is linear in those scalars, so its coefficient, shifts and base are affine
  in `c`, the rest constant (`rowIn_rowSideOf`);
* each functional of a pointer word reads one chunk of `r`, and the chunks are disjoint
  (`chunk_disjoint`): `(c·D_0 + Σ_s c_s·T_s)·Π_{i ≥ 1} D_i` is of degree two, and each
  certificate term `D_i(r)·D_i(1 + r) + π_i` too (`polyIn_summand`).

A sum over the row cube keeps the degree (`polyIn_sumTail`), so the index summand, the row side's
full sum at no fresh coefficient, is of degree two in each index variable (`linkIdxAt_perVarDeg`),
and so is each weight, a difference of two such sums (`linkB_perVarDeg`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Protocol.Hotwire Finset IdxPoly

public section

namespace IdxDeg

/-! ## The program's split -/

theorem length_powersFrom (base : E) : ∀ (count : ℕ) (acc : E),
    (powersFrom acc base count).length = count
  | 0, _ => rfl
  | count + 1, acc => by simp [powersFrom, length_powersFrom base count]

theorem getD_map_zipIdx_zip {G : (E × E) × ℕ → E} (a b : List E) {j : ℕ} (ha : j < a.length)
    (hb : j < b.length) :
    (((a.zip b).zipIdx).map G).getD j 0 = G ((a.getD j 0, b.getD j 0), j) := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ ha,
    List.getD_eq_getElem _ _ hb]
  simp

/-- The program's rows read against a weight linear in the equality weight. -/
theorem polyIn_sumE_rows (u v : List E) {G : (E × E) × ℕ → E}
    (hG : ∀ e gk k, G ((e, gk), k) = e * G ((1, gk), k)) :
    PolyIn (fun c ↦ sumE ((((eqKernel (u ++ c :: v)).zip
      (powers gen (2 ^ (u ++ c :: v).length))).zipIdx).map G)) 1 := by
  set n := u.length + 1 + v.length
  have hl : ∀ c : E, (u ++ c :: v).length = n := fun c ↦ by simp [n]; omega
  have hk : ∀ c : E, (eqKernel (u ++ c :: v)).length = 2 ^ n := fun c ↦ by
    rw [eqKernel_length, hl]
  have hp : (powers gen (2 ^ n)).length = 2 ^ n := length_powersFrom _ _ _
  simp only [hl]
  refine polyIn_sumE (fun c ↦ by simp [hk, hp]) fun j hj ↦ ?_
  have hj' : j < 2 ^ n := by simpa [hk, hp] using hj
  refine (polyIn_mulc (G ((1, (powers gen (2 ^ n)).getD j 0), j))
    (polyIn_eqKernel u v j)).congr fun c ↦ ?_
  rw [getD_map_zipIdx_zip _ _ (by rw [hk]; exact hj') (by rw [hp]; exact hj'),
    hG ((eqKernel (u ++ c :: v)).getD j 0)]

/-- Every entry of the program's split is affine in a free coordinate of its point. -/
theorem polyIn_splitAt (bytecode : List K) (pcs : List (ℕ × ℕ)) (u v : List E) (t s : ℕ) :
    PolyIn (fun c ↦ (splitAt bytecode (u ++ c :: v) pcs).count.getD t 0) 1 ∧
    PolyIn (fun c ↦ ((splitAt bytecode (u ++ c :: v) pcs).slots.getD t []).getD s 0) 1 ∧
    PolyIn (fun c ↦ ((splitAt bytecode (u ++ c :: v) pcs).pc.getD t []).getD s 0) 1 := by
  by_cases ht : t < opKeccak + 1
  · refine ⟨?_, ?_, ?_⟩
    · simp only [splitAt, getD_map_range, ht, ↓reduceIte]
      exact polyIn_sumE_rows u v fun e gk k ↦ by dsimp only; split_ifs <;> ring
    · simp only [splitAt, getD_map_range, ht, ↓reduceIte]
      refine polyIn_ite _ (fun _ ↦ polyIn_ite _ (fun _ ↦ ?_) fun _ ↦ polyIn_zero 1)
        fun _ ↦ polyIn_zero 1
      exact polyIn_sumE_rows u v fun e gk k ↦ by dsimp only; split_ifs <;> ring
    · simp only [splitAt, getD_map_range, ht, ↓reduceIte]
      refine polyIn_ite _ (fun _ ↦ polyIn_ite _ (fun _ ↦ ?_) fun _ ↦ polyIn_zero 1)
        fun _ ↦ polyIn_zero 1
      exact polyIn_sumE_rows u v fun e gk k ↦ by dsimp only; split_ifs <;> ring
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [splitAt, getD_map_range, ht, ↓reduceIte, List.getD_nil] <;>
      exact polyIn_zero 1

/-- Both components of a pair affine in the free coordinate. -/
def PairIn (G : E → E × E) : Prop := PolyIn (fun c ↦ (G c).1) 1 ∧ PolyIn (fun c ↦ (G c).2) 1

/-- The program side's sums at a split whose entries are affine. -/
theorem pairIn_programSums (layout : Layout) (ch : LinkCh) {S : E → Split}
    (hS : ∀ t s, PolyIn (fun c ↦ (S c).count.getD t 0) 1 ∧
      PolyIn (fun c ↦ ((S c).slots.getD t []).getD s 0) 1 ∧
      PolyIn (fun c ↦ ((S c).pc.getD t []).getD s 0) 1) :
    PairIn fun c ↦ programSums layout ch (S c) := by
  simp only [programSums]
  refine foldl_inv PairIn _ _ (fun _ ↦ (0, 0)) ⟨polyIn_zero 1, polyIn_zero 1⟩ fun t _ B hB ↦ ?_
  refine foldl_inv PairIn _ _ _ ⟨?_, hB.2⟩ fun s _ B' hB' ↦ ⟨?_, ?_⟩
  · exact hB.1.add_le (polyIn_cmul _ (hS t 0).1)
  · exact hB'.1.add_le ((polyIn_cmul _ (hS t s).2.1).add_le (polyIn_cmul _ (hS t s).2.2))
  · exact hB'.2.add_le (polyIn_cmul _ (hS t s).2.1)

/-! ## The index side's scalars -/

/-- The index side's scalars, each affine in the free coordinate. -/
def IdxIn (a : E → IdxAt) : Prop :=
  PolyIn (fun c ↦ (a c).eq0R) 1 ∧ PolyIn (fun c ↦ (a c).eqZetaR) 1 ∧
    PolyIn (fun c ↦ (a c).shiftZetaR) 1 ∧ PolyIn (fun c ↦ (a c).xBc) 1 ∧
    PolyIn (fun c ↦ (a c).pFp) 1 ∧ PolyIn (fun c ↦ (a c).yMem) 1 ∧ PolyIn (fun c ↦ (a c).m1) 1

section Point

variable (pre rest : List E) (layout : Layout) (chunks : Chunks)

theorem polyIn_honestM1 {μ : ℕ} (q : Column μ)
    (hw : pre.length + 1 + rest.length = chunks.width) :
    PolyIn (fun c ↦ honestM1 layout chunks q (pre ++ c :: rest)) 1 := by
  unfold honestM1
  by_cases hk : pre.length < layout.logMemory
  · have hb := belowAt_const pre rest chunks (m := layout.logMemory) (by omega)
    set b0 := belowAt chunks (pre ++ (0 : E) :: rest) layout.logMemory
    refine ((polyIn_cmul b0 (polyIn_rowMle_take pre rest layout.logMemory
      (columnValue layout q memory0))).add_le (polyIn_cmul (eY * b0)
        (polyIn_rowMle_take pre rest layout.logMemory (columnValue layout q memory1)))).congr
      fun c ↦ by rw [hb c]
  · have hr := rowMle_take_const pre rest (h := layout.logMemory) (by omega)
    refine ((polyIn_mulc (rowMle ((pre ++ (0 : E) :: rest).take layout.logMemory)
      (columnValue layout q memory0)) (polyIn_belowAt pre rest chunks layout.logMemory)).add_le
        (polyIn_mulc (rowMle ((pre ++ (0 : E) :: rest).take layout.logMemory)
          (columnValue layout q memory1))
          (polyIn_cmul eY (polyIn_belowAt pre rest chunks layout.logMemory)))).congr
      fun c ↦ by rw [hr _ c, hr _ c]

theorem idxIn_idxAt (ch : LinkCh) {m1 : E → E} (hm1 : PolyIn m1 1)
    (hw : pre.length + 1 + rest.length = chunks.width) :
    IdxIn fun c ↦ idxAt layout chunks ch (pre ++ c :: rest) (m1 c)
      (linkSplit layout (pre ++ c :: rest)) := by
  have hxp : PolyIn (fun c ↦ belowAt chunks (pre ++ c :: rest) layout.logBytecode *
        (ch.etaBc * (eqKernel ch.alpha).getD 2 0 +
          (programSums layout ch (linkSplit layout (pre ++ c :: rest))).1)) 1 ∧
      PolyIn (fun c ↦ belowAt chunks (pre ++ c :: rest) layout.logBytecode *
        (programSums layout ch (linkSplit layout (pre ++ c :: rest))).2) 1 := by
    by_cases hk : pre.length < layout.logBytecode
    · have hb := belowAt_const pre rest chunks (m := layout.logBytecode) (by omega)
      set b0 := belowAt chunks (pre ++ (0 : E) :: rest) layout.logBytecode
      have hsplit : ∀ c, linkSplit layout (pre ++ c :: rest) =
          splitAt layout.bytecode (pre.drop 0 ++ c ::
            rest.take (layout.logBytecode - (pre.length - 0) - 1)) (pcSlots layout.tables) := by
        intro c
        rw [linkSplit, take_eq_window, window_split (by omega) (by omega)]
      have hp := pairIn_programSums layout ch (S := fun c ↦ splitAt layout.bytecode (pre.drop 0 ++
        c :: rest.take (layout.logBytecode - (pre.length - 0) - 1)) (pcSlots layout.tables))
        fun t s ↦ polyIn_splitAt _ _ _ _ t s
      refine ⟨(polyIn_cmul b0 (((PolyIn.const (ch.etaBc * (eqKernel ch.alpha).getD 2 0)).mono
        (Nat.zero_le 1)).add_le hp.1)).congr fun c ↦ by rw [hb c, hsplit],
        (polyIn_cmul b0 hp.2).congr fun c ↦ by rw [hb c, hsplit]⟩
    · have hsplit : ∀ c, linkSplit layout (pre ++ c :: rest) = linkSplit layout (pre ++ 0 :: rest) :=
        fun c ↦ by rw [linkSplit, linkSplit, take_eq_window, take_eq_window (pre ++ _ :: rest),
          window_const (by omega) c 0]
      refine ⟨(polyIn_mulc _ (polyIn_belowAt pre rest chunks _)).congr fun c ↦ by rw [hsplit c],
        (polyIn_mulc _ (polyIn_belowAt pre rest chunks _)).congr fun c ↦ by rw [hsplit c]⟩
  refine ⟨polyIn_belowAt pre rest chunks 0, polyIn_eqEval pre rest ch.zeta,
    polyIn_linkShiftEq pre rest ch.zeta,
    (polyIn_cmul _ (polyIn_indexMle pre rest)).add_le hxp.1, hxp.2,
    ((polyIn_cmul _ (polyIn_indexMle pre rest)).add_le
      (polyIn_cmul _ (polyIn_belowAt pre rest chunks _))).add_le (polyIn_cmul _ hm1), hm1⟩

end Point

/-! ## The row side's fold -/

/-- Two row sides agree but on the coefficient, the shifts' values and the base. -/
def SameShape (x y : LinkRowSide) : Prop :=
  x.certWeight = y.certWeight ∧ x.pieces = y.pieces ∧ x.q = y.q ∧ x.columns = y.columns ∧
    x.sent = y.sent ∧ x.shifts.length = y.shifts.length

/-- The row side as a function of the free coordinate: its coefficient, shifts and base affine,
the rest constant. -/
def RowIn (A : E → LinkRowSide) : Prop :=
  (∀ c, SameShape (A c) (A 0)) ∧ PolyIn (fun c ↦ (A c).coef) 1 ∧ PolyIn (fun c ↦ (A c).base) 1 ∧
    ∀ s, PolyIn (fun c ↦ (A c).shifts.getD s 0) 1

/-- A coefficient and shifts, affine in the free coordinate, the shifts' count constant. -/
def ShiftIn (G : E → E × List E) : Prop :=
  PolyIn (fun c ↦ (G c).1) 1 ∧ (∀ c, (G c).2.length = (G 0).2.length) ∧
    ∀ s, PolyIn (fun c ↦ (G c).2.getD s 0) 1

theorem RowIn.congr {A A' : E → LinkRowSide} (h : RowIn A) (hA : ∀ c, A c = A' c) : RowIn A' := by
  obtain rfl : A = A' := funext hA
  exact h

theorem rowIn_const (S : LinkRowSide) : RowIn fun _ ↦ S :=
  ⟨fun _ ↦ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, polyIn_of_const (fun _ ↦ rfl) 1,
    polyIn_of_const (fun _ ↦ rfl) 1, fun _ ↦ polyIn_of_const (fun _ ↦ rfl) 1⟩

theorem rowIn_columns {X : E → LinkRowSide} (hX : RowIn X) (p : List E × List (ℕ × E)) :
    RowIn fun c ↦ { X c with columns := (X c).columns ++ [p] } := by
  obtain ⟨hs, h1, h2, h3⟩ := hX
  exact ⟨fun c ↦ ⟨(hs c).1, (hs c).2.1, (hs c).2.2.1, congrArg (· ++ [p]) (hs c).2.2.2.1,
    (hs c).2.2.2.2.1, (hs c).2.2.2.2.2⟩, h1, h2, h3⟩

theorem rowIn_start {B : E → LinkRowSide} (hB : RowIn B) {g : E → E} (hg : PolyIn g 1)
    (s0 : List E) : RowIn fun c ↦ { B c with base := (B c).base + g c, sent := s0 } := by
  obtain ⟨hs, h1, h2, h3⟩ := hB
  exact ⟨fun c ↦ ⟨(hs c).1, (hs c).2.1, (hs c).2.2.1, (hs c).2.2.2.1, rfl, (hs c).2.2.2.2.2⟩, h1,
    h2.add_le hg, h3⟩

/-- The word reads' part of a memory pointer's coefficient (`ptrStep`). -/
def wordCoef (ch : LinkCh) (a : IdxAt) (e omega : E) (table : Table) (t pointer : ℕ)
    (col : ℕ → E) (coef : E) : E :=
  (table.links.memory.zip (ch.mu.getD t [])).foldl (fun coef (access, m) ↦
    access.reads.foldl (fun coef read ↦
      match read with
      | .word p scale =>
        if p = pointer then
          coef + e * omega * ch.etaMem * m * ch.gammaMem.getD 1 0 * a.m1 * scale.evaluate col
        else coef
      | _ => coef) coef) coef

/-- The accesses' part of a memory pointer's coefficient and shifts (`ptrStep`). -/
def accessCoef (ch : LinkCh) (a : IdxAt) (e omega : E) (table : Table) (t pointer : ℕ)
    (col : ℕ → E) (cs : E × List E) : E × List E :=
  ((table.links.memory.zip (ch.mu.getD t [])).filter (·.1.pointer = pointer)).foldl
    (fun (cs : E × List E) (access, m) ↦
      let c := e * omega * (access.gate.map col).getD 1 * ch.etaMem * m * a.yMem
      match access.shift with
      | 0 => (cs.1 + c, cs.2)
      | s + 1 => (cs.1, addAtSlot cs.2 s c)) cs

theorem polyIn_wordCoef (ch : LinkCh) {a : E → IdxAt} (ha : IdxIn a) (e omega : E) (table : Table)
    (t pointer : ℕ) (col : ℕ → E) {g : E → E} (hg : PolyIn g 1) :
    PolyIn (fun c ↦ wordCoef ch (a c) e omega table t pointer col (g c)) 1 := by
  unfold wordCoef
  refine foldl_inv (fun g : E → E ↦ PolyIn g 1) _ _ _ hg fun x _ B hB ↦ ?_
  obtain ⟨access, m⟩ := x
  dsimp only
  refine foldl_inv (fun g : E → E ↦ PolyIn g 1) _ _ _ hB fun read _ B' hB' ↦ ?_
  cases read with
  | word p scale =>
    by_cases hp : p = pointer
    · simp only [hp, ↓reduceIte]
      exact hB'.add_le (polyIn_mulc _ (polyIn_cmul _ ha.2.2.2.2.2.2))
    · simp only [hp, ↓reduceIte]
      exact hB'
  | slot _ _ => exact hB'
  | frame _ _ => exact hB'
  | pc _ _ => exact hB'

theorem shiftIn_accessCoef (ch : LinkCh) {a : E → IdxAt} (ha : IdxIn a) (e omega : E)
    (table : Table) (t pointer : ℕ) (col : ℕ → E) {G : E → E × List E} (hG : ShiftIn G) :
    ShiftIn fun c ↦ accessCoef ch (a c) e omega table t pointer col (G c) := by
  unfold accessCoef
  refine foldl_inv ShiftIn _ _ _ hG fun x _ B hB ↦ ?_
  obtain ⟨⟨ptr, shift, gate, address, frame, value, reads⟩, m⟩ := x
  have hy : PolyIn (fun c ↦ e * omega * (gate.map col).getD 1 * ch.etaMem * m * (a c).yMem) 1 :=
    polyIn_cmul _ ha.2.2.2.2.2.1
  cases shift with
  | zero =>
    dsimp only
    exact ⟨hB.1.add_le hy, hB.2.1, hB.2.2⟩
  | succ s =>
    dsimp only
    refine ⟨hB.1, fun c ↦ by rw [length_addAtSlot, length_addAtSlot, hB.2.1 c], fun j ↦ ?_⟩
    exact (polyIn_ite (j = s ∧ s < (B 0).2.length) (fun _ ↦ (hB.2.2 j).add_le hy)
      fun _ ↦ hB.2.2 j).congr fun c ↦ by rw [getD_addAtSlot, hB.2.1 c]

/-- `tableBaseOf` reads `eq(0, r)` alone, linearly. -/
theorem tableBaseOf_eq (ch : LinkCh) (a : IdxAt) (jump point : List E) (height : ℕ) (omega : E)
    (table : Table) (t : ℕ) (values : List E) :
    tableBaseOf ch a jump point height omega table t values =
      tableBaseOf ch ⟨0, 0, 0, 0, 0, 0, 0⟩ jump point height omega table t values +
        a.eq0R * (tableBaseOf ch ⟨1, 0, 0, 0, 0, 0, 0⟩ jump point height omega table t values -
          tableBaseOf ch ⟨0, 0, 0, 0, 0, 0, 0⟩ jump point height omega table t values) := by
  simp only [tableBaseOf]
  split_ifs <;> ring

theorem polyIn_tableBaseOf (ch : LinkCh) {a : E → IdxAt} (ha : IdxIn a) (jump point : List E)
    (height : ℕ) (omega : E) (table : Table) (t : ℕ) (values : List E) :
    PolyIn (fun c ↦ tableBaseOf ch (a c) jump point height omega table t values) 1 := by
  set T0 := tableBaseOf ch ⟨0, 0, 0, 0, 0, 0, 0⟩ jump point height omega table t values
  set T1 := tableBaseOf ch ⟨1, 0, 0, 0, 0, 0, 0⟩ jump point height omega table t values
  exact (((PolyIn.const T0).mono (Nat.zero_le 1)).add_le (polyIn_mulc (T1 - T0) ha.1)).congr
    fun c ↦ (tableBaseOf_eq ch (a c) jump point height omega table t values).symm

section Ptr

variable (layout : Layout) (ch : LinkCh) (eqQ point : List E) (corner omega act sHat sNext : E)
  (table : Table) (t : ℕ) (col : ℕ → E)

theorem ptrStep_shape (a a' : IdxAt) (acc acc' : LinkRowSide) (x : ℕ × ℕ)
    (h : SameShape acc acc')
    (hlen : (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc x).shifts.length =
      (ptrStep layout ch a' eqQ point corner omega act sHat sNext table t col acc' x).shifts.length) :
    SameShape (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc x)
      (ptrStep layout ch a' eqQ point corner omega act sHat sNext table t col acc' x) := by
  obtain ⟨pointer, k⟩ := x
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := h
  refine ⟨?_, ?_, ?_, h4, h5, hlen⟩
  · show acc.certWeight + eqQ.getD acc.q 0 * corner * omega * ch.eps.getD acc.q 0 =
      acc'.certWeight + eqQ.getD acc'.q 0 * corner * omega * ch.eps.getD acc'.q 0
    rw [h1, h3]
  · show acc.pieces ++ [(⟨_, point, eqQ.getD acc.q 0⟩ : RingPiece)] =
      acc'.pieces ++ [(⟨_, point, eqQ.getD acc'.q 0⟩ : RingPiece)]
    rw [h2, h3]
  · show acc.q + 1 = acc'.q + 1
    rw [h3]

theorem ptrStep_zero (a : IdxAt) (acc : LinkRowSide) (pointer : ℕ) :
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (pointer, 0)).coef =
      acc.coef + eqQ.getD acc.q 0 * corner * act * (a.eqZetaR * sHat + a.shiftZetaR * sNext) ∧
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (pointer, 0)).shifts =
      acc.shifts := ⟨rfl, rfl⟩

theorem ptrStep_one (a : IdxAt) (acc : LinkRowSide) (pointer : ℕ) :
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (pointer, 0 + 1)).coef =
      acc.coef + eqQ.getD acc.q 0 * corner * omega *
        (a.xBc + col table.links.stateLink.fp * a.pFp) ∧
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc
      (pointer, 0 + 1)).shifts = acc.shifts := ⟨rfl, rfl⟩

theorem ptrStep_two (a : IdxAt) (acc : LinkRowSide) (pointer k : ℕ) :
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc
      (pointer, k + 1 + 1)).coef =
      (accessCoef ch a (eqQ.getD acc.q 0 * corner) omega table t pointer col
        (wordCoef ch a (eqQ.getD acc.q 0 * corner) omega table t pointer col acc.coef,
          acc.shifts)).1 ∧
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc
      (pointer, k + 1 + 1)).shifts =
      (accessCoef ch a (eqQ.getD acc.q 0 * corner) omega table t pointer col
        (wordCoef ch a (eqQ.getD acc.q 0 * corner) omega table t pointer col acc.coef,
          acc.shifts)).2 := ⟨rfl, rfl⟩

theorem rowIn_ptrStep {a : E → IdxAt} (ha : IdxIn a) {B : E → LinkRowSide} (hB : RowIn B)
    (x : ℕ × ℕ) :
    RowIn fun c ↦ ptrStep layout ch (a c) eqQ point corner omega act sHat sNext table t col (B c) x := by
  obtain ⟨pointer, k⟩ := x
  obtain ⟨hs, hco, hba, hsh⟩ := hB
  have hq : ∀ c, (B c).q = (B 0).q := fun c ↦ (hs c).2.2.1
  have hlen : ∀ c, (B c).shifts.length = (B 0).shifts.length := fun c ↦ (hs c).2.2.2.2.2
  have hbase : PolyIn (fun c ↦ (ptrStep layout ch (a c) eqQ point corner omega act sHat sNext table
      t col (B c) (pointer, k)).base) 1 := hba.congr fun _ ↦ rfl
  rcases k with _ | _ | k
  · have e := fun c ↦ ptrStep_zero layout ch eqQ point corner omega act sHat sNext table t col
      (a c) (B c) pointer
    refine ⟨fun c ↦ ptrStep_shape layout ch eqQ point corner omega act sHat sNext table t col _ _ _ _
      _ (hs c) (by rw [(e c).2, (e 0).2, hlen c]), ?_, hbase,
      fun s ↦ (hsh s).congr fun c ↦ by rw [(e c).2]⟩
    exact (hco.add_le (polyIn_cmul (eqQ.getD (B 0).q 0 * corner * act)
      ((polyIn_mulc sHat ha.2.1).add_le (polyIn_mulc sNext ha.2.2.1)))).congr
      fun c ↦ by rw [(e c).1, hq c]
  · have e := fun c ↦ ptrStep_one layout ch eqQ point corner omega act sHat sNext table t col
      (a c) (B c) pointer
    refine ⟨fun c ↦ ptrStep_shape layout ch eqQ point corner omega act sHat sNext table t col _ _ _ _
      _ (hs c) (by rw [(e c).2, (e 0).2, hlen c]), ?_, hbase,
      fun s ↦ (hsh s).congr fun c ↦ by rw [(e c).2]⟩
    exact (hco.add_le (polyIn_cmul (eqQ.getD (B 0).q 0 * corner * omega)
      (ha.2.2.2.1.add_le (polyIn_cmul (col table.links.stateLink.fp) ha.2.2.2.2.1)))).congr
      fun c ↦ by rw [(e c).1, hq c]
  · have e := fun c ↦ ptrStep_two layout ch eqQ point corner omega act sHat sNext table t col
      (a c) (B c) pointer k
    set e0 := eqQ.getD (B 0).q 0 * corner with he0
    have hG : ShiftIn fun c ↦ accessCoef ch (a c) e0 omega table t pointer col
        (wordCoef ch (a c) e0 omega table t pointer col (B c).coef, (B c).shifts) :=
      shiftIn_accessCoef ch ha e0 omega table t pointer col
        ⟨polyIn_wordCoef ch ha e0 omega table t pointer col hco, hlen, hsh⟩
    have hrw : ∀ c, eqQ.getD (B c).q 0 * corner = e0 := fun c ↦ by rw [hq c]
    refine ⟨fun c ↦ ptrStep_shape layout ch eqQ point corner omega act sHat sNext table t col _ _ _ _
      _ (hs c) ?_, hG.1.congr fun c ↦ by rw [(e c).1, hrw c], hbase,
      fun s ↦ (hG.2.2 s).congr fun c ↦ by rw [(e c).2, hrw c]⟩
    rw [(e c).2, (e 0).2, hrw c, hrw 0]
    exact hG.2.1 c

end Ptr

/-- `rowStep` with the values it reads given (`sent0` for `acc.sent`). -/
def rowStepAt (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi : List E)
    (sent0 : List E) (acc : LinkRowSide) (table : Table) (t : ℕ) : LinkRowSide :=
  let height := layout.tableLogHeights.getD t 0
  let tableRows := layout.tableRows.getD t 0
  let point := chi.take height
  let corner := prodE ((chi.drop height).map (1 + ·))
  let columns := nonPointerOf layout t table
  let sent := columns.zip (sent0.take columns.length)
  let values := (List.range table.width).map fun c ↦ (sent.lookup c).getD 0
  let col := fun (c : ℕ) ↦ values.getD c 0
  let state := table.links.stateLink
  let omega := omegaAt (ch.theta.getD t 0) (ch.tau.take height) point tableRows
  let act := lessThan point tableRows
  let sHat := ch.stateGamma (col state.pc) (col state.fp)
  let sNext := ch.stateGamma (state.next.1.evaluate col) (state.next.2.evaluate col)
  let tableBase := tableBaseOf ch a jump point height omega table t values
  let acc := (((layout.tables.map (·.links.pointers)).getD t []).zipIdx.foldl
    (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col))
    { acc with base := acc.base + corner * tableBase, sent := sent0.drop columns.length }
  { acc with columns := acc.columns ++ [(point, sent)] }

theorem rowStep_eq_at (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi : List E)
    (acc : LinkRowSide) (table : Table) (t : ℕ) :
    rowStep layout ch a jump eqQ chi acc (table, t) =
      rowStepAt layout ch a jump eqQ chi acc.sent acc table t := by
  simp only [rowStep, rowStepAt]

theorem rowIn_rowStepAt (layout : Layout) (ch : LinkCh) {a : E → IdxAt} (ha : IdxIn a)
    (jump eqQ chi sent0 : List E) (table : Table) (t : ℕ) {B : E → LinkRowSide} (hB : RowIn B) :
    RowIn fun c ↦ rowStepAt layout ch (a c) jump eqQ chi sent0 (B c) table t := by
  simp only [rowStepAt]
  refine rowIn_columns ?_ _
  refine foldl_inv RowIn _ _ _ ?_ fun x _ B' hB' ↦ rowIn_ptrStep _ _ _ _ _ _ _ _ _ _ _ _ ha hB' x
  exact rowIn_start hB (polyIn_cmul _ (polyIn_tableBaseOf ch ha _ _ _ _ _ _ _)) _

/-- **The row side's fold is affine in the free coordinate** when the index side's scalars are. -/
theorem rowIn_rowSideOf (layout : Layout) (ch : LinkCh) {a : E → IdxAt} (ha : IdxIn a)
    (jump eqQ chi message : List E) :
    RowIn fun c ↦ rowSideOf layout ch (a c) jump eqQ chi message := by
  unfold rowSideOf
  refine foldl_inv RowIn _ _ (fun _ ↦ rowStart layout message) (rowIn_const _)
    fun x _ B hB ↦ ?_
  obtain ⟨table, t⟩ := x
  exact (rowIn_rowStepAt layout ch ha jump eqQ chi (B 0).sent table t hB).congr fun c ↦ by
    rw [rowStep_eq_at, (hB.1 c).2.2.2.2.1]

/-! ## The chunks -/

theorem exclusivePrefix_foldl : ∀ (sizes L : List ℕ) (s : ℕ),
    sizes.foldl (fun (acc : List ℕ × ℕ) size ↦ (acc.1 ++ [acc.2], acc.2 + size)) (L, s) =
      (L ++ (List.range sizes.length).map (fun i ↦ s + (sizes.take i).sum), s + sizes.sum)
  | [], L, s => by simp
  | x :: xs, L, s => by
    rw [List.foldl_cons, exclusivePrefix_foldl xs]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.take_zero, List.sum_nil, add_zero, List.sum_cons, List.append_assoc,
      List.singleton_append, Prod.mk.injEq]
    refine ⟨?_, by ring⟩
    congr 2
    exact List.map_congr_left fun i _ ↦ by simp [List.take_succ_cons, add_assoc]

theorem getD_exclusivePrefix (sizes : List ℕ) {i : ℕ} (hi : i < sizes.length) :
    (exclusivePrefix sizes).getD i 0 = (sizes.take i).sum := by
  rw [exclusivePrefix, exclusivePrefix_foldl]
  simp [hi]

theorem take_sum_le {l : List ℕ} {i j : ℕ} (h : i ≤ j) : (l.take i).sum ≤ (l.take j).sum := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.sum_append]
  omega

theorem take_succ_sum {l : List ℕ} {i : ℕ} (h : i < l.length) :
    (l.take (i + 1)).sum = (l.take i).sum + l.getD i 0 := by
  rw [List.take_add_one, List.sum_append, List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h]
  simp

theorem chunks_of_new {w : ℕ} {chunks : Chunks} (hc : Chunks.new w = some chunks) :
    chunks.indexShifts = exclusivePrefix chunks.widths ∧ 0 < chunks.d := by
  unfold Chunks.new at hc
  split_ifs at hc
  obtain rfl := Option.some.inj hc
  exact ⟨rfl, by simp [Chunks.d]⟩

/-- Chunk `i` holds the coordinate `k`. -/
def Hit (chunks : Chunks) (k i : ℕ) : Prop :=
  chunks.indexShifts.getD i 0 ≤ k ∧ k < chunks.indexShifts.getD i 0 + chunks.widths.getD i 0

/-- **The chunks are disjoint**: at most one holds a coordinate. -/
theorem chunk_disjoint {w : ℕ} {chunks : Chunks} (hc : Chunks.new w = some chunks) (k : ℕ) :
    ∃ i0, ∀ i < chunks.d, i ≠ i0 → ¬ Hit chunks k i := by
  have hs : ∀ i < chunks.d, chunks.indexShifts.getD i 0 = (chunks.widths.take i).sum :=
    fun i hi ↦ by rw [(chunks_of_new hc).1, getD_exclusivePrefix _ hi]
  have key : ∀ i j, i < j → j < chunks.d → Hit chunks k i → ¬ Hit chunks k j := by
    intro i j hij hj hi hj'
    have h1 := take_succ_sum (l := chunks.widths) (i := i) (by simp [Chunks.d] at hj; omega)
    have h2 := take_sum_le (l := chunks.widths) (show i + 1 ≤ j by omega)
    unfold Hit at hi hj'
    rw [hs i (by omega)] at hi
    rw [hs j hj] at hj'
    omega
  by_cases hex : ∃ i < chunks.d, Hit chunks k i
  · obtain ⟨i0, hi0, hk⟩ := hex
    refine ⟨i0, fun i hi hne hki ↦ ?_⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i i0 h hi0 hki hk
    · exact key i0 i h hi hk hki
  · exact ⟨0, fun i hi _ hki ↦ hex ⟨i, hi, hki⟩⟩

/-! ## The functionals -/

theorem getD_drop' (l : List E) (a j : ℕ) : (l.drop a).getD j 0 = l.getD (a + j) 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_take_drop (l : List E) {a b j : ℕ} (hj : j < b) :
    ((l.drop a).take b).getD j 0 = l.getD (a + j) 0 := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem getD_reverse_of_lt (l : List E) {j : ℕ} (hj : j < l.length) :
    l.reverse.getD j 0 = l.getD (l.length - 1 - j) 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_reverse,
    List.getD_eq_getElem _ _ (by omega)]

/-- The chunk functional `j` reads. -/
def chunkOf (d j : ℕ) : ℕ := if j < d then j else if j < 2 * d then j - d else 0

/-- Functional `j`'s table from its chunk's coordinates. -/
def tableOf (d j : ℕ) (p : List E) : List E :=
  if j < d then eqKernel p
  else if j < 2 * d then (eqKernel p).reverse
  else linkWindowShift (eqKernel p) (j - 2 * d + 1)

/-- Entry `i` of functional `j`'s table is the kernel's entry `tableIdx d j n i`. -/
def tableIdx (d j n i : ℕ) : ℕ :=
  if j < d then i else if j < 2 * d then 2 ^ n - 1 - i else i + (j - 2 * d + 1)

theorem length_tableOf (d j : ℕ) (p : List E) : (tableOf d j p).length = 2 ^ p.length := by
  unfold tableOf linkWindowShift
  split_ifs <;> simp [eqKernel_length]

theorem getD_tableOf (d j : ℕ) (p : List E) {i : ℕ} (hi : i < 2 ^ p.length) :
    (tableOf d j p).getD i 0 = (eqKernel p).getD (tableIdx d j p.length i) 0 := by
  unfold tableOf tableIdx
  split_ifs with h1 h2
  · rfl
  · rw [getD_reverse_of_lt _ (by rw [eqKernel_length]; exact hi), eqKernel_length]
  · unfold linkWindowShift
    rw [getD_map_range, ite_eq_left_of_eq_true _ _ (eq_true (by rw [eqKernel_length]; exact hi))]

theorem polyIn_tableOf_sum (d j : ℕ) (S u v : List E) :
    PolyIn (fun c ↦ sumE (List.zipWith (· * ·) (tableOf d j (u ++ c :: v)) S)) 1 := by
  have hl : ∀ c : E, (u ++ c :: v).length = u.length + 1 + v.length := fun c ↦ by simp; omega
  refine polyIn_sumE (fun c ↦ by simp [length_tableOf, hl]) fun i hi ↦ ?_
  simp only [List.length_zipWith, length_tableOf, hl, lt_min_iff] at hi
  refine (polyIn_mulc (S.getD i 0) (polyIn_eqKernel u v
    (tableIdx d j (u.length + 1 + v.length) i))).congr fun c ↦ ?_
  rw [getD_zipWith_of_lt _ _ _ (by rw [length_tableOf, hl]; exact hi.1) hi.2,
    getD_tableOf _ _ _ (by rw [hl]; exact hi.1), hl]

theorem tables_eq (chunks : Chunks) (r : List E) (ms : ℕ) (hd : 0 < chunks.d) :
    (Functionals.new chunks r ms).tables =
      (List.range chunks.d).map (fun i ↦ (i, eqKernel (chunks.part r i))) ++
      (List.range chunks.d).map (fun i ↦ (i, (eqKernel (chunks.part r i)).reverse)) ++
      (List.range ms).map (fun s ↦ (0, linkWindowShift (eqKernel (chunks.part r 0)) (s + 1))) := by
  have hz : (List.range chunks.d).zip ((List.range chunks.d).map fun i ↦
      eqKernel (chunks.part r i)) = (List.range chunks.d).map (fun i ↦ (i, eqKernel (chunks.part r i))) :=
    List.ext_getElem (by simp) fun n h1 h2 ↦ by simp
  have hh : ((List.range chunks.d).map fun i ↦ eqKernel (chunks.part r i)).headD [] =
      eqKernel (chunks.part r 0) := by
    obtain ⟨d', hd'⟩ : ∃ d', chunks.d = d' + 1 := ⟨chunks.d - 1, by omega⟩
    rw [hd', List.range_succ_eq_map]
    rfl
  simp only [Functionals.new, hz, hh, List.map_map]
  rfl

theorem values_getD (chunks : Chunks) (r : List E) (ms : ℕ) (slices : List E) (hd : 0 < chunks.d)
    (j : ℕ) : ((Functionals.new chunks r ms).values chunks slices).getD j 0 =
      if j < 2 * chunks.d + ms then sumE (List.zipWith (· * ·)
        (tableOf chunks.d j (chunks.part r (chunkOf chunks.d j)))
        (slices.drop (chunks.wordShifts.getD (chunkOf chunks.d j) 0))) else 0 := by
  unfold Functionals.values
  rw [tables_eq chunks r ms hd]
  split_ifs with hj
  · rw [getD_map_of_lt _ _ (by simp; omega) (0, [])]
    by_cases h1 : j < chunks.d
    · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
        getD_map_range, ite_eq_left_of_eq_true _ _ (eq_true h1)]
      simp [chunkOf, tableOf, h1]
    · by_cases h2 : j < 2 * chunks.d
      · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega),
          List.length_map, List.length_range, getD_map_range, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
        simp [chunkOf, tableOf, h1, h2]
      · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_append, List.length_map,
          List.length_map, List.length_range, getD_map_range,
          ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
        have h2' : ¬ j < chunks.d + chunks.d := by omega
        simp [chunkOf, tableOf, h1, h2', two_mul]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem length_values (chunks : Chunks) (r : List E) (ms : ℕ) (slices : List E) (hd : 0 < chunks.d) :
    ((Functionals.new chunks r ms).values chunks slices).length = 2 * chunks.d + ms := by
  unfold Functionals.values
  rw [tables_eq chunks r ms hd]
  simp
  ring

theorem getD_mirrors (chunks : Chunks) (r : List E) (ms i : ℕ) :
    (Functionals.new chunks r ms).mirrors.getD i 0 =
      if i < chunks.d then prodE ((chunks.part r i).map fun x ↦ x * (1 + x)) else 0 :=
  getD_map_range _ _ _ _

section Summand

variable {w : ℕ} {chunks : Chunks} (hc : Chunks.new w = some chunks) (pre rest : List E) (ms : ℕ)
  (slices : List E)

include hc

theorem polyIn_values (j : ℕ) :
    PolyIn (fun c ↦ ((Functionals.new chunks (pre ++ c :: rest) ms).values chunks slices).getD j 0)
      1 := by
  have hd := (chunks_of_new hc).2
  refine (polyIn_ite (j < 2 * chunks.d + ms) (fun _ ↦ polyIn_window pre rest
    (chunks.indexShifts.getD (chunkOf chunks.d j) 0) (chunks.widths.getD (chunkOf chunks.d j) 0)
    (F := fun p ↦ sumE (List.zipWith (· * ·) (tableOf chunks.d j p)
      (slices.drop (chunks.wordShifts.getD (chunkOf chunks.d j) 0))))
    fun u v ↦ polyIn_tableOf_sum chunks.d j _ u v) fun _ ↦ polyIn_zero 1).congr fun c ↦ ?_
  rw [values_getD _ _ _ _ hd]
  rfl

theorem values_const {j : ℕ} (h : ¬ Hit chunks pre.length (chunkOf chunks.d j)) (c : E) :
    ((Functionals.new chunks (pre ++ c :: rest) ms).values chunks slices).getD j 0 =
      ((Functionals.new chunks (pre ++ (0 : E) :: rest) ms).values chunks slices).getD j 0 := by
  have hd := (chunks_of_new hc).2
  rw [values_getD _ _ _ _ hd, values_getD _ _ _ _ hd]
  unfold Chunks.part
  rw [window_const h c 0]

omit hc in
theorem polyIn_mirror (i : ℕ) :
    PolyIn (fun c ↦ (Functionals.new chunks (pre ++ c :: rest) ms).mirrors.getD i 0) 2 := by
  refine (polyIn_ite (i < chunks.d) (fun _ ↦ polyIn_window pre rest
    (chunks.indexShifts.getD i 0) (chunks.widths.getD i 0) (F := fun p ↦ prodE (p.map fun x ↦
      x * (1 + x))) fun u v ↦ polyIn_prodE_map u v ((PolyIn.var.mul
        ((PolyIn.const 1).add PolyIn.var)).mono (by simp))) fun _ ↦ polyIn_zero 2).congr
    fun c ↦ ?_
  rw [getD_mirrors]
  rfl

/-- **The pointer word's summand is of degree two** in a free index coordinate, when the
coefficient and shifts are affine. -/
theorem polyIn_summand (certs : List E) {co : E → E} {sh : E → List E} (hco : PolyIn co 1)
    (hshl : ∀ c, (sh c).length = (sh 0).length) (hsh : ∀ s, PolyIn (fun c ↦ (sh c).getD s 0) 1) :
    PolyIn (fun c ↦ (Functionals.new chunks (pre ++ c :: rest) ms).summand (co c) (sh c)
      ((Functionals.new chunks (pre ++ c :: rest) ms).values chunks slices) certs) 2 := by
  have hd := (chunks_of_new hc).2
  set d := chunks.d with hdd
  set V : E → List E := fun c ↦ (Functionals.new chunks (pre ++ c :: rest) ms).values chunks slices
  have hV1 : ∀ j, PolyIn (fun c ↦ (V c).getD j 0) 1 := polyIn_values hc pre rest ms slices
  have hVc : ∀ j, ¬ Hit chunks pre.length (chunkOf d j) → ∀ c, (V c).getD j 0 = (V 0).getD j 0 :=
    fun j h c ↦ values_const hc pre rest ms slices h c
  have hlenV : ∀ c, (V c).length = 2 * d + ms := fun c ↦ length_values _ _ _ _ hd
  -- the certificate
  have hcert : PolyIn (fun c ↦ sumE ((List.range d).map fun i ↦ certs.getD i 0 *
      ((V c).getD i 0 * (V c).getD (d + i) 0 +
        (Functionals.new chunks (pre ++ c :: rest) ms).mirrors.getD i 0))) 2 :=
    (PolyIn.listSum (List.range d) (f := fun i c ↦ certs.getD i 0 *
      ((V c).getD i 0 * (V c).getD (d + i) 0 +
        (Functionals.new chunks (pre ++ c :: rest) ms).mirrors.getD i 0)) fun i _ ↦
      polyIn_cmul _ (((hV1 i).mul (hV1 (d + i))).add_le (polyIn_mirror pre rest ms i))).congr
      fun c ↦ by rw [sumE_eq]
  -- the shifted reads
  have hlow : ∀ e, (∀ j, PolyIn (fun c ↦ (V c).getD (2 * d + j) 0) e) →
      PolyIn (fun c ↦ sumE (List.zipWith (· * ·) (sh c) ((V c).drop (2 * d)))) (1 + e) := by
    intro e he
    refine polyIn_sumE (fun c ↦ by simp [hshl c, hlenV c, hlenV 0]) fun j hj ↦ ?_
    simp only [List.length_zipWith, List.length_drop, lt_min_iff] at hj
    refine ((hsh j).mul (he j)).congr fun c ↦ ?_
    rw [getD_zipWith_of_lt _ _ _ (by rw [hshl c]; exact hj.1)
      (by rw [List.length_drop, hlenV c]; rw [hlenV 0] at hj; exact hj.2), getD_drop']
  -- the other chunks' product
  have hrestL : ∀ c, ((V c).drop 1 |>.take (d - 1)).length = ((V 0).drop 1 |>.take (d - 1)).length :=
    fun c ↦ by simp [hlenV c, hlenV 0]
  have hrestE : ∀ j, j < ((V 0).drop 1 |>.take (d - 1)).length → ∀ c,
      ((V c).drop 1 |>.take (d - 1)).getD j 0 = (V c).getD (1 + j) 0 := fun j hj c ↦
    getD_take_drop _ (by simp at hj; omega)
  obtain ⟨i0, hi0⟩ := chunk_disjoint hc pre.length
  simp only [Functionals.summand]
  by_cases h0 : i0 = 0
  · -- every other chunk misses the coordinate: the product is constant
    have hrest : PolyIn (fun c ↦ prodE ((V c).drop 1 |>.take (d - 1))) 0 :=
      polyIn_prodE_one d hrestL (fun j hj _ c ↦ by
        rw [hrestE j hj c, hrestE j hj 0]
        exact hVc (1 + j) (by
          have : 1 + j < d := by simp at hj; omega
          rw [show chunkOf d (1 + j) = 1 + j by simp [chunkOf, this]]
          exact hi0 (1 + j) this (by omega)) c)
        fun h ↦ absurd h (by simp)
    exact ((((hco.mul (hV1 0)).add_le (hlow 1 fun j ↦ hV1 (2 * d + j))).mul hrest).add_le
      hcert).mono (by simp) |>.congr fun c ↦ rfl
  · -- chunk `0` misses the coordinate
    have hm0 : ¬ Hit chunks pre.length 0 := hi0 0 hd (Ne.symm h0)
    have hv0 : PolyIn (fun c ↦ co c * (V c).getD 0 0) 1 :=
      (polyIn_mulc ((V 0).getD 0 0) hco).congr fun c ↦ by
        rw [hVc 0 (by simpa [chunkOf, hd] using hm0) c]
    have hT : ∀ j, PolyIn (fun c ↦ (V c).getD (2 * d + j) 0) 0 := fun j ↦
      polyIn_of_const (fun c ↦ hVc (2 * d + j) (by
        rw [show chunkOf d (2 * d + j) = 0 by simp [chunkOf]; omega]
        exact hm0) c) 0
    have hrest : PolyIn (fun c ↦ prodE ((V c).drop 1 |>.take (d - 1))) 1 :=
      polyIn_prodE_one (i0 - 1) hrestL (fun j hj hne c ↦ by
        rw [hrestE j hj c, hrestE j hj 0]
        exact hVc (1 + j) (by
          have : 1 + j < d := by simp at hj; omega
          rw [show chunkOf d (1 + j) = 1 + j by simp [chunkOf, this]]
          exact hi0 (1 + j) this (by omega)) c)
        fun hj ↦ (hV1 (1 + (i0 - 1))).congr fun c ↦ (hrestE _ hj c).symm
    exact ((((hv0.add_le ((hlow 0 hT).mono (by omega))).mul hrest)).add_le hcert).mono
      (by simp) |>.congr fun c ↦ rfl

end Summand


/-! ## The row summand and the index side -/

theorem rowSummand_eq (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r fresh x : List E) :
    rowSummand layout chunks q theta0 drawn r fresh x =
      lastOf layout chunks (linkCh layout chunks theta0 drawn) r (fresh.getD 0 0)
        (x.drop (linkRows layout))
        ((honestMessage layout q (x.take (linkRows layout)) (x.drop (linkRows layout))).drop
          (nValuesOf layout))
        (rowSideOf layout (linkCh layout chunks theta0 drawn)
          (idxAt layout chunks (linkCh layout chunks theta0 drawn) r (honestM1 layout chunks q r)
            (linkSplit layout r))
          (fresh.drop 1) (eqKernel (x.drop (linkRows layout))) (x.take (linkRows layout))
          (honestMessage layout q (x.take (linkRows layout)) (x.drop (linkRows layout)))) := rfl

theorem lastOf_eq (layout : Layout) (chunks : Chunks) (ch : LinkCh) (r : List E) (cert : E)
    (qPoint slices : List E) (rs : LinkRowSide) :
    lastOf layout chunks ch r cert qPoint slices rs =
      (Functionals.new chunks r (layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0)).summand
        rs.coef rs.shifts
        ((Functionals.new chunks r (layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0)).values
          chunks slices)
        (ch.nu.map fun n ↦ cert * rs.certWeight * n) + prodE (qPoint.map (1 + ·)) * rs.base := rfl

/-- **The row summand is of degree two in each index variable.** -/
theorem polyIn_rowSummand {layout : Layout} {w : ℕ} {chunks : Chunks}
    (hc : Chunks.new w = some chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn fresh x pre rest : List E) (hw : pre.length + 1 + rest.length = chunks.width) :
    PolyIn (fun c ↦ rowSummand layout chunks q theta0 drawn (pre ++ c :: rest) fresh x) 2 := by
  set ch := linkCh layout chunks theta0 drawn
  set ms := layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  set message := honestMessage layout q (x.take (linkRows layout)) (x.drop (linkRows layout))
  set RS : E → LinkRowSide := fun c ↦ rowSideOf layout ch
    (idxAt layout chunks ch (pre ++ c :: rest) (honestM1 layout chunks q (pre ++ c :: rest))
      (linkSplit layout (pre ++ c :: rest)))
    (fresh.drop 1) (eqKernel (x.drop (linkRows layout))) (x.take (linkRows layout)) message
    with hRS
  have hR : RowIn RS := rowIn_rowSideOf layout ch
    (idxIn_idxAt pre rest layout chunks ch (polyIn_honestM1 pre rest layout chunks q hw) hw) _ _ _ _
  obtain ⟨hs, hco, hba, hsh⟩ := hR
  refine ((polyIn_summand hc pre rest ms (message.drop (nValuesOf layout))
    (ch.nu.map fun n ↦ fresh.getD 0 0 * (RS 0).certWeight * n) hco (fun c ↦ (hs c).2.2.2.2.2)
    hsh).add_le ((polyIn_cmul (prodE ((x.drop (linkRows layout)).map (1 + ·))) hba).mono
      (by omega))).congr fun c ↦ ?_
  rw [rowSummand_eq, lastOf_eq, ← (hs c).1]

theorem polyIn_sumTail {f : E → List E → E} {d : ℕ} (hf : ∀ x, PolyIn (fun c ↦ f c x) d) :
    ∀ (k : ℕ) (p : List E), PolyIn (fun c ↦ sumTail (f c) k p) d
  | 0, p => hf p
  | k + 1, p => ((polyIn_sumTail hf k (p ++ [0])).add_le (polyIn_sumTail hf k (p ++ [1]))).congr
      fun _ ↦ rfl

end IdxDeg

open IdxDeg

/-- **`idx_deg`**: the index summand is of degree at most `2` in each index variable. -/
theorem linkIdxAt_perVarDeg {layout : Layout} {μ : ℕ} (q : Column μ) {w : ℕ} {chunks : Chunks}
    (hc : Chunks.new w = some chunks) (theta0 : E) (drawn : List E) :
    PerVarDegAt (linkIdxAt layout chunks q theta0 drawn) chunks.width fun _ ↦ 2 :=
  fun pre rest hl ↦ (polyIn_sumTail (fun x ↦ polyIn_rowSummand hc q theta0 drawn [] x pre rest hl)
    _ []).congr fun _ ↦ rfl

/-- **`B_deg`**: each fresh coefficient's weight is of degree at most `2` in each index
variable. -/
theorem linkB_perVarDeg {layout : Layout} {μ : ℕ} (q : Column μ) {w : ℕ} {chunks : Chunks}
    (hc : Chunks.new w = some chunks) (theta0 : E) (drawn : List E) (i : Fin 5) :
    PerVarDeg (fun r ↦ linkB layout chunks q theta0 drawn r i) chunks.width 2 :=
  fun pre rest hl ↦
    ((polyIn_sumTail (fun x ↦ polyIn_rowSummand hc q theta0 drawn (unitFresh i) x pre rest hl)
      _ []).sub (linkIdxAt_perVarDeg q hc theta0 drawn pre rest hl)).congr fun _ ↦ rfl


/-- `LinkSummandFacts`'s `idx_deg` and `B_deg`, at any stack. -/
theorem linkSummand_degs {layout : Layout} {μ : ℕ} (q : Column μ) {w : ℕ} {chunks : Chunks}
    (hc : Chunks.new w = some chunks) :
    (∀ theta0 drawn, PerVarDegAt (linkIdxAt layout chunks q theta0 drawn) chunks.width
      fun _ ↦ 2) ∧
    ∀ theta0 drawn i, PerVarDeg (fun r ↦ linkB layout chunks q theta0 drawn r i) chunks.width 2 :=
  ⟨linkIdxAt_perVarDeg q hc, linkB_perVarDeg q hc⟩

end

end LeanVM.Protocol.Relation
