/-
  LeanVM.Protocol.Relation.Link.GroupLinksCollapse

  The index side's sum at Boolean points, table by table and row by row: the row and pointer-column
  variables select one pointer column of one row, whose word the functionals read.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupLinks
public import LeanVM.Protocol.Relation.Link.GroupLinksWindow
public import LeanVM.Protocol.Relation.Link.GroupJump
public import LeanVM.Protocol.Relation.Link.GroupOneHot

/-!
# The index side's sum at Boolean points

`lk_sum_xq`: the row summand summed over the Boolean row and pointer-column points is, per table
`t` and row `u < 2^h_t`, the table's base terms plus each pointer column's share read from that
column's word at row `u` (`lkPtrW`), the values read from the stack's own row (`honestValues`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

/-- The functionals' values at `r` of the word `w`. -/
def lkWV (layout : Layout) (chunks : Chunks) (r : List E) (w : K) : List E :=
  (Functionals.new chunks r (lkMaxShift layout)).values chunks ((List.range kBits).map (bitOf w))

/-- Pointer column `k` of table `t`'s share, its functionals read from the word `w` at `r`. -/
def lkPtrW (layout : Layout) (chunks : Chunks) (ch : LinkCh) (a : IdxAt) (chi message r : List E)
    (w : K) (t k : ℕ) : E :=
  lkPtrAt layout ch a chi message ((lkWV layout chunks r w).getD 0 0)
    (prodE (((lkWV layout chunks r w).drop 1).take (chunks.d - 1)))
    ((lkWV layout chunks r w).drop (2 * chunks.d)) t k

theorem lkVals_honest (layout : Layout) {μ : ℕ} (q : Column μ) (chi qP : List E) (t : ℕ) :
    lkVals layout (honestMessage layout q chi qP) t = lkVals layout (honestValues layout q chi) t := by
  have h1 := rowStart_sent_honest layout q chi qP
  have h2 : (rowStart layout (honestValues layout q chi)).sent = honestValues layout q chi := by
    show (honestValues layout q chi).take (nValuesOf layout) = _
    exact List.take_of_length_le (by rw [length_honestValues])
  unfold lkVals
  rw [h1, h2]

theorem prodE_boolL_zero {Q jq : ℕ} (hjq : jq < 2 ^ Q) :
    prodE ((boolL Q jq).map (1 + ·)) = if jq = 0 then 1 else 0 := by
  have h := prodE_drop_boolL (m := Q) (h := 0) (Nat.zero_le _) hjq
  simp only [List.drop_zero, pow_zero, Nat.lt_one_iff] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **The row summand at a Boolean point** `(jx, jq)`. -/
theorem lk_rowSummand_bool (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r : List E) {jx jq : ℕ} (hjx : jx < 2 ^ linkRows layout) (hjq : jq < 2 ^ linkQVars layout) :
    rowSummand layout chunks q theta0 drawn r [] (boolL (linkRows layout) jx ++ boolL (linkQVars layout) jq) =
      ∑ t ∈ range layout.tables.length,
        ((if jq = 0 then 1 else 0) * (if jx < 2 ^ heightOf layout t then 1 else 0) *
          lkBase layout (linkCh layout chunks theta0 drawn)
            (lkIdx layout chunks q (linkCh layout chunks theta0 drawn) r) [] (boolL (linkRows layout) jx)
            (honestValues layout q (boolL (linkRows layout) jx)) t +
        ∑ k ∈ range (ptrsOf layout t).length, (if qBase layout t + k = jq then 1 else 0) *
          (if jx < 2 ^ heightOf layout t then 1 else 0) *
          lkPtrW layout chunks (linkCh layout chunks theta0 drawn)
            (lkIdx layout chunks q (linkCh layout chunks theta0 drawn) r) (boolL (linkRows layout) jx)
            (honestValues layout q (boolL (linkRows layout) jx)) r (wordAt layout q t k jx) t k) := by
  rw [lk_rowSummand]
  simp only [List.take_left' (length_boolL _ _), List.drop_left' (length_boolL _ _)]
  refine sum_congr rfl fun t ht ↦ ?_
  rw [prodE_boolL_zero hjq, cornerAt, prodE_drop_boolL (heightOf_le layout t) hjx]
  have hb : lkBase layout (linkCh layout chunks theta0 drawn)
      (lkIdx layout chunks q (linkCh layout chunks theta0 drawn) r) [] (boolL (linkRows layout) jx)
      (honestMessage layout q (boolL (linkRows layout) jx) (boolL (linkQVars layout) jq)) t =
      lkBase layout (linkCh layout chunks theta0 drawn)
      (lkIdx layout chunks q (linkCh layout chunks theta0 drawn) r) [] (boolL (linkRows layout) jx)
      (honestValues layout q (boolL (linkRows layout) jx)) t := by
    simp only [lkBase, lkVals_honest]
  rw [hb]
  refine congrArg₂ (· + ·) rfl ?_
  refine sum_congr rfl fun k hk ↦ ?_
  rw [eqKernel_boolL hjq]
  by_cases he : qBase layout t + k = jq
  · by_cases hlt : jx < 2 ^ heightOf layout t
    · have hS : (honestMessage layout q (boolL (linkRows layout) jx) (boolL (linkQVars layout) jq)).drop
          (nValuesOf layout) = (List.range kBits).map (bitOf (wordAt layout q t k jx)) := by
        rw [honestSlices_closed]
        refine List.map_congr_left fun b _ ↦ ?_
        simp only [eqKernel_boolL hjq]
        rw [← he, sum_ptr_single layout _ (fun t' k' ↦ rowMle ((boolL (linkRows layout) jx).take
          (heightOf layout t')) fun j ↦ bitOf (pieceRow q (placementAt layout t' k') j) b) (mem_range.mp ht)
          (mem_range.mp hk)]
        rw [take_boolL (heightOf_le layout t), Nat.mod_eq_of_lt hlt, rowMle_boolL hlt]
        rfl
      have hF : lkFVals layout chunks q r (boolL (linkRows layout) jx ++ boolL (linkQVars layout) jq) =
          lkWV layout chunks r (wordAt layout q t k jx) := by
        simp only [lkFVals, List.take_left' (length_boolL _ _), List.drop_left' (length_boolL _ _), hS, lkWV]
      simp only [he, hlt, ↓reduceIte, hF, lkPtrW, lkPtrAt, lkVals_honest]
    · simp only [hlt, ↓reduceIte]; ring
  · simp only [he, ↓reduceIte]; ring

theorem qBase_add_lt_pow (layout : Layout) {t k : ℕ} (ht : t < layout.tables.length)
    (hk : k < (ptrsOf layout t).length) : qBase layout t + k < 2 ^ linkQVars layout := by
  have h1 := qBase_add_lt layout ht hk
  rw [sum_length_eq_qBase] at h1
  exact h1.trans_le (qBase_le_pow layout)

/-- **The row summand over the Boolean row and pointer-column points**, table by table and row by
row. -/
theorem lk_sum_xq (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r : List E) :
    ∑ jx ∈ range (2 ^ linkRows layout), ∑ jq ∈ range (2 ^ linkQVars layout),
      rowSummand layout chunks q theta0 drawn r [] (boolL (linkRows layout) jx ++ boolL (linkQVars layout) jq) =
    ∑ t ∈ range layout.tables.length, ∑ u ∈ range (2 ^ heightOf layout t),
      (lkBase layout (linkCh layout chunks theta0 drawn)
          (lkIdx layout chunks q (linkCh layout chunks theta0 drawn) r) [] (boolL (linkRows layout) u)
          (honestValues layout q (boolL (linkRows layout) u)) t +
        ∑ k ∈ range (ptrsOf layout t).length, lkPtrW layout chunks (linkCh layout chunks theta0 drawn)
          (lkIdx layout chunks q (linkCh layout chunks theta0 drawn) r) (boolL (linkRows layout) u)
          (honestValues layout q (boolL (linkRows layout) u)) r (wordAt layout q t k u) t k) := by
  set ch := linkCh layout chunks theta0 drawn
  set a := lkIdx layout chunks q ch r
  set B : ℕ → ℕ → E := fun t u ↦ lkBase layout ch a [] (boolL (linkRows layout) u)
    (honestValues layout q (boolL (linkRows layout) u)) t
  set P : ℕ → ℕ → ℕ → E := fun t k u ↦ lkPtrW layout chunks ch a (boolL (linkRows layout) u)
    (honestValues layout q (boolL (linkRows layout) u)) r (wordAt layout q t k u) t k
  have hjx : ∀ jx ∈ range (2 ^ linkRows layout), ∑ jq ∈ range (2 ^ linkQVars layout),
      rowSummand layout chunks q theta0 drawn r [] (boolL (linkRows layout) jx ++ boolL (linkQVars layout) jq) =
      ∑ t ∈ range layout.tables.length, (if jx < 2 ^ heightOf layout t then B t jx + ∑ k ∈ range (ptrsOf layout t).length,
        P t k jx else 0) := by
    intro jx hjx
    rw [sum_congr rfl fun jq hjq ↦ lk_rowSummand_bool layout chunks q theta0 drawn r (mem_range.mp hjx)
      (mem_range.mp hjq), sum_comm]
    refine sum_congr rfl fun t ht ↦ ?_
    rw [sum_add_distrib, sum_comm]
    have h0 : (0 : ℕ) < 2 ^ linkQVars layout := Nat.two_pow_pos _
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, h0, ↓reduceIte]
    have hk : ∀ k ∈ range (ptrsOf layout t).length, ∑ jq ∈ range (2 ^ linkQVars layout),
        (if qBase layout t + k = jq then (if jx < 2 ^ heightOf layout t then P t k jx else 0) else 0) =
        if jx < 2 ^ heightOf layout t then P t k jx else 0 := by
      intro k hk
      rw [sum_ite_eq]
      simp [qBase_add_lt_pow layout (mem_range.mp ht) (mem_range.mp hk)]
    rw [sum_congr rfl hk]
    split_ifs <;> first | rfl | simp
  rw [sum_congr rfl hjx, sum_comm]
  refine sum_congr rfl fun t _ ↦ ?_
  exact sum_range_ite_lt (Nat.pow_le_pow_right (by norm_num) (heightOf_le layout t)) _

/-! ## The index variables -/

/-- The index scalars at the Boolean point of `j`. -/
abbrev lkIdxB (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (ch : LinkCh) (j : ℕ) : IdxAt :=
  lkIdx layout chunks q ch (boolL chunks.width j)

/-- Table `t`'s base terms at no index point: `ω·(η_mem·Σ μ·gate·(γ_0·addr + γ_3 + γ_1·value) +
η_bc·rBc)`. -/
def lkBaseC (layout : Layout) (ch : LinkCh) (chi message : List E) (t : ℕ) : E :=
  let table := layout.tables.getD t default
  let values := lkVals layout message t
  omegaOf layout ch chi t * (ch.etaMem *
    ((table.links.memory.zip (ch.mu.getD t [])).map fun x ↦ x.2 * lkGate (fun c ↦ values.getD c 0) x.1 *
      (ch.gammaMem.getD 0 0 * x.1.address.evaluate (fun c ↦ values.getD c 0) + ch.gammaMem.getD 3 0 +
        ch.gammaMem.getD 1 0 * x.1.value.evaluate (fun c ↦ values.getD c 0))).sum +
    ch.etaBc * lkRBc ch table values)

/-- Pointer column `k` of table `t`'s share summed over the index points, for a one-hot word decoding
to `σ`: the state at `σ`, the program at `σ`, the word reads at `σ` and each access at its window's
cell. -/
def lkPtrC (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (ch : LinkCh) (chi message : List E)
    (σ t k : ℕ) : E :=
  let table := layout.tables.getD t default
  let col := fun (c : ℕ) ↦ (lkVals layout message t).getD c 0
  let state := table.links.stateLink
  let omega := omegaOf layout ch chi t
  let act := lessThan (chi.take (heightOf layout t)) (layout.tableRows.getD t 0)
  let sHat := ch.stateGamma (col state.pc) (col state.fp)
  let sNext := ch.stateGamma (state.next.1.evaluate col) (state.next.2.evaluate col)
  let a := lkIdxB layout chunks q ch
  let pointer := (ptrsOf layout t).getD k 0
  match k with
  | 0 => act * ((a σ).eqZetaR * sHat + (a σ).shiftZetaR * sNext)
  | 1 => omega * ((a σ).xBc + col state.fp * (a σ).pFp)
  | _ + 2 =>
    ((table.links.memory.zip (ch.mu.getD t [])).map fun x ↦ (x.1.reads.map (lkRead pointer
        (fun m scale ↦ omega * ch.etaMem * m * ch.gammaMem.getD 1 0 * (a σ).m1 * scale.evaluate col)
        x.2)).sum).sum +
      (((table.links.memory.zip (ch.mu.getD t [])).filter (·.1.pointer = pointer)).map fun x ↦
        omega * lkGate col x.1 * ch.etaMem * x.2 *
          match windowHit (chunks.widths.getD 0 0) σ x.1.shift with
          | some j => (a j).yMem
          | none => 0).sum

theorem lk_eq0R_bool (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (ch : LinkCh) {j : ℕ}
    (hj : j < 2 ^ chunks.width) : (lkIdxB layout chunks q ch j).eq0R = if j = 0 then 1 else 0 := by
  have h := prodE_drop_boolL (m := chunks.width) (h := 0) (Nat.zero_le _) hj
  simp only [pow_zero, Nat.lt_one_iff] at h
  simp only [lkIdxB, lkIdx, idxAt, belowAt, Nat.zero_min]
  exact h

theorem lkBase_eq (layout : Layout) (ch : LinkCh) (a : IdxAt) (chi message : List E) (t : ℕ) :
    lkBase layout ch a [] chi message t = a.eq0R * lkBaseC layout ch chi message t := by
  rw [lkBase, tableBaseOf_nil, lkBaseC]
  ring

/-- The base terms summed over the index points. -/
theorem lk_sum_base (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (ch : LinkCh)
    (chi message : List E) (t : ℕ) :
    ∑ jr ∈ range (2 ^ chunks.width), lkBase layout ch (lkIdxB layout chunks q ch jr) [] chi message t =
      lkBaseC layout ch chi message t := by
  rw [sum_congr rfl fun jr hjr ↦ by rw [lkBase_eq, lk_eq0R_bool layout chunks q ch (mem_range.mp hjr)]]
  simp

theorem sum_list_map_comm {α : Type} (s : Finset ℕ) (L : List α) (f : ℕ → α → E) :
    ∑ j ∈ s, (L.map (f j)).sum = (L.map fun x ↦ ∑ j ∈ s, f j x).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [sum_add_distrib, ih]

theorem lkMaxShift_ge (layout : Layout) {t : ℕ} (ht : t < layout.tables.length) :
    (layout.tables.getD t default).links.maxShift ≤ lkMaxShift layout := by
  have key : ∀ (L : List Table) (m : ℕ), m ≤ L.foldl (fun m t ↦ max m t.links.maxShift) m ∧
      ∀ i < L.length, (L.getD i default).links.maxShift ≤ L.foldl (fun m t ↦ max m t.links.maxShift) m := by
    intro L
    induction L with
    | nil => intro m; simp
    | cons x L ih =>
      intro m
      obtain ⟨h1, h2⟩ := ih (max m x.links.maxShift)
      refine ⟨(le_max_left _ _).trans h1, fun i hi ↦ ?_⟩
      rcases i with _ | i
      · exact (le_max_right _ _).trans h1
      · simpa using h2 i (by simpa using hi)
  exact (key layout.tables 0).2 t ht

theorem shift_le_maxShift (links : Links) {a : Access} (ha : a ∈ links.memory) : a.shift ≤ links.maxShift := by
  have key : ∀ (L : List ℕ) (m : ℕ), m ≤ L.foldl max m ∧ ∀ x ∈ L, x ≤ L.foldl max m := by
    intro L
    induction L with
    | nil => intro m; simp
    | cons x L ih =>
      intro m
      obtain ⟨h1, h2⟩ := ih (max m x)
      refine ⟨(le_max_left _ _).trans h1, fun y hy ↦ ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact (le_max_right _ _).trans h1
      · exact h2 y hy
  exact (key _ 0).2 _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem windowHit_zero (w0 σ : ℕ) : windowHit w0 σ 0 = some σ := by
  simp [windowHit, Nat.mod_lt _ (Nat.two_pow_pos w0)]

section Window

variable {layout : Layout} {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks) {w : K}
  (hone : ∀ i < chunks.d, ChunkOneHot chunks w i)
include hch hone

/-- A shift's window read times the other chunks, at the Boolean point of `jr`. -/
theorem lk_shW_bool {jr : ℕ} (hjr : jr < 2 ^ chunks.width) {s : ℕ} (hs : s ≤ lkMaxShift layout) :
    lkShW ((lkWV layout chunks (boolL chunks.width jr) w).getD 0 0)
        ((lkWV layout chunks (boolL chunks.width jr) w).drop (2 * chunks.d)) (lkMaxShift layout) s *
      prodE (((lkWV layout chunks (boolL chunks.width jr) w).drop 1).take (chunks.d - 1)) =
    if windowHit (chunks.widths.getD 0 0) (ptrIndex chunks w) s = some jr then 1 else 0 := by
  have h := lk_window_bool hch w hone (lkMaxShift layout) hjr s hs
  rcases s with _ | s
  · simpa [lkWV, lkShW] using h
  · have hs' : s < lkMaxShift layout := by omega
    simp only [lkShW, hs', ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_drop] at h ⊢
    simpa [lkWV] using h

theorem lk_d0_bool {jr : ℕ} (hjr : jr < 2 ^ chunks.width) :
    (lkWV layout chunks (boolL chunks.width jr) w).getD 0 0 *
      prodE (((lkWV layout chunks (boolL chunks.width jr) w).drop 1).take (chunks.d - 1)) =
    if ptrIndex chunks w = jr then 1 else 0 := by
  have h := lk_shW_bool (layout := layout) hch hone hjr (Nat.zero_le _)
  simpa [lkShW, windowHit_zero] using h

theorem lk_sum_ind (F : ℕ → E) (s : ℕ) :
    ∑ jr ∈ range (2 ^ chunks.width), F jr *
      (if windowHit (chunks.widths.getD 0 0) (ptrIndex chunks w) s = some jr then 1 else 0) =
    match windowHit (chunks.widths.getD 0 0) (ptrIndex chunks w) s with
    | some j => F j
    | none => 0 := by
  have hσ := ptrIndex_lt hch w hone
  rcases hw : windowHit (chunks.widths.getD 0 0) (ptrIndex chunks w) s with _ | j
  · simp
  · have hw0 : chunks.widths.getD 0 0 ≤ chunks.width := by
      have := (chunks_geometry hch 0 (lkw_chunks_tile hch).1).1
      omega
    have hj : j < 2 ^ chunks.width := windowHit_lt hw0 hσ hw
    simp [hj]

theorem lk_sum_eq (F : ℕ → E) :
    ∑ jr ∈ range (2 ^ chunks.width), F jr * (if ptrIndex chunks w = jr then 1 else 0) = F (ptrIndex chunks w) := by
  have hσ := ptrIndex_lt hch w hone
  simp [hσ]

end Window

/-- A memory pointer column's share: its word reads at `D_0`, its accesses at their window reads. -/
theorem lkPtr_two (ch : LinkCh) (a : IdxAt) (omega act sHat sNext : E) (table : Table) (t : ℕ)
    (col : ℕ → E) (d0 rest : E) (ts : List E) (N pointer k : ℕ) :
    lkPtr ch a omega act sHat sNext table t col d0 rest ts N pointer (k + 2) =
      ((table.links.memory.zip (ch.mu.getD t [])).map fun x ↦ (x.1.reads.map (lkRead pointer
        (fun m scale ↦ omega * ch.etaMem * m * ch.gammaMem.getD 1 0 * a.m1 * scale.evaluate col)
        x.2)).sum).sum * (d0 * rest) +
      (((table.links.memory.zip (ch.mu.getD t [])).filter (·.1.pointer = pointer)).map fun x ↦
        omega * lkGate col x.1 * ch.etaMem * x.2 * a.yMem * (lkShW d0 ts N x.1.shift * rest)).sum := by
  simp only [lkPtr]
  rw [add_mul]
  refine congrArg₂ (· + ·) (by ring) ?_
  rw [← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun x _ ↦ ?_)
  show _ * lkShW d0 ts N x.1.shift * rest = _
  ring

theorem mem_of_mem_filter_zip {L : List Access} {M : List E} {p : ℕ} {x : Access × E}
    (hx : x ∈ (L.zip M).filter (·.1.pointer = p)) : x.1 ∈ L :=
  (List.of_mem_zip (List.mem_filter.mp hx).1).1

/-- **A pointer column's share summed over the index points**, for a word one-hot in every chunk. -/
theorem lk_sum_ptr {layout : Layout} {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    {μ : ℕ} (q : Column μ) {w : K} (hone : ∀ i < chunks.d, ChunkOneHot chunks w i) (ch : LinkCh)
    (chi message : List E) {t : ℕ} (hN : ∀ x ∈ (layout.tables.getD t default).links.memory,
      x.shift ≤ lkMaxShift layout) (k : ℕ) :
    ∑ jr ∈ range (2 ^ chunks.width), lkPtrW layout chunks ch (lkIdxB layout chunks q ch jr) chi message
      (boolL chunks.width jr) w t k = lkPtrC layout chunks q ch chi message (ptrIndex chunks w) t k := by
  rcases k with _ | _ | k
  · have e : ∀ jr ∈ range (2 ^ chunks.width), lkPtrW layout chunks ch (lkIdxB layout chunks q ch jr) chi
        message (boolL chunks.width jr) w t 0 = lkPtrC layout chunks q ch chi message jr t 0 *
          (if ptrIndex chunks w = jr then 1 else 0) := by
      intro jr hjr
      rw [← lk_d0_bool hch hone (mem_range.mp hjr)]
      simp only [lkPtrW, lkPtrAt, lkPtr, lkPtrC]
      ring
    rw [sum_congr rfl e, lk_sum_eq hch hone]
  · have e : ∀ jr ∈ range (2 ^ chunks.width), lkPtrW layout chunks ch (lkIdxB layout chunks q ch jr) chi
        message (boolL chunks.width jr) w t 1 = lkPtrC layout chunks q ch chi message jr t 1 *
          (if ptrIndex chunks w = jr then 1 else 0) := by
      intro jr hjr
      rw [← lk_d0_bool hch hone (mem_range.mp hjr)]
      simp only [lkPtrW, lkPtrAt, lkPtr, lkPtrC]
      ring
    rw [sum_congr rfl e, lk_sum_eq hch hone]
  · set table := layout.tables.getD t default
    set col := fun (c : ℕ) ↦ (lkVals layout message t).getD c 0
    set omega := omegaOf layout ch chi t
    set pointer := (ptrsOf layout t).getD (k + 2) 0
    set L := table.links.memory.zip (ch.mu.getD t [])
    set Rd : ℕ → E := fun j ↦ (L.map fun x ↦ (x.1.reads.map (lkRead pointer
      (fun m scale ↦ omega * ch.etaMem * m * ch.gammaMem.getD 1 0 * (lkIdxB layout chunks q ch j).m1 *
        scale.evaluate col) x.2)).sum).sum
    set G : Access × E → ℕ → E := fun x j ↦ omega * lkGate col x.1 * ch.etaMem * x.2 *
      (lkIdxB layout chunks q ch j).yMem
    have e : ∀ jr ∈ range (2 ^ chunks.width), lkPtrW layout chunks ch (lkIdxB layout chunks q ch jr) chi
        message (boolL chunks.width jr) w t (k + 2) = Rd jr * (if ptrIndex chunks w = jr then 1 else 0) +
          ((L.filter (·.1.pointer = pointer)).map fun x ↦ G x jr *
            (if windowHit (chunks.widths.getD 0 0) (ptrIndex chunks w) x.1.shift = some jr then 1 else 0)).sum := by
      intro jr hjr
      rw [← lk_d0_bool hch hone (mem_range.mp hjr)]
      simp only [lkPtrW, lkPtrAt]
      rw [lkPtr_two]
      refine congrArg₂ (· + ·) rfl (congrArg List.sum (List.map_congr_left fun x hx ↦ ?_))
      rw [← lk_shW_bool hch hone (mem_range.mp hjr) (hN x.1 (mem_of_mem_filter_zip hx))]
    rw [sum_congr rfl e, sum_add_distrib, lk_sum_eq hch hone, sum_list_map_comm]
    simp only [lkPtrC]
    refine congrArg₂ (· + ·) rfl (congrArg List.sum (List.map_congr_left fun x _ ↦ ?_))
    rw [lk_sum_ind hch hone]
    rcases windowHit (chunks.widths.getD 0 0) (ptrIndex chunks w) x.1.shift with _ | j
    · simp
    · rfl

/-! ## The whole sum -/

theorem lessThan_boolL {h u n : ℕ} (hu : u < 2 ^ h) (hn : n ≤ 2 ^ h) :
    lessThan (boolL h u) n = if u < n then 1 else 0 := by
  rw [lessThan, one_add_paddingWeight_eq_mle _ _ (by rw [length_boolL]; exact hn), ← rowMle_eq_mle,
    rowMle_boolL hu]

theorem lkPtr_zero (ch : LinkCh) (a : IdxAt) (sHat sNext : E) (table : Table) (t : ℕ)
    (col : ℕ → E) (d0 rest : E) (ts : List E) (N pointer k : ℕ) :
    lkPtr ch a 0 0 sHat sNext table t col d0 rest ts N pointer k = 0 := by
  rcases k with _ | _ | k <;> simp [lkPtr]
  · rw [List.sum_eq_zero]
    · simp
    · intro x hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      rw [List.sum_eq_zero]
      intro z hz
      obtain ⟨rd, -, rfl⟩ := List.mem_map.mp hz
      cases rd <;> simp [lkRead]

/-- The table's pointer column `k` at row `u` is its column `ptrs[k]`'s word. -/
theorem wordAt_eq {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {t k : ℕ} (ht : t < nTables) (hk : k < (ptrsOf layout t).length) (u : ℕ) :
    wordAt layout q t k u = tableWord layout q t ((ptrsOf layout t).getD k 0) u ∧
      (ptrsOf layout t).getD k 0 ∈ (tableAt layout t).links.pointers := by
  have hT := (announced_facts hA).2.1
  have hTlen : layout.tables.length = nTables := by rw [hT, tables_length]
  have hptrs : ptrsOf layout t = (tableAt layout t).links.pointers := by
    unfold ptrsOf tableAt
    rw [List.getD_eq_getElem _ _ (by simp [hTlen, ht]), List.getElem_map,
      List.getD_eq_getElem _ _ (by simp [hTlen, ht])]
  have hp0 : (ptrsOf layout t).getD k 0 ∈ (tableAt layout t).links.pointers := by
    rw [List.getD_eq_getElem _ _ hk]
    simp only [hptrs]
    exact List.getElem_mem _
  refine ⟨?_, hp0⟩
  obtain ⟨lm, rows, hB⟩ := announced_build hA
  have htab : tableAt layout t = tables.getD t default := by rw [tableAt, hT]
  obtain ⟨hc, hk', -⟩ := pointers_placed t ht _ (htab ▸ hp0)
  obtain ⟨pl, hpl⟩ := Option.isSome_iff_exists.mp (placement_isSome hB hc hk')
  simp only [wordAt, placementAt, pieceRow, tableWord, columnRow, hpl, Option.getD_some]

/-- **The index side's sum in closed form**, for one-hot pointers: per table and executed row, the
base terms and each pointer column's share at the index its word decodes to. -/
theorem lk_linkIdx_closed {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hone : PointersOneHot layout q chunks) (theta0 : E) (drawn : List E)
    (hτ : (linkCh layout chunks theta0 drawn).tau.length = linkRows layout) :
    linkIdx layout chunks q theta0 drawn [] = ∑ t ∈ range nTables, ∑ u ∈ range (tableRowCount layout t),
      (lkBaseC layout (linkCh layout chunks theta0 drawn) (boolL (linkRows layout) u)
          (honestValues layout q (boolL (linkRows layout) u)) t +
        ∑ k ∈ range (ptrsOf layout t).length, lkPtrC layout chunks q (linkCh layout chunks theta0 drawn)
          (boolL (linkRows layout) u) (honestValues layout q (boolL (linkRows layout) u))
          (ptrIndex chunks (wordAt layout q t k u)) t k) := by
  set ch := linkCh layout chunks theta0 drawn
  have hT := (announced_facts hA).2.1
  have hTlen : layout.tables.length = nTables := by rw [hT, tables_length]
  rw [linkIdx_nil_eq]
  rw [sum_congr rfl fun jr _ ↦ lk_sum_xq layout chunks q theta0 drawn (boolL chunks.width jr), sum_comm]
  rw [hTlen]
  refine sum_congr rfl fun t ht ↦ ?_
  have ht' : t < nTables := mem_range.mp ht
  have hrows : layout.tableRows.getD t 0 ≤ 2 ^ heightOf layout t := tableRows_le_height hA ht'
  rw [sum_comm]
  refine (sum_subset (range_subset_range.mpr hrows) (fun u hu hnot ↦ ?_)).symm.trans
    (sum_congr rfl fun u hu ↦ ?_)
  · -- a row past the executed ones adds nothing
    have hu' := mem_range.mp hu
    have hnu : ¬ u < layout.tableRows.getD t 0 := fun h ↦ hnot (mem_range.mpr h)
    have hτh : (ch.tau.take (heightOf layout t)).length = heightOf layout t := by
      rw [List.length_take, hτ]; exact min_eq_left (heightOf_le layout t)
    have hom : omegaOf layout ch (boolL (linkRows layout) u) t = 0 := by
      rw [omegaOf, take_boolL (heightOf_le layout t), Nat.mod_eq_of_lt hu',
        omegaAt_boolL _ _ hτh hu' hrows]
      simp only [hnu, ↓reduceIte, mul_zero]
    have hact : lessThan ((boolL (linkRows layout) u).take (heightOf layout t)) (layout.tableRows.getD t 0) = 0 := by
      rw [take_boolL (heightOf_le layout t), Nat.mod_eq_of_lt hu', lessThan_boolL hu' hrows]
      simp only [hnu, ↓reduceIte]
    rw [sum_add_distrib, sum_comm]
    simp only [lkBase_eq, ← sum_mul]
    rw [lkBaseC, hom]
    simp only [zero_mul, mul_zero, zero_add]
    refine sum_eq_zero fun k _ ↦ sum_eq_zero fun jr _ ↦ ?_
    simp only [lkPtrW, lkPtrAt]
    rw [hom, hact, lkPtr_zero]
  · -- an executed row
    have hu' := mem_range.mp hu
    rw [sum_add_distrib, lk_sum_base]
    refine congrArg₂ (· + ·) rfl ?_
    rw [sum_comm]
    refine sum_congr rfl fun k hk ↦ ?_
    obtain ⟨hw, hp⟩ := wordAt_eq hA q ht' (mem_range.mp hk) u
    have hw1 : ∀ i < chunks.d, ChunkOneHot chunks (wordAt layout q t k u) i := by
      rw [hw]; exact hone t ht' u hu' _ hp
    refine lk_sum_ptr hch q hw1 ch _ _ (fun x hx ↦ ?_) k
    exact (shift_le_maxShift _ hx).trans (lkMaxShift_ge layout (hTlen ▸ ht'))

end

end LeanVM.Protocol.Relation

/-- info: 'LeanVM.Protocol.Relation.lk_linkIdx_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.lk_linkIdx_closed
