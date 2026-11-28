/-
  LeanVM.Protocol.Relation.Link.GroupLinksMemory

  The memory case of the link's failing polynomial: a failed memory access gives a draw at which
  the rest (`lkRest`) is nonzero.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupLinksRest
public import LeanVM.Protocol.Relation.Link.GroupLinksWeights
public import LeanVM.Protocol.Relation.Link.GroupLinksSplit
public import LeanVM.Protocol.Relation.Link.Steps

/-!
# The memory case

`lkRest_ne_of_memory`: under the program lookup, a failed memory lookup (`¬ MemoryHolds`) gives a
draw `lkp_set x` at which `lkRest` is nonzero. The draw (`lkmm_x`) puts `θ` on the failing table,
`τ` on the failing row's bits, `μ` on the failing access, `η_mem = 1`, `η_bc = 0`, and one
coordinate of `γ_mem`. There `lkRest` is that access's terms alone (`lkmm_rest_eq`): its base term
`gate·(γ_0·addr + γ_3 + γ_1·value)`, its reads of the instruction through the program pointer's
share, its word reads at their pointers' cells (`m1`) and its window read `gate·y_mem(j)`. The
coordinate is the presence `γ_3` if some access of the row with a nonzero gate misses its window
or the memory, else the address `γ_0` if the address differs, else the word `γ_1`; in the last
case every word read's pointer has an ungated access at shift `0` (`lkt_word_read`), so its cell is
in the memory and `m1` reads its word.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

/-! ## The draw -/

/-- The draw that isolates access `a0` of row `u0` of table `t0`, `γ_mem = (g0, g1, g2)`. -/
def lkmm_x (t0 u0 a0 : ℕ) (g0 g1 g2 : E) : lkp_Vals where
  theta t := if t = t0 then 1 else 0
  gammaState _ := 0
  gammaMem i := if i = 0 then g0 else if i = 1 then g1 else g2
  mu t k := if t = t0 ∧ k = a0 then 1 else 0
  alpha _ := 0
  etaMem := 1
  etaBc := 0
  eps _ := 0
  tau i := if u0.testBit i then 1 else 0
  zeta _ := 0
  nu _ := 0

/-! ## Sums over lists -/

theorem lkmm_zip_sum (L : List Access) (g : ℕ → E) (f : Access × E → E) :
    ((L.zip (List.ofFn (n := L.length) fun k ↦ g k)).map f).sum =
      ∑ k ∈ range L.length, f (L.getD k default, g k) := by
  induction L generalizing g with
  | nil => simp
  | cons b L ih =>
    rw [List.length_cons, List.ofFn_succ, List.zip_cons_cons, List.map_cons, List.sum_cons,
      sum_range_succ']
    have h := ih (fun k ↦ g (k + 1))
    simp only [Fin.val_succ, Fin.val_zero] at h ⊢
    rw [h, add_comm]
    simp

/-- A list zipped with a unit vector, summed: the unit's entry. -/
theorem lkmm_zip_unit (L : List Access) {a0 : ℕ} (ha0 : a0 < L.length) (f : Access × E → E)
    (hf : ∀ a, f (a, 0) = 0) :
    ((L.zip (List.ofFn (n := L.length) fun k ↦ if (k : ℕ) = a0 then (1 : E) else 0)).map f).sum =
      f (L.getD a0 default, 1) := by
  rw [lkmm_zip_sum L (fun k ↦ if k = a0 then 1 else 0) f, sum_eq_single a0]
  · simp
  · intro k _ hk
    simp [hk, hf]
  · intro h
    exact absurd (mem_range.mpr ha0) h

theorem lkmm_sum_filter {β : Type} (l : List β) (P : β → Prop) [DecidablePred P] (f : β → E) :
    ((l.filter fun x ↦ decide (P x)).map f).sum = (l.map fun x ↦ if P x then f x else 0).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    by_cases hx : P x
    · simp [hx, ih]
    · simp [hx, ih]

/-- Over the memory pointer columns, the one named `p`. -/
theorem lkmm_sum_ptrs {ptrs : List ℕ} (hnd : ptrs.Nodup) {p : ℕ} (hp : p ∈ ptrs.drop 2) (F : ℕ → E) :
    ∑ k ∈ Ico 2 ptrs.length, (if p = ptrs.getD k 0 then F (ptrs.getD k 0) else 0) = F p := by
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
  rw [List.length_drop] at hi
  rw [List.getElem_drop] at hpi
  have hk : 2 + i < ptrs.length := by omega
  rw [sum_eq_single (2 + i)]
  · rw [List.getD_eq_getElem _ _ hk, hpi]
    simp
  · intro k hk' hne
    rw [mem_Ico] at hk'
    rw [List.getD_eq_getElem _ _ hk'.2, ← hpi]
    refine ite_eq_right_iff.mpr fun h ↦ absurd ((List.Nodup.getElem_inj_iff hnd).mp h.symm) hne
  · intro h
    exact absurd (mem_Ico.mpr ⟨by omega, hk⟩) h

/-- Over the slots `4 ..< 2^BYTECODE_SLOT_BITS`, the one named `s'`. -/
theorem lkmm_sum_slot {s' : ℕ} (h4 : 4 ≤ s') (hs : s' < 2 ^ bytecodeSlotBits) (c : E) (F : ℕ → E) :
    ∑ s ∈ range (2 ^ bytecodeSlotBits - 4), (if s' = s + 4 then c else 0) * F (s + 4) = c * F s' := by
  rw [sum_eq_single (s' - 4)]
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Nat.sub_add_cancel h4]
  · intro s _ hne
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), zero_mul]
  · intro h
    exact absurd (mem_range.mpr (by omega)) h

/-! ## The row weight -/

theorem lkmm_omega {layout : Layout} (ch : LinkCh) {t0 u0 : ℕ}
    (hθ : ∀ t < nTables, ch.theta.getD t 0 = if t = t0 then 1 else 0)
    (hτ : ch.tau = boolL (linkRows layout) u0)
    (hrows : ∀ t < nTables, tableRowCount layout t ≤ 2 ^ heightOf layout t) (hu0 : u0 < tableRowCount layout t0)
    {t u : ℕ} (ht : t < nTables) (hu : u < tableRowCount layout t) :
    omegaOf layout ch (boolL (linkRows layout) u) t = if t = t0 ∧ u = u0 then 1 else 0 := by
  have hh := heightOf_le layout t
  have hr := hrows t ht
  have hu' : u < 2 ^ heightOf layout t := lt_of_lt_of_le hu hr
  rw [omegaOf, hτ, take_boolL hh, take_boolL hh, Nat.mod_eq_of_lt hu',
    omegaAt_boolL _ _ (length_boolL _ _) hu' (show layout.tableRows.getD t 0 ≤ _ from hr), hθ t ht]
  simp only [show u < layout.tableRows.getD t 0 from hu, ite_true]
  rw [eqAt_boolL hu' (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases htt : t = t0
  · subst htt
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hu0 hr)]
    by_cases huu : u = u0 <;> simp [huu]
  · simp [htt]

/-! ## A row outside the draw -/

theorem lkmm_base_zero (layout : Layout) (ch : LinkCh) (chi message : List E) (t : ℕ)
    (h : omegaOf layout ch chi t = 0) : lkBaseC layout ch chi message t = 0 := by
  simp only [lkBaseC, h, zero_mul]

theorem lkmm_lkRead_zero (p : ℕ) (m : E) : lkRead p (fun _ _ ↦ 0) m = fun _ ↦ 0 := by
  funext rd
  cases rd <;> simp [lkRead]

theorem lkmm_ptr_zero (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (ch : LinkCh)
    (chi message : List E) (σ t : ℕ) {k : ℕ} (hk : 1 ≤ k) (h : omegaOf layout ch chi t = 0) :
    lkPtrC layout chunks q ch chi message σ t k = 0 := by
  rcases k with _ | _ | k
  · omega
  · simp only [lkPtrC, h, zero_mul]
  · simp only [lkPtrC, h, zero_mul]
    simp only [lkmm_lkRead_zero]
    simp

/-- **Only the drawn row survives.** -/
theorem lkmm_rest_single {layout : Layout} {μ : ℕ} (q : Column μ) {chunks : Chunks}
    (v : Fin (linkDrawn layout chunks + 1) → E) {t0 u0 : ℕ}
    (ht0 : t0 < nTables) (hu0 : u0 < tableRowCount layout t0)
    (hω : ∀ t < nTables, ∀ u < tableRowCount layout t,
      omegaOf layout (chV layout chunks v) (boolL (linkRows layout) u) t = if t = t0 ∧ u = u0 then 1 else 0) :
    lkRest layout chunks q v =
      lkBaseC layout (chV layout chunks v) (boolL (linkRows layout) u0)
          (honestValues layout q (boolL (linkRows layout) u0)) t0 +
        ∑ k ∈ Ico 1 (ptrsOf layout t0).length, lkPtrC layout chunks q (chV layout chunks v)
          (boolL (linkRows layout) u0) (honestValues layout q (boolL (linkRows layout) u0))
          (ptrIndex chunks (wordAt layout q t0 k u0)) t0 k := by
  have hz : ∀ t < nTables, ∀ u < tableRowCount layout t, ¬ (t = t0 ∧ u = u0) →
      lkBaseC layout (chV layout chunks v) (boolL (linkRows layout) u)
          (honestValues layout q (boolL (linkRows layout) u)) t +
        ∑ k ∈ Ico 1 (ptrsOf layout t).length, lkPtrC layout chunks q (chV layout chunks v)
          (boolL (linkRows layout) u) (honestValues layout q (boolL (linkRows layout) u))
          (ptrIndex chunks (wordAt layout q t k u)) t k = 0 := by
    intro t ht u hu hne
    have h0 := hω t ht u hu
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne)] at h0
    rw [lkmm_base_zero _ _ _ _ _ h0, zero_add]
    exact sum_eq_zero fun k hk ↦ lkmm_ptr_zero _ _ _ _ _ _ _ _ (mem_Ico.mp hk).1 h0
  rw [lkRest, sum_eq_single t0]
  · rw [sum_eq_single u0]
    · intro u hu hne
      exact hz t0 ht0 u (mem_range.mp hu) fun h ↦ hne h.2
    · intro h
      exact absurd (mem_range.mpr hu0) h
  · intro t ht hne
    exact sum_eq_zero fun u hu ↦ hz t (mem_range.mp ht) u (mem_range.mp hu) fun h ↦ hne h.1
  · intro h
    exact absurd (mem_range.mpr ht0) h

/-! ## The draw's challenges -/

section Draw

variable {layout : Layout} {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
  (t0 u0 a0 : ℕ) (g0 g1 g2 : E)
include hch

theorem lkmm_ch_eta : (chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 g0 g1 g2))).etaMem = 1 ∧
    (chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 g0 g1 g2))).etaBc = 0 := by
  rw [lkp_chV_etaMem hch, lkp_chV_etaBc hch]
  exact ⟨rfl, rfl⟩

theorem lkmm_ch_gamma :
    (chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 g0 g1 g2))).gammaMem.getD 0 0 = g0 ∧
    (chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 g0 g1 g2))).gammaMem.getD 1 0 = g1 ∧
    (chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 g0 g1 g2))).gammaMem.getD 3 0 = g2 := by
  rw [lkp_chV_gammaMem hch]
  simp [lkmm_x]

theorem lkmm_ch_mu {t : ℕ} (ht : t < layout.tables.length) :
    (chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 g0 g1 g2))).mu.getD t [] =
      List.ofFn (n := (layout.tables.getD t default).links.memory.length)
        fun k ↦ if t = t0 ∧ (k : ℕ) = a0 then 1 else 0 := by
  rw [lkp_chV_mu hch _ ht]
  rfl

theorem lkmm_ch_theta {t : ℕ} (ht : t < nTables) :
    (chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 g0 g1 g2))).theta.getD t 0 =
      if t = t0 then 1 else 0 := by
  rw [lkp_chV_theta hch, List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_ofFn]
  rfl

theorem lkmm_ch_tau :
    (chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 g0 g1 g2))).tau = boolL (linkRows layout) u0 := by
  rw [lkp_chV_tau hch]
  rfl

end Draw

/-! ## Boolean index points -/

theorem lkmm_take {W h j : ℕ} (hjh : j < 2 ^ h) :
    (boolL W j).take h = boolL (min h W) j := by
  by_cases hh : h ≤ W
  · rw [take_boolL hh, Nat.mod_eq_of_lt hjh, min_eq_left hh]
  · rw [List.take_of_length_le (by rw [length_boolL]; omega), min_eq_right (by omega)]

theorem lkmm_below (chunks : Chunks) {j : ℕ} (hj : j < 2 ^ chunks.width) (h : ℕ) :
    belowAt chunks (boolL chunks.width j) h = if j < 2 ^ h then 1 else 0 := by
  rw [belowAt, prodE_drop_boolL (min_le_right _ _) hj]
  by_cases hh : h ≤ chunks.width
  · rw [min_eq_left hh]
  · rw [min_eq_right (by omega)]
    have : j < 2 ^ h := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [hj, this]

/-- **The memory term at a cell in the memory** is the cell's word. -/
theorem lkmm_m1 (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) {j : ℕ}
    (hj : j < 2 ^ chunks.width) (hjm : j < 2 ^ layout.logMemory) :
    honestM1 layout chunks q (boolL chunks.width j) = memWord layout q j := by
  have hm0 : keccakOutputLane memory0 = none := by decide
  have hm1 : keccakOutputLane memory1 = none := by decide
  have hjm' : j < 2 ^ min layout.logMemory chunks.width := by
    rcases min_choice layout.logMemory chunks.width with h | h <;> rw [h] <;> assumption
  rw [honestM1, lkmm_below chunks hj, ite_eq_left_of_eq_true _ _ (eq_true hjm),
    lkmm_take (W := chunks.width) hjm, rowMle_boolL hjm', rowMle_boolL hjm',
    memWord, ← word_of_limbs]
  simp [columnValue, hm0, hm1]

/-! ## The program's split at an instruction -/

/-- `lk_splitAt_bool` at a point of any length `m`, for a program of `N` instructions. -/
theorem lkmm_splitAt_bool {bytecode : List K} {N m k : ℕ} (hn : bytecode.length >>> bytecodeSlotBits = N)
    (hk : k < 2 ^ m) (pc : List (ℕ × ℕ)) (F s : ℕ) :
    let sp := splitAt bytecode (boolL m k) pc
    let op := opcodeOf (bytecode.getD (3 * N + k) 0)
    sp.count.getD F 0 = (if F ≤ opKeccak ∧ op = F then 1 else 0) ∧
    (sp.slots.getD F []).getD s 0 =
      (if F ≤ opKeccak ∧ op = F ∧ 4 ≤ s ∧ s < 2 ^ bytecodeSlotBits then
        ofK (bytecode.getD (s * N + k) 0) else 0) ∧
    (sp.pc.getD F []).getD s 0 =
      (if F ≤ opKeccak ∧ op = F ∧ 4 ≤ s ∧ s < 2 ^ bytecodeSlotBits ∧ pc.contains (F, s) then
        gpow k * ofK (bytecode.getD (s * N + k) 0) else 0) := by
  dsimp only
  by_cases hF : F ≤ opKeccak
  · have hF' : F < opKeccak + 1 := Nat.lt_succ_of_le hF
    refine ⟨?_, ?_, ?_⟩
    · unfold splitAt
      dsimp only
      rw [IdxPoly.getD_map_range, ite_eq_left hF', lks_sumE_rows hk]
      · dsimp only
        rw [hn]
        by_cases ho : opcodeOf (bytecode.getD (3 * N + k) 0) = F
        · rw [ite_eq_left ho, ite_eq_left ⟨hF, ho⟩]
        · rw [ite_eq_right ho, ite_eq_right (fun h ↦ ho h.2)]
      · intro gk j
        simp
    · unfold splitAt
      dsimp only
      rw [IdxPoly.getD_map_range, ite_eq_left hF', IdxPoly.getD_map_range]
      by_cases hs : s < 2 ^ bytecodeSlotBits
      · rw [ite_eq_left hs]
        by_cases h4 : 4 ≤ s
        · rw [ite_eq_left h4, lks_sumE_rows hk]
          · dsimp only
            rw [hn]
            by_cases ho : opcodeOf (bytecode.getD (3 * N + k) 0) = F
            · rw [ite_eq_left ho, ite_eq_left ⟨hF, ho, h4, hs⟩, one_mul]
            · rw [ite_eq_right ho, ite_eq_right (fun h ↦ ho h.2.1)]
          · intro gk j
            simp
        · rw [ite_eq_right h4, ite_eq_right (fun h ↦ h4 h.2.2.1)]
      · rw [ite_eq_right hs, ite_eq_right (fun h ↦ hs h.2.2.2)]
    · unfold splitAt
      dsimp only
      rw [IdxPoly.getD_map_range, ite_eq_left hF', IdxPoly.getD_map_range]
      by_cases hs : s < 2 ^ bytecodeSlotBits
      · rw [ite_eq_left hs]
        by_cases h4 : 4 ≤ s ∧ pc.contains (F, s) = true
        · rw [ite_eq_left h4, lks_sumE_rows hk]
          · dsimp only
            rw [hn]
            by_cases ho : opcodeOf (bytecode.getD (3 * N + k) 0) = F
            · rw [ite_eq_left ho, ite_eq_left ⟨hF, ho, h4.1, hs, h4.2⟩, one_mul]
            · rw [ite_eq_right ho, ite_eq_right (fun h ↦ ho h.2.1)]
          · intro gk j
            simp
        · rw [ite_eq_right h4, ite_eq_right (fun h ↦ h4 ⟨h.2.2.1, h.2.2.2.2⟩)]
      · rw [ite_eq_right hs, ite_eq_right (fun h ↦ hs h.2.2.2.1)]
  · have hF' : ¬ F < opKeccak + 1 := by omega
    refine ⟨?_, ?_, ?_⟩ <;> unfold splitAt <;> dsimp only <;>
      rw [IdxPoly.getD_map_range, ite_eq_right hF'] <;> simp [hF]

/-! ## The drawn row's base terms -/

/-- The drawn row's base terms: access `a0`'s `gate·(γ_0·addr + γ_3 + γ_1·value)`. -/
theorem lkmm_base (layout : Layout) (ch : LinkCh) (chi message : List E) {t0 a0 : ℕ}
    (hω : omegaOf layout ch chi t0 = 1) (hη : ch.etaMem = 1) (hηb : ch.etaBc = 0)
    (hmu : ch.mu.getD t0 [] = List.ofFn (n := (layout.tables.getD t0 default).links.memory.length)
      fun k ↦ if (k : ℕ) = a0 then 1 else 0)
    (ha0 : a0 < (layout.tables.getD t0 default).links.memory.length) :
    lkBaseC layout ch chi message t0 =
      lkGate (fun c ↦ (lkVals layout message t0).getD c 0)
          ((layout.tables.getD t0 default).links.memory.getD a0 default) *
        (ch.gammaMem.getD 0 0 * ((layout.tables.getD t0 default).links.memory.getD a0 default).address.evaluate
            (fun c ↦ (lkVals layout message t0).getD c 0) + ch.gammaMem.getD 3 0 +
          ch.gammaMem.getD 1 0 * ((layout.tables.getD t0 default).links.memory.getD a0 default).value.evaluate
            (fun c ↦ (lkVals layout message t0).getD c 0)) := by
  simp only [lkBaseC, hω, hη, hηb, hmu, zero_mul, add_zero, one_mul]
  rw [lkmm_zip_unit _ ha0 _ (fun a ↦ by simp)]
  simp only [one_mul]

/-! ## The drawn row's program pointer -/

/-- A read of the instruction, slot or `pc` (`readValue` at instruction `k`). -/
def lkmm_rs (layout : Layout) (k : ℕ) : Read → E
  | .slot s sc => sc * bcWord layout s k
  | .pc s sc => sc * (gpow k * bcWord layout s k)
  | _ => 0

/-- A read of the instruction times `fp`, without the `fp`. -/
def lkmm_rf (layout : Layout) (k : ℕ) : Read → E
  | .frame s sc => sc * bcWord layout s k
  | _ => 0

/-- A framed address's `g^e·BC_slot`, without the `fp`. -/
def lkmm_fa (layout : Layout) (k : ℕ) (a : Access) : E :=
  match a.frame with
  | some (s, e) => gpow e * bcWord layout s k
  | none => 0

theorem lkmm_lsum2 {α : Type} (l : List α) (f g : α → E) (c d : E) :
    (l.map f).sum * c + (l.map g).sum * d = (l.map fun x ↦ f x * c + g x * d).sum := by
  rw [List.sum_map_add, List.sum_map_mul_right, List.sum_map_mul_right]

/-- **The program side's sums at the drawn row's instruction**: access `a0`'s reads of the
instruction and its framed address. -/
theorem lkmm_ps {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    (ch : LinkCh) {t0 a0 σ W : ℕ} (ht0 : t0 < nTables) (hσW : σ < 2 ^ W)
    (hσ : σ < 2 ^ layout.logBytecode)
    (hop : opcodeOf (layout.bytecode.getD (3 * 2 ^ layout.logBytecode + σ) 0) = t0)
    (hη : ch.etaMem = 1) (hηb : ch.etaBc = 0)
    (hmu : ch.mu.getD t0 [] = List.ofFn (n := (layout.tables.getD t0 default).links.memory.length)
      fun k ↦ if (k : ℕ) = a0 then 1 else 0)
    (ha0 : a0 < (layout.tables.getD t0 default).links.memory.length) :
    (programSums layout ch (linkSplit layout (boolL W σ))).1 =
        ch.gammaMem.getD 1 0 *
          (((layout.tables.getD t0 default).links.memory.getD a0 default).reads.map (lkmm_rs layout σ)).sum ∧
      (programSums layout ch (linkSplit layout (boolL W σ))).2 =
        ch.gammaMem.getD 0 0 * lkmm_fa layout σ ((layout.tables.getD t0 default).links.memory.getD a0 default) +
        ch.gammaMem.getD 1 0 *
          (((layout.tables.getD t0 default).links.memory.getD a0 default).reads.map (lkmm_rf layout σ)).sum := by
  obtain ⟨hbc, hT, hn, -⟩ := announced_facts hA
  have hTlen : layout.tables.length = nTables := by rw [hT, tables_length]
  set L := (layout.tables.getD t0 default).links.memory with hL
  set A := L.getD a0 default with hAdef
  have hAL : A ∈ L := by
    rw [hAdef, List.getD_eq_getElem _ _ ha0]
    exact List.getElem_mem _
  have hAmem : A ∈ (tables.getD t0 default).links.memory := by
    rw [← hT]
    exact hAL
  have hslots := (lkt_read_slots t0 ht0 A hAmem)
  have hσm : σ < 2 ^ min layout.logBytecode W := by
    rcases min_choice layout.logBytecode W with h | h <;> rw [h] <;> assumption
  have hsplit : linkSplit layout (boolL W σ) =
      splitAt layout.bytecode (boolL (min layout.logBytecode W) σ) (pcSlots layout.tables) := by
    rw [linkSplit, lkmm_take hσ]
  have hn' : layout.bytecode.length >>> bytecodeSlotBits = 2 ^ layout.logBytecode := by rw [hbc]; exact hn
  have hS := fun F s ↦ lkmm_splitAt_bool hn' hσm (pcSlots layout.tables) F s
  simp only [hop] at hS
  have hK : t0 ≤ opKeccak := by
    have : nTables = opKeccak + 1 := by decide
    omega
  -- the weights of table `t0`
  have hw : ∀ i < 2 ^ bytecodeSlotBits,
      let w := slotWeights layout.tables (eqKernel ch.alpha) (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0)
        ch.mu ch.etaMem ch.etaBc
      (w.omega.getD t0 []).getD i 0 = ch.gammaMem.getD 1 0 * (A.reads.map (lkSlotRead i)).sum ∧
      (w.pc.getD t0 []).getD i 0 = ch.gammaMem.getD 1 0 * (A.reads.map (lkPcRead i)).sum ∧
      (w.frame.getD t0 []).getD i 0 = ch.gammaMem.getD 0 0 * lkFrameAddr i A +
        ch.gammaMem.getD 1 0 * (A.reads.map (lkFrameRead i)).sum := by
    intro i hi w
    obtain ⟨e1, e2, e3⟩ := slotWeights_getD layout.tables (eqKernel ch.alpha)
      (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) ch.mu ch.etaMem ch.etaBc (t := t0) (by omega)
    obtain ⟨f1, f2, f3⟩ := tsw_closed (layout.tables.getD t0 default) (eqKernel ch.alpha)
      (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) (ch.mu.getD t0 []) ch.etaMem ch.etaBc hi
    refine ⟨?_, ?_, ?_⟩
    · rw [e1, f1, hmu, lkmm_zip_unit _ ha0 _ (fun a ↦ by simp)]
      simp only [hηb, hη, zero_mul, ite_self, one_mul, List.map_const', List.sum_replicate, smul_zero,
        zero_add]
      rw [List.sum_map_mul_left]
    · rw [e2, f2, hmu, lkmm_zip_unit _ ha0 _ (fun a ↦ by simp)]
      simp only [hη, one_mul]
      rw [List.sum_map_mul_left]
    · rw [e3, f3, hmu, lkmm_zip_unit _ ha0 _ (fun a ↦ by simp)]
      simp only [hη, one_mul]
      rw [List.sum_map_mul_left]
  rw [hsplit, programSums_closed]
  dsimp only
  have hBC : ∀ s, ofK (layout.bytecode.getD (s * 2 ^ layout.logBytecode + σ) 0) = bcWord layout s σ :=
    fun s ↦ rfl
  refine ⟨?_, ?_⟩
  · rw [sum_eq_single t0]
    · obtain ⟨h3, -, -⟩ := hw 3 (by decide)
      rw [h3, (hS t0 0).1, ite_eq_left_of_eq_true _ _ (eq_true ⟨hK, rfl⟩)]
      have hz3 : (A.reads.map (lkSlotRead 3)).sum = 0 := by
        refine List.sum_eq_zero fun z hz ↦ ?_
        obtain ⟨rd, hrd, rfl⟩ := List.mem_map.mp hz
        cases rd with
        | slot s sc =>
          have := (hslots.2 _ hrd s sc (Or.inl rfl)).1
          simp only [lkSlotRead]
          exact ite_eq_right_of_eq_false _ _ (eq_false (by omega))
        | _ => rfl
      rw [hz3, mul_zero, zero_mul, zero_mul, zero_add]
      have hsum : ∀ s ∈ range (2 ^ bytecodeSlotBits - 4),
          (((slotWeights layout.tables (eqKernel ch.alpha) (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0)
            ch.mu ch.etaMem ch.etaBc).omega.getD t0 []).getD (s + 4) 0 *
            ((splitAt layout.bytecode (boolL (min layout.logBytecode W) σ) (pcSlots layout.tables)).slots.getD
              t0 []).getD (s + 4) 0 +
          ((slotWeights layout.tables (eqKernel ch.alpha) (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0)
            ch.mu ch.etaMem ch.etaBc).pc.getD t0 []).getD (s + 4) 0 *
            ((splitAt layout.bytecode (boolL (min layout.logBytecode W) σ) (pcSlots layout.tables)).pc.getD
              t0 []).getD (s + 4) 0) =
          ch.gammaMem.getD 1 0 * (A.reads.map fun rd ↦ lkSlotRead (s + 4) rd * bcWord layout (s + 4) σ +
            lkPcRead (s + 4) rd * (if (pcSlots layout.tables).contains (t0, s + 4) = true then
              gpow σ * bcWord layout (s + 4) σ else 0)).sum := by
        intro s hs
        have hs' : s + 4 < 2 ^ bytecodeSlotBits := by have := mem_range.mp hs; omega
        obtain ⟨h1, h2, -⟩ := hw (s + 4) hs'
        rw [h1, h2, (hS t0 (s + 4)).2.1, (hS t0 (s + 4)).2.2, mul_assoc, mul_assoc, ← mul_add, lkmm_lsum2]
        simp only [hK, true_and, show 4 ≤ s + 4 by omega, hs', hBC, ite_true]
      rw [sum_congr rfl hsum, ← mul_sum, sum_list_map_comm]
      congr 1
      refine congrArg List.sum (List.map_congr_left fun rd hrd ↦ ?_)
      cases rd with
      | word p sc => simp only [lkSlotRead, lkPcRead, lkmm_rs, zero_mul, add_zero, sum_const_zero]
      | slot s' sc =>
        obtain ⟨h4, hs⟩ := hslots.2 _ hrd s' sc (Or.inl rfl)
        simp only [lkSlotRead, lkPcRead, zero_mul, add_zero, lkmm_rs]
        exact lkmm_sum_slot h4 hs sc (fun i ↦ bcWord layout i σ)
      | frame s' sc => simp only [lkSlotRead, lkPcRead, lkmm_rs, zero_mul, add_zero, sum_const_zero]
      | pc s' sc =>
        obtain ⟨h4, hs⟩ := hslots.2 _ hrd s' sc (Or.inr (Or.inr rfl))
        have hc : (pcSlots layout.tables).contains (t0, s') = true := by
          rw [hT]; exact lkt_pcSlots t0 ht0 A hAmem s' sc hrd
        simp only [lkSlotRead, lkPcRead, zero_mul, zero_add, lkmm_rs]
        rw [lkmm_sum_slot h4 hs sc (fun i ↦ if (pcSlots layout.tables).contains (t0, i) = true then
          gpow σ * bcWord layout i σ else 0)]
        simp only [hc, ite_true]
    · intro t ht hne
      rw [(hS t 0).1, ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hne h.2.symm), mul_zero, zero_add]
      refine sum_eq_zero fun s _ ↦ ?_
      rw [(hS t (s + 4)).2.1, (hS t (s + 4)).2.2, ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hne h.2.1.symm),
        ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hne h.2.1.symm)]
      simp only [mul_zero, add_zero]
    · intro h
      exact absurd (mem_range.mpr ht0) h
  · rw [sum_eq_single t0]
    · have hsum : ∀ s ∈ range (2 ^ bytecodeSlotBits - 4),
          ((slotWeights layout.tables (eqKernel ch.alpha) (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0)
            ch.mu ch.etaMem ch.etaBc).frame.getD t0 []).getD (s + 4) 0 *
            ((splitAt layout.bytecode (boolL (min layout.logBytecode W) σ) (pcSlots layout.tables)).slots.getD
              t0 []).getD (s + 4) 0 =
          ch.gammaMem.getD 0 0 * (lkFrameAddr (s + 4) A * bcWord layout (s + 4) σ) +
            ch.gammaMem.getD 1 0 * (A.reads.map fun rd ↦ lkFrameRead (s + 4) rd * bcWord layout (s + 4) σ).sum := by
        intro s hs
        have hs' : s + 4 < 2 ^ bytecodeSlotBits := by have := mem_range.mp hs; omega
        obtain ⟨-, -, h3⟩ := hw (s + 4) hs'
        rw [h3, (hS t0 (s + 4)).2.1]
        simp only [hK, true_and, show 4 ≤ s + 4 by omega, hs', ite_true, hBC]
        rw [List.sum_map_mul_right]
        ring
      rw [sum_congr rfl hsum, sum_add_distrib, ← mul_sum, ← mul_sum, sum_list_map_comm]
      refine congrArg₂ (· + ·) (congrArg (ch.gammaMem.getD 0 0 * ·) ?_) (congrArg (ch.gammaMem.getD 1 0 * ·) ?_)
      · rcases hf : A.frame with _ | ⟨s', e⟩
        · simp [lkFrameAddr, lkmm_fa, hf]
        · obtain ⟨h4, hs⟩ := hslots.1 s' e hf
          simp only [lkFrameAddr, lkmm_fa, hf]
          exact lkmm_sum_slot h4 hs _ (fun i ↦ bcWord layout i σ)
      · refine congrArg List.sum (List.map_congr_left fun rd hrd ↦ ?_)
        cases rd with
        | frame s' sc =>
          obtain ⟨h4, hs⟩ := hslots.2 _ hrd s' sc (Or.inr (Or.inl rfl))
          simp only [lkFrameRead, lkmm_rf]
          exact lkmm_sum_slot h4 hs sc (fun i ↦ bcWord layout i σ)
        | _ => simp only [lkFrameRead, lkmm_rf, zero_mul, sum_const_zero]
    · intro t ht hne
      refine sum_eq_zero fun s _ ↦ ?_
      rw [(hS t (s + 4)).2.1, ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hne h.2.1.symm), mul_zero]
    · intro h
      exact absurd (mem_range.mpr ht0) h

/-- **The drawn row's program pointer share**: access `a0`'s reads of the instruction and its framed
address, at the row's instruction `rowBc`. -/
theorem lkmm_ptr1 {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hone : PointersOneHot layout q chunks) (hp : ProgramHolds layout q chunks) (ch : LinkCh)
    {t0 u0 a0 : ℕ} (ht0 : t0 < nTables) (hu0 : u0 < tableRowCount layout t0)
    (hω : omegaOf layout ch (boolL (linkRows layout) u0) t0 = 1) (hη : ch.etaMem = 1) (hηb : ch.etaBc = 0)
    (hmu : ch.mu.getD t0 [] = List.ofFn (n := (layout.tables.getD t0 default).links.memory.length)
      fun k ↦ if (k : ℕ) = a0 then 1 else 0)
    (ha0 : a0 < (layout.tables.getD t0 default).links.memory.length) :
    lkPtrC layout chunks q ch (boolL (linkRows layout) u0) (honestValues layout q (boolL (linkRows layout) u0))
        (ptrIndex chunks (wordAt layout q t0 1 u0)) t0 1 =
      ch.gammaMem.getD 1 0 * (((layout.tables.getD t0 default).links.memory.getD a0 default).reads.map
          (lkmm_rs layout (rowBc layout q chunks t0 u0))).sum +
        (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0).getD
            (layout.tables.getD t0 default).links.stateLink.fp 0 *
          (ch.gammaMem.getD 0 0 * lkmm_fa layout (rowBc layout q chunks t0 u0)
              ((layout.tables.getD t0 default).links.memory.getD a0 default) +
            ch.gammaMem.getD 1 0 * (((layout.tables.getD t0 default).links.memory.getD a0 default).reads.map
              (lkmm_rf layout (rowBc layout q chunks t0 u0))).sum) := by
  have hT := (announced_facts hA).2.1
  obtain ⟨hpre, -, -⟩ := lkt_pointers t0 ht0
  have h2 := two_le_ptrsOf hA ht0
  have hbcp : (ptrsOf layout t0).getD 1 0 = (tableAt layout t0).links.bytecodeLink.pointer := by
    have h := congrArg (fun l ↦ l.getD 1 0) hpre
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take] at h
    rw [ptrsOf_eq hA ht0, tableAt, hT]
    simpa using h
  have hσeq : ptrIndex chunks (wordAt layout q t0 1 u0) = rowBc layout q chunks t0 u0 := by
    rw [(wordAt_eq hA q ht0 (by omega) u0).1, hbcp]
    rfl
  have hbmem : (tableAt layout t0).links.bytecodeLink.pointer ∈ (tableAt layout t0).links.pointers := by
    have h := (wordAt_eq hA q ht0 (k := 1) (by omega) u0).2
    rwa [hbcp] at h
  have hσW : rowBc layout q chunks t0 u0 < 2 ^ chunks.width :=
    ptrIndex_lt hch _ (hone t0 ht0 u0 hu0 _ hbmem)
  obtain ⟨hk, -, hop, -, -⟩ := hp t0 ht0 u0 hu0
  obtain ⟨hps1, hps2⟩ := lkmm_ps hA ch (W := chunks.width) ht0 hσW hk hop hη hηb hmu ha0
  rw [hσeq]
  simp only [lkPtrC, hω, one_mul, lkIdxB, lkIdx, idxAt, hηb, zero_mul, zero_add,
    lkmm_below chunks hσW, ite_eq_left_of_eq_true _ _ (eq_true hk), hps1, hps2]

/-- A word read through a pointer: the memory term at the pointer's cell times its scale. -/
def lkmm_rw (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (t u : ℕ) (col : ℕ → E) :
    Read → E
  | .word p sc => honestM1 layout chunks q (boolL chunks.width (rowPtr layout q chunks t p u)) * sc.evaluate col
  | _ => 0

/-- An access's window read: `y_mem` at the cell its pointer and shift name, `0` outside the window. -/
def lkmm_y (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (ch : LinkCh) (t u : ℕ) (a : Access) : E :=
  match windowHit (chunks.widths.getD 0 0) (rowPtr layout q chunks t a.pointer u) a.shift with
  | some j => (lkIdxB layout chunks q ch j).yMem
  | none => 0

/-- **The drawn row's memory pointers' shares**: access `a0`'s word reads and its window read. -/
theorem lkmm_ptrs {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) (chunks : Chunks) (ch : LinkCh) {t0 u0 a0 : ℕ} (ht0 : t0 < nTables)
    (hω : omegaOf layout ch (boolL (linkRows layout) u0) t0 = 1) (hη : ch.etaMem = 1)
    (hmu : ch.mu.getD t0 [] = List.ofFn (n := (layout.tables.getD t0 default).links.memory.length)
      fun k ↦ if (k : ℕ) = a0 then 1 else 0)
    (ha0 : a0 < (layout.tables.getD t0 default).links.memory.length) :
    ∑ k ∈ Ico 2 (ptrsOf layout t0).length, lkPtrC layout chunks q ch (boolL (linkRows layout) u0)
        (honestValues layout q (boolL (linkRows layout) u0)) (ptrIndex chunks (wordAt layout q t0 k u0)) t0 k =
      ch.gammaMem.getD 1 0 * (((layout.tables.getD t0 default).links.memory.getD a0 default).reads.map
          (lkmm_rw layout chunks q t0 u0
            fun c ↦ (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0).getD c 0)).sum +
        lkGate (fun c ↦ (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0).getD c 0)
            ((layout.tables.getD t0 default).links.memory.getD a0 default) *
          lkmm_y layout chunks q ch t0 u0 ((layout.tables.getD t0 default).links.memory.getD a0 default) := by
  have hT := (announced_facts hA).2.1
  set col := fun c ↦ (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0).getD c 0 with hcol
  set L := (layout.tables.getD t0 default).links.memory with hL
  set A := L.getD a0 default with hAdef
  have hAL : A ∈ L := by
    rw [hAdef, List.getD_eq_getElem _ _ ha0]
    exact List.getElem_mem _
  have hAmem : A ∈ (tables.getD t0 default).links.memory := by
    rw [← hT]
    exact hAL
  obtain ⟨-, hnd, hacc⟩ := lkt_pointers t0 ht0
  rw [← ptrsOf_eq hA ht0] at hnd hacc
  set G : ℕ → E → Form → E := fun p m sc ↦
    m * ch.gammaMem.getD 1 0 * honestM1 layout chunks q (boolL chunks.width (rowPtr layout q chunks t0 p u0)) *
      sc.evaluate col with hG
  have hk : ∀ k ∈ Ico 2 (ptrsOf layout t0).length, lkPtrC layout chunks q ch (boolL (linkRows layout) u0)
      (honestValues layout q (boolL (linkRows layout) u0)) (ptrIndex chunks (wordAt layout q t0 k u0)) t0 k =
      (A.reads.map fun rd ↦ lkRead ((ptrsOf layout t0).getD k 0) (G ((ptrsOf layout t0).getD k 0)) 1 rd).sum +
        (if A.pointer = (ptrsOf layout t0).getD k 0 then
          lkGate col A * lkmm_y layout chunks q ch t0 u0 A else 0) := by
    intro k hk
    have hk' := mem_Ico.mp hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    rw [(wordAt_eq hA q ht0 hk'.2 u0).1]
    simp only [lkPtrC, hω, hη, hmu]
    rw [lkmm_zip_unit _ ha0 _ ?_, lkmm_sum_filter, lkmm_zip_unit _ ha0 _ ?_]
    · simp only [← hAdef, one_mul, mul_one]
      refine congrArg₂ (· + ·) ?_ ?_
      · refine congrArg List.sum (List.map_congr_left fun rd _ ↦ ?_)
        cases rd with
        | word p sc => simp only [lkRead, hG, one_mul]; split_ifs <;> rfl
        | _ => simp only [lkRead]
      · by_cases hpk : A.pointer = (ptrsOf layout t0).getD (k' + 2) 0
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hpk), ite_eq_left_of_eq_true _ _ (eq_true hpk), lkmm_y, hpk]
          rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hpk), ite_eq_right_of_eq_false _ _ (eq_false hpk)]
    · intro a
      simp
    · intro a
      refine List.sum_eq_zero fun z hz ↦ ?_
      obtain ⟨rd, -, rfl⟩ := List.mem_map.mp hz
      cases rd <;> simp [lkRead]
  rw [sum_congr rfl hk, sum_add_distrib, sum_list_map_comm]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun rd hrd ↦ ?_)
    cases rd with
    | word p sc =>
      obtain ⟨b, hb, hbp, -, -⟩ := lkt_word_read t0 ht0 A hAmem p sc hrd
      have hp := hacc b hb
      rw [hbp] at hp
      simp only [lkRead]
      rw [lkmm_sum_ptrs hnd hp (fun p' ↦ G p' 1 sc)]
      simp only [hG, lkmm_rw]
      ring
    | _ => simp [lkRead, lkmm_rw]
  · exact lkmm_sum_ptrs hnd (hacc A hAmem) (fun p ↦ lkGate col A * lkmm_y layout chunks q ch t0 u0 A)

/-! ## The rest at the draw -/

theorem lkmm_yMem (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (ch : LinkCh) (j : ℕ) :
    (lkIdxB layout chunks q ch j).yMem = ch.gammaMem.getD 0 0 * indexMle (boolL chunks.width j) +
      ch.gammaMem.getD 3 0 * belowAt chunks (boolL chunks.width j) layout.logMemory +
      ch.gammaMem.getD 1 0 * honestM1 layout chunks q (boolL chunks.width j) := rfl

/-- **The rest at the draw `lkmm_x`**: access `a0`'s terms alone. -/
theorem lkmm_rest_eq {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hone : PointersOneHot layout q chunks) (hp : ProgramHolds layout q chunks)
    {t0 u0 a0 : ℕ} (ht0 : t0 < nTables) (hu0 : u0 < tableRowCount layout t0)
    (ha0 : a0 < (layout.tables.getD t0 default).links.memory.length) (g0 g1 g2 : E) :
    let ch := chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 g0 g1 g2))
    let col := fun c ↦ (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0).getD c 0
    let A := (layout.tables.getD t0 default).links.memory.getD a0 default
    let σ := rowBc layout q chunks t0 u0
    lkRest layout chunks q (lkp_set layout chunks (lkmm_x t0 u0 a0 g0 g1 g2)) =
      lkGate col A * (g0 * A.address.evaluate col + g2 + g1 * A.value.evaluate col) +
      (g1 * (A.reads.map (lkmm_rs layout σ)).sum +
        col (layout.tables.getD t0 default).links.stateLink.fp *
          (g0 * lkmm_fa layout σ A + g1 * (A.reads.map (lkmm_rf layout σ)).sum)) +
      (g1 * (A.reads.map (lkmm_rw layout chunks q t0 u0 col)).sum +
        lkGate col A * lkmm_y layout chunks q ch t0 u0 A) := by
  intro ch col A σ
  have hT := (announced_facts hA).2.1
  have hTlen : layout.tables.length = nTables := by rw [hT, tables_length]
  have hrows : ∀ t < nTables, tableRowCount layout t ≤ 2 ^ heightOf layout t :=
    fun t ht ↦ tableRows_le_height hA ht
  have hω : ∀ t < nTables, ∀ u < tableRowCount layout t,
      omegaOf layout ch (boolL (linkRows layout) u) t = if t = t0 ∧ u = u0 then 1 else 0 :=
    fun t ht u hu ↦ lkmm_omega (layout := layout) ch (fun t ht ↦ lkmm_ch_theta hch t0 u0 a0 g0 g1 g2 ht)
      (lkmm_ch_tau hch t0 u0 a0 g0 g1 g2) hrows hu0 ht hu
  have hω0 : omegaOf layout ch (boolL (linkRows layout) u0) t0 = 1 := by
    rw [hω t0 ht0 u0 hu0]
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, rfl⟩)
  obtain ⟨hη, hηb⟩ := lkmm_ch_eta hch t0 u0 a0 g0 g1 g2
  obtain ⟨hγ0, hγ1, hγ3⟩ := lkmm_ch_gamma hch t0 u0 a0 g0 g1 g2
  have hmu : ch.mu.getD t0 [] = List.ofFn (n := (layout.tables.getD t0 default).links.memory.length)
      fun k ↦ if (k : ℕ) = a0 then 1 else 0 := by
    rw [lkmm_ch_mu hch t0 u0 a0 g0 g1 g2 (by omega)]
    simp only [true_and]
  have h2 := two_le_ptrsOf hA ht0
  rw [lkmm_rest_single q _ ht0 hu0 hω, sum_eq_sum_Ico_succ_bot (by omega),
    lkmm_base layout ch _ _ hω0 hη hηb hmu ha0, lkmm_ptr1 hA q hch hone hp ch ht0 hu0 hω0 hη hηb hmu ha0,
    lkmm_ptrs hA q chunks ch ht0 hω0 hη hmu ha0, hγ0, hγ1, hγ3]
  exact (add_assoc _ _ _).symm

/-! ## The row's columns -/

theorem lkmm_index {L : List Access} {a : Access} (ha : a ∈ L) : ∃ a0 < L.length, L.getD a0 default = a := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩

/-- At an executed row, an access's columns as the row side reads them are the stack's. -/
theorem lkmm_cols {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {t0 u0 : ℕ} (ht0 : t0 < nTables) (hu0 : u0 < tableRowCount layout t0)
    {a : Access} (ha : a ∈ (tableAt layout t0).links.memory) :
    let col := fun c ↦ (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0).getD c 0
    let tv := fun c ↦ tableValue layout q t0 c u0
    lkGate col a = accessGate layout q t0 u0 a ∧ a.address.evaluate col = a.address.evaluate tv ∧
      a.value.evaluate col = a.value.evaluate tv ∧
      col (tableAt layout t0).links.stateLink.fp = tv (tableAt layout t0).links.stateLink.fp ∧
      ∀ p sc, Read.word p sc ∈ a.reads → sc.evaluate col = sc.evaluate tv := by
  intro col tv
  have hT := (announced_facts hA).2.1
  have hTlen : layout.tables.length = nTables := by rw [hT, tables_length]
  have hu0' : u0 < 2 ^ heightOf layout t0 := lt_of_lt_of_le hu0 (tableRows_le_height hA ht0)
  have hc : ∀ c, c < (tables.getD t0 default).width ∧ c ∉ (tables.getD t0 default).links.pointers →
      col c = tv c := by
    intro c ⟨h1, h2⟩
    refine lkVals_bool layout q (by omega) hu0' (by rw [hT]; exact h1) ?_
    rw [ptrsOf_eq hA ht0]
    exact h2
  have hcols := lkt_cols t0 ht0
  dsimp only at hcols
  obtain ⟨-, hfp, -, -, -, hmem⟩ := hcols
  have ha' : a ∈ (tables.getD t0 default).links.memory := by
    rw [tableAt, hT] at ha
    exact ha
  obtain ⟨hav, hg, hrd⟩ := hmem a ha'
  have htab : tableAt layout t0 = tables.getD t0 default := by rw [tableAt, hT]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold lkGate accessGate
    rcases hga : a.gate with _ | c
    · rfl
    · simp only [Option.map_some, Option.getD_some]
      exact hc c (hg c hga)
  · exact form_evaluate_congr _ fun c hc' ↦ hc c (hav c (List.mem_append_left _ hc'))
  · exact form_evaluate_congr _ fun c hc' ↦ hc c (hav c (List.mem_append_right _ hc'))
  · rw [htab]
    exact hc _ hfp
  · exact fun p sc h ↦ form_evaluate_congr _ fun c hc' ↦ hc c (hrd p sc h c hc')

theorem lkmm_eq_of_add_eq_zero {a b : E} (h : a + b = 0) : a = b := by
  linear_combination h - CharTwo.add_self_eq_zero b

/-! ## The memory case -/

/-- **A failed memory lookup gives a draw at which the rest is nonzero**, under the program lookup. -/
theorem lkRest_ne_of_memory {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hone : PointersOneHot layout q chunks) (hp : ProgramHolds layout q chunks)
    (hm : ¬ MemoryHolds layout q chunks) :
    ∃ x : lkp_Vals, lkRest layout chunks q (lkp_set layout chunks x) ≠ 0 := by
  have hT := (announced_facts hA).2.1
  unfold MemoryHolds at hm
  push Not at hm
  obtain ⟨t0, ht0, u0, hu0, a, ha, hga, hfail⟩ := hm
  have hw0 : chunks.widths.getD 0 0 ≤ chunks.width := by
    have := (chunks_geometry hch 0 (lkw_chunks_tile hch).1).1
    omega
  obtain ⟨-, -, hacc⟩ := lkt_pointers t0 ht0
  have htab : tableAt layout t0 = tables.getD t0 default := by rw [tableAt, hT]
  -- every access's pointer decodes below `2^W`
  have hσW : ∀ b ∈ (tableAt layout t0).links.memory,
      rowPtr layout q chunks t0 b.pointer u0 < 2 ^ chunks.width := by
    intro b hb
    have hb' : b ∈ (tables.getD t0 default).links.memory := htab ▸ hb
    refine ptrIndex_lt hch _ (hone t0 ht0 u0 hu0 _ ?_)
    rw [htab]
    exact List.mem_of_mem_drop (hacc b hb')
  by_cases hpres : ∃ b ∈ (tableAt layout t0).links.memory, accessGate layout q t0 u0 b ≠ 0 ∧
      ∀ j, windowHit (chunks.widths.getD 0 0) (rowPtr layout q chunks t0 b.pointer u0) b.shift = some j →
        ¬ j < 2 ^ layout.logMemory
  · -- a presence failure: `γ_mem = (0, 0, 1)`
    obtain ⟨b, hb, hgb, hnb⟩ := hpres
    obtain ⟨a0, ha0, rfl⟩ := lkmm_index hb
    refine ⟨lkmm_x t0 u0 a0 0 0 1, ?_⟩
    rw [lkmm_rest_eq hA q hch hone hp ht0 hu0 ha0]
    rw [show layout.tables.getD t0 default = tableAt layout t0 from rfl]
    obtain ⟨hgate, -, -, -, -⟩ := lkmm_cols hA q ht0 hu0 hb
    obtain ⟨hγ0, hγ1, hγ3⟩ := lkmm_ch_gamma (layout := layout) hch t0 u0 a0 0 0 1
    have hY : lkmm_y layout chunks q (chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 0 0 1))) t0 u0
        ((tableAt layout t0).links.memory.getD a0 default) = 0 := by
      unfold lkmm_y
      rcases hw : windowHit (chunks.widths.getD 0 0)
          (rowPtr layout q chunks t0 ((tableAt layout t0).links.memory.getD a0 default).pointer u0)
          ((tableAt layout t0).links.memory.getD a0 default).shift with _ | j
      · rfl
      · have hjW := windowHit_lt hw0 (hσW _ hb) hw
        simp only
        rw [lkmm_yMem, hγ0, hγ1, hγ3, lkmm_below chunks hjW,
          ite_eq_right_of_eq_false _ _ (eq_false (hnb j hw))]
        ring
    dsimp only
    rw [hY, hgate]
    ring_nf
    exact hgb
  · push Not at hpres
    obtain ⟨a0, ha0, rfl⟩ := lkmm_index ha
    set A := (tableAt layout t0).links.memory.getD a0 default with hAdef
    obtain ⟨j, hw, hjm⟩ := hpres A ha hga
    have hjW := windowHit_lt hw0 (hσW _ ha) hw
    obtain ⟨hgate, haddr, hval, hfp, hrds⟩ := lkmm_cols hA q ht0 hu0 ha
    dsimp only at hgate haddr hval hfp hrds
    have hA' : A ∈ (tables.getD t0 default).links.memory := htab ▸ ha
    by_cases haddrEq : gpow j = accessAddress layout q t0 u0 (rowBc layout q chunks t0 u0) A
    · -- a word failure: `γ_mem = (0, 1, 0)`
      have hword := hfail j hw hjm haddrEq
      refine ⟨lkmm_x t0 u0 a0 0 1 0, ?_⟩
      rw [lkmm_rest_eq hA q hch hone hp ht0 hu0 ha0]
      rw [show layout.tables.getD t0 default = tableAt layout t0 from rfl]
      rw [← hAdef]
      obtain ⟨hγ0, hγ1, hγ3⟩ := lkmm_ch_gamma (layout := layout) hch t0 u0 a0 0 1 0
      have hY : lkmm_y layout chunks q (chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 0 1 0))) t0 u0 A =
          memWord layout q j := by
        unfold lkmm_y
        rw [hw]
        simp only
        rw [lkmm_yMem, hγ0, hγ1, hγ3, lkmm_m1 layout chunks q hjW hjm]
        ring
      dsimp only
      rw [hY, hgate, hval]
      intro h0
      apply hword
      rcases hg : A.gate with _ | c
      · -- ungated: the reads' values
        have hg1 : accessGate layout q t0 u0 A = 1 := by simp [accessGate, hg]
        have hR : (A.reads.map (readValue layout q chunks t0 u0 (rowBc layout q chunks t0 u0))).sum =
            (A.reads.map (lkmm_rs layout (rowBc layout q chunks t0 u0))).sum +
              (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0).getD
                  (tableAt layout t0).links.stateLink.fp 0 *
                (A.reads.map (lkmm_rf layout (rowBc layout q chunks t0 u0))).sum +
              (A.reads.map (lkmm_rw layout chunks q t0 u0
                fun c ↦ (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0).getD c 0)).sum := by
          rw [← List.sum_map_mul_left, ← List.sum_map_add, ← List.sum_map_add]
          refine congrArg List.sum (List.map_congr_left fun rd hrd ↦ ?_)
          cases rd with
          | word p sc =>
            obtain ⟨b, hb, hbp, hb0, hbg⟩ := lkt_word_read t0 ht0 A hA' p sc hrd
            have hb' : b ∈ (tableAt layout t0).links.memory := htab ▸ hb
            obtain ⟨jb, hwb, hjb⟩ := hpres b hb' (by simp [accessGate, hbg])
            rw [hb0, windowHit_zero] at hwb
            obtain rfl := Option.some.inj hwb
            have hpW := hσW b hb'
            rw [hbp] at hpW hjb
            simp only [readValue, lkmm_rs, lkmm_rf, lkmm_rw, mul_zero, zero_add,
              lkmm_m1 layout chunks q hpW hjb, hrds p sc hrd]
            ring
          | slot s sc => simp [readValue, lkmm_rs, lkmm_rf, lkmm_rw]
          | frame s sc =>
            simp only [readValue, lkmm_rs, lkmm_rf, lkmm_rw, zero_add, add_zero]
            rw [hfp]
            ring
          | pc s sc =>
            simp only [readValue, lkmm_rs, lkmm_rf, lkmm_rw, mul_zero, add_zero]
            ring
        rw [hg1] at h0
        rw [accessWord, hR]
        refine (lkmm_eq_of_add_eq_zero ?_).symm
        linear_combination h0
      · -- gated: no reads
        have hr := (lkt_gated t0 ht0 A hA' (by simp [hg])).2
        have hgz : accessGate layout q t0 u0 A ≠ 0 := hga
        rw [hr] at h0
        simp only [List.map_nil, List.sum_nil, mul_zero, zero_mul, add_zero, zero_add] at h0
        rw [accessWord, hr, List.map_nil, List.sum_nil, add_zero]
        have h1 : accessGate layout q t0 u0 A * (A.value.evaluate (fun c ↦ tableValue layout q t0 c u0) +
            memWord layout q j) = 0 := by linear_combination h0
        exact (lkmm_eq_of_add_eq_zero ((mul_eq_zero.mp h1).resolve_left hgz)).symm
    · -- an address failure: `γ_mem = (1, 0, 0)`
      refine ⟨lkmm_x t0 u0 a0 1 0 0, ?_⟩
      rw [lkmm_rest_eq hA q hch hone hp ht0 hu0 ha0]
      rw [show layout.tables.getD t0 default = tableAt layout t0 from rfl]
      rw [← hAdef]
      obtain ⟨hγ0, hγ1, hγ3⟩ := lkmm_ch_gamma (layout := layout) hch t0 u0 a0 1 0 0
      have hY : lkmm_y layout chunks q (chV layout chunks (lkp_set layout chunks (lkmm_x t0 u0 a0 1 0 0))) t0 u0 A =
          gpow j := by
        unfold lkmm_y
        rw [hw]
        simp only
        rw [lkmm_yMem, hγ0, hγ1, hγ3, indexMle_boolL hjW]
        ring
      dsimp only
      rw [hY, hgate, haddr]
      intro h0
      apply haddrEq
      rcases hg : A.gate with _ | c
      · have hg1 : accessGate layout q t0 u0 A = 1 := by simp [accessGate, hg]
        rw [hg1] at h0
        refine lkmm_eq_of_add_eq_zero ?_
        rw [accessAddress]
        rcases hf : A.frame with _ | ⟨s, e⟩
        · simp only [lkmm_fa, hf] at h0
          linear_combination h0
        · simp only [lkmm_fa, hf] at h0
          rw [hfp] at h0
          dsimp only
          linear_combination h0
      · have hf := (lkt_gated t0 ht0 A hA' (by simp [hg])).1
        have hgz : accessGate layout q t0 u0 A ≠ 0 := hga
        simp only [lkmm_fa, hf] at h0
        have h1 : accessGate layout q t0 u0 A * (gpow j +
            A.address.evaluate (fun c ↦ tableValue layout q t0 c u0)) = 0 := by linear_combination h0
        have h2 := (mul_eq_zero.mp h1).resolve_left hgz
        rw [accessAddress, hf, add_zero]
        exact lkmm_eq_of_add_eq_zero h2

end

end LeanVM.Protocol.Relation

/-- info: 'LeanVM.Protocol.Relation.lkRest_ne_of_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.lkRest_ne_of_memory
