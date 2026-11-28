/-
  LeanVM.Protocol.Relation.Link.GroupLinksProgram

  The program case of the link's failing polynomial: a failing program lookup gives a draw at which
  the rest (`lkRest`) is nonzero.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupLinksRest
public import LeanVM.Protocol.Relation.Link.GroupLinksWeights
public import LeanVM.Protocol.Relation.Link.GroupLinksSplit
public import LeanVM.Protocol.Relation.Link.Valid
public import LeanVM.Parameters.Generator
public import LeanVM.Parameters.Field

/-!
# The program case

`lkRest_ne_of_program`: if an executed row's program lookup fails, `lkRest` is nonzero at the draw
`lkpg_vals t0 u0 s0`: `θ` the unit at the row's table `t0`, `τ` the bits of its row `u0`,
`η_mem = 0`, `η_bc = 1` and `α` the bits of a slot `s0`, all else zero. Only that row's base term
and program pointer's share survive (`lkpg_rest`), and they are slot `s0`'s equation, both sides
added: `2` for a pointer past the program, `1` for the `pc`, `3` for the opcode, an operand
equation's first slot for that equation.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

/-- The program case's draw: `θ` the unit at `t0`, `τ` the bits of `u0`, `α` the bits of `s0`,
`η_bc = 1`, all else zero. -/
def lkpg_vals (t0 u0 s0 : ℕ) : lkp_Vals where
  theta := fun i ↦ if i = t0 then 1 else 0
  gammaState := fun _ ↦ 0
  gammaMem := fun _ ↦ 0
  mu := fun _ _ ↦ 0
  alpha := fun i ↦ if s0.testBit i then 1 else 0
  etaMem := 0
  etaBc := 1
  eps := fun _ ↦ 0
  tau := fun i ↦ if u0.testBit i then 1 else 0
  zeta := fun _ ↦ 0
  nu := fun _ ↦ 0

/-- The draw's challenges. -/
abbrev lkpg_ch (layout : Layout) (chunks : Chunks) (t0 u0 s0 : ℕ) : LinkCh :=
  chV layout chunks (lkp_set layout chunks (lkpg_vals t0 u0 s0))

/-- Table `t`'s `omega` weight on slot `i` at the draw: the opcode's at `s0 = 3`, and each operand
equation whose first slot is `s0` on its slots. -/
def lkpg_Om (layout : Layout) (s0 t i : ℕ) : E :=
  (if i = 3 then (if 3 = s0 then (1 : E) else 0) else 0) +
    ((layout.tables.getD t default).links.bytecodeLink.operands.map fun op ↦
      (op.1.map fun s ↦ if s = i then (if op.1.headD 0 = s0 then (1 : E) else 0) else 0).sum).sum

theorem lkpg_eq_of_add {a b : E} (h : a + b = 0) : a = b := by
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  exact h

theorem lkpg_gpow_ne_zero (n : ℕ) : gpow n ≠ 0 := by
  intro h
  have h1 := gpow_eq_ofK n
  rw [h] at h1
  have h0 : ofK 0 = 0 := by
    show algebraMap K E 0 = 0
    exact map_zero _
  exact LeanVM.Parameters.gpow_ne_zero n (ofK_injective (h1.symm.trans h0.symm))

theorem lkpg_gpow_inj {a b : ℕ} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (h : gpow a = gpow b) : a = b := by
  rw [gpow_eq_ofK, gpow_eq_ofK] at h
  exact gpow_injOn (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) (ofK_injective h)

/-- With distinct heads, the weights `[hd y = hd x]` select `x`. -/
theorem lkpg_sum_head {α : Type} (hd : α → ℕ) (F : α → E) : ∀ (L : List α), (L.map hd).Nodup →
    ∀ x ∈ L, (L.map fun y ↦ (if hd y = hd x then (1 : E) else 0) * F y).sum = F x
  | [], _, x, hx => by simp at hx
  | y :: L, hnd, x, hx => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [ite_eq_left rfl, one_mul, List.sum_eq_zero, add_zero]
      intro z hz
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      have hne : hd w ≠ hd x := fun h ↦ hnd.1 (by rw [← h]; exact List.mem_map.mpr ⟨w, hw, rfl⟩)
      rw [ite_eq_right hne, zero_mul]
    · have hne : hd y ≠ hd x := fun h ↦ hnd.1 (by rw [h]; exact List.mem_map.mpr ⟨x, hx, rfl⟩)
      rw [ite_eq_right hne, zero_mul, zero_add]
      exact lkpg_sum_head hd F L hnd.2 x hx

theorem lkpg_lkRead_zero (p : ℕ) (m : E) : lkRead p (fun _ _ ↦ 0) m = fun _ ↦ 0 := by
  funext rd
  cases rd <;> simp [lkRead]

/-- At `η_mem = 0` a memory pointer's share vanishes. -/
theorem lkpg_ptr_two (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (ch : LinkCh)
    (h0 : ch.etaMem = 0) (chi message : List E) (σ t k : ℕ) :
    lkPtrC layout chunks q ch chi message σ t (k + 2) = 0 := by
  simp only [lkPtrC, h0, mul_zero, zero_mul, lkpg_lkRead_zero]
  simp

/-- At `η_mem = 0` and `η_bc = 1`, a row's base term and non-cycle shares: its weight times its
program equations. -/
theorem lkpg_row {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    (chunks : Chunks) {μ : ℕ} (q : Column μ) (ch : LinkCh) (hem : ch.etaMem = 0) (hbc : ch.etaBc = 1)
    {t : ℕ} (ht : t < nTables) (chi message : List E) (σ : ℕ → ℕ) :
    lkBaseC layout ch chi message t +
        ∑ k ∈ Ico 1 (ptrsOf layout t).length, lkPtrC layout chunks q ch chi message (σ k) t k =
      omegaOf layout ch chi t * (lkRBc ch (layout.tables.getD t default) (lkVals layout message t) +
        (lkIdxB layout chunks q ch (σ 1)).xBc +
        (lkVals layout message t).getD (layout.tables.getD t default).links.stateLink.fp 0 *
          (lkIdxB layout chunks q ch (σ 1)).pFp) := by
  have h2 := two_le_ptrsOf hA ht
  have hz : ∑ k ∈ Ico (1 + 1) (ptrsOf layout t).length, lkPtrC layout chunks q ch chi message (σ k) t k = 0 := by
    refine sum_eq_zero fun k hk ↦ ?_
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by have := (mem_Ico.mp hk).1; omega⟩
    exact lkpg_ptr_two layout chunks q ch hem _ _ _ _ _
  rw [sum_eq_sum_Ico_succ_bot (by omega : 1 < (ptrsOf layout t).length), hz]
  simp only [lkBaseC, lkPtrC, hem, hbc]
  ring

section Draw

variable {layout : Layout} {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks) (t0 u0 s0 : ℕ)
include hch

theorem lkpg_etaMem : (lkpg_ch layout chunks t0 u0 s0).etaMem = 0 := lkp_chV_etaMem hch _

theorem lkpg_etaBc : (lkpg_ch layout chunks t0 u0 s0).etaBc = 1 := lkp_chV_etaBc hch _

theorem lkpg_slot {s0 : ℕ} (hs0 : s0 < 2 ^ bytecodeSlotBits) (j : ℕ) :
    (eqKernel (lkpg_ch layout chunks t0 u0 s0).alpha).getD j 0 = if j = s0 then 1 else 0 := by
  rw [lkp_chV_alpha hch]
  exact eqKernel_boolL hs0 j

theorem lkpg_theta {t : ℕ} (ht : t < nTables) :
    (lkpg_ch layout chunks t0 u0 s0).theta.getD t 0 = if t = t0 then 1 else 0 := by
  rw [lkp_chV_theta hch, List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_ofFn]
  rfl

theorem lkpg_tau : (lkpg_ch layout chunks t0 u0 s0).tau = boolL (linkRows layout) u0 := by
  rw [lkp_chV_tau hch]
  rfl

/-- The draw's row weight: one at row `u0` of table `t0`, zero at the other executed rows. -/
theorem lkpg_omega {bytecode : List K} {ρ : ℕ} (hA : Announced bytecode layout ρ) (ht0 : t0 < nTables)
    (hu0 : u0 < tableRowCount layout t0) {t u : ℕ} (ht : t < nTables) (hu : u < tableRowCount layout t) :
    omegaOf layout (lkpg_ch layout chunks t0 u0 s0) (boolL (linkRows layout) u) t =
      if t = t0 ∧ u = u0 then 1 else 0 := by
  have hrows : layout.tableRows.getD t 0 ≤ 2 ^ heightOf layout t := tableRows_le_height hA ht
  have hu' : u < 2 ^ heightOf layout t := lt_of_lt_of_le hu hrows
  have hτh : ((lkpg_ch layout chunks t0 u0 s0).tau.take (heightOf layout t)).length = heightOf layout t := by
    rw [List.length_take, chV_tau_length hch]
    exact min_eq_left (heightOf_le layout t)
  rw [omegaOf, take_boolL (heightOf_le layout t), Nat.mod_eq_of_lt hu', omegaAt_boolL _ _ hτh hu' hrows,
    ite_eq_left (show u < layout.tableRows.getD t 0 from hu), lkpg_theta hch t0 u0 s0 ht, lkpg_tau hch,
    take_boolL (heightOf_le layout t), eqAt_boolL hu' (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases htt : t = t0
  · subst htt
    have h0 : u0 < 2 ^ heightOf layout t := lt_of_lt_of_le hu0 hrows
    rw [Nat.mod_eq_of_lt h0]
    simp
  · simp [htt]

/-- **The rest at the draw**: row `u0` of table `t0`'s base term and program pointer's share. -/
theorem lkpg_rest {bytecode : List K} {ρ : ℕ} (hA : Announced bytecode layout ρ) {μ : ℕ} (q : Column μ)
    (ht0 : t0 < nTables) (hu0 : u0 < tableRowCount layout t0) :
    lkRest layout chunks q (lkp_set layout chunks (lkpg_vals t0 u0 s0)) =
      lkRBc (lkpg_ch layout chunks t0 u0 s0) (layout.tables.getD t0 default)
          (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0) +
        (lkIdxB layout chunks q (lkpg_ch layout chunks t0 u0 s0) (ptrIndex chunks (wordAt layout q t0 1 u0))).xBc +
        (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0).getD
            (layout.tables.getD t0 default).links.stateLink.fp 0 *
          (lkIdxB layout chunks q (lkpg_ch layout chunks t0 u0 s0)
            (ptrIndex chunks (wordAt layout q t0 1 u0))).pFp := by
  have hem := lkpg_etaMem (layout := layout) hch t0 u0 s0
  have hbc := lkpg_etaBc (layout := layout) hch t0 u0 s0
  have hrow := fun {t : ℕ} (ht : t < nTables) (u : ℕ) ↦
    lkpg_row hA chunks q (lkpg_ch layout chunks t0 u0 s0) hem hbc ht (boolL (linkRows layout) u)
      (honestValues layout q (boolL (linkRows layout) u)) (fun k ↦ ptrIndex chunks (wordAt layout q t k u))
  unfold lkRest
  have hin : ∀ t ∈ range nTables, t ≠ t0 → ∑ u ∈ range (tableRowCount layout t),
      (lkBaseC layout (chV layout chunks (lkp_set layout chunks (lkpg_vals t0 u0 s0))) (boolL (linkRows layout) u)
        (honestValues layout q (boolL (linkRows layout) u)) t +
      ∑ k ∈ Ico 1 (ptrsOf layout t).length, lkPtrC layout chunks q
        (chV layout chunks (lkp_set layout chunks (lkpg_vals t0 u0 s0)))
        (boolL (linkRows layout) u) (honestValues layout q (boolL (linkRows layout) u))
        (ptrIndex chunks (wordAt layout q t k u)) t k) = 0 := by
    intro t ht hne
    refine sum_eq_zero fun u hu ↦ ?_
    rw [hrow (mem_range.mp ht) u, lkpg_omega hch t0 u0 s0 hA ht0 hu0 (mem_range.mp ht) (mem_range.mp hu),
      ite_eq_right (fun h ↦ hne h.1), zero_mul]
  rw [sum_eq_single t0 hin (fun h ↦ absurd (mem_range.mpr ht0) h)]
  have hin' : ∀ u ∈ range (tableRowCount layout t0), u ≠ u0 →
      lkBaseC layout (chV layout chunks (lkp_set layout chunks (lkpg_vals t0 u0 s0))) (boolL (linkRows layout) u)
        (honestValues layout q (boolL (linkRows layout) u)) t0 +
      ∑ k ∈ Ico 1 (ptrsOf layout t0).length, lkPtrC layout chunks q
        (chV layout chunks (lkp_set layout chunks (lkpg_vals t0 u0 s0)))
        (boolL (linkRows layout) u) (honestValues layout q (boolL (linkRows layout) u))
        (ptrIndex chunks (wordAt layout q t0 k u)) t0 k = 0 := by
    intro u hu hne
    rw [hrow ht0 u, lkpg_omega hch t0 u0 s0 hA ht0 hu0 ht0 (mem_range.mp hu), ite_eq_right (fun h ↦ hne h.2),
      zero_mul]
  rw [sum_eq_single u0 hin' (fun h ↦ absurd (mem_range.mpr hu0) h), hrow ht0 u0,
    lkpg_omega hch t0 u0 s0 hA ht0 hu0 ht0 hu0, ite_eq_left ⟨rfl, rfl⟩, one_mul]

/-- The program pointer's scalars at `σ`: `X_bc` and `P_fp`. -/
theorem lkpg_idx {s0 : ℕ} (hs0 : s0 < 2 ^ bytecodeSlotBits) (hW : layout.logBytecode ≤ chunks.width)
    {σ : ℕ} (hσ : σ < 2 ^ chunks.width) {μ : ℕ} (q : Column μ) :
    (lkIdxB layout chunks q (lkpg_ch layout chunks t0 u0 s0) σ).xBc =
      (if 1 = s0 then 1 else 0) * gpow σ + (if σ < 2 ^ layout.logBytecode then 1 else 0) *
        ((if 2 = s0 then 1 else 0) +
          (programSums layout (lkpg_ch layout chunks t0 u0 s0) (linkSplit layout (boolL chunks.width σ))).1) ∧
    (lkIdxB layout chunks q (lkpg_ch layout chunks t0 u0 s0) σ).pFp =
      (if σ < 2 ^ layout.logBytecode then 1 else 0) *
        (programSums layout (lkpg_ch layout chunks t0 u0 s0) (linkSplit layout (boolL chunks.width σ))).2 := by
  have hb : belowAt chunks (boolL chunks.width σ) layout.logBytecode =
      if σ < 2 ^ layout.logBytecode then 1 else 0 := by
    rw [belowAt, min_eq_left hW, prodE_drop_boolL hW hσ]
  simp only [lkIdxB, lkIdx, idxAt, hb, indexMle_boolL hσ, lkpg_etaBc hch, lkpg_slot hch t0 u0 hs0, one_mul]
  refine ⟨?_, ?_⟩ <;> trivial

/-- The draw's slot weights: `omega` is `lkpg_Om`, `pc` and `frame` are zero. -/
theorem lkpg_weights {s0 : ℕ} (hs0 : s0 < 2 ^ bytecodeSlotBits) {t : ℕ} (ht : t < layout.tables.length)
    {i : ℕ} (hi : i < 2 ^ bytecodeSlotBits) :
    let ch := lkpg_ch layout chunks t0 u0 s0
    let w := slotWeights layout.tables (eqKernel ch.alpha) (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0)
      ch.mu ch.etaMem ch.etaBc
    (w.omega.getD t []).getD i 0 = lkpg_Om layout s0 t i ∧ (w.pc.getD t []).getD i 0 = 0 ∧
      (w.frame.getD t []).getD i 0 = 0 := by
  intro ch w
  obtain ⟨h1, h2, h3⟩ := slotWeights_getD layout.tables (eqKernel ch.alpha)
    (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) ch.mu ch.etaMem ch.etaBc ht
  obtain ⟨k1, k2, k3⟩ := tsw_closed (layout.tables.getD t default) (eqKernel ch.alpha)
    (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) (ch.mu.getD t []) ch.etaMem ch.etaBc hi
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, k1]
    simp only [ch, lkpg_etaMem hch, lkpg_etaBc hch, lkpg_slot hch t0 u0 hs0, one_mul, zero_mul, lkpg_Om]
    simp
  · rw [h2, k2]
    simp [ch, lkpg_etaMem hch]
  · rw [h3, k3]
    simp [ch, lkpg_etaMem hch]

/-- The program side's frame sum vanishes at the draw. -/
theorem lkpg_ps2 {bytecode : List K} {ρ : ℕ} (hA : Announced bytecode layout ρ) {s0 : ℕ}
    (hs0 : s0 < 2 ^ bytecodeSlotBits) (split : Split) :
    (programSums layout (lkpg_ch layout chunks t0 u0 s0) split).2 = 0 := by
  have hTlen : layout.tables.length = nTables := by rw [(announced_facts hA).2.1, tables_length]
  have hps := programSums_closed layout (lkpg_ch layout chunks t0 u0 s0) split
  dsimp only at hps
  rw [hps]
  dsimp only
  refine sum_eq_zero fun t ht ↦ sum_eq_zero fun s hs ↦ ?_
  have hsl : s + 4 < 2 ^ bytecodeSlotBits := by
    have := mem_range.mp hs
    unfold bytecodeSlotBits at this ⊢
    omega
  rw [(lkpg_weights hch t0 u0 hs0 (hTlen ▸ mem_range.mp ht) hsl).2.2, zero_mul]

/-- **The program side's sum at an instruction `σ` of the program**: per table whose opcode is
`σ`'s, its `omega` weights on the opcode and on `σ`'s operand slots. -/
theorem lkpg_ps1 {bytecode : List K} {ρ : ℕ} (hA : Announced bytecode layout ρ) {s0 : ℕ}
    (hs0 : s0 < 2 ^ bytecodeSlotBits) (hW : layout.logBytecode ≤ chunks.width) {σ : ℕ}
    (hσ : σ < 2 ^ layout.logBytecode) :
    (programSums layout (lkpg_ch layout chunks t0 u0 s0) (linkSplit layout (boolL chunks.width σ))).1 =
      ∑ t ∈ range nTables, if opcodeOf (layout.bytecode.getD (3 * 2 ^ layout.logBytecode + σ) 0) = t then
        lkpg_Om layout s0 t 3 * gpow t + ∑ s ∈ range (2 ^ bytecodeSlotBits - 4),
          lkpg_Om layout s0 t (s + 4) * bcWord layout (s + 4) σ
      else 0 := by
  obtain ⟨hBc, hT, hn, -⟩ := announced_facts hA
  have hTlen : layout.tables.length = nTables := by rw [hT, tables_length]
  have hn' : layout.bytecode.length >>> bytecodeSlotBits = 2 ^ layout.logBytecode := by rw [hBc]; exact hn
  have hsplit : linkSplit layout (boolL chunks.width σ) =
      splitAt layout.bytecode (boolL layout.logBytecode σ) (pcSlots layout.tables) := by
    rw [linkSplit, take_boolL hW, Nat.mod_eq_of_lt hσ]
  have hps := programSums_closed layout (lkpg_ch layout chunks t0 u0 s0) (linkSplit layout (boolL chunks.width σ))
  dsimp only at hps
  rw [hps, hsplit]
  dsimp only
  refine sum_congr rfl fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  have htl : t < layout.tables.length := hTlen ▸ ht'
  have hto : t ≤ opKeccak := by unfold opKeccak; unfold nTables at ht'; omega
  obtain ⟨c1, -, -⟩ := lk_splitAt_bool hn' hσ (pcSlots layout.tables) t 0
  rw [(lkpg_weights hch t0 u0 hs0 htl (by decide : 3 < 2 ^ bytecodeSlotBits)).1, c1]
  by_cases hop : opcodeOf (layout.bytecode.getD (3 * 2 ^ layout.logBytecode + σ) 0) = t
  · rw [ite_eq_left hop, ite_eq_left ⟨hto, hop⟩, mul_one]
    congr 1
    refine sum_congr rfl fun s hs ↦ ?_
    have hsl : s + 4 < 2 ^ bytecodeSlotBits := by
      have := mem_range.mp hs
      unfold bytecodeSlotBits at this ⊢
      omega
    obtain ⟨-, c2, -⟩ := lk_splitAt_bool hn' hσ (pcSlots layout.tables) t (s + 4)
    obtain ⟨w1, w2, -⟩ := lkpg_weights hch t0 u0 hs0 htl hsl
    rw [w1, w2, c2, ite_eq_left ⟨hto, hop, by omega, hsl⟩, zero_mul, add_zero]
    rfl
  · rw [ite_eq_right hop, ite_eq_right (fun h ↦ hop h.2), mul_zero, zero_add]
    refine sum_eq_zero fun s hs ↦ ?_
    have hsl : s + 4 < 2 ^ bytecodeSlotBits := by
      have := mem_range.mp hs
      unfold bytecodeSlotBits at this ⊢
      omega
    obtain ⟨-, c2, -⟩ := lk_splitAt_bool hn' hσ (pcSlots layout.tables) t (s + 4)
    obtain ⟨w1, w2, -⟩ := lkpg_weights hch t0 u0 hs0 htl hsl
    rw [w1, w2, c2, ite_eq_right (fun h ↦ hop h.2.1), mul_zero, zero_mul, add_zero]

end Draw

section Facts

variable {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
include hA

/-- An operand equation's slots are operand slots, its first among them. -/
theorem lkpg_op_slots {t : ℕ} (ht : t < nTables) {op : List ℕ × Form}
    (hop : op ∈ (tableAt layout t).links.bytecodeLink.operands) :
    (∀ s ∈ op.1, 4 ≤ s ∧ s < 2 ^ bytecodeSlotBits) ∧ op.1.headD 0 ∈ op.1 := by
  have htab : tableAt layout t = tables.getD t default := by rw [tableAt, (announced_facts hA).2.1]
  rw [htab] at hop
  obtain ⟨-, h⟩ := lkt_operands t ht
  obtain ⟨hne, -, hs⟩ := h op hop
  refine ⟨hs, ?_⟩
  rcases hl : op.1 with _ | ⟨a, l⟩
  · exact absurd hl hne
  · simp

/-- Below slot `4`, no operand equation's first slot is `s0`. -/
theorem lkpg_ops_zero {t : ℕ} (ht : t < nTables) {s0 : ℕ} (hs0 : s0 < 4) (F : List ℕ × Form → E) :
    ((tableAt layout t).links.bytecodeLink.operands.map fun op ↦
      (if op.1.headD 0 = s0 then (1 : E) else 0) * F op).sum = 0 := by
  refine List.sum_eq_zero fun z hz ↦ ?_
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hz
  obtain ⟨hs, hh⟩ := lkpg_op_slots hA ht hop
  have := (hs _ hh).1
  rw [ite_eq_right (by omega), zero_mul]

/-- Below slot `4`, the draw's `omega` weights are the opcode's alone. -/
theorem lkpg_Om_low {t : ℕ} (ht : t < nTables) {s0 : ℕ} (hs0 : s0 < 4) (i : ℕ) :
    lkpg_Om layout s0 t i = if i = 3 then (if 3 = s0 then 1 else 0) else 0 := by
  rw [lkpg_Om, add_eq_left]
  refine List.sum_eq_zero fun z hz ↦ ?_
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hz
  obtain ⟨hs, hh⟩ := lkpg_op_slots hA ht hop
  have := (hs _ hh).1
  refine List.sum_eq_zero fun y hy ↦ ?_
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hy
  have hne : ¬ op.1.headD 0 = s0 := by omega
  simp only [hne, ↓reduceIte, ite_self]

/-- The draw's `omega` weight on the opcode slot, at an operand equation's first slot `s0 ≥ 4`. -/
theorem lkpg_Om_three {t : ℕ} (ht : t < nTables) {s0 : ℕ} (hs0 : 4 ≤ s0) : lkpg_Om layout s0 t 3 = 0 := by
  rw [lkpg_Om, ite_eq_left rfl, ite_eq_right (by omega), zero_add]
  refine List.sum_eq_zero fun z hz ↦ ?_
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hz
  obtain ⟨hs, -⟩ := lkpg_op_slots hA ht hop
  refine List.sum_eq_zero fun y hy ↦ ?_
  obtain ⟨s, hs', rfl⟩ := List.mem_map.mp hy
  have := (hs s hs').1
  rw [ite_eq_right (by omega)]

/-- The draw's `omega` weights on the operand slots, against `F`: each operand equation whose first
slot is `s0`, on its slots. -/
theorem lkpg_Om_slots {t : ℕ} (ht : t < nTables) (s0 : ℕ) (F : ℕ → E) :
    ∑ s ∈ range (2 ^ bytecodeSlotBits - 4), lkpg_Om layout s0 t (s + 4) * F (s + 4) =
      ((tableAt layout t).links.bytecodeLink.operands.map fun op ↦
        (if op.1.headD 0 = s0 then (1 : E) else 0) * (op.1.map F).sum).sum := by
  set L := (tableAt layout t).links.bytecodeLink.operands
  have e1 : ∀ s ∈ range (2 ^ bytecodeSlotBits - 4), lkpg_Om layout s0 t (s + 4) * F (s + 4) =
      (L.map fun op ↦ (op.1.map fun s' ↦ if s' = s + 4 then
        (if op.1.headD 0 = s0 then (1 : E) else 0) * F (s + 4) else 0).sum).sum := by
    intro s _
    rw [lkpg_Om, ite_eq_right (by omega), zero_add, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun op _ ↦ ?_)
    rw [← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun s' _ ↦ ?_)
    split_ifs <;> simp
  rw [sum_congr rfl e1, sum_list_map_comm]
  refine congrArg List.sum (List.map_congr_left fun op hop ↦ ?_)
  obtain ⟨hs, -⟩ := lkpg_op_slots hA ht hop
  rw [sum_list_map_comm, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun s' hs' ↦ ?_)
  have h4 := hs s' hs'
  rw [sum_eq_single (s' - 4)]
  · rw [ite_eq_left (by omega), Nat.sub_add_cancel h4.1]
  · intro b _ hb
    rw [ite_eq_right (by omega)]
  · intro h
    exact absurd (mem_range.mpr (by unfold bytecodeSlotBits at h4 ⊢; omega)) h

end Facts

/-- **The rest at the draw, in closed form**: slot `s0`'s program equations at row `u0` of table
`t0`, its two sides added. -/
theorem lkpg_G {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hW : layout.logBytecode ≤ chunks.width) (hone : PointersOneHot layout q chunks) {t0 u0 : ℕ}
    (ht0 : t0 < nTables) (hu0 : u0 < tableRowCount layout t0) {s0 : ℕ} (hs0 : s0 < 2 ^ bytecodeSlotBits) :
    lkRest layout chunks q (lkp_set layout chunks (lkpg_vals t0 u0 s0)) =
      (if 1 = s0 then 1 else 0) * (tableValue layout q t0 (tableAt layout t0).links.bytecodeLink.pc u0 +
          gpow (rowBc layout q chunks t0 u0)) +
        (if 2 = s0 then 1 else 0) * (1 + if rowBc layout q chunks t0 u0 < 2 ^ layout.logBytecode then 1 else 0) +
        (if 3 = s0 then 1 else 0) * gpow t0 +
        ((tableAt layout t0).links.bytecodeLink.operands.map fun op ↦
          (if op.1.headD 0 = s0 then (1 : E) else 0) * op.2.evaluate fun c ↦ tableValue layout q t0 c u0).sum +
        (if rowBc layout q chunks t0 u0 < 2 ^ layout.logBytecode then 1 else 0) *
          (programSums layout (lkpg_ch layout chunks t0 u0 s0)
            (linkSplit layout (boolL chunks.width (rowBc layout q chunks t0 u0)))).1 := by
  obtain ⟨-, hT, -⟩ := announced_facts hA
  have hTlen : layout.tables.length = nTables := by rw [hT, tables_length]
  have htab : layout.tables.getD t0 default = tables.getD t0 default := by rw [hT]
  have h2 := two_le_ptrsOf hA ht0
  obtain ⟨hw, hpm⟩ := wordAt_eq hA q ht0 (show 1 < (ptrsOf layout t0).length by omega) u0
  have hptr1 : (ptrsOf layout t0).getD 1 0 = (tableAt layout t0).links.bytecodeLink.pointer := by
    have h := congrArg (fun L : List ℕ ↦ L.getD 1 0) (lkt_pointers t0 ht0).1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take] at h
    rw [ptrsOf_eq hA ht0, tableAt, htab]
    simpa using h
  have hσ : ptrIndex chunks (wordAt layout q t0 1 u0) = rowBc layout q chunks t0 u0 := by
    rw [hw, hptr1]
    rfl
  have hσW : rowBc layout q chunks t0 u0 < 2 ^ chunks.width := by
    rw [← hσ]
    exact ptrIndex_lt hch _ (by rw [hw]; exact hone t0 ht0 u0 hu0 _ hpm)
  have hrows := tableRows_le_height hA ht0
  have hcol : ∀ c, c < (tables.getD t0 default).width ∧ c ∉ (tables.getD t0 default).links.pointers →
      (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0).getD c 0 =
        tableValue layout q t0 c u0 := by
    intro c hc
    exact lkVals_bool layout q (by rw [hTlen]; exact ht0) (lt_of_lt_of_le hu0 hrows) (by rw [htab]; exact hc.1)
      (by rw [ptrsOf_eq hA ht0]; exact hc.2)
  obtain ⟨-, -, hpc, -, hops, -⟩ := lkt_cols t0 ht0
  have hopc : (layout.tables.getD t0 default).links.bytecodeLink.opcode = t0 := by
    rw [htab]
    exact (lkt_opcode t0 ht0).2
  obtain ⟨hx, hp⟩ := lkpg_idx hch t0 u0 hs0 hW hσW q
  have hsum : ((layout.tables.getD t0 default).links.bytecodeLink.operands.map fun op ↦
      (if op.1.headD 0 = s0 then (1 : E) else 0) *
        op.2.evaluate fun c ↦ (lkVals layout (honestValues layout q (boolL (linkRows layout) u0)) t0).getD c 0).sum =
      ((layout.tables.getD t0 default).links.bytecodeLink.operands.map fun op ↦
        (if op.1.headD 0 = s0 then (1 : E) else 0) * op.2.evaluate fun c ↦ tableValue layout q t0 c u0).sum := by
    refine congrArg List.sum (List.map_congr_left fun op hop ↦ ?_)
    rw [form_evaluate_congr op.2 fun c hc ↦ hcol c (hops op (htab ▸ hop) c hc)]
  rw [show tableAt layout t0 = layout.tables.getD t0 default from rfl, lkpg_rest hch t0 u0 s0 hA q ht0 hu0, hσ,
    hx, hp, lkpg_ps2 hch t0 u0 hA hs0]
  simp only [lkRBc, lkpg_slot hch t0 u0 hs0, mul_zero, add_zero]
  rw [hcol _ (by rw [htab]; exact hpc), hopc, hsum]
  ring

/-- **The program case**: if an executed row's program lookup fails, the rest is nonzero at some
draw. -/
theorem lkRest_ne_of_program {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hW : layout.logBytecode ≤ chunks.width) (hone : PointersOneHot layout q chunks)
    (hp : ¬ ProgramHolds layout q chunks) :
    ∃ x : lkp_Vals, lkRest layout chunks q (lkp_set layout chunks x) ≠ 0 := by
  obtain ⟨t0, ht0, u0, hu0, hfail⟩ : ∃ t0 < nTables, ∃ u0 < tableRowCount layout t0,
      ¬ (rowBc layout q chunks t0 u0 < 2 ^ layout.logBytecode ∧
        tableValue layout q t0 (tableAt layout t0).links.bytecodeLink.pc u0 = gpow (rowBc layout q chunks t0 u0) ∧
        opcodeOf (layout.bytecode.getD (3 * 2 ^ layout.logBytecode + rowBc layout q chunks t0 u0) 0) = t0 ∧
        (tableAt layout t0).links.bytecodeLink.opcode = t0 ∧
        ∀ op ∈ (tableAt layout t0).links.bytecodeLink.operands,
          (op.1.map fun s ↦ bcWord layout s (rowBc layout q chunks t0 u0)).sum =
            op.2.evaluate fun c ↦ tableValue layout q t0 c u0) := by
    by_contra hc
    exact hp fun t ht u hu ↦ by_contra fun h ↦ hc ⟨t, ht, u, hu, h⟩
  have htab : tableAt layout t0 = tables.getD t0 default := by rw [tableAt, (announced_facts hA).2.1]
  have hopc : (tableAt layout t0).links.bytecodeLink.opcode = t0 := by
    rw [htab]
    exact (lkt_opcode t0 ht0).2
  have hG := fun {s0 : ℕ} (hs0 : s0 < 2 ^ bytecodeSlotBits) ↦ lkpg_G hA q hch hW hone ht0 hu0 hs0
  by_cases h1 : rowBc layout q chunks t0 u0 < 2 ^ layout.logBytecode
  swap
  · -- a program pointer past the program: slot `2`
    refine ⟨lkpg_vals t0 u0 2, ?_⟩
    rw [hG (by decide), ite_eq_right h1, lkpg_ops_zero hA ht0 (by norm_num)]
    simp
  have hps := fun {s0 : ℕ} (hs0 : s0 < 2 ^ bytecodeSlotBits) ↦ lkpg_ps1 hch t0 u0 hA hs0 hW h1
  by_cases h2 : tableValue layout q t0 (tableAt layout t0).links.bytecodeLink.pc u0 =
    gpow (rowBc layout q chunks t0 u0)
  swap
  · -- the `pc` is not the instruction's: slot `1`
    refine ⟨lkpg_vals t0 u0 1, ?_⟩
    have hz : lkRest layout chunks q (lkp_set layout chunks (lkpg_vals t0 u0 1)) =
        tableValue layout q t0 (tableAt layout t0).links.bytecodeLink.pc u0 + gpow (rowBc layout q chunks t0 u0) := by
      rw [hG (by decide), ite_eq_left h1, lkpg_ops_zero hA ht0 (by norm_num), hps (by decide), sum_ite_eq]
      by_cases hm : opcodeOf (layout.bytecode.getD (3 * 2 ^ layout.logBytecode + rowBc layout q chunks t0 u0) 0) ∈
          range nTables
      · rw [ite_eq_left hm]
        simp only [lkpg_Om_low hA (mem_range.mp hm) (by norm_num : 1 < 4)]
        simp
      · rw [ite_eq_right hm]
        simp
    rw [hz]
    exact fun h ↦ h2 (lkpg_eq_of_add h)
  by_cases h3 : opcodeOf (layout.bytecode.getD (3 * 2 ^ layout.logBytecode + rowBc layout q chunks t0 u0) 0) = t0
  swap
  · -- the instruction's opcode is not the table's: slot `3`
    refine ⟨lkpg_vals t0 u0 3, ?_⟩
    set op := opcodeOf (layout.bytecode.getD (3 * 2 ^ layout.logBytecode + rowBc layout q chunks t0 u0) 0)
    have hz : lkRest layout chunks q (lkp_set layout chunks (lkpg_vals t0 u0 3)) =
        gpow t0 + if op ∈ range nTables then gpow op else 0 := by
      rw [hG (by decide), ite_eq_left h1, lkpg_ops_zero hA ht0 (by norm_num), hps (by decide), sum_ite_eq]
      by_cases hm : op ∈ range nTables
      · rw [ite_eq_left hm, ite_eq_left hm]
        simp only [lkpg_Om_low hA (mem_range.mp hm) (by norm_num : 3 < 4)]
        simp
      · rw [ite_eq_right hm, ite_eq_right hm]
        simp
    rw [hz]
    intro h
    by_cases hm : op ∈ range nTables
    · rw [ite_eq_left hm] at h
      have h6 : nTables = 6 := rfl
      exact h3 (lkpg_gpow_inj (by omega) (by have := mem_range.mp hm; omega) (lkpg_eq_of_add h)).symm
    · rw [ite_eq_right hm, add_zero] at h
      exact lkpg_gpow_ne_zero t0 h
  -- an operand equation fails: its first slot
  obtain ⟨op, hop, hne⟩ : ∃ op ∈ (tableAt layout t0).links.bytecodeLink.operands,
      (op.1.map fun s ↦ bcWord layout s (rowBc layout q chunks t0 u0)).sum ≠
        op.2.evaluate fun c ↦ tableValue layout q t0 c u0 := by
    by_contra hc
    exact hfail ⟨h1, h2, h3, hopc, fun op hop ↦ by_contra fun h ↦ hc ⟨op, hop, h⟩⟩
  obtain ⟨hs, hh⟩ := lkpg_op_slots hA ht0 hop
  have hh4 := (hs _ hh).1
  have hh16 := (hs _ hh).2
  have hnd := (lkt_operands t0 ht0).1
  rw [← htab] at hnd
  refine ⟨lkpg_vals t0 u0 (op.1.headD 0), ?_⟩
  have hz : lkRest layout chunks q (lkp_set layout chunks (lkpg_vals t0 u0 (op.1.headD 0))) =
      op.2.evaluate (fun c ↦ tableValue layout q t0 c u0) +
        (op.1.map fun s ↦ bcWord layout s (rowBc layout q chunks t0 u0)).sum := by
    rw [hG hh16, ite_eq_left h1, hps hh16, sum_ite_eq, h3, ite_eq_left (mem_range.mpr ht0),
      lkpg_Om_three hA ht0 hh4, zero_mul, zero_add,
      lkpg_Om_slots hA ht0 _ (fun s ↦ bcWord layout s (rowBc layout q chunks t0 u0)),
      ite_eq_right (show ¬ 1 = op.1.headD 0 by omega), ite_eq_right (show ¬ 2 = op.1.headD 0 by omega),
      ite_eq_right (show ¬ 3 = op.1.headD 0 by omega),
      lkpg_sum_head (fun o ↦ o.1.headD 0) (fun o ↦ o.2.evaluate fun c ↦ tableValue layout q t0 c u0) _ hnd op hop,
      lkpg_sum_head (fun o ↦ o.1.headD 0)
        (fun o ↦ (o.1.map fun s ↦ bcWord layout s (rowBc layout q chunks t0 u0)).sum) _ hnd op hop]
    ring
  rw [hz]
  exact fun h ↦ hne (lkpg_eq_of_add h).symm

end

end LeanVM.Protocol.Relation

/-- info: 'LeanVM.Protocol.Relation.lkRest_ne_of_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.lkRest_ne_of_program
