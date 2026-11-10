import Rv64Verifier.Model.Layout

/-!
# Every placement `build_layout` returns fits the stack

`buildLayoutRust_within`: a placement's variable count is at most `stack_log`. A committed block's
`2 ^ κ` words lie in the stacked total, whose `log2_ceil` is at most `stack_log`; a column with a
`q_keccak` slot is a `KECCAK` column, its `κ` the table's height, at most `q_keccak`'s, a block.
-/

namespace Rv64Verifier.Model.LayoutMirror
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier

theorem le_log2Ceil {k n : ℕ} (h : 2 ^ k ≤ n) : k ≤ log2Ceil n := by
  unfold log2Ceil bitLength
  split
  · next h0 =>
    have : 2 ^ k ≤ 1 := by omega
    rcases k with _ | k
    · omega
    · have := Nat.one_lt_two_pow (n := k + 1) (by omega); omega
  · next h0 =>
    rcases k with _ | k
    · omega
    · have hk : 2 ^ k ≤ n - 1 := by rw [Nat.pow_succ] at h; have := Nat.one_le_two_pow (n := k); omega
      have := (Nat.le_log2 h0).mpr hk
      omega

theorem stackOffsets_snd (sizes : List ℕ) :
    (stackOffsets sizes).2 = log2Ceil (sizes.map (2 ^ ·)).sum := by
  have h := (stackFold_le (fun i ↦ sizes.getD i 0)
    ((List.range sizes.length).mergeSort fun i j ↦
      decide (sizes.getD j 0 < sizes.getD i 0) ||
        (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j)))
    (List.replicate sizes.length 0) 0 (by simp)).2
  rw [((List.mergeSort_perm _ _).map _).sum_eq, sum_map_range_getD] at h
  simp only [stackOffsets]
  rw [h]
  simp

theorem placementsOf_within (kappas : List ℕ) (hq : qkeccak < kappas.length)
    (h5 : keccakSlot qkeccak = none ∧ qkeccak ∉ keccakOutputColumns)
    (hs : ∀ c < kappas.length, keccakSlot c ≠ none → kappas.getD c 0 ≤ kappas.getD qkeccak 0) :
    ∀ p ∈ (placementsOf kappas).1, ∀ q, p = some q → q.variableCount ≤ (placementsOf kappas).2 := by
  have hB : ∀ c, c < kappas.length → keccakSlot c = none → c ∉ keccakOutputColumns →
      kappas.getD c 0 ≤ (stackOffsets (((List.range kappas.length).filter fun c ↦
        (keccakSlot c).isNone ∧ c ∉ keccakOutputColumns).map (kappas.getD · 0))).2 := by
    intro c hc h1 h2
    rw [stackOffsets_snd]
    apply le_log2Ceil
    apply List.le_sum_of_mem
    rw [List.map_map]
    refine List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨List.mem_range.mpr hc, ?_⟩, rfl⟩
    simp [h1, h2]
  intro p hp q hpq
  unfold placementsOf at hp ⊢
  simp only at hp ⊢
  obtain ⟨⟨kappa, column⟩, hmem, rfl⟩ := List.mem_map.mp hp
  have hget := List.mem_zipIdx_iff_getElem?.mp hmem
  simp only at hget
  have hcl : column < kappas.length := (List.getElem?_eq_some_iff.mp hget).1
  have hk : kappas.getD column 0 = kappa := by
    rw [List.getD_eq_getElem?_getD, hget]; rfl
  simp only at hpq
  split at hpq
  · next slot hslot =>
    simp only [Option.some.injEq] at hpq
    subst hpq
    have := hs column hcl (by rw [hslot]; simp)
    have := hB qkeccak hq h5.1 h5.2
    simp only
    omega
  · next hslot =>
    split at hpq
    · simp at hpq
    · next hout =>
      simp only [Option.some.injEq] at hpq
      subst hpq
      have := hB column hcl hslot hout
      simp only
      omega

/-- The `KECCAK` columns: from its base `73` on, every `κ` the table's height. -/
theorem columnKappas_keccak (lm lb : ℕ) (H : List ℕ) (c : ℕ) (h1 : 73 ≤ c) (h2 : c < 165) :
    (columnKappas lm lb H).getD c 0 = H.getD opKeccak 0 := by
  have hw : tables.map (fun t ↦ (t.width, t.opcode)) =
      [(15, 0), (15, 1), (8, 2), (15, 3), (14, 4), (92, 5)] := by decide +kernel
  have e : tables.flatMap (fun t ↦ List.replicate t.width (H.getD t.opcode 0)) =
      ([(15, 0), (15, 1), (8, 2), (15, 3), (14, 4), (92, 5)] : List (ℕ × ℕ)).flatMap
        fun p ↦ List.replicate p.1 (H.getD p.2 0) := by
    rw [← hw, List.flatMap_map]
  have ho : opKeccak = 5 := rfl
  simp only [columnKappas, e, List.flatMap_cons, List.flatMap_nil, List.append_nil, ho]
  rw [List.getD_eq_getElem?_getD]
  simp only [← List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  rw [List.getElem?_replicate]
  simp only [show c - 73 < 92 by omega, ite_true, Option.getD_some]

theorem keccakSlot_base {c : ℕ} (h : keccakSlot c ≠ none) : 73 ≤ c := by
  have hb : globalColumnBases.getD opKeccak 0 = 73 := by decide +kernel
  unfold keccakSlot at h
  rw [hb] at h
  split at h
  · assumption
  · exact absurd rfl h

/-- **Every placement `build_layout` returns fits the stack.** -/
theorem buildLayoutRust_within {bytecodeLen logMemory : BitVec 64} {tableRows : List (BitVec 64)}
    {l : LayoutRust} (h : buildLayoutRust bytecodeLen logMemory tableRows = some l) :
    ∀ p ∈ l.placements, ∀ q, p = some q → q.variableCount ≤ l.stackLog := by
  unfold buildLayoutRust at h
  split at h
  · simp at h
  · next L _ =>
    split_ifs at h with hc
    obtain ⟨⟨-, h32⟩, hall, -, h36⟩ := hc
    simp only [Option.some.injEq] at h
    subst h
    have hrows' : ∀ r ∈ tableRows, r.toNat ≤ 2 ^ 32 := by
      intro r hr
      have := List.all_eq_true.mp hall r hr
      have h1 : (1#64 <<< maxTableLogRust).toNat = 2 ^ 32 := by decide +kernel
      simpa [BitVec.le_def, h1] using this
    have hH := tableLogHeightsRust_le tableRows hrows'
    have hm : logMemory.toNat ≤ 32 := by simpa [BitVec.le_def] using h32
    simp only
    rw [kappasRust_eq]
    have hK := columnKappas_le logMemory.toNat (L - busBitsRust) _ hm (by
      simp only [busBitsRust] at h36 ⊢; omega) hH
    have hKl := columnKappas_length logMemory.toNat (L - busBitsRust) (tableLogHeightsRust tableRows)
    have hq : (columnKappas logMemory.toNat (L - busBitsRust) (tableLogHeightsRust tableRows)).getD
        qkeccak 0 = (tableLogHeightsRust tableRows).getD opKeccakRust 0 +
          slotBitsRust keccakDepthRust := by
      have hs : slotBitsRust keccakDepthRust = qkeccakSlotBits := by decide +kernel
      rw [hs]
      rfl
    obtain ⟨hpl, hsl, -⟩ := placementsRust_eq _ _ hq hK (by omega)
    intro p hp q hpq
    subst hpq
    have hmem : some q.toSpec ∈ (placementsOf (columnKappas logMemory.toNat (L - busBitsRust)
        (tableLogHeightsRust tableRows))).1 := by
      rw [← hpl]
      exact List.mem_map.mpr ⟨some q, hp, rfl⟩
    have := placementsOf_within _ (by rw [hKl]; decide) (by decide +kernel) (fun c hc hn ↦ by
      rw [hKl] at hc
      rw [columnKappas_keccak _ _ _ c (keccakSlot_base hn) hc, hq]
      exact Nat.le_add_right _ _) _ hmem _ rfl
    rw [hsl]
    exact this

end Rv64Verifier.Model.LayoutMirror
