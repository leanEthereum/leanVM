module

public import LeanVM.Cost.AS.Bounds.Tactic
public import LeanVM.Cost.AS.Top
import all LeanVM.Protocol.Extraction.AS.Lite
import all Statement.Verifier.Layout
import all Statement.Verifier.Multilinear
import all Statement.LeanIsa

/-!
# The announced sizes' facts

What the finish's prices assume of the lite layout the announced sizes decode to, proved for
every layout `buildLayoutLite` returns (`LayoutFacts`): memory and bytecode of log-size at most
`30`, six tables of at most `2^30` rows and log-height at most `30`, every placement's offset
below `2^48` (`stackOffsets_le`: blocks of log-size at most `s` sit at offsets at most `2^s·n`).
**`decSizesL_facts`**: a decoded layout meets them, its rate is `1` to `4` and its stack's
log-size within the verifier's range.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Parameters LeanVM.Protocol
open LeanVM.Protocol.Verifier LeanVM.Extraction.AS LeanVM.Protocol.EndToEnd.Sound

public section

/-- What the finish's prices assume of a lite layout. -/
structure LayoutFacts (L : LayoutLite) : Prop where
  logMemory_le : L.logMemory ≤ 30
  logBytecode_le : L.logBytecode ≤ 30
  heights_length : L.tableLogHeights.length = 6
  heights_le : ∀ h ∈ L.tableLogHeights, h ≤ 30
  rows_length : L.tableRows.length = 6
  rows_le : ∀ r ∈ L.tableRows, r ≤ 2 ^ 30
  index_lt : ∀ o ∈ L.placements, ∀ p : Placement, o = some p → p.index < 2 ^ 48

/-- A layout with the facts and a stack of at most `2^30` is admissible. -/
theorem LayoutFacts.layOk {L : LayoutLite} (h : LayoutFacts L) (hs : L.stackLog ≤ 30) : LayOk L :=
  ⟨hs, h.logMemory_le, h.logBytecode_le, h.heights_length.le, h.heights_le, h.rows_length.le,
    h.rows_le⟩

/-! ## The offsets -/

/-- `stackOffsets`' fold: each offset at most the running total, the total grown by at most `2^s`
per block. -/
theorem offsetsFold_le (sizes : List ℕ) (s : ℕ) (hs : ∀ i, sizes.getD i 0 ≤ s) :
    ∀ (order : List ℕ) (acc : List ℕ × ℕ), (∀ x ∈ acc.1, x ≤ acc.2) →
      (∀ x ∈ (order.foldl (fun (acc : List ℕ × ℕ) i ↦
          (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0)) acc).1,
        x ≤ (order.foldl (fun (acc : List ℕ × ℕ) i ↦
          (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0)) acc).2) ∧
      (order.foldl (fun (acc : List ℕ × ℕ) i ↦
          (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0)) acc).2 ≤ acc.2 + 2 ^ s * order.length := by
  intro order
  induction order with
  | nil => intro acc h; exact ⟨h, by simp⟩
  | cons i order ih =>
    intro acc h
    have hp : 2 ^ sizes.getD i 0 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (hs i)
    have hp0 : 0 < 2 ^ sizes.getD i 0 := Nat.two_pow_pos _
    obtain ⟨h1, h2⟩ := ih (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0) (fun x hx ↦ by
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · have := h x hx; dsimp only; omega
      · dsimp only; omega)
    refine ⟨h1, ?_⟩
    simp only [List.foldl_cons, List.length_cons, Nat.mul_succ] at h2 ⊢
    omega

/-- **The stack's offsets**: blocks of log-size at most `s`: every offset at most `2^s·n`. -/
theorem stackOffsets_le (sizes : List ℕ) (s : ℕ) (hs : ∀ x ∈ sizes, x ≤ s) :
    ∀ x ∈ (stackOffsets sizes).1, x ≤ 2 ^ s * sizes.length := by
  have hs' : ∀ i, sizes.getD i 0 ≤ s := fun i ↦ by
    rcases getD_mem_or sizes i 0 with h | h
    · exact hs _ h
    · rw [h]; omega
  unfold stackOffsets
  dsimp only
  intro x hx
  obtain ⟨h1, h2⟩ := offsetsFold_le sizes s hs' ((List.range sizes.length).mergeSort fun i j ↦
      decide (sizes.getD j 0 < sizes.getD i 0) ||
        (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j)))
    (List.replicate sizes.length 0, 0) (fun y hy ↦ by simp [List.eq_of_mem_replicate hy])
  have := h1 x hx
  simp only [List.length_mergeSort, List.length_range, Nat.zero_add] at h2
  omega

theorem lookup_snd_mem : ∀ (l : List (ℕ × ℕ)) (a b : ℕ), l.lookup a = some b → b ∈ l.map Prod.snd
  | [], _, _, h => by simp [List.lookup] at h
  | (k, v) :: l, a, b, h => by
    simp only [List.lookup] at h
    simp only [List.map_cons, List.mem_cons]
    split at h
    · cases h; exact Or.inl rfl
    · exact Or.inr (lookup_snd_mem l a b h)

/-- The stack's offsets at columns of log-size at most `40`: below `52·2^40`. -/
theorem stack_offsets_le (kappas : List ℕ) (hk : ∀ x ∈ kappas, x ≤ 40) (c b : ℕ)
    (h : (stack kappas).1.lookup c = some b) : b ≤ 2 ^ 40 * 52 := by
  rw [stackLit] at h
  unfold stackOfColumns at h
  dsimp only at h
  have hb := lookup_snd_mem _ c b h
  obtain ⟨⟨c', y⟩, hm, rfl⟩ := List.mem_map.1 hb
  have hy := (List.of_mem_zip hm).2
  have hl : (stackColumns.map fun c ↦ kappas.getD c 0).length = 52 := by
    simp [stackColumns]
  have := stackOffsets_le _ 40 (fun x hx ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    rcases getD_mem_or kappas i 0 with h | h
    · exact hk _ h
    · rw [h]; omega) y hy
  rw [hl] at this
  exact this

/-! ## The layouts -/

theorem mem_zipWith_le {f : ℕ → ℕ → ℕ} {M : ℕ} :
    ∀ (as bs : List ℕ), (∀ a ∈ as, ∀ b ∈ bs, f a b ≤ M) → ∀ x ∈ List.zipWith f as bs, x ≤ M
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], _, x, hx => by simp at hx
  | a :: as, b :: bs, h, x, hx => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h a List.mem_cons_self b List.mem_cons_self
    · exact mem_zipWith_le as bs (fun a ha b hb ↦ h a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb)) x hx

theorem log2Ceil_le {v : ℕ} (h : v ≤ 2 ^ 30) : log2Ceil v ≤ 30 := by
  unfold log2Ceil bitLength
  split_ifs with h0
  · omega
  · have := (Nat.log2_lt h0).2 (show v - 1 < 2 ^ 30 by omega)
    omega

theorem columnKappasL_le (lm : ℕ) (hs : List ℕ) (hm : lm ≤ 30) (hh : ∀ h ∈ hs, h ≤ 30) :
    ∀ x ∈ columnKappasL lm hs, x ≤ 40 := by
  have hg : ∀ i, hs.getD i 0 ≤ 30 := fun i ↦ by
    rcases getD_mem_or hs i 0 with h | h
    · exact hh _ h
    · rw [h]; omega
  have hq : qkeccakSlotBits = 6 := by decide
  intro x hx
  unfold columnKappasL at hx
  simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_nil_iff, or_false] at hx
  rcases hx with (rfl | rfl | rfl) | ⟨t, -, hx⟩
  · omega
  · omega
  · have := hg opKeccak; omega
  · rw [List.eq_of_mem_replicate hx]; have := hg t; omega

theorem qkeccakSlot_lt {c s : ℕ} (h : qkeccakSlot c = some s) : s < 64 := by
  unfold qkeccakSlot at h
  have h1 : qkeccakSlots = 50 := by decide
  have h2 : qkeccakSpare = 14 := by decide
  have h3 : keccakIn = 8 := rfl
  have h4 : keccakOut = 33 := rfl
  dsimp only at h
  rcases hf : List.find? (fun x ↦ decide (spareLocal x = c - globalColumnBases.getD opKeccak 0))
    (List.range qkeccakSpare) with _ | k
  · simp only [hf] at h
    split_ifs at h
    cases h
    omega
  · simp only [hf] at h
    have := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    split_ifs at h
    cases h
    omega

/-- **`buildLayoutLite`'s layouts** meet `LayoutFacts`. -/
theorem buildLayoutLite_facts {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ}
    {L : LayoutLite} (h : buildLayoutLite bytecode logMemory tableRows = some L) :
    LayoutFacts L := by
  unfold buildLayoutLite at h
  split at h
  · cases h
  · rename_i logLength _
    split_ifs at h with hc
    obtain ⟨-, h2, h3, -, h5, h6⟩ := hc
    dsimp only at h
    have e1 : maxLogMemory = 30 := rfl
    have e2 : Verifier.maxLogBytecode = 30 := rfl
    have e3 : bytecodeSlotBits = 4 := rfl
    have e4 : maxTableLog = 30 := rfl
    have e5 : nTables = 6 := rfl
    have hrows : ∀ r ∈ tableRows, r ≤ 2 ^ 30 := fun r hr ↦ by
      have := List.all_eq_true.1 h3 r hr
      rw [e4] at this
      simpa using this
    have hheights : ∀ x ∈ List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
        tableLogFloors, x ≤ 30 :=
      mem_zipWith_le _ _ fun a ha b hb ↦ by
        have := log2Ceil_le (hrows a ha)
        have : b ≤ 9 := by
          simp only [tableLogFloors, keccakMinStepsLog, List.mem_cons, List.mem_nil_iff,
            or_false] at hb
          omega
        omega
    generalize hH : List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
      tableLogFloors = H at h hheights
    have hHl : H.length = 6 := by
      rw [← hH, List.length_zipWith, h6, e5]; rfl
    have hk := columnKappasL_le logMemory H (by omega) hheights
    generalize columnKappasL logMemory H = kappas at h hk
    have hoff := stack_offsets_le kappas hk
    generalize stack kappas = st at h hoff
    obtain ⟨offsets, stackLog⟩ := st
    dsimp only at h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨by dsimp only; omega, by dsimp only; omega, hHl, hheights, by dsimp only; omega,
      hrows, ?_⟩
    intro o ho p hp
    obtain ⟨⟨kappa, column⟩, hm, rfl⟩ := List.mem_map.1 ho
    have hkap : kappa ≤ 40 := hk _ (List.fst_mem_of_mem_zipIdx hm)
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hp
    dsimp only at hi ⊢
    generalize hq : qkeccakSlot column = q at hi
    cases q with
    | some slot =>
      have hs := qkeccakSlot_lt hq
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hi
      have := hoff qkeccak b hb
      have h1 : slot <<< kappa ≤ 63 * 2 ^ 40 := by
        rw [Nat.shiftLeft_eq]
        exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hkap)
      omega
    | none =>
      have := hoff column i hi
      omega

/-- **The announced sizes' facts**: a decoded layout meets `LayoutFacts`, its rate is `1` to `4`
and its stack's log-size within the verifier's range. -/
theorem decSizesL_facts {bytecode : List K} {h : List EvP} {lay : LayoutLite} {ρ : ℕ}
    (hd : decSizesL bytecode h = some (lay, ρ)) :
    LayoutFacts lay ∧ 1 ≤ ρ ∧ ρ ≤ 4 ∧ Whir.minLogStack ≤ lay.stackLog ∧
      lay.stackLog ≤ Whir.maxLogStack := by
  unfold decSizesL at hd
  obtain ⟨ann, -, hd⟩ := Option.bind_eq_some_iff.mp hd
  unfold sizesOfL at hd
  dsimp only at hd
  split_ifs at hd with h1 h2
  obtain ⟨L, hL, hd⟩ := Option.bind_eq_some_iff.mp hd
  split_ifs at hd with h3
  rw [Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨rfl, rfl⟩ := hd
  exact ⟨buildLayoutLite_facts hL, h2.1, h2.2, h3.1, h3.2⟩

end

end LeanVM.Cost.Bounds.AS
