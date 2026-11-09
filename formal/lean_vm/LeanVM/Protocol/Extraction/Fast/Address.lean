module

public import LeanVM.Protocol.Extraction.Run

/-!
# Address lookups by binary search

The extractor indexes the `2^κ` addresses `g^i` in a `Std.HashMap` from the lane of `g^i` to `i`
(`powIndex`, `gLogIn`). Here the same index is a table of the pairs `(lane of g^i, i)` sorted by
lane (`powTable`), read by binary search (`findLane`): `O(log 2^κ)` comparisons per lookup,
worst-case.

* `findLane_some`, `findLane_complete`: on a table sorted by lane, the search finds a pair with
  the key whenever there is one, and only such pairs;
* `gLogTable_eq`: on at most `2^63` words the lookup is `gLogIn (powIndex κ)` (the lanes of `g^i`,
  `i < 2^κ`, are distinct: `lane_gpow_inj`);
* `stepTable`, `haltLoopTable`, `haltingRunTable`, `candidateExecutionTable`: the halting search
  with the tables, equal to the statement's with `powIndex` (`candidateExecutionTable_eq`).
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol LeanVM.Protocol.Halting
open LeanVM.Extraction LeanVM.Protocol.Compile

public section

/-- The pairs `(lane of g^i, i)` for the `n` indices `i` from `i₀`, where `x = g^i₀`. -/
@[expose] def powPairs : ℕ → ℕ → K → List (ℕ × ℕ)
  | 0, _, _ => []
  | n + 1, i, x => (x.lane.toNat, i) :: powPairs n (i + 1) (x * g)

/-- **The address table** of `2^κ` words: the pairs `(lane of g^i, i)`, `i < 2^κ`, by lane. -/
@[expose] def powTable (κ : ℕ) : Array (ℕ × ℕ) :=
  ((powPairs (2 ^ κ) 0 1).mergeSort fun a b ↦ decide (a.1 ≤ b.1)).toArray

/-- Binary search for `key` among entries `[lo, hi)` of a table sorted by lane. -/
@[expose] def findLane (t : Array (ℕ × ℕ)) (key : ℕ) (lo hi : ℕ) : Option ℕ :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    let e := t.getD mid (0, 0)
    if e.1 = key then some e.2
    else if e.1 < key then findLane t key (mid + 1) hi
    else findLane t key lo mid
  else none
termination_by hi - lo

/-- `gLogIn`, by binary search in a table. -/
@[expose] def gLogTable (t : Array (ℕ × ℕ)) (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  match findLane t a.lane.toNat 0 t.size with
  | some i => if h : i < 2 ^ κ then some ⟨i, h⟩ else none
  | none => none

/-! ## The search -/

/-- A table sorted by lane, as a property of its entries. -/
def SortedLanes (t : Array (ℕ × ℕ)) : Prop :=
  ∀ i j, i ≤ j → j < t.size → (t.getD i (0, 0)).1 ≤ (t.getD j (0, 0)).1

theorem findLane_sound (t : Array (ℕ × ℕ)) (key : ℕ) :
    ∀ (n lo hi : ℕ), hi - lo = n → hi ≤ t.size → ∀ {v : ℕ},
      findLane t key lo hi = some v → (key, v) ∈ t.toList := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lo hi hn hhi v h
  rw [findLane] at h
  dsimp only at h
  by_cases hlt : lo < hi
  · simp only [hlt, ↓reduceDIte] at h
    have hmid : (lo + hi) / 2 < t.size := by omega
    by_cases he : (t.getD ((lo + hi) / 2) (0, 0)).1 = key
    · simp only [he, ↓reduceIte, Option.some.injEq] at h
      subst h
      rw [← he]
      have : t.getD ((lo + hi) / 2) (0, 0) = t[(lo + hi) / 2] := by
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hmid]
      rw [this]
      exact Array.getElem_mem_toList hmid
    · simp only [he, ↓reduceIte] at h
      by_cases hl : (t.getD ((lo + hi) / 2) (0, 0)).1 < key
      · simp only [hl, ↓reduceIte] at h
        exact ih (hi - ((lo + hi) / 2 + 1)) (by omega) ((lo + hi) / 2 + 1) hi rfl hhi h
      · simp only [hl, ↓reduceIte] at h
        exact ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl (by omega) h
  · simp only [hlt, ↓reduceDIte, reduceCtorEq] at h

theorem findLane_complete (t : Array (ℕ × ℕ)) (hs : SortedLanes t) (key : ℕ) :
    ∀ (n lo hi : ℕ), hi - lo = n → hi ≤ t.size → ∀ {idx : ℕ}, lo ≤ idx → idx < hi →
      (t.getD idx (0, 0)).1 = key → (findLane t key lo hi).isSome := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lo hi hn hhi idx h₁ h₂ hk
  rw [findLane]
  dsimp only
  simp only [show lo < hi by omega, ↓reduceDIte]
  by_cases he : (t.getD ((lo + hi) / 2) (0, 0)).1 = key
  · simp only [he, ↓reduceIte, Option.isSome_some]
  · simp only [he, ↓reduceIte]
    by_cases hlt' : (t.getD ((lo + hi) / 2) (0, 0)).1 < key
    · simp only [hlt', ↓reduceIte]
      refine ih (hi - ((lo + hi) / 2 + 1)) (by omega) ((lo + hi) / 2 + 1) hi rfl hhi ?_ h₂ hk
      by_contra hc
      have := hs idx ((lo + hi) / 2) (by omega) (by omega)
      rw [hk] at this
      exact absurd (lt_of_le_of_lt this hlt') (lt_irrefl _)
    · simp only [hlt', ↓reduceIte]
      refine ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl (by omega) h₁ ?_ hk
      by_contra hc
      have hle := hs ((lo + hi) / 2) idx (by omega) (by omega)
      rw [hk] at hle
      exact hlt' (lt_of_le_of_ne hle he)

/-! ## The table -/

theorem mem_powPairs (k : ℕ) (v : ℕ) :
    ∀ (n i : ℕ), (k, v) ∈ powPairs n i (addressOfIndex i) ↔ i ≤ v ∧ v < i + n ∧ k = (addressOfIndex
        v).lane.toNat
  | 0, i => by simp [powPairs]; omega
  | n + 1, i => by
    rw [powPairs, show addressOfIndex i * g = addressOfIndex (i + 1) from (pow_succ g i).symm,
        List.mem_cons,
      mem_powPairs k v n (i + 1), Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨h₁, h₂, h₃⟩)
      · exact ⟨le_rfl, by omega, rfl⟩
      · exact ⟨by omega, by omega, h₃⟩
    · rintro ⟨h₁, h₂, h₃⟩
      rcases h₁.lt_or_eq with h₁ | rfl
      · exact .inr ⟨h₁, by omega, h₃⟩
      · exact .inl ⟨h₃, rfl⟩

theorem mem_powTable (κ : ℕ) (k : ℕ) (v : ℕ) :
    (k, v) ∈ (powTable κ).toList ↔ v < 2 ^ κ ∧ k = (addressOfIndex v).lane.toNat := by
  rw [powTable, List.toList_toArray, List.mem_mergeSort,
    show (1 : K) = addressOfIndex 0 from (pow_zero g).symm, mem_powPairs]
  simp only [Nat.zero_le, true_and, Nat.zero_add]

theorem sortedLanes_powTable (κ : ℕ) : SortedLanes (powTable κ) := by
  set l := (powPairs (2 ^ κ) 0 1).mergeSort fun a b : ℕ × ℕ ↦ decide (a.1 ≤ b.1) with hl
  have hp : l.Pairwise fun a b ↦ decide (a.1 ≤ b.1) = true :=
    List.pairwise_mergeSort (fun a b c h₁ h₂ ↦ by simp only [decide_eq_true_eq] at *; omega)
      (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _
  have hsize : (powTable κ).size = l.length := by simp [powTable, hl]
  have hget : ∀ m (hm : m < l.length), (powTable κ).getD m (0, 0) = l[m] := by
    intro m hm
    simp [powTable, ← hl, Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem hm]
  intro i j hij hj
  rw [hsize] at hj
  rw [hget i (by omega), hget j hj]
  rcases hij.lt_or_eq with hij | rfl
  · simpa using List.pairwise_iff_getElem.1 hp i j (by omega) hj hij
  · exact le_rfl

/-- **The table lookup is the hash-map lookup** on at most `2^63` words. -/
theorem gLogTable_eq {κ : ℕ} (hκ : κ < 64) (a : K) :
    gLogTable (powTable κ) κ a = gLogIn (powIndex κ) κ a := by
  rw [gLogIn_powIndex hκ]
  have hb : 2 ^ κ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [gLogTable]
  by_cases h : ∃ i : Fin (2 ^ κ), a = addressOfIndex i
  · obtain ⟨i, rfl⟩ := h
    rw [(gLog?_spec hκ).mpr rfl]
    have hmem : ((addressOfIndex i.val).lane.toNat, i.val) ∈ (powTable κ).toList :=
      (mem_powTable κ _ _).2 ⟨i.isLt, rfl⟩
    obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hmem
    have hsome := findLane_complete (powTable κ) (sortedLanes_powTable κ) (addressOfIndex i.val).lane.toNat _ 0
      (powTable κ).size rfl le_rfl (idx := idx) (Nat.zero_le _) (by simpa using hidx)
      (by simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hidx),
            ← Array.getElem_toList, hget])
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
    obtain ⟨hvlt, hvl⟩ := (mem_powTable κ _ _).1 (findLane_sound _ _ _ _ _ rfl le_rfl hv)
    have := lane_gpow_inj (by omega) (by omega) (UInt64.toNat_inj.1 hvl)
    subst this
    simp [hv, hvlt]
  · rw [gLog?_eq_none_iff.mpr fun i hi ↦ h ⟨i, hi⟩]
    cases hv : findLane (powTable κ) a.lane.toNat 0 (powTable κ).size with
    | none => rfl
    | some v =>
      obtain ⟨hvlt, hvl⟩ := (mem_powTable κ _ _).1 (findLane_sound _ _ _ _ _ rfl le_rfl hv)
      exact absurd ⟨⟨v, hvlt⟩, K.lane_injective (UInt64.toNat_inj.1 hvl)⟩ h

/-! ## The halting search with the tables -/

/-- `stepIn`, with tables. -/
@[expose] def stepTable (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram) {κ : ℕ}
    (L : MemoryImage κ) (r : Registers K) : Option (Registers K) :=
  (gLogTable codeT prog.logSize r.pc).map prog.instructions >>=
    executeWith (fun a ↦ (gLogTable memT κ a).map L) r

/-- `haltLoop`, with tables. -/
@[expose] def haltLoopTable (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram) {κ : ℕ}
    (L : MemoryImage κ) : ℕ → ℕ → Registers K → Option ℕ
  | 0, n, r => if r = Registers.final prog then some n else none
  | fuel + 1, n, r =>
    if r = Registers.final prog then some n
    else
      match stepTable memT codeT prog L r with
      | none => none
      | some r' => haltLoopTable memT codeT prog L fuel (n + 1) r'

/-- `candidateExecutionIn`, with tables. -/
@[expose] def candidateExecutionTable (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram)
    (input : PublicInput) (layout : Verifier.Layout) {μ : ℕ} (q : Vector K (2 ^ μ)) :
    Option (Execution prog) :=
  ((haltLoopTable memT codeT prog (memoryImage layout q) (stepCap layout) 0
      Registers.initial).map fun n ↦ ⟨layout.logMemory, memoryImage layout q, n⟩).filter
    (boundaryOK input)

theorem stepTable_eq {prog : LeanIsaProgram} {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) (r :
    Registers K) :
    stepTable (powTable κ) (powTable prog.logSize) prog L r =
      stepIn (powIndex κ) (powIndex prog.logSize) prog L r := by
  simp only [stepTable, stepIn, gLogTable_eq hκ, gLogTable_eq (logSize_lt prog)]

theorem haltLoopTable_eq {prog : LeanIsaProgram} {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    ∀ fuel n r, haltLoopTable (powTable κ) (powTable prog.logSize) prog L fuel n r =
      haltLoop (powIndex κ) (powIndex prog.logSize) prog L fuel n r
  | 0, n, r => rfl
  | fuel + 1, n, r => by
    rw [haltLoopTable, haltLoop, stepTable_eq hκ]
    split
    · rfl
    · cases stepIn (powIndex κ) (powIndex prog.logSize) prog L r with
      | none => rfl
      | some r' => exact haltLoopTable_eq hκ L fuel (n + 1) r'

/-- **The halting search with the tables is the statement's**, on at most `2^63` words. -/
theorem candidateExecutionTable_eq {prog : LeanIsaProgram} {input : PublicInput} {layout :
    Verifier.Layout}
    (hκ : layout.logMemory < 64) {μ : ℕ} (q : Vector K (2 ^ μ)) :
    candidateExecutionTable (powTable layout.logMemory) (powTable prog.logSize) prog input layout q =
      candidateExecutionIn (powIndex layout.logMemory) (powIndex prog.logSize) prog input layout q := by
  rw [candidateExecutionTable, candidateExecutionIn, haltingRunIn, haltLoopTable_eq hκ]

/-- **A stack's execution, fast**: through the address tables, built once, on at most `2^63`
words; through the statement's hash maps otherwise. -/
@[expose] def candidateExecutionFast (prog : LeanIsaProgram) (input : PublicInput)
    (layout : Verifier.Layout) : Vector K (2 ^ layout.stackLog) → Option (Execution prog) :=
  if layout.logMemory < 64 then
    let memT := powTable layout.logMemory
    let codeT := powTable prog.logSize
    candidateExecutionTable memT codeT prog input layout
  else
    let memIdx := powIndex layout.logMemory
    let codeIdx := powIndex prog.logSize
    candidateExecutionIn memIdx codeIdx prog input layout

theorem candidateExecutionFast_eq (prog : LeanIsaProgram) (input : PublicInput)
    (layout : Verifier.Layout) :
    candidateExecutionFast prog input layout =
      candidateExecutionIn (powIndex layout.logMemory) (powIndex prog.logSize) prog input layout := by
  rw [candidateExecutionFast]
  split
  · rename_i h
    funext q
    exact candidateExecutionTable_eq h q
  · rfl

end

end LeanVM.Extraction.Fast
