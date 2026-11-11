module

public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Extractor.Replay
import all Statement.LeanVmVerifier
import all Statement.Field
import all LeanVM.Protocol.Extraction.Fast.AfterRoot

/-!
# Bounds: the verifier's replay up to the stack's root

`afterRootLite bytecode π` (`Cost/Extractor/Replay.lean`) reads eight scalars, builds the
layout's fields the extractor reads (`165` columns: their log-sizes, their placements on the
stack, sorted by size) and reads the stack's root at the ladder's first level. Its price depends on
the proof only through those ten scalars, and on the bytecode only through its length:

* **`afterRootLite_cost`**: at most `8·|bytecode| + 977131026` (`≈ 2^29.87` plus `8` per bytecode
  word), for a bytecode of fewer than `2^63` words;
* `readSizesLite_cost`: `8·|bytecode| + 977124630`; `buildLayoutLite_cost`:
  `8·|bytecode| + 977122709`; `placementsOf_cost`: `977100324` for at most `200` columns of
  log-size at most `40` (`stackOffsets_cost`: `973716067`, its quadratic merge sort of the blocks
  (run twice) dominating, each comparison reading the sizes by `getD`); `commitStackPure_cost`:
  `11·|roots| + 6312` (`ladder_cost`: `6000`; `commitPure_cost`: `11·|roots| + 290`);
  `readPure_cost`: `148` per scalar; `absorbPure_cost`: `94`; `keccakSlot_cost`: `2522`;
  `log2Strict_cost`: `789`; `bitLength_cost`: `771`.
* The list functions compiled only here, on word-sized lengths (`W = 2^64`): `elem_cost`,
  `set_cost`, `findIdxGo_cost`, `findIdxOptGo_cost`; `listFoldl_le'` (a fold with an invariant of
  the accumulator and the elements left). The others are `Bounds/ListLib.lean`'s.

The functions compiled on demand are named by the program's indices (`Auto.List.length.c128`,
…): when the chain of compiled modules before `Cost/Extractor/Replay.lean` changes, those names
change, and this file's references with them (a renaming, the proofs unchanged).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-! ## Lists -/

section Lists

variable {α : Type} [MachineEncoding α]

theorem elem_cost (hP : Includes P Auto.List.elem.c340.costDeps) (a : ℕ) (ha : a < 2 ^ 64) :
    ∀ l : List ℕ, (∀ b ∈ l, b < 2 ^ 64) →
      machineCost P Auto.List.elem.c340.costIdx [encodeValue a, encodeValue l] ≤ 11 * l.length + 3
  | [], _ => by rw [Auto.List.elem.c340.costEq_nil P hP]; omega
  | b :: l, hb => by
    rw [Auto.List.elem.c340.costEq_cons P hP, limbs_of_lt ha, limbs_of_lt (hb b (by simp))]
    have := elem_cost hP a ha l fun c hc ↦ hb c (by simp [hc])
    simp only [List.length_cons]
    cases a == b <;> dsimp only <;> omega

theorem set_cost (hP : Includes P Auto.List.set.c337.costDeps) (a : α) :
    ∀ (l : List α) (n : ℕ), n < 2 ^ 64 →
      machineCost P Auto.List.set.c337.costIdx [encodeValue l, encodeValue n, encodeValue a] ≤ 20 * l.length + 3
  | [], n, _ => by rw [Auto.List.set.c337.costEq_nil P hP]; omega
  | x :: l, 0, _ => by
    rw [Auto.List.set.c337.costEq_cons P hP]
    simp only [limbs_zero, List.length_cons, Nat.rec_zero]
    omega
  | x :: l, n + 1, h => by
    rw [Auto.List.set.c337.costEq_cons P hP, limbs_of_lt h]
    have := set_cost hP a l n (by omega)
    simp only [List.length_cons]
    omega

theorem findIdxGo_cost (hP : Includes P Auto.List.findIdx.go.c344.costDeps) (p : α → Bool)
    (pVal : MachineValue) (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : ℕ) :
    ∀ (l : List α) (n : ℕ), n + l.length < 2 ^ 64 → (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B) →
      machineCost P Auto.List.findIdx.go.c344.costIdx [pVal, encodeValue l, encodeValue n] ≤
        (B + 14) * l.length + 3
  | [], n, _, _ => by rw [Auto.List.findIdx.go.c344.costEq_nil P hP p pVal hp]; omega
  | x :: l, n, h, hB => by
    rw [Auto.List.findIdx.go.c344.costEq_cons P hP p pVal hp, limbs_of_lt (by simp at h; omega : n < 2 ^ 64),
      limbs_of_lt (by simp at h; omega : n + 1 < 2 ^ 64), max_self]
    have h1 := findIdxGo_cost hP p pVal hp B l (n + 1) (by simp at h; omega)
      fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons]
    split <;> nlinarith

theorem findIdxOptGo_cost (hP : Includes P Auto.List.findIdx?.go.c332.costDeps) (p : α → Bool)
    (pVal : MachineValue) (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : ℕ) :
    ∀ (l : List α) (n : ℕ), n + l.length < 2 ^ 64 → (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B) →
      machineCost P Auto.List.findIdx?.go.c332.costIdx [pVal, encodeValue l, encodeValue n] ≤
        (B + 14) * l.length + 3
  | [], n, _, _ => by rw [Auto.List.findIdx?.go.c332.costEq_nil P hP p pVal hp]; omega
  | x :: l, n, h, hB => by
    rw [Auto.List.findIdx?.go.c332.costEq_cons P hP p pVal hp, limbs_of_lt (by simp at h; omega : n < 2 ^ 64),
      limbs_of_lt (by simp at h; omega : n + 1 < 2 ^ 64), max_self]
    have h1 := findIdxOptGo_cost hP p pVal hp B l (n + 1) (by simp at h; omega)
      fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons]
    split <;> nlinarith

end Lists

/-! ## The sponge, the reads and the root -/

open LeanVM.Protocol.Compile in
theorem absorbPure_pending_le (sp : Sponge) (x : E) (tag : ℕ) (h : sp.pending.length ≤ 4) :
    (absorbPure sp x tag).pending.length ≤ 4 := by
  unfold absorbPure
  dsimp only
  split
  · simp
  · simp only [List.length_append, List.length_cons, List.length_nil]
    simp only [rateScalars] at *
    omega

open LeanVM.Protocol.Compile in
/-- Absorbing a scalar into a queue of at most four: at most `94`. -/
theorem absorbPure_cost (hP : Includes P absorbPureC.costDeps) (sp : Sponge) (x : E) (tag : ℕ)
    (h : sp.pending.length ≤ 4) :
    machineCost P absorbPureC.costIdx [encodeValue sp, encodeValue x, encodeValue tag] ≤ 94 := by
  rw [absorbPureC.costEq P hP]
  have h1 := length_cost P (by includes) sp.pending (by omega)
  have hlen : (if sp.pending.length = rateScalars then ({ state := default, pending := [] } : Sponge)
      else sp).pending.length ≤ 4 := by split <;> simp_all
  have h2 := append_cost P (by includes)
    (if sp.pending.length = rateScalars then ({ state := default, pending := [] } : Sponge)
      else sp).pending [(x, tag)]
  rw [limbs_of_lt (by omega : sp.pending.length < 2 ^ 64)]
  simp only [rateScalars, limbs_of_lt (by norm_num : (4 : ℕ) < 2 ^ 64), max_self] at h2 hlen ⊢
  by_cases hc : sp.pending.length = 4
  · simp only [hc, ↓reduceIte, List.length_nil] at h2 hlen ⊢
    omega
  · simp only [hc, ↓reduceIte] at h2 hlen ⊢
    omega

open LeanVM.Protocol.Compile in
/-- Reading `n` scalars: at most `148` per scalar. -/
theorem readPure_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.readPure.c323.costDeps) :
    ∀ (n : ℕ) (s : VerifierProgramState), n < 2 ^ 64 → s.sponge.pending.length ≤ 4 →
      machineCost P Auto.LeanVM.Extraction.Fast.readPure.c323.costIdx [encodeValue n, encodeValue s] ≤ 148 * n + 11
  | 0, s, _, _ => by rw [Auto.LeanVM.Extraction.Fast.readPure.c323.costEq_zero P hP]
  | n + 1, s, hn, hs => by
    rw [Auto.LeanVM.Extraction.Fast.readPure.c323.costEq_succ P hP, limbs_of_lt hn]
    obtain ⟨sp, stream, os, roots⟩ := s
    cases stream with
    | nil => simp only; omega
    | cons x xs =>
      simp only at hs ⊢
      have ha := absorbPure_cost P (by includes) sp x dsObserve hs
      have hr := readPure_cost hP n ⟨absorbPure sp x dsObserve, xs, os, roots⟩ (by omega)
        (absorbPure_pending_le sp x dsObserve hs)
      have hm : machineCost P Auto.Option.map.c194.costIdx [MachineValue.closure readPureC.lam0.costIdx [encodeValue x],
          encodeValue (readPure n ⟨absorbPure sp x dsObserve, xs, os, roots⟩)] ≤ 20 := by
        rw [Auto.Option.map.c194.costEq P (by includes) _ _
          (fun r ↦ RunsApp.of_spec (readPureC.lam0.costSpec P (by includes) x r))]
        cases readPure n ⟨absorbPure sp x dsObserve, xs, os, roots⟩ with
        | none => simp
        | some r => simp only [appCost_fn, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
            readPureC.lam0.costEq P (by includes)]; omega
      omega

theorem digestOfScalars_cost (hP : Includes P digestOfScalarsC.costDeps) (s : E × E) :
    machineCost P digestOfScalarsC.costIdx [encodeValue s] ≤ 44 := by
  rw [digestOfScalarsC.costEq P hP]
  split_ifs <;> omega

open LeanVM.Protocol.Compile in
/-- Reading the root: at most `11·|roots| + 290`. -/
theorem commitPure_cost (hP : Includes P commitPureC.costDeps) (height width : ℕ) (s :
    VerifierProgramState)
    (hs : s.sponge.pending.length ≤ 4) :
    machineCost P commitPureC.costIdx [encodeValue height, encodeValue width, encodeValue s] ≤ 11 * s.roots.length + 290 := by
  rw [commitPureC.costEq P hP]
  obtain ⟨sp, stream, os, roots⟩ := s
  simp only at hs ⊢
  rcases stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
  · simp
  · simp
  · simp only
    have hd := digestOfScalars_cost P (by includes) (x0, x1)
    cases LeanVM.Protocol.KeccakHash.digestFromHalves (x0, x1) with
    | none => simp only; omega
    | some root =>
      simp only
      have h1 := absorbPure_cost P (by includes) sp x0 dsObserve hs
      have h2 := absorbPure_cost P (by includes) (absorbPure sp x0 dsObserve) x1 dsObserve
        (absorbPure_pending_le sp x0 dsObserve hs)
      have h3 := append_cost P (by includes) roots [(root, height, width)]
      omega

/-! ## The ladder -/

open LeanVM.Parameters.Whir in
theorem length_levelsFrom : ∀ (fuel rem pf pr red : ℕ), (levelsFrom fuel rem pf pr red).length ≤ fuel
  | 0, _, _, _, _ => by simp [levelsFrom]
  | fuel + 1, rem, pf, pr, red => by
    rw [levelsFrom]
    split
    · simp
    · have := length_levelsFrom fuel (rem - min subsequentFold rem) (min subsequentFold rem)
        (pr + pf - red) subsequentReduction
      simp only [List.length_cons]
      omega

open LeanVM.Parameters.Whir in
/-- The ladder's levels after the first: at most `44` per level. -/
theorem levelsFrom_cost (hP : Includes P Auto.LeanVM.Parameters.Whir.levelsFrom.c349.costDeps) :
    ∀ (fuel rem pf pr red : ℕ), fuel < 2 ^ 64 → rem < 2 ^ 64 → pr + pf + 4 * fuel < 2 ^ 63 →
      red < 2 ^ 64 →
      machineCost P Auto.LeanVM.Parameters.Whir.levelsFrom.c349.costIdx [encodeValue fuel, encodeValue rem, encodeValue pf, encodeValue pr, encodeValue red] ≤
        44 * fuel + 15
  | 0, rem, pf, pr, red, _, _, _, _ => by rw [Auto.LeanVM.Parameters.Whir.levelsFrom.c349.costEq_zero P hP]; omega
  | fuel + 1, rem, pf, pr, red, hf, hr, hpp, hred => by
    rw [Auto.LeanVM.Parameters.Whir.levelsFrom.c349.costEq_succ P hP]
    have hrec := levelsFrom_cost hP fuel (rem - min subsequentFold rem) (min subsequentFold rem)
      (pr + pf - red) subsequentReduction (by omega) (by omega)
      (by simp only [subsequentFold]; omega) (by simp [subsequentReduction])
    simp only [residualMaxLog, subsequentFold, subsequentReduction] at hrec ⊢
    rw [limbs_of_lt hf, limbs_of_lt hr, limbs_of_lt (by omega : pr < 2 ^ 64),
      limbs_of_lt (by omega : pf < 2 ^ 64), limbs_of_lt (by omega : pr + pf < 2 ^ 64),
      limbs_of_lt hred, limbs_of_lt (by omega : min 4 rem < 2 ^ 64),
      limbs_of_lt (by norm_num : (5 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (4 : ℕ) < 2 ^ 64)]
    simp only [max_self]
    by_cases h5 : rem ≤ 5
    · simp only [h5, ↓reduceIte]; omega
    · simp only [h5, ↓reduceIte, show 4 ≤ rem by omega]
      omega

open LeanVM.Parameters.Whir in
theorem shape_cost (hP : Includes P shapeC.costDeps) (μ R : ℕ) (hμ : μ ≤ 64) (hR : R ≤ 2 ^ 32) :
    machineCost P shapeC.costIdx [encodeValue μ, encodeValue R] ≤ 44 * μ + 31 := by
  rw [shapeC.costEq P hP]
  have := levelsFrom_cost P (by includes) μ (μ - initialFold) initialFold R initialReduction
    (by omega) (by omega) (by simp only [initialFold]; omega) (by simp [initialReduction])
  rw [limbs_of_lt (by omega : μ < 2 ^ 64), limbs_of_lt (by simp [initialFold])]
  omega

open LeanVM.Parameters.Whir in
theorem queryTable_rows : ∀ r ∈ queryTable, r.length = 17 ∧ ∀ q ∈ r, q.length ≤ 7 := by
  decide +kernel

open LeanVM.Parameters.Whir in
theorem foldGrindingTable_rows : ∀ r ∈ foldGrindingTable, r.length = 17 ∧ ∀ q ∈ r, q.length ≤ 7 := by
  decide +kernel

theorem getD_mem_or {β : Type} (l : List β) (i : ℕ) (d : β) : l.getD i d ∈ l ∨ l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact Or.inr rfl
  | some r => exact Or.inl (List.mem_of_getElem? h)

/-- A table's row has at most `n` entries, each of at most `m`. -/
theorem table_row_length {t : List (List (List ℕ))} {n m : ℕ}
    (ht : ∀ r ∈ t, r.length = n ∧ ∀ q ∈ r, q.length ≤ m) (i : ℕ) : (t.getD i []).length ≤ n := by
  rcases getD_mem_or t i [] with h | h
  · exact le_of_eq (ht _ h).1
  · rw [h]; simp

theorem table_entry_length {t : List (List (List ℕ))} {n m : ℕ}
    (ht : ∀ r ∈ t, r.length = n ∧ ∀ q ∈ r, q.length ≤ m) (i j : ℕ) :
    ((t.getD i []).getD j []).length ≤ m := by
  rcases getD_mem_or (t.getD i []) j [] with h | h
  · rcases getD_mem_or t i [] with h' | h'
    · exact (ht _ h').2 _ h
    · rw [h'] at h; simp at h
  · rw [h]; simp

open LeanVM.Parameters.Whir in
theorem queryTable_row_length (i : ℕ) : (queryTable.getD i []).length ≤ 17 :=
  table_row_length queryTable_rows i

open LeanVM.Parameters.Whir in
theorem queryTable_queries_length (i j : ℕ) : ((queryTable.getD i []).getD j []).length ≤ 7 :=
  table_entry_length queryTable_rows i j

/-- **`List.zipWith3`** (`zipWith3.c353`): the closure's price and `25` per element of the first
list, `11` at the end. -/
theorem zipWith3_cost (hP : Includes P Auto.List.zipWith3.c353.costDeps) {α β γ δ : Type}
    [MachineEncoding α] [MachineEncoding β] [MachineEncoding γ] [MachineEncoding δ]
    (f : α → β → γ → δ) (fVal : MachineValue)
    (hf : ∀ a b c, RunsApp P fVal [encodeValue a, encodeValue b, encodeValue c] (encodeValue (f a b c)))
    (B : ℕ) (hB : ∀ (a : α) (b : β) (c : γ), appCost P fVal [encodeValue a, encodeValue b, encodeValue c] ≤ B) :
    ∀ (xs : List α) (ys : List β) (zs : List γ),
      machineCost P Auto.List.zipWith3.c353.costIdx [fVal, encodeValue xs, encodeValue ys, encodeValue zs] ≤
        (B + 25) * xs.length + 11 := by
  intro xs
  induction xs with
  | nil => intro ys zs; rw [Auto.List.zipWith3.c353.costEq_nil P hP f fVal hf]; omega
  | cons a xs ih =>
    intro ys zs
    rw [Auto.List.zipWith3.c353.costEq_cons P hP f fVal hf]
    cases ys with
    | nil => simp only [List.length_cons]; nlinarith
    | cons b ys =>
      cases zs with
      | nil => simp only [List.length_cons]; nlinarith
      | cons c zs =>
        have h1 := ih ys zs
        have h2 := hB a b c
        simp only [List.length_cons]
        nlinarith

open LeanVM.Parameters.Whir in
/-- The ladder of a shape: at most `6000`. -/
theorem ladder_cost (hP : Includes P ladderC.costDeps) (μ R : ℕ) (hμ : μ < 2 ^ 64)
    (hR : R < 2 ^ 64) : machineCost P ladderC.costIdx [encodeValue μ, encodeValue R] ≤ 6000 := by
  rw [ladderC.costEq P hP]
  simp only [minLogStack, maxLogStack, Admissible,
    limbs_of_lt hμ, limbs_of_lt hR, limbs_of_lt (by norm_num : (16 : ℕ) < 2 ^ 64),
    limbs_of_lt (by norm_num : (32 : ℕ) < 2 ^ 64), max_self]
  by_cases hadm : 16 ≤ μ ∧ μ ≤ 32 ∧ 1 ≤ R ∧ R ≤ 4
  · obtain ⟨h1, h2, h3, h4⟩ := hadm
    have hs := shape_cost P (by includes) μ R (by omega) (by omega)
    rw [queryTableC.costEq P (by includes),
      Auto.LeanVM.Parameters.Whir.foldGrindingTable.c352.costEq P (by includes)]
    have hg1 := getD_cost P (by includes) queryTable (R - 1) [] (by omega)
    have hg2 := getD_cost P (by includes) (queryTable.getD (R - 1) []) (μ - 16) [] (by omega)
    have hg3 := getD_cost P (by includes) foldGrindingTable (R - 1) [] (by omega)
    have hg4 := getD_cost P (by includes) (foldGrindingTable.getD (R - 1) []) (μ - 16) [] (by omega)
    have hsl : (ladderShape μ R).length ≤ 7 := by
      have key : ∀ μ < 33, ∀ R < 5, (ladderShape μ R).length ≤ 7 := by decide
      exact key μ (by omega) R (by omega)
    have hl1 := length_cost P (by includes) (ladderShape μ R) (by omega)
    have hqq := queryTable_queries_length (R - 1) (μ - 16)
    have hgg := table_entry_length foldGrindingTable_rows (R - 1) (μ - 16)
    have hl2 := length_cost P (by includes) ((queryTable.getD (R - 1) []).getD (μ - 16) []) (by omega)
    have hl3 := length_cost P (by includes) ((foldGrindingTable.getD (R - 1) []).getD (μ - 16) [])
      (by omega)
    have hqt : queryTable.length = 4 := by decide +kernel
    have hgt : foldGrindingTable.length = 4 := by decide +kernel
    have hrow := queryTable_row_length (R - 1)
    have hrow' := table_row_length foldGrindingTable_rows (R - 1)
    rw [hqt] at hg1
    rw [hgt] at hg3
    rw [limbs_of_lt (by omega : (ladderShape μ R).length < 2 ^ 64),
      limbs_of_lt (by omega : ((queryTable.getD (R - 1) []).getD (μ - 16) []).length < 2 ^ 64),
      limbs_of_lt (by omega : ((foldGrindingTable.getD (R - 1) []).getD (μ - 16) []).length < 2 ^ 64)]
    have hz := zipWith3_cost P (by includes) (fun (g : ℕ × ℕ) (q b : ℕ) ↦ (⟨g.1, g.2, q, b⟩ : Level))
      (.closure ladderC.lam0.costIdx [])
      (fun g q b ↦ RunsApp.of_spec (ladderC.lam0.costSpec P (by includes) g q b)) 12
      (fun g q b ↦ by
        rw [appCost_fn, List.length_nil, Nat.add_zero, List.nil_append, ladderC.lam0.costEq P (by includes)]
        omega)
      (ladderShape μ R) ((queryTable.getD (R - 1) []).getD (μ - 16) [])
      ((foldGrindingTable.getD (R - 1) []).getD (μ - 16) [])
    simp only [h1, h2, h3, h4, and_self, ↓reduceIte, max_self]
    generalize machineCost P Auto.List.zipWith3.c353.costIdx
        [MachineValue.closure ladderC.lam0.costIdx [], encodeValue (ladderShape μ R),
          encodeValue ((queryTable.getD (R - 1) []).getD (μ - 16) []),
          encodeValue ((foldGrindingTable.getD (R - 1) []).getD (μ - 16) [])] = Z at hz ⊢
    by_cases hc : (ladderShape μ R).length = ((queryTable.getD (R - 1) []).getD (μ - 16) []).length ∧
        (ladderShape μ R).length = ((foldGrindingTable.getD (R - 1) []).getD (μ - 16) []).length
    · have hC := hc.1 ▸ hc.2
      simp only [hc.1, hC, and_self, ↓reduceIte]
      omega
    · simp only [hc, ↓reduceIte]
      split_ifs <;> omega
  · split_ifs <;> simp_all

open LeanVM.Parameters.Whir in
theorem ladder_head {μ R : ℕ} {lv : Level} {rest : List Level}
    (h : ladder μ R = some (lv :: rest)) : lv.fold = initialFold ∧ lv.logInvRate = R := by
  unfold ladder at h
  dsimp only at h
  split_ifs at h
  obtain h := Option.some.inj h
  rw [ladderShape] at h
  generalize (queryTable.getD (R - 1) []).getD (μ - minLogStack) [] = qs at h
  generalize (foldGrindingTable.getD (R - 1) []).getD (μ - minLogStack) [] = gs at h
  cases qs with
  | nil => simp [List.zipWith3] at h
  | cons q qs =>
    cases gs with
    | nil => simp [List.zipWith3] at h
    | cons b gs =>
      simp only [List.zipWith3, List.cons.injEq] at h
      rw [← h.1]
      exact ⟨rfl, rfl⟩

open LeanVM.Protocol.Compile in
/-- **Reading the stack's root**: the ladder, then the root at its first level: at most
`6312 + 11·|roots|`. -/
theorem commitStackPure_cost (hP : Includes P commitStackPureC.costDeps) (logN R : ℕ) (s : VerifierProgramState)
    (hN : logN < 2 ^ 63) (hR : R < 2 ^ 60) (hs : s.sponge.pending.length ≤ 4) :
    machineCost P commitStackPureC.costIdx [encodeValue logN, encodeValue R, encodeValue s] ≤ 11 * s.roots.length + 6312 := by
  rw [commitStackPureC.costEq P hP]
  have hl := ladder_cost P (by includes) logN R (by omega) (by omega)
  cases hla : LeanVM.Parameters.Whir.ladder logN R with
  | none => simp only; omega
  | some levels =>
    cases levels with
    | nil => simp only; omega
    | cons lv rest =>
      obtain ⟨hf, hr⟩ := ladder_head hla
      simp only [hf, hr, LeanVM.Parameters.Whir.initialFold]
      have hc := commitPure_cost P (by includes) (logN - 6 + R) (2 ^ 6) s hs
      rw [limbs_of_lt (by omega : logN < 2 ^ 64), limbs_of_lt (by norm_num : (6 : ℕ) < 2 ^ 64),
        limbs_of_lt (by omega : logN - 6 + R < 2 ^ 64),
        limbs_of_lt (by omega : logN - 6 < 2 ^ 64), limbs_of_lt (by omega : R < 2 ^ 64),
        limbs_of_lt (by norm_num : 1 <<< 6 < 2 ^ 64)]
      omega

/-! ## Logarithms -/

theorem log2_lt_64 {n : ℕ} (hn : n < 2 ^ 64) : Nat.log2 n < 64 := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · exact (Nat.log2_lt (by omega)).2 hn

theorem bitLength_cost (hP : Includes P bitLengthC.costDeps) (n : ℕ) (hn : n < 2 ^ 64) :
    machineCost P bitLengthC.costIdx [encodeValue n] ≤ 771 := by
  rw [bitLengthC.costEq P hP, limbs_of_lt hn]
  have h64 := log2_lt_64 hn
  split_ifs
  · omega
  · have := log2Rec_cost_word P (by includes) n hn
    rw [limbs_of_lt (by omega : Nat.log2 n < 2 ^ 64), limbs_of_lt (by omega : Nat.log2 n + 1 < 2 ^ 64)]
    omega

theorem bitLength_lt {n : ℕ} (hn : n < 2 ^ 64) : LeanVM.Protocol.Verifier.bitLength n ≤ 64 := by
  unfold LeanVM.Protocol.Verifier.bitLength
  have := log2_lt_64 hn
  split <;> omega

theorem log2Strict_cost (hP : Includes P log2StrictC.costDeps) (v : ℕ) (hv : v < 2 ^ 64) :
    machineCost P log2StrictC.costIdx [encodeValue v] ≤ 789 := by
  rw [log2StrictC.costEq P hP, limbs_of_lt hv, limbs_of_lt (by omega : v - 1 < 2 ^ 64),
    limbs_of_lt (lt_of_le_of_lt Nat.and_le_left hv)]
  have := bitLength_cost P (by includes) v hv
  rw [limbs_of_lt (by have := bitLength_lt hv; omega : LeanVM.Protocol.Verifier.bitLength v < 2 ^ 64)]
  simp only [max_self]
  split_ifs <;> omega

/-! ## The `KECCAK` slots -/

open LeanVM.Protocol.Verifier in
theorem globalColumnBases_length : globalColumnBases.length = 6 := by
  rw [FastLib.globalColumnBasesLit]; rfl

open LeanVM.Protocol.Verifier in
theorem keccakBase : globalColumnBases.getD opKeccak 0 = 73 := by
  rw [FastLib.globalColumnBasesLit]; rfl

open LeanVM.Protocol.Verifier in
/-- A column's `KECCAK` slot: at most `2522`. -/
theorem keccakSlot_cost (hP : Includes P keccakSlotC.costDeps) (c : ℕ) (hc : c < 2 ^ 64) :
    machineCost P keccakSlotC.costIdx [encodeValue c] ≤ 2522 := by
  rw [keccakSlotC.costEq P hP]
  have hg := getD_cost P (by includes) globalColumnBases opKeccak 0 (by simp [opKeccak])
  rw [globalColumnBases_length] at hg
  have hf := findIdxOptGo_cost P (by includes) (fun x ↦ x == c - globalColumnBases.getD opKeccak 0)
    (.closure keccakSlotC.lam1.costIdx [encodeValue c])
    (fun x ↦ RunsApp.of_spec (keccakSlotC.lam1.costSpec P (by includes) c x)) 132
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 0 (by simp)
    (fun x hx ↦ by
      rw [appCost_fn, List.length_singleton, List.cons_append, List.nil_append, keccakSlotC.lam1.costEq P (by includes),
        keccakBase, limbs_of_lt hc, limbs_of_lt (by norm_num : (73 : ℕ) < 2 ^ 64),
        limbs_of_lt (by simp at hx; omega : x < 2 ^ 64), limbs_of_lt (by omega : c - 73 < 2 ^ 64)]
      simp only [max_self]
      omega)
  have hm : ∀ o : Option ℕ, o.all (· < 2 ^ 63) → machineCost P Auto.Option.map.c194.costIdx
      [MachineValue.closure keccakSlotC.lam0.costIdx [], encodeValue o] ≤ 11 := by
    intro o ho
    rw [Auto.Option.map.c194.costEq P (by includes) _ _
      (fun x ↦ RunsApp.of_spec (keccakSlotC.lam0.costSpec P (by includes) x))]
    cases o with
    | none => simp
    | some x =>
      simp only [Option.all_some, decide_eq_true_eq] at ho
      simp only [appCost_fn, List.length_nil, List.nil_append, keccakSlotC.lam0.costEq P (by includes),
        limbs_of_lt (by omega : x < 2 ^ 64), limbs_of_lt (by omega : 50 + x < 2 ^ 64)]
      omega
  have hidx := hm (List.idxOf? (c - globalColumnBases.getD opKeccak 0)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]) (by
      cases h : List.idxOf? (c - globalColumnBases.getD opKeccak 0)
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] with
      | none => rfl
      | some k =>
        obtain ⟨hk, -⟩ := List.idxOf?_eq_some_iff.1 h
        simp only [Option.all_some, decide_eq_true_eq]
        simp at hk; omega)
  rw [keccakBase] at hidx ⊢
  rw [limbs_of_lt hc, limbs_of_lt (by norm_num : (73 : ℕ) < 2 ^ 64),
    limbs_of_lt (by omega : c - 73 < 2 ^ 64), limbs_of_lt (by norm_num : (15 + 25 : ℕ) < 2 ^ 64)]
  simp only [max_self, List.length_cons, List.length_nil] at hf ⊢
  split_ifs <;> omega

/-! ## Folds with an invariant on the rest of the list -/

/-- **`List.foldl` with an invariant `J acc rest`** of the accumulator and the elements left. -/
theorem listFoldl_le' {α β : Type} [MachineEncoding α] [MachineEncoding β] (hP : Includes P listFoldl.costDeps)
    (f : α → β → α) (fVal : MachineValue) (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (B : ℕ)
    (J : α → List β → Prop)
    (hJ : ∀ acc b l, J acc (b :: l) → J (f acc b) l ∧ appCost P fVal [encodeValue acc, encodeValue b] ≤ B) :
    ∀ (l : List β) (init : α), J init l →
      machineCost P listFoldl.costIdx [fVal, encodeValue init, encodeValue l] ≤ (B + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro init _; rw [listFoldl.costEq_nil P hP f fVal hf]; omega
  | cons b l ih =>
    intro init hI
    rw [listFoldl.costEq_cons P hP f fVal hf]
    obtain ⟨hI', h2⟩ := hJ init b l hI
    have h1 := ih (f init b) hI'
    simp only [List.length_cons]
    nlinarith

theorem foldl_inv {α β : Type} (f : α → β → α) (J : α → List β → Prop)
    (hJ : ∀ acc b l, J acc (b :: l) → J (f acc b) l) :
    ∀ (l : List β) (init : α), J init l → J (l.foldl f init) [] := by
  intro l
  induction l with
  | nil => intro init h; exact h
  | cons b l ih => intro init h; exact ih (f init b) (hJ init b l h)

/-! ## The stack's offsets -/

/-- The invariant of `stackOffsets`'s fold: the offsets' length, every offset at most the running
total, and room for `2^40` per element left. -/
def OffsetsInv (n : ℕ) (acc : List ℕ × ℕ) (rest : List ℕ) : Prop :=
  acc.1.length = n ∧ (∀ x ∈ acc.1, x ≤ acc.2) ∧ acc.2 + 2 ^ 40 * rest.length < 2 ^ 64

theorem offsetsInv_step (sizes : List ℕ) (hs : ∀ x ∈ sizes, x ≤ 40) (acc : List ℕ × ℕ) (i : ℕ)
    (rest : List ℕ) (h : OffsetsInv sizes.length acc (i :: rest)) :
    OffsetsInv sizes.length (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0) rest := by
  obtain ⟨h1, h2, h3⟩ := h
  have hsz : sizes.getD i 0 ≤ 40 := by
    rcases getD_mem_or sizes i 0 with hm | hm
    · exact hs _ hm
    · rw [hm]; omega
  have hp : 2 ^ sizes.getD i 0 ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hsz
  have hp0 : 0 < 2 ^ sizes.getD i 0 := Nat.two_pow_pos _
  simp only [List.length_cons] at h3
  refine ⟨by simp [h1], fun x hx ↦ ?_, ?_⟩
  · rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · have := h2 x hx; dsimp only; omega
    · dsimp only; omega
  · dsimp only; omega

open LeanVM.Protocol.Verifier in
theorem stackOffsets_bounds (sizes : List ℕ) (hn : sizes.length ≤ 200)
    (hs : ∀ x ∈ sizes, x ≤ 40) :
    (∀ x ∈ (stackOffsets sizes).1, x < 2 ^ 63) ∧ (stackOffsets sizes).2 ≤ 64 := by
  unfold stackOffsets
  dsimp only
  set order := (List.range sizes.length).mergeSort fun i j ↦
    decide (sizes.getD j 0 < sizes.getD i 0) ||
      (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j))
  have hlen : order.length = sizes.length := by simp [order]
  have hf := foldl_inv (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0))
    (fun acc rest ↦ OffsetsInv sizes.length acc rest ∧ acc.2 + 2 ^ 40 * rest.length < 2 ^ 63)
    (fun acc i rest h ↦ ⟨offsetsInv_step sizes hs acc i rest h.1, by
      have := offsetsInv_step sizes hs acc i rest h.1
      have hsz : sizes.getD i 0 ≤ 40 := by
        rcases getD_mem_or sizes i 0 with hm | hm
        · exact hs _ hm
        · rw [hm]; omega
      have hp : 2 ^ sizes.getD i 0 ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hsz
      have := h.2; simp only [List.length_cons] at this; dsimp only; omega⟩)
    order (List.replicate sizes.length 0, 0)
    ⟨⟨by simp, fun x hx ↦ by simp [List.eq_of_mem_replicate hx], by rw [hlen]; omega⟩,
      by rw [hlen]; simp only; omega⟩
  have hT := hf.2
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hT
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · have := hf.1.2.1 x hx
    omega
  · exact bitLength_lt (by omega)

open LeanVM.Protocol.Verifier in
/-- **The stack's offsets** of at most `200` blocks of at most `2^40` cells: at most `973716067`
(`≈ 2^29.86`). -/
theorem stackOffsets_cost (hP : Includes P stackOffsetsC.costDeps) (sizes : List ℕ)
    (hn : sizes.length ≤ 200) (hs : ∀ x ∈ sizes, x ≤ 40) :
    machineCost P stackOffsetsC.costIdx [encodeValue sizes] ≤ 973716067 := by
  rw [stackOffsetsC.costEq P hP]
  set n := sizes.length with hnd
  have hsz : ∀ i, sizes.getD i 0 ≤ 40 := fun i ↦ by
    rcases getD_mem_or sizes i 0 with hm | hm
    · exact hs _ hm
    · rw [hm]; omega
  have hlen := length_cost P (by includes) sizes (by omega)
  have hrange := rangeLoop_cost P (by includes) n [] (by omega)
  have hrep := replicate_cost P (by includes) (0 : ℕ) n (by omega)
  -- the comparison
  have hcmp : ∀ i ∈ List.range n, ∀ j ∈ List.range n,
      appCost P (.closure stackOffsetsC.lam0.costIdx [encodeValue sizes]) [encodeValue i, encodeValue j] ≤ 12062 := by
    intro i hi j hj
    simp only [List.mem_range] at hi hj
    rw [appCost_fn, List.length_singleton, List.cons_append, List.nil_append, stackOffsetsC.lam0.costEq P (by includes)]
    have g1 := getD_cost P (by includes) sizes i 0 (by omega)
    have g2 := getD_cost P (by includes) sizes j 0 (by omega)
    rw [limbs_of_lt (by have := hsz i; omega : sizes.getD i 0 < 2 ^ 64),
      limbs_of_lt (by have := hsz j; omega : sizes.getD j 0 < 2 ^ 64),
      limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt (by omega : j < 2 ^ 64)]
    simp only [max_self]
    split_ifs <;> omega
  have hsort := mergeSortList_cost_sq P (by includes) _ (.closure stackOffsetsC.lam0.costIdx [encodeValue sizes])
    (fun i j ↦ RunsApp.of_spec (stackOffsetsC.lam0.costSpec P (by includes) sizes i j))
    (· ∈ List.range n) 12062 (fun a b ha hb ↦ hcmp a ha b hb) n (List.range n) (by simp)
    (by omega) (fun a ha ↦ ha)
  -- the fold
  set order := (List.range n).mergeSort fun i j ↦
    decide (sizes.getD j 0 < sizes.getD i 0) ||
      (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j))
  have hord : order.length = n := by simp [order]
  have hfold := listFoldl_le' P (by includes)
    (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0))
    (.closure stackOffsetsC.lam1.costIdx [encodeValue sizes])
    (fun acc i ↦ RunsApp.of_spec (stackOffsetsC.lam1.costSpec P (by includes) sizes acc i)) 7031
    (fun acc rest ↦ OffsetsInv n acc rest ∧ ∀ i ∈ rest, i < n)
    (fun acc i rest h ↦ ⟨⟨offsetsInv_step sizes hs acc i rest h.1,
        fun k hk ↦ h.2 k (by simp [hk])⟩, by
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
      have hi := h4 i (by simp)
      rw [appCost_fn, List.length_singleton, List.cons_append, List.nil_append, stackOffsetsC.lam1.costEq P (by includes)]
      have s1 := set_cost P (by includes) acc.2 acc.1 i (by omega)
      have g1 := getD_cost P (by includes) sizes i 0 (by omega)
      have hp : 2 ^ sizes.getD i 0 ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (hsz i)
      have hsh : 1 <<< sizes.getD i 0 < 2 ^ 64 := by
        rw [Nat.one_shiftLeft]; have : (2 : ℕ) ^ 40 < 2 ^ 64 := by norm_num
        omega
      simp only [List.length_cons] at h3
      rw [limbs_of_lt hsh, limbs_of_lt (by have := hsz i; omega : sizes.getD i 0 < 2 ^ 64),
        limbs_of_lt (by omega : acc.2 < 2 ^ 64),
        limbs_of_lt (by have h40 : (2 : ℕ) ^ 40 < 2 ^ 64 := (by norm_num); omega :
          2 ^ sizes.getD i 0 < 2 ^ 64),
        limbs_of_lt (by omega : acc.2 + 2 ^ sizes.getD i 0 < 2 ^ 64)]
      rw [h1] at s1
      simp only [max_self]
      omega⟩)
    order (List.replicate n 0, 0)
    ⟨⟨by simp, fun x hx ↦ by simp [List.eq_of_mem_replicate hx], by rw [hord]; omega⟩,
      fun i hi ↦ by simpa [order] using hi⟩
  rw [hord] at hfold
  -- the total
  have hfin := foldl_inv (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0))
    (OffsetsInv n) (fun acc i rest h ↦ offsetsInv_step sizes hs acc i rest h) order
    (List.replicate n 0, 0) ⟨by simp, fun x hx ↦ by simp [List.eq_of_mem_replicate hx],
      by rw [hord]; omega⟩
  obtain ⟨-, -, hT⟩ := hfin
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hT
  have hb := bitLength_cost P (by includes)
    ((List.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0))
      (List.replicate n 0, 0) order).2 - 1) (by omega)
  rw [limbs_of_lt hT]
  have hsq : n * n ≤ 40000 := by nlinarith
  omega

/-! ## The placements -/

open LeanVM.Protocol.Verifier in
theorem keccakOutputColumns_facts :
    keccakOutputColumns.length = 25 ∧ ∀ x ∈ keccakOutputColumns, x < 2 ^ 64 := by
  rw [FastLib.keccakOutputColumnsLit]
  refine ⟨by simp, fun x hx ↦ ?_⟩
  simp only [List.mem_map, List.mem_range] at hx
  omega

open LeanVM.Protocol.Verifier in
theorem keccakSlot_lt {c v : ℕ} (h : keccakSlot c = some v) : v < 64 := by
  unfold keccakSlot at h
  split_ifs at h
  rw [FastLib.keccakSlotOfLit] at h
  split_ifs at h with h1
  · obtain rfl := Option.some.inj h; omega
  · obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hk', -⟩ := List.idxOf?_eq_some_iff.1 hk
    simp at hk'; omega

open LeanVM.Protocol.Verifier in
/-- The test whether a column is placed in a block of its own: at most `3597`. -/
theorem placementsLam0_cost (hP : Includes P placementsOfC.lam0.costDeps) (c : ℕ) (hc : c < 2 ^ 64) :
    machineCost P placementsOfC.lam0.costIdx [encodeValue c] ≤ 3597 := by
  rw [placementsOfC.lam0.costEq P hP]
  have hk := keccakSlot_cost P (by includes) c hc
  have hr := rangeLoop_cost P (by includes) 25 [] (by norm_num)
  have hm := map_cost P (by includes) (fun x : ℕ ↦ 113 + x) (.closure placementsOfC.lam0.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (placementsOfC.lam0.lam0.costSpec P (by includes) x)) 3 (List.range 25)
    (fun x hx ↦ by
      simp only [List.mem_range] at hx
      rw [appCost_fn, List.length_nil, Nat.add_zero, List.nil_append, placementsOfC.lam0.lam0.costEq P (by includes),
        limbs_of_lt (by omega : x < 2 ^ 64), limbs_of_lt (by omega : 113 + x < 2 ^ 64), max_self])
  obtain ⟨ho1, ho2⟩ := keccakOutputColumns_facts
  have he := elem_cost P (by includes) c hc keccakOutputColumns ho2
  simp only [List.length_range, ho1] at hm he
  cases keccakSlot c <;> simp only [Option.isNone_none, Option.isNone_some, ↓reduceIte,
    Bool.false_eq_true] <;> omega

open LeanVM.Protocol.Verifier in
/-- **The placements** of at most `200` columns of log-sizes at most `40`: at most `977100324`. -/
theorem placementsOf_cost (hP : Includes P placementsOfC.costDeps) (kappas : List ℕ)
    (hn : kappas.length ≤ 200) (hk : ∀ x ∈ kappas, x ≤ 40) :
    machineCost P placementsOfC.costIdx [encodeValue kappas] ≤ 977100324 := by
  rw [placementsOfC.costEq P hP]
  set N := kappas.length with hN
  have hkD : ∀ i, kappas.getD i 0 ≤ 40 := fun i ↦ by
    rcases getD_mem_or kappas i 0 with hm | hm
    · exact hk _ hm
    · rw [hm]; omega
  set cap0 := List.filter (fun c ↦ decide ((keccakSlot c).isNone = true ∧ c ∉ keccakOutputColumns))
    (List.range N) with hcap
  have hcapl : cap0.length ≤ N := (List.length_filter_le _ _).trans (by simp)
  have hcapm : ∀ x ∈ cap0, x < N := fun x hx ↦ by
    have := (List.mem_filter.1 hx).1; simpa using this
  have hlen := length_cost P (by includes) kappas (by omega)
  have hrange := rangeLoop_cost P (by includes) N [] (by omega)
  have hfilt := filter_cost P (by includes) _ (.closure placementsOfC.lam0.costIdx [])
    (fun c ↦ RunsApp.of_spec (placementsOfC.lam0.costSpec P (by includes) c)) 3597 (List.range N)
    (fun c hc ↦ by
      simp only [List.mem_range] at hc
      rw [appCost_fn, List.length_nil, Nat.add_zero, List.nil_append]
      exact placementsLam0_cost P (by includes) c (by omega))
  simp only [List.length_range] at hfilt
  have hmap1 := map_cost P (by includes) (fun x ↦ kappas.getD x 0) (.closure placementsOfC.lam1.costIdx [encodeValue kappas])
    (fun x ↦ RunsApp.of_spec (placementsOfC.lam1.costSpec P (by includes) kappas x)) 3014 cap0
    (fun x hx ↦ by
      have := hcapm x hx
      rw [appCost_fn, List.length_singleton, List.cons_append, List.nil_append, placementsOfC.lam1.costEq P (by includes)]
      have := getD_cost P (by includes) kappas x 0 (by omega)
      omega)
  set sizes := List.map (fun x ↦ kappas.getD x 0) cap0 with hsizes
  have hso := stackOffsets_cost P (by includes) sizes (by simp [sizes]; omega)
    (fun x hx ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact hkD i)
  obtain ⟨hfst, hsnd⟩ := stackOffsets_bounds sizes (by simp [sizes]; omega)
    (fun x hx ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact hkD i)
  have hfstl : (stackOffsets sizes).1.length = sizes.length := by
    unfold stackOffsets
    dsimp only
    apply foldl_inv (J := fun (acc : List ℕ × ℕ) (_ : List ℕ) ↦ acc.1.length = sizes.length)
    · intro acc i rest h; simp [h]
    · simp
  have hsl : sizes.length ≤ 200 := by simp [sizes]; omega
  -- the map over the columns
  have hzip := zipIdx_cost P (by includes) kappas 0 (by omega)
  have hlam2 : ∀ x ∈ kappas.zipIdx, appCost P (.closure placementsOfC.lam2.costIdx
      [encodeValue (stackOffsets sizes).1, encodeValue cap0]) [encodeValue x] ≤ 10229 := by
    intro x hx
    obtain ⟨kappa, col⟩ := x
    have hcol : col < N := by
      have := List.snd_lt_of_mem_zipIdx hx
      simp only at this; omega
    have hkap : kappa ≤ 40 := hk _ (List.fst_mem_of_mem_zipIdx hx)
    rw [appCost_fn, List.length_cons, List.length_singleton, List.cons_append, List.cons_append, List.nil_append,
      placementsOfC.lam2.costEq_mk P (by includes)]
    have hks := keccakSlot_cost P (by includes) col (by omega)
    have hr := rangeLoop_cost P (by includes) 25 [] (by norm_num)
    have hm := map_cost P (by includes) (fun x : ℕ ↦ 113 + x) (.closure placementsOfC.lam0.lam0.costIdx [])
      (fun x ↦ RunsApp.of_spec (placementsOfC.lam0.lam0.costSpec P (by includes) x)) 3
      (List.range 25)
      (fun x hx ↦ by
        simp only [List.mem_range] at hx
        rw [appCost_fn, List.length_nil, Nat.add_zero, List.nil_append, placementsOfC.lam0.lam0.costEq P (by includes),
          limbs_of_lt (by omega : x < 2 ^ 64), limbs_of_lt (by omega : 113 + x < 2 ^ 64), max_self])
    obtain ⟨ho1, ho2⟩ := keccakOutputColumns_facts
    have he := elem_cost P (by includes) col (by omega) keccakOutputColumns ho2
    have hf0 := findIdxGo_cost P (by includes) (fun x ↦ x == col)
      (.closure placementsOfC.lam2.lam0.costIdx [encodeValue col])
      (fun x ↦ RunsApp.of_spec (placementsOfC.lam2.lam0.costSpec P (by includes) col x)) 4 cap0 0
      (by omega) (fun x hx ↦ by
        have := hcapm x hx
        rw [appCost_fn, List.length_singleton, List.cons_append, List.nil_append,
          placementsOfC.lam2.lam0.costEq P (by includes), limbs_of_lt (by omega : x < 2 ^ 64),
          limbs_of_lt (by omega : col < 2 ^ 64)]
        simp)
    have hf1 := findIdxGo_cost P (by includes) (fun x ↦ x == qkeccak)
      (.closure placementsOfC.lam2.lam1.costIdx [])
      (fun x ↦ RunsApp.of_spec (placementsOfC.lam2.lam1.costSpec P (by includes) x)) 3 cap0 0
      (by omega) (fun x hx ↦ by
        have := hcapm x hx
        rw [appCost_fn, List.length_nil, Nat.add_zero, List.nil_append, placementsOfC.lam2.lam1.costEq P (by includes),
          limbs_of_lt (by omega : x < 2 ^ 64), limbs_of_lt (by simp [qkeccak])]
        simp)
    have hg0 := getD_cost P (by includes) (stackOffsets sizes).1 (List.idxOf col cap0) 0 (by
      have := List.idxOf_le_length (a := col) (l := cap0); omega)
    have hg1 := getD_cost P (by includes) (stackOffsets sizes).1 (List.idxOf qkeccak cap0) 0 (by
      have := List.idxOf_le_length (a := qkeccak) (l := cap0); omega)
    simp only [List.length_range, ho1, hfstl] at hm he hg0 hg1
    have hp : 2 ^ kappa ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) hkap
    have h40 : (2 : ℕ) ^ 40 < 2 ^ 58 := by norm_num
    cases hsl' : keccakSlot col with
    | none =>
      simp only
      split <;> omega
    | some v =>
      simp only
      have hv := keccakSlot_lt hsl'
      have hoff : (stackOffsets sizes).1.getD (List.idxOf qkeccak cap0) 0 < 2 ^ 63 := by
        rcases getD_mem_or (stackOffsets sizes).1 (List.idxOf qkeccak cap0) 0 with hm' | hm'
        · have := hfst _ hm'; omega
        · rw [hm']; norm_num
      have hvk : v * 2 ^ kappa < 2 ^ 63 := by
        calc v * 2 ^ kappa ≤ 64 * 2 ^ 40 := Nat.mul_le_mul (by omega) hp
          _ < 2 ^ 63 := by norm_num
      rw [limbs_of_lt (by rw [Nat.one_shiftLeft]; omega : 1 <<< kappa < 2 ^ 64),
        limbs_of_lt (by omega : kappa < 2 ^ 64), limbs_of_lt (by omega : v < 2 ^ 64),
        limbs_of_lt (by omega : 2 ^ kappa < 2 ^ 64), limbs_of_lt (by omega : (stackOffsets sizes).1.getD (List.idxOf qkeccak cap0) 0 < 2 ^ 64),
        limbs_of_lt (by omega : v * 2 ^ kappa < 2 ^ 64),
        limbs_of_lt (by omega : (stackOffsets sizes).1.getD (List.idxOf qkeccak cap0) 0 + v * 2 ^ kappa < 2 ^ 64)]
      simp only [max_self]
      omega
  have hmap2 := map_cost P (by includes) _ (.closure placementsOfC.lam2.costIdx
      [encodeValue (stackOffsets sizes).1, encodeValue cap0])
    (fun x ↦ RunsApp.of_spec (placementsOfC.lam2.costSpec P (by includes) _ cap0 x)) 10229
    kappas.zipIdx hlam2
  simp only [List.length_zipIdx] at hmap2
  generalize hst : stackOffsets sizes = st at hmap2 hsnd hso
  obtain ⟨fst, snd⟩ := st
  simp only at hmap2 hsnd ⊢
  rw [limbs_of_lt (by omega : snd < 2 ^ 64), limbs_of_lt (by simp [Whir.minLogStack])]
  simp only [max_self, ite_self]
  omega

/-! ## The layout -/

open LeanVM.Protocol.Verifier in
theorem log2Ceil_le {r : ℕ} (h : r ≤ 2 ^ 32) : log2Ceil r ≤ 32 := by
  unfold log2Ceil bitLength
  split
  · omega
  · have : Nat.log2 (r - 1) < 32 := (Nat.log2_lt (by omega)).2 (by omega)
    omega

open LeanVM.Protocol.Verifier in
theorem log2Ceil_lt {r : ℕ} (h : r < 2 ^ 64) : log2Ceil r ≤ 64 := by
  unfold log2Ceil; exact bitLength_lt (by omega)

open LeanVM.Protocol.Verifier in
theorem log2Strict_le {v k : ℕ} (hv : v < 2 ^ 64) (h : log2Strict v = some k) : k ≤ 64 := by
  unfold log2Strict at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  have := bitLength_lt hv
  omega

open LeanVM.Protocol.Verifier in
theorem tableLogFloors_eq : tableLogFloors = [0, 0, 0, 0, 0, 9] := rfl

open LeanVM.Protocol.Verifier in
theorem qkeccakSlotBits_eq : qkeccakSlotBits = 6 := by decide +kernel

open LeanVM.Protocol.Verifier in
/-- The tables' log-heights from their row counts. -/
theorem heights_facts (rows : List ℕ) (hr : ∀ r ∈ rows, r ≤ 2 ^ 32) :
    (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors).length ≤ 6 ∧
    ∀ h ∈ List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors, h ≤ 32 := by
  have key : ∀ (rows floors : List ℕ), (∀ r ∈ rows, r ≤ 2 ^ 32) → (∀ f ∈ floors, f ≤ 32) →
      ∀ h ∈ List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows floors, h ≤ 32 := by
    intro rows
    induction rows with
    | nil => intro floors _ _ h hh; simp at hh
    | cons r rows ih =>
      intro floors hr hf h hh
      cases floors with
      | nil => simp at hh
      | cons f floors =>
        simp only [List.zipWith_cons_cons, List.mem_cons] at hh
        rcases hh with rfl | hh
        · have := log2Ceil_le (hr r (by simp)); have := hf f (by simp); omega
        · exact ih floors (fun x hx ↦ hr x (by simp [hx])) (fun x hx ↦ hf x (by simp [hx])) h hh
  refine ⟨by simp [tableLogFloors_eq], key rows tableLogFloors hr (by
    rw [tableLogFloors_eq]; intro f hf; simp at hf; omega)⟩

open LeanVM.Protocol.Verifier in
theorem columnKappas_facts (logMemory logBytecode : ℕ) (heights : List ℕ) (hm : logMemory ≤ 32)
    (hb : logBytecode ≤ 32) (hh : ∀ i, heights.getD i 0 ≤ 32) :
    (columnKappas logMemory logBytecode heights).length = 165 ∧
      ∀ x ∈ columnKappas logMemory logBytecode heights, x ≤ 40 := by
  rw [FastLib.columnKappasLit, qkeccakSlotBits_eq]
  refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil, List.flatMap_cons,
    List.flatMap_nil, List.length_replicate, List.append_nil], fun x hx ↦ ?_⟩
  simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_replicate,
    List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨p, -, -, rfl⟩
  all_goals first | omega | (have := hh opKeccak; omega) | (have := hh p.2; omega)

open LeanVM.Protocol.Verifier in
/-- **The layout's fields**: `8` per bytecode word, then at most `977122709`. -/
theorem buildLayoutLite_cost (hP : Includes P buildLayoutLiteC.costDeps) (bytecode : List K)
    (logMemory : ℕ) (tableRows : List ℕ) (hb : bytecode.length < 2 ^ 63) (hm : logMemory < 2 ^ 64)
    (hr : ∀ r ∈ tableRows, r < 2 ^ 64) (hrl : tableRows.length ≤ 6) :
    machineCost P buildLayoutLiteC.costIdx [encodeValue bytecode, encodeValue logMemory, encodeValue tableRows] ≤
      8 * bytecode.length + 977122709 := by
  rw [buildLayoutLiteC.costEq P hP]
  have hbl := length_cost P (by includes) bytecode (by omega)
  have hls := log2Strict_cost P (by includes) bytecode.length (by omega)
  cases hlog : log2Strict bytecode.length with
  | none => simp only; omega
  | some val =>
    simp only
    have hval := log2Strict_le (by omega) hlog
    have hall := all_cost P (by includes) (fun x : ℕ ↦ decide (x ≤ 2 ^ 32))
      (.closure buildLayoutLiteC.lam0.costIdx [])
      (fun x ↦ RunsApp.of_spec (buildLayoutLiteC.lam0.costSpec P (by includes) x)) 7 tableRows
      (fun x hx ↦ by
        rw [appCost_fn, List.length_nil, Nat.add_zero, List.nil_append, buildLayoutLiteC.lam0.costEq P (by includes),
          limbs_of_lt (hr x hx), limbs_of_lt (by norm_num : 1 <<< 32 < 2 ^ 64),
          limbs_of_lt (by norm_num : (2 : ℕ) ^ 32 < 2 ^ 64)]
        simp)
    have hlr := length_cost P (by includes) tableRows (by omega)
    simp only [busBits, FastLib.tablesLength, limbs_of_lt hm, limbs_of_lt (by omega : val < 2 ^ 64),
      limbs_of_lt (by omega : val - 4 < 2 ^ 64), limbs_of_lt (by omega : tableRows.length < 2 ^ 64),
      limbs_of_lt (by norm_num : (4 : ℕ) < 2 ^ 64), max_self]
    have h6 : limbCount 6 = 1 := limbs_of_lt (by norm_num)
    by_cases hc : 4 ≤ val ∧ 1 ≤ logMemory ∧ logMemory ≤ 32 ∧
        (tableRows.all fun x ↦ decide (x ≤ 2 ^ 32)) = true ∧ val - 4 ≤ 32 ∧ tableRows.length = 6
    · obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hc
      have hr32 : ∀ r ∈ tableRows, r ≤ 2 ^ 32 := fun r hr' ↦ by
        have := List.all_eq_true.1 c4 r hr'; simpa using this
      set heights := List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
        tableLogFloors with hheights
      obtain ⟨hhl, hhm⟩ := heights_facts tableRows hr32
      have hhl' : heights.length ≤ 6 := hhl
      have hhD : ∀ i, heights.getD i 0 ≤ 32 := fun i ↦ by
        rcases getD_mem_or heights i 0 with h' | h'
        · exact hhm _ h'
        · rw [h']; omega
      have htf : machineCost P tableLogFloorsC.costIdx [] = 25 := tableLogFloorsC.costEq P (by includes)
      have hzip := listZipWith_le P (by includes) (fun rows floor ↦ max (log2Ceil rows) floor)
        (.closure buildLayoutLiteC.lam1.costIdx [])
        (fun r f ↦ RunsApp.of_spec (buildLayoutLiteC.lam1.costSpec P (by includes) r f)) 1555
        tableRows tableLogFloors (fun r hr' f hf ↦ by
          rw [tableLogFloors_eq] at hf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
          have hf9 : f ≤ 9 := by rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
          rw [appCost_fn, List.length_nil, Nat.add_zero, List.nil_append, buildLayoutLiteC.lam1.costEq P (by includes)]
          have hb1 := bitLength_cost P (by includes) (r - 1) (by have := hr r hr'; omega)
          have hl := log2Ceil_lt (hr r hr')
          rw [limbs_of_lt (hr r hr'), limbs_of_lt (by omega : log2Ceil r < 2 ^ 64),
            limbs_of_lt (by omega : f < 2 ^ 64)]
          simp only [max_self]
          split_ifs <;> omega)
      have hgk := getD_cost P (by includes) heights opKeccak 0 (by simp [opKeccak])
      have hb49 := bitLength_cost P (by includes) (25 * keccakSegments - 1)
        (by simp [keccakSegments, keccakDepth])
      have hmap := map_cost P (by includes)
        (fun p : ℕ × ℕ ↦ List.replicate p.1 (heights.getD p.2 0))
        (.closure buildLayoutLiteC.lam2.costIdx [encodeValue heights])
        (fun p ↦ RunsApp.of_spec (buildLayoutLiteC.lam2.costSpec P (by includes) heights p)) 1493
        [(15, 0), (15, 1), (8, 2), (15, 3), (14, 4), (92, 5)] (fun p hp ↦ by
          have hp1 : p.1 ≤ 92 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
          rw [appCost_fn, List.length_singleton, List.cons_append, List.nil_append,
            buildLayoutLiteC.lam2.costEq P (by includes)]
          have g := getD_cost P (by includes) heights p.2 0 (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
          have rp := replicate_cost P (by includes) (heights.getD p.2 0) p.1 (by omega)
          omega)
      have hflat := (flatten_cost_length P (by includes)
        ((List.map (fun p : ℕ × ℕ ↦ List.replicate p.1 (heights.getD p.2 0))
          [(15, 0), (15, 1), (8, 2), (15, 3), (14, 4), (92, 5)]))).trans (le_of_eq (show _ = 1818 by
            simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
              List.length_append, List.length_replicate, List.length_cons, List.length_nil]))
      have happ := (append_cost P (by includes)
        [logMemory, logMemory, logMemory, logMemory, val - 4,
          heights.getD opKeccak 0 + qkeccakSlotBits]
        (List.flatMap (fun p : ℕ × ℕ ↦ List.replicate p.1 (heights.getD p.2 0))
          [(15, 0), (15, 1), (8, 2), (15, 3), (14, 4), (92, 5)])).trans (le_of_eq (show _ = 69 by rfl))
      have htl : tableLogFloors.length = 6 := by rw [tableLogFloors_eq]; rfl
      obtain ⟨hkl, hkm⟩ := columnKappas_facts logMemory (val - 4) heights c3 c5 hhD
      have hpl := placementsOf_cost P (by includes) (columnKappas logMemory (val - 4) heights)
        (by omega) hkm
      have hq := qkeccakSlotBits_eq
      have hgk' := hhD opKeccak
      simp only [List.length_cons, List.length_nil] at hmap
      rw [hhl.antisymm (by simp [tableLogFloors_eq]; omega)] at hgk
      rw [ite_eq_left (show 4 ≤ val ∧ 1 ≤ logMemory ∧ logMemory ≤ 32 ∧
        (tableRows.all fun x ↦ decide (x ≤ 2 ^ 32)) = true ∧ val - 4 ≤ 32 ∧ tableRows.length = 6
        from ⟨c1, c2, c3, c4, c5, c6⟩)]
      simp only [c1, c2, c3, c4, c5, ↓reduceIte, keccakDepth, keccakSegments,
        limbs_of_lt (by norm_num : (12 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (2 : ℕ) < 2 ^ 64),
        limbs_of_lt (by norm_num : (50 : ℕ) < 2 ^ 64),
        limbs_of_lt (by omega : heights.getD opKeccak 0 < 2 ^ 64),
        limbs_of_lt (by omega : qkeccakSlotBits < 2 ^ 64),
        limbs_of_lt (by omega : heights.getD opKeccak 0 + qkeccakSlotBits < 2 ^ 64)] at hb49 ⊢
      simp only [Nat.reduceDiv, Nat.reduceMul] at hb49 ⊢
      have hmin : min tableRows.length tableLogFloors.length ≤ 6 := by omega
      simp only [max_self] at ⊢
      omega
    · rw [ite_eq_right hc]
      split_ifs <;> omega

/-! ## The sizes and the root -/

open LeanVM.Protocol.Compile in
theorem readPure_some : ∀ (n : ℕ) (s : VerifierProgramState) (xs : List E) (s' :
    VerifierProgramState),
    readPure n s = some (xs, s') → xs.length = n ∧ s'.roots = s.roots ∧
      (s.sponge.pending.length ≤ 4 → s'.sponge.pending.length ≤ 4)
  | 0, s, xs, s', h => by
    simp only [readPure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, id⟩
  | n + 1, ⟨sp, stream, os, roots⟩, xs, s', h => by
    cases stream with
    | nil => simp [readPure] at h
    | cons x rest =>
      simp only [readPure] at h
      obtain ⟨r, hr, hr'⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at hr'
      obtain ⟨rfl, rfl⟩ := hr'
      obtain ⟨h1, h2, h3⟩ := readPure_some n _ r.1 r.2 hr
      exact ⟨by simp [h1], h2, fun hp ↦ h3 (absorbPure_pending_le sp x dsObserve hp)⟩

theorem kToNat_lt (a : K) : LeanVM.Protocol.Verifier.kToNat a < 2 ^ 64 := by
  rw [FastLib.kToNatLane]; exact UInt64.toNat_lt _

open LeanVM.Protocol.Verifier in
theorem buildLayoutLite_stackLog {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ}
    {L : LayoutLite} (h : buildLayoutLite bytecode logMemory tableRows = some L) :
    L.stackLog ≤ 64 := by
  unfold buildLayoutLite at h
  split at h
  · simp at h
  · rename_i val _
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hc
    have hr32 : ∀ r ∈ tableRows, r ≤ 2 ^ 32 := fun r hr' ↦ by
      have := List.all_eq_true.1 c4 r hr'; simpa using this
    obtain ⟨-, hhm⟩ := heights_facts tableRows hr32
    set heights := List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
      tableLogFloors
    have hhD : ∀ i, heights.getD i 0 ≤ 32 := fun i ↦ by
      rcases getD_mem_or heights i 0 with h' | h'
      · exact hhm _ h'
      · rw [h']; omega
    obtain ⟨hkl, hkm⟩ := columnKappas_facts logMemory (val - busBits) heights c3
      (by simp only [busBits] at c5 ⊢; omega) hhD
    show (placementsOf (columnKappas logMemory (val - busBits) heights)).2 ≤ 64
    unfold placementsOf
    dsimp only
    set kappas := columnKappas logMemory (val - busBits) heights
    set cols := List.filter (fun c ↦ decide ((keccakSlot c).isNone = true ∧ c ∉ keccakOutputColumns))
      (List.range kappas.length)
    have hcl : cols.length ≤ 165 := (List.length_filter_le _ _).trans (by simp [hkl])
    obtain ⟨-, hsnd⟩ := stackOffsets_bounds (cols.map (kappas.getD · 0)) (by simp; omega)
      (fun x hx ↦ by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        rcases getD_mem_or kappas i 0 with h' | h'
        · exact hkm _ h'
        · rw [h']; omega)
    simp only [Whir.minLogStack]
    omega

open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier in
/-- **The announced sizes**: eight scalars read, the layout built: `8` per bytecode word and at
most `977124630`. -/
theorem readSizesLite_cost (hP : Includes P readSizesLiteC.costDeps) (bytecode : List K)
    (s : VerifierProgramState) (hb : bytecode.length < 2 ^ 63) (hs : s.sponge.pending.length ≤ 4) :
    machineCost P readSizesLiteC.costIdx [encodeValue bytecode, encodeValue s] ≤
      8 * bytecode.length + 977124630 := by
  rw [readSizesLiteC.costEq P hP, FastLib.tablesLength, limbs_of_lt (by norm_num : (6 : ℕ) < 2 ^ 64)]
  have hr := readPure_cost P (by includes) 8 s (by norm_num) hs
  rw [show (2 + 6 : ℕ) = 8 from rfl, limbs_of_lt (by norm_num : (8 : ℕ) < 2 ^ 64), Auto.Option.bind.c154.costEq P (by includes) _ _ _
    (fun r ↦ RunsApp.of_spec (readSizesLiteC.lam0.costSpec P (by includes) bytecode r))]
  cases hrp : readPure 8 s with
  | none => simp only; omega
  | some r =>
    obtain ⟨xs, s'⟩ := r
    obtain ⟨hxl, -, -⟩ := readPure_some 8 s xs s' hrp
    simp only [appCost_fn, List.length_cons, List.length_nil, List.cons_append, List.nil_append]
    rw [readSizesLiteC.lam0.costEq P (by includes)]
    simp only [FastLib.tablesLength]
    have hall := all_cost P (by includes) (fun value : E ↦ decide (value.limb 1 = 0 ∧ value.limb 2 = 0))
      (.closure readSizesLiteC.lam0.lam0.costIdx [])
      (fun v ↦ RunsApp.of_spec (readSizesLiteC.lam0.lam0.costSpec P (by includes) v)) 9 xs
      (fun v _ ↦ by
        rw [appCost_fn, List.length_nil, Nat.add_zero, List.nil_append, readSizesLiteC.lam0.lam0.costEq P (by includes)]
        split <;> omega)
    have hd := drop_cost_length P (by includes) 1 xs (by norm_num)
    have ht := take_cost_length P (by includes) 6 (List.drop 1 xs) (by norm_num)
    have hm := map_cost P (by includes) (fun value : E ↦ kToNat (value.limb 0))
      (.closure readSizesLiteC.lam0.lam1.costIdx [])
      (fun v ↦ RunsApp.of_spec (readSizesLiteC.lam0.lam1.costSpec P (by includes) v)) 2
      (List.take 6 (List.drop 1 xs))
      (fun v _ ↦ by rw [appCost_fn, List.length_nil, Nat.add_zero, List.nil_append, readSizesLiteC.lam0.lam1.costEq P (by includes)])
    have hrv := reverseAux_cost P (by includes) xs []
    have hbl := buildLayoutLite_cost P (by includes) bytecode (kToNat ((xs.headD 0).limb 0))
      (List.map (fun value ↦ kToNat (value.limb 0)) (List.take 6 (List.drop 1 xs))) hb
      (kToNat_lt _) (fun r hr' ↦ by
        obtain ⟨v, -, rfl⟩ := List.mem_map.1 hr'
        exact kToNat_lt _) (by simp)
    have hbind : ∀ o : Option LayoutLite, (∀ L, o = some L → L.stackLog ≤ 64) →
        machineCost P Auto.Option.bind.c154.costIdx [encodeValue o, MachineValue.closure readSizesLiteC.lam0.lam2.costIdx
          [encodeValue (xs, s'), encodeValue (kToNat ((xs.getLastD 0).limb 0))]] ≤ 34 := by
      intro o ho
      rw [Auto.Option.bind.c154.costEq P (by includes) _ _ _
        (fun L ↦ RunsApp.of_spec (readSizesLiteC.lam0.lam2.costSpec P (by includes) (xs, s') _ L))]
      cases o with
      | none => simp
      | some L =>
        have hL := ho L rfl
        simp only [appCost_fn, List.length_cons, List.length_nil, List.cons_append, List.nil_append]
        rw [readSizesLiteC.lam0.lam2.costEq P (by includes),
          limbs_of_lt (by omega : L.stackLog < 2 ^ 64), limbs_of_lt (by simp [Whir.minLogStack]),
          limbs_of_lt (by simp [Whir.maxLogStack])]
        simp only [max_self]
        split_ifs <;> omega
    have hbd := hbind (buildLayoutLite bytecode (kToNat ((xs.headD 0).limb 0))
      (List.map (fun value ↦ kToNat (value.limb 0)) (List.take 6 (List.drop 1 xs))))
      (fun L hL ↦ buildLayoutLite_stackLog hL)
    have hdl : (List.drop 1 xs).length = 7 := by simp [hxl]
    have htl : (List.take 6 (List.drop 1 xs)).length = 6 := by rw [List.length_take, hdl]; rfl
    rw [hxl] at hall hd hrv
    rw [hdl] at ht
    rw [htl] at hm
    have hk := kToNat_lt ((xs.getLastD 0).limb 0)
    rw [limbs_of_lt hk]
    obtain ⟨x0, t, rfl⟩ : ∃ x0 t, xs = x0 :: t := List.exists_cons_of_ne_nil (by
      intro h; rw [h] at hxl; simp at hxl)
    obtain ⟨y0, u, hy⟩ : ∃ y0 u, (x0 :: t).reverse = y0 :: u :=
      List.exists_cons_of_ne_nil (by simp)
    rw [hy]
    simp only
    split_ifs <;> omega

open LeanVM.Protocol.Compile in
theorem readSizesLite_some {bytecode : List K} {s s' : VerifierProgramState} {L : LayoutLite}
    {R : ℕ}
    (h : readSizesLite bytecode s = some ((L, R), s')) :
    R ≤ 4 ∧ L.stackLog ≤ 32 ∧ s'.roots = s.roots ∧
      (s.sponge.pending.length ≤ 4 → s'.sponge.pending.length ≤ 4) := by
  unfold readSizesLite at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨-, hroots, hpend⟩ := readPure_some _ s r.1 r.2 hr
  split_ifs at h
  dsimp only at h
  split_ifs at h with h2
  obtain ⟨L', -, hl⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at hl with h3
  simp only [Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hl
  simp only [LeanVM.Parameters.Whir.maxLogStack] at h3
  exact ⟨h2.2, h3.2, hroots, hpend⟩

/-- **The replay up to the stack's root** (`afterRootLite bytecode π`): at most
`8·|bytecode| + 977131026`, whatever the proof (it reads ten scalars of it). -/
theorem afterRootLite_cost (hP : Includes P afterRootLiteC.costDeps) (bytecode : List K)
    (π : LeanVM.Protocol.Compile.Proof) (hb : bytecode.length < 2 ^ 63) :
    machineCost P afterRootLiteC.costIdx [encodeValue bytecode, encodeValue π] ≤
      8 * bytecode.length + 977131026 := by
  rw [afterRootLiteC.costEq P hP, initialStateC.costEq P (by includes)]
  have hrs := readSizesLite_cost P (by includes) bytecode (initialState π) hb (by simp [initialState])
  rw [Auto.Option.bind.c154.costEq P (by includes) _ _ _
    (fun r ↦ RunsApp.of_spec (afterRootLiteC.lam0.costSpec P (by includes) r))]
  cases hr : readSizesLite bytecode (initialState π) with
  | none => simp only; omega
  | some r =>
    obtain ⟨⟨L, R⟩, s'⟩ := r
    obtain ⟨hR, hL, hroots, hpend⟩ := readSizesLite_some hr
    simp only [appCost_fn, List.length_nil, List.nil_append]
    rw [afterRootLiteC.lam0.costEq P (by includes)]
    dsimp only
    have hc := commitStackPure_cost P (by includes) L.stackLog R s' (by omega) (by omega)
      (hpend (by simp [initialState]))
    rw [hroots] at hc
    simp only [initialState, List.length_nil] at hc
    have hm : machineCost P Auto.Option.map.c194.costIdx [MachineValue.closure afterRootLiteC.lam0.lam0.costIdx
        [encodeValue ((L, R), s')], encodeValue (commitStackPure L.stackLog R s')] ≤ 16 := by
      rw [Auto.Option.map.c194.costEq P (by includes) _ _
        (fun t ↦ RunsApp.of_spec (afterRootLiteC.lam0.lam0.costSpec P (by includes) ((L, R), s') t))]
      cases commitStackPure L.stackLog R s' with
      | none => simp
      | some t =>
        simp only [appCost_fn, List.length_cons, List.length_nil, List.cons_append, List.nil_append]
        rw [afterRootLiteC.lam0.lam0.costEq P (by includes)]
    omega

end

end LeanVM.Cost.Bounds
