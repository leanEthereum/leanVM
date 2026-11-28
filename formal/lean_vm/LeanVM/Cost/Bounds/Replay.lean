module

public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Extractor.Replay
import all Statement.LeanVmVerifier
import all Statement.Field

/-!
# Bounds: lists, logarithms, the ladder and the stack's offsets

* the list functions compiled on word-sized lengths (`W = 2^64`): `set_cost`, `findIdxGo_cost`;
  `listFoldl_le'` (a fold with an invariant of the accumulator and the elements left);
* the ladder: `ladder_cost`, `ladder_head`;
* `bitLength_cost`, `log2Strict_cost`;
* `stackOffsets_cost`: the stack's offsets, its quadratic merge sort of the blocks dominating;
* the tables' heights (`heights_facts`).

The functions compiled on demand are named by the program's indices (`Auto.List.length.c21`, …):
when the chain of compiled modules changes, those names change, and this file's references with
them (a renaming, the proofs unchanged).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-! ## Lists -/

section Lists

variable {α : Type} [MachineEncoding α]

/-- `List.set`. -/
theorem set_cost (hP : Includes P Auto.List.set.c142.costDeps) (a : α) :
    ∀ (l : List α) (n : ℕ), n < 2 ^ 64 →
      machineCost P Auto.List.set.c142.costIdx [encodeValue l, encodeValue n, encodeValue a] ≤ 20 * l.length + 3
  | [], n, _ => by rw [Auto.List.set.c142.costEq_nil P hP]; omega
  | x :: l, 0, _ => by
    rw [Auto.List.set.c142.costEq_cons P hP]
    simp only [limbs_zero, List.length_cons, Nat.rec_zero]
    omega
  | x :: l, n + 1, h => by
    rw [Auto.List.set.c142.costEq_cons P hP, limbs_of_lt h]
    have := set_cost hP a l n (by omega)
    simp only [List.length_cons]
    omega

theorem findIdxGo_cost (hP : Includes P Auto.List.findIdx.go.c159.costDeps) (p : α → Bool)
    (pVal : MachineValue) (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : ℕ) :
    ∀ (l : List α) (n : ℕ), n + l.length < 2 ^ 64 → (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B) →
      machineCost P Auto.List.findIdx.go.c159.costIdx [pVal, encodeValue l, encodeValue n] ≤
        (B + 14) * l.length + 3
  | [], n, _, _ => by rw [Auto.List.findIdx.go.c159.costEq_nil P hP p pVal hp]; omega
  | x :: l, n, h, hB => by
    rw [Auto.List.findIdx.go.c159.costEq_cons P hP p pVal hp, limbs_of_lt (by simp at h; omega : n < 2 ^ 64),
      limbs_of_lt (by simp at h; omega : n + 1 < 2 ^ 64), max_self]
    have h1 := findIdxGo_cost hP p pVal hp B l (n + 1) (by simp at h; omega)
      fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons]
    split <;> nlinarith

end Lists

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
theorem levelsFrom_cost (hP : Includes P Auto.LeanVM.Parameters.Whir.levelsFrom.c145.costDeps) :
    ∀ (fuel rem pf pr red : ℕ), fuel < 2 ^ 64 → rem < 2 ^ 64 → pr + pf + 4 * fuel < 2 ^ 63 →
      red < 2 ^ 64 →
      machineCost P Auto.LeanVM.Parameters.Whir.levelsFrom.c145.costIdx [encodeValue fuel, encodeValue rem, encodeValue pf, encodeValue pr, encodeValue red] ≤
        44 * fuel + 15
  | 0, rem, pf, pr, red, _, _, _, _ => by rw [Auto.LeanVM.Parameters.Whir.levelsFrom.c145.costEq_zero P hP]; omega
  | fuel + 1, rem, pf, pr, red, hf, hr, hpp, hred => by
    rw [Auto.LeanVM.Parameters.Whir.levelsFrom.c145.costEq_succ P hP]
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
theorem queryTable_rows : ∀ r ∈ queryTable, r.length = 15 ∧ ∀ q ∈ r, q.length ≤ 6 := by
  decide +kernel

theorem getD_mem_or {β : Type} (l : List β) (i : ℕ) (d : β) : l.getD i d ∈ l ∨ l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact Or.inr rfl
  | some r => exact Or.inl (List.mem_of_getElem? h)

open LeanVM.Parameters.Whir in
theorem queryTable_row_length (i : ℕ) : (queryTable.getD i []).length ≤ 15 := by
  rcases getD_mem_or queryTable i [] with h | h
  · exact le_of_eq (queryTable_rows _ h).1
  · rw [h]; simp

open LeanVM.Parameters.Whir in
theorem queryTable_queries_length (i j : ℕ) : ((queryTable.getD i []).getD j []).length ≤ 6 := by
  rcases getD_mem_or (queryTable.getD i []) j [] with h | h
  · rcases getD_mem_or queryTable i [] with h' | h'
    · exact (queryTable_rows _ h').2 _ h
    · rw [h'] at h; simp at h
  · rw [h]; simp

open LeanVM.Parameters.Whir in
/-- The ladder of a shape: at most `3496`. -/
theorem ladder_cost (hP : Includes P ladderC.costDeps) (μ R : ℕ) (hμ : μ < 2 ^ 64)
    (hR : R < 2 ^ 64) : machineCost P ladderC.costIdx [encodeValue μ, encodeValue R] ≤ 3496 := by
  rw [ladderC.costEq P hP]
  simp only [minLogStack, maxLogStack, Admissible,
    limbs_of_lt hμ, limbs_of_lt hR, limbs_of_lt (by norm_num : (16 : ℕ) < 2 ^ 64),
    limbs_of_lt (by norm_num : (30 : ℕ) < 2 ^ 64), max_self]
  by_cases hadm : 16 ≤ μ ∧ μ ≤ 30 ∧ 1 ≤ R ∧ R ≤ 4
  · obtain ⟨h1, h2, h3, h4⟩ := hadm
    have hs := shape_cost P (by includes) μ R (by omega) (by omega)
    have hq : machineCost P queryTableC.costIdx [] = 1313 := queryTableC.costEq P (by includes)
    have hg1 := getD_cost P (by includes) queryTable (R - 1) [] (by omega)
    have hg2 := getD_cost P (by includes) (queryTable.getD (R - 1) []) (μ - 16) [] (by omega)
    have hl1 := length_cost P (by includes) (ladderShape μ R) (by
      have := length_levelsFrom μ (μ - initialFold) initialFold R initialReduction
      simp only [ladderShape, List.length_cons]; omega)
    have hl2 := length_cost P (by includes) ((queryTable.getD (R - 1) []).getD (μ - 16) []) (by
      have := queryTable_queries_length (R - 1) (μ - 16); omega)
    have hqt : queryTable.length = 4 := by decide +kernel
    have hrow := queryTable_row_length (R - 1)
    have hqq := queryTable_queries_length (R - 1) (μ - 16)
    have hsl : (ladderShape μ R).length ≤ 31 := by
      have := length_levelsFrom μ (μ - initialFold) initialFold R initialReduction
      simp only [ladderShape, List.length_cons]; omega
    have hz := listZipWith_le P (by includes) (fun (g : ℕ × ℕ) (q : ℕ) ↦ (⟨g.1, g.2, q⟩ : Level))
      (.closure ladderC.lam0.costIdx []) (fun g q ↦ RunsApp.of_spec (ladderC.lam0.costSpec P (by includes) g q))
      9 (ladderShape μ R) ((queryTable.getD (R - 1) []).getD (μ - 16) [])
      (fun g _ q _ ↦ by rw [appCost_fn, List.length_nil, Nat.add_zero, List.nil_append, ladderC.lam0.costEq P (by includes)])
    have hmin : min (ladderShape μ R).length ((queryTable.getD (R - 1) []).getD (μ - 16)
        []).length ≤ 6 :=
      le_trans (min_le_right _ _) hqq
    rw [limbs_of_lt (by omega : (ladderShape μ R).length < 2 ^ 64),
      limbs_of_lt (by omega : ((queryTable.getD (R - 1) []).getD (μ - 16) []).length < 2 ^ 64)]
    simp only [h1, h2, h3, h4, and_self, ↓reduceIte, max_self]
    rw [hqt] at hg1
    by_cases he : (ladderShape μ R).length = ((queryTable.getD (R - 1) []).getD (μ - 16) []).length
    · simp only [he, ↓reduceIte] at hz ⊢; omega
    · simp only [he, ↓reduceIte]; omega
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
  cases qs with
  | nil => simp at h
  | cons q qs =>
    simp only [List.zipWith_cons_cons, List.cons.injEq] at h
    rw [← h.1]
    exact ⟨rfl, rfl⟩

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

/-! ## The layout -/

open LeanVM.Protocol.Verifier in
theorem log2Ceil_le {r : ℕ} (h : r ≤ 2 ^ 30) : log2Ceil r ≤ 30 := by
  unfold log2Ceil bitLength
  split
  · omega
  · have : Nat.log2 (r - 1) < 30 := (Nat.log2_lt (by omega)).2 (by omega)
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
theorem heights_facts (rows : List ℕ) (hr : ∀ r ∈ rows, r ≤ 2 ^ 30) :
    (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors).length ≤ 6 ∧
    ∀ h ∈ List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors, h ≤ 30 := by
  have key : ∀ (rows floors : List ℕ), (∀ r ∈ rows, r ≤ 2 ^ 30) → (∀ f ∈ floors, f ≤ 30) →
      ∀ h ∈ List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows floors, h ≤ 30 := by
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

end

end LeanVM.Cost.Bounds
