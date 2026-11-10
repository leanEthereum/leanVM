module

public import LeanVM.Cost.Bounds.Step
public import LeanVM.Cost.Prices

/-!
# Bounds: the candidate runner

The runner (`Cost/Extractor/Runner.lean`): its tables built once per layout (`runnerTablesC`),
then per candidate stack the public boundary, the memory vector and the halting loop
(`runWithTablesC`). With `κ ≤ 32` the memory's and `ℓ ≤ 32` the bytecode's log-size, at most six
tables of at most `2^32` rows (the layout's checks in `buildLayoutLite`), and the step cap
`stepCapLite ≤ 2^35`:

* **`powTable_cost`**: the address table of `2^κ` words, `(74κ + 121)·2^κ + 17`; `pcFinal_cost`
  (`88 + 73ℓ`), `stepCapLite_cost` (`205`);
* **`runnerTables_cost`**: `(74κ + 121)·2^κ + (74ℓ + 121)·2^ℓ + 73ℓ + 357`; at `κ = ℓ = 32`,
  `4978·2^32 + 2693 ≈ 2^44.28`;
* `boundaryOfStack_cost` (`1429`), `memoryVec_cost` (`45·2^κ + 211`), **`haltLoopVec_cost`**
  (`(S + 41)·n + 19` for fuel `n`, `S` a step's price);
* **`runWithTables_cost`**: one stack, `(runnerStepPrice κ ℓ + 41)·stepCapLite + 45·2^κ + 1738`, with
  `runnerStepPrice κ ℓ = 366000 + 36ℓ + 936κ` (`stepVec_cost`, `Bounds/Step.lean`); at the worst shape
  **`runWithTables_cost_worst`**: `397145·2^35 + 45·2^32 + 1738 ≈ 2^53.60`;
* **`runner_cost`**: the tables and at most `1 + 2^12` stacks (the fast path's at most one,
  `FastInv`; the decoder's at most `2^12`, `decodeStacksDistinct_length_le_johnson`): at most
  `runnerBudget ≈ 2^65.60`.

Hypotheses: placements' offsets below `2^63` (`(layout.placement c).index < 2^63`, so an offset
plus an address of a memory of at most `2^62` words is a word) and the layout's
sizes above; `afterRootLite`'s layouts meet them (`afterRootLite_facts`, offsets below `2^48`) and
`runner_cost_afterRootLite` discharges them (`Bounds/Layout.lean`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction.Fast

public section

variable (P : LeanVM.Cost.MachineProgram)

/-! ## The runner's tables -/

section Tables
open Auto.LeanVM.Extraction.Fast

theorem length_powPairs : ∀ (n i : ℕ) (x : K), (powPairs n i x).length = n
  | 0, _, _ => rfl
  | n + 1, i, x => by rw [powPairs, List.length_cons, length_powPairs n]

theorem mem_powPairs : ∀ (n i : ℕ) (x : K) (e : ℕ × ℕ), e ∈ powPairs n i x →
    e.1 < 2 ^ 64 ∧ e.2 < i + n
  | 0, _, _, e, h => by simp [powPairs] at h
  | n + 1, i, x, e, h => by
    rw [powPairs, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨UInt64.toNat_lt _, by dsimp only; omega⟩
    · have := mem_powPairs n (i + 1) (x * LeanVM.Parameters.g) e h
      omega

theorem powTable_size (κ : ℕ) : (powTable κ).size = 2 ^ κ := by
  rw [powTable, List.size_toArray, List.length_mergeSort, length_powPairs]

/-- The address table of `2^κ` words, `κ ≤ 62`, is a table of word-sized pairs. -/
theorem wordTable_powTable {κ : ℕ} (hκ : κ ≤ 62) : WordTable (powTable κ) := by
  refine ⟨by rw [powTable_size]; exact Nat.pow_lt_pow_right (by norm_num) (by omega), ?_⟩
  intro e he
  rw [powTable, List.toList_toArray, List.mem_mergeSort] at he
  have := mem_powPairs _ _ _ e he
  have : 2 ^ κ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- The pairs `(lane of g^i, i)` (`powPairs.c241`): `52` per pair, `5` at the end. -/
theorem powPairs_cost (hP : Includes P powPairs.c241.costDeps) :
    ∀ (n i : ℕ) (x : K), n + i < 2 ^ 64 →
      machineCost P powPairs.c241.costIdx [encodeValue n, encodeValue i, encodeValue x] ≤ 52 * n + 5
  | 0, i, x, _ => by rw [powPairs.c241.costEq_zero P hP]
  | n + 1, i, x, h => by
    rw [powPairs.c241.costEq_succ P hP, limbs_of_lt (by omega : n + 1 < 2 ^ 64),
      limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt (by omega : i + 1 < 2 ^ 64)]
    have := powPairs_cost hP n (i + 1) (x * LeanVM.Parameters.g) (by omega)
    omega

/-- **The address table** (`powTable.c237`) of `2^κ` words: `2^κ` powers and their merge sort, at
most `(74κ + 121)·2^κ + 17`. -/
theorem powTable_cost (hP : Includes P powTable.c237.costDeps) (κ : ℕ) (hκ : κ ≤ 62) :
    machineCost P powTable.c237.costIdx [encodeValue κ] ≤ (74 * κ + 121) * 2 ^ κ + 17 := by
  rw [powTable.c237.costEq P hP, limbs_shift (by omega), limbs_of_lt (by omega : κ < 2 ^ 64),
    List.length_mergeSort, length_powPairs]
  have hN : 2 ^ κ < 2 ^ 63 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 := powPairs_cost P (by includes) (2 ^ κ) 0 1 (by omega)
  have h2 := mergeSortList_cost P (by includes) _ (.closure powTable.c237.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (powTable.c237.lam0.costSpec P (by includes) a b)) 7
    (fun e ↦ e.1 < 2 ^ 64)
    (fun a b ha hb ↦ by
      simp only [appCost_fn, List.nil_append, List.length_nil]
      rw [powTable.c237.lam0.costEq P (by includes), limbs_of_lt ha, limbs_of_lt hb]
      omega)
    (powPairs (2 ^ κ) 0 1) (by rw [length_powPairs]; exact hN)
    (fun e he ↦ (mem_powPairs _ _ _ e he).1)
  rw [length_powPairs, Nat.clog_pow 2 κ (by norm_num)] at h2
  have : (74 * κ + 121) * 2 ^ κ = 74 * (2 ^ κ * κ) + 121 * 2 ^ κ := by ring
  omega

/-- The final `pc` (`pcFinal.c242`): `g^(2^ℓ − 1)` by squaring, at most `88 + 73·ℓ`. -/
theorem pcFinal_cost (hP : Includes P Auto.LeanVM.Semantics.LeanIsaProgram.pcFinal.c242.costDeps)
    (prog : Semantics.LeanIsaProgram) :
    machineCost P Auto.LeanVM.Semantics.LeanIsaProgram.pcFinal.c242.costIdx [encodeValue prog] ≤
      88 + 73 * prog.logSize := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  rw [Auto.LeanVM.Semantics.LeanIsaProgram.pcFinal.c242.costEq P hP, limbs_shift (by omega),
    limbs_of_lt (by omega : prog.logSize < 2 ^ 64), limbs_two_pow (by omega)]
  have h2 : 2 ^ prog.logSize ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hls
  have := powSq_cost P (by includes) LeanVM.Parameters.g (2 ^ prog.logSize - 1) (by omega)
  have hlog : Nat.log2 (2 ^ prog.logSize - 1) ≤ prog.logSize := by
    rcases Nat.eq_zero_or_pos prog.logSize with h0 | hpos
    · rw [h0]; simp
    · have := log2_lt_of hpos (by have := Nat.one_le_two_pow (n := prog.logSize); omega :
        2 ^ prog.logSize - 1 < 2 ^ prog.logSize)
      omega
  have := Nat.mul_le_mul_left 73 (Nat.add_le_add_right hlog 1)
  omega

theorem sum_pow_le (l : List ℕ) (hl : ∀ h ∈ l, h ≤ 32) :
    (l.map (2 ^ ·)).sum ≤ l.length * 2 ^ 32 := by
  induction l with
  | nil => simp
  | cons h l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih (fun x hx ↦ hl x (by simp [hx]))
    have : 2 ^ h ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (hl h (by simp))
    nlinarith

theorem foldr_add_eq (l : List ℕ) : List.foldr (fun x1 x2 ↦ x1 + x2) 0 l = l.sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.foldr_cons, ih, List.sum_cons]

/-- `List.sum` (`sum.c244`) of word-sized partial sums: `14` per element, `7` at the end. -/
theorem listSum_cost (hP : Includes P Auto.List.sum.c244.costDeps) (l : List ℕ)
    (hl : l.sum < 2 ^ 64) : machineCost P Auto.List.sum.c244.costIdx [encodeValue l] ≤ 14 * l.length + 7 := by
  rw [Auto.List.sum.c244.costEq P hP]
  have hF : Includes P Auto.List.foldr.c23.costDeps := by includes
  have hf : ∀ a b : ℕ, RunsApp P (.closure Auto.List.sum.c244.lam0.costIdx []) [encodeValue a, encodeValue b] (encodeValue (a + b)) :=
    fun a b ↦ RunsApp.of_spec (Auto.List.sum.c244.lam0.costSpec P (by includes) a b)
  suffices ∀ l : List ℕ, l.sum < 2 ^ 64 → machineCost P Auto.List.foldr.c23.costIdx
      [.closure Auto.List.sum.c244.lam0.costIdx [], encodeValue 0, encodeValue l] ≤ 14 * l.length + 3 by
    have := this l hl; omega
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.foldr.c23.costEq_nil P hF _ _ hf]; omega
  | cons x l ih =>
    intro hs
    rw [Auto.List.foldr.c23.costEq_cons P hF _ _ hf, foldr_add_eq]
    simp only [List.sum_cons] at hs
    simp only [appCost_fn, List.nil_append, List.length_nil]
    rw [Auto.List.sum.c244.lam0.costEq P (by includes), limbs_of_lt (by omega : x < 2 ^ 64),
      limbs_of_lt (by omega : l.sum < 2 ^ 64), limbs_of_lt (by omega : x + l.sum < 2 ^ 64)]
    have := ih (by omega)
    simp only [List.length_cons, max_self]
    omega

/-- The step cap (`stepCapLite.c243`) of a layout of at most six tables of at most `2^32` rows, at
most `2^32` memory and bytecode words: at most `205`; the cap itself at most `2^35`. -/
theorem stepCapLite_cost (hP : Includes P stepCapLite.c243.costDeps) (layout : LayoutLite)
    (hm : layout.logMemory ≤ 32) (hb : layout.logBytecode ≤ 32)
    (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32) (hl : layout.tableLogHeights.length ≤ 6) :
    machineCost P stepCapLite.c243.costIdx [encodeValue layout] ≤ 205 := by
  rw [stepCapLite.c243.costEq P hP]
  have hs := sum_pow_le _ hh
  have hm2 : 2 ^ layout.logMemory ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hm
  have hb2 : 2 ^ layout.logBytecode ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hb
  have h1 := map_cost P (by includes) _ (.closure stepCapLite.c243.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (stepCapLite.c243.lam0.costSpec P (by includes) x)) 3
    layout.tableLogHeights (fun x hx ↦ by
      simp only [appCost_fn, List.nil_append, List.length_nil]
      have := hh x hx
      rw [stepCapLite.c243.lam0.costEq P (by includes), limbs_shift (by omega),
        limbs_of_lt (by omega : x < 2 ^ 64)]
      omega)
  have h2 := listSum_cost P (by includes) (layout.tableLogHeights.map (2 ^ ·)) (by nlinarith)
  rw [List.length_map] at h2
  rw [limbs_shift (by omega), limbs_of_lt (by omega : layout.logMemory < 2 ^ 64),
    limbs_shift (by omega), limbs_of_lt (by omega : layout.logBytecode < 2 ^ 64),
    limbs_of_lt (by nlinarith : (layout.tableLogHeights.map (2 ^ ·)).sum < 2 ^ 64),
    limbs_two_pow (by omega : layout.logMemory < 64), limbs_two_pow (by omega : layout.logBytecode < 64),
    limbs_of_lt (by nlinarith : (layout.tableLogHeights.map (2 ^ ·)).sum + 2 ^ layout.logMemory < 2 ^ 64),
    limbs_of_lt (by nlinarith : (layout.tableLogHeights.map (2 ^ ·)).sum + 2 ^ layout.logMemory +
      2 ^ layout.logBytecode < 2 ^ 64)]
  simp only [max_self]
  omega

theorem stepCapLite_le (layout : LayoutLite) (hm : layout.logMemory ≤ 32) (hb : layout.logBytecode ≤ 32)
    (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32) (hl : layout.tableLogHeights.length ≤ 6) :
    stepCapLite layout ≤ 2 ^ 35 := by
  have hs := sum_pow_le _ hh
  have hm2 : 2 ^ layout.logMemory ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hm
  have hb2 : 2 ^ layout.logBytecode ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hb
  unfold stepCapLite
  nlinarith

end Tables

/-- **The runner's tables** (`runnerTablesC`): the memory's and the code's address tables, the
final `pc`, the step cap: at most `(74·κ + 121)·2^κ + (74·ℓ + 121)·2^ℓ + 73·ℓ + 357`, `κ` the
memory's and `ℓ` the bytecode's log-size. -/
theorem runnerTables_cost (hP : Includes P runnerTablesC.costDeps) (prog : Semantics.LeanIsaProgram)
    (layout : LayoutLite) (hm : layout.logMemory ≤ 32) (hb : layout.logBytecode ≤ 32)
    (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32) (hl : layout.tableLogHeights.length ≤ 6) :
    machineCost P runnerTablesC.costIdx [encodeValue prog, encodeValue layout] ≤
      (74 * layout.logMemory + 121) * 2 ^ layout.logMemory +
        (74 * prog.logSize + 121) * 2 ^ prog.logSize + 73 * prog.logSize + 357 := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  rw [runnerTablesC.costEq P hP, limbs_of_lt (by omega : layout.logMemory < 2 ^ 64)]
  have h1 := powTable_cost P (by includes) layout.logMemory (by omega)
  have h2 := powTable_cost P (by includes) prog.logSize (by omega)
  have h3 := pcFinal_cost P (by includes) prog
  have h4 := stepCapLite_cost P (by includes) layout hm hb hh hl
  split_ifs <;> omega

/-! ## A stack -/

section Stack
open Auto.LeanVM.Extraction.Fast

theorem placementGetD_cost (hP : Includes P Auto.List.getD.c225.costDeps) (layout : LayoutLite)
    (c : ℕ) (hc : c ≤ 2) :
    machineCost P Auto.List.getD.c225.costIdx
      [encodeValue layout.placements, encodeValue c, encodeValue (none : Option LeanVM.Protocol.Verifier.Placement)] ≤ 47 := by
  have := getD_cost_idx P hP layout.placements c none (by omega)
  omega

/-- A word of the memory image (`memoryImageLite.c250`): two placements and two stack reads,
at most `202`. -/
theorem memoryImageLite_cost (hP : Includes P memoryImageLite.c250.costDeps) (layout : LayoutLite)
    (hm : layout.logMemory ≤ 62) (hidx : ∀ c, (layout.placement c).index < 2 ^ 63) {μ : ℕ}
    (q : Vector K (2 ^ μ)) (a : Fin (2 ^ layout.logMemory)) :
    machineCost P memoryImageLite.c250.costIdx [encodeValue layout, encodeValue μ, encodeValue q, encodeValue a] ≤ 202 := by
  rw [memoryImageLite.c250.costEq P hP]
  have hD : Includes P Auto.List.getD.c225.costDeps := by includes
  have h0 := placementGetD_cost P hD layout LeanVM.Protocol.Verifier.memory0 (by decide)
  have h1 := placementGetD_cost P hD layout LeanVM.Protocol.Verifier.memory1 (by decide)
  have ha : (a : ℕ) < 2 ^ 62 :=
    lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by norm_num) hm)
  have hix := fun c ↦ (hidx c).trans (by norm_num : 2 ^ 63 < 2 ^ 64)
  have hs := fun c ↦ (by have := hidx c; omega : (layout.placement c).index + (a : ℕ) < 2 ^ 64)
  rw [limbs_of_lt (by omega : (a : ℕ) < 2 ^ 64), limbs_of_lt (hix _), limbs_of_lt (hix _),
    limbs_of_lt (hs _), limbs_of_lt (hs _)]
  simp only [max_self]
  generalize layout.placements.getD LeanVM.Protocol.Verifier.memory0 none = o0
  generalize layout.placements.getD LeanVM.Protocol.Verifier.memory1 none = o1
  cases o0 <;> cases o1 <;> dsimp only <;> omega

theorem word01_cost (hP : Includes P Auto.LeanVM.Semantics.PublicInput.word0.c251.costDeps)
    (hP' : Includes P Auto.LeanVM.Semantics.PublicInput.word1.c253.costDeps) (input : PublicInput) :
    machineCost P Auto.LeanVM.Semantics.PublicInput.word0.c251.costIdx [encodeValue input] = 21 ∧
      machineCost P Auto.LeanVM.Semantics.PublicInput.word1.c253.costIdx [encodeValue input] = 21 := by
  have hF : Includes P Auto.Fin.ofNat.c252.costDeps := by includes
  rw [Auto.LeanVM.Semantics.PublicInput.word0.c251.costEq P hP,
    Auto.LeanVM.Semantics.PublicInput.word1.c253.costEq P hP']
  simp only [Auto.Fin.ofNat.c252.costEq P hF]
  constructor <;> cost_simp

/-- **The public boundary** (`boundaryOfStack.c249`): the memory's words `0` and `1` against the
public input, at most `1429`. -/
theorem boundaryOfStack_cost (hP : Includes P boundaryOfStack.c249.costDeps) (input : PublicInput)
    (layout : LayoutLite) (hm : layout.logMemory ≤ 62) (hidx : ∀ c, (layout.placement c).index < 2 ^ 63)
    {μ : ℕ} (q : Vector K (2 ^ μ)) :
    machineCost P boundaryOfStack.c249.costIdx [encodeValue input, encodeValue layout, encodeValue μ, encodeValue q] ≤ 1429 := by
  rw [boundaryOfStack.c249.costEq P hP]
  obtain ⟨hw0, hw1⟩ := word01_cost P (by includes) (by includes) input
  rw [hw0, hw1, limbs_of_lt (by omega : layout.logMemory < 2 ^ 64),
    limbs_of_lt (show minLogMem < 2 ^ 64 by unfold minLogMem; norm_num),
    limbs_of_lt (show maxLogMem < 2 ^ 64 by unfold maxLogMem; norm_num)]
  have hall := memoryImageLite_cost P (by includes) layout hm hidx q
  have h0 := hall ⟨0, Nat.two_pow_pos _⟩
  by_cases hc : minLogMem ≤ layout.logMemory ∧ layout.logMemory ≤ maxLogMem
  · have h1 := hall ⟨1, Nat.one_lt_two_pow (by unfold minLogMem at hc; omega)⟩
    split_ifs <;> omega
  · split_ifs <;> omega

/-- **The memory vector** (`memoryVec.c254`): two placements, then `2^κ` words of two limbs:
at most `45·2^κ + 211`. -/
theorem memoryVec_cost (hP : Includes P memoryVec.c254.costDeps) (layout : LayoutLite)
    (hm : layout.logMemory ≤ 62) (hidx : ∀ c, (layout.placement c).index < 2 ^ 63) {μ : ℕ}
    (q : Vector K (2 ^ μ)) :
    machineCost P memoryVec.c254.costIdx [encodeValue layout, encodeValue μ, encodeValue q] ≤ 45 * 2 ^ layout.logMemory + 211 := by
  rw [memoryVec.c254.costEq P hP, ofFnFrom_length]
  have hD : Includes P Auto.List.getD.c225.costDeps := by includes
  have h0 := placementGetD_cost P hD layout LeanVM.Protocol.Verifier.memory0 (by decide)
  have h1 := placementGetD_cost P hD layout LeanVM.Protocol.Verifier.memory1 (by decide)
  have hN : 2 ^ layout.logMemory < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hN2 : 2 ^ layout.logMemory ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hm
  have hof := ofFnFrom_cost P (by includes) hN _
    (.closure memoryVec.c254.lam0.costIdx [encodeValue layout, encodeValue μ, encodeValue q,
      encodeValue (layout.placement LeanVM.Protocol.Verifier.memory0).index,
      encodeValue (layout.placement LeanVM.Protocol.Verifier.memory1).index])
    (fun i ↦ RunsApp.of_spec (memoryVec.c254.lam0.costSpec P (by includes) layout q _ _ i)) 28
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have hi := i.isLt
      have hs := fun c ↦ (by have := hidx c; omega : (layout.placement c).index + (i : ℕ) < 2 ^ 64)
      have hix := fun c ↦ (hidx c).trans (by norm_num : 2 ^ 63 < 2 ^ 64)
      rw [memoryVec.c254.lam0.costEq P (by includes), limbs_of_lt (lt_trans i.isLt hN),
        limbs_of_lt (hix _), limbs_of_lt (hix _), limbs_of_lt (hs _), limbs_of_lt (hs _)]
      simp only [max_self]
      omega) 0 (Nat.zero_le _)
  rw [limbs_shift (by omega), limbs_of_lt (by omega : layout.logMemory < 2 ^ 64)]
  simp only [Nat.sub_zero] at hof
  generalize layout.placements.getD LeanVM.Protocol.Verifier.memory0 none = o0
  generalize layout.placements.getD LeanVM.Protocol.Verifier.memory1 none = o1
  cases o0 <;> cases o1 <;> dsimp only <;> omega

end Stack


/-! ## The halting loop and a stack -/

section Loop
open Auto.LeanVM.Extraction.Fast

/-- **The halting loop** (`haltLoopVec.c257`): `n` steps at most, each one step's price (at most
`S`) and `41`; `19` at the end. The step counter `a` stays a word. -/
theorem haltLoopVec_cost (hP : Includes P haltLoopVec.c257.costDeps)
    (memT codeT : Array (ℕ × ℕ)) (prog : LeanVM.Semantics.LeanIsaProgram) {κ : ℕ} (mem : Vector E
        (2 ^ κ))
    (fin : Registers K) (S : ℕ)
    (hS : ∀ r : Registers K, machineCost P Auto.LeanVM.Extraction.Fast.stepVec.c258.costIdx
      [encodeValue memT, encodeValue codeT, encodeValue prog, encodeValue κ, encodeValue mem, encodeValue r] ≤ S) :
    ∀ (n a : ℕ) (r : Registers K), n + a < 2 ^ 64 →
      machineCost P Auto.LeanVM.Extraction.Fast.haltLoopVec.c257.costIdx
        [encodeValue memT, encodeValue codeT, encodeValue prog, encodeValue κ, encodeValue mem, encodeValue fin, encodeValue n, encodeValue a, encodeValue r] ≤
        (S + 41) * n + 19 := by
  intro n
  induction n with
  | zero =>
    intro a r _
    rw [Auto.LeanVM.Extraction.Fast.haltLoopVec.c257.costEq_zero P hP]
    split_ifs <;> omega
  | succ n ih =>
    intro a r hna
    rw [Auto.LeanVM.Extraction.Fast.haltLoopVec.c257.costEq_succ P hP,
      limbs_of_lt (by omega : n + 1 < 2 ^ 64)]
    have hs := hS r
    generalize hst : stepVec memT codeT prog mem r = o
    cases o with
    | none => split_ifs <;> (try dsimp only) <;> nlinarith
    | some r' =>
      have := ih (a + 1) r' (by omega)
      rw [limbs_of_lt (by omega : a < 2 ^ 64), limbs_of_lt (by omega : a + 1 < 2 ^ 64)]
      simp only [max_self]
      split_ifs <;> nlinarith


/-- **A stack's execution** (`candidateExecutionVec.c248`): the boundary, then the memory vector
and the halting loop of fuel `cap`: at most `(S + 41)·cap + 45·2^κ + 1712`. -/
theorem candidateExecutionVec_cost (hP : Includes P candidateExecutionVec.c248.costDeps)
    (memT codeT : Array (ℕ × ℕ)) (prog : Semantics.LeanIsaProgram) (input : PublicInput) (layout : LayoutLite)
    (hm : layout.logMemory ≤ 62) (hidx : ∀ c, (layout.placement c).index < 2 ^ 63)
    (fin : Registers K) (cap : ℕ) (hcap : cap < 2 ^ 64) {μ : ℕ} (q : Vector K (2 ^ μ)) (S : ℕ)
    (hS : ∀ r : Registers K, machineCost P stepVec.c258.costIdx
      [encodeValue memT, encodeValue codeT, encodeValue prog, encodeValue layout.logMemory, encodeValue (memoryVec layout q), encodeValue r] ≤ S) :
    machineCost P candidateExecutionVec.c248.costIdx
        [encodeValue memT, encodeValue codeT, encodeValue prog, encodeValue input, encodeValue layout, encodeValue fin, encodeValue cap, encodeValue μ, encodeValue q] ≤
      (S + 41) * cap + 45 * 2 ^ layout.logMemory + 1712 := by
  rw [candidateExecutionVec.c248.costEq P hP]
  have h1 := boundaryOfStack_cost P (by includes) input layout hm hidx q
  have h2 := memoryVec_cost P (by includes) layout hm hidx q
  have h3 := haltLoopVec_cost P (by includes) memT codeT prog (memoryVec layout q) fin S hS cap 0
    Registers.initial (by omega)
  have h4 := optionMap_cost P (by includes) _
    (.closure candidateExecutionVec.c248.lam0.costIdx [encodeValue prog, encodeValue layout, encodeValue (memoryVec layout q)])
    (fun n ↦ RunsApp.of_spec (candidateExecutionVec.c248.lam0.costSpec P (by includes) prog layout _ n)) 11
    (haltLoopVec memT codeT prog (memoryVec layout q) fin cap 0 Registers.initial) (fun n _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [candidateExecutionVec.c248.lam0.costEq P (by includes)])
  split_ifs <;> omega

/-- **One stack, from the runner's tables** (`runWithTablesC`): at most
`(runnerStepPrice κ ℓ + 41)·stepCapLite + 45·2^κ + 1738`. -/
theorem runWithTables_cost (hP : Includes P runWithTablesC.costDeps) (prog :
    Semantics.LeanIsaProgram)
    (input : PublicInput) (layout : LayoutLite) (hm : layout.logMemory ≤ 32)
    (hb : layout.logBytecode ≤ 32) (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32)
    (hl : layout.tableLogHeights.length ≤ 6) (hidx : ∀ c, (layout.placement c).index < 2 ^ 63)
    (q : Vector K (2 ^ layout.stackLog)) :
    machineCost P runWithTablesC.costIdx
        [encodeValue (runnerTables prog layout), encodeValue prog, encodeValue input, encodeValue layout, encodeValue q] ≤
      (runnerStepPrice layout.logMemory prog.logSize + 41) * stepCapLite layout +
        45 * 2 ^ layout.logMemory + 1738 := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  have hcap := stepCapLite_le layout hm hb hh hl
  unfold runnerTables
  simp only [show layout.logMemory < 64 by omega, ↓reduceIte]
  rw [runWithTablesC.costEq_some P hP]
  dsimp only
  have := candidateExecutionVec_cost P (by includes) (powTable layout.logMemory) (powTable prog.logSize)
    prog input layout (by omega) hidx (Registers.final prog) (stepCapLite layout)
    (lt_of_le_of_lt hcap (by norm_num)) q (runnerStepPrice layout.logMemory prog.logSize)
    (fun r ↦ by
      have := stepVec_cost P (by includes) (powTable layout.logMemory) (powTable prog.logSize)
        (wordTable_powTable (by omega)) (wordTable_powTable (by omega)) prog (by omega)
        (memoryVec layout q) r
      rw [powTable_size, powTable_size, Nat.log2_two_pow, Nat.log2_two_pow] at this
      unfold runnerStepPrice
      omega)
  omega

/-- **One stack at the worst shape** (`κ, ℓ ≤ 32`, at most six tables of at most `2^32` rows):
at most `397145·2^35 + 45·2^32 + 1738` (`≈ 2^53.60`). -/
theorem runWithTables_cost_worst (hP : Includes P runWithTablesC.costDeps) (prog : Semantics.LeanIsaProgram)
    (input : PublicInput) (layout : LayoutLite) (hm : layout.logMemory ≤ 32)
    (hb : layout.logBytecode ≤ 32) (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32)
    (hl : layout.tableLogHeights.length ≤ 6) (hidx : ∀ c, (layout.placement c).index < 2 ^ 63)
    (q : Vector K (2 ^ layout.stackLog)) :
    machineCost P runWithTablesC.costIdx
        [encodeValue (runnerTables prog layout), encodeValue prog, encodeValue input, encodeValue layout, encodeValue q] ≤
      397145 * 2 ^ 35 + 45 * 2 ^ 32 + 1738 := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  have h := runWithTables_cost P hP prog input layout hm hb hh hl hidx q
  have hcap := stepCapLite_le layout hm hb hh hl
  have hS : runnerStepPrice layout.logMemory prog.logSize + 41 ≤ 397145 := by unfold runnerStepPrice; omega
  have h2 : 2 ^ layout.logMemory ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hm
  have := Nat.mul_le_mul hS hcap
  omega

end Loop

/-! ## The runner -/

/-- The runner's budget at the worst shape: the tables, and `1 + 2^12` stacks. -/
@[expose] def runnerBudget : ℕ :=
  (4978 * 2 ^ 32 + 2693) + (2 ^ 12 + 1) * (397145 * 2 ^ 35 + 45 * 2 ^ 32 + 1738)

/-- **The runner** at the worst shape: its tables once, and at most `1 + 2^12` candidate stacks
(at most one from the fast path, at most `2^12` from the decoder): at most `runnerBudget`
(`≈ 2^65.60`). -/
theorem runner_cost (hT : Includes P runnerTablesC.costDeps) (hW : Includes P runWithTablesC.costDeps)
    (prog : Semantics.LeanIsaProgram) (input : PublicInput) (layout : LayoutLite)
    (hm : layout.logMemory ≤ 32) (hb : layout.logBytecode ≤ 32)
    (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32) (hl : layout.tableLogHeights.length ≤ 6)
    (hidx : ∀ c, (layout.placement c).index < 2 ^ 63) (qs : List (Vector K (2 ^ layout.stackLog)))
    (hqs : qs.length ≤ 2 ^ 12 + 1) :
    machineCost P runnerTablesC.costIdx [encodeValue prog, encodeValue layout] +
        (qs.map fun q ↦ machineCost P runWithTablesC.costIdx
          [encodeValue (runnerTables prog layout), encodeValue prog, encodeValue input, encodeValue layout, encodeValue q]).sum ≤
      runnerBudget := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  have h1 := runnerTables_cost P hT prog layout hm hb hh hl
  have hm2 : (74 * layout.logMemory + 121) * 2 ^ layout.logMemory ≤ (74 * 32 + 121) * 2 ^ 32 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hm)
  have hl2 : (74 * prog.logSize + 121) * 2 ^ prog.logSize ≤ (74 * 32 + 121) * 2 ^ 32 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hls)
  have h2 : (qs.map fun q ↦ machineCost P runWithTablesC.costIdx
      [encodeValue (runnerTables prog layout), encodeValue prog, encodeValue input, encodeValue layout, encodeValue q]).sum ≤
      qs.length * (397145 * 2 ^ 35 + 45 * 2 ^ 32 + 1738) := by
    have := List.sum_le_length_nsmul (qs.map fun q ↦ machineCost P runWithTablesC.costIdx
      [encodeValue (runnerTables prog layout), encodeValue prog, encodeValue input, encodeValue layout, encodeValue q])
      (397145 * 2 ^ 35 + 45 * 2 ^ 32 + 1738) (fun x hx ↦ by
        obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
        exact runWithTables_cost_worst P hW prog input layout hm hb hh hl hidx q)
    simpa using this
  have h3 := Nat.mul_le_mul_right (397145 * 2 ^ 35 + 45 * 2 ^ 32 + 1738) hqs
  unfold runnerBudget
  omega

end

end LeanVM.Cost.Bounds
