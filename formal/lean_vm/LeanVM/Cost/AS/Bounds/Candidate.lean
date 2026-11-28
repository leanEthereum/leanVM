module

public import LeanVM.Cost.AS.Bounds.Facts
public import LeanVM.Cost.AS.Bounds.StepUp
import all LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Protocol.Relation.Link.Rel
import all Statement.Verifier.Link
import all Statement.Verifier.Layout

/-!
# Bounds: the candidate execution

The candidate (`candidateLC`, `candidateL` with its memory as a vector) reads the memory's
`2^logMemory` words off the stack (two cells each, `columnRowL_cost`) and the cycle the run halts
at (`firstFinalL`): every row of every table, its state's three cells and, where it is final, its
cycle pointer decoded (`ptrIndex_cost`, over chunks of at most `24` pieces of at most `6` bits:
`chunksNew_ok`, every width `Chunks.new` takes by the kernel). **`candidateL_cost`**: at most
`2^53` at every layout with `LayoutFacts`, given the link's chunks' price (`chunksL`, at most
`C`).
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Extraction.AS LeanVM.Protocol.EndToEnd.Sound

public section

variable (P : MachineProgram)

/-! ## The chunks -/

/-- The chunks' sizes the decoder's price assumes. -/
@[expose] def chunksSmall (c : Chunks) : Bool :=
  decide (c.width ≤ 24) && decide (c.widths.length ≤ 24) && c.widths.all (· ≤ 6) &&
    c.indexShifts.all (· ≤ 64) && c.wordShifts.all (· ≤ 64)

theorem chunksNew_small_all : (List.range 25).all (fun w ↦ match Chunks.new w with
    | some c => chunksSmall c
    | none => true) = true := by
  decide +kernel

/-- The sizes of the chunks `Chunks.new` returns. -/
structure ChunksOk (c : Chunks) : Prop where
  width : c.width ≤ 24
  len : c.widths.length ≤ 24
  widths : ∀ w ∈ c.widths, w ≤ 6
  idx : ∀ s ∈ c.indexShifts, s ≤ 64
  word : ∀ s ∈ c.wordShifts, s ≤ 64

theorem chunksNew_ok {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) : ChunksOk c := by
  have hs : chunksSmall c = true := by
    by_cases hw : w < 25
    · have := List.all_eq_true.1 chunksNew_small_all w (List.mem_range.2 hw)
      rw [h] at this
      exact this
    · unfold Chunks.new at h
      split_ifs at h with hc'
      exact absurd hc'.2 (by unfold maxPointerWidth; omega)
  simp only [chunksSmall, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hs
  exact ⟨h1, h2, fun x hx ↦ by simpa using h3 x hx, fun x hx ↦ by simpa using h4 x hx,
    fun x hx ↦ by simpa using h5 x hx⟩

theorem getD_le_of' (l : List ℕ) (i M : ℕ) (h : ∀ x ∈ l, x ≤ M) : l.getD i 0 ≤ M := by
  rcases getD_mem_or l i 0 with h' | h'
  · exact h _ h'
  · rw [h']; omega

theorem chunkPos_lt (chunks : Chunks) (w : K) (i : ℕ) :
    Relation.chunkPos chunks w i < 2 ^ chunks.widths.getD i 0 := by
  unfold Relation.chunkPos
  cases hf : List.find? (fun v ↦ w.toBitVec.getLsbD (chunks.wordShifts.getD i 0 + v))
    (List.range (2 ^ chunks.widths.getD i 0)) with
  | none => exact Nat.two_pow_pos _
  | some v => exact List.mem_range.1 (List.mem_of_find?_eq_some hf)

/-- `List.find?` (`find?.c385`): `11` per element and the predicate's price, `3`. -/
theorem findOpt_cost (hP : Includes P Auto.List.find?.c385.costDeps) {α : Type} [MachineEncoding α]
    (p : α → Bool) (pVal : MachineValue) (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a)))
    (B : ℕ) : ∀ l : List α, (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B) →
      machineCost P Auto.List.find?.c385.costIdx [pVal, encodeValue l] ≤ (B + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.find?.c385.costEq_nil P hP p pVal hp]; omega
  | cons a l ih =>
    intro hB
    rw [Auto.List.find?.c385.costEq_cons P hP p pVal hp]
    have h1 := ih fun a' ha ↦ hB a' (by simp [ha])
    have h2 := hB a (by simp)
    simp only [List.length_cons]
    generalize p a = b
    cases b <;> dsimp only <;> nlinarith

theorem foldr_add_le (M : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ M) → l.foldr (· + ·) 0 ≤ M * l.length
  | [], _ => by simp
  | x :: l, h => by
    have := foldr_add_le M l fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    have := h x List.mem_cons_self
    simp only [List.foldr_cons, List.length_cons, Nat.mul_succ]
    omega

/-- **A pointer word decoded** (`ptrIndex.c469`), chunks within `ChunksOk`: at most `700000`. -/
theorem ptrIndex_cost (hP : Includes P Auto.LeanVM.Protocol.Relation.ptrIndex.c469.costDeps)
    (chunks : Chunks) (hc : ChunksOk chunks) (w : K) :
    machineCost P Auto.LeanVM.Protocol.Relation.ptrIndex.c469.costIdx [encodeValue chunks, encodeValue w] ≤
      700000 := by
  have hd : chunks.d ≤ 24 := hc.len
  have hwi : ∀ i, chunks.widths.getD i 0 ≤ 6 := fun i ↦ getD_le_of' _ i 6 hc.widths
  have hii : ∀ i, chunks.indexShifts.getD i 0 ≤ 64 := fun i ↦ getD_le_of' _ i 64 hc.idx
  have hwo : ∀ i, chunks.wordShifts.getD i 0 ≤ 64 := fun i ↦ getD_le_of' _ i 64 hc.word
  have hpow : ∀ i, 2 ^ chunks.widths.getD i 0 ≤ 64 := fun i ↦
    (Nat.pow_le_pow_right (by norm_num) (hwi i)).trans (by norm_num)
  have hpowi : ∀ i, 2 ^ chunks.indexShifts.getD i 0 ≤ 2 ^ 64 := fun i ↦
    Nat.pow_le_pow_right (by norm_num) (hii i)
  have hterm : ∀ i, Relation.chunkPos chunks w i * 2 ^ chunks.indexShifts.getD i 0 ≤ 64 * 2 ^ 64 :=
    fun i ↦ Nat.mul_le_mul (by have := chunkPos_lt chunks w i; have := hpow i; omega) (hpowi i)
  rw [Auto.LeanVM.Protocol.Relation.ptrIndex.c469.costEq P hP]
  have hwl : chunks.widths.length ≤ 24 := hc.len
  have h1 := length_cost P (by includes) chunks.widths (by omega)
  have h2 := rangeLoop_cost P (by includes) chunks.d [] (by omega)
  have h3 := map_cost P (by includes) _
    (.closure Auto.LeanVM.Protocol.Relation.ptrIndex.c469.lam0.costIdx [encodeValue chunks, encodeValue w])
    (fun i ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Relation.ptrIndex.c469.lam0.costSpec P (by includes)
      chunks w i)) 28100 (List.range chunks.d) (fun i hi ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Auto.LeanVM.Protocol.Relation.ptrIndex.c469.lam0.costEq P (by includes)]
      have hi' : i < 24 := by have := List.mem_range.1 hi; omega
      have e1 := getD_cost_idx P (by includes) chunks.widths i 0 (by omega)
      have e2 := getD_cost_idx P (by includes) chunks.indexShifts i 0 (by omega)
      have e3 := rangeLoop_cost P (by includes) (2 ^ chunks.widths.getD i 0) [] (by have := hpow i; omega)
      have e4 := findOpt_cost P (by includes) _
        (.closure Auto.LeanVM.Protocol.Relation.ptrIndex.c469.lam0.lam0.costIdx
          [encodeValue chunks, encodeValue i, encodeValue w.lane.toNat])
        (fun v ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Relation.ptrIndex.c469.lam0.lam0.costSpec P
          (by includes) chunks i w.lane.toNat v)) 400
        (List.range (2 ^ chunks.widths.getD i 0)) (fun v hv ↦ by
          have hv' : v < 64 := by have := List.mem_range.1 hv; have := hpow i; omega
          rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
            Auto.LeanVM.Protocol.Relation.ptrIndex.c469.lam0.lam0.costEq P (by includes)]
          have g1 := getD_cost_idx P (by includes) chunks.wordShifts i 0 (by omega)
          have hl : w.lane.toNat < 2 ^ 64 := UInt64.toNat_lt _
          have := hwo i
          have l1 := limbs_le_two (show chunks.wordShifts.getD i 0 + v < 2 ^ 128 by omega)
          have l2 := limbs_le_two (show chunks.wordShifts.getD i 0 < 2 ^ 128 by omega)
          have l3 := limbs_le_two (show v < 2 ^ 128 by omega)
          have l4 := limbs_le_two (show w.lane.toNat < 2 ^ 128 by omega)
          have l5 := limbs_le_two (show w.lane.toNat >>> (chunks.wordShifts.getD i 0 + v) < 2 ^ 128 by
            have := Nat.shiftRight_le w.lane.toNat (chunks.wordShifts.getD i 0 + v); omega)
          have l6 := limbs_le_two (show 1 &&& w.lane.toNat >>> (chunks.wordShifts.getD i 0 + v) < 2 ^ 128 by
            have := Nat.and_le_left (n := 1) (m := w.lane.toNat >>> (chunks.wordShifts.getD i 0 + v))
            omega)
          simp only [List.length_cons, List.length_nil]
          omega)
      have hl : (List.range (2 ^ chunks.widths.getD i 0)).length ≤ 64 := by
        rw [List.length_range]; exact hpow i
      have e5 := Nat.mul_le_mul_left (400 + 11) hl
      have hcp := chunkPos_lt chunks w i
      have l1 := limbs_le_two (show 1 <<< chunks.widths.getD i 0 < 2 ^ 128 by
        rw [Nat.shiftLeft_eq, one_mul]; have := hpow i; omega)
      have l2 := limbs_le_two (show chunks.widths.getD i 0 < 2 ^ 128 by have := hwi i; omega)
      have l3 := limbs_le_two (show 1 <<< chunks.indexShifts.getD i 0 < 2 ^ 128 by
        rw [Nat.shiftLeft_eq, one_mul]; have := hpowi i; omega)
      have l4 := limbs_le_two (show chunks.indexShifts.getD i 0 < 2 ^ 128 by have := hii i; omega)
      have l5 := limbs_le_two (show Relation.chunkPos chunks w i * 2 ^ chunks.indexShifts.getD i 0 <
        2 ^ 128 by have := hterm i; omega)
      have l6 := limbs_le_two (show Relation.chunkPos chunks w i < 2 ^ 128 by have := hpow i; omega)
      have l7 := limbs_le_two (show 2 ^ chunks.indexShifts.getD i 0 < 2 ^ 128 by have := hpowi i; omega)
      have l8 := Nat.mul_le_mul l6 l7
      have hpi := hpow i
      simp only [List.length_cons, List.length_nil]
      rcases List.find? (fun v ↦ 1 &&& w.lane.toNat >>> (chunks.wordShifts.getD i 0 + v) != 0)
        (List.range (2 ^ chunks.widths.getD i 0)) with _ | v <;> dsimp only <;> omega)
  have h4 := foldrSuffix_cost P (by includes) (· + ·)
    (.closure Auto.List.sum.c405.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (Auto.List.sum.c405.lam0.costSpec P (by includes) a b)) 10 0
    ((List.range chunks.d).map fun i ↦ Relation.chunkPos chunks w i * 2 ^ chunks.indexShifts.getD i 0)
    (fun x tl hs ↦ by
      rw [appCost_fn, List.nil_append, Auto.List.sum.c405.lam0.costEq P (by includes)]
      have hx : x ≤ 64 * 2 ^ 64 := by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 (hs.subset List.mem_cons_self)
        exact hterm i
      have htl := foldr_add_le (64 * 2 ^ 64) tl fun y hy ↦ by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 (hs.subset (List.mem_cons_of_mem _ hy))
        exact hterm i
      have hlen : tl.length ≤ 24 := by
        have := hs.length_le
        simp only [List.length_cons, List.length_map, List.length_range] at this
        omega
      have hm := Nat.mul_le_mul_left (64 * 2 ^ 64) hlen
      have l1 := limbs_le_two (show x + tl.foldr (· + ·) 0 < 2 ^ 128 by omega)
      have l2 := limbs_le_two (show x < 2 ^ 128 by omega)
      have l3 := limbs_le_two (show tl.foldr (· + ·) 0 < 2 ^ 128 by omega)
      simp only [List.length_nil]
      omega)
  rw [Auto.List.sum.c405.costEq P (by includes)]
  simp only [List.length_map, List.length_range] at h3 h4
  have m1 := Nat.mul_le_mul_left (28100 + 13) hd
  have m2 := Nat.mul_le_mul_left (10 + 11) hd
  have hdw : chunks.d = chunks.widths.length := rfl
  omega

/-! ## The stack's cells -/

/-- **A stack cell of a global column** (`columnRowL.c460`). -/
theorem columnRowL_cost (hP : Includes P Auto.LeanVM.Extraction.AS.columnRowL.c460.costDeps)
    (lay : LayoutLite) (hF : LayoutFacts lay) {μ : ℕ} (q : Column μ) (c i : ℕ) (hc : c < 2 ^ 60)
    (hi : i < 2 ^ 60) :
    machineCost P Auto.LeanVM.Extraction.AS.columnRowL.c460.costIdx
      [encodeValue lay, encodeValue μ, encodeValue q, encodeValue c, encodeValue i] ≤ 15 * c + 50 := by
  rw [Auto.LeanVM.Extraction.AS.columnRowL.c460.costEq P hP]
  have h1 := getD_cost_idx P (by includes) lay.placements c none (by omega)
  rcases hg : lay.placements.getD c none with _ | p
  · dsimp only; omega
  · dsimp only
    rw [Auto.LeanVM.Protocol.Relation.cell.c461.costEq P (by includes)]
    have hp : p.index < 2 ^ 48 := by
      rcases getD_mem_or lay.placements c none with h | h
      · rw [hg] at h; exact hF.index_lt _ h p rfl
      · rw [hg] at h; cases h
    rw [limbs_of_lt (by omega : p.index + i < 2 ^ 64), limbs_of_lt (by omega : p.index < 2 ^ 64),
      limbs_of_lt (by omega : i < 2 ^ 64)]
    omega

theorem globalColumnBases_le (t : ℕ) : globalColumnBases.getD t 0 ≤ 48 := by
  rw [globalColumnBasesLit]
  exact getD_le_of' _ t 48 (by decide)

/-- **A table's cell** (`tableWordL.c467`), at a local column below `70`. -/
theorem tableWordL_cost (hP : Includes P Auto.LeanVM.Extraction.AS.tableWordL.c467.costDeps)
    (lay : LayoutLite) (hF : LayoutFacts lay) {μ : ℕ} (q : Column μ) (t c u : ℕ) (ht : t < 6)
    (hc : c < 70) (hu : u < 2 ^ 60) :
    machineCost P Auto.LeanVM.Extraction.AS.tableWordL.c467.costIdx
      [encodeValue lay, encodeValue μ, encodeValue q, encodeValue t, encodeValue c, encodeValue u] ≤
        2000 := by
  rw [Auto.LeanVM.Extraction.AS.tableWordL.c467.costEq P hP]
  have hb := globalColumnBases_le t
  have h1 := getD_cost P (by includes) globalColumnBases t 0 (by omega)
  have hl : globalColumnBases.length = 6 := by rw [globalColumnBasesLit]; rfl
  have h2 := columnRowL_cost P (by includes) lay hF q (globalColumnBases.getD t 0 + c) u (by omega) hu
  rw [limbs_of_lt (by omega : globalColumnBases.getD t 0 + c < 2 ^ 64),
    limbs_of_lt (by omega : globalColumnBases.getD t 0 < 2 ^ 64), limbs_of_lt (by omega : c < 2 ^ 64)]
  omega

/-! ## The final cycle -/

theorem stateCyclesL_le (t : ℕ) : stateCyclesL.getD t 0 ≤ 67 :=
  getD_le_of' _ t 67 (by decide)

/-- **A row's final cycle, if final** (`finalCyclesL.c464.lam0.lam0`): at most `720000`. -/
theorem finalRow_cost (hP : Includes P Auto.LeanVM.Extraction.AS.finalCyclesL.c464.lam0.lam0.costDeps)
    (lay : LayoutLite) (hF : LayoutFacts lay) {μ : ℕ} (q : Column μ) (chunks : Chunks)
    (hc : ChunksOk chunks) (t u : ℕ) (ht : t < 6) (hu : u < 2 ^ 60) :
    machineCost P Auto.LeanVM.Extraction.AS.finalCyclesL.c464.lam0.lam0.costIdx
      [encodeValue lay, encodeValue μ, encodeValue q, encodeValue chunks, encodeValue t, encodeValue u] ≤
        720000 := by
  rw [Auto.LeanVM.Extraction.AS.finalCyclesL.c464.lam0.lam0.costEq P hP,
    Auto.LeanVM.Extraction.AS.stateCyclesL.c472.costEq P (by includes)]
  have hb := hF.logBytecode_le
  have hp : 2 ^ lay.logBytecode ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hb
  have hpw : 2 ^ chunks.width ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) hc.width
  have w0 := tableWordL_cost P (by includes) lay hF q t 0 u ht (by omega) hu
  have w1 := tableWordL_cost P (by includes) lay hF q t 1 u ht (by omega) hu
  have w2 := tableWordL_cost P (by includes) lay hF q t (stateCyclesL.getD t 0) u ht
    (by have := stateCyclesL_le t; omega) hu
  have g1 := getD_cost P (by includes) stateCyclesL t 0 (by omega)
  have hsl : stateCyclesL.length = 6 := rfl
  have pw := powSq_cost P (by includes) g (2 ^ lay.logBytecode - 1) (by omega)
  have hlog := log2_lt_of (k := 30) (by norm_num) (show 2 ^ lay.logBytecode - 1 < 2 ^ 30 by omega)
  have pi := ptrIndex_cost P (by includes) chunks hc
    (tableWordL lay q t (stateCyclesL.getD t 0) u)
  have hpi : Relation.ptrIndex chunks (tableWordL lay q t (stateCyclesL.getD t 0) u) < 2 ^ 128 := by
    unfold Relation.ptrIndex
    have hd : chunks.d ≤ 24 := hc.len
    have := List.sum_le_length_nsmul
      ((List.range chunks.d).map fun i ↦ Relation.chunkPos chunks
        (tableWordL lay q t (stateCyclesL.getD t 0) u) i * 2 ^ chunks.indexShifts.getD i 0)
      (64 * 2 ^ 64) (fun x hx ↦ by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        refine Nat.mul_le_mul ?_ (Nat.pow_le_pow_right (by norm_num) (getD_le_of' _ i 64 hc.idx))
        have := chunkPos_lt chunks (tableWordL lay q t (stateCyclesL.getD t 0) u) i
        have := Nat.pow_le_pow_right (n := 2) (by norm_num) (getD_le_of' _ i 6 hc.widths)
        omega)
    simp only [List.length_map, List.length_range, smul_eq_mul] at this
    have := Nat.mul_le_mul_right (64 * 2 ^ 64) hd
    omega
  have l1 := limbs_le_two hpi
  rw [limbs_of_lt (by rw [Nat.shiftLeft_eq, one_mul]; omega : 1 <<< lay.logBytecode < 2 ^ 64),
    limbs_of_lt (by omega : lay.logBytecode < 2 ^ 64), limbs_of_lt (by omega : 2 ^ lay.logBytecode < 2 ^ 64),
    limbs_of_lt (by rw [Nat.shiftLeft_eq, one_mul]; omega : 1 <<< chunks.width < 2 ^ 64),
    limbs_of_lt (by have := hc.width; omega : chunks.width < 2 ^ 64),
    limbs_of_lt (by omega : 2 ^ chunks.width < 2 ^ 64)]
  split_ifs <;> omega

/-- **The final cycles** (`finalCyclesL.c464`): at most `(720100)·2^30·6 + 2^37`. -/
theorem finalCyclesL_cost (hP : Includes P Auto.LeanVM.Extraction.AS.finalCyclesL.c464.costDeps)
    (lay : LayoutLite) (hF : LayoutFacts lay) {μ : ℕ} (q : Column μ) (chunks : Chunks)
    (hc : ChunksOk chunks) :
    machineCost P Auto.LeanVM.Extraction.AS.finalCyclesL.c464.costIdx
      [encodeValue lay, encodeValue μ, encodeValue q, encodeValue chunks] ≤
        720100 * 2 ^ 30 * 6 + 2 ^ 37 := by
  have hrow : ∀ t, lay.tableRows.getD t 0 ≤ 2 ^ 30 := fun t ↦ getD_le_of' _ t _ hF.rows_le
  have hn : (List.range nTables).length = 6 := by simp [nTables]
  rw [Auto.LeanVM.Extraction.AS.finalCyclesL.c464.costEq P hP]
  have h1 := rangeLoop_cost P (by includes) nTables [] (by decide)
  have h2 := map_cost P (by includes) _
    (.closure Auto.LeanVM.Extraction.AS.finalCyclesL.c464.lam0.costIdx
      [encodeValue lay, encodeValue μ, encodeValue q, encodeValue chunks])
    (fun t ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.finalCyclesL.c464.lam0.costSpec P (by includes)
      lay q chunks t)) (720100 * 2 ^ 30) (List.range nTables) (fun t ht ↦ by
      have ht' : t < 6 := by have := List.mem_range.1 ht; simpa [nTables] using this
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Auto.LeanVM.Extraction.AS.finalCyclesL.c464.lam0.costEq P (by includes)]
      have hr := hrow t
      have e1 := getD_cost P (by includes) lay.tableRows t 0 (by omega)
      have e2 := rangeLoop_cost P (by includes) (lay.tableRows.getD t 0) [] (by omega)
      have e3 := filterMap_cost P (by includes) _
        (.closure Auto.LeanVM.Extraction.AS.finalCyclesL.c464.lam0.lam0.costIdx
          [encodeValue lay, encodeValue μ, encodeValue q, encodeValue chunks, encodeValue t])
        (fun u ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.finalCyclesL.c464.lam0.lam0.costSpec P
          (by includes) lay q chunks t u)) 720010 (List.range (lay.tableRows.getD t 0)) (fun u hu ↦ by
          have hu' : u < 2 ^ 60 := by have := List.mem_range.1 hu; omega
          rw [appCost_fn]
          have := finalRow_cost P (by includes) lay hF q chunks hc t u ht' hu'
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil] at this ⊢
          omega)
      rw [List.length_range] at e3
      have e4 := Nat.mul_le_mul_left (720010 + 16) hr
      have hl := hF.rows_length
      simp only [List.length_cons, List.length_nil]
      omega)
  rw [hn] at h2
  refine (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add h1 h2)
    (flatten_cost P (by includes) (2 ^ 30) _ ?_)) 14).trans ?_
  · intro l hl
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hl
    exact (List.length_filterMap_le _ _).trans (by rw [List.length_range]; exact hrow t)
  · rw [List.length_map, hn]
    have : nTables = 6 := rfl
    omega

/-- The sum of the rows (`listFoldl` with `List.sum`'s step), word-sized throughout. -/
theorem sumFoldl_cost (hP : Includes P listFoldl.costDeps)
    (hP' : Includes P Auto.List.sum.c405.lam0.costDeps) :
    ∀ (l : List ℕ) (init : ℕ), init + l.sum < 2 ^ 64 →
      machineCost P listFoldl.costIdx [.closure Auto.List.sum.c405.lam0.costIdx [], encodeValue init,
        encodeValue l] ≤ 20 * l.length + 3
  | [], init, _ => by
    rw [listFoldl.costEq_nil P hP (· + ·) _
      (fun a b ↦ RunsApp.of_spec (Auto.List.sum.c405.lam0.costSpec P hP' a b))]
    omega
  | b :: l, init, h => by
    rw [listFoldl.costEq_cons P hP (· + ·) _
      (fun a b ↦ RunsApp.of_spec (Auto.List.sum.c405.lam0.costSpec P hP' a b))]
    simp only [List.sum_cons] at h
    have ih := sumFoldl_cost hP hP' l (init + b) (by omega)
    rw [appCost_fn, List.nil_append, Auto.List.sum.c405.lam0.costEq P hP',
      limbs_of_lt (by omega : init + b < 2 ^ 64), limbs_of_lt (by omega : init < 2 ^ 64),
      limbs_of_lt (by omega : b < 2 ^ 64)]
    simp only [List.length_cons, List.length_nil]
    omega

theorem rows_sum_le (lay : LayoutLite) (hF : LayoutFacts lay) : lay.tableRows.sum ≤ 6 * 2 ^ 30 := by
  have := List.sum_le_length_nsmul lay.tableRows (2 ^ 30) hF.rows_le
  rw [hF.rows_length, smul_eq_mul] at this
  exact this

theorem mem_finalCyclesL {lay : LayoutLite} {μ : ℕ} {q : Column μ} {chunks : Chunks} {b : ℕ}
    (hb : b ∈ finalCyclesL lay q chunks) : b < 2 ^ chunks.width := by
  unfold finalCyclesL at hb
  simp only [List.mem_flatMap, List.mem_filterMap] at hb
  obtain ⟨t, -, u, -, hu⟩ := hb
  split_ifs at hu
  cases hu
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem length_finalCyclesL (lay : LayoutLite) (hF : LayoutFacts lay) {μ : ℕ} (q : Column μ)
    (chunks : Chunks) : (finalCyclesL lay q chunks).length ≤ 6 * 2 ^ 30 := by
  unfold finalCyclesL
  rw [List.length_flatMap]
  refine (List.sum_le_length_nsmul _ (2 ^ 30) ?_).trans ?_
  · intro x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    exact (List.length_filterMap_le _ _).trans (by
      rw [List.length_range]; exact getD_le_of' _ t _ hF.rows_le)
  · simp [nTables]

/-- **The cycle the run halts at** (`firstFinalL.c462`), the chunks' price at most `C`. -/
theorem firstFinalL_cost (hP : Includes P Auto.LeanVM.Extraction.AS.firstFinalL.c462.costDeps)
    (lay : LayoutLite) (hF : LayoutFacts lay) {μ : ℕ} (q : Column μ) (C : ℕ)
    (hC : machineCost P Auto.LeanVM.Protocol.EndToEnd.Sound.chunksL.c402.costIdx [encodeValue lay] ≤ C) :
    machineCost P Auto.LeanVM.Extraction.AS.firstFinalL.c462.costIdx
      [encodeValue lay, encodeValue μ, encodeValue q] ≤ C + 720100 * 2 ^ 30 * 6 + 2 ^ 38 := by
  rw [Auto.LeanVM.Extraction.AS.firstFinalL.c462.costEq P hP]
  have hs := rows_sum_le lay hF
  have hf : List.foldl (fun x1 x2 ↦ x1 + x2) 0 lay.tableRows = lay.tableRows.sum := by
    rw [List.sum_eq_foldl]
  have h1 := sumFoldl_cost P (by includes) (by includes) lay.tableRows 0 (by omega)
  rw [hF.rows_length] at h1
  rcases hch : chunksL lay with _ | chunks
  · dsimp only; omega
  · dsimp only
    have hc := chunksNew_ok hch
    have h2 := finalCyclesL_cost P (by includes) lay hF q chunks hc
    have hw : 2 ^ chunks.width ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) hc.width
    have h3 := listFoldl_le P (by includes) min
      (.closure Auto.LeanVM.Extraction.AS.firstFinalL.c462.lam0.costIdx [])
      (fun a b ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.AS.firstFinalL.c462.lam0.costSpec P (by includes)
        a b)) 10 (fun acc ↦ acc < 2 ^ 64) (finalCyclesL lay q chunks)
      (List.foldl (fun x1 x2 ↦ x1 + x2) 0 lay.tableRows) (by rw [hf]; omega) (fun acc hacc b hb ↦ by
        have := mem_finalCyclesL hb
        refine ⟨by omega, ?_⟩
        rw [appCost_fn, List.nil_append, Auto.LeanVM.Extraction.AS.firstFinalL.c462.lam0.costEq P
          (by includes), limbs_of_lt hacc, limbs_of_lt (by omega : b < 2 ^ 64)]
        simp only [List.length_nil]
        split_ifs <;> omega)
    have hl := length_finalCyclesL lay hF q chunks
    have := Nat.mul_le_mul_left (10 + 11) hl
    omega

/-- **The candidate execution** (`candidateLC`), the chunks' price at most `C`. -/
theorem candidateL_cost (hP : Includes P candidateLC.costDeps) (prog : Semantics.LeanIsaProgram)
    (lay : LayoutLite) (hF : LayoutFacts lay) {μ : ℕ} (q : Column μ) (C : ℕ)
    (hC : machineCost P Auto.LeanVM.Protocol.EndToEnd.Sound.chunksL.c402.costIdx [encodeValue lay] ≤ C) :
    machineCost P candidateLC.costIdx [encodeValue prog, encodeValue lay, encodeValue μ, encodeValue q] ≤
      C + 720100 * 2 ^ 30 * 6 + 2 ^ 39 := by
  rw [candidateLC.costEq P hP, ofFnFrom_length]
  have hm := hF.logMemory_le
  have hp : 2 ^ lay.logMemory ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hm
  have h1 := ofFnFrom_cost P (by includes) (n := 2 ^ lay.logMemory) (by omega) _
    (.closure candidateLC.lam0.costIdx [encodeValue lay, encodeValue μ, encodeValue q])
    (fun i ↦ RunsApp.of_spec (candidateLC.lam0.costSpec P (by includes) lay q i)) 200 (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        candidateLC.lam0.costEq P (by includes)]
      have hi : (i : ℕ) < 2 ^ 60 := by have := i.2; omega
      have c0 := columnRowL_cost P (by includes) lay hF q memory0 i (by decide) hi
      have c1 := columnRowL_cost P (by includes) lay hF q memory1 i (by decide) hi
      have e0 : memory0 = 0 := rfl
      have e1 : memory1 = 1 := rfl
      simp only [List.length_cons, List.length_nil]
      omega) 0 (Nat.zero_le _)
  have h2 := firstFinalL_cost P (by includes) lay hF q C hC
  rw [limbs_of_lt (by rw [Nat.shiftLeft_eq, one_mul]; omega : 1 <<< lay.logMemory < 2 ^ 64),
    limbs_of_lt (by omega : lay.logMemory < 2 ^ 64)]
  have := Nat.mul_le_mul_left (200 + 16) hp
  simp only [Nat.sub_zero] at h1
  omega

end

end LeanVM.Cost.Bounds.AS
