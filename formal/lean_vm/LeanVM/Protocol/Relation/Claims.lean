/-
  LeanVM.Protocol.Relation.Claims

  The front phases' claims, placed on the stack: where they fail on a stack, a ring claim fails
  on it or a claim of the stacked opening does.
-/

module

public import LeanVM.Protocol.Relation.Front
public import LeanVM.Protocol.Relation.Bridge
import LeanVM.Protocol.Tables
import LeanVM.ToMathlib.Finset

/-!
# The front phases' claims on the stack

The stacked opening reads the link's memory term (`memoryTermClaim`) and every column claim with
a placement (`ColumnClaim.onStack`): the link's, the public input's and the Keccak reduction's
on `q_keccak`; the `KECCAK` output lanes have none, and the Keccak reduction answers for them.
**`not_frontHolds`**: where the front phases' claims fail on a stack (`FrontHolds`), one of the two
ring claims fails on it, or one of the stack claims the opening reads, the claims of shapes the
phases return (`LinkShape`, `KeccakShape`, the public input's claims at `(c, 0, …, 0)`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Tables Finset

@[expose] public section

/-- What `buildLayout` keeps of its sizes. -/
theorem buildLayout_logMemory {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) :
    layout.logMemory = lm ∧ minLogMemory ≤ lm := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, hc.1⟩
    · cases h

/-- A placed column claim's stack claim. -/
theorem onStack_eq {layout : Layout} {c : ColumnClaim} {p : Placement}
    (hp : layout.placements.getD c.column none = some p) :
    c.onStack layout = some (fun x ↦ eqEval (p.stackPoint c.point layout.stackLog) x, c.value) := by
  unfold ColumnClaim.onStack
  rw [hp]
  rfl

/-- A claim the opening reads, placed. -/
theorem mem_filterMap_onStack {layout : Layout} {cs : List ColumnClaim} {c : ColumnClaim}
    (hc : c ∈ cs) {p : Placement} (hp : layout.placements.getD c.column none = some p) :
    (fun x ↦ eqEval (p.stackPoint c.point layout.stackLog) x, c.value) ∈
      cs.filterMap (·.onStack layout) :=
  List.mem_filterMap.mpr ⟨c, hc, onStack_eq hp⟩

/-- **A placed column claim the opening reads holds of its column** where it holds on the stack.
-/
theorem columnClaim_of_stack {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) (q : Column layout.stackLog)
    {cs : List ColumnClaim} (hall : ∀ sc ∈ cs.filterMap (·.onStack layout), StackClaimHolds sc q)
    {c : ColumnClaim} (hc : c ∈ cs) {p : Placement}
    (hp : layout.placements.getD c.column none = some p) (hlen : c.point.length = p.variableCount)
    (hk : keccakOutputLane c.column = none) : ColumnClaimHolds layout q c :=
  (stackClaimHolds_onStack_iff hb q hp hlen hk).mp (hall _ (mem_filterMap_onStack hc hp))

/-- A table's claims the link sends: its row point, a column below its width. -/
theorem mem_linkColumnClaims {e : LinkEnd} {c : ColumnClaim} (hc : c ∈ linkColumnClaims e) :
    ∃ t < nTables, ∃ j value, (j, value) ∈ (e.columns.getD t ([], [])).2 ∧
      c = ⟨globalColumnBases.getD t 0 + j, (e.columns.getD t ([], [])).1, value⟩ := by
  unfold linkColumnClaims at hc
  obtain ⟨x, hx, hcx⟩ := List.mem_flatMap.mp hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.getElem_zip] at hcx
  obtain ⟨⟨j, value⟩, hjv, rfl⟩ := List.mem_map.mp hcx
  have hi1 : i < globalColumnBases.length := by simp at hi; omega
  have hi2 : i < e.columns.length := by simp at hi; omega
  refine ⟨i, by simpa [globalColumnBases_eq, nTables] using hi1, j, value, ?_, ?_⟩
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2] using hjv
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2]

/-- **The link's committed claims are placed, at points over their variables.** -/
theorem linkClaim_placed {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) {e : LinkEnd} (he : LinkShape layout e)
    {c : ColumnClaim} (hc : c ∈ linkColumnClaims e) (hk : keccakOutputLane c.column = none) :
    ∃ p, layout.placements.getD c.column none = some p ∧ c.point.length = p.variableCount := by
  obtain ⟨-, -, hpts, hcols, -⟩ := he
  obtain ⟨t, ht, j, value, hjv, rfl⟩ := mem_linkColumnClaims hc
  have hj : j < tableWidths.getD t 0 := (hcols t ht).2 _ hjv
  have hbound : globalColumnBases.getD t 0 + j < 116 := by
    have : globalColumnBases.getD t 0 + tableWidths.getD t 0 ≤ 116 := by
      simp only [nTables] at ht
      interval_cases t <;> decide
    omega
  have hnk : ¬ (globalColumnBases.getD opKeccak 0 + keccakOut ≤ globalColumnBases.getD t 0 + j ∧
      globalColumnBases.getD t 0 + j < globalColumnBases.getD opKeccak 0 + keccakOut +
        keccakStateLanes) := by
    intro h
    simp only [keccakOutputLane] at hk
    split_ifs at hk
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (placement_isSome hb hbound hnk)
  refine ⟨p, hp, ?_⟩
  rw [placement_variableCount hb hp, columnKappas_table _ _ ht hj, hpts t ht]

/-- The memory columns and `q_keccak` are placed, at their log-sizes. -/
theorem global_placed {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) :
    (∃ p, layout.placements.getD memory0 none = some p ∧ p.variableCount = layout.logMemory) ∧
    (∃ p, layout.placements.getD memory1 none = some p ∧ p.variableCount = layout.logMemory) ∧
    (∃ p, layout.placements.getD qkeccak none = some p ∧
      p.variableCount = keccakHeight layout + qkeccakSlotBits) := by
  have hs := columnKappas_memory layout.logMemory layout.tableLogHeights
  have h33 : keccakOut = 33 := by decide
  have hn : ∀ c < 3, ¬ (globalColumnBases.getD opKeccak 0 + keccakOut ≤ c ∧
      c < globalColumnBases.getD opKeccak 0 + keccakOut + keccakStateLanes) := by
    intro c hc
    rw [keccakBase_eq, h33]
    omega
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
      (placement_isSome hb (c := memory0) (by decide) (hn _ (by decide)))
    exact ⟨p, hp, by rw [placement_variableCount hb hp, hs.1]⟩
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
      (placement_isSome hb (c := memory1) (by decide) (hn _ (by decide)))
    exact ⟨p, hp, by rw [placement_variableCount hb hp, hs.2.1]⟩
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
      (placement_isSome hb (c := qkeccak) (by decide) (hn _ (by decide)))
    exact ⟨p, hp, by rw [placement_variableCount hb hp, hs.2.2]; rfl⟩

/-! ## The memory term -/

/-- The memory term's stack claim, its limbs at their placements. -/
def memoryTermOf (layout : Layout) (p0 p1 : Placement) (e : LinkEnd) : StackClaim :=
  (fun x ↦ sumE [e.memoryScales.1 * eqEval (p0.stackPoint e.memoryPoint layout.stackLog) x,
    e.memoryScales.2 * eqEval (p1.stackPoint e.memoryPoint layout.stackLog) x], e.memoryValue)

theorem memoryTermClaim_eq (layout : Layout) (e : LinkEnd) {p0 p1 : Placement}
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1) :
    memoryTermClaim layout e = VerifierProgram.ret (memoryTermOf layout p0 p1 e) := by
  unfold memoryTermClaim
  rw [h0, h1]
  rfl

theorem keccakOutputLane_low {c : ℕ} (hc : c < 81) : keccakOutputLane c = none := by
  have h33 : keccakOut = 33 := by decide
  simp only [keccakOutputLane, keccakBase_eq, h33]
  split_ifs with h
  · omega
  · rfl

/-- A placed column's stack sum under its stack point is its multilinear extension. -/
theorem stackSum_eq_rowMle {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) (q : Column layout.stackLog) {c : ℕ}
    {p : Placement} (hp : layout.placements.getD c none = some p) (point : List E)
    (hlen : point.length = p.variableCount) (hk : keccakOutputLane c = none) :
    ∑ x : Fin (2 ^ layout.stackLog),
        eqEval (p.stackPoint point layout.stackLog) (boolPoint layout.stackLog x) * ofK (cell q x) =
      rowMle point (columnValue layout q c) := by
  have h := stackClaimHolds_onStack_iff hb q (c := ⟨c, point, rowMle point (columnValue layout q c)⟩)
    hp hlen hk
  exact h.mpr rfl

/-- The memory term's sum, limb by limb. -/
theorem memoryTerm_sum (layout : Layout) (q : Column layout.stackLog) (e : LinkEnd)
    (p0 p1 : Placement) :
    StackClaimHolds (memoryTermOf layout p0 p1 e) q ↔
      e.memoryScales.1 * ∑ x : Fin (2 ^ layout.stackLog),
          eqEval (p0.stackPoint e.memoryPoint layout.stackLog) (boolPoint layout.stackLog x) *
            ofK (cell q x) +
        e.memoryScales.2 * ∑ x : Fin (2 ^ layout.stackLog),
          eqEval (p1.stackPoint e.memoryPoint layout.stackLog) (boolPoint layout.stackLog x) *
            ofK (cell q x) = e.memoryValue := by
  have h : ∑ x : Fin (2 ^ layout.stackLog), (memoryTermOf layout p0 p1 e).1
      (boolPoint layout.stackLog x) * ofK (cell q x) =
      e.memoryScales.1 * ∑ x : Fin (2 ^ layout.stackLog),
          eqEval (p0.stackPoint e.memoryPoint layout.stackLog) (boolPoint layout.stackLog x) *
            ofK (cell q x) +
        e.memoryScales.2 * ∑ x : Fin (2 ^ layout.stackLog),
          eqEval (p1.stackPoint e.memoryPoint layout.stackLog) (boolPoint layout.stackLog x) *
            ofK (cell q x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [show (memoryTermOf layout p0 p1 e).1 (boolPoint layout.stackLog x) =
        e.memoryScales.1 * eqEval (p0.stackPoint e.memoryPoint layout.stackLog)
          (boolPoint layout.stackLog x) +
        e.memoryScales.2 * eqEval (p1.stackPoint e.memoryPoint layout.stackLog)
          (boolPoint layout.stackLog x) by
      simp only [memoryTermOf, sumE_eq, List.sum_cons, List.sum_nil, add_zero]]
    rw [add_mul, mul_assoc, mul_assoc]
  unfold StackClaimHolds
  rw [h]
  rfl

/-- **The memory term holds on the stack exactly as the link's memory equation.** -/
theorem memoryTerm_holds_iff {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) (q : Column layout.stackLog) {e : LinkEnd}
    {p0 p1 : Placement} (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1)
    (hl0 : e.memoryPoint.length = p0.variableCount) (hl1 : e.memoryPoint.length = p1.variableCount) :
    StackClaimHolds (memoryTermOf layout p0 p1 e) q ↔
      e.memoryValue =
        e.memoryScales.1 * rowMle e.memoryPoint (columnValue layout q memory0) +
          e.memoryScales.2 * rowMle e.memoryPoint (columnValue layout q memory1) := by
  have hsum := memoryTerm_sum layout q e p0 p1
  have hm0 : keccakOutputLane memory0 = none := keccakOutputLane_low (by norm_num [memory0])
  have hm1 : keccakOutputLane memory1 = none := keccakOutputLane_low (by norm_num [memory1])
  have e0 := stackSum_eq_rowMle hb q h0 _ hl0 hm0
  have e1 := stackSum_eq_rowMle hb q h1 _ hl1 hm1
  rw [hsum, e0, e1, eq_comm]

/-! ## The front phases' claims on the stack -/

theorem placement_unique {layout : Layout} {c : ℕ} {p p' : Placement}
    (h : layout.placements.getD c none = some p) (h' : layout.placements.getD c none = some p') :
    p = p' := Option.some.inj (h.symm.trans h')

/-- **Where the front phases' claims fail on a stack**, one of the two ring claims fails on it, or
one of the stack claims the opening reads: the memory term, and the placed column claims of the
link, the public input and the Keccak reduction. -/
theorem not_frontHolds {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) (q : Column layout.stackLog) (input : PublicInput)
    {qk p0 p1 : Placement} (hqk : layout.placements.getD qkeccak none = some qk)
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1)
    {link : LinkEnd} {pub outs : List ColumnClaim} {pt sl : List E} (hls : LinkShape layout link)
    (hpub : ∃ c m, layout.placements.getD memory0 none = some m ∧ pub = publicClaims input m c)
    (hks : KeccakShape layout (outs, pt, sl))
    (hn : ¬ FrontHolds layout qk q (link, pub, (outs, pt, sl))) :
    (∃ rc ∈ [keccakRingClaim qk pt sl, link.ring], ¬ RingClaimHolds q rc) ∨
      ∃ sc ∈ memoryTermOf layout p0 p1 link ::
          (linkColumnClaims link ++ pub ++ outs).filterMap (·.onStack layout),
        ¬ StackClaimHolds sc q := by
  by_contra hc
  simp only [not_or, not_exists, not_and, not_not] at hc
  obtain ⟨hr, hs⟩ := hc
  obtain ⟨⟨m0, hm0, hv0⟩, ⟨m1, hm1, hv1⟩, ⟨mk, hmk, hvk⟩⟩ := global_placed hb
  cases placement_unique h0 hm0
  cases placement_unique h1 hm1
  cases placement_unique hqk hmk
  have hlen := hls.1
  obtain ⟨_, hlm⟩ := buildLayout_logMemory hb
  have hall : ∀ sc ∈ (linkColumnClaims link ++ pub ++ outs).filterMap (·.onStack layout),
      StackClaimHolds sc q := fun sc hsc ↦ hs sc (List.mem_cons_of_mem _ hsc)
  apply hn
  refine ⟨?_, ?_, hr _ (by simp), ?_, ?_, hr _ (by simp)⟩
  · exact (memoryTerm_holds_iff hb q h0 h1 (by rw [hlen, hv0]) (by rw [hlen, hv1])).mp
      (hs _ List.mem_cons_self)
  · intro c hc
    have hc' := (List.mem_filter.mp hc)
    have hk : keccakOutputLane c.column = none := by simpa using hc'.2
    obtain ⟨p, hp, hpl⟩ := linkClaim_placed hb hls hc'.1 hk
    exact columnClaim_of_stack hb q hall (by simp [hc'.1]) hp hpl hk
  · obtain ⟨c, m, hm, rfl⟩ := hpub
    cases placement_unique hm h0
    have hlm1 : 1 ≤ layout.logMemory := by
      obtain ⟨h1', _⟩ := buildLayout_logMemory hb; rw [h1']; simpa [minLogMemory] using hlm
    intro cl hcl
    have hcl' := hcl
    simp only [publicClaims, List.map_cons, List.map_nil, List.zipWith_cons_cons,
      List.zipWith_nil_left, List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl
    · exact columnClaim_of_stack hb q hall (by simp [hcl]) h0 (by simp; omega)
        (keccakOutputLane_low (by norm_num [memory0]))
    · exact columnClaim_of_stack hb q hall (by simp [hcl]) h1 (by simp; omega)
        (keccakOutputLane_low (by norm_num [memory1]))
  · intro c hc
    obtain ⟨hcol, hpl⟩ := hks.1 c hc
    exact columnClaim_of_stack hb q hall (by simp [hc]) (hcol ▸ hqk) (by rw [hpl, hvk])
      (hcol ▸ keccakOutputLane_low (by norm_num [qkeccak]))

end

end LeanVM.Protocol.Relation
