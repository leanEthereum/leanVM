module

public import LeanVM.Guest.Complete.Agg.W10

/-!
# `aggregate_claims`' runs around `bc_chain`

* `aW4` (statements `477 ..< 488`, `w4A`): `bc_chain`'s `HeapBuf(2 (m + 1))` at the cursor, its
  record `0` stored: `λ^0 = 1` and the empty combination `0`. `runHypT_w4`, at the cursor
  `aB c m 7`.
* `aW6` (statements `489 ..< 495`, `w6A`): the last record's claim read (`bc_chain[2m + 1]`),
  `bc_point`'s `HeapBuf(25)` at the cursor, the rounds' pointer `bc_msgs·g`. `runHypT_w6`, at the
  cursor `aB c m 8`.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-- `aW4`'s atoms. -/
def w4A : List Atom :=
  [.const (.n 446) (word 2 0), .mul (.n 447) (.n 0) (.n 446), .mul (.n 448) (.n 447) (.n 447),
    .hint (.allocDyn (.n 449) (.n 448)), .const (.n 450) (word 1 0), .load (.n 450) (.n 449) 0,
    .const (.n 451) (word 0 0), .load (.n 451) (.n 449) 1, .const (.n 452) (word 1 0),
    .add (.n 453) (.n 452) (.n 0), .const (.n 454) (word 1 0)]

/-- `aW6`'s atoms. -/
def w6A : List Atom :=
  [.mul (.n 455) (.n 0) (.n 0), .mul (.n 456) (.n 449) (.n 455), .load (.n 457) (.n 456) 1,
    .hint (.alloc (.n 458) 25), .const (.n 459) (word 2 0), .mul (.n 460) (.n 6) (.n 459)]

set_option maxRecDepth 200000 in
theorem w46_eq : atomsOf ((aggP.drop 477).take 11) = w4A ∧ atomsOf ((aggP.drop 489).take 6) = w6A := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem w46_mem : (∀ x ∈ w4A, x ∈ atomsOf aggP) ∧ (∀ x ∈ w6A, x ∈ atomsOf aggP) ∧
    Atom.load (.n 457) (.n 456) 1 ∉ storesOf 6 aggP := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem w46_shape : w4A.all noHeapB = true ∧ allocDsts (w4A.map Ev.atom) = [.n 449] ∧
    w4A.filterMap allocK = [.inr (.n 448)] ∧ w6A.all noHeapB = true ∧ allocDsts (w6A.map Ev.atom) = [.n 458] ∧
    w6A.filterMap allocK = [.inl 25] := by
  decide +kernel

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

theorem aV_448 : aV al s w cover c (.n 448) = gen ^ (2 * (w.children.length + 1)) :=
  (aVal_sizes (aggArgs_length _ _) rfl).2.1

/-- **`bc_chain`'s run** with its record `0` stored, at the cursor `aB c m 7`. -/
theorem runHypT_w4 {k fp a : ℕ} {es : List Ev} {D : ℕ → Prop} {O : Reader → Prop}
    (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ []) (hn : w.children.length ≤ 16)
    (ha : a = aB c w.children.length 7) (hO : ∀ rd, O rd → HoldsWords rd (aWo s w c)) :
    RunHypT k (aV al s w cover c) (aOrc w c) a
      (ownData B2C.cert fp c "aggregate_claims" (aBufs w.children.length) es) (mainR al (mainCounts s w)) D
      (MainPreA al s w cover) O w4A := by
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  obtain ⟨-, -, -, -, -, -, -, p449, -, -, -⟩ := aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  obtain ⟨hnh, hdst, hak, -, -, -⟩ := w46_shape
  obtain ⟨hm4, -, -⟩ := w46_mem
  have h7 : ∀ o < 2, o < (aBufs w.children.length).getD 7 0 := fun o ho => by simp [aBufs]; omega
  obtain ⟨hq7, hlen7⟩ := aWo_get (c := c) hl (j := 7) (by norm_num)
  have e7 : (aLists s w).getD 7 [] = (List.range (w.children.length + 1)).flatMap (aChain (aCs w) (aCols w) (aLam w)) :=
    rfl
  have rec0 : ((aLists s w).getD 7 []).getD 0 0 = 1 ∧ ((aLists s w).getD 7 []).getD 1 0 = 0 := by
    rw [e7, List.range_succ_eq_map, List.flatMap_cons]
    refine ⟨?_, ?_⟩
    · rw [List.getD_append _ _ _ _ (by simp [aChain])]; simp [aChain]
    · rw [List.getD_append _ _ _ _ (by simp [aChain])]; simp [aChain, Batch.lambdaPowers]; rfl
  have st : ∀ rd, O rd → ∀ o < 2, LoadHolds rd (aV al s w cover c (.n 449)) o (((aLists s w).getD 7 []).getD o 0) :=
    fun rd hOr o ho => by
      rw [p449]
      exact loadHolds_of_rd (holds_run (hO rd hOr) hq7 (by rw [hlen7]; exact h7 o ho))
  have c450 : aV al s w cover c (.n 450) = 1 :=
    (aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c)
      (hm4 (.const (.n 450) (word 1 0)) (by simp [w4A]))).trans word_one
  have c451 : aV al s w cover c (.n 451) = 0 :=
    (aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c)
      (hm4 (.const (.n 451) (word 0 0)) (by simp [w4A]))).trans word_zero
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdst, allocs_mapAtom, hak]
    simp only [List.map_cons, List.map_nil, allocSz, aV_448]
    rw [logG_gen_pow (by omega), ha]
    rfl
  · intro A hA
    obtain ⟨x, hx, hxA⟩ := loadAddr_mem hA
    simp only [w4A, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Ev.loadAddr?, Option.some.injEq, reduceCtorEq] at hxA
    · rw [← hxA, p449, addr_ptr]
      exact ⟨_, rfl, Or.inl (own_aB (by norm_num) (h7 0 (by norm_num)))⟩
    · rw [← hxA, p449, addr_ptr]
      exact ⟨_, rfl, Or.inl (own_aB (by norm_num) (h7 1 (by norm_num)))⟩
  · rw [heapHintAddrs_noHeap hnh]; intro A hA; simp at hA
  · intro x hx
    simp only [w4A, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact True.intro
  · intro rd _ _ hOr x hx
    simp only [w4A, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact True.intro
    · show LoadHolds _ _ _ _
      rw [c450, ← rec0.1]; exact st rd hOr 0 (by norm_num)
    · show LoadHolds _ _ _ _
      rw [c451, ← rec0.2]; exact st rd hOr 1 (by norm_num)

/-- **The last record's claim and `bc_point`'s run**, at the cursor `aB c m 8`. -/
theorem runHypT_w6 {k fp a : ℕ} {es : List Ev} {D : ℕ → Prop} {O : Reader → Prop}
    (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ []) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) (ha : a = aB c w.children.length 8) (hO : ∀ rd, O rd → HoldsWords rd (aWo s w c)) :
    RunHypT k (aV al s w cover c) (aOrc w c) a
      (ownData B2C.cert fp c "aggregate_claims" (aBufs w.children.length) es) (mainR al (mainCounts s w)) D
      (MainPreA al s w cover) O w6A := by
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  have hsum := aBufs_sum w.children.length
  obtain ⟨-, -, -, -, -, -, -, p449, p458, -, -⟩ := aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  obtain ⟨-, -, -, hnh, hdst, hak⟩ := w46_shape
  obtain ⟨-, hm6, f457⟩ := w46_mem
  have v0 : aV al s w cover c (.n 0) = gen ^ w.children.length := aV_param (by norm_num)
  have g455 : aV al s w cover c (.n 455) = aV al s w cover c (.n 0) * aV al s w cover c (.n 0) :=
    aGood_mul (aggArgs_length _ _) (hm6 _ (by simp [w6A])) (by norm_num) (by norm_num)
  have g456 : aV al s w cover c (.n 456) = aV al s w cover c (.n 449) * aV al s w cover c (.n 455) :=
    aGood_mul (aggArgs_length _ _) (hm6 _ (by simp [w6A])) (by norm_num) (by norm_num)
  have v456 : aV al s w cover c (.n 456) = ptrAt (aB c w.children.length 7 + (w.children.length + w.children.length)) := by
    rw [g456, g455, v0, p449, ← pow_add, ptrAt_mul_gen_pow]
  have h7 : w.children.length + w.children.length + 1 < (aBufs w.children.length).getD 7 0 := by
    simp [aBufs]; omega
  obtain ⟨i457, -⟩ := valAt_own (al := al) (cover := cover) (c := c) hl (by norm_num) h7
  have L457 := aLoad_fresh (al := al) (s := s) (w := w) (cover := cover) (c := c)
    (hm6 _ (by simp [w6A])) f457 v456 (by rwa [← Nat.add_assoc] at i457)
    (by have := (aB_lt (c := c) (by norm_num) h7).2; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdst, allocs_mapAtom, hak]
    simp only [List.map_cons, List.map_nil, allocSz, ha]
    rfl
  · intro A hA
    obtain ⟨x, hx, hxA⟩ := loadAddr_mem hA
    simp only [w6A, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Ev.loadAddr?, Option.some.injEq, reduceCtorEq] at hxA
    rw [← hxA, v456, addr_ptr, Nat.add_assoc]
    exact ⟨_, rfl, Or.inl (own_aB (by norm_num) h7)⟩
  · rw [heapHintAddrs_noHeap hnh]; intro A hA; simp at hA
  · intro x hx
    simp only [w6A, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact True.intro
  · intro rd _ hP hOr x hx
    simp only [w6A, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact True.intro
    exact L457.2 rd (holds_aAll (hO rd hOr) hP)

end

end
end LeanVM.Guest.Complete.Agg
