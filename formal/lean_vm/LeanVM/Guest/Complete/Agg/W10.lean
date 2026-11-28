module

public import LeanVM.Guest.Complete.Agg.HonFacts
public import LeanVM.Guest.Complete.Agg.Batched
public import LeanVM.Guest.Complete.MainBytes
public import LeanVM.Guest.Complete.DaPadA
public import LeanVM.Guest.B1.Main.AggFs
public import LeanVM.Guest.Complete.MainPreWins

/-!
# `aggregate_claims`' last run

The window `aW10` (statements `629 ..< 684`, `w10A`): the last weight `bc_wsum[m]` read, the check
`final_claim = bc_star_hint · bc_wsum[m]`, then the claim written at `defer_stmt`: the point read
from `bc_point`, and `bc_star_hint`.

* `aBatched`: on an inner node with `NodeRelation`, the batching runs to `true` on the children's claims
  `aCs w`, so `batched_of_run` holds there.
* `aWsum_full`: the last weight is the batched weight, the children's fresh points of `19` coordinates.
* `holds_aAll`: a memory with the own words and `MainPreA` holds the evaluation memory's runs.
* `runHypT_w10`: the window's `RunHypT` at the honest data, below `2^62`, given the fresh points'
  length.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-! ## The batching -/

/-- **The batching runs to `true`** on an inner node with `NodeRelation`. -/
theorem aBatched {s : NodeStatement} {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w)
    (hne : w.children ≠ []) :
    Batch.runBatching (m := Id) keccakF1600 (Batch.nodeBatchingProgram (· = s.deferredClaim) guestBytecode (aCs w))
      ⟨Batch.batchingStream (aCs w) w.batchingHints, []⟩ = true := by
  have h := hr.2.2.2
  simp only [DeferredClaimBatched, hne, ↓reduceIte] at h
  exact h

/-- **The batching's lengths and outcome**: `25` rounds and challenges, the final claim the hinted
value times the batched weight, the deferred claim the point with the hinted value. -/
theorem aBatched_facts {s : NodeStatement} {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w)
    (hne : w.children ≠ []) :
    w.batchingHints.sumcheckMessages.length = 25 ∧ (aPt w).length = 25 ∧
      (aggRun (aCs w) w.batchingHints).1.2 = w.batchingHints.finalBytecodeValue *
        Batch.batchedBytecodeWeight (aCs w) (aggLam (aCs w) w.batchingHints.lambdaGrindNonce) (aCols w) (aPt w) ∧
      s.deferredClaim = ⟨aPt w, w.batchingHints.finalBytecodeValue⟩ := by
  obtain ⟨-, h2, h3, h4⟩ := batched_of_run (aBatched hr hne)
  rw [guest_deferredVariableCount] at h2
  refine ⟨h2, ?_, h3, h4⟩
  show (bsRun _ _ _).1.1.length = 25
  rw [bsRun_len, h2]

/-- A fresh claim's weight splits at its `19` coordinates. -/
theorem eqEval_split {pt cols r : List E} (hpt : pt.length = 19) (hr : r.length = 25) :
    eqEval (pt ++ cols) r = eqEval pt (r.take 19) * aEqc cols r := by
  have h := Tables.eqEval_append pt cols (r.take 19) (r.drop 19) (by rw [hpt, List.length_take, hr]; rfl)
  rwa [List.take_append_drop] at h

/-- **The last weight is the batched weight**, each fresh point of `19` coordinates and `r` of `25`. -/
theorem aWsum_full {cs : List ChildClaims} {cols r : List E} {lam : E}
    (hpt : ∀ ch ∈ cs, ch.freshClaim.point.length = 19) (hr : r.length = 25) :
    aWsum cs cols lam r cs.length = Batch.batchedBytecodeWeight cs (Batch.lambdaPowers lam cs.length) cols r := by
  unfold aWsum Batch.batchedBytecodeWeight
  rw [List.take_length]
  refine congrArg sumE (zipWith_congr_mem cs _ fun ch hch l => ?_)
  rw [eqEval_split (hpt ch hch) hr]

/-! ## The runs a memory holds -/

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

/-- **The window table's run** from `ExpWinTab`. -/
theorem holds_aTab {rd : Reader} (h : ExpWinTab rd (ptrAt (mGS al (mainCounts s w)))) :
    HoldsWords rd [aTab al s w] := by
  intro q hq n hn
  rw [List.mem_singleton] at hq
  subst hq
  simp only [aTab, List.length_map, List.length_range] at hn ⊢
  refine ⟨ofK_isInK _, ?_⟩
  rw [List.getElem_map, List.getElem_range, Main.addr_ofK, Nat.add_assoc, ← addr_ptr]
  exact (h n hn).2

/-- **A memory with the own words and `main`'s precondition holds the evaluation memory's runs.** -/
theorem holds_aAll {rd : Reader} (hO : HoldsWords rd (aWo s w c)) (hP : MainPreA al s w cover rd) :
    HoldsWords rd (aAll al s w cover c) :=
  holdsWords_append (holdsWords_append hO hP.1) (holds_aTab hP.2.2.1)

end

/-- **`main`'s buffers lie in its region.** -/
theorem mBase_lt {m : MainCounts} {j o : ℕ} (hj : j < 10) (ho : o < m.bufs.getD j 0) :
    B2C.fs "main" ≤ mBase m j + o ∧ mBase m j + o < mTop m := by
  have hl : m.bufs.length = 10 := rfl
  have hb : (bases (B2C.fs "main") m.bufs).length = 10 := by rw [length_bases, hl]
  have hm : (m.bufs.getD j 0, mBase m j) ∈ m.bufs.zip (bases (B2C.fs "main") m.bufs) := by
    refine List.mem_iff_getElem.mpr ⟨j, by simp [hb, hl, hj], ?_⟩
    simp only [List.getElem_zip, mBase]
    rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hj), List.getD_eq_getElem _ _ (by rw [hb]; exact hj)]
  have := bases_zip hm
  exact ⟨by omega, by rw [mTop]; omega⟩

theorem aBufs_sum (m : ℕ) : (aBufs m).sum = 249 + 19 * m := by
  simp [aBufs]; ring

/-! ## The window -/

/-- `aW10`'s atoms. -/
def w10A : List Atom :=
  [.mul (.n 573) (.n 568) (.n 0), .load (.n 574) (.n 573) 0, .mul (.n 575) (.n 7) (.n 574),
    .assertEq (.n 466) (.n 575)] ++
  (List.range 25).flatMap (fun k => [.load (.n (576 + k)) (.n 458) k, .load (.n (576 + k)) (.n 4) k]) ++
  [.load (.n 7) (.n 4) 25]

set_option maxRecDepth 200000 in
theorem w10_eq : atomsOf ((aggP.drop 629).take 55) = w10A := by decide +kernel

set_option maxRecDepth 200000 in
theorem w10_mem : ∀ x ∈ w10A, x ∈ atomsOf aggP := by decide +kernel

set_option maxRecDepth 200000 in
theorem w10_fresh : Atom.load (.n 574) (.n 573) 0 ∉ storesOf 6 aggP ∧
    ∀ k < 25, Atom.load (.n (576 + k)) (.n 458) k ∉ storesOf 6 aggP := by decide +kernel

set_option maxRecDepth 200000 in
theorem w10_shape : w10A.all noHeapB = true ∧ allocDsts (w10A.map Ev.atom) = [] ∧ w10A.filterMap allocK = [] := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem agg_star_mem : Atom.hint (.witness "bc_star_hint" (.stack [.n 7])) ∈ atomsOf aggP := by
  decide +kernel

theorem agg_bs_mem : Stmt.call "batch_sumcheck__L25" [.n 230, .n 231, .n 232, .n 233, .n 234, .n 460, .n 457,
    .n 458, .n 5] [.n 461, .n 462, .n 463, .n 464, .n 465, .n 466] ∈ aggP := by
  rw [← wAgg_flat]
  exact mem_flat_call (by unfold wAgg; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))

theorem w10_cases {x : Atom} (hx : x ∈ w10A) :
    x = .mul (.n 573) (.n 568) (.n 0) ∨ x = .load (.n 574) (.n 573) 0 ∨ x = .mul (.n 575) (.n 7) (.n 574) ∨
      x = .assertEq (.n 466) (.n 575) ∨
      (∃ k < 25, x = .load (.n (576 + k)) (.n 458) k ∨ x = .load (.n (576 + k)) (.n 4) k) ∨
      x = .load (.n 7) (.n 4) 25 := by
  simp only [w10A, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap,
    List.mem_range] at hx
  rcases hx with ((h | h | h | h) | ⟨k, hk, h | h⟩) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, Or.inl h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, Or.inr h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

/-- **`aggregate_claims`' last run's hypotheses** at the honest data, below `2^62`, its children's
fresh points of `19` coordinates. -/
theorem runHypT_w10 {k fp a : ℕ} {es : List Ev} {D : ℕ → Prop} {O : Reader → Prop}
    (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ [])
    (hpt : ∀ ch ∈ w.children, ch.freshClaim.point.length = 19) (hc : c < 2 ^ 62) (hn : w.children.length ≤ 16)
    (hO : ∀ rd, O rd → HoldsWords rd (aWo s w c)) :
    RunHypT k (aV al s w cover c) (aOrc w c) a
      (ownData B2C.cert fp c "aggregate_claims" (aBufs w.children.length) es) (mainR al (mainCounts s w)) D
      (MainPreA al s w cover) O w10A := by
  obtain ⟨h25, hp25, hfin, hd⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  have hsum := aBufs_sum w.children.length
  have hbd : ∀ j o, j < 11 → o < (aBufs w.children.length).getD j 0 → aB c w.children.length j + o < 2 ^ 64 - 1 :=
    fun j o hj ho => by have := (aB_lt (c := c) hj ho).2; omega
  obtain ⟨-, -, -, -, -, -, -, -, p458, -, p568⟩ := aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  obtain ⟨hnh, hdst, hak⟩ := w10_shape
  obtain ⟨f574, f576⟩ := w10_fresh
  have v0 : aV al s w cover c (.n 0) = gen ^ w.children.length := aV_param (by norm_num)
  have v4 : aV al s w cover c (.n 4) = ptrAt (mBase (mainCounts s w) 9) :=
    (aV_param (i := 4) (by norm_num)).trans (congrArg ptrAt (Nat.add_zero _))
  have v7 : aV al s w cover c (.n 7) = w.batchingHints.finalBytecodeValue :=
    (aV_good agg_star_mem (.n 7) (by simp)).trans rfl
  have v466 : aV al s w cover c (.n 466) = (aggRun (aCs w) w.batchingHints).1.2 :=
    (aVal_good (aggArgs_length _ _) _ agg_bs_mem (.n 466) (by simp)).trans rfl
  have g573 : aV al s w cover c (.n 573) = aV al s w cover c (.n 568) * aV al s w cover c (.n 0) :=
    aGood_mul (aggArgs_length _ _) (w10_mem _ (by simp [w10A])) (by norm_num) (by norm_num)
  have g575 : aV al s w cover c (.n 575) = aV al s w cover c (.n 7) * aV al s w cover c (.n 574) :=
    aGood_mul (aggArgs_length _ _) (w10_mem _ (by simp [w10A])) (by norm_num) (by norm_num)
  have v573 : aV al s w cover c (.n 573) = ptrAt (aB c w.children.length 10 + w.children.length) := by
    rw [g573, p568, v0, ptrAt_mul_gen_pow]
  have h10 : w.children.length < (aBufs w.children.length).getD 10 0 := by simp [aBufs]
  have h8 : ∀ k < 25, k < (aBufs w.children.length).getD 8 0 := fun k hk => by simpa [aBufs] using hk
  obtain ⟨i574, e574⟩ := valAt_own (al := al) (cover := cover) (c := c) hl (by norm_num) h10
  have L574 := aLoad_fresh (al := al) (s := s) (w := w) (cover := cover) (c := c)
    (w10_mem _ (by simp [w10A])) f574 v573 (by rwa [Nat.add_zero]) (by rw [Nat.add_zero]; exact hbd 10 _ (by norm_num) h10)
  have v574 : aV al s w cover c (.n 574) = aWsum (aCs w) (aCols w) (aLam w) (aPt w) w.children.length := by
    rw [L574.1, Nat.add_zero, e574]
    simp [aLists]
  have L576 : ∀ k < 25, aV al s w cover c (.n (576 + k)) = (aPt w).getD k 0 ∧
      ∀ rd, HoldsWords rd (aAll al s w cover c) →
        LoadHolds rd (aV al s w cover c (.n 458)) k (aV al s w cover c (.n (576 + k))) := by
    intro k hk
    obtain ⟨ik, ek⟩ := valAt_own (al := al) (cover := cover) (c := c) hl (by norm_num) (h8 k hk)
    have L := aLoad_fresh (al := al) (s := s) (w := w) (cover := cover) (c := c)
      (w10_mem _ (by simp only [w10A, List.mem_append, List.mem_flatMap, List.mem_range]; exact Or.inl (Or.inr
        ⟨k, hk, by simp⟩))) (f576 k hk) p458 ik (hbd 8 k (by norm_num) (h8 k hk))
    refine ⟨?_, L.2⟩
    rw [L.1, ek]
    simp [aLists]
  have hcells : s.deferredClaim.cells = aPt w ++ [w.batchingHints.finalBytecodeValue] := by
    rw [hd]; rfl
  have hq9 : (mBase (mainCounts s w) 9, s.deferredClaim.cells) ∈ mainWords s w cover := by simp [mainWords]
  have st9 : ∀ rd, MainPreA al s w cover rd → ∀ j < 26,
      LoadHolds rd (aV al s w cover c (.n 4)) j (s.deferredClaim.cells.getD j 0) := fun rd hP j hj => by
    rw [v4]
    exact loadHolds_of_rd (holds_run hP.1 hq9 (by rw [hcells, List.length_append, hp25]; simpa using hj))
  have hb9 : (mainCounts s w).bufs.getD 9 0 = 26 := rfl
  have e25 : s.deferredClaim.cells.getD 25 0 = aV al s w cover c (.n 7) := by
    rw [hcells, v7, List.getD_append_right _ _ _ _ (by rw [hp25]), hp25]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdst, allocs_mapAtom, hak]; rfl
  · intro A hA
    obtain ⟨x, hx, hxA⟩ := loadAddr_mem hA
    rcases w10_cases hx with rfl | rfl | rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl
    · simp [Ev.loadAddr?] at hxA
    · simp only [Ev.loadAddr?, Option.some.injEq] at hxA
      rw [← hxA, v573, addr_ptr]
      exact ⟨_, rfl, Or.inl (by rw [Nat.add_zero]; exact own_aB (by norm_num) h10)⟩
    · simp [Ev.loadAddr?] at hxA
    · simp [Ev.loadAddr?] at hxA
    · simp only [Ev.loadAddr?, Option.some.injEq] at hxA
      rw [← hxA, p458, addr_ptr]
      exact ⟨_, rfl, Or.inl (own_aB (by norm_num) (h8 j hj))⟩
    · simp only [Ev.loadAddr?, Option.some.injEq] at hxA
      rw [← hxA, v4, addr_ptr]
      exact ⟨_, rfl, Or.inr (Or.inl (Or.inl (mBase_lt (by norm_num) (by rw [hb9]; omega))))⟩
    · simp only [Ev.loadAddr?, Option.some.injEq] at hxA
      rw [← hxA, v4, addr_ptr]
      exact ⟨_, rfl, Or.inr (Or.inl (Or.inl (mBase_lt (by norm_num) (by rw [hb9]; omega))))⟩
  · rw [heapHintAddrs_noHeap hnh]; intro A hA; simp at hA
  · intro x hx
    rcases w10_cases hx with rfl | rfl | rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl
    · exact pureT_triv (by decide)
    · trivial
    · exact pureT_triv (by decide)
    · show aV al s w cover c (.n 466) + aV al s w cover c (.n 575) = 0
      have hcs : ∀ ch ∈ aCs w, ch.freshClaim.point.length = 19 := fun ch hch => by
        obtain ⟨ch', hch', rfl⟩ := List.mem_map.mp hch
        exact hpt ch' hch'
      have hw := aWsum_full (lam := aLam w) (cols := aCols w) hcs hp25
      have hlam : aggLam (aCs w) w.batchingHints.lambdaGrindNonce = Batch.lambdaPowers (aLam w) (aCs w).length := rfl
      rw [← aCs_length] at v574
      rw [g575, v7, v574, v466, hfin, hw, hlam]
      exact e_add_self _
    · trivial
    · trivial
    · trivial
  · intro rd _ hP hOr x hx
    have hA := holds_aAll (hO rd hOr) hP
    rcases w10_cases hx with rfl | rfl | rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl
    · trivial
    · exact L574.2 rd hA
    · trivial
    · trivial
    · exact (L576 j hj).2 rd hA
    · have e : s.deferredClaim.cells.getD j 0 = aV al s w cover c (.n (576 + j)) := by
        rw [hcells, (L576 j hj).1, List.getD_append _ _ _ _ (by rw [hp25]; exact hj)]
      show LoadHolds _ _ _ _
      rw [← e]; exact st9 rd hP j (by omega)
    · show LoadHolds _ _ _ _
      rw [← e25]; exact st9 rd hP 25 (by norm_num)

end

end
end LeanVM.Guest.Complete.Agg
