module

public import LeanVM.Guest.Complete.Agg.W8
public import LeanVM.Guest.Complete.ClaimCells

/-!
# `aggregate_claims`' first run

The window `aW0` (statements `0 ..< 42`, `w0A`): the `HeapBuf`s `bc_msgs`, `fresh_row`,
`carried_row`, `absorb` at the cursor, the hints `bc_sumcheck_msgs` (into `bc_msgs`) and
`bc_star_hint`, and row `0` of `absorb` stored: the batching seed's capacity, the packed count and
three packed zeros (`absSt m cs 0`).

* `fresh_len`: on a node with `ChildrenOk`, each child's fresh point has `19` coordinates.
* `runHypT_w0`: the window's `RunHypT` at the honest data, at the cursor `c`.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-- **Each child's fresh point has `19` coordinates**, the deferring verifier accepting it. -/
theorem fresh_len {w : NodeWitness} (hok : ChildrenOk guestBytecode guestSeed w) :
    ∀ ch ∈ w.children, ch.freshClaim.point.length = 19 := fun ch hch =>
  (fresh_shape_of_verifyDeferred (hok ch hch).verifies).1.trans guest_instructionVariableCount

/-! ## The window -/

/-- `aW0`'s atoms. -/
def w0A : List Atom :=
  [.hint (.alloc (.n 6) 51), .hint (.witness "bc_sumcheck_msgs" (.heap (.n 6) 0 51)),
    .hint (.witness "bc_star_hint" (.stack [.n 7])), .hint (.allocDyn (.n 8) (.n 0)),
    .hint (.allocDyn (.n 9) (.n 0)),
    .const (.n 10) (word 1562680967124014521 0), .const (.n 11) (word 7666384441264927334 11925545048015809408),
    .const (.n 12) (word 14528471851986820829 15194020773630548750),
    .const (.n 13) (word 6704907289165917069 10885225211858021658),
    .const (.n 14) (word 10587785389206534793 159208925504336485),
    .copy (.n 15) (.n 0), .const (.n 16) (word 0 1), .const (.n 17) (word 0 0), .const (.n 18) (word 0 1),
    .const (.n 19) (word 0 0), .const (.n 20) (word 0 1), .const (.n 21) (word 0 0), .const (.n 22) (word 0 1),
    .const (.n 23) (word 2 0), .mul (.n 24) (.n 0) (.n 23), .mul (.n 25) (.n 24) (.n 24),
    .mul (.n 26) (.n 25) (.n 24), .mul (.n 27) (.n 26) (.n 26), .mul (.n 28) (.n 27) (.n 27),
    .mul (.n 29) (.n 28) (.n 24), .hint (.allocDyn (.n 30) (.n 29))] ++
  (List.range 13).map (fun i => .load (.n (10 + i)) (.n 30) i) ++
  [.const (.n 31) (word 1 0), .add (.n 32) (.n 31) (.n 0), .const (.n 33) (word 1 0)]

set_option maxRecDepth 200000 in
theorem w0_eq : atomsOf ((aggP.drop 0).take 42) = w0A := by decide +kernel

set_option maxRecDepth 200000 in
theorem w0_mem : ∀ x ∈ w0A, x ∈ atomsOf aggP := by decide +kernel

set_option maxRecDepth 200000 in
theorem w0_shape : allocDsts (w0A.map Ev.atom) = [.n 6, .n 8, .n 9, .n 30] ∧
    w0A.filterMap allocK = [.inl 51, .inr (.n 0), .inr (.n 0), .inr (.n 29)] := by
  decide +kernel

/-- An atom asking nothing of the valuation beyond its equations. -/
def pureB : Atom → Bool
  | .mul d x y => decide (x.idx < d.idx) && decide (y.idx < d.idx)
  | .assertEq .. | .assertInK .. | .rangeCheck .. | .touch .. => false
  | _ => true

theorem pureT_of_pureB {σ : Val} {a : Atom} (h : pureB a = true) : PureT σ a := by
  cases a with
  | mul d x y =>
    simp only [pureB, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [PureT, h]
  | assertEq x y => simp [pureB] at h
  | assertInK x y => simp [pureB] at h
  | rangeCheck x y t1 t2 kk => simp [pureB] at h
  | touch t p => simp [pureB] at h
  | _ => trivial

set_option maxRecDepth 200000 in
theorem w0_split : w0A.all pureB = true ∧
    ∀ x ∈ w0A, isNL x = true ∨ ∃ i < 13, x = .load (.n (10 + i)) (.n 30) i := by
  decide +kernel

/-- The heap words `w0A`'s hints write: `bc_sumcheck_msgs`' `51` words from `bc_msgs`. -/
theorem w0_hints (σ : Val) : heapHintAddrs σ (w0A.map Ev.atom) =
    (List.range 51).map fun k => (σ (.n 6)).limb 0 * addressOfIndex (0 + k) := by
  simp [w0A, heapHintAddrs, Ev.hintAddrs, hintDest?, destHeap?]

/-- Row `0`'s rate cells: the packed count, three packed zeros. -/
theorem rate_row0 (m : ℕ) : rateOf ([gen ^ m, 0, 0, 0].map (·, dsObserve)) =
    [gen ^ m, word 0 1, 0, word 0 1, 0, word 0 1, 0, word 0 1] := by
  have h := fun k hk => Keccak.rateCell_scalar ([gen ^ m, 0, 0, 0].map (·, dsObserve)) k hk
  obtain ⟨a0, b0⟩ := Prod.mk.inj (h 0 (by simp))
  obtain ⟨a1, b1⟩ := Prod.mk.inj (h 1 (by simp))
  obtain ⟨a2, b2⟩ := Prod.mk.inj (h 2 (by simp))
  obtain ⟨a3, b3⟩ := Prod.mk.inj (h 3 (by simp))
  show [Keccak.rateCell _ (2 * 0), Keccak.rateCell _ (2 * 0 + 1), Keccak.rateCell _ (2 * 1),
    Keccak.rateCell _ (2 * 1 + 1), Keccak.rateCell _ (2 * 2), Keccak.rateCell _ (2 * 2 + 1),
    Keccak.rateCell _ (2 * 3), Keccak.rateCell _ (2 * 3 + 1)] = _
  rw [a0, b0, a1, b1, a2, b2, a3, b3]
  rfl

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

/-- **Row `0`'s stored words** are the first absorbing row's. -/
theorem w0_row (i : ℕ) (hi : i < 13) :
    aV al s w cover c (.n (10 + i)) = (rowW (absSt w.children.length (aCs w) 0)).getD i 0 := by
  have cst : ∀ {d : ℕ} {e : E}, Atom.const (.n d) e ∈ w0A → aV al s w cover c (.n d) = e := fun h =>
    aGood_const (aggArgs_length _ _) (w0_mem _ h)
  have v0 : aV al s w cover c (.n 0) = gen ^ w.children.length := aV_param (by norm_num)
  have v15 : aV al s w cover c (.n 15) = gen ^ w.children.length :=
    (aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c) (w0_mem (.copy (.n 15) (.n 0))
      (by simp [w0A]))).trans v0
  rw [absSt_zero, rowW, rate_row0]
  have hcap : (capOf batchSeed).length = 5 := rfl
  by_cases h5 : i < 5
  · rw [List.getD_append _ _ _ _ (by rw [hcap]; exact h5), ← seed_cells i h5]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · rw [cst (e := word 1562680967124014521 0) (by simp [w0A])]; rfl
    · rw [cst (e := word 7666384441264927334 11925545048015809408) (by simp [w0A])]; rfl
    · rw [cst (e := word 14528471851986820829 15194020773630548750) (by simp [w0A])]; rfl
    · rw [cst (e := word 6704907289165917069 10885225211858021658) (by simp [w0A])]; rfl
    · rw [cst (e := word 10587785389206534793 159208925504336485) (by simp [w0A])]; rfl
  · rw [List.getD_append_right _ _ _ _ (by rw [hcap]; omega), hcap]
    rcases (show i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact v15
    · exact cst (by simp [w0A])
    · exact (cst (by simp [w0A])).trans word_zero
    · exact cst (by simp [w0A])
    · exact (cst (by simp [w0A])).trans word_zero
    · exact cst (by simp [w0A])
    · exact (cst (by simp [w0A])).trans word_zero
    · exact cst (by simp [w0A])

/-- **`aggregate_claims`' first run's hypotheses** at the honest data, at the cursor `c`. -/
theorem runHypT_w0 {k fp a : ℕ} {es : List Memory.Ev} {D : ℕ → Prop} {O : Reader → Prop}
    (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ [])
    (hn : w.children.length ≤ 16) (ha : a = c) (hO : ∀ rd, O rd → HoldsWords rd (aWo s w c)) :
    RunHypT k (aV al s w cover c) (aOrc w c) a
      (ownData B2C.cert fp c "aggregate_claims" (aBufs w.children.length) es) (mainR al (mainCounts s w)) D
      (MainPreA al s w cover) O w0A := by
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  obtain ⟨p6, -, -, p30, -, -, -, -, -, -, -⟩ := aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  obtain ⟨hdst, hak⟩ := w0_shape
  obtain ⟨hpure, hsplit⟩ := w0_split
  have v0 : aV al s w cover c (.n 0) = gen ^ w.children.length := aV_param (by norm_num)
  have v29 : aV al s w cover c (.n 29) = gen ^ (13 * (w.children.length + 1)) :=
    (aVal_sizes (aggArgs_length _ _) rfl).1
  have s3 : ∀ i < 13, i < (aBufs w.children.length).getD 3 0 := fun i hi => by simp [aBufs]; omega
  have s0 : ∀ i < 51, i < (aBufs w.children.length).getD 0 0 := fun i hi => by simpa [aBufs] using hi
  have row : ∀ i < 13, aV al s w cover c (.n (10 + i)) = ((aLists s w).getD 3 []).getD i 0 := fun i hi => by
    rw [w0_row i hi]
    show _ = ((List.range (w.children.length + 1)).flatMap fun j => rowW (absSt w.children.length (aCs w) j)).getD i 0
    rw [List.range_succ_eq_map, List.flatMap_cons,
      List.getD_append _ _ _ _ (by rw [rowW_length (absSt_ok _ _ _)]; exact hi)]
  refine ⟨?_, ?_, ?_, fun x hx => pureT_of_pureB (List.all_eq_true.mp hpure x hx), ?_⟩
  · rw [hdst, allocs_mapAtom, hak]
    simp only [List.map_cons, List.map_nil, allocSz, v0, v29]
    rw [logG_gen_pow (by omega), logG_gen_pow (by omega), ha]
    rfl
  · intro A hA
    obtain ⟨x, hx, hxA⟩ := loadAddr_mem hA
    rcases hsplit x hx with hN | ⟨i, hi, rfl⟩
    · rw [(isNL_spec (rd := fun _ => none) hN).2] at hxA; exact absurd hxA (by simp)
    · exact own_addr p30 (by norm_num) (s3 i hi) hxA
  · intro A hA
    rw [w0_hints] at hA
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
    rw [List.mem_range] at hi
    rw [p6, addr_ptr]
    exact ⟨_, rfl, Or.inl (own_aB (by norm_num) (by rw [Nat.zero_add]; exact s0 i hi))⟩
  · intro rd _ _ hOr x hx
    rcases hsplit x hx with hN | ⟨i, hi, rfl⟩
    · exact (isNL_spec hN).1
    · exact own_store hl p30 (by norm_num) (s3 i hi) (row i hi) rd (hO rd hOr)

end

end
end LeanVM.Guest.Complete.Agg
