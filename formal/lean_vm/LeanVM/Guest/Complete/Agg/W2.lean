module

public import LeanVM.Guest.Complete.Agg.W2T
public import LeanVM.Guest.Complete.Agg.W2G

/-!
# `aggregate_claims`' second run

`runHypT_w2`: the window `aW2`'s `RunHypT` at the honest data, at the cursor `aB c m 4`: the
buffers `col`, `eq_col_tree`, `fresh_val` there, every load in the node's own data (the last row,
the nonce, `col`, `eq_col_tree`) or the window table, each store its honest word (the column
challenges, `eqtree`'s levels), the grind's facts (`w2_grindT`).
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

set_option maxRecDepth 400000 in
theorem w2Sq_split : ∀ x ∈ w2Sq, isNL x = true ∨ ∃ k < 6, x = .load (.n (157 + 13 * k)) (.n 156) k := by
  decide +kernel

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

/-- **`aggregate_claims`' second run's hypotheses** at the honest data, at the cursor `aB c m 4`. -/
theorem runHypT_w2 {k fp a : ℕ} {es : List Memory.Ev} {D : ℕ → Prop} {O : Reader → Prop}
    (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ []) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) (hlo : mLo al (mainCounts s w) ≤ c)
    (hmw : (mainLists s w cover).map List.length = (mainCounts s w).bufs) (hk : 11 ≤ k)
    (ha : a = aB c w.children.length 4) (hO : ∀ rd, O rd → HoldsWords rd (aWo s w c)) :
    RunHypT k (aV al s w cover c) (aOrc w c) a
      (ownData B2C.cert fp c "aggregate_claims" (aBufs w.children.length) es) (mainR al (mainCounts s w)) D
      (MainPreA al s w cover) O w2A := by
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  obtain ⟨p6, -, -, -, p156, p235, -⟩ := aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  obtain ⟨hpure, hnh, hdst, hak, hNL, hNon, hSq, hTree⟩ := w2_shape
  obtain ⟨gP, gA, gM⟩ := w2_grindT (al := al) (cover := cover) (fp := fp) (es := es) (D := D) hr hne hl hc hn hlo
    hmw hk
  obtain ⟨tv235, tv156⟩ := w2_treeV (al := al) (cover := cover) hl hc hn
  have v0 : aV al s w cover c (.n 0) = gen ^ w.children.length := aV_param (by norm_num)
  have q156 : aV al s w cover c (.n 156) = ptrAt (aB c w.children.length 4 + 0) := by rw [p156, Nat.add_zero]
  have q235 : aV al s w cover c (.n 235) = ptrAt (aB c w.children.length 5 + 0) := by rw [p235, Nat.add_zero]
  have q6 : aV al s w cover c (.n 6) = ptrAt (aB c w.children.length 0 + 0) := by rw [p6, Nat.add_zero]
  -- the loads, by part
  have rowL : ∀ i < 13, aV al s w cover c (.n (40 + i)) =
      ((aLists s w).getD 3 []).getD (13 * w.children.length + i) 0 := fun i hi =>
    freshAt hl hc hn (mem_row (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)) (w2_fresh.1 i hi) w2_ptr
      (by norm_num) (by simp [aBufs]; omega)
  have rowB : ∀ i < 13, 13 * w.children.length + i < (aBufs w.children.length).getD 3 0 := fun i hi => by
    simp [aBufs]; omega
  have nonV : aV al s w cover c (.n 70) = ((aLists s w).getD 0 []).getD (0 + 0) 0 :=
    freshAt hl hc hn (mem_non (by simp [w2Non])) w2_fresh.2.1 q6 (by norm_num) (by simp [aBufs])
  have sqV : ∀ k < 6, aV al s w cover c (.n (157 + 13 * k)) = ((aLists s w).getD 4 []).getD (0 + k) 0 :=
    fun k hk => by rw [Nat.zero_add]; exact w2_col hl hc hn hk
  have b4 : ∀ k < 6, 0 + k < (aBufs w.children.length).getD 4 0 := fun k hk => by simp [aBufs]; omega
  have b5 : ∀ k < 126, 0 + k < (aBufs w.children.length).getD 5 0 := fun k hk => by simp [aBufs]; omega
  have parts : ∀ x ∈ w2A, x ∈ w2Ptr ∨ x ∈ w2Row ∨ x ∈ w2Perm ∨ x ∈ w2Non ∨ x ∈ aggGrindA ∨ x ∈ w2Sq ∨
      x ∈ w2Tree ∨ x ∈ w2Tail := fun x hx => by
    simp only [w2A, List.mem_append] at hx
    rcases hx with ((((((h | h) | h) | h) | h) | h) | h) | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inl h))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))]
  have nonG : ∀ x ∈ w2A, x ∉ aggGrindA → x ∈ w2Ptr ++ w2Row ++ w2Perm ++ w2Non ++ w2Sq ++ w2Tree ++ w2Tail :=
    fun x hx hg => by
      simp only [List.mem_append]
      rcases parts x hx with h | h | h | h | h | h | h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact (hg h).elim
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  -- the cases of a load
  have nl : ∀ x ∈ w2Ptr ++ w2Perm ++ w2Tail, isNL x = true := fun x hx => List.all_eq_true.mp hNL x hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdst, allocs_mapAtom, hak]
    simp only [List.map_cons, List.map_nil, allocSz, v0]
    rw [logG_gen_pow (by omega), ha]
    show [ptrAt (aB c w.children.length 4), ptrAt (aB c w.children.length 5), ptrAt (aB c w.children.length 6)] = _
    rw [aB_succ c w.children.length 5 (by norm_num), aB_succ c w.children.length 4 (by norm_num)]
    rfl
  · intro A hA
    obtain ⟨x, hx, hxA⟩ := loadAddr_mem hA
    have none_of : isNL x = true → False := fun hN => by
      rw [(isNL_spec (rd := fun _ => none) hN).2] at hxA; exact absurd hxA (by simp)
    rcases parts x hx with h | h | h | h | h | h | h | h
    · exact (none_of (nl x (by simp [h]))).elim
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
      rw [List.mem_range] at hi
      exact (bufLoad hl w2_ptr (by norm_num) (rowB i hi) (rowL i hi)).2 A hxA
    · exact (none_of (nl x (by simp [h]))).elim
    · have := List.all_eq_true.mp hNon x h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with hN | rfl
      · exact (none_of hN).elim
      · exact (bufLoad hl q6 (by norm_num) (by simp [aBufs]) nonV).2 A hxA
    · exact gA x h A hxA
    · rcases w2Sq_split x h with hN | ⟨k, hk, rfl⟩
      · exact (none_of hN).elim
      · exact (bufLoad hl q156 (by norm_num) (b4 k hk) (sqV k hk)).2 A hxA
    · have := List.all_eq_true.mp hTree x h
      simp only [Bool.or_eq_true] at this
      rcases this with (hN | h1) | h2
      · exact (none_of hN).elim
      · obtain ⟨d, off, rfl, hoff⟩ := ldIn_spec h1
        exact (bufLoad hl q156 (by norm_num) (b4 off hoff)
          (by rw [Nat.zero_add]; exact tv156 _ h d off rfl)).2 A hxA
      · obtain ⟨d, off, rfl, hoff⟩ := ldIn_spec h2
        exact (bufLoad hl q235 (by norm_num) (b5 off hoff)
          (by rw [Nat.zero_add]; exact tv235 _ h d off rfl)).2 A hxA
    · exact (none_of (nl x (by simp [h]))).elim
  · rw [heapHintAddrs_noHeap hnh]; intro A hA; simp at hA
  · intro x hx
    by_cases hg : x ∈ aggGrindA
    · exact gP x hg
    · exact pureT_of_pureB (List.all_eq_true.mp hpure x (nonG x hx hg))
  · intro rd hlow hP hOr x hx
    have hW := hO rd hOr
    rcases parts x hx with h | h | h | h | h | h | h | h
    · exact (isNL_spec (nl x (by simp [h]))).1
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
      rw [List.mem_range] at hi
      exact (bufLoad (cert := B2C.cert) (fp := fp) (f := "aggregate_claims") (es := es) (R := mainR al (mainCounts s w))
        (D := D) hl w2_ptr (by norm_num) (rowB i hi) (rowL i hi)).1 rd hW
    · exact (isNL_spec (nl x (by simp [h]))).1
    · have := List.all_eq_true.mp hNon x h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with hN | rfl
      · exact (isNL_spec hN).1
      · exact (bufLoad (cert := B2C.cert) (fp := fp) (f := "aggregate_claims") (es := es)
          (R := mainR al (mainCounts s w)) (D := D) hl q6 (by norm_num) (by simp [aBufs]) nonV).1 rd hW
    · exact gM rd hlow hP hW x h
    · rcases w2Sq_split x h with hN | ⟨k, hk, rfl⟩
      · exact (isNL_spec hN).1
      · exact (bufLoad (cert := B2C.cert) (fp := fp) (f := "aggregate_claims") (es := es)
          (R := mainR al (mainCounts s w)) (D := D) hl q156 (by norm_num) (b4 k hk) (sqV k hk)).1 rd hW
    · have := List.all_eq_true.mp hTree x h
      simp only [Bool.or_eq_true] at this
      rcases this with (hN | h1) | h2
      · exact (isNL_spec hN).1
      · obtain ⟨d, off, rfl, hoff⟩ := ldIn_spec h1
        exact (bufLoad (cert := B2C.cert) (fp := fp) (f := "aggregate_claims") (es := es)
          (R := mainR al (mainCounts s w)) (D := D) hl q156 (by norm_num) (b4 off hoff)
          (by rw [Nat.zero_add]; exact tv156 _ h d off rfl)).1 rd hW
      · obtain ⟨d, off, rfl, hoff⟩ := ldIn_spec h2
        exact (bufLoad (cert := B2C.cert) (fp := fp) (f := "aggregate_claims") (es := es)
          (R := mainR al (mainCounts s w)) (D := D) hl q235 (by norm_num) (b5 off hoff)
          (by rw [Nat.zero_add]; exact tv235 _ h d off rfl)).1 rd hW
    · exact (isNL_spec (nl x (by simp [h]))).1

end

end
end LeanVM.Guest.Complete.Agg
