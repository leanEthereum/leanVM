module

public import LeanVM.Guest.Complete.Agg.W46

/-!
# `aggregate_claims`' run after the sumcheck

The window `aW8` (statements `496 ..< 628`, `w8A`): `bc_point1`'s `HeapBuf(25)` and its words
`1 + bc_point[k]` (`w8P k`), the column factor `eq_cols` from `col` and `bc_point1[19 ..]` (`w8E`,
loads and products only), then `bc_wsum`'s `HeapBuf(m + 1)` and its word `0` stored (`w8T`).

* `own_fresh`, `own_store`, `own_addr`: a load from a buffer's base reads its honest content, a
  store holds its honest content, and either's address is the node's own data.
* `aB_succ`: buffer `j + 1` starts where buffer `j` ends.
* `runHypT_w8`: the window's `RunHypT` at the honest data, at the cursor `aB c m 9`.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

theorem bases_getD_succ : ∀ (b : ℕ) (L : List ℕ) (j : ℕ), j + 1 < L.length →
    (bases b L).getD (j + 1) 0 = (bases b L).getD j 0 + L.getD j 0
  | _, [], _, h => by simp at h
  | _, [_], _, h => by simp at h
  | b, x :: y :: L, 0, _ => by simp [bases]
  | b, x :: y :: L, j + 1, h => by
    have := bases_getD_succ (b + x) (y :: L) j (by simp at h ⊢; omega)
    simp only [bases, List.getD_cons_succ] at this ⊢
    exact this

/-- **Buffer `j + 1` starts where buffer `j` ends.** -/
theorem aB_succ (c m j : ℕ) (hj : j + 1 < 11) : aB c m (j + 1) = aB c m j + (aBufs m).getD j 0 :=
  bases_getD_succ c (aBufs m) j hj

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

/-- **A load into a new value from a buffer's base** reads its honest content, on every memory
holding the runs. -/
theorem own_fresh (hl : (aLists s w).map List.length = aBufs w.children.length) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) {d p : V} {off j : ℕ} (hx : Atom.load d p off ∈ atomsOf aggP)
    (hS : Atom.load d p off ∉ storesOf 6 aggP) (hp : aV al s w cover c p = ptrAt (aB c w.children.length j))
    (hj : j < 11) (ho : off < (aBufs w.children.length).getD j 0) :
    aV al s w cover c d = ((aLists s w).getD j []).getD off 0 ∧
      ∀ rd, HoldsWords rd (aAll al s w cover c) → LoadHolds rd (aV al s w cover c p) off (aV al s w cover c d) := by
  obtain ⟨hi, hv⟩ := valAt_own (al := al) (cover := cover) (c := c) hl hj ho
  have hsum := aBufs_sum w.children.length
  have hb := (aB_lt (c := c) hj ho).2
  have L := aLoad_fresh hx hS hp hi (by omega)
  exact ⟨L.1.trans hv, L.2⟩

/-- **A store into a buffer** holds its honest content on every memory holding the own words. -/
theorem own_store (hl : (aLists s w).map List.length = aBufs w.children.length) {p : V} {off j : ℕ} {v : E}
    (hp : aV al s w cover c p = ptrAt (aB c w.children.length j)) (hj : j < 11)
    (ho : off < (aBufs w.children.length).getD j 0) (hv : v = ((aLists s w).getD j []).getD off 0) :
    ∀ rd, HoldsWords rd (aWo s w c) → LoadHolds rd (aV al s w cover c p) off v := fun rd h => by
  obtain ⟨hq, hlen⟩ := aWo_get (c := c) hl hj
  rw [hp, hv]
  exact loadHolds_of_rd (holds_run h hq (by rw [hlen]; exact ho))

/-- **A load from a buffer's base** addresses the node's own data. -/
theorem own_addr {cert : String → V → ℕ} {fp : ℕ} {f : String} {es : List Ev} {R D : ℕ → Prop} {d p : V}
    {off j : ℕ} {A : K} (hp : aV al s w cover c p = ptrAt (aB c w.children.length j)) (hj : j < 11)
    (ho : off < (aBufs w.children.length).getD j 0)
    (h : Ev.loadAddr? (aV al s w cover c) (.atom (.load d p off)) = some A) :
    ∃ i, A = addressOfIndex i ∧ (ownData cert fp c f (aBufs w.children.length) es i ∨ R i ∨ D i) := by
  simp only [Ev.loadAddr?, Option.some.injEq] at h
  rw [← h, hp, addr_ptr]
  exact ⟨_, rfl, Or.inl (own_aB hj ho)⟩

end

/-! ## The window -/

/-- `bc_point1[k] = 1 + bc_point[k]`. -/
def w8P (k : ℕ) : List Atom :=
  [.const (.n (468 + 3 * k)) (word 1 0), .load (.n (469 + 3 * k)) (.n 458) k,
    .add (.n (470 + 3 * k)) (.n (468 + 3 * k)) (.n (469 + 3 * k)), .load (.n (470 + 3 * k)) (.n 467) k]

/-- `eq_cols`: `Π_i (col[i] + bc_point1[19 + i])`. -/
def w8E : List Atom :=
  [.load (.n 543) (.n 156) 0, .load (.n 544) (.n 467) 19, .add (.n 545) (.n 543) (.n 544),
    .load (.n 546) (.n 156) 1, .load (.n 547) (.n 467) 20, .add (.n 548) (.n 546) (.n 547),
    .mul (.n 549) (.n 545) (.n 548),
    .load (.n 550) (.n 156) 2, .load (.n 551) (.n 467) 21, .add (.n 552) (.n 550) (.n 551),
    .mul (.n 553) (.n 549) (.n 552),
    .load (.n 554) (.n 156) 3, .load (.n 555) (.n 467) 22, .add (.n 556) (.n 554) (.n 555),
    .mul (.n 557) (.n 553) (.n 556),
    .load (.n 558) (.n 156) 4, .load (.n 559) (.n 467) 23, .add (.n 560) (.n 558) (.n 559),
    .mul (.n 561) (.n 557) (.n 560),
    .load (.n 562) (.n 156) 5, .load (.n 563) (.n 467) 24, .add (.n 564) (.n 562) (.n 563),
    .mul (.n 565) (.n 561) (.n 564)]

/-- `bc_wsum` and its word `0`, the guard of `aggregate_claims_loop3`. -/
def w8T : List Atom :=
  [.const (.n 566) (word 2 0), .mul (.n 567) (.n 0) (.n 566), .hint (.allocDyn (.n 568) (.n 567)),
    .const (.n 569) (word 0 0), .load (.n 569) (.n 568) 0, .const (.n 570) (word 1 0),
    .add (.n 571) (.n 570) (.n 0), .const (.n 572) (word 1 0)]

/-- `aW8`'s atoms. -/
def w8A : List Atom := [.hint (.alloc (.n 467) 25)] ++ (List.range 25).flatMap w8P ++ w8E ++ w8T

set_option maxRecDepth 200000 in
theorem w8_eq : atomsOf ((aggP.drop 496).take 132) = w8A := by decide +kernel

set_option maxRecDepth 200000 in
theorem w8_mem : ∀ x ∈ w8A, x ∈ atomsOf aggP := by decide +kernel

set_option maxRecDepth 200000 in
theorem w8_fresh : (∀ k < 25, Atom.load (.n (469 + 3 * k)) (.n 458) k ∉ storesOf 6 aggP) ∧
    ∀ x ∈ w8E, x ∉ storesOf 6 aggP := by decide +kernel

set_option maxRecDepth 200000 in
theorem w8_shape : w8A.all noHeapB = true ∧ allocDsts (w8A.map Ev.atom) = [.n 467, .n 568] ∧
    w8A.filterMap allocK = [.inl 25, .inr (.n 567)] := by
  decide +kernel

/-- `eq_cols`' loads' first value: `col[i]` read into `eD i`, `bc_point1[19 + i]` into `eD i + 1`. -/
def eD : ℕ → ℕ
  | 0 => 543
  | i + 1 => 546 + 4 * i

/-- An atom neither loading nor reading memory otherwise. -/
def isNL : Atom → Bool
  | .load .. | .rangeCheck .. | .touch .. => false
  | _ => true

theorem isNL_spec {rd : Reader} {σ : Val} {x : Atom} (h : isNL x = true) :
    MemT rd σ x ∧ Ev.loadAddr? σ (.atom x) = none := by
  cases x <;> simp_all [isNL, MemT, Ev.loadAddr?]

set_option maxRecDepth 200000 in
theorem w8E_split : ∀ x ∈ w8E, isNL x = true ∨ (∃ i < 6, x = .load (.n (eD i)) (.n 156) i) ∨
    ∃ i < 6, x = .load (.n (eD i + 1)) (.n 467) (19 + i) := by decide +kernel

theorem w8_cases {x : Atom} (hx : x ∈ w8A) :
    x = .hint (.alloc (.n 467) 25) ∨ (∃ k < 25, x ∈ w8P k) ∨ x ∈ w8E ∨ x ∈ w8T := by
  simp only [w8A, List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_range] at hx
  rcases hx with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

/-- **`aggregate_claims`' run after the sumcheck** at the honest data, at the cursor `aB c m 9`. -/
theorem runHypT_w8 {k fp a : ℕ} {es : List Ev} {D : ℕ → Prop} {O : Reader → Prop}
    (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ []) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) (ha : a = aB c w.children.length 9) (hO : ∀ rd, O rd → HoldsWords rd (aWo s w c)) :
    RunHypT k (aV al s w cover c) (aOrc w c) a
      (ownData B2C.cert fp c "aggregate_claims" (aBufs w.children.length) es) (mainR al (mainCounts s w)) D
      (MainPreA al s w cover) O w8A := by
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  obtain ⟨-, -, -, -, p156, -, -, -, p458, p467, p568⟩ :=
    aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  obtain ⟨hnh, hdst, hak⟩ := w8_shape
  obtain ⟨f458, fE⟩ := w8_fresh
  have s4 : ∀ i < 6, i < (aBufs w.children.length).getD 4 0 := fun i hi => by simpa [aBufs] using hi
  have s8 : ∀ i < 25, i < (aBufs w.children.length).getD 8 0 := fun i hi => by simpa [aBufs] using hi
  have s9 : ∀ i < 25, i < (aBufs w.children.length).getD 9 0 := fun i hi => by simpa [aBufs] using hi
  have s10 : 0 < (aBufs w.children.length).getD 10 0 := by simp [aBufs]
  have hmemP : ∀ k < 25, ∀ x ∈ w8P k, x ∈ atomsOf aggP := fun k hk x hx => w8_mem x (by
    simp only [w8A, List.mem_append, List.mem_flatMap, List.mem_range]; exact Or.inl (Or.inl (Or.inr ⟨k, hk, hx⟩)))
  have hmemE : ∀ x ∈ w8E, x ∈ atomsOf aggP := fun x hx => w8_mem x (by
    simp only [w8A, List.mem_append]; exact Or.inl (Or.inr hx))
  have hmemT : ∀ x ∈ w8T, x ∈ atomsOf aggP := fun x hx => w8_mem x (by
    simp only [w8A, List.mem_append]; exact Or.inr hx)
  -- bc_point1's words
  have P : ∀ k < 25, aV al s w cover c (.n (470 + 3 * k)) = ((aLists s w).getD 9 []).getD k 0 ∧
      ∀ rd, HoldsWords rd (aAll al s w cover c) →
        LoadHolds rd (aV al s w cover c (.n 458)) k (aV al s w cover c (.n (469 + 3 * k))) := by
    intro k hk
    have F := own_fresh (al := al) (cover := cover) hl hc hn (hmemP k hk _ (by simp [w8P])) (f458 k hk) p458
      (by norm_num) (s8 k hk)
    have c1 : aV al s w cover c (.n (468 + 3 * k)) = 1 :=
      (aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c)
        (hmemP k hk (.const (.n (468 + 3 * k)) (word 1 0)) (by simp [w8P]))).trans word_one
    have a1 : aV al s w cover c (.n (470 + 3 * k)) =
        aV al s w cover c (.n (468 + 3 * k)) + aV al s w cover c (.n (469 + 3 * k)) :=
      aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c)
        (hmemP k hk (.add (.n (470 + 3 * k)) (.n (468 + 3 * k)) (.n (469 + 3 * k))) (by simp [w8P]))
    refine ⟨?_, F.2⟩
    have e9 : (aLists s w).getD 9 [] = (aPt w).map (1 + ·) := rfl
    have e8 : (aLists s w).getD 8 [] = aPt w := rfl
    rw [a1, c1, F.1, e9, e8, List.getD_eq_getElem ((aPt w).map (1 + ·)) 0 (by rw [List.length_map, hp25]; exact hk),
      List.getElem_map, List.getD_eq_getElem (aPt w) 0 (by rw [hp25]; exact hk)]
  have v567 : aV al s w cover c (.n 567) = gen ^ (w.children.length + 1) :=
    (aVal_sizes (aggArgs_length _ _) rfl).2.2
  have c569 : aV al s w cover c (.n 569) = 0 :=
    (aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c)
      (hmemT (.const (.n 569) (word 0 0)) (by simp [w8T]))).trans word_zero
  have w0 : ((aLists s w).getD 10 []).getD 0 0 = 0 := by
    show ((List.range (w.children.length + 1)).map _).getD 0 0 = 0
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
    simp [aWsum]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdst, allocs_mapAtom, hak]
    simp only [List.map_cons, List.map_nil, allocSz, v567]
    rw [logG_gen_pow (by omega), ha]
    show [ptrAt (aB c w.children.length 9), ptrAt (aB c w.children.length 10)] = _
    rw [aB_succ c w.children.length 9 (by norm_num)]
    rfl
  · intro A hA
    obtain ⟨x, hx, hxA⟩ := loadAddr_mem hA
    rcases w8_cases hx with rfl | ⟨j, hj, hx⟩ | hx | hx
    · simp [Ev.loadAddr?] at hxA
    · simp only [w8P, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simp [Ev.loadAddr?] at hxA
      · exact own_addr p458 (by norm_num) (s8 j hj) hxA
      · simp [Ev.loadAddr?] at hxA
      · exact own_addr p467 (by norm_num) (s9 j hj) hxA
    · rcases w8E_split x hx with hN | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · rw [(isNL_spec (rd := fun _ => none) hN).2] at hxA; exact absurd hxA (by simp)
      · exact own_addr p156 (by norm_num) (s4 i hi) hxA
      · exact own_addr p467 (by norm_num) (s9 _ (by omega)) hxA
    · simp only [w8T, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | (simp [Ev.loadAddr?] at hxA; done)
          | exact own_addr p568 (by norm_num) s10 hxA
  · rw [heapHintAddrs_noHeap hnh]; intro A hA; simp at hA
  · intro x hx
    rcases w8_cases hx with rfl | ⟨j, hj, hx⟩ | hx | hx
    · exact True.intro
    · simp only [w8P, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact True.intro
    · simp only [w8E, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact True.intro
    · simp only [w8T, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact True.intro
  · intro rd _ hP hOr x hx
    have hA := holds_aAll (hO rd hOr) hP
    rcases w8_cases hx with rfl | ⟨j, hj, hx⟩ | hx | hx
    · exact True.intro
    · simp only [w8P, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact True.intro
      · exact (P j hj).2 rd hA
      · exact True.intro
      · exact own_store hl p467 (by norm_num) (s9 j hj) (P j hj).1 rd (hO rd hOr)
    · have hxS := fE x hx
      have hxm := hmemE x hx
      rcases w8E_split x hx with hN | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · exact (isNL_spec hN).1
      · exact (own_fresh (al := al) (cover := cover) hl hc hn hxm hxS p156 (by norm_num) (s4 i hi)).2 rd hA
      · exact (own_fresh (al := al) (cover := cover) hl hc hn hxm hxS p467 (by norm_num) (s9 _ (by omega))).2 rd hA
    · simp only [w8T, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact True.intro
      exact own_store hl p568 (by norm_num) s10 (c569.trans w0.symm) rd (hO rd hOr)

end

end
end LeanVM.Guest.Complete.Agg
