/-
  LeanVM.Guest.B1.Stack.TermFacts

  The facts `check_stack_terminal`'s proof reads off its template, segment by segment.
-/

module

public import LeanVM.Guest.B1.Stack.TermT
public import LeanVM.Guest.B1.Eq.Meaning
public import LeanVM.Guest.B1.Ring.Cols
import LeanVM.Guest.Value.FieldBits

/-!
# `check_stack_terminal`: the segments

Each lemma takes a segment of `cstBodyA` holding (`AllOk`) and gives what its statements say:
the header's loads and calls (`head_facts`), the ring row's sum (`rowSum_facts`), the pointers'
scales (`rq_facts`), the pointers' masks (`masks_facts`), the sent columns' Horner (`sent_facts`).
`stackLog_le`: a layout's stack is below `2^42` words.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Small facts -/

theorem readsAt_prefix {p : E} {xs ys : List E} (h1 : ReadsAt rd p xs) (h2 : ReadsAt rd p ys)
    (hl : xs.length ≤ ys.length) : xs = ys.take xs.length := by
  refine List.ext_getElem (by simp; omega) fun i hi _ ↦ ?_
  rw [List.getElem_take]
  exact loadHolds_unique (h1 i hi) (h2 i (by omega))

theorem readsAt_get {p : E} {xs : List E} (h : ReadsAt rd p xs) {i : ℕ} (hi : i < xs.length) :
    LoadHolds rd p i (xs.getD i 0) := by
  rw [List.getD_eq_getElem _ _ hi]
  exact h i hi

theorem gen16_inv : gen ^ 16 * word 8198521646651277316 0 = 1 := by
  rw [show gen = ofK (K.ofBits 2) from rfl, show word 8198521646651277316 0 = ofK (K.ofBits 8198521646651277316)
    from word_eOfNat _, ← ofK_pow, ← ofK_mul, show K.ofBits 2 ^ 16 * K.ofBits 8198521646651277316 = 1 by
      decide +kernel, ofK_one]

/-- **A layout's stack is at most `2^42` words.** -/
theorem stackLog_le {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) : layout.stackLog ≤ 42 := by
  obtain ⟨hlm, hlm30, -, -, hh30, hsl, -⟩ := buildLayout_some hbl
  rw [← hlm] at hsl hlm30
  rw [hsl, stack_eq]
  set sizes := stackBlocks.map fun b ↦ (columnKappas tables layout.logMemory layout.tableLogHeights).getD b.column 0
    with hsizes
  have hszl : sizes.length = 52 := by simp [hsizes, stackBlocks_length]
  obtain ⟨-, hlog⟩ := stackOffsets_closed sizes
  rw [hszl] at hlog
  rw [hlog]
  refine max_le (by decide) (log2Ceil_le_iff.mpr ?_)
  have hsz : ∀ j < 52, sizes.getD j 0 ≤ 36 := fun j hj ↦ by
    have e : sizes.getD j 0 = blockKap layout j := by
      simp [hsizes, blockKap, blockColumn, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show j < stackBlocks.length by rw [stackBlocks_length]; exact hj)]
    rw [e, blockKap, blockKappa _ _ hj, csKap]
    obtain ⟨hg, -⟩ := grpOf_facts j hj
    obtain ⟨hsrc, hadj, -⟩ := csGroups_facts _ hg
    have hkv : ∀ i < 8, kvOf layout.logMemory layout.tableLogHeights i ≤ 30 := fun i hi ↦ by
      unfold kvOf
      split_ifs
      · omega
      · omega
      · exact hh30 (i - 2) (by simp [nTables]; omega)
    have := hkv _ hsrc
    omega
  calc ∑ j ∈ Finset.range 52, 2 ^ sizes.getD j 0 ≤ ∑ _j ∈ Finset.range 52, 2 ^ 36 :=
        Finset.sum_le_sum fun j hj ↦ Nat.pow_le_pow_right (by decide) (hsz j (Finset.mem_range.1 hj))
    _ ≤ 2 ^ 42 := by simp

/-- The dispatch's arm `j` is `stack_selectors` at `⌈(16 + j)/4⌉` nibbles. -/
theorem cstArms_mem : ∀ j < 15, ((19 + j) / 4, cstArms.getD j "") ∈ stackSelectorsNames := by decide

/-! ## Segments -/

theorem allOk_flatten_range (f : ℕ → List Stmt) (n : ℕ) :
    AllOk C rd σ ((List.range n).map f).flatten ↔ ∀ i < n, AllOk C rd σ (f i) := by
  rw [allOk_flatten]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

theorem word_g39 : word 549755813888 0 = gen ^ 39 := word_two_pow (a := 39) (by decide)
theorem word_g6 : word 64 0 = gen ^ 6 := word_two_pow (a := 6) (by decide)
theorem word_g5 : word 32 0 = gen ^ 5 := word_two_pow (a := 5) (by decide)
theorem word_g13 : word 8192 0 = gen ^ 13 := word_two_pow (a := 13) (by decide)

/-- **The header.** -/
theorem head_facts (hA : AllOk C rd σ cstHead) :
    (∃ j < 15, σ (.n 4) * word 8198521646651277316 0 = ofK (addressOfIndex j) ∧
      C (cstArms.getD j "") [σ (.n 2), σ (.n 3), σ (.n 17), σ (.n 18), σ (.n 0)] [σ (.n 43)]) ∧
    (∀ i < 8, LoadHolds rd (σ (.n 1)) i (σ (.n (44 + i)))) ∧
    LoadHolds rd (σ (.n 43)) 2 (σ (.n 52)) ∧ LoadHolds rd (σ (.n 43)) 0 (σ (.n 53)) ∧
    LoadHolds rd (σ (.n 43)) 1 (σ (.n 54)) ∧
    C "rs_eq_run" [σ (.n 10) * gen ^ 39, σ (.n 18), σ (.n 51) * gen ^ 6, σ (.n 12)] [σ (.n 59)] := by
  simp only [cstHead, allOk_cons, allOk_nil, and_true] at hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h41, h42, hd, l0, l1, l2, l3, l4, l5, l6, l7,
    l52, l53, l54, h55, h56, h57, h58, hrs⟩ := hA
  simp only [StmtOk, Atom.Holds, List.map_cons, List.map_nil] at h41 h42 hd l0 l1 l2 l3 l4 l5 l6 l7
  simp only [StmtOk, Atom.Holds, List.map_cons, List.map_nil] at l52 l53 l54 h55 h56 h57 h58 hrs
  refine ⟨?_, fun i hi ↦ ?_, l52, l53, l54, ?_⟩
  · obtain ⟨j, hj, hjx, hc⟩ := hd
    have hj15 : j < 15 := by simpa [cstArms] using hj
    rw [h42] at hjx
    rw [h41] at hjx
    refine ⟨j, hj15, hjx, ?_⟩
    rw [List.getD_eq_getElem _ _ hj]
    exact hc
  · interval_cases i
    exacts [l0, l1, l2, l3, l4, l5, l6, l7]
  · rw [h56, h58, h55, h57, word_g39, word_g6] at hrs
    exact hrs

/-- Word `k` of `q_keccak`'s ring row, as the sum reads it. -/
def rowV (σ : Val) (k : ℕ) : E := if k = 0 then σ (.n 60) else σ (.n (59 + 2 * k))

/-- **The row's sum.** -/
theorem rowSum_facts (hA : AllOk C rd σ cstRowSum) :
    (∀ k < 64, LoadHolds rd (σ (.n 59)) k (rowV σ k)) ∧
      σ (.n 187) = (∑ k ∈ Finset.range 64, rowV σ k) * σ (.n 52) := by
  simp only [cstRowSum, allOk_append, allOk_cons, allOk_nil, and_true, allOk_flatten_range] at hA
  obtain ⟨⟨⟨l0, l1, a2⟩, hrun⟩, hm⟩ := hA
  simp only [StmtOk, Atom.Holds] at l0 l1 a2 hm
  have hstep : ∀ i < 62, LoadHolds rd (σ (.n 59)) (i + 2) (σ (.n (63 + 2 * i))) ∧
      σ (.n (64 + 2 * i)) = σ (.n (62 + 2 * i)) + σ (.n (63 + 2 * i)) := fun i hi ↦ by
    have := hrun i hi
    simp only [StmtOk, Atom.Holds] at this
    exact this
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · rcases k with _ | _ | k
    · simpa [rowV] using l0
    · simpa [rowV] using l1
    · have := (hstep k (by omega)).1
      simp only [rowV, show k + 1 + 1 ≠ 0 by omega, ↓reduceIte, show 59 + 2 * (k + 1 + 1) = 63 + 2 * k by omega]
      exact this
  · have hsum : ∀ i ≤ 62, σ (.n (62 + 2 * i)) = ∑ k ∈ Finset.range (i + 2), rowV σ k := by
      intro i hi
      induction i with
      | zero => simp [Finset.sum_range_succ, rowV, a2]
      | succ i ih =>
        rw [show 62 + 2 * (i + 1) = 64 + 2 * i by omega, (hstep i (by omega)).2, ih (by omega),
          Finset.sum_range_succ _ (i + 1 + 1)]
        simp only [rowV, show i + 1 + 1 ≠ 0 by omega, ↓reduceIte, show 59 + 2 * (i + 1 + 1) = 63 + 2 * i by omega]
    rw [hm, hsum 62 le_rfl]

/-- **The pointers' scales.** -/
theorem rq_facts (hA : AllOk C rd σ cstRq) : ∀ q < 33, LoadHolds rd (σ (.n 11)) (62 + q) (σ (.n (188 + 2 * q))) ∧
    σ (.n (189 + 2 * q)) = σ (.n 13) * σ (.n (188 + 2 * q)) ∧ LoadHolds rd (σ (.n 33)) q (σ (.n (189 + 2 * q))) := by
  intro q hq
  have := (allOk_flatten_range _ _).1 hA q hq
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at this
  exact this

/-- **A table's masks.** -/
theorem masks_facts : ∀ (ks : List ℕ) (v q : ℕ), AllOk C rd σ (cstMasks v q ks) →
    ∀ i < ks.length, ∃ val, LoadHolds rd (σ (.n 32)) (q + i) val ∧
      (ks.getD i 0 < 52 → LoadHolds rd (σ (.n 43)) (ks.getD i 0) val) ∧
      (52 ≤ ks.getD i 0 → ∃ w, LoadHolds rd (σ (.n 39)) (ks.getD i 0 + 10) w ∧ val = w * σ (.n 52))
  | [], _, _, _ => fun i hi ↦ absurd hi (by simp)
  | k :: ks, v, q, hA => by
    rw [cstMasks, allOk_append] at hA
    intro i hi
    rcases i with _ | i
    · simp only [List.getD_cons_zero, Nat.add_zero]
      unfold cstMask at hA
      split_ifs at hA with hk
      · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hA
        exact ⟨_, hA.1.2, fun _ ↦ hA.1.1, fun h ↦ absurd h (by omega)⟩
      · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hA
        obtain ⟨⟨h1, h2, h3⟩, -⟩ := hA
        exact ⟨_, h3, fun h ↦ absurd h hk, fun _ ↦ ⟨_, h1, h2⟩⟩
    · obtain ⟨val, h1, h2, h3⟩ := masks_facts ks _ (q + 1) hA.2 i (by simpa using hi)
      refine ⟨val, by rw [show q + (i + 1) = q + 1 + i by omega]; exact h1, ?_, ?_⟩ <;>
        simpa only [List.getD_cons_succ]

/-- **`kb^64`.** -/
theorem sq_facts {w kb : ℕ} (hA : AllOk C rd σ (cstSq w kb)) : σ (.n (w + 5)) = σ (.n kb) ^ 64 := by
  simp only [cstSq, allOk_cons] at hA
  obtain ⟨h0, h⟩ := hA
  have hs : ∀ i < 5, σ (.n (w + 1 + i)) = σ (.n (w + i)) * σ (.n (w + i)) := fun i hi ↦ by
    have := h _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
    simpa only [StmtOk, Atom.Holds] using this
  simp only [StmtOk, Atom.Holds] at h0
  have e : ∀ i ≤ 5, σ (.n (w + i)) = σ (.n kb) ^ 2 ^ (i + 1) := by
    intro i hi
    induction i with
    | zero => rw [Nat.add_zero, h0]; ring
    | succ i ih => rw [show w + (i + 1) = w + 1 + i by omega, hs i (by omega), ih (by omega)]; ring
  rw [e 5 le_rfl]
  norm_num

/-- **A later table**: its masks, `kb^64`, the scales' and masks' pointers, `ring_cols` and the sum. -/
theorem tab_facts {v0 q0 kb rq pm acc : ℕ} {ks : List ℕ} {W : E} {name : String}
    (hA : AllOk C rd σ (cstTab v0 q0 ks kb W rq pm acc name)) :
    (∀ i < ks.length, ∃ val, LoadHolds rd (σ (.n 32)) (q0 + i) val ∧
      (ks.getD i 0 < 52 → LoadHolds rd (σ (.n 43)) (ks.getD i 0) val) ∧
      (52 ≤ ks.getD i 0 → ∃ w, LoadHolds rd (σ (.n 39)) (ks.getD i 0 + 10) w ∧ val = w * σ (.n 52))) ∧
    C name [σ (.n 31) * σ (.n kb) ^ 64, σ (.n rq) * W, σ (.n pm) * W] [σ (.n (v0 + masksVals ks + 11))] ∧
    σ (.n (v0 + masksVals ks + 12)) = σ (.n acc) + σ (.n (v0 + masksVals ks + 11)) ∧
    σ (.n (v0 + masksVals ks + 8)) = σ (.n rq) * W ∧ σ (.n (v0 + masksVals ks + 10)) = σ (.n pm) * W := by
  unfold cstTab at hA
  simp only [allOk_append, allOk_cons, allOk_nil, and_true] at hA
  obtain ⟨⟨hm, hs⟩, h6, h7, h8, h9, h10, hc, h12⟩ := hA
  simp only [StmtOk, Atom.Holds, List.map_cons, List.map_nil] at h6 h7 h8 h9 h10 hc h12
  rw [h7] at h8
  rw [h9] at h10
  refine ⟨masks_facts ks v0 q0 hm, ?_, h12, h8, h10⟩
  rw [h6, sq_facts hs, h8, h10] at hc
  exact hc

/-- **Table `0`.** -/
theorem tab0_facts (hA : AllOk C rd σ cstTab0) :
    (∀ i < 5, ∃ val, LoadHolds rd (σ (.n 32)) i val ∧
      LoadHolds rd (σ (.n 43)) ([9, 8, 5, 6, 7].getD i 0) val) ∧
    C "ring_cols__L5" [σ (.n 31) * σ (.n 46) ^ 64, σ (.n 33), σ (.n 32)] [σ (.n 471)] := by
  unfold cstTab0 at hA
  simp only [allOk_append, allOk_cons, allOk_nil, and_true] at hA
  obtain ⟨⟨hm, hs⟩, h6, hc⟩ := hA
  simp only [StmtOk, Atom.Holds, List.map_cons, List.map_nil] at h6 hc
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · obtain ⟨val, h1, h2, -⟩ := masks_facts _ 459 0 hm i (by simpa using hi)
    refine ⟨val, by simpa using h1, h2 ?_⟩
    interval_cases i <;> decide
  · rw [h6, sq_facts hs] at hc
    exact hc

/-- **The ring segment.** -/
theorem ring_facts (hA : AllOk C rd σ cstRing) :
    C "ring_rows" [σ (.n 31), σ (.n 5), σ (.n 18), σ (.n 12), σ (.n 6)] [] ∧ σ (.n 254) = σ (.n 17) * σ (.n 51) ∧
    (∀ a, Stmt.atom a ∈ eqtreeT (.n 254) (.n 39) 0 255 6 → a.Holds rd σ) ∧ AllOk C rd σ cstTab0 ∧
    AllOk C rd σ (cstTab 472 5 [18, 17, 14, 15, 16] 47 (word 32 0) 33 32 471 "ring_cols__L5") ∧
    AllOk C rd σ (cstTab 490 10 [23, 22, 21] 48 (word 32 0) 485 487 489 "ring_cols__L3") ∧
    AllOk C rd σ (cstTab 506 13 [33, 32, 29, 30, 31] 49 (word 8192 0) 33 32 505 "ring_cols__L5") ∧
    AllOk C rd σ (cstTab 524 18 [47, 46, 43, 44, 45] 50 (word 32 0) 519 521 523 "ring_cols__L5") ∧
    AllOk C rd σ (cstTab 542 23 [51, 50, 110, 111, 112, 113, 114, 115, 48, 49] 51 (word 32 0) 537 539 541
      "ring_cols__L10") ∧
    σ (.n 571) = σ (.n 187) + σ (.n 570) := by
  unfold cstRing at hA
  simp only [allOk_append, allOk_cons, allOk_nil, and_true] at hA
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hr, hm⟩, het⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, hadd⟩ := hA
  simp only [StmtOk, Atom.Holds, List.map_cons, List.map_nil] at hr hm hadd
  exact ⟨hr, hm, fun a ha ↦ het _ ha, h0, h1, h2, h3, h4, h5, hadd⟩

/-- **The prefix chains and the claims before the sent columns.** -/
theorem mem_facts (hA : AllOk C rd σ cstMem) :
    C "eq_prefix_chain" [σ (.n 36), 1, σ (.n 7), σ (.n 18), σ (.n 8)] [] ∧
    LoadHolds rd (σ (.n 36) * σ (.n 8)) 0 (σ (.n 574)) ∧
    σ (.n 578) = σ (.n 574) * (σ (.n 15) * σ (.n 53) + σ (.n 16) * σ (.n 54)) ∧
    LoadHolds rd (σ (.n 38)) 0 (σ (.n 9)) ∧ (∀ i < 30, LoadHolds rd (σ (.n 38)) (i + 1) 0) ∧
    C "eq_prefix_chain" [σ (.n 37), 1, σ (.n 38), σ (.n 18), σ (.n 8)] [] ∧
    LoadHolds rd (σ (.n 37) * σ (.n 8)) 0 (σ (.n 611)) ∧
    C "eq_prefix_chain" [σ (.n 35), 1, σ (.n 10), σ (.n 18), σ (.n 51) * gen ^ 6] [] ∧
    C "eq_prefix_chain" [σ (.n 40), 1, σ (.n 22), σ (.n 18), σ (.n 4)] [] ∧
    C "eq_prefix_chain" [σ (.n 34), 1, σ (.n 5), σ (.n 18), σ (.n 6)] [] ∧
    LoadHolds rd (σ (.n 40) * σ (.n 4)) 0 (σ (.n 618)) ∧ LoadHolds rd (σ (.n 35) * σ (.n 51)) 6 (σ (.n 621)) ∧
    LoadHolds rd (σ (.n 34) * σ (.n 51)) 0 (σ (.n 631)) ∧
    σ (.n 629) = ((σ (.n 618) * σ (.n 14) + σ (.n 621) * σ (.n 52)) * σ (.n 14) + σ (.n 611) * σ (.n 54)) *
      σ (.n 14) + σ (.n 611) * σ (.n 53) ∧
    σ (.n 632) = σ (.n 631) * σ (.n 52) := by
  unfold cstMem at hA
  simp only [allOk_append, allOk_cons, allOk_nil, and_true, allOk_flatten_range] at hA
  obtain ⟨⟨⟨c572, ch1, m573, l574, m575, m576, a577, m578, l9⟩, hz⟩, c609, ch2, m610, l611, c612, c613, m614, ch3,
    c615, ch4, c616, ch5, m617, l618, m619, m620, l621, m622, a623, m624, m625, a626, m627, m628, a629, m630,
    l631, m632⟩ := hA
  simp only [StmtOk, Atom.Holds, List.map_cons, List.map_nil] at c572 ch1 m573 l574 m575 m576 a577 m578 l9
  simp only [StmtOk, Atom.Holds, List.map_cons, List.map_nil] at c609 ch2 m610 l611 c612 c613 m614 ch3
  simp only [StmtOk, Atom.Holds, List.map_cons, List.map_nil] at c615 ch4 c616 ch5 m617 l618 m619 m620 l621
  simp only [StmtOk, Atom.Holds] at m622 a623 m624 m625 a626 m627 m628 a629
  simp only [StmtOk, Atom.Holds] at m630 l631 m632
  rw [c572, word_one] at ch1
  rw [c609, word_one] at ch2
  rw [c612, word_one, m614, c613, word_g6] at ch3
  rw [c615, word_one] at ch4
  rw [c616, word_one] at ch5
  rw [m573] at l574
  rw [m610] at l611
  rw [m617] at l618
  rw [m620] at l621
  rw [m630] at l631
  refine ⟨ch1, l574, by rw [m578, a577, m575, m576], l9, fun i hi ↦ ?_, ch2, l611, ch3, ch4, ch5, l618, l621, l631,
    by rw [a629, m627, m628, a626, m624, m625, a623, m619, m622], m632⟩
  obtain ⟨hc, hl⟩ := hz i hi
  simp only [StmtOk, Atom.Holds] at hc hl
  rw [hc, word_zero] at hl
  exact hl

/-- Where `cstSent`'s batch ends. -/
def sentAcc : ℕ → ℕ → List ℕ → ℕ
  | _, acc, [] => acc
  | v, _, k :: ks => sentAcc (v + sentVals k) (v + sentVals k - 1) ks

/-- **The sent columns, by Horner**: on weights `W` the reads give, the batch is `W`'s fold. -/
theorem sent_facts (W : ℕ → E) : ∀ (ks : List ℕ) (v acc : ℕ), AllOk C rd σ (cstSent v acc ks) →
    (∀ k ∈ ks, (k < 52 → ∀ a b c, LoadHolds rd (σ (.n 3)) k a → LoadHolds rd (σ (.n 34) * a) 0 b →
        LoadHolds rd (σ (.n 43)) k c → b * c = W k) ∧
      (52 ≤ k → ∀ a, LoadHolds rd (σ (.n 39)) (k + 10) a → σ (.n 632) * a = W k)) →
    σ (.n (sentAcc v acc ks)) = ks.foldl (fun a k ↦ a * σ (.n 14) + W k) (σ (.n acc))
  | [], _, _, _, _ => rfl
  | k :: ks, v, acc, hA, hW => by
    rw [cstSent, allOk_append] at hA
    rw [sentAcc, List.foldl_cons, sent_facts W ks _ _ hA.2 fun k' hk' ↦ hW k' (List.mem_cons_of_mem _ hk')]
    congr 1
    obtain ⟨hb, hs⟩ := hW k List.mem_cons_self
    have h1 := hA.1
    unfold cstSentOne at h1
    unfold sentVals
    split_ifs at h1 ⊢ with hk
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h1
      obtain ⟨l0, m1, l2, l3, m4, m5, a6⟩ := h1
      rw [show v + 7 - 1 = v + 6 by omega, a6, m5, m4, hb hk _ _ _ l0 (m1 ▸ l2) l3]
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h1
      obtain ⟨l0, m1, m2, a3⟩ := h1
      rw [show v + 4 - 1 = v + 3 by omega, a3, m2, m1, hs (by omega) _ l0]

/-- **The check.** -/
theorem tail_facts (hA : AllOk C rd σ cstTail) :
    (σ (.n 19) + (σ (.n 571) + (σ (.n 918) * σ (.n 14) + σ (.n 578)) * σ (.n 14))) * σ (.n 20) = σ (.n 21) := by
  unfold cstTail at hA
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hA
  obtain ⟨m919, a920, m921, a922, a923, m924, hassert⟩ := hA
  rw [← e_add_eq_zero_iff.mp hassert, m924, a923, a922, m921, a920, m919]

end
end LeanVM.Guest.B1.Stack
