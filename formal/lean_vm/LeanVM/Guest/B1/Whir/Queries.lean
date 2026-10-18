/-
  LeanVM.Guest.B1.Whir.Queries

  B1 for `opening_queries` and its loop: per query, the leaf row and its dot product with the
  row weights, the leaf hash, `verify_merkle_path` below the cap, and the cap leaf.
-/

module

public import LeanVM.Guest.B1.Whir.QueriesT

/-!
# `opening_queries` (TRIAGE #28, #35)

The blocks of `oqLoopBody`, each as a lemma: soundness (`*_sound`, the block's facts from its
relation) and completeness (`*_complete`, the relation from the block's honest values and its
facts).

* the row (`RowFacts`): its words in `K`, its packed cells, its dot product with the weights;
* the leaf hash (`leaf_digest`): `hashWords` (`Spec/Blake2s.lean:201`) of the row's words, when
  the row fills `blocks` whole blocks;
* the Merkle path (`PathFacts`): `verify_merkle_path` (G:899-916, TRIAGE #28), each level's
  selected child the running node, pinned by the frame run and the Boolean direction bit;
* the cap leaf (`CapFacts`): the parent's flag and the path's top.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Atom-only blocks -/

theorem holdsList_true_of {ss : List Stmt} {next : Prop} {kret : List E → Prop}
    (hs : Stmt.noRetList ss = true) (h : Stmt.HoldsList C rd σ ss next kret) :
    Stmt.HoldsList C rd σ ss True kret ∧ next :=
  (holdsList_noRet ss hs next kret).mp h

/-! ## The row -/

/-- The number of hinted row words: `I` at level 0, `3I` limbs deeper. -/
def oqR (base I : ℕ) : ℕ := if base = 1 then I else 3 * I

/-- Row word `jw`: level 0's word `jw`, a deeper level's three limbs at `3jw`. -/
def oqRowWord (base : ℕ) (r : ℕ → E) (jw : ℕ) : E :=
  if base = 1 then r jw else E.ofLimbs ((r (3 * jw)).limb 0) ((r (3 * jw + 1)).limb 0) ((r (3 * jw + 2)).limb 0)

/-- The row values of `σ`. -/
def rowv (σ : Val) (j : ℕ) : E := σ (.n (8 + j))

/-- What the row asks: its words in `K`, its packed cells, the weights readable, and the dot
product of its words with them. -/
def RowFacts (base I : ℕ) (rd : Reader) (σ : Val) : Prop :=
  (∀ j < oqR base I, IsInK (rowv σ j)) ∧
    (∀ j < oqR base I / 2, σ (.n (oqPk base I j)) =
      E.ofLimbs ((rowv σ (2 * j)).limb 0) ((rowv σ (2 * j + 1)).limb 0) 0) ∧
    (∀ jw < I, LoadHolds rd (σ (.n 2)) jw (memAt rd (σ (.n 2)) jw)) ∧
    σ (.n (oqK1 base I - 1)) =
      ∑ jw ∈ Finset.range I, oqRowWord base (rowv σ) jw * memAt rd (σ (.n 2)) jw

theorem holds_pack4T (b r : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (pack4T b r) next kret ↔
      (IsInK (σ (.n r)) ∧ IsInK (σ (.n (r + 1))) ∧ σ (.n b) = y ∧ σ (.n (b + 1)) = y * σ (.n (r + 1)) ∧
        σ (.n (b + 2)) = E.ofLimbs ((σ (.n r)).limb 0) ((σ (.n (r + 1))).limb 0) 0) ∧
      (IsInK (σ (.n (r + 2))) ∧ IsInK (σ (.n (r + 3))) ∧ σ (.n (b + 3)) = y ∧
        σ (.n (b + 3 + 1)) = y * σ (.n (r + 3)) ∧
        σ (.n (b + 3 + 2)) = E.ofLimbs ((σ (.n (r + 2))).limb 0) ((σ (.n (r + 3))).limb 0) 0) ∧ next := by
  rw [pack4T, holdsList_append, holds_pack64x2T, holds_pack64x2T]

/-- The dot block's facts: the four weights readable, and the sum. -/
theorem dot4T_sound {b r wo : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (dot4T b r wo) next kret) :
    (∀ t < 4, LoadHolds rd (σ (.n 2)) (wo + t) (memAt rd (σ (.n 2)) (wo + t))) ∧
      σ (.n (b + 10)) = ∑ t ∈ Finset.range 4, σ (.n (r + t)) * memAt rd (σ (.n 2)) (wo + t) ∧ next := by
  simp only [dot4T, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, h1, l2, h3, h4, l5, h6, h7, l8, h9, h10, hn⟩ := h
  refine ⟨fun t ht => ?_, ?_, hn⟩
  · interval_cases t
    · exact loadHolds_memAt l0
    · exact loadHolds_memAt l2
    · exact loadHolds_memAt l5
    · exact loadHolds_memAt l8
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero,
      memAt_of_load l0, memAt_of_load l2, memAt_of_load l5, memAt_of_load l8]
    rw [h10, h7, h9, h4, h6, h1, h3]

/-- The facts of two packs and a dot block over the words `r .. r + 3`. -/
theorem pack4dot_sound {b r wo : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (pack4T b r ++ dot4T (b + 6) r wo) next kret) :
    (∀ t < 4, IsInK (σ (.n (r + t)))) ∧
      σ (.n (b + 2)) = E.ofLimbs ((σ (.n r)).limb 0) ((σ (.n (r + 1))).limb 0) 0 ∧
      σ (.n (b + 3 + 2)) = E.ofLimbs ((σ (.n (r + 2))).limb 0) ((σ (.n (r + 3))).limb 0) 0 ∧
      (∀ t < 4, LoadHolds rd (σ (.n 2)) (wo + t) (memAt rd (σ (.n 2)) (wo + t))) ∧
      σ (.n (b + 6 + 10)) = ∑ t ∈ Finset.range 4, σ (.n (r + t)) * memAt rd (σ (.n 2)) (wo + t) ∧
      next := by
  rw [holdsList_append, holds_pack4T] at h
  obtain ⟨⟨k0, k1, -, -, p0⟩, ⟨k2, k3, -, -, p1⟩, h⟩ := h
  obtain ⟨hl, hs, hn⟩ := dot4T_sound h
  refine ⟨fun t ht => ?_, p0, p1, hl, hs, hn⟩
  interval_cases t
  · exact k0
  · exact k1
  · exact k2
  · exact k3

/-- The four weighted words of block `jb`. -/
def rowFour (rd : Reader) (σ : Val) (jb : ℕ) : E :=
  ∑ t ∈ Finset.range 4, rowv σ (4 * jb + t) * memAt rd (σ (.n 2)) (4 * jb + t)

theorem sum_range_four_mul (f : ℕ → E) (jb : ℕ) :
    ∑ j ∈ Finset.range (4 * (jb + 1)), f j = ∑ j ∈ Finset.range (4 * jb), f j +
      ∑ t ∈ Finset.range 4, f (4 * jb + t) := by
  rw [show 4 * (jb + 1) = 4 * jb + 4 by ring, Finset.sum_range_add]

/-- Level 0's row (`base = 1`), from its relation: `I ≥ 4` words in blocks of four. -/
theorem oqRows1_sound {I : ℕ} (hI : 4 ≤ I) (h4 : I % 4 = 0) {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (oqRows1 I) True kret) : RowFacts 1 I rd σ := by
  rw [oqRows1, holdsList_append, holdsList_append] at h
  simp only [oqRowHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  rw [rowHead1T] at h
  obtain ⟨k0, p00, p01, l0, s0, h⟩ := pack4dot_sound h
  rw [holdsList_range_flatten _ _ (fun _ => rfl)] at h
  obtain ⟨hb, -⟩ := h
  have hblk : ∀ j < I / 4 - 1, (∀ t < 4, IsInK (σ (.n (8 + 4 * (j + 1) + t)))) ∧
      σ (.n (7 + I + 18 * (j + 1) + 2)) =
        E.ofLimbs ((σ (.n (8 + 4 * (j + 1)))).limb 0) ((σ (.n (8 + 4 * (j + 1) + 1))).limb 0) 0 ∧
      σ (.n (7 + I + 18 * (j + 1) + 3 + 2)) =
        E.ofLimbs ((σ (.n (8 + 4 * (j + 1) + 2))).limb 0) ((σ (.n (8 + 4 * (j + 1) + 3))).limb 0) 0 ∧
      (∀ t < 4, LoadHolds rd (σ (.n 2)) (4 * (j + 1) + t) (memAt rd (σ (.n 2)) (4 * (j + 1) + t))) ∧
      σ (.n (6 + I + 18 * (j + 2))) = σ (.n (6 + I + 18 * (j + 1))) + rowFour rd σ (j + 1) := by
    intro j hj
    have hj' := hb j hj
    rw [oq1Blk, rowBlk1T, holdsList_append] at hj'
    obtain ⟨k, p0, p1, l, s, ha⟩ := pack4dot_sound hj'
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at ha
    refine ⟨k, p0, p1, l, ?_⟩
    rw [show 6 + I + 18 * (j + 2) = 7 + I + 18 * (j + 1) + 17 by ring, ha,
      show 7 + I + 18 * (j + 1) + 16 = 7 + I + 18 * (j + 1) + 6 + 10 by ring, s]
    simp only [rowFour, rowv]
    exact congrArg (σ (.n (6 + I + 18 * (j + 1))) + ·) (Finset.sum_congr rfl fun t _ => by
      rw [show 8 + (4 * (j + 1) + t) = 8 + 4 * (j + 1) + t by ring])
  have hn4 : 4 * (I / 4) = I := by omega
  -- the partial sums
  have hps : ∀ jb < I / 4, σ (.n (6 + I + 18 * (jb + 1))) =
      ∑ j ∈ Finset.range (4 * (jb + 1)), rowv σ j * memAt rd (σ (.n 2)) j := by
    intro jb hjb
    induction jb with
    | zero =>
      rw [show 6 + I + 18 * (0 + 1) = 8 + I + 6 + 10 by ring, s0]
      simp only [rowv, Nat.zero_add, Nat.mul_one]
    | succ jb ih =>
      rw [(hblk jb (by omega)).2.2.2.2, ih (by omega), sum_range_four_mul _ (jb + 1)]
      rfl
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun jw hjw => ?_, ?_⟩
  · simp only [oqR, ↓reduceIte] at hj
    obtain ⟨jb, t, ht, rfl⟩ : ∃ jb t, t < 4 ∧ j = 4 * jb + t := ⟨j / 4, j % 4, by omega, by omega⟩
    rcases Nat.eq_zero_or_pos jb with h0 | hpos
    · subst h0
      simpa [rowv] using k0 t ht
    · have := (hblk (jb - 1) (by omega)).1 t ht
      rw [show jb - 1 + 1 = jb by omega] at this
      simpa [rowv, show 8 + (4 * jb + t) = 8 + 4 * jb + t by ring] using this
  · simp only [oqR, ↓reduceIte] at hj
    obtain ⟨jb, e, he, rfl⟩ : ∃ jb e, e < 2 ∧ j = 2 * jb + e := ⟨j / 2, j % 2, by omega, by omega⟩
    have hd : (2 * jb + e) / 2 = jb := by omega
    have hm : (2 * jb + e) % 2 = e := by omega
    simp only [oqPk, ↓reduceIte, hd, hm, rowv]
    rcases Nat.eq_zero_or_pos jb with h0 | hpos
    · subst h0
      interval_cases e
      · simpa using p00
      · simpa [show 8 + I + 2 + 3 = 8 + I + 3 + 2 by ring] using p01
    · have hb' := hblk (jb - 1) (by omega)
      rw [show jb - 1 + 1 = jb by omega] at hb'
      simp only [show jb ≠ 0 by omega, ↓reduceIte]
      interval_cases e
      · simpa [show 8 + 2 * (2 * jb) = 8 + 4 * jb by ring,
          show 8 + (2 * (2 * jb) + 1) = 8 + 4 * jb + 1 by ring] using hb'.2.1
      · simpa [show 7 + I + 18 * jb + 2 + 3 * 1 = 7 + I + 18 * jb + 3 + 2 by ring,
          show 8 + 2 * (2 * jb + 1) = 8 + 4 * jb + 2 by ring,
          show 8 + (2 * (2 * jb + 1) + 1) = 8 + 4 * jb + 3 by ring] using hb'.2.2.1
  · obtain ⟨jb, t, ht, rfl⟩ : ∃ jb t, t < 4 ∧ jw = 4 * jb + t := ⟨jw / 4, jw % 4, by omega, by omega⟩
    rcases Nat.eq_zero_or_pos jb with h0 | hpos
    · subst h0
      simpa using l0 t ht
    · have := (hblk (jb - 1) (by omega)).2.2.2.1 t ht
      rwa [show jb - 1 + 1 = jb by omega] at this
  · have := hps (I / 4 - 1) (by omega)
    rw [show I / 4 - 1 + 1 = I / 4 by omega, hn4] at this
    simp only [oqK1, ↓reduceIte, oqRowWord]
    rw [show 7 + I + 18 * (I / 4) - 1 = 6 + I + 18 * (I / 4) by omega, this]

/-- A deeper level's word block's facts: the word from its limbs and packed cells, its weight
readable, and the product. -/
theorem word0_sound {R jw c : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (oq0WordT R jw c ++ wordDotT c jw) next kret) :
    σ (.n (c + 2)) = (if jw % 2 = 0 then σ (.n (oq0Pk R (3 * jw / 2))) + y * y * σ (.n (8 + (3 * jw + 2)))
        else σ (.n (8 + 3 * jw)) + y * σ (.n (oq0Pk R ((3 * jw + 1) / 2)))) ∧
      LoadHolds rd (σ (.n 2)) jw (memAt rd (σ (.n 2)) jw) ∧
      σ (.n (c + 4)) = σ (.n (c + 2)) * memAt rd (σ (.n 2)) jw ∧ next := by
  rw [holdsList_append, oq0WordT] at h
  split at h
  · rename_i he
    simp only [wordEvenT, wordDotT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_yy] at h
    obtain ⟨h0, h1, h2, l3, h4, hn⟩ := h
    refine ⟨?_, loadHolds_memAt l3, by rw [h4, memAt_of_load l3], hn⟩
    rw [ite_pos' he, h2, h1, h0]
  · rename_i he
    simp only [wordOddT, wordDotT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_y] at h
    obtain ⟨h0, h1, h2, l3, h4, hn⟩ := h
    refine ⟨?_, loadHolds_memAt l3, by rw [h4, memAt_of_load l3], hn⟩
    rw [ite_neg' he, h2, h1, h0]

theorem ofLimbs_add_yy {a b : K} {z : E} (hz : IsInK z) :
    E.ofLimbs a b 0 + y * y * z = E.ofLimbs a b (z.limb 0) := by
  rw [eq_ofK_limb hz, add_y_mul_y_mul_ofK]
  simp [limb_ofK]

theorem ofK_add_y_ofLimbs {z : E} (hz : IsInK z) (b c : K) :
    z + y * E.ofLimbs b c 0 = E.ofLimbs (z.limb 0) b c := by
  rw [eq_ofK_limb hz, mul_comm, ofLimbs_mul_y, ofK_eq_ofLimbs, ofLimbs_add]
  simp

theorem oq0Blk_noRet (I jw : ℕ) : Stmt.noRetList (oq0Blk I jw) = true := by
  unfold oq0Blk oq0WordT
  split <;> rfl

/-- A deeper level's row (`base = 0`), from its relation: `I ≥ 4` words, a multiple of four. -/
theorem oqRows0_sound {I : ℕ} (hI : 4 ≤ I) (h4 : I % 4 = 0) {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (oqRows0 I) True kret) : RowFacts 0 I rd σ := by
  rw [oqRows0, holdsList_append, holdsList_append, holdsList_append, holdsList_append] at h
  simp only [oqRowHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  rw [holdsList_range_flatten _ _ (fun _ => rfl)] at h
  obtain ⟨hp, h⟩ := h
  rw [← holdsList_append] at h
  obtain ⟨w0, l0, m0, h⟩ := word0_sound h
  rw [holdsList_range_flatten _ _ (fun _ => oq0Blk_noRet _ _)] at h
  obtain ⟨hb, -⟩ := h
  have hpk : ∀ jb < 3 * I / 4, (∀ t < 4, IsInK (σ (.n (8 + 4 * jb + t)))) ∧
      σ (.n (oq0Pk (3 * I) (2 * jb))) =
        E.ofLimbs ((σ (.n (8 + 4 * jb))).limb 0) ((σ (.n (8 + 4 * jb + 1))).limb 0) 0 ∧
      σ (.n (oq0Pk (3 * I) (2 * jb + 1))) =
        E.ofLimbs ((σ (.n (8 + 4 * jb + 2))).limb 0) ((σ (.n (8 + 4 * jb + 3))).limb 0) 0 := by
    intro jb hjb
    have := hp jb hjb
    rw [oq0Pack, holds_pack4T] at this
    obtain ⟨⟨k0, k1, -, -, p0⟩, ⟨k2, k3, -, -, p1⟩, -⟩ := this
    refine ⟨fun t ht => ?_, ?_, ?_⟩
    · interval_cases t
      · simpa using k0
      · exact k1
      · exact k2
      · exact k3
    · rw [oq0Pk, show 10 + 3 * I + 3 * (2 * jb) = 8 + 3 * I + 6 * jb + 2 by ring]; exact p0
    · rw [oq0Pk, show 10 + 3 * I + 3 * (2 * jb + 1) = 8 + 3 * I + 6 * jb + 3 + 2 by ring]; exact p1
  have hK : ∀ j < 3 * I, IsInK (rowv σ j) := fun j hj => by
    have := (hpk (j / 4) (by omega)).1 (j % 4) (by omega)
    rwa [show 8 + 4 * (j / 4) + j % 4 = 8 + j by omega] at this
  have hpkv : ∀ j < 3 * I / 2, σ (.n (oq0Pk (3 * I) j)) =
      E.ofLimbs ((rowv σ (2 * j)).limb 0) ((rowv σ (2 * j + 1)).limb 0) 0 := fun j hj => by
    rcases Nat.even_or_odd j with ⟨jb, rfl⟩ | ⟨jb, rfl⟩
    · have := (hpk jb (by omega)).2.1
      rw [show jb + jb = 2 * jb by ring, this]
      simp only [rowv, show 8 + 2 * (2 * jb) = 8 + 4 * jb by ring,
        show 8 + (2 * (2 * jb) + 1) = 8 + 4 * jb + 1 by ring]
    · have := (hpk jb (by omega)).2.2
      rw [this]
      simp only [rowv, show 8 + 2 * (2 * jb + 1) = 8 + 4 * jb + 2 by ring,
        show 8 + (2 * (2 * jb + 1) + 1) = 8 + 4 * jb + 3 by ring]
  -- each word is its three limbs
  have hword : ∀ jw < I, (if jw % 2 = 0 then σ (.n (oq0Pk (3 * I) (3 * jw / 2))) +
      y * y * σ (.n (8 + (3 * jw + 2)))
      else σ (.n (8 + 3 * jw)) + y * σ (.n (oq0Pk (3 * I) ((3 * jw + 1) / 2)))) =
      oqRowWord 0 (rowv σ) jw := by
    intro jw hjw
    simp only [oqRowWord, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
    split
    · rename_i he
      rw [hpkv _ (by omega), show 2 * (3 * jw / 2) = 3 * jw by omega]
      exact ofLimbs_add_yy (hK (3 * jw + 2) (by omega))
    · rename_i he
      rw [hpkv _ (by omega), show 2 * ((3 * jw + 1) / 2) = 3 * jw + 1 by omega,
        show 3 * jw + 1 + 1 = 3 * jw + 2 by omega]
      exact ofK_add_y_ofLimbs (hK (3 * jw) (by omega)) _ _
  have hblk : ∀ j < I - 1, LoadHolds rd (σ (.n 2)) (j + 1) (memAt rd (σ (.n 2)) (j + 1)) ∧
      σ (.n (oq0W0 I + 6 * (j + 1) + 4)) = σ (.n (oq0W0 I + 6 * j + 4)) +
        oqRowWord 0 (rowv σ) (j + 1) * memAt rd (σ (.n 2)) (j + 1) := by
    intro j hj
    have hj' := hb j hj
    rw [oq0Blk, holdsList_append] at hj'
    obtain ⟨w, l, m, ha⟩ := word0_sound hj'
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at ha
    refine ⟨l, ?_⟩
    rw [show oq0W0 I + 6 * (j + 1) + 4 = oq0W0 I + 6 * (j + 1) - 1 + 5 by omega, ha, m, w,
      hword (j + 1) (by omega), show oq0W0 I + 6 * (j + 1) - 2 = oq0W0 I + 6 * j + 4 by omega]
  have hps : ∀ jw < I, σ (.n (oq0W0 I + 6 * jw + 4)) =
      ∑ j ∈ Finset.range (jw + 1), oqRowWord 0 (rowv σ) j * memAt rd (σ (.n 2)) j := by
    intro jw hjw
    induction jw with
    | zero => rw [Finset.sum_range_one, Nat.mul_zero, Nat.add_zero, m0, w0, hword 0 (by omega)]
    | succ jw ih => rw [(hblk jw (by omega)).2, ih (by omega), Finset.sum_range_succ _ (jw + 1)]
  refine ⟨fun j hj => hK j (by simpa [oqR] using hj), fun j hj => ?_, fun jw hjw => ?_, ?_⟩
  · simp only [oqPk, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
    exact hpkv j (by simpa [oqR] using hj)
  · rcases Nat.eq_zero_or_pos jw with h0 | hpos
    · subst h0; exact l0
    · have := (hblk (jw - 1) (by omega)).1
      rwa [show jw - 1 + 1 = jw by omega] at this
  · simp only [oqK1, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
    rw [show oq0W0 I + 6 * I - 1 - 1 = oq0W0 I + 6 * (I - 1) + 4 by omega, hps (I - 1) (by omega),
      show I - 1 + 1 = I by omega]

/-- The row, from its relation. -/
theorem oqRows_sound {base I : ℕ} (hb : base = 0 ∨ base = 1) (hI : 4 ≤ I) (h4 : I % 4 = 0)
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (oqRows base I) True kret) :
    RowFacts base I rd σ := by
  rcases hb with rfl | rfl
  · exact oqRows0_sound hI h4 h
  · exact oqRows1_sound hI h4 h

/-! ## The leaf hash -/

/-- The row's words as the leaf's words: each word's low limb. -/
def leafWords (base I : ℕ) (r : ℕ → E) : List K := (List.range (oqR base I)).map fun j => (r j).limb 0

theorem oqMd_eq (blocks jb : ℕ) : oqMd blocks jb = metadataCell (64 * (jb + 1)) (decide (jb + 1 = blocks)) := by
  rw [oqMd, metadataCell, word]
  by_cases h : jb + 1 = blocks <;> simp [h, ofBits_zero]

theorem flatMap_range_mul {α : Type} (k n : ℕ) (g : ℕ → List α) :
    (List.range n).flatMap (fun i => (List.range k).flatMap fun t => g (k * i + t)) =
      (List.range (k * n)).flatMap g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.mul_succ, List.range_add, List.flatMap_append,
      List.flatMap_singleton, List.flatMap_map]

theorem blockBytes_eq_flatMap (m : Fin 4 → E) :
    blockBytes m = (List.range 4).flatMap fun t => cellBytes (m (Fin.ofNat 4 t)) := by
  simp [blockBytes, List.range_succ, List.append_assoc]
  rfl

/-- **The leaf hash** (G:1019-1023): from its relation, the chain's last state is `hashWords`
(`Spec/Blake2s.lean:201`) of the row's words, when the row fills its `blocks ≥ 1` whole blocks. -/
theorem oqLeaf_sound {base I blocks : ℕ} (hbl : 1 ≤ blocks) (hR : oqR base I = 8 * blocks)
    (hrow : RowFacts base I rd σ) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (oqLeafT base I blocks) next kret) :
    (σ (.n (oqK1 base I + 3 * blocks)), σ (.n (oqK1 base I + 3 * blocks + 1))) =
      digestScalars (hashWords (leafWords base I (rowv σ))) ∧ next := by
  set K1 := oqK1 base I
  rw [oqLeafT, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_iv0, word_iv1] at h
  obtain ⟨h0, h1, h2, hc0, h⟩ := h
  rw [holdsList_range_flatten _ _ (fun _ => rfl)] at h
  obtain ⟨hb, hn⟩ := h
  refine ⟨?_, hn⟩
  let st : ℕ → E × E := fun j => if j = 0 then Value.ivCells else (σ (.n (K1 + 3 * j)), σ (.n (K1 + 3 * j + 1)))
  let bl : ℕ → Fin 4 → E := fun j =>
    ![σ (.n (oqPk base I (4 * j))), σ (.n (oqPk base I (4 * j + 1))), σ (.n (oqPk base I (4 * j + 2))),
      σ (.n (oqPk base I (4 * j + 3)))]
  have hst : st blocks = (σ (.n (K1 + 3 * blocks)), σ (.n (K1 + 3 * blocks + 1))) := by
    simp only [st, show blocks ≠ 0 by omega, ↓reduceIte]
  have hc : ∀ j ≤ blocks - 1, CompressCells (bl j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2
      (oqMd blocks j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp only [st, ↓reduceIte, Nat.one_ne_zero, Nat.mul_one, bl, Nat.mul_zero, Nat.zero_add]
      rw [← h0, ← h1, ← h2]
      exact hc0
    · have := hb (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at this
      simp only [oqLeafBlk, leafBlkT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
      obtain ⟨hm, hc⟩ := this
      simp only [st, show j ≠ 0 by omega, show j + 1 ≠ 0 by omega, ↓reduceIte, bl]
      rw [← hm, show K1 + 3 * (j + 1) = K1 + 3 * j + 2 + 1 by ring,
        show K1 + 3 * j + 2 + 1 + 1 = K1 + 3 * j + 2 + 2 by ring]
      exact hc
  have hchain := chain_eq_blake2sBytes_blocks (n := blocks - 1) (blocks := bl) (st := st)
    (md := oqMd blocks) (by simp [st])
    (fun j hj => by rw [oqMd_eq]; congr 1; simp; omega)
    (by rw [oqMd_eq, show blocks - 1 + 1 = blocks by omega]; simp)
    hc
  rw [show blocks - 1 + 1 = blocks by omega, hst] at hchain
  rw [hchain, hashWords]
  congr 2
  obtain ⟨-, hpk, -, -⟩ := hrow
  rw [leafWords, hR, List.flatMap_map, show 8 * blocks = 2 * (4 * blocks) by ring,
    ← flatMap_range_mul 2 (4 * blocks), ← flatMap_range_mul 4 blocks]
  refine List.flatMap_congr fun jb hjb => ?_
  rw [List.mem_range] at hjb
  rw [blockBytes_eq_flatMap]
  refine List.flatMap_congr fun t ht => ?_
  rw [List.mem_range] at ht
  have hfin : ((Fin.ofNat 4 t : Fin 4) : ℕ) = t := by simp [Fin.ofNat, Nat.mod_eq_of_lt ht]
  have hbl : bl jb (Fin.ofNat 4 t) = σ (.n (oqPk base I (4 * jb + t))) := by
    interval_cases t <;> rfl
  rw [hbl, hpk _ (by omega), cellBytes]
  simp [List.range_succ, rowv]

/-! ## The query sum, the path and the cap leaf -/

/-- The query sum and the bit run (`oqSumT`), from their relation. -/
theorem oqSum_sound {base I blocks : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (oqSumT base I blocks) next kret) :
    let k := oqK2 base I blocks
    LoadHolds rd (σ (.n 3) * σ (.n 0)) 0 (σ (.n (k + 1))) ∧
      LoadHolds rd (σ (.n 4) * σ (.n 0)) 0 (σ (.n (k + 3))) ∧
      LoadHolds rd (σ (.n 3) * σ (.n 0)) 1
        (σ (.n (k + 1)) + σ (.n (k + 3)) * σ (.n (oqK1 base I - 1))) ∧
      LoadHolds rd (σ (.n 5) * σ (.n 0)) 0 (σ (.n (k + 8))) ∧ next := by
  simp only [oqSumT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨h0, l1, h2, l3, h4, h5, h6, l7, h8, l9, hn⟩ := h
  rw [h0] at l1
  rw [h2] at l3
  rw [h6, h5, h4] at l7
  rw [h8] at l9
  exact ⟨l1, l3, l7, l9, hn⟩

/-- The index of the running node entering path level `l`. -/
def oqNode (P K l : ℕ) : ℕ := if l = 0 then K else P + 77 + 13 * l

theorem getElem_frameRun {P pd k : ℕ} (hk : k < 4 * pd) (h : k < ((List.range (4 * pd)).map (fun j => V.n (P + j)) ++
      (List.range (80 - 4 * pd)).map fun j => V.n (P + 4 * pd + 1 + j)).length) :
    ((List.range (4 * pd)).map (fun j => V.n (P + j)) ++
      (List.range (80 - 4 * pd)).map fun j => V.n (P + 4 * pd + 1 + j))[k] = V.n (P + k) := by
  rw [List.getElem_append_left (by simpa using hk)]
  simp

/-- What one path level asks: the direction word `d`, the running node at the child it selects,
the level's four children hashed into the next node. -/
def PathLevel (rd : Reader) (σ : Val) (P pd K l : ℕ) : Prop :=
  ∃ d, LoadHolds rd (σ (.n (P - 1))) l d ∧
    LoadHolds rd (σ (.n (P + 4 * pd)) * gen ^ (4 * l) * (1 + d * eOfNat 5)) 0 (σ (.n (oqNode P K l))) ∧
    LoadHolds rd (σ (.n (P + 4 * pd)) * gen ^ (4 * l) * (1 + d * eOfNat 5)) 1 (σ (.n (oqNode P K l + 1))) ∧
    CompressCells ![σ (.n (P + 4 * l)), σ (.n (P + 4 * l + 1)), σ (.n (P + 4 * l + 2)),
        σ (.n (P + 4 * l + 3))] Value.ivCells.1 Value.ivCells.2 (σ (.n (oqNode P K (l + 1))))
      (σ (.n (oqNode P K (l + 1) + 1))) (metadataCell 64 true)

/-- `verify_merkle_path` (`oqPathT`), from its relation: the frame run of the hinted children, and
every level. -/
theorem oqPath_sound {base I blocks pd : ℕ} (hpd : 1 ≤ pd) (hpd20 : pd ≤ 20) {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (oqPathT base I blocks pd) next kret) :
    (IsInK (σ (.n (oqP base I blocks + 4 * pd))) ∧ ∀ k < 4 * pd, ∀ w,
        rd ((σ (.n (oqP base I blocks + 4 * pd))).limb 0 * Parameters.gpow k) = some w →
          w = σ (.n (oqP base I blocks + k))) ∧
      (∀ l < pd, PathLevel rd σ (oqP base I blocks) pd (oqK1 base I + 3 * blocks) l) ∧ next := by
  rw [oqPathT, holdsList_append] at h
  generalize oqP base I blocks = P at h ⊢
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, word_iv0, word_iv1,
    word_md64, word_eOfNat, eOfNat_one] at h
  obtain ⟨⟨hp, hfr⟩, l81, h82, h83, h84, h85, h86, ln0, ln1, h87, h88, h89, hc0, h⟩ := h
  rw [holdsList_range_flatten _ _ (fun _ => rfl)] at h
  obtain ⟨hb, hn⟩ := h
  refine ⟨⟨hp, fun k hk w hw => ?_⟩, fun l hl => ?_, hn⟩
  · have := hfr k (by simp; omega) w hw
    rwa [getElem_frameRun hk] at this
  · rcases Nat.eq_zero_or_pos l with rfl | hpos
    · refine ⟨σ (.n (P + 81)), l81, ?_, ?_, ?_⟩
      · rw [h86, h85, h84, h83, h82] at ln0
        simpa [oqNode] using ln0
      · rw [h86, h85, h84, h83, h82] at ln1
        simpa [oqNode] using ln1
      · rw [h87, h88, h89] at hc0
        simpa [oqNode, show P + 77 + 13 = P + 90 by ring] using hc0
    · have := hb (l - 1) (by omega)
      rw [show l - 1 + 1 = l by omega] at this
      simp only [oqLevel, levelT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
        word_iv0, word_iv1, word_md64, word_eOfNat, eOfNat_one] at this
      obtain ⟨lL, h1, h2, h3, h4, h5, h6, h7, n0, n1, h8, h9, h10, hc⟩ := this
      have hg : kw (gpowK (4 * l)) = gen ^ (4 * l) := kw_gpowK (by
        have : 4 * l < 2 ^ 7 := by omega
        exact lt_trans this (by decide))
      refine ⟨_, lL, ?_, ?_, ?_⟩
      · rw [h7, h6, h5, h4, h3, h2, h1, hg] at n0
        simpa [oqNode, show l ≠ 0 by omega] using n0
      · rw [h7, h6, h5, h4, h3, h2, h1, hg] at n1
        simpa [oqNode, show l ≠ 0 by omega, show P + 78 + 13 * l = P + 77 + 13 * l + 1 by ring] using n1
      · rw [h8, h9, h10] at hc
        simpa [oqNode, show l ≠ 0 by omega, show P + 79 + 13 * l + 11 = P + 77 + 13 * (l + 1) by ring,
          show P + 79 + 13 * l + 12 = P + 77 + 13 * (l + 1) + 1 by ring] using hc

theorem eOfNat_two : eOfNat 2 = gen := rfl

/-- The cap leaf's parent index after `t` of its bits. -/
def capPar (rd : Reader) (dbp : E) (pd cd t : ℕ) : E :=
  gen ^ 2 ^ (cd - 1) * ∏ s ∈ Finset.range t, (1 + memAt rd dbp (pd + 1 + s) * (1 + gen ^ 2 ^ s))

/-- The cap leaf's index from its parent's and the level's own bit. -/
def capIdx (rd : Reader) (dbp : E) (pd cd : ℕ) : E :=
  capPar rd dbp pd cd (cd - 1) * capPar rd dbp pd cd (cd - 1) * (1 + memAt rd dbp pd * eOfNat 3)

theorem kw_one_add_gpowK {t : ℕ} (ht : 2 ^ t < 2 ^ 128) : kw (1 + gpowK (2 ^ t)) = 1 + gen ^ 2 ^ t := by
  rw [kw_eq, ofK_add, ofK_one, gpowK_eq ht, gen_pow_eq_ofK]

/-- What the cap leaf asks (G:1027-1043): its bits readable, the parent's flag `1`, the path's top
stored at the leaf. -/
def CapLeaf (rd : Reader) (flags cap dbp : E) (pd cd : ℕ) (top : E × E) : Prop :=
  (∀ t < cd, LoadHolds rd dbp (pd + t) (memAt rd dbp (pd + t))) ∧
    LoadHolds rd (flags * capPar rd dbp pd cd (cd - 1)) 0 1 ∧
    LoadHolds rd (cap * (capIdx rd dbp pd cd * capIdx rd dbp pd cd)) 0 top.1 ∧
    LoadHolds rd (cap * (gen * capIdx rd dbp pd cd * capIdx rd dbp pd cd)) 0 top.2

/-- The cap leaf and the loop's tail (`oqCapT`), from their relation. -/
theorem oqCap_sound {P pd cd : ℕ} (hcd : 1 ≤ cd) (hcd8 : cd ≤ 8) {loop : String} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (oqCapT P pd cd loop) False kret) :
    CapLeaf rd (σ (.n 6)) (σ (.n 7)) (σ (.n (P - 1))) pd cd
        (σ (.n (P + 77 + 13 * pd)), σ (.n (P + 77 + 13 * pd + 1))) ∧
      IsInK (σ (.n 0) * gen + σ (.n 1)) ∧
      (σ (.n 0) * gen + σ (.n 1) ≠ 0 →
        C loop [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)] []) ∧
      kret [] := by
  set K6 := P + 79 + 13 * pd
  rw [oqCapT, holdsList_append, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨h0, h⟩ := h
  rw [holdsList_range_flatten _ _ (fun _ => rfl)] at h
  obtain ⟨hb, h⟩ := h
  simp only [List.map_cons, List.map_nil, word_eOfNat, eOfNat_one, eOfNat_two] at h
  obtain ⟨g0, g1, lf, g2, g3, lb, g5, g6, g7, g8, g9, g10, lc0, g11, g12, g13, g14, lc1, t0, t1, t2,
    t3, t4, hK, hcall, hret⟩ := h
  -- the parent's index, bit by bit
  have hpar : ∀ t ≤ cd - 1, σ (.n (K6 + 6 * t)) = capPar rd (σ (.n (P - 1))) pd cd t ∧
      ∀ s < t, LoadHolds rd (σ (.n (P - 1))) (pd + 1 + s) (memAt rd (σ (.n (P - 1))) (pd + 1 + s)) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨?_, fun s hs => absurd hs (Nat.not_lt_zero s)⟩
      rw [Nat.mul_zero, Nat.add_zero, h0, kw_gpowK (Nat.pow_lt_pow_right (by decide)
        (show cd - 1 < 128 by omega)), capPar]
      simp
    | succ t ih =>
      intro ht
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have := hb t (by omega)
      simp only [oqCapBit, capBitT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at this
      obtain ⟨u0, lu, u2, u3, u4, u5⟩ := this
      have hc : kw (1 + gpowK (2 ^ t)) = 1 + gen ^ 2 ^ t :=
        kw_one_add_gpowK (Nat.pow_lt_pow_right (by decide) (show t < 128 by omega))
      refine ⟨?_, fun s hs => ?_⟩
      · rw [show K6 + 6 * (t + 1) = P + 80 + 13 * pd + 6 * t + 5 by ring, u5, u4, u3, u2, u0, hc,
          show P + 79 + 13 * pd + 6 * t = K6 + 6 * t by ring, ih1, ← memAt_of_load lu, capPar, capPar,
          Finset.prod_range_succ, mul_assoc]
      · rcases Nat.lt_or_ge s t with hst | hst
        · exact ih2 s hst
        · rw [show s = t by omega]; exact loadHolds_memAt lu
  obtain ⟨hp1, hp2⟩ := hpar (cd - 1) le_rfl
  have hK7 : K6 + 6 * cd - 5 - 1 = K6 + 6 * (cd - 1) := by omega
  rw [hK7, hp1] at g1
  rw [g1] at lf
  rw [g0] at lf
  rw [hK7, hp1] at g2
  refine ⟨⟨fun t ht => ?_, lf, ?_, ?_⟩, ?_, ?_, hret⟩
  · rcases Nat.eq_zero_or_pos t with rfl | hpos
    · simpa using loadHolds_memAt lb
    · have := hp2 (t - 1) (by omega)
      rwa [show pd + 1 + (t - 1) = pd + t by omega] at this
  · rw [g10, g9, g8, g7, g6, g5, g3, g2, ← memAt_of_load lb] at lc0
    simpa [capIdx, K6] using lc0
  · rw [g14, g13, g12, g11, g8, g7, g6, g5, g3, g2, ← memAt_of_load lb] at lc1
    simpa [capIdx, K6, mul_assoc] using lc1
  · rwa [t2, t1, t0] at hK
  · intro hne
    have := hcall (by rwa [t2, t1, t0])
    rwa [t4, t3] at this

/-! ## One query -/

theorem noRetList_append (xs ys : List Stmt) :
    Stmt.noRetList (xs ++ ys) = (Stmt.noRetList xs && Stmt.noRetList ys) := by
  induction xs with
  | nil => simp [Stmt.noRetList]
  | cons x xs ih => simp [Stmt.noRetList, ih, Bool.and_assoc]

theorem noRetList_flatten_range (n : ℕ) (blk : ℕ → List Stmt) (h : ∀ i, Stmt.noRetList (blk i) = true) :
    Stmt.noRetList ((List.range n).map blk).flatten = true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.flatten_append, noRetList_append, ih]; simp [h]

theorem oqRows_noRet (base I : ℕ) : Stmt.noRetList (oqRows base I) = true := by
  unfold oqRows
  split
  · rw [oqRows1, noRetList_append, noRetList_append,
      noRetList_flatten_range _ (fun j => oq1Blk I (j + 1)) (fun _ => rfl)]
    rfl
  · rw [oqRows0, noRetList_append, noRetList_append, noRetList_append, noRetList_append,
      noRetList_flatten_range _ (oq0Pack (3 * I)) (fun _ => rfl),
      noRetList_flatten_range _ (fun j => oq0Blk I (j + 1)) (fun _ => oq0Blk_noRet _ _)]
    unfold oq0WordT
    split <;> rfl

theorem oqLeafT_noRet (base I blocks : ℕ) : Stmt.noRetList (oqLeafT base I blocks) = true := by
  rw [oqLeafT, noRetList_append,
    noRetList_flatten_range _ (fun j => oqLeafBlk base I blocks (j + 1)) (fun _ => rfl)]
  rfl

theorem oqPathT_noRet (base I blocks pd : ℕ) : Stmt.noRetList (oqPathT base I blocks pd) = true := by
  simp only [oqPathT]
  rw [noRetList_append, noRetList_flatten_range _ (fun j => oqLevel (oqP base I blocks) pd (j + 1))
    (fun _ => rfl)]
  rfl

/-- **One query**, as the loop's body asks it at `x` (G:991-1043): the row in `K`, its weights
readable, the query sum, the bit run `dbp`, the path's frame run and levels, every running node
`nd l`, from the leaf digest `nd 0` to the top `nd pd`, and the cap leaf. -/
def OqSem (base I pd cd : ℕ) (rd : Reader) (rew qsc qw qbp flags cap x : E) : Prop :=
  ∃ r : ℕ → E, (∀ j < oqR base I, IsInK (r j)) ∧ (∀ jw < I, LoadHolds rd rew jw (memAt rd rew jw)) ∧
    (∃ s w, LoadHolds rd (qsc * x) 0 s ∧ LoadHolds rd (qw * x) 0 w ∧
      LoadHolds rd (qsc * x) 1 (s + w * ∑ jw ∈ Finset.range I, oqRowWord base r jw * memAt rd rew jw)) ∧
    ∃ dbp, LoadHolds rd (qbp * x) 0 dbp ∧
    ∃ (ptr : E) (cs : ℕ → E) (nd : ℕ → E × E), nd 0 = digestScalars (hashWords (leafWords base I r)) ∧
      IsInK ptr ∧ (∀ k < 4 * pd, ∀ w, rd (ptr.limb 0 * Parameters.gpow k) = some w → w = cs k) ∧
      (∀ l < pd, ∃ d, LoadHolds rd dbp l d ∧
        LoadHolds rd (ptr * gen ^ (4 * l) * (1 + d * eOfNat 5)) 0 (nd l).1 ∧
        LoadHolds rd (ptr * gen ^ (4 * l) * (1 + d * eOfNat 5)) 1 (nd l).2 ∧
        CompressCells ![cs (4 * l), cs (4 * l + 1), cs (4 * l + 2), cs (4 * l + 3)] Value.ivCells.1
          Value.ivCells.2 (nd (l + 1)).1 (nd (l + 1)).2 (metadataCell 64 true)) ∧
      CapLeaf rd flags cap dbp pd cd (nd pd)

/-- The shapes the template is proved at: a level kind, `I` a multiple of four filling `blocks`
whole blocks, a path of at most 20 levels below a cap of depth at most 8. -/
structure OqShape (base I blocks pd cd : ℕ) : Prop where
  hbase : base = 0 ∨ base = 1
  i4 : 4 ≤ I
  imod : I % 4 = 0
  hblocks : 1 ≤ blocks
  fill : oqR base I = 8 * blocks
  pd1 : 1 ≤ pd
  pd20 : pd ≤ 20
  cd1 : 1 ≤ cd
  cd8 : cd ≤ 8

/-- The loop helper's step, from its relation: one query, then the call at `x·g`. -/
theorem oqLoop_sound {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd) {loop : String}
    {fn : Fn} (hfind : coreProgram.find? loop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hb : fn.body = oqLoopBody base I blocks pd cd loop) {rd : Reader} {N rew qsc qw qbp flags cap : E}
    {d : ℕ} {x : E}
    (h : coreProgram.relN rd (d + 1) loop (x :: [N, rew, qsc, qw, qbp, flags, cap]) []) :
    OqSem base I pd cd rd rew qsc qw qbp flags cap x ∧ IsInK (x * gen + N) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d loop (x * gen :: [N, rew, qsc, qw, qbp, flags, cap]) []) := by
  rw [relN_succ_iff hfind, hp, hb, oqLoopBody] at h
  obtain ⟨σ, hpar, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hpar
  simp only [holdsList_append] at h
  obtain ⟨hrows, h⟩ := holdsList_true_of (oqRows_noRet _ _) h
  have hrf := oqRows_sound hs.hbase hs.i4 hs.imod hrows
  obtain ⟨hleaf, h⟩ := holdsList_true_of (oqLeafT_noRet _ _ _) h
  have hl := (oqLeaf_sound hs.hblocks hs.fill hrf hleaf).1
  obtain ⟨hsum, h⟩ := holdsList_true_of rfl h
  obtain ⟨s1, s3, s7, s9, -⟩ := oqSum_sound hsum
  obtain ⟨hpath, h⟩ := holdsList_true_of (oqPathT_noRet _ _ _ _) h
  obtain ⟨⟨hptr, hfr⟩, hlev, -⟩ := oqPath_sound hs.pd1 hs.pd20 hpath
  obtain ⟨hcap, hK, hcall, -⟩ := oqCap_sound hs.cd1 hs.cd8 h
  refine ⟨⟨rowv σ, hrf.1, hrf.2.2.1, ⟨_, _, s1, s3, by rw [← hrf.2.2.2]; exact s7⟩, _, s9, _,
    fun k => σ (.n (oqP base I blocks + k)),
    fun l => (σ (.n (oqNode (oqP base I blocks) (oqK1 base I + 3 * blocks) l)),
      σ (.n (oqNode (oqP base I blocks) (oqK1 base I + 3 * blocks) l + 1))),
    by simpa [oqNode] using hl, hptr, hfr, fun l hl => ?_, ?_⟩, hK, hcall⟩
  · obtain ⟨dv, ld, n0, n1, hc⟩ := hlev l hl
    exact ⟨dv, by simpa [oqP] using ld, n0, n1, by simpa [add_assoc] using hc⟩
  · simpa [oqNode, show pd ≠ 0 by have := hs.pd1; omega, oqP] using hcap

/-! ## A query in the specification's terms -/

/-- The digest of two canonical cells. -/
def pairDigest (a b : E) : Digest := cellWords a ++ cellWords b

theorem pairDigest_eq {a b : E} (ha : IsCanonical128 a) (hb : IsCanonical128 b) :
    (a, b) = digestScalars (pairDigest a b) := pair_eq_digestScalars_iff.mpr ⟨ha, hb, rfl⟩

theorem pairDigest_digestScalars (d : Digest) :
    pairDigest (digestScalars d).1 (digestScalars d).2 = d := cellWords_digestScalars d

/-- The running node after `l` levels of `climb` (V:526). -/
def climbAt (D : Digest) (q : ℕ) (sibs : List Digest) (l : ℕ) : Digest :=
  climb (m := Id) blake2sBytes D q (sibs.take l)

theorem climb_append (D : Digest) (q : ℕ) (ss : List Digest) (s : Digest) :
    climb (m := Id) blake2sBytes D q (ss ++ [s]) =
      if q / 2 ^ ss.length % 2 = 0 then hashPair (climb (m := Id) blake2sBytes D q ss) s
      else hashPair s (climb (m := Id) blake2sBytes D q ss) := by
  induction ss generalizing D q with
  | nil => simp only [List.nil_append, climb_cons, List.length_nil, pow_zero, Nat.div_one]; rfl
  | cons x ss ih =>
    rw [List.cons_append, climb_cons, ih, climb_cons, List.length_cons, Nat.div_div_eq_div_mul,
      pow_succ']

theorem climbAt_zero (D : Digest) (q : ℕ) (sibs : List Digest) : climbAt D q sibs 0 = D := rfl

theorem climbAt_succ (D : Digest) (q : ℕ) (sibs : List Digest) {l : ℕ} (hl : l < sibs.length) :
    climbAt D q sibs (l + 1) =
      if q.testBit l then hashPair (sibs.getD l default) (climbAt D q sibs l)
      else hashPair (climbAt D q sibs l) (sibs.getD l default) := by
  rw [climbAt, List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some, climb_append,
    List.length_take, Nat.min_eq_left hl.le, ← Nat.toNat_testBit, climbAt,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  cases q.testBit l <;> rfl

theorem climbAt_length (D : Digest) (q : ℕ) (sibs : List Digest) :
    climbAt D q sibs sibs.length = climb (m := Id) blake2sBytes D q sibs := by
  rw [climbAt, List.take_length]

/-- The four cells of a path level: the running node and its sibling, in order. -/
def lvlCells (node sib : Digest) (b : Bool) : List E :=
  if b then [(digestScalars sib).1, (digestScalars sib).2, (digestScalars node).1, (digestScalars node).2]
  else [(digestScalars node).1, (digestScalars node).2, (digestScalars sib).1, (digestScalars sib).2]

theorem length_lvlCells (node sib : Digest) (b : Bool) : (lvlCells node sib b).length = 4 := by
  cases b <;> rfl

/-- The cells `verify_merkle_path` hints for the climb from `D` at `q` over `sibs`. -/
def climbCells (D : Digest) (q : ℕ) (sibs : List Digest) : List E :=
  (List.range sibs.length).flatMap fun l => lvlCells (climbAt D q sibs l) (sibs.getD l default) (q.testBit l)

/-- A path's frame run at `ptr` (G:902-904): every readable word below `4·|sibs|` is its hinted
cell, and the running node is readable at the child each level selects. -/
def PathFrame (rd : Reader) (ptr : E) (D : Digest) (q : ℕ) (sibs : List Digest) : Prop :=
  IsInK ptr ∧
    (∀ k < 4 * sibs.length, ∀ w, rd (ptr.limb 0 * Parameters.gpow k) = some w →
      w = (climbCells D q sibs).getD k 0) ∧
    ∀ l < sibs.length,
      LoadHolds rd ptr (4 * l + 2 * (q.testBit l).toNat) (digestScalars (climbAt D q sibs l)).1 ∧
      LoadHolds rd ptr (4 * l + 2 * (q.testBit l).toNat + 1) (digestScalars (climbAt D q sibs l)).2

/-- Row word `jw` of a leaf's words. -/
def leafRowWord (base : ℕ) (leaf : List K) (jw : ℕ) : E :=
  oqRowWord base (fun j => ofK (leaf.getD j 0)) jw

/-- The bit run at `p` of a position `q`: every readable word below `depth` is bit `l` of `q`
(what `decode_query_bits` leaves at `qbp[i]`). -/
def BitsAt (rd : Reader) (p : E) (q depth : ℕ) : Prop :=
  IsInK p ∧ ∀ l < depth, ∀ w, rd (p.limb 0 * Parameters.gpow l) = some w → w = bitE (q.testBit l)

/-- **Query `i` at the position `q`**: its bits readable at `qbp[i]`, its leaf of `oqR base I`
words with the query sum `qsc[i + 1] = qsc[i] + qw[i]·⟨row, weights⟩`, the path's siblings in the
frame run, the climb (V:526) from the leaf's `hashWords` (`Spec/Blake2s.lean:201`) stored at the
cap leaf `2^cd + q / 2^pd`, and its parent's flag `1`. -/
def QueryOk (base I depth cd : ℕ) (rd : Reader) (rew qsc qw qbp flags cap : E) (i q : ℕ) : Prop :=
  ∃ dbp, LoadHolds rd qbp i dbp ∧ (∀ l < depth, LoadHolds rd dbp l (bitE (q.testBit l))) ∧
    ∃ leaf : List K, leaf.length = oqR base I ∧ (∀ jw < I, LoadHolds rd rew jw (memAt rd rew jw)) ∧
    (∃ s w, LoadHolds rd qsc i s ∧ LoadHolds rd qw i w ∧ LoadHolds rd qsc (i + 1)
      (s + w * ∑ jw ∈ Finset.range I, leafRowWord base leaf jw * memAt rd rew jw)) ∧
    ∃ sibs : List Digest, sibs.length = depth - cd ∧ ∃ ptr, PathFrame rd ptr (hashWords leaf) q sibs ∧
      CapCell rd cap (2 ^ cd + q / 2 ^ (depth - cd)) (climb (m := Id) blake2sBytes (hashWords leaf) q sibs) ∧
      LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (depth - cd + 1)) 1

theorem one_add_bitE_five (b : Bool) : 1 + bitE b * eOfNat 5 = gen ^ (2 * b.toNat) := by
  cases b
  · simp [bitE]
  · simp only [bitE, ↓reduceIte, one_mul, Bool.toNat_true, Nat.mul_one]
    rw [← eOfNat_one, ← eOfNat_xor, gen_pow_eq_eOfNat (by decide)]
    rfl

theorem one_add_bitE_three (b : Bool) : 1 + bitE b * eOfNat 3 = gen ^ b.toNat := by
  cases b
  · simp [bitE]
  · simp only [bitE, ↓reduceIte, one_mul, Bool.toNat_true, pow_one]
    rw [← eOfNat_one, ← eOfNat_xor]
    rfl

theorem bitsVal_shift (q s n : ℕ) : bitsVal (fun t => q.testBit (s + t)) n = q / 2 ^ s % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitsVal, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i s]

theorem prod_bitE_gen_pow' (f : ℕ → Bool) (n : ℕ) :
    ∏ j ∈ Finset.range n, (1 + bitE (f j) * (1 + gen ^ 2 ^ j)) = gen ^ bitsVal f n := by
  rw [← prod_bitE_gen_pow]
  exact Finset.prod_congr rfl fun j _ => by rw [add_comm (1 : E) (gen ^ 2 ^ j)]

/-- The cap leaf of a query at the position `q < 2^(pd + cd)`. -/
theorem capLeaf_index {pd cd q : ℕ} (hcd : 1 ≤ cd) (hq : q < 2 ^ (pd + cd)) :
    q / 2 ^ (pd + 1) % 2 ^ (cd - 1) = q / 2 ^ (pd + 1) ∧
      2 * (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) + (q.testBit pd).toNat = 2 ^ cd + q / 2 ^ pd := by
  have h2 : 2 ^ (pd + cd) = 2 ^ (pd + 1) * 2 ^ (cd - 1) := by rw [← pow_add]; congr 1; omega
  have hlt : q / 2 ^ (pd + 1) < 2 ^ (cd - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [h2] at hq; linarith
  refine ⟨Nat.mod_eq_of_lt hlt, ?_⟩
  rw [Nat.toNat_testBit, pow_succ, ← Nat.div_div_eq_div_mul]
  have hc : 2 ^ cd = 2 * 2 ^ (cd - 1) := by rw [← pow_succ']; congr 1; omega
  have := Nat.div_add_mod (q / 2 ^ pd) 2
  omega

theorem leafWords_getD {base I : ℕ} {r : ℕ → E} {j : ℕ} (hj : j < oqR base I) :
    (leafWords base I r).getD j 0 = (r j).limb 0 := by
  simp [leafWords, List.getD_eq_getElem?_getD, hj]

theorem length_leafWords (base I : ℕ) (r : ℕ → E) : (leafWords base I r).length = oqR base I := by
  simp [leafWords]

theorem oqRowWord_leaf {base I : ℕ} {r : ℕ → E} (hK : ∀ j < oqR base I, IsInK (r j)) {jw : ℕ}
    (hjw : jw < I) : oqRowWord base r jw = leafRowWord base (leafWords base I r) jw := by
  have hr : ∀ j < oqR base I, r j = ofK ((leafWords base I r).getD j 0) := fun j hj => by
    rw [leafWords_getD hj]; exact eq_ofK_limb (hK j hj)
  simp only [leafRowWord, oqRowWord]
  split
  · rename_i hb
    exact hr jw (by simp [oqR, hb]; omega)
  · rename_i hb
    have h3 : oqR base I = 3 * I := by simp [oqR, hb]
    rw [hr (3 * jw) (by omega), hr (3 * jw + 1) (by omega), hr (3 * jw + 2) (by omega)]

/-- One level of the path at the position's bit: with the running node the cells of
`climbAt l`, the frame's cells are the level's `lvlCells`, the selected child is readable, and
the next node is `climbAt (l + 1)`. -/
theorem path_level {ptr : E} {cs : ℕ → E} {nd : ℕ → E × E} {D : Digest} {q pd l : ℕ}
    (sibs : List Digest) (hsl : sibs.length = pd)
    (hsib : sibs.getD l default = if q.testBit l then pairDigest (cs (4 * l)) (cs (4 * l + 1))
      else pairDigest (cs (4 * l + 2)) (cs (4 * l + 3)))
    (hl : l < pd)
    (hfr : ∀ k < 4 * pd, ∀ w, rd (ptr.limb 0 * Parameters.gpow k) = some w → w = cs k)
    (hd : ∃ d, LoadHolds rd (ptr * gen ^ (4 * l) * (1 + d * eOfNat 5)) 0 (nd l).1 ∧
      LoadHolds rd (ptr * gen ^ (4 * l) * (1 + d * eOfNat 5)) 1 (nd l).2 ∧ d = bitE (q.testBit l))
    (hc : CompressCells ![cs (4 * l), cs (4 * l + 1), cs (4 * l + 2), cs (4 * l + 3)] Value.ivCells.1
      Value.ivCells.2 (nd (l + 1)).1 (nd (l + 1)).2 (metadataCell 64 true))
    (hnd : nd l = digestScalars (climbAt D q sibs l)) :
    lvlCells (climbAt D q sibs l) (sibs.getD l default) (q.testBit l) =
        [cs (4 * l), cs (4 * l + 1), cs (4 * l + 2), cs (4 * l + 3)] ∧
      LoadHolds rd ptr (4 * l + 2 * (q.testBit l).toNat) (digestScalars (climbAt D q sibs l)).1 ∧
      LoadHolds rd ptr (4 * l + 2 * (q.testBit l).toNat + 1) (digestScalars (climbAt D q sibs l)).2 ∧
      nd (l + 1) = digestScalars (climbAt D q sibs (l + 1)) := by
  obtain ⟨d, n0, n1, rfl⟩ := hd
  rw [one_add_bitE_five, mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero] at n0
  rw [one_add_bitE_five, mul_assoc, ← pow_add, loadHolds_mul_gen_pow] at n1
  rw [hnd] at n0 n1
  obtain ⟨L, R, hL, hR, ho⟩ := compress_hashPair hc
  change (cs (4 * l), cs (4 * l + 1)) = _ at hL
  change (cs (4 * l + 2), cs (4 * l + 3)) = _ at hR
  have e0 := hfr _ (by cases q.testBit l <;> simp <;> omega) _ n0.2
  have e1 := hfr _ (by cases q.testBit l <;> simp <;> omega) _ n1.2
  have c0 : IsCanonical128 (cs (4 * l)) := hc.1 0
  have c1 : IsCanonical128 (cs (4 * l + 1)) := hc.1 1
  have c2 : IsCanonical128 (cs (4 * l + 2)) := hc.1 2
  have c3 : IsCanonical128 (cs (4 * l + 3)) := hc.1 3
  have ho' : nd (l + 1) = digestScalars (hashPair L R) := Prod.mk.eta.symm.trans ho
  refine ⟨?_, n0, n1, ?_⟩
  · cases hb : q.testBit l
    · simp only [hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e0 e1
      rw [hsib, hb]
      simp only [lvlCells, Bool.false_eq_true, ↓reduceIte, e0, e1]
      rw [← pairDigest_eq c2 c3]
    · simp only [hb, Bool.toNat_true, Nat.mul_one] at e0 e1
      rw [hsib, hb]
      simp only [lvlCells, ↓reduceIte, e0, e1, show 4 * l + 2 + 1 = 4 * l + 3 by ring]
      rw [← pairDigest_eq c0 c1]
  · rw [climbAt_succ D q sibs (by omega), ho']
    cases hb : q.testBit l
    · simp only [hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e0 e1
      have hn : climbAt D q sibs l = L :=
        digestScalars_injective (by rw [← hL, ← e0, ← e1])
      rw [hsib, hb]
      simp only [Bool.false_eq_true, ↓reduceIte, hn]
      rw [show pairDigest (cs (4 * l + 2)) (cs (4 * l + 3)) = R by
        rw [show cs (4 * l + 2) = (digestScalars R).1 from congrArg Prod.fst hR,
          show cs (4 * l + 3) = (digestScalars R).2 from congrArg Prod.snd hR, pairDigest_digestScalars]]
    · simp only [hb, Bool.toNat_true, Nat.mul_one, show 4 * l + 2 + 1 = 4 * l + 3 by ring] at e0 e1
      have hn : climbAt D q sibs l = R :=
        digestScalars_injective (by rw [← hR, ← e0, ← e1])
      rw [hsib, hb]
      simp only [↓reduceIte, hn]
      rw [show pairDigest (cs (4 * l)) (cs (4 * l + 1)) = L by
        rw [show cs (4 * l) = (digestScalars L).1 from congrArg Prod.fst hL,
          show cs (4 * l + 1) = (digestScalars L).2 from congrArg Prod.snd hL, pairDigest_digestScalars]]

/-- **A query, in the specification's terms**: the loop body at `g^i`, with the position's
bits at `qbp[i]`, is `QueryOk`. -/
theorem oqSem_query {base I blocks pd cd i q : ℕ} (hs : OqShape base I blocks pd cd) (hq : q < 2 ^ (pd + cd))
    {rew qsc qw qbp flags cap : E}
    (hbits : ∀ dbp, LoadHolds rd qbp i dbp → BitsAt rd dbp q (pd + cd))
    (h : OqSem base I pd cd rd rew qsc qw qbp flags cap (gen ^ i)) :
    QueryOk base I (pd + cd) cd rd rew qsc qw qbp flags cap i q := by
  obtain ⟨r, hrK, hw, ⟨s, w, ls, lw, ls1⟩, dbp, ldbp, ptr, cs, nd, hnd0, hptr, hfr, hlev, hcap⟩ := h
  rw [loadHolds_gen_pow] at ls lw ldbp
  rw [loadHolds_mul_gen_pow] at ls1
  have hB := hbits dbp ldbp
  have bit : ∀ l < pd + cd, ∀ d, LoadHolds rd dbp l d → d = bitE (q.testBit l) :=
    fun l hl d hd => hB.2 l hl d hd.2
  set leaf := leafWords base I r
  set D := hashWords leaf
  set sibs : List Digest := (List.range pd).map fun l =>
    if q.testBit l then pairDigest (cs (4 * l)) (cs (4 * l + 1)) else pairDigest (cs (4 * l + 2)) (cs (4 * l + 3))
  have hsl : sibs.length = pd := by simp [sibs]
  have hsib : ∀ l < pd, sibs.getD l default = if q.testBit l then pairDigest (cs (4 * l)) (cs (4 * l + 1))
      else pairDigest (cs (4 * l + 2)) (cs (4 * l + 3)) := fun l hl => by
    simp [sibs, List.getD_eq_getElem?_getD, hl]
  have hlvl : ∀ l < pd, nd l = digestScalars (climbAt D q sibs l) →
      lvlCells (climbAt D q sibs l) (sibs.getD l default) (q.testBit l) =
        [cs (4 * l), cs (4 * l + 1), cs (4 * l + 2), cs (4 * l + 3)] ∧
      LoadHolds rd ptr (4 * l + 2 * (q.testBit l).toNat) (digestScalars (climbAt D q sibs l)).1 ∧
      LoadHolds rd ptr (4 * l + 2 * (q.testBit l).toNat + 1) (digestScalars (climbAt D q sibs l)).2 ∧
      nd (l + 1) = digestScalars (climbAt D q sibs (l + 1)) := fun l hl hn => by
    obtain ⟨dv, ld, n0, n1, hc⟩ := hlev l hl
    exact path_level sibs hsl (hsib l hl) hl hfr ⟨dv, n0, n1, bit l (by omega) dv ld⟩ hc hn
  have hnd : ∀ l ≤ pd, nd l = digestScalars (climbAt D q sibs l) := by
    intro l hl
    induction l with
    | zero => rw [climbAt_zero]; exact hnd0
    | succ l ih => exact (hlvl l (by omega) (ih (by omega))).2.2.2
  obtain ⟨hcl, hcf, hci0, hci1⟩ := hcap
  have hcb : ∀ t < cd, memAt rd dbp (pd + t) = bitE (q.testBit (pd + t)) := fun t ht =>
    bit (pd + t) (by omega) _ (hcl t ht)
  have hpar : capPar rd dbp pd cd (cd - 1) = gen ^ (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) := by
    rw [capPar]
    rw [Finset.prod_congr rfl fun t ht => by
      rw [show pd + 1 + t = pd + (t + 1) by ring, hcb (t + 1) (by simp at ht; have := hs.cd1; omega)]]
    rw [prod_bitE_gen_pow' (fun t => q.testBit (pd + (t + 1))) (cd - 1), ← pow_add]
    congr 2
    rw [show (fun t => q.testBit (pd + (t + 1))) = (fun t => q.testBit ((pd + 1) + t)) from
      funext fun t => by rw [show pd + (t + 1) = pd + 1 + t by ring], bitsVal_shift,
      (capLeaf_index hs.cd1 hq).1]
  have hidx : capIdx rd dbp pd cd = gen ^ (2 ^ cd + q / 2 ^ pd) := by
    rw [capIdx, hpar, show memAt rd dbp pd = bitE (q.testBit pd) by simpa using hcb 0 hs.cd1,
      one_add_bitE_three, ← pow_add, ← pow_add, ← (capLeaf_index hs.cd1 hq).2]
    congr 1; ring
  rw [hpar, loadHolds_gen_pow] at hcf
  rw [hidx, ← pow_add, loadHolds_gen_pow] at hci0
  rw [hidx, mul_assoc, ← pow_add, ← pow_succ', loadHolds_gen_pow] at hci1
  have htop : nd pd = digestScalars (climb (m := Id) blake2sBytes D q sibs) := by
    rw [hnd pd le_rfl, ← climbAt_length, hsl]
  refine ⟨dbp, ldbp, fun l hl => ?_, leaf, length_leafWords _ _ _, hw,
    ⟨s, w, ls, lw, ?_⟩, sibs, by rw [hsl]; omega, ptr, ⟨hptr, fun k hk w hw => ?_, fun l hl => ?_⟩,
    ⟨?_, ?_⟩, ?_⟩
  · -- the bits: the path's levels and the cap's
    rcases Nat.lt_or_ge l pd with hlp | hlp
    · obtain ⟨dv, ld, -⟩ := hlev l hlp
      rw [← bit l hl dv ld]; exact ld
    · have := hcl (l - pd) (by omega)
      rw [show pd + (l - pd) = l by omega] at this
      rw [← bit l hl _ this]; exact this
  · rw [Finset.sum_congr rfl fun jw hjw => by rw [oqRowWord_leaf hrK (Finset.mem_range.mp hjw)]] at ls1
    exact ls1
  · rw [hsl] at hk
    obtain ⟨l, j, hj, rfl⟩ : ∃ l j, j < 4 ∧ k = 4 * l + j := ⟨k / 4, k % 4, by omega, by omega⟩
    rw [hfr _ (by omega) w hw, climbCells, getD_flatMap_four _ (fun _ => length_lvlCells _ _ _) 0
      _ l j (by simp; omega) hj]
    simp only [List.getElem_range]
    rw [(hlvl l (by omega) (hnd l (by omega))).1]
    interval_cases j <;> rfl
  · rw [hsl] at hl
    exact ⟨(hlvl l hl (hnd l hl.le)).2.1, (hlvl l hl (hnd l hl.le)).2.2.1⟩
  · rw [htop] at hci0
    rw [show pd + cd - cd = pd by omega, two_mul]; exact hci0
  · rw [htop] at hci1
    rw [show pd + cd - cd = pd by omega, two_mul]; exact hci1
  · rwa [show pd + cd - cd + 1 = pd + 1 by omega]

/-! ## `opening_queries` -/

/-- A `mul_range` loop from `g^k`, soundness only: the step's relation gives its body. -/
theorem loop_sound {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {N : E} {B : E → Prop}
    (hstep : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] →
      B x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) [])) (k : ℕ)
    (h : P.Rel rd f (gen ^ k :: ps) []) :
    ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧ ∀ j, k ≤ j → j < m → B (gen ^ j) := by
  obtain ⟨d, hd⟩ := h
  induction d generalizing k with
  | zero => exact hd.elim
  | succ d ih =>
    obtain ⟨hB, -, hnext⟩ := hstep d _ hd
    by_cases h0 : gen ^ k * gen + N = 0
    · refine ⟨k + 1, by omega, (gen_pow_add_eq_zero_iff k).mp h0, fun j h1 h2 => by omega,
        fun j h1 h2 => ?_⟩
      rwa [show j = k by omega]
    · have := hnext h0
      rw [gen_pow_mul_gen] at this
      obtain ⟨m, hm, hN, hfirst, hall⟩ := ih (k + 1) this
      refine ⟨m, by omega, hN, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
      · rcases Nat.lt_or_ge (k + 1) j with h | h
        · exact hfirst j h h2
        · rw [show j = k + 1 by omega]
          intro he
          exact h0 ((gen_pow_add_eq_zero_iff k).mpr he.symm)
      · rcases Nat.lt_or_ge k j with h | h
        · exact hall j (by omega) h2
        · rwa [show j = k by omega]

/-- A loop behind its guard, soundness only: `N = g^m` below the order of `g`, the body at every
`g^j`, `j < m`. -/
theorem guarded_loop_sound {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hstep : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] →
      B x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) []))
    (hrun : 1 + N ≠ 0 → P.Rel rd f (1 :: ps) []) :
    ∃ m < ordG, N = gen ^ m ∧ ∀ j < m, B (gen ^ j) := by
  by_cases h1 : 1 + N = 0
  · exact ⟨0, by decide, by rw [pow_zero]; exact (e_add_eq_zero_iff.mp h1).symm,
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  · have hr := hrun h1
    rw [← pow_zero gen] at hr
    obtain ⟨m, hm, hN, hfirst, hall⟩ := loop_sound hstep 0 hr
    refine ⟨m, ?_, hN, fun j hj => hall j (Nat.zero_le j) hj⟩
    by_contra hge
    rcases Nat.lt_or_ge ordG m with hgt | hle
    · have : gen ^ (m - ordG) = N := by
        obtain ⟨t, rfl⟩ : ∃ t, m = ordG + t := ⟨m - ordG, by omega⟩
        rw [hN, pow_add, gen_pow_ordG, one_mul, Nat.add_sub_cancel_left]
      exact hfirst (m - ordG) (Nat.sub_pos_of_lt hgt) (Nat.sub_lt (by omega) ordG_pos) this
    · have hm' : m = ordG := by omega
      rw [hm', gen_pow_ordG] at hN
      exact h1 (by rw [hN]; exact e_add_self 1)

/-- The positions' bit runs: `qbp[i]` points at the bits of `pos i < 2^depth` (what
`decode_query_bits`, TRIAGE #17, writes). -/
def QueryBits (rd : Reader) (qbp : E) (n depth : ℕ) (pos : ℕ → ℕ) : Prop :=
  ∀ i < n, pos i < 2 ^ depth ∧ ∀ dbp, LoadHolds rd qbp i dbp → BitsAt rd dbp (pos i) depth

/-- **`opening_queries(cap, flags, qw, qbp, rew, g^n)`** (G:987-1044; TRIAGE #28, #35), with
the query sum chain at `qsc`: `qsc[0] = 0`, every query `i < n` is `QueryOk` at its position,
and the function returns `qsc[n]`. -/
def MeaningOpeningQueries (base I depth cd n : ℕ) (pos : ℕ → ℕ) (rd : Reader) (qsc : E) :
    List E → List E → Prop
  | [cap, flags, qw, qbp, rew, nq], rets =>
      nq = gen ^ n ∧ LoadHolds rd qsc 0 0 ∧
        (∀ i < n, QueryOk base I depth cd rd rew qsc qw qbp flags cap i (pos i)) ∧
        ∃ s, LoadHolds rd qsc n s ∧ rets = [s]
  | _, _ => False

/-- **`opening_queries`, soundness**: at a shape `OqShape` and `n` queries below the order of
`g` whose positions' bits are at `qbp`, the relation gives the meaning at some chain `qsc`. -/
theorem opening_queries_sound {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd)
    {name loop : String} {f lf : Fn} (hfind : coreProgram.find? name = some f)
    (hp : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]) (hb : f.body = oqBody loop)
    (hlf : coreProgram.find? loop = some lf)
    (hlp : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hlb : lf.body = oqLoopBody base I blocks pd cd loop) {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n (pd + cd) pos) {rets : List E}
    (h : coreProgram.Rel rd name [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries base I (pd + cd) cd n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n]
      rets := by
  rw [rel_iff_sem hfind, hb, hp, oqBody] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen,
    word_zero, word_one, List.cons.injEq] at h
  obtain ⟨σ, ⟨rfl, rfl, rfl, rfl, rfl, h5, -⟩, h6, h7, -, h9, l9, h10, h11, h12, hK, hrun, h13, l14, hret⟩ := h
  have hloop := guarded_loop_sound (B := fun x => OqSem base I pd cd rd (σ (.n 4)) (σ (.n 8))
      (σ (.n 2)) (σ (.n 3)) (σ (.n 1)) (σ (.n 0)) x)
    (fun d x hx => oqLoop_sound hs hlf hlp hlb hx) (fun hne => by
      have := hrun (by rw [h11, h10]; exact hne)
      rwa [h12] at this)
  obtain ⟨m, hm, hN, hB⟩ := hloop
  have hmn : m = n := gen_pow_inj (by simp only [ordG] at hm; omega) (by simp only [ordG] at hn; omega)
    (hN.symm.trans h5)
  subst hmn
  rw [h9] at l9
  rw [h13, h5, loadHolds_gen_pow] at l14
  refine ⟨σ (.n 8), rfl, l9, fun i hi => ?_, _, l14, hret.symm⟩
  exact oqSem_query hs (hpre i hi).1 (hpre i hi).2 (hB i hi)

end
end LeanVM.Guest.B1
