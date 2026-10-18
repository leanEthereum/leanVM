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

end
end LeanVM.Guest.B1
