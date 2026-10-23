/-
  LeanVM.Guest.B1.Whir.QueriesComplete

  The completeness of `opening_queries`' blocks: each block holds at its honest values.
-/

module

public import LeanVM.Guest.B1.Whir.Queries
public import LeanVM.Guest.B1.Digest.Common

/-!
# `opening_queries`, completeness of the blocks (TRIAGE #28, #35)

Each block's completeness (`*_complete`): its relation from the honest values at its value range
(`*Vals`, a list from the block's first value) and the facts its checks ask.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The row -/

/-- The honest values of `pack4T` over the words `r0 .. r3`. -/
def oqPack4Vals (r0 r1 r2 r3 : E) : List E := [y, y * r1, r0 + y * r1, y, y * r3, r2 + y * r3]

/-- The honest values of `dot4T` over the words `r0 .. r3` and the weights `w0 .. w3`. -/
def oqDot4Vals (r0 r1 r2 r3 w0 w1 w2 w3 : E) : List E :=
  [w0, r0 * w0, w1, r1 * w1, r0 * w0 + r1 * w1, w2, r2 * w2, r0 * w0 + r1 * w1 + r2 * w2, w3, r3 * w3,
    r0 * w0 + r1 * w1 + r2 * w2 + r3 * w3]

theorem pack4T_complete {b r : ℕ} {next : Prop} {kret : List E → Prop}
    (hK : ∀ t < 4, IsInK (σ (.n (r + t))))
    (hv : ∀ k < 6, σ (.n (b + k)) = (oqPack4Vals (σ (.n r)) (σ (.n (r + 1))) (σ (.n (r + 2)))
      (σ (.n (r + 3)))).getD k 0) (hn : next) :
    Stmt.HoldsList C rd σ (pack4T b r) next kret := by
  rw [holds_pack4T]
  have v0 := hv 0 (by omega); have v1 := hv 1 (by omega); have v2 := hv 2 (by omega)
  have v3 := hv 3 (by omega); have v4 := hv 4 (by omega); have v5 := hv 5 (by omega)
  simp only [oqPack4Vals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5
  have k0 := hK 0 (by omega); have k1 := hK 1 (by omega); have k2 := hK 2 (by omega)
  have k3 := hK 3 (by omega)
  simp only [Nat.add_zero] at k0
  refine ⟨⟨k0, k1, v0, v1, by rw [v2, pack64x2_eq k0 k1]⟩, ⟨k2, k3, by simpa using v3,
    by simpa [Nat.add_assoc] using v4, by rw [show b + 3 + 2 = b + 5 by ring, v5, pack64x2_eq k2 k3]⟩,
    hn⟩

theorem dot4T_complete {b r wo : ℕ} {next : Prop} {kret : List E → Prop}
    (hw : ∀ t < 4, LoadHolds rd (σ (.n 2)) (wo + t) (memAt rd (σ (.n 2)) (wo + t)))
    (hv : ∀ k < 11, σ (.n (b + k)) = (oqDot4Vals (σ (.n r)) (σ (.n (r + 1))) (σ (.n (r + 2)))
      (σ (.n (r + 3))) (memAt rd (σ (.n 2)) wo) (memAt rd (σ (.n 2)) (wo + 1))
      (memAt rd (σ (.n 2)) (wo + 2)) (memAt rd (σ (.n 2)) (wo + 3))).getD k 0) (hn : next) :
    Stmt.HoldsList C rd σ (dot4T b r wo) next kret := by
  simp only [dot4T, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  have e0 := hv 0 (by omega); have e1 := hv 1 (by omega); have e2 := hv 2 (by omega)
  have e3 := hv 3 (by omega); have e4 := hv 4 (by omega); have e5 := hv 5 (by omega)
  have e6 := hv 6 (by omega); have e7 := hv 7 (by omega); have e8 := hv 8 (by omega)
  have e9 := hv 9 (by omega); have e10 := hv 10 (by omega)
  simp only [oqDot4Vals, List.getD_cons_zero, List.getD_cons_succ,
    Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  refine ⟨by rw [e0]; simpa using hw 0 (by omega), by rw [e1, e0], by rw [e2]; exact hw 1 (by omega),
    by rw [e3, e2], by rw [e4, e1, e3], by rw [e5]; exact hw 2 (by omega), by rw [e6, e5],
    by rw [e7, e4, e6], by rw [e8]; exact hw 3 (by omega), by rw [e9, e8], by rw [e10, e7, e9], hn⟩

theorem oq_getD_flatten_uniform {α : Type} {d : α} (f : ℕ → List α) (L : ℕ) (hL : ∀ j, (f j).length = L) :
    ∀ (n j p : ℕ), j < n → p < L →
      (((List.range n).map f).flatten).getD (L * j + p) d = (f j).getD p d := by
  intro n
  induction n with
  | zero => intro j p hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro j p hj hp
    rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
      List.flatten_singleton]
    have hlen : (((List.range n).map f).flatten).length = L * n := by
      rw [List.length_flatten, List.map_map]
      have : (List.range n).map (List.length ∘ f) = List.replicate n L :=
        List.ext_getElem (by simp) (fun i h1 h2 => by simp [hL])
      rw [this, List.sum_replicate, smul_eq_mul, mul_comm]
    rcases Nat.lt_or_ge j n with h | h
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; nlinarith),
        ← List.getD_eq_getElem?_getD, ih j p h hp]
    · obtain rfl : j = n := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega), hlen,
        ← List.getD_eq_getElem?_getD, Nat.add_sub_cancel_left]

/-- A row block's partial sums: the weighted words below `m`. -/
def oqRowSum (r w : ℕ → E) (m : ℕ) : E := ∑ j ∈ Finset.range m, r j * w j

/-- The honest values of level 0's row block `jb ≥ 1` (`rowBlk1T`, 18 values). -/
def oqBlk1Vals (r w : ℕ → E) (jb : ℕ) : List E :=
  oqPack4Vals (r (4 * jb)) (r (4 * jb + 1)) (r (4 * jb + 2)) (r (4 * jb + 3)) ++
    oqDot4Vals (r (4 * jb)) (r (4 * jb + 1)) (r (4 * jb + 2)) (r (4 * jb + 3)) (w (4 * jb))
      (w (4 * jb + 1)) (w (4 * jb + 2)) (w (4 * jb + 3)) ++ [oqRowSum r w (4 * (jb + 1))]

/-- The honest values of level 0's row after its words, from `8 + I`. -/
def oqRows1Vals (r w : ℕ → E) (I : ℕ) : List E :=
  oqPack4Vals (r 0) (r 1) (r 2) (r 3) ++ oqDot4Vals (r 0) (r 1) (r 2) (r 3) (w 0) (w 1) (w 2) (w 3) ++
    ((List.range (I / 4 - 1)).map fun j => oqBlk1Vals r w (j + 1)).flatten

theorem oq_length_pack4Vals (a b c d : E) : (oqPack4Vals a b c d).length = 6 := rfl
theorem oq_length_dot4Vals (a b c d e f g h : E) : (oqDot4Vals a b c d e f g h).length = 11 := rfl
theorem oq_length_blk1Vals (r w : ℕ → E) (jb : ℕ) : (oqBlk1Vals r w jb).length = 18 := rfl

theorem oq_getD_app_lt {α : Type} {d : α} {l l' : List α} {n : ℕ} (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem oq_getD_app_ge {α : Type} {d : α} {l l' : List α} {n : ℕ} (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem oq_rowSum_succ4 (r w : ℕ → E) (jb : ℕ) :
    oqRowSum r w (4 * (jb + 1)) = oqRowSum r w (4 * jb) + (r (4 * jb) * w (4 * jb) +
      r (4 * jb + 1) * w (4 * jb + 1) + r (4 * jb + 2) * w (4 * jb + 2) + r (4 * jb + 3) * w (4 * jb + 3)) := by
  simp only [oqRowSum, show 4 * (jb + 1) = 4 * jb + 3 + 1 by ring, Finset.sum_range_succ]
  ring

/-- **Level 0's row** (`base = 1`) at its honest values. -/
theorem oqRows1_complete {I : ℕ} (hI : 4 ≤ I) (h4 : I % 4 = 0) {r : ℕ → E} {kret : List E → Prop}
    (hrow : ∀ j < I, σ (.n (8 + j)) = r j) (hK : ∀ j < I, IsInK (r j))
    (hw : ∀ jw < I, LoadHolds rd (σ (.n 2)) jw (memAt rd (σ (.n 2)) jw))
    (hv : ∀ k < 17 + 18 * (I / 4 - 1), σ (.n (8 + I + k)) =
      (oqRows1Vals r (memAt rd (σ (.n 2))) I).getD k 0) :
    Stmt.HoldsList C rd σ (oqRows1 I) True kret := by
  set w := memAt rd (σ (.n 2))
  rw [oqRows1, holdsList_append, holdsList_append]
  simp only [oqRowHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and]
  rw [rowHead1T, holdsList_append]
  have hr : ∀ jb < I / 4, ∀ t < 4, σ (.n (8 + 4 * jb + t)) = r (4 * jb + t) := fun jb hjb t ht => by
    rw [show 8 + 4 * jb + t = 8 + (4 * jb + t) by ring]; exact hrow _ (by omega)
  have hK' : ∀ jb < I / 4, ∀ t < 4, IsInK (σ (.n (8 + 4 * jb + t))) := fun jb hjb t ht => by
    rw [hr jb hjb t ht]; exact hK _ (by omega)
  have q0 : σ (.n 8) = r 0 := by simpa using hrow 0 (by omega)
  have q1 : σ (.n (8 + 1)) = r 1 := hrow 1 (by omega)
  have q2 : σ (.n (8 + 2)) = r 2 := hrow 2 (by omega)
  have q3 : σ (.n (8 + 3)) = r 3 := hrow 3 (by omega)
  refine pack4T_complete (fun t ht => by simpa using hK' 0 (by omega) t ht) (fun k hk => ?_)
    (dot4T_complete (fun t ht => by simpa using hw t (by omega)) (fun k hk => ?_) ?_)
  · rw [hv k (by omega), oqRows1Vals, oq_getD_app_lt (by simp [oq_length_pack4Vals, oq_length_dot4Vals]; omega),
      oq_getD_app_lt (by simp [oq_length_pack4Vals]; omega), q0, q1, q2, q3]
  · rw [show 8 + I + 6 + k = 8 + I + (6 + k) by ring, hv _ (by omega), oqRows1Vals,
      oq_getD_app_lt (by simp [oq_length_pack4Vals, oq_length_dot4Vals]; omega),
      oq_getD_app_ge (by simp [oq_length_pack4Vals]), oq_length_pack4Vals, Nat.add_sub_cancel_left, q0, q1, q2, q3]
  · have hb' : ∀ j < I / 4 - 1, ∀ p < 18, σ (.n (7 + I + 18 * (j + 1) + p)) =
        (oqBlk1Vals r w (j + 1)).getD p 0 := by
      intro j hj p hp
      rw [show 7 + I + 18 * (j + 1) + p = 8 + I + (17 + (18 * j + p)) by ring, hv _ (by omega),
        oqRows1Vals, oq_getD_app_ge (by simp [oq_length_pack4Vals, oq_length_dot4Vals]),
        show 17 + (18 * j + p) - (oqPack4Vals (r 0) (r 1) (r 2) (r 3) ++
          oqDot4Vals (r 0) (r 1) (r 2) (r 3) (w 0) (w 1) (w 2) (w 3)).length = 18 * j + p by
          simp [oq_length_pack4Vals, oq_length_dot4Vals],
        oq_getD_flatten_uniform (fun j => oqBlk1Vals r w (j + 1)) 18 (fun _ => oq_length_blk1Vals r w _) _ _ _
          hj hp]
    rw [holdsList_range_flatten _ _ (fun _ => rfl)]
    refine ⟨fun j hj => ?_, trivial⟩
    rw [oq1Blk, rowBlk1T, holdsList_append, holdsList_append]
    have hb := hb' j hj
    have hrj := hr (j + 1) (by omega)
    refine pack4T_complete (hK' (j + 1) (by omega)) (fun k hk => ?_)
      (dot4T_complete (fun t ht => hw _ (by omega)) (fun k hk => ?_) ?_)
    · rw [hb k (by omega), oqBlk1Vals, oq_getD_app_lt (by simp [oq_length_pack4Vals, oq_length_dot4Vals]; omega),
        oq_getD_app_lt (by simp [oq_length_pack4Vals]; omega)]
      rw [show σ (.n (8 + 4 * (j + 1))) = r (4 * (j + 1)) from by simpa using hrj 0 (by omega),
        hrj 1 (by omega), hrj 2 (by omega), hrj 3 (by omega)]
    · rw [show 7 + I + 18 * (j + 1) + 6 + k = 7 + I + 18 * (j + 1) + (6 + k) by ring, hb _ (by omega),
        oqBlk1Vals, oq_getD_app_lt (by simp [oq_length_pack4Vals, oq_length_dot4Vals]; omega),
        oq_getD_app_ge (by simp [oq_length_pack4Vals]), oq_length_pack4Vals, Nat.add_sub_cancel_left]
      rw [show σ (.n (8 + 4 * (j + 1))) = r (4 * (j + 1)) from by simpa using hrj 0 (by omega),
        hrj 1 (by omega), hrj 2 (by omega), hrj 3 (by omega)]
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      have e17 := hb 17 (by omega)
      have e16 := hb 16 (by omega)
      simp only [oqBlk1Vals, oqPack4Vals, oqDot4Vals, List.cons_append, List.nil_append, List.getD_cons_succ,
        List.getD_cons_zero] at e17 e16
      rw [e17, show 7 + I + 18 * (j + 1) + 16 = 7 + I + 18 * (j + 1) + 16 from rfl, e16]
      rw [oq_rowSum_succ4]
      congr 1
      rcases j with _ | j
      · have := hv 16 (by omega)
        simp only [oqRows1Vals, oqPack4Vals, oqDot4Vals, List.cons_append, List.nil_append, List.getD_cons_succ,
          List.getD_cons_zero] at this
        rw [show 6 + I + 18 * (0 + 1) = 8 + I + 16 by ring, this, oqRowSum]
        simp [Finset.sum_range_succ]
      · have := hb' j (by omega) 17 (by omega)
        simp only [oqBlk1Vals, oqPack4Vals, oqDot4Vals, List.cons_append, List.nil_append, List.getD_cons_succ,
          List.getD_cons_zero] at this
        rw [show 6 + I + 18 * (j + 1 + 1) = 7 + I + 18 * (j + 1) + 17 by ring, this]

/-- A deeper level's packed cell `j`: limbs `2j`, `2j + 1`. -/
def oqPk0 (r : ℕ → E) (j : ℕ) : E := r (2 * j) + y * r (2 * j + 1)

/-- A deeper level's word `jw` as the guest computes it from its packed cells and limbs. -/
def oqWord0 (r : ℕ → E) (jw : ℕ) : E :=
  if jw % 2 = 0 then oqPk0 r (3 * jw / 2) + y * y * r (3 * jw + 2) else r (3 * jw) + y * oqPk0 r ((3 * jw + 1) / 2)

/-- The honest values of a deeper level's word `jw` and its weight: the word's three values, the
weight, the product. -/
def oqWordVals (r w : ℕ → E) (jw : ℕ) : List E :=
  (if jw % 2 = 0 then [y * y, y * y * r (3 * jw + 2), oqWord0 r jw]
    else [y, y * oqPk0 r ((3 * jw + 1) / 2), oqWord0 r jw]) ++ [w jw, oqWord0 r jw * w jw]

/-- The honest values of a deeper level's word `jw ≥ 1`, with the running dot product. -/
def oqWord0BlkVals (r w : ℕ → E) (jw : ℕ) : List E :=
  oqWordVals r w jw ++ [∑ j ∈ Finset.range (jw + 1), oqWord0 r j * w j]

/-- The honest values of a deeper level's row after its limbs, from `8 + 3I`: the packs, then the
words. -/
def oqRows0Vals (r w : ℕ → E) (I : ℕ) : List E :=
  ((List.range (3 * I / 4)).map fun jb =>
      oqPack4Vals (r (4 * jb)) (r (4 * jb + 1)) (r (4 * jb + 2)) (r (4 * jb + 3))).flatten ++
    oqWordVals r w 0 ++ ((List.range (I - 1)).map fun j => oqWord0BlkVals r w (j + 1)).flatten

theorem oq_length_wordVals (r w : ℕ → E) (jw : ℕ) : (oqWordVals r w jw).length = 5 := by
  unfold oqWordVals; split <;> rfl

theorem oq_length_word0BlkVals (r w : ℕ → E) (jw : ℕ) : (oqWord0BlkVals r w jw).length = 6 := by
  simp [oqWord0BlkVals, oq_length_wordVals]

theorem oq_length_flatten_uniform {α : Type} (f : ℕ → List α) (L : ℕ) (hL : ∀ j, (f j).length = L)
    (n : ℕ) : (((List.range n).map f).flatten).length = L * n := by
  rw [List.length_flatten, List.map_map]
  have : (List.range n).map (List.length ∘ f) = List.replicate n L :=
    List.ext_getElem (by simp) (fun i h1 h2 => by simp [hL])
  rw [this, List.sum_replicate, smul_eq_mul, mul_comm]

theorem word0T_complete {R jw c : ℕ} {r w : ℕ → E} {next : Prop} {kret : List E → Prop}
    (hr : ∀ j < 3 * jw + 3, σ (.n (8 + j)) = r j) (hpk : ∀ j ≤ (3 * jw + 1) / 2, σ (.n (oq0Pk R j)) = oqPk0 r j)
    (hw : LoadHolds rd (σ (.n 2)) jw (w jw)) (hv : ∀ k < 5, σ (.n (c + k)) = (oqWordVals r w jw).getD k 0)
    (hn : next) : Stmt.HoldsList C rd σ (oq0WordT R jw c ++ wordDotT c jw) next kret := by
  rw [holdsList_append, oq0WordT]
  have e3 := hv 3 (by omega); have e4 := hv 4 (by omega)
  have e0 := hv 0 (by omega); have e1 := hv 1 (by omega); have e2 := hv 2 (by omega)
  simp only [oqWordVals] at e0 e1 e2 e3 e4
  split
  · rename_i he
    simp only [he, ↓reduceIte, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
      Nat.add_zero] at e0 e1 e2 e3 e4
    simp only [wordEvenT, wordDotT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_yy]
    refine ⟨e0, by rw [e1, e0, hr _ (by omega)], ?_, by rw [e3]; exact hw, by rw [e4, e2, e3], hn⟩
    rw [e2, e1, hpk _ (by omega), oqWord0, ite_pos' he]
  · rename_i he
    simp only [he, ↓reduceIte, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
      Nat.add_zero] at e0 e1 e2 e3 e4
    simp only [wordOddT, wordDotT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_y]
    refine ⟨e0, by rw [e1, e0, hpk _ le_rfl], ?_, by rw [e3]; exact hw, by rw [e4, e2, e3], hn⟩
    rw [e2, e1, hr _ (by omega), oqWord0, ite_neg' he]

/-- **A deeper level's row** (`base = 0`) at its honest values. -/
theorem oqRows0_complete {I : ℕ} (hI : 4 ≤ I) (h4 : I % 4 = 0) {r : ℕ → E} {kret : List E → Prop}
    (hrow : ∀ j < 3 * I, σ (.n (8 + j)) = r j) (hK : ∀ j < 3 * I, IsInK (r j))
    (hw : ∀ jw < I, LoadHolds rd (σ (.n 2)) jw (memAt rd (σ (.n 2)) jw))
    (hv : ∀ k < 6 * (3 * I / 4) + 5 + 6 * (I - 1), σ (.n (8 + 3 * I + k)) =
      (oqRows0Vals r (memAt rd (σ (.n 2))) I).getD k 0) :
    Stmt.HoldsList C rd σ (oqRows0 I) True kret := by
  set w := memAt rd (σ (.n 2))
  have hlp : (((List.range (3 * I / 4)).map fun jb =>
      oqPack4Vals (r (4 * jb)) (r (4 * jb + 1)) (r (4 * jb + 2)) (r (4 * jb + 3))).flatten).length =
        6 * (3 * I / 4) := oq_length_flatten_uniform _ 6 (fun _ => rfl) _
  have hpack : ∀ jb < 3 * I / 4, ∀ p < 6, σ (.n (8 + 3 * I + 6 * jb + p)) =
      (oqPack4Vals (r (4 * jb)) (r (4 * jb + 1)) (r (4 * jb + 2)) (r (4 * jb + 3))).getD p 0 := by
    intro jb hjb p hp
    rw [show 8 + 3 * I + 6 * jb + p = 8 + 3 * I + (6 * jb + p) by ring, hv _ (by omega), oqRows0Vals,
      List.append_assoc, oq_getD_app_lt (by rw [hlp]; omega),
      oq_getD_flatten_uniform (fun jb => oqPack4Vals (r (4 * jb)) (r (4 * jb + 1)) (r (4 * jb + 2))
        (r (4 * jb + 3))) 6 (fun _ => rfl) _ _ _ hjb hp]
  have hpk : ∀ j < 3 * I / 2, σ (.n (oq0Pk (3 * I) j)) = oqPk0 r j := by
    intro j hj
    obtain ⟨jb, e, he, rfl⟩ : ∃ jb e, e < 2 ∧ j = 2 * jb + e := ⟨j / 2, j % 2, by omega, by omega⟩
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · rw [oq0Pk, show 10 + 3 * I + 3 * (2 * jb + 0) = 8 + 3 * I + 6 * jb + 2 by ring,
        hpack jb (by omega) 2 (by omega)]
      simp [oqPack4Vals, oqPk0, show 2 * (2 * jb) = 4 * jb by ring]
    · rw [oq0Pk, show 10 + 3 * I + 3 * (2 * jb + 1) = 8 + 3 * I + 6 * jb + 5 by ring,
        hpack jb (by omega) 5 (by omega)]
      simp [oqPack4Vals, oqPk0, show 2 * (2 * jb + 1) = 4 * jb + 2 by ring, show 4 * jb + 2 + 1 = 4 * jb + 3 by ring]
  have hword : ∀ jw < I, ∀ k < 5, ∀ c, c = oq0W0 I + (if jw = 0 then 0 else 6 * jw - 1) →
      σ (.n (c + k)) = (oqWordVals r w jw).getD k 0 := by
    intro jw hjw k hk c hc
    subst hc
    rcases Nat.eq_zero_or_pos jw with rfl | hpos
    · rw [ite_pos' rfl, Nat.add_zero, oq0W0, show 8 + 3 * I + 6 * (3 * I / 4) + k =
        8 + 3 * I + (6 * (3 * I / 4) + k) by ring, hv _ (by omega), oqRows0Vals, oq_getD_app_lt (by
        rw [List.length_append, hlp, oq_length_wordVals]; omega), oq_getD_app_ge (by rw [hlp]; omega), hlp]
      congr 1; omega
    · rw [ite_neg' (by omega), oq0W0, show 8 + 3 * I + 6 * (3 * I / 4) + (6 * jw - 1) + k =
        8 + 3 * I + (6 * (3 * I / 4) + 5 + (6 * (jw - 1) + k)) by omega, hv _ (by omega), oqRows0Vals,
        oq_getD_app_ge (by rw [List.length_append, hlp, oq_length_wordVals]; omega), List.length_append, hlp,
        oq_length_wordVals, show 6 * (3 * I / 4) + 5 + (6 * (jw - 1) + k) - (6 * (3 * I / 4) + 5) =
          6 * (jw - 1) + k by omega,
        oq_getD_flatten_uniform (fun j => oqWord0BlkVals r w (j + 1)) 6 (fun _ => oq_length_word0BlkVals r w _)
          _ _ _ (by omega) (by omega), show jw - 1 + 1 = jw by omega, oqWord0BlkVals,
        oq_getD_app_lt (by rw [oq_length_wordVals]; omega)]
  rw [oqRows0, holdsList_append, holdsList_append, holdsList_append, holdsList_append]
  simp only [oqRowHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and]
  rw [holdsList_range_flatten _ _ (fun _ => rfl)]
  refine ⟨fun jb hjb => ?_, ?_⟩
  · rw [oq0Pack]
    have h4r : ∀ t < 4, σ (.n (8 + 4 * jb + t)) = r (4 * jb + t) := fun t ht => by
      rw [show 8 + 4 * jb + t = 8 + (4 * jb + t) by ring]; exact hrow _ (by omega)
    refine pack4T_complete (fun t ht => ?_) (fun k hk => ?_) trivial
    · rw [h4r t ht]; exact hK _ (by omega)
    · rw [hpack jb hjb k hk, h4r 1 (by omega), h4r 2 (by omega), h4r 3 (by omega),
        show σ (.n (8 + 4 * jb)) = r (4 * jb) from by simpa using h4r 0 (by omega)]
  rw [← holdsList_append]
  refine word0T_complete (jw := 0) (fun j hj => hrow j (by omega)) (fun j hj => hpk j (by omega))
    (by simpa using hw 0 (by omega)) (fun k hk => hword 0 (by omega) k hk _ (by simp)) ?_
  rw [holdsList_range_flatten _ _ (fun _ => oq0Blk_noRet _ _)]
  refine ⟨fun j hj => ?_, trivial⟩
  rw [oq0Blk, holdsList_append]
  refine word0T_complete (jw := j + 1) (fun j' hj' => hrow j' (by omega)) (fun j' hj' => hpk j' (by omega))
    (hw _ (by omega)) (fun k hk => hword (j + 1) (by omega) k hk _ (by simp; omega)) ?_
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
  have e5 : σ (.n (oq0W0 I + 6 * (j + 1) - 1 + 5)) = ∑ i ∈ Finset.range (j + 2), oqWord0 r i * w i := by
    have := hv (6 * (3 * I / 4) + 5 + (6 * j + 5)) (by omega)
    rw [oqRows0Vals, oq_getD_app_ge (by rw [List.length_append, hlp, oq_length_wordVals]; omega),
      List.length_append, hlp, oq_length_wordVals, show 6 * (3 * I / 4) + 5 + (6 * j + 5) - (6 * (3 * I / 4) + 5) =
        6 * j + 5 by omega,
      oq_getD_flatten_uniform (fun j => oqWord0BlkVals r w (j + 1)) 6 (fun _ => oq_length_word0BlkVals r w _)
        _ _ _ hj (by omega)] at this
    rw [show oq0W0 I + 6 * (j + 1) - 1 + 5 = 8 + 3 * I + (6 * (3 * I / 4) + 5 + (6 * j + 5)) by
      simp [oq0W0]; omega, this]
    simp [oqWord0BlkVals, oq_length_wordVals]
  have e4 := hword (j + 1) (by omega) 4 (by omega) (oq0W0 I + 6 * (j + 1) - 1) (by simp; omega)
  simp only [oqWordVals] at e4
  have hprev : σ (.n (oq0W0 I + 6 * (j + 1) - 2)) = ∑ i ∈ Finset.range (j + 1), oqWord0 r i * w i := by
    rcases j with _ | j
    · have := hword 0 (by omega) 4 (by omega) (oq0W0 I) (by simp)
      simp only [oqWordVals] at this
      rw [show oq0W0 I + 6 * (0 + 1) - 2 = oq0W0 I + 4 by omega, this]
      split <;> simp
    · have := hv (6 * (3 * I / 4) + 5 + (6 * j + 5)) (by omega)
      rw [oqRows0Vals, oq_getD_app_ge (by rw [List.length_append, hlp, oq_length_wordVals]; omega),
        List.length_append, hlp, oq_length_wordVals, show 6 * (3 * I / 4) + 5 + (6 * j + 5) - (6 * (3 * I / 4) + 5) =
          6 * j + 5 by omega,
        oq_getD_flatten_uniform (fun j => oqWord0BlkVals r w (j + 1)) 6 (fun _ => oq_length_word0BlkVals r w _)
          _ _ _ (by omega) (by omega)] at this
      rw [show oq0W0 I + 6 * (j + 1 + 1) - 2 = 8 + 3 * I + (6 * (3 * I / 4) + 5 + (6 * j + 5)) by
        simp [oq0W0]; omega, this]
      simp [oqWord0BlkVals, oq_length_wordVals]
  rw [e5, hprev, Finset.sum_range_succ _ (j + 1)]
  split at e4 <;> simp at e4 <;> rw [e4]

/-! ## The leaf hash -/

/-- The leaf's blocks as the guest packs them. -/
def oqLeafBl (σ : Val) (base I : ℕ) (j : ℕ) : Fin 4 → E :=
  ![σ (.n (oqPk base I (4 * j))), σ (.n (oqPk base I (4 * j + 1))), σ (.n (oqPk base I (4 * j + 2))),
    σ (.n (oqPk base I (4 * j + 3)))]

/-- **The leaf hash** at its honest values: the IV, then each block's metadata and the chain's
next state (`chainRun`). -/
theorem oqLeaf_complete {base I blocks : ℕ} (hbl : 1 ≤ blocks) {next : Prop} {kret : List E → Prop}
    (hcan : ∀ j < blocks, ∀ t, IsCanonical128 (oqLeafBl σ base I j t))
    (hiv0 : σ (.n (oqK1 base I)) = (digestScalars paramIv).1)
    (hiv1 : σ (.n (oqK1 base I + 1)) = (digestScalars paramIv).2)
    (hmd : ∀ j < blocks, σ (.n (oqK1 base I + 3 * j + 2)) = oqMd blocks j)
    (hst : ∀ j < blocks, (σ (.n (oqK1 base I + 3 * j + 3)), σ (.n (oqK1 base I + 3 * j + 4))) =
      digestScalars (chainRun paramIv (oqLeafBl σ base I) (oqMd blocks) (j + 1))) (hn : next) :
    Stmt.HoldsList C rd σ (oqLeafT base I blocks) next kret := by
  set K1 := oqK1 base I
  have hmdc : ∀ j, IsCanonical128 (oqMd blocks j) := fun j => by
    rw [oqMd_eq]; exact isCanonical128_metadataCell _ _
  have hchain : ∀ j ≤ blocks, (if j = 0 then (σ (.n K1), σ (.n (K1 + 1)))
      else (σ (.n (K1 + 3 * j)), σ (.n (K1 + 3 * j + 1)))) =
      digestScalars (chainRun paramIv (oqLeafBl σ base I) (oqMd blocks) j) := by
    intro j hj
    rcases j with _ | j
    · simp only [↓reduceIte, chainRun, hiv0, hiv1]
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [show K1 + 3 * (j + 1) = K1 + 3 * j + 3 by ring, show K1 + 3 * j + 3 + 1 = K1 + 3 * j + 4 by ring]
      exact hst j (by omega)
  rw [oqLeafT, holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_iv0, word_iv1]
  have c0 := hchain 0 (by omega)
  simp only [↓reduceIte] at c0
  refine ⟨by rw [hiv0, ← iv0_word]; exact word_iv0, by rw [hiv1, ← iv1_word]; exact word_iv1,
    by simpa using hmd 0 hbl, ?_, ?_⟩
  · have := (compressCells_chainRun (h := paramIv) (blocks := oqLeafBl σ base I) (md := oqMd blocks)
      (i := 0) (hcan 0 hbl) (hmdc 0)).mpr (by simpa using hst 0 hbl)
    simp only [chainRun] at this
    rw [show σ (.n (oqK1 base I + 2)) = oqMd blocks 0 by simpa using hmd 0 hbl, hiv0, hiv1]
    exact this
  · rw [holdsList_range_flatten _ _ (fun _ => rfl)]
    refine ⟨fun j hj => ?_, hn⟩
    simp only [oqLeafBlk, leafBlkT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    have hc := hchain (j + 1) (by omega)
    simp only [Nat.add_one_ne_zero, ↓reduceIte] at hc
    refine ⟨hmd (j + 1) (by omega), ?_⟩
    have := (compressCells_chainRun (h := paramIv) (blocks := oqLeafBl σ base I) (md := oqMd blocks)
      (i := j + 1) (o0 := σ (.n (oqK1 base I + 3 * (j + 1) + 2 + 1)))
      (o1 := σ (.n (oqK1 base I + 3 * (j + 1) + 2 + 2))) (hcan (j + 1) (by omega)) (hmdc (j + 1))).mpr (by
        rw [show oqK1 base I + 3 * (j + 1) + 2 + 1 = oqK1 base I + 3 * (j + 1) + 3 by ring,
          show oqK1 base I + 3 * (j + 1) + 2 + 2 = oqK1 base I + 3 * (j + 1) + 4 by ring]
        exact hst (j + 1) (by omega))
    rw [← congrArg Prod.fst hc, ← congrArg Prod.snd hc, ← hmd (j + 1) (by omega)] at this
    exact this

/-! ## The query sum and the bit run -/

/-- **The query sum and the bit run** at their honest values: `qsc[x]`, `qw[x]`, the row's dot
`σ (K1 - 1)`, `qsc[x·g] = qsc[x] + qw[x]·dot`, the bit run `qbp[x]`. -/
theorem oqSumT_complete {base I blocks : ℕ} {next : Prop} {kret : List E → Prop}
    (h0 : σ (.n (oqK2 base I blocks)) = σ (.n 3) * σ (.n 0))
    (l1 : LoadHolds rd (σ (.n 3) * σ (.n 0)) 0 (σ (.n (oqK2 base I blocks + 1))))
    (h2 : σ (.n (oqK2 base I blocks + 2)) = σ (.n 4) * σ (.n 0))
    (l3 : LoadHolds rd (σ (.n 4) * σ (.n 0)) 0 (σ (.n (oqK2 base I blocks + 3))))
    (h4 : σ (.n (oqK2 base I blocks + 4)) = σ (.n (oqK2 base I blocks + 3)) * σ (.n (oqK1 base I - 1)))
    (h5 : σ (.n (oqK2 base I blocks + 5)) = σ (.n (oqK2 base I blocks + 1)) + σ (.n (oqK2 base I blocks + 4)))
    (h6 : σ (.n (oqK2 base I blocks + 6)) = σ (.n 3) * σ (.n 0))
    (l7 : LoadHolds rd (σ (.n 3) * σ (.n 0)) 1 (σ (.n (oqK2 base I blocks + 5))))
    (h8 : σ (.n (oqK2 base I blocks + 7)) = σ (.n 5) * σ (.n 0))
    (l9 : LoadHolds rd (σ (.n 5) * σ (.n 0)) 0 (σ (.n (oqK2 base I blocks + 8)))) (hn : next) :
    Stmt.HoldsList C rd σ (oqSumT base I blocks) next kret := by
  simp only [oqSumT, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  exact ⟨h0, by rw [h0]; exact l1, h2, by rw [h2]; exact l3, h4, h5, h6, by rw [h6]; exact l7, h8,
    by rw [h8]; exact l9, hn⟩

/-! ## The Merkle path -/

theorem oq_climbCells_getD {D : Digest} {q : ℕ} {sibs : List Digest} {l t : ℕ} (hl : l < sibs.length)
    (ht : t < 4) : (climbCells D q sibs).getD (4 * l + t) 0 =
      (lvlCells (climbAt D q sibs l) (sibs.getD l default) (q.testBit l)).getD t 0 :=
  oq_getD_flatten_uniform (fun l => lvlCells (climbAt D q sibs l) (sibs.getD l default) (q.testBit l)) 4
    (fun _ => length_lvlCells _ _ _) _ _ _ hl ht

/-- The honest values of path level `0` from `P + 81`. -/
def oqPath0Vals (ptr : E) (D : Digest) (q : ℕ) (sibs : List Digest) : List E :=
  [bitE (q.testBit 0), 1, eOfNat 5, bitE (q.testBit 0) * eOfNat 5, 1 + bitE (q.testBit 0) * eOfNat 5,
    ptr * (1 + bitE (q.testBit 0) * eOfNat 5), Value.ivCells.1, Value.ivCells.2, metadataCell 64 true,
    (digestScalars (climbAt D q sibs 1)).1, (digestScalars (climbAt D q sibs 1)).2]

/-- The honest values of path level `l ≥ 1` from `P + 79 + 13·l`. -/
def oqPathLVals (ptr : E) (D : Digest) (q : ℕ) (sibs : List Digest) (l : ℕ) : List E :=
  [bitE (q.testBit l), gen ^ (4 * l), ptr * gen ^ (4 * l), 1, eOfNat 5, bitE (q.testBit l) * eOfNat 5,
    1 + bitE (q.testBit l) * eOfNat 5, ptr * gen ^ (4 * l) * (1 + bitE (q.testBit l) * eOfNat 5),
    Value.ivCells.1, Value.ivCells.2, metadataCell 64 true, (digestScalars (climbAt D q sibs (l + 1))).1,
    (digestScalars (climbAt D q sibs (l + 1))).2]

/-- One level's hash: the level's four cells compress to the next node. -/
theorem oq_compress_level {D : Digest} {q : ℕ} {sibs : List Digest} {l : ℕ} (hl : l < sibs.length) :
    CompressCells ![(climbCells D q sibs).getD (4 * l) 0, (climbCells D q sibs).getD (4 * l + 1) 0,
      (climbCells D q sibs).getD (4 * l + 2) 0, (climbCells D q sibs).getD (4 * l + 3) 0]
      Value.ivCells.1 Value.ivCells.2 (digestScalars (climbAt D q sibs (l + 1))).1
      (digestScalars (climbAt D q sibs (l + 1))).2 (metadataCell 64 true) := by
  have e := fun t (ht : t < 4) => oq_climbCells_getD (D := D) (q := q) (l := l) hl ht
  rw [show 4 * l = 4 * l + 0 from rfl, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega),
    climbAt_succ D q sibs hl]
  cases q.testBit l <;> exact compress_of_hashPair _ _

/-- The selected child: the running node at offset `4l + 2b` of the level's cells. -/
theorem oq_node_load {D : Digest} {q : ℕ} {sibs : List Digest} {l : ℕ} (hl : l < sibs.length) {ptr : E}
    (hcell : ∀ j < 4 * sibs.length, LoadHolds rd ptr j ((climbCells D q sibs).getD j 0)) :
    LoadHolds rd (ptr * gen ^ (4 * l) * (1 + bitE (q.testBit l) * eOfNat 5)) 0
        (digestScalars (climbAt D q sibs l)).1 ∧
      LoadHolds rd (ptr * gen ^ (4 * l) * (1 + bitE (q.testBit l) * eOfNat 5)) 1
        (digestScalars (climbAt D q sibs l)).2 := by
  rw [one_add_bitE_five, mul_assoc, ← pow_add, LeanVM.Guest.B1.loadHolds_mul_gen_pow,
    LeanVM.Guest.B1.loadHolds_mul_gen_pow]
  have e := fun t (ht : t < 4) => oq_climbCells_getD (D := D) (q := q) (l := l) hl ht
  have c0 := hcell (4 * l + 2 * (q.testBit l).toNat) (by cases q.testBit l <;> simp <;> omega)
  have c1 := hcell (4 * l + 2 * (q.testBit l).toNat + 1) (by cases q.testBit l <;> simp <;> omega)
  rw [e _ (by cases q.testBit l <;> simp)] at c0
  rw [show 4 * l + 2 * (q.testBit l).toNat + 1 = 4 * l + (2 * (q.testBit l).toNat + 1) by ring,
    e _ (by cases q.testBit l <;> simp)] at c1
  rw [Nat.add_zero]
  rcases hb : q.testBit l with _ | _
  · rw [hb] at c0 c1
    simp only [lvlCells, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.mul_zero, Nat.zero_add,
      Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at c0 c1 ⊢
    exact ⟨c0, c1⟩
  · rw [hb] at c0 c1
    simp only [lvlCells, ↓reduceIte, Bool.toNat_true, Nat.mul_one, List.getD_cons_zero,
      List.getD_cons_succ] at c0 c1 ⊢
    exact ⟨c0, by simpa [Nat.add_assoc] using c1⟩

/-- **`verify_merkle_path`** (`oqPathT`) at its honest values: the hinted children the climb's
cells (`climbCells`), the frame run at `ptr` holding them, the running nodes the climb's. -/
theorem oqPathT_complete {base I blocks pd : ℕ} (hpd : 1 ≤ pd) (hpd20 : pd ≤ 20) {D : Digest} {q : ℕ}
    {sibs : List Digest} (hsl : sibs.length = pd) {ptr : E} {next : Prop} {kret : List E → Prop}
    (hK : (σ (.n (oqK1 base I + 3 * blocks)), σ (.n (oqK1 base I + 3 * blocks + 1))) = digestScalars D)
    (hcs : ∀ j < 4 * pd, σ (.n (oqP base I blocks + j)) = (climbCells D q sibs).getD j 0)
    (hptr : σ (.n (oqP base I blocks + 4 * pd)) = ptr) (hptrK : IsInK ptr)
    (hcell : ∀ j < 4 * pd, LoadHolds rd ptr j ((climbCells D q sibs).getD j 0))
    (hfr2 : ∀ j < 80 - 4 * pd, ∀ w, rd (ptr.limb 0 * Parameters.gpow (4 * pd + j)) = some w →
      w = σ (.n (oqP base I blocks + 4 * pd + 1 + j)))
    (hbits : ∀ l < pd, LoadHolds rd (σ (.n (oqP base I blocks - 1))) l (bitE (q.testBit l)))
    (hv0 : ∀ t < 11, σ (.n (oqP base I blocks + 81 + t)) = (oqPath0Vals ptr D q sibs).getD t 0)
    (hvl : ∀ l < pd - 1, ∀ t < 13, σ (.n (oqP base I blocks + 79 + 13 * (l + 1) + t)) =
      (oqPathLVals ptr D q sibs (l + 1)).getD t 0) (hn : next) :
    Stmt.HoldsList C rd σ (oqPathT base I blocks pd) next kret := by
  rw [oqPathT, holdsList_append]
  subst hsl
  have hcell' : ∀ j < 4 * sibs.length, LoadHolds rd ptr j ((climbCells D q sibs).getD j 0) := hcell
  generalize oqP base I blocks = P at *
  generalize oqK1 base I + 3 * blocks = K at *
  have e0 := hv0 0 (by omega); have e1 := hv0 1 (by omega); have e2 := hv0 2 (by omega)
  have e3 := hv0 3 (by omega); have e4 := hv0 4 (by omega); have e5 := hv0 5 (by omega)
  have e6 := hv0 6 (by omega); have e7 := hv0 7 (by omega); have e8 := hv0 8 (by omega)
  have e9 := hv0 9 (by omega); have e10 := hv0 10 (by omega)
  simp only [oqPath0Vals, List.getD_cons_zero, List.getD_cons_succ,
    show ∀ t, P + 81 + t = t + P + 81 from fun t => by ring] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, word_iv0, word_iv1, word_md64,
    word_eOfNat, eOfNat_one]
  obtain ⟨n0, n1⟩ := oq_node_load (l := 0) (by omega) hcell'
  have k0 : (σ (.n K), σ (.n (K + 1))) = digestScalars (climbAt D q sibs 0) := hK
  have r81 : ∀ t, P + 81 + t = t + P + 81 := fun t => by ring
  refine ⟨⟨by rw [hptr]; exact hptrK, fun k hk w hw => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · rw [show P + 81 = 0 + P + 81 by ring, e0]; simpa using hbits 0 (by omega)
  · rw [show P + 82 = 1 + P + 81 by ring, e1]
  · rw [show P + 83 = 2 + P + 81 by ring, e2]
  · rw [show P + 84 = 3 + P + 81 by ring, e3, show P + 81 = 0 + P + 81 by ring, e0,
      show P + 83 = 2 + P + 81 by ring, e2]
  · rw [show P + 85 = 4 + P + 81 by ring, e4, show P + 82 = 1 + P + 81 by ring, e1,
      show P + 84 = 3 + P + 81 by ring, e3]
  · rw [show P + 86 = 5 + P + 81 by ring, e5, hptr, show P + 85 = 4 + P + 81 by ring, e4]
  · rw [show P + 86 = 5 + P + 81 by ring, e5, show σ (.n K) = _ from congrArg Prod.fst k0]
    simpa using n0
  · rw [show P + 86 = 5 + P + 81 by ring, e5, show σ (.n (K + 1)) = _ from congrArg Prod.snd k0]
    simpa using n1
  · rw [show P + 87 = 6 + P + 81 by ring, e6]
  · rw [show P + 88 = 7 + P + 81 by ring, e7]
  · rw [show P + 89 = 8 + P + 81 by ring, e8]
  rotate_left 2
  · rw [hptr] at hw
    rcases Nat.lt_or_ge k (4 * sibs.length) with hk4 | hk4
    · rw [getElem_frameRun hk4, hcs k hk4]
      exact Option.some.inj (hw.symm.trans (hcell' k hk4).2)
    · have hk80 : k < 80 := by simp at hk; omega
      rw [List.getElem_append_right (by simpa using hk4)]
      simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range]
      have := hfr2 (k - 4 * sibs.length) (by omega) w (by rw [show 4 * sibs.length + (k - 4 * sibs.length) = k by omega]; exact hw)
      exact this
  · rw [show P + 87 = 6 + P + 81 by ring, e6, show P + 88 = 7 + P + 81 by ring, e7,
      show P + 89 = 8 + P + 81 by ring, e8, show P + 90 = 9 + P + 81 by ring, e9,
      show P + 91 = 10 + P + 81 by ring, e10]
    have hc := oq_compress_level (D := D) (q := q) (sibs := sibs) (l := 0) (by omega)
    rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.zero_add] at hc
    have h0' : σ (.n P) = (climbCells D q sibs).getD 0 0 := by simpa using hcs 0 (by omega)
    rw [h0', hcs 1 (by omega), hcs 2 (by omega), hcs 3 (by omega)]
    exact hc
  · rw [holdsList_range_flatten _ _ (fun _ => rfl)]
    refine ⟨fun j hj => ?_, hn⟩
    have hv := hvl j hj
    set l := j + 1 with hl
    have f := fun t (ht : t < 13) => hv t ht
    have f0 := f 0 (by omega); have f1 := f 1 (by omega); have f2 := f 2 (by omega)
    have f3 := f 3 (by omega); have f4 := f 4 (by omega); have f5 := f 5 (by omega)
    have f6 := f 6 (by omega); have f7 := f 7 (by omega); have f8 := f 8 (by omega)
    have f9 := f 9 (by omega); have f10 := f 10 (by omega); have f11 := f 11 (by omega)
    have f12 := f 12 (by omega)
    simp only [oqPathLVals, List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add,
      show ∀ t, P + 79 + 13 * l + t = t + (P + 79 + 13 * l) from fun t => by ring]
      at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
    simp only [oqLevel, levelT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_iv0, word_iv1,
      word_md64, word_eOfNat, eOfNat_one, show ∀ t, P + 79 + 13 * l + t = t + (P + 79 + 13 * l) from
        fun t => by ring]
    have hg : kw (gpowK (4 * l)) = gen ^ (4 * l) := kw_gpowK (lt_trans (show 4 * l < 2 ^ 7 by omega) (by decide))
    obtain ⟨m0, m1⟩ := oq_node_load (l := l) (by omega) hcell'
    have hprev : σ (.n (P + 77 + 13 * l)) = (digestScalars (climbAt D q sibs l)).1 ∧
        σ (.n (P + 77 + 13 * l + 1)) = (digestScalars (climbAt D q sibs l)).2 := by
      rcases j with _ | j
      · rw [show P + 77 + 13 * l + 1 = 10 + P + 81 by omega, show P + 77 + 13 * l = 9 + P + 81 by omega,
          e9, e10]
        exact ⟨rfl, rfl⟩
      · have g := hvl j (by omega)
        have g11 := g 11 (by omega); have g12 := g 12 (by omega)
        simp only [oqPathLVals, List.getD_cons_zero, List.getD_cons_succ] at g11 g12
        rw [show P + 77 + 13 * l + 1 = P + 79 + 13 * (j + 1) + 12 by omega,
          show P + 77 + 13 * l = P + 79 + 13 * (j + 1) + 11 by omega, g11, g12]
        exact ⟨rfl, rfl⟩
    have hc := oq_compress_level (D := D) (q := q) (sibs := sibs) (l := l) (by omega)
    rw [← hcs (4 * l) (by omega), ← hcs (4 * l + 1) (by omega), ← hcs (4 * l + 2) (by omega),
      ← hcs (4 * l + 3) (by omega)] at hc
    refine ⟨by rw [f0]; exact hbits l (by omega), by rw [f1, hg], by rw [f2, hptr, f1], by rw [f3],
      by rw [f4], by rw [f5, f0, f4], by rw [f6, f3, f5], by rw [f7, f2, f6], ?_, ?_, by rw [f8],
      by rw [f9], by rw [f10], ?_⟩
    · rw [f7, show P + 77 + 13 * l = P + 77 + 13 * l from rfl, hprev.1]; exact m0
    · rw [f7, show P + 78 + 13 * l = P + 77 + 13 * l + 1 by ring, hprev.2]; exact m1
    · rw [f8, f9, f10, f11, f12]
      simpa [show 4 * l + 1 = 4 * l + 1 from rfl, Nat.add_assoc] using hc

/-! ## The cap leaf and the tail -/

/-- The honest values of cap bit `t` from `K6 + 1 + 6t`. -/
def oqCapBitVals (rd : Reader) (dbp : E) (pd cd t : ℕ) : List E :=
  [1, memAt rd dbp (pd + 1 + t), 1 + gen ^ 2 ^ t, memAt rd dbp (pd + 1 + t) * (1 + gen ^ 2 ^ t),
    1 + memAt rd dbp (pd + 1 + t) * (1 + gen ^ 2 ^ t), capPar rd dbp pd cd (t + 1)]

/-- The honest values of the cap leaf's tail from `K7`. -/
def oqCapTailVals (rd : Reader) (dbp flags cap x N : E) (pd cd : ℕ) : List E :=
  let P' := capPar rd dbp pd cd (cd - 1)
  let b := memAt rd dbp pd
  let idx := capIdx rd dbp pd cd
  [1, flags * P', P' * P', 1, b, eOfNat 3, b * eOfNat 3, 1 + b * eOfNat 3, idx, idx * idx, cap * (idx * idx),
    gen, gen * idx, gen * idx * idx, cap * (gen * idx * idx), gen, x * gen, x * gen + N, gen, x * gen]

/-- The honest values of the cap leaf (`oqCapT`) from `K6 = P + 79 + 13·pd`. -/
def oqCapVals (rd : Reader) (dbp flags cap x N : E) (pd cd : ℕ) : List E :=
  [gen ^ 2 ^ (cd - 1)] ++ ((List.range (cd - 1)).map (oqCapBitVals rd dbp pd cd)).flatten ++
    oqCapTailVals rd dbp flags cap x N pd cd

theorem oq_length_capBitVals (rd : Reader) (dbp : E) (pd cd t : ℕ) :
    (oqCapBitVals rd dbp pd cd t).length = 6 := rfl

/-- **The cap leaf and the loop's tail** at their honest values: the bits read, the parent's flag
`1`, the path's top at the leaf, the next iteration's call. -/
theorem oqCapT_complete {P pd cd : ℕ} (hcd : 1 ≤ cd) (hcd8 : cd ≤ 8) {loop : String} {kret : List E → Prop}
    (hv : ∀ k < 1 + 6 * (cd - 1) + 20, σ (.n (P + 79 + 13 * pd + k)) =
      (oqCapVals rd (σ (.n (P - 1))) (σ (.n 6)) (σ (.n 7)) (σ (.n 0)) (σ (.n 1)) pd cd).getD k 0)
    (hbits : ∀ t < cd, LoadHolds rd (σ (.n (P - 1))) (pd + t) (memAt rd (σ (.n (P - 1))) (pd + t)))
    (hflag : LoadHolds rd (σ (.n 6) * capPar rd (σ (.n (P - 1))) pd cd (cd - 1)) 0 1)
    (htop0 : LoadHolds rd (σ (.n 7) * (capIdx rd (σ (.n (P - 1))) pd cd * capIdx rd (σ (.n (P - 1))) pd cd))
      0 (σ (.n (P + 77 + 13 * pd))))
    (htop1 : LoadHolds rd (σ (.n 7) * (gen * capIdx rd (σ (.n (P - 1))) pd cd *
      capIdx rd (σ (.n (P - 1))) pd cd)) 0 (σ (.n (P + 77 + 13 * pd + 1))))
    (hK : IsInK (σ (.n 0) * gen + σ (.n 1)))
    (hcall : σ (.n 0) * gen + σ (.n 1) ≠ 0 →
      C loop [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)] [])
    (hret : kret []) :
    Stmt.HoldsList C rd σ (oqCapT P pd cd loop) False kret := by
  set K6 := P + 79 + 13 * pd
  set dbp := σ (.n (P - 1))
  have hlb : (((List.range (cd - 1)).map (oqCapBitVals rd dbp pd cd)).flatten).length = 6 * (cd - 1) :=
    oq_length_flatten_uniform _ 6 (fun _ => rfl) _
  have hbit : ∀ t < cd - 1, ∀ c < 6, σ (.n (K6 + 1 + 6 * t + c)) = (oqCapBitVals rd dbp pd cd t).getD c 0 := by
    intro t ht c hc
    rw [show K6 + 1 + 6 * t + c = K6 + (1 + (6 * t + c)) by ring, hv _ (by omega), oqCapVals,
      List.append_assoc, oq_getD_app_ge (by simp), List.length_singleton, Nat.add_sub_cancel_left,
      oq_getD_app_lt (by rw [hlb]; omega),
      oq_getD_flatten_uniform _ 6 (fun _ => rfl) _ _ _ ht hc]
  have htail : ∀ c < 20, σ (.n (K6 + 6 * cd - 5 + c)) =
      (oqCapTailVals rd dbp (σ (.n 6)) (σ (.n 7)) (σ (.n 0)) (σ (.n 1)) pd cd).getD c 0 := by
    intro c hc
    rw [show K6 + 6 * cd - 5 + c = K6 + (1 + 6 * (cd - 1) + c) by omega, hv _ (by omega), oqCapVals,
      oq_getD_app_ge (by simp [hlb]; omega), List.length_append, List.length_singleton, hlb]
    congr 1; omega
  have hpar : ∀ t ≤ cd - 1, σ (.n (K6 + 6 * t)) = capPar rd dbp pd cd t := by
    intro t ht
    rcases t with _ | t
    · have := hv 0 (by omega)
      simp only [oqCapVals, List.singleton_append, Nat.add_zero] at this
      rw [Nat.mul_zero, Nat.add_zero, this, capPar]; simp
    · have := hbit t (by omega) 5 (by omega)
      rw [show K6 + 1 + 6 * t + 5 = K6 + 6 * (t + 1) by ring] at this
      rw [this]; rfl
  rw [oqCapT, holdsList_append, holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, show P + 79 + 13 * pd = K6 from rfl]
  refine ⟨?_, ?_⟩
  · have := hpar 0 (by omega)
    rw [Nat.mul_zero, Nat.add_zero] at this
    rw [this, kw_gpowK (Nat.pow_lt_pow_right (by decide) (show cd - 1 < 128 by omega)), capPar]; simp
  rw [holdsList_range_flatten _ _ (fun _ => rfl)]
  refine ⟨fun t ht => ?_, ?_⟩
  · have e := fun c (hc : c < 6) => hbit t ht c hc
    have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
    have e3 := e 3 (by omega); have e4 := e 4 (by omega); have e5 := e 5 (by omega)
    simp only [oqCapBitVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4 e5
    simp only [oqCapBit, capBitT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one]
    have hc : kw (1 + gpowK (2 ^ t)) = 1 + gen ^ 2 ^ t :=
      kw_one_add_gpowK (Nat.pow_lt_pow_right (by decide) (show t < 128 by omega))
    have hb := hbits (t + 1) (by omega)
    rw [show pd + (t + 1) = pd + 1 + t by ring] at hb
    rw [show P + 80 + 13 * pd + 6 * t = K6 + 1 + 6 * t by ring]
    refine ⟨e0, by rw [e1]; exact hb, by rw [e2, hc], by rw [e3, e1, e2], by rw [e4, e0, e3], ?_⟩
    rw [e5, show P + 79 + 13 * pd + 6 * t = K6 + 6 * t by ring, hpar t (by omega), e4, capPar, capPar,
      Finset.prod_range_succ, mul_assoc]
  · have e := htail
    have g0 := e 0 (by omega); have g1 := e 1 (by omega); have g2 := e 2 (by omega)
    have g3 := e 3 (by omega); have g4 := e 4 (by omega); have g5 := e 5 (by omega)
    have g6 := e 6 (by omega); have g7 := e 7 (by omega); have g8 := e 8 (by omega)
    have g9 := e 9 (by omega); have g10 := e 10 (by omega); have g11 := e 11 (by omega)
    have g12 := e 12 (by omega); have g13 := e 13 (by omega); have g14 := e 14 (by omega)
    have g15 := e 15 (by omega); have g16 := e 16 (by omega); have g17 := e 17 (by omega)
    have g18 := e 18 (by omega); have g19 := e 19 (by omega)
    simp only [oqCapTailVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
      at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
    have hK7 : K6 + 6 * cd - 5 - 1 = K6 + 6 * (cd - 1) := by omega
    have hP' := hpar (cd - 1) le_rfl
    simp only [List.map_cons, List.map_nil, word_eOfNat, eOfNat_one, eOfNat_two]
    rw [hK7, hP']
    have hb0 := hbits 0 (by omega)
    rw [Nat.add_zero] at hb0
    refine ⟨g0, by rw [g1], by rw [g1, g0]; exact hflag, by rw [g2], g3, by rw [g4]; exact hb0, g5,
      by rw [g6, g4, g5], by rw [g7, g3, g6], by rw [g8, g2, g7]; rfl, by rw [g9, g8], by rw [g10, g9],
      by rw [g10]; exact htop0, g11, by rw [g12, g11, g8], by rw [g13, g12, g8], by rw [g14, g13],
      by rw [g14]; exact htop1, g15, by rw [g16, g15], by rw [g17, g16], g18, by rw [g19, g18],
      by rw [g17]; exact hK, fun h => ?_, hret⟩
    rw [g19]
    exact hcall (by rwa [g17] at h)

end
end LeanVM.Guest.B1
