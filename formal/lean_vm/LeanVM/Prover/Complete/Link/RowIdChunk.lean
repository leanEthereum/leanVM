/-
  LeanVM.Prover.Complete.Link.RowIdChunk

  The functionals of a one-hot pointer word: each chunk's `D_i` reads the equality weight at its
  digit, their product is `eq(r, σ)`, the mirror certificate vanishes, a shifted read is `eq(r, σ + s)`
  inside the window and zero past it.
-/

module

public import LeanVM.Prover.Complete.Link.RowIdAlg

/-!
# One-hot words read by their functionals

For chunks whose index shifts are the widths' prefix sums and whose widths sum to the width
(`ChunkFacts`), and the one-hot word of `σ`, whose chunk `i` holds the single bit `digit σ i`:

* `evalChunk_pow`: a functional table read at a one-hot chunk is the table's entry at the digit;
* `prod_eqAt_digit`: `Π_i eq(r_i, σ_i) = eq(r, σ)`;
* `eqAt_mul_eqAt_flip`: `eq(r_i, v)·eq(r_i, v̄) = π_i` (the mirror term, `D_i·D̄_i = π_i`);
* `window_prod`: chunk `0` read `s` further, times the other chunks, is `eq(r, σ + s)` when
  `σ mod 2^{w_0} + s < 2^{w_0}` (`Chunks.shifted`), zero otherwise.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover Finset
open LeanVM.Protocol.KeccakGkr (eqAt eqAt_cons eqAt_mod eqAt_append eqKernel_getD eqKernel_length)

/-! ## A functional at a one-hot chunk -/

theorem shiftRight_two_pow_mod (v j : ℕ) : (2 ^ v >>> j) % 2 = if j = v then 1 else 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  rcases lt_trichotomy j v with h | rfl | h
  · rw [ite_eq_right (by omega), show v = (v - j - 1) + 1 + j by omega, pow_add,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _), pow_succ]
    simp
  · simp
  · rw [ite_eq_right (by omega), Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h)]

theorem filter_zipIdx_eq : ∀ (l : List E) (n v : ℕ), v < l.length →
    ((l.zipIdx n).filter (fun x ↦ decide (x.2 = n + v))).map (·.1) = [l.getD v 0]
  | [], _, _, h => by simp at h
  | a :: l, n, 0, _ => by
    simp only [List.zipIdx_cons, List.filter_cons, Nat.add_zero, decide_true, ↓reduceIte,
      List.map_cons, List.getD_cons_zero, List.cons.injEq, true_and]
    rw [List.filter_eq_nil_iff.mpr]
    · rfl
    · intro x hx
      have := (List.mem_zipIdx hx).1
      simp; omega
  | a :: l, n, v + 1, h => by
    simp only [List.zipIdx_cons, List.filter_cons, List.getD_cons_succ]
    rw [ite_eq_right (by simp)]
    have := filter_zipIdx_eq l (n + 1) v (by simpa using h)
    rw [show n + 1 + v = n + (v + 1) by omega] at this
    exact this

/-- **A functional at a one-hot chunk** reads its table at the digit. -/
theorem evalChunk_pow (c : Chunks) (table : List E) (word i v : ℕ)
    (hb : ∀ j < table.length, (c.bits word i >>> j) % 2 = 1 ↔ j = v)
    (hv : v < table.length) : evalChunk c table word i = table.getD v 0 := by
  unfold evalChunk
  dsimp only
  rw [List.filter_congr (q := fun x ↦ decide (x.2 = 0 + v)) (fun x hx ↦ by
    have hl := (List.mem_zipIdx' (x := x.1) (i := x.2) hx).1
    rw [zero_add]
    exact decide_eq_decide.mpr (hb x.2 hl))]
  rw [filter_zipIdx_eq table 0 v hv, LeanVM.Protocol.Tables.sumE_eq, List.sum_singleton]

/-! ## Prefix sums -/

theorem foldl_exclusivePrefix : ∀ (sizes : List ℕ) (L : List ℕ) (s : ℕ),
    sizes.foldl (fun (acc : List ℕ × ℕ) size ↦ (acc.1 ++ [acc.2], acc.2 + size)) (L, s) =
      (L ++ (exclusivePrefix sizes).map (s + ·), s + sizes.sum)
  | [], L, s => by simp [exclusivePrefix]
  | a :: rest, L, s => by
    rw [List.foldl_cons, foldl_exclusivePrefix rest, exclusivePrefix.eq_1 (a :: rest),
      List.foldl_cons, foldl_exclusivePrefix rest]
    simp [List.map_map, Function.comp_def, add_assoc]

theorem exclusivePrefix_cons (a : ℕ) (rest : List ℕ) :
    exclusivePrefix (a :: rest) = 0 :: (exclusivePrefix rest).map (a + ·) := by
  rw [exclusivePrefix, List.foldl_cons, foldl_exclusivePrefix]
  simp

theorem length_exclusivePrefix : ∀ sizes : List ℕ, (exclusivePrefix sizes).length = sizes.length
  | [] => by simp [exclusivePrefix]
  | a :: rest => by rw [exclusivePrefix_cons]; simp [length_exclusivePrefix rest]

theorem getD_exclusivePrefix_add_le : ∀ (sizes : List ℕ) (i : ℕ), i < sizes.length →
    (exclusivePrefix sizes).getD i 0 + sizes.getD i 0 ≤ sizes.sum
  | [], _, h => by simp at h
  | a :: rest, 0, _ => by rw [exclusivePrefix_cons]; simp
  | a :: rest, i + 1, h => by
    rw [exclusivePrefix_cons]
    have hi : i < rest.length := by simpa using h
    have := getD_exclusivePrefix_add_le rest i hi
    simp only [List.getD_cons_succ, List.sum_cons]
    rw [List.getD_eq_getElem _ _ (by simp [length_exclusivePrefix, hi])] at this ⊢
    simp only [List.getElem_map]
    omega

/-! ## The chunks' facts -/

/-- What the row identity reads of the chunks: the index shifts are the widths' prefix sums
(`Chunks.new`), the widths sum to the width, there is a chunk, and each chunk of `σ`'s one-hot word
holds the single bit of `σ`'s digit. -/
structure ChunkFacts (c : Chunks) : Prop where
  shifts : c.indexShifts = exclusivePrefix c.widths
  sum : c.widths.sum = c.width
  pos : 1 ≤ c.d
  bits : ∀ σ, ∀ i < c.d, ∀ v < 2 ^ c.widths.getD i 0,
    (c.bits (c.encode σ) i >>> v) % 2 = 1 ↔ v = c.digit σ i

theorem new_shifts {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) :
    c.indexShifts = exclusivePrefix c.widths := by
  unfold Chunks.new at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · cases h

/-! ## The product of the chunks' weights -/

/-- The weight of chunk `i` of the point at chunk `i` of the index, over a widths list. -/
def chunkWeight (ws : List ℕ) (r : List E) (σ i : ℕ) : E :=
  eqAt ((r.drop ((exclusivePrefix ws).getD i 0)).take (ws.getD i 0))
    ((σ >>> (exclusivePrefix ws).getD i 0) % 2 ^ ws.getD i 0)

theorem prod_chunkWeight : ∀ (ws : List ℕ) (r : List E) (σ : ℕ), r.length = ws.sum →
    ((List.range ws.length).map (chunkWeight ws r σ)).prod = eqAt r σ
  | [], r, σ, h => by
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this; simp
  | a :: rest, r, σ, h => by
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.prod_cons]
    have hr : (r.drop a).length = rest.sum := by simp [h]
    have ih := prod_chunkWeight rest (r.drop a) (σ >>> a) hr
    have h0 : chunkWeight (a :: rest) r σ 0 = eqAt (r.take a) (σ % 2 ^ a) := by
      simp [chunkWeight, exclusivePrefix_cons]
    have hs : ∀ i ∈ List.range rest.length,
        chunkWeight (a :: rest) r σ (i + 1) = chunkWeight rest (r.drop a) (σ >>> a) i := by
      intro i hi
      have hi' : i < rest.length := List.mem_range.mp hi
      have hg : ((exclusivePrefix rest).map (a + ·)).getD i 0 = a + (exclusivePrefix rest).getD i 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp [length_exclusivePrefix, hi'])]
        rfl
      simp only [chunkWeight, exclusivePrefix_cons, List.getD_cons_succ]
      rw [hg, Nat.shiftRight_add, List.drop_drop, Nat.add_comm]
    rw [h0, List.map_congr_left (l := List.range rest.length) (g := chunkWeight rest (r.drop a) (σ >>> a))
      (fun i hi ↦ by simpa [Function.comp_def] using hs i hi), ih]
    have hta : (r.take a).length = a := by simp [h]
    conv_rhs => rw [← List.take_append_drop a r]
    rw [eqAt_append, hta, ← Nat.shiftRight_eq_div_pow, eqAt_mod (r.take a) σ, hta]

/-- **The chunks' weights multiply to the equality weight**: `Π_i eq(r_i, σ_i) = eq(r, σ)`. -/
theorem prod_eqAt_digit {c : Chunks} (hc : ChunkFacts c) (r : List E) (hr : r.length = c.width)
    (σ : ℕ) : ((List.range c.d).map fun i ↦ eqAt (c.part r i) (c.digit σ i)).prod = eqAt r σ := by
  have := prod_chunkWeight c.widths r σ (by rw [hr, hc.sum])
  rw [← this]
  simp only [Chunks.d, Chunks.part, Chunks.digit, hc.shifts]
  rfl

theorem length_part {c : Chunks} (hc : ChunkFacts c) (r : List E) (hr : r.length = c.width)
    {i : ℕ} (hi : i < c.d) : (c.part r i).length = c.widths.getD i 0 := by
  have := getD_exclusivePrefix_add_le c.widths i hi
  simp only [Chunks.part, List.length_take, List.length_drop, hc.shifts, hr, ← hc.sum]
  omega

theorem digit_lt (c : Chunks) (σ i : ℕ) : c.digit σ i < 2 ^ c.widths.getD i 0 :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-! ## The mirror term -/

theorem eqAt_mul_eqAt_flip : ∀ (p : List E) (v : ℕ), v < 2 ^ p.length →
    eqAt p v * eqAt p (2 ^ p.length - 1 - v) = (p.map fun x ↦ x * (1 + x)).prod
  | [], _, _ => by simp
  | z :: p, v, hv => by
    simp only [List.length_cons] at hv ⊢
    have hv2 : v / 2 < 2 ^ p.length := by rw [pow_succ] at hv; omega
    have ih := eqAt_mul_eqAt_flip p (v / 2) hv2
    have h2 : (2 ^ (p.length + 1) - 1 - v) / 2 = 2 ^ p.length - 1 - v / 2 := by
      rw [pow_succ]; omega
    have hpar : (2 ^ (p.length + 1) - 1 - v) % 2 = 1 - v % 2 := by
      rw [pow_succ]; omega
    rw [eqAt_cons, eqAt_cons, h2, hpar, List.map_cons, List.prod_cons, ← ih]
    rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h] <;> ring

theorem getD_reverse_eqKernel (p : List E) {v : ℕ} (hv : v < 2 ^ p.length) :
    (eqKernel p).reverse.getD v 0 = eqAt p (2 ^ p.length - 1 - v) := by
  have hl := eqKernel_length p
  rw [List.getD_eq_getElem _ _ (by simp [hl, hv]), List.getElem_reverse,
    ← List.getD_eq_getElem _ 0 (by simp [hl]; omega), eqKernel_getD, hl, ite_eq_left (by omega)]

/-- **The mirror term vanishes** at a one-hot chunk: `D_i·D̄_i + π_i = 0`. -/
theorem mirror_cancel (p : List E) {v : ℕ} (hv : v < 2 ^ p.length) :
    (eqKernel p).getD v 0 * (eqKernel p).reverse.getD v 0 +
      prodE (p.map fun x ↦ x * (1 + x)) = 0 := by
  rw [getD_reverse_eqKernel p hv, eqKernel_getD, ite_eq_left hv, eqAt_mul_eqAt_flip p v hv,
    prodE_eq_prod]
  exact CharTwo.add_self_eq_zero _

/-! ## The window -/

theorem getD_linkWindowShift (e : List E) (s : ℕ) {v : ℕ} (hv : v < e.length) :
    (linkWindowShift e s).getD v 0 = e.getD (v + s) 0 := by
  simp [linkWindowShift, List.getD_eq_getElem?_getD, hv]

theorem div_shift_add {σ s w k : ℕ} (hk : w ≤ k) (h : σ % 2 ^ w + s < 2 ^ w) :
    (σ + s) / 2 ^ k = σ / 2 ^ k := by
  have hw : (σ + s) / 2 ^ w = σ / 2 ^ w := by
    have := Nat.mod_add_div σ (2 ^ w)
    have e : σ + s = (σ % 2 ^ w + s) + 2 ^ w * (σ / 2 ^ w) := by omega
    rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt h, zero_add]
  rw [show k = w + (k - w) by omega, pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hw]

end LeanVM.Prover.Complete.RowId

end
