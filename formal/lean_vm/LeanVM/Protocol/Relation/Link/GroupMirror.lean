/-
  LeanVM.Protocol.Relation.Link.GroupMirror

  A pointer word's chunk certificate, as `verify_link`'s functionals compute it from the word's
  bit-slices, is `Mirror.lean`'s `mirrorCert` of the chunk's table.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupCert
public import LeanVM.Protocol.Relation.Link.Rel
import LeanVM.Parameters.Field

/-!
# The functionals' certificate is the mirror certificate

`certAt_eq_mirrorCert`: chunk `i`'s certificate `D_i(r)·D_i(1 + r) + π_i` of a word `w`, read from
its `64` bits by `Functionals::values`, is `mirrorCert` of chunk `i`'s coordinates of `r` and the
chunk's table of bits (`chunkTable`), when the chunk fits the point and the word
(`chunks_geometry`, decided over every width `Chunks.new` accepts). The table at `1 + r` is the one
at `r` reversed (`eqKernel_reverse`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

theorem eqAt_compl : ∀ (p : List E) (v : ℕ), v < 2 ^ p.length →
    eqAt p (2 ^ p.length - 1 - v) = eqAt (p.map (1 + ·)) v
  | [], v, _ => by simp
  | z :: zs, v, hv => by
    simp only [List.length_cons, List.map_cons] at hv ⊢
    rw [eqAt_cons, eqAt_cons]
    have hp : 2 ^ (zs.length + 1) = 2 * 2 ^ zs.length := by rw [pow_succ]; ring
    have h1 : (2 ^ (zs.length + 1) - 1 - v) / 2 = 2 ^ zs.length - 1 - v / 2 := by omega
    rw [h1, eqAt_compl zs (v / 2) (by omega)]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one v with h | h
    · have : (2 ^ (zs.length + 1) - 1 - v) % 2 = 1 := by omega
      simp only [this, h, ↓reduceIte, zero_ne_one]
      rw [CharTwo.sub_eq_add, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    · have : (2 ^ (zs.length + 1) - 1 - v) % 2 = 0 := by omega
      simp only [this, h, ↓reduceIte, zero_ne_one]
      rw [CharTwo.sub_eq_add]

/-- **The table at `1 + r` is the one at `r` reversed.** -/
theorem eqKernel_reverse (p : List E) : (eqKernel p).reverse = eqKernel (p.map (1 + ·)) := by
  refine List.ext_getElem (by simp [eqKernel_length]) fun v h1 h2 ↦ ?_
  simp only [List.length_reverse, eqKernel_length] at h1
  rw [List.getElem_reverse, ← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, eqKernel_getD,
    eqKernel_getD]
  simp only [eqKernel_length, List.length_map, h1, ↓reduceIte]
  simp only [show 2 ^ p.length - 1 - v < 2 ^ p.length by omega, ↓reduceIte]
  rw [← eqAt_compl p v h1]

theorem sumE_zipWith_eq : ∀ (a l : List E), a.length ≤ l.length →
    sumE (List.zipWith (· * ·) a l) = ∑ v ∈ range a.length, a.getD v 0 * l.getD v 0
  | [], _, _ => by simp [sumE]
  | x :: a, [], h => by simp at h
  | x :: a, y :: l, h => by
    simp only [List.length_cons] at h
    rw [List.zipWith_cons_cons, sumE_eq_sum', List.sum_cons, ← sumE_eq_sum', sumE_zipWith_eq a l (by omega),
      List.length_cons, sum_range_succ']
    simp [add_comm]

theorem sumE_zipWith_eqKernel (p l : List E) (h : 2 ^ p.length ≤ l.length) :
    sumE (List.zipWith (· * ·) (eqKernel p) l) = mle p (l.getD · 0) := by
  rw [sumE_zipWith_eq _ _ (by rw [eqKernel_length]; exact h), eqKernel_length, mle]
  refine sum_congr rfl fun v hv ↦ ?_
  rw [eqKernel_getD]
  simp only [mem_range.mp hv, ↓reduceIte]

theorem values_getD_lo (chunks : Chunks) (r : List E) (ms : ℕ) (sl : List E) {i : ℕ} (hi : i < chunks.d) :
    ((Functionals.new chunks r ms).values chunks sl).getD i 0 =
      sumE (List.zipWith (· * ·) (eqKernel (chunks.part r i)) (sl.drop (chunks.wordShifts.getD i 0))) := by
  unfold Functionals.values Functionals.new
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp [List.getElem_append_left, hi]

theorem values_getD_hi (chunks : Chunks) (r : List E) (ms : ℕ) (sl : List E) {i : ℕ} (hi : i < chunks.d) :
    ((Functionals.new chunks r ms).values chunks sl).getD (chunks.d + i) 0 =
      sumE (List.zipWith (· * ·) (eqKernel (chunks.part r i)).reverse
        (sl.drop (chunks.wordShifts.getD i 0))) := by
  unfold Functionals.values Functionals.new
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp [List.getElem_append_left, List.getElem_append_right, hi]

theorem mirrors_getD (chunks : Chunks) (r : List E) (ms : ℕ) {i : ℕ} (hi : i < chunks.d) :
    (Functionals.new chunks r ms).mirrors.getD i 0 = mirror (chunks.part r i) := by
  unfold Functionals.new mirror
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp [prodE_eq_prod]

/-- **A chunk's certificate from the word's bits** is the mirror certificate of the chunk's table. -/
theorem certAt_eq_mirrorCert (layout : Layout) (chunks : Chunks) (r : List E) (w : K) {i : ℕ}
    (hi : i < chunks.d) (hlen : (chunks.part r i).length = chunks.widths.getD i 0)
    (hfit : chunks.wordShifts.getD i 0 + 2 ^ chunks.widths.getD i 0 ≤ kBits) :
    certAt layout chunks r w i = mirrorCert (chunks.part r i) (chunkTable chunks w i) := by
  have hslice : ∀ (p : List E), p.length = chunks.widths.getD i 0 →
      sumE (List.zipWith (· * ·) (eqKernel p) (((List.range kBits).map (bitOf w)).drop
        (chunks.wordShifts.getD i 0))) = chunkEval p (chunkTable chunks w i) := by
    intro p hp
    rw [sumE_zipWith_eqKernel _ _ (by rw [List.length_drop, List.length_map, List.length_range, hp]; omega),
      chunkEval_eq_mle]
    unfold mle
    refine sum_congr rfl fun v hv ↦ ?_
    have hv' := mem_range.mp hv
    rw [hp] at hv'
    congr 1
    have hlt : v < (((List.range kBits).map (bitOf w)).drop (chunks.wordShifts.getD i 0)).length := by
      rw [List.length_drop, List.length_map, List.length_range]; omega
    show (((List.range kBits).map (bitOf w)).drop (chunks.wordShifts.getD i 0)).getD v 0 = _
    rw [List.getD_eq_getElem _ _ hlt, List.getElem_drop, List.getElem_map, List.getElem_range]
    rfl
  unfold certAt mirrorCert
  simp only
  rw [values_getD_lo _ _ _ _ hi, values_getD_hi _ _ _ _ hi, mirrors_getD _ _ _ hi, eqKernel_reverse,
    hslice _ hlen, hslice _ (by rw [List.length_map, hlen])]
  rfl

/-- **Every chunk fits the point and the word**, for every width `Chunks.new` accepts. -/
theorem chunks_geometry {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) : ∀ i < c.d,
    c.indexShifts.getD i 0 + c.widths.getD i 0 ≤ c.width ∧ c.wordShifts.getD i 0 + 2 ^ c.widths.getD i 0 ≤ kBits := by
  have key : ∀ w < 25, ∀ c, Chunks.new w = some c → ∀ i < c.d,
      c.indexShifts.getD i 0 + c.widths.getD i 0 ≤ c.width ∧
        c.wordShifts.getD i 0 + 2 ^ c.widths.getD i 0 ≤ kBits := by decide +kernel
  by_cases hw : w < 25
  · exact key w hw c h
  · unfold Chunks.new at h
    split_ifs at h with hc
    · exact absurd hc.2 (by simp [maxPointerWidth]; omega)

theorem part_length (chunks : Chunks) (r : List E) {i : ℕ}
    (h : chunks.indexShifts.getD i 0 + chunks.widths.getD i 0 ≤ r.length) :
    (chunks.part r i).length = chunks.widths.getD i 0 := by
  simp only [Chunks.part, List.length_take, List.length_drop]; omega

/-- **A table that is not one-hot has a point where its certificate is nonzero**, placed in chunk `i`'s
coordinates of an index point. -/
theorem exists_part_mirrorCert_ne (chunks : Chunks) {W i : ℕ}
    (hgeo : chunks.indexShifts.getD i 0 + chunks.widths.getD i 0 ≤ W) (hw : chunks.widths.getD i 0 < 2 ^ 126)
    {e : ℕ → E} (hbad : ¬ ∃ σ < 2 ^ chunks.widths.getD i 0, OneHot (chunks.widths.getD i 0) e σ) :
    ∃ r : List E, r.length = W ∧ mirrorCert (chunks.part r i) e ≠ 0 := by
  set w := chunks.widths.getD i 0
  set s := chunks.indexShifts.getD i 0
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin w → E, mirrorCert (List.ofFn ρ) e ≠ 0 := by
    by_contra hc
    push Not at hc
    have h := card_mirrorCert_eq_zero_le hbad
    rw [filter_true_of_mem fun ρ _ ↦ hc ρ, card_univ, Fintype.card_fun, Fintype.card_fin,
      Protocol.card_E] at h
    rcases Nat.eq_zero_or_pos w with h0 | hpos
    · rw [h0] at h; simp at h
    · have h1 : (2 ^ 128) ^ w = 2 ^ 128 * (2 ^ 128) ^ (w - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hpos]
      rw [h1] at h
      have h2 := Nat.le_of_mul_le_mul_right h (pow_pos (by norm_num) _)
      omega
  refine ⟨List.ofFn fun j : Fin W ↦ if hj : s ≤ j.val ∧ j.val < s + w then ρ ⟨j.val - s, by omega⟩ else 0,
    by simp, ?_⟩
  convert hρ using 2
  refine List.ext_getElem (by simp only [Chunks.part, List.length_take, List.length_drop, List.length_ofFn]; omega)
    fun j h1 h2 ↦ ?_
  simp only [Chunks.part, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
  simp only [List.length_ofFn] at h2
  split_ifs with hj
  · congr 1
    ext
    simp only [s]
    omega
  · exact absurd ⟨by omega, by omega⟩ hj

end

end LeanVM.Protocol.Relation
