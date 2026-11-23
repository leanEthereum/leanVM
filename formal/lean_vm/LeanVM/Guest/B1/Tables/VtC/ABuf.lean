/-
  LeanVM.Guest.B1.Tables.VtC.ABuf

  Buffers of fixed-stride blocks, and the shared selector tables' honest words.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SAll

/-!
# Strided buffers

`padTo S l`: `l` padded with zeros to `S` words. `tbReadsAt_chunks`: a buffer holding the blocks
`blk i` each padded to `S` words holds block `i` at `S·i`.

`vtShEqW`, `vtShGW`: the shared selector tables' buffers (`shared_eq`, `shared_g`): table `t`'s
nibble `j` at block `9t + j`, its eq levels (stride `32`) and `g`-power table (stride `16`) of the
run of `|point| − τ_t` coordinates above `τ_t`. `vt_runTables`: they give `RunTables`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `l` padded with zeros to `S` words. -/
def padTo (S : ℕ) (l : List E) : List E := l ++ List.replicate (S - l.length) 0

theorem padTo_length {S : ℕ} {l : List E} (h : l.length ≤ S) : (padTo S l).length = S := by
  simp [padTo]; omega

theorem getD_flatMap_const {S : ℕ} (f : ℕ → List E) (hf : ∀ i, (f i).length = S) :
    ∀ (m i k : ℕ), i < m → k < S →
      ((List.range m).flatMap f).getD (S * i + k) 0 = (f i).getD k 0
  | 0, _, _, hi, _ => absurd hi (by omega)
  | m + 1, i, k, hi, hk => by
    rw [List.range_succ, List.flatMap_append]
    have hlen : ((List.range m).flatMap f).length = S * m := by
      rw [List.length_flatMap]
      simp [hf, List.sum_replicate, Nat.mul_comm]
    rcases Nat.lt_or_ge i m with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact getD_flatMap_const f hf m i k h hk
    · obtain rfl : i = m := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
      simp

/-- **A buffer of padded blocks holds each block at its stride.** -/
theorem tbReadsAt_chunks {rd : Reader} {p : E} {S m : ℕ} (blk : ℕ → List E)
    (hb : ∀ i, (blk i).length ≤ S) (h : TbReadsAt rd p ((List.range m).flatMap fun i ↦ padTo S (blk i)))
    {i : ℕ} (hi : i < m) : TbReadsAt rd (p * gen ^ (S * i)) (blk i) := by
  intro k hk
  rw [tb_loadHolds_mul_gen_pow]
  have hS : k < S := lt_of_lt_of_le hk (hb i)
  have hlen : ((List.range m).flatMap fun i ↦ padTo S (blk i)).length = S * m := by
    rw [List.length_flatMap]
    simp [padTo_length (hb _), List.sum_replicate, Nat.mul_comm]
  have hidx : S * i + k < S * m := by nlinarith
  have := h (S * i + k) (by rw [hlen]; exact hidx)
  rw [← List.getD_eq_getElem _ 0,
    getD_flatMap_const (fun i ↦ padTo S (blk i)) (fun i ↦ padTo_length (hb i)) m i k hi hS] at this
  rwa [padTo, List.getD_append _ _ _ _ hk, List.getD_eq_getElem _ _ hk] at this

/-- **A buffer of padded blocks holds zeros past each block, to its stride.** -/
theorem tbReadsAt_chunks_pad {rd : Reader} {p : E} {S m : ℕ} (blk : ℕ → List E)
    (hb : ∀ i, (blk i).length ≤ S) (h : TbReadsAt rd p ((List.range m).flatMap fun i ↦ padTo S (blk i)))
    {i : ℕ} (hi : i < m) {e : ℕ} (he1 : (blk i).length ≤ e) (he2 : e < S) :
    LoadHolds rd (p * gen ^ (S * i)) e 0 := by
  rw [tb_loadHolds_mul_gen_pow]
  have hlen : ((List.range m).flatMap fun i ↦ padTo S (blk i)).length = S * m := by
    rw [List.length_flatMap]
    simp [padTo_length (hb _), List.sum_replicate, Nat.mul_comm]
  have hidx : S * i + e < S * m := by nlinarith
  have := h (S * i + e) (by rw [hlen]; exact hidx)
  rw [← List.getD_eq_getElem _ 0,
    getD_flatMap_const (fun i ↦ padTo S (blk i)) (fun i ↦ padTo_length (hb i)) m i e hi he2] at this
  have h0 : (List.replicate (S - (blk i).length) (0 : E)).getD (e - (blk i).length) 0 = 0 := by simp
  rwa [padTo, List.getD_append_right _ _ _ _ he1, h0] at this

/-! ## The shared selector tables -/

/-- Table `t`'s run of coordinates above `τ_t`, their complements and shares. -/
def shZs (point : List E) (τ : ℕ) : List E := point.drop τ
def shZs1 (point : List E) (τ : ℕ) : List E := (point.map (1 + ·)).drop τ
def shGs (point : List E) (τ : ℕ) : List E := (gSquaresList.drop τ).take (point.length - τ)

/-- Block `9t + j` of the eq buffer. -/
def shEqBlk (point : List E) (τ : ℕ → ℕ) (i : ℕ) : List E :=
  if i % 9 < (point.length - τ (i / 9) + 3) / 4 then
    eqLevels (nib (shZs point (τ (i / 9))) (i % 9)) (nib (shZs1 point (τ (i / 9))) (i % 9))
  else []

/-- Block `9t + j` of the `g` buffer. -/
def shGBlk (point : List E) (τ : ℕ → ℕ) (i : ℕ) : List E :=
  if i % 9 < (point.length - τ (i / 9) + 3) / 4 then gTable (nib (shGs point (τ (i / 9))) (i % 9))
  else []

/-- `shared_eq`'s honest words. -/
def vtShEqW (point : List E) (τ : ℕ → ℕ) : List E :=
  (List.range 54).flatMap fun i ↦ padTo 32 (shEqBlk point τ i)

/-- `shared_g`'s honest words. -/
def vtShGW (point : List E) (τ : ℕ → ℕ) : List E :=
  (List.range 54).flatMap fun i ↦ padTo 16 (shGBlk point τ i)

theorem nib_length_le (l : List E) (j : ℕ) : (nib l j).length ≤ 4 := by
  simp [nib]

theorem shEqBlk_length (point : List E) (τ : ℕ → ℕ) (i : ℕ) : (shEqBlk point τ i).length ≤ 32 := by
  unfold shEqBlk
  split_ifs
  · have h1 := nib_length_le (shZs point (τ (i / 9))) (i % 9)
    have h2 : (nib (shZs1 point (τ (i / 9))) (i % 9)).length =
        (nib (shZs point (τ (i / 9))) (i % 9)).length := by
      simp [nib, shZs, shZs1]
    rw [eqLevels_length rfl h2]
    have : 2 ^ ((nib (shZs point (τ (i / 9))) (i % 9)).length + 1) ≤ 2 ^ 5 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · simp

theorem shGBlk_length (point : List E) (τ : ℕ → ℕ) (i : ℕ) : (shGBlk point τ i).length ≤ 16 := by
  unfold shGBlk
  split_ifs
  · rw [gTable_length rfl]
    have := nib_length_le (shGs point (τ (i / 9))) (i % 9)
    have : 2 ^ (nib (shGs point (τ (i / 9))) (i % 9)).length ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by norm_num) this
    omega
  · simp

theorem vtShEqW_length (point : List E) (τ : ℕ → ℕ) : (vtShEqW point τ).length = 1728 := by
  rw [vtShEqW, List.length_flatMap]
  simp [padTo_length (shEqBlk_length _ _ _)]

theorem vtShGW_length (point : List E) (τ : ℕ → ℕ) : (vtShGW point τ).length = 864 := by
  rw [vtShGW, List.length_flatMap]
  simp [padTo_length (shGBlk_length _ _ _)]

/-- **The shared tables' buffers give `RunTables`.** -/
theorem vt_runTables {rd : Reader} {pe pg : E} {point : List E} {τ : ℕ → ℕ}
    (hμ : point.length < 33) (he : TbReadsAt rd pe (vtShEqW point τ))
    (hg : TbReadsAt rd pg (vtShGW point τ)) {t : ℕ} (ht : t < 6) :
    RunTables rd (pe * gen ^ (288 * t)) (pg * gen ^ (144 * t)) (point.length - τ t)
      (point.drop (τ t)) ((point.map (1 + ·)).drop (τ t))
      ((gSquaresList.drop (τ t)).take (point.length - τ t)) := by
  intro j hj
  have hj9 : j < 9 := by omega
  have hi : 9 * t + j < 54 := by omega
  have hdiv : (9 * t + j) / 9 = t := by omega
  have hmod : (9 * t + j) % 9 = j := by omega
  constructor
  · have := tbReadsAt_chunks (shEqBlk point τ) (shEqBlk_length point τ) he hi
    rw [shEqBlk, hdiv, hmod] at this
    simp only [hj, ↓reduceIte] at this
    rwa [show 32 * (9 * t + j) = 288 * t + 32 * j by ring, pow_add, ← mul_assoc] at this
  · have := tbReadsAt_chunks (shGBlk point τ) (shGBlk_length point τ) hg hi
    rw [shGBlk, hdiv, hmod] at this
    simp only [hj, ↓reduceIte] at this
    rwa [show 16 * (9 * t + j) = 144 * t + 16 * j by ring, pow_add, ← mul_assoc] at this

/-- **The shared tables' buffers give `RunPads`**: past each nibble's tables, zeros. -/
theorem vt_runPads {rd : Reader} {pe pg : E} {point : List E} {τ : ℕ → ℕ}
    (hμ : point.length < 33) (he : TbReadsAt rd pe (vtShEqW point τ))
    (hg : TbReadsAt rd pg (vtShGW point τ)) {t : ℕ} (ht : t < 6) :
    RunPads rd (pe * gen ^ (288 * t)) (pg * gen ^ (144 * t)) (point.length - τ t)
      (point.drop (τ t)) := by
  intro j hj
  have hj9 : j < 9 := by omega
  have hi : 9 * t + j < 54 := by omega
  have hdiv : (9 * t + j) / 9 = t := by omega
  have hmod : (9 * t + j) % 9 = j := by omega
  have hw := nib_length_le (point.drop (τ t)) j
  constructor
  · intro e he1 he2
    have hl : (shEqBlk point τ (9 * t + j)).length ≤ e := by
      rw [shEqBlk, hdiv, hmod]
      simp only [hj, ↓reduceIte]
      rw [eqLevels_length rfl (by simp [nib, shZs, shZs1])]
      exact he1
    have := tbReadsAt_chunks_pad (shEqBlk point τ) (shEqBlk_length point τ) he hi hl (by omega)
    rwa [show 32 * (9 * t + j) = 288 * t + 32 * j by ring, pow_add, ← mul_assoc] at this
  · intro u hu1 hu2
    have hsql : gSquaresList.length = 34 := by simp [gSquaresList]
    have hgl : (nib (shGs point (τ t)) j).length = (nib (point.drop (τ t)) j).length := by
      simp [nib, shGs, hsql]; omega
    have hl : (shGBlk point τ (9 * t + j)).length ≤ u := by
      rw [shGBlk, hdiv, hmod]
      simp only [hj, ↓reduceIte]
      rw [gTable_length rfl, hgl]
      exact hu1
    have := tbReadsAt_chunks_pad (shGBlk point τ) (shGBlk_length point τ) hg hi hl (by omega)
    rwa [show 16 * (9 * t + j) = 144 * t + 16 * j by ring, pow_add, ← mul_assoc] at this

end
end LeanVM.Guest.B1.Tables
