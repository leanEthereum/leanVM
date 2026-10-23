/-
  LeanVM.Guest.B1.Tables.Common

  Shared lemmas of the bus and table phase's B1 files: range checks on a memory image, sums of
  g-powers, and the offsets `stackOffsets` lays out.
-/

module

public import LeanVM.Guest.B1.Tables.ColumnSelector

/-!
# Range checks, exponents and stack offsets

* `rc_sound`, `rc_complete`, `RcAux`: `assert log(x) < K` on a memory image of `2^μ` words,
  `μ ≤ 32`, `K ≤ 2^μ` (`rangeCheck_iff`), with a choice of the gadget's auxiliary words for an
  honest valuation.
* `gen_pow_mul_inj`: products of small g-powers are g-powers of the sums.
* `stackFold_*`: the fold of `stackOffsets` (V:877) over an order without repeats sets each
  index to the sum of the sizes before it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Range checks -/

/-- `g^91`, the constant of `assert log(x) < 92`, as the data writes it. -/
theorem word_g91 : word 3623878656 0 0 = ofK (Parameters.gpow 91) := by
  rw [word_eOfNat]
  show ofK (K.ofBits 3623878656) = ofK (Parameters.gpow 91)
  rw [show K.ofBits 3623878656 = Parameters.gpow 91 by decide +kernel]

theorem word_g33 : word 8589934592 0 0 = ofK (Parameters.gpow 33) := word_two_pow_33

/-- **A range check is sound** on a memory image: `x = g^e` with `e < K`. -/
theorem rc_sound {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : K ≤ 2 ^ μ) {x y t1 t2 k : E} (hk : k = ofK (Parameters.gpow (K - 1)))
    (h1 : LoadHolds Lm.read x 0 t1) (h2 : k = x * y) (h3 : LoadHolds Lm.read y 0 t2) :
    ∃ e < K, x = gen ^ e := by
  obtain ⟨e, he, hx⟩ := (rangeCheck_iff hμ Lm x hK1 hK).mp ⟨y, t1, t2, h1, by rw [← h2, hk], h3⟩
  exact ⟨e, he, by rw [hx, gen_pow_eq_ofK]⟩

/-- **A range check is sound** on any memory image of at most `2^32` words, whatever `K ≤ 2^33`:
both reads are below `2^32`, so their exponents' sum `K - 1` is below the order of `g`. -/
theorem rc_sound' {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : K ≤ 2 ^ 33) {x y t1 t2 k : E} (hk : k = ofK (Parameters.gpow (K - 1)))
    (h1 : LoadHolds Lm.read x 0 t1) (h2 : k = x * y) (h3 : LoadHolds Lm.read y 0 t2) :
    ∃ e < K, x = gen ^ e := by
  have hμ64 : μ < 64 := by omega
  have h32 : 2 ^ μ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hμ
  obtain ⟨hx, h1⟩ := h1
  obtain ⟨hy, h3⟩ := h3
  rw [Parameters.gpow, pow_zero, mul_one] at h1 h3
  obtain ⟨i, hi, -⟩ := (read_some_iff hμ64 Lm _ _).mp h1
  obtain ⟨j, hj, -⟩ := (read_some_iff hμ64 Lm _ _).mp h3
  have ex : x = ofK (Parameters.gpow i) := by rw [eq_ofK_limb hx, hi]
  have ey : y = ofK (Parameters.gpow j) := by rw [eq_ofK_limb hy, hj]
  rw [hk, ex, ey, ← ofK_mul, Parameters.gpow, Parameters.gpow, ← pow_add] at h2
  have hij := gpow_injOn (by have := i.isLt; have := j.isLt; simp only [Set.mem_Iio]; omega)
    (by simp only [Set.mem_Iio]; omega) (ofK_injective h2).symm
  exact ⟨i, by omega, by rw [ex, gen_pow_eq_ofK]⟩

/-- The auxiliary words of a passing range check, chosen. -/
noncomputable def rcAux {μ : ℕ} (Lm : MemImage μ) (x : E) (K : ℕ) : E × E × E :=
  open Classical in
  if h : ∃ y t1 t2 : E, LoadHolds Lm.read x 0 t1 ∧ ofK (Parameters.gpow (K - 1)) = x * y ∧
      LoadHolds Lm.read y 0 t2 then
    (Classical.choose h, Classical.choose (Classical.choose_spec h),
      Classical.choose (Classical.choose_spec (Classical.choose_spec h)))
  else (0, 0, 0)

/-- **A range check is complete**: `x = g^e`, `e < K`, passes with the chosen words. -/
theorem rc_complete {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : K ≤ 2 ^ μ) {e : ℕ} (he : e < K) :
    LoadHolds Lm.read (gen ^ e) 0 (rcAux Lm (gen ^ e) K).2.1 ∧
      ofK (Parameters.gpow (K - 1)) = gen ^ e * (rcAux Lm (gen ^ e) K).1 ∧
      LoadHolds Lm.read (rcAux Lm (gen ^ e) K).1 0 (rcAux Lm (gen ^ e) K).2.2 := by
  have h : ∃ y t1 t2 : E, LoadHolds Lm.read (gen ^ e) 0 t1 ∧
      ofK (Parameters.gpow (K - 1)) = gen ^ e * y ∧ LoadHolds Lm.read y 0 t2 :=
    (rangeCheck_iff hμ Lm (gen ^ e) hK1 hK).mpr ⟨e, he, gen_pow_eq_ofK e⟩
  simp only [rcAux, h, ↓reduceDIte]
  exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))

/-- A run of mapped words, entry by entry. -/
theorem readsAt_map_iff {rd : Reader} {p : E} {l : List ℕ} {f : ℕ → E} :
    ReadsAt rd p (l.map f) ↔ ∀ c < l.length, LoadHolds rd p c (f (l.getD c 0)) := by
  unfold ReadsAt
  constructor
  · intro h c hc
    have := h c (by simpa using hc)
    rwa [List.getElem_map, ← List.getD_eq_getElem l 0 hc] at this
  · intro h c hc
    have hc' : c < l.length := by simpa using hc
    rw [List.getElem_map, ← List.getD_eq_getElem l 0 hc']
    exact h c hc'

/-! ## Exponents -/

theorem gen_pow_inj' {a b : ℕ} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (h : gen ^ a = gen ^ b) :
    a = b := gen_pow_inj (by omega) (by omega) h

/-- `g^a = g^d · g^b` with all three small: `a = d + b`. -/
theorem gen_pow_eq_mul {a b d : ℕ} (ha : a < 2 ^ 62) (hb : b < 2 ^ 62) (hd : d < 2 ^ 62)
    (h : gen ^ a = gen ^ d * gen ^ b) : a = d + b := by
  rw [← pow_add] at h; exact gen_pow_inj' (by omega) (by omega) h

/-! ## Stack offsets -/

/-- The fold of `stackOffsets` (V:877-884). -/
def stackStep (size : ℕ → ℕ) (acc : List ℕ × ℕ) (i : ℕ) : List ℕ × ℕ :=
  (acc.1.set i acc.2, acc.2 + 2 ^ size i)

/-- The sum of the sizes of the first `r` entries of `ord`. -/
def prefixSize (size : ℕ → ℕ) (ord : List ℕ) (r : ℕ) : ℕ :=
  ((ord.take r).map fun i => 2 ^ size i).sum

theorem stackFold_take (size : ℕ → ℕ) (n : ℕ) (ord : List ℕ) (hnd : ord.Nodup)
    (hlt : ∀ i ∈ ord, i < n) :
    ∀ m ≤ ord.length,
      ((ord.take m).foldl (stackStep size) (List.replicate n 0, 0)).2 = prefixSize size ord m ∧
      ((ord.take m).foldl (stackStep size) (List.replicate n 0, 0)).1.length = n ∧
      ∀ r < m, ((ord.take m).foldl (stackStep size) (List.replicate n 0, 0)).1.getD
        (ord.getD r 0) 0 = prefixSize size ord r := by
  intro m hm
  induction m with
  | zero => simp [prefixSize]
  | succ m ih =>
    obtain ⟨h2, hl, h1⟩ := ih (by omega)
    have hmo : m < ord.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hmo, Option.toList_some, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, stackStep]
    refine ⟨?_, ?_, fun r hr => ?_⟩
    · rw [h2, prefixSize, prefixSize, List.take_add_one, List.getElem?_eq_getElem hmo,
        Option.toList_some, List.map_append, List.sum_append]
      simp
    · rw [List.length_set, hl]
    · have hin : ord[m] < n := hlt _ (List.getElem_mem hmo)
      rcases Nat.lt_or_ge r m with hr' | hr'
      · have hne : ord[m] ≠ ord.getD r 0 := by
          rw [List.getD_eq_getElem _ _ (by omega)]
          intro he
          exact absurd ((List.Nodup.getElem_inj_iff hnd).mp he) (by omega)
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
        exact h1 r hr'
      · obtain rfl : r = m := by omega
        rw [List.getD_eq_getElem _ _ hmo, List.getD_eq_getElem?_getD, List.getElem?_set_self
          (by rw [hl]; exact hin), Option.getD_some, h2]

/-- **`stackOffsets`'s offsets** (V:877-884): along its order, entry `order[r]` is the sum of the
sizes before it, and the total is their sum. -/
theorem stackOffsets_fst (sizes : List ℕ) (r : ℕ)
    (hr : r < sizes.length) :
    (stackOffsets sizes).1.getD
        (((List.range sizes.length).mergeSort (stackLe (sizes.getD · 0))).getD r 0) 0 =
      prefixSize (sizes.getD · 0) ((List.range sizes.length).mergeSort (stackLe (sizes.getD · 0)))
        r := by
  set ord := (List.range sizes.length).mergeSort (stackLe (sizes.getD · 0))
  have hperm : ord.Perm (List.range sizes.length) := List.mergeSort_perm _ _
  have hlen : ord.length = sizes.length := by rw [hperm.length_eq, List.length_range]
  have h := stackFold_take (sizes.getD · 0) sizes.length ord (hperm.nodup_iff.mpr List.nodup_range)
    (fun i hi => List.mem_range.mp (hperm.subset hi)) ord.length le_rfl
  rw [List.take_length] at h
  have hst : stackOffsets sizes = ((ord.foldl (stackStep (sizes.getD · 0))
      (List.replicate sizes.length 0, 0)).1, log2Ceil (ord.foldl (stackStep (sizes.getD · 0))
      (List.replicate sizes.length 0, 0)).2) := rfl
  rw [hst]
  exact h.2.2 r (by omega)

theorem stackOffsets_length (sizes : List ℕ) : (stackOffsets sizes).1.length = sizes.length := by
  set ord := (List.range sizes.length).mergeSort (stackLe (sizes.getD · 0))
  have hperm : ord.Perm (List.range sizes.length) := List.mergeSort_perm _ _
  have h := stackFold_take (sizes.getD · 0) sizes.length ord (hperm.nodup_iff.mpr List.nodup_range)
    (fun i hi => List.mem_range.mp (hperm.subset hi)) ord.length le_rfl
  rw [List.take_length] at h
  exact h.2.1

theorem prefixSize_full (size : ℕ → ℕ) (ord : List ℕ) :
    prefixSize size ord ord.length = (ord.map fun i => 2 ^ size i).sum := by
  rw [prefixSize, List.take_length]

theorem prefixSize_succ (size : ℕ → ℕ) (ord : List ℕ) (r : ℕ) (hr : r < ord.length) :
    prefixSize size ord (r + 1) = prefixSize size ord r + 2 ^ size (ord.getD r 0) := by
  rw [prefixSize, prefixSize, List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some,
    List.map_append, List.sum_append, List.getD_eq_getElem _ _ hr]
  simp

end
end LeanVM.Guest.B1
