/-
  LeanVM.Prover.Complete.Link.OneHot

  One-hot pointer words: their decoding, and the arrays the link scatters at them.
-/

module

public import LeanVM.Prover.Complete.Keccak.Witness
public import LeanVM.Facts.Hotwire
public import Statement.Prover.LinkIndex
public import LeanVM.Prover.Complete.Link.IndexTabs

/-!
# One-hot words

`Chunks.new` splits a pointer of `width` bits into `d` chunks (`Statement/Verifier/Link.lean`).
`ChunksOK c` collects what every chunks of a width up to `maxPointerWidth` satisfy (`chunksOK_new`,
decided): the index blocks tile `[0, width)` and the word blocks of `2^{w_i}` bits sit end to end
within 64 bits. Then:

* `testBit_encode`: the one-hot word `Chunks.encode σ` has bit `WS_i + v` (`v < 2^{w_i}`) set
  exactly when `v` is `σ`'s digit `i`; `encode_lt`: it fits a word;
* `indices_encode`: it decodes back to `[σ]` for `σ < 2^width`;
* `getD_scatterWords`, `sum_mul_scatterWords`: `scatterWords` of rows whose words are one-hot
  (`OneHotWords`) adds row `u`'s weight at `σ_u + shift` inside its window, so a sum against the
  array is a sum over the rows; `mleA_scatterWords`: the multilinear extension of such an array.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Prover Finset
open LeanVM.Protocol.Hotwire (eqAt)

/-! ## The chunks -/

/-- Chunk `i`'s bits. -/
abbrev _root_.LeanVM.Protocol.Verifier.Chunks.w (c : Chunks) (i : ℕ) : ℕ := c.widths.getD i 0
/-- Chunk `i`'s first index bit. -/
abbrev _root_.LeanVM.Protocol.Verifier.Chunks.is (c : Chunks) (i : ℕ) : ℕ := c.indexShifts.getD i 0
/-- Chunk `i`'s first word bit. -/
abbrev _root_.LeanVM.Protocol.Verifier.Chunks.ws (c : Chunks) (i : ℕ) : ℕ := c.wordShifts.getD i 0

/-- **What `Chunks.new` gives**: at least one chunk; the index blocks `[is_i, is_i + w_i)` tile
`[0, width)`; the word blocks `[ws_i, ws_i + 2^{w_i})` sit end to end from `0` within 64 bits; the
lowest chunk is the window's `min(width, WINDOW_BITS)` bits. -/
def ChunksOK (c : Chunks) : Prop :=
  1 ≤ c.d ∧ c.is 0 = 0 ∧ c.ws 0 = 0 ∧
    (∀ i < c.d - 1, c.is (i + 1) = c.is i + c.w i ∧ c.ws (i + 1) = c.ws i + 2 ^ c.w i) ∧
    c.is (c.d - 1) + c.w (c.d - 1) = c.width ∧ c.ws (c.d - 1) + 2 ^ c.w (c.d - 1) ≤ 64 ∧
    c.w 0 = min c.width windowBits

instance (c : Chunks) : Decidable (ChunksOK c) := by unfold ChunksOK; infer_instance

theorem chunksOK_new_all : ∀ w < maxPointerWidth + 1, ∀ c ∈ Chunks.new w, ChunksOK c ∧ c.width = w := by
  decide +kernel

/-- **`Chunks.new`'s chunks are good.** -/
theorem chunksOK_new {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) : ChunksOK c ∧ c.width = w := by
  have hw : w ≤ maxPointerWidth := by
    unfold Chunks.new at h
    split at h
    · rename_i hw; exact hw.2
    · cases h
  exact chunksOK_new_all w (by omega) c h


/-! ## Sums of increasing powers of two -/

/-- `Σ_{i < n} 2^{p_i}`. -/
def powSum (p : ℕ → ℕ) (n : ℕ) : ℕ := ((List.range n).map fun i ↦ 2 ^ p i).sum

theorem powSum_succ (p : ℕ → ℕ) (n : ℕ) : powSum p (n + 1) = powSum p n + 2 ^ p n := by
  simp [powSum, List.range_succ]

theorem lt_of_succ_lt (p : ℕ → ℕ) {n : ℕ} (h : ∀ i, i + 1 < n → p i < p (i + 1)) :
    ∀ {i j : ℕ}, i < j → j < n → p i < p j
  | i, 0, hij, _ => absurd hij (by omega)
  | i, j + 1, hij, hj => by
    rcases (show i < j ∨ i = j by omega) with hi | rfl
    · exact (lt_of_succ_lt p h hi (by omega)).trans (h j hj)
    · exact h i hj

/-- Increasing positions: the sum is below the next power, and its bits are the positions. -/
theorem powSum_spec (p : ℕ → ℕ) : ∀ n, (∀ i, i + 1 < n → p i < p (i + 1)) →
    (∀ b, powSum p n < 2 ^ b ∨ (0 < n ∧ b ≤ p (n - 1)) ) ∧
      ∀ b, (powSum p n).testBit b = decide (∃ i < n, p i = b)
  | 0, _ => ⟨fun b ↦ Or.inl (by simp [powSum]), fun b ↦ by simp [powSum]⟩
  | n + 1, h => by
    obtain ⟨hlt, hbit⟩ := powSum_spec p n fun i hi ↦ h i (by omega)
    have hbelow : powSum p n < 2 ^ p n := by
      rcases hlt (p n) with h1 | ⟨h0, h1⟩
      · exact h1
      · have := h (n - 1) (by omega)
        rw [Nat.sub_add_cancel h0] at this
        omega
    refine ⟨fun b ↦ ?_, fun b ↦ ?_⟩
    · by_cases hb : b ≤ p n
      · exact Or.inr ⟨by omega, by simpa using hb⟩
      · left
        rw [powSum_succ]
        have : 2 ^ p n + 2 ^ p n ≤ 2 ^ b := by
          rw [← two_mul, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    · rw [powSum_succ, add_comm]
      rcases lt_trichotomy b (p n) with hb | rfl | hb
      · rw [Nat.testBit_two_pow_add_gt hb, hbit]
        refine decide_eq_decide.mpr ⟨fun ⟨i, hi, he⟩ ↦ ⟨i, by omega, he⟩, fun ⟨i, hi, he⟩ ↦ ⟨i, ?_, he⟩⟩
        rcases (show i < n ∨ i = n by omega) with hi | rfl
        · exact hi
        · omega
      · rw [Nat.testBit_two_pow_add_eq, hbit]
        have hn : ¬ ∃ i < n, p i = p n := fun ⟨i, hi, he⟩ ↦ by
          have := Nat.testBit_lt_two_pow hbelow
          rw [hbit] at this
          simp only [decide_eq_false_iff_not] at this
          exact this ⟨i, hi, he⟩
        simp only [hn, decide_false, Bool.not_false]
        exact (decide_eq_true ⟨n, by omega, rfl⟩).symm
      · have hlt2 : 2 ^ p n + powSum p n < 2 ^ b := by
          have : 2 ^ p n + 2 ^ p n ≤ 2 ^ b := by
            rw [← two_mul, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        rw [Nat.testBit_lt_two_pow hlt2]
        refine (decide_eq_false fun ⟨i, hi, he⟩ ↦ ?_).symm
        rcases (show i < n ∨ i = n by omega) with hi | rfl
        · have := lt_of_succ_lt p h hi (by omega)
          omega
        · omega

/-! ## The one-hot word -/

section Encode

variable {c : Chunks} (hc : ChunksOK c)
include hc

/-- Word blocks sit end to end: block `i` ends before block `j > i` starts. -/
theorem ws_le {i j : ℕ} (hij : i < j) (hj : j < c.d) : c.ws i + 2 ^ c.w i ≤ c.ws j := by
  obtain ⟨-, -, -, hstep, -⟩ := hc
  induction j with
  | zero => omega
  | succ j ih =>
    have h1 := (hstep j (by omega)).2
    have h2 : 0 < 2 ^ c.w j := Nat.two_pow_pos _
    rcases (show i < j ∨ i = j by omega) with h | rfl
    · have h3 := ih h (by omega); omega
    · omega

/-- Index blocks tile: block `i` ends where block `i + 1` starts, so `is_j ≥ is_i + w_i`. -/
theorem is_succ {i : ℕ} (hi : i + 1 < c.d) : c.is (i + 1) = c.is i + c.w i :=
  (hc.2.2.2.1 i (by omega)).1

omit hc in
theorem digit_lt (σ i : ℕ) : c.digit σ i < 2 ^ c.w i := Nat.mod_lt _ (Nat.two_pow_pos _)

omit hc in
theorem encode_eq_powSum (σ : ℕ) : c.encode σ = powSum (fun i ↦ c.ws i + c.digit σ i) c.d := rfl

theorem encode_positions (σ : ℕ) :
    ∀ i, i + 1 < c.d → c.ws i + c.digit σ i < c.ws (i + 1) + c.digit σ (i + 1) := by
  intro i hi
  have h1 := ws_le hc (show i < i + 1 by omega) hi
  have h2 := digit_lt (c := c) σ i
  omega

/-- **A one-hot word fits one word.** -/
theorem encode_lt (σ : ℕ) : c.encode σ < 2 ^ 64 := by
  rw [encode_eq_powSum]
  rcases (powSum_spec _ c.d (encode_positions hc σ)).1 64 with h | ⟨h0, h1⟩
  · exact h
  · obtain ⟨-, -, -, -, -, hlast, -⟩ := hc
    have := digit_lt (c := c) σ (c.d - 1)
    omega

/-- **The one-hot word's bits**: in block `i`, the bit `v` is set exactly at `σ`'s digit `i`. -/
theorem testBit_encode (σ : ℕ) {i v : ℕ} (hi : i < c.d) (hv : v < 2 ^ c.w i) :
    (c.encode σ).testBit (c.ws i + v) = decide (v = c.digit σ i) := by
  rw [encode_eq_powSum, (powSum_spec _ c.d (encode_positions hc σ)).2]
  refine decide_eq_decide.mpr ⟨fun ⟨i', hi', he⟩ ↦ ?_, fun h ↦ ⟨i, hi, by rw [h]⟩⟩
  rcases lt_trichotomy i' i with h | rfl | h
  · have := ws_le hc h hi
    have := digit_lt (c := c) σ i'
    omega
  · omega
  · have := ws_le hc h hi'
    omega

omit hc in
theorem shiftRight_mod_two (x v : ℕ) : (x >>> v) % 2 = 1 ↔ x.testBit v = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  simp

/-- Chunk `i`'s indicator bits are set exactly at `σ`'s digit `i`. -/
theorem bits_encode (σ : ℕ) {i v : ℕ} (hi : i < c.d) (hv : v < 2 ^ c.w i) :
    (c.bits (c.encode σ) i >>> v) % 2 = 1 ↔ v = c.digit σ i := by
  rw [shiftRight_mod_two, Chunks.bits, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    testBit_encode hc σ hi hv]
  simp only [hv, decide_true, Bool.true_and, decide_eq_true_eq]

omit hc in
theorem filter_range_eq (n a : ℕ) (ha : a < n) :
    (List.range n).filter (fun v ↦ decide (v = a)) = [a] := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    rcases (show a < n ∨ a = n by omega) with h | rfl
    · rw [ih h]; simp; omega
    · rw [List.filter_eq_nil_iff.mpr (fun v hv ↦ by simp at hv ⊢; omega)]; simp

/-- `σ`'s digits below chunk `k`, each at its index bits. -/
def digitSum (c : Chunks) (σ k : ℕ) : ℕ := ((List.range k).map fun i ↦ c.digit σ i <<< c.is i).sum

theorem foldl_indices (σ : ℕ) : ∀ k ≤ c.d,
    (List.range k).foldl (fun sigmas i ↦
      let bits := c.bits (c.encode σ) i
      sigmas.flatMap fun sigma ↦ ((List.range (2 ^ c.widths.getD i 0)).filter
        fun v ↦ (bits >>> v) % 2 = 1).map fun v ↦ sigma + v <<< c.indexShifts.getD i 0) [0] =
      [digitSum c σ k]
  | 0, _ => by simp [digitSum]
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, foldl_indices σ k (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rw [List.filter_congr (q := fun v ↦ decide (v = c.digit σ k)) fun v hv ↦ by
        rw [decide_eq_decide]; exact bits_encode hc σ (by omega) (List.mem_range.mp hv),
      filter_range_eq _ _ (digit_lt σ k)]
    simp [digitSum, List.range_succ]

/-- The digits below chunk `k + 1` are `σ`'s low bits there. -/
theorem digitSum_succ (σ : ℕ) : ∀ k < c.d, digitSum c σ (k + 1) = σ % 2 ^ (c.is k + c.w k)
  | 0, _ => by
    obtain ⟨-, h0, -⟩ := hc
    have h0' : c.indexShifts.getD 0 0 = 0 := h0
    simp only [digitSum, List.range_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, Chunks.digit, Chunks.is, Chunks.w, h0', Nat.shiftRight_zero, Nat.shiftLeft_zero,
      zero_add]
  | k + 1, hk => by
    rw [digitSum, List.range_succ, List.map_append, List.sum_append, ← digitSum,
      digitSum_succ σ k (by omega), ← is_succ hc hk]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Chunks.digit,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rw [pow_add, Nat.mod_mul]
    ring

/-- **A one-hot word decodes to its index.** -/
theorem indices_encode {σ : ℕ} (hσ : σ < 2 ^ c.width) : c.indices (c.encode σ) = [σ] := by
  have hd := hc.1
  rw [Chunks.indices, foldl_indices hc σ c.d le_rfl,
    show c.d = c.d - 1 + 1 by omega, digitSum_succ hc σ _ (by omega), hc.2.2.2.2.1,
    Nat.mod_eq_of_lt hσ]

end Encode

/-! ## Scattering at one-hot words -/

/-- **One-hot rows**: row `u < rows` of `words` is the one-hot word of `σ u < 2^width`. -/
def OneHotWords (c : Chunks) (words : Array K) (rows : ℕ) (σ : ℕ → ℕ) : Prop :=
  ∀ u < rows, σ u < 2 ^ c.width ∧ words.getD u 0 = K.ofBits (c.encode (σ u))

theorem OneHotWords.mono {c : Chunks} {words : Array K} {rows rows' : ℕ} {σ : ℕ → ℕ}
    (h : OneHotWords c words rows σ) (hr : rows' ≤ rows) : OneHotWords c words rows' σ :=
  fun u hu ↦ h u (by omega)

/-- A one-hot row decodes to its index. -/
theorem indices_word {c : Chunks} (hc : ChunksOK c) {words : Array K} {rows : ℕ} {σ : ℕ → ℕ}
    (h : OneHotWords c words rows σ) {u : ℕ} (hu : u < rows) :
    c.indices (kToNat (words.getD u 0)) = [σ u] := by
  obtain ⟨hσ, hw⟩ := h u hu
  rw [hw, kToNat_ofBits, Nat.mod_eq_of_lt (encode_lt hc _), indices_encode hc hσ]

/-- An index unshifted stays in its window. -/
theorem shifted_zero (c : Chunks) (σ : ℕ) : c.shifted σ 0 = some σ := by
  simp [Chunks.shifted, Nat.mod_lt _ (Nat.two_pow_pos _)]

theorem scatterWords_succ (c : Chunks) (words : Array K) (rows shift : ℕ) (weight : ℕ → E)
    (a : Array E) :
    scatterWords c words (rows + 1) shift weight a =
      let a' := scatterWords c words rows shift weight a
      if weight rows = 0 then a'
      else (c.indices (kToNat (words.getD rows 0))).foldl (fun a j ↦
        match c.shifted j shift with
        | some j => a.modify j (· + weight rows)
        | none => a) a' := by
  rw [scatterWords, Nat.fold_succ]
  rfl

/-- **A scattered array's entry**: what it started with plus the weight of every row whose
one-hot index, shifted, lands there inside its window. -/
theorem getD_scatterWords {c : Chunks} (hc : ChunksOK c) {words : Array K} {σ : ℕ → ℕ}
    (shift : ℕ) (weight : ℕ → E) (a : Array E) {j : ℕ} (hj : j < a.size) :
    ∀ rows, OneHotWords c words rows σ →
      (scatterWords c words rows shift weight a).getD j 0 =
        a.getD j 0 + ∑ u ∈ range rows, if c.shifted (σ u) shift = some j then weight u else 0
  | 0, _ => by simp [scatterWords]
  | n + 1, h => by
    rw [scatterWords_succ, Finset.sum_range_succ, ← add_assoc,
      ← getD_scatterWords hc shift weight a hj n (h.mono (by omega))]
    have hs := Complete.size_scatterWords c words n shift weight a
    generalize scatterWords c words n shift weight a = a' at hs ⊢
    dsimp only
    by_cases hw : weight n = 0
    · simp [hw]
    · rw [ite_eq_right hw, indices_word hc h (Nat.lt_succ_self n), List.foldl_cons, List.foldl_nil]
      rcases hsh : c.shifted (σ n) shift with _ | j'
      · simp
      · dsimp only
        by_cases hjj : j' = j
        · subst hjj
          rw [Keccak.getD_modify_self, ite_eq_left (show j' < a'.size by omega)]
          simp
        · rw [Keccak.getD_modify_of_ne _ hjj]
          simp [hjj]

/-- Where a row's weight lands, summed against `f` over `N` entries: `f` at its shifted index when
that is inside the window and below `N`, else nothing. -/
def landAt (f : ℕ → E) (N : ℕ) (o : Option ℕ) (w : E) : E :=
  match o with
  | some j => if j < N then f j * w else 0
  | none => 0

theorem sum_ite_some (f : ℕ → E) (N : ℕ) (o : Option ℕ) (w : E) :
    ∑ j ∈ range N, f j * (if o = some j then w else 0) = landAt f N o w := by
  rcases o with _ | j0
  · simp [landAt]
  · simp only [Option.some.injEq, mul_ite, mul_zero, landAt]
    rw [Finset.sum_ite_eq]
    simp

/-- **A sum against a scattered array is a sum over the rows.** -/
theorem sum_mul_scatterWords {c : Chunks} (hc : ChunksOK c) {words : Array K} {rows : ℕ}
    {σ : ℕ → ℕ} (h : OneHotWords c words rows σ) (shift : ℕ) (weight : ℕ → E) (a : Array E)
    (f : ℕ → E) :
    ∑ j ∈ range a.size, f j * (scatterWords c words rows shift weight a).getD j 0 =
      ∑ j ∈ range a.size, f j * a.getD j 0 +
        ∑ u ∈ range rows, landAt f a.size (c.shifted (σ u) shift) (weight u) := by
  rw [Finset.sum_congr rfl fun j hj ↦ by
    rw [getD_scatterWords hc shift weight a (Finset.mem_range.mp hj) rows h]]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun u _ ↦ sum_ite_some f a.size _ _

/-- The same, unshifted, from zeros of `2^width` entries. -/
theorem sum_mul_scatterWords_zero {c : Chunks} (hc : ChunksOK c) {words : Array K} {rows : ℕ}
    {σ : ℕ → ℕ} (h : OneHotWords c words rows σ) (weight : ℕ → E) (a : Array E)
    (ha : a.size = 2 ^ c.width) (f : ℕ → E) :
    ∑ j ∈ range a.size, f j * (scatterWords c words rows 0 weight a).getD j 0 =
      ∑ j ∈ range a.size, f j * a.getD j 0 + ∑ u ∈ range rows, f (σ u) * weight u := by
  rw [sum_mul_scatterWords hc h]
  congr 1
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [shifted_zero, landAt, ite_eq_left (by rw [ha]; exact (h u (Finset.mem_range.mp hu)).1)]

/-- **The extension of an array** of `2^|pt|` entries, as an `eq`-weighted sum. -/
theorem mleA_eq_sum (t : Array E) (pt : List E) (ht : t.size = 2 ^ pt.length) :
    mleA t pt = ∑ j ∈ range (2 ^ pt.length), eqAt pt j * t.getD j 0 := by
  rw [Keccak.mleA_eq, LeanVM.Protocol.Hotwire.multilinearEval_eq_mle _ _ (by simp [ht])]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Keccak.getD_toList]

/-- **The extension of a scattered array**: a sum over the rows of `eq(pt, σ_u + shift)`, inside
the window. -/
theorem mleA_scatterWords {c : Chunks} (hc : ChunksOK c) {words : Array K} {rows : ℕ}
    {σ : ℕ → ℕ} (h : OneHotWords c words rows σ) (shift : ℕ) (weight : ℕ → E) (a : Array E)
    (pt : List E) (ha : a.size = 2 ^ pt.length) :
    mleA (scatterWords c words rows shift weight a) pt =
      mleA a pt + ∑ u ∈ range rows, landAt (eqAt pt) a.size (c.shifted (σ u) shift) (weight u) := by
  rw [mleA_eq_sum _ _ (by rw [Complete.size_scatterWords, ha]), mleA_eq_sum _ _ ha, ← ha,
    sum_mul_scatterWords hc h]

end LeanVM.Prover.Complete

end
