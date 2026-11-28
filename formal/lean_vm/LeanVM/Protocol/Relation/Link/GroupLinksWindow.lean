/-
  LeanVM.Protocol.Relation.Link.GroupLinksWindow

  A one-hot pointer word read by `verify_link`'s functionals at a Boolean index point, at its index
  and `s` cells further inside its window.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupMirror
public import LeanVM.Protocol.Relation.Link.GroupCube
import LeanVM.Parameters.Field

/-!
# The window read at a Boolean point

For the chunks `Chunks.new` gives and a pointer word one-hot in every chunk, decoding to
`σ = ptrIndex`:

* `ptrIndex_lt`: `σ < 2^W`;
* `lk_window_bool`: the functionals `Functionals::new` builds at the Boolean point of `j`
  (`boolL`), read from the word's bits by `Functionals::values`, give
  `T_s(e_0)·Π_{i ≥ 1} D_i(e_i)` (`T_0 = D_0`) equal to one exactly when the shift `s` read names `j`
  inside the window (`windowHit`), zero otherwise.

The route is `Window.lean`'s `window_read` over the chunks' parts of the point (`Chunks.part`),
whose concatenation is the point (`lkw_flatten`), with the chunks' positions encoding `σ`
(`lkw_encodes`, `lkw_ptrIndex_eq`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

/-! ## The chunks' layout -/

/-- **The chunks tile the pointer's bits in order**, the lowest at word bit `0`, for every width
`Chunks.new` accepts. -/
theorem lkw_chunks_tile {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) :
    0 < c.d ∧ c.indexShifts.getD 0 0 = 0 ∧ c.wordShifts.getD 0 0 = 0 ∧
      c.indexShifts.getD (c.d - 1) 0 + c.widths.getD (c.d - 1) 0 = c.width ∧
      ∀ i < c.d - 1, c.indexShifts.getD (i + 1) 0 = c.indexShifts.getD i 0 + c.widths.getD i 0 := by
  have key : ∀ w < 25, ∀ c, Chunks.new w = some c →
      0 < c.d ∧ c.indexShifts.getD 0 0 = 0 ∧ c.wordShifts.getD 0 0 = 0 ∧
        c.indexShifts.getD (c.d - 1) 0 + c.widths.getD (c.d - 1) 0 = c.width ∧
        ∀ i < c.d - 1, c.indexShifts.getD (i + 1) 0 = c.indexShifts.getD i 0 + c.widths.getD i 0 := by
    decide +kernel
  by_cases hw : w < 25
  · exact key w hw c h
  · unfold Chunks.new at h
    split_ifs at h with hc
    · exact absurd hc.2 (by simp [maxPointerWidth]; omega)

/-- The positions `h i` of the chunks `L`, chunk `i` of `(f i).length` bits, lowest first. -/
def lkwVal (f : ℕ → List E) (h : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | i :: L => h i + 2 ^ (f i).length * lkwVal f h L

theorem lkw_encodes (f : ℕ → List E) (g : ℕ → ℕ → E) (h : ℕ → ℕ) : ∀ L : List ℕ,
    (∀ i ∈ L, h i < 2 ^ (f i).length ∧ OneHot (f i).length (g i) (h i)) →
    Encodes (L.map f) (L.map g) (lkwVal f h L)
  | [], _ => by simp [Encodes, lkwVal]
  | i :: L, hL => by
    obtain ⟨hlt, hone⟩ := hL i List.mem_cons_self
    have hpos : 0 < 2 ^ (f i).length := Nat.two_pow_pos _
    simp only [List.map_cons, Encodes]
    refine ⟨?_, ?_⟩
    · rw [lkwVal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      exact hone
    · rw [lkwVal, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, zero_add]
      exact lkw_encodes f g h L fun j hj ↦ hL j (List.mem_cons_of_mem _ hj)

theorem lkwVal_lt (f : ℕ → List E) (h : ℕ → ℕ) : ∀ L : List ℕ, (∀ i ∈ L, h i < 2 ^ (f i).length) →
    lkwVal f h L < 2 ^ (L.map f).flatten.length
  | [], _ => by simp [lkwVal]
  | i :: L, hL => by
    have h1 := hL i List.mem_cons_self
    have h2 := lkwVal_lt f h L fun j hj ↦ hL j (List.mem_cons_of_mem _ hj)
    rw [lkwVal, List.map_cons, List.flatten_cons, List.length_append, pow_add]
    calc h i + 2 ^ (f i).length * lkwVal f h L < 2 ^ (f i).length * (lkwVal f h L + 1) := by
          rw [mul_add, mul_one]; omega
      _ ≤ 2 ^ (f i).length * 2 ^ (L.map f).flatten.length := Nat.mul_le_mul_left _ h2

theorem lkw_sum_eq (f : ℕ → List E) (h is : ℕ → ℕ) : ∀ (n k : ℕ),
    (∀ i, k ≤ i → i + 1 < k + n → is (i + 1) = is i + (f i).length) →
    ((List.range' k n).map fun i ↦ h i * 2 ^ is i).sum = 2 ^ is k * lkwVal f h (List.range' k n)
  | 0, k, _ => by simp [lkwVal]
  | n + 1, k, hs => by
    rw [List.range'_succ, List.map_cons, List.sum_cons,
      lkw_sum_eq f h is n (k + 1) (fun i hi hi' ↦ hs i (by omega) (by omega)), lkwVal]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [List.range'_zero, lkwVal, mul_zero, add_zero]
      ring
    · rw [hs k le_rfl (by omega), pow_add]
      ring

theorem lkw_flatten_drop (r : List E) (is w : ℕ → ℕ) : ∀ (n k : ℕ), 0 < n →
    (∀ i, k ≤ i → i + 1 < k + n → is (i + 1) = is i + w i) → is (k + n - 1) + w (k + n - 1) = r.length →
    ((List.range' k n).map fun i ↦ (r.drop (is i)).take (w i)).flatten = r.drop (is k)
  | 0, _, h0, _, _ => absurd h0 (lt_irrefl 0)
  | 1, k, _, _, hend => by
    simp only [Nat.add_sub_cancel] at hend
    simp only [List.range'_succ, List.range'_zero, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    rw [List.take_of_length_le]
    rw [List.length_drop]
    omega
  | n + 2, k, _, hs, hend => by
    rw [List.range'_succ, List.map_cons, List.flatten_cons,
      lkw_flatten_drop r is w (n + 1) (k + 1) (by omega) (fun i hi hi' ↦ hs i (by omega) (by omega))
        (by rw [show k + 1 + (n + 1) - 1 = k + (n + 2) - 1 by omega]; exact hend),
      hs k le_rfl (by omega), show r.drop (is k + w k) = (r.drop (is k)).drop (w k) by
        rw [List.drop_drop], List.take_append_drop]

/-! ## The pointer's chunks -/

/-- A one-hot chunk's first set bit is its hot value. -/
theorem lkw_chunkPos {c : Chunks} {word : K} {i σ : ℕ} (hσ : σ < 2 ^ c.widths.getD i 0)
    (he : OneHot (c.widths.getD i 0) (chunkTable c word i) σ) : chunkPos c word i = σ := by
  have hbit : ∀ v < 2 ^ c.widths.getD i 0,
      word.toBitVec.getLsbD (c.wordShifts.getD i 0 + v) = true ↔ v = σ := by
    intro v hv
    have := he v hv
    simp only [chunkTable, bitOf] at this
    by_cases hb : word.toBitVec.getLsbD (c.wordShifts.getD i 0 + v) = true <;>
      by_cases hvs : v = σ <;> simp_all
  have hf : (List.range (2 ^ c.widths.getD i 0)).find?
      (fun v ↦ word.toBitVec.getLsbD (c.wordShifts.getD i 0 + v)) = some σ :=
    List.find?_range_eq_some.mpr ⟨(hbit σ hσ).mpr rfl, List.mem_range.mpr hσ, fun j hj ↦ by
      have := (hbit j (by omega)).not.mpr (by omega)
      simpa using this⟩
  unfold chunkPos
  simp only [hf, Option.getD_some]

/-- **The chunks' positions encode the pointer**: `ptrIndex` is their value in the chunks' layout. -/
theorem lkw_ptrIndex_eq {w : ℕ} {c : Chunks} (hch : Chunks.new w = some c) (word : K) (r : List E)
    (hr : r.length = c.width) :
    ptrIndex c word = lkwVal (c.part r) (chunkPos c word) (List.range c.d) := by
  obtain ⟨hd, his0, -, -, hstep⟩ := lkw_chunks_tile hch
  have hgeo := chunks_geometry hch
  unfold ptrIndex
  rw [List.range_eq_range', lkw_sum_eq (c.part r) (chunkPos c word) (c.indexShifts.getD · 0) c.d 0
    (fun i _ hi ↦ by rw [hstep i (by omega), part_length _ _ (by rw [hr]; exact (hgeo i (by omega)).1)]),
    his0, pow_zero, one_mul]

theorem lkw_pos {c : Chunks} (word : K) (hone : ∀ i < c.d, ChunkOneHot c word i) :
    ∀ i < c.d, chunkPos c word i < 2 ^ c.widths.getD i 0 ∧
      OneHot (c.widths.getD i 0) (chunkTable c word i) (chunkPos c word i) := by
  intro i hi
  obtain ⟨σ, hσ, he⟩ := hone i hi
  rw [lkw_chunkPos hσ he]
  exact ⟨hσ, he⟩

/-- **A one-hot pointer decodes below `2^W`.** -/
theorem ptrIndex_lt {w : ℕ} {chunks : Chunks} (hch : Chunks.new w = some chunks) (word : K)
    (hone : ∀ i < chunks.d, ChunkOneHot chunks word i) : ptrIndex chunks word < 2 ^ chunks.width := by
  obtain ⟨hd, his0, -, hend, hstep⟩ := lkw_chunks_tile hch
  have hgeo := chunks_geometry hch
  have hr : (boolL chunks.width 0).length = chunks.width := length_boolL _ _
  have hpos := lkw_pos word hone
  rw [lkw_ptrIndex_eq hch word _ hr]
  have hlt := lkwVal_lt (chunks.part (boolL chunks.width 0)) (chunkPos chunks word) (List.range chunks.d)
    fun i hi ↦ by
      rw [part_length _ _ (by rw [hr]; exact (hgeo i (List.mem_range.mp hi)).1)]
      exact (hpos i (List.mem_range.mp hi)).1
  have hflat : ((List.range chunks.d).map (chunks.part (boolL chunks.width 0))).flatten =
      boolL chunks.width 0 := by
    have := lkw_flatten_drop (boolL chunks.width 0) (chunks.indexShifts.getD · 0) (chunks.widths.getD · 0)
      chunks.d 0 hd (fun i _ hi ↦ hstep i (by omega)) (by rw [zero_add, hr]; exact hend)
    rw [List.range_eq_range']
    rw [his0, List.drop_zero] at this
    exact this
  rwa [hflat, hr] at hlt

/-! ## The functionals' values -/

theorem lkw_values_lo (c : Chunks) (r : List E) (ms : ℕ) (word : K) {i : ℕ} (hi : i < c.d)
    (hlen : (c.part r i).length = c.widths.getD i 0)
    (hfit : c.wordShifts.getD i 0 + 2 ^ c.widths.getD i 0 ≤ kBits) :
    ((Functionals.new c r ms).values c ((List.range kBits).map (bitOf word))).getD i 0 =
      chunkEval (c.part r i) (chunkTable c word i) := by
  rw [values_getD_lo _ _ _ _ hi, sumE_zipWith_eqKernel _ _
    (by rw [List.length_drop, List.length_map, List.length_range, hlen]; omega), chunkEval_eq_mle]
  unfold mle
  refine sum_congr rfl fun v hv ↦ ?_
  have hv' := mem_range.mp hv
  rw [hlen] at hv'
  congr 1
  have hlt : v < (((List.range kBits).map (bitOf word)).drop (c.wordShifts.getD i 0)).length := by
    rw [List.length_drop, List.length_map, List.length_range]; omega
  show (((List.range kBits).map (bitOf word)).drop (c.wordShifts.getD i 0)).getD v 0 = _
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rfl

theorem lkw_values_shift_raw (c : Chunks) (r : List E) (ms : ℕ) (sl : List E) {s : ℕ} (hs1 : 1 ≤ s)
    (hs : s ≤ ms) (hd : 0 < c.d) :
    ((Functionals.new c r ms).values c sl).getD (2 * c.d + (s - 1)) 0 =
      sumE (List.zipWith (· * ·) (linkWindowShift (eqKernel (c.part r 0)) s) (sl.drop (c.wordShifts.getD 0 0))) := by
  have hs' : s - 1 + 1 = s := by omega
  have hhead : ((List.range c.d).map fun i ↦ eqKernel (c.part r i)).headD [] = eqKernel (c.part r 0) := by
    obtain ⟨n, hn⟩ : ∃ n, c.d = n + 1 := ⟨c.d - 1, by omega⟩
    simp [hn, List.range_succ_eq_map]
  unfold Functionals.values Functionals.new
  dsimp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_map, List.length_zip, List.length_range, min_self]
  rw [show 2 * c.d + (s - 1) - (c.d + c.d) = s - 1 by omega, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some, hs', hhead]

theorem lkw_values_shift (c : Chunks) (r : List E) (ms : ℕ) (word : K) {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ ms)
    (hd : 0 < c.d) (h0 : c.wordShifts.getD 0 0 = 0) (hlen : (c.part r 0).length = c.widths.getD 0 0)
    (hfit : 2 ^ c.widths.getD 0 0 ≤ kBits) :
    ((Functionals.new c r ms).values c ((List.range kBits).map (bitOf word))).getD (2 * c.d + (s - 1)) 0 =
      windowShift (c.part r 0) (chunkTable c word 0) s := by
  rw [lkw_values_shift_raw c r ms _ hs1 hs hd, h0, List.drop_zero]
  have hwl : (linkWindowShift (eqKernel (c.part r 0)) s).length = 2 ^ (c.part r 0).length := by
    rw [linkWindowShift, List.length_map, List.length_range, eqKernel_length]
  rw [sumE_zipWith_eq _ _ (by rw [hwl, List.length_map, List.length_range, hlen]; exact hfit), hwl,
    windowShift]
  refine sum_congr rfl fun v hv ↦ ?_
  have hv' := mem_range.mp hv
  have hv64 : v < kBits := by rw [hlen] at hv'; omega
  rw [mul_comm]
  congr 1
  · rw [List.getD_eq_getElem _ _ (by simpa using hv64), List.getElem_map, List.getElem_range]
    simp only [chunkTable, h0, zero_add]
  · rw [linkWindowShift, List.getD_eq_getElem _ _ (by simpa [eqKernel_length] using hv'),
      List.getElem_map, List.getElem_range, eqKernel_getD]

theorem lkw_chunksEval_map (f : ℕ → List E) (g : ℕ → ℕ → E) : ∀ L : List ℕ,
    chunksEval (L.map f) (L.map g) = (L.map fun i ↦ chunkEval (f i) (g i)).prod
  | [] => by simp [chunksEval]
  | i :: L => by simp only [List.map_cons, chunksEval, List.prod_cons, lkw_chunksEval_map f g L]

/-! ## The window read -/

/-- **The window read at a Boolean point**: a pointer word one-hot in every chunk, read by the
functionals at the Boolean point of `jr` at shift `s ≤ max_shift` (`T_0 = D_0`, times the other
chunks' `D_i`), is one when its shift-`s` read names `jr` inside its window, zero otherwise. -/
theorem lk_window_bool {w : ℕ} {chunks : Chunks} (hch : Chunks.new w = some chunks) (word : K)
    (hone : ∀ i < chunks.d, ChunkOneHot chunks word i) (ms : ℕ) {jr : ℕ} (hjr : jr < 2 ^ chunks.width)
    (s : ℕ) (hs : s ≤ ms) :
    let f := Functionals.new chunks (boolL chunks.width jr) ms
    let vals := f.values chunks ((List.range kBits).map (bitOf word))
    (if s = 0 then vals.getD 0 0 else vals.getD (2 * chunks.d + (s - 1)) 0) *
        prodE ((vals.drop 1).take (chunks.d - 1)) =
      if Hotwire.windowHit (chunks.widths.getD 0 0) (ptrIndex chunks word) s = some jr then 1 else 0 := by
  dsimp only
  obtain ⟨hd, his0, hws0, hend, hstep⟩ := lkw_chunks_tile hch
  have hgeo := chunks_geometry hch
  have hr : (boolL chunks.width jr).length = chunks.width := length_boolL _ _
  have hlen : ∀ i < chunks.d, (chunks.part (boolL chunks.width jr) i).length = chunks.widths.getD i 0 :=
    fun i hi ↦ part_length _ _ (by rw [hr]; exact (hgeo i hi).1)
  have hpos := lkw_pos word hone
  have hrange : List.range chunks.d = 0 :: List.range' 1 (chunks.d - 1) := by
    rw [List.range_eq_range', show chunks.d = (chunks.d - 1) + 1 by omega, List.range'_succ]
    simp
  set r := boolL chunks.width jr with hrdef
  set vals := (Functionals.new chunks r ms).values chunks ((List.range kBits).map (bitOf word)) with hvals
  set σ := ptrIndex chunks word with hσdef
  set P' := (List.range' 1 (chunks.d - 1)).map (chunks.part r)
  set E' := (List.range' 1 (chunks.d - 1)).map (chunkTable chunks word)
  -- the low factor
  have hlow : (if s = 0 then vals.getD 0 0 else vals.getD (2 * chunks.d + (s - 1)) 0) =
      windowShift (chunks.part r 0) (chunkTable chunks word 0) s := by
    split_ifs with h0
    · rw [h0, windowShift_zero]
      exact lkw_values_lo chunks r ms word hd (hlen 0 hd) (hgeo 0 hd).2
    · exact lkw_values_shift chunks r ms word (by omega) hs hd hws0 (hlen 0 hd)
        (by have := (hgeo 0 hd).2; omega)
  -- the other chunks
  have hrest : prodE ((vals.drop 1).take (chunks.d - 1)) = chunksEval P' E' := by
    have hvl : chunks.d ≤ vals.length := by
      simp [hvals, Functionals.values, Functionals.new]
    have hvlo : ∀ i < chunks.d, vals.getD i 0 = chunkEval (chunks.part r i) (chunkTable chunks word i) :=
      fun i hi ↦ lkw_values_lo chunks r ms word hi (hlen i hi) (hgeo i hi).2
    have hl : (vals.drop 1).take (chunks.d - 1) =
        (List.range' 1 (chunks.d - 1)).map fun i ↦ chunkEval (chunks.part r i) (chunkTable chunks word i) := by
      refine List.ext_getElem (by simp; omega) fun j h1 h2 ↦ ?_
      simp only [List.length_take, List.length_drop] at h1
      simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range', one_mul]
      rw [← hvlo (1 + j) (by omega)]
      exact (List.getD_eq_getElem _ _ _).symm
    rw [hl, lkw_chunksEval_map, prodE_eq_prod]
  -- the encoding
  have henc : Encodes (chunks.part r 0 :: P') (chunkTable chunks word 0 :: E') σ := by
    have := lkw_encodes (chunks.part r) (chunkTable chunks word) (chunkPos chunks word) (List.range chunks.d)
      fun i hi ↦ by rw [hlen i (List.mem_range.mp hi)]; exact hpos i (List.mem_range.mp hi)
    rw [hσdef, lkw_ptrIndex_eq hch word r hr]
    rw [hrange] at this ⊢
    simp only [List.map_cons] at this
    exact this
  have hflat : (chunks.part r 0 :: P').flatten = r := by
    have := lkw_flatten_drop r (chunks.indexShifts.getD · 0) (chunks.widths.getD · 0)
      chunks.d 0 hd (fun i _ hi ↦ hstep i (by omega)) (by rw [zero_add, hr]; exact hend)
    rw [his0, List.drop_zero, ← List.range_eq_range', hrange, List.map_cons] at this
    exact this
  have hσlt : σ < 2 ^ chunks.width := ptrIndex_lt hch word hone
  have hw0 : chunks.widths.getD 0 0 ≤ chunks.width := by have := (hgeo 0 hd).1; omega
  rw [hlow, hrest, window_read _ _ _ _ σ s henc, hflat, hlen 0 hd]
  unfold Hotwire.windowHit
  by_cases hin : σ % 2 ^ chunks.widths.getD 0 0 + s < 2 ^ chunks.widths.getD 0 0
  · have hlt : σ + s < 2 ^ chunks.width :=
      windowHit_lt hw0 hσlt (by unfold windowHit; rw [ite_eq_left hin])
    rw [ite_eq_left hin, ite_eq_left hin, hrdef, eqAt_boolL hlt hjr]
    by_cases he : σ + s = jr
    · rw [ite_eq_left he, ite_eq_left (congrArg some he)]
    · rw [ite_eq_right he, ite_eq_right (fun h ↦ he (Option.some.inj h))]
  · rw [ite_eq_right hin, ite_eq_right hin, ite_eq_right (by simp : ¬ (none : Option ℕ) = some jr)]

end

end LeanVM.Protocol.Relation

/-! The window read's theorems use Lean's three standard axioms only. -/

/-- info: 'LeanVM.Protocol.Relation.lk_window_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.lk_window_bool

/-- info: 'LeanVM.Protocol.Relation.ptrIndex_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.ptrIndex_lt
