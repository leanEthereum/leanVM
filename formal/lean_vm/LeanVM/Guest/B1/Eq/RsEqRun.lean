/-
  LeanVM.Guest.B1.Eq.RsEqRun

  B1 for `rs_eq_run`: the telescoped ring-switch rows, eight coordinates a row.
-/

module

public import LeanVM.Guest.B1.Eq.RsLoop
public import LeanVM.Guest.B1.Bits.GPower
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.B1.Common.Vc

/-!
# `rs_eq_run` (lean_ethereum.py)

`rs_eq_run(chain, z_vals, point1, count_g)` hints the six bits of `count` (`count_g = g^count`),
pins them by booleanity and `q_g^8 · r_g = count_g` (`r_g` from bits `0 .. 2`, `q_g` from bits
`3 .. 5`, so `count = 8q + r`), runs `rs_eq_run_loop0` over the `q` full chunks (`rs_eq_rows__L8`
each), and dispatches the remainder's `rs_eq_rows__L{r}` on the row `chain·g^(64q)`; it returns that
call's return, the last row (`rs_eq_run_holds`).

The rows from the chunks and back: `rows_of_chunks`, `chunks_of_rows` (chunk `t` is coordinates
`8t ..` and row `t`, `ChunkOk`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The expansion of `rs_eq_run`. -/
def rsBody : List Stmt :=
  [.atom (.hint (.bitsExp (.n 3) 6 (.stack [.n 4, .n 5, .n 6, .n 7, .n 8, .n 9]))),
    .atom (.mul (.n 4) (.n 4) (.n 4)), .atom (.const (.n 10) (word 1 0)),
    .atom (.const (.n 11) (word 3 0)), .atom (.mul (.n 12) (.n 4) (.n 11)),
    .atom (.add (.n 13) (.n 10) (.n 12)), .atom (.mul (.n 5) (.n 5) (.n 5)),
    .atom (.const (.n 14) (word 1 0)), .atom (.const (.n 15) (word 5 0)),
    .atom (.mul (.n 16) (.n 5) (.n 15)), .atom (.add (.n 17) (.n 14) (.n 16)),
    .atom (.mul (.n 18) (.n 13) (.n 17)), .atom (.mul (.n 6) (.n 6) (.n 6)),
    .atom (.const (.n 19) (word 1 0)), .atom (.const (.n 20) (word 17 0)),
    .atom (.mul (.n 21) (.n 6) (.n 20)), .atom (.add (.n 22) (.n 19) (.n 21)),
    .atom (.mul (.n 23) (.n 18) (.n 22)), .atom (.mul (.n 7) (.n 7) (.n 7)),
    .atom (.const (.n 24) (word 1 0)), .atom (.const (.n 25) (word 3 0)),
    .atom (.mul (.n 26) (.n 7) (.n 25)), .atom (.add (.n 27) (.n 24) (.n 26)),
    .atom (.mul (.n 8) (.n 8) (.n 8)), .atom (.const (.n 28) (word 1 0)),
    .atom (.const (.n 29) (word 5 0)), .atom (.mul (.n 30) (.n 8) (.n 29)),
    .atom (.add (.n 31) (.n 28) (.n 30)), .atom (.mul (.n 32) (.n 27) (.n 31)),
    .atom (.mul (.n 9) (.n 9) (.n 9)), .atom (.const (.n 33) (word 1 0)),
    .atom (.const (.n 34) (word 17 0)), .atom (.mul (.n 35) (.n 9) (.n 34)),
    .atom (.add (.n 36) (.n 33) (.n 35)), .atom (.mul (.n 37) (.n 32) (.n 36)),
    .atom (.mul (.n 38) (.n 37) (.n 37)), .atom (.mul (.n 39) (.n 38) (.n 38)),
    .atom (.mul (.n 40) (.n 39) (.n 39)), .atom (.mul (.n 41) (.n 40) (.n 23)),
    .atom (.assertEq (.n 41) (.n 3)), .atom (.const (.n 42) (word 1 0)),
    .atom (.add (.n 43) (.n 42) (.n 37)), .atom (.const (.n 44) (word 1 0)),
    .callIf (.n 43) name% «rs_eq_run_loop0» [.n 44, .n 37, .n 0, .n 1, .n 2],
    .atom (.mul (.n 45) (.n 37) (.n 37)), .atom (.mul (.n 46) (.n 45) (.n 45)),
    .atom (.mul (.n 47) (.n 46) (.n 46)), .atom (.mul (.n 48) (.n 37) (.n 37)),
    .atom (.mul (.n 49) (.n 48) (.n 48)), .atom (.mul (.n 50) (.n 49) (.n 49)),
    .atom (.mul (.n 51) (.n 50) (.n 50)), .atom (.mul (.n 52) (.n 51) (.n 51)),
    .atom (.mul (.n 53) (.n 52) (.n 52)), .atom (.mul (.n 54) (.n 0) (.n 53)),
    .atom (.mul (.n 55) (.n 1) (.n 47)), .atom (.mul (.n 56) (.n 2) (.n 47)),
    .dispatch (.n 23) ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3",
      "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"] [.n 54, .n 55, .n 56]
      [.n 57],
    .atom (.copy (.n 58) (.n 57)), .ret [.n 58]]

theorem rs_eq_run_body : Fn.body fn% «rs_eq_run» = rsBody := stmtsEqb_sound (by decide +kernel)

theorem find_rs_eq_run : coreProgram.find? "rs_eq_run" = some fn% «rs_eq_run» :=
  coreProgram_find?_at (j := idx% «rs_eq_run») rfl

theorem rs_consts : word 3 0 = gen ^ 2 ^ 0 + 1 ∧ word 5 0 = gen ^ 2 ^ 1 + 1 ∧
    word 17 0 = gen ^ 2 ^ 2 + 1 :=
  ⟨word_gpow_one 0 (by norm_num) 3 (by decide), word_gpow_one 1 (by norm_num) 5 (by decide),
    word_gpow_one 2 (by norm_num) 17 (by decide)⟩

/-! ## Chunks and rows -/

/-- Chunk `t`: its coordinates from `z·g^(8t)`, `p·g^(8t)`, row `t` from `chain·g^(64t)`, and
row `t + 1` its product. -/
def ChunkOk (rd : Reader) (chain z p : E) (t : ℕ) (zt pt ct : List E) : Prop :=
  ReadsAt rd (z * gen ^ (8 * t)) zt ∧ ReadsAt rd (p * gen ^ (8 * t)) pt ∧ ct.length = 64 ∧
    ReadsAt rd (chain * gen ^ (64 * t)) ct ∧
    ∀ k < 64, LoadHolds rd (chain * gen ^ (64 * t)) (64 + k) (ringRow (ct.getD k 0) zt pt k)

theorem ringRow_append (c : E) (A A' B B' : List E) (k : ℕ) (h : A.length = B.length) :
    ringRow c (A ++ A') (B ++ B') k = ringRow (ringRow c A B k) A' B' k := by
  rw [ringRow, ringRow, ringRow, List.zipWith_append h, List.foldl_append]

theorem take_flatMap_eight (Z : ℕ → List E) (q : ℕ) (hZ : ∀ t < q, (Z t).length = 8)
    (rest : List E) (t : ℕ) (h : t ≤ q) :
    ((List.range q).flatMap Z ++ rest).take (8 * t) = (List.range t).flatMap Z := by
  obtain ⟨q', rfl⟩ : ∃ q', q = t + q' := ⟨q - t, by omega⟩
  have hl : ((List.range t).flatMap Z).length = 8 * t := by
    rw [length_flatMap_range 8 Z t (fun i hi ↦ hZ i (by omega)), Nat.mul_comm]
  rw [List.range_add, List.flatMap_append, List.append_assoc, List.take_append_of_le_length
    (by rw [hl]), List.take_of_length_le (by rw [hl])]

theorem readsAt_mul_gen_pow {rd : Reader} {p : E} {o : ℕ} {xs : List E} :
    ReadsAt rd (p * gen ^ o) xs ↔ ∀ i < xs.length, LoadHolds rd p (o + i) (xs.getD i 0) := by
  constructor
  · intro h i hi
    rw [← loadHolds_mul_gen_pow]
    exact readsAt_getD h hi
  · intro h i hi
    have := h i hi
    rwa [← loadHolds_mul_gen_pow, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] at this

/-- The honest rows: row `t` is row `0` times the products over the first `8t` coordinates. -/
def rsR (c zs ps : List E) (t k : ℕ) : E := ringRow (c.getD k 0) (zs.take (8 * t)) (ps.take (8 * t)) k

/-- The words of `q` chunks of eight, then one of `r`, read from `z`. -/
theorem readsAt_chunks {rd : Reader} {z : E} {q r : ℕ} (Z : ℕ → List E)
    (hZ : ∀ t < q, (Z t).length = 8) (hZq : (Z q).length = r)
    (hrd : ∀ t < q, ReadsAt rd (z * gen ^ (8 * t)) (Z t))
    (hl : 0 < r → ReadsAt rd (z * gen ^ (8 * q)) (Z q)) :
    ReadsAt rd z ((List.range q).flatMap Z ++ Z q) := by
  have lZ : ((List.range q).flatMap Z).length = 8 * q := by
    rw [length_flatMap_range 8 Z q hZ, Nat.mul_comm]
  intro i hi
  rw [List.length_append, lZ, hZq] at hi
  rw [← List.getD_eq_getElem _ (0 : E)]
  rcases Nat.lt_or_ge i (8 * q) with h | h
  · rw [List.getD_append _ _ _ _ (by rw [lZ]; exact h),
      show i = i / 8 * 8 + i % 8 by omega,
      getD_flatMap_range 8 0 (i / 8) Z q (i % 8) (by omega) (fun j hj ↦ hZ j (by omega))
        (by rw [hZ _ (by omega)]; omega)]
    have := (readsAt_mul_gen_pow.mp (hrd (i / 8) (by omega))) (i % 8)
      (by rw [hZ _ (by omega)]; omega)
    rwa [show 8 * (i / 8) + i % 8 = i / 8 * 8 + i % 8 by ring] at this
  · rw [List.getD_append_right _ _ _ _ (by rw [lZ]; exact h), lZ]
    have := (readsAt_mul_gen_pow.mp (hl (by omega))) (i - 8 * q) (by rw [hZq]; omega)
    rwa [show 8 * q + (i - 8 * q) = i by omega] at this

/-- **The rows from the chunks**: `q` chunks of eight coordinates, then one of `r`. -/
theorem rows_of_chunks {rd : Reader} {chain z p : E} {q r : ℕ} (hr8 : r < 8) (Z P C : ℕ → List E)
    (hZ : ∀ t < q, (Z t).length = 8) (hP : ∀ t < q, (P t).length = 8) (hZq : (Z q).length = r)
    (hPq : (P q).length = r) (hok : ∀ t < q, ChunkOk rd chain z p t (Z t) (P t) (C t))
    (hlast : 0 < r → ChunkOk rd chain z p q (Z q) (P q) (C q)) :
    let zs := (List.range q).flatMap Z ++ Z q
    let ps := (List.range q).flatMap P ++ P q
    let c := (List.range 64).map fun k ↦ (C 0).getD k 0
    zs.length = 8 * q + r ∧ ps.length = 8 * q + r ∧ c.length = 64 ∧ ReadsAt rd z zs ∧
      ReadsAt rd p ps ∧ (0 < 8 * q + r → ReadsAt rd chain c) ∧
      ∀ h, 1 ≤ h → h ≤ (8 * q + r + 7) / 8 → ∀ k < 64,
        LoadHolds rd chain (64 * h + k)
          (ringRow (c.getD k 0) (zs.take (min (8 * h) (8 * q + r)))
            (ps.take (min (8 * h) (8 * q + r))) k) := by
  intro zs ps c
  have lZ : ((List.range q).flatMap Z).length = 8 * q := by
    rw [length_flatMap_range 8 Z q hZ, Nat.mul_comm]
  have lP : ((List.range q).flatMap P).length = 8 * q := by
    rw [length_flatMap_range 8 P q hP, Nat.mul_comm]
  have hzs : zs.length = 8 * q + r := by simp only [zs, List.length_append, lZ, hZq]
  have hps : ps.length = 8 * q + r := by simp only [ps, List.length_append, lP, hPq]
  have hc : c.length = 64 := by simp [c]
  have ex : 0 < q ∨ 0 < r → ∀ t, t ≤ q → (t < q ∨ 0 < r) →
      ChunkOk rd chain z p t (Z t) (P t) (C t) := fun _ t ht h ↦ by
    rcases Nat.lt_or_ge t q with h' | h'
    · exact hok t h'
    · obtain rfl : t = q := by omega
      exact hlast (by omega)
  -- the take of the first `t` chunks
  have tz : ∀ t ≤ q, zs.take (8 * t) = (List.range t).flatMap Z := fun t ht ↦
    take_flatMap_eight Z q hZ (Z q) t ht
  have tp : ∀ t ≤ q, ps.take (8 * t) = (List.range t).flatMap P := fun t ht ↦
    take_flatMap_eight P q hP (P q) t ht
  have rstep : ∀ t < q, ∀ k, rsR c zs ps (t + 1) k = ringRow (rsR c zs ps t k) (Z t) (P t) k := by
    intro t ht k
    rw [rsR, rsR, tz (t + 1) ht, tp (t + 1) ht, tz t ht.le, tp t ht.le, List.range_succ,
      List.flatMap_append, List.flatMap_append, List.flatMap_singleton, List.flatMap_singleton,
      ringRow_append _ _ _ _ _ _ (by rw [length_flatMap_range 8 Z t (fun i hi ↦ hZ i (by omega)),
        length_flatMap_range 8 P t (fun i hi ↦ hP i (by omega))])]
  -- row `t` is what chunk `t` reads
  have hrow : ∀ t ≤ q, (t < q ∨ 0 < r) → ∀ k < 64, (C t).getD k 0 = rsR c zs ps t k := by
    intro t
    induction t with
    | zero =>
      intro _ _ k hk
      rw [rsR, Nat.mul_zero, ringRow_nil]
      simp [c, List.getD_eq_getElem?_getD, hk]
    | succ t ih =>
      intro ht hex k hk
      obtain ⟨-, -, -, -, hst⟩ := hok t (by omega)
      obtain ⟨-, -, hl, hrd, -⟩ := ex (by omega) (t + 1) ht hex
      have a := readsAt_getD hrd (show k < (C (t + 1)).length by omega)
      have b := hst k hk
      rw [ih (by omega) (by omega) k hk, ← rstep t (by omega) k] at b
      rw [loadHolds_mul_gen_pow] at a b
      rw [show 64 * (t + 1) + k = 64 * t + (64 + k) by ring] at a
      exact loadHolds_unique a b
  refine ⟨hzs, hps, hc, fun i hi ↦ ?_, fun i hi ↦ ?_, fun hpos ↦ ?_, fun h h1 h2 k hk ↦ ?_⟩
  · exact readsAt_chunks Z hZ hZq (fun t ht ↦ (hok t ht).1) (fun h ↦ (hlast h).1) i hi
  · exact readsAt_chunks P hP hPq (fun t ht ↦ (hok t ht).2.1) (fun h ↦ (hlast h).2.1) i hi
  · obtain ⟨-, -, hl, hrd, -⟩ := ex (by omega) 0 (Nat.zero_le _) (by omega)
    refine readsAt_range fun k hk ↦ ?_
    have := (readsAt_mul_gen_pow.mp hrd) k (by omega)
    rwa [Nat.mul_zero, Nat.zero_add] at this
  · rcases Nat.lt_or_ge q h with hq | hq
    · -- the remainder's row
      have hr0 : 0 < r := by omega
      obtain rfl : h = q + 1 := by omega
      obtain ⟨-, -, -, -, hst⟩ := hlast hr0
      have b := hst k hk
      rw [hrow q le_rfl (Or.inr hr0) k hk, rsR, tz q le_rfl, tp q le_rfl,
        ← ringRow_append _ _ _ _ _ _ (by rw [lZ, lP]), loadHolds_mul_gen_pow] at b
      rw [min_eq_right (by omega), ← hzs, List.take_length, hzs, ← hps, List.take_length,
        show 64 * (q + 1) + k = 64 * q + (64 + k) by ring]
      exact b
    · obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      obtain ⟨-, -, -, -, hst⟩ := hok h' (by omega)
      have b := hst k hk
      rw [hrow h' (by omega) (Or.inl (by omega)) k hk, ← rstep h' (by omega) k,
        loadHolds_mul_gen_pow] at b
      rw [min_eq_left (by omega), show 64 * (h' + 1) + k = 64 * h' + (64 + k) by ring]
      exact b

theorem take_min_length {xs : List E} {n a : ℕ} (h : xs.length = n) :
    xs.take (min a n) = xs.take a := by
  rcases Nat.le_total a n with ha | ha
  · rw [min_eq_left ha]
  · rw [min_eq_right ha, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

theorem getD_map_range (f : ℕ → E) {n k : ℕ} (hk : k < n) :
    ((List.range n).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- The words from `a·g^(8t)`: eight from `8t`, or the rest. -/
theorem readsAt_drop_take {rd : Reader} {a : E} {xs : List E} (h : ReadsAt rd a xs) (t : ℕ) :
    ReadsAt rd (a * gen ^ (8 * t)) ((xs.drop (8 * t)).take 8) := by
  refine readsAt_mul_gen_pow.mpr fun i hi ↦ ?_
  simp only [List.length_take, List.length_drop] at hi
  have := readsAt_getD h (i := 8 * t + i) (by omega)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    ← List.getD_eq_getElem?_getD]

/-- **The chunks from the rows**: chunk `t` (`8t < count`) is the coordinates from `8t` (eight,
or the remainder's) and the honest row `t` (`rsR`). -/
theorem chunks_of_rows {rd : Reader} {chain z p : E} {count : ℕ} {zs ps c : List E}
    (lz : zs.length = count) (lp : ps.length = count) (lc : c.length = 64)
    (hz : ReadsAt rd z zs) (hp : ReadsAt rd p ps) (hc : 0 < count → ReadsAt rd chain c)
    (hr : ∀ h, 1 ≤ h → h ≤ (count + 7) / 8 → ∀ k < 64,
      LoadHolds rd chain (64 * h + k)
        (ringRow (c.getD k 0) (zs.take (min (8 * h) count)) (ps.take (min (8 * h) count)) k))
    (t : ℕ) (ht : 8 * t < count) :
    ChunkOk rd chain z p t ((zs.drop (8 * t)).take 8) ((ps.drop (8 * t)).take 8)
      ((List.range 64).map (rsR c zs ps t)) := by
  have hrow : ∀ k < 64, LoadHolds rd chain (64 * t + k) (rsR c zs ps t k) := by
    intro k hk
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0
      have := readsAt_getD (hc (by omega)) (i := k) (by omega)
      rwa [rsR, Nat.mul_zero, ringRow_nil, Nat.zero_add]
    · have := hr t h0 (by omega) k hk
      rwa [min_eq_left (by omega)] at this
  have hlen : (zs.take (8 * t)).length = (ps.take (8 * t)).length := by
    simp only [List.length_take, lz, lp]
  refine ⟨readsAt_drop_take hz t, readsAt_drop_take hp t, by simp, ?_, fun k hk ↦ ?_⟩
  · refine readsAt_mul_gen_pow.mpr fun k hk ↦ ?_
    simp only [List.length_map, List.length_range] at hk
    rw [getD_map_range _ hk]
    exact hrow k hk
  · rw [getD_map_range _ hk, rsR, ← ringRow_append _ _ _ _ _ _ hlen, ← List.take_add,
      ← List.take_add, loadHolds_mul_gen_pow, show 64 * t + (64 + k) = 64 * (t + 1) + k by ring]
    have := hr (t + 1) (by omega) (by omega) k hk
    rwa [take_min_length lz, take_min_length lp, show 8 * (t + 1) = 8 * t + 8 by ring] at this

/-! ## The theorem -/

theorem rsNames_get (j : ℕ) (hj : j < 8) :
    ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
      "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"][j] = rsEqRowsNames.getD j "" := by
  interval_cases j <;> rfl

/-- A chunk of `n > 0` coordinates from `rs_eq_rows__L{n}`'s meaning. -/
theorem chunk_of_meaning {rd : Reader} {chain z p ret : E} {n t : ℕ} (hn : 0 < n)
    (h : MeaningRsEqRows n rd [chain * gen ^ (64 * t), z * gen ^ (8 * t), p * gen ^ (8 * t)] [ret]) :
    ∃ zt pt ct, zt.length = n ∧ pt.length = n ∧ ChunkOk rd chain z p t zt pt ct ∧
      ret = chain * gen ^ (64 * t) * gen ^ 64 := by
  rcases h with ⟨h0, -⟩ | ⟨-, zt, pt, ct, hz, hp, hc, rz, rp, rc, hst, hret⟩
  · omega
  · simp only [List.cons.injEq, and_true] at hret
    exact ⟨zt, pt, ct, hz, hp, ⟨rz, rp, hc, rc, hst⟩, hret⟩

/-- Three pinned bits, as the body multiplies them: `g^r` for some `r < 8`. -/
private theorem rs_bits {b0 b1 b2 : E} (h0 : b0 = b0 * b0) (h1 : b1 = b1 * b1) (h2 : b2 = b2 * b2) :
    ∃ r < 8, (1 + b0 * word 3 0) * (1 + b1 * word 5 0) * (1 + b2 * word 17 0) = gen ^ r := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  have hb : ∀ j < 3, [b0, b1, b2].getD j 0 * [b0, b1, b2].getD j 0 = [b0, b1, b2].getD j 0 := by
    intro j hj
    interval_cases j
    exacts [h0.symm, h1.symm, h2.symm]
  refine ⟨_, bitsVal_lt (fun j ↦ decide ([b0, b1, b2].getD j 0 = 1)) 3, ?_⟩
  rw [← prod_gen_pow_of_bool hb, w3, w5, w17]
  simp [Finset.prod_range_succ]

/-- The bits of `r < 8`, as the body multiplies them. -/
private theorem rs_bits_of (r : ℕ) (hr : r < 8) :
    (1 + bitE (r.testBit 0) * word 3 0) * (1 + bitE (r.testBit 1) * word 5 0) *
      (1 + bitE (r.testBit 2) * word 17 0) = gen ^ r := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  have := prod_bitE_gen_pow r.testBit 3
  rw [bitsVal_testBit (show r < 2 ^ 3 by omega), Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at this
  rw [w3, w5, w17]
  exact this

/-- **`rs_eq_run`'s core IR is its meaning.** -/
theorem rs_eq_run_holds : rs_eq_run_Spec := by
  intro rd args rets
  have h8 : ∀ x : E, x * x * (x * x) * (x * x * (x * x)) = x ^ 8 := fun x ↦ by ring
  rw [rel_iff_fnSem find_rs_eq_run]
  rcases args with _ | ⟨chain, _ | ⟨z, _ | ⟨p, _ | ⟨cg, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> vc [word_one] <;>
    simp only [MeaningRsEqRun, h8]
  constructor
  · rintro ⟨x4, b0, x5, b1, x6, b2, x7, b3, x8, b4, x9, b5, ha, hK, hcall, x57,
      ⟨j, hx, hj, hdisp⟩, rfl⟩
    obtain ⟨r, hr8, hR⟩ := rs_bits b0 b1 b2
    obtain ⟨q, hq8, hQ⟩ := rs_bits b3 b4 b5
    rw [hR, hQ] at ha
    rw [hR] at hx
    rw [hQ] at hK hcall hdisp
    have hcg : cg = gen ^ (8 * q + r) := by
      rw [← e_add_eq_zero_iff.mp ha, ← pow_mul, ← pow_add, Nat.mul_comm]
    -- the loop over the full chunks
    obtain ⟨m, hm, hm', hB⟩ := (guarded_loop_rel_iff
      (fun d x ↦ loop5_sound rd (gen ^ q) chain z p d x)
      (fun x hb hk hn ↦ loop5_complete rd _ _ _ _ x hb hk hn)).mp ⟨hK, hcall⟩
    obtain rfl : m = q := gen_pow_inj hm (by show q < 2 ^ 64 - 1; omega) hm'.symm
    have hch : ∀ t < m, ∃ zt pt ct, zt.length = 8 ∧ pt.length = 8 ∧
        ChunkOk rd chain z p t zt pt ct := fun t ht ↦ by
      obtain ⟨ret, hr⟩ := hB t ht
      rw [← pow_mul, ← pow_mul, Nat.mul_comm t 64, Nat.mul_comm t 8] at hr
      obtain ⟨zt, pt, ct, a, b, c, -⟩ :=
        chunk_of_meaning (by norm_num) ((rs_eq_rows_holds 8 le_rfl rd _ _).1 hr)
      exact ⟨zt, pt, ct, a, b, c⟩
    choose! Zc Pc Cc hZc hPc hCc using hch
    -- the remainder
    obtain rfl : j = r := gen_pow_inj (by show j < 2 ^ 64 - 1; omega)
      (by show r < 2 ^ 64 - 1; omega) (by rw [gen_pow_eq_ofK, hx])
    rw [rsNames_get _ hj, ← pow_mul, ← pow_mul, ← pow_mul, show m * (8 * 8) = 64 * m by ring,
      show m * 8 = 8 * m by ring] at hdisp
    have hm8 := (rs_eq_rows_holds j (by omega) rd _ _).1 hdisp
    obtain ⟨Zl, Pl, Cl, hZl, hPl, hl, h57⟩ : ∃ Zl Pl Cl, Zl.length = j ∧ Pl.length = j ∧
        (0 < j → ChunkOk rd chain z p m Zl Pl Cl) ∧
        x57 = chain * gen ^ (64 * ((8 * m + j + 7) / 8)) := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rcases hm8 with ⟨-, hr⟩ | ⟨h, -⟩
        · simp only [List.cons.injEq, and_true] at hr
          refine ⟨[], [], [], by simp [h0], by simp [h0], fun h ↦ absurd h (by omega), ?_⟩
          rw [hr, show (8 * m + j + 7) / 8 = m by omega]
        · omega
      · obtain ⟨zt, pt, ct, a, b, c, d⟩ := chunk_of_meaning h0 hm8
        refine ⟨zt, pt, ct, a, b, fun _ ↦ c, ?_⟩
        rw [d, mul_assoc, ← pow_add, show (8 * m + j + 7) / 8 = m + 1 by omega]
        ring_nf
    let Z : ℕ → List E := fun t ↦ if t < m then Zc t else Zl
    let P : ℕ → List E := fun t ↦ if t < m then Pc t else Pl
    let C : ℕ → List E := fun t ↦ if t < m then Cc t else Cl
    obtain ⟨lz, lp, lc, rz, rp, rc, rows⟩ := rows_of_chunks (rd := rd) (chain := chain) (z := z)
      (p := p) (q := m) (r := j) (by omega) Z P C
      (fun t ht ↦ by simp only [Z, ite_pos' ht]; exact hZc t ht)
      (fun t ht ↦ by simp only [P, ite_pos' ht]; exact hPc t ht)
      (by simp only [Z, ite_neg' (lt_irrefl m)]; exact hZl)
      (by simp only [P, ite_neg' (lt_irrefl m)]; exact hPl)
      (fun t ht ↦ by simp only [Z, P, C, ite_pos' ht]; exact hCc t ht)
      (fun h ↦ by simp only [Z, P, C, ite_neg' (lt_irrefl m)]; exact hl h)
    exact ⟨8 * m + j, by omega, hcg, _, _, _, lz, lp, lc, rz, rp, rc, rows, by rw [h57]⟩
  · rintro ⟨count, hcount, rfl, zs, ps, c, lz, lp, lc, hz, hpp, hc, hr, rfl⟩
    have hch := chunks_of_rows lz lp lc hz hpp hc hr
    obtain ⟨q, hq⟩ : ∃ q, q = count / 8 := ⟨_, rfl⟩
    obtain ⟨r, hr8⟩ : ∃ r, r = count % 8 := ⟨_, rfl⟩
    -- the loop over the full chunks
    have hbody : ∀ j < q, L5Body rd chain z p (gen ^ j) := by
      intro j hj
      have hok := hch j (by omega)
      show ∃ x, coreProgram.Rel rd "rs_eq_rows__L8"
        [chain * (gen ^ j) ^ 64, z * (gen ^ j) ^ 8, p * (gen ^ j) ^ 8] [x]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm j 64, Nat.mul_comm j 8]
      exact ⟨_, (rs_eq_rows_holds 8 le_rfl rd _ _).2 (Or.inr ⟨by norm_num, _, _, _,
        by simp only [List.length_take, List.length_drop, lz]; omega,
        by simp only [List.length_take, List.length_drop, lp]; omega,
        hok.2.2.1, hok.1, hok.2.1, hok.2.2.2.1, hok.2.2.2.2, rfl⟩)⟩
    have hloop := (guarded_loop_rel_iff (B := L5Body rd chain z p)
      (fun d x ↦ loop5_sound rd (gen ^ q) chain z p d x)
      (fun x hb hk hn ↦ loop5_complete rd _ _ _ _ x hb hk hn)).mpr
      ⟨q, by show q < 2 ^ 64 - 1; omega, rfl, hbody⟩
    -- the remainder
    have hdisp : coreProgram.Rel rd (rsEqRowsNames.getD r "")
        [chain * gen ^ (64 * q), z * gen ^ (8 * q), p * gen ^ (8 * q)]
        [chain * gen ^ (64 * ((count + 7) / 8))] := by
      refine (rs_eq_rows_holds r (by omega) rd _ _).2 ?_
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · exact Or.inl ⟨h0, by rw [show (count + 7) / 8 = q by omega]⟩
      · have hok := hch q (by omega)
        refine Or.inr ⟨h0, _, _, _, ?_, ?_, hok.2.2.1, hok.1, hok.2.1, hok.2.2.2.1, hok.2.2.2.2, ?_⟩
        · simp only [List.length_take, List.length_drop, lz]; omega
        · simp only [List.length_take, List.length_drop, lp]; omega
        · rw [show (count + 7) / 8 = q + 1 by omega, mul_assoc, ← pow_add]
          ring_nf
    have hb := fun n i ↦ (bitE_mul_self (Nat.testBit n i)).symm
    refine ⟨_, hb r 0, _, hb r 1, _, hb r 2, _, hb q 0, _, hb q 1, _, hb q 2, ?_, ?_, ?_,
      _, ⟨r, ?_, by omega, ?_⟩, rfl⟩ <;>
      simp only [rs_bits_of q (by omega), rs_bits_of r (by omega)]
    · rw [e_add_eq_zero_iff, ← pow_mul, ← pow_add]
      congr 1; omega
    · exact hloop.1
    · exact hloop.2
    · rw [gen_pow_eq_ofK]
    · rw [rsNames_get r (by omega), ← pow_mul, ← pow_mul, ← pow_mul,
        show q * (8 * 8) = 64 * q by ring, show q * 8 = 8 * q by ring]
      exact hdisp

/-- **`rs_eq_run`'s core IR computes its meaning.** -/
theorem rs_eq_run_sound (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "rs_eq_run" args rets) : MeaningRsEqRun rd args rets :=
  (rs_eq_run_holds rd args rets).mp h

end
end LeanVM.Guest.B1
