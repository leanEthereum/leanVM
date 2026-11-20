/-
  LeanVM.Guest.B1.Eq.RsEqRun

  B1 for `rs_eq_run`: the telescoped ring-switch rows, eight coordinates a row.
-/

module

public import LeanVM.Guest.B1.Eq.RsLoop
public import LeanVM.Guest.B1.Bits.GPower
public import LeanVM.Guest.Data.NameStrings

/-!
# `rs_eq_run` (lean_ethereum.py)

`rs_eq_run(z_vals, point1, count_g)` hints the six bits of `count` (`count_g = g^count`), pins
them by booleanity and `q_g^8 · r_g = count_g` (`r_g` from bits `0 .. 2`, `q_g` from bits `3 .. 5`,
so `count = 8q + r`), allocates its chain of `q + 2` rows and stores row `0`'s ones, runs
`rs_eq_run_loop0` over the `q` full chunks (`rs_eq_rows__L8` each), and dispatches the remainder's
`rs_eq_rows__L{r}` on the row `chain·g^(64q)`; it returns that call's return, the last row
(`rs_eq_run_holds`).

The rows from the chunks and back: `rows_of_chunks`, `chunks_of_rows` (chunk `t` is coordinates
`8t ..` and row `t`, `ChunkOk`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- `rs_eq_run`'s statements up to its chain's allocation: the count's bits, `r_g`, `q_g`, the
check `q_g^8·r_g = count_g`, and the chain's `64 (q + 2)` words. -/
def rsHead : List Stmt :=
  [.atom (.hint (.bitsExp (.n 2) 6 (.stack [.n 3, .n 4, .n 5, .n 6, .n 7, .n 8]))),
    .atom (.mul (.n 3) (.n 3) (.n 3)), .atom (.const (.n 9) (word 1 0)),
    .atom (.const (.n 10) (word 3 0)), .atom (.mul (.n 11) (.n 3) (.n 10)),
    .atom (.add (.n 12) (.n 9) (.n 11)), .atom (.mul (.n 4) (.n 4) (.n 4)),
    .atom (.const (.n 13) (word 1 0)), .atom (.const (.n 14) (word 5 0)),
    .atom (.mul (.n 15) (.n 4) (.n 14)), .atom (.add (.n 16) (.n 13) (.n 15)),
    .atom (.mul (.n 17) (.n 12) (.n 16)), .atom (.mul (.n 5) (.n 5) (.n 5)),
    .atom (.const (.n 18) (word 1 0)), .atom (.const (.n 19) (word 17 0)),
    .atom (.mul (.n 20) (.n 5) (.n 19)), .atom (.add (.n 21) (.n 18) (.n 20)),
    .atom (.mul (.n 22) (.n 17) (.n 21)), .atom (.mul (.n 6) (.n 6) (.n 6)),
    .atom (.const (.n 23) (word 1 0)), .atom (.const (.n 24) (word 3 0)),
    .atom (.mul (.n 25) (.n 6) (.n 24)), .atom (.add (.n 26) (.n 23) (.n 25)),
    .atom (.mul (.n 7) (.n 7) (.n 7)), .atom (.const (.n 27) (word 1 0)),
    .atom (.const (.n 28) (word 5 0)), .atom (.mul (.n 29) (.n 7) (.n 28)),
    .atom (.add (.n 30) (.n 27) (.n 29)), .atom (.mul (.n 31) (.n 26) (.n 30)),
    .atom (.mul (.n 8) (.n 8) (.n 8)), .atom (.const (.n 32) (word 1 0)),
    .atom (.const (.n 33) (word 17 0)), .atom (.mul (.n 34) (.n 8) (.n 33)),
    .atom (.add (.n 35) (.n 32) (.n 34)), .atom (.mul (.n 36) (.n 31) (.n 35)),
    .atom (.mul (.n 37) (.n 36) (.n 36)), .atom (.mul (.n 38) (.n 37) (.n 37)),
    .atom (.mul (.n 39) (.n 38) (.n 38)), .atom (.mul (.n 40) (.n 39) (.n 22)),
    .atom (.assertEq (.n 40) (.n 2)), .atom (.const (.n 41) (word 4 0)),
    .atom (.mul (.n 42) (.n 36) (.n 41)), .atom (.mul (.n 43) (.n 42) (.n 42)),
    .atom (.mul (.n 44) (.n 43) (.n 43)), .atom (.mul (.n 45) (.n 44) (.n 44)),
    .atom (.mul (.n 46) (.n 45) (.n 45)), .atom (.mul (.n 47) (.n 46) (.n 46)),
    .atom (.mul (.n 48) (.n 47) (.n 47)), .atom (.hint (.allocDyn (.n 49) (.n 48)))]

/-- Row `0` of the chain: its `64` ones. -/
def rsOne (k : ℕ) : List Stmt :=
  [.atom (.const (.n (50 + k)) (word 1 0)), .atom (.load (.n (50 + k)) (.n 49) k)]

/-- `rs_eq_run`'s stores of row `0`. -/
def rsOnes : List Stmt := ((List.range 64).map rsOne).flatten

/-- `rs_eq_run`'s statements after row `0`: `rs_eq_run_loop0` over the full chunks, the
remainder's `rs_eq_rows__L{r}` on the row `chain·g^(64q)`, its return copied and returned. -/
def rsTail : List Stmt :=
  [.atom (.const (.n 114) (word 1 0)), .atom (.add (.n 115) (.n 114) (.n 36)),
    .atom (.const (.n 116) (word 1 0)),
    .callIf (.n 115) name% «rs_eq_run_loop0» [.n 116, .n 36, .n 49, .n 0, .n 1],
    .atom (.mul (.n 117) (.n 36) (.n 36)), .atom (.mul (.n 118) (.n 117) (.n 117)),
    .atom (.mul (.n 119) (.n 118) (.n 118)), .atom (.mul (.n 120) (.n 36) (.n 36)),
    .atom (.mul (.n 121) (.n 120) (.n 120)), .atom (.mul (.n 122) (.n 121) (.n 121)),
    .atom (.mul (.n 123) (.n 122) (.n 122)), .atom (.mul (.n 124) (.n 123) (.n 123)),
    .atom (.mul (.n 125) (.n 124) (.n 124)), .atom (.mul (.n 126) (.n 49) (.n 125)),
    .atom (.mul (.n 127) (.n 0) (.n 119)), .atom (.mul (.n 128) (.n 1) (.n 119)),
    .dispatch (.n 22) ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3",
      "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"] [.n 126, .n 127, .n 128]
      [.n 129],
    .atom (.copy (.n 130) (.n 129)), .ret [.n 130]]

/-- The expansion of `rs_eq_run`. -/
def rsBody : List Stmt := rsHead ++ rsOnes ++ rsTail

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

theorem rsHead_noRet : Stmt.noRetList rsHead = true := rfl

theorem rsOnes_noRet : Stmt.noRetList rsOnes = true := by decide +kernel

/-- Row `0`'s stores hold exactly when the chain holds `64` ones. -/
theorem rsOnes_holds {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    Stmt.HoldsList C rd σ rsOnes True kret ↔
      (∀ k < 64, σ (.n (50 + k)) = word 1 0 ∧ LoadHolds rd (σ (.n 49)) k (σ (.n (50 + k)))) := by
  rw [rsOnes, holdsList_flatten _ (fun b hb ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb; rfl)]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, and_true, rsOne, Stmt.HoldsList, Stmt.Holds, Atom.Holds]

theorem rsOnes_reads {rd : Reader} {σ : Val}
    (h : ∀ k < 64, σ (.n (50 + k)) = word 1 0 ∧ LoadHolds rd (σ (.n 49)) k (σ (.n (50 + k)))) :
    ReadsAt rd (σ (.n 49)) (List.replicate 64 1) := by
  intro i hi
  simp only [List.length_replicate] at hi
  obtain ⟨e, l⟩ := h i hi
  rw [e, word_one] at l
  rwa [List.getElem_replicate]

/-- **`rs_eq_run`'s core IR computes its meaning.** -/
theorem rs_eq_run_sound (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "rs_eq_run" args rets) : MeaningRsEqRun rd args rets := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  rw [rel_iff_sem find_rs_eq_run, show Fn.params fn% «rs_eq_run» = [.n 0, .n 1, .n 2] from rfl,
    rs_eq_run_body, rsBody] at h
  simp only [holdsList_append] at h
  obtain ⟨σ, hp, h⟩ := h
  rw [holdsList_noRet _ rsHead_noRet, holdsList_noRet _ rsOnes_noRet, rsOnes_holds] at h
  obtain ⟨hH, hO, hT⟩ := h
  have hones := rsOnes_reads hO
  simp only [rsHead, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true] at hH
  simp only [rsTail, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hT
  obtain ⟨b0, h9, h10, h11, h12, b1, h13, h14, h15, h16, h17, b2, h18, h19, h20, h21, h22,
    b3, h23, h24, h25, h26, b4, h27, h28, h29, h30, h31, b5, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, ha, -, -, -, -, -, -, -, -⟩ := hH
  obtain ⟨h114, h115, h116, hK, hcall, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126,
    h127, h128, ⟨j, hj, hx, hdisp⟩, h130, hret⟩ := hT
  subst hp
  have hbr : ∀ j < 3, σ (.n (3 + j)) * σ (.n (3 + j)) = σ (.n (3 + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm]
  have hbq : ∀ j < 3, σ (.n (6 + j)) * σ (.n (6 + j)) = σ (.n (6 + j)) := by
    intro j hj; interval_cases j
    exacts [b3.symm, b4.symm, b5.symm]
  have rg : σ (.n 22) = ∏ j ∈ Finset.range 3, (1 + σ (.n (3 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h22, h17, h12, h16, h21, h11, h15, h20, h9, h13, h18, h10, h14, h19, w3, w5, w17, word_one]
  have qg : σ (.n 36) = ∏ j ∈ Finset.range 3, (1 + σ (.n (6 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h36, h31, h26, h30, h35, h25, h29, h34, h23, h27, h32, h24, h28, h33, w3, w5, w17, word_one]
  rw [prod_gen_pow_of_bool hbr] at rg
  rw [prod_gen_pow_of_bool hbq] at qg
  set r := bitsVal (fun j ↦ decide (σ (.n (3 + j)) = 1)) 3 with hrdef
  set q := bitsVal (fun j ↦ decide (σ (.n (6 + j)) = 1)) 3 with hqdef
  have hr8 : r < 8 := bitsVal_lt _ 3
  have hq8 : q < 8 := bitsVal_lt _ 3
  have hcg : σ (.n 2) = gen ^ (8 * q + r) := by
    rw [← e_add_eq_zero_iff.mp ha, h40, h39, h38, h37, qg, rg, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    congr 1; ring
  -- the loop over the full chunks
  rw [h115, h114, word_one] at hK hcall
  rw [h116, word_one] at hcall
  obtain ⟨m, hm, hm', hB⟩ := (guarded_loop_rel_iff
    (fun d x ↦ loop5_sound rd (σ (.n 36)) (σ (.n 49)) (σ (.n 0)) (σ (.n 1)) d x)
    (fun x hb hk hn ↦ loop5_complete rd _ _ _ _ x hb hk hn)).mp ⟨hK, hcall⟩
  have hmq : m = q := by
    rw [qg] at hm'
    exact gen_pow_inj hm (by show q < 2 ^ 64 - 1; omega) hm'.symm
  subst hmq
  have hch : ∀ t < q, ∃ zt pt ct, zt.length = 8 ∧ pt.length = 8 ∧
      ChunkOk rd (σ (.n 49)) (σ (.n 0)) (σ (.n 1)) t zt pt ct := fun t ht ↦ by
    obtain ⟨ret, hr⟩ := hB t ht
    rw [← pow_mul, ← pow_mul, Nat.mul_comm t 64, Nat.mul_comm t 8] at hr
    obtain ⟨zt, pt, ct, a, b, c, -⟩ :=
      chunk_of_meaning (by norm_num) ((rs_eq_rows_holds 8 le_rfl rd _ _).1 hr)
    exact ⟨zt, pt, ct, a, b, c⟩
  choose! Zc Pc Cc hZc hPc hCc using hch
  -- the remainder
  have hj' : j = r := by
    rw [rg, gen_pow_eq_ofK] at hx
    exact gen_pow_inj (by simp only [List.length_cons, List.length_nil] at hj; show j < 2 ^ 64 - 1; omega) (by show r < 2 ^ 64 - 1; omega)
      (by rw [gen_pow_eq_ofK, gen_pow_eq_ofK]; exact hx.symm)
  subst hj'
  rw [rsNames_get _ hj] at hdisp
  have e125 : σ (.n 125) = gen ^ (64 * q) := by
    rw [h125, h124, h123, h122, h121, h120, qg]; ring
  have e119 : σ (.n 119) = gen ^ (8 * q) := by rw [h119, h118, h117, qg]; ring
  rw [h126, h127, h128, e125, e119] at hdisp
  have hm8 := (rs_eq_rows_holds r (by omega) rd _ _).1 hdisp
  obtain ⟨Zl, Pl, Cl, hZl, hPl, hl, h129⟩ : ∃ Zl Pl Cl, Zl.length = r ∧ Pl.length = r ∧
      (0 < r → ChunkOk rd (σ (.n 49)) (σ (.n 0)) (σ (.n 1)) q Zl Pl Cl) ∧
      σ (.n 129) = σ (.n 49) * gen ^ (64 * ((8 * q + r + 7) / 8)) := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rcases hm8 with ⟨-, hr⟩ | ⟨h, -⟩
      · simp only [List.cons.injEq, and_true] at hr
        refine ⟨[], [], [], by simp [h0], by simp [h0], fun h ↦ absurd h (by omega), ?_⟩
        rw [hr, show (8 * q + r + 7) / 8 = q by omega]
      · omega
    · obtain ⟨zt, pt, ct, a, b, c, d⟩ := chunk_of_meaning h0 hm8
      refine ⟨zt, pt, ct, a, b, fun _ ↦ c, ?_⟩
      rw [d, mul_assoc, ← pow_add, show (8 * q + r + 7) / 8 = q + 1 by omega]
      ring_nf
  let Z : ℕ → List E := fun t ↦ if t < q then Zc t else Zl
  let P : ℕ → List E := fun t ↦ if t < q then Pc t else Pl
  let C : ℕ → List E := fun t ↦ if t < q then Cc t else Cl
  obtain ⟨lz, lp, lc, rz, rp, rc, rows⟩ := rows_of_chunks (rd := rd) (chain := σ (.n 49))
    (z := σ (.n 0)) (p := σ (.n 1)) (q := q) (r := r) (by omega) Z P C
    (fun t ht ↦ by simp only [Z, ite_pos' ht]; exact hZc t ht)
    (fun t ht ↦ by simp only [P, ite_pos' ht]; exact hPc t ht)
    (by simp only [Z, ite_neg' (lt_irrefl q)]; exact hZl)
    (by simp only [P, ite_neg' (lt_irrefl q)]; exact hPl)
    (fun t ht ↦ by simp only [Z, P, C, ite_pos' ht]; exact hCc t ht)
    (fun h ↦ by simp only [Z, P, C, ite_neg' (lt_irrefl q)]; exact hl h)
  refine ⟨8 * q + r, by omega, hcg, _, _, lz, lp, rz, rp, σ (.n 49), hones,
    fun h h1 h2 k hk ↦ ?_, ?_⟩
  · -- row `0` is the ones
    have h1k : (List.map (fun k ↦ (C 0).getD k 0) (List.range 64)).getD k 0 = 1 := by
      have e := readsAt_getD (rc (by omega)) (i := k) (by simp; omega)
      have o := readsAt_getD hones (i := k) (by simp; omega)
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate] at o
      exact loadHolds_unique e o
    have := rows h h1 h2 k hk
    rwa [h1k] at this
  · rw [← hret, h130, h129]

/-- `g^(Σ bits)` from the three hinted bits, as the template multiplies them. -/
theorem prod_three_bits (r : ℕ) (hr : r < 8) :
    (1 + bitE (r.testBit 0) * (gen ^ 2 ^ 0 + 1)) * (1 + bitE (r.testBit 1) * (gen ^ 2 ^ 1 + 1)) *
      (1 + bitE (r.testBit 2) * (gen ^ 2 ^ 2 + 1)) = gen ^ r := by
  have := prod_bitE_gen_pow r.testBit 3
  rw [bitsVal_testBit (show r < 2 ^ 3 by omega), Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at this
  exact this

/-- **The words `rs_eq_run` runs on**: `count` coordinates `zs` at `z` and `ps` at `p`, the chain at
`chain` with row `0` ones and row `h`, `1 ≤ h ≤ ⌈count/8⌉`, the products over the first
`min(8h, count)` coordinates. -/
def RsMem (rd : Reader) (z p chain : E) (count : ℕ) (zs ps : List E) : Prop :=
  zs.length = count ∧ ps.length = count ∧ ReadsAt rd z zs ∧ ReadsAt rd p ps ∧
    ReadsAt rd chain (List.replicate 64 1) ∧
    ∀ h, 1 ≤ h → h ≤ (count + 7) / 8 → ∀ k < 64, LoadHolds rd chain (64 * h + k)
      (ringRow 1 (zs.take (min (8 * h) count)) (ps.take (min (8 * h) count)) k)

/-- **`rs_eq_run`'s callees on its words**: `rs_eq_run_loop0` over the `count / 8` full chunks
(guarded by `1 + g^(count / 8)`), the remainder's `rs_eq_rows__L{count % 8}` returning the last
row. -/
theorem rs_kids_rel {rd : Reader} {z p chain : E} {count : ℕ} {zs ps : List E} (hcount : count < 64)
    (hm : RsMem rd z p chain count zs ps) :
    (IsInK (1 + gen ^ (count / 8)) ∧ (1 + gen ^ (count / 8) ≠ 0 →
      coreProgram.Rel rd name% «rs_eq_run_loop0» [1, gen ^ (count / 8), chain, z, p] [])) ∧
    coreProgram.Rel rd (rsEqRowsNames.getD (count % 8) "")
      [chain * gen ^ (64 * (count / 8)), z * gen ^ (8 * (count / 8)), p * gen ^ (8 * (count / 8))]
      [chain * gen ^ (64 * ((count + 7) / 8))] := by
  obtain ⟨lz, lp, hz, hpp, hones, hr⟩ := hm
  have hch := chunks_of_rows (c := List.replicate 64 1) lz lp (by simp) hz hpp (fun _ ↦ hones)
    (fun h h1 h2 k hk ↦ by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate]
      exact hr h h1 h2 k hk)
  obtain ⟨q, hq⟩ : ∃ q, q = count / 8 := ⟨_, rfl⟩
  obtain ⟨r, hr8⟩ : ∃ r, r = count % 8 := ⟨_, rfl⟩
  rw [← hq, ← hr8]
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
  refine ⟨hloop, ?_⟩
  -- the remainder
  refine (rs_eq_rows_holds r (by omega) rd _ _).2 ?_
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · exact Or.inl ⟨h0, by rw [show (count + 7) / 8 = q by omega]⟩
  · have hok := hch q (by omega)
    refine Or.inr ⟨h0, _, _, _, ?_, ?_, hok.2.2.1, hok.1, hok.2.1, hok.2.2.2.1, hok.2.2.2.2, ?_⟩
    · simp only [List.length_take, List.length_drop, lz]; omega
    · simp only [List.length_take, List.length_drop, lp]; omega
    · rw [show (count + 7) / 8 = q + 1 by omega, mul_assoc, ← pow_add]
      ring_nf

/-- **The honest valuation of `rs_eq_run`'s body** on the coordinates at `z`, the point at `p`, the
chain at `chain` and the count `count`: the bits of `count % 8` and `count / 8`, the chain's size,
row `0`'s ones, the remainder's row pointers and its return, the last row. -/
noncomputable def rsW (z p chain : E) (count : ℕ) : List E :=
  let q := count / 8
  let r := count % 8
  let b : ℕ → E := fun j ↦ bitE (r.testBit j)
  let b' : ℕ → E := fun j ↦ bitE (q.testBit j)
  let u13 := word 1 0 + b 0 * word 3 0
  let u17 := word 1 0 + b 1 * word 5 0
  let u22 := word 1 0 + b 2 * word 17 0
  let u23 := u13 * u17 * u22
  let u27 := word 1 0 + b' 0 * word 3 0
  let u31 := word 1 0 + b' 1 * word 5 0
  let u36 := word 1 0 + b' 2 * word 17 0
  let u37 := u27 * u31 * u36
  let s40 := u37 * u37 * (u37 * u37) * (u37 * u37 * (u37 * u37))
  let x42 := u37 * word 4 0
  let x45 := x42 * x42 * (x42 * x42) * (x42 * x42 * (x42 * x42))
  let x48 := x45 * x45 * (x45 * x45) * (x45 * x45 * (x45 * x45))
  let t47 := u37 * u37 * (u37 * u37) * (u37 * u37 * (u37 * u37))
  let t50 := u37 * u37 * (u37 * u37) * (u37 * u37 * (u37 * u37))
  let t53 := t50 * t50 * (t50 * t50) * (t50 * t50 * (t50 * t50))
  let res := chain * gen ^ (64 * ((count + 7) / 8))
  [z, p, gen ^ count, b 0, b 1, b 2, b' 0, b' 1, b' 2,
    word 1 0, word 3 0, b 0 * word 3 0, u13, word 1 0, word 5 0, b 1 * word 5 0, u17,
    u13 * u17, word 1 0, word 17 0, b 2 * word 17 0, u22, u23,
    word 1 0, word 3 0, b' 0 * word 3 0, u27, word 1 0, word 5 0, b' 1 * word 5 0, u31,
    u27 * u31, word 1 0, word 17 0, b' 2 * word 17 0, u36, u37,
    u37 * u37, u37 * u37 * (u37 * u37), s40, s40 * u23, word 4 0, x42, x42 * x42,
    x42 * x42 * (x42 * x42), x45, x45 * x45, x45 * x45 * (x45 * x45), x48, chain] ++
    List.replicate 64 (word 1 0) ++
    [word 1 0, word 1 0 + u37, word 1 0,
    u37 * u37, u37 * u37 * (u37 * u37), t47, u37 * u37, u37 * u37 * (u37 * u37), t50, t50 * t50,
    t50 * t50 * (t50 * t50), t53, chain * t53, z * t47, p * t47, res, res]

/-- The honest valuation, as a valuation. -/
noncomputable def rsVal (z p chain : E) (count : ℕ) : Val := Val.ofArgs (rsW z p chain count)

/-- **The honest valuation's words**: the parameters, `q_g`, `r_g`, the chain and its size, the
loop's guard and start, the remainder's pointers and the return. -/
theorem rsVal_vals (z p chain : E) {count : ℕ} (hcount : count < 64) :
    let σ := rsVal z p chain count
    σ (.n 0) = z ∧ σ (.n 1) = p ∧ σ (.n 2) = gen ^ count ∧ σ (.n 36) = gen ^ (count / 8) ∧
      σ (.n 22) = gen ^ (count % 8) ∧ σ (.n 48) = gen ^ (64 * (count / 8 + 2)) ∧
      σ (.n 49) = chain ∧ σ (.n 115) = 1 + gen ^ (count / 8) ∧ σ (.n 116) = 1 ∧
      σ (.n 126) = chain * gen ^ (64 * (count / 8)) ∧ σ (.n 127) = z * gen ^ (8 * (count / 8)) ∧
      σ (.n 128) = p * gen ^ (8 * (count / 8)) ∧
      σ (.n 129) = chain * gen ^ (64 * ((count + 7) / 8)) ∧
      σ (.n 130) = chain * gen ^ (64 * ((count + 7) / 8)) ∧
      ∀ k < 64, σ (.n (50 + k)) = 1 := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  have w4 : word 4 0 = gen ^ 2 := word_two_pow (a := 2) (by norm_num)
  have e37 : (word 1 0 + bitE ((count / 8).testBit 0) * word 3 0) *
      (word 1 0 + bitE ((count / 8).testBit 1) * word 5 0) *
      (word 1 0 + bitE ((count / 8).testBit 2) * word 17 0) = gen ^ (count / 8) := by
    rw [← prod_three_bits (count / 8) (by omega), ← w3, ← w5, ← w17, ← word_one]
  have e23 : (word 1 0 + bitE ((count % 8).testBit 0) * word 3 0) *
      (word 1 0 + bitE ((count % 8).testBit 1) * word 5 0) *
      (word 1 0 + bitE ((count % 8).testBit 2) * word 17 0) = gen ^ (count % 8) := by
    rw [← prod_three_bits (count % 8) (by omega), ← w3, ← w5, ← w17, ← word_one]
  intro σ
  refine ⟨rfl, rfl, rfl, e37, e23, ?_, rfl, ?_, word_one, ?_, ?_, ?_, rfl, rfl, fun k hk ↦ ?_⟩
  · show _ * _ * (_ * _) * (_ * _ * (_ * _)) * (_ * _ * (_ * _) * (_ * _ * (_ * _))) = _
    simp only [e37, w4]; ring
  · show word 1 0 + _ = _
    rw [e37, word_one]
  · show chain * (_ * _ * (_ * _) * (_ * _ * (_ * _))) = _
    simp only [e37]; ring
  · show z * (_ * _ * (_ * _) * (_ * _ * (_ * _))) = _
    simp only [e37]; ring
  · show p * (_ * _ * (_ * _) * (_ * _ * (_ * _))) = _
    simp only [e37]; ring
  · show (rsW z p chain count).getD (50 + k) 0 = 1
    rw [← word_one]
    interval_cases k <;> rfl

/-- **The honest valuation satisfies `rs_eq_run`'s body** on its words (`RsMem`), returning the
last row. -/
theorem rsVal_holds {rd : Reader} {z p chain : E} {count : ℕ} {zs ps : List E} (hcount : count < 64)
    (hm : RsMem rd z p chain count zs ps) :
    Stmt.HoldsList (coreProgram.Rel rd) rd (rsVal z p chain count) rsBody False
      (fun rs ↦ rs = [chain * gen ^ (64 * ((count + 7) / 8))]) := by
  obtain ⟨hloop, hdisp⟩ := rs_kids_rel hcount hm
  obtain ⟨-, -, -, -, hones, -⟩ := hm
  obtain ⟨-, -, -, e36, e22, -, -, e115, e116, e126, e127, e128, -, -, e50⟩ :=
    rsVal_vals z p chain hcount
  rw [rsBody, holdsList_append, holdsList_append]
  rw [holdsList_noRet _ rsHead_noRet, holdsList_noRet _ rsOnes_noRet, rsOnes_holds]
  refine ⟨?_, fun k hk ↦ ⟨?_, ?_⟩, ?_⟩
  · simp only [rsHead, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true]
    refine ⟨(bitE_mul_self _).symm, rfl, rfl, rfl, rfl, (bitE_mul_self _).symm,
      rfl, rfl, rfl, rfl, rfl, (bitE_mul_self _).symm, rfl, rfl, rfl, rfl, rfl,
      (bitE_mul_self _).symm, rfl, rfl, rfl, rfl, (bitE_mul_self _).symm, rfl, rfl, rfl, rfl, rfl,
      (bitE_mul_self _).symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
    show rsVal z p chain count (.n 39) * rsVal z p chain count (.n 22) + gen ^ count = 0
    have e39 : rsVal z p chain count (.n 39) =
        rsVal z p chain count (.n 36) * rsVal z p chain count (.n 36) *
          (rsVal z p chain count (.n 36) * rsVal z p chain count (.n 36)) *
          (rsVal z p chain count (.n 36) * rsVal z p chain count (.n 36) *
            (rsVal z p chain count (.n 36) * rsVal z p chain count (.n 36))) := rfl
    rw [e39, e36, e22, e_add_eq_zero_iff, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1; omega
  · rw [e50 k hk, word_one]
  · rw [e50 k hk]
    have := readsAt_getD hones (i := k) (by simp; omega)
    rwa [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate] at this
  · simp only [rsTail, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨count % 8, by simp only [List.length_cons, List.length_nil]; omega, ?_, ?_⟩, rfl, rfl⟩
    · rw [e115]; exact hloop.1
    · rw [e115, e116, e36]
      exact hloop.2
    · rw [e22, gen_pow_eq_ofK]
    · rw [rsNames_get (count % 8) (by omega), e126, e127, e128]
      exact hdisp

/-- **`rs_eq_run`'s meaning gives its core IR**: the honest valuation (`rsVal_holds`). -/
theorem rs_eq_run_complete (rd : Reader) (args rets : List E) (hm : MeaningRsEqRun rd args rets) :
    coreProgram.Rel rd "rs_eq_run" args rets := by
  obtain ⟨z, p, cg, rfl⟩ : ∃ z p cg, args = [z, p, cg] := by
    match args, hm with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  obtain ⟨count, hcount, rfl, zs, ps, lz, lp, hz, hpp, chain, hones, hr, rfl⟩ := hm
  rw [rel_iff_sem find_rs_eq_run, show Fn.params fn% «rs_eq_run» = [.n 0, .n 1, .n 2] from rfl,
    rs_eq_run_body]
  exact ⟨rsVal z p chain count, rfl, rsVal_holds hcount ⟨lz, lp, hz, hpp, hones, hr⟩⟩

/-- **`rs_eq_run`'s core IR is its meaning.** -/
theorem rs_eq_run_holds : rs_eq_run_Spec := fun rd args rets ↦
  ⟨rs_eq_run_sound rd args rets, rs_eq_run_complete rd args rets⟩

end
end LeanVM.Guest.B1
