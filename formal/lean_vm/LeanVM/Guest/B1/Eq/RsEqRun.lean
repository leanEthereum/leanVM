/-
  LeanVM.Guest.B1.Eq.RsEqRun

  B1 for `rs_eq_run`: the telescoped ring-switch rows, eight coordinates a row.
-/

module

public import LeanVM.Guest.B1.Eq.RsLoop
public import LeanVM.Guest.B1.Bits.GPower
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«rs_eq_run»
import LeanVM.Guest.Value.FieldBits
import LeanVM.ToMathlib.List

/-!
# `rs_eq_run` (lean_ethereum.py)

`rs_eq_run(z_vals, point1, count_g, seed)` hints the six bits of `count` (`count_g = g^count`),
pins them by booleanity and `q_g^8 · r_g = count_g` (`r_g` from bits `0 .. 2`, `q_g` from bits
`3 .. 5`, so `count = 8q + r`), allocates its chain (`HeapBuf` of `64 (q + 2)` words, `rsAlloc`),
writes row `0` from the seed (`rsInits`), runs `rs_eq_run_loop0` over the `q` full chunks
(`rs_eq_rows__L8` each), and dispatches the remainder's `rs_eq_rows__L{r}` on the row
`chain·g^(64q)`; it returns that call's return, the last row (`rs_eq_run_sound`).

The rows from the chunks and back: `rows_of_chunks`, `chunks_of_rows` (chunk `t` is coordinates
`8t ..` and row `t`, `ChunkOk`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- `rs_eq_run`'s atoms before its chain: the count's bits, `r_g`, `q_g`, the check. -/
def rsA : List Stmt :=
  [.atom (.hint (.bitsExp (.n (val% «rs_eq_run» "count_g")) 6 (.stack [.n (val% «rs_eq_run» "bits[0]"), .n (val% «rs_eq_run» "bits[1]"), .n (val% «rs_eq_run» "bits[2]"), .n (val% «rs_eq_run» "bits[3]"), .n (val% «rs_eq_run» "bits[4]"), .n (val% «rs_eq_run» "bits[5]")]))),
    .atom (.mul (.n (val% «rs_eq_run» "bits[0]")) (.n (val% «rs_eq_run» "bits[0]")) (.n (val% «rs_eq_run» "bits[0]"))), .atom (.const (.n (val% «rs_eq_run» "r_g@1~0")) (word 1 0)),
    .atom (.const (.n (val% «rs_eq_run» "r_g@1~1")) (word 3 0)), .atom (.mul (.n (val% «rs_eq_run» "r_g@1~2")) (.n (val% «rs_eq_run» "bits[0]")) (.n (val% «rs_eq_run» "r_g@1~1"))),
    .atom (.add (.n (val% «rs_eq_run» "r_g@1")) (.n (val% «rs_eq_run» "r_g@1~0")) (.n (val% «rs_eq_run» "r_g@1~2"))), .atom (.mul (.n (val% «rs_eq_run» "bits[1]")) (.n (val% «rs_eq_run» "bits[1]")) (.n (val% «rs_eq_run» "bits[1]"))),
    .atom (.const (.n (val% «rs_eq_run» "r_g@2~0")) (word 1 0)), .atom (.const (.n (val% «rs_eq_run» "r_g@2~1")) (word 5 0)),
    .atom (.mul (.n (val% «rs_eq_run» "r_g@2~2")) (.n (val% «rs_eq_run» "bits[1]")) (.n (val% «rs_eq_run» "r_g@2~1"))), .atom (.add (.n (val% «rs_eq_run» "r_g@2~3")) (.n (val% «rs_eq_run» "r_g@2~0")) (.n (val% «rs_eq_run» "r_g@2~2"))),
    .atom (.mul (.n (val% «rs_eq_run» "r_g@2")) (.n (val% «rs_eq_run» "r_g@1")) (.n (val% «rs_eq_run» "r_g@2~3"))), .atom (.mul (.n (val% «rs_eq_run» "bits[2]")) (.n (val% «rs_eq_run» "bits[2]")) (.n (val% «rs_eq_run» "bits[2]"))),
    .atom (.const (.n (val% «rs_eq_run» "r_g@3~0")) (word 1 0)), .atom (.const (.n (val% «rs_eq_run» "r_g@3~1")) (word 17 0)),
    .atom (.mul (.n (val% «rs_eq_run» "r_g@3~2")) (.n (val% «rs_eq_run» "bits[2]")) (.n (val% «rs_eq_run» "r_g@3~1"))), .atom (.add (.n (val% «rs_eq_run» "r_g@3~3")) (.n (val% «rs_eq_run» "r_g@3~0")) (.n (val% «rs_eq_run» "r_g@3~2"))),
    .atom (.mul (.n (val% «rs_eq_run» "r_g@3")) (.n (val% «rs_eq_run» "r_g@2")) (.n (val% «rs_eq_run» "r_g@3~3"))), .atom (.mul (.n (val% «rs_eq_run» "bits[3]")) (.n (val% «rs_eq_run» "bits[3]")) (.n (val% «rs_eq_run» "bits[3]"))),
    .atom (.const (.n (val% «rs_eq_run» "q_g@1~0")) (word 1 0)), .atom (.const (.n (val% «rs_eq_run» "q_g@1~1")) (word 3 0)),
    .atom (.mul (.n (val% «rs_eq_run» "q_g@1~2")) (.n (val% «rs_eq_run» "bits[3]")) (.n (val% «rs_eq_run» "q_g@1~1"))), .atom (.add (.n (val% «rs_eq_run» "q_g@1")) (.n (val% «rs_eq_run» "q_g@1~0")) (.n (val% «rs_eq_run» "q_g@1~2"))),
    .atom (.mul (.n (val% «rs_eq_run» "bits[4]")) (.n (val% «rs_eq_run» "bits[4]")) (.n (val% «rs_eq_run» "bits[4]"))), .atom (.const (.n (val% «rs_eq_run» "q_g@2~0")) (word 1 0)),
    .atom (.const (.n (val% «rs_eq_run» "q_g@2~1")) (word 5 0)), .atom (.mul (.n (val% «rs_eq_run» "q_g@2~2")) (.n (val% «rs_eq_run» "bits[4]")) (.n (val% «rs_eq_run» "q_g@2~1"))),
    .atom (.add (.n (val% «rs_eq_run» "q_g@2~3")) (.n (val% «rs_eq_run» "q_g@2~0")) (.n (val% «rs_eq_run» "q_g@2~2"))), .atom (.mul (.n (val% «rs_eq_run» "q_g@2")) (.n (val% «rs_eq_run» "q_g@1")) (.n (val% «rs_eq_run» "q_g@2~3"))),
    .atom (.mul (.n (val% «rs_eq_run» "bits[5]")) (.n (val% «rs_eq_run» "bits[5]")) (.n (val% «rs_eq_run» "bits[5]"))), .atom (.const (.n (val% «rs_eq_run» "q_g@3~0")) (word 1 0)),
    .atom (.const (.n (val% «rs_eq_run» "q_g@3~1")) (word 17 0)), .atom (.mul (.n (val% «rs_eq_run» "q_g@3~2")) (.n (val% «rs_eq_run» "bits[5]")) (.n (val% «rs_eq_run» "q_g@3~1"))),
    .atom (.add (.n (val% «rs_eq_run» "q_g@3~3")) (.n (val% «rs_eq_run» "q_g@3~0")) (.n (val% «rs_eq_run» "q_g@3~2"))), .atom (.mul (.n (val% «rs_eq_run» "q_g@3")) (.n (val% «rs_eq_run» "q_g@2")) (.n (val% «rs_eq_run» "q_g@3~3"))),
    .atom (.mul (.n (val% «rs_eq_run» "s0.i0:split_count.s5#0")) (.n (val% «rs_eq_run» "q_g@3")) (.n (val% «rs_eq_run» "q_g@3"))), .atom (.mul (.n (val% «rs_eq_run» "s0.i0:split_count.s5#1")) (.n (val% «rs_eq_run» "s0.i0:split_count.s5#0")) (.n (val% «rs_eq_run» "s0.i0:split_count.s5#0"))),
    .atom (.mul (.n (val% «rs_eq_run» "s0.i0:split_count.s5#2")) (.n (val% «rs_eq_run» "s0.i0:split_count.s5#1")) (.n (val% «rs_eq_run» "s0.i0:split_count.s5#1"))), .atom (.mul (.n (val% «rs_eq_run» "s0.i0:split_count.s5#3")) (.n (val% «rs_eq_run» "s0.i0:split_count.s5#2")) (.n (val% «rs_eq_run» "r_g@3"))),
    .atom (.assertEq (.n (val% «rs_eq_run» "s0.i0:split_count.s5#3")) (.n (val% «rs_eq_run» "count_g")))]

/-- Its chain, a `HeapBuf` of `64 (q + 2)` words, `(q_g·g^2)^64`. -/
def rsAlloc : List Stmt :=
  [.atom (.const (.n (val% «rs_eq_run» "chain~0")) (word 4 0)), .atom (.mul (.n (val% «rs_eq_run» "chain~1")) (.n (val% «rs_eq_run» "q_g@3")) (.n (val% «rs_eq_run» "chain~0"))),
    .atom (.mul (.n (val% «rs_eq_run» "chain~2")) (.n (val% «rs_eq_run» "chain~1")) (.n (val% «rs_eq_run» "chain~1"))),
    .atom (.mul (.n (val% «rs_eq_run» "chain~3")) (.n (val% «rs_eq_run» "chain~2")) (.n (val% «rs_eq_run» "chain~2"))),
    .atom (.mul (.n (val% «rs_eq_run» "chain~4")) (.n (val% «rs_eq_run» "chain~3")) (.n (val% «rs_eq_run» "chain~3"))),
    .atom (.mul (.n (val% «rs_eq_run» "chain~5")) (.n (val% «rs_eq_run» "chain~4")) (.n (val% «rs_eq_run» "chain~4"))),
    .atom (.mul (.n (val% «rs_eq_run» "chain~6")) (.n (val% «rs_eq_run» "chain~5")) (.n (val% «rs_eq_run» "chain~5"))),
    .atom (.mul (.n (val% «rs_eq_run» "chain~7")) (.n (val% «rs_eq_run» "chain~6")) (.n (val% «rs_eq_run» "chain~6"))),
    .atom (.hint (.allocDyn (.n (val% «rs_eq_run» "chain")) (.n (val% «rs_eq_run» "chain~7"))))]

/-- Row `0`'s entry `k`: the seed's (`chain[k] = seed[k]`). -/
def rsInit (k : ℕ) : List Stmt :=
  [.atom (.load (.n ((val% «rs_eq_run» "s2.u0.s0#0") + k)) (.n (val% «rs_eq_run» "seed")) k),
    .atom (.load (.n ((val% «rs_eq_run» "s2.u0.s0#0") + k)) (.n (val% «rs_eq_run» "chain")) k)]

/-- Row `0`, the seed. -/
def rsInits : List Stmt := ((List.range 64).map rsInit).flatten

/-- The loop's guard. -/
def rsG : List Stmt :=
  [.atom (.const (.n (val% «rs_eq_run» "s3#0")) (word 1 0)), .atom (.add (.n (val% «rs_eq_run» "s3#1")) (.n (val% «rs_eq_run» "s3#0")) (.n (val% «rs_eq_run» "q_g@3"))), .atom (.const (.n (val% «rs_eq_run» "s3#2")) (word 1 0))]

/-- `rs_eq_run_loop0`'s call and the remainder's pointers. -/
def rsT0 : List Stmt :=
  [.callIf (.n (val% «rs_eq_run» "s3#1")) name% «rs_eq_run_loop0» [.n (val% «rs_eq_run» "s3#2"), .n (val% «rs_eq_run» "q_g@3"), .n (val% «rs_eq_run» "chain"), .n (val% «rs_eq_run» "z_vals"), .n (val% «rs_eq_run» "point1")],
    .atom (.mul (.n (val% «rs_eq_run» "base~0")) (.n (val% «rs_eq_run» "q_g@3")) (.n (val% «rs_eq_run» "q_g@3"))),
    .atom (.mul (.n (val% «rs_eq_run» "base~1")) (.n (val% «rs_eq_run» "base~0")) (.n (val% «rs_eq_run» "base~0"))),
    .atom (.mul (.n (val% «rs_eq_run» "base")) (.n (val% «rs_eq_run» "base~1")) (.n (val% «rs_eq_run» "base~1"))),
    .atom (.mul (.n (val% «rs_eq_run» "row~0")) (.n (val% «rs_eq_run» "q_g@3")) (.n (val% «rs_eq_run» "q_g@3"))),
    .atom (.mul (.n (val% «rs_eq_run» "row~1")) (.n (val% «rs_eq_run» "row~0")) (.n (val% «rs_eq_run» "row~0"))),
    .atom (.mul (.n (val% «rs_eq_run» "row~2")) (.n (val% «rs_eq_run» "row~1")) (.n (val% «rs_eq_run» "row~1"))),
    .atom (.mul (.n (val% «rs_eq_run» "row~3")) (.n (val% «rs_eq_run» "row~2")) (.n (val% «rs_eq_run» "row~2"))),
    .atom (.mul (.n (val% «rs_eq_run» "row~4")) (.n (val% «rs_eq_run» "row~3")) (.n (val% «rs_eq_run» "row~3"))),
    .atom (.mul (.n (val% «rs_eq_run» "row~5")) (.n (val% «rs_eq_run» "row~4")) (.n (val% «rs_eq_run» "row~4"))),
    .atom (.mul (.n (val% «rs_eq_run» "row")) (.n (val% «rs_eq_run» "chain")) (.n (val% «rs_eq_run» "row~5"))),
    .atom (.mul (.n (val% «rs_eq_run» "s6#1")) (.n (val% «rs_eq_run» "z_vals")) (.n (val% «rs_eq_run» "base"))),
    .atom (.mul (.n (val% «rs_eq_run» "s6#2")) (.n (val% «rs_eq_run» "point1")) (.n (val% «rs_eq_run» "base")))]

/-- The remainder's dispatch. -/
def rsD : Stmt :=
  .dispatch (.n (val% «rs_eq_run» "r_g@3")) ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3",
    "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"] [.n (val% «rs_eq_run» "row"), .n (val% «rs_eq_run» "s6#1"), .n (val% «rs_eq_run» "s6#2")] [.n (val% «rs_eq_run» "last")]

/-- `rs_eq_run`'s statements after its chain's row `0`, before its `ret`. -/
def rsT : List Stmt := rsG ++ rsT0 ++ [rsD, .atom (.copy (.n (val% «rs_eq_run» "s7#0")) (.n (val% «rs_eq_run» "last")))]

/-- The expansion of `rs_eq_run`. -/
def rsBody : List Stmt := rsA ++ (rsAlloc ++ (rsInits ++ (rsT ++ [.ret [.n (val% «rs_eq_run» "s7#0")]])))

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
    rw [List.getD_map_range _ hk]
    exact hrow k hk
  · rw [List.getD_map_range _ hk, rsR, ← ringRow_append _ _ _ _ _ _ hlen, ← List.take_add,
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

theorem rsInit_noRet (k : ℕ) : Stmt.noRetList (rsInit k) = true := rfl

/-- What row `0`'s entry `k` asks of a valuation: the chain holds the seed's word there. -/
theorem holds_rsInit {C : CallRel} {rd : Reader} {σ : Val} {k : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (rsInit k) True kret) :
    LoadHolds rd (σ (.n (val% «rs_eq_run» "seed"))) k (σ (.n ((val% «rs_eq_run» "s2.u0.s0#0") + k))) ∧
      LoadHolds rd (σ (.n (val% «rs_eq_run» "chain"))) k (σ (.n ((val% «rs_eq_run» "s2.u0.s0#0") + k))) := by
  simp only [rsInit, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  exact h

/-- **`rs_eq_run`'s core IR computes its meaning.** -/
theorem rs_eq_run_sound (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "rs_eq_run" args rets) : MeaningRsEqRun rd args rets := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  rw [rel_iff_sem find_rs_eq_run, show Fn.params fn% «rs_eq_run» = [.n (val% «rs_eq_run» "z_vals"), .n (val% «rs_eq_run» "point1"), .n (val% «rs_eq_run» "count_g"),
      .n (val% «rs_eq_run» "seed")] from rfl,
    rs_eq_run_body, rsBody] at h
  obtain ⟨σ, hp, h⟩ := h
  subst hp
  simp only [rsA, rsAlloc, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    true_and] at h
  obtain ⟨b0, h10, h11, h12, h13, b1, h14, h15, h16, h17, h18, b2, h19, h20, h21, h22, h23,
    b3, h24, h25, h26, h27, b4, h28, h29, h30, h31, h32, b5, h33, h34, h35, h36, h37, h38, h39,
    h40, h41, ha, -, -, -, -, -, -, -, -, h⟩ := h
  rw [holdsList_append, rsInits, holdsList_range_flatten 64 rsInit rsInit_noRet] at h
  obtain ⟨hinit, h⟩ := h
  simp only [rsT, rsG, rsT0, rsD, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨h42, h43, h44, hK, hcall, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54,
    h55, h56, ⟨j, hj, hx, hdisp⟩, h58, hret⟩ := h
  have hbr : ∀ j < 3, σ (.n ((val% «rs_eq_run» "bits[0]") + j)) * σ (.n ((val% «rs_eq_run» "bits[0]") + j)) = σ (.n ((val% «rs_eq_run» "bits[0]") + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm]
  have hbq : ∀ j < 3, σ (.n ((val% «rs_eq_run» "bits[3]") + j)) * σ (.n ((val% «rs_eq_run» "bits[3]") + j)) = σ (.n ((val% «rs_eq_run» "bits[3]") + j)) := by
    intro j hj; interval_cases j
    exacts [b3.symm, b4.symm, b5.symm]
  have rg : σ (.n (val% «rs_eq_run» "r_g@3")) = ∏ j ∈ Finset.range 3, (1 + σ (.n ((val% «rs_eq_run» "bits[0]") + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h23, h18, h13, h17, h22, h12, h16, h21, h10, h14, h19, h11, h15, h20, w3, w5, w17, word_one]
  have qg : σ (.n (val% «rs_eq_run» "q_g@3")) = ∏ j ∈ Finset.range 3, (1 + σ (.n ((val% «rs_eq_run» "bits[3]") + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h37, h32, h27, h31, h36, h26, h30, h35, h24, h28, h33, h25, h29, h34, w3, w5, w17, word_one]
  rw [prod_gen_pow_of_bool hbr] at rg
  rw [prod_gen_pow_of_bool hbq] at qg
  set r := bitsVal (fun j ↦ decide (σ (.n ((val% «rs_eq_run» "bits[0]") + j)) = 1)) 3 with hrdef
  set q := bitsVal (fun j ↦ decide (σ (.n ((val% «rs_eq_run» "bits[3]") + j)) = 1)) 3 with hqdef
  have hr8 : r < 8 := bitsVal_lt _ 3
  have hq8 : q < 8 := bitsVal_lt _ 3
  have hcg : σ (.n (val% «rs_eq_run» "count_g")) = gen ^ (8 * q + r) := by
    rw [← e_add_eq_zero_iff.mp ha, h41, h40, h39, h38, qg, rg, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    congr 1; ring
  -- the loop over the full chunks
  rw [h43, h42, word_one] at hK hcall
  rw [h44, word_one] at hcall
  obtain ⟨m, hm, hm', hB⟩ := (guarded_loop_rel_iff
    (fun d x ↦ loop5_sound rd (σ (.n (val% «rs_eq_run» "q_g@3"))) (σ (.n (val% «rs_eq_run» "chain"))) (σ (.n (val% «rs_eq_run» "z_vals"))) (σ (.n (val% «rs_eq_run» "point1"))) d x)
    (fun x hb hk hn ↦ loop5_complete rd _ _ _ _ x hb hk hn)).mp ⟨hK, hcall⟩
  have hmq : m = q := by
    rw [qg] at hm'
    exact gen_pow_inj hm (by show q < 2 ^ 64 - 1; omega) hm'.symm
  subst hmq
  have hch : ∀ t < q, ∃ zt pt ct, zt.length = 8 ∧ pt.length = 8 ∧
      ChunkOk rd (σ (.n (val% «rs_eq_run» "chain"))) (σ (.n (val% «rs_eq_run» "z_vals"))) (σ (.n (val% «rs_eq_run» "point1"))) t zt pt ct := fun t ht ↦ by
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
  have e53 : σ (.n (val% «rs_eq_run» "row~5")) = gen ^ (64 * q) := by
    rw [h53, h52, h51, h50, h49, h48, qg]; ring
  have e47 : σ (.n (val% «rs_eq_run» "base")) = gen ^ (8 * q) := by rw [h47, h46, h45, qg]; ring
  rw [h54, h55, h56, e53, e47] at hdisp
  have hm8 := (rs_eq_rows_holds r (by omega) rd _ _).1 hdisp
  obtain ⟨Zl, Pl, Cl, hZl, hPl, hl, h57⟩ : ∃ Zl Pl Cl, Zl.length = r ∧ Pl.length = r ∧
      (0 < r → ChunkOk rd (σ (.n (val% «rs_eq_run» "chain"))) (σ (.n (val% «rs_eq_run» "z_vals"))) (σ (.n (val% «rs_eq_run» "point1"))) q Zl Pl Cl) ∧
      σ (.n (val% «rs_eq_run» "last")) = σ (.n (val% «rs_eq_run» "chain")) * gen ^ (64 * ((8 * q + r + 7) / 8)) := by
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
  obtain ⟨lz, lp, lc, rz, rp, rc, rows⟩ := rows_of_chunks (rd := rd) (chain := σ (.n (val% «rs_eq_run» "chain")))
    (z := σ (.n (val% «rs_eq_run» "z_vals"))) (p := σ (.n (val% «rs_eq_run» "point1"))) (q := q) (r := r) (by omega) Z P C
    (fun t ht ↦ by simp only [Z, ite_pos' ht]; exact hZc t ht)
    (fun t ht ↦ by simp only [P, ite_pos' ht]; exact hPc t ht)
    (by simp only [Z, ite_neg' (lt_irrefl q)]; exact hZl)
    (by simp only [P, ite_neg' (lt_irrefl q)]; exact hPl)
    (fun t ht ↦ by simp only [Z, P, C, ite_pos' ht]; exact hCc t ht)
    (fun h ↦ by simp only [Z, P, C, ite_neg' (lt_irrefl q)]; exact hl h)
  set c : List E := (List.range 64).map fun k ↦ σ (.n ((val% «rs_eq_run» "s2.u0.s0#0") + k)) with hcdef
  have hcget : ∀ k < 64, c.getD k 0 = σ (.n ((val% «rs_eq_run» "s2.u0.s0#0") + k)) := fun k hk ↦ by
    simp [hcdef, List.getD_eq_getElem?_getD, hk]
  refine ⟨8 * q + r, by omega, hcg, σ (.n (val% «rs_eq_run» "chain")), _, _, c, lz, lp, by simp [hcdef], rz, rp,
    fun k hk ↦ ?_, fun k hk ↦ ?_, fun h h1 h2 k hk ↦ ?_, ?_⟩
  · simp only [hcdef, List.length_map, List.length_range] at hk
    simpa [hcdef] using (holds_rsInit (hinit k hk)).1
  · simp only [hcdef, List.length_map, List.length_range] at hk
    simpa [hcdef] using (holds_rsInit (hinit k hk)).2
  · have hrow := rows h h1 h2 k hk
    have hc1 : ((List.range 64).map fun k ↦ (C 0).getD k 0).getD k 0 = c.getD k 0 := by
      have := readsAt_getD (rc (by omega)) (i := k) (by rw [lc]; exact hk)
      rw [hcget k hk]
      exact loadHolds_unique this (holds_rsInit (hinit k hk)).2
    rwa [hc1] at hrow
  · rw [← hret, h58, h57]

end
end LeanVM.Guest.B1
