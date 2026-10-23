/-
  LeanVM.Guest.B1.Da.Loops

  B1 for `da_verify`'s loops but the row branch's hashing: `__loop88` (the prefix bases),
  `__loop89` (the row sums' chains), `__loop90`, `__loop91` (the columns), `__loop92` (the row sums'
  ends) and `__loop94` (the row tree's padding).
-/

module

public import LeanVM.Guest.B1.Da.VerifyColumn

/-!
# `da_verify`'s loops

Each `mul_range` helper is `loop_iff` over its body: `L88Step` (`prefix_bases[x]` is
`prefix_digests·x^128`), `L89Step` (`rowbase[x]` is `acc·x^129`, whose first cell is `0`), the
column loops (`da_verify_column__L1` for `x < g^64`, `__L0` up to `g^128`), `L92Step` (the cell
`128` of `rowbase[x]` is `0`) and `L94Step` (the zero row's digest after the `n_blob` rows).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

set_option maxRecDepth 100000 in
theorem word_g64 : word 27 0 0 = gen ^ 64 := by
  rw [word_eq_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

set_option maxRecDepth 100000 in
theorem word_g128 : word 325 0 0 = gen ^ 128 := by
  rw [word_eq_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

/-- A loop's end reached first at `m` is `n`, when `n` is above the start. -/
theorem loop_end_exact {k m n : ℕ} (hn : n < 2 ^ 33) (hkn : k < n) (hN : gen ^ n = gen ^ m)
    (hfirst : ∀ j, k < j → j < m → gen ^ j ≠ gen ^ n) : m = n := by
  have hmn : m ≤ n := by
    by_contra h
    exact hfirst n hkn (by omega) rfl
  exact (gen_pow_inj' (by omega) (by omega) hN).symm

theorem pow128 (x : E) : x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x))) *
    (x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x)))) *
    (x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x))) *
      (x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x))))) *
    (x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x))) *
      (x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x)))) *
      (x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x))) *
        (x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x)))))) = x ^ 128 := by
  ring

/-! ## `__loop88`: the prefix bases -/

/-- `prefix_bases[x] = prefix_digests·x^128`. -/
def L88Step (rd : Reader) (pb pd x : E) : Prop := LoadHolds rd (pb * x) 0 (pd * x ^ 128)

def l88Body : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)), .atom (.mul (.n 6) (.n 5) (.n 5)),
   .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 7) (.n 7)), .atom (.mul (.n 9) (.n 8) (.n 8)),
   .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 3) (.n 10)), .atom (.mul (.n 12) (.n 2) (.n 0)),
   .atom (.load (.n 11) (.n 12) 0), .atom (.const (.n 13) (word 2 0 0)), .atom (.mul (.n 14) (.n 0) (.n 13)),
   .atom (.add (.n 15) (.n 14) (.n 1)), .atom (.const (.n 16) (word 2 0 0)), .atom (.mul (.n 17) (.n 0) (.n 16)),
   .callIf (.n 15) "__loop88" [.n 17, .n 1, .n 2, .n 3], .ret []]

set_option maxRecDepth 100000 in
theorem find_l88 : coreProgram.find? "__loop88" = some ⟨"__loop88", [.n 0, .n 1, .n 2, .n 3], l88Body⟩ :=
  Program.find?_of_indexOf? (j := 529) (by decide +kernel) rfl

theorem l88_step (rd : Reader) (W pb pd : E) (C : CallRel) (x : E) :
    (∃ fn, coreProgram.find? "__loop88" = some fn ∧ fn.Sem C rd (x :: [W, pb, pd]) []) ↔
      L88Step rd pb pd x ∧ IsInK (x * gen + W) ∧ (x * gen + W ≠ 0 → C "__loop88" (x * gen :: [W, pb, pd]) []) := by
  simp only [find_l88, Option.some.injEq, exists_eq_left', Fn.Sem, l88Body, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_cons, List.map_nil, L88Step, word_gen]
  constructor
  · rintro ⟨σ, hp, m4, m5, m6, m7, m8, m9, m10, m11, m12, l11, c13, m14, a15, c16, m17, hk, hnext, -⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
    rw [m11, m10, m9, m8, m7, m6, m5, m4, pow128, m12] at l11
    rw [a15, m14, c13] at hk hnext
    rw [m17, c16] at hnext
    exact ⟨l11, hk, hnext⟩
  · rintro ⟨l11, hk, hnext⟩
    refine ⟨listVal [x, W, pb, pd, x ^ 2, x ^ 4, x ^ 8, x ^ 16, x ^ 32, x ^ 64, x ^ 128, pd * x ^ 128, pb * x,
      gen, x * gen, x * gen + W, gen, x * gen], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
    refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring, l11, hk, hnext, trivial⟩

theorem l88_iff (rd : Reader) (W pb pd : E) (k : ℕ) :
    coreProgram.Rel rd "__loop88" (gen ^ k :: [W, pb, pd]) [] ↔
      ∃ m, k < m ∧ W = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ W) ∧
        ∀ j, k ≤ j → j < m → L88Step rd pb pd (gen ^ j) :=
  loop_iff (B := fun _ x => L88Step rd pb pd x) (fun _ _ _ _ h => h) (l88_step rd W pb pd) k

/-! ## `__loop89`: the row sums' chains -/

/-- `rowbase[x] = acc·x^129`, and its first cell is `0`. -/
def L89Step (rd : Reader) (acc rb x : E) : Prop :=
  LoadHolds rd (rb * x) 0 (acc * x ^ 129) ∧ LoadHolds rd (acc * x ^ 129) 0 0

def l89Body : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)), .atom (.mul (.n 6) (.n 5) (.n 5)),
   .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 7) (.n 7)), .atom (.mul (.n 9) (.n 8) (.n 8)),
   .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 0)), .atom (.mul (.n 12) (.n 2) (.n 11)),
   .atom (.mul (.n 13) (.n 3) (.n 0)), .atom (.load (.n 12) (.n 13) 0), .atom (.const (.n 14) (word 0 0 0)),
   .atom (.load (.n 14) (.n 12) 0), .atom (.const (.n 15) (word 2 0 0)), .atom (.mul (.n 16) (.n 0) (.n 15)),
   .atom (.add (.n 17) (.n 16) (.n 1)), .atom (.const (.n 18) (word 2 0 0)), .atom (.mul (.n 19) (.n 0) (.n 18)),
   .callIf (.n 17) "__loop89" [.n 19, .n 1, .n 2, .n 3], .ret []]

set_option maxRecDepth 100000 in
theorem find_l89 : coreProgram.find? "__loop89" = some ⟨"__loop89", [.n 0, .n 1, .n 2, .n 3], l89Body⟩ :=
  Program.find?_of_indexOf? (j := 530) (by decide +kernel) rfl

theorem l89_step (rd : Reader) (W acc rb : E) (C : CallRel) (x : E) :
    (∃ fn, coreProgram.find? "__loop89" = some fn ∧ fn.Sem C rd (x :: [W, acc, rb]) []) ↔
      L89Step rd acc rb x ∧ IsInK (x * gen + W) ∧ (x * gen + W ≠ 0 → C "__loop89" (x * gen :: [W, acc, rb]) []) := by
  simp only [find_l89, Option.some.injEq, exists_eq_left', Fn.Sem, l89Body, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_cons, List.map_nil, L89Step, word_gen, word_zero]
  have e129 : ∀ y : E, y ^ 128 * y = y ^ 129 := fun y => by ring
  constructor
  · rintro ⟨σ, hp, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, l12, c14, l14, c15, m16, a17, c18, m19, hk,
      hnext, -⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
    rw [m12, m11, m10, m9, m8, m7, m6, m5, m4, pow128, e129, m13] at l12
    rw [m12, m11, m10, m9, m8, m7, m6, m5, m4, pow128, e129, c14] at l14
    rw [a17, m16, c15] at hk hnext
    rw [m19, c18] at hnext
    exact ⟨⟨l12, l14⟩, hk, hnext⟩
  · rintro ⟨⟨l12, l14⟩, hk, hnext⟩
    refine ⟨listVal [x, W, acc, rb, x ^ 2, x ^ 4, x ^ 8, x ^ 16, x ^ 32, x ^ 64, x ^ 128, x ^ 129,
      acc * x ^ 129, rb * x, 0, gen, x * gen, x * gen + W, gen, x * gen], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
    refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, l12, l14, hk, hnext,
      trivial⟩

theorem l89_iff (rd : Reader) (W acc rb : E) (k : ℕ) :
    coreProgram.Rel rd "__loop89" (gen ^ k :: [W, acc, rb]) [] ↔
      ∃ m, k < m ∧ W = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ W) ∧
        ∀ j, k ≤ j → j < m → L89Step rd acc rb (gen ^ j) :=
  loop_iff (B := fun _ x => L89Step rd acc rb x) (fun _ _ _ _ h => h) (l89_step rd W acc rb) k

/-! ## `__loop92`: the row sums' ends -/

/-- The cell `128` of `rowbase[x]` is `0`. -/
def L92Step (rd : Reader) (rb x : E) : Prop := ∃ R, LoadHolds rd (rb * x) 0 R ∧ LoadHolds rd R 128 0

def l92Body : List Stmt :=
  [.atom (.mul (.n 3) (.n 2) (.n 0)), .atom (.load (.n 4) (.n 3) 0), .atom (.load (.n 5) (.n 4) 128),
   .atom (.const (.n 6) (word 0 0 0)), .atom (.assertEq (.n 5) (.n 6)), .atom (.const (.n 7) (word 2 0 0)),
   .atom (.mul (.n 8) (.n 0) (.n 7)), .atom (.add (.n 9) (.n 8) (.n 1)), .atom (.const (.n 10) (word 2 0 0)),
   .atom (.mul (.n 11) (.n 0) (.n 10)), .callIf (.n 9) "__loop92" [.n 11, .n 1, .n 2], .ret []]

set_option maxRecDepth 100000 in
theorem find_l92 : coreProgram.find? "__loop92" = some ⟨"__loop92", [.n 0, .n 1, .n 2], l92Body⟩ :=
  Program.find?_of_indexOf? (j := 533) (by decide +kernel) rfl

theorem l92_step (rd : Reader) (W rb : E) (C : CallRel) (x : E) :
    (∃ fn, coreProgram.find? "__loop92" = some fn ∧ fn.Sem C rd (x :: [W, rb]) []) ↔
      L92Step rd rb x ∧ IsInK (x * gen + W) ∧ (x * gen + W ≠ 0 → C "__loop92" (x * gen :: [W, rb]) []) := by
  simp only [find_l92, Option.some.injEq, exists_eq_left', Fn.Sem, l92Body, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_cons, List.map_nil, L92Step, word_gen, word_zero]
  constructor
  · rintro ⟨σ, hp, m3, l4, l5, c6, e56, c7, m8, a9, c10, m11, hk, hnext, -⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    rw [c6, add_zero] at e56
    rw [m3] at l4
    rw [e56] at l5
    rw [a9, m8, c7] at hk hnext
    rw [m11, c10] at hnext
    exact ⟨⟨_, l4, l5⟩, hk, hnext⟩
  · rintro ⟨⟨R, l4, l5⟩, hk, hnext⟩
    refine ⟨listVal [x, W, rb, rb * x, R, 0, 0, gen, x * gen, x * gen + W, gen, x * gen], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and, add_zero]
    exact ⟨l4, l5, hk, hnext, trivial⟩

theorem l92_iff (rd : Reader) (W rb : E) (k : ℕ) :
    coreProgram.Rel rd "__loop92" (gen ^ k :: [W, rb]) [] ↔
      ∃ m, k < m ∧ W = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ W) ∧
        ∀ j, k ≤ j → j < m → L92Step rd rb (gen ^ j) :=
  loop_iff (B := fun _ x => L92Step rd rb x) (fun _ _ _ _ h => h) (l92_step rd W rb) k

/-! ## `__loop94`: the row tree's padding -/

/-- The zero row's digest (`DA_PAD_ROW_0`, `DA_PAD_ROW_1`). -/
abbrev padRow0 : E := word 15848538831469629367 12384209104348663257 0
abbrev padRow1 : E := word 15157803279540669797 1453370424372192157 0

/-- Padding row `x`: the zero row's digest as the leaf after the `n_blob` rows. -/
def L94Step (rd : Reader) (rt nb x : E) : Prop :=
  CellsAt rd (rt * (nb * nb) * (x * x)) [padRow0, padRow1]

def l94Body : List Stmt :=
  [.atom (.mul (.n 4) (.n 3) (.n 3)), .atom (.mul (.n 5) (.n 2) (.n 4)), .atom (.mul (.n 6) (.n 0) (.n 0)),
   .atom (.mul (.n 7) (.n 5) (.n 6)), .atom (.const (.n 8) padRow0), .atom (.load (.n 8) (.n 7) 0),
   .atom (.const (.n 9) padRow1), .atom (.load (.n 9) (.n 7) 1), .atom (.const (.n 10) (word 2 0 0)),
   .atom (.mul (.n 11) (.n 0) (.n 10)), .atom (.add (.n 12) (.n 11) (.n 1)),
   .atom (.const (.n 13) (word 2 0 0)), .atom (.mul (.n 14) (.n 0) (.n 13)),
   .callIf (.n 12) "__loop94" [.n 14, .n 1, .n 2, .n 3], .ret []]

set_option maxRecDepth 100000 in
theorem find_l94 : coreProgram.find? "__loop94" = some ⟨"__loop94", [.n 0, .n 1, .n 2, .n 3], l94Body⟩ :=
  Program.find?_of_indexOf? (j := 536) (by decide +kernel) rfl

theorem l94_step (rd : Reader) (W rt nb : E) (C : CallRel) (x : E) :
    (∃ fn, coreProgram.find? "__loop94" = some fn ∧ fn.Sem C rd (x :: [W, rt, nb]) []) ↔
      L94Step rd rt nb x ∧ IsInK (x * gen + W) ∧ (x * gen + W ≠ 0 → C "__loop94" (x * gen :: [W, rt, nb]) []) := by
  simp only [find_l94, Option.some.injEq, exists_eq_left', Fn.Sem, l94Body, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_cons, List.map_nil, L94Step, cellsAt_two, word_gen]
  constructor
  · rintro ⟨σ, hp, m4, m5, m6, m7, c8, l8, c9, l9, c10, m11, a12, c13, m14, hk, hnext, -⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
    rw [m7, m6, m5, m4, c8] at l8
    rw [m7, m6, m5, m4, c9] at l9
    rw [a12, m11, c10] at hk hnext
    rw [m14, c13] at hnext
    exact ⟨⟨l8, l9⟩, hk, hnext⟩
  · rintro ⟨⟨l8, l9⟩, hk, hnext⟩
    refine ⟨listVal [x, W, rt, nb, nb * nb, rt * (nb * nb), x * x, rt * (nb * nb) * (x * x),
      padRow0, padRow1, gen, x * gen, x * gen + W, gen, x * gen], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
    exact ⟨l8, l9, hk, hnext, trivial⟩

theorem l94_iff (rd : Reader) (W rt nb : E) (k : ℕ) :
    coreProgram.Rel rd "__loop94" (gen ^ k :: [W, rt, nb]) [] ↔
      ∃ m, k < m ∧ W = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ W) ∧
        ∀ j, k ≤ j → j < m → L94Step rd rt nb (gen ^ j) :=
  loop_iff (B := fun _ x => L94Step rd rt nb x) (fun _ _ _ _ h => h) (l94_step rd W rt nb) k

/-! ## `__loop90`, `__loop91`: the columns -/

/-- The column loop: `__loop90` over the prefix columns, `__loop91` over the rest. -/
def colLoopName (store : Bool) : String := if store then "__loop90" else "__loop91"

/-- The column loop's end, `g^64` or `g^128`. -/
def colLoopEnd (store : Bool) : E := if store then word 27 0 0 else word 325 0 0

def colLoopBody (store : Bool) : List Stmt :=
  [.call (colName store) [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] [],
   .atom (.const (.n 10) (word 2 0 0)), .atom (.mul (.n 11) (.n 0) (.n 10)),
   .atom (.const (.n 12) (colLoopEnd store)), .atom (.add (.n 13) (.n 11) (.n 12)),
   .atom (.const (.n 14) (word 2 0 0)), .atom (.mul (.n 15) (.n 0) (.n 14)),
   .callIf (.n 13) (colLoopName store) [.n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9],
   .ret []]

set_option maxRecDepth 100000 in
theorem find_colLoop (store : Bool) : coreProgram.find? (colLoopName store) =
    some ⟨colLoopName store, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9], colLoopBody store⟩ := by
  cases store
  · exact Program.find?_of_indexOf? (j := 532) (by decide +kernel) rfl
  · exact Program.find?_of_indexOf? (j := 531) (by decide +kernel) rfl

theorem colLoop_step (store : Bool) (rd : Reader) (ps : List E) (hps : ps.length = 9) (C : CallRel) (x : E) :
    (∃ fn, coreProgram.find? (colLoopName store) = some fn ∧ fn.Sem C rd (x :: ps) []) ↔
      C (colName store) (x :: ps) [] ∧ IsInK (x * gen + colLoopEnd store) ∧
        (x * gen + colLoopEnd store ≠ 0 → C (colLoopName store) (x * gen :: ps) []) := by
  match ps, hps with
  | [nb, np, gap, glp, pb, ct, rb, hs, ctr], _ =>
  simp only [find_colLoop, Option.some.injEq, exists_eq_left', Fn.Sem, colLoopBody, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen]
  constructor
  · rintro ⟨σ, hp, hcall, c10, m11, c12, a13, c14, m15, hk, hnext, -⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
    rw [a13, m11, c10, c12] at hk hnext
    rw [m15, c14] at hnext
    exact ⟨hcall, hk, hnext⟩
  · rintro ⟨hcall, hk, hnext⟩
    refine ⟨listVal [x, nb, np, gap, glp, pb, ct, rb, hs, ctr, gen, x * gen, colLoopEnd store,
      x * gen + colLoopEnd store, gen, x * gen], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
    exact ⟨hcall, hk, hnext, trivial⟩

theorem colLoopEnd_eq (store : Bool) : colLoopEnd store = gen ^ (if store then 64 else 128) := by
  cases store
  · exact word_g128
  · exact word_g64

/-- **The column loop** from `g^k`: every column below its end, the end exactly. -/
theorem colLoop_iff (store : Bool) (rd : Reader) (ps : List E) (hps : ps.length = 9) (k : ℕ) :
    coreProgram.Rel rd (colLoopName store) (gen ^ k :: ps) [] ↔
      ∃ m, k < m ∧ colLoopEnd store = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ colLoopEnd store) ∧
        ∀ j, k ≤ j → j < m → coreProgram.Rel rd (colName store) (gen ^ j :: ps) [] :=
  loop_iff (B := fun C x => C (colName store) (x :: ps) []) (fun _ _ _ hC h => hC _ _ _ h)
    (colLoop_step store rd ps hps) k

/-- The prefix columns: `__loop90` from `1` runs `da_verify_column__L1` at every `g^b`, `b < 64`. -/
theorem colLoop_prefix {rd : Reader} {ps : List E} (hps : ps.length = 9)
    (h : coreProgram.Rel rd "__loop90" (1 :: ps) []) :
    ∀ b < 64, Meaning_da_verify_column true rd (gen ^ b :: ps) [] := by
  rw [← pow_zero gen] at h
  obtain ⟨m, hkm, hN, hfirst, hall⟩ := (colLoop_iff true rd ps hps 0).mp h
  rw [colLoopEnd_eq, ite_pos' rfl] at hN hfirst
  have := loop_end_exact (by norm_num) (by norm_num) hN hfirst
  subst this
  exact fun b hb => (da_verify_column_iff true rd _ _).mp (hall b (Nat.zero_le _) hb)

/-- The other columns: `__loop91` from `g^64` runs `da_verify_column__L0` at every `g^b`,
`64 ≤ b < 128`. -/
theorem colLoop_rest {rd : Reader} {ps : List E} (hps : ps.length = 9)
    (h : coreProgram.Rel rd "__loop91" (word 27 0 0 :: ps) []) :
    ∀ b, 64 ≤ b → b < 128 → Meaning_da_verify_column false rd (gen ^ b :: ps) [] := by
  rw [word_g64] at h
  obtain ⟨m, hkm, hN, hfirst, hall⟩ := (colLoop_iff false rd ps hps 64).mp h
  rw [colLoopEnd_eq, ite_neg' (by decide)] at hN hfirst
  have := loop_end_exact (by norm_num) (by norm_num) hN hfirst
  subst this
  exact fun b hb hb' => (da_verify_column_iff false rd _ _).mp (hall b hb hb')

end
end LeanVM.Guest.B1.Digest
