/-
  LeanVM.Guest.B1.Da.Column

  B1 for `da_vector_dispatch` (G:3030-3042), `da_verify_column__L0` and `__L1` (G:2971-2997) and
  their loops `__loop484` to `__loop487`: one column of the matrix.
-/

module

public import LeanVM.Guest.B1.Da.Vector
public import LeanVM.Guest.B1.Da.Cell
public import LeanVM.Guest.B1.Da.Tree

/-!
# A column

`da_vector_dispatch(xb, h0, h1, counters)` runs `da_vector_cell__L1` at the last column
`xb = g^127` and `__L0` elsewhere. `da_verify_column(xb, …)` reads the vector hash's state for
column `xb` at `hashes·xb²`, runs the dispatch, stores the next state at `hashes·(xb·g)²`, then
for each row `xi = g^i` below `n_blob` checks a cell against the weights (`__loop484`, which also
stores the cell digest for the row branch, or `__loop486`), adding its inner product to the row's
running sum `rowbase[xi]·xb`, and writes the cell digest as leaf `i` of the column's tree; the gap
rows' leaves are the zero cell's digest (`__loop485`, `__loop487`). The column's tree root is
stored at `coltree·xb²`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

theorem isInK_add_left {a b : E} (ha : IsInK a) : IsInK (a + b) ↔ IsInK b := by
  unfold IsInK; rw [limb_add, limb_add, ha.1, ha.2, zero_add, zero_add]

set_option maxRecDepth 100000 in
theorem word_g127 : word 9223372036854775983 0 0 = gen ^ 127 := by
  rw [word_eq_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

theorem isInK_gen_pow (j : ℕ) : IsInK (gen ^ j) := by
  rw [gen_pow_eq_ofK]; exact ofK_isInK _

/-! ## `da_vector_dispatch` -/

/-- **`da_vector_dispatch(xb, h0, h1, counters)`**: `xb` is in `K`, and the vector cell runs,
final exactly at `xb = g^127`. -/
def Meaning_da_vector_dispatch (rd : Reader) (args rets : List E) : Prop :=
  ∃ xb rest, args = xb :: rest ∧ IsInK xb ∧
    Meaning_da_vector_cell (decide (xb = gen ^ 127)) rd args rets

/-- `da_vector_dispatch`'s body. -/
def vdBody : List Stmt :=
  [.atom (.const (.n 4) (word 9223372036854775983 0 0)), .atom (.add (.n 5) (.n 0) (.n 4)),
   .ite (.n 5)
    [.call "da_vector_cell__L1" [.n 0, .n 1, .n 2, .n 3] [.n 6, .n 7, .n 8],
     .atom (.copy (.n 9) (.n 6)), .atom (.copy (.n 10) (.n 7)), .atom (.copy (.n 11) (.n 8))]
    [.call "da_vector_cell__L0" [.n 0, .n 1, .n 2, .n 3] [.n 12, .n 13, .n 14],
     .atom (.copy (.n 9) (.n 12)), .atom (.copy (.n 10) (.n 13)), .atom (.copy (.n 11) (.n 14))],
   .atom (.copy (.n 15) (.n 9)), .atom (.copy (.n 16) (.n 10)), .atom (.copy (.n 17) (.n 11)),
   .ret [.n 15, .n 16, .n 17]]

set_option maxRecDepth 100000 in
theorem find_vd : coreProgram.find? "da_vector_dispatch" =
    some ⟨"da_vector_dispatch", [.n 0, .n 1, .n 2, .n 3], vdBody⟩ :=
  Program.find?_of_indexOf? (j := 26) (by decide +kernel) rfl

theorem da_vector_dispatch_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "da_vector_dispatch" args rets ↔ Meaning_da_vector_dispatch rd args rets := by
  rw [rel_of_find find_vd]
  simp only [Fn.Sem, vdBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  have hk := isInK_gen_pow 127
  constructor
  · rintro ⟨σ, rfl, c4, a5, hk5, hz, hnz⟩
    rw [a5, c4, word_g127] at hk5 hz hnz
    have hx : IsInK (σ (.n 0)) := by
      rw [add_comm] at hk5; exact (isInK_add_left hk).mp hk5
    refine ⟨σ (.n 0), [σ (.n 1), σ (.n 2), σ (.n 3)], rfl, hx, ?_⟩
    by_cases h : σ (.n 0) = gen ^ 127
    · obtain ⟨hc, c9, c10, c11, c15, c16, c17, hr⟩ := hz (e_add_eq_zero_iff.mpr h)
      rw [decide_eq_true h, ← hr, c15, c16, c17, c9, c10, c11]
      exact (da_vector_cell_iff true rd _ _).mp hc
    · obtain ⟨hc, c9, c10, c11, c15, c16, c17, hr⟩ := hnz (fun h' => h (e_add_eq_zero_iff.mp h'))
      rw [decide_eq_false h, ← hr, c15, c16, c17, c9, c10, c11]
      exact (da_vector_cell_iff false rd _ _).mp hc
  · rintro ⟨xb, rest, rfl, hx, hM⟩
    obtain ⟨_, h0, h1, ctr, o0, o1, wp, ha, rfl, -⟩ := id hM
    simp only [List.cons.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    refine ⟨listVal [xb, h0, h1, ctr, word 9223372036854775983 0 0, xb + word 9223372036854775983 0 0,
      o0, o1, wp, o0, o1, wp, o0, o1, wp, o0, o1, wp], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, word_g127, true_and, and_true]
    refine ⟨(isInK_add_left hx).mpr hk, fun hz => ?_, fun hnz => ?_⟩
    · have h := e_add_eq_zero_iff.mp hz
      rw [decide_eq_true h] at hM
      exact (da_vector_cell_iff true rd _ _).mpr hM
    · have h : xb ≠ gen ^ 127 := fun h => hnz (e_add_eq_zero_iff.mpr h)
      rw [decide_eq_false h] at hM
      exact (da_vector_cell_iff false rd _ _).mpr hM


/-! ## The loops -/

/-- The row loop: `__loop484` stores the row branch's digests, `__loop486` does not. -/
def rowName (store : Bool) : String := if store then "__loop484" else "__loop486"

/-- The gap loop. -/
def gapName (store : Bool) : String := if store then "__loop485" else "__loop487"

/-- The row loop's body. -/
def rowBody (store : Bool) : List Stmt :=
  if store then
    [.call "da_verify_cell" [.n 2] [.n 7, .n 8, .n 9], .atom (.mul (.n 10) (.n 3) (.n 0)),
     .atom (.load (.n 11) (.n 10) 0), .atom (.mul (.n 12) (.n 11) (.n 4)), .atom (.load (.n 13) (.n 12) 0),
     .atom (.add (.n 14) (.n 13) (.n 9)), .atom (.load (.n 14) (.n 12) 1), .atom (.mul (.n 15) (.n 0) (.n 0)),
     .atom (.mul (.n 16) (.n 5) (.n 15)), .atom (.load (.n 7) (.n 16) 0), .atom (.load (.n 8) (.n 16) 1),
     .atom (.mul (.n 17) (.n 6) (.n 0)), .atom (.load (.n 18) (.n 17) 0), .atom (.mul (.n 19) (.n 4) (.n 4)),
     .atom (.mul (.n 20) (.n 18) (.n 19)), .atom (.load (.n 7) (.n 20) 0), .atom (.load (.n 8) (.n 20) 1),
     .atom (.const (.n 21) (word 2 0 0)), .atom (.mul (.n 22) (.n 0) (.n 21)),
     .atom (.add (.n 23) (.n 22) (.n 1)), .atom (.const (.n 24) (word 2 0 0)),
     .atom (.mul (.n 25) (.n 0) (.n 24)),
     .callIf (.n 23) "__loop484" [.n 25, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], .ret []]
  else
    [.call "da_verify_cell" [.n 2] [.n 7, .n 8, .n 9], .atom (.mul (.n 10) (.n 3) (.n 0)),
     .atom (.load (.n 11) (.n 10) 0), .atom (.mul (.n 12) (.n 11) (.n 4)), .atom (.load (.n 13) (.n 12) 0),
     .atom (.add (.n 14) (.n 13) (.n 9)), .atom (.load (.n 14) (.n 12) 1), .atom (.mul (.n 15) (.n 0) (.n 0)),
     .atom (.mul (.n 16) (.n 5) (.n 15)), .atom (.load (.n 7) (.n 16) 0), .atom (.load (.n 8) (.n 16) 1),
     .atom (.const (.n 17) (word 2 0 0)), .atom (.mul (.n 18) (.n 0) (.n 17)),
     .atom (.add (.n 19) (.n 18) (.n 1)), .atom (.const (.n 20) (word 2 0 0)),
     .atom (.mul (.n 21) (.n 0) (.n 20)),
     .callIf (.n 19) "__loop486" [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], .ret []]

/-- The zero cell's digest, the gap rows' leaves (`DA_PAD_CELL_0`, `DA_PAD_CELL_1`). -/
abbrev padCell0 : E := word 4310910678787625070 18387342490366197401 0
abbrev padCell1 : E := word 18147972247064536329 14917646806905992560 0

/-- The gap loop's body. -/
def gapBody (store : Bool) : List Stmt :=
  [.atom (.mul (.n 4) (.n 3) (.n 3)), .atom (.mul (.n 5) (.n 2) (.n 4)), .atom (.mul (.n 6) (.n 0) (.n 0)),
   .atom (.mul (.n 7) (.n 5) (.n 6)), .atom (.const (.n 8) padCell0), .atom (.load (.n 8) (.n 7) 0),
   .atom (.const (.n 9) padCell1), .atom (.load (.n 9) (.n 7) 1), .atom (.const (.n 10) (word 2 0 0)),
   .atom (.mul (.n 11) (.n 0) (.n 10)), .atom (.add (.n 12) (.n 11) (.n 1)),
   .atom (.const (.n 13) (word 2 0 0)), .atom (.mul (.n 14) (.n 0) (.n 13)),
   .callIf (.n 12) (gapName store) [.n 14, .n 1, .n 2, .n 3], .ret []]

set_option maxRecDepth 100000 in
theorem find_row (store : Bool) : coreProgram.find? (rowName store) =
    some ⟨rowName store, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], rowBody store⟩ := by
  cases store
  · exact Program.find?_of_indexOf? (j := 1041) (by decide +kernel) rfl
  · exact Program.find?_of_indexOf? (j := 1039) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_gap (store : Bool) : coreProgram.find? (gapName store) =
    some ⟨gapName store, [.n 0, .n 1, .n 2, .n 3], gapBody store⟩ := by
  cases store
  · exact Program.find?_of_indexOf? (j := 1042) (by decide +kernel) rfl
  · exact Program.find?_of_indexOf? (j := 1040) (by decide +kernel) rfl

/-- Row `x` of a column: the cell checked against the weights at `lv`, its inner product added to
the row's running sum at `rowbase[x]·xb`, its digest the column tree's leaf at `node·x²` and, when
`store`, the row branch's at `prefix_bases[x]·xb²`. -/
def RowStep (store : Bool) (rd : Reader) (lv rb xb node pb : E) (C : CallRel) (x : E) : Prop :=
  ∃ d0 d1 s R a, C "da_verify_cell" [lv] [d0, d1, s] ∧ LoadHolds rd (rb * x) 0 R ∧
    LoadHolds rd (R * xb) 0 a ∧ LoadHolds rd (R * xb) 1 (a + s) ∧ CellsAt rd (node * (x * x)) [d0, d1] ∧
    (store = true → ∃ P, LoadHolds rd (pb * x) 0 P ∧ CellsAt rd (P * (xb * xb)) [d0, d1])

/-- Gap row `x`: the zero cell's digest as the leaf after the `n_blob` rows. -/
def GapStep (rd : Reader) (node nb x : E) : Prop :=
  CellsAt rd (node * (nb * nb) * (x * x)) [padCell0, padCell1]

theorem row_step (store : Bool) (rd : Reader) (W lv rb xb node pb : E) (C : CallRel) (x : E) :
    (∃ fn, coreProgram.find? (rowName store) = some fn ∧
        fn.Sem C rd (x :: [W, lv, rb, xb, node, pb]) []) ↔
      RowStep store rd lv rb xb node pb C x ∧ IsInK (x * gen + W) ∧
        (x * gen + W ≠ 0 → C (rowName store) (x * gen :: [W, lv, rb, xb, node, pb]) []) := by
  have hf : ∀ fn, coreProgram.find? (rowName store) = some fn ↔
      fn = ⟨rowName store, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], rowBody store⟩ := fun fn => by
    rw [find_row]; exact ⟨fun h => (Option.some.inj h).symm, fun h => by rw [h]⟩
  simp only [hf, exists_eq_left]
  cases store
  · simp only [Fn.Sem, rowBody, Bool.false_eq_true, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil, RowStep, cellsAt_two, ← word_gen, rowName, false_implies, and_true]
    constructor
    · rintro ⟨σ, hp, hcall, m10, l11, m12, l13, a14, l14, m15, m16, l7, l8, c17, m18, a19, c20, m21,
        hk, hnext⟩
      simp only [List.cons.injEq, and_true] at hp
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
      rw [m10] at l11
      rw [m12] at l13 l14
      rw [a14] at l14
      rw [m16, m15] at l7 l8
      rw [a19, m18, c17] at hk hnext
      rw [m21, c20] at hnext
      exact ⟨⟨_, _, _, _, _, hcall, l11, l13, l14, l7, l8⟩, hk, hnext⟩
    · rintro ⟨⟨d0, d1, s, R, a, hcall, l11, l13, l14, l7, l8⟩, hk, hnext⟩
      refine ⟨listVal [x, W, lv, rb, xb, node, pb, d0, d1, s, rb * x, R, R * xb, a, a + s, x * x,
        node * (x * x), word 2 0 0, x * word 2 0 0, x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0],
        rfl, ?_⟩
      simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
      exact ⟨hcall, l11, l13, l14, l7, l8, hk, hnext⟩
  · simp only [Fn.Sem, rowBody, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil, RowStep, cellsAt_two, ← word_gen, rowName, forall_const]
    constructor
    · rintro ⟨σ, hp, hcall, m10, l11, m12, l13, a14, l14, m15, m16, l7, l8, m17, l18, m19, m20, l7', l8',
        c21, m22, a23, c24, m25, hk, hnext, -⟩
      simp only [List.cons.injEq, and_true] at hp
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
      rw [m10] at l11
      rw [m12] at l13 l14
      rw [a14] at l14
      rw [m16, m15] at l7 l8
      rw [m17] at l18
      rw [m20, m19] at l7' l8'
      rw [a23, m22, c21] at hk hnext
      rw [m25, c24] at hnext
      exact ⟨⟨_, _, _, _, _, hcall, l11, l13, l14, ⟨l7, l8⟩, _, l18, l7', l8'⟩, hk, hnext⟩
    · rintro ⟨⟨d0, d1, s, R, a, hcall, l11, l13, l14, ⟨l7, l8⟩, P, l18, l7', l8'⟩, hk, hnext⟩
      refine ⟨listVal [x, W, lv, rb, xb, node, pb, d0, d1, s, rb * x, R, R * xb, a, a + s, x * x,
        node * (x * x), pb * x, P, xb * xb, P * (xb * xb), word 2 0 0, x * word 2 0 0,
        x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0], rfl, ?_⟩
      simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
      exact ⟨hcall, l11, l13, l14, l7, l8, l18, l7', l8', hk, hnext, trivial⟩

theorem gap_step (store : Bool) (rd : Reader) (W node nb : E) (C : CallRel) (x : E) :
    (∃ fn, coreProgram.find? (gapName store) = some fn ∧ fn.Sem C rd (x :: [W, node, nb]) []) ↔
      GapStep rd node nb x ∧ IsInK (x * gen + W) ∧
        (x * gen + W ≠ 0 → C (gapName store) (x * gen :: [W, node, nb]) []) := by
  have hf : ∀ fn, coreProgram.find? (gapName store) = some fn ↔
      fn = ⟨gapName store, [.n 0, .n 1, .n 2, .n 3], gapBody store⟩ := fun fn => by
    rw [find_gap]; exact ⟨fun h => (Option.some.inj h).symm, fun h => by rw [h]⟩
  simp only [hf, exists_eq_left]
  simp only [Fn.Sem, gapBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    GapStep, cellsAt_two, ← word_gen]
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
    refine ⟨listVal [x, W, node, nb, nb * nb, node * (nb * nb), x * x, node * (nb * nb) * (x * x),
      padCell0, padCell1, word 2 0 0, x * word 2 0 0, x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0],
      rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
    exact ⟨l8, l9, hk, hnext, trivial⟩

theorem rowStep_mono (store : Bool) (rd : Reader) (lv rb xb node pb : E) :
    ∀ C C' x, CallRel.Le C C' → RowStep store rd lv rb xb node pb C x → RowStep store rd lv rb xb node pb C' x :=
  fun _ _ _ hC ⟨a, b, c, d, e, h1, h2⟩ => ⟨a, b, c, d, e, hC _ _ _ h1, h2⟩

/-- **The row loop** from `g^k` to `W`. -/
theorem row_loop_iff (store : Bool) (rd : Reader) (W lv rb xb node pb : E) (k : ℕ) :
    coreProgram.Rel rd (rowName store) (gen ^ k :: [W, lv, rb, xb, node, pb]) [] ↔
      ∃ m, k < m ∧ W = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ W) ∧
        ∀ j, k ≤ j → j < m → RowStep store rd lv rb xb node pb (coreProgram.Rel rd) (gen ^ j) :=
  loop_iff (rowStep_mono store rd lv rb xb node pb) (row_step store rd W lv rb xb node pb) k

/-- **The gap loop** from `g^k` to `W`. -/
theorem gap_loop_iff (store : Bool) (rd : Reader) (W node nb : E) (k : ℕ) :
    coreProgram.Rel rd (gapName store) (gen ^ k :: [W, node, nb]) [] ↔
      ∃ m, k < m ∧ W = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ W) ∧
        ∀ j, k ≤ j → j < m → GapStep rd node nb (gen ^ j) :=
  loop_iff (B := fun _ x => GapStep rd node nb x) (fun _ _ _ _ h => h) (gap_step store rd W node nb) k

end
end LeanVM.Guest.B1.Digest
