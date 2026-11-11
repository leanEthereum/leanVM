/-
  LeanVM.Guest.B1.Whir.HelperT

  The core IR of the helpers `open_stacked`'s dispatches call, generated from their
  specializations' constants as the expansion numbers it: `level_positions`, `level_queries`,
  `level_residual`, `residual_batch`, and their loops.
-/

module

public import LeanVM.Guest.B1.Whir.Template

/-!
# The templates of `open_stacked`'s helpers

Each is the body of a specialization at its compile-time constants, value by value as the
expansion numbers it (`lean_ethereum.py`):

* `lpBody sq loop`: `level_positions(fs0..fs4, positions, win_ptrs, win_tabs)` at `sq` squeezes,
  its loop `loop`; `lpLoopBody d cd loop`: the loop's iteration (one squeeze, decoded by
  `decode_query_windows__L{d}_L{cd}`), the pointers already shifted to the level's slots;
* `lqBody q base il leaf d cd`: `level_queries(lam, win_ptrs, row_eq_weights)`: the cap hinted and
  checked to its root, `lam^q`, the `opening_queries` specialization;
* `lrBody q loop1 loop2`: `level_residual(positions, row_d, mu)` at `q` queries: the batches' loop
  `loop1` (`lrLoop1Body`, a `residual_batch` call an iteration), then, when `8 ∤ q`, the rest's loop
  `loop2` (`lrLoop2Body`, an inline `residual_query` an iteration);
* `rbBody cols`: `residual_batch(batch, row_d, mu, h)`: eight inline `residual_query`s over `cols`
  columns.

`Whir/HelperData*.lean` check every specialization's body equal to these by kernel evaluation.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-- `level_positions` at `sq` squeezes: the squeeze run `sqz` (`HeapBuf((g^(sq+1))^5)` at `8, 9`),
the capacity stored in its first row, the loop over the squeezes, the last row's capacity loaded and
returned. -/
def lpBody (sq : ℕ) (loop : String) : List Stmt :=
  osHeap ((sq + 1) * 5) 8 ++
    ((List.range 5).map fun i ↦ .atom (.load (.n i) (.n 9) i)) ++
    osLoopCall loop sq [9, 5, 6, 7] 10 ++
    [.atom (.const (.n 15) (gw (sq * 5))), .atom (.mul (.n 16) (.n 9) (.n 15))] ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (17 + i)) (.n 16) i)) ++
    ((List.range 5).map fun i ↦ .atom (.copy (.n (22 + i)) (.n (17 + i)))) ++
    [.ret ((List.range 5).map fun i ↦ .n (22 + i))]

/-- `level_positions`' loop, at `x, N, sqz, positions, win_ptrs, tabs` (values `0 .. 5`), for a
level of tree depth `d` and cap depth `cd`: the row `sqz·x^5`, its capacity loaded, one squeeze,
the next capacity stored, the decoded positions and windows at `positions·x^(192/d)` and
`win_ptrs·x^(192/d)`, then the loop's tail. -/
def lpLoopBody (d cd : ℕ) (name : String) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits (192 / d)) 0 40
  let e := 40 + osPowLen (192 / d)
  [.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 7) (.n 0)),
    .atom (.mul (.n 9) (.n 2) (.n 8))] ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (10 + i)) (.n 9) i)) ++
    [.atom (.const (.n 15) (word 1 0 0)), .atom (.const (.n 16) (word 0 0 0)),
      .atom (.const (.n 17) (word 0 0 0)), .atom (.const (.n 18) (word 0 0 0)),
      .atom (.const (.n 19) (word 0 0 0))] ++
    osSqueeze0 15 [10, 11, 12, 13, 14] 20 ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (28 + i)) (.n 9) (5 + i))) ++
    pw.1 ++ [.atom (.mul (.n e) (.n 3) (.n pw.2)), .atom (.mul (.n (e + 1)) (.n 4) (.n pw.2))] ++
    [.call ("decode_query_windows__L" ++ natStr d ++ "_L" ++ natStr cd)
      [.n 39, .n e, .n (e + 1), .n 5] []] ++
    osLoopTail name 6 (e + 2)

/-- The name of `opening_queries`' specialization a level calls. -/
def oqName (q base il leaf d cd : ℕ) : String :=
  "opening_queries__L" ++ natStr (q % 2 * base) ++ "_L" ++ natStr base ++ "_L" ++ natStr il ++
    "_L" ++ natStr leaf ++ "_L" ++ natStr d ++ "_L" ++ natStr cd

/-- `level_queries` at `q` queries of a level of base `base` (`1` at level 0), `il` words a row,
`leaf` cells a leaf, tree depth `d` and cap depth `cd`, at `lam, win_ptrs, row_eq_weights`
(values `0 .. 2`): the cap (`4·2^cd` cells) and its flags hinted, the cap checked to its root,
`lam^q`, the queries, the root, the sum and `lam^q` returned. -/
def lqBody (q base il leaf d cd : ℕ) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits q) 0 9
  let k := 9 + osPowLen q
  let iters := if base = 1 then q / 2 else q
  osHeap (4 * 2 ^ cd) 3 ++
    [.atom (.hint (.witness "merkle_caps" (.heap (.n 4) 0 (4 * 2 ^ cd))))] ++
    osHeap (2 ^ cd) 5 ++
    [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 6) 0 (2 ^ cd)))),
      .call ("verify_merkle_cap__L" ++ natStr cd) [.n 4, .n 6] [.n 7, .n 8]] ++
    pw.1 ++
    [.atom (.const (.n k) (gw iters)),
      .call (oqName q base il leaf d cd) [.n 4, .n 6, .n 0, .n pw.2, .n 1, .n 2, .n k] [.n (k + 1)],
      .atom (.copy (.n (k + 2)) (.n 7)), .atom (.copy (.n (k + 3)) (.n 8)),
      .atom (.copy (.n (k + 4)) (.n (k + 1))), .atom (.copy (.n (k + 5)) (.n pw.2)),
      .ret [.n (k + 2), .n (k + 3), .n (k + 4), .n (k + 5)]]

/-- `level_residual` at `q` queries, at `positions, row_d, mu` (values `0 .. 2`): the chain
(`HeapBuf(g^(q/8 + 1))` at `3, 4`) from `0`, the batches' loop, then, when `8 ∤ q`, the rest's
chain (`HeapBuf(g^(q%8 + 1))`) from the batches' last value, the rest's positions
`positions·g^(8·(q/8))`, the rest's loop; the last value returned. -/
def lrBody (q : ℕ) (loop1 loop2 : String) : List Stmt :=
  osHeap (q / resBatch + 1) 3 ++
    [.atom (.const (.n 5) (word 0 0 0)), .atom (.load (.n 5) (.n 4) 0)] ++
    osLoopCall loop1 (q / resBatch) [4, 0, 1, 2] 6 ++
    [.atom (.load (.n 11) (.n 4) (q / resBatch))] ++
    if q % resBatch = 0 then [.atom (.copy (.n 12) (.n 11)), .ret [.n 12]]
    else
      osHeap (q % resBatch + 1) 12 ++
        [.atom (.load (.n 11) (.n 13) 0), .atom (.const (.n 14) (gw (resBatch * (q / resBatch)))),
          .atom (.mul (.n 15) (.n 0) (.n 14))] ++
        osLoopCall loop2 (q % resBatch) [13, 15, 1, 2] 16 ++
        [.atom (.load (.n 21) (.n 13) (q % resBatch)), .atom (.copy (.n 22) (.n 21)), .ret [.n 22]]

/-- The name of `residual_batch`' specialization at `cols` columns. -/
def rbName (cols : ℕ) : String := "residual_batch__L" ++ natStr cols

/-- `level_residual`'s batches' loop, at `x, N, chain, positions, row_d, mu` (values `0 .. 5`),
for `cols` columns: the batch's positions `positions·x^8`, `h = chain[x]`, the batch's
`residual_batch`, `chain[x·g] = h`, then the loop's tail. -/
def lrLoop1Body (cols : ℕ) (name : String) : List Stmt :=
  [.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 7) (.n 7)),
    .atom (.mul (.n 9) (.n 3) (.n 8)), .atom (.mul (.n 10) (.n 2) (.n 0)), .atom (.load (.n 11) (.n 10) 0),
    .call (rbName cols) [.n 9, .n 4, .n 5, .n 11] [.n 12],
    .atom (.mul (.n 13) (.n 2) (.n 0)), .atom (.load (.n 12) (.n 13) 1)] ++
    osLoopTail name 6 14

/-- `level_residual`'s rest's loop, at `x, N, rest, tail, row_d, mu` (values `0 .. 5`), for
`cols` columns: `h = rest[x]`, the position `tail[x]`, its inline `residual_query` over the
vanishing values of `cols` columns, `rest[x·g] = (h + eq)·mu`, then the loop's tail. -/
def lrLoop2Body (cols : ℕ) (name : String) : List Stmt :=
  let e := osResQuery 9 4 0 (cols * (cols + 1) / 2) cols 10
  [.atom (.mul (.n 6) (.n 2) (.n 0)), .atom (.load (.n 7) (.n 6) 0), .atom (.mul (.n 8) (.n 3) (.n 0)),
    .atom (.load (.n 9) (.n 8) 0)] ++ e.1 ++
    [.atom (.add (.n e.2.2) (.n 7) (.n e.2.1)), .atom (.mul (.n (e.2.2 + 1)) (.n e.2.2) (.n 5)),
      .atom (.mul (.n (e.2.2 + 2)) (.n 2) (.n 0)), .atom (.load (.n (e.2.2 + 1)) (.n (e.2.2 + 2)) 1)] ++
    osLoopTail name 6 (e.2.2 + 3)

/-- `residual_batch` at `cols` columns, at `batch, row_d, mu, h` (values `0 .. 3`): eight steps
`h ← (h + eq_k)·mu`, the position `batch[g^k]`, `h` returned. -/
def rbBody (cols : ℕ) : List Stmt :=
  let r := osResSteps 0 1 0 (cols * (cols + 1) / 2) cols 2 (List.range resBatch) 3 4
  r.1 ++ [.atom (.copy (.n r.2.2) (.n r.2.1)), .ret [.n r.2.2]]

end
end LeanVM.Guest.B1.Whir
