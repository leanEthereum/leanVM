/-
  LeanVM.Guest.B1.Whir.HelperT

  The core IR of the helpers `open_stacked`'s dispatches call, generated from their
  specializations' constants as the expansion numbers it: `level_positions`, `level_queries`,
  `level_residual`, and their loops.
-/

module

public import LeanVM.Guest.B1.Whir.Template

/-!
# The templates of `open_stacked`'s helpers

Each is the body of a specialization at its compile-time constants, value by value as the
expansion numbers it (`lean_ethereum.py`):

* `lpBody d cd loop`: `level_positions(word0, fs0..fs4, positions, win_ptrs, tabs, squeezes_g)`
  of a level of tree depth `d` and cap depth `cd`, the squeezes runtime: the first word decoded,
  then the loop `loop`; `lpLoopBody d cd loop`: the loop's iteration (one squeeze, decoded by
  `decode_query_windows__L{d}_L{cd}`), the pointers already shifted to the level's slots;
* `lqBody q base folds leaf d cd mu nhs hbits fin`: `level_queries(lam, lam_inv, coefs, hs,
  positions, win_ptrs)`: the cap hinted and checked to its root, the `opening_queries`
  specialization, `lam^q`;
* `lrBody loop1 loop2`: `level_residual(positions, row_d, hs, mu, batches_g, rest_g)`, the query
  counts runtime: the batches' loop `loop1` (`lrLoop1Body`, `resBatch` inline `residual_query`s an
  iteration), then the rest's loop `loop2` (`lrLoop2Body`, one an iteration).

`Whir/HelperData*.lean` check every specialization's body equal to these by kernel evaluation.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-- The name of `decode_query_windows`' specialization at tree depth `d` and cap depth `cd`. -/
def dqwName (d cd : ℕ) : String := "decode_query_windows__L" ++ natStr d ++ "_L" ++ natStr cd

/-- A loop's entry `for x in mul_range(g^e0, N)` at a runtime bound `N` (value `nv`), from `k`: the
guard `g^e0 + N` at `k + 1`, the loop called at `[g^e0, N] ++ args`. -/
def osLoopCallR (name : String) (e0 nv : ℕ) (args : List ℕ) (k : ℕ) : List Stmt :=
  [osCst k (gw e0), osAdd (k + 1) k nv, osCst (k + 2) (gw e0),
    .callIf (.n (k + 1)) name (.n (k + 2) :: .n nv :: args.map V.n)]

/-- `level_positions` at `word0, fs0 .. fs4, positions, win_ptrs, tabs, squeezes_g` (values `0 .. 9`),
`squeezes_g = g^S` runtime: the squeeze run `sqz` (`HeapBuf((squeezes_g·g)^5)` at `15`), the capacity
stored in its row `1`, the first word decoded, the loop over the other squeezes, the last row's
capacity loaded and returned. -/
def lpBody (d cd : ℕ) (loop : String) : List Stmt :=
  [osCst 10 (gw 1), osMul 11 9 10, osMul 12 11 11, osMul 13 12 12, osMul 14 13 11,
    .atom (.hint (.allocDyn (.n 15) (.n 14)))] ++
    ((List.range 5).map fun i ↦ osLd (1 + i) 15 (5 + i)) ++
    [.call (dqwName d cd) [.n 0, .n 6, .n 7, .n 8] []] ++
    osLoopCallR loop 1 9 [15, 6, 7, 8] 16 ++
    [osMul 19 9 9, osMul 20 19 19, osMul 21 20 9, osMul 22 15 21] ++
    ((List.range 5).map fun i ↦ osLd (23 + i) 22 i) ++
    ((List.range 5).map fun i ↦ osCp (28 + i) (23 + i)) ++
    [.ret ((List.range 5).map fun i ↦ .n (28 + i))]

/-- A row of tree depth `d` and cap depth `cd`, its positions at offset `0`: the row
`level_positions`' loop reads. -/
def lpLv (d cd : ℕ) : OsLv := { (default : OsLv) with depth := d, capDepth := cd }

/-- `level_positions`' loop, at `x, N, sqz, positions, win_ptrs, tabs` (values `0 .. 5`), for a
level of tree depth `d` and cap depth `cd`: the squeeze loop's template (`sqLoopBody`) at offset
`0`: the row `sqz·x^5`, its capacity loaded, one squeeze, the next capacity stored, the decoded
positions and windows at `positions·x^(128/d)` and `win_ptrs·x^(128/d)`, then the loop's tail. -/
def lpLoopBody (d cd : ℕ) (name : String) : List Stmt := sqLoopBody (lpLv d cd) name

/-- The name of `opening_queries`' specialization a level calls: its base, folds, leaf's cells,
path depth below the cap, and at the final level (`fin = 1`) the message log `mu`, the vanishing
tables' offset `mu(mu+1)/2`, the lane's length and index bits (else zeros). -/
def oqName (base folds leaf pd mu nhs hbits fin : ℕ) : String :=
  "opening_queries__L" ++ natStr base ++ "_L" ++ natStr folds ++ "_L" ++ natStr leaf ++ "_L" ++
    natStr pd ++ "_L" ++ natStr mu ++ "_L" ++ natStr (mu * (mu + 1) / 2) ++ "_L" ++ natStr nhs ++
    "_L" ++ natStr hbits ++ "_L" ++ natStr fin

/-- `level_queries` at `q` queries of a level of base `base` (`1` at level 0), `folds` folds,
`leaf` cells a leaf, tree depth `d` and cap depth `cd` (and the final level's `mu`, `nhs`, `hbits`,
`fin`), at `lam, lam_inv, coefs, hs, positions, win_ptrs` (values `0 .. 5`): the cap (`4·2^cd`
cells) and its flags hinted, the cap checked to its root, the queries on the cap and flags offset
past the levels above it (`cap·g^(2^(cd+1))`, `flags·g^(2^(cd-1))`), their iterations `g^iters` and
the odd query `g^(q % 2)` at level 0, the root, the sum and `lam^q` returned. -/
def lqBody (q base folds leaf d cd mu nhs hbits fin : ℕ) : List Stmt :=
  let iters := if base = 1 then q / 2 else q
  let odd := if base = 1 then q % 2 else 0
  let pw := osPowSteps 0 (osPowDigits q) 0 22
  let k := 22 + osPowLen q
  osHeap (4 * 2 ^ cd) 6 ++
    [.atom (.hint (.witness "merkle_caps" (.heap (.n 7) 0 (4 * 2 ^ cd))))] ++
    osHeap (2 ^ cd) 8 ++
    [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 9) 0 (2 ^ cd)))),
      .call ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11],
      osCst 12 (gw (2 ^ (cd + 1))), osMul 13 7 12, osCst 14 (gw (2 ^ (cd - 1))), osMul 15 9 14,
      osCst 16 (gw iters), osCst 17 (gw odd),
      .call (oqName base folds leaf (d - cd) mu nhs hbits fin)
        [.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17] [.n 18],
      osCp 19 10, osCp 20 11, osCp 21 18] ++
    pw.1 ++ [osCp k pw.2, .ret [.n 19, .n 20, .n 21, .n k]]

/-- `level_residual` over a column shape, at `positions, row_d, hs, lam_inv, batches_g, rest_g`
(values `0 .. 5`), `n = b·B + r` queries for `b = resBatch`, `batches_g = g^B`, `rest_g = g^r`: the
chains (`HeapBuf((batches_g·rest_g·g)^2)` at `10`) from `0, 0`, the batches' loop `loop1`, the rest's
chains `chain·batches_g^2` and positions `positions·batches_g^b`, the rest's loop `loop2`; the last
values returned. -/
def lrBody (loop1 loop2 : String) : List Stmt :=
  let pw := osPowSteps 4 (osPowDigits resBatch) 4 18
  let k := 18 + osPowLen resBatch
  [osMul 6 4 5, osCst 7 (gw 1), osMul 8 6 7, osMul 9 8 8, .atom (.hint (.allocDyn (.n 10) (.n 9))),
    osCst 11 (word 0 0), osLd 11 10 0, osCst 12 (word 0 0), osLd 12 10 1] ++
    osLoopCallR loop1 0 4 [0, 10, 1, 2, 3] 13 ++
    [osMul 16 4 4, osMul 17 10 16] ++ pw.1 ++ [osMul k 0 pw.2] ++
    osLoopCallR loop2 0 5 [17, k, 1, 2, 3] (k + 1) ++
    [osMul (k + 4) 5 5, osMul (k + 5) 17 (k + 4), osLd (k + 6) (k + 5) 0, osLd (k + 7) (k + 5) 1,
      .ret [.n (k + 6), .n (k + 7)]]

/-- `level_residual`'s batches' loop, at `x, N, positions, chain, row_d, hs, mu` (values
`0 .. 6`), for `cols` columns and a high part of `nhs` coefficients and `hbits` bits: `x^resBatch`
(`osBatchPow`), the batch's positions `positions·x^resBatch`, `h, hh = chain[x]`, `resBatch` steps,
`chain[x·g] = h, hh`, then the loop's tail. -/
def lrLoop1Body (cols nhs hbits : ℕ) (name : String) : List Stmt :=
  let y := 7 + batchLen
  let st := osResSteps y 4 0 5 0 (cols * (cols + 1) / 2) cols nhs hbits 6 (List.range resBatch)
    (y + 3) (y + 4) (y + 5)
  (osBatchPow 7).1 ++ [osMul y 2 (osBatchPow 7).2, osMul (y + 1) 3 0, osMul (y + 2) (y + 1) 0,
    osLd (y + 3) (y + 2) 0, osLd (y + 4) (y + 2) 1] ++ st.1 ++
    [osLd st.2.1 (y + 2) 2, osLd st.2.2.1 (y + 2) 3] ++
    osLoopTail name 7 st.2.2.2

/-- `level_residual`'s rest's loop, at `x, N, rest, tail, row_d, hs, mu` (values `0 .. 6`): the
position `tail[x]`, its inline `residual_query`, `h, hh = rest[x]`, `rest[x·g] = (h + eq)·mu,
(hh + high)·mu`, then the loop's tail. -/
def lrLoop2Body (cols nhs hbits : ℕ) (name : String) : List Stmt :=
  let q := osResQuery 10 4 0 5 0 (cols * (cols + 1) / 2) cols nhs hbits 11
  let e := q.2.2.2
  [osMul 7 2 0, osMul 8 7 0, osMul 9 3 0, osLd 10 9 0] ++ q.1 ++
    [osLd e 8 0, osAdd (e + 1) e q.2.1, osMul (e + 2) (e + 1) 6, osLd (e + 2) 8 2,
      osLd (e + 3) 8 1, osAdd (e + 4) (e + 3) q.2.2.1, osMul (e + 5) (e + 4) 6, osLd (e + 5) 8 3] ++
    osLoopTail name 7 (e + 6)

end
end LeanVM.Guest.B1.Whir
