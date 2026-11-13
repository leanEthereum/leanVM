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

* `lpBody sq d cd loop`: `level_positions(word0, fs0..fs4, positions, win_ptrs, tabs)` at `sq`
  squeezes of a level of tree depth `d` and cap depth `cd`: the first word decoded, then the loop
  `loop`; `lpLoopBody d cd loop`: the loop's iteration (one squeeze, decoded by
  `decode_query_windows__L{d}_L{cd}`), the pointers already shifted to the level's slots;
* `lqBody q base folds leaf d cd mu nhs hbits fin`: `level_queries(lam, lam_inv, coefs, hs,
  positions, win_ptrs)`: the cap hinted and checked to its root, the `opening_queries`
  specialization, `lam^q`;
* `lrBody q cols nhs hbits loop1 loop2`: `level_residual(positions, row_d, hs, mu)` at `q` queries:
  the batches' loop `loop1` (`lrLoop1Body`, `resBatch` inline `residual_query`s an iteration), then,
  when `resBatch ∤ q`, the rest's loop `loop2` (`lrLoop2Body`, one an iteration).

`Whir/HelperData*.lean` check every specialization's body equal to these by kernel evaluation.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-- The name of `decode_query_windows`' specialization at tree depth `d` and cap depth `cd`. -/
def dqwName (d cd : ℕ) : String := "decode_query_windows__L" ++ natStr d ++ "_L" ++ natStr cd

/-- `level_positions` at `sq` squeezes, at `word0, fs0 .. fs4, positions, win_ptrs, tabs` (values
`0 .. 8`): the squeeze run `sqz` (`HeapBuf((g^(sq+1))^5)` at `9, 10`), the capacity stored in its
row `1`, the first word decoded, the loop over the other squeezes, the last row's capacity loaded
and returned. -/
def lpBody (sq d cd : ℕ) (loop : String) : List Stmt :=
  osHeap ((sq + 1) * 5) 9 ++
    ((List.range 5).map fun i ↦ osLd (1 + i) 10 (5 + i)) ++
    [.call (dqwName d cd) [.n 0, .n 6, .n 7, .n 8] []] ++
    osLoopCall loop 1 sq [10, 6, 7, 8] 11 ++
    [osCst 16 (gw (sq * 5)), osMul 17 10 16] ++
    ((List.range 5).map fun i ↦ osLd (18 + i) 17 i) ++
    ((List.range 5).map fun i ↦ osCp (23 + i) (18 + i)) ++
    [.ret ((List.range 5).map fun i ↦ .n (23 + i))]

/-- A row of tree depth `d` and cap depth `cd`, its positions at offset `0`: the row
`level_positions`' loop reads. -/
def lpLv (d cd : ℕ) : OsLv := { (default : OsLv) with depth := d, capDepth := cd }

/-- `level_positions`' loop, at `x, N, sqz, positions, win_ptrs, tabs` (values `0 .. 5`), for a
level of tree depth `d` and cap depth `cd`: the squeeze loop's template (`sqLoopBody`) at offset
`0`: the row `sqz·x^5`, its capacity loaded, one squeeze, the next capacity stored, the decoded
positions and windows at `positions·x^(128/d)` and `win_ptrs·x^(128/d)`, then the loop's tail. -/
def lpLoopBody (d cd : ℕ) (name : String) : List Stmt := sqLoopBody (lpLv d cd) name

/-- The name of `opening_queries`' specialization a level calls: its odd query, base, folds,
leaf's cells, tree and cap depths, and at the final level (`fin = 1`) the message log `mu`, the
vanishing tables' offset `mu(mu+1)/2`, the lane's length and index bits (else zeros). -/
def oqName (q base folds leaf d cd mu nhs hbits fin : ℕ) : String :=
  "opening_queries__L" ++ natStr (q % 2 * base) ++ "_L" ++ natStr base ++ "_L" ++ natStr folds ++
    "_L" ++ natStr leaf ++ "_L" ++ natStr d ++ "_L" ++ natStr cd ++ "_L" ++ natStr mu ++ "_L" ++
    natStr (mu * (mu + 1) / 2) ++ "_L" ++ natStr nhs ++ "_L" ++ natStr hbits ++ "_L" ++ natStr fin

/-- `level_queries` at `q` queries of a level of base `base` (`1` at level 0), `folds` folds,
`leaf` cells a leaf, tree depth `d` and cap depth `cd` (and the final level's `mu`, `nhs`, `hbits`,
`fin`), at `lam, lam_inv, coefs, hs, positions, win_ptrs` (values `0 .. 5`): the cap (`4·2^cd`
cells) and its flags hinted, the cap checked to its root, the queries, the root, the sum and
`lam^q` returned. -/
def lqBody (q base folds leaf d cd mu nhs hbits fin : ℕ) : List Stmt :=
  let iters := if base = 1 then q / 2 else q
  let pw := osPowSteps 0 (osPowDigits q) 0 17
  let k := 17 + osPowLen q
  osHeap (4 * 2 ^ cd) 6 ++
    [.atom (.hint (.witness "merkle_caps" (.heap (.n 7) 0 (4 * 2 ^ cd))))] ++
    osHeap (2 ^ cd) 8 ++
    [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 9) 0 (2 ^ cd)))),
      .call ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11],
      osCst 12 (gw iters),
      .call (oqName q base folds leaf d cd mu nhs hbits fin) [.n 7, .n 9, .n 1, .n 2, .n 3, .n 4, .n 5, .n 12]
        [.n 13],
      osCp 14 10, osCp 15 11, osCp 16 13] ++
    pw.1 ++ [osCp k pw.2, .ret [.n 14, .n 15, .n 16, .n k]]

/-- `level_residual` at `q` queries over `cols` message columns, a high part of `nhs` coefficients
and `hbits` index bits, at `positions, row_d, hs, mu` (values `0 .. 3`): the chains (`HeapBuf(g^(2
(q/b + 1)))` at `4, 5`, `b = resBatch`) from `0, 0`, the batches' loop, then, when `b ∤ q`, the
rest's chains (`HeapBuf(g^(2(q%b + 1)))`) from the batches' last values, the rest's positions
`positions·g^(b·(q/b))`, the rest's loop; the last values returned. -/
def lrBody (q : ℕ) (loop1 loop2 : String) : List Stmt :=
  let nb := q / resBatch
  let r := q % resBatch
  osHeap (2 * (nb + 1)) 4 ++
    [osCst 6 (word 0 0), osLd 6 5 0, osCst 7 (word 0 0), osLd 7 5 1] ++
    osLoopCall loop1 0 nb [0, 5, 1, 2, 3] 8 ++
    [osLd 13 5 (2 * nb), osLd 14 5 (2 * nb + 1)] ++
    if r = 0 then [osCp 15 13, osCp 16 14, .ret [.n 15, .n 16]]
    else
      osHeap (2 * (r + 1)) 15 ++
        [osLd 13 16 0, osLd 14 16 1, osCst 17 (gw (resBatch * nb)), osMul 18 0 17] ++
        osLoopCall loop2 0 r [16, 18, 1, 2, 3] 19 ++
        [osLd 24 16 (2 * r), osLd 25 16 (2 * r + 1), osCp 26 24, osCp 27 25, .ret [.n 26, .n 27]]

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
