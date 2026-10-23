/-
  LeanVM.Guest.B1.Whir.QueriesT

  The expansion of `opening_queries` and of its loop helper, as templates over the shape of a
  level: the leaf rows, the leaf hash, the query sum, the Merkle path below the cap and the cap
  leaf.
-/

module

public import LeanVM.Guest.B1.Whir.Cap
public import LeanVM.Guest.B1.Opening

/-!
# The templates of `opening_queries` (TRIAGE #28, #35)

`opening_queries(cap, flags, qw, qbp, rew, g^n, base, I, blocks, depth, cd)` (G:987-1044) has 50
specializations, one per level shape. Its body allocates the query sum chain and runs the loop
`__loopK` over the queries; the loop's body (`oqLoopBody`) is, at the parameters `x` (the query
`g^i`), `N`, `rew`, `qsc`, `qw`, `qbp`, `flags`, `cap` (values `0..7`):

* the row: `R` hinted words (`I` at level 0, `base = 1`; `3I` limbs deeper) at `8 .. 8 + R`, packed
  in pairs (`pack64x2T`), and its dot product with the weights at `rew`
  (`oqRows1`, `oqRows0`), ending at `oqK1`;
* the leaf hash: the packed cells as `blocks` chained compressions (`oqLeafT`);
* the query sum `qsc[x·g] = qsc[x] + qw[x]·dot` and the query's bit run `qbp[x]` (`oqSumT`);
* `verify_merkle_path` (G:899-916, inline): the hinted children (`merkle_children`) in a frame run of
  `LIG_PATH_CAP = 80` cells, one level per path bit (`oqPathT`);
* the cap leaf: the parent's flag set and the path's top stored (`oqCapT`), then the loop's tail.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Constants -/

/-- The word of a `K` constant, as the compiler folds it. -/
def kw (a : K) : E := word (kToNat a) 0 0

theorem kw_eq (a : K) : kw a = ofK a := by
  rw [kw, word, ofBits_kToNat, ofK_eq_ofLimbs]
  rfl

theorem kw_gpowK {n : ℕ} (h : n < 2 ^ 128) : kw (gpowK n) = gen ^ n := by
  rw [kw_eq, gpowK_eq h, gen_pow_eq_ofK]

/-! ## The row -/

/-- The row's hint: `R` words at `8 ..`. -/
def oqRowHint (R : ℕ) : List Stmt :=
  [.atom (.hint (.witness "merkle_leaf_rows" (.stack ((List.range R).map fun j => .n (8 + j)))))]

/-- Four weighted row words `r .. r + 3` against `rew[wo ..]`, summed, first value `b`. -/
def dot4T (b r wo : ℕ) : List Stmt :=
  [.atom (.load (.n b) (.n 2) wo), .atom (.mul (.n (b + 1)) (.n r) (.n b)),
    .atom (.load (.n (b + 2)) (.n 2) (wo + 1)), .atom (.mul (.n (b + 3)) (.n (r + 1)) (.n (b + 2))),
    .atom (.add (.n (b + 4)) (.n (b + 1)) (.n (b + 3))),
    .atom (.load (.n (b + 5)) (.n 2) (wo + 2)), .atom (.mul (.n (b + 6)) (.n (r + 2)) (.n (b + 5))),
    .atom (.add (.n (b + 7)) (.n (b + 4)) (.n (b + 6))),
    .atom (.load (.n (b + 8)) (.n 2) (wo + 3)), .atom (.mul (.n (b + 9)) (.n (r + 3)) (.n (b + 8))),
    .atom (.add (.n (b + 10)) (.n (b + 7)) (.n (b + 9)))]

/-- Two packs of the row words `r .. r + 3`, first value `b`. -/
def pack4T (b r : ℕ) : List Stmt :=
  pack64x2T (.n r) (.n (r + 1)) b ++ pack64x2T (.n (r + 2)) (.n (r + 3)) (b + 3)

/-- Level 0's first block of four words (`base = 1`), first value `b`: two packs, the four weighted
words. -/
def rowHead1T (b r : ℕ) : List Stmt := pack4T b r ++ dot4T (b + 6) r 0

/-- Level 0's block of four words after the first, first value `b`: two packs, the four weighted
words, added to the running dot product `prev`. -/
def rowBlk1T (b r wo prev : ℕ) : List Stmt :=
  pack4T b r ++ dot4T (b + 6) r wo ++ [.atom (.add (.n (b + 17)) (.n prev) (.n (b + 16)))]

/-- Block `jb ≥ 1` of level 0's row, at `7 + I + 18·jb`. -/
def oq1Blk (I jb : ℕ) : List Stmt :=
  rowBlk1T (7 + I + 18 * jb) (8 + 4 * jb) (4 * jb) (6 + I + 18 * jb)

/-- Level 0's row: `I` words, `I / 4` blocks, the first without the running sum. -/
def oqRows1 (I : ℕ) : List Stmt :=
  oqRowHint I ++ rowHead1T (8 + I) 8 ++ ((List.range (I / 4 - 1)).map fun j => oq1Blk I (j + 1)).flatten

/-- A deeper level's pack block `jb`, at `8 + 3I + 6·jb`. -/
def oq0Pack (R jb : ℕ) : List Stmt := pack4T (8 + R + 6 * jb) (8 + 4 * jb)

/-- The packed cell `j` of a deeper level's row. -/
def oq0Pk (R j : ℕ) : ℕ := 10 + R + 3 * j

/-- An even word from its packed low limbs `pk` and its top limb `l2`, first value `c`. -/
def wordEvenT (c l2 pk : ℕ) : List Stmt :=
  [.atom (.const (.n c) (word 0 0 1)), .atom (.mul (.n (c + 1)) (.n c) (.n l2)),
    .atom (.add (.n (c + 2)) (.n pk) (.n (c + 1)))]

/-- An odd word from its low limb `l0` and its packed high limbs `pk`, first value `c`. -/
def wordOddT (c l0 pk : ℕ) : List Stmt :=
  [.atom (.const (.n c) (word 0 1 0)), .atom (.mul (.n (c + 1)) (.n c) (.n pk)),
    .atom (.add (.n (c + 2)) (.n l0) (.n (c + 1)))]

/-- A deeper level's word `jw` from its three limbs, first value `c` (G:1009-1015). -/
def oq0WordT (R jw c : ℕ) : List Stmt :=
  if jw % 2 = 0 then wordEvenT c (8 + (3 * jw + 2)) (oq0Pk R (3 * jw / 2))
  else wordOddT c (8 + 3 * jw) (oq0Pk R ((3 * jw + 1) / 2))

/-- The first value of a deeper level's words. -/
def oq0W0 (I : ℕ) : ℕ := 8 + 3 * I + 6 * (3 * I / 4)

/-- A word's weight and product, first value `c + 3`. -/
def wordDotT (c jw : ℕ) : List Stmt :=
  [.atom (.load (.n (c + 3)) (.n 2) jw), .atom (.mul (.n (c + 4)) (.n (c + 2)) (.n (c + 3)))]

/-- A deeper level's word `jw ≥ 1`, first value `W0 + 6·jw - 1`: the word, its weight, added to the
running dot product at `W0 + 6·jw - 2`. -/
def oq0Blk (I jw : ℕ) : List Stmt :=
  oq0WordT (3 * I) jw (oq0W0 I + 6 * jw - 1) ++ wordDotT (oq0W0 I + 6 * jw - 1) jw ++
    [.atom (.add (.n (oq0W0 I + 6 * jw - 1 + 5)) (.n (oq0W0 I + 6 * jw - 2))
      (.n (oq0W0 I + 6 * jw - 1 + 4)))]

/-- A deeper level's row: `3I` limbs, their packs, then the `I` words. -/
def oqRows0 (I : ℕ) : List Stmt :=
  oqRowHint (3 * I) ++ ((List.range (3 * I / 4)).map (oq0Pack (3 * I))).flatten ++
    oq0WordT (3 * I) 0 (oq0W0 I) ++ wordDotT (oq0W0 I) 0 ++
    ((List.range (I - 1)).map fun j => oq0Blk I (j + 1)).flatten

/-- The row, by level kind. -/
def oqRows (base I : ℕ) : List Stmt := if base = 1 then oqRows1 I else oqRows0 I

/-- The first value after the row; the dot product is the one before it. -/
def oqK1 (base I : ℕ) : ℕ := if base = 1 then 7 + I + 18 * (I / 4) else oq0W0 I + 6 * I - 1

/-- The packed cell `j` of the row. -/
def oqPk (base I j : ℕ) : ℕ :=
  if base = 1 then (if j / 2 = 0 then 8 + I else 7 + I + 18 * (j / 2)) + 2 + 3 * (j % 2)
  else oq0Pk (3 * I) j

/-! ## The leaf hash -/

/-- The metadata word of block `jb` of `blocks`. -/
def oqMd (blocks jb : ℕ) : E := word (64 * (jb + 1)) (if jb + 1 = blocks then 4294967295 else 0) 0

/-- A chained compression of four cells, first value `e`, from the chaining value at `st`. -/
def leafBlkT (e st p0 p1 p2 p3 : ℕ) (md : E) : List Stmt :=
  [.atom (.const (.n e) md),
    .atom (.blake2s (.n p0) (.n p1) (.n p2) (.n p3) (.n st) (.n (st + 1)) (.n (e + 1)) (.n (e + 2))
      (.n e))]

/-- Leaf block `jb ≥ 1`, first value `K1 + 3·jb + 2`, chained from `K1 + 3·jb`. -/
def oqLeafBlk (base I blocks jb : ℕ) : List Stmt :=
  leafBlkT (oqK1 base I + 3 * jb + 2) (oqK1 base I + 3 * jb) (oqPk base I (4 * jb))
    (oqPk base I (4 * jb + 1)) (oqPk base I (4 * jb + 2)) (oqPk base I (4 * jb + 3)) (oqMd blocks jb)

/-- The leaf hash: `blocks` compressions of the packed cells from the IV (G:1019-1023). -/
def oqLeafT (base I blocks : ℕ) : List Stmt :=
  [.atom (.const (.n (oqK1 base I)) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n (oqK1 base I + 1)) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n (oqK1 base I + 2)) (oqMd blocks 0)),
    .atom (.blake2s (.n (oqPk base I 0)) (.n (oqPk base I 1)) (.n (oqPk base I 2)) (.n (oqPk base I 3))
      (.n (oqK1 base I)) (.n (oqK1 base I + 1)) (.n (oqK1 base I + 3)) (.n (oqK1 base I + 4))
      (.n (oqK1 base I + 2)))] ++
    ((List.range (blocks - 1)).map fun j => oqLeafBlk base I blocks (j + 1)).flatten

/-- The first value after the leaf hash. -/
def oqK2 (base I blocks : ℕ) : ℕ := oqK1 base I + 3 * blocks + 2

/-! ## The query sum and the bit run -/

/-- `qsc[x·g] = qsc[x] + qw[x]·dot` (G:1024), then the query's bit run `qbp[x]` (G:1025). -/
def oqSumT (base I blocks : ℕ) : List Stmt :=
  let k := oqK2 base I blocks
  [.atom (.mul (.n k) (.n 3) (.n 0)), .atom (.load (.n (k + 1)) (.n k) 0),
    .atom (.mul (.n (k + 2)) (.n 4) (.n 0)), .atom (.load (.n (k + 3)) (.n (k + 2)) 0),
    .atom (.mul (.n (k + 4)) (.n (k + 3)) (.n (oqK1 base I - 1))),
    .atom (.add (.n (k + 5)) (.n (k + 1)) (.n (k + 4))), .atom (.mul (.n (k + 6)) (.n 3) (.n 0)),
    .atom (.load (.n (k + 5)) (.n (k + 6)) 1),
    .atom (.mul (.n (k + 7)) (.n 5) (.n 0)), .atom (.load (.n (k + 8)) (.n (k + 7)) 0)]

/-! ## The Merkle path -/

/-- The first hinted child of the path. -/
def oqP (base I blocks : ℕ) : ℕ := oqK2 base I blocks + 9

/-- Path level `l ≥ 1` at `L`: the direction bit, the selected child's address, the running node
stored there, the children at `C` hashed. -/
def levelT (L ptr bits l node0 node1 C : ℕ) : List Stmt :=
  [.atom (.load (.n L) (.n bits) l), .atom (.const (.n (L + 1)) (kw (gpowK (4 * l)))),
    .atom (.mul (.n (L + 2)) (.n ptr) (.n (L + 1))), .atom (.const (.n (L + 3)) (word 1 0 0)),
    .atom (.const (.n (L + 4)) (word 5 0 0)), .atom (.mul (.n (L + 5)) (.n L) (.n (L + 4))),
    .atom (.add (.n (L + 6)) (.n (L + 3)) (.n (L + 5))), .atom (.mul (.n (L + 7)) (.n (L + 2)) (.n (L + 6))),
    .atom (.load (.n node0) (.n (L + 7)) 0), .atom (.load (.n node1) (.n (L + 7)) 1),
    .atom (.const (.n (L + 8)) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n (L + 9)) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n (L + 10)) (word 64 4294967295 0)),
    .atom (.blake2s (.n C) (.n (C + 1)) (.n (C + 2)) (.n (C + 3)) (.n (L + 8)) (.n (L + 9))
      (.n (L + 11)) (.n (L + 12)) (.n (L + 10)))]

/-- Path level `l ≥ 1` of `oqPathT`, at `P + 79 + 13·l`. -/
def oqLevel (P pd l : ℕ) : List Stmt :=
  levelT (P + 79 + 13 * l) (P + 4 * pd) (P - 1) l (P + 77 + 13 * l) (P + 78 + 13 * l) (P + 4 * l)

/-- `verify_merkle_path` (G:899-916) over `pd` levels from the leaf digest at `K1 + 3·blocks`. -/
def oqPathT (base I blocks pd : ℕ) : List Stmt :=
  let P := oqP base I blocks
  let K := oqK1 base I + 3 * blocks
  [.atom (.hint (.witness "merkle_children" (.stack ((List.range (4 * pd)).map fun j => .n (P + j))))),
    .atom (.frameAddr (.n (P + 4 * pd))
      ((List.range (4 * pd)).map (fun j => .n (P + j)) ++
        (List.range (80 - 4 * pd)).map fun j => .n (P + 4 * pd + 1 + j))),
    .atom (.load (.n (P + 81)) (.n (P - 1)) 0), .atom (.const (.n (P + 82)) (word 1 0 0)),
    .atom (.const (.n (P + 83)) (word 5 0 0)), .atom (.mul (.n (P + 84)) (.n (P + 81)) (.n (P + 83))),
    .atom (.add (.n (P + 85)) (.n (P + 82)) (.n (P + 84))),
    .atom (.mul (.n (P + 86)) (.n (P + 4 * pd)) (.n (P + 85))),
    .atom (.load (.n K) (.n (P + 86)) 0), .atom (.load (.n (K + 1)) (.n (P + 86)) 1),
    .atom (.const (.n (P + 87)) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n (P + 88)) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n (P + 89)) (word 64 4294967295 0)),
    .atom (.blake2s (.n P) (.n (P + 1)) (.n (P + 2)) (.n (P + 3)) (.n (P + 87)) (.n (P + 88))
      (.n (P + 90)) (.n (P + 91)) (.n (P + 89)))] ++
    ((List.range (pd - 1)).map fun j => oqLevel P pd (j + 1)).flatten

/-! ## The cap leaf and the tail -/

/-- A cap bit at `u`: the parent's index `par` times `1 + d·c`, `d` the bit at `bits·g^off`. -/
def capBitT (u bits off par : ℕ) (c : E) : List Stmt :=
  [.atom (.const (.n u) (word 1 0 0)), .atom (.load (.n (u + 1)) (.n bits) off),
    .atom (.const (.n (u + 2)) c), .atom (.mul (.n (u + 3)) (.n (u + 1)) (.n (u + 2))),
    .atom (.add (.n (u + 4)) (.n u) (.n (u + 3))), .atom (.mul (.n (u + 5)) (.n par) (.n (u + 4)))]

/-- Cap bit `t` of `oqCapT`, at `K6 + 1 + 6t`. -/
def oqCapBit (P pd t : ℕ) : List Stmt :=
  capBitT (P + 80 + 13 * pd + 6 * t) (P - 1) (pd + 1 + t) (P + 79 + 13 * pd + 6 * t)
    (kw (1 + gpowK (2 ^ t)))

/-- The cap leaf (G:1027-1043): the parent's flag set, the path's top stored at the leaf. -/
def oqCapT (P pd cd : ℕ) (loop : String) : List Stmt :=
  let K6 := P + 79 + 13 * pd
  let K7 := K6 + 6 * cd - 5
  let par := K7 - 1
  let n0 := P + 77 + 13 * pd
  [.atom (.const (.n K6) (kw (gpowK (2 ^ (cd - 1)))))] ++
    ((List.range (cd - 1)).map (oqCapBit P pd)).flatten ++
    [.atom (.const (.n K7) (word 1 0 0)), .atom (.mul (.n (K7 + 1)) (.n 6) (.n par)),
      .atom (.load (.n K7) (.n (K7 + 1)) 0), .atom (.mul (.n (K7 + 2)) (.n par) (.n par)),
      .atom (.const (.n (K7 + 3)) (word 1 0 0)), .atom (.load (.n (K7 + 4)) (.n (P - 1)) pd),
      .atom (.const (.n (K7 + 5)) (word 3 0 0)), .atom (.mul (.n (K7 + 6)) (.n (K7 + 4)) (.n (K7 + 5))),
      .atom (.add (.n (K7 + 7)) (.n (K7 + 3)) (.n (K7 + 6))),
      .atom (.mul (.n (K7 + 8)) (.n (K7 + 2)) (.n (K7 + 7))),
      .atom (.mul (.n (K7 + 9)) (.n (K7 + 8)) (.n (K7 + 8))), .atom (.mul (.n (K7 + 10)) (.n 7) (.n (K7 + 9))),
      .atom (.load (.n n0) (.n (K7 + 10)) 0), .atom (.const (.n (K7 + 11)) (word 2 0 0)),
      .atom (.mul (.n (K7 + 12)) (.n (K7 + 11)) (.n (K7 + 8))),
      .atom (.mul (.n (K7 + 13)) (.n (K7 + 12)) (.n (K7 + 8))),
      .atom (.mul (.n (K7 + 14)) (.n 7) (.n (K7 + 13))), .atom (.load (.n (n0 + 1)) (.n (K7 + 14)) 0),
      .atom (.const (.n (K7 + 15)) (word 2 0 0)), .atom (.mul (.n (K7 + 16)) (.n 0) (.n (K7 + 15))),
      .atom (.add (.n (K7 + 17)) (.n (K7 + 16)) (.n 1)), .atom (.const (.n (K7 + 18)) (word 2 0 0)),
      .atom (.mul (.n (K7 + 19)) (.n 0) (.n (K7 + 18))),
      .callIf (.n (K7 + 17)) loop [.n (K7 + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], .ret []]

/-- The loop helper's body: one query. -/
def oqLoopBody (base I blocks pd cd : ℕ) (loop : String) : List Stmt :=
  oqRows base I ++ oqLeafT base I blocks ++ oqSumT base I blocks ++ oqPathT base I blocks pd ++
    oqCapT (oqP base I blocks) pd cd loop

/-- The body of `opening_queries`: the query sum chain from `0`, the loop, its last entry. -/
def oqBody (loop : String) : List Stmt :=
  [.atom (.const (.n 6) (word 2 0 0)), .atom (.mul (.n 7) (.n 5) (.n 6)),
    .atom (.hint (.allocDyn (.n 8) (.n 7))), .atom (.const (.n 9) (word 0 0 0)),
    .atom (.load (.n 9) (.n 8) 0), .atom (.const (.n 10) (word 1 0 0)),
    .atom (.add (.n 11) (.n 10) (.n 5)), .atom (.const (.n 12) (word 1 0 0)),
    .callIf (.n 11) loop [.n 12, .n 5, .n 4, .n 8, .n 2, .n 3, .n 1, .n 0],
    .atom (.mul (.n 13) (.n 8) (.n 5)), .atom (.load (.n 14) (.n 13) 0), .ret [.n 14]]

end
end LeanVM.Guest.B1
