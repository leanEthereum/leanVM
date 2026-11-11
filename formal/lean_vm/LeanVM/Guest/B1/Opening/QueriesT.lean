/-
  LeanVM.Guest.B1.Opening.QueriesT

  The expansion of `opening_queries` and of its loop helper as templates over the shape of a
  level: the leaf row and its dot product, the leaf hash, the Merkle path below the cap, the cap
  leaf, and the query chain.
-/

module

public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Guest.B1.Fs.Templates

/-!
# The templates of `opening_queries` (TRIAGE G #33, #39, #40)

`opening_queries(cap, flags, lam, lam_n, query_bit_ptrs, row_eq_weights, n_iters_g, odd, base, I,
leaf_cells, depth, cd)` (G:1393-1417) has 49 specializations, one per level shape (`Oq`). One
query (`opening_query`, G:1346-1390, inline, with `walk_path`, G:1308-1343) from its first
value `b` is `oqQueryT`:

* the row: `R` hinted words (`I` at level 0, `base = 1`; `3I` limbs deeper) at `b .. b + R`, packed
  in pairs (`pack64x2`), the packed cell `j` at `oqPk b R j`;
* its dot product with the weights at `wp`: `I / 8` groups of `8` words, each a sum of words times
  `wp[l]`, times `wp[8 + h]`, summed (`oqDotT`), the deeper levels' words assembled from their
  limbs first; the result at `oqDot`;
* the zero/padding run `pr .. pr + 4` (`1, 0, 0, 0, 0`), emitted by the first query of a function
  and reused by the second;
* the leaf hash: `keccak_cells` of the `R / 2` packed cells in `B = 16·(R/2)/136 + 1` blocks
  (`oqLeafT`), the padding `0x01` (the run's first cell) and `0x80` XORed into the last block;
* the path: the hinted children (`merkle_children`) in a frame run of 80 cells at `pp`, one level
  per path bit: the node stored into the child its bit selects, the children hashed (`oqLevelT`);
* the cap leaf: the parent's flag set and the node stored at the cap leaf (`oqCapT`).

The templates mirror the compiler's expansion exactly; `B1/Opening/QueriesBody*.lean` check them
against the data by kernel evaluation.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Shapes -/

/-- A level's shape: `base` (`1` at level 0), the interleave `I`, the path depth below the cap
`pd = depth - cd` and the cap depth `cd`. -/
structure Oq where
  base : ℕ
  I : ℕ
  pd : ℕ
  cd : ℕ

namespace Oq

/-- The row's hinted words. -/
def R (s : Oq) : ℕ := if s.base = 1 then s.I else 3 * s.I

/-- The words of a group of the dot product. -/
def lo (s : Oq) : ℕ := rowLo s.I

/-- The values a deeper level's word takes to assemble. -/
def tsz (s : Oq) : ℕ := if s.base = 1 then 0 else 3

/-- The values of group `0` of the dot product (the others take one more, their sum). -/
def G (s : Oq) : ℕ := (2 + s.tsz) + (s.lo - 1) * (3 + s.tsz) + 2

/-- The values of the dot product. -/
def D (s : Oq) : ℕ := s.G + (s.I / s.lo - 1) * (s.G + 1)

/-- The packed cells. -/
def ncells (s : Oq) : ℕ := s.R / 2

/-- The leaf hash's blocks. -/
def B (s : Oq) : ℕ := 16 * s.ncells / rate + 1

/-- The values of the leaf hash (`B ≥ 2`): block `0` writes 13, a middle block XORs 9 and writes 13,
the last XORs 9 with one padding constant and writes the digest's 2 (`out_cells` two). -/
def chainLen (s : Oq) : ℕ := 13 + (s.B - 2) * 22 + 12

end Oq

/-- `1 + g^(2^j)` as the compiler folds it (`K` words, `x^64 = x^4 + x^3 + x + 1`). -/
def capFac : List ℕ := [3, 5, 17, 257, 65537, 4294967297, 26]

/-! ## The row -/

/-- The packed cell `j` of a row hinted at `b`. -/
def oqPk (b R j : ℕ) : ℕ := b + R + 3 * j + 2

/-- The row's hint. -/
def oqRowT (b R : ℕ) : List Stmt :=
  [.atom (.hint (.witness "merkle_leaf_rows" (.stack ((List.range R).map fun j ↦ .n (b + j)))))]

/-- Pack `j` of the row (`pack64x2(row[2j], row[2j+1])`). -/
def oqPackT (b R j : ℕ) : List Stmt :=
  [.atom (.assertInK (.n (b + 2 * j)) (.n (b + 2 * j + 1))),
    .atom (.const (.n (b + R + 3 * j)) (word 0 1 0)),
    .atom (.mul (.n (b + R + 3 * j + 1)) (.n (b + R + 3 * j)) (.n (b + 2 * j + 1))),
    .atom (.add (.n (b + R + 3 * j + 2)) (.n (b + 2 * j)) (.n (b + R + 3 * j + 1)))]

/-- The row's packs. -/
def oqPacksT (b R : ℕ) : List Stmt := ((List.range (R / 2)).map (oqPackT b R)).flatten

/-- The first value of the dot product. -/
def oqK1 (b R : ℕ) : ℕ := b + R + 3 * (R / 2)

/-! ## The dot product -/

/-- The first value of group `h`. -/
def oqGs (s : Oq) (b h : ℕ) : ℕ := oqK1 b s.R + (if h = 0 then 0 else h * (s.G + 1) - 1)

/-- The first value of term `l` of group `h`. -/
def oqTs (s : Oq) (b h l : ℕ) : ℕ :=
  oqGs s b h + (if l = 0 then 0 else (2 + s.tsz) + (l - 1) * (3 + s.tsz))

/-- The row word of term `l` of group `h`: the hinted word at level 0, the assembled one deeper. -/
def oqWordV (s : Oq) (b h l : ℕ) : ℕ :=
  if s.base = 1 then b + (s.lo * h + l) else oqTs s b h l + 2

/-- A deeper level's word `jw` from its limbs, first value `t`. -/
def oqWordT (s : Oq) (b jw t : ℕ) : List Stmt :=
  if jw % 2 = 0 then
    [.atom (.const (.n t) (word 0 0 1)), .atom (.mul (.n (t + 1)) (.n t) (.n (b + (3 * jw + 2)))),
      .atom (.add (.n (t + 2)) (.n (oqPk b s.R (3 * jw / 2))) (.n (t + 1)))]
  else
    [.atom (.const (.n t) (word 0 1 0)),
      .atom (.mul (.n (t + 1)) (.n t) (.n (oqPk b s.R ((3 * jw + 1) / 2)))),
      .atom (.add (.n (t + 2)) (.n (b + 3 * jw)) (.n (t + 1)))]

/-- The running part of group `h` after its term `l`. -/
def oqPart (s : Oq) (b h l : ℕ) : ℕ :=
  oqTs s b h l + s.tsz + (if l = 0 then 1 else 2)

/-- Term `l` of group `h`: the word (deeper levels), its weight `wp[l]`, the product, the sum. -/
def oqTermT (s : Oq) (wp : V) (b h l : ℕ) : List Stmt :=
  (if s.base = 1 then [] else oqWordT s b (s.lo * h + l) (oqTs s b h l)) ++
    [.atom (.load (.n (oqTs s b h l + s.tsz)) wp l),
      .atom (.mul (.n (oqTs s b h l + s.tsz + 1)) (.n (oqWordV s b h l)) (.n (oqTs s b h l + s.tsz)))] ++
    (if l = 0 then [] else
      [.atom (.add (.n (oqTs s b h l + s.tsz + 2)) (.n (oqPart s b h (l - 1)))
        (.n (oqTs s b h l + s.tsz + 1)))])

/-- The dot product after group `h`. -/
def oqDotAfter (s : Oq) (b h : ℕ) : ℕ := oqGs s b h + s.G - (if h = 0 then 1 else 0)

/-- Group `h`: its terms, times `wp[lo + h]`, added to the running dot product. -/
def oqGroupT (s : Oq) (wp : V) (b h : ℕ) : List Stmt :=
  ((List.range s.lo).map (oqTermT s wp b h)).flatten ++
    [.atom (.load (.n (oqGs s b h + s.G - 2)) wp (s.lo + h)),
      .atom (.mul (.n (oqGs s b h + s.G - 1)) (.n (oqGs s b h + s.G - 2))
        (.n (oqPart s b h (s.lo - 1))))] ++
    (if h = 0 then [] else
      [.atom (.add (.n (oqGs s b h + s.G)) (.n (oqDotAfter s b (h - 1))) (.n (oqGs s b h + s.G - 1)))])

/-- The dot product. -/
def oqDotT (s : Oq) (wp : V) (b : ℕ) : List Stmt :=
  ((List.range (s.I / s.lo)).map (oqGroupT s wp b)).flatten

/-- The value of the dot product. -/
def oqDot (s : Oq) (b : ℕ) : ℕ := oqDotAfter s b (s.I / s.lo - 1)

/-! ## The padding run and the leaf hash -/

/-- The first value of block `k` of the leaf hash. -/
def oqBs (kL k : ℕ) : ℕ := if k = 0 then kL else kL + 13 + (k - 1) * 22

/-- Cell `c` of the state after block `k` (`k < B`): block `k`'s outputs. -/
def oqOut (s : Oq) (kL k c : ℕ) : ℕ :=
  if k = 0 then kL + c else if k + 1 = s.B then oqBs kL k + 10 + c else oqBs kL k + 9 + c

/-- The cells block `k` writes: the state's thirteen, the last block the digest's two. -/
def oqOutN (s : Oq) (k : ℕ) : ℕ := if k + 1 = s.B then 2 else 13

/-- The `0x80` padding constant of the last block's cell `8` (`byteCell (136B - 1) 0x80`). -/
def oqW80 (s : Oq) : E :=
  if (rate * s.B - 1) % 16 < 8 then word (2 ^ 63) 0 0 else word 0 (2 ^ 63) 0

/-- Block `k ≥ 1`'s input cell `c < 9`: the previous output plus the packed cell, the padding
`0x01` (the run's first cell) or the padding `0x80` (a constant), as the cell index is a row cell,
the cell after it or the next. -/
def oqXorT (s : Oq) (b pr kL k c : ℕ) : List Stmt :=
  let m := 17 * k / 2 + c
  let t := oqBs kL k + c
  if m < s.ncells then [.atom (.add (.n t) (.n (oqOut s kL (k - 1) c)) (.n (oqPk b s.R m)))]
  else if m = s.ncells then [.atom (.add (.n t) (.n (oqOut s kL (k - 1) c)) (.n pr))]
  else [.atom (.const (.n t) (oqW80 s)), .atom (.add (.n (t + 1)) (.n (oqOut s kL (k - 1) c)) (.n t))]

/-- Block `k ≥ 1`'s input cell `c < 9`'s value. -/
def oqIn (s : Oq) (kL k c : ℕ) : ℕ :=
  if 17 * k / 2 + c ≤ s.ncells then oqBs kL k + c else oqBs kL k + c + 1

/-- Block `k` of the leaf hash. -/
def oqBlockT (s : Oq) (b pr kL k : ℕ) : List Stmt :=
  if k = 0 then
    [.atom (.keccak (((List.range 9).map fun c ↦ .n (oqPk b s.R c)) ++
        [.n (pr + 1), .n (pr + 2), .n (pr + 3), .n (pr + 4)])
      ((List.range (oqOutN s 0)).map fun c ↦ .n (oqOut s kL 0 c)) (Keccak.inLayout 0)
        (Keccak.outLayout s.B 0))]
  else
    ((List.range 9).map (oqXorT s b pr kL k)).flatten ++
      [.atom (.keccak (((List.range 9).map fun c ↦ .n (oqIn s kL k c)) ++
          ((List.range 4).map fun c ↦ .n (oqOut s kL (k - 1) (9 + c))))
        ((List.range (oqOutN s k)).map fun c ↦ .n (oqOut s kL k c)) (Keccak.inLayout k)
          (Keccak.outLayout s.B k))]

/-- The leaf hash. -/
def oqLeafT (s : Oq) (b pr kL : ℕ) : List Stmt :=
  ((List.range s.B).map (oqBlockT s b pr kL)).flatten

/-! ## The path (`walk_path`, a function of its own at 40f877dc) -/

/-- The path's windows: six levels each from the bottom, the last the remainder
(`walk_path`, lean_ethereum.py:1308-1343 at 40f877dc). -/
def oqNpw (s : Oq) : ℕ := (s.pd + 5) / 6

/-- Window `i`'s levels. -/
def oqWw (s : Oq) (i : ℕ) : ℕ := if i + 1 = oqNpw s then s.pd - 6 * i else 6

/-- The values window `i` places before its hoisted `0x80`: window `0` the function's padding run
(its first keccak), the others none. -/
def oqWo (i : ℕ) : ℕ := if i = 0 then 5 else 0

/-- Window `i`'s first value: its window word, then (window `0`) the padding run, then the hoisted
`0x80`, then the arms. The children hinted at `ch .. ch + 4pd - 1` come first. -/
def oqWk (s : Oq) (ch : ℕ) : ℕ → ℕ
  | 0 => ch + 4 * s.pd
  | i + 1 => oqWk s ch i + 4 + oqWo i + 3 * oqWw s i * 2 ^ oqWw s i

/-- The match targets of window `i`: the node after its levels. -/
def oqWT (s : Oq) (ch i : ℕ) : ℕ := oqWk s ch i + 2 + oqWo i + 3 * oqWw s i

/-- Cell `c` of the node window `i` starts from: the node the walk is given at `kL, kL + 1`, then
the previous window's targets; window `oqNpw` is the cap leaf. -/
def oqNd (s : Oq) (kL ch i c : ℕ) : ℕ :=
  if i = 0 then kL + c else oqWT s ch (i - 1) + c

/-- Arm `a`'s first value in window `i` (the first arm's targets follow it). -/
def oqArmK (s : Oq) (ch i a : ℕ) : ℕ :=
  if a = 0 then oqWk s ch i + 2 + oqWo i else oqWk s ch i + 4 + oqWo i + 3 * oqWw s i * a

/-- One level `l` of an arm from `K`: the running node `n0, n1` hashed with its sibling on the
side the bit leaves (`keccak([n0, n1], path[4l+2:4l+4])` at bit `0`, `keccak(path[4l:4l+2],
[n0, n1])` at `1`), the zero/padding run at `pr`. -/
def oqStepT (pr ch l K n0 n1 : ℕ) (bit : Bool) : List Stmt :=
  [.atom (.const (.n K) (word (2 ^ 63) 0 0)),
    .atom (.keccak ((if bit then [.n (ch + 4 * l), .n (ch + 4 * l + 1), .n n0, .n n1]
        else [.n n0, .n n1, .n (ch + 4 * l + 2), .n (ch + 4 * l + 3)]) ++
      [.n pr, .n (pr + 1), .n (pr + 2), .n (pr + 3), .n K, .n (pr + 1), .n (pr + 2), .n (pr + 3),
        .n (pr + 4)]) [.n (K + 1), .n (K + 2)] false false)]

/-- The node before level `r` of arm `a` of window `i`. -/
def oqArmN (s : Oq) (kL ch i a r c : ℕ) : ℕ :=
  if r = 0 then oqNd s kL ch i c else oqArmK s ch i a + 3 * (r - 1) + 1 + c

/-- Arm `a` of window `i` (`walk_window`): its levels, the order bits `a`'s, then the node copied
into the match's targets. -/
def oqArmT (s : Oq) (pr kL ch i a : ℕ) : List Stmt :=
  ((List.range (oqWw s i)).map fun r ↦ oqStepT pr ch (6 * i + r) (oqArmK s ch i a + 3 * r)
      (oqArmN s kL ch i a r 0) (oqArmN s kL ch i a r 1) (a.testBit r)).flatten ++
    [.atom (.copy (.n (oqWT s ch i)) (.n (oqArmN s kL ch i a (oqWw s i) 0))),
      .atom (.copy (.n (oqWT s ch i + 1)) (.n (oqArmN s kL ch i a (oqWw s i) 1)))]

/-- The zero/padding run (`keccak_pad_run`): `1`, then four zeros. -/
def oqPadT (pr : ℕ) : List Stmt :=
  [.atom (.const (.n pr) (word 1 0 0)), .atom (.const (.n (pr + 1)) (word 0 0 0)),
    .atom (.const (.n (pr + 2)) (word 0 0 0)), .atom (.const (.n (pr + 3)) (word 0 0 0)),
    .atom (.const (.n (pr + 4)) (word 0 0 0))]

/-- Window `i`: its word read, (window `0`) the padding run at `pr`, the hoisted `0x80`, the
dispatch on the word's log. -/
def oqWinT (s : Oq) (bp : V) (pr kL ch i : ℕ) : List Stmt :=
  [.atom (.load (.n (oqWk s ch i)) bp i)] ++ (if i = 0 then oqPadT pr else []) ++
    [.atom (.const (.n (oqWk s ch i + 1 + oqWo i)) (word (2 ^ 63) 0 0)),
      .match_ (.n (oqWk s ch i)) ((List.range (2 ^ oqWw s i)).map (oqArmT s pr kL ch i))]

/-- The path: the children hinted, the windows. -/
def oqPathT (s : Oq) (bp : V) (pr kL ch : ℕ) : List Stmt :=
  [.atom (.hint (.witness "merkle_children" (.stack ((List.range (4 * s.pd)).map fun j ↦ .n (ch + j)))))] ++
    ((List.range (oqNpw s)).map (oqWinT s bp pr kL ch)).flatten

/-! ## The cap leaf -/

/-- The cap section's first value. -/
def oqCq (s : Oq) (ch : ℕ) : ℕ := oqWk s ch (oqNpw s)

/-- The cap leaf (`cd ≥ 2`): the child bit `g^b` and the parent index `q = g^Q` read from the last
two windows, the parent's flag set, the node stored at the cap leaf `cap·q⁴·g^(2b)` at
`2^(cd+1)`. -/
def oqCapT (s : Oq) (bp cap flags : V) (kL ch : ℕ) : List Stmt :=
  let k := oqCq s ch
  [.atom (.load (.n k) bp (oqNpw s)), .atom (.load (.n (k + 1)) bp (oqNpw s + 1)),
    .atom (.mul (.n (k + 2)) flags (.n (k + 1))), .atom (.const (.n (k + 3)) (word 1 0 0)),
    .atom (.load (.n (k + 3)) (.n (k + 2)) (2 ^ (s.cd - 1))),
    .atom (.mul (.n (k + 4)) (.n (k + 1)) (.n (k + 1))), .atom (.mul (.n (k + 5)) cap (.n (k + 4))),
    .atom (.mul (.n (k + 6)) (.n (k + 5)) (.n (k + 4))), .atom (.mul (.n (k + 7)) (.n k) (.n k)),
    .atom (.mul (.n (k + 8)) (.n (k + 6)) (.n (k + 7))),
    .atom (.load (.n (oqNd s kL ch (oqNpw s) 0)) (.n (k + 8)) (2 ^ (s.cd + 1))),
    .atom (.load (.n (oqNd s kL ch (oqNpw s) 1)) (.n (k + 8)) (2 ^ (s.cd + 1) + 1))]

/-! ## `walk_path` -/

/-- `walk_path`'s children: after its parameters `n0, n1, wins, cap, flags` (`0 .. 4`). -/
def wpCh : ℕ := 5

/-- `walk_path`'s padding run: after its children and its first window's word. -/
def wpPr (s : Oq) : ℕ := wpCh + 4 * s.pd + 1

/-- **`walk_path__L{pd}_L{cd}`'s body** (lean_ethereum.py:1308-1343 at 40f877dc): the path from the
node `n0, n1` (`.n 0`, `.n 1`) by the windows at `wins` (`.n 2`), the cap leaf into `cap`
(`.n 3`), the flag into `flags` (`.n 4`). -/
def wpBodyT (s : Oq) : List Stmt :=
  oqPathT s (.n 2) (wpPr s) 0 wpCh ++ oqCapT s (.n 2) (.n 3) (.n 4) 0 wpCh ++ [.ret []]

/-- The deployed specializations of `walk_path`, `(pd, cd, name)` (a name built by `++ toString`
does not reduce in a `module`'s kernel). -/
def walkPathNames : List (ℕ × ℕ × String) :=
  [(6, 6, "walk_path__L6_L6"),
    (6, 7, "walk_path__L6_L7"),
    (12, 2, "walk_path__L12_L2"),
    (12, 3, "walk_path__L12_L3"),
    (12, 4, "walk_path__L12_L4"),
    (12, 5, "walk_path__L12_L5"),
    (12, 6, "walk_path__L12_L6"),
    (12, 7, "walk_path__L12_L7"),
    (12, 8, "walk_path__L12_L8"),
    (18, 2, "walk_path__L18_L2"),
    (18, 3, "walk_path__L18_L3"),
    (18, 4, "walk_path__L18_L4"),
    (18, 5, "walk_path__L18_L5"),
    (18, 6, "walk_path__L18_L6"),
    (18, 7, "walk_path__L18_L7"),
    (18, 8, "walk_path__L18_L8"),
    (24, 2, "walk_path__L24_L2"),
    (24, 3, "walk_path__L24_L3"),
    (24, 4, "walk_path__L24_L4"),
    (24, 5, "walk_path__L24_L5"),
    (24, 6, "walk_path__L24_L6")]

/-- The specialization of `walk_path` a shape's queries call. -/
def oqWalkOf (s : Oq) : String :=
  ((walkPathNames.find? fun p ↦ p.1 == s.pd && p.2.1 == s.cd).map (·.2.2)).getD ""

/-! ## One query -/

/-- The first value of the leaf hash: after the dot product, and the padding run if emitted. -/
def oqKL (s : Oq) (b : ℕ) (emit : Bool) : ℕ := oqK1 b s.R + s.D + (if emit then 5 else 0)

/-- The padding run's first value. -/
def oqPr (s : Oq) (b : ℕ) (emit : Bool) (pr : ℕ) : ℕ := if emit then oqK1 b s.R + s.D else pr

/-- The first value after the leaf hash. -/
def oqCh (s : Oq) (b : ℕ) (emit : Bool) : ℕ := oqKL s b emit + s.chainLen

/-- **One query** from the value `b`, its windows at `bp`, emitting the padding run (`emit`) or
reusing the one at `pr`: the row, its dot product, the leaf hash, and the call of `walk`
(`walk_path__L{pd}_L{cd}`) on the leaf digest, the windows, the cap and the flags. -/
def oqQueryT (s : Oq) (bp cap flags wp : V) (b : ℕ) (emit : Bool) (pr : ℕ) (walk : String) :
    List Stmt :=
  oqRowT b s.R ++ oqPacksT b s.R ++ oqDotT s wp b ++ (if emit then oqPadT (oqK1 b s.R + s.D) else []) ++
    oqLeafT s b (oqPr s b emit pr) (oqKL s b emit) ++
    [.call walk [.n (oqOut s (oqKL s b emit) (s.B - 1) 0), .n (oqOut s (oqKL s b emit) (s.B - 1) 1), bp,
      cap, flags] []]

/-- The first value after a query. -/
def oqEnd (s : Oq) (b : ℕ) (emit : Bool) : ℕ := oqCh s b emit

/-! ## The loop and the function -/

/-- The first value of the second query of a level-0 iteration. -/
def oqE1 (s : Oq) : ℕ := oqEnd s 11 true

/-- The first value of a level-0 iteration's chain step. -/
def oqC1 (s : Oq) : ℕ := oqEnd s (oqE1 s + 1) false

/-- The atoms and calls of the loop helper's body at level 0 (`base = 1`: two queries an
iteration, from the window pointers at `qptrs·x²` offsets `odd`, `odd + 1`), on its parameters
`x, N, qptrs, cap, flags, wp, chain, μ` (`0 .. 7`): the queries, the chain step
`chain[x·g] = ((chain[x] + d0)·μ + d1)·μ`, the guard `x·g + N` and the next `x·g`. -/
def oqLoop1A (s : Oq) (odd : ℕ) (walk : String) : List Stmt :=
  let e1 := oqE1 s
  let c := oqC1 s
  [.atom (.mul (.n 8) (.n 2) (.n 0)), .atom (.mul (.n 9) (.n 8) (.n 0)), .atom (.load (.n 10) (.n 9) odd)] ++
    oqQueryT s (.n 10) (.n 3) (.n 4) (.n 5) 11 true 0 walk ++
    [.atom (.load (.n e1) (.n 9) (odd + 1))] ++
    oqQueryT s (.n e1) (.n 3) (.n 4) (.n 5) (e1 + 1) false (oqK1 11 s.R + s.D) walk ++
    [.atom (.mul (.n c) (.n 6) (.n 0)), .atom (.load (.n (c + 1)) (.n c) 0),
      .atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 11))),
      .atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 7)),
      .atom (.add (.n (c + 4)) (.n (c + 3)) (.n (oqDot s (e1 + 1)))),
      .atom (.mul (.n (c + 5)) (.n (c + 4)) (.n 7)), .atom (.mul (.n (c + 6)) (.n 6) (.n 0)),
      .atom (.load (.n (c + 5)) (.n (c + 6)) 1),
      .atom (.const (.n (c + 7)) (word 2 0 0)), .atom (.mul (.n (c + 8)) (.n 0) (.n (c + 7))),
      .atom (.add (.n (c + 9)) (.n (c + 8)) (.n 1)), .atom (.const (.n (c + 10)) (word 2 0 0)),
      .atom (.mul (.n (c + 11)) (.n 0) (.n (c + 10)))]

/-- The loop helper's body at level 0. -/
def oqLoop1T (s : Oq) (odd : ℕ) (walk name : String) : List Stmt :=
  oqLoop1A s odd walk ++
    [.callIf (.n (oqC1 s + 9)) name
      [.n (oqC1 s + 11), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], .ret []]

/-- The first value of a deeper iteration's chain step. -/
def oqC0 (s : Oq) : ℕ := oqEnd s 10 true

/-- The atoms and the call of the loop helper's body deeper (`base = 0`: one query an iteration,
from the window pointer `qptrs[x]`). -/
def oqLoop0A (s : Oq) (walk : String) : List Stmt :=
  let c := oqC0 s
  [.atom (.mul (.n 8) (.n 2) (.n 0)), .atom (.load (.n 9) (.n 8) 0)] ++
    oqQueryT s (.n 9) (.n 3) (.n 4) (.n 5) 10 true 0 walk ++
    [.atom (.mul (.n c) (.n 6) (.n 0)), .atom (.load (.n (c + 1)) (.n c) 0),
      .atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 10))),
      .atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 7)), .atom (.mul (.n (c + 4)) (.n 6) (.n 0)),
      .atom (.load (.n (c + 3)) (.n (c + 4)) 1),
      .atom (.const (.n (c + 5)) (word 2 0 0)), .atom (.mul (.n (c + 6)) (.n 0) (.n (c + 5))),
      .atom (.add (.n (c + 7)) (.n (c + 6)) (.n 1)), .atom (.const (.n (c + 8)) (word 2 0 0)),
      .atom (.mul (.n (c + 9)) (.n 0) (.n (c + 8)))]

/-- The loop helper's body deeper. -/
def oqLoop0T (s : Oq) (walk name : String) : List Stmt :=
  oqLoop0A s walk ++
    [.callIf (.n (oqC0 s + 7)) name
      [.n (oqC0 s + 9), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], .ret []]

/-- The first value after the function's start. -/
def oqMK (s : Oq) (odd : ℕ) : ℕ := if odd = 1 then oqEnd s 13 true + 1 else 13

/-- The atoms and the call of the function's start, on its parameters `cap, flags, λ, λ_n, qptrs,
wp, N` (`0 .. 6`): `μ` with `1 = μ·λ`, the chain allocated, its start (the odd first query's value
times `μ`, or `0`), the loop's guard `1 + N` and start `1`. -/
def oqMainA (s : Oq) (odd : ℕ) (walk : String) : List Stmt :=
  let k := oqMK s odd
  [.atom (.const (.n 7) (word 1 0 0)), .atom (.mul (.n 7) (.n 8) (.n 2)),
    .atom (.const (.n 9) (word 2 0 0)), .atom (.mul (.n 10) (.n 6) (.n 9)),
    .atom (.hint (.allocDyn (.n 11) (.n 10)))] ++
  (if odd = 1 then
      [.atom (.load (.n 12) (.n 4) 0)] ++ oqQueryT s (.n 12) (.n 0) (.n 1) (.n 5) 13 true 0 walk ++
        [.atom (.mul (.n (k - 1)) (.n (oqDot s 13)) (.n 8)), .atom (.load (.n (k - 1)) (.n 11) 0)]
    else [.atom (.const (.n 12) (word 0 0 0)), .atom (.load (.n 12) (.n 11) 0)]) ++
  [.atom (.const (.n k) (word 1 0 0)), .atom (.add (.n (k + 1)) (.n k) (.n 6)),
    .atom (.const (.n (k + 2)) (word 1 0 0))]

/-- The function's body: the start, the loop, the chain's end times `λ_n`. -/
def oqMainT (s : Oq) (odd : ℕ) (walk loop : String) : List Stmt :=
  let k := oqMK s odd
  oqMainA s odd walk ++
    [.callIf (.n (k + 1)) loop [.n (k + 2), .n 6, .n 4, .n 0, .n 1, .n 5, .n 11, .n 8],
      .atom (.mul (.n (k + 3)) (.n 11) (.n 6)), .atom (.load (.n (k + 4)) (.n (k + 3)) 0),
      .atom (.mul (.n (k + 5)) (.n (k + 4)) (.n 3)), .ret [.n (k + 5)]]

end
end LeanVM.Guest.B1
