/-
  LeanVM.Guest.B1.Opening.QueriesT

  The expansion of `opening_queries` and of its loop helper as templates over the shape of a
  level: the leaf row, the leaf hash, the Merkle path below the cap, the cap leaf, the row's fold
  and, at the final level, the final polynomial's check; and the query chain.
-/

module

public import LeanVM.Guest.B1.Opening.Interface
public import LeanVM.Guest.B1.Fs.Templates

/-!
# The templates of `opening_queries`

`opening_queries(cap, flags, lam_inv, coefs, hs, positions, query_win_ptrs, n_iters_g)`
(`crates/rec_aggregation/guests/lean_ethereum.py`) has 73 specializations, one per level shape
(`Oq`). One query (`opening_query`, inline, with `walk_path` and `novel_eval`) from its first
value `b`, at the point `x`, is `oqQueryT`:

* the row: `I = 2^folds` hinted words at `b .. b + I`; at level 0 (`base = 1`) packed in pairs
  (`pack64x2`, which proves both in `K`), the packed cell `j` at `oqPk`; deeper, the cells are the
  row itself;
* the zero/padding run `pr .. pr + 4` (`1, 0, 0, 0, 0`), emitted by the first query of a function
  and reused by the second;
* the leaf hash: `keccak_cells` of the `ncells` cells in `B = 16·ncells/136 + 1` blocks
  (`oqLeafT`), the padding `0x01` and `0x80` XORed into the last block: the run's first cell and a
  constant, or one constant holding both when they share a cell;
* the call of `walk_path` on the leaf digest, the windows, the cap and the flags;
* the fold (`oqFoldT`): round `j` reads `α, β, θ` at `coefs[3j ..]`, `t = α + β·x`, its inverse
  (`1 = t⁻¹·t`), `r = θ + t⁻¹`, the scale `Π t` so far, and folds the lane pairs `lo + r·hi`;
  the value is the scale times the last lane;
* at the final level (`oqFinT`): the chain `W_0 = x`, `W_(i+1) = W_i (W_i + vs_i)`, the novel sum
  of the `n_hs` words at `hs` folded the lowest bit first (`nvLevelT`), asserted equal to the
  value; the query returns `0`.

The templates mirror the compiler's expansion exactly; `B1/Opening/QueriesBody*.lean` check them
against the data by kernel evaluation.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Shapes -/

/-- A level's shape: `base` (`1` at level 0), the fold rounds `folds`, the path depth below the
cap `pd = depth - cd`, the cap depth `cd`; at the final level (`final = 1`) the vanishing
constants `vs` (`mu` of them), the final coefficients `nHs` and their index bits `hsBits`. -/
structure Oq where
  base : ℕ
  folds : ℕ
  pd : ℕ
  cd : ℕ
  final : ℕ
  vs : List ℕ
  nHs : ℕ
  hsBits : ℕ

namespace Oq

/-- The row's hinted words, the lanes: `2^folds`. -/
def I (s : Oq) : ℕ := 2 ^ s.folds

/-- The leaf's cells: the packed pairs at level 0, the row's words deeper. -/
def ncells (s : Oq) : ℕ := if s.base = 1 then s.I / 2 else s.I

/-- The leaf hash's blocks. -/
def B (s : Oq) : ℕ := 16 * s.ncells / rate + 1

/-- The values of the leaf hash (`B ≥ 2`): block `0` writes 13, a middle block XORs 9 and writes 13,
the last XORs 9 with one padding constant and writes the digest's 2 (`out_cells` two). -/
def chainLen (s : Oq) : ℕ := 13 + (s.B - 2) * 22 + 12

/-- The vanishing constants' count, `mu`. -/
def mu (s : Oq) : ℕ := s.vs.length

end Oq

/-- `1 + g^(2^j)` as the compiler folds it (`K` words, `x^64 = x^4 + x^3 + x + 1`). -/
def capFac : List ℕ := [3, 5, 17, 257, 65537, 4294967297, 26]

/-! ## The row -/

/-- The row's hint: `I` words from `b`. -/
def oqRowT (b I : ℕ) : List Stmt :=
  [.atom (.hint (.witness "merkle_leaf_rows" (.stack ((List.range I).map fun j ↦ .n (b + j)))))]

/-- Pack `j` of a level-0 row (`pack64x2(row[2j], row[2j+1])`). -/
def oqPackT (b I j : ℕ) : List Stmt :=
  [.atom (.assertInK (.n (b + 2 * j)) (.n (b + 2 * j + 1))),
    .atom (.const (.n (b + I + 3 * j)) (word 0 1)),
    .atom (.mul (.n (b + I + 3 * j + 1)) (.n (b + I + 3 * j)) (.n (b + 2 * j + 1))),
    .atom (.add (.n (b + I + 3 * j + 2)) (.n (b + 2 * j)) (.n (b + I + 3 * j + 1)))]

/-- The row's packs. -/
def oqPacksT (b I : ℕ) : List Stmt := ((List.range (I / 2)).map (oqPackT b I)).flatten

/-- The leaf's cell `j`: the pack at level 0, the row's word deeper. -/
def oqPk (s : Oq) (b j : ℕ) : ℕ := if s.base = 1 then b + s.I + 3 * j + 2 else b + j

/-- The row and (level 0) its packs. -/
def oqPrepT (s : Oq) (b : ℕ) : List Stmt :=
  oqRowT b s.I ++ (if s.base = 1 then oqPacksT b s.I else [])

/-- The first value after the row and its packs. -/
def oqK1 (s : Oq) (b : ℕ) : ℕ := b + s.I + (if s.base = 1 then 3 * (s.I / 2) else 0)

/-! ## The padding run and the leaf hash -/

/-- The zero/padding run (`keccak_pad_run`): `1`, then four zeros. -/
def oqPadT (pr : ℕ) : List Stmt :=
  [.atom (.const (.n pr) (word 1 0)), .atom (.const (.n (pr + 1)) (word 0 0)),
    .atom (.const (.n (pr + 2)) (word 0 0)), .atom (.const (.n (pr + 3)) (word 0 0)),
    .atom (.const (.n (pr + 4)) (word 0 0))]

/-- The first value of block `k` of the leaf hash. -/
def oqBs (kL k : ℕ) : ℕ := if k = 0 then kL else kL + 13 + (k - 1) * 22

/-- Cell `c` of the state after block `k` (`k < B`): block `k`'s outputs. -/
def oqOut (s : Oq) (kL k c : ℕ) : ℕ :=
  if k = 0 then kL + c else if k + 1 = s.B then oqBs kL k + 10 + c else oqBs kL k + 9 + c

/-- The cells block `k` writes: the state's thirteen, the last block the digest's two. -/
def oqOutN (s : Oq) (k : ℕ) : ℕ := if k + 1 = s.B then 2 else 13

/-- The `0x80` padding constant of the last block's cell `8` (`byteCell (136B - 1) 0x80`). -/
def oqW80 (s : Oq) : E :=
  if (rate * s.B - 1) % 16 < 8 then word (2 ^ 63) 0 else word 0 (2 ^ 63)

/-- The last block's cell `8` when it holds both paddings, `0x01` at its first byte. -/
def oqW81 (s : Oq) : E :=
  if (rate * s.B - 1) % 16 < 8 then word (2 ^ 63 + 1) 0 else word 1 (2 ^ 63)

/-- Whether block `k`'s input cell `c` is a constant XORed in (two values): the `0x80` cell. -/
def oqTwo (s : Oq) (k c : ℕ) : Bool := s.ncells < 17 * k / 2 + c || (17 * k / 2 + c = s.ncells && c = 8)

/-- Block `k ≥ 1`'s input cell `c < 9`: the previous output plus the leaf's cell, the padding
`0x01` (the run's first cell), or a constant (`0x80`, or both paddings). -/
def oqXorT (s : Oq) (b pr kL k c : ℕ) : List Stmt :=
  let m := 17 * k / 2 + c
  let t := oqBs kL k + c
  if m < s.ncells then [.atom (.add (.n t) (.n (oqOut s kL (k - 1) c)) (.n (oqPk s b m)))]
  else if oqTwo s k c then
    [.atom (.const (.n t) (if m = s.ncells then oqW81 s else oqW80 s)),
      .atom (.add (.n (t + 1)) (.n (oqOut s kL (k - 1) c)) (.n t))]
  else [.atom (.add (.n t) (.n (oqOut s kL (k - 1) c)) (.n pr))]

/-- Block `k ≥ 1`'s input cell `c < 9`'s value. -/
def oqIn (s : Oq) (kL k c : ℕ) : ℕ :=
  if oqTwo s k c then oqBs kL k + c + 1 else oqBs kL k + c

/-- Block `k` of the leaf hash. -/
def oqBlockT (s : Oq) (b pr kL k : ℕ) : List Stmt :=
  if k = 0 then
    [.atom (.keccak (((List.range 9).map fun c ↦ .n (oqPk s b c)) ++
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

/-! ## The path (`walk_path`, a function of its own) -/

/-- The path's windows: six levels each from the bottom, the last the remainder
(`walk_path`, lean_ethereum.py, `walk_path`). -/
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
  [.atom (.const (.n K) (word (2 ^ 63) 0)),
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

/-- Window `i`: its word read, (window `0`) the padding run at `pr`, the hoisted `0x80`, the
dispatch on the word's log. -/
def oqWinT (s : Oq) (bp : V) (pr kL ch i : ℕ) : List Stmt :=
  [.atom (.load (.n (oqWk s ch i)) bp i)] ++ (if i = 0 then oqPadT pr else []) ++
    [.atom (.const (.n (oqWk s ch i + 1 + oqWo i)) (word (2 ^ 63) 0)),
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
    .atom (.mul (.n (k + 2)) flags (.n (k + 1))), .atom (.const (.n (k + 3)) (word 1 0)),
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

/-- **`walk_path__L{pd}_L{cd}`'s body** (lean_ethereum.py, `walk_path`): the path from the
node `n0, n1` (`.n 0`, `.n 1`) by the windows at `wins` (`.n 2`), the cap leaf into `cap`
(`.n 3`), the flag into `flags` (`.n 4`). -/
def wpBodyT (s : Oq) : List Stmt :=
  oqPathT s (.n 2) (wpPr s) 0 wpCh ++ oqCapT s (.n 2) (.n 3) (.n 4) 0 wpCh ++ [.ret []]

/-- The deployed specializations of `walk_path`, `(pd, cd, name)` (a name built by `++ toString`
does not reduce in a `module`'s kernel). -/
def walkPathNames : List (ℕ × ℕ × String) :=
  [(14, 4, "walk_path__L14_L4"),
    (15, 4, "walk_path__L15_L4"),
    (16, 4, "walk_path__L16_L4"),
    (17, 4, "walk_path__L17_L4"),
    (18, 4, "walk_path__L18_L4"),
    (10, 5, "walk_path__L10_L5"),
    (11, 5, "walk_path__L11_L5"),
    (12, 5, "walk_path__L12_L5"),
    (13, 5, "walk_path__L13_L5"),
    (14, 5, "walk_path__L14_L5"),
    (15, 5, "walk_path__L15_L5"),
    (16, 5, "walk_path__L16_L5"),
    (17, 5, "walk_path__L17_L5"),
    (18, 5, "walk_path__L18_L5"),
    (19, 5, "walk_path__L19_L5"),
    (20, 5, "walk_path__L20_L5"),
    (9, 5, "walk_path__L9_L5"),
    (10, 6, "walk_path__L10_L6"),
    (11, 6, "walk_path__L11_L6"),
    (12, 6, "walk_path__L12_L6"),
    (13, 6, "walk_path__L13_L6"),
    (14, 6, "walk_path__L14_L6"),
    (15, 6, "walk_path__L15_L6"),
    (16, 6, "walk_path__L16_L6"),
    (17, 6, "walk_path__L17_L6"),
    (18, 6, "walk_path__L18_L6"),
    (19, 6, "walk_path__L19_L6"),
    (20, 6, "walk_path__L20_L6"),
    (11, 7, "walk_path__L11_L7"),
    (12, 7, "walk_path__L12_L7"),
    (13, 7, "walk_path__L13_L7"),
    (14, 7, "walk_path__L14_L7"),
    (15, 7, "walk_path__L15_L7"),
    (16, 7, "walk_path__L16_L7"),
    (17, 7, "walk_path__L17_L7"),
    (18, 7, "walk_path__L18_L7"),
    (10, 8, "walk_path__L10_L8"),
    (11, 8, "walk_path__L11_L8"),
    (12, 8, "walk_path__L12_L8"),
    (13, 8, "walk_path__L13_L8"),
    (14, 8, "walk_path__L14_L8"),
    (15, 8, "walk_path__L15_L8"),
    (9, 8, "walk_path__L9_L8")]

/-- The specialization of `walk_path` a shape's queries call. -/
def oqWalkOf (s : Oq) : String :=
  ((walkPathNames.find? fun p ↦ p.1 == s.pd && p.2.1 == s.cd).map (·.2.2)).getD ""

/-! ## The fold -/

/-- The first value of fold round `j`, the fold starting at `F`: a round takes eight values, a
later round one more (the scale), and two per output, `2^(folds - 1 - j)` outputs. -/
def oqRK (s : Oq) (F : ℕ) : ℕ → ℕ
  | 0 => F
  | j + 1 => oqRK s F j + 8 + (if j = 0 then 0 else 1) + 2 * 2 ^ (s.folds - 1 - j)

/-- The first output value of fold round `j`. -/
def oqRO (s : Oq) (F j : ℕ) : ℕ := oqRK s F j + 8 + (if j = 0 then 0 else 1)

/-- The scale `Π_(i ≤ j) t_i` after round `j`. -/
def oqScale (s : Oq) (F j : ℕ) : ℕ := if j = 0 then oqRK s F 0 + 3 else oqRK s F j + 8

/-- Lane `m` after round `j`. -/
def oqAcc (s : Oq) (F j m : ℕ) : ℕ := oqRO s F j + 2 * m + 1

/-- The lanes `(lo, hi)` round `j` folds into its output `m`: the row's (reversed at level 0),
then the previous round's. -/
def oqLoHi (s : Oq) (b F j m : ℕ) : ℕ × ℕ :=
  if j = 0 then
    (if s.base = 1 then (b + s.I - 1 - 2 * m, b + s.I - 2 - 2 * m) else (b + 2 * m, b + 2 * m + 1))
  else (oqAcc s F (j - 1) (2 * m), oqAcc s F (j - 1) (2 * m + 1))

/-- Fold round `j` at the point `x`, the challenges at `coefs`: `t = α + β·x`, `1 = t⁻¹·t`,
`r = θ + t⁻¹`, the scale, the outputs `lo + r·hi`. -/
def oqRoundT (s : Oq) (coefs x : V) (b F j : ℕ) : List Stmt :=
  let K := oqRK s F j
  let O := oqRO s F j
  [.atom (.load (.n K) coefs (3 * j)), .atom (.load (.n (K + 1)) coefs (3 * j + 1)),
    .atom (.mul (.n (K + 2)) (.n (K + 1)) x), .atom (.add (.n (K + 3)) (.n K) (.n (K + 2))),
    .atom (.load (.n (K + 4)) coefs (3 * j + 2)), .atom (.const (.n (K + 5)) (word 1 0)),
    .atom (.mul (.n (K + 5)) (.n (K + 6)) (.n (K + 3))),
    .atom (.add (.n (K + 7)) (.n (K + 4)) (.n (K + 6)))] ++
  (if j = 0 then [] else [.atom (.mul (.n (K + 8)) (.n (oqScale s F (j - 1))) (.n (K + 3)))]) ++
  ((List.range (2 ^ (s.folds - 1 - j))).map fun m ↦
    [.atom (.mul (.n (O + 2 * m)) (.n (K + 7)) (.n (oqLoHi s b F j m).2)),
      .atom (.add (.n (O + 2 * m + 1)) (.n (oqLoHi s b F j m).1) (.n (O + 2 * m)))]).flatten

/-- The fold's value: the scale times the last lane. -/
def oqVal (s : Oq) (F : ℕ) : ℕ := oqRK s F s.folds

/-- The fold of the row from `b` at `x`, from the value `F`. -/
def oqFoldT (s : Oq) (coefs x : V) (b F : ℕ) : List Stmt :=
  ((List.range s.folds).map (oqRoundT s coefs x b F)).flatten ++
    [.atom (.mul (.n (oqVal s F)) (.n (oqScale s F (s.folds - 1))) (.n (oqAcc s F (s.folds - 1) 0)))]

/-! ## The final level's check -/

/-- The chain's `W_i` after the value `v`: `W_0` a copy of the point, `W_(i+1)` three values on. -/
def oqWs (v i : ℕ) : ℕ := if i = 0 then v + 1 else v + 3 * i + 1

/-- The chain `W_0 = x`, `W_(i+1) = W_i·(W_i + vs_i)` after the value `v`. -/
def oqWsT (s : Oq) (x : V) (v : ℕ) : List Stmt :=
  [.atom (.copy (.n (v + 1)) x)] ++
    ((List.range s.mu).map fun i ↦
      [.atom (.const (.n (v + 2 + 3 * i)) (word (s.vs.getD i 0) 0)),
        .atom (.add (.n (v + 3 + 3 * i)) (.n (oqWs v i)) (.n (v + 2 + 3 * i))),
        .atom (.mul (.n (v + 4 + 3 * i)) (.n (oqWs v i)) (.n (v + 3 + 3 * i)))]).flatten

/-- Level `0` of `novel_eval` from `k`: the coefficients' pairs `hs[2m] + W_0·hs[2m + 1]`, `n / 2`
of them. -/
def nvLevel0T (hs w : V) (n k : ℕ) : List Stmt :=
  ((List.range (n / 2)).map fun m ↦
    [.atom (.load (.n (k + 4 * m)) hs (2 * m)), .atom (.load (.n (k + 4 * m + 1)) hs (2 * m + 1)),
      .atom (.mul (.n (k + 4 * m + 2)) w (.n (k + 4 * m + 1))),
      .atom (.add (.n (k + 4 * m + 3)) (.n (k + 4 * m)) (.n (k + 4 * m + 2)))]).flatten

/-- A later level of `novel_eval` on the values `ins` from `k`: each pair `lo + w·hi`, an odd last
value copied; the statements, the outputs and the next free value. -/
def nvLevelT (w : V) : List ℕ → ℕ → List Stmt × List ℕ × ℕ
  | lo :: hi :: rest, k =>
    let r := nvLevelT w rest (k + 2)
    ([.atom (.mul (.n k) w (.n hi)), .atom (.add (.n (k + 1)) (.n lo) (.n k))] ++ r.1, (k + 1) :: r.2.1,
      r.2.2)
  | [lo], k => ([.atom (.copy (.n k) (.n lo))], [k], k + 1)
  | [], k => ([], [], k)

/-- Levels `i .. i + c` of `novel_eval` on the values `ins` from `k`, `W_i` at `ws i`. -/
def nvLevelsT (ws : ℕ → ℕ) : ℕ → ℕ → List ℕ → ℕ → List Stmt × List ℕ × ℕ
  | 0, _, ins, k => ([], ins, k)
  | c + 1, i, ins, k =>
    let l := nvLevelT (.n (ws i)) ins k
    let r := nvLevelsT ws c (i + 1) l.2.1 l.2.2
    (l.1 ++ r.1, r.2.1, r.2.2)

/-- `novel_eval(hs, ws, n_hs, hs_bits)` after the chain from `v`: level `0`'s statements, then the
later levels'; the statements, the outputs (one) and the next free value. -/
def oqNovel (s : Oq) (hs : V) (v : ℕ) : List Stmt × List ℕ × ℕ :=
  let k := v + 2 + 3 * s.mu
  let r := nvLevelsT (oqWs v) (s.hsBits - 1) 1
    ((List.range (s.nHs / 2)).map fun m ↦ k + 4 * m + 3) (k + 4 * (s.nHs / 2))
  (nvLevel0T hs (.n (oqWs v 0)) s.nHs k ++ r.1, r.2.1, r.2.2)

/-- The final level's check after the fold's value `v`: the chain, the novel sum, its equality with
the value, the query's result `0`. -/
def oqFinT (s : Oq) (x hs : V) (v : ℕ) : List Stmt :=
  oqWsT s x v ++ (oqNovel s hs v).1 ++
    [.atom (.assertEq (.n v) (.n ((oqNovel s hs v).2.1.headD 0))),
      .atom (.const (.n (oqNovel s hs v).2.2) (word 0 0))]

/-! ## One query -/

/-- The first value of the leaf hash: after the row, and the padding run if emitted. -/
def oqKL (s : Oq) (b : ℕ) (emit : Bool) : ℕ := oqK1 s b + (if emit then 5 else 0)

/-- The padding run's first value. -/
def oqPr (s : Oq) (b : ℕ) (emit : Bool) (pr : ℕ) : ℕ := if emit then oqK1 s b else pr

/-- The first value after the leaf hash: the fold's start. -/
def oqCh (s : Oq) (b : ℕ) (emit : Bool) : ℕ := oqKL s b emit + s.chainLen

/-- The query's result: the fold's value, or (final level) the constant `0` after the check. -/
def oqRes (s : Oq) (b : ℕ) (emit : Bool) : ℕ :=
  if s.final = 1 then (oqNovel s (.n 0) (oqVal s (oqCh s b emit))).2.2 else oqVal s (oqCh s b emit)

/-- The first value after a query. -/
def oqEnd (s : Oq) (b : ℕ) (emit : Bool) : ℕ := oqRes s b emit + 1

/-- **One query** from the value `b` at the point `x`, its windows at `bp`, emitting the padding
run (`emit`) or reusing the one at `pr`: the row, the leaf hash, the call of `walk`
(`walk_path__L{pd}_L{cd}`) on the leaf digest, the windows, the cap and the flags, the fold by the
challenges at `coefs`, and at the final level the check against the coefficients at `hs`. -/
def oqQueryT (s : Oq) (x bp cap flags coefs hs : V) (b : ℕ) (emit : Bool) (pr : ℕ) (walk : String) :
    List Stmt :=
  oqPrepT s b ++ (if emit then oqPadT (oqK1 s b) else []) ++
    oqLeafT s b (oqPr s b emit pr) (oqKL s b emit) ++
    [.call walk [.n (oqOut s (oqKL s b emit) (s.B - 1) 0), .n (oqOut s (oqKL s b emit) (s.B - 1) 1), bp,
      cap, flags] []] ++
    oqFoldT s coefs x b (oqCh s b emit) ++
    (if s.final = 1 then oqFinT s x hs (oqVal s (oqCh s b emit)) else [])

/-! ## The loop and the function -/

/-- The loop's guard and its next call from `g`, on its parameters `x, N, …` (`0 .. 9`). -/
def oqGuardT (g : ℕ) (name : String) : List Stmt :=
  [.atom (.const (.n g) (word 2 0)), .atom (.mul (.n (g + 1)) (.n 0) (.n g)),
    .atom (.add (.n (g + 2)) (.n (g + 1)) (.n 1)), .atom (.const (.n (g + 3)) (word 2 0)),
    .atom (.mul (.n (g + 4)) (.n 0) (.n (g + 3))),
    .callIf (.n (g + 2)) name
      [.n (g + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9], .ret []]

/-- The first value of the second query of a level-0 iteration (its point; its windows next). -/
def oqE1 (s : Oq) : ℕ := oqEnd s 16 true

/-- The first value of a level-0 iteration's chain step. -/
def oqC1 (s : Oq) : ℕ := oqEnd s (oqE1 s + 2) false

/-- **The loop helper's body at level 0** (`base = 1`: two queries an iteration, the points and
window pointers at `positions·x²`, `qptrs·x²` offsets `odd`, `odd + 1`), on its parameters
`x, N, positions, qptrs, cap, flags, coefs, hs, chain, λ⁻¹` (`0 .. 9`): the queries, the chain
step `chain[x·g] = ((chain[x] + d0)·λ⁻¹ + d1)·λ⁻¹` (non-final levels), the guard and the next call. -/
def oqLoop1T (s : Oq) (odd : ℕ) (walk name : String) : List Stmt :=
  let e1 := oqE1 s
  let c := oqC1 s
  [.atom (.mul (.n 10) (.n 2) (.n 0)), .atom (.mul (.n 11) (.n 10) (.n 0)),
    .atom (.mul (.n 12) (.n 3) (.n 0)), .atom (.mul (.n 13) (.n 12) (.n 0)),
    .atom (.load (.n 14) (.n 11) odd), .atom (.load (.n 15) (.n 13) odd)] ++
    oqQueryT s (.n 14) (.n 15) (.n 4) (.n 5) (.n 6) (.n 7) 16 true 0 walk ++
    [.atom (.load (.n e1) (.n 11) (odd + 1)), .atom (.load (.n (e1 + 1)) (.n 13) (odd + 1))] ++
    oqQueryT s (.n e1) (.n (e1 + 1)) (.n 4) (.n 5) (.n 6) (.n 7) (e1 + 2) false (oqK1 s 16) walk ++
    (if s.final = 1 then oqGuardT c name else
      [.atom (.mul (.n c) (.n 8) (.n 0)), .atom (.load (.n (c + 1)) (.n c) 0),
        .atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqRes s 16 true))),
        .atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 9)),
        .atom (.add (.n (c + 4)) (.n (c + 3)) (.n (oqRes s (e1 + 2) false))),
        .atom (.mul (.n (c + 5)) (.n (c + 4)) (.n 9)), .atom (.mul (.n (c + 6)) (.n 8) (.n 0)),
        .atom (.load (.n (c + 5)) (.n (c + 6)) 1)] ++ oqGuardT (c + 7) name)

/-- The first value of a deeper iteration's chain step. -/
def oqC0 (s : Oq) : ℕ := oqEnd s 14 true

/-- **The loop helper's body deeper** (`base = 0`: one query an iteration, its point
`positions[x]` and window pointer `qptrs[x]`): the query, the chain step
`chain[x·g] = (chain[x] + d)·λ⁻¹` (non-final levels), the guard and the next call. -/
def oqLoop0T (s : Oq) (walk name : String) : List Stmt :=
  let c := oqC0 s
  [.atom (.mul (.n 10) (.n 2) (.n 0)), .atom (.load (.n 11) (.n 10) 0),
    .atom (.mul (.n 12) (.n 3) (.n 0)), .atom (.load (.n 13) (.n 12) 0)] ++
    oqQueryT s (.n 11) (.n 13) (.n 4) (.n 5) (.n 6) (.n 7) 14 true 0 walk ++
    (if s.final = 1 then oqGuardT c name else
      [.atom (.mul (.n c) (.n 8) (.n 0)), .atom (.load (.n (c + 1)) (.n c) 0),
        .atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqRes s 14 true))),
        .atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 9)), .atom (.mul (.n (c + 4)) (.n 8) (.n 0)),
        .atom (.load (.n (c + 3)) (.n (c + 4)) 1)] ++ oqGuardT (c + 5) name)

/-- The first value after the function's start. -/
def oqMK (s : Oq) (odd : ℕ) : ℕ := if odd = 1 then oqEnd s 13 true + 1 else 12

/-- **The function's body**, on its parameters `cap, flags, λ⁻¹, coefs, hs, positions, qptrs, N`
(`0 .. 7`): the chain allocated, its start (the odd first query's result times `λ⁻¹`, or `0`),
the loop from `1`, the chain's end (non-final levels) or `0`. -/
def oqMainT (s : Oq) (odd : ℕ) (walk loop : String) : List Stmt :=
  let k := oqMK s odd
  [.atom (.const (.n 8) (word 2 0)), .atom (.mul (.n 9) (.n 7) (.n 8)),
    .atom (.hint (.allocDyn (.n 10) (.n 9)))] ++
  (if odd = 1 then
      [.atom (.load (.n 11) (.n 5) 0), .atom (.load (.n 12) (.n 6) 0)] ++
        oqQueryT s (.n 11) (.n 12) (.n 0) (.n 1) (.n 3) (.n 4) 13 true 0 walk ++
        [.atom (.mul (.n (k - 1)) (.n (oqRes s 13 true)) (.n 2)), .atom (.load (.n (k - 1)) (.n 10) 0)]
    else [.atom (.const (.n 11) (word 0 0)), .atom (.load (.n 11) (.n 10) 0)]) ++
  [.atom (.const (.n k) (word 1 0)), .atom (.add (.n (k + 1)) (.n k) (.n 7)),
    .atom (.const (.n (k + 2)) (word 1 0)),
    .callIf (.n (k + 1)) loop [.n (k + 2), .n 7, .n 5, .n 6, .n 0, .n 1, .n 3, .n 4, .n 10, .n 2]] ++
  (if s.final = 1 then [.atom (.const (.n (k + 3)) (word 0 0)), .ret [.n (k + 3)]]
   else [.atom (.mul (.n (k + 3)) (.n 10) (.n 7)), .atom (.load (.n (k + 4)) (.n (k + 3)) 0),
     .atom (.copy (.n (k + 5)) (.n (k + 4))), .ret [.n (k + 5)]])

/-- The template shape of a deployed specialization. -/
def OqShape.oq (sh : OqShape) : Oq :=
  ⟨sh.base, sh.folds, sh.depth - sh.cd, sh.cd, sh.final, sh.vs, sh.nHs, sh.hsBits⟩

end
end LeanVM.Guest.B1
