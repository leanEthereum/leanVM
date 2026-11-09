/-
  LeanVM.Guest.B1.Opening.Meaning

  The interface of B1's WHIR opening functions: what each computes on the carried sponge, and
  the statement that its core IR computes it.
-/

module

public import LeanVM.Guest.B1.Common.Sponge
public import LeanVM.Guest.B1.Bits.QueryWindowsT
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# The stacked WHIR opening's helpers: meanings (TRIAGE G #35-38)

For each function of the guest (`lean_ethereum.py` at leanVM main `40f877dc`, G below) its meaning
on its argument and return words, the sponge as the guest carries it (`Fs`), and `…_Spec`, the
statement that its core IR relation is that meaning (proved as `…_holds`). The Spec steps they
are (`foldRounds`, `tailRounds`, V:1750, 1702; `sampleN`; `readN` and `grindP`) are the `…_run`
theorems of `B1/Opening/`.

| function | G | meaning |
| --- | --- | --- |
| `opening_fold` | 1103-1115 | squeeze with two scalars waiting, fold the quadratic, read the next `c0, c2` (left waiting) |
| `opening_ood_point__L{n}` | 1118-1129 | `n` challenges, the first from a permutation of the given rate cells |
| `opening_final_message__L{n}` | 1132-1150 | absorb the final message's `n` words and the nonce (`dsPowNonce`), permute |
| `opening_row_weights__L{f}_L{r}` | 1153-1176 | the row's `eqKernel` weights as two tensor factors, reversed at level 0 |
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `opening_fold` (G:1216-1229, TRIAGE #35) -/

/-- **`opening_fold(fs0..fs4, w0, w1, cursor, c0, c1, c2)`**: from the carried capacity
(canonical cells) with the scalars `w0`, `w1` waiting (`dsObserve`), the challenge `r` is
squeezed, the claim folded to `(c2·r + c1)·r + c0` (`polyEval [c0, c1, c2] r`), and the two
stream words at the cursor, the next round's `c0`, `c2`, are read (they wait in the next sponge,
which the next call packs); the function returns the capacity after the squeeze, the cursor two
words on, the claim, the two words and `r`. -/
def MeaningOpeningFold (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, w0, w1, cur, c0, c1, c2], rets =>
      AllCanonical [f0, f1, f2, f3, f4] ∧ ∃ d0 d2 : E, ReadsAt rd cur [d0, d2] ∧
        let r := (⟨[f0, f1, f2, f3, f4], [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).squeeze
        rets = r.2.cap ++ [cur * gen ^ 2, (c2 * r.1 + c1) * r.1 + c0, d0, d2, r.1]
  | _, _ => False

/-- `opening_fold`'s core IR is its meaning. -/
def opening_fold_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "opening_fold" args rets ↔ MeaningOpeningFold rd args rets

/-! ## `opening_ood_point` (G:1232-1243, TRIAGE #36) -/

/-- **`opening_ood_point(fs0..fs4, r0..r7, point, n)`** (`n ≥ 1`): the rate cells `r0..r7` and the
capacity are canonical; the first coordinate is the challenge of their permutation, the other
`n - 1` are squeezed with nothing waiting; the coordinates are stored at `point`, and the
function returns the final capacity. With `r0..r7 = rateOf pend`, it is `sampleN n` from the
sponge carried as `⟨cap, pend⟩`. -/
def MeaningOpeningOodPoint (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, r0, r1, r2, r3, r4, r5, r6, r7, point], rets =>
      AllCanonical [r0, r1, r2, r3, r4, r5, r6, r7, f0, f1, f2, f3, f4] ∧
        let S := permOf [r0, r1, r2, r3, r4, r5, r6, r7, f0, f1, f2, f3, f4]
        let rest := (⟨capOf S, []⟩ : Fs).squeezeN (n - 1)
        ReadsAt rd point (challengeOf S :: rest.1) ∧ rets = rest.2.cap
  | _, _ => False

/-- The deployed specializations, dimensions `6 .. 22`, by name (a name built by `++ toString`
does not reduce in a `module`'s kernel). -/
def oodPointNames : List (String × ℕ) :=
  [("opening_ood_point__L6", 6), ("opening_ood_point__L7", 7), ("opening_ood_point__L8", 8),
    ("opening_ood_point__L9", 9), ("opening_ood_point__L10", 10), ("opening_ood_point__L11", 11),
    ("opening_ood_point__L12", 12), ("opening_ood_point__L13", 13),
    ("opening_ood_point__L14", 14), ("opening_ood_point__L15", 15),
    ("opening_ood_point__L16", 16), ("opening_ood_point__L17", 17),
    ("opening_ood_point__L18", 18), ("opening_ood_point__L19", 19),
    ("opening_ood_point__L20", 20), ("opening_ood_point__L21", 21),
    ("opening_ood_point__L22", 22)]

/-- `opening_ood_point__L{n}`'s core IR is its meaning, `6 ≤ n ≤ 22`. -/
def opening_ood_point_Spec : Prop :=
  ∀ p ∈ oodPointNames, ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd p.1 args rets ↔ MeaningOpeningOodPoint p.2 rd args rets

/-! ## `opening_final_message` (G:1246-1265, TRIAGE #37) -/

/-- **`opening_final_message(fs0..fs4, w0, w1, cursor, out, n)`**: from the carried capacity
(canonical cells) with `w0`, `w1` waiting, the `n` stream words at the cursor (the final message,
stored at `out`) are absorbed, then the next word, the nonce, with the tag `dsPowNonce`, and the
sponge permutes; the function returns that state's first cell (whose first limb `grind_check`
reads, `challengeOf_limb0`), its capacity, the cursor past the nonce and the nonce. -/
def MeaningOpeningFinalMessage (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, w0, w1, cur, out], rets =>
      AllCanonical [f0, f1, f2, f3, f4] ∧ ∃ (ms : List E) (nonce : E), ms.length = n ∧
        ReadsAt rd cur (ms ++ [nonce]) ∧ ReadsAt rd out ms ∧
        let s := ((⟨[f0, f1, f2, f3, f4], [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorbAll ms
          dsObserve).absorb nonce dsPowNonce
        rets = [cellsOfState s.perm false 0] ++ capOf s.perm ++ [cur * gen ^ (n + 1), nonce]
  | _, _ => False

/-- The deployed specializations, by name. -/
def finalMessageNames : List (String × ℕ) :=
  [("opening_final_message__L4", 4), ("opening_final_message__L8", 8),
    ("opening_final_message__L16", 16), ("opening_final_message__L32", 32)]

/-- `opening_final_message__L{n}`'s core IR is its meaning, `n ∈ {4, 8, 16, 32}`. -/
def opening_final_message_Spec : Prop :=
  ∀ p ∈ finalMessageNames, ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd p.1 args rets ↔ MeaningOpeningFinalMessage p.2 rd args rets

/-! ## `opening_row_weights` (G:1268-1289, TRIAGE #38) -/

/-- Slot `i` of a run of `2^m`, reversed when `rev = 1`. -/
def rwSlot (m rev i : ℕ) : ℕ := if rev = 1 then 2 ^ m - 1 - i else i

/-- The low factor's coordinates: `min folds 3`. -/
def rwLo (folds : ℕ) : ℕ := if folds / 3 = 0 then folds else 3

/-- **`opening_row_weights(point, out, folds, reverse)`**: the `folds` words at `point`; the low
factor `out[i] = eqKernel(point[..lo])[slot i]`, `i < 2^lo`, and the high factor
`out[2^lo + i] = eqKernel(point[lo..])[slot i]`, `i < 2^(folds - lo)`, the slots reversed at
`reverse = 1`: weight `i` of the row is `out[i % 2^lo] · out[2^lo + i / 2^lo]`, entry `i` (or
`2^folds - 1 - i`) of `eqKernel` (V:642). -/
def MeaningOpeningRowWeights (folds rev : ℕ) (rd : Reader) : List E → List E → Prop
  | [point, out], rets =>
      rets = [] ∧ ∃ rs : List E, rs.length = folds ∧ ReadsAt rd point rs ∧
        (∀ i < 2 ^ rwLo folds,
          LoadHolds rd out i ((eqKernel (rs.take (rwLo folds))).getD (rwSlot (rwLo folds) rev i) 0)) ∧
        ∀ i < 2 ^ (folds - rwLo folds),
          LoadHolds rd out (2 ^ rwLo folds + i)
            ((eqKernel (rs.drop (rwLo folds))).getD (rwSlot (folds - rwLo folds) rev i) 0)
  | _, _ => False

/-- `opening_row_weights__L6_L1` and `__L4_L0`'s core IR are their meanings. -/
def opening_row_weights_Spec : Prop :=
  (∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "opening_row_weights__L6_L1" args rets ↔
      MeaningOpeningRowWeights 6 1 rd args rets) ∧
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "opening_row_weights__L4_L0" args rets ↔
      MeaningOpeningRowWeights 4 0 rd args rets

/-! ## `opening_query`, `opening_queries` (G:1347-1417, TRIAGE #39, #40) -/

/-- `climb` (V:492) at the deployed hash: the node a path reaches. -/
def climbD (leaf : Digest) (q : ℕ) (sibs : List Digest) : Digest :=
  Id.run (Compile.climbWithHash (m := Id) keccak256 leaf q sibs)

/-- The row's `E` word `j`: the `K` word `j` at level 0 (`base = 1`), else the three limbs from
`3j` (`extRow`, V:1686). -/
def rowWord (base : ℕ) (row : List K) (j : ℕ) : E :=
  if base = 1 then ofK (row.getD j 0)
  else E.ofLimbs (row.getD (3 * j) 0) (row.getD (3 * j + 1) 0) (row.getD (3 * j + 2) 0)

/-- The low factor's length of a row of `I` words: `min I 8`. -/
def rowLo (I : ℕ) : ℕ := if I / 8 = 0 then I else 8

/-- **A row's dot product with its tensor weights** (`opening_query`, G:1368-1385): run `h` of
`lo` words, weighted by `w (lo + h)`, of the sums of its words weighted by `w l`, in the guest's
order. -/
def rowDot (base I : ℕ) (row : List K) (w : ℕ → E) : E :=
  ((List.range (I / rowLo I)).map fun h ↦ w (rowLo I + h) *
    ((List.range (rowLo I)).map fun l ↦ rowWord base row (rowLo I * h + l) * w l).foldl (· + ·) 0
  ).foldl (· + ·) 0

/-- The node a path reaches after its first `l` levels. -/
def climbNode (leaf : Digest) (q : ℕ) (sibs : List Digest) (l : ℕ) : Digest :=
  climbD leaf q (sibs.take l)

/-- Cell `k` of a path's frame run (`walk_path`'s `path`, G:1311-1312): level `k / 4`'s
children, two cells each, the node reached so far on the side of the position's bit at the level,
the sibling on the other. -/
def pathCell (leaf : Digest) (q : ℕ) (sibs : List Digest) (k : ℕ) : E :=
  let d := if (k % 4) / 2 = (if q.testBit (k / 4) then 1 else 0) then climbNode leaf q sibs (k / 4)
    else sibs.getD (k / 4) (Vector.replicate 4 0)
  if k % 2 = 0 then (digestHalves d).1 else (digestHalves d).2

/-- **One query** (`opening_query`, lean_ethereum.py:1347-1390 at 40f877dc, with `walk_path`,
:1295-1331; TRIAGE #33, #39) at the position `q`: the hinted row of `I` (`base = 1`) or `3I` words
of `K`, hashed (`merkleLeafDigest`, the leaf of `openOne`, V:501) and climbed `depth - cd` levels
by hinted siblings (`climb`, V:492, the position's low bits: `climbD`); the node reached is
written at the cap's cells of node `2^cd + q / 2^(depth - cd)` and its parent flagged; the
query's value is the row's dot product with the weights at `wp`. -/
def QueryOpens (rd : Reader) (base I depth cd : ℕ) (cap flags wp : E) (q : ℕ) (row : List K)
    (d : E) : Prop :=
  row.length = (if base = 1 then I else 3 * I) ∧
    ∃ (sibs : List Digest) (w : ℕ → E), sibs.length = depth - cd ∧
      (∀ l < rowLo I + I / rowLo I, LoadHolds rd wp l (w l)) ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ (depth - cd)))
        (digestHalves (climbD (merkleLeafDigest row) q sibs)).1 ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ (depth - cd)) + 1)
        (digestHalves (climbD (merkleLeafDigest row) q sibs)).2 ∧
      LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (depth - cd + 1)) 1 ∧
      d = rowDot base I row w

/-- The number of queries of `opening_queries` at `n_iters_g = g^N`: `odd + 2N` at level 0, `N`
deeper. -/
def oqCount (odd base N : ℕ) : ℕ := if base = 1 then odd + 2 * N else N

/-- The chain `h ← (h + d_k)·μ` over the queries' values, `μ = λ⁻¹`, after `i` iterations (two
queries an iteration at level 0, an odd count's first alone before them). -/
def oqChain (odd base : ℕ) (mu : E) (ds : ℕ → E) : ℕ → E
  | 0 => if odd = 1 then ds 0 * mu else 0
  | i + 1 =>
    if base = 1 then ((oqChain odd base mu ds i + ds (odd + 2 * i)) * mu + ds (odd + 2 * i + 1)) * mu
    else (oqChain odd base mu ds i + ds i) * mu

/-- The window pointers point to positions' windows: every pointer `qptrs[k]`, `k < Q`, names a
frame run holding the `qwN depth cd` windows `g^(qwVal …)` of a position below `2^depth` (what
`decode_query_windows` writes, `MeaningDecodeQueryWindows`). -/
def QueryWinsOk (rd : Reader) (qptrs : E) (Q depth cd : ℕ) : Prop :=
  ∀ k < Q, ∀ bp, LoadHolds rd qptrs k bp →
    ∃ q < 2 ^ depth, FrameRun rd bp (qwN depth cd) fun i ↦ gen ^ qwVal depth cd q i

/-- **`opening_queries(cap, flags, lam, lam_n, query_win_ptrs, row_eq_weights, n_iters_g, odd,
base, I, leaf_cells, depth, cd)`** (lean_ethereum.py:1393-1417 at 40f877dc; TRIAGE #40):
`n_iters_g = g^N`, `λ ≠ 0`; query `k < Q` (`oqCount`) reads its window pointer and the windows
`g^(qwVal …)` of its position `q_k < 2^depth`, and opens
(`QueryOpens`) to the value `d_k`; the chain `h ← (h + d_k)·λ⁻¹` is in a heap run, and the
function returns its end times `lam_n`: `lam_n · Σ_k d_k λ^(k - Q)` (`Σ_k λ^k d_k` at
`lam_n = λ^Q`, `enforcedSum`, V:1694). -/
def MeaningOpeningQueries (odd base I depth cd : ℕ) (rd : Reader) : List E → List E → Prop
  | [cap, flags, lam, lamN, qptrs, wp, nG], rets =>
      ∃ N < ordG, nG = gen ^ N ∧ lam ≠ 0 ∧
        ∃ (bps : ℕ → E) (qs : ℕ → ℕ) (rows : ℕ → List K) (ds : ℕ → E),
          (∀ k < oqCount odd base N, LoadHolds rd qptrs k (bps k) ∧ qs k < 2 ^ depth ∧
            (∀ i < qwN depth cd, LoadHolds rd (bps k) i (gen ^ qwVal depth cd (qs k) i)) ∧
            QueryOpens rd base I depth cd cap flags wp (qs k) (rows k) (ds k)) ∧
          ∃ ch : E, (∀ i ≤ N, LoadHolds rd ch i (oqChain odd base lam⁻¹ ds i)) ∧
            rets = [oqChain odd base lam⁻¹ ds N * lamN]
  | _, _ => False

/-- `opening_queries`' core IR (the function named `name`, of shape `(odd, base, I, leafCells,
depth, cd)`) is its meaning, when the window pointers point to positions' windows. -/
def opening_queries_Spec (name : String) (odd base I depth cd : ℕ) : Prop :=
  ∀ (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E),
    (∀ N, nG = gen ^ N → N < ordG → QueryWinsOk rd qptrs (oqCount odd base N) depth cd) →
    (coreProgram.Rel rd name [cap, flags, lam, lamN, qptrs, wp, nG] rets ↔
      MeaningOpeningQueries odd base I depth cd rd [cap, flags, lam, lamN, qptrs, wp, nG] rets)

/-- The 56 deployed specializations, by name (a name built by `++ toString` does not reduce in a
`module`'s kernel), with their shapes `(odd, base, I, leafCells, depth, cd)`: `base = 1`,
`I = 64`, `leafCells = 32`, or `base = 0`, `odd = 0`, `I = 16`, `leafCells = 24`; `4 ≤ cd ≤ 8`. -/
def openingQueriesShapes : List (String × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [("opening_queries__L0_L1_L64_L32_L17_L8", 0, 1, 64, 32, 17, 8),
    ("opening_queries__L0_L1_L64_L32_L18_L7", 0, 1, 64, 32, 18, 7),
    ("opening_queries__L0_L1_L64_L32_L18_L8", 0, 1, 64, 32, 18, 8),
    ("opening_queries__L0_L1_L64_L32_L19_L7", 0, 1, 64, 32, 19, 7),
    ("opening_queries__L0_L1_L64_L32_L19_L8", 0, 1, 64, 32, 19, 8),
    ("opening_queries__L0_L1_L64_L32_L20_L6", 0, 1, 64, 32, 20, 6),
    ("opening_queries__L0_L1_L64_L32_L20_L7", 0, 1, 64, 32, 20, 7),
    ("opening_queries__L0_L1_L64_L32_L20_L8", 0, 1, 64, 32, 20, 8),
    ("opening_queries__L0_L1_L64_L32_L21_L6", 0, 1, 64, 32, 21, 6),
    ("opening_queries__L0_L1_L64_L32_L21_L7", 0, 1, 64, 32, 21, 7),
    ("opening_queries__L0_L1_L64_L32_L21_L8", 0, 1, 64, 32, 21, 8),
    ("opening_queries__L0_L1_L64_L32_L22_L6", 0, 1, 64, 32, 22, 6),
    ("opening_queries__L0_L1_L64_L32_L22_L7", 0, 1, 64, 32, 22, 7),
    ("opening_queries__L0_L1_L64_L32_L23_L6", 0, 1, 64, 32, 23, 6),
    ("opening_queries__L0_L1_L64_L32_L23_L7", 0, 1, 64, 32, 23, 7),
    ("opening_queries__L0_L1_L64_L32_L24_L6", 0, 1, 64, 32, 24, 6),
    ("opening_queries__L0_L1_L64_L32_L24_L7", 0, 1, 64, 32, 24, 7),
    ("opening_queries__L0_L1_L64_L32_L25_L6", 0, 1, 64, 32, 25, 6),
    ("opening_queries__L0_L1_L64_L32_L26_L6", 0, 1, 64, 32, 26, 6),
    ("opening_queries__L1_L1_L64_L32_L19_L7", 1, 1, 64, 32, 19, 7),
    ("opening_queries__L1_L1_L64_L32_L20_L7", 1, 1, 64, 32, 20, 7),
    ("opening_queries__L1_L1_L64_L32_L21_L7", 1, 1, 64, 32, 21, 7),
    ("opening_queries__L1_L1_L64_L32_L22_L7", 1, 1, 64, 32, 22, 7),
    ("opening_queries__L1_L1_L64_L32_L22_L8", 1, 1, 64, 32, 22, 8),
    ("opening_queries__L1_L1_L64_L32_L23_L7", 1, 1, 64, 32, 23, 7),
    ("opening_queries__L1_L1_L64_L32_L23_L8", 1, 1, 64, 32, 23, 8),
    ("opening_queries__L1_L1_L64_L32_L24_L7", 1, 1, 64, 32, 24, 7),
    ("opening_queries__L1_L1_L64_L32_L25_L7", 1, 1, 64, 32, 25, 7),
    ("opening_queries__L0_L0_L16_L24_L14_L5", 0, 0, 16, 24, 14, 5),
    ("opening_queries__L0_L0_L16_L24_L15_L5", 0, 0, 16, 24, 15, 5),
    ("opening_queries__L0_L0_L16_L24_L16_L4", 0, 0, 16, 24, 16, 4),
    ("opening_queries__L0_L0_L16_L24_L16_L5", 0, 0, 16, 24, 16, 5),
    ("opening_queries__L0_L0_L16_L24_L16_L6", 0, 0, 16, 24, 16, 6),
    ("opening_queries__L0_L0_L16_L24_L17_L4", 0, 0, 16, 24, 17, 4),
    ("opening_queries__L0_L0_L16_L24_L17_L5", 0, 0, 16, 24, 17, 5),
    ("opening_queries__L0_L0_L16_L24_L17_L6", 0, 0, 16, 24, 17, 6),
    ("opening_queries__L0_L0_L16_L24_L18_L4", 0, 0, 16, 24, 18, 4),
    ("opening_queries__L0_L0_L16_L24_L18_L5", 0, 0, 16, 24, 18, 5),
    ("opening_queries__L0_L0_L16_L24_L18_L6", 0, 0, 16, 24, 18, 6),
    ("opening_queries__L0_L0_L16_L24_L19_L4", 0, 0, 16, 24, 19, 4),
    ("opening_queries__L0_L0_L16_L24_L19_L5", 0, 0, 16, 24, 19, 5),
    ("opening_queries__L0_L0_L16_L24_L19_L6", 0, 0, 16, 24, 19, 6),
    ("opening_queries__L0_L0_L16_L24_L20_L4", 0, 0, 16, 24, 20, 4),
    ("opening_queries__L0_L0_L16_L24_L20_L5", 0, 0, 16, 24, 20, 5),
    ("opening_queries__L0_L0_L16_L24_L20_L6", 0, 0, 16, 24, 20, 6),
    ("opening_queries__L0_L0_L16_L24_L21_L4", 0, 0, 16, 24, 21, 4),
    ("opening_queries__L0_L0_L16_L24_L21_L5", 0, 0, 16, 24, 21, 5),
    ("opening_queries__L0_L0_L16_L24_L21_L6", 0, 0, 16, 24, 21, 6),
    ("opening_queries__L0_L0_L16_L24_L22_L4", 0, 0, 16, 24, 22, 4),
    ("opening_queries__L0_L0_L16_L24_L22_L5", 0, 0, 16, 24, 22, 5),
    ("opening_queries__L0_L0_L16_L24_L22_L6", 0, 0, 16, 24, 22, 6),
    ("opening_queries__L0_L0_L16_L24_L23_L5", 0, 0, 16, 24, 23, 5),
    ("opening_queries__L0_L0_L16_L24_L23_L6", 0, 0, 16, 24, 23, 6),
    ("opening_queries__L0_L0_L16_L24_L24_L5", 0, 0, 16, 24, 24, 5),
    ("opening_queries__L0_L0_L16_L24_L24_L6", 0, 0, 16, 24, 24, 6),
    ("opening_queries__L0_L0_L16_L24_L25_L5", 0, 0, 16, 24, 25, 5)]

/-- Every deployed specialization of `opening_queries` is its meaning. -/
def opening_queries_all_Spec : Prop :=
  ∀ sh ∈ openingQueriesShapes,
    opening_queries_Spec sh.1 sh.2.1 sh.2.2.1 sh.2.2.2.1 sh.2.2.2.2.2.1 sh.2.2.2.2.2.2

end
end LeanVM.Guest.B1
