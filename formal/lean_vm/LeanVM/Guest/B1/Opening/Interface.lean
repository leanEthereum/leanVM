/-
  LeanVM.Guest.B1.Opening.Interface

  The interface of the WHIR queries (`opening_queries`, its inline `opening_query` and
  `novel_eval`): what a call establishes against the Spec's `foldRow` and `novelEval`, and the
  statement that every specialization's core IR establishes it.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsT
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.B1.Opening.FoldAlg

/-!
# The WHIR queries: the interface

`opening_queries(cap, flags, lam_inv, coefs, hs, positions, query_win_ptrs, n_iters_g)` with the
compile-time `(odd, base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)`
(`crates/rec_aggregation/guests/lean_ethereum.py`, `opening_queries` and `opening_query`) runs one
level's queries of the stacked WHIR opening (`whirLevels`, `Statement/LeanVmVerifier.lean`;
`crates/verifier/src/whir.rs`, `verify_whir`). Query `k` at the position `q_k` (its word
`positions[k] = eOfNat q_k` and its windows at `query_win_ptrs[k]`, both `decode_query_windows`'):

* hints the row: `2^folds` words, each in `K` at level `0` (`base = 1`; the leaf's `K` words), each
  an `E` cell deeper (the leaf's `K` words two by two, `extRow`);
* hashes it (`merkleLeafDigest`) and climbs `depth - cap_depth` levels by hinted siblings into the
  cap (`walk_path`): the node reached is written at the cap's cells of node
  `2^cd + q / 2^(depth - cd)` and its parent's flag set (`QueryOpens`);
* folds the row's lanes (`lanesOf`: level `0`'s reversed, deeper ones as they are) at its point
  round by round (`foldRow`), the rounds' `(α, β)` at `coefs[2j], coefs[2j + 1]`;
* at a non-final level (`final = 0`) the fold is the query's value `d_k`, and the function returns
  `Σ_k d_k λ^(k - Q)` (`oqChain`, `λ⁻¹ = lam_inv`), which the caller scales by `λ^Q`; at the final
  level (`final = 1`) the fold must be the final polynomial at the point: `novelSum hs` over the
  unnormalized subspace chain `wsChain vs x` (`W_0 = x`, `W_(i+1) = W_i (W_i + vs_i)`, `vs` the
  specialization's `LIG_VANISH_VALS` row, `W_i(β_i)`), the normalizers carried by `hs`; it
  returns `0`.

`novelSum_eq_novelEval` relates the final check to the Spec's
`novelEval folded (subspaceAt mu x)` when `hs` carries the normalizers.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The Merkle path -/

/-- `climb` (V:351) at the deployed hash: the node a path reaches. -/
def climbD (leaf : Digest) (q : ℕ) (sibs : List Digest) : Digest :=
  Id.run (Compile.climbWithHash (m := Id) keccak256 leaf q sibs)

/-- The node a path reaches after its first `l` levels. -/
def climbNode (leaf : Digest) (q : ℕ) (sibs : List Digest) (l : ℕ) : Digest :=
  climbD leaf q (sibs.take l)

/-- Cell `k` of a path's frame run (`walk_path`'s `path`): level `k / 4`'s children, two cells
each, the node reached so far on the side of the position's bit at the level, the sibling on the
other. -/
def pathCell (leaf : Digest) (q : ℕ) (sibs : List Digest) (k : ℕ) : E :=
  let d := if (k % 4) / 2 = (if q.testBit (k / 4) then 1 else 0) then climbNode leaf q sibs (k / 4)
    else sibs.getD (k / 4) (Vector.replicate 4 0)
  if k % 2 = 0 then (digestHalves d).1 else (digestHalves d).2

/-! ## The row and its fold -/

/-- The `K` words of a row: `2^folds` at level `0` (`base = 1`), `2·2^folds` deeper. -/
def rowLen (base folds : ℕ) : ℕ := if base = 1 then 2 ^ folds else 2 * 2 ^ folds

/-- The row's lanes in `eq_kernel` order (`whirLevels`' `lanesOf`): level `0`'s leaf image
reversed, a deeper level's regrouped into `E` (`extRow`). -/
def lanesOf (base : ℕ) (row : List K) : List E :=
  if base = 1 then row.reverse.map ofK else extRow row

/-- The rounds' challenges at `coefs`: round `j`'s `α, β` at `2j, 2j + 1`. -/
def RoundsAt (rd : Reader) (coefs : E) (rounds : List FoldRound) : Prop :=
  ∀ j < rounds.length, LoadHolds rd coefs (2 * j) (rounds.getD j ⟨0, 0⟩).alpha ∧
    LoadHolds rd coefs (2 * j + 1) (rounds.getD j ⟨0, 0⟩).beta

/-- The `n` words at `p`. -/
def WordsAt (rd : Reader) (p : E) (xs : List E) : Prop :=
  ∀ c < xs.length, LoadHolds rd p c (xs.getD c 0)

/-! ## One query -/

/-- A query's witness: its position, its row and its siblings below the cap. -/
abbrev QW : Type := ℕ × List K × List Digest

/-- **One query opens** at the position `q`, with the siblings `sibs`: the row of
`rowLen base folds` words of `K`, hashed (`merkleLeafDigest`, the leaf of `openOne`) and climbed
`depth - cd` levels by the siblings (`climbD`, the position's low bits); the node reached is
written at the cap's cells of node `2^cd + q / 2^(depth - cd)` and its parent flagged. -/
def QueryOpensS (rd : Reader) (base folds depth cd : ℕ) (cap flags : E) (q : ℕ) (row : List K)
    (sibs : List Digest) : Prop :=
  row.length = rowLen base folds ∧ sibs.length = depth - cd ∧
    LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ (depth - cd)))
      (digestHalves (climbD (merkleLeafDigest row) q sibs)).1 ∧
    LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ (depth - cd)) + 1)
      (digestHalves (climbD (merkleLeafDigest row) q sibs)).2 ∧
    LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (depth - cd + 1)) 1

/-- `QueryOpensS` for some siblings. -/
def QueryOpens (rd : Reader) (base folds depth cd : ℕ) (cap flags : E) (q : ℕ) (row : List K) :
    Prop :=
  ∃ sibs, QueryOpensS rd base folds depth cd cap flags q row sibs

/-! ## `opening_queries` -/

/-- The shape of a specialization: its compile-time parameters, and its row of
`LIG_VANISH_VALS` (`vs`, `mu` words from `vanish`, as the core IR's constants). -/
structure OqShape where
  odd : ℕ
  base : ℕ
  folds : ℕ
  leafCells : ℕ
  depth : ℕ
  cd : ℕ
  mu : ℕ
  vanish : ℕ
  nHs : ℕ
  hsBits : ℕ
  final : ℕ
  vs : List ℕ

/-- The number of queries at `n_iters_g = g^N`: `odd + 2N` at level 0, `N` deeper. -/
def oqCount (odd base N : ℕ) : ℕ := if base = 1 then odd + 2 * N else N

/-- The chain `h ← (h + d_k)·μ` over the queries' values, `μ = λ⁻¹`, after `i` iterations (two
queries an iteration at level 0, an odd count's first alone before them). -/
def oqChain (odd base : ℕ) (mu : E) (ds : ℕ → E) : ℕ → E
  | 0 => if odd = 1 then ds 0 * mu else 0
  | i + 1 =>
    if base = 1 then ((oqChain odd base mu ds i + ds (odd + 2 * i)) * mu + ds (odd + 2 * i + 1)) * mu
    else (oqChain odd base mu ds i + ds i) * mu

/-- The positions and window pointers name positions: query `k < Q`'s word `positions[k]` is
`eOfNat q` and its window pointer names a frame run holding `q`'s windows `g^(qwVal …)`, for some
`q < 2^depth` (what `decode_query_windows` writes, `MeaningDecodeQueryWindows`). -/
def QueryPosOk (rd : Reader) (positions qptrs : E) (Q depth cd : ℕ) : Prop :=
  ∀ k < Q, ∀ x bp, LoadHolds rd positions k x → LoadHolds rd qptrs k bp →
    ∃ q < 2 ^ depth, x = eOfNat q ∧ FrameRun rd bp (qwN depth cd) fun i ↦ gen ^ qwVal depth cd q i

/-- **Query `k` of `opening_queries`** of shape `sh`, its witness `w = (q, row, sibs)`, the rounds
at `coefs` and the final coefficients at `hs` (`n_hs`, read at the final level only): the query
reads the rounds, its position `positions[k] = eOfNat q`, `q < 2^depth`, and its windows through
its window pointer; it opens the row (`QueryOpensS`), whose fold at `q` is, at the final level,
the final polynomial at `q`. -/
def QueryHolds (sh : OqShape) (rd : Reader) (cap flags coefs hs positions qptrs : E)
    (rounds : List FoldRound) (hsv : List E) (k : ℕ) (w : QW) : Prop :=
  RoundsAt rd coefs rounds ∧ (sh.final = 1 → WordsAt rd hs hsv) ∧
    LoadHolds rd positions k (eOfNat w.1) ∧ w.1 < 2 ^ sh.depth ∧
    (∃ bp, LoadHolds rd qptrs k bp ∧
      ∀ i < qwN sh.depth sh.cd, LoadHolds rd bp i (gen ^ qwVal sh.depth sh.cd w.1 i)) ∧
    QueryOpensS rd sh.base sh.folds sh.depth sh.cd cap flags w.1 w.2.1 w.2.2 ∧
    (sh.final = 1 → foldRow (lanesOf sh.base w.2.1) (K.ofBits w.1) rounds =
      novelSum hsv (wsChain (sh.vs.map K.ofBits) (eOfNat w.1)) sh.nHs sh.hsBits)

/-- A query's value: its row's fold at its position. -/
def qwFold (base : ℕ) (rounds : List FoldRound) (w : QW) : E :=
  foldRow (lanesOf base w.2.1) (K.ofBits w.1) rounds

/-- **`opening_queries`, its queries those of `ws`**, of shape `sh` on `[cap, flags, lam_inv,
coefs, hs, positions, qptrs, n_iters_g]`: `n_iters_g = g^N`; for some rounds (`folds` of them)
and final coefficients (`n_hs`), query `k < Q` (`oqCount`) holds (`QueryHolds`) with the witness
`ws[k]`; at a non-final level the chain of the folds is in a heap run and returned (the caller
scales it by `λ^Q`), at the final level `0` is returned. -/
def MeaningOpeningQueriesW (sh : OqShape) (rd : Reader) (ws : List QW) : List E → List E → Prop
  | [cap, flags, lamInv, coefs, hs, positions, qptrs, nG], rets =>
      ∃ N < ordG, nG = gen ^ N ∧ ws.length = oqCount sh.odd sh.base N ∧
        ∃ (rounds : List FoldRound) (hsv : List E), rounds.length = sh.folds ∧ hsv.length = sh.nHs ∧
          (∀ k < oqCount sh.odd sh.base N,
            QueryHolds sh rd cap flags coefs hs positions qptrs rounds hsv k (ws.getD k default)) ∧
          if sh.final = 1 then rets = [0]
          else ∃ ch : E,
            (∀ i ≤ N, LoadHolds rd ch i
              (oqChain sh.odd sh.base lamInv (fun k ↦ qwFold sh.base rounds (ws.getD k default)) i)) ∧
            rets = [oqChain sh.odd sh.base lamInv (fun k ↦ qwFold sh.base rounds (ws.getD k default)) N]
  | _, _ => False

/-- **`opening_queries`** of shape `sh`: its meaning for some queries. -/
def MeaningOpeningQueries (sh : OqShape) (rd : Reader) (args rets : List E) : Prop :=
  ∃ ws, MeaningOpeningQueriesW sh rd ws args rets

/-- `opening_queries`' core IR (the function named `name`, of shape `sh`) is its meaning, when
the positions and window pointers name positions. -/
def opening_queries_Spec (name : String) (sh : OqShape) : Prop :=
  ∀ (rd : Reader) (cap flags lamInv coefs hs positions qptrs nG : E) (rets : List E),
    (∀ N, nG = gen ^ N → N < ordG → QueryPosOk rd positions qptrs (oqCount sh.odd sh.base N)
      sh.depth sh.cd) →
    (coreProgram.Rel rd name [cap, flags, lamInv, coefs, hs, positions, qptrs, nG] rets ↔
      MeaningOpeningQueries sh rd [cap, flags, lamInv, coefs, hs, positions, qptrs, nG] rets)

/-- The 73 deployed specializations, by name (a name built by `++ toString` does not reduce in a
`module`'s kernel), with their shapes: level 0 (`base = 1`, `folds = 6`, `leaf_cells = 32`), deeper
levels (`base = 0`, `odd = 0`, `folds = 4`, `leaf_cells = 16`), the final ones (`final = 1`) with
their `mu`, `n_hs = 2^mu + 4`, `hs_bits = mu + 1` and vanishing constants. -/
def openingQueriesShapes : List (String × OqShape) :=
  [("opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 15, 3, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L1_L1_L6_L32_L16_L4_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 14, 2, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L15_L3_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 15, 3, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L16_L4_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 16, 4, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 13, 7, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L12_L6_L2_L3_L8_L3_L1", ⟨0, 0, 4, 16, 12, 6, 2, 3, 8, 3, 1, [1,
        6]⟩),
    ("opening_queries__L0_L0_L4_L16_L13_L7_L2_L3_L8_L3_L1", ⟨0, 0, 4, 16, 13, 7, 2, 3, 8, 3, 1, [1,
        6]⟩),
    ("opening_queries__L0_L0_L4_L16_L14_L2_L2_L3_L8_L3_L1", ⟨0, 0, 4, 16, 14, 2, 2, 3, 8, 3, 1, [1,
        6]⟩),
    ("opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1", ⟨0, 0, 4, 16, 15, 3, 2, 3, 8, 3, 1, [1,
        6]⟩),
    ("opening_queries__L0_L1_L6_L32_L16_L4_L0_L0_L0_L0_L0", ⟨0, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1", ⟨0, 0, 4, 16, 13, 7, 3, 6, 12, 4, 1,
        [1, 6, 360]⟩),
    ("opening_queries__L0_L0_L4_L16_L14_L2_L3_L6_L12_L4_L1", ⟨0, 0, 4, 16, 14, 2, 3, 6, 12, 4, 1,
        [1, 6, 360]⟩),
    ("opening_queries__L0_L0_L4_L16_L15_L3_L3_L6_L12_L4_L1", ⟨0, 0, 4, 16, 15, 3, 3, 6, 12, 4, 1,
        [1, 6, 360]⟩),
    ("opening_queries__L0_L0_L4_L16_L16_L4_L3_L6_L12_L4_L1", ⟨0, 0, 4, 16, 16, 4, 3, 6, 12, 4, 1,
        [1, 6, 360]⟩),
    ("opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0", ⟨0, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L20_L2_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 20, 2, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L19_L7_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 19, 7, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L14_L2_L4_L10_L20_L5_L1", ⟨0, 0, 4, 16, 14, 2, 4, 10, 20, 5, 1,
        [1, 6, 360, 18245760]⟩),
    ("opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1", ⟨0, 0, 4, 16, 15, 3, 4, 10, 20, 5, 1,
        [1, 6, 360, 18245760]⟩),
    ("opening_queries__L0_L0_L4_L16_L16_L4_L4_L10_L20_L5_L1", ⟨0, 0, 4, 16, 16, 4, 4, 10, 20, 5, 1,
        [1, 6, 360, 18245760]⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L5_L4_L10_L20_L5_L1", ⟨0, 0, 4, 16, 17, 5, 4, 10, 20, 5, 1,
        [1, 6, 360, 18245760]⟩),
    ("opening_queries__L0_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0", ⟨0, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L20_L2_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 20, 2, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L15_L3_L5_L15_L36_L6_L1", ⟨0, 0, 4, 16, 15, 3, 5, 15, 36, 6, 1,
        [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L0_L0_L4_L16_L16_L4_L5_L15_L36_L6_L1", ⟨0, 0, 4, 16, 16, 4, 5, 15, 36, 6, 1,
        [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1", ⟨0, 0, 4, 16, 17, 5, 5, 15, 36, 6, 1,
        [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L6_L5_L15_L36_L6_L1", ⟨0, 0, 4, 16, 18, 6, 5, 15, 36, 6, 1,
        [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L0_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0", ⟨0, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 21, 3, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L16_L4_L2_L3_L8_L3_L1", ⟨0, 0, 4, 16, 16, 4, 2, 3, 8, 3, 1, [1,
        6]⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L5_L2_L3_L8_L3_L1", ⟨0, 0, 4, 16, 17, 5, 2, 3, 8, 3, 1, [1,
        6]⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L6_L2_L3_L8_L3_L1", ⟨0, 0, 4, 16, 18, 6, 2, 3, 8, 3, 1, [1,
        6]⟩),
    ("opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0", ⟨0, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L5_L3_L6_L12_L4_L1", ⟨0, 0, 4, 16, 17, 5, 3, 6, 12, 4, 1,
        [1, 6, 360]⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1", ⟨0, 0, 4, 16, 18, 6, 3, 6, 12, 4, 1,
        [1, 6, 360]⟩),
    ("opening_queries__L0_L0_L4_L16_L19_L7_L3_L6_L12_L4_L1", ⟨0, 0, 4, 16, 19, 7, 3, 6, 12, 4, 1,
        [1, 6, 360]⟩),
    ("opening_queries__L0_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0", ⟨0, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L6_L4_L10_L20_L5_L1", ⟨0, 0, 4, 16, 18, 6, 4, 10, 20, 5, 1,
        [1, 6, 360, 18245760]⟩),
    ("opening_queries__L0_L0_L4_L16_L19_L7_L4_L10_L20_L5_L1", ⟨0, 0, 4, 16, 19, 7, 4, 10, 20, 5, 1,
        [1, 6, 360, 18245760]⟩),
    ("opening_queries__L0_L0_L4_L16_L20_L2_L4_L10_L20_L5_L1", ⟨0, 0, 4, 16, 20, 2, 4, 10, 20, 5, 1,
        [1, 6, 360, 18245760]⟩),
    ("opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0", ⟨0, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L19_L7_L5_L15_L36_L6_L1", ⟨0, 0, 4, 16, 19, 7, 5, 15, 36, 6, 1,
        [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1", ⟨0, 0, 4, 16, 20, 2, 5, 15, 36, 6, 1,
        [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L0_L0_L4_L16_L21_L3_L5_L15_L36_L6_L1", ⟨0, 0, 4, 16, 21, 3, 5, 15, 36, 6, 1,
        [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L0_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0", ⟨0, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L26_L2_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 26, 2, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 25, 7, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L19_L7_L2_L3_L8_L3_L1", ⟨0, 0, 4, 16, 19, 7, 2, 3, 8, 3, 1, [1,
        6]⟩),
    ("opening_queries__L0_L0_L4_L16_L20_L2_L2_L3_L8_L3_L1", ⟨0, 0, 4, 16, 20, 2, 2, 3, 8, 3, 1, [1,
        6]⟩),
    ("opening_queries__L0_L0_L4_L16_L21_L3_L2_L3_L8_L3_L1", ⟨0, 0, 4, 16, 21, 3, 2, 3, 8, 3, 1, [1,
        6]⟩),
    ("opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0", ⟨0, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L27_L3_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 27, 3, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L26_L2_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 26, 2, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L20_L2_L3_L6_L12_L4_L1", ⟨0, 0, 4, 16, 20, 2, 3, 6, 12, 4, 1,
        [1, 6, 360]⟩),
    ("opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1", ⟨0, 0, 4, 16, 21, 3, 3, 6, 12, 4, 1,
        [1, 6, 360]⟩),
    ("opening_queries__L0_L0_L4_L16_L22_L4_L3_L6_L12_L4_L1", ⟨0, 0, 4, 16, 22, 4, 3, 6, 12, 4, 1,
        [1, 6, 360]⟩),
    ("opening_queries__L0_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0", ⟨0, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L1_L1_L6_L32_L28_L4_L0_L0_L0_L0_L0", ⟨1, 1, 6, 32, 28, 4, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0", ⟨0, 0, 4, 16, 27, 3, 0, 0, 0, 0, 0,
        []⟩),
    ("opening_queries__L0_L0_L4_L16_L21_L3_L4_L10_L20_L5_L1", ⟨0, 0, 4, 16, 21, 3, 4, 10, 20, 5, 1,
        [1, 6, 360, 18245760]⟩),
    ("opening_queries__L0_L0_L4_L16_L22_L4_L4_L10_L20_L5_L1", ⟨0, 0, 4, 16, 22, 4, 4, 10, 20, 5, 1,
        [1, 6, 360, 18245760]⟩),
    ("opening_queries__L0_L0_L4_L16_L23_L5_L4_L10_L20_L5_L1", ⟨0, 0, 4, 16, 23, 5, 4, 10, 20, 5, 1,
        [1, 6, 360, 18245760]⟩)]

/-- Every deployed specialization of `opening_queries` is its meaning. -/
def opening_queries_all_Spec : Prop :=
  ∀ p ∈ openingQueriesShapes, opening_queries_Spec p.1 p.2

/-! ## The Spec's novel basis -/

/-- The normalizers' product of the coefficient `c`: `Π_(i < nbits, c_i = 1) inv_i`. -/
def novelScale (invs : List K) (nbits c : ℕ) : E :=
  ((List.range nbits).map fun i ↦ if c.testBit i then ofK (invs.getD i 0) else 1).prod

end
end LeanVM.Guest.B1
