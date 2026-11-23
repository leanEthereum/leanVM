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
public import LeanVM.Guest.B1.Opening.QueriesT

/-!
# The WHIR queries: the interface

`opening_queries(cap, flags, lam_inv, coefs, hs, positions, query_win_ptrs, n_iters_g, odd_g)` with
the compile-time `(base, folds, leaf_cells, path_depth, mu, vanish, n_hs, hs_bits, final)`
(`guests/lean_ethereum.py`, `opening_queries` and `opening_query`) runs one
level's queries of the stacked WHIR opening (`whirLevels`, `Statement/LeanVmVerifier.lean`;
`crates/verifier/src/whir.rs`, `verify_whir`). Query `k` at the position `q_k` (its word
`positions[k] = eOfNat q_k` and its windows at `query_win_ptrs[k]`, both `decode_query_windows`'):

* hints the row: `2^folds` words, each in `K` at level `0` (`base = 1`; the leaf's `K` words), each
  an `E` cell deeper (the leaf's `K` words two by two, `extRow`);
* hashes it (`merkleLeafDigest`) and climbs `path_depth` levels by hinted siblings into the cap
  (`walk_path`, inline): the node reached is written at the cap's leaf `q / 2^path_depth`, at the
  cap pointer the caller offsets past the levels above, and its parent's flag set (`QueryOpens`);
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

/-- `climb` at the deployed hash: the node a path reaches. -/
def climbD (leaf : Digest) (q : ℕ) (sibs : List Digest) : Digest :=
  Id.run (Compile.climbWithHash (m := Id) keccak256 leaf q sibs)

/-- The node a path reaches after its first `l` levels. -/
def climbNode (leaf : Digest) (q : ℕ) (sibs : List Digest) (l : ℕ) : Digest :=
  climbD leaf q (sibs.take l)

/-- Cell `k` of a path's hinted run (`walk_path`'s `path`): level `k / 2`'s sibling, two cells
each. -/
def pathCell (sibs : List Digest) (k : ℕ) : E :=
  let d := sibs.getD (k / 2) (Vector.replicate 4 0)
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

/-- **One query opens** at the position `q`, with the siblings `sibs`, into the cap's leaves at
`capL` and their parents' flags at `flagsL` (the cap and flags offset by the caller past the levels
above, `cap·g^(2^(cd+1))`, `flags·g^(2^(cd-1))`): the row of `rowLen base folds` words of `K`, hashed
(`merkleLeafDigest`, the leaf of `openOne`) and climbed `pd` levels by the siblings (`climbD`, the
position's low bits); the node reached is written at leaf `q / 2^pd`'s cells and its parent
flagged. -/
def QueryOpensS (rd : Reader) (base folds pd : ℕ) (capL flagsL : E) (q : ℕ) (row : List K)
    (sibs : List Digest) : Prop :=
  row.length = rowLen base folds ∧ sibs.length = pd ∧
    LoadHolds rd capL (2 * (q / 2 ^ pd)) (digestHalves (climbD (merkleLeafDigest row) q sibs)).1 ∧
    LoadHolds rd capL (2 * (q / 2 ^ pd) + 1) (digestHalves (climbD (merkleLeafDigest row) q sibs)).2 ∧
    LoadHolds rd flagsL (q / 2 ^ (pd + 1)) 1

/-- `QueryOpensS` for some siblings. -/
def QueryOpens (rd : Reader) (base folds pd : ℕ) (capL flagsL : E) (q : ℕ) (row : List K) : Prop :=
  ∃ sibs, QueryOpensS rd base folds pd capL flagsL q row sibs

/-! ## `opening_queries` -/

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

/-- **Query `k` of `opening_queries`** of shape `sh` at a level of cap depth `cd`, its witness
`w = (q, row, sibs)`, the rounds at `coefs` and the final coefficients at `hs` (`n_hs`, read at the
final level only): the query reads the rounds, its position `positions[k] = eOfNat q`,
`q < 2^(pd + cd)`, and its windows through its window pointer; it opens the row (`QueryOpensS`),
whose fold at `q` is, at the final level, the final polynomial at `q`. -/
def QueryHolds (sh : OqShape) (cd : ℕ) (rd : Reader) (capL flagsL coefs hs positions qptrs : E)
    (rounds : List FoldRound) (hsv : List E) (k : ℕ) (w : QW) : Prop :=
  RoundsAt rd coefs rounds ∧ (sh.final = 1 → WordsAt rd hs hsv) ∧
    LoadHolds rd positions k (eOfNat w.1) ∧ w.1 < 2 ^ (sh.pd + cd) ∧
    (∃ bp, LoadHolds rd qptrs k bp ∧
      ∀ i < qwN (sh.pd + cd) cd, LoadHolds rd bp i (gen ^ qwVal (sh.pd + cd) cd w.1 i)) ∧
    QueryOpensS rd sh.base sh.folds sh.pd capL flagsL w.1 w.2.1 w.2.2 ∧
    (sh.final = 1 → foldRow (lanesOf sh.base w.2.1) (K.ofBits w.1) rounds =
      novelSum hsv (wsChain (sh.vs.map K.ofBits) (eOfNat w.1)) sh.nHs sh.hsBits)

/-- A query's value: its row's fold at its position. -/
def qwFold (base : ℕ) (rounds : List FoldRound) (w : QW) : E :=
  foldRow (lanesOf base w.2.1) (K.ofBits w.1) rounds

/-- **`opening_queries`, its queries those of `ws`**, of shape `sh` at a level of cap depth `cd`
on `[capL, flagsL, lam_inv, coefs, hs, positions, qptrs, n_iters_g, odd_g]`: `n_iters_g = g^N`,
`odd_g = g^odd` (`odd ≤ 1`, `0` deeper than level 0); for some rounds (`folds` of them) and final
coefficients (`n_hs`), query `k < Q` (`oqCount`) holds (`QueryHolds`) with the witness `ws[k]`; at
a non-final level the chain of the folds is in a heap run and returned (the caller scales it by
`λ^Q`), at the final level `0` is returned. -/
def MeaningOpeningQueriesW (sh : OqShape) (cd : ℕ) (rd : Reader) (ws : List QW) :
    List E → List E → Prop
  | [capL, flagsL, lamInv, coefs, hs, positions, qptrs, nG, oddG], rets =>
      ∃ N < ordG, nG = gen ^ N ∧ ∃ odd ≤ sh.base, oddG = gen ^ odd ∧ ws.length = oqCount odd sh.base N ∧
        ∃ (rounds : List FoldRound) (hsv : List E), rounds.length = sh.folds ∧ hsv.length = sh.nHs ∧
          (∀ k < oqCount odd sh.base N,
            QueryHolds sh cd rd capL flagsL coefs hs positions qptrs rounds hsv k (ws.getD k default)) ∧
          if sh.final = 1 then rets = [0]
          else ∃ ch : E,
            (∀ i ≤ N, LoadHolds rd ch i
              (oqChain odd sh.base lamInv (fun k ↦ qwFold sh.base rounds (ws.getD k default)) i)) ∧
            rets = [oqChain odd sh.base lamInv (fun k ↦ qwFold sh.base rounds (ws.getD k default)) N]
  | _, _ => False

/-- **`opening_queries`** of shape `sh` at cap depth `cd`: its meaning for some queries. -/
def MeaningOpeningQueries (sh : OqShape) (cd : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  ∃ ws, MeaningOpeningQueriesW sh cd rd ws args rets

/-- `opening_queries`' function in the program `P` (named `name`, of shape `sh`) is its meaning
at every cap depth `1 ≤ cd ≤ 8`, when the positions and window pointers name positions of depth
`pd + cd` and `odd_g` is `g^odd`, `odd ≤ base`. -/
def opening_queries_SpecP (P : Program) (name : String) (sh : OqShape) : Prop :=
  ∀ (cd : ℕ), 1 ≤ cd → cd ≤ 8 →
    ∀ (rd : Reader) (capL flagsL lamInv coefs hs positions qptrs nG oddG : E) (rets : List E),
    (∀ N odd, nG = gen ^ N → N < ordG → oddG = gen ^ odd → odd ≤ sh.base →
      QueryPosOk rd positions qptrs (oqCount odd sh.base N) (sh.pd + cd) cd) →
    (P.Rel rd name [capL, flagsL, lamInv, coefs, hs, positions, qptrs, nG, oddG] rets ↔
      MeaningOpeningQueries sh cd rd [capL, flagsL, lamInv, coefs, hs, positions, qptrs, nG, oddG] rets)

/-- The deployed specializations, by name (a name built by `++ toString` does not reduce in a
`module`'s kernel), with their shapes: level 0 (`base = 1`, `folds = 6`, `leaf_cells = 32`), deeper
levels (`base = 0`, `folds = 4`, `leaf_cells = 16`), the final ones (`final = 1`) with their `mu`,
`n_hs = 2^mu + 4`, `hs_bits = mu + 1` and vanishing constants. -/
def openingQueriesShapes : List (String × OqShape) :=
  -- Generated by `scripts/whir-queries/lists.py`; do not edit.
  [("opening_queries__L1_L6_L32_L12_L0_L0_L0_L0_L0", ⟨1, 6, 32, 12, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L4_L16_L12_L0_L0_L0_L0_L0", ⟨0, 4, 16, 12, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L4_L16_L6_L0_L0_L0_L0_L0", ⟨0, 4, 16, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L4_L16_L6_L2_L3_L8_L3_L1", ⟨0, 4, 16, 6, 2, 3, 8, 3, 1, [1, 6]⟩),
    ("opening_queries__L0_L4_L16_L12_L2_L3_L8_L3_L1", ⟨0, 4, 16, 12, 2, 3, 8, 3, 1, [1, 6]⟩),
    ("opening_queries__L0_L4_L16_L6_L3_L6_L12_L4_L1", ⟨0, 4, 16, 6, 3, 6, 12, 4, 1, [1, 6, 360]⟩),
    ("opening_queries__L0_L4_L16_L12_L3_L6_L12_L4_L1", ⟨0, 4, 16, 12, 3, 6, 12, 4, 1, [1, 6, 360]⟩),
    ("opening_queries__L1_L6_L32_L18_L0_L0_L0_L0_L0", ⟨1, 6, 32, 18, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L4_L16_L12_L4_L10_L20_L5_L1", ⟨0, 4, 16, 12, 4, 10, 20, 5, 1, [1, 6, 360,
        18245760]⟩),
    ("opening_queries__L0_L4_L16_L18_L0_L0_L0_L0_L0", ⟨0, 4, 16, 18, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L4_L16_L12_L5_L15_L36_L6_L1", ⟨0, 4, 16, 12, 5, 15, 36, 6, 1, [1, 6, 360,
        18245760, 78274681211224091]⟩),
    ("opening_queries__L0_L4_L16_L18_L4_L10_L20_L5_L1", ⟨0, 4, 16, 18, 4, 10, 20, 5, 1, [1, 6, 360,
        18245760]⟩),
    ("opening_queries__L0_L4_L16_L18_L5_L15_L36_L6_L1", ⟨0, 4, 16, 18, 5, 15, 36, 6, 1, [1, 6, 360,
        18245760, 78274681211224091]⟩),
    ("opening_queries__L1_L6_L32_L24_L0_L0_L0_L0_L0", ⟨1, 6, 32, 24, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L4_L16_L18_L2_L3_L8_L3_L1", ⟨0, 4, 16, 18, 2, 3, 8, 3, 1, [1, 6]⟩),
    ("opening_queries__L0_L4_L16_L24_L0_L0_L0_L0_L0", ⟨0, 4, 16, 24, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L4_L16_L18_L3_L6_L12_L4_L1", ⟨0, 4, 16, 18, 3, 6, 12, 4, 1, [1, 6, 360]⟩)]

/-- Every deployed specialization of `opening_queries` is its meaning. -/
def opening_queries_all_SpecP (P : Program) : Prop :=
  ∀ p ∈ openingQueriesShapes, opening_queries_SpecP P p.1 p.2

/-! ## The Spec's novel basis -/

/-- The normalizers' product of the coefficient `c`: `Π_(i < nbits, c_i = 1) inv_i`. -/
def novelScale (invs : List K) (nbits c : ℕ) : E :=
  ((List.range nbits).map fun i ↦ if c.testBit i then ofK (invs.getD i 0) else 1).prod

end
end LeanVM.Guest.B1
