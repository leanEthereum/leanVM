/-
  LeanVM.Guest.B1.Place.Lq

  `level_queries` complete placed, at every specialization of `lqTable`: the statement.
-/

module

public import LeanVM.Guest.B1.Place.HelperAt
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Opening.QueriesPlacedAll
public import LeanVM.Guest.B1.Whir.CLq
public import LeanVM.Guest.B1.Whir.HelperAll

/-!
# `level_queries`, placed

`level_queries__L{q}_L{base}_L{il}_L{leaf}_L{d}_L{cd}(lam, win_ptrs, row_eq_weights)`
(`lqBody q base il leaf d cd`) hints the cap (`4·2^cd` cells) and its active flags (`2^cd`) into
two `HeapBuf`s of its own, checks the cap up to the root `(r0, r1)` by `verify_merkle_cap__L{cd}`,
computes `lam^q`, calls `opening_queries` (`oqName q base il leaf d cd`, shape `lqShape`, `odd =
q % 2 · base`, `lqIters q base` iterations) on the cap, the flags, `lam`, `lam^q`, the window
pointers and the row weights, and returns the root, the queries' sum and `lam^q`.

**The statement** (`LqAtO`): the honest cap `capW` and flags `flW` (the hints), checked to
`(r0, r1)` by `verify_merkle_cap` on every memory holding them, each query `k < q`'s leaf
climbed to the cap's cells and its parent flagged; the caller's words `Lin` holding the row
weights `w` at `ewp`, query `k`'s window pointer `g^(eb k)` at `eqp + k` and its position `qs k`'s
windows at `eb k` (all three where `OqLinReg` puts them); then the helper on
`[lam, g^eqp, g^ewp]` returns `[r0, r1, chain·lam^q, lam^q]`, `chain` the queries' values'
`oqChain`, by a tree within `Bd` when given. `level_queries_completeAt_Spec`: every entry of
`lqTable`.

**Design note for the proof.** Build on:
* `lq_complete` (`Whir/CLq.lean`): the unplaced relation from `verify_merkle_cap`'s and
  `opening_queries`' relations; `lqTable_ok` for the bodies.
* `opening_queries_completeAtB` (`Opening/QueriesPlacedAll.lean`, `OqCompleteDB`, its `toD`): the
  callee placed, its `OqLinMem` from `Lin` and the two hinted buffers (the helper's own words,
  holding `capW` and `flW`); its entry in `openingQueriesLoops` at `oqName …` by `decide`.
* `verify_merkle_cap` a leaf: `completeRelRegDB_of_iff` with `merkleCap_leafSpec` and
  `verify_merkle_cap_holds` (`Place/OsMeanB.lean`'s `kindDB` does the same).
* a straight-line body with two `HeapBuf`s, two calls in sequence (`kidsFromIn_append`), the
  bound by `TotalLe` at `Bd = some B`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (lqIters lqTable natStr)
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- The shape of `opening_queries` a level of base `base`, `il` words a row, depth `d` and cap
depth `cd` calls. -/
def lqShape (base il d cd : ℕ) : Oq := ⟨base, il, d - cd, cd⟩

/-- The honest cap and flags of `q` queries: the cap checked to the root `(r0, r1)` on every
memory holding both, each query's leaf climbed to its cap cells, its parent flagged. -/
def LqCaps (s : Oq) (q : ℕ) (capW flW : List E) (r0 r1 : E) (qs : ℕ → ℕ) (rows : ℕ → List K)
    (sibs : ℕ → List Digest) : Prop :=
  capW.length = 4 * 2 ^ s.cd ∧ flW.length = 2 ^ s.cd ∧
    (∀ (rd : Reader) (CAP FL : E), ReadsAt rd CAP capW → ReadsAt rd FL flW →
      coreProgram.Rel rd ("verify_merkle_cap__L" ++ natStr s.cd) [CAP, FL] [r0, r1]) ∧
    ∀ k < q, qs k < 2 ^ (s.pd + s.cd) ∧ (rows k).length = s.R ∧ (sibs k).length = s.pd ∧
      capW.getD (2 * (2 ^ s.cd + qs k / 2 ^ s.pd)) 0 =
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).1 ∧
      capW.getD (2 * (2 ^ s.cd + qs k / 2 ^ s.pd) + 1) 0 =
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).2 ∧
      flW.getD (2 ^ (s.cd - 1) + qs k / 2 ^ (s.pd + 1)) 0 = 1

/-- Where the caller's words `level_queries` reads lie: the row weights from `ewp`, the window
pointers from `eqp`, query `k`'s windows from `eb k`. -/
def LqReg (R : ℕ → Prop) (s : Oq) (q eqp ewp : ℕ) (eb : ℕ → ℕ) : Prop :=
  (∀ l < s.lo + s.I / s.lo, R (ewp + l)) ∧
    ∀ k < q, R (eqp + k) ∧ ∀ i < qwN (s.pd + s.cd) s.cd, R (eb k + i)

/-- The caller's words `level_queries` reads, on a memory: the row weights `w`, query `k`'s window
pointer `g^(eb k)` and, there, its position `qs k`'s windows. -/
def LqMem (rd : Reader) (s : Oq) (q eqp ewp : ℕ) (w : ℕ → E) (eb qs : ℕ → ℕ) : Prop :=
  (∀ l < s.lo + s.I / s.lo, LoadHolds rd (ofK (addressOfIndex ewp)) l (w l)) ∧
    ∀ k < q, LoadHolds rd (ofK (addressOfIndex eqp)) k (ofK (addressOfIndex (eb k))) ∧
      ∀ i < qwN (s.pd + s.cd) s.cd,
        LoadHolds rd (ofK (addressOfIndex (eb k))) i (gen ^ qwVal (s.pd + s.cd) s.cd (qs k) i)

/-- **`level_queries` at `(name, q, base, il, leaf, d, cd)`, placed**: on the honest cap and flags
(`LqCaps`) and the caller's words (`LqReg`, `LqMem`), complete by a tree within `Bd` when given,
returning the root, the queries' chain times `lam^q`, and `lam^q`. -/
def LqAtO (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String)
    (q base il _leaf d cd : ℕ) (Bd : Option ℕ) : Prop :=
  ∀ (Lin : Layout) (eqp ewp : ℕ) (lam : E) (w : ℕ → E) (eb qs : ℕ → ℕ) (rows : ℕ → List K)
    (sibs : ℕ → List Digest) (capW flW : List E) (r0 r1 : E), lam ≠ 0 →
    LqCaps (lqShape base il d cd) q capW flW r0 r1 qs rows sibs →
    LqReg (RegionL Lin) (lqShape base il d cd) q eqp ewp eb →
    (∀ rd, LowDef κ rd → MemL rd Lin → LqMem rd (lqShape base il d cd) q eqp ewp w eb qs) →
    BoundsAt fs name Bd →
    CompleteAtO fs cert κ name Lin [lam, ofK (addressOfIndex eqp), ofK (addressOfIndex ewp)]
      (Returns [r0, r1, oqChain (q % 2 * base) base lam⁻¹ (fun k ↦ rowDot base il (rows k) w)
        (lqIters q base) * lam ^ q, lam ^ q]) Bd

/-- **`level_queries` is complete placed at every specialization**: for frame runs fitting their
frames, their cells consecutive, on memories defined below `2^κ`, `7 ≤ κ`, each entry of
`lqTable` is `LqAtO` at every bound. -/
def level_queries_completeAt_Spec : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), Lift.RunsFit fs cert → RunsConsec cert →
    7 ≤ κ → ∀ e ∈ lqTable, ∀ Bd : Option ℕ,
      LqAtO fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 Bd

end
end LeanVM.Guest.B1
