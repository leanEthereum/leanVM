/-
  LeanVM.Guest.B1.Place.Lq

  `level_queries` complete placed, at every specialization of `lqTable`: the statement.
-/

module

public import LeanVM.Guest.B1.Place.HelperAt
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2
public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.B1.Whir.HelperT
public import LeanVM.Guest.B1.Whir.Witness
public import LeanVM.Guest.B1.Whir.LqSound
public import LeanVM.Guest.B1.Bits.QueryWindowsAt

/-!
# `level_queries`, placed

`level_queries__L{q}_L{base}_…_L{d}_L{cd}_…(lam, lam_inv, coefs, hs, positions, win_ptrs)`
(`lqBody`) hints the cap (`4·2^cd` cells) and its active flags (`2^cd`) into two `HeapBuf`s of
its own, checks the cap up to the root `(r0, r1)` by `verify_merkle_cap__L{cd}`, calls
`opening_queries` (`oqName …`, its shape `lqOqS`, `lqIters q base` iterations) on the cap, the
flags, `1/λ`, the round coefficients, the high part, the positions and the window pointers, and
returns the root, the queries' sum and `λ^q`.

**The statement** (`LqAtEP`, `LqProofP.lean`, with the pops): the honest cap `capW` and flags `flW` (the hints), checked to
`(r0, r1)` by `verify_merkle_cap` on every memory holding them, each query `k < q`'s leaf climbed
to the cap's cells and its parent flagged (`LqCaps`); the caller's words `Lin` holding the rounds
at `coefs`, the final level's high part at `hs`, query `k`'s position at `positions`, its window
pointer `g^(eb k)` at `win_ptrs` and its windows there (`LqReg`, `LqMem`); then the helper on
`[λ, 1/λ, g^ecoefs, g^ehs, g^epos, g^eqp]` returns `[r0, r1, chain, λ^q]`, `chain` the queries'
`oqChain` (`0` at the final level).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- The `opening_queries` specialization of `level_queries` at the entry's numbers. -/
abbrev lqOqN (base folds leaf d cd mu nhs hbits fin : ℕ) : String :=
  oqName base folds leaf (d - cd) mu nhs hbits fin

/-- Its shape. -/
abbrev lqOqS (base folds leaf d cd mu nhs hbits fin : ℕ) : Oq :=
  (oqShapeOf (lqOqN base folds leaf d cd mu nhs hbits fin)).oq

/-- The honest cap and flags of `q` queries at cap depth `cd`: the cap checked to the root
`(r0, r1)` on every memory holding both, each query's leaf climbed to its cap cells, its parent
flagged. -/
def LqCaps (s : Oq) (cd q : ℕ) (capW flW : List E) (r0 r1 : E) (qs : ℕ → ℕ) (rows : ℕ → List K)
    (sibs : ℕ → List Digest) : Prop :=
  capW.length = 4 * 2 ^ cd ∧ flW.length = 2 ^ cd ∧
    (∀ (rd : Reader) (CAP FL : E), ReadsAt rd CAP capW → ReadsAt rd FL flW →
      MeaningVerifyMerkleCap cd rd [CAP, FL] [r0, r1]) ∧
    ∀ k < q,
      capW.getD (2 * (2 ^ cd + qs k / 2 ^ s.pd)) 0 =
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).1 ∧
      capW.getD (2 * (2 ^ cd + qs k / 2 ^ s.pd) + 1) 0 =
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).2 ∧
      flW.getD (2 ^ (cd - 1) + qs k / 2 ^ (s.pd + 1)) 0 = 1

/-- Where the caller's words `level_queries` reads lie: the rounds' coefficients from `ecoefs`,
the final level's high part from `ehs`, the positions from `epos`, the window pointers from
`eqp`, query `k`'s windows from `eb k`. -/
def LqReg (R : ℕ → Prop) (s : Oq) (cd q ecoefs ehs epos eqp : ℕ) (eb : ℕ → ℕ) : Prop :=
  (∀ l < 2 * s.folds, R (ecoefs + l)) ∧ (s.final = 1 → ∀ l < s.nHs, R (ehs + l)) ∧
    ∀ k < q, R (epos + k) ∧ R (eqp + k) ∧ ∀ i < qwN (s.pd + cd) cd, R (eb k + i)

/-- The caller's words `level_queries` reads, on a memory. -/
def LqMem (rd : Reader) (s : Oq) (cd q ecoefs ehs epos eqp : ℕ) (rounds : List FoldRound)
    (hsv : List E) (eb qs : ℕ → ℕ) : Prop :=
  RoundsAt rd (ofK (addressOfIndex ecoefs)) rounds ∧
    (s.final = 1 → WordsAt rd (ofK (addressOfIndex ehs)) hsv) ∧
    ∀ k < q, LoadHolds rd (ofK (addressOfIndex epos)) k (eOfNat (qs k)) ∧
      LoadHolds rd (ofK (addressOfIndex eqp)) k (ofK (addressOfIndex (eb k))) ∧
      ∀ i < qwN (s.pd + cd) cd,
        LoadHolds rd (ofK (addressOfIndex (eb k))) i (gen ^ qwVal (s.pd + cd) cd (qs k) i)

/-- The queries' sum `level_queries` returns: `0` at the final level, else the chain of the
queries' folded rows by `1/λ`. -/
def lqSum (s : Oq) (odd N : ℕ) (lamInv : E) (rounds : List FoldRound) (qs : ℕ → ℕ)
    (rows : ℕ → List K) : E :=
  if s.final = 1 then 0 else
    oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N

end
end LeanVM.Guest.B1

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

end
end LeanVM.Guest.B1.Arm
