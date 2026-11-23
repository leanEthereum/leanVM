module

public import NativeRustcVm.Arrays.Read
public import NativeRustcVm.Transcript.Rep
public import NativeVm.Model.Whir

/-!
# WHIR's working area in memory

The crate's `#[repr(C)]` structs of `whir.rs` (offsets: `offset_of!`) represent the model's values
(`NativeVm/Model/Whir.lean`):

| struct | bytes | fields | represents |
|---|---|---|---|
| `Level` | `24` | `fold` `0`, `log_inv_rate` `8`, `queries` `16` | `Whir.Level` (`LevelAt`) |
| `FoldRoundW` | `32` | `alpha` `0`, `beta` `16` | `FoldRoundW` (`RoundsAt`) |
| `Buf<FoldRoundW, 6>` | `200` | `len` `0`, `items` `8` | the level's rounds (`BufRoundsAt`) |
| `GluedClaimW` | `6064` | `scalar` `0`, `fold_start` `16`, `kind` `24`, `mu` `32`, `p: Buf<EW, 30>` `40`, `queries: Buf<u64, 230>` `528`, `weights: Buf<EW, 230>` `2376` | `GluedClaimW` (`GluedAt`) |
| `WhirStateW` | `61152` | `claim` `0`, `alphas: Buf<EW, 30>` `16`, `glued: Buf<GluedClaimW, 10>` `504` | `WhirStateW` (`WhirStateAt`) |
| `WhirW` | `63200` | `state` `0`, `rounds` `61152`, `queries: Buf<u64, 230>` `61352` | the state and the level's rounds (`WhirAt`) |
| `Buf<(u64, u64), 31>` | `504` | `len` `0`, `items` `8` | `subspaceTable μ` (`PairsAt`) |
| `ScalesW = Buf<EW, 162>` | `2600` | `len` `0`, `items` `8` | the batching scales |

A glued claim's `kind` is `0` for `eq p` (its `mu`, `queries`, `weights` unconstrained) and `1` for
`induced μ queries weights` (its `p` unconstrained), `μ ≤ 30` (the stack's variables). The entries
past a buffer's count are unconstrained.

`lanesOf index row` is `whirLevels`' `lanesOf`: level `0`'s row reversed, a later level's pairs.
-/

namespace NativeRustcVm.Whir

open NativeVm.Model LeanVM.Parameters
open NativeRustcVm.Transcript (off)

@[expose] public section

/-! ## Sizes -/

/-- `STACK_CAP`: the most fold rounds over the stack, a point on it. -/
def stackCap : Nat := 30
/-- `QUERY_CAP`: a level's query positions. -/
def queryCap : Nat := 230
/-- `GLUED_CAP`: two glued claims per non-final level. -/
def gluedCap : Nat := 10
/-- `ROUND_CAP`: a level's fold rounds. -/
def roundCap : Nat := 6
/-- `ROOT_CAP`: the roots of `subspaceRoots μ`, `μ ≤ 30`. -/
def rootCap : Nat := 31
/-- `LANE_CAP`: an opened row's lanes. -/
def laneCap : Nat := 64
/-- `STACK_CLAIM_CAP`: the stack claims. -/
def stackClaimCap : Nat := 162

/-- `Level`'s bytes. -/
def levelBytes : Nat := 24
/-- `FoldRoundW`'s bytes. -/
def roundBytes : Nat := 32
/-- `GluedClaimW`'s bytes. -/
def gluedBytes : Nat := 6064
/-- `WhirStateW`'s bytes. -/
def stateBytes : Nat := 61152
/-- `WhirW`'s bytes. -/
def whirBytes : Nat := 63200
/-- `Buf<u64, 230>`'s bytes. -/
def queryBufBytes : Nat := 8 + 8 * queryCap
/-- `Buf<(u64, u64), 31>`'s bytes. -/
def tableBytes : Nat := 8 + 16 * rootCap
/-- `Buf<u64, 31>`'s bytes. -/
def whatBytes : Nat := 8 + 8 * rootCap
/-- `ScalesW`'s bytes. -/
def scalesBytes : Nat := 8 + 16 * stackClaimCap
/-- `[EW; LANE_CAP]`'s bytes. -/
def lanesBytes : Nat := 16 * laneCap

/-- Offset of `WhirW.rounds`. -/
def roundsOff : Nat := 61152
/-- Offset of `WhirW.queries`. -/
def queriesOff : Nat := 61352
/-- Offset of `WhirStateW.alphas`. -/
def alphasOff : Nat := 16
/-- Offset of `WhirStateW.glued`. -/
def gluedOff : Nat := 504

theorem stateBytes_eq : stateBytes = gluedOff + 8 + gluedBytes * gluedCap := rfl
theorem whirBytes_eq : whirBytes = queriesOff + queryBufBytes := rfl
theorem roundsOff_eq : roundsOff + 8 + roundBytes * roundCap = queriesOff := rfl

/-! ## Values -/

/-- `whirLevels`' `lanesOf`: level `0`'s words reversed as `K` elements, a later level's pairs of
words. -/
def lanesOf (index : Nat) (row : Array UInt64) : Array EW :=
  if index = 0 then row.reverse.map EW.ofK else extRow row

/-- The words of `(u64, u64)` pairs, end to end. -/
def pairWords (ps : List (UInt64 × UInt64)) : List UInt64 := ps.flatMap fun p ↦ [p.1, p.2]

/-- The `n` pairs `(u64, u64)` from `a`. -/
def pairsOf (d : Mem 64) (a : BitVec 64) (n : Nat) : List (UInt64 × UInt64) :=
  (ewsOf d a n).map fun e ↦ (e.c0, e.c1)

/-- The `E` elements of fold rounds, `α` then `β`, end to end. -/
def roundEWs (rs : List FoldRoundW) : List EW := rs.flatMap fun r ↦ [r.alpha, r.beta]

/-- The `n` fold rounds from `a`. -/
def roundsOf (d : Mem 64) (a : BitVec 64) (n : Nat) : List FoldRoundW :=
  (List.range n).map fun i ↦
    ⟨ewOf d (a + BitVec.ofNat 64 (32 * i)), ewOf d (a + BitVec.ofNat 64 (32 * i + 16))⟩

/-! ## The structs -/

/-- **A level** at `p` (`Level`, 24 bytes): its fold, rate exponent and query count. -/
def LevelAt (d : Mem 64) (p : BitVec 64) (l : Whir.Level) : Prop :=
  l.fold < 2 ^ 64 ∧ l.logInvRate < 2 ^ 64 ∧ l.queries < 2 ^ 64 ∧
    WordsAt d p [l.fold.toUInt64, l.logInvRate.toUInt64, l.queries.toUInt64]

/-- The levels from `p` (a `&[Level]`). -/
def LevelsAt (d : Mem 64) (p : BitVec 64) (ls : List Whir.Level) : Prop :=
  ∀ i (h : i < ls.length), LevelAt d (off p (levelBytes * i)) ls[i]

/-- The pairs `(u64, u64)` from `p`, end to end. -/
def PairsAt (d : Mem 64) (p : BitVec 64) (ps : List (UInt64 × UInt64)) : Prop :=
  WordsAt d p (pairWords ps)

/-- The fold rounds from `p`, 32 bytes each. -/
def RoundsAt (d : Mem 64) (p : BitVec 64) (rs : List FoldRoundW) : Prop :=
  EWsAt d p (roundEWs rs)

/-- A `Buf<FoldRoundW, 6>` at `p` holding `rs`. -/
def BufRoundsAt (d : Mem 64) (p : BitVec 64) (rs : List FoldRoundW) : Prop :=
  rs.length ≤ roundCap ∧ WordAt d p rs.length.toUInt64 ∧ RoundsAt d (off p 8) rs

/-- A `Buf<(u64, u64), N>` at `p` holding `ps`. -/
def BufPairsAt (d : Mem 64) (p : BitVec 64) (N : Nat) (ps : List (UInt64 × UInt64)) : Prop :=
  ps.length ≤ N ∧ WordAt d p ps.length.toUInt64 ∧ PairsAt d (off p 8) ps

/-- A glued claim's weight at `p` (the `GluedClaimW` at `p`): `kind` `0` and `p`'s points, or
`kind` `1`, `μ ≤ 30`, the queries and their weights. -/
def GluedWeightAt (d : Mem 64) (p : BitVec 64) : GluedWeight → Prop
  | .eq z => WordAt d (off p 24) 0 ∧ BufEWAt d (off p 40) stackCap z.toList
  | .induced mu queries weights => WordAt d (off p 24) 1 ∧ mu ≤ stackCap ∧
      WordAt d (off p 32) mu.toUInt64 ∧ BufWordsAt d (off p 528) queryCap queries.toList ∧
      BufEWAt d (off p 2376) queryCap weights.toList

/-- **A glued claim** at `p` (`GluedClaimW`, 6064 bytes). -/
def GluedAt (d : Mem 64) (p : BitVec 64) (g : GluedClaimW) : Prop :=
  EWAt d p g.scalar ∧ g.foldStart < 2 ^ 64 ∧ WordAt d (off p 16) g.foldStart.toUInt64 ∧
    GluedWeightAt d p g.weight

/-- **WHIR's state** at `p` (`WhirStateW`, 61152 bytes): the claim, the `α`s (a `Buf<EW, 30>`),
the glued claims (a `Buf<GluedClaimW, 10>`, claim `i` at byte `512 + 6064 i`). -/
structure WhirStateAt (d : Mem 64) (p : BitVec 64) (s : WhirStateW) : Prop where
  claim : EWAt d p s.claim
  alphas : BufEWAt d (off p alphasOff) stackCap s.alphas.toList
  glued_le : s.glued.size ≤ gluedCap
  glued_len : WordAt d (off p gluedOff) s.glued.size.toUInt64
  glued : ∀ i (h : i < s.glued.size), GluedAt d (off p (gluedOff + 8 + gluedBytes * i)) s.glued[i]

/-- **The phase-7 state** at `w` (`WhirW`, 63200 bytes): WHIR's state and the current level's
fold rounds (its query buffer scratch). -/
def WhirAt (d : Mem 64) (w : BitVec 64) (s : WhirStateW) (rounds : Array FoldRoundW) : Prop :=
  WhirStateAt d w s ∧ BufRoundsAt d (off w roundsOff) rounds.toList

end

end NativeRustcVm.Whir
