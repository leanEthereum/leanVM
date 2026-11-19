module

public import NativeVm.Code.Phase6.Scr

/-!
# Phase 6's scratch layout

Every value phase 6 keeps has a fixed element of the scratch (`NativeVm.Code.P6.Scr`): the scalars
and arrays the layers write first (`LW`), then those that persist across the layers, the constant
tables (words as `EW.ofK`), and the long arrays over the `keccakBits` bit positions. `p6_omega`
unfolds them and runs `omega`.
-/

@[expose] public section

namespace NativeVm.Code.P6

/-! ## Scalars the layers write -/

/-- The running claim's value. -/
def eCV : Nat := 0
/-- The layer's challenge `s`. -/
def eS : Nat := 1
/-- `κ`. -/
def eKappa : Nat := 2
/-- `β`. -/
def eBeta : Nat := 3
/-- The layer's `projected`. -/
def eProj : Nat := 4
/-- The layer's `iota`. -/
def eIota : Nat := 5
/-- The sum of the claim's instance weights. -/
def eSumMu : Nat := 6
/-- A sumcheck's running claim. -/
def eSC : Nat := 7
/-- The claim's two segment weights (`eqKernel` of its point from `packBits`, entries `0`, `1`). -/
def eSegW : Nat := 8
/-- The word: the claim's instance weights' count. -/
def eMuN : Nat := 10
/-- The word: the claim's point's size. -/
def ePtN : Nat := 11
/-- The word: a sumcheck's round. -/
def eRK : Nat := 12
/-- The three values `t`. -/
def eT : Nat := 13
/-- A sumcheck round's message, at most four coefficients. -/
def eMsg : Nat := 16
/-- A sumcheck round's challenge. -/
def eCh : Nat := 20
/-- A value to match. -/
def eVal : Nat := 21
/-- The word: an `eqKernel` entry's coordinates. -/
def eKn : Nat := 22
/-- The word: where an `eqKernel` entry's coordinates start, from its base. -/
def eKd : Nat := 23
/-! ## Scalars that persist -/

/-- `committed`. -/
def eComm : Nat := 32
/-- The first claim's segment weights. -/
def eSegW1 : Nat := 33
/-- The word `packBits`. -/
def ePB : Nat := 35
/-- The word: the layer's step. -/
def eStep : Nat := 36
/-- The word: `KECCAK`'s point's size. -/
def eInstN : Nat := 37
/-- The word: `KECCAK`'s evaluations' count. -/
def eNV : Nat := 38
/-- The word: the coordinates of a claim's point from `packBits`. -/
def eSegN : Nat := 39
/-- The word: the first claim's instance weights' count. -/
def eMuFN : Nat := 40
/-! ## Arrays the layers write -/

/-- The claim's instance weights, at most `16`. -/
def eMu : Nat := 48
/-- The claim's point, at most `31` coordinates. -/
def ePt : Nat := 64
/-- The layer's bit-position point, `keccakLocalBits` coordinates. -/
def eLp : Nat := 96
/-- The product polynomial's `productBits` coefficients. -/
def eProd : Nat := 112
/-- The powers of `s`, `embedBits` of them. -/
def ePow : Nat := 160
/-- `multilinearEval`'s work area, `16`. -/
def eMleW : Nat := 184
/-! ## Arrays that persist -/

/-- The segment challenge. -/
def eSegPt : Nat := 200
/-- The lane challenges, `keccakLaneBits`. -/
def eLanePt : Nat := 201
/-- The instances' point `low`, `4` coordinates. -/
def eLow : Nat := 206
/-- An opening's slot point, `qkeccakSlotBits` coordinates. -/
def eSlot : Nat := 210
/-- `KECCAK`'s point, at most `tablePointCap` coordinates. -/
def eInst : Nat := 216
/-- `KECCAK`'s output lanes' evaluations, `25`. -/
def eOut : Nat := 248
/-- The lanes' equality weights, `32`. -/
def eLanes : Nat := 280
/-- The first claim's instance weights, at most `16`. -/
def eMuF : Nat := 312
/-! ## Tables (words) -/

/-- `KECCAK_RC`, `24`. -/
def eRC : Nat := 336
/-- Per lane, the position of its column `4` along, `25`. -/
def eA4 : Nat := 360
/-- Per lane, the position of its column `3` along, `25`. -/
def eA3 : Nat := 385
/-- Per lane, `64 · π(lane)`, `25`. -/
def ePi : Nat := 410
/-- Per lane, `ρ(lane)`, `25`. -/
def eRho : Nat := 435
/-- Per lane, `64 ·` the column one along, `25`. -/
def eC1 : Nat := 460
/-- Per lane, `64 ·` the column four along, `25`. -/
def eC4 : Nat := 485
/-- `RMFE_EMBED`, `16`. -/
def eEmbed : Nat := 510
/-- `RMFE_PROJECT`, `16`. -/
def eProject : Nat := 526
/-! ## Long arrays -/

/-- The claim's bit weights, `keccakBits`. -/
def eW : Nat := 1024
/-- The bit-position equality weights, `2^keccakLocalBits`. -/
def eEq : Nat := 2624
/-- The layer's new weights before the linear map. -/
def eW2 : Nat := 4672
/-- `linear_transpose`'s `g`. -/
def eG : Nat := 6272
/-- `linear_transpose`'s columns, `320`. -/
def eCol : Nat := 7872
/-- An opening's rows, column by column, `64 · 2^qkeccakSlotBits`. -/
def eRows : Nat := 8192
/-- The first claim's bit weights. -/
def eWF : Nat := 12288
/-- The slices, `kBits`. -/
def eSl : Nat := 13888
/-- An opening's slice weights, `64`. -/
def eOW : Nat := 13952

/-- The elements a layer writes. -/
def LW (i : Nat) : Prop := i < 32 ∨ (48 ≤ i ∧ i < 200) ∨ (1024 ≤ i ∧ i < 8192)

/-- Unfold the layout everywhere, then `omega`. -/
macro "p6_omega" : tactic => `(tactic| (
  (try simp only [eCV, eS, eKappa, eBeta, eProj, eIota, eSumMu, eSC, eSegW, eMuN, ePtN, eRK, eT, eMsg, eCh,
    eVal, eKn, eKd, eComm, eSegW1, ePB, eStep, eInstN, eNV, eSegN, eMuFN, eMu, ePt, eLp,
    eProd, ePow, eMleW, eSegPt, eLanePt, eLow, eSlot, eInst, eOut, eLanes, eMuF, eRC, eA4,
    eA3, ePi, eRho, eC1, eC4, eEmbed, eProject, eW, eEq, eW2, eG, eCol, eRows, eWF, eSl, eOW,
    scrN_val] at *) <;>
  omega))

/-- Unfold the layout in the goal, then `omega`: a discharger. -/
macro "p6_ne" : tactic => `(tactic| (
  (try simp only [eCV, eS, eKappa, eBeta, eProj, eIota, eSumMu, eSC, eSegW, eMuN, ePtN, eRK, eT, eMsg, eCh,
    eVal, eKn, eKd, eComm, eSegW1, ePB, eStep, eInstN, eNV, eSegN, eMuFN, eMu, ePt, eLp,
    eProd, ePow, eMleW, eSegPt, eLanePt, eLow, eSlot, eInst, eOut, eLanes, eMuF, eRC, eA4,
    eA3, ePi, eRho, eC1, eC4, eEmbed, eProject, eW, eEq, eW2, eG, eCol, eRows, eWF, eSl, eOW,
    scrN_val]) <;>
  omega))

end NativeVm.Code.P6
