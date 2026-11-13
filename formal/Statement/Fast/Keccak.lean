/-
  Statement.Fast.Keccak

  Keccak-f[1600] and Keccak-256 as the compiled verifier runs them: the rounds with their lanes
  written out as scalars, and a block's lanes read from an array, each proved equal to the
  definition it replaces and swapped in for compilation by `@[csimp]`.

  Speed only: `@[csimp]` lemmas, each proved, that change how the statement's definitions are
  compiled and nothing they mean. Not part of what a reviewer of `Statement/` must read.
-/

module

public import Statement.Keccak
public import Mathlib.Tactic.IntervalCases

/-!
# The compiled Keccak

`Keccak.round` (`Statement.Keccak`) is written as loops: θ's parities and its
mix as vectors built from functions, ρ and π as twenty-five writes into a zero state, χ as a
vector of index arithmetic. `roundLanes` is the same round with its twenty-five lanes written
out, the indices and rotations computed once (`round_eq_roundLanes`, lane by lane).
`KeccakHash.littleEndianLane` reads a block's bytes by indexing a list, a walk from its head per
byte;
`leLaneArray` reads them from an array (`leLane_eq_leLaneArray`).

A `@[csimp]` lemma acts where code is compiled, and `keccakF1600` and `keccak256` were compiled with
the definitions above. `keccakF1600` compiles as `keccakFScalar`: the twenty-four rounds of
`roundLanes` as one loop whose twenty-five lanes are scalars passed from round to round
(`keccakLoop`), so that it allocates the final state only, with `Keccak.rot` inlined
(`keccakF_eq_keccakFScalar`, from `keccakLoop_lanes`); and `keccak256`, Keccak-256 over
Keccak-f[1600] in `Id`, without the monad
and with the blocks read from arrays (`keccak256_eq_keccak256Blocks`); the lemma equating each
with its restatement compiles it as the restatement in every module that imports this one
(`Statement.Field` and `Statement.LeanDa` do, so the statement's own definitions and every module
of the repository compile them so). `keccak256With`, over any permutation in any monad, is
restated with the blocks read from arrays (`keccak256With_eq_keccak256WithArray`): the verifier,
the prover and the schemes hash with it, over Keccak-f[1600] when run. Nothing here transcribes
a source.
-/

namespace LeanVM.Fast.Keccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-! ## The round -/

/-- `Keccak.rot`, inlined: at a constant offset it compiles to two shifts. -/
@[inline] def rotInline (x : UInt64) (n : ℕ) : UInt64 :=
  if n = 0 then x else (x <<< n.toUInt64) ||| (x >>> (64 - n).toUInt64)

/-- `Keccak.rot` compiles inlined. -/
@[csimp] theorem rot_eq_rotInline : @Keccak.rot = @rotInline := rfl

/-- `Keccak.round`, its lanes written out: θ's column parities `c` and their mixes `d`, ρ and π
as the lane each `b` takes, then χ and ι. -/
def roundLanes (a : KeccakState) (rc : UInt64) : KeccakState :=
  let c0 := Keccak.lane a 0 ^^^ Keccak.lane a 5 ^^^ Keccak.lane a 10 ^^^
      Keccak.lane a 15 ^^^ Keccak.lane a 20
  let c1 := Keccak.lane a 1 ^^^ Keccak.lane a 6 ^^^ Keccak.lane a 11 ^^^
      Keccak.lane a 16 ^^^ Keccak.lane a 21
  let c2 := Keccak.lane a 2 ^^^ Keccak.lane a 7 ^^^ Keccak.lane a 12 ^^^
      Keccak.lane a 17 ^^^ Keccak.lane a 22
  let c3 := Keccak.lane a 3 ^^^ Keccak.lane a 8 ^^^ Keccak.lane a 13 ^^^
      Keccak.lane a 18 ^^^ Keccak.lane a 23
  let c4 := Keccak.lane a 4 ^^^ Keccak.lane a 9 ^^^ Keccak.lane a 14 ^^^
      Keccak.lane a 19 ^^^ Keccak.lane a 24
  let d0 := c4 ^^^ Keccak.rot c1 1
  let d1 := c0 ^^^ Keccak.rot c2 1
  let d2 := c1 ^^^ Keccak.rot c3 1
  let d3 := c2 ^^^ Keccak.rot c4 1
  let d4 := c3 ^^^ Keccak.rot c0 1
  let b0 := Keccak.rot (Keccak.lane a 0 ^^^ d0) 0
  let b1 := Keccak.rot (Keccak.lane a 6 ^^^ d1) 44
  let b2 := Keccak.rot (Keccak.lane a 12 ^^^ d2) 43
  let b3 := Keccak.rot (Keccak.lane a 18 ^^^ d3) 21
  let b4 := Keccak.rot (Keccak.lane a 24 ^^^ d4) 14
  let b5 := Keccak.rot (Keccak.lane a 3 ^^^ d3) 28
  let b6 := Keccak.rot (Keccak.lane a 9 ^^^ d4) 20
  let b7 := Keccak.rot (Keccak.lane a 10 ^^^ d0) 3
  let b8 := Keccak.rot (Keccak.lane a 16 ^^^ d1) 45
  let b9 := Keccak.rot (Keccak.lane a 22 ^^^ d2) 61
  let b10 := Keccak.rot (Keccak.lane a 1 ^^^ d1) 1
  let b11 := Keccak.rot (Keccak.lane a 7 ^^^ d2) 6
  let b12 := Keccak.rot (Keccak.lane a 13 ^^^ d3) 25
  let b13 := Keccak.rot (Keccak.lane a 19 ^^^ d4) 8
  let b14 := Keccak.rot (Keccak.lane a 20 ^^^ d0) 18
  let b15 := Keccak.rot (Keccak.lane a 4 ^^^ d4) 27
  let b16 := Keccak.rot (Keccak.lane a 5 ^^^ d0) 36
  let b17 := Keccak.rot (Keccak.lane a 11 ^^^ d1) 10
  let b18 := Keccak.rot (Keccak.lane a 17 ^^^ d2) 15
  let b19 := Keccak.rot (Keccak.lane a 23 ^^^ d3) 56
  let b20 := Keccak.rot (Keccak.lane a 2 ^^^ d2) 62
  let b21 := Keccak.rot (Keccak.lane a 8 ^^^ d3) 55
  let b22 := Keccak.rot (Keccak.lane a 14 ^^^ d4) 39
  let b23 := Keccak.rot (Keccak.lane a 15 ^^^ d0) 41
  let b24 := Keccak.rot (Keccak.lane a 21 ^^^ d1) 2
  #v[(b0 ^^^ (~~~ b1 &&& b2)) ^^^ rc,
    b1 ^^^ (~~~ b2 &&& b3),
    b2 ^^^ (~~~ b3 &&& b4),
    b3 ^^^ (~~~ b4 &&& b0),
    b4 ^^^ (~~~ b0 &&& b1),
    b5 ^^^ (~~~ b6 &&& b7),
    b6 ^^^ (~~~ b7 &&& b8),
    b7 ^^^ (~~~ b8 &&& b9),
    b8 ^^^ (~~~ b9 &&& b5),
    b9 ^^^ (~~~ b5 &&& b6),
    b10 ^^^ (~~~ b11 &&& b12),
    b11 ^^^ (~~~ b12 &&& b13),
    b12 ^^^ (~~~ b13 &&& b14),
    b13 ^^^ (~~~ b14 &&& b10),
    b14 ^^^ (~~~ b10 &&& b11),
    b15 ^^^ (~~~ b16 &&& b17),
    b16 ^^^ (~~~ b17 &&& b18),
    b17 ^^^ (~~~ b18 &&& b19),
    b18 ^^^ (~~~ b19 &&& b15),
    b19 ^^^ (~~~ b15 &&& b16),
    b20 ^^^ (~~~ b21 &&& b22),
    b21 ^^^ (~~~ b22 &&& b23),
    b22 ^^^ (~~~ b23 &&& b24),
    b23 ^^^ (~~~ b24 &&& b20),
    b24 ^^^ (~~~ b20 &&& b21)]

/-- Position `p` after writes `g i` at `π i` for each `i` of `l` in turn: the last write there, or
what was there. -/
private theorem getElem_foldl_setIfInBounds {α : Type} {n : ℕ} (π : ℕ → ℕ) (g : ℕ → α) :
    ∀ (l : List ℕ) (b : Vector α n) (p : ℕ) (hp : p < n),
      (l.foldl (fun b i ↦ b.setIfInBounds (π i) (g i)) b)[p] =
        ((l.reverse.find? (π · = p)).map g).getD b[p]
  | [], b, p, hp => by simp
  | i :: l, b, p, hp => by
    rw [List.foldl_cons, getElem_foldl_setIfInBounds π g l _ p hp, List.reverse_cons,
      List.find?_append]
    cases h : l.reverse.find? (π · = p) with
    | none => by_cases hi : π i = p <;> simp [hi]
    | some k => simp

/-- The lane ρ and π move to position `p`: `keccakPi (rhoPiSrc[p]) = p`. -/
private def rhoPiSrc : List ℕ :=
  [0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21]

private theorem find_keccakPi : ∀ p < 25,
    (List.range 25).reverse.find? (keccakPi · = p) = some (rhoPiSrc.getD p 0) := by decide

-- Lane by lane, ρ and π's twenty-five writes read through `getElem_foldl_setIfInBounds` rather
-- than unfolded.
/-- **The round with its lanes written out is `Keccak.round`.** -/
@[csimp] theorem round_eq_roundLanes : @Keccak.round = @roundLanes := by
  funext a rc
  apply Vector.ext
  intro j hj
  simp only [Keccak.round]
  interval_cases j <;> simp only [Keccak.lane, Array.getD_eq_getD_getElem?, Vector.size_toArray,
    Fin.is_lt, getElem?_pos, Vector.getElem_toArray, Option.getD_some, Vector.getElem?_toArray,
    UInt64.xor_assoc, Vector.toArray_ofFn, keccakRho, List.getD_eq_getElem?_getD,
    getElem_foldl_setIfInBounds, find_keccakPi, rhoPiSrc, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Option.map_some, Vector.getElem_replicate, Array.size_ofFn,
    Nat.ofNat_pos, Array.getElem_ofFn, List.getElem_cons_zero, Nat.mod_succ, Nat.lt_add_one,
    Nat.reduceLT, Nat.one_mod, Nat.one_lt_ofNat, Nat.zero_mod, tsub_self, List.getElem_cons_succ,
    Nat.reduceMod, Vector.getElem_setIfInBounds_self, roundLanes, Vector.getElem_mk,
    List.getElem_toArray, ne_eq, zero_ne_one, not_false_eq_true, Vector.getElem_setIfInBounds_ne,
    Vector.getElem_ofFn, OfNat.zero_ne_ofNat, Nat.mod_self, add_zero, tsub_zero,
    Nat.add_one_sub_one, Nat.reduceSub]

/-- `keccakF1600`, restated. -/
def keccakFLanes (a : KeccakState) : KeccakState := keccakRC.foldl Keccak.round a

/-- `keccakF1600` is its restatement. -/
theorem keccakF_eq_keccakFLanes : @keccakF1600 = @keccakFLanes := rfl

/-! ## The permutation on lanes held in scalars -/

/-- The round constants as an array. -/
def keccakRCArray : Array UInt64 := keccakRC.toArray

/-- Keccak-f[1600] from round `i` on, the state's lanes held in scalars: `roundLanes` with the
lane `k` read from `ak`, the next round's lanes passed on, so that the compiled loop allocates
only the final state. -/
def keccakLoop (i : ℕ)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
      a24 : UInt64) :
    KeccakState :=
  if i < 24 then
    let rc := keccakRCArray.getD i 0
    let c0 := a0 ^^^ a5 ^^^ a10 ^^^ a15 ^^^ a20
    let c1 := a1 ^^^ a6 ^^^ a11 ^^^ a16 ^^^ a21
    let c2 := a2 ^^^ a7 ^^^ a12 ^^^ a17 ^^^ a22
    let c3 := a3 ^^^ a8 ^^^ a13 ^^^ a18 ^^^ a23
    let c4 := a4 ^^^ a9 ^^^ a14 ^^^ a19 ^^^ a24
    let d0 := c4 ^^^ Keccak.rot c1 1
    let d1 := c0 ^^^ Keccak.rot c2 1
    let d2 := c1 ^^^ Keccak.rot c3 1
    let d3 := c2 ^^^ Keccak.rot c4 1
    let d4 := c3 ^^^ Keccak.rot c0 1
    let b0 := Keccak.rot (a0 ^^^ d0) 0
    let b1 := Keccak.rot (a6 ^^^ d1) 44
    let b2 := Keccak.rot (a12 ^^^ d2) 43
    let b3 := Keccak.rot (a18 ^^^ d3) 21
    let b4 := Keccak.rot (a24 ^^^ d4) 14
    let b5 := Keccak.rot (a3 ^^^ d3) 28
    let b6 := Keccak.rot (a9 ^^^ d4) 20
    let b7 := Keccak.rot (a10 ^^^ d0) 3
    let b8 := Keccak.rot (a16 ^^^ d1) 45
    let b9 := Keccak.rot (a22 ^^^ d2) 61
    let b10 := Keccak.rot (a1 ^^^ d1) 1
    let b11 := Keccak.rot (a7 ^^^ d2) 6
    let b12 := Keccak.rot (a13 ^^^ d3) 25
    let b13 := Keccak.rot (a19 ^^^ d4) 8
    let b14 := Keccak.rot (a20 ^^^ d0) 18
    let b15 := Keccak.rot (a4 ^^^ d4) 27
    let b16 := Keccak.rot (a5 ^^^ d0) 36
    let b17 := Keccak.rot (a11 ^^^ d1) 10
    let b18 := Keccak.rot (a17 ^^^ d2) 15
    let b19 := Keccak.rot (a23 ^^^ d3) 56
    let b20 := Keccak.rot (a2 ^^^ d2) 62
    let b21 := Keccak.rot (a8 ^^^ d3) 55
    let b22 := Keccak.rot (a14 ^^^ d4) 39
    let b23 := Keccak.rot (a15 ^^^ d0) 41
    let b24 := Keccak.rot (a21 ^^^ d1) 2
    keccakLoop (i + 1)
      ((b0 ^^^ (~~~ b1 &&& b2)) ^^^ rc)
      (b1 ^^^ (~~~ b2 &&& b3))
      (b2 ^^^ (~~~ b3 &&& b4))
      (b3 ^^^ (~~~ b4 &&& b0))
      (b4 ^^^ (~~~ b0 &&& b1))
      (b5 ^^^ (~~~ b6 &&& b7))
      (b6 ^^^ (~~~ b7 &&& b8))
      (b7 ^^^ (~~~ b8 &&& b9))
      (b8 ^^^ (~~~ b9 &&& b5))
      (b9 ^^^ (~~~ b5 &&& b6))
      (b10 ^^^ (~~~ b11 &&& b12))
      (b11 ^^^ (~~~ b12 &&& b13))
      (b12 ^^^ (~~~ b13 &&& b14))
      (b13 ^^^ (~~~ b14 &&& b10))
      (b14 ^^^ (~~~ b10 &&& b11))
      (b15 ^^^ (~~~ b16 &&& b17))
      (b16 ^^^ (~~~ b17 &&& b18))
      (b17 ^^^ (~~~ b18 &&& b19))
      (b18 ^^^ (~~~ b19 &&& b15))
      (b19 ^^^ (~~~ b15 &&& b16))
      (b20 ^^^ (~~~ b21 &&& b22))
      (b21 ^^^ (~~~ b22 &&& b23))
      (b22 ^^^ (~~~ b23 &&& b24))
      (b23 ^^^ (~~~ b24 &&& b20))
      (b24 ^^^ (~~~ b20 &&& b21))
  else #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21, a22, a23, a24]
termination_by 24 - i

/-- The loop from round `i` on a state's lanes is the rounds from `i` on. -/
theorem keccakLoop_lanes (i : ℕ) (a : KeccakState) :
    keccakLoop i
      (Keccak.lane a 0) (Keccak.lane a 1) (Keccak.lane a 2) (Keccak.lane a 3) (Keccak.lane a 4)
      (Keccak.lane a 5) (Keccak.lane a 6) (Keccak.lane a 7) (Keccak.lane a 8) (Keccak.lane a 9)
      (Keccak.lane a 10) (Keccak.lane a 11) (Keccak.lane a 12) (Keccak.lane a 13)
      (Keccak.lane a 14) (Keccak.lane a 15) (Keccak.lane a 16) (Keccak.lane a 17)
      (Keccak.lane a 18) (Keccak.lane a 19) (Keccak.lane a 20) (Keccak.lane a 21)
      (Keccak.lane a 22) (Keccak.lane a 23) (Keccak.lane a 24) =
      (keccakRC.drop i).foldl roundLanes a := by
  rw [keccakLoop]
  split
  · rename_i h
    have hd : keccakRC.drop i = keccakRC.getD i 0 :: keccakRC.drop (i + 1) := by
      have hi : i < keccakRC.length := by simpa [keccakRC] using h
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.drop_eq_getElem_cons hi
    have hrc : keccakRCArray.getD i 0 = keccakRC.getD i 0 := by
      simp [keccakRCArray, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    rw [hd, List.foldl_cons, ← keccakLoop_lanes (i + 1) (roundLanes a (keccakRC.getD i 0)), hrc]
    rfl
  · rename_i h
    have : keccakRC.drop i = [] := List.drop_eq_nil_of_le (by simp [keccakRC]; omega)
    rw [this, List.foldl_nil]
    apply Vector.ext
    intro j hj
    interval_cases j <;> simp [Keccak.lane, Array.getD_eq_getD_getElem?]
termination_by 24 - i

/-- Keccak-f[1600] on scalars. -/
def keccakFScalar (a : KeccakState) : KeccakState :=
  keccakLoop 0
    (Keccak.lane a 0) (Keccak.lane a 1) (Keccak.lane a 2) (Keccak.lane a 3) (Keccak.lane a 4)
    (Keccak.lane a 5) (Keccak.lane a 6) (Keccak.lane a 7) (Keccak.lane a 8) (Keccak.lane a 9)
    (Keccak.lane a 10) (Keccak.lane a 11) (Keccak.lane a 12) (Keccak.lane a 13) (Keccak.lane a 14)
    (Keccak.lane a 15) (Keccak.lane a 16) (Keccak.lane a 17) (Keccak.lane a 18) (Keccak.lane a 19)
    (Keccak.lane a 20) (Keccak.lane a 21) (Keccak.lane a 22) (Keccak.lane a 23) (Keccak.lane a 24)

/-- **Keccak-f[1600] on scalars is `keccakF1600`**, and compiles in its place: the compiled
permutation allocates its final state only. -/
@[csimp] theorem keccakF_eq_keccakFScalar : @keccakF1600 = @keccakFScalar := by
  funext a
  rw [keccakFScalar, keccakLoop_lanes, List.drop_zero, keccakF1600, round_eq_roundLanes]

/-! ## The blocks and the hash -/

/-- `littleEndianLane` reading the bytes from an array. -/
def leLaneArray (bytes : Array UInt8) (i : ℕ) : UInt64 :=
  (List.range 8).foldl
    (fun acc k ↦ acc ||| ((bytes.getD (8 * i + k) 0).toUInt64 <<< (8 * k).toUInt64)) 0

/-- **Reading a lane from the bytes as an array is `littleEndianLane`.** -/
theorem leLane_eq_leLaneArray (bytes : List UInt8) (i : ℕ) :
    littleEndianLane bytes i = leLaneArray bytes.toArray i := by
  have h : ∀ j, bytes.toArray.getD j 0 = bytes.getD j 0 := fun j ↦ by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  simp only [littleEndianLane, leLaneArray, h]

/-- Absorbing one block with Keccak-f[1600], the block read from an array. -/
def absorbBlockArray (state : KeccakState) (block : List UInt8) : KeccakState :=
  let bytes := block.toArray
  keccakF1600 (Vector.ofFn fun i ↦
    if i.val < 17 then Keccak.lane state i ^^^ leLaneArray bytes i else Keccak.lane state i)

/-- `absorbWith` with Keccak-f[1600], without the monad. -/
def absorbBlocks : (blocks : ℕ) → KeccakState → List UInt8 → KeccakState
  | 0, state, data => absorbBlockArray state (padBlock data)
  | blocks + 1, state, data =>
    absorbBlocks blocks (absorbBlockArray state (data.take rate)) (data.drop rate)

/-- `keccak256`, without the monad. -/
def keccak256Blocks (data : List UInt8) : Digest :=
  let state := absorbBlocks (data.length / rate) (Vector.replicate 25 0) data
  #v[Keccak.lane state 0, Keccak.lane state 1, Keccak.lane state 2, Keccak.lane state 3]

/-- `absorbWith` over Keccak-f[1600] in `Id` is `absorbBlocks`. -/
theorem absorbWith_eq_absorbBlocks : ∀ (blocks : ℕ) (state : KeccakState) (data : List UInt8),
    absorbWith (m := Id) (fun s ↦ pure (keccakF1600 s)) blocks state data =
      absorbBlocks blocks state data
  | 0, state, data => by
    simp only [absorbWith, absorbBlockWith, absorbBlocks, absorbBlockArray, leLane_eq_leLaneArray]
    rfl
  | blocks + 1, state, data => by
    simp only [absorbWith, absorbBlocks]
    rw [← absorbWith_eq_absorbBlocks blocks]
    simp only [absorbBlockWith, absorbBlockArray, leLane_eq_leLaneArray]
    rfl

/-- Keccak-256 over a function in `Id`. -/
theorem keccak256With_id (f : KeccakState → KeccakState) (data : List UInt8) :
    keccak256With (m := Id) (fun s ↦ pure (f s)) data =
      pure ((fun state : KeccakState ↦
        #v[Keccak.lane state 0, Keccak.lane state 1, Keccak.lane state 2, Keccak.lane state 3])
        (absorbWith (m := Id) (fun s ↦ pure (f s)) (data.length / rate) (Vector.replicate 25 0)
          data)) :=
  rfl

/-- `keccak256` compiles as `keccak256Blocks`. -/
@[csimp] theorem keccak256_eq_keccak256Blocks : @keccak256 = @keccak256Blocks := by
  funext data
  rw [keccak256, keccak256With_id, absorbWith_eq_absorbBlocks]
  rfl

/-! ## Keccak-256 over any permutation -/

section With

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- `absorbBlockWith`, the block read from an array. -/
def absorbBlockWithArray (state : KeccakState) (block : List UInt8) : m KeccakState :=
  let bytes := block.toArray
  π (Vector.ofFn fun i ↦
    if i.val < 17 then Keccak.lane state i ^^^ leLaneArray bytes i else Keccak.lane state i)

/-- `absorbWith`, with `absorbBlockWithArray`. -/
def absorbWithArray : (blocks : ℕ) → KeccakState → List UInt8 → m KeccakState
  | 0, state, data => absorbBlockWithArray π state (padBlock data)
  | blocks + 1, state, data => do
    let state ← absorbBlockWithArray π state (data.take rate)
    absorbWithArray blocks state (data.drop rate)

/-- `keccak256With`, with `absorbWithArray`. -/
def keccak256WithArray (data : List UInt8) : m Digest := do
  let state ← absorbWithArray π (data.length / rate) (Vector.replicate 25 0) data
  pure #v[Keccak.lane state 0, Keccak.lane state 1, Keccak.lane state 2, Keccak.lane state 3]

/-- `absorbWith` is `absorbWithArray`. -/
theorem absorbWith_eq_absorbWithArray : ∀ (blocks : ℕ) (state : KeccakState) (data : List UInt8),
    absorbWith π blocks state data = absorbWithArray π blocks state data
  | 0, state, data => by
    simp only [absorbWith, absorbWithArray, absorbBlockWith, absorbBlockWithArray,
      leLane_eq_leLaneArray]
  | blocks + 1, state, data => by
    simp only [absorbWith, absorbWithArray, absorbBlockWith, absorbBlockWithArray,
      leLane_eq_leLaneArray, absorbWith_eq_absorbWithArray blocks]

end With

/-- `keccak256With` compiles as `keccak256WithArray`, over every permutation in every monad. -/
@[csimp] theorem keccak256With_eq_keccak256WithArray :
    @keccak256With = @keccak256WithArray := by
  funext m _ π data
  simp only [keccak256With, keccak256WithArray, absorbWith_eq_absorbWithArray]


end

end LeanVM.Fast.Keccak
