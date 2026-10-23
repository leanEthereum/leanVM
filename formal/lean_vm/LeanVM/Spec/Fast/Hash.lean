/-
  LeanVM.Spec.Fast.Hash

  BLAKE2s-256 as the compiled verifier runs it: the rotation on machine words and the block's
  words read from an array, each proved equal to the definition it replaces and swapped in for
  compilation by `@[csimp]`.
-/

module

public import LeanVM.Spec.Blake2s

/-!
# The compiled BLAKE2s

`Blake2s.rotr` rotates through `BitVec.rotateRight`, which compiles to arithmetic on `Nat`, and
`blockWords` reads the sixteen words of a block by indexing a list, `64` walks from its head.
`rotrWords` rotates on `UInt32` (`rotr_eq_rotrWords`) and `blockWordsArray` reads the block from
an array (`blockWords_eq_blockWordsArray`).

A `@[csimp]` lemma acts where code is compiled, and `mix`, `round`, `compress`, `absorb` and
`blake2sBytes` were compiled with the definitions above. Each is restated here, word for word,
so that it is compiled with the replacements, and the lemma equating it with its restatement
(`rfl`, or an induction for the recursive `absorb`) compiles `blake2sBytes` as the restatement
in every module that imports this one. The verifier (`LeanVM.Spec.Verifier`) does.
Nothing here transcribes a source.
-/

namespace LeanVM.Protocol.Verifier.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash

@[expose] public section

/-! ## The rotation and the block -/

/-- `Blake2s.rotr` on `UInt32`: right by `n % 32`, the bits shifted out coming back on top. -/
def rotrWords (x : UInt32) (n : ℕ) : UInt32 :=
  (x >>> (n % 32).toUInt32) ||| (x <<< (32 - n % 32).toUInt32)

/-- **The word rotation is `Blake2s.rotr`.** -/
@[csimp] theorem rotr_eq_rotrWords : @Blake2s.rotr = @rotrWords := by
  funext x n
  apply UInt32.toBitVec_inj.mp
  have hn : n % 32 < 32 := Nat.mod_lt _ (by omega)
  have hs : ((n % 32).toUInt32.toBitVec % 32).toNat = n % 32 := by
    rw [BitVec.toNat_umod, UInt32.toNat_toBitVec]; simp
  have ht : ((32 - n % 32).toUInt32.toBitVec % 32).toNat = (32 - n % 32) % 32 := by
    rw [BitVec.toNat_umod, UInt32.toNat_toBitVec]; simp
  simp only [Blake2s.rotr, rotrWords, UInt32.toBitVec_or, UInt32.toBitVec_shiftRight,
    UInt32.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', hs, ht,
    BitVec.rotateRight, BitVec.rotateRightAux]
  by_cases h0 : n % 32 = 0
  · simp [h0]
  · rw [Nat.mod_eq_of_lt (show 32 - n % 32 < 32 by omega)]

/-- `blockWords` reading the block from an array. -/
def blockWordsArray (block : List UInt8) : Vector UInt32 16 :=
  let bytes := block.toArray
  let b := fun i ↦ bytes.getD i 0
  #v[leWord (b 0) (b 1) (b 2) (b 3), leWord (b 4) (b 5) (b 6) (b 7),
     leWord (b 8) (b 9) (b 10) (b 11), leWord (b 12) (b 13) (b 14) (b 15),
     leWord (b 16) (b 17) (b 18) (b 19), leWord (b 20) (b 21) (b 22) (b 23),
     leWord (b 24) (b 25) (b 26) (b 27), leWord (b 28) (b 29) (b 30) (b 31),
     leWord (b 32) (b 33) (b 34) (b 35), leWord (b 36) (b 37) (b 38) (b 39),
     leWord (b 40) (b 41) (b 42) (b 43), leWord (b 44) (b 45) (b 46) (b 47),
     leWord (b 48) (b 49) (b 50) (b 51), leWord (b 52) (b 53) (b 54) (b 55),
     leWord (b 56) (b 57) (b 58) (b 59), leWord (b 60) (b 61) (b 62) (b 63)]

/-- **Reading the block from an array is `blockWords`.** -/
@[csimp] theorem blockWords_eq_blockWordsArray : @blockWords = @blockWordsArray := by
  funext block
  have h : ∀ i, block.toArray.getD i 0 = block.getD i 0 := fun i ↦ by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  simp only [blockWords, blockWordsArray, h]

/-! ## The compression and the hash, restated -/

/-- `Blake2s.mix`, restated. -/
def mixWords (v : Vector UInt32 16) (a b c d : Fin 16) (x y : UInt32) : Vector UInt32 16 :=
  let va := v[a] + v[b] + x
  let vd := Blake2s.rotr (v[d] ^^^ va) 16
  let vc := v[c] + vd
  let vb := Blake2s.rotr (v[b] ^^^ vc) 12
  let va := va + vb + y
  let vd := Blake2s.rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := Blake2s.rotr (vb ^^^ vc) 7
  (((v.set a va).set b vb).set c vc).set d vd

/-- `Blake2s.mix` compiles as its restatement. -/
@[csimp] theorem mix_eq_mixWords : @Blake2s.mix = @mixWords := rfl

/-- `Blake2s.round`, restated. -/
def roundWords (v m : Vector UInt32 16) (s : Vector (Fin 16) 16) : Vector UInt32 16 :=
  let v := Blake2s.mix v 0 4 8 12 m[s[0]] m[s[1]]
  let v := Blake2s.mix v 1 5 9 13 m[s[2]] m[s[3]]
  let v := Blake2s.mix v 2 6 10 14 m[s[4]] m[s[5]]
  let v := Blake2s.mix v 3 7 11 15 m[s[6]] m[s[7]]
  let v := Blake2s.mix v 0 5 10 15 m[s[8]] m[s[9]]
  let v := Blake2s.mix v 1 6 11 12 m[s[10]] m[s[11]]
  let v := Blake2s.mix v 2 7 8 13 m[s[12]] m[s[13]]
  Blake2s.mix v 3 4 9 14 m[s[14]] m[s[15]]

/-- `Blake2s.round` compiles as its restatement. -/
@[csimp] theorem round_eq_roundWords : @Blake2s.round = @roundWords := rfl

/-- `compress`, restated. -/
def compressWords (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Vector UInt32 8 :=
  let v := sigma.foldl (fun v s ↦ Blake2s.round v m s) (Blake2s.initialState h t f0 f1)
  #v[h[0] ^^^ v[0] ^^^ v[8], h[1] ^^^ v[1] ^^^ v[9], h[2] ^^^ v[2] ^^^ v[10],
     h[3] ^^^ v[3] ^^^ v[11], h[4] ^^^ v[4] ^^^ v[12], h[5] ^^^ v[5] ^^^ v[13],
     h[6] ^^^ v[6] ^^^ v[14], h[7] ^^^ v[7] ^^^ v[15]]

/-- `compress` compiles as its restatement. -/
@[csimp] theorem compress_eq_compressWords : @compress = @compressWords := rfl

/-- `absorb`, restated. -/
def absorbWords (h : Vector UInt32 8) (t : ℕ) : (blocks : ℕ) → List UInt8 → Digest
  | 0, data => compress h (blockWords data) (t + data.length).toUInt64 lastBlock 0
  | blocks + 1, data =>
    absorbWords (compress h (blockWords (data.take 64)) (t + 64).toUInt64 0 0) (t + 64) blocks
      (data.drop 64)

/-- `absorb` compiles as its restatement. -/
@[csimp] theorem absorb_eq_absorbWords : @absorb = @absorbWords := by
  funext h t blocks data
  induction blocks generalizing h t data with
  | zero => rfl
  | succ blocks ih => exact ih _ _ _

/-- `blake2sBytes`, restated. -/
def blake2sBytesWords (data : List UInt8) : Digest :=
  absorb paramIv 0 ((data.length - 1) / 64) data

/-- `blake2sBytes` compiles as its restatement. -/
@[csimp] theorem blake2sBytes_eq_blake2sBytesWords : @blake2sBytes = @blake2sBytesWords := rfl

end

end LeanVM.Protocol.Verifier.Fast
