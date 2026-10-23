/-
  LeanVM.Spec.Fast.Da

  LeanDA's membership vector as the compiled node vectors compute it: the additive NTT restated,
  word for word, to be compiled with this project's field arithmetic, and swapped in by
  `@[csimp]`.
-/

module

public import LeanDa.Scheme
public import LeanVM.Spec.Field

/-!
# The compiled membership vector

`formal/lean_da` compiles `LeanDa.membershipVector` with CompPoly's arithmetic: a `@[csimp]` lemma
acts where code is compiled, so the word products of `LeanVM.Spec.Field` do not reach it there.
The NTT's butterflies and layers, the encoding, the dual codeword and the membership vector are
restated here word for word, each equal to its definition by `rfl`, so that every module importing
this one compiles `LeanDa.membershipVector` with them. Nothing here transcribes a source.
-/

namespace LeanVM.Da.Fast

open LeanVM.Parameters

@[expose] public section

/-- `LeanDa.butterfly`. -/
def butterfly (twiddle : K) (block : List E) : List E :=
  let top := block.take (block.length / 2)
  let bottom := block.drop (block.length / 2)
  let top := List.zipWith (fun u v ↦ u + v * CompPoly.Extension.Ext.ofBase twiddle) top bottom
  top ++ List.zipWith (· + ·) bottom top

/-- `LeanDa.encodeLayer`, with `butterfly`. -/
def encodeLayer (layer : ℕ) (codeword : List E) : List E :=
  let row := (LeanDa.subspaceEvaluations (LeanDa.logM - layer - 1)).drop 1
  let size := 2 ^ (LeanDa.logM - layer)
  (List.range (codeword.length / size)).flatMap fun b ↦
    let twiddle := ((List.range layer).filter b.testBit).foldl (fun t bit ↦ t + row.getD bit 0) 0
    butterfly twiddle ((codeword.drop (b * size)).take size)

/-- `LeanDa.encode`, with `encodeLayer`. -/
def encode (message : List E) : List E :=
  (List.range' 1 (LeanDa.logM - 1)).foldl (fun codeword layer ↦ encodeLayer layer codeword)
    (message ++ message)

/-- `LeanDa.dualCodeword`, with `encode`. -/
def dualCodeword (z : List E) : List E :=
  encode (z.foldl (fun t challenge ↦ t ++ t.map (· * challenge)) [1])

/-- `LeanDa.membershipVector`, with `dualCodeword`. -/
def membershipVector (H : List UInt8 → LeanDa.Digest) (root : LeanDa.Digest) : List E :=
  dualCodeword (LeanDa.membershipChallenges H root)

@[csimp] theorem butterfly_eq : @LeanDa.butterfly = @butterfly := rfl

@[csimp] theorem encodeLayer_eq : @LeanDa.encodeLayer = @encodeLayer := rfl

@[csimp] theorem encode_eq : @LeanDa.encode = @encode := rfl

@[csimp] theorem dualCodeword_eq : @LeanDa.dualCodeword = @dualCodeword := rfl

@[csimp] theorem membershipVector_eq : @LeanDa.membershipVector = @membershipVector := rfl

end
end LeanVM.Da.Fast
