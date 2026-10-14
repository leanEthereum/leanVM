import WhirAeneas.Generated.Portable.Primitives
import WhirAeneas.Hash.Interface

namespace WhirAeneas.Hash
open Aeneas Aeneas.Std

theorem scalar_tryMk_ofNatCore {ty : UScalarTy} (k : Nat) (h : k < 2 ^ ty.numBits) :
    UScalar.tryMk ty k = .ok (UScalar.ofNatCore k h) := by
  simp only [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, decide_eq_true_eq,
    h, _root_.dite_true, Result.ofOption]

theorem scalar_add_ofNatCore {ty : UScalarTy} (a b : Nat)
    (ha : a < 2 ^ ty.numBits) (hb : b < 2 ^ ty.numBits) (hab : a + b < 2 ^ ty.numBits) :
    UScalar.add (UScalar.ofNatCore a ha) (UScalar.ofNatCore b hb) =
      .ok (UScalar.ofNatCore (a + b) hab) := by
  simp only [UScalar.add, UScalar.ofNatCore_val_eq]
  exact scalar_tryMk_ofNatCore (a + b) hab

@[simp] theorem index_encodeMessage (words : Vector Word 16) (i : Usize) (hi : i.val < 16) :
    Aeneas.Std.Array.index_usize (encodeMessage words) i = .ok (⟨words[i.val]⟩ : U32) := by
  simp [Aeneas.Std.Array.index_usize, encodeMessage, hi]

@[simp] theorem update_encodeMessage (words : Vector Word 16) (i : Usize) (hi : i.val < 16) (word : Word) :
    Aeneas.Std.Array.update (encodeMessage words) i ⟨word⟩ =
      .ok (encodeMessage (words.set i.val word)) := by
  simp [Aeneas.Std.Array.update, encodeMessage, hi]
  congr 1
  simp [List.map_set, Vector.toList_set]

@[simp] theorem index_encodeState (words : Vector Word 8) (i : Usize) (hi : i.val < 8) :
    Aeneas.Std.Array.index_usize (encodeState words) i = .ok (⟨words[i.val]⟩ : U32) := by
  simp [Aeneas.Std.Array.index_usize, encodeState, hi]

@[simp] theorem update_encodeState (words : Vector Word 8) (i : Usize) (hi : i.val < 8) (word : Word) :
    Aeneas.Std.Array.update (encodeState words) i ⟨word⟩ =
      .ok (encodeState (words.set i.val word)) := by
  simp [Aeneas.Std.Array.update, encodeState, hi]
  congr 1
  simp [List.map_set, Vector.toList_set]

end WhirAeneas.Hash
