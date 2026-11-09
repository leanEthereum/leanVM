/-
  LeanVM.Protocol.KeccakHash

  Lemmas about the byte encodings and the digest encoding of `Statement.RandomPermutation`.
-/

module

public import LeanVM.Semantics.Lemmas
public import LeanVM.Protocol.KeccakAbsorb
public import Statement.Field
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords

/-!
# Lemmas about the digest encoding

The hash and the digest encoding are defined in `Statement.RandomPermutation` and
`Statement.Field`, the Merkle node hash `hashPair` here. This module proves the round trips the
proofs use: a digest and its two field elements
(`digestOfScalars_digestScalars`, `digestScalars_digestOfScalars`), and the lengths and
injectivity of the byte encodings.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

namespace KeccakHash

/-- The digest of a Merkle node (`hash_pair`, `crates/verifier/src/merkle.rs:6-11`): Keccak-256 of
the 64 bytes of its two children, left first. -/
def hashPair (left right : Digest) : Digest := keccak256 (digestBytes left ++ digestBytes right)

/-! ## Bytes -/

theorem wordBytes_length (w : UInt64) : (wordBytes w).length = 8 := rfl

/-- A word is read back from its eight bytes. -/
theorem wordBytes_injective : Function.Injective wordBytes := by
  intro a b h
  simp only [wordBytes, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  apply UInt64.toNat_inj.mp
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  replace h0 := congrArg UInt8.toNat h0
  replace h1 := congrArg UInt8.toNat h1
  replace h2 := congrArg UInt8.toNat h2
  replace h3 := congrArg UInt8.toNat h3
  replace h4 := congrArg UInt8.toNat h4
  replace h5 := congrArg UInt8.toNat h5
  replace h6 := congrArg UInt8.toNat h6
  replace h7 := congrArg UInt8.toNat h7
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    Nat.mul_zero, Nat.mul_one] at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 ha hb
  omega

theorem digestBytes_length (d : Digest) : (digestBytes d).length = 32 := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [_, _, _, _], _ => rfl

theorem kBytes_length (a : K) : (K.toBytes a).length = 8 := rfl

/-- Digests are read back from their bytes. -/
theorem digestBytes_injective : Function.Injective digestBytes := by
  rintro ⟨⟨l⟩, hl⟩ ⟨⟨l'⟩, hl'⟩ h
  match l, hl, l', hl' with
  | [a0, a1, a2, a3], _, [b0, b1, b2, b3], _ =>
    simp only [digestBytes, Vector.toList_mk, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at h
    obtain ⟨e0, h⟩ := List.append_inj h (by rfl)
    obtain ⟨e1, h⟩ := List.append_inj h (by rfl)
    obtain ⟨e2, e3⟩ := List.append_inj h (by rfl)
    rw [wordBytes_injective e0, wordBytes_injective e1, wordBytes_injective e2,
      wordBytes_injective e3]

/-! ## The digest encoding -/

/-- Decoding the encoding of a digest gives the digest back. -/
theorem digestOfScalars_digestScalars (d : Digest) :
    digestFromHalves (digestHalves d) = some d := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [_, _, _, _], _ => simp [digestFromHalves, digestHalves, IsCanonical128, limb_ofLimbs]

/-- Encoding a decoded pair gives the pair back: the encoding is a bijection between digests and
pairs of canonical cells. -/
theorem digestScalars_digestOfScalars {s : E × E} {d : Digest}
    (h : digestFromHalves s = some d) : digestHalves d = s := by
  obtain ⟨a, b⟩ := s
  unfold digestFromHalves at h
  split at h
  · rename_i hc
    have ha : a.limb 2 = 0 := hc.1
    have hb : b.limb 2 = 0 := hc.2
    rw [Option.some.injEq] at h
    subst h
    simp only [digestHalves, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, K.ofLane_lane, Prod.mk.injEq]
    exact ⟨E.ext fun i ↦ by fin_cases i <;> simp [limb_ofLimbs, ha],
      E.ext fun i ↦ by fin_cases i <;> simp [limb_ofLimbs, hb]⟩
  · exact absurd h (by simp)

end KeccakHash

end
end LeanVM.Protocol
