/-
  LeanVM.Protocol.Blake2sHash

  Lemmas about BLAKE2s-256 and the digest encoding of `LeanVM.Spec.Blake2s`.
-/

module

public import LeanVM.Semantics.Lemmas
public import LeanVM.Spec.Blake2s

/-!
# Lemmas about the BLAKE2s byte hasher and the digest encoding

The hasher, the Merkle hashes and the digest encoding are defined in `LeanVM.Spec.Blake2s`.
This module proves the round trips the proofs use: words and cells (`cellWords_wordsCell`), and a
digest and its two field elements (`digestOfScalars_digestScalars`,
`digestScalars_digestOfScalars`).
-/

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

namespace Blake2sHash

/-! ## Load-bearing lemmas -/

theorem lowWord_ofWords (lo hi : UInt32) : lowWord (ofWords lo hi) = lo := by
  apply UInt32.toBitVec_inj.mp
  simp only [lowWord, ofWords, UInt32.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]
  exact BitVec.extractLsb'_append_eq_right

theorem highWord_ofWords (lo hi : UInt32) : highWord (ofWords lo hi) = hi := by
  apply UInt32.toBitVec_inj.mp
  simp only [highWord, ofWords, UInt32.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]
  exact BitVec.extractLsb'_append_eq_left

/-- A four-word vector is the vector of its four words. -/
private theorem vector4_eta {α : Type} (v : Vector α 4) : #v[v[0], v[1], v[2], v[3]] = v := by
  ext i hi
  rcases i with _ | _ | _ | _ | i <;> first | rfl | omega

/-- Reading the words of the cell built from four words gives the words back. -/
theorem cellWords_wordsCell (w : Vector UInt32 4) : cellWords (wordsCell w) = w := by
  simp only [cellWords, wordsCell, limb_ofLimbs, lowWord_ofWords, highWord_ofWords,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact vector4_eta w

/-- The cell built from four words is canonical. -/
theorem isCanonical128_wordsCell (w : Vector UInt32 4) : IsCanonical128 (wordsCell w) := by
  show (E.ofLimbs _ _ 0).limb 2 = 0
  rw [limb_ofLimbs]; rfl

/-- Decoding the encoding of a digest gives the digest back. -/
theorem digestOfScalars_digestScalars (d : Digest) :
    digestOfScalars (digestScalars d) = some d := by
  simp only [digestOfScalars, digestScalars, isCanonical128_wordsCell, and_self, ↓reduceIte,
    cellWords_wordsCell, Option.some.injEq]
  ext i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | rfl | omega

/-- The first four words of the concatenation of two four-word vectors. -/
private theorem append_left4 {α : Type} (x y : Vector α 4) :
    #v[(x ++ y)[0], (x ++ y)[1], (x ++ y)[2], (x ++ y)[3]] = x := by
  rw [Vector.getElem_append_left (show 0 < 4 by decide),
    Vector.getElem_append_left (show 1 < 4 by decide),
    Vector.getElem_append_left (show 2 < 4 by decide),
    Vector.getElem_append_left (show 3 < 4 by decide)]
  exact vector4_eta x

/-- The last four words of the concatenation of two four-word vectors. -/
private theorem append_right4 {α : Type} (x y : Vector α 4) :
    #v[(x ++ y)[4], (x ++ y)[5], (x ++ y)[6], (x ++ y)[7]] = y := by
  rw [Vector.getElem_append_right (show 4 < 4 + 4 by decide) (show 4 ≤ 4 by decide),
    Vector.getElem_append_right (show 5 < 4 + 4 by decide) (show 4 ≤ 5 by decide),
    Vector.getElem_append_right (show 6 < 4 + 4 by decide) (show 4 ≤ 6 by decide),
    Vector.getElem_append_right (show 7 < 4 + 4 by decide) (show 4 ≤ 7 by decide)]
  exact vector4_eta y

/-- Encoding a decoded pair gives the pair back: the encoding is a bijection between digests and
pairs of canonical cells. -/
theorem digestScalars_digestOfScalars {s : E × E} {d : Digest}
    (h : digestOfScalars s = some d) : digestScalars d = s := by
  obtain ⟨a, b⟩ := s
  unfold digestOfScalars at h
  split at h
  · rename_i hc
    have ha : IsCanonical128 a := hc.1
    have hb : IsCanonical128 b := hc.2
    rw [Option.some.injEq] at h
    subst h
    show (wordsCell _, wordsCell _) = (a, b)
    rw [append_left4, append_right4, wordsCell_cellWords ha, wordsCell_cellWords hb]
  · exact absurd h (by simp)

end Blake2sHash

end
end LeanVM.Protocol
