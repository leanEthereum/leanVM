import Sphincs.Uniform
import Mathlib.Data.BitVec

/-!
The full view of a 234-bit message digest (its index and the 26-bit field of each of the 8 trees)
is a bijection, so a uniform digest gives a uniform view. The 26 bits of a tree lie in three places
of the digest (its two codeword indices among the first 16 bytes, its leaf, its two WOTS keys);
`coordField` gathers them. A field decodes to the tree's mark: the
leaf of the tree, and for each of the two subtrees the WOTS key and the codeword index. Coverage of a
view by disclosed fields: every chain of both WOTS keys of every tree is disclosed at or below the
position the view needs.
-/

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000
set_option exponentiation.threshold 512

namespace Sphincs.Concrete

/-- The 26 bits of one tree's field. -/
abbrev FieldVal := Fin (2 ^ coordBits)

abbrev FullDigestView := Index × (Coord → FieldVal)

/-- Offset of subtree `j`'s WOTS-key bits within a field. -/
def fieldChildOffset (j : SubIdx) : Nat := 4 + 11 * j.val

/-- Offset of subtree `j`'s codeword bits within a field. -/
def fieldWordOffset (j : SubIdx) : Nat := 7 + 11 * j.val

/-- The field of tree `c` of a digest: its 26 bits, gathered from the three places of the digest that
hold them. From the low bits: the leaf (4 bits), then for subtree 0 and for subtree 1 the WOTS key
(3 bits) and the codeword index (8 bits). -/
def coordField (digest : MessageDigest) (c : Coord) : FieldVal :=
  (digest.extractLsb' (wordOffset c 1) 8 ++ digest.extractLsb' (childOffset c 1) 3 ++
    digest.extractLsb' (wordOffset c 0) 8 ++ digest.extractLsb' (childOffset c 0) 3 ++
    digest.extractLsb' (superOffset c) 4 : BitVec 26).toFin

def fullDigestView (digest : MessageDigest) : FullDigestView :=
  (digestIndex digest, coordField digest)

/-- The five parts of a field. -/
theorem field_parts (w1 : BitVec 8) (c1 : BitVec 3) (w0 : BitVec 8) (c0 : BitVec 3) (s : BitVec 4) :
    (w1 ++ c1 ++ w0 ++ c0 ++ s : BitVec 26).extractLsb' 0 4 = s ∧
    (w1 ++ c1 ++ w0 ++ c0 ++ s : BitVec 26).extractLsb' 4 3 = c0 ∧
    (w1 ++ c1 ++ w0 ++ c0 ++ s : BitVec 26).extractLsb' 7 8 = w0 ∧
    (w1 ++ c1 ++ w0 ++ c0 ++ s : BitVec 26).extractLsb' 15 3 = c1 ∧
    (w1 ++ c1 ++ w0 ++ c0 ++ s : BitVec 26).extractLsb' 18 8 = w1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hk, decide_true, Bool.true_and]
    repeat' split
    all_goals first
      | omega
      | (congr 1; omega)

/-- A field determines its five parts. -/
theorem field_inj {w1 w1' : BitVec 8} {c1 c1' : BitVec 3} {w0 w0' : BitVec 8} {c0 c0' : BitVec 3}
    {s s' : BitVec 4}
    (h : (w1 ++ c1 ++ w0 ++ c0 ++ s : BitVec 26) = (w1' ++ c1' ++ w0' ++ c0' ++ s' : BitVec 26)) :
    s = s' ∧ c0 = c0' ∧ w0 = w0' ∧ c1 = c1' ∧ w1 = w1' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := field_parts w1 c1 w0 c0 s
  obtain ⟨h1', h2', h3', h4', h5'⟩ := field_parts w1' c1' w0' c0' s'
  exact ⟨by rw [← h1, h, h1'], by rw [← h2, h, h2'], by rw [← h3, h, h3'], by rw [← h4, h, h4'],
    by rw [← h5, h, h5']⟩

/-- Two digests with the same bits in a window agree at every position of the window. -/
theorem getLsbD_of_extract {left right : MessageDigest} {offset len position : Nat}
    (h : left.extractLsb' offset len = right.extractLsb' offset len)
    (hlow : offset ≤ position) (hhigh : position < offset + len) :
    left.getLsbD position = right.getLsbD position := by
  have hwithin : position - offset < len := by omega
  have hbit := congrArg (fun bits : BitVec len => bits.getLsbD (position - offset)) h
  simp only [BitVec.getLsbD_extractLsb', hwithin, decide_true, Bool.true_and] at hbit
  rwa [show offset + (position - offset) = position by omega] at hbit

/-- The index and the 8 fields hold every bit of the digest: bits 0 to 127 are the 16 codeword
indices, 128 to 153 the index, 154 to 185 the 8 tree leaves and 186 to 233 the 16 WOTS keys. -/
theorem fullDigestView_injective : Function.Injective fullDigestView := by
  intro left right heq
  have hidx : left.extractLsb' indexOffset totalHeight = right.extractLsb' indexOffset totalHeight := by
    have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin view.1) heq
    simpa only [fullDigestView, digestIndex, BitVec.ofFin_toFin] using hcomponent
  have hfield : ∀ c : Coord,
      left.extractLsb' (superOffset c) 4 = right.extractLsb' (superOffset c) 4 ∧
      (∀ j : SubIdx, left.extractLsb' (childOffset c j) 3 = right.extractLsb' (childOffset c j) 3) ∧
      (∀ j : SubIdx, left.extractLsb' (wordOffset c j) 8 = right.extractLsb' (wordOffset c j) 8) := by
    intro c
    have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin (view.2 c)) heq
    simp only [fullDigestView, coordField, BitVec.ofFin_toFin] at hcomponent
    obtain ⟨hs, hc0, hw0, hc1, hw1⟩ := field_inj hcomponent
    exact ⟨hs, Fin.forall_fin_two.2 ⟨hc0, hc1⟩, Fin.forall_fin_two.2 ⟨hw0, hw1⟩⟩
  apply BitVec.eq_of_getLsbD_eq
  intro position hposition
  have hposition' : position < 234 := hposition
  by_cases hword : position < 128
  · let c : Coord := ⟨position / 16, by simp only [forestCoords]; omega⟩
    let j : SubIdx := ⟨position / 8 % 2, by omega⟩
    refine getLsbD_of_extract ((hfield c).2.2 j) ?_ ?_ <;>
    · simp only [wordOffset, c, j]
      omega
  · by_cases hindex : position < 154
    · refine getLsbD_of_extract hidx ?_ ?_ <;>
      · simp only [indexOffset, totalHeight]
        omega
    · by_cases hsuper : position < 186
      · let c : Coord := ⟨(position - 154) / 4, by simp only [forestCoords]; omega⟩
        refine getLsbD_of_extract (hfield c).1 ?_ ?_ <;>
        · simp only [superOffset, c]
          omega
      · let c : Coord := ⟨(position - 186) / 6, by simp only [forestCoords]; omega⟩
        let j : SubIdx := ⟨(position - 186) / 3 % 2, by omega⟩
        refine getLsbD_of_extract ((hfield c).2.1 j) ?_ ?_ <;>
        · simp only [childOffset, c, j]
          omega

theorem fullDigestView_bijective : Function.Bijective fullDigestView := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fullDigestView_injective, ?_⟩
  rw [card_bitVec, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, ← pow_add]
  rfl

theorem evalDist_fullDigestView_uniform :
    𝒟[fullDigestView <$> ($ᵗ MessageDigest : ProbComp MessageDigest)] =
    𝒟[($ᵗ FullDigestView : ProbComp FullDigestView)] :=
  evalDist_map_bijective_uniform_cross (α := MessageDigest) (β := FullDigestView)
    fullDigestView fullDigestView_bijective

/-! ### Decoding a field -/

/-- The mark of a tree read from its field. -/
def decodeMark (v : FieldVal) : CoordMark where
  super := ((BitVec.ofFin v).extractLsb' 0 topHeight).toFin
  child := fun j => ((BitVec.ofFin v).extractLsb' (fieldChildOffset j) subHeight).toFin
  word := fun j => ((BitVec.ofFin v).extractLsb' (fieldWordOffset j) 8).toFin

/-- The marks the verifier reads are the decoded fields. -/
theorem digestMarks_eq (digest : MessageDigest) (c : Coord) :
    digestMarks digest c = decodeMark (coordField digest c) := by
  obtain ⟨hs, hc0, hw0, hc1, hw1⟩ := field_parts (digest.extractLsb' (wordOffset c 1) 8)
    (digest.extractLsb' (childOffset c 1) 3) (digest.extractLsb' (wordOffset c 0) 8)
    (digest.extractLsb' (childOffset c 0) 3) (digest.extractLsb' (superOffset c) 4)
  simp only [digestMarks, decodeMark, coordField, BitVec.ofFin_toFin]
  congr 1
  · exact congrArg BitVec.toFin hs.symm
  · funext j
    revert j
    rw [Fin.forall_fin_two]
    exact ⟨congrArg BitVec.toFin hc0.symm, congrArg BitVec.toFin hc1.symm⟩
  · funext j
    revert j
    rw [Fin.forall_fin_two]
    exact ⟨congrArg BitVec.toFin hw0.symm, congrArg BitVec.toFin hw1.symm⟩

/-! ### Coverage -/

/-- The deficit `d_i` that target field `t` needs at chain `i` of subtree `j`: the verifier starts
at position `4 - d_i`. -/
def chainNeed (t : FieldVal) (j : SubIdx) (i : FChain) : Nat := (lut ((decodeMark t).word j) i).val

/-- A disclosed field `v` opens the WOTS key that target field `t` needs in subtree `j`, at chain
`i`, at or below the position `t` needs. -/
def KeyCovers (v t : FieldVal) (j : SubIdx) (i : FChain) : Prop :=
  (decodeMark v).super = (decodeMark t).super ∧ (decodeMark v).child j = (decodeMark t).child j ∧
    chainNeed t j i ≤ chainNeed v j i

instance (v t : FieldVal) (j : SubIdx) (i : FChain) : Decidable (KeyCovers v t j i) := by
  unfold KeyCovers; infer_instance

/-- The revealed positions of every forest chain. -/
abbrev Disclosures := Index → Coord → SuperIdx → SubIdx → ChildIdx → FChain → Finset FPos

/-- Chain `i` of the WOTS key that the view selects in tree `c`, subtree `j`, needs only the public
top, or has a revealed position at or below the one the view needs. -/
def ChainCov (revealed : Disclosures) (view : FullDigestView) (c : Coord) (j : SubIdx) (i : FChain) : Prop :=
  chainNeed (view.2 c) j i = 0 ∨
    ∃ p ∈ revealed view.1 c (decodeMark (view.2 c)).super j ((decodeMark (view.2 c)).child j) i,
      p.val ≤ chainTop - chainNeed (view.2 c) j i

instance (revealed : Disclosures) (view : FullDigestView) (c : Coord) (j : SubIdx) (i : FChain) :
    Decidable (ChainCov revealed view c j i) := by
  unfold ChainCov; infer_instance

/-- Every chain of both WOTS keys of every tree that the view selects is covered. -/
def Covered (revealed : Disclosures) (view : FullDigestView) : Prop :=
  ∀ (c : Coord) (j : SubIdx) (i : FChain), ChainCov revealed view c j i

instance (revealed : Disclosures) : DecidablePred (Covered revealed) := fun view => by
  unfold Covered; infer_instance

end Sphincs.Concrete
