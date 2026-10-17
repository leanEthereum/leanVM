import Sphincs.ForestCoverage
import Sphincs.H0Factor

/-! A tree's 26-bit field (`coordField`, the 26 digest bits of the tree) is a uniform mark: decoding is a bijection onto the marks (a tree leaf,
a WOTS key and a codeword index per subtree), so averages over uniform fields are averages over
uniform marks. -/

open ENNReal

namespace Sphincs.Concrete

theorem extract_val {v : FieldVal} (o len : Nat) :
    (((BitVec.ofFin v).extractLsb' o len).toFin).val = v.val / 2 ^ o % 2 ^ len := by
  rw [BitVec.val_toFin, BitVec.extractLsb'_toNat, BitVec.toNat_ofFin, Nat.shiftRight_eq_div_pow]

theorem decodeMark_super_val (v : FieldVal) : ((decodeMark v).super).val = v.val % 16 := by
  simp only [decodeMark]
  rw [extract_val]
  simp [topHeight]

theorem decodeMark_child_val (v : FieldVal) (j : SubIdx) :
    ((decodeMark v).child j).val = v.val / 2 ^ (4 + 11 * j.val) % 8 := by
  simp only [decodeMark]
  rw [extract_val]
  simp [fieldChildOffset, subHeight]

theorem decodeMark_word_val (v : FieldVal) (j : SubIdx) :
    ((decodeMark v).word j).val = v.val / 2 ^ (7 + 11 * j.val) % 256 := by
  simp only [decodeMark]
  rw [extract_val]
  simp [fieldWordOffset]

/-- The field of a mark. -/
def encodeMark (m : CoordMark) : FieldVal :=
  ⟨m.super.val + 16 * (m.child 0).val + 128 * (m.word 0).val + 32768 * (m.child 1).val +
      262144 * (m.word 1).val, by
    have h1 := m.super.isLt
    have h2 := (m.child 0).isLt
    have h3 := (m.word 0).isLt
    have h4 := (m.child 1).isLt
    have h5 := (m.word 1).isLt
    simp only [topHeight, subHeight, coordBits] at *
    norm_num at *
    omega⟩

/-- **Decoding is a bijection.** -/
def markEquiv : FieldVal ≃ CoordMark where
  toFun := decodeMark
  invFun := encodeMark
  left_inv v := by
    apply Fin.ext
    have hv := v.isLt
    simp only [coordBits] at hv
    simp only [encodeMark, decodeMark_super_val, decodeMark_child_val, decodeMark_word_val]
    norm_num
    omega
  right_inv m := by
    have h1 := m.super.isLt
    have h2 := (m.child 0).isLt
    have h3 := (m.word 0).isLt
    have h4 := (m.child 1).isLt
    have h5 := (m.word 1).isLt
    simp only [topHeight, subHeight] at h1 h2 h4
    norm_num at h1 h2 h4
    have hs : (decodeMark (encodeMark m)).super = m.super := by
      apply Fin.ext
      rw [decodeMark_super_val]
      simp only [encodeMark]
      omega
    have hc : (decodeMark (encodeMark m)).child = m.child := by
      funext j
      apply Fin.ext
      rw [decodeMark_child_val]
      fin_cases j <;> simp only [encodeMark] <;> norm_num <;> omega
    have hw : (decodeMark (encodeMark m)).word = m.word := by
      funext j
      apply Fin.ext
      rw [decodeMark_word_val]
      fin_cases j <;> simp only [encodeMark] <;> norm_num <;> omega
    cases hm : decodeMark (encodeMark m)
    cases m
    simp_all

end Sphincs.Concrete
