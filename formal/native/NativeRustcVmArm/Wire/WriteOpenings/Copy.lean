module

public import NativeRustcVmArm.Wire.WriteOpenings.Keep

/-!
# `write_openings`' leaf copies, both branches

A word a copy loaded and stored is the leaf's (`leaf_copied`); four words copied (`Geo.copy4`,
`b9`, `b32`) or one (`Geo.copy1`, `b12`, `b35`): the opening still begun, its leaf one chunk
longer. `lsl3`: `lsl #3`.
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)

public section

theorem toNat_take3 {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

theorem lsl3 (x : BitVec 64) : UnOp.apply (.ubfm 61 60) .W64 x = BitVec.ofNat 64 (8 * x.toNat) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take3, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

variable {R : Run}

/-- **A copied word**: word `t + u` of leaf `i`, at opening `j`'s leaf word `t + u`. -/
theorem leaf_copied (G : Geo R) {m : MachineData} (hfr : Frm R m) {i t u j : Nat}
    (hi : i < R.np) (ht : t + u < 64) {d : Mem 64}
    (h : WordAt d (R.oa (ob j + 8 + 8 * t) + BitVec.ofNat 64 (8 * u))
      (wordOf m.dmem (R.lv + BitVec.ofNat 64 (512 * i + 8 * t) + BitVec.ofNat 64 (8 * u)))) :
    WordAt d (R.oa (ob j + 8 + 8 * (t + u))) (R.lfw i (t + u)) := by
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add,
    show 512 * i + 8 * t + 8 * u = 512 * i + 8 * (t + u) by omega, lfw_at G hfr hi ht,
    show ob j + 8 + 8 * t + 8 * u = ob j + 8 + 8 * (t + u) by omega] at h
  exact h

/-- **Four leaf words copied**: opening `j` still begun, its leaf to word `t + 4`. -/
theorem Geo.copy4 (G : Geo R) {d d' : Mem 64} {j i t : Nat} (hj : j < R.nq) (ht : t + 4 ≤ 64)
    (hs : SameOutside d d' (InRange (R.oa (ob j + 8 + 8 * t)) 32)) (hb : Begun R j d)
    (hl : R.LeafPart d j i t) (w0 : WordAt d' (R.oa (ob j + 8 + 8 * (t + 0))) (R.lfw i (t + 0)))
    (w1 : WordAt d' (R.oa (ob j + 8 + 8 * (t + 1))) (R.lfw i (t + 1)))
    (w2 : WordAt d' (R.oa (ob j + 8 + 8 * (t + 2))) (R.lfw i (t + 2)))
    (w3 : WordAt d' (R.oa (ob j + 8 + 8 * (t + 3))) (R.lfw i (t + 3))) :
    Begun R j d' ∧ R.LeafPart d' j i (t + 4) := by
  have hob := ob_le (j := j) (by have := G.nq256; omega)
  have hon : ob j + 8 + 8 * t + 32 ≤ phaseBytes := by omega
  refine ⟨⟨G.done_keep hs hon (by omega) hb.1 (by omega),
    G.wordAt_keep hs hon hb.2 (by omega) (by omega)⟩, ?_⟩
  have l0 : R.LeafPart d' j i t := G.wordsAt_keep hs hon hl (by simp; omega) (by simp)
  exact leaf_succ (leaf_succ (leaf_succ (leaf_succ l0 w0) w1) w2) w3

/-- **One leaf word copied**: opening `j` still begun, its leaf to word `t + 1`. -/
theorem Geo.copy1 (G : Geo R) {d d' : Mem 64} {j i t : Nat} (hj : j < R.nq) (ht : t < 64)
    (hs : SameOutside d d' (InRange (R.oa (ob j + 8 + 8 * t)) 8)) (hb : Begun R j d)
    (hl : R.LeafPart d j i t) (w0 : WordAt d' (R.oa (ob j + 8 + 8 * (t + 0))) (R.lfw i (t + 0))) :
    Begun R j d' ∧ R.LeafPart d' j i (t + 1) := by
  have hob := ob_le (j := j) (by have := G.nq256; omega)
  have hon : ob j + 8 + 8 * t + 8 ≤ phaseBytes := by omega
  refine ⟨⟨G.done_keep hs hon (by omega) hb.1 (by omega),
    G.wordAt_keep hs hon hb.2 (by omega) (by omega)⟩, ?_⟩
  have l0 : R.LeafPart d' j i t := G.wordsAt_keep hs hon hl (by simp; omega) (by simp)
  exact leaf_succ l0 w0

end

end NativeRustcVmArm.Wire.WriteOpenings
