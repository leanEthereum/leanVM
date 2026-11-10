import Rv64Verifier.Proofs.Field.Contracts
import Rv64Verifier.Field.BaseMul

/-!
# The compiled `spread` and `reduce` of a square

`K::square` and `E::square` spread a word's two halves to the even bit positions of two words
(`lo16E`, `hi16E`, then `sprE`), and reduce the pair with an `|||` where `reduce` has `^^^`
(`sqReduceE`): the spread high word has no odd bits, so the two agree, and `hi >>> 63` is zero.
`sqE_eval`: the whole is `Model.kSquare`.
-/

namespace Rv64Verifier.Proofs.Field.Spread
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Field

def orE (a b : E) : E := .bin .or a b
def xorE (a b : E) : E := .bin .xor a b

/-- One step: `(y | y << k) & m`. -/
def stepE (y : E) (k m : Word) : E := BaseMul.andC (orE (BaseMul.sllC y k) y) m

/-- The low half, after the steps of 32 and 16. -/
def lo16E (x : E) : E :=
  BaseMul.andC (orE (BaseMul.sllC x 16) (BaseMul.srlC (BaseMul.sllC x 48) 48)) 0x0000ffff0000ffff

/-- The high half, after the steps of 32 and 16. -/
def hi16E (x : E) : E :=
  BaseMul.andC (orE (BaseMul.sllC (BaseMul.srlC x 32) 16) (BaseMul.srlC x 32)) 0x0000ffff0000ffff

/-- The low half as `E::square` computes it: `x & 0xffff` for `x << 48 >> 48`. -/
def lo16E' (x : E) : E :=
  BaseMul.andC (orE (BaseMul.sllC x 16) (BaseMul.andC x 0xffff)) 0x0000ffff0000ffff

/-- The steps of 8, 4 and 2. -/
def spr3E (y : E) : E :=
  stepE (stepE (stepE y 8 0x00ff00ff00ff00ff) 4 0x0f0f0f0f0f0f0f0f) 2 0x3333333333333333

/-- The step of 1 before its mask. -/
def pre1E (y : E) : E := orE (BaseMul.sllC y 1) y

/-- The steps of 8, 4, 2 and 1. -/
def sprE (y : E) : E := BaseMul.andC (pre1E (spr3E y)) 0x5555555555555555

/-- The compiled reduction of a spread pair. -/
def sqReduceE (hi lo : E) : E :=
  let v := xorE (orE (BaseMul.srlC hi 61) (BaseMul.srlC hi 60)) hi
  xorE (xorE (xorE (xorE lo (BaseMul.sllC v 1)) (BaseMul.sllC v 3)) (BaseMul.sllC v 4)) v

/-- `K::square` of `x`. -/
def sqE (x : E) : E := sqReduceE (sprE (hi16E x)) (sprE (lo16E x))

/-- `E::square`'s square of a limb. -/
def sqE' (x : E) : E := sqReduceE (sprE (hi16E x)) (sprE (lo16E' x))

/-- `E::square`'s reduction of the sum of two spread limbs: the sum before the last mask. -/
def sqSumE (x y : E) : E := sqReduceE
  (BaseMul.andC (xorE (pre1E (spr3E (hi16E x))) (pre1E (spr3E (hi16E y)))) 0x5555555555555555)
  (BaseMul.andC (xorE (pre1E (spr3E (lo16E' x))) (pre1E (spr3E (lo16E' y)))) 0x5555555555555555)

/-! ## Meaning -/

theorem spread_bit (a : BitVec 64) (k : Nat) : (Model.spread a).getLsbD k =
    (decide (k < 128) && decide (k % 2 = 0) && a.getLsbD (k / 2)) := by
  rw [Model.spread_spread a k]
  by_cases hk : k % 2 = 0
  · simp [hk]
  · simp [hk, show ¬ k % (2 * 1) < 1 by omega]

theorem sprE_lo (s : MachineState) (x : E) :
    (sprE (lo16E x)).eval s = (Model.spread (x.eval s)).extractLsb' 0 64 := by
  simp only [sprE, spr3E, pre1E, stepE, lo16E, orE, BaseMul.andC, BaseMul.srlC, BaseMul.sllC, E.eval,
    BinOp.eval]
  generalize x.eval s = v
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', spread_bit]
  interval_cases i <;> simp

theorem sprE_hi (s : MachineState) (x : E) :
    (sprE (hi16E x)).eval s = (Model.spread (x.eval s)).extractLsb' 64 64 := by
  simp only [sprE, spr3E, pre1E, stepE, hi16E, orE, BaseMul.andC, BaseMul.srlC, BaseMul.sllC, E.eval,
    BinOp.eval]
  generalize x.eval s = v
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', spread_bit]
  interval_cases i <;> simp

/-- A word with no odd bits: `|||` of its shifts by 61 and 60 is their `^^^`, and its shift by
63 is zero. -/
theorem even_shifts (h : BitVec 64) (hodd : ∀ j, j % 2 = 1 → h.getLsbD j = false) :
    (h >>> 61 ||| h >>> 60) = h >>> 63 ^^^ h >>> 61 ^^^ h >>> 60 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h61 : h[61] = false := by rw [← BitVec.getLsbD_eq_getElem]; exact hodd 61 rfl
  have h63 : h[63] = false := by rw [← BitVec.getLsbD_eq_getElem]; exact hodd 63 rfl
  interval_cases i <;> simp [h61, h63]

theorem sqReduceE_eval (s : MachineState) (hi lo : E)
    (hodd : ∀ j, j % 2 = 1 → (hi.eval s).getLsbD j = false) :
    (sqReduceE hi lo).eval s = Model.reduceWords (hi.eval s) (lo.eval s) := by
  simp only [sqReduceE, xorE, orE, BaseMul.srlC, BaseMul.sllC, E.eval, BinOp.eval,
    Model.reduceWords, BitVec.reduceToNat, Nat.reduceMod]
  rw [even_shifts _ hodd]
  simp only [BitVec.xor_assoc]
  ac_rfl

theorem sqE_eval (s : MachineState) (x : E) :
    (sqE x).eval s = Model.kSquare (x.eval s) := by
  rw [sqE, sqReduceE_eval, sprE_hi, sprE_lo]
  · rfl
  · intro j hj
    rw [sprE_hi, BitVec.getLsbD_extractLsb', spread_bit]
    simp [show ¬ (64 + j) % 2 = 0 by omega]

theorem lo16E'_eval (s : MachineState) (x : E) : (lo16E' x).eval s = (lo16E x).eval s := by
  simp only [lo16E', lo16E, orE, BaseMul.andC, BaseMul.srlC, BaseMul.sllC, E.eval, BinOp.eval]
  congr 2
  generalize x.eval s = v
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

theorem sprE_lo' (s : MachineState) (x : E) :
    (sprE (lo16E' x)).eval s = (Model.spread (x.eval s)).extractLsb' 0 64 := by
  rw [← sprE_lo s x]
  simp only [sprE, spr3E, pre1E, stepE, orE, BaseMul.andC, BaseMul.sllC, E.eval, BinOp.eval,
    lo16E'_eval]

theorem hi_odd (s : MachineState) (x : E) (j : Nat) (hj : j % 2 = 1) :
    ((sprE (hi16E x)).eval s).getLsbD j = false := by
  rw [sprE_hi, BitVec.getLsbD_extractLsb', spread_bit]
  simp [show ¬ (64 + j) % 2 = 0 by omega]

theorem sqE'_eval (s : MachineState) (x : E) :
    (sqE' x).eval s = Model.reduce128 (Model.spread (x.eval s)) := by
  rw [sqE', sqReduceE_eval _ _ _ (hi_odd s x), sprE_hi, sprE_lo']
  rfl

theorem and_xor (a b m : BitVec 64) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, Bool.and_xor_distrib_right]

theorem sqSumE_eval (s : MachineState) (x y : E) :
    (sqSumE x y).eval s =
      Model.reduce128 (Model.spread (x.eval s) ^^^ Model.spread (y.eval s)) := by
  have hsum (u : E → E) : (BaseMul.andC (xorE (pre1E (spr3E (u x))) (pre1E (spr3E (u y))))
      0x5555555555555555).eval s = (sprE (u x)).eval s ^^^ (sprE (u y)).eval s := by
    simp only [sprE, BaseMul.andC, xorE, E.eval, BinOp.eval, and_xor]
  rw [sqSumE, sqReduceE_eval _ _ _ ?odd]
  · rw [hsum hi16E, hsum lo16E', sprE_hi, sprE_hi, sprE_lo', sprE_lo', Model.reduce128,
      BitVec.extractLsb'_xor, BitVec.extractLsb'_xor]
  case odd =>
    intro j hj
    rw [hsum hi16E, BitVec.getLsbD_xor, hi_odd s x j hj, hi_odd s y j hj]
    rfl

end Rv64Verifier.Proofs.Field.Spread
