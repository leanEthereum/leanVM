module

public import LeanVMCircuits.Adder

@[expose] public section

/-! Little-endian GF(2) bit vectors read as machine words, and the word operations BLAKE2s builds from bits. -/

namespace LeanVMCircuits.Blake2s

/-- The word whose bit `i` is `bits[i]`. -/
def toWord {n : ℕ} (bits : Vector Bit n) : BitVec n := BitVec.ofNat n (Adder.value bits)

/-- Bitwise XOR, the sum in GF(2). -/
def xorBits {α : Type} [Add α] {n : ℕ} (x y : Vector α n) : Vector α n := Vector.zipWith (· + ·) x y

/-- Rotation right by `r`: output bit `i` is input bit `(i + r) mod n`. -/
def rotr {α : Type} {n : ℕ} [NeZero n] (x : Vector α n) (r : ℕ) : Vector α n :=
  Vector.ofFn fun i => x[(i.val + r) % n]'(Nat.mod_lt _ (Nat.pos_of_neZero n))

/-- The bits of a literal word. -/
def literal {F : Type} [Zero F] [One F] {n : ℕ} (k : BitVec n) : Vector F n :=
  Vector.ofFn fun i => if k.getLsbD i then 1 else 0

theorem bit_cases (b : Bit) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem testBit_value {n : ℕ} (bits : Vector Bit n) (i : ℕ) :
    (Adder.value bits).testBit i = if h : i < n then decide (bits[i] = 1) else false := by
  induction bits using Vector.induct generalizing i with
  | nil => simp [Adder.value]
  | @cons n head tail ih =>
    simp only [Adder.value, Vector.toList_listCons, List.foldr_cons] at ih ⊢
    have hhead := ZMod.val_lt head
    cases i with
    | zero =>
      rcases bit_cases head with h | h <;> subst h <;> first | (simp [Nat.testBit_zero]; done) | (simp [Nat.testBit_zero]; rfl)
    | succ i =>
      have hdiv : (head.val + 2 * List.foldr (fun b acc => b.val + 2 * acc) 0 tail.toList) / 2 =
          List.foldr (fun b acc => b.val + 2 * acc) 0 tail.toList := by omega
      rw [Nat.testBit_succ, hdiv, ih]
      simp only [Nat.add_lt_add_iff_right]
      split <;> simp_all [Vector.getElem_listCons_succ]

theorem getLsbD_toWord {n : ℕ} (bits : Vector Bit n) (i : ℕ) :
    (toWord bits).getLsbD i = if h : i < n then decide (bits[i] = 1) else false := by
  rw [toWord, BitVec.getLsbD_ofNat, testBit_value]
  split <;> simp_all

theorem toWord_ext {n : ℕ} {x : Vector Bit n} {w : BitVec n}
    (h : ∀ i (hi : i < n), (x[i] = 1) ↔ w.getLsbD i = true) : toWord x = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_toWord, dif_pos hi]
  exact Bool.eq_iff_iff.mpr (by simpa using h i hi)

theorem toWord_xor {n : ℕ} (x y : Vector Bit n) : toWord (xorBits x y) = toWord x ^^^ toWord y := by
  apply toWord_ext
  intro i hi
  simp only [xorBits, Vector.getElem_zipWith, BitVec.getLsbD_xor, getLsbD_toWord, dif_pos hi]
  rcases bit_cases x[i] with hx | hx <;> rcases bit_cases y[i] with hy | hy <;> simp [hx, hy]

theorem toWord_rotr {n : ℕ} [NeZero n] (x : Vector Bit n) (r : ℕ) (hr : r < n) :
    toWord (rotr x r) = (toWord x).rotateRight r := by
  apply toWord_ext
  intro i hi
  simp only [rotr, Vector.getElem_ofFn, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hr]
  by_cases hlt : i < n - r
  · simp only [hlt, decide_true, cond_true, getLsbD_toWord, dif_pos (show r + i < n by omega)]
    have : (i + r) % n = r + i := by rw [Nat.mod_eq_of_lt (by omega), Nat.add_comm]
    simp [this]
  · have : (i + r) % n = i - (n - r) := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    simp only [hlt, decide_false, cond_false, getLsbD_toWord, dif_pos (show i - (n - r) < n by omega),
      decide_eq_true hi, Bool.true_and]
    simp [this]

theorem toWord_literal {n : ℕ} (k : BitVec n) : toWord (literal k : Vector Bit n) = k := by
  apply toWord_ext
  intro i hi
  simp only [literal, Vector.getElem_ofFn]
  split <;> simp_all

theorem toWord_add {n : ℕ} (x y s : Vector Bit n)
    (h : Adder.value s = (Adder.value x + Adder.value y) % 2 ^ n) : toWord s = toWord x + toWord y := by
  simp only [toWord, h, BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

end LeanVMCircuits.Blake2s
