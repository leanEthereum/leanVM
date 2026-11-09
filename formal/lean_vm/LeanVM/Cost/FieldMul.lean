module

public import Statement.CostMachine
public import Statement.Fast.FieldWords

/-!
# The product in `GF(2^64)` on the machine

The cost machine (`Statement.CostMachine`, v2) has no field product: a `K` element is the natural
number of its lane, and its product is compiled code on the machine's natural-number primitives.
This module gives that code and proves it:

* `carryless_eq`: the machine's carry-less product (`carrylessMultiply`, the verifier's
  `carryless`) on two words is CompPoly's `carryLessMul (w := 128)` (the product `BF64.mul`
  reduces), and below `2^127` (`carryless_lt_two_pow_127`);
* `mulKNat a b`: the product of the elements of lanes `a`, `b`, a straight line of primitives,
  and `mulKNat_eq`: it is `(a * b).lane.toNat`, below `2^64` (`mulKNat_lt`);
* `mulKTerm i j`: `mulKNat` as a machine term on the environment's positions `i`, `j`, and
  `evaluateTerm_mulKTerm` (on natural numbers) and `evaluateTerm_mulKTerm_encode` (on encoded
  `K` elements): its value and **a price of at most `21`**.

**The reduction** is Barrett's, whose constant `⌊x^128 / P⌋` is the modulus
`P = x^64 + x^4 + x^3 + x + 1` itself (`0x1000000000000001B`, since `x^128 = (x^64 + T)·P + T²`
with `T = x^4 + x^3 + x + 1`): with `p = a·b`, `q = ⌊⌊p / x^64⌋·P / x^64⌋` is the exact quotient
and `p + q·P` the remainder, below `x^64` without a mask (`mulKNat_eq_folds`: it equals the two
folds of `BF64.reduce`).

**The price**, as `evaluateTerm` charges: six primitives at `2` each (three carry-less products,
each with a factor or a result of two limbs; two shifts right and one `xor` reading the two-limb
product), eight reads at `1` (`a`, `b`, `p` twice, the literals `64` and `P` twice each) and one
`let` at `1`: `12 + 8 + 1 = 21`, exactly `21` when `a·b` has degree at least `64`, at least `17`
otherwise. The alternatives considered, priced the same way on the worst inputs:

* the two folds by `0x1B` (`let p := a·b; let s := ⌊p / x^64⌋·0x1B;
  ((p ^^^ s) &&& (2^64 - 1)) ^^^ ⌊s / x^64⌋·0x1B`): `27`;
* `FieldWords`' shift reduction (`tailLow`, `tailHigh`) on natural numbers with one final mask:
  `60`;
* Barrett with `q = ⌊p·P / x^128⌋` (one shift, but a two-by-two-limb carry-less product at `4`):
  `21`, no better.

Squaring has no cheaper form on this machine (`carryless a a` is priced as any product, and a
bit-spreading square needs many more operations): a square is `mulKNat a a`.
-/

namespace LeanVM.Cost

open LeanVM.Parameters LeanVM.Protocol.Verifier BF64 BinaryField

@[expose] public section

/-! ## The carry-less product -/

/-- The sum of `b·x^i` over the bits `i < n` of `a`: CompPoly's `carryLessMul`, and the
verifier's `carryless` with its factors swapped. -/
def carrylessFold (a b n : ℕ) : ℕ :=
  (List.range n).foldl (fun acc i ↦ if a.testBit i then acc ^^^ (b <<< i) else acc) 0

/-- Bits of `a` from `k` on, all clear, add nothing. -/
theorem carrylessFold_add (a b k m : ℕ) (h : ∀ i, k ≤ i → a.testBit i = false) :
    carrylessFold a b (k + m) = carrylessFold a b k := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← Nat.add_assoc, carrylessFold, List.range_succ, List.foldl_append, ← carrylessFold, ih]
    simp [h (k + m) (by omega)]

/-- The fold over more bits, all clear from `k` on, is the fold over `k` bits. -/
theorem carrylessFold_eq_of_le (a b k n : ℕ) (hk : k ≤ n)
    (h : ∀ i, k ≤ i → a.testBit i = false) : carrylessFold a b n = carrylessFold a b k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact carrylessFold_add a b k m h

/-- Any number of bits covering `a` gives the same fold. -/
theorem carrylessFold_congr (a b : ℕ) {n m : ℕ} (hn : a < 2 ^ n) (hm : a < 2 ^ m) :
    carrylessFold a b n = carrylessFold a b m := by
  have hk : a < 2 ^ min n m := by
    rcases Nat.le_total n m with h | h
    · rwa [Nat.min_eq_left h]
    · rwa [Nat.min_eq_right h]
  have hbits : ∀ i, min n m ≤ i → a.testBit i = false := fun i hi ↦
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) hi))
  exact (carrylessFold_eq_of_le a b _ n (Nat.min_le_left n m) hbits).trans
    (carrylessFold_eq_of_le a b _ m (Nat.min_le_right n m) hbits).symm

/-- A fold of `xor`s from `c` is `c` `xor` the fold from `0`. -/
theorem foldl_ite_xor (l : List ℕ) (p : ℕ → Bool) (x : ℕ → ℕ) (c : ℕ) :
    l.foldl (fun acc i ↦ if p i then acc ^^^ x i else acc) c =
      c ^^^ l.foldl (fun acc i ↦ if p i then acc ^^^ x i else acc) 0 := by
  induction l generalizing c with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons]
    split
    · rw [ih, ih (0 ^^^ x i), Nat.zero_xor, Nat.xor_assoc]
    · rw [ih, ih 0]

/-- The fold from the low bit of `a`. -/
theorem carrylessFold_succ (a b n : ℕ) :
    carrylessFold a b (n + 1) =
      (if a.testBit 0 then b else 0) ^^^ carrylessFold (a >>> 1) (b <<< 1) n := by
  rw [carrylessFold, List.range_succ_eq_map, List.foldl_cons, List.foldl_map, foldl_ite_xor,
    carrylessFold]
  congr 1
  · split <;> simp
  · congr 1
    funext acc i
    simp only [Nat.testBit_shiftRight, ← Nat.shiftLeft_add, Nat.add_comm 1 i, Nat.succ_eq_add_one]

/-- The verifier's loop is the fold over the bits of its second factor. -/
theorem carrylessAux_eq (fuel a b out : ℕ) (hb : b < 2 ^ fuel) :
    carrylessAux fuel a b out = out ^^^ carrylessFold b a fuel := by
  induction fuel generalizing a b out with
  | zero =>
    have : b = 0 := by simpa using hb
    subst this
    simp [carrylessAux, carrylessFold]
  | succ fuel ih =>
    rw [carrylessAux]
    by_cases h0 : b = 0
    · subst h0
      rw [ite_eq_left rfl, carrylessFold_congr 0 a (n := fuel + 1) (m := 0) hb (by norm_num)]
      simp [carrylessFold]
    · rw [ite_eq_right h0, ih _ _ _ (by
        rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_succ]
        exact hb), carrylessFold_succ, Nat.testBit_zero]
      by_cases h1 : b % 2 = 1
      · simp [h1, Nat.xor_assoc]
      · simp [h1]

/-- **`carryless a b` is the fold over the bits below `n` of `b`**, for any `n` with
`b < 2^n`. -/
theorem carryless_eq_fold (a : ℕ) {b n : ℕ} (hb : b < 2 ^ n) :
    carryless a b = carrylessFold b a n := by
  rw [carryless, carrylessAux_eq b a b 0 Nat.lt_two_pow_self, Nat.zero_xor]
  exact carrylessFold_congr b a Nat.lt_two_pow_self hb

/-- The fold's partial results stay below `2^(n + m - 1)`. -/
theorem carrylessFold_lt {a b n m : ℕ} (hb : b < 2 ^ m) (k : ℕ) (hk : k ≤ n) :
    carrylessFold a b k < 2 ^ (n + m - 1) := by
  induction k with
  | zero => simp [carrylessFold]
  | succ k ih =>
    rw [carrylessFold, List.range_succ, List.foldl_append, ← carrylessFold]
    simp only [List.foldl_cons, List.foldl_nil]
    split
    · refine Nat.xor_lt_two_pow (ih (by omega)) ?_
      rw [Nat.shiftLeft_eq]
      calc b * 2 ^ k < 2 ^ m * 2 ^ k := Nat.mul_lt_mul_of_pos_right hb (by positivity)
        _ = 2 ^ (m + k) := (Nat.pow_add 2 m k).symm
        _ ≤ 2 ^ (n + m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact ih (by omega)

/-- **The carry-less product's bound**: of factors below `2^n` and `2^m`, below
`2^(n + m - 1)`. -/
theorem carryless_lt {a b n m : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ m) :
    carryless a b < 2 ^ (n + m - 1) := by
  rw [carryless_eq_fold a hb, Nat.add_comm n m]
  exact carrylessFold_lt ha m le_rfl

/-- CompPoly's fold, on `BitVec 128`, has the value of `carrylessFold`. -/
theorem toNat_foldl_carryLessMul (a b : BitVec 64) (n : ℕ) (hn : n ≤ 64) :
    (Fin.foldl n (fun (acc : BitVec 128) (i : Fin n) ↦
      if a.getLsbD i then acc ^^^ (zeroExtendTo b <<< (i : ℕ)) else acc) 0).toNat =
      carrylessFold a.toNat b.toNat n := by
  induction n with
  | zero => simp [carrylessFold]
  | succ n ih =>
    rw [Fin.foldl_succ_last, carrylessFold, List.range_succ, List.foldl_append, ← carrylessFold]
    simp only [Fin.val_last, Fin.val_castSucc, List.foldl_cons, List.foldl_nil,
      BitVec.testBit_toNat]
    split
    · rw [BitVec.toNat_xor, ih (by omega), BitVec.toNat_shiftLeft,
        toNat_zeroExtendTo _ (by omega)]
      congr 1
      refine Nat.mod_eq_of_lt ?_
      rw [Nat.shiftLeft_eq]
      calc b.toNat * 2 ^ n < 2 ^ 64 * 2 ^ n := Nat.mul_lt_mul_of_pos_right b.isLt (by positivity)
        _ = 2 ^ (64 + n) := (Nat.pow_add 2 64 n).symm
        _ ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact ih (by omega)

/-- CompPoly's `carryLessMul (w := 128)` on words is commutative. -/
theorem carryLessMul_comm (a b : BitVec 64) :
    carryLessMul (w := 128) a b = carryLessMul (w := 128) b a := by
  apply bitVec_toPoly_injective
  rw [toPoly_carryLessMul _ _ (by omega), toPoly_carryLessMul _ _ (by omega), mul_comm]

/-- **The machine's carry-less product is CompPoly's** `carryLessMul (w := 128)` on words (the
product `BF64.mul` reduces). -/
theorem carryless_eq (a b : UInt64) :
    carryless a.toNat b.toNat = (carryLessMul (w := 128) a.toBitVec b.toBitVec).toNat := by
  rw [carryless_eq_fold a.toNat b.toNat_lt, carryLessMul_comm, carryLessMul]
  exact (toNat_foldl_carryLessMul b.toBitVec a.toBitVec 64 le_rfl).symm

/-- The carry-less product of two words is below `2^127`. -/
theorem carryless_lt_two_pow_127 (a b : UInt64) : carryless a.toNat b.toNat < 2 ^ 127 :=
  carryless_lt (n := 64) (m := 64) a.toNat_lt b.toNat_lt

/-! ## The product by the modulus -/

/-- The product by `x^4 + x^3 + x + 1` (`0x1B`), as shifts. -/
def timesTail (x : ℕ) : ℕ := x ^^^ x <<< 1 ^^^ x <<< 3 ^^^ x <<< 4

/-- **The product by the modulus `x^64 + x^4 + x^3 + x + 1`** (`0x1000000000000001B`). -/
theorem carryless_modulus (x : ℕ) :
    carryless x 0x1000000000000001B = timesTail x ^^^ x <<< 64 := by
  rw [carryless_eq_fold x (n := 65) (by norm_num), carrylessFold]
  simp [List.range_succ, timesTail, Nat.testBit]

/-- `timesTail` distributes over `xor`. -/
theorem timesTail_xor (x y : ℕ) : timesTail (x ^^^ y) = timesTail x ^^^ timesTail y := by
  simp only [timesTail, Nat.shiftLeft_xor_distrib]
  ac_rfl

/-- `timesTail` widens by four bits. -/
theorem timesTail_lt {x n : ℕ} (hx : x < 2 ^ n) : timesTail x < 2 ^ (n + 4) := by
  have hs : ∀ k ≤ 4, x <<< k < 2 ^ (n + 4) := fun k hk ↦ by
    rw [Nat.shiftLeft_eq]
    calc x * 2 ^ k < 2 ^ n * 2 ^ k := Nat.mul_lt_mul_of_pos_right hx (by positivity)
      _ = 2 ^ (n + k) := (Nat.pow_add 2 n k).symm
      _ ≤ 2 ^ (n + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h0 : x < 2 ^ (n + 4) := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h0 (hs 1 (by omega)))
    (hs 3 (by omega))) (hs 4 (by omega))

/-- A natural number is its high part shifted back, `xor` its low part. -/
theorem eq_shiftLeft_xor_mod (n k : ℕ) : n = (n >>> k) <<< k ^^^ n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_mod_two_pow]
  by_cases h : k ≤ i
  · simp [h, Nat.add_sub_cancel' h, show ¬ i < k by omega]
  · simp [h, show i < k by omega]

/-- A natural number is its high part shifted back, `or` its low part. -/
theorem eq_shiftLeft_or_mod (n k : ℕ) : n = (n >>> k) <<< k ||| n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_mod_two_pow]
  by_cases h : k ≤ i
  · simp [h, Nat.add_sub_cancel' h, show ¬ i < k by omega]
  · simp [h, show i < k by omega]

/-! ## The product in `GF(2^64)` -/

/-- **The product in `GF(2^64)` on the machine's natural numbers**: the lanes `a`, `b` of two
elements (both below `2^64`) give the lane of their product (`mulKNat_eq`). Barrett's reduction,
whose constant `⌊x^128 / P⌋` is the modulus `P = x^64 + x^4 + x^3 + x + 1` itself
(`0x1000000000000001B`): the carry-less product `p`, the quotient `q = ⌊⌊p / x^64⌋ · P / x^64⌋`,
and the remainder `p + q · P`, below `x^64` without a mask. -/
def mulKNat (a b : ℕ) : ℕ :=
  let p := carryless a b
  let h := p >>> 64
  let t := carryless h 0x1000000000000001B
  let q := t >>> 64
  let u := carryless q 0x1000000000000001B
  p ^^^ u

/-- `mulKNat` is the two folds of `reduceWords` on natural numbers. -/
theorem mulKNat_eq_folds (a b : ℕ) :
    mulKNat a b = carryless a b % 2 ^ 64 ^^^ timesTail (carryless a b >>> 64) % 2 ^ 64
      ^^^ timesTail (timesTail (carryless a b >>> 64) >>> 64) := by
  simp only [mulKNat, carryless_modulus]
  generalize carryless a b = p
  have hp := eq_shiftLeft_xor_mod p 64
  have ht := eq_shiftLeft_xor_mod (timesTail (p >>> 64)) 64
  rw [Nat.shiftRight_xor_distrib, Nat.shiftLeft_shiftRight, timesTail_xor,
    Nat.shiftLeft_xor_distrib]
  generalize p >>> 64 = h at *
  generalize timesTail h >>> 64 = g at *
  generalize timesTail h = th at *
  generalize timesTail g = tg at *
  generalize p % 2 ^ 64 = l at *
  generalize th % 2 ^ 64 = m at *
  subst hp ht
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases (h <<< 64).testBit i <;> cases (g <<< 64).testBit i <;> cases l.testBit i <;>
    cases m.testBit i <;> cases tg.testBit i <;> rfl

/-- `tailLow` on natural numbers. -/
theorem toNat_tailLow (w : UInt64) : (tailLow w).toNat = timesTail w.toNat % 2 ^ 64 := by
  simp only [tailLow, timesTail, UInt64.toNat_xor, UInt64.toNat_shiftLeft, Nat.xor_mod_two_pow,
    Nat.mod_eq_of_lt w.toNat_lt]
  rfl

/-- `tailHigh` on natural numbers. -/
theorem toNat_tailHigh (w : UInt64) : (tailHigh w).toNat = timesTail w.toNat >>> 64 := by
  have hw := w.toNat_lt
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [tailHigh, timesTail, UInt64.toNat_xor, UInt64.toNat_shiftRight, Nat.testBit_xor,
    Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  rw [Nat.testBit_lt_two_pow (i := 64 + i)
    (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  simp only [show 64 + i - 1 = 63 + i by omega, show 64 + i - 3 = 61 + i by omega,
    show 64 + i - 4 = 60 + i by omega, show 1 ≤ 64 + i by omega, show 3 ≤ 64 + i by omega,
    show 4 ≤ 64 + i by omega, decide_true, Bool.true_and]
  simp

/-- **The product's lane on natural numbers.** -/
theorem mulKNat_eq (a b : K) : mulKNat a.lane.toNat b.lane.toNat = (a * b).lane.toNat := by
  have hp : carryless a.lane.toNat b.lane.toNat =
      (carryLessMul (w := 128) a.toBitVec b.toBitVec).toNat := carryless_eq a.lane b.lane
  generalize hc : carryLessMul (w := 128) a.toBitVec b.toBitVec = c at hp
  have hprod : (a * b).lane.toNat = (reduce c).toNat := by
    rw [← hc]
    rfl
  have hcLt := c.isLt
  have hhi : c.toNat >>> 64 < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
    exact hcLt
  have hlo : c.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
  have hwords :
      c = wordsToBitVec (UInt64.ofNat (c.toNat >>> 64), UInt64.ofNat (c.toNat % 2 ^ 64)) := by
    apply BitVec.eq_of_toNat_eq
    rw [wordsToBitVec, BitVec.toNat_append, UInt64.toNat_toBitVec, UInt64.toNat_toBitVec,
      UInt64.toNat_ofNat_of_lt' hhi, UInt64.toNat_ofNat_of_lt' hlo]
    exact eq_shiftLeft_or_mod c.toNat 64
  rw [hprod, hwords, ← reduceWords_eq, UInt64.toNat_toBitVec, mulKNat_eq_folds, hp]
  simp only [reduceWords, UInt64.toNat_xor, toNat_tailLow, toNat_tailHigh,
    UInt64.toNat_ofNat_of_lt' hhi, UInt64.toNat_ofNat_of_lt' hlo]
  have hg : timesTail (c.toNat >>> 64) >>> 64 < 2 ^ 4 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
    exact timesTail_lt hhi
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (timesTail_lt hg) (Nat.pow_le_pow_right (by norm_num)
    (by omega)))]

/-- The product's lane is below `2^64`. -/
theorem mulKNat_lt (a b : K) : mulKNat a.lane.toNat b.lane.toNat < 2 ^ 64 := by
  rw [mulKNat_eq]
  exact UInt64.toNat_lt _

/-! ## On the machine -/

/-- A number below `2^(64·k)` has at most `k` limbs. -/
theorem limbCount_le_of_lt_two_pow {n k : ℕ} (hk : 1 ≤ k) (h : n < 2 ^ (64 * k)) :
    limbCount n ≤ k := by
  unfold limbCount
  by_cases h0 : n = 0
  · subst h0
    simp [Nat.log2_zero, hk]
  · have := (Nat.log2_lt h0).mpr h
    omega

/-- `mulKNat` as a term of the machine, the lanes at positions `i` and `j` of the environment:
the carry-less product bound once, the rest nested. -/
def mulKTerm (i j : ℕ) : Term :=
  .letIn (.primitive .carrylessMultiply [.position i, .position j])
    (.primitive .bitwiseXor [.position 0, .primitive .carrylessMultiply [
      .primitive .shiftRight [.primitive .carrylessMultiply [.primitive .shiftRight [.position 0,
          .literal (.nat 64)],
        .literal (.nat 0x1000000000000001B)], .literal (.nat 64)],
      .literal (.nat 0x1000000000000001B)]])

/-- **`mulKTerm` computes `mulKNat` at a price of at most `21`** (see the module docstring). -/
theorem evaluateTerm_mulKTerm (P : MachineProgram) (n : ℕ) (env : List MachineValue)
    {i j a b : ℕ} (hi : env[i]? = some (.nat a)) (hj : env[j]? = some (.nat b))
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ∃ c ≤ 21, evaluateTerm P n env (mulKTerm i j) = some (.nat (mulKNat a b), c) := by
  simp only [mulKTerm, evaluateTerm, evaluateTerms, hi, hj, PrimitiveOperation.apply,
    linearlyPricedResult, quadraticallyPricedResult, Option.map_some, Option.bind_eq_bind,
    Option.bind_some, List.getElem?_cons_zero, Option.pure_def]
  refine ⟨_, ?_, rfl⟩
  have hP : (0x1000000000000001B : ℕ) < 2 ^ 65 := by norm_num
  have hp : carryless a b < 2 ^ 127 := carryless_lt (n := 64) (m := 64) ha hb
  generalize carryless a b = p at *
  have hh : p >>> 64 < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
    exact hp
  have ht := carryless_lt hh hP
  generalize carryless (p >>> 64) 0x1000000000000001B = t at *
  generalize p >>> 64 = h at *
  have hq : t >>> 64 < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
    exact ht
  have hu := carryless_lt hq hP
  generalize carryless (t >>> 64) 0x1000000000000001B = u at *
  generalize t >>> 64 = q at *
  have hr : p ^^^ u < 2 ^ 127 := Nat.xor_lt_two_pow hp hu
  have two : ∀ x : ℕ, x < 2 ^ 127 → limbCount x ≤ 2 := fun x hx ↦
    limbCount_le_of_lt_two_pow (by omega)
      (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have one : ∀ x : ℕ, x < 2 ^ 64 → limbCount x = 1 := fun x hx ↦
    le_antisymm (limbCount_le_of_lt_two_pow le_rfl hx) (by unfold limbCount; omega)
  have := two _ hp
  have := two _ ht
  have := two _ hu
  have := two _ hr
  have := two 0x1000000000000001B (by norm_num)
  rw [one _ ha, one _ hb, one 64 (by norm_num), one h (lt_of_lt_of_le hh (by norm_num)),
    one q (lt_of_lt_of_le hq (by norm_num))]
  omega

/-- **`mulKTerm` computes the product of two encoded `K` elements at a price of at most
`21`.** -/
theorem evaluateTerm_mulKTerm_encode (P : MachineProgram) (n : ℕ) (env : List MachineValue)
    {i j : ℕ} {a b : K} (hi : env[i]? = some (encodeValue a))
    (hj : env[j]? = some (encodeValue b)) :
    ∃ c ≤ 21, evaluateTerm P n env (mulKTerm i j) = some (encodeValue (a * b), c) := by
  obtain ⟨c, hc, h⟩ := evaluateTerm_mulKTerm P n env (a := a.lane.toNat) (b := b.lane.toNat) hi hj
    a.lane.toNat_lt b.lane.toNat_lt
  exact ⟨c, hc, by rw [h, mulKNat_eq]; rfl⟩

end

end LeanVM.Cost
