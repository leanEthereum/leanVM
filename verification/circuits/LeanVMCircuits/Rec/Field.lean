module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.RingTheory.AdjoinRoot
public import Clean.Utils.FiniteField

@[expose] public section

/-!
The recursion machine's base field `K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, with its elements written as the
machine writes them: a 64-bit word whose bit `i` is the coefficient of `x^i`.

The modulus is proven irreducible from two certificates the kernel checks with carry-less word arithmetic:
`x^(2^64) = x` modulo it, and `x^(2^32) - x` is a unit modulo it.
-/

namespace LeanVMCircuits.Rec

open Polynomial

/-- The modulus of `K`. -/
noncomputable def modulus : (ZMod 2)[X] := X ^ 64 + X ^ 4 + X ^ 3 + X + 1

/-- The modulus as a word of coefficients. -/
def modulusWord : ℕ := 2 ^ 64 + 27

abbrev Quot := AdjoinRoot modulus

noncomputable def root : Quot := AdjoinRoot.root modulus

/-- The coefficient word `n` evaluated at the root: bit `i` is the coefficient of `root ^ i`. -/
noncomputable def ev (n : ℕ) : Quot :=
  if n = 0 then 0 else (if n % 2 = 1 then 1 else 0) + root * ev (n / 2)
decreasing_by omega

theorem ev_zero : ev 0 = 0 := by rw [ev]; simp

theorem ev_step (n : ℕ) : ev n = (if n % 2 = 1 then 1 else 0) + root * ev (n / 2) := by
  rw [ev]
  split
  · subst n; simp [ev_zero]
  · rfl

theorem two_eq_zero : (2 : Quot) = 0 := by
  have h := congrArg (algebraMap (ZMod 2) Quot) (show (2 : ZMod 2) = 0 from rfl)
  rwa [map_ofNat, map_zero] at h

private theorem coeff_xor (a b : ℕ) :
    (if (a ^^^ b) % 2 = 1 then (1 : Quot) else 0) =
      (if a % 2 = 1 then 1 else 0) + (if b % 2 = 1 then 1 else 0) := by
  have ha := Nat.mod_two_eq_zero_or_one a
  have hb := Nat.mod_two_eq_zero_or_one b
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [Nat.xor_mod_two_eq_one, ha, hb, ← two_eq_zero]
  norm_num

theorem ev_xor (a b : ℕ) : ev (a ^^^ b) = ev a + ev b := by
  induction h : a + b using Nat.strong_induction_on generalizing a b with
  | _ s ih =>
    by_cases hs : a + b = 0
    · have : a = 0 := by omega
      have : b = 0 := by omega
      subst a; subst b; simp [ev_zero]
    rw [ev_step (a ^^^ b), ev_step a, ev_step b, Nat.xor_div_two, coeff_xor,
      ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl]
    ring

theorem ev_double (a : ℕ) : ev (2 * a) = root * ev a := by
  rw [ev_step (2 * a)]
  simp

theorem ev_one : ev 1 = 1 := by
  rw [ev_step]; simp [ev_zero]

theorem ev_two : ev 2 = root := by
  have h : ev (2 * 1) = root := by rw [ev_double, ev_one, mul_one]
  simpa using h

theorem neg_eq_self (x : Quot) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul, two_eq_zero, zero_mul]

theorem ev_two_pow_mul (k a : ℕ) : ev (2 ^ k * a) = root ^ k * ev a := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc, ev_double, ih]; ring

/-- Carry-less product, `b` read through `n` bits. -/
def clmul : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, a, b => (if b % 2 = 1 then a else 0) ^^^ clmul n (2 * a) (b / 2)

theorem ev_clmul (n a b : ℕ) (hb : b < 2 ^ n) : ev (clmul n a b) = ev a * ev b := by
  induction n generalizing a b with
  | zero => simp at hb; subst hb; simp [clmul, ev_zero]
  | succ n ih =>
    rw [clmul, ev_xor, ih _ _ (by rw [pow_succ] at hb; omega), ev_double, ev_step b]
    split_ifs <;> (try simp only [ev_zero]) <;> ring

/-- One reduction step at bit `d`: clear it with the modulus shifted to it. -/
def reduceAt (d a : ℕ) : ℕ := if a.testBit d then a ^^^ 2 ^ (d - 64) * modulusWord else a

/-- Reduction of a product below `2^128`, high bits first. -/
def reduce (a : ℕ) : ℕ := (List.range 64).foldl (fun a j => reduceAt (127 - j) a) a

theorem ev_modulusWord : ev modulusWord = 0 := by
  have h : modulusWord = 2 ^ 64 * 1 ^^^ (2 ^ 4 * 1 ^^^ (2 ^ 3 * 1 ^^^ (2 ^ 1 * 1 ^^^ 1))) := by decide
  rw [h, ev_xor, ev_xor, ev_xor, ev_xor, ev_two_pow_mul, ev_two_pow_mul, ev_two_pow_mul, ev_two_pow_mul,
    ev_one, mul_one, mul_one, mul_one, mul_one]
  have hz : AdjoinRoot.mk modulus (X ^ 64 + X ^ 4 + X ^ 3 + X + 1) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one] at hz
  rw [← hz, root]
  ring

theorem ev_reduceAt (d a : ℕ) : ev (reduceAt d a) = ev a := by
  unfold reduceAt
  split
  · rw [ev_xor, ev_two_pow_mul, ev_modulusWord]; simp
  · rfl

theorem ev_reduce (a : ℕ) : ev (reduce a) = ev a := by
  unfold reduce
  generalize List.range 64 = l
  induction l generalizing a with
  | nil => rfl
  | cons j l ih => rw [List.foldl_cons, ih, ev_reduceAt]

/-- The product in `K` of two coefficient words below `2^64`. -/
def mul (a b : ℕ) : ℕ := reduce (clmul 64 a b)

theorem ev_mul (a b : ℕ) (hb : b < 2 ^ 64) : ev (mul a b) = ev a * ev b := by
  rw [mul, ev_reduce, ev_clmul _ _ _ hb]

/-- `x^(2^k)` as a word for `k ≤ 64`, each the square of the one before (`chain_squares`). -/
def chain : List ℕ :=
  [0x2, 0x4, 0x10, 0x100, 0x10000, 0x100000000, 0x1b, 0x145, 0x11011, 0x101000101, 0x100000001001a, 0x1a00000144, 0x10dbc, 0x100514550, 0x11011011111b, 0x10001011a1a015e, 0x15f0144001a114f, 0x1aad43011ba1e5, 0x11cefef6be466, 0x5455145e48670f13, 0xbaf1bebe1ae4ad02, 0xb0ef530df44bb042, 0xe2170b43ee771735, 0x48380fd207a3b527, 0xb6d535c542116f62, 0xa6df6baa62f965f5, 0xb9df3947cea0ffe7, 0xe1882807248fe588, 0x180d86953ed141c6, 0x1894566cd1db8abf, 0x4cc78bf4ea999e25, 0xe333308087e402ba, 0x5c62236777028505, 0xb964dc682c67ddcd, 0xb58ac9a23d208acb, 0xb3fcc2ab3699fc73, 0xb2644136253abfe8, 0xb37cd8f5f54e22c6, 0xe267d02369c356e5, 0x82c8dc57a143827, 0x13846a66c22c75be, 0x4b75c5e1cfbc9888, 0xe6e383fc30ec5c40, 0x18db4821d1201031, 0x4cc669b6b7c0691a, 0xf26221ddce9cb783, 0x57399d3c29092c2f, 0xae86719cd83b743e, 0xfa5ac498d20dd97e, 0x50a9adfa20f7c8d5, 0xaf06ffc8fb2c50a6, 0xfe42058b1100328e, 0x11cb06c04a986a2, 0xb5837f7159f74, 0x551507a7ec9563d7, 0xfefb5bba15c4fcc9, 0x10a51a6f8e1e1ac, 0x555b52acff1ce98c, 0xfffface6ff2beb3b, 0x55550444ff3218d8, 0xffffafaf00f1e0eb, 0x5500ff01ff03, 0x55550000fffe0005, 0xffffffff0000000a, 0x2]

theorem chain_squares : ∀ k < 64, mul (chain.getD k 0) (chain.getD k 0) = chain.getD (k + 1) 0 ∧
    chain.getD k 0 < 2 ^ 64 := by
  decide +kernel

theorem ev_chain (k : ℕ) (hk : k ≤ 64) : ev (chain.getD k 0) = root ^ 2 ^ k := by
  induction k with
  | zero => rw [show chain.getD 0 0 = 2 by decide, ev_two]; simp
  | succ k ih =>
    obtain ⟨hsq, hlt⟩ := chain_squares k (by omega)
    rw [← hsq, ev_mul _ _ hlt, ih (by omega), pow_succ, pow_mul]
    ring

/-- `x^(2^64) = x` modulo the modulus. -/
theorem root_pow_two_pow_64 : root ^ 2 ^ 64 = root := by
  rw [← ev_chain 64 le_rfl, show chain.getD 64 0 = 2 by decide, ev_two]

/-- The inverse of `x^(2^32) - x` modulo the modulus. -/
def cofactor : ℕ := 0x53cad161bf5a89c7

theorem cofactor_mul : mul cofactor (chain.getD 32 0 ^^^ 2) = 1 := by decide +kernel

theorem root_pow_two_pow_32_sub_unit : ev cofactor * (root ^ 2 ^ 32 - root) = 1 := by
  have h := congrArg ev cofactor_mul
  rw [ev_mul _ _ (by decide +kernel), ev_xor, ev_chain 32 (by omega), ev_two, ev_one] at h
  rwa [sub_eq_add_neg, neg_eq_self]

theorem modulus_natDegree : modulus.natDegree = 64 := by
  unfold modulus; compute_degree!

theorem modulus_monic : modulus.Monic := by
  unfold modulus; monicity!

theorem modulus_ne_zero : modulus ≠ 0 := modulus_monic.ne_zero

theorem mk_X : AdjoinRoot.mk modulus X = root := AdjoinRoot.mk_X

theorem dvd_frobenius_64 : modulus ∣ X ^ 2 ^ 64 - X := by
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, mk_X, root_pow_two_pow_64, sub_self]

/-- A common divisor of the modulus and `X^n - X` is a unit when `x^n - x` is invertible modulo the modulus. -/
theorem isUnit_of_dvd_of_inverse (n : ℕ) (u : Quot) (hu : u * (root ^ n - root) = 1) (f : (ZMod 2)[X])
    (hm : f ∣ modulus) (h32 : f ∣ X ^ n - X) : IsUnit f := by
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective (g := modulus) u
  have hone : modulus ∣ q * (X ^ n - X) - 1 := by
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_mul, hq, map_sub, map_pow, mk_X, map_one, hu, sub_self]
  have h1 : f ∣ 1 := by
    have := (dvd_trans hm hone)
    have h2 : f ∣ q * (X ^ n - X) := dvd_mul_of_dvd_right h32 q
    simpa using (dvd_sub h2 this)
  exact isUnit_of_dvd_one h1

theorem card_zmod_two : Nat.card (ZMod 2) = 2 := by simp

theorem modulus_irreducible : Irreducible modulus := by
  have hnu : ¬IsUnit modulus := by
    intro hu
    have := natDegree_eq_zero_of_isUnit hu
    rw [modulus_natDegree] at this
    exact absurd this (by norm_num)
  obtain ⟨f, hf, hfm⟩ := WfDvdMonoid.exists_irreducible_factor hnu modulus_ne_zero
  have hdeg : f.natDegree ∣ 64 := by
    apply hf.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
    rw [card_zmod_two]
    exact dvd_trans hfm dvd_frobenius_64
  have hle : f.natDegree ≤ 64 := modulus_natDegree ▸ natDegree_le_of_dvd hfm modulus_ne_zero
  have h64 : f.natDegree = 64 := by
    by_contra hne
    have h32 : f.natDegree ∣ 32 := by
      obtain ⟨i, hi, hfi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show f.natDegree ∣ 2 ^ 6 by simpa using hdeg)
      rw [hfi]
      have : i ≠ 6 := by rintro rfl; exact hne (by rw [hfi]; norm_num)
      exact Nat.pow_dvd_pow 2 (by omega : i ≤ 5)
    have hdvd : f ∣ X ^ 2 ^ 32 - X := by
      have := (hf.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := 32)).mp h32
      rwa [card_zmod_two] at this
    exact hf.not_isUnit (isUnit_of_dvd_of_inverse _ _ root_pow_two_pow_32_sub_unit f hfm hdvd)
  obtain ⟨g, hg⟩ := hfm
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg; exact modulus_ne_zero hg
  have hgdeg : g.natDegree = 0 := by
    have := congrArg natDegree hg
    rw [natDegree_mul hf.ne_zero hg0, h64, modulus_natDegree] at this
    omega
  have hgu : IsUnit g := by
    rw [eq_C_of_natDegree_eq_zero hgdeg]
    exact isUnit_C.mpr (Ne.isUnit (by
      intro h0; apply hg0; rw [eq_C_of_natDegree_eq_zero hgdeg, h0, C_0]))
  rw [hg]
  exact (irreducible_mul_isUnit hgu).mpr hf

instance : Fact (Irreducible modulus) := ⟨modulus_irreducible⟩

/-- The recursion machine's base field `K`. -/
abbrev K := AdjoinRoot modulus

noncomputable instance : Field K := AdjoinRoot.instField

/-! `K`'s elements as the machine writes them: the word of their coefficients in the basis `1, x, ..., x^63`. -/

noncomputable def basis : PowerBasis (ZMod 2) K := AdjoinRoot.powerBasis' modulus_monic

def bitZ (n i : ℕ) : ZMod 2 := if n.testBit i then 1 else 0

theorem zmod2_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The number whose bit `i` is `c i`, for `i < m`. -/
def num (c : ℕ → ZMod 2) : ℕ → ℕ
  | 0 => 0
  | m + 1 => (c 0).val + 2 * num (fun i => c (i + 1)) m

theorem num_lt (c : ℕ → ZMod 2) (m : ℕ) : num c m < 2 ^ m := by
  induction m generalizing c with
  | zero => simp [num]
  | succ m ih =>
    have := ih (fun i => c (i + 1))
    have hc := ZMod.val_lt (c 0)
    simp only [num, pow_succ]
    omega

theorem testBit_num (c : ℕ → ZMod 2) (m i : ℕ) (hi : i < m) : (num c m).testBit i = decide (c i = 1) := by
  induction m generalizing c i with
  | zero => omega
  | succ m ih =>
    have hc := ZMod.val_lt (c 0)
    rcases i with _ | i
    · simp only [num, Nat.testBit_zero]
      have h2 : ((c 0).val + 2 * num (fun i => c (i + 1)) m) % 2 = (c 0).val := by omega
      rw [h2]
      rcases zmod2_cases (c 0) with h | h <;> rw [h] <;> decide
    · rw [num, Nat.testBit_succ,
        show ((c 0).val + 2 * num (fun i => c (i + 1)) m) / 2 = num (fun i => c (i + 1)) m by omega]
      exact ih _ _ (by omega)

theorem num_bitZ (n m : ℕ) (hn : n < 2 ^ m) : num (bitZ n) m = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · rw [testBit_num _ _ _ hi, bitZ]; split <;> simp_all
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (num_lt _ m) (Nat.pow_le_pow_right (by norm_num) (show m ≤ i by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (show m ≤ i by omega)))]

theorem bitZ_succ (n i : ℕ) : bitZ n (i + 1) = bitZ (n / 2) i := by simp [bitZ, Nat.testBit_succ]

theorem ev_eq_sum (m n : ℕ) (hn : n < 2 ^ m) : ev n = ∑ i : Fin m, bitZ n i • root ^ (i : ℕ) := by
  induction m generalizing n with
  | zero => simp at hn; subst hn; simp [ev_zero]
  | succ m ih =>
    rw [ev_step, ih (n / 2) (by rw [pow_succ] at hn; omega), Fin.sum_univ_succ, Finset.mul_sum]
    congr 1
    · simp only [bitZ, Nat.testBit_zero, Fin.val_zero, pow_zero]
      split <;> simp_all
    · apply Finset.sum_congr rfl
      intro i _
      rw [Fin.val_succ, bitZ_succ, pow_succ, mul_smul_comm]
      ring_nf

/-- Coefficient `i` of `x` in the basis `x^i`. -/
noncomputable def coeff (x : K) (i : ℕ) : ZMod 2 := if h : i < basis.dim then basis.basis.repr x ⟨i, h⟩ else 0

theorem basis_dim : basis.dim = 64 := modulus_natDegree

theorem coeff_ev (n i : ℕ) (hn : n < 2 ^ 64) : coeff (ev n) i = bitZ n i := by
  unfold coeff
  split
  · rename_i h
    have hsum : ev n = ∑ j : Fin basis.dim, bitZ n j • basis.basis j := by
      rw [PowerBasis.coe_basis, ev_eq_sum basis.dim n (by rw [basis_dim]; exact hn)]
      rfl
    rw [hsum, Module.Basis.repr_sum_self]
  · rename_i h
    rw [basis_dim] at h
    simp [bitZ, Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (show 64 ≤ i by omega)))]

theorem ext_coeff (x y : K) (h : ∀ i, coeff x i = coeff y i) : x = y := by
  apply basis.basis.repr.injective
  ext ⟨i, hi⟩
  have := h i
  simp only [coeff, hi, dif_pos] at this
  exact this

/-- The coefficient word of `x`. -/
noncomputable def toWord (x : K) : ℕ := num (coeff x) 64

/-- The element of a coefficient word. -/
noncomputable def ofWord (n : ℕ) : K := ev (n % 2 ^ 64)

theorem toWord_ofWord (n : ℕ) (hn : n < 2 ^ 64) : toWord (ofWord n) = n := by
  unfold toWord ofWord
  rw [Nat.mod_eq_of_lt hn]
  have : coeff (ev n) = bitZ n := funext fun i => coeff_ev n i hn
  rw [this, num_bitZ n 64 hn]

theorem toWord_injective : Function.Injective toWord := by
  intro x y h
  apply ext_coeff
  intro i
  by_cases hi : i < 64
  · have hx := testBit_num (coeff x) 64 i hi
    have hy := testBit_num (coeff y) 64 i hi
    unfold toWord at h
    rw [h, hy] at hx
    rcases zmod2_cases (coeff x i) with a | a <;> rcases zmod2_cases (coeff y i) with b | b <;> simp_all
  · unfold coeff
    rw [dif_neg (by rw [basis_dim]; exact hi), dif_neg (by rw [basis_dim]; exact hi)]

noncomputable instance : FiniteField K where
  val := toWord
  fromNat := ofWord
  size := 2 ^ 64
  val_lt x := num_lt _ _
  val_injective := toWord_injective
  val_fromNat n hn := toWord_ofWord n hn
  val_zero := by
    have := toWord_ofWord 0 (by norm_num)
    simpa [ofWord, ev_zero] using this
  val_one := by
    have := toWord_ofWord 1 (by norm_num)
    simpa [ofWord, ev_one] using this

end LeanVMCircuits.Rec
