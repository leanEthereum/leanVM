/-
  LeanVM.Guest.B1.Sig.SpWotsGroups

  `sp_wots`'s codeword on cells: its chain step and leaf, the digits its groups' dispatches take,
  and the arithmetic of its running product and encoding.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsLayout
public import LeanVM.Guest.B1.Sig.Codeword
public import LeanVM.Guest.B1.Sig.Merkle

/-!
# `sp_wots`'s codeword

* `spStepCell`, `spLeafCell`: the chain step and the one-time leaf over cells;
* `spDigitWord σ p` (`logG`, the unique exponent below the arm count), `spDigit σ i`, `spStart σ i`:
  the digits the dispatches take in a valuation of the template's numbering, chain `i`'s digit and
  the cell its start is hinted in (`spStartAt`, `SpWotsLayout`);
* `spCodeword_prod`, `spCodeword_enc`: the arithmetic: the running product is `g` to the digits'
  sum; the running encoding is the `XOR` of the digits' fields (`spX`), whose field at
  `spDigitPos i` is digit `i` (`spX_digit`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Cells -/

/-- **`sp_wots`'s chain step on cells**: step `s` of chain `i` on `x`, the first cell of the hash
of `pp`, `a0`, `a1 + spStepC i s` and `x` (`walk`, `lean_ethereum.py`). -/
def spStepCell (pp a0 a1 : E) (i s : Nat) (x : E) : E :=
  (hcell [pp, a0, a1 + lit (spStepC i s), x]).1

/-- **The one-time leaf over cells**: chain `i` walked from digit `d i` from `starts i` with the
step `spStepCell pp a0 a1`, the ends hashed after `pp`, `a0` and `a1 + SP_WOTS_PK` (`T_v`). -/
def spLeafCell (pp a0 a1 : E) (d : Nat → Nat) (starts : Nat → E) : E :=
  (hcell (pp :: a0 :: (a1 + spPkC) :: (List.range 64).map fun i =>
    chainT (spStepCell pp a0 a1) i (3 - d i) (d i) (starts i))).1

theorem lit_zero : lit 0 = 0 := by simp [lit, word_zero]

/-- `g^128`, the target sum in the exponent. -/
theorem spTarget_eq : spTarget = gen ^ 128 := by
  rw [Value.gen_pow_eq_ofK, spTarget, word, K.ofBits_zero, ← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

theorem spN_of_lt {p : Nat} (hp : p < 21) : spN p = 3 := by simp [spN, hp]

theorem spN_le (p : Nat) : spN p ≤ 3 := by unfold spN; split <;> omega

/-! ## The digits and the starts -/

/-- **The digit word group `p`'s dispatch takes**: its selector's exponent. -/
noncomputable def spDigitWord (σ : Val) (p : Nat) : Nat :=
  logG (σ (.n (spState p).2.2)) (4 ^ spN p)

/-- **The digit of chain `i`.** -/
noncomputable def spDigit (σ : Val) (i : Nat) : Nat := spDigitWord σ (i / 3) / 4 ^ (i % 3) % 4

/-- **Chain `i`'s start**: the value its walk hints, in the arm its group's dispatch takes. -/
noncomputable def spStart (σ : Val) (i : Nat) : V := spStartAt (spDigitWord σ) i

/-! ## The values -/

/-- **The codeword's product**: running products folded group by group (`G` groups of three digits,
then the last chain's) give `g` to the digits' sum. -/
theorem spCodeword_prod {G : Nat} (hG : 0 < G) (hG21 : G ≤ 21) (K : Nat → Nat)
    (hK : ∀ p ≤ G, K p < 4 ^ cwN G p) (pw : Nat → E) (hpow : ∀ s < 10, pw s = gen ^ s)
    (prodV : Nat → E)
    (hprod0 : prodV 0 = pw (digitSum (K 0) (cwN G 0)))
    (hprod : ∀ p < G, prodV (p + 1) = prodV p * pw (digitSum (K (p + 1)) (cwN G (p + 1)))) :
    prodV G = gen ^ (∑ i ∈ Finset.range (3 * G + 1), K (i / 3) / 4 ^ (i % 3) % 4) := by
  have hKG : K G < 4 := by simpa [cwN] using hK G le_rfl
  have hpr : ∀ p < G, prodV p = gen ^ (∑ q ∈ Finset.range (p + 1), digitSum (K q) 3) := by
    intro p hp
    induction p with
    | zero =>
        rw [hprod0]
        simp only [cwN, hp, ↓reduceIte]
        rw [hpow _ (by rw [digitSum_three]; omega)]
        simp
    | succ p ih =>
        rw [hprod p (by omega), ih (by omega)]
        simp only [cwN, hp, ↓reduceIte]
        rw [hpow _ (by rw [digitSum_three]; omega), Finset.sum_range_succ (n := p + 1), pow_add]
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  rw [hprod G' (by omega), hpr G' (by omega)]
  simp only [cwN, lt_irrefl, ↓reduceIte]
  rw [hpow _ (by rw [digitSum_one _ hKG]; omega), digitSum_one _ hKG, ← pow_add,
    Finset.sum_range_succ (n := 3 * (G' + 1)), sum_range_three_mul]
  congr 1
  simp only [show ∀ q, (3 * q) / 3 = q from fun q => by omega,
    show ∀ q, (3 * q + 1) / 3 = q from fun q => by omega, show ∀ q, (3 * q + 2) / 3 = q from fun q => by omega,
    show ∀ q, (3 * q) % 3 = 0 from fun q => by omega, show ∀ q, (3 * q + 1) % 3 = 1 from fun q => by omega,
    show ∀ q, (3 * q + 2) % 3 = 2 from fun q => by omega, digitSum_three]
  congr 1
  · apply Finset.sum_congr rfl
    intro q _
    simp
  · rw [pow_zero, Nat.div_one]; exact (Nat.mod_eq_of_lt hKG).symm

/-! ## The encoding, bit by bit -/

/-- Digit `j`'s field in the encoding digest's cell. -/
def spField (d : Nat → Nat) (j : Nat) : Nat := d j * 2 ^ spDigitPos j

/-- **The encoding of the digits `j < m`**: the `XOR` of their fields. -/
def spX (d : Nat → Nat) (m : Nat) : Nat := ((List.range m).map (spField d)).foldr (· ^^^ ·) 0

theorem foldr_xor_append (a b : List Nat) :
    (a ++ b).foldr (· ^^^ ·) 0 = a.foldr (· ^^^ ·) 0 ^^^ b.foldr (· ^^^ ·) 0 := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih, Nat.xor_assoc]

theorem foldr_xor_lt {w : Nat} : ∀ (l : List Nat), (∀ x ∈ l, x < 2 ^ w) → l.foldr (· ^^^ ·) 0 < 2 ^ w
  | [], _ => by simp
  | x :: l, h => by
      simp only [List.foldr_cons]
      exact Nat.xor_lt_two_pow (h x (by simp)) (foldr_xor_lt l fun y hy => h y (by simp [hy]))

theorem spX_add (d : Nat → Nat) (m n : Nat) :
    spX d (m + n) = spX d m ^^^ ((List.range n).map fun r => spField d (m + r)).foldr (· ^^^ ·) 0 := by
  rw [spX, List.range_add, List.map_append, foldr_xor_append, List.map_map]
  rfl

theorem spDigitPos_le {j : Nat} (hj : j < 64) : spDigitPos j ≤ 126 := by
  unfold spDigitPos; omega

theorem spField_lt {d : Nat → Nat} {j : Nat} (hd : d j < 4) (hj : j < 64) : spField d j < 2 ^ 128 := by
  unfold spField
  calc d j * 2 ^ spDigitPos j < 4 * 2 ^ spDigitPos j :=
        Nat.mul_lt_mul_of_pos_right hd (by positivity)
    _ = 2 ^ (spDigitPos j + 2) := by rw [pow_add]; ring
    _ ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by have := spDigitPos_le hj; omega)

theorem spX_lt {d : Nat → Nat} (hd : ∀ j, d j < 4) {m : Nat} (hm : m ≤ 64) : spX d m < 2 ^ 128 :=
  foldr_xor_lt _ fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact spField_lt (hd j) (by simp at hj; omega)

/-- A group's encoding constant is the `XOR` of its digits' fields. -/
theorem spDigitsC_eq (d : Nat → Nat) {p n k : Nat}
    (hd : ∀ r < n, d (3 * p + r) = k / 4 ^ r % 4) :
    spDigitsC (3 * p) n k = ((List.range n).map fun r => spField d (3 * p + r)).foldr (· ^^^ ·) 0 := by
  unfold spDigitsC
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [spField, hd r (List.mem_range.mp hr)]

theorem testBit_spField_ne {d : Nat → Nat} (hd : ∀ j, d j < 4) {i j t : Nat} (hij : j ≠ i) (ht : t < 2) : (spField d j).testBit (spDigitPos i + t) = false := by
  unfold spField
  rw [Nat.testBit_mul_two_pow]
  by_cases hle : spDigitPos j ≤ spDigitPos i + t
  · have hne : spDigitPos j ≠ spDigitPos i := by unfold spDigitPos; omega
    have h2 : 2 ≤ spDigitPos i + t - spDigitPos j := by
      have : spDigitPos j % 2 = 0 ∧ spDigitPos i % 2 = 0 := by unfold spDigitPos; omega
      omega
    simp only [hle, decide_true, Bool.true_and]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hd j) (by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (spDigitPos i + t - spDigitPos j) := Nat.pow_le_pow_right (by norm_num) h2))
  · simp [hle]

/-- **The encoding's bits**: bit `t < 2` of digit `i`'s field is digit `i`'s bit `t`, once the
digits `j < m` are in, `i < m`; none, `i ≥ m`. -/
theorem testBit_spX {d : Nat → Nat} (hd : ∀ j, d j < 4) {i t : Nat} (hi : i < 64) (ht : t < 2) :
    ∀ m, m ≤ 64 → (spX d m).testBit (spDigitPos i + t) = (decide (i < m) && (d i).testBit t)
  | 0, _ => by simp [spX]
  | m + 1, hm => by
      rw [spX_add, Nat.testBit_xor, testBit_spX hd hi ht m (by omega)]
      simp only [List.range_one, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
        Nat.add_zero, Nat.xor_zero]
      by_cases hmi : m = i
      · subst hmi
        simp only [lt_irrefl, decide_false, Bool.false_and, Bool.false_xor, Nat.lt_succ_self,
          decide_true, Bool.true_and, spField]
        rw [Nat.testBit_mul_two_pow]
        simp
      · rw [testBit_spField_ne hd hmi ht, Bool.xor_false]
        congr 1
        simp only [decide_eq_decide]
        omega

/-- **Digit `i` of the encoding**: its two bits at `spDigitPos i`. -/
theorem spX_digit {d : Nat → Nat} (hd : ∀ j, d j < 4) {i : Nat} (hi : i < 64) :
    spX d 64 / 2 ^ spDigitPos i % 4 = d i := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [show (4 : Nat) = 2 ^ 2 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases ht : t < 2
  · simp only [ht, decide_true, Bool.true_and]
    rw [Nat.add_comm, testBit_spX hd hi ht 64 le_rfl]
    simp [hi]
  · simp only [ht, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le (hd i) (by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

/-- **The codeword's encoding**: running encodings folded group by group (21 groups of three
digits, then the last chain's) give the `XOR` of the digits' fields, the digits `K`'s. -/
theorem spCodeword_enc (K : Nat → Nat) (encV : Nat → E)
    (henc0 : encV 0 = lit (spDigitsC 0 3 (K 0)))
    (henc : ∀ p < 21, encV (p + 1) =
      encV p + lit (spDigitsC (3 * (p + 1)) (spN (p + 1)) (K (p + 1)))) :
    encV 21 = Value.eOfNat128 (spX (fun i => K (i / 3) / 4 ^ (i % 3) % 4) 64) := by
  set d : Nat → Nat := fun i => K (i / 3) / 4 ^ (i % 3) % 4 with hdd
  have hd : ∀ j, d j < 4 := fun j => Nat.mod_lt _ (by norm_num)
  have hdg : ∀ p, ∀ r < 3, d (3 * p + r) = K p / 4 ^ r % 4 := fun p r hr => by
    simp only [hdd]
    rw [show (3 * p + r) / 3 = p by omega, show (3 * p + r) % 3 = r by omega]
  have hgrp : ∀ p n, n ≤ 3 → spDigitsC (3 * p) n (K p) =
      ((List.range n).map fun r => spField d (3 * p + r)).foldr (· ^^^ ·) 0 :=
    fun p n hn => spDigitsC_eq d fun r hr => hdg p r (by omega)
  have hlt : ∀ p n, n ≤ 3 → 3 * p + n ≤ 64 → spDigitsC (3 * p) n (K p) < 2 ^ 128 := by
    intro p n hn hpn
    rw [hgrp p n hn]
    exact foldr_xor_lt _ fun x hx => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact spField_lt (hd _) (by simp at hr; omega)
  have hrun : ∀ p ≤ 21, encV p = Value.eOfNat128 (spX d (3 * p + spN p)) := by
    intro p hp
    induction p with
    | zero =>
        rw [henc0, lit_eq _ (hlt 0 3 le_rfl (by norm_num)), spN_of_lt (by norm_num),
          show 3 * 0 + 3 = 0 + 3 by rfl, spX_add, hgrp 0 3 le_rfl]
        simp [spX]
    | succ p ih =>
        have hn := spN_le (p + 1)
        rw [henc p (by omega), ih (by omega), spN_of_lt (show p < 21 by omega),
          lit_eq _ (hlt (p + 1) _ hn (by unfold spN; split <;> omega)), ← Value.eOfNat128_xor,
          hgrp (p + 1) _ hn, spX_add d (3 * (p + 1)) (spN (p + 1)),
          show 3 * p + 3 = 3 * (p + 1) by ring]
  rw [hrun 21 le_rfl]
  rfl

theorem spLeafCell_congr {pp a0 a1 : E} {d d' : Nat → Nat} {s s' : Nat → E}
    (hd : ∀ i < 64, d i = d' i) (hs : ∀ i < 64, s i = s' i) :
    spLeafCell pp a0 a1 d s = spLeafCell pp a0 a1 d' s' := by
  unfold spLeafCell
  rw [List.map_congr_left fun i hi => by
    rw [hd i (List.mem_range.mp hi), hs i (List.mem_range.mp hi)]]

theorem spX_congr {d d' : Nat → Nat} (hd : ∀ i < 64, d i = d' i) : spX d 64 = spX d' 64 := by
  unfold spX
  rw [List.map_congr_left fun i hi => show spField d i = spField d' i by
    unfold spField; rw [hd i (List.mem_range.mp hi)]]

end
end LeanVM.Guest.B1.Sig
