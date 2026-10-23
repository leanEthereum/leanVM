/-
  LeanVM.Guest.B1.Tables.Padding

  B1 for `padding_weight`: a table's padding weight at the bus point, and the certificate that
  its hinted log height is the least holding its rows, at each of its 29 specializations.
-/

module

public import LeanVM.Guest.B1.Log2

/-!
# `padding_weight` (TRIAGE #38)

`padding_weight(rows, zeta, tau)` (G:1441-1472) hints the `τ + 1` bits of the word
`W = rows + (2^τ - 1)`, pins them Boolean, reconstructs `W` from them and checks that the top bit
`n_τ` is set only alone: that is `rows = E(n)` for an integer `n ≤ 2^τ`, the `τ` low bits being
`n`'s complements (`pw_bits`). From the complements it folds `paddingWeight` (V:713) over
`zeta[..τ]`, and it returns two words, `lead` and `rest`, with `lead = 1 ∧ rest ≠ 0` exactly when
`τ = log2Ceil n` (`lead_rest_iff`), which `verify_tables` asserts.

The expansion at `τ ≥ 2` is `pwBody τ`: the head, the fold's first step and its `τ - 1` later
steps, the top bit's booleanity, `τ - 2` Horner steps of the low bits and the tail; it is equal
to each specialization `__L2` .. `__L28` by kernel evaluation. `__L0` and `__L1` are their own.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The head: `W = rows + (2^τ - 1)` and its `τ + 1` hinted bits, at values `4 .. 4 + τ`. -/
def pwHead (τ : ℕ) : List Stmt :=
  [.atom (.const (.n 2) (word (2 ^ τ - 1) 0 0)), .atom (.add (.n 3) (.n 0) (.n 2)),
    .atom (.hint (.bits (.n 3) 0 (τ + 1) (.stack ((List.range (τ + 1)).map fun k => .n (4 + k)))))]

/-- The fold's first step, its `pad = 1` folded. -/
def pwStep0 (τ : ℕ) : List Stmt :=
  [.atom (.mul (.n 4) (.n 4) (.n 4)), .atom (.load (.n (τ + 5)) (.n 1) 0),
    .atom (.mul (.n (τ + 6)) (.n 4) (.n (τ + 5))), .atom (.add (.n (τ + 7)) (.n 4) (.n (τ + 5))),
    .atom (.add (.n (τ + 8)) (.n (τ + 6)) (.n (τ + 7)))]

/-- The fold's step `k ≥ 1`: `pad = c·z + (c + z)·pad`. -/
def pwStep (τ k : ℕ) : List Stmt :=
  [.atom (.mul (.n (4 + k)) (.n (4 + k)) (.n (4 + k))), .atom (.load (.n (τ + 4 + 5 * k)) (.n 1) k),
    .atom (.mul (.n (τ + 5 + 5 * k)) (.n (4 + k)) (.n (τ + 4 + 5 * k))),
    .atom (.add (.n (τ + 6 + 5 * k)) (.n (4 + k)) (.n (τ + 4 + 5 * k))),
    .atom (.mul (.n (τ + 7 + 5 * k)) (.n (τ + 6 + 5 * k)) (.n (τ + 3 + 5 * k))),
    .atom (.add (.n (τ + 8 + 5 * k)) (.n (τ + 5 + 5 * k)) (.n (τ + 7 + 5 * k)))]

/-- The running sum of the bits below `τ - 1` after Horner step `j`, by its value number. -/
def pwBelow (τ j : ℕ) : ℕ := if j = 0 then τ + 2 else 6 * τ + 3 + 3 * j

/-- Horner step `j`: `below = below·2 + bit (τ - 3 - j)`. -/
def pwHorner (τ j : ℕ) : List Stmt :=
  [.atom (.const (.n (6 * τ + 4 + 3 * j)) (word 2 0 0)),
    .atom (.mul (.n (6 * τ + 5 + 3 * j)) (.n (pwBelow τ j)) (.n (6 * τ + 4 + 3 * j))),
    .atom (.add (.n (6 * τ + 6 + 3 * j)) (.n (6 * τ + 5 + 3 * j)) (.n (τ + 1 - j)))]

/-- The tail, from value `L = 9τ - 2`: `low`, `lead`, `rest`, the two checks, the returns. -/
def pwTail (τ : ℕ) : List Stmt :=
  let L := 9 * τ - 2
  let top := 4 + τ
  let b1 := 3 + τ
  let bl := pwBelow τ (τ - 2)
  [.atom (.const (.n L) (word (2 ^ (τ - 1)) 0 0)), .atom (.mul (.n (L + 1)) (.n b1) (.n L)),
    .atom (.add (.n (L + 2)) (.n bl) (.n (L + 1))),
    .atom (.const (.n (L + 3)) (word 1 0 0)), .atom (.add (.n (L + 4)) (.n top) (.n (L + 3))),
    .atom (.add (.n (L + 5)) (.n (L + 4)) (.n b1)),
    .atom (.add (.n (L + 6)) (.n top) (.n bl)),
    .atom (.const (.n (L + 7)) (word (2 ^ (τ - 1) - 1) 0 0)),
    .atom (.add (.n (L + 8)) (.n (L + 6)) (.n (L + 7))),
    .atom (.const (.n (L + 9)) (word (2 ^ τ) 0 0)), .atom (.mul (.n (L + 10)) (.n top) (.n (L + 9))),
    .atom (.add (.n (L + 11)) (.n (L + 2)) (.n (L + 10))), .atom (.assertEq (.n (L + 11)) (.n 3)),
    .atom (.const (.n (L + 12)) (word (2 ^ τ - 1) 0 0)),
    .atom (.add (.n (L + 13)) (.n (L + 2)) (.n (L + 12))),
    .atom (.mul (.n (L + 14)) (.n top) (.n (L + 13))), .atom (.const (.n (L + 15)) (word 0 0 0)),
    .atom (.assertEq (.n (L + 14)) (.n (L + 15))),
    .atom (.const (.n (L + 16)) (word 1 0 0)), .atom (.add (.n (L + 17)) (.n (L + 16)) (.n top)),
    .atom (.mul (.n (L + 18)) (.n (L + 17)) (.n (6 * τ + 3))),
    .atom (.copy (.n (L + 19)) (.n (L + 5))), .atom (.copy (.n (L + 20)) (.n (L + 8))),
    .ret [.n (L + 18), .n (L + 19), .n (L + 20)]]

/-- The expansion of `padding_weight` at `τ ≥ 2`. -/
def pwBody (τ : ℕ) : List Stmt :=
  pwHead τ ++ pwStep0 τ ++ ((List.range (τ - 1)).map fun i => pwStep τ (i + 1)).flatten ++
    [.atom (.mul (.n (4 + τ)) (.n (4 + τ)) (.n (4 + τ)))] ++
    ((List.range (τ - 2)).map (pwHorner τ)).flatten ++ pwTail τ

theorem core44_body : Fn.body Data.core44 = pwBody 2 := stmtsEqb_sound (by decide +kernel)
theorem core45_body : Fn.body Data.core45 = pwBody 3 := stmtsEqb_sound (by decide +kernel)
theorem core46_body : Fn.body Data.core46 = pwBody 4 := stmtsEqb_sound (by decide +kernel)
theorem core47_body : Fn.body Data.core47 = pwBody 5 := stmtsEqb_sound (by decide +kernel)
theorem core48_body : Fn.body Data.core48 = pwBody 6 := stmtsEqb_sound (by decide +kernel)
theorem core49_body : Fn.body Data.core49 = pwBody 7 := stmtsEqb_sound (by decide +kernel)
theorem core50_body : Fn.body Data.core50 = pwBody 8 := stmtsEqb_sound (by decide +kernel)
theorem core51_body : Fn.body Data.core51 = pwBody 9 := stmtsEqb_sound (by decide +kernel)
theorem core52_body : Fn.body Data.core52 = pwBody 10 := stmtsEqb_sound (by decide +kernel)
theorem core53_body : Fn.body Data.core53 = pwBody 11 := stmtsEqb_sound (by decide +kernel)
theorem core54_body : Fn.body Data.core54 = pwBody 12 := stmtsEqb_sound (by decide +kernel)
theorem core55_body : Fn.body Data.core55 = pwBody 13 := stmtsEqb_sound (by decide +kernel)
theorem core56_body : Fn.body Data.core56 = pwBody 14 := stmtsEqb_sound (by decide +kernel)
theorem core57_body : Fn.body Data.core57 = pwBody 15 := stmtsEqb_sound (by decide +kernel)
theorem core58_body : Fn.body Data.core58 = pwBody 16 := stmtsEqb_sound (by decide +kernel)
theorem core59_body : Fn.body Data.core59 = pwBody 17 := stmtsEqb_sound (by decide +kernel)
theorem core60_body : Fn.body Data.core60 = pwBody 18 := stmtsEqb_sound (by decide +kernel)
theorem core61_body : Fn.body Data.core61 = pwBody 19 := stmtsEqb_sound (by decide +kernel)
theorem core62_body : Fn.body Data.core62 = pwBody 20 := stmtsEqb_sound (by decide +kernel)
theorem core63_body : Fn.body Data.core63 = pwBody 21 := stmtsEqb_sound (by decide +kernel)
theorem core64_body : Fn.body Data.core64 = pwBody 22 := stmtsEqb_sound (by decide +kernel)
theorem core65_body : Fn.body Data.core65 = pwBody 23 := stmtsEqb_sound (by decide +kernel)
theorem core66_body : Fn.body Data.core66 = pwBody 24 := stmtsEqb_sound (by decide +kernel)
theorem core67_body : Fn.body Data.core67 = pwBody 25 := stmtsEqb_sound (by decide +kernel)
theorem core68_body : Fn.body Data.core68 = pwBody 26 := stmtsEqb_sound (by decide +kernel)
theorem core69_body : Fn.body Data.core69 = pwBody 27 := stmtsEqb_sound (by decide +kernel)
theorem core70_body : Fn.body Data.core70 = pwBody 28 := stmtsEqb_sound (by decide +kernel)

/-! ## Bits and words -/

/-- The word whose bits the guest hints: `n` with its `τ` low bits complemented. -/
def pwW (τ n : ℕ) : ℕ := n ^^^ (2 ^ τ - 1)

theorem testBit_pwW (τ n k : ℕ) : (pwW τ n).testBit k = (n.testBit k ^^ decide (k < τ)) := by
  rw [pwW, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]

theorem pwW_pwW (τ n : ℕ) : pwW τ (pwW τ n) = n := by
  rw [pwW, pwW, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem two_pow_sub_one_lt (τ : ℕ) : 2 ^ τ - 1 < 2 ^ (τ + 1) := by
  have := Nat.two_pow_pos τ
  rw [pow_succ]; omega

theorem pwW_lt {τ n : ℕ} (hn : n < 2 ^ (τ + 1)) : pwW τ n < 2 ^ (τ + 1) :=
  Nat.xor_lt_two_pow hn (two_pow_sub_one_lt τ)

theorem eOfNat_shift_mod (n k : ℕ) : eOfNat ((n >>> k) % 2) = bitE (n.testBit k) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;>
    simp [h, bitE, eOfNat_zero, eOfNat_one]

theorem one_add_bitE (c : Bool) : 1 + bitE c = bitE (!c) := by
  cases c <;> simp [bitE, e_add_self]

theorem bitE_xor_true (c : Bool) : bitE (c ^^ true) = 1 + bitE c := by
  cases c <;> simp [bitE, e_add_self]

/-- A run of bits read off a word: `Σ_{k < j} bit k · E(2^k) = E(W mod 2^j)`. -/
theorem sum_testBit_gen_pow (W j : ℕ) (hj : j ≤ 64) :
    ∑ k ∈ Finset.range j, bitE (W.testBit k) * gen ^ k = eOfNat (W % 2 ^ j) := by
  rw [← sum_bits_mod W j hj]
  exact Finset.sum_congr rfl fun k hk => by
    rw [coordBasis_of_lt (by have := Finset.mem_range.mp hk; omega),
      gen_pow_eq_eOfNat (by have := Finset.mem_range.mp hk; omega)]

/-- **The hinted bits are `n`'s** (G:1444-1471): Boolean `b_k` reconstructing
`rows + E(2^τ - 1)`, the top one set only with every bit below it, make `rows = E(n)` with
`n ≤ 2^τ`, `b_k` bit `k` of `pwW τ n`. -/
theorem pw_bits {τ : ℕ} (hτ : τ < 63) {b : ℕ → E} (hb : ∀ k ≤ τ, b k * b k = b k) {rows : E}
    (hrec : ∑ k ∈ Finset.range (τ + 1), b k * gen ^ k = rows + eOfNat (2 ^ τ - 1))
    (htop : b τ * (∑ k ∈ Finset.range τ, b k * gen ^ k + eOfNat (2 ^ τ - 1)) = 0) :
    ∃ n ≤ 2 ^ τ, rows = eOfNat n ∧ ∀ k ≤ τ, b k = bitE ((pwW τ n).testBit k) := by
  have hrec' : ∑ k ∈ Finset.range (τ + 1), b k * coordBasis (0 + k) =
      rows + eOfNat (2 ^ τ - 1) := by
    rw [← hrec]
    exact Finset.sum_congr rfl fun k hk => by
      rw [Nat.zero_add, coordBasis_of_lt (by have := Finset.mem_range.mp hk; omega),
        gen_pow_eq_eOfNat (by have := Finset.mem_range.mp hk; omega)]
  obtain ⟨W, hW, hx, hbits⟩ := bits_of_reconstruct (fun k hk => hb k (by omega)) hrec'
  have hW64 : W < 2 ^ 64 := lt_of_lt_of_le hW (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.pow_zero, Nat.one_mul, eOfNat192_of_lt hW64] at hx
  have hrows : rows = eOfNat (pwW τ W) := by
    rw [pwW, eOfNat_xor, ← hx, add_assoc, e_add_self, add_zero]
  have hb' : ∀ k ≤ τ, b k = bitE ((pwW τ (pwW τ W)).testBit k) := fun k hk => by
    rw [pwW_pwW]; exact hbits k (by omega)
  refine ⟨pwW τ W, ?_, hrows, hb'⟩
  have hlow : ∑ k ∈ Finset.range τ, b k * gen ^ k = eOfNat (W % 2 ^ τ) := by
    rw [← sum_testBit_gen_pow W τ (by omega)]
    exact Finset.sum_congr rfl fun k hk => by rw [hbits k (by have := Finset.mem_range.mp hk; omega)]
  rw [hlow, hbits τ (by omega)] at htop
  have hlt : pwW τ W < 2 ^ (τ + 1) := pwW_lt hW
  cases hWt : W.testBit τ
  · have hWτ : W < 2 ^ τ := by
      refine Nat.lt_pow_two_of_testBit W fun i hi => ?_
      rcases Nat.lt_or_ge τ i with h | h
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hW (Nat.pow_le_pow_right (by decide) h))
      · rw [show i = τ by omega]; exact hWt
    have : pwW τ W < 2 ^ τ := Nat.xor_lt_two_pow hWτ (by have := Nat.two_pow_pos τ; omega)
    omega
  · rw [hWt] at htop
    simp only [bitE, ↓reduceIte, one_mul] at htop
    have hmod : W % 2 ^ τ = 2 ^ τ - 1 :=
      eOfNat_inj (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos τ))
        (Nat.pow_le_pow_right (by decide) (by omega)))
        (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by decide) (by omega)))
        (e_add_eq_zero_iff.mp htop)
    have hpw : pwW τ W = 2 ^ τ := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      rw [testBit_pwW, Nat.testBit_two_pow]
      rcases Nat.lt_trichotomy i τ with h | h | h
      · have := Nat.testBit_mod_two_pow W τ i
        rw [hmod, Nat.testBit_two_pow_sub_one] at this
        simp only [h, decide_true, Bool.true_and] at this
        rw [← this]
        simp [h, Nat.ne_of_gt h]
      · subst h; simp [hWt]
      · have h1 : W.testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hW (Nat.pow_le_pow_right (by decide) h))
        simp [h1, show ¬ i < τ by omega, show τ ≠ i by omega]
    omega

/-- **Completeness of the bits**: `n ≤ 2^τ` gives Boolean bits of `pwW τ n` that reconstruct
`E(n) + E(2^τ - 1)` and pass the top check. -/
theorem pw_bits_complete {τ n : ℕ} (hτ : τ < 63) (hn : n ≤ 2 ^ τ) :
    ∑ k ∈ Finset.range (τ + 1), bitE ((pwW τ n).testBit k) * gen ^ k =
        eOfNat n + eOfNat (2 ^ τ - 1) ∧
      bitE ((pwW τ n).testBit τ) *
        (∑ k ∈ Finset.range τ, bitE ((pwW τ n).testBit k) * gen ^ k + eOfNat (2 ^ τ - 1)) = 0 := by
  have hn1 : n < 2 ^ (τ + 1) := by rw [pow_succ]; have := Nat.two_pow_pos τ; omega
  have hlt := pwW_lt hn1
  refine ⟨?_, ?_⟩
  · rw [sum_testBit_gen_pow _ _ (by omega), Nat.mod_eq_of_lt hlt, pwW, eOfNat_xor]
  · rw [sum_testBit_gen_pow _ _ (by omega), testBit_pwW]
    simp only [lt_irrefl, decide_false, Bool.xor_false]
    rcases Nat.lt_or_ge n (2 ^ τ) with h | h
    · rw [Nat.testBit_lt_two_pow h]; simp [bitE]
    · have hn' : n = 2 ^ τ := by omega
      subst hn'
      have : pwW τ (2 ^ τ) % 2 ^ τ = 2 ^ τ - 1 := by
        refine Nat.eq_of_testBit_eq fun i => ?_
        rw [Nat.testBit_mod_two_pow, testBit_pwW, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
        rcases Nat.lt_or_ge i τ with h' | h'
        · simp [h', Nat.ne_of_gt h']
        · simp [show ¬ i < τ by omega]
      rw [this, e_add_self, mul_zero]

/-! ## The padding fold -/

/-- The guest's fold: `pad ← c_k·z_k + (c_k + z_k)·pad` from `1`, `m` steps. -/
def padFold (c z : ℕ → E) : ℕ → E
  | 0 => 1
  | m + 1 => c m * z m + (c m + z m) * padFold c z m

theorem zipIdx_take_succ {α : Type} (l : List α) (m : ℕ) (hm : m < l.length) :
    (l.take (m + 1)).zipIdx = (l.take m).zipIdx ++ [(l[m], m)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, List.zipIdx_append]
  simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hm)]

/-- `paddingWeight` (V:713) is the guest's fold over the complements, times the top's
complement. -/
theorem paddingWeight_eq (zs : List E) (n : ℕ) :
    paddingWeight zs n = (1 + bitE (n.testBit zs.length)) *
      padFold (fun k => bitE (!n.testBit k)) (fun k => zs.getD k 0) zs.length := by
  rw [paddingWeight, eOfNat_shift_mod]
  congr 1
  have key : ∀ m ≤ zs.length, (zs.take m).zipIdx.foldl (fun pad (r, k) ↦
      let b := eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) 1 =
      padFold (fun k => bitE (!n.testBit k)) (fun k => zs.getD k 0) m := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [zipIdx_take_succ zs m (by omega), List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, padFold, eOfNat_shift_mod, one_add_bitE,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m < zs.length by omega),
        Option.getD_some]
  rw [← key zs.length le_rfl, List.take_length]

/-! ## `lead` and `rest` -/

/-- `lead`: the top bit and the one below it, which are never both set. -/
def pwLead (τ n : ℕ) : E := if τ = 0 then 1 else bitE (n.testBit τ) + bitE (n.testBit (τ - 1))

/-- `rest`: the top bit and the bits below `τ - 1`. -/
def pwRest (τ n : ℕ) : E := if τ = 0 then 1 else bitE (n.testBit τ) + eOfNat (n % 2 ^ (τ - 1))

/-- **`lead = 1 ∧ rest ≠ 0` certifies the height** (G:1555-1557): for `n ≤ 2^τ`, `τ` is the
least height holding `n` rows, `log2Ceil n` (V:695). -/
theorem lead_rest_iff {τ n : ℕ} (hτ : τ < 64) (hn : n ≤ 2 ^ τ) :
    pwLead τ n = 1 ∧ pwRest τ n ≠ 0 ↔ log2Ceil n = τ := by
  rcases Nat.eq_zero_or_pos τ with rfl | hτ0
  · simp only [pwLead, pwRest, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true, and_self,
      true_iff]
    have := log2Ceil_le_iff.mpr hn
    omega
  have hsplit : log2Ceil n = τ ↔ 2 ^ (τ - 1) < n := by
    have h1 := log2Ceil_le_iff.mpr hn
    have h2 := @lt_log2Ceil_iff n (τ - 1)
    omega
  rw [hsplit]
  simp only [pwLead, pwRest, Nat.ne_of_gt hτ0, ↓reduceIte]
  have hp : 2 ^ τ = 2 * 2 ^ (τ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hτ0]
  rcases Nat.lt_or_ge n (2 ^ τ) with h | h
  · rw [Nat.testBit_lt_two_pow h]
    simp only [bitE, Bool.false_eq_true, ↓reduceIte, zero_add, ne_eq]
    have hb : n.testBit (τ - 1) = decide (2 ^ (τ - 1) ≤ n) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have : n / 2 ^ (τ - 1) < 2 := Nat.div_lt_of_lt_mul (by rw [mul_comm, ← hp]; exact h)
      by_cases hc : 2 ^ (τ - 1) ≤ n
      · have : 1 ≤ n / 2 ^ (τ - 1) := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega)
        simp [hc, show n / 2 ^ (τ - 1) = 1 by omega]
      · have : n / 2 ^ (τ - 1) = 0 := Nat.div_eq_of_lt (by omega)
        simp [hc, this]
    have hm : eOfNat (n % 2 ^ (τ - 1)) = 0 ↔ n % 2 ^ (τ - 1) = 0 := by
      rw [← eOfNat_zero]
      exact ⟨fun h' => eOfNat_inj (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by decide) (by omega))) (by decide) h', fun h' => by rw [h']⟩
    rw [hb, hm]
    have hmod : n % 2 ^ (τ - 1) = n - 2 ^ (τ - 1) ∨ n < 2 ^ (τ - 1) := by
      by_cases hc : 2 ^ (τ - 1) ≤ n
      · left; rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
      · right; omega
    by_cases hc : 2 ^ (τ - 1) ≤ n <;> simp [hc] <;> omega
  · have hn' : n = 2 ^ τ := by omega
    subst hn'
    have hlt : 2 ^ (τ - 1) < 2 ^ τ := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [Nat.testBit_two_pow_self, Nat.testBit_two_pow, hp, Nat.mul_mod_left]
    simp [bitE, show τ ≠ τ - 1 by omega, eOfNat_zero, hlt, ← hp]

/-! ## The meaning -/

/-- **`padding_weight(rows, zeta, τ)`** (G:1441-1472; TRIAGE #38): `rows` is a row count
`n ≤ 2^τ`, the `τ` words `zs` lie at `zeta`, and the function returns `paddingWeight zs n`
(V:713) with `lead` and `rest` (`lead_rest_iff`). -/
def MeaningPaddingWeight (τ : ℕ) (rd : Reader) : List E → List E → Prop
  | [rows, zeta], rets => ∃ n zs, n ≤ 2 ^ τ ∧ rows = eOfNat n ∧ zs.length = τ ∧
      ReadsAt rd zeta zs ∧ rets = [paddingWeight zs n, pwLead τ n, pwRest τ n]
  | _, _ => False


/-! ## The template's conditions -/

section
variable {C : CallRel} {rd : Reader} {σ : Val}

/-- What the fold's step `k ≥ 1` asks of a valuation. -/
def PwStepOk (rd : Reader) (σ : Val) (τ k : ℕ) : Prop :=
  σ (.n (4 + k)) = σ (.n (4 + k)) * σ (.n (4 + k)) ∧
    LoadHolds rd (σ (.n 1)) k (σ (.n (τ + 4 + 5 * k))) ∧
    σ (.n (τ + 5 + 5 * k)) = σ (.n (4 + k)) * σ (.n (τ + 4 + 5 * k)) ∧
    σ (.n (τ + 6 + 5 * k)) = σ (.n (4 + k)) + σ (.n (τ + 4 + 5 * k)) ∧
    σ (.n (τ + 7 + 5 * k)) = σ (.n (τ + 6 + 5 * k)) * σ (.n (τ + 3 + 5 * k)) ∧
    σ (.n (τ + 8 + 5 * k)) = σ (.n (τ + 5 + 5 * k)) + σ (.n (τ + 7 + 5 * k))

theorem holds_pwStep (τ k : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (pwStep τ k) True kret ↔ PwStepOk rd σ τ k := by
  simp only [pwStep, PwStepOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

/-- What Horner step `j` asks of a valuation. -/
def PwHornOk (σ : Val) (τ j : ℕ) : Prop :=
  σ (.n (6 * τ + 4 + 3 * j)) = word 2 0 0 ∧
    σ (.n (6 * τ + 5 + 3 * j)) = σ (.n (pwBelow τ j)) * σ (.n (6 * τ + 4 + 3 * j)) ∧
    σ (.n (6 * τ + 6 + 3 * j)) = σ (.n (6 * τ + 5 + 3 * j)) + σ (.n (τ + 1 - j))

theorem holds_pwHorner (τ j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (pwHorner τ j) True kret ↔ PwHornOk σ τ j := by
  simp only [pwHorner, PwHornOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

/-- The tail's value `i`, from `L = 9τ - 2`. -/
abbrev pwS (σ : Val) (τ i : ℕ) : E := σ (.n (9 * τ - 2 + i))

/-- What the tail asks of a valuation, its returns `rets`. -/
def PwTailOk (σ : Val) (τ : ℕ) (rets : List E) : Prop :=
  pwS σ τ 0 = word (2 ^ (τ - 1)) 0 0 ∧ pwS σ τ 1 = σ (.n (3 + τ)) * pwS σ τ 0 ∧
    pwS σ τ 2 = σ (.n (pwBelow τ (τ - 2))) + pwS σ τ 1 ∧ pwS σ τ 3 = word 1 0 0 ∧
    pwS σ τ 4 = σ (.n (4 + τ)) + pwS σ τ 3 ∧ pwS σ τ 5 = pwS σ τ 4 + σ (.n (3 + τ)) ∧
    pwS σ τ 6 = σ (.n (4 + τ)) + σ (.n (pwBelow τ (τ - 2))) ∧
    pwS σ τ 7 = word (2 ^ (τ - 1) - 1) 0 0 ∧ pwS σ τ 8 = pwS σ τ 6 + pwS σ τ 7 ∧
    pwS σ τ 9 = word (2 ^ τ) 0 0 ∧ pwS σ τ 10 = σ (.n (4 + τ)) * pwS σ τ 9 ∧
    pwS σ τ 11 = pwS σ τ 2 + pwS σ τ 10 ∧ pwS σ τ 11 + σ (.n 3) = 0 ∧
    pwS σ τ 12 = word (2 ^ τ - 1) 0 0 ∧ pwS σ τ 13 = pwS σ τ 2 + pwS σ τ 12 ∧
    pwS σ τ 14 = σ (.n (4 + τ)) * pwS σ τ 13 ∧ pwS σ τ 15 = word 0 0 0 ∧
    pwS σ τ 14 + pwS σ τ 15 = 0 ∧ pwS σ τ 16 = word 1 0 0 ∧
    pwS σ τ 17 = pwS σ τ 16 + σ (.n (4 + τ)) ∧ pwS σ τ 18 = pwS σ τ 17 * σ (.n (6 * τ + 3)) ∧
    pwS σ τ 19 = pwS σ τ 5 ∧ pwS σ τ 20 = pwS σ τ 8 ∧ [pwS σ τ 18, pwS σ τ 19, pwS σ τ 20] = rets

theorem holds_pwTail (τ : ℕ) (next : Prop) (rets : List E) :
    Stmt.HoldsList C rd σ (pwTail τ) next (fun rs => rs = rets) ↔ PwTailOk σ τ rets := by
  simp only [pwTail, PwTailOk, pwS, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil, Nat.add_zero]

/-- The function's body, simplified to its conditions. -/
theorem pw_unfold {name : String} {f : Fn} (τ : ℕ) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = pwBody τ) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ ∃ σ : Val, [σ (.n 0), σ (.n 1)] = args ∧
      σ (.n 2) = word (2 ^ τ - 1) 0 0 ∧ σ (.n 3) = σ (.n 0) + σ (.n 2) ∧
      σ (.n 4) = σ (.n 4) * σ (.n 4) ∧ LoadHolds rd (σ (.n 1)) 0 (σ (.n (τ + 5))) ∧
      σ (.n (τ + 6)) = σ (.n 4) * σ (.n (τ + 5)) ∧ σ (.n (τ + 7)) = σ (.n 4) + σ (.n (τ + 5)) ∧
      σ (.n (τ + 8)) = σ (.n (τ + 6)) + σ (.n (τ + 7)) ∧
      (∀ i < τ - 1, PwStepOk rd σ τ (i + 1)) ∧
      σ (.n (4 + τ)) = σ (.n (4 + τ)) * σ (.n (4 + τ)) ∧
      (∀ j < τ - 2, PwHornOk σ τ j) ∧ PwTailOk σ τ rets := by
  rw [rel_iff_sem hfind, hbody, hparams, pwBody]
  simp only [holdsList_append, holdsList_range_flatten (τ - 1) (fun i => pwStep τ (i + 1))
    (fun _ => rfl), holdsList_range_flatten (τ - 2) (pwHorner τ) (fun _ => rfl), holds_pwStep,
    holds_pwHorner, holds_pwTail, pwHead, pwStep0, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil, true_and]

end

/-! ## Soundness -/

/-- The value number of the fold's word `k`. -/
def pwZ (τ k : ℕ) : ℕ := if k = 0 then τ + 5 else τ + 4 + 5 * k

/-- The guest's Horner recursion over the bits below `τ - 1`. -/
def pwBl (b : ℕ → E) (τ : ℕ) : ℕ → E
  | 0 => b (τ - 2)
  | j + 1 => pwBl b τ j * gen + b (τ - 3 - j)

theorem pwBl_eq (b : ℕ → E) {τ : ℕ} (hτ : 2 ≤ τ) :
    ∀ j ≤ τ - 2, pwBl b τ j = ∑ i ∈ Finset.range (j + 1), b (τ - 2 - j + i) * gen ^ i
  | 0, _ => by simp [pwBl]
  | j + 1, hj => by
    rw [pwBl, pwBl_eq b hτ j (by omega), Finset.sum_mul, Finset.sum_range_succ' _ (j + 1),
      pow_zero, mul_one]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) ?_
    · rw [mul_assoc, ← pow_succ, show τ - 2 - (j + 1) + (i + 1) = τ - 2 - j + i by omega]
    · rw [show τ - 2 - (j + 1) + 0 = τ - 3 - j by omega]

theorem pwBl_top (b : ℕ → E) {τ : ℕ} (hτ : 2 ≤ τ) :
    pwBl b τ (τ - 2) = ∑ i ∈ Finset.range (τ - 1), b i * gen ^ i := by
  rw [pwBl_eq b hτ _ le_rfl, show τ - 2 + 1 = τ - 1 by omega]
  exact Finset.sum_congr rfl fun i _ => by rw [show τ - 2 - (τ - 2) + i = i by omega]

/-- The three returns, from bits of `pwW τ n` and the words `zs`. -/
theorem pw_rets {τ n : ℕ} (h2 : 2 ≤ τ) (h28 : τ ≤ 28) {b z : ℕ → E}
    (hbits : ∀ k ≤ τ, b k = bitE ((pwW τ n).testBit k)) {zs : List E} (hlen : zs.length = τ)
    (hzs : ∀ k < τ, z k = zs.getD k 0) :
    [(word 1 0 0 + b τ) * padFold b z τ, b τ + word 1 0 0 + b (τ - 1),
        b τ + pwBl b τ (τ - 2) + word (2 ^ (τ - 1) - 1) 0 0] =
      [paddingWeight zs n, pwLead τ n, pwRest τ n] := by
  have hcomp : ∀ k < τ, b k = bitE (!n.testBit k) := fun k hk => by
    rw [hbits k (by omega), testBit_pwW]; simp [hk]
  have htopb : b τ = bitE (n.testBit τ) := by rw [hbits τ le_rfl, testBit_pwW]; simp
  have hpf : padFold b z τ = padFold (fun k => bitE (!n.testBit k)) (fun k => zs.getD k 0) τ := by
    have : ∀ m ≤ τ, padFold b z m =
        padFold (fun k => bitE (!n.testBit k)) (fun k => zs.getD k 0) m := by
      intro m hm
      induction m with
      | zero => rfl
      | succ m ih => rw [padFold, padFold, ih (by omega), hcomp m (by omega), hzs m (by omega)]
    exact this τ le_rfl
  have hbelow : pwBl b τ (τ - 2) = eOfNat ((n % 2 ^ (τ - 1)) ^^^ (2 ^ (τ - 1) - 1)) := by
    rw [pwBl_top b h2, ← Nat.mod_eq_of_lt (Nat.xor_lt_two_pow
      (Nat.mod_lt n (Nat.two_pow_pos (τ - 1))) (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)),
      ← sum_testBit_gen_pow _ (τ - 1) (by omega)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [hcomp k (by omega), Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
    simp [hk']
  simp only [pwLead, pwRest, Nat.ne_of_gt (show 0 < τ by omega), ↓reduceIte]
  rw [paddingWeight_eq, hlen, hpf, htopb, hcomp (τ - 1) (by omega), hbelow, word_one,
    word_eOfNat, add_assoc (bitE (n.testBit τ)) (eOfNat _) _, ← eOfNat_xor, Nat.xor_assoc,
    Nat.xor_self, Nat.xor_zero]
  refine List.cons_eq_cons.mpr ⟨by ring, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
  rw [add_assoc, one_add_bitE, Bool.not_not]

theorem pw_sound {name : String} {f : Fn} (τ : ℕ) (h2 : 2 ≤ τ) (h28 : τ ≤ 28)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = pwBody τ) (rd : Reader) (rows zeta : E) (rets : List E)
    (h : coreProgram.Rel rd name [rows, zeta] rets) :
    MeaningPaddingWeight τ rd [rows, zeta] rets := by
  rw [pw_unfold τ hfind hparams hbody] at h
  obtain ⟨σ, hp, e2, e3, s0b, s0l, s0m, s0a, s0p, hsteps, htop, hhorn, ht⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1⟩ := hp
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, a11, t12, t13, t14, t15, a14, t16,
    t17, t18, t19, t20, hret⟩ := ht
  set b : ℕ → E := fun k => σ (.n (4 + k))
  set z : ℕ → E := fun k => σ (.n (pwZ τ k))
  have hb : ∀ k ≤ τ, b k * b k = b k := fun k hk => by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact s0b.symm
    rcases Nat.lt_or_ge k τ with hkτ | hkτ
    · obtain ⟨e, -⟩ := hsteps (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at e
      exact e.symm
    · rw [show k = τ by omega]; exact htop.symm
  have hz : ∀ k < τ, LoadHolds rd (σ (.n 1)) k (z k) := fun k hk => by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact s0l
    · obtain ⟨-, e, -⟩ := hsteps (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at e
      simp only [z, pwZ, Nat.ne_of_gt hk0, ↓reduceIte]
      exact e
  have hpad : ∀ k < τ, σ (.n (τ + 8 + 5 * k)) = padFold b z (k + 1) := fun k hk => by
    induction k with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, padFold, mul_one]
      rw [s0p, s0m, s0a]
      rfl
    | succ k ih =>
      obtain ⟨-, -, em, ea, ep, eq⟩ := hsteps k (by omega)
      rw [padFold, ← ih (by omega)]
      rw [eq, em, ep, ea, show τ + 3 + 5 * (k + 1) = τ + 8 + 5 * k by ring]
      simp only [b, z, pwZ, Nat.succ_ne_zero, ↓reduceIte]
  have hbl : ∀ j ≤ τ - 2, σ (.n (pwBelow τ j)) = pwBl b τ j := fun j hj => by
    induction j with
    | zero => simp only [pwBelow, ↓reduceIte, pwBl, b]; congr 2; omega
    | succ j ih =>
      obtain ⟨c, m, a⟩ := hhorn j (by omega)
      rw [pwBl, ← ih (by omega), show pwBelow τ (j + 1) = 6 * τ + 6 + 3 * j by
        simp only [pwBelow, Nat.succ_ne_zero, ↓reduceIte]; ring, a, m, c, word_gen]
      simp only [b]; congr 3; omega
  have hlow : pwS σ τ 2 = ∑ k ∈ Finset.range τ, b k * gen ^ k := by
    rw [t2, t1, t0, hbl _ le_rfl, pwBl_top b h2, word_two_pow (by omega),
      show τ = τ - 1 + 1 by omega, Finset.sum_range_succ, show τ - 1 + 1 - 1 = τ - 1 by omega]
    simp only [b]; rw [show 3 + (τ - 1 + 1) = 4 + (τ - 1) by omega]
  have hrec : ∑ k ∈ Finset.range (τ + 1), b k * gen ^ k = σ (.n 0) + eOfNat (2 ^ τ - 1) := by
    rw [Finset.sum_range_succ, ← hlow, show σ (.n 0) + eOfNat (2 ^ τ - 1) = σ (.n 3) by
      rw [e3, e2, word_eOfNat], ← e_add_eq_zero_iff.mp a11, t11, t10, t9, word_two_pow (by omega)]
  have htop' : b τ * (∑ k ∈ Finset.range τ, b k * gen ^ k + eOfNat (2 ^ τ - 1)) = 0 := by
    rw [← hlow, ← word_eOfNat, ← t12, ← t13, ← t14]
    rw [t15, word_zero, add_zero] at a14
    exact a14
  obtain ⟨n, hn, hrows, hbits⟩ := pw_bits (by omega) hb hrec htop'
  rw [h0] at hrows
  set zs := (List.range τ).map z
  have hzs : ∀ k < τ, z k = zs.getD k 0 := fun k hk => by simp [zs, hk]
  have hlen : zs.length = τ := by simp [zs]
  refine ⟨n, zs, hn, hrows, hlen, fun k hk => ?_, ?_⟩
  · have hk' : k < τ := hlen ▸ hk
    have := hz k hk'
    rw [hzs k hk', h1] at this
    simpa [List.getD_eq_getElem?_getD, hk] using this
  have hb1 : σ (.n (3 + τ)) = b (τ - 1) := by simp only [b]; congr 2; omega
  rw [← hret, t18, t17, t16, show 6 * τ + 3 = τ + 8 + 5 * (τ - 1) by omega,
    hpad (τ - 1) (by omega), show τ - 1 + 1 = τ by omega, t19, t5, t4, t3, t20, t8, t7, t6, hb1,
    hbl _ le_rfl]
  exact pw_rets h2 h28 hbits hlen hzs

/-! ## Completeness -/

/-- The tail's honest values. -/
def pwTailVals (τ : ℕ) (b z : ℕ → E) : List E :=
  let top := b τ
  let b1 := b (τ - 1)
  let bl := pwBl b τ (τ - 2)
  let low := bl + b1 * word (2 ^ (τ - 1)) 0 0
  [word (2 ^ (τ - 1)) 0 0, b1 * word (2 ^ (τ - 1)) 0 0, low, word 1 0 0, top + word 1 0 0,
    top + word 1 0 0 + b1, top + bl, word (2 ^ (τ - 1) - 1) 0 0,
    top + bl + word (2 ^ (τ - 1) - 1) 0 0, word (2 ^ τ) 0 0, top * word (2 ^ τ) 0 0,
    low + top * word (2 ^ τ) 0 0, word (2 ^ τ - 1) 0 0, low + word (2 ^ τ - 1) 0 0,
    top * (low + word (2 ^ τ - 1) 0 0), word 0 0 0, word 1 0 0, word 1 0 0 + top,
    (word 1 0 0 + top) * padFold b z τ, top + word 1 0 0 + b1,
    top + bl + word (2 ^ (τ - 1) - 1) 0 0]

/-- The honest value of value number `i`, at `τ ≥ 2`. -/
def pwF (τ : ℕ) (rows zeta : E) (b z : ℕ → E) (i : ℕ) : E :=
  if i < 4 then [rows, zeta, word (2 ^ τ - 1) 0 0, rows + word (2 ^ τ - 1) 0 0].getD i 0
  else if i < τ + 5 then b (i - 4)
  else if i < 6 * τ + 4 then
    let k := (i - (τ + 4)) / 5
    if k = 0 then [0, z 0, b 0 * z 0, b 0 + z 0, padFold b z 1].getD ((i - (τ + 4)) % 5) 0
    else [z k, b k * z k, b k + z k, (b k + z k) * padFold b z k, padFold b z (k + 1)].getD
      ((i - (τ + 4)) % 5) 0
  else if i < 9 * τ - 2 then
    let j := (i - (6 * τ + 4)) / 3
    [word 2 0 0, pwBl b τ j * word 2 0 0, pwBl b τ (j + 1)].getD ((i - (6 * τ + 4)) % 3) 0
  else (pwTailVals τ b z).getD (i - (9 * τ - 2)) 0

section
variable {τ : ℕ} {rows zeta : E} {b z : ℕ → E}

theorem pwF_lt4 {i : ℕ} (hi : i < 4) :
    pwF τ rows zeta b z i = [rows, zeta, word (2 ^ τ - 1) 0 0, rows + word (2 ^ τ - 1) 0 0].getD i 0 := by
  rw [pwF, ite_pos' hi]

theorem pwF_bit {k : ℕ} (hk : k ≤ τ) : pwF τ rows zeta b z (4 + k) = b k := by
  rw [pwF, ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel_left]

theorem pwF_s0 {r : ℕ} (hr1 : 1 ≤ r) (hr : r < 5) (hτ : 2 ≤ τ) :
    pwF τ rows zeta b z (τ + 4 + r) =
      [0, z 0, b 0 * z 0, b 0 + z 0, padFold b z 1].getD r 0 := by
  rw [pwF, ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
  simp only
  rw [ite_pos' (by omega), show (τ + 4 + r - (τ + 4)) % 5 = r by omega]

theorem pwF_step {k r : ℕ} (hk1 : 1 ≤ k) (hk : k < τ) (hr : r < 5) :
    pwF τ rows zeta b z (τ + 4 + 5 * k + r) = [z k, b k * z k, b k + z k,
      (b k + z k) * padFold b z k, padFold b z (k + 1)].getD r 0 := by
  rw [pwF, ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
  simp only
  rw [ite_neg' (by omega), show (τ + 4 + 5 * k + r - (τ + 4)) / 5 = k by omega,
    show (τ + 4 + 5 * k + r - (τ + 4)) % 5 = r by omega]

theorem pwF_horn {j r : ℕ} (hj : j < τ - 2) (hr : r < 3) :
    pwF τ rows zeta b z (6 * τ + 4 + 3 * j + r) =
      [word 2 0 0, pwBl b τ j * word 2 0 0, pwBl b τ (j + 1)].getD r 0 := by
  rw [pwF, ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
  simp only
  rw [show (6 * τ + 4 + 3 * j + r - (6 * τ + 4)) / 3 = j by omega,
    show (6 * τ + 4 + 3 * j + r - (6 * τ + 4)) % 3 = r by omega]

theorem pwF_tail (hτ : 2 ≤ τ) (r : ℕ) :
    pwF τ rows zeta b z (9 * τ - 2 + r) = (pwTailVals τ b z).getD r 0 := by
  rw [pwF, ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    Nat.add_sub_cancel_left]

theorem pwF_below (hτ : 2 ≤ τ) {j : ℕ} (hj : j ≤ τ - 2) :
    pwF τ rows zeta b z (pwBelow τ j) = pwBl b τ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [pwBelow, ↓reduceIte]
    rw [show τ + 2 = 4 + (τ - 2) by omega, pwF_bit (by omega)]; rfl
  · simp only [pwBelow, Nat.ne_of_gt hj0, ↓reduceIte]
    rw [show 6 * τ + 3 + 3 * j = 6 * τ + 4 + 3 * (j - 1) + 2 by omega, pwF_horn (by omega)
      (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [show j - 1 + 1 = j by omega]

end

theorem pwF_s0' {τ : ℕ} {rows zeta : E} {b z : ℕ → E} {i r : ℕ} (hi : i = τ + 4 + r)
    (hr1 : 1 ≤ r) (hr : r < 5) (hτ : 2 ≤ τ) :
    pwF τ rows zeta b z i = [0, z 0, b 0 * z 0, b 0 + z 0, padFold b z 1].getD r 0 := by
  subst hi; exact pwF_s0 hr1 hr hτ

theorem pwF_step' {τ : ℕ} {rows zeta : E} {b z : ℕ → E} {i k r : ℕ}
    (hi : i = τ + 4 + 5 * k + r) (hk1 : 1 ≤ k) (hk : k < τ) (hr : r < 5) :
    pwF τ rows zeta b z i = [z k, b k * z k, b k + z k,
      (b k + z k) * padFold b z k, padFold b z (k + 1)].getD r 0 := by
  subst hi; exact pwF_step hk1 hk hr

theorem pwF_horn' {τ : ℕ} {rows zeta : E} {b z : ℕ → E} {i j r : ℕ}
    (hi : i = 6 * τ + 4 + 3 * j + r) (hj : j < τ - 2) (hr : r < 3) :
    pwF τ rows zeta b z i = [word 2 0 0, pwBl b τ j * word 2 0 0, pwBl b τ (j + 1)].getD r 0 := by
  subst hi; exact pwF_horn hj hr

theorem pwF_bit' {τ : ℕ} {rows zeta : E} {b z : ℕ → E} {i k : ℕ} (hi : i = 4 + k) (hk : k ≤ τ) :
    pwF τ rows zeta b z i = b k := by
  subst hi; exact pwF_bit hk

theorem pw_complete {name : String} {f : Fn} (τ : ℕ) (h2 : 2 ≤ τ) (h28 : τ ≤ 28)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = pwBody τ) (rd : Reader) (rows zeta : E) (rets : List E)
    (h : MeaningPaddingWeight τ rd [rows, zeta] rets) :
    coreProgram.Rel rd name [rows, zeta] rets := by
  obtain ⟨n, zs, hn, hrows, hlen, hread, hret⟩ := h
  rw [pw_unfold τ hfind hparams hbody]
  set b : ℕ → E := fun k => bitE ((pwW τ n).testBit k)
  set z : ℕ → E := fun k => zs.getD k 0
  set F := pwF τ rows zeta b z
  have hbool : ∀ k, b k = b k * b k := fun k => (bitE_mul_self _).symm
  have hz : ∀ k < τ, LoadHolds rd zeta k (z k) := fun k hk => by
    have := hread k (by omega)
    simpa [z, List.getD_eq_getElem?_getD, show k < zs.length by omega] using this
  obtain ⟨hrec, htop⟩ := pw_bits_complete (show τ < 63 by omega) hn
  have hlow : pwBl b τ (τ - 2) + b (τ - 1) * word (2 ^ (τ - 1)) 0 0 =
      ∑ k ∈ Finset.range τ, b k * gen ^ k := by
    rw [pwBl_top b h2, word_two_pow (by omega), show τ = τ - 1 + 1 by omega,
      Finset.sum_range_succ, show τ - 1 + 1 - 1 = τ - 1 by omega]
  have f0 : F 0 = rows := pwF_lt4 (by omega)
  have f1 : F 1 = zeta := pwF_lt4 (by omega)
  have f2 : F 2 = word (2 ^ τ - 1) 0 0 := pwF_lt4 (by omega)
  have f3 : F 3 = rows + word (2 ^ τ - 1) 0 0 := pwF_lt4 (by omega)
  have fb : ∀ k ≤ τ, F (4 + k) = b k := fun k hk => pwF_bit hk
  have s1 : F (τ + 5) = z 0 := pwF_s0' (r := 1) (by omega) (by omega) (by omega) h2
  have s2 : F (τ + 6) = b 0 * z 0 := pwF_s0' (r := 2) (by omega) (by omega) (by omega) h2
  have s3 : F (τ + 7) = b 0 + z 0 := pwF_s0' (r := 3) (by omega) (by omega) (by omega) h2
  have s4 : F (τ + 8) = padFold b z 1 := pwF_s0' (r := 4) (by omega) (by omega) (by omega) h2
  have t := fun r => pwF_tail (rows := rows) (zeta := zeta) (b := b) (z := z) h2 r
  refine ⟨fun v => F v.idx, ?_, f2, by show F 3 = F 0 + F 2; rw [f3, f0, f2], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · show [F 0, F 1] = [rows, zeta]; rw [f0, f1]
  · show F 4 = F 4 * F 4; rw [fb 0 (by omega)]; exact hbool 0
  · show LoadHolds rd (F 1) 0 (F (τ + 5)); rw [f1, s1]; exact hz 0 (by omega)
  · show F (τ + 6) = F 4 * F (τ + 5); rw [s2, fb 0 (by omega), s1]
  · show F (τ + 7) = F 4 + F (τ + 5); rw [s3, fb 0 (by omega), s1]
  · show F (τ + 8) = F (τ + 6) + F (τ + 7); rw [s4, s2, s3]; simp only [padFold, mul_one]
  · intro i hi
    have hk1 : 1 ≤ i + 1 := by omega
    have hk : i + 1 < τ := by omega
    have r0 : F (τ + 4 + 5 * (i + 1)) = z (i + 1) := pwF_step' (r := 0) (by omega) hk1 hk (by omega)
    have r1 : F (τ + 5 + 5 * (i + 1)) = b (i + 1) * z (i + 1) :=
      pwF_step' (r := 1) (by omega) hk1 hk (by omega)
    have r2 : F (τ + 6 + 5 * (i + 1)) = b (i + 1) + z (i + 1) :=
      pwF_step' (r := 2) (by omega) hk1 hk (by omega)
    have r3 : F (τ + 7 + 5 * (i + 1)) = (b (i + 1) + z (i + 1)) * padFold b z (i + 1) :=
      pwF_step' (r := 3) (by omega) hk1 hk (by omega)
    have r4 : F (τ + 8 + 5 * (i + 1)) = padFold b z (i + 1 + 1) :=
      pwF_step' (r := 4) (by omega) hk1 hk (by omega)
    have hp : F (τ + 3 + 5 * (i + 1)) = padFold b z (i + 1) := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact pwF_s0' (r := 4) (by omega) (by omega) (by omega) h2
      · have this : F (τ + 3 + 5 * (i + 1)) = _ := pwF_step' (τ := τ) (rows := rows) (zeta := zeta) (b := b) (z := z) (i := τ + 3 + 5 * (i + 1))
          (k := i) (r := 4) (by omega) (by omega) (by omega) (by omega)
        rw [this]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show F (4 + (i + 1)) = F (4 + (i + 1)) * F (4 + (i + 1))
      rw [fb (i + 1) (by omega)]; exact hbool _
    · show LoadHolds rd (F 1) (i + 1) (F (τ + 4 + 5 * (i + 1)))
      rw [f1, r0]; exact hz _ hk
    · show F (τ + 5 + 5 * (i + 1)) = F (4 + (i + 1)) * F (τ + 4 + 5 * (i + 1))
      rw [r1, fb (i + 1) (by omega), r0]
    · show F (τ + 6 + 5 * (i + 1)) = F (4 + (i + 1)) + F (τ + 4 + 5 * (i + 1))
      rw [r2, fb (i + 1) (by omega), r0]
    · show F (τ + 7 + 5 * (i + 1)) = F (τ + 6 + 5 * (i + 1)) * F (τ + 3 + 5 * (i + 1))
      rw [r3, r2, hp]
    · show F (τ + 8 + 5 * (i + 1)) = F (τ + 5 + 5 * (i + 1)) + F (τ + 7 + 5 * (i + 1))
      rw [r4, r1, r3]; rfl
  · show F (4 + τ) = F (4 + τ) * F (4 + τ)
    rw [fb _ le_rfl]; exact hbool _
  · intro j hj
    have q0 : F (6 * τ + 4 + 3 * j) = word 2 0 0 := pwF_horn' (r := 0) (by omega) hj (by omega)
    have q1 : F (6 * τ + 5 + 3 * j) = pwBl b τ j * word 2 0 0 :=
      pwF_horn' (r := 1) (by omega) hj (by omega)
    have q2 : F (6 * τ + 6 + 3 * j) = pwBl b τ (j + 1) := pwF_horn' (r := 2) (by omega) hj (by omega)
    have qb : F (τ + 1 - j) = b (τ - 3 - j) := pwF_bit' (k := τ - 3 - j) (by omega) (by omega)
    refine ⟨q0, ?_, ?_⟩
    · show F (6 * τ + 5 + 3 * j) = F (pwBelow τ j) * F (6 * τ + 4 + 3 * j)
      rw [q1, q0, show F (pwBelow τ j) = pwBl b τ j from pwF_below h2 (by omega)]
    · show F (6 * τ + 6 + 3 * j) = F (6 * τ + 5 + 3 * j) + F (τ + 1 - j)
      rw [q2, q1, qb, pwBl, word_gen]
  · have hbl : F (pwBelow τ (τ - 2)) = pwBl b τ (τ - 2) := pwF_below h2 le_rfl
    have hb1 : F (3 + τ) = b (τ - 1) := pwF_bit' (k := τ - 1) (by omega) (by omega)
    have hbt : F (4 + τ) = b τ := pwF_bit le_rfl
    have hp : F (6 * τ + 3) = padFold b z τ := by
      have this : F (6 * τ + 3) = _ := pwF_step' (τ := τ) (rows := rows) (zeta := zeta) (b := b) (z := z) (i := 6 * τ + 3)
        (k := τ - 1) (r := 4) (by omega) (by omega) (by omega) (by omega)
      rw [this]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [show τ - 1 + 1 = τ by omega]
    show PwTailOk (fun v => F v.idx) τ rets
    simp only [PwTailOk, pwS, hbl, hb1, hbt, hp, f3]
    simp only [F, t, pwTailVals, List.getD_cons_succ, List.getD_cons_zero, true_and]
    refine ⟨?_, ?_, ?_⟩
    · rw [hlow, word_two_pow (by omega), ← Finset.sum_range_succ, hrec, hrows, word_eOfNat]
      exact e_add_self _
    · rw [hlow, word_eOfNat, word_zero, add_zero]; exact htop
    · rw [hret]
      exact pw_rets h2 h28 (fun k _ => rfl) hlen (fun k _ => rfl)

/-! ## `τ = 0` and `τ = 1` -/

/-- The expansion of `padding_weight` at `τ = 0`. -/
def pwBody0 : List Stmt :=
  [.atom (.hint (.bits (.n 0) 0 1 (.stack [.n 2]))), .atom (.mul (.n 2) (.n 2) (.n 2)),
    .atom (.assertEq (.n 2) (.n 0)), .atom (.const (.n 3) (word 0 0 0)),
    .atom (.mul (.n 4) (.n 2) (.n 3)), .atom (.const (.n 5) (word 0 0 0)),
    .atom (.assertEq (.n 4) (.n 5)), .atom (.const (.n 6) (word 1 0 0)),
    .atom (.add (.n 7) (.n 6) (.n 2)), .atom (.const (.n 8) (word 1 0 0)),
    .atom (.const (.n 9) (word 1 0 0)), .ret [.n 7, .n 8, .n 9]]

/-- The expansion of `padding_weight` at `τ = 1`. -/
def pwBody1 : List Stmt :=
  [.atom (.const (.n 2) (word 1 0 0)), .atom (.add (.n 3) (.n 0) (.n 2)),
    .atom (.hint (.bits (.n 3) 0 2 (.stack [.n 4, .n 5]))), .atom (.mul (.n 4) (.n 4) (.n 4)),
    .atom (.load (.n 6) (.n 1) 0), .atom (.mul (.n 7) (.n 4) (.n 6)),
    .atom (.add (.n 8) (.n 4) (.n 6)), .atom (.add (.n 9) (.n 7) (.n 8)),
    .atom (.mul (.n 5) (.n 5) (.n 5)), .atom (.const (.n 10) (word 1 0 0)),
    .atom (.add (.n 11) (.n 5) (.n 10)), .atom (.add (.n 12) (.n 11) (.n 4)),
    .atom (.const (.n 13) (word 2 0 0)), .atom (.mul (.n 14) (.n 5) (.n 13)),
    .atom (.add (.n 15) (.n 4) (.n 14)), .atom (.assertEq (.n 15) (.n 3)),
    .atom (.const (.n 16) (word 1 0 0)), .atom (.add (.n 17) (.n 4) (.n 16)),
    .atom (.mul (.n 18) (.n 5) (.n 17)), .atom (.const (.n 19) (word 0 0 0)),
    .atom (.assertEq (.n 18) (.n 19)), .atom (.const (.n 20) (word 1 0 0)),
    .atom (.add (.n 21) (.n 20) (.n 5)), .atom (.mul (.n 22) (.n 21) (.n 9)),
    .atom (.copy (.n 23) (.n 12)), .atom (.copy (.n 24) (.n 5)), .ret [.n 22, .n 23, .n 24]]

theorem core42_body : Fn.body Data.core42 = pwBody0 := stmtsEqb_sound (by decide +kernel)

theorem core43_body : Fn.body Data.core43 = pwBody1 := stmtsEqb_sound (by decide +kernel)

theorem pw0_iff {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = pwBody0) (rd : Reader)
    (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd name [rows, zeta] rets ↔ MeaningPaddingWeight 0 rd [rows, zeta] rets := by
  rw [rel_iff_sem hfind, hbody, hparams, pwBody0]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and]
  constructor
  · rintro ⟨σ, hp, hb, a2, h3, h4, h5, a4, h6, h7, h8, h9, hret⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨h0, -⟩ := hp
    have hc := bitE_of_mul_self hb.symm
    set c := decide (σ (.n 2) = 1)
    refine ⟨c.toNat, [], by cases c <;> simp, ?_, rfl, readsAt_nil _ _, ?_⟩
    · rw [← h0, ← e_add_eq_zero_iff.mp a2, hc]; cases c <;> simp [bitE, eOfNat_zero, eOfNat_one]
    · rw [← hret, h7, h6, h8, h9, hc, word_one]
      simp only [paddingWeight, List.length_nil, List.zipIdx_nil, List.foldl_nil, mul_one,
        pwLead, pwRest, ↓reduceIte, Nat.shiftRight_zero]
      cases c <;> simp [bitE, eOfNat_zero, eOfNat_one]
  · rintro ⟨n, zs, hn, hrows, hlen, -, hret⟩
    have hz : zs = [] := List.eq_nil_of_length_eq_zero hlen
    subst hz hret
    refine ⟨fun v => [rows, zeta, rows, 0, 0, 0, 1, 1 + rows, 1, 1].getD v.idx 0, rfl, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [List.getD_cons_succ, List.getD_cons_zero, word_zero, word_one, mul_zero,
      add_zero]
    · rw [hrows]; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;>
        simp [eOfNat_zero, eOfNat_one]
    · exact e_add_self _
    · simp only [paddingWeight, List.length_nil, List.zipIdx_nil, List.foldl_nil, mul_one,
        pwLead, pwRest, ↓reduceIte, Nat.shiftRight_zero, hrows]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> simp

theorem pw1_iff {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = pwBody1) (rd : Reader)
    (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd name [rows, zeta] rets ↔ MeaningPaddingWeight 1 rd [rows, zeta] rets := by
  rw [rel_iff_sem hfind, hbody, hparams, pwBody1]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and]
  constructor
  · rintro ⟨σ, hp, h2, h3, hb0, l6, h7, h8, h9, hb1, h10, h11, h12, h13, h14, h15, a15, h16, h17,
      h18, h19, a18, h20, h21, h22, h23, h24, hret⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨h0, h1⟩ := hp
    set b : ℕ → E := fun k => σ (.n (4 + k))
    have hb : ∀ k ≤ 1, b k * b k = b k := fun k hk => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
      · exact hb0.symm
      · exact hb1.symm
    have hrec : ∑ k ∈ Finset.range (1 + 1), b k * gen ^ k = σ (.n 0) + eOfNat (2 ^ 1 - 1) := by
      rw [show σ (.n 0) + eOfNat (2 ^ 1 - 1) = σ (.n 3) by rw [h3, h2, word_one]; rfl,
        ← e_add_eq_zero_iff.mp a15, h15, h14, h13, word_gen]
      simp [Finset.sum_range_succ, b, mul_comm]
    have htop : b 1 * (∑ k ∈ Finset.range 1, b k * gen ^ k + eOfNat (2 ^ 1 - 1)) = 0 := by
      rw [h19, word_zero, add_zero, h18, h17, h16, word_one] at a18
      simpa [b, eOfNat_one] using a18
    obtain ⟨n, hn, hrows, hbits⟩ := pw_bits (by omega) hb hrec htop
    rw [h0] at hrows
    refine ⟨n, [σ (.n 6)], hn, hrows, rfl, fun k hk => ?_, ?_⟩
    · obtain rfl : k = 0 := by simpa using hk
      rw [← h1]; exact l6
    have e0 : σ (.n 4) = bitE (!n.testBit 0) := by
      rw [show σ (.n 4) = b 0 from rfl, hbits 0 (by omega), testBit_pwW]; simp
    have e1 : σ (.n 5) = bitE (n.testBit 1) := by
      rw [show σ (.n 5) = b 1 from rfl, hbits 1 le_rfl, testBit_pwW]; simp
    rw [← hret, h22, h21, h20, h9, h7, h8, h23, h12, h11, h10, h24, word_one, e0, e1,
      paddingWeight_eq]
    simp only [pwLead, pwRest, Nat.one_ne_zero, ↓reduceIte, List.length_cons, List.length_nil,
      Nat.zero_add, padFold, List.getD_cons_zero, mul_one, Nat.sub_self, pow_zero, Nat.mod_one,
      eOfNat_zero, add_zero]
    rw [add_assoc, show (1 : E) + bitE (!n.testBit 0) = bitE (n.testBit 0) by
      rw [one_add_bitE, Bool.not_not]]
  · rintro ⟨n, zs, hn, hrows, hlen, hread, hret⟩
    obtain ⟨z0, rfl⟩ : ∃ z0, zs = [z0] := List.length_eq_one_iff.mp hlen
    have hz : LoadHolds rd zeta 0 z0 := hread 0 (by simp)
    obtain ⟨hrec, htop⟩ := pw_bits_complete (show 1 < 63 by omega) hn
    set b0 := bitE ((pwW 1 n).testBit 0)
    set b1 := bitE ((pwW 1 n).testBit 1)
    have hrec' : b0 + b1 * gen = rows + 1 := by
      rw [hrows, ← eOfNat_one, ← show eOfNat (2 ^ 1 - 1) = eOfNat 1 from rfl, ← hrec]
      simp [Finset.sum_range_succ, b0, b1, mul_comm]
    have htop' : b1 * (b0 + 1) = 0 := by simpa [b0, b1, eOfNat_one] using htop
    refine ⟨fun v => [rows, zeta, 1, rows + 1, b0, b1, z0, b0 * z0, b0 + z0, b0 * z0 + (b0 + z0),
      1, b1 + 1, b1 + 1 + b0, gen, b1 * gen, b0 + b1 * gen, 1, b0 + 1, b1 * (b0 + 1), 0, 1, 1 + b1,
      (1 + b1) * (b0 * z0 + (b0 + z0)), b1 + 1 + b0, b1].getD v.idx 0, rfl, ?_, rfl, ?_, ?_,
      rfl, rfl, rfl, ?_, ?_, rfl, rfl, ?_, rfl, rfl, ?_, ?_, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl,
      rfl, ?_⟩
    all_goals simp only [List.getD_cons_succ, List.getD_cons_zero]
    · exact word_one.symm
    · exact (bitE_mul_self _).symm
    · exact hz
    · exact (bitE_mul_self _).symm
    · exact word_one.symm
    · exact word_gen.symm
    · rw [hrec']; exact e_add_self _
    · exact word_one.symm
    · exact word_zero.symm
    · rw [htop', add_zero]
    · exact word_one.symm
    · rw [hret, paddingWeight_eq]
      have e0 : b0 = bitE (!n.testBit 0) := by simp only [b0]; rw [testBit_pwW]; simp
      have e1 : b1 = bitE (n.testBit 1) := by simp only [b1]; rw [testBit_pwW]; simp
      simp only [pwLead, pwRest, Nat.one_ne_zero, ↓reduceIte, List.length_cons, List.length_nil,
        Nat.zero_add, padFold, List.getD_cons_zero, mul_one, Nat.sub_self, pow_zero, Nat.mod_one,
        eOfNat_zero, add_zero, e0, e1]
      rw [add_assoc, show (1 : E) + bitE (!n.testBit 0) = bitE (n.testBit 0) by
        rw [one_add_bitE, Bool.not_not]]

/-! ## The specializations -/

/-- **`padding_weight` at every `τ ≤ 28`**, for a compiled function whose body is the
expansion at `τ`. -/
theorem padding_weight_iff {name : String} {f : Fn} (τ : ℕ) (h28 : τ ≤ 28)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = if τ = 0 then pwBody0 else if τ = 1 then pwBody1 else pwBody τ)
    (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd name [rows, zeta] rets ↔ MeaningPaddingWeight τ rd [rows, zeta] rets := by
  rcases Nat.lt_or_ge τ 2 with h | h
  · rcases Nat.lt_or_ge τ 1 with h' | h'
    · obtain rfl : τ = 0 := by omega
      exact pw0_iff hfind hparams hbody rd rows zeta rets
    · obtain rfl : τ = 1 := by omega
      exact pw1_iff hfind hparams hbody rd rows zeta rets
  · rw [ite_neg' (by omega), ite_neg' (by omega)] at hbody
    exact ⟨pw_sound τ h h28 hfind hparams hbody rd rows zeta rets,
      pw_complete τ h h28 hfind hparams hbody rd rows zeta rets⟩

set_option maxRecDepth 100000 in
theorem padding_weight_L0_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L0" [rows, zeta] rets ↔
      MeaningPaddingWeight 0 rd [rows, zeta] rets :=
  padding_weight_iff 0 (by decide) (Program.find?_of_indexOf? (j := 42) (by decide +kernel) rfl)
    rfl (by rw [core42_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L1_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L1" [rows, zeta] rets ↔
      MeaningPaddingWeight 1 rd [rows, zeta] rets :=
  padding_weight_iff 1 (by decide) (Program.find?_of_indexOf? (j := 43) (by decide +kernel) rfl)
    rfl (by rw [core43_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L2_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L2" [rows, zeta] rets ↔
      MeaningPaddingWeight 2 rd [rows, zeta] rets :=
  padding_weight_iff 2 (by decide) (Program.find?_of_indexOf? (j := 44) (by decide +kernel) rfl)
    rfl (by rw [core44_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L3_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L3" [rows, zeta] rets ↔
      MeaningPaddingWeight 3 rd [rows, zeta] rets :=
  padding_weight_iff 3 (by decide) (Program.find?_of_indexOf? (j := 45) (by decide +kernel) rfl)
    rfl (by rw [core45_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L4_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L4" [rows, zeta] rets ↔
      MeaningPaddingWeight 4 rd [rows, zeta] rets :=
  padding_weight_iff 4 (by decide) (Program.find?_of_indexOf? (j := 46) (by decide +kernel) rfl)
    rfl (by rw [core46_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L5_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L5" [rows, zeta] rets ↔
      MeaningPaddingWeight 5 rd [rows, zeta] rets :=
  padding_weight_iff 5 (by decide) (Program.find?_of_indexOf? (j := 47) (by decide +kernel) rfl)
    rfl (by rw [core47_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L6_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L6" [rows, zeta] rets ↔
      MeaningPaddingWeight 6 rd [rows, zeta] rets :=
  padding_weight_iff 6 (by decide) (Program.find?_of_indexOf? (j := 48) (by decide +kernel) rfl)
    rfl (by rw [core48_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L7_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L7" [rows, zeta] rets ↔
      MeaningPaddingWeight 7 rd [rows, zeta] rets :=
  padding_weight_iff 7 (by decide) (Program.find?_of_indexOf? (j := 49) (by decide +kernel) rfl)
    rfl (by rw [core49_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L8_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L8" [rows, zeta] rets ↔
      MeaningPaddingWeight 8 rd [rows, zeta] rets :=
  padding_weight_iff 8 (by decide) (Program.find?_of_indexOf? (j := 50) (by decide +kernel) rfl)
    rfl (by rw [core50_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L9_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L9" [rows, zeta] rets ↔
      MeaningPaddingWeight 9 rd [rows, zeta] rets :=
  padding_weight_iff 9 (by decide) (Program.find?_of_indexOf? (j := 51) (by decide +kernel) rfl)
    rfl (by rw [core51_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L10_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L10" [rows, zeta] rets ↔
      MeaningPaddingWeight 10 rd [rows, zeta] rets :=
  padding_weight_iff 10 (by decide) (Program.find?_of_indexOf? (j := 52) (by decide +kernel) rfl)
    rfl (by rw [core52_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L11_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L11" [rows, zeta] rets ↔
      MeaningPaddingWeight 11 rd [rows, zeta] rets :=
  padding_weight_iff 11 (by decide) (Program.find?_of_indexOf? (j := 53) (by decide +kernel) rfl)
    rfl (by rw [core53_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L12_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L12" [rows, zeta] rets ↔
      MeaningPaddingWeight 12 rd [rows, zeta] rets :=
  padding_weight_iff 12 (by decide) (Program.find?_of_indexOf? (j := 54) (by decide +kernel) rfl)
    rfl (by rw [core54_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L13_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L13" [rows, zeta] rets ↔
      MeaningPaddingWeight 13 rd [rows, zeta] rets :=
  padding_weight_iff 13 (by decide) (Program.find?_of_indexOf? (j := 55) (by decide +kernel) rfl)
    rfl (by rw [core55_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L14_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L14" [rows, zeta] rets ↔
      MeaningPaddingWeight 14 rd [rows, zeta] rets :=
  padding_weight_iff 14 (by decide) (Program.find?_of_indexOf? (j := 56) (by decide +kernel) rfl)
    rfl (by rw [core56_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L15_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L15" [rows, zeta] rets ↔
      MeaningPaddingWeight 15 rd [rows, zeta] rets :=
  padding_weight_iff 15 (by decide) (Program.find?_of_indexOf? (j := 57) (by decide +kernel) rfl)
    rfl (by rw [core57_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L16_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L16" [rows, zeta] rets ↔
      MeaningPaddingWeight 16 rd [rows, zeta] rets :=
  padding_weight_iff 16 (by decide) (Program.find?_of_indexOf? (j := 58) (by decide +kernel) rfl)
    rfl (by rw [core58_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L17_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L17" [rows, zeta] rets ↔
      MeaningPaddingWeight 17 rd [rows, zeta] rets :=
  padding_weight_iff 17 (by decide) (Program.find?_of_indexOf? (j := 59) (by decide +kernel) rfl)
    rfl (by rw [core59_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L18_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L18" [rows, zeta] rets ↔
      MeaningPaddingWeight 18 rd [rows, zeta] rets :=
  padding_weight_iff 18 (by decide) (Program.find?_of_indexOf? (j := 60) (by decide +kernel) rfl)
    rfl (by rw [core60_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L19_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L19" [rows, zeta] rets ↔
      MeaningPaddingWeight 19 rd [rows, zeta] rets :=
  padding_weight_iff 19 (by decide) (Program.find?_of_indexOf? (j := 61) (by decide +kernel) rfl)
    rfl (by rw [core61_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L20_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L20" [rows, zeta] rets ↔
      MeaningPaddingWeight 20 rd [rows, zeta] rets :=
  padding_weight_iff 20 (by decide) (Program.find?_of_indexOf? (j := 62) (by decide +kernel) rfl)
    rfl (by rw [core62_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L21_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L21" [rows, zeta] rets ↔
      MeaningPaddingWeight 21 rd [rows, zeta] rets :=
  padding_weight_iff 21 (by decide) (Program.find?_of_indexOf? (j := 63) (by decide +kernel) rfl)
    rfl (by rw [core63_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L22_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L22" [rows, zeta] rets ↔
      MeaningPaddingWeight 22 rd [rows, zeta] rets :=
  padding_weight_iff 22 (by decide) (Program.find?_of_indexOf? (j := 64) (by decide +kernel) rfl)
    rfl (by rw [core64_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L23_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L23" [rows, zeta] rets ↔
      MeaningPaddingWeight 23 rd [rows, zeta] rets :=
  padding_weight_iff 23 (by decide) (Program.find?_of_indexOf? (j := 65) (by decide +kernel) rfl)
    rfl (by rw [core65_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L24_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L24" [rows, zeta] rets ↔
      MeaningPaddingWeight 24 rd [rows, zeta] rets :=
  padding_weight_iff 24 (by decide) (Program.find?_of_indexOf? (j := 66) (by decide +kernel) rfl)
    rfl (by rw [core66_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L25_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L25" [rows, zeta] rets ↔
      MeaningPaddingWeight 25 rd [rows, zeta] rets :=
  padding_weight_iff 25 (by decide) (Program.find?_of_indexOf? (j := 67) (by decide +kernel) rfl)
    rfl (by rw [core67_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L26_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L26" [rows, zeta] rets ↔
      MeaningPaddingWeight 26 rd [rows, zeta] rets :=
  padding_weight_iff 26 (by decide) (Program.find?_of_indexOf? (j := 68) (by decide +kernel) rfl)
    rfl (by rw [core68_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L27_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L27" [rows, zeta] rets ↔
      MeaningPaddingWeight 27 rd [rows, zeta] rets :=
  padding_weight_iff 27 (by decide) (Program.find?_of_indexOf? (j := 69) (by decide +kernel) rfl)
    rfl (by rw [core69_body]; rfl) rd rows zeta rets

set_option maxRecDepth 100000 in
theorem padding_weight_L28_iff (rd : Reader) (rows zeta : E) (rets : List E) :
    coreProgram.Rel rd "padding_weight__L28" [rows, zeta] rets ↔
      MeaningPaddingWeight 28 rd [rows, zeta] rets :=
  padding_weight_iff 28 (by decide) (Program.find?_of_indexOf? (j := 70) (by decide +kernel) rfl)
    rfl (by rw [core70_body]; rfl) rd rows zeta rets

end
end LeanVM.Guest.B1
