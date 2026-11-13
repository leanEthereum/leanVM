/-
  LeanVM.Guest.B1.Sig.SpWotsGroups

  `sp_wots`'s codeword, sound: each digit group's dispatch takes the arm of its hinted digit word,
  and with the digits those choose each chain's tip is its chain from its start, the product is
  `g` to the digits' sum and the encoding their base-4 number.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsCheck
public import LeanVM.Guest.B1.Sig.Codeword

/-!
# `sp_wots`'s codeword, sound

* `spGroupT_sound`, `spGroupsT_sound`: a group's dispatch runs one arm `k < 4^n`, its selector
  `g^k`; the 21 groups of three digits each do (`SpGroupOK`);
* `spDigitWord σ p` (`logG`, the unique exponent below the arm count), `spDigit σ i`, `spStart σ i`:
  the digits the dispatches take, chain `i`'s digit and the cell its start is hinted in
  (`spStartAt`, `SpWotsLayout`);
* `spCodeword_prod`, `spCodeword_enc`: the arithmetic: the running product is `g` to the digits'
  sum; the running encoding is the `XOR` of the digits' fields (`spX`), whose field at
  `spDigitPos i` is digit `i` (`spX_digit`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## Atoms -/

theorem atomsOnly_iff : ∀ {L : List Stmt}, atomsOnly L = true ↔ ∀ x ∈ L, ∃ a, x = .atom a
  | [] => by simp [atomsOnly]
  | .atom a :: L => by
      simp only [atomsOnly, List.mem_cons, forall_eq_or_imp, atomsOnly_iff]
      exact ⟨fun h => ⟨⟨a, rfl⟩, h⟩, fun h => h.2⟩
  | .ite .. :: _ | .match_ .. :: _ | .call .. :: _ | .callIf .. :: _ | .dispatch .. :: _
  | .ret _ :: _ => by simp [atomsOnly]

theorem spW_atoms : StepAtoms spW := by
  intro i s v c o
  simp only [spW, spWp]
  split <;> rfl

theorem spPre_atoms (fold : Bool) (B : Nat) : atomsOnly (spPre fold B) = true := by
  cases fold <;> rfl

/-! ## The groups -/

/-- **A group's dispatch takes one arm**: what it sets before holds, and some `k < 4^n` is the
selector's exponent, and arm `k`'s atoms hold, from its base. -/
theorem spGroupT_sound {first n : Nat} {fold : Bool} {prodIn encIn : V} {B : Nat} {rest : List Stmt}
    {next : Prop} (h : Stmt.HoldsList C rd σ ((spGroupT first n fold prodIn encIn B).1 ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧ AtomsHold rd σ (spPre fold B) ∧ ∃ k < 4 ^ n,
      σ (.n B) = ofK (addressOfIndex k) ∧
      AtomsHold rd σ (spArmK first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k)).1 :=
  groupD_sound spW_atoms (spPre_atoms fold B) h

/-- **What group `p` establishes**: its digit word `k < 4^n` and its arm's atoms. -/
def SpGroupOK (rd : Reader) (σ : Val) (p : Nat) : Prop :=
  ∃ k < 4 ^ spN p, σ (.n (spState p).2.2) = ofK (addressOfIndex k) ∧
    AtomsHold rd σ (spArmK (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k
      (spArmB (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k)).1

theorem spN_of_lt {p : Nat} (hp : p < 21) : spN p = 3 := by simp [spN, hp]

theorem spN_le (p : Nat) : spN p ≤ 3 := by unfold spN; split <;> omega

/-- **The groups of three digits, sound.** -/
theorem spGroupsT_sound {rest : List Stmt} {next : Prop} : ∀ (m p : Nat), p + m ≤ 21 →
    Stmt.HoldsList C rd σ ((spGroupsT m p (spState p).1 (spState p).2.1 (spState p).2.2).1 ++ rest)
      next kret →
      Stmt.HoldsList C rd σ rest next kret ∧ (p = 0 → 0 < m → PadOK σ spPad) ∧
        ∀ j < m, SpGroupOK rd σ (p + j)
  | 0, p, _, h => ⟨by simpa [spGroupsT] using h, fun _ h => absurd h (by omega),
      fun j hj => absurd hj (by omega)⟩
  | m + 1, p, hm, h => by
      rw [spGroupsT_succ, List.append_assoc] at h
      obtain ⟨h1, hpre, k, hk, hx, ha⟩ := spGroupT_sound h
      have ih := spGroupsT_sound m (p + 1) (by omega) (by rw [spState_succ]; exact h1)
      refine ⟨ih.1, fun hp _ => ?_, fun j hj => ?_⟩
      · subst hp
        exact padRun_ok (P := 16 + 5) (by simpa [spPre, spState_zero] using hpre)
      rcases j with _ | j
      · refine ⟨k, by rw [Nat.add_zero, spN_of_lt (by omega)]; exact hk, by simpa using hx, ?_⟩
        rw [Nat.add_zero, spN_of_lt (by omega)]
        exact ha
      · have := ih.2.2 j (by omega)
        rwa [show p + 1 + j = p + (j + 1) by omega] at this

/-! ## The digits and the starts -/

/-- **The digit word group `p`'s dispatch takes**: its selector's exponent. -/
noncomputable def spDigitWord (σ : Val) (p : Nat) : Nat :=
  logG (σ (.n (spState p).2.2)) (4 ^ spN p)

/-- **The digit of chain `i`.** -/
noncomputable def spDigit (σ : Val) (i : Nat) : Nat := spDigitWord σ (i / 3) / 4 ^ (i % 3) % 4

/-- **Chain `i`'s start**: the value its walk hints, in the arm its group's dispatch takes. -/
noncomputable def spStart (σ : Val) (i : Nat) : V := spStartAt (spDigitWord σ) i

theorem spDigitWord_eq {p k : Nat} (hk : k < 4 ^ spN p)
    (hx : σ (.n (spState p).2.2) = ofK (addressOfIndex k)) : spDigitWord σ p = k :=
  logG_eq hk (by unfold spN; split <;> norm_num) hx

/-! ## The values -/

/-- **The codeword's product**: running products folded group by group (`G` groups of three digits,
then the last chain's) give `g` to the digits' sum. -/
theorem spCodeword_prod {G : Nat} (hG : 0 < G) (hG21 : G ≤ 21) (K : Nat → Nat)
    (hK : ∀ p ≤ G, K p < 4 ^ cwN G p) (hpow : ∀ s < 10, σ (.n (6 + s)) = gen ^ s) (prodV : Nat → E)
    (hprod0 : prodV 0 = σ (.n (6 + digitSum (K 0) (cwN G 0))))
    (hprod : ∀ p < G, prodV (p + 1) = prodV p * σ (.n (6 + digitSum (K (p + 1)) (cwN G (p + 1))))) :
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

end
end LeanVM.Guest.B1.Sig
