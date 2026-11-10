/-
  LeanVM.Guest.B1.Sig.Codeword

  What a codeword's check computes (`codewordT`, any chain step): each chain's tip is its chain
  from the hinted start at its digit, the digits sum to the target, and they are the digest's
  first cell, base 4.
-/

module

public import LeanVM.Guest.B1.Sig.WotsSound

/-!
# The codeword, sound

`codewordT W G target d0 b` runs `G` groups of three digits and the last chain's group. The digit
values a group's dispatch takes are its selector's exponent, `cwK σ p` (`logG`, the unique exponent
below the arm count). Then (`codewordT_sound`), with the digits `cwDigit σ i` of the chains
`i < 3G + 1`:

* chain `i`'s tip `cwTip i` is `chainT f i (3 - x) x` of its start `cwStart σ i`, `x` its digit;
* `g^(Σ digits) = target` (the assertion, the powers being `g^s`);
* the digest's first cell `d0` is `Σ x_i · 4^i`, as a 192-bit word.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## Exponents -/

open Classical in
/-- The exponent `k < bound` with `x = g^k` (`0` if none). -/
noncomputable def logG (x : E) (bound : Nat) : Nat :=
  ((List.range bound).find? fun k => decide (x = ofK (addressOfIndex k))).getD 0

theorem logG_eq {x : E} {k bound : Nat} (hk : k < bound) (hb : bound ≤ 2 ^ 64 - 1)
    (hx : x = ofK (addressOfIndex k)) : logG x bound = k := by
  classical
  unfold logG
  have hsome : ((List.range bound).find? fun k => decide (x = ofK (addressOfIndex k))).isSome := by
    rw [List.find?_isSome]
    exact ⟨k, List.mem_range.mpr hk, by simp [hx]⟩
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp hsome
  rw [hk', Option.getD_some]
  have hmem := List.mem_of_find?_eq_some hk'
  have hp := List.find?_some hk'
  simp only [decide_eq_true_eq] at hp
  rw [hx] at hp
  have hk' := List.mem_range.mp hmem
  exact (gpow_injOn (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) (ofK_injective hp)).symm

/-! ## The groups of a codeword -/

/-- Group `p` of a codeword from base `b`: its running product's and encoding's cells and its base. -/
def cwState (W : WotsT) (b : Nat) : Nat → V × V × Nat
  | 0 => (.n 0, .n 0, b)
  | p + 1 =>
      let st := cwState W b p
      (prodT W (p == 0) 3 st.2.2, encT W (p == 0) 3 st.2.2,
        (groupT W (3 * p) 3 (p == 0) st.1 st.2.1 st.2.2).2)

/-- What group `q` of `G + 1` establishes: its digits `k < 4^n`, its arm. -/
def GroupOK (rd : Reader) (σ : Val) (W : WotsT) (b q : Nat) (fold : Bool) (n : Nat) : Prop :=
  ∃ k < 4 ^ n, σ (.n (cwState W b q).2.2) = ofK (addressOfIndex k) ∧
    AtomsHold rd σ (armT W (slotsT W fold (cwState W b q).2.2) (3 * q) n fold (cwState W b q).1
      (cwState W b q).2.1 (prodT W fold n (cwState W b q).2.2) (encT W fold n (cwState W b q).2.2) k
      (armBase W (slotsT W fold (cwState W b q).2.2) (3 * q) n fold (cwState W b q).1
        (cwState W b q).2.1 (prodT W fold n (cwState W b q).2.2) (encT W fold n (cwState W b q).2.2)
        0 k ((cwState W b q).2.2 + 6))).1

theorem groupsT_eq (W : WotsT) (b : Nat) : ∀ (m p : Nat),
    (groupsT W m p (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2).2 =
      ((cwState W b (p + m)).2.2, (List.range m).flatMap (fun j => (List.range 3).map fun r =>
        V.n (slotsT W (p + j == 0) (cwState W b (p + j)).2.2 r 2)),
        (cwState W b (p + m)).1, (cwState W b (p + m)).2.1)
  | 0, p => by simp [groupsT]
  | m + 1, p => by
      have ih := groupsT_eq W b m (p + 1)
      have e : (groupsT W m (p + 1) (prodT W (p == 0) 3 (cwState W b p).2.2)
          (encT W (p == 0) 3 (cwState W b p).2.2)
          (groupT W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2).2).2 =
          ((cwState W b (p + 1 + m)).2.2, (List.range m).flatMap (fun j => (List.range 3).map fun r =>
            V.n (slotsT W (p + 1 + j == 0) (cwState W b (p + 1 + j)).2.2 r 2)),
            (cwState W b (p + 1 + m)).1, (cwState W b (p + 1 + m)).2.1) := ih
      simp only [groupsT]
      rw [e, show p + 1 + m = p + (m + 1) by omega]
      simp only [Prod.mk.injEq, true_and, and_true]
      rw [List.range_succ_eq_map (n := m), List.flatMap_cons, List.flatMap_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.flatMap_congr
      intro j _
      simp only [Nat.succ_eq_add_one, show p + 1 + j = p + (j + 1) by omega]

theorem groupsT_sound {W : WotsT} (hW : StepAtoms W) (b : Nat) {rest : List Stmt} {next : Prop} :
    ∀ (m p : Nat),
    Stmt.HoldsList C rd σ ((groupsT W m p (cwState W b p).1 (cwState W b p).2.1
      (cwState W b p).2.2).1 ++ rest) next kret →
      Stmt.HoldsList C rd σ rest next kret ∧ ∀ j < m, GroupOK rd σ W b (p + j) (p + j == 0) 3
  | 0, p, h => ⟨by simpa [groupsT] using h, fun j hj => absurd hj (by omega)⟩
  | m + 1, p, h => by
      simp only [groupsT, List.append_assoc] at h
      obtain ⟨h1, k, hk, hx, ha⟩ := groupT_sound hW h
      have ih := groupsT_sound hW b m (p + 1) (by simpa only [cwState] using h1)
      refine ⟨ih.1, fun j hj => ?_⟩
      rcases j with _ | j
      · exact ⟨k, hk, hx, ha⟩
      · have := ih.2 j (by omega)
        rwa [show p + 1 + j = p + (j + 1) by omega] at this

/-! ## The codeword -/

/-- The digits of group `p` of a codeword of `G` groups of three and the last chain's. -/
def cwN (G p : Nat) : Nat := if p < G then 3 else 1

/-- Group `p`'s arm `k`, from its base. -/
def cwArm (W : WotsT) (G b p k : Nat) : List Stmt × Nat :=
  armT W (slotsT W (p == 0) (cwState W b p).2.2) (3 * p) (cwN G p) (p == 0) (cwState W b p).1
    (cwState W b p).2.1 (prodT W (p == 0) (cwN G p) (cwState W b p).2.2)
    (encT W (p == 0) (cwN G p) (cwState W b p).2.2) k
    (armBase W (slotsT W (p == 0) (cwState W b p).2.2) (3 * p) (cwN G p) (p == 0) (cwState W b p).1
      (cwState W b p).2.1 (prodT W (p == 0) (cwN G p) (cwState W b p).2.2)
      (encT W (p == 0) (cwN G p) (cwState W b p).2.2) 0 k ((cwState W b p).2.2 + 6))

/-- The digit values group `p`'s dispatch takes: its selector's exponent. -/
noncomputable def cwK (W : WotsT) (G b : Nat) (σ : Val) (p : Nat) : Nat :=
  logG (σ (.n (cwState W b p).2.2)) (4 ^ cwN G p)

/-- **The digit of chain `i`.** -/
noncomputable def cwDigit (W : WotsT) (G b : Nat) (σ : Val) (i : Nat) : Nat :=
  cwK W G b σ (i / 3) / 4 ^ (i % 3) % 4

/-- **Chain `i`'s tip**: the slot of its last step. -/
def cwTip (W : WotsT) (b i : Nat) : V := .n (slotsT W (i / 3 == 0) (cwState W b (i / 3)).2.2 (i % 3) 2)

/-- **Chain `i`'s start**: the value its walk hints, in the arm its group's dispatch takes. -/
noncomputable def cwStart (W : WotsT) (G b : Nat) (σ : Val) (i : Nat) : V :=
  armStart W (slotsT W (i / 3 == 0) (cwState W b (i / 3)).2.2) (i / 3 == 0) (cwK W G b σ (i / 3))
    (armBase W (slotsT W (i / 3 == 0) (cwState W b (i / 3)).2.2) (3 * (i / 3)) (cwN G (i / 3))
      (i / 3 == 0) (cwState W b (i / 3)).1 (cwState W b (i / 3)).2.1
      (prodT W (i / 3 == 0) (cwN G (i / 3)) (cwState W b (i / 3)).2.2)
      (encT W (i / 3 == 0) (cwN G (i / 3)) (cwState W b (i / 3)).2.2) 0 (cwK W G b σ (i / 3))
      ((cwState W b (i / 3)).2.2 + 6)) (i % 3)

theorem codewordT_groups {W : WotsT} (hW : StepAtoms W) {G : Nat} (hG : 0 < G) {target : E} {d0 : V}
    {b : Nat} {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ ((codewordT W G target d0 b).1 ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧
      (∀ p ≤ G, ∃ k < 4 ^ cwN G p, σ (.n (cwState W b p).2.2) = ofK (addressOfIndex k) ∧
        AtomsHold rd σ (cwArm W G b p k).1) ∧
      σ d0 = σ (encT W false 1 (cwState W b G).2.2) ∧
      σ (prodT W false 1 (cwState W b G).2.2) = target := by
  have hgs := groupsT_eq W b G 0
  simp only [Nat.zero_add] at hgs
  simp only [codewordT, List.append_assoc] at h
  have hgs' : (groupsT W G 0 (.n 0) (.n 0) b).2 = _ := hgs
  rw [hgs'] at h
  obtain ⟨h1, hg⟩ := groupsT_sound (rd := rd) (σ := σ) (C := C) (kret := kret) hW b G 0 h
  obtain ⟨h2, kL, hkL, hxL, haL⟩ := groupT_sound hW h1
  have hc := h2
  simp only [List.cons_append, List.nil_append] at hc
  have e1 : σ d0 = σ (encT W false 1 (cwState W b G).2.2) := hc.1
  have e2 := hc.2.1
  have e3 := hc.2.2.1
  simp only [Atom.Holds] at e2 e3
  refine ⟨hc.2.2.2, fun p hp => ?_, e1, ?_⟩
  · by_cases hpG : p < G
    · obtain ⟨k, hk, hx, ha⟩ := hg p hpG
      simp only [Nat.zero_add] at hk hx ha
      exact ⟨k, by simp only [cwN, hpG, ↓reduceIte]; exact hk, hx, by simpa [cwArm, cwN, hpG] using ha⟩
    · have hpe : p = G := by omega
      subst hpe
      have hf : (p == 0) = false := by simp; omega
      exact ⟨kL, by simpa [cwN] using hkL, hxL, by simpa [cwArm, cwN, hf] using haL⟩
  · rw [← e2]
    exact (Value.e_add_eq_zero_iff).mp e3

/-! ## Sums of digits -/

theorem sum_range_three_mul {M : Type} [AddCommMonoid M] (g : Nat → M) :
    ∀ m, ∑ i ∈ Finset.range (3 * m), g i = ∑ p ∈ Finset.range m, (g (3 * p) + g (3 * p + 1) + g (3 * p + 2))
  | 0 => by simp
  | m + 1 => by
      rw [Finset.sum_range_succ (n := m), ← sum_range_three_mul g m,
        show 3 * (m + 1) = 3 * m + 2 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      simp only [add_assoc]

theorem digits_three (k : Nat) (hk : k < 64) : k % 4 + k / 4 % 4 * 4 + k / 16 % 4 * 16 = k := by
  omega

theorem digitSum_three (k : Nat) : digitSum k 3 = k % 4 + k / 4 % 4 + k / 16 % 4 := by
  simp [digitSum]; omega

theorem digitSum_one (k : Nat) (hk : k < 4) : digitSum k 1 = k := by
  simp [digitSum]; omega

theorem eOfNat128_add_shift {S k s : Nat} (hS : S < 2 ^ s) :
    eOfNat128 S + eOfNat128 (2 ^ s * k) = eOfNat128 (S + 2 ^ s * k) := by
  rw [← eOfNat128_xor, Nat.xor_comm, two_pow_mul_xor hS, add_comm]

theorem sum_lt_pow64 (K : Nat → Nat) (hK : ∀ q, K q < 64) :
    ∀ p, ∑ q ∈ Finset.range p, K q * 4 ^ (3 * q) < 2 ^ (6 * p)
  | 0 => by simp
  | p + 1 => by
      rw [Finset.sum_range_succ]
      have ih := sum_lt_pow64 K hK p
      have h1 : K p * 4 ^ (3 * p) ≤ 63 * 2 ^ (6 * p) := by
        rw [show (4 : Nat) ^ (3 * p) = 2 ^ (6 * p) by rw [pow_mul, pow_mul]; norm_num]
        exact Nat.mul_le_mul_right _ (by have := hK p; omega)
      rw [show 6 * (p + 1) = 6 * p + 6 by ring, pow_add]
      omega

theorem group_lit_bound {k q : Nat} (hk : k < 64) (hq : q ≤ 20) : k * 4 ^ (3 * q) < 2 ^ 128 := by
  have h1 : 4 ^ (3 * q) ≤ 4 ^ 60 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc k * 4 ^ (3 * q) < 64 * 4 ^ (3 * q) := Nat.mul_lt_mul_of_pos_right hk (by positivity)
    _ ≤ 64 * 4 ^ 60 := Nat.mul_le_mul_left _ h1
    _ < 2 ^ 128 := by norm_num

theorem last_lit_bound {k q : Nat} (hk : k < 4) (hq : q ≤ 21) : k * 4 ^ (3 * q) < 2 ^ 128 := by
  have h1 : 4 ^ (3 * q) ≤ 4 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc k * 4 ^ (3 * q) < 4 * 4 ^ (3 * q) := Nat.mul_lt_mul_of_pos_right hk (by positivity)
    _ ≤ 4 * 4 ^ 63 := Nat.mul_le_mul_left _ h1
    _ = 2 ^ 128 := by norm_num

/-- **The codeword's values**: with the digits `cwDigit` its groups' dispatches choose, each chain's
tip is its chain from its start, the running product is `g` to the digits' sum and the encoding
their base-4 number. -/
theorem codeword_vals {W : WotsT} {f : Nat → Nat → E → E}
    (hs : StepSound rd σ W f) (hpow : ∀ s < 10, σ (W.power s) = gen ^ s) {G : Nat} (hG : 0 < G)
    (hG21 : G ≤ 21) {b : Nat}
    (hgrp : ∀ p ≤ G, ∃ k < 4 ^ cwN G p, σ (.n (cwState W b p).2.2) = ofK (addressOfIndex k) ∧
        AtomsHold rd σ (cwArm W G b p k).1)
    (hE : ∀ first n k, W.enc first n k = k * 4 ^ first := by intros; rfl) :
      (∀ i < 3 * G + 1, cwDigit W G b σ i < 4 ∧
        σ (cwTip W b i) = chainT f i (3 - cwDigit W G b σ i) (cwDigit W G b σ i)
          (σ (cwStart W G b σ i))) ∧
      σ (prodT W false 1 (cwState W b G).2.2) = gen ^ (∑ i ∈ Finset.range (3 * G + 1), cwDigit W G b σ i) ∧
      σ (encT W false 1 (cwState W b G).2.2) =
        lit (∑ i ∈ Finset.range (3 * G + 1), cwDigit W G b σ i * 4 ^ i) := by
  set K := cwK W G b σ with hKdef
  have hK : ∀ p ≤ G, K p < 4 ^ cwN G p ∧ AtomsHold rd σ (cwArm W G b p (K p)).1 := by
    intro p hp
    obtain ⟨k, hk, hx, ha⟩ := hgrp p hp
    have hn : 4 ^ cwN G p ≤ 2 ^ 64 - 1 := by
      unfold cwN; split <;> norm_num
    have e : K p = k := logG_eq hk hn hx
    rw [e]
    exact ⟨hk, ha⟩
  have harm : ∀ p ≤ G, ArmOK W f σ (slotsT W (p == 0) (cwState W b p).2.2) (3 * p) (cwN G p) (p == 0)
      (cwState W b p).1 (cwState W b p).2.1 (prodT W (p == 0) (cwN G p) (cwState W b p).2.2)
      (encT W (p == 0) (cwN G p) (cwState W b p).2.2) (K p)
      (armStart W (slotsT W (p == 0) (cwState W b p).2.2) (p == 0) (K p)
        (armBase W (slotsT W (p == 0) (cwState W b p).2.2) (3 * p) (cwN G p) (p == 0)
          (cwState W b p).1 (cwState W b p).2.1 (prodT W (p == 0) (cwN G p) (cwState W b p).2.2)
          (encT W (p == 0) (cwN G p) (cwState W b p).2.2) 0 (K p) ((cwState W b p).2.2 + 6))) :=
    fun p hp => armT_sound hs (hK p hp).2
  have hK64 : ∀ q, q < G → K q < 64 := fun q hq => by
    have := (hK q (by omega)).1
    simpa [cwN, hq] using this
  have hKG : K G < 4 := by simpa [cwN] using (hK G le_rfl).1
  -- the digits
  have hdig : ∀ i, cwDigit W G b σ i = K (i / 3) / 4 ^ (i % 3) % 4 := fun i => rfl
  refine ⟨fun i hi => ⟨Nat.mod_lt _ (by norm_num), ?_⟩, ?_, ?_⟩
  · have hp : i / 3 ≤ G := by omega
    have hr : i % 3 < cwN G (i / 3) := by
      unfold cwN
      split
      · omega
      · omega
    have := (harm (i / 3) hp).tip (i % 3) hr
    rw [show 3 * (i / 3) + i % 3 = i by omega] at this
    exact this
  · -- the product
    have hpr : ∀ p < G, σ (prodT W (p == 0) 3 (cwState W b p).2.2) =
        gen ^ (∑ q ∈ Finset.range (p + 1), digitSum (K q) 3) := by
      intro p hp
      induction p with
      | zero =>
          have := (harm 0 (by omega)).prod
          simp only [cwN, hp, ↓reduceIte, beq_self_eq_true] at this
          simp only [beq_self_eq_true]
          rw [this, hpow _ (by rw [digitSum_three]; omega)]
          simp
      | succ p ih =>
          have := (harm (p + 1) (by omega)).prod
          simp only [cwN, hp, ↓reduceIte, Nat.add_one_ne_zero, beq_iff_eq] at this
          rw [this, hpow _ (by rw [digitSum_three]; omega), Finset.sum_range_succ, pow_add,
            ← ih (by omega)]
          rfl
    have hlast := (harm G le_rfl).prod
    simp only [cwN, lt_irrefl, ↓reduceIte, show (G == 0) = false by simp; omega,
      Bool.false_eq_true] at hlast
    symm
    rw [hlast, hpow _ (by rw [digitSum_one _ hKG]; omega), digitSum_one _ hKG]
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have e1 : σ (cwState W b (G' + 1)).1 = gen ^ (∑ q ∈ Finset.range (G' + 1), digitSum (K q) 3) :=
      hpr G' (by omega)
    rw [e1, ← pow_add, Finset.sum_range_succ, sum_range_three_mul]
    congr 1
    simp only [hdig, show ∀ q, (3 * q) / 3 = q from fun q => by omega,
      show ∀ q, (3 * q + 1) / 3 = q from fun q => by omega, show ∀ q, (3 * q + 2) / 3 = q from fun q => by omega,
      show ∀ q, (3 * q) % 3 = 0 from fun q => by omega, show ∀ q, (3 * q + 1) % 3 = 1 from fun q => by omega,
      show ∀ q, (3 * q + 2) % 3 = 2 from fun q => by omega, digitSum_three]
    congr 1
    · apply Finset.sum_congr rfl
      intro q _
      simp
    · simpa using hKG
  · -- the encoding
    have h4 : ∀ q, (4 : Nat) ^ (3 * q) = 2 ^ (6 * q) := fun q => by rw [pow_mul, pow_mul]; norm_num
    let K' : Nat → Nat := fun q => if q < G then K q else 0
    have hK' : ∀ q, K' q < 64 := fun q => by
      simp only [K']; split
      · exact hK64 q (by assumption)
      · omega
    have hsum : ∀ p, p ≤ G → ∑ q ∈ Finset.range p, K' q * 4 ^ (3 * q) =
        ∑ q ∈ Finset.range p, K q * 4 ^ (3 * q) := fun p hp =>
      Finset.sum_congr rfl fun q hq => by simp [K', show q < G by simp at hq; omega]
    have hen : ∀ p < G, σ (encT W (p == 0) 3 (cwState W b p).2.2) =
        eOfNat128 (∑ q ∈ Finset.range (p + 1), K q * 4 ^ (3 * q)) := by
      intro p hp
      induction p with
      | zero =>
          have := (harm 0 (by omega)).enc
          rw [hE] at this
          simp only [cwN, hp, ↓reduceIte, beq_self_eq_true] at this
          simp only [beq_self_eq_true]
          rw [this, zero_add, lit_eq _ (group_lit_bound (hK64 0 hp) (by omega))]
          simp
      | succ p ih =>
          have := (harm (p + 1) (by omega)).enc
          rw [hE] at this
          simp only [cwN, hp, ↓reduceIte, Nat.add_one_ne_zero, beq_iff_eq] at this
          have hlt := sum_lt_pow64 K' hK' (p + 1)
          rw [hsum (p + 1) (by omega)] at hlt
          rw [this, Finset.sum_range_succ,
            lit_eq _ (group_lit_bound (hK64 (p + 1) hp) (by omega))]
          show σ (encT W (p == 0) 3 (cwState W b p).2.2) + _ = _
          rw [ih (by omega), show K (p + 1) * 4 ^ (3 * (p + 1)) = 2 ^ (6 * (p + 1)) * K (p + 1) by
            rw [h4, mul_comm], eOfNat128_add_shift hlt]
    have hlast := (harm G le_rfl).enc
    rw [hE] at hlast
    simp only [cwN, lt_irrefl, ↓reduceIte, show (G == 0) = false by simp; omega,
      Bool.false_eq_true] at hlast
    rw [hlast]
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have e1 : σ (cwState W b (G' + 1)).2.1 = eOfNat128 (∑ q ∈ Finset.range (G' + 1), K q * 4 ^ (3 * q)) :=
      hen G' (by omega)
    have hlt := sum_lt_pow64 K' hK' (G' + 1)
    rw [hsum (G' + 1) (by omega)] at hlt
    have hbound : K (G' + 1) * 4 ^ (3 * (G' + 1)) < 2 ^ 128 := last_lit_bound hKG (by omega)
    rw [e1, lit_eq _ hbound, show K (G' + 1) * 4 ^ (3 * (G' + 1)) = 2 ^ (6 * (G' + 1)) * K (G' + 1) by
      rw [h4, mul_comm], eOfNat128_add_shift hlt]
    have hN : ∑ q ∈ Finset.range (G' + 1), K q * 4 ^ (3 * q) + 2 ^ (6 * (G' + 1)) * K (G' + 1) =
        ∑ i ∈ Finset.range (3 * (G' + 1) + 1), cwDigit W (G' + 1) b σ i * 4 ^ i := by
      rw [Finset.sum_range_succ (n := 3 * (G' + 1)), sum_range_three_mul]
      simp only [hdig, show ∀ q, (3 * q) / 3 = q from fun q => by omega,
        show ∀ q, (3 * q + 1) / 3 = q from fun q => by omega,
        show ∀ q, (3 * q + 2) / 3 = q from fun q => by omega,
        show ∀ q, (3 * q) % 3 = 0 from fun q => by omega, show ∀ q, (3 * q + 1) % 3 = 1 from fun q => by omega,
        show ∀ q, (3 * q + 2) % 3 = 2 from fun q => by omega]
      congr 1
      · apply Finset.sum_congr rfl
        intro q hq
        have hq' := hK64 q (by simp at hq; omega)
        have e := digits_three (K q) hq'
        simp only [pow_zero, pow_one, Nat.div_one, pow_add, show (4 : Nat) ^ 2 = 16 by norm_num]
        nth_rewrite 1 [← e]
        ring
      · rw [← h4]
        simp [Nat.mod_eq_of_lt hKG, mul_comm]
    rw [hN, lit_eq _ (by
      rw [← hN]
      have := Nat.mul_le_mul_left (2 ^ (6 * (G' + 1))) (show K (G' + 1) ≤ 3 by omega)
      calc _ < 2 ^ (6 * (G' + 1)) + 2 ^ (6 * (G' + 1)) * 3 := by omega
        _ = 2 ^ 2 * 2 ^ (6 * (G' + 1)) := by ring
        _ ≤ 2 ^ 2 * 2 ^ 126 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 2 ^ 128 := by norm_num)]

/-- **The codeword, sound.** With the digits `cwDigit` its dispatches choose, each chain's tip is
its chain from its start, the digits sum to the target in the exponent, and the digest's first
cell is their base-4 number. -/
theorem codewordT_sound {W : WotsT} (hW : StepAtoms W) {f : Nat → Nat → E → E}
    (hs : StepSound rd σ W f) (hpow : ∀ s < 10, σ (W.power s) = gen ^ s) {G : Nat} (hG : 0 < G)
    (hG21 : G ≤ 21) {target : E} {d0 : V} {b : Nat} {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ ((codewordT W G target d0 b).1 ++ rest) next kret)
    (hE : ∀ first n k, W.enc first n k = k * 4 ^ first := by intros; rfl) :
    Stmt.HoldsList C rd σ rest next kret ∧
      (∀ i < 3 * G + 1, cwDigit W G b σ i < 4 ∧
        σ (cwTip W b i) = chainT f i (3 - cwDigit W G b σ i) (cwDigit W G b σ i)
          (σ (cwStart W G b σ i))) ∧
      gen ^ (∑ i ∈ Finset.range (3 * G + 1), cwDigit W G b σ i) = target ∧
      σ d0 = lit (∑ i ∈ Finset.range (3 * G + 1), cwDigit W G b σ i * 4 ^ i) := by
  obtain ⟨hrest, hgrp, hd0, hprod⟩ := codewordT_groups hW hG h
  obtain ⟨ht, hp, he⟩ := codeword_vals hs hpow hG hG21 hgrp hE
  exact ⟨hrest, ht, hp.symm.trans hprod, hd0.trans he⟩

theorem map_range_three_mul {α : Type} (g : Nat → α) :
    ∀ G, (List.range (3 * G)).map g = (List.range G).flatMap (fun j => (List.range 3).map fun r => g (3 * j + r))
  | 0 => rfl
  | G + 1 => by
      rw [show 3 * (G + 1) = 3 * G + 3 by ring, List.range_add, List.map_append, map_range_three_mul g G,
        List.range_succ (n := G), List.flatMap_append, List.map_map]
      simp

/-- **The codeword's tips** are the chains' tips, in order. -/
theorem codewordT_tips (W : WotsT) {G : Nat} (hG : 0 < G) (target : E) (d0 : V) (b : Nat) :
    (codewordT W G target d0 b).2.2 = (List.range (3 * G + 1)).map (cwTip W b) := by
  have hgs := groupsT_eq W b G 0
  simp only [Nat.zero_add] at hgs
  have hgs' : (groupsT W G 0 (.n 0) (.n 0) b).2 = _ := hgs
  simp only [codewordT]
  rw [hgs']
  rw [List.range_succ (n := 3 * G), List.map_append, map_range_three_mul]
  simp only [List.map_cons, List.map_nil]
  congr 1
  · apply List.flatMap_congr
    intro j _
    apply List.map_congr_left
    intro r hr
    have hr' : r < 3 := List.mem_range.mp hr
    simp only [cwTip, show (3 * j + r) / 3 = j by omega, show (3 * j + r) % 3 = r by omega]
  · simp only [cwTip, show 3 * G / 3 = G by omega, show 3 * G % 3 = 0 by omega,
      show (G == 0) = false by simp; omega]

theorem codewordT_tips_length (W : WotsT) {G : Nat} (hG : 0 < G) (target : E) (d0 : V) (b : Nat) :
    (codewordT W G target d0 b).2.2.length = 3 * G + 1 := by
  rw [codewordT_tips W hG]; simp

end
end LeanVM.Guest.B1.Sig
