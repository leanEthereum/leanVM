/-
  LeanVM.Guest.B1.Sig.Codeword

  The WOTS+C codeword of a one-time signature (G:2416-2433, G:2611-2626): the digit groups in
  sequence, the last chain's group, and the assertions that the digits reach the target sum and
  encode the digest's first cell.
-/

module

public import LeanVM.Guest.B1.Sig.Group

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Digits -/

theorem digitSum_eq (k : Nat) : ∀ n, digitSum k n = ∑ r ∈ Finset.range n, armDigit k r
  | 0 => rfl
  | n + 1 => by rw [digitSum, Finset.sum_range_succ, digitSum_eq k n, armDigit, Nat.add_comm]

theorem digits_eq (k : Nat) : ∀ n, k % 4 ^ n = ∑ r ∈ Finset.range n, armDigit k r * 4 ^ r
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
      rw [Finset.sum_range_succ, ← digits_eq k n, armDigit, pow_succ, Nat.mod_mul, Nat.mul_comm (k / 4 ^ n % 4)]

theorem lit_xor (a b : Nat) : lit (a ^^^ b) = lit a + lit b := by
  simp only [lit, word]
  rw [ofLimbs_add]
  congr 1
  · rw [Nat.xor_mod_two_pow, ofBits_xor]
  · rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow, ofBits_xor]

theorem lit_add_of_lt {s q r : Nat} (hr : r < 2 ^ s) : lit (2 ^ s * q + r) = lit (2 ^ s * q) + lit r := by
  rw [← two_pow_mul_xor hr, lit_xor]

/-! ## Groups in sequence -/

/-- The tips of `cGroups`, chain `3q + r` of group `q`. -/
theorem cGroups_tips (w : Wots) (power : Nat → V) :
    ∀ (m p : Nat) (prod enc : V) (b q r : Nat), q < m → r < 3 → ∃ bq, b ≤ bq ∧
      (cGroups w power m p prod enc b).2.2.1[3 * q + r]? = some (groupTips w.lx (p + q == 0) bq r)
  | 0, _, _, _, _, _, _, h, _ => absurd h (by omega)
  | m + 1, p, prod, enc, b, 0, r, _, hr => ⟨b, le_rfl, by
      simp only [cGroups, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      rw [List.getElem?_append_left (by simpa using hr)]
      simp [hr]⟩
  | m + 1, p, prod, enc, b, q + 1, r, hq, hr => by
      obtain ⟨bq, hb, h⟩ := cGroups_tips w power m (p + 1) (groupProd w.lx (p == 0) 3 b)
        (groupEnc w.lx (p == 0) 3 b) (cGroup w power prod enc (3 * p) 3 (p == 0) b).2 q r (by omega) hr
      have := groupStart_ge (p == 0) b
      refine ⟨bq, le_trans (le_trans (by omega) (cGroup_snd_ge ..)) hb, ?_⟩
      simp only [cGroups]
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range]
      rw [show 3 * (q + 1) + r - 3 = 3 * q + r by omega, h, show p + 1 + q = p + (q + 1) by omega]

/-- The tips of a group's chains, then of the groups after it. -/
theorem cGroups_tips_succ (w : Wots) (power : Nat → V) (m p : Nat) (prod enc : V) (b i : Nat) :
    (cGroups w power (m + 1) p prod enc b).2.2.1.getD i (.n 0, .n 0) =
      if i < 3 then groupTips w.lx (p == 0) b i
      else (cGroups w power m (p + 1) (groupProd w.lx (p == 0) 3 b) (groupEnc w.lx (p == 0) 3 b)
        (cGroup w power prod enc (3 * p) 3 (p == 0) b).2).2.2.1.getD (i - 3) (.n 0, .n 0) := by
  simp only [cGroups]
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

theorem pow_digitSum_lt (k : Nat) : digitSum k 3 < 10 := by
  rw [digitSum_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  have := armDigit_lt k 0; have := armDigit_lt k 1; have := armDigit_lt k 2
  omega

/-- **Groups in sequence are sound**: their digit values `ks`, every chain's end at its digit,
the product times `g` to the digit sums, the encoding plus the digits' literals. -/
theorem cGroups_sound {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} (hpow : ∀ s < 10, σ (power s) = gen ^ s) :
    ∀ (m p : Nat) (prod enc : V) (b : Nat) {next : Prop} {kret : List E → Prop}, (p = 0 → 0 < m) →
      Stmt.HoldsList C rd σ (cGroups w power m p prod enc b).1 next kret →
      (∃ ks : Nat → Nat, (∀ q < m, ks q < 64) ∧
        (∀ q < m, ∀ r < 3, ∃ x, TipSet w σ (3 * (p + q) + r) (armDigit (ks q) r) x
          ((cGroups w power m p prod enc b).2.2.1.getD (3 * q + r) (.n 0, .n 0))) ∧
        σ (cGroups w power m p prod enc b).2.2.2.1 =
          (if p = 0 then 1 else σ prod) * gen ^ (∑ q ∈ Finset.range m, digitSum (ks q) 3) ∧
        σ (cGroups w power m p prod enc b).2.2.2.2 =
          (if p = 0 then 0 else σ enc) + ∑ q ∈ Finset.range m, lit (ks q * 4 ^ (3 * (p + q)))) ∧ next
  | 0, p, prod, enc, b, next, kret, hm, h => by
      have hp : p ≠ 0 := fun h => absurd (hm h) (by omega)
      exact ⟨⟨fun _ => 0, fun q h => absurd h (by omega), fun q h => absurd h (by omega),
        by simp [cGroups, hp], by simp [cGroups, hp]⟩, h⟩
  | m + 1, p, prod, enc, b, next, kret, _, h => by
      simp only [cGroups] at h ⊢
      rw [holdsList_append] at h
      obtain ⟨⟨k, hk, -, harm, hfold⟩, h⟩ := cGroup_sound hmd h
      obtain ⟨⟨ks, hks, htips, hprod, henc⟩, hn⟩ := cGroups_sound hmd hpow m (p + 1) _ _ _ (by omega) h
      refine ⟨⟨fun q => if q = 0 then k else ks (q - 1), fun q hq => ?_, fun q hq r hr => ?_, ?_, ?_⟩, hn⟩
      · by_cases hq0 : q = 0
        · subst hq0; simpa using hk
        · simp only [hq0, ↓reduceIte]; exact hks _ (by omega)
      · by_cases hq0 : q = 0
        · subst hq0
          obtain ⟨x, hx⟩ := harm r hr
          refine ⟨x, ?_⟩
          rw [List.getD_append _ _ _ _ (by simpa using hr)]
          simpa [hr] using hx
        · obtain ⟨x, hx⟩ := htips (q - 1) (by omega) r hr
          refine ⟨x, ?_⟩
          rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          simp only [hq0, ↓reduceIte, List.length_map, List.length_range]
          rw [show 3 * q + r - 3 = 3 * (q - 1) + r by omega, show 3 * (p + q) + r = 3 * (p + 1 + (q - 1)) + r by
            omega]
          exact hx
      · unfold ArmFold groupProd at hfold
        rw [hprod, Finset.sum_range_succ']
        simp only [groupProd, ↓reduceIte, Nat.add_sub_cancel, Nat.add_one_ne_zero]
        rw [hfold.1, hpow _ (pow_digitSum_lt k), pow_add]
        by_cases hp : p = 0 <;> simp [hp] <;> ring
      · unfold ArmFold groupEnc at hfold
        rw [henc, Finset.sum_range_succ']
        simp only [groupEnc, ↓reduceIte, Nat.add_sub_cancel, Nat.add_one_ne_zero, Nat.add_zero]
        rw [hfold.2]
        by_cases hp : p = 0 <;> simp [hp] <;> ring_nf

theorem groupTips_lt (lx fold : Bool) (b r n : Nat) (hr : r < n) :
    (∃ j < groupStart fold b + chainStride lx * n + 2, (groupTips lx fold b r).1 = .n j) ∧
      (∃ j < groupStart fold b + chainStride lx * n + 2, (groupTips lx fold b r).2 = .n j) := by
  have hst := ws_lt_stride lx
  have : chainStride lx * r + chainStride lx ≤ chainStride lx * n := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩

theorem cGroups_snd_ge (w : Wots) (power : Nat → V) :
    ∀ (m p : Nat) (prod enc : V) (b : Nat), b ≤ (cGroups w power m p prod enc b).2.1
  | 0, _, _, _, _ => le_rfl
  | m + 1, p, prod, enc, b => by
      simp only [cGroups]
      have := groupStart_ge (p == 0) b
      exact le_trans (le_trans (by omega) (cGroup_snd_ge ..)) (cGroups_snd_ge w power m (p + 1) _ _ _)

theorem cGroups_below {w : Wots} {power : Nat → V} :
    ∀ (m p : Nat) (prod enc : V) (b : Nat), w.Below b → NB b prod → NB b enc → (∀ s < 10, NB b (power s)) →
      NumBelow (cGroups w power m p prod enc b).2.1 (Stmt.valsList (cGroups w power m p prod enc b).1)
  | 0, _, _, _, _, _, _, _, _ => NumBelow.nil _
  | m + 1, p, prod, enc, b, hw, hp, he, hpow => by
      simp only [cGroups]
      rw [valsList_append]
      have hg := cGroup_snd_ge w power prod enc (3 * p) 3 (p == 0) b
      have h5 := groupStart_ge (p == 0) b
      have hr := cGroups_snd_ge w power m (p + 1) (groupProd w.lx (p == 0) 3 b) (groupEnc w.lx (p == 0) 3 b)
        (cGroup w power prod enc (3 * p) 3 (p == 0) b).2
      exact ((cGroup_below (by norm_num) hw ⟨hp, he, hpow⟩).mono hr).append
        (cGroups_below m (p + 1) _ _ _ (hw.mono (by omega)) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
          fun s hs => (hpow s hs).mono (by omega))

/-- **Groups in sequence are complete**: for digit values `ks` and chain values `xs`. -/
theorem cGroups_complete {w : Wots} {power : Nat → V} (hrd : MemOK rd 64) {ks : Nat → Nat} {xs : Nat → E} :
    ∀ (m p : Nat) (prod enc : V) (b : Nat) (σ : Val), (p = 0 → 0 < m) → w.Below b → NB b prod → NB b enc →
      (∀ s < 10, NB b (power s)) → σ w.md = mdw (stepCount w.lx) true → w.Canon σ →
      (∀ s < 10, σ (power s) = gen ^ s) → (∀ q < m, ks (p + q) < 64) →
      (∀ i, IsCanonical128 (xs i)) →
      Completes C rd b (cGroups w power m p prod enc b).2.1 (cGroups w power m p prod enc b).1 σ (fun σ' =>
        (∀ q < m, ∀ r < 3, TipSet w σ' (3 * (p + q) + r) (armDigit (ks (p + q)) r) (xs (3 * (p + q) + r))
          ((cGroups w power m p prod enc b).2.2.1.getD (3 * q + r) (.n 0, .n 0))) ∧
        σ' (cGroups w power m p prod enc b).2.2.2.1 =
          (if p = 0 then 1 else σ prod) * gen ^ (∑ q ∈ Finset.range m, digitSum (ks (p + q)) 3) ∧
        σ' (cGroups w power m p prod enc b).2.2.2.2 =
          (if p = 0 then 0 else σ enc) + ∑ q ∈ Finset.range m, lit (ks (p + q) * 4 ^ (3 * (p + q))))
  | 0, p, prod, enc, b, σ, hm, _, _, _, _, _, _, _, _, _ => by
      have hp : p ≠ 0 := fun h => absurd (hm h) (by omega)
      exact ⟨σ, Ext.refl _ _ _, ⟨fun q h => absurd h (by omega), by simp [cGroups, hp], by simp [cGroups, hp]⟩,
        fun _ _ hn => hn⟩
  | m + 1, p, prod, enc, b, σ, _, hw, hprod, henc, hpw, hmd, hc, hpow, hks, hxs => by
      simp only [cGroups]
      have hg := cGroup_snd_ge w power prod enc (3 * p) 3 (p == 0) b
      have h5 := groupStart_ge (p == 0) b
      have hG := cGroup_complete (C := C) (rd := rd) (w := w) (power := power) (first := 3 * p) (n := 3)
        (fold := p == 0) (σ := σ) (hrd.mono (by norm_num)) le_rfl hw ⟨hprod, henc, hpw⟩ hmd hc
        (k := ks (p + 0)) (by have := hks 0 (by omega); norm_num; omega) (xs := fun r => xs (3 * p + r))
        (fun r _ => hxs _)
      refine Completes.append (m := (cGroup w power prod enc (3 * p) 3 (p == 0) b).2) (by omega)
        (cGroups_snd_ge w power m (p + 1) _ _ _) (cGroup_below (by norm_num) hw ⟨hprod, henc, hpw⟩) hG.withExt ?_
      intro σ' he ⟨⟨_, htip, hfold⟩, he'⟩
      have hk := hw.keep he
      have hR := cGroups_complete hrd m (p + 1)
        (groupProd w.lx (p == 0) 3 b) (groupEnc w.lx (p == 0) 3 b) (cGroup w power prod enc (3 * p) 3 (p == 0) b).2
        σ' (by omega) (hw.mono (by omega)) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩ (fun s hs => (hpw s hs).mono (by omega))
        (by rw [hk.2.2.2, hmd]) (hc.congr hk) (fun s hs => by rw [he.below (hpw s hs), hpow s hs])
        (fun q hq => by rw [show p + 1 + q = p + (q + 1) by omega]; exact hks _ (by omega)) hxs
      refine hR.withExt.mono le_rfl le_rfl fun σ'' ⟨⟨htips, hP, hE⟩, he''⟩ => ⟨fun q hq r hr => ?_, ?_, ?_⟩
      · have hk'' := (hw.mono (show b ≤ (cGroup w power prod enc (3 * p) 3 (p == 0) b).2 by omega)).keep he''
        by_cases hq0 : q = 0
        · subst hq0
          obtain ⟨o1, o2⟩ := groupTips_lt w.lx (p == 0) b r 3 hr
          have := (htip r hr).congr hk'' (he''.below (NB.mono o1 hg)) (he''.below (NB.mono o2 hg))
          rw [List.getD_append _ _ _ _ (by simpa using hr)]
          simpa [hr] using this
        · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          simp only [List.length_map, List.length_range]
          have := htips (q - 1) (by omega) r hr
          rw [show 3 * q + r - 3 = 3 * (q - 1) + r by omega]
          rw [show p + 1 + (q - 1) = p + q by omega] at this
          exact this
      · rw [hP, Finset.sum_range_succ', groupProd]
        unfold ArmFold groupProd at hfold
        simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_zero]
        rw [hfold.1, he.below (hpw _ (pow_digitSum_lt _)), hpow _ (pow_digitSum_lt _), pow_add, he.below hprod]
        simp only [show ∀ q, p + 1 + q = p + (q + 1) from fun q => by omega]
        by_cases hp : p = 0 <;> simp [hp] <;> ring
      · rw [hE, Finset.sum_range_succ', groupEnc]
        unfold ArmFold groupEnc at hfold
        simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_zero]
        rw [hfold.2, he.below henc]
        simp only [show ∀ q, p + 1 + q = p + (q + 1) from fun q => by omega]
        by_cases hp : p = 0 <;> simp [hp] <;> ring_nf

/-! ## Digit arithmetic -/

theorem sum_range_three {α : Type*} [AddCommMonoid α] (g : Nat → α) :
    ∀ G, ∑ i ∈ Finset.range (3 * G), g i = ∑ q ∈ Finset.range G, (g (3 * q) + g (3 * q + 1) + g (3 * q + 2))
  | 0 => by simp
  | G + 1 => by
      rw [show 3 * (G + 1) = 3 * G + 1 + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, sum_range_three g G, Finset.sum_range_succ]
      simp only [add_assoc]

/-- The digits of a codeword of `3G + 1` chains, from the groups' values `ks` and the last
chain's `kl`. -/
def codeDigit (G : Nat) (ks : Nat → Nat) (kl i : Nat) : Nat :=
  if i < 3 * G then armDigit (ks (i / 3)) (i % 3) else kl

theorem codeDigit_lt {G : Nat} {ks : Nat → Nat} {kl : Nat} (hkl : kl < 4) (i : Nat) :
    codeDigit G ks kl i < 4 := by
  unfold codeDigit; split
  · exact armDigit_lt _ _
  · exact hkl

theorem codeDigit_group {G : Nat} {ks : Nat → Nat} {kl q r : Nat} (hq : q < G) (hr : r < 3) :
    codeDigit G ks kl (3 * q + r) = armDigit (ks q) r := by
  unfold codeDigit
  simp only [show 3 * q + r < 3 * G by omega, ↓reduceIte]
  congr 2 <;> omega

theorem lit_sum_groups (ks : Nat → Nat) :
    ∀ G, (∀ q < G, ks q < 64) → ∑ q ∈ Finset.range G, lit (ks q * 4 ^ (3 * q)) = lit (∑ q ∈ Finset.range G, ks q * 4 ^ (3 * q)) ∧
      ∑ q ∈ Finset.range G, ks q * 4 ^ (3 * q) < 2 ^ (6 * G)
  | 0, _ => by simp [lit_zero]
  | G + 1, hks => by
      obtain ⟨h1, h2⟩ := lit_sum_groups ks G fun q hq => hks q (by omega)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, h1]
      have e : ks G * 4 ^ (3 * G) = 2 ^ (6 * G) * ks G := by
        have h4 : (4 : Nat) ^ (3 * G) = 2 ^ (6 * G) := by
          rw [show (4 : Nat) = 2 ^ 2 from rfl, ← pow_mul]; ring_nf
        rw [Nat.mul_comm, h4]
      rw [e, add_comm (lit _), ← lit_add_of_lt h2, add_comm]
      refine ⟨rfl, ?_⟩
      have := hks G (by omega)
      rw [show 6 * (G + 1) = 6 * G + 6 by ring, pow_add]
      nlinarith [Nat.one_le_two_pow (n := 6 * G)]

theorem cGroups_tips_length (w : Wots) (power : Nat → V) :
    ∀ (m p : Nat) (prod enc : V) (b : Nat), (cGroups w power m p prod enc b).2.2.1.length = 3 * m
  | 0, _, _, _, _ => rfl
  | m + 1, p, prod, enc, b => by
      simp only [cGroups, List.length_append, List.length_map, List.length_range, cGroups_tips_length]
      ring

theorem digitSum_one {k : Nat} (hk : k < 4) : digitSum k 1 = k := by
  simp [digitSum, Nat.mod_eq_of_lt hk]

theorem codeDigit_sum (G : Nat) (ks : Nat → Nat) (kl : Nat) :
    ∑ i ∈ Finset.range (3 * G + 1), codeDigit G ks kl i =
      ∑ q ∈ Finset.range G, digitSum (ks q) 3 + kl := by
  rw [Finset.sum_range_succ, sum_range_three]
  congr 1
  · refine Finset.sum_congr rfl fun q hq => ?_
    simp only [Finset.mem_range] at hq
    have h0 : codeDigit G ks kl (3 * q) = armDigit (ks q) 0 := by
      simpa using codeDigit_group (G := G) (ks := ks) (kl := kl) hq (r := 0) (by norm_num)
    rw [h0, codeDigit_group hq (by norm_num), codeDigit_group hq (by norm_num), digitSum_eq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  · simp [codeDigit]

theorem codeDigit_enc (G : Nat) (ks : Nat → Nat) (kl : Nat) (hks : ∀ q < G, ks q < 64) :
    ∑ i ∈ Finset.range (3 * G + 1), codeDigit G ks kl i * 4 ^ i =
      ∑ q ∈ Finset.range G, ks q * 4 ^ (3 * q) + kl * 4 ^ (3 * G) := by
  rw [Finset.sum_range_succ, sum_range_three]
  congr 1
  · refine Finset.sum_congr rfl fun q hq => ?_
    simp only [Finset.mem_range] at hq
    have h0 : codeDigit G ks kl (3 * q) = armDigit (ks q) 0 := by
      simpa using codeDigit_group (G := G) (ks := ks) (kl := kl) hq (r := 0) (by norm_num)
    rw [h0, codeDigit_group hq (by norm_num), codeDigit_group hq (by norm_num)]
    have h := digits_eq (ks q) 3
    rw [Nat.mod_eq_of_lt (by have := hks q hq; norm_num; omega)] at h
    rw [show ks q * 4 ^ (3 * q) = (∑ r ∈ Finset.range 3, armDigit (ks q) r * 4 ^ r) * 4 ^ (3 * q) by rw [← h]]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, pow_add]
    ring
  · simp [codeDigit]

/-- **The codeword is sound**: digits below 4, every chain's end at its digit, the digits summing
to the target's exponent and encoding the digest's cell `d0`. -/
theorem cCodeword_sound {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} (hpow : ∀ s < 10, σ (power s) = gen ^ s) {G : Nat} (hG : 0 < G) {target : E}
    {d0 : V} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (cCodeword w power G target d0 b).1 next kret) :
    (∃ dig : Nat → Nat, (∀ i, dig i < 4) ∧
      (∀ i < 3 * G + 1, ∃ x, TipSet w σ i (dig i) x ((cCodeword w power G target d0 b).2.2.getD i (.n 0, .n 0))) ∧
      target = gen ^ (∑ i ∈ Finset.range (3 * G + 1), dig i) ∧
      σ d0 = lit (∑ i ∈ Finset.range (3 * G + 1), dig i * 4 ^ i)) ∧ next := by
  simp only [cCodeword] at h ⊢
  rw [holdsList_append, holdsList_append] at h
  obtain ⟨⟨ks, hks, htips, hprod, henc⟩, h⟩ := cGroups_sound hmd hpow G 0 _ _ _ (fun _ => hG) h
  obtain ⟨⟨kl, hkl, -, harm, hfold⟩, h⟩ := cGroup_sound hmd h
  simp only [cst, holdsList_cons_atom, holdsList_nil, Atom.Holds] at h
  obtain ⟨hc, hp, he, hn⟩ := h
  rw [e_add_eq_zero_iff] at hp he
  simp only [pow_one] at hkl
  have hlen := cGroups_tips_length w power G 0 (.n 0) (.n 0) b
  refine ⟨⟨codeDigit G ks kl, codeDigit_lt hkl, fun i hi => ?_, ?_, ?_⟩, hn⟩
  · by_cases hi' : i < 3 * G
    · obtain ⟨x, hx⟩ := htips (i / 3) (by omega) (i % 3) (Nat.mod_lt _ (by norm_num))
      refine ⟨x, ?_⟩
      rw [List.getD_append _ _ _ _ (by omega)]
      rw [show i = 3 * (i / 3) + i % 3 by omega, codeDigit_group (by omega) (Nat.mod_lt _ (by norm_num))]
      simpa using hx
    · obtain ⟨x, hx⟩ := harm 0 (by norm_num)
      have hi3 : i = 3 * G := by omega
      subst hi3
      refine ⟨x, ?_⟩
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
      simp only [codeDigit, lt_irrefl, ↓reduceIte, List.getD_cons_zero]
      simpa [armDigit, Nat.mod_eq_of_lt hkl] using hx
  · unfold ArmFold at hfold
    rw [codeDigit_sum, ← hc, ← hp, hfold.1, hprod, hpow _ (by rw [digitSum_one hkl]; omega), digitSum_one hkl,
      pow_add]
    simp
  · unfold ArmFold at hfold
    rw [← he, hfold.2, henc]
    simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [codeDigit_enc G ks kl hks, (lit_sum_groups ks G hks).1]
    have h2 := (lit_sum_groups ks G hks).2
    have e : kl * 4 ^ (3 * G) = 2 ^ (6 * G) * kl := by
      have h4 : (4 : Nat) ^ (3 * G) = 2 ^ (6 * G) := by
        rw [show (4 : Nat) = 2 ^ 2 from rfl, ← pow_mul]; ring_nf
      rw [Nat.mul_comm, h4]
    rw [e, add_comm (∑ q ∈ Finset.range G, ks q * 4 ^ (3 * q)), lit_add_of_lt h2, add_comm]

/-! ## Completeness of the codeword -/

theorem cGroups_tips_lt (w : Wots) (power : Nat → V) :
    ∀ (m p : Nat) (prod enc : V) (b i : Nat), i < 3 * m →
      NB (cGroups w power m p prod enc b).2.1 ((cGroups w power m p prod enc b).2.2.1.getD i (.n 0, .n 0)).1 ∧
      NB (cGroups w power m p prod enc b).2.1 ((cGroups w power m p prod enc b).2.2.1.getD i (.n 0, .n 0)).2
  | 0, _, _, _, _, _, h => absurd h (by omega)
  | m + 1, p, prod, enc, b, i, hi => by
      rw [cGroups_tips_succ]
      have hr := cGroups_snd_ge w power m (p + 1) (groupProd w.lx (p == 0) 3 b) (groupEnc w.lx (p == 0) 3 b)
        (cGroup w power prod enc (3 * p) 3 (p == 0) b).2
      have hg := cGroup_snd_ge w power prod enc (3 * p) 3 (p == 0) b
      simp only [cGroups] at hr ⊢
      split_ifs with h
      · obtain ⟨o1, o2⟩ := groupTips_lt w.lx (p == 0) b i 3 h
        exact ⟨NB.mono o1 (by omega), NB.mono o2 (by omega)⟩
      · exact cGroups_tips_lt w power m (p + 1) (groupProd w.lx (p == 0) 3 b) (groupEnc w.lx (p == 0) 3 b)
          (cGroup w power prod enc (3 * p) 3 (p == 0) b).2 (i - 3) (by omega)

theorem cGroups_outs_lt (w : Wots) (power : Nat → V) :
    ∀ (m p : Nat) (prod enc : V) (b : Nat), 0 < m →
      NB (cGroups w power m p prod enc b).2.1 (cGroups w power m p prod enc b).2.2.2.1 ∧
      NB (cGroups w power m p prod enc b).2.1 (cGroups w power m p prod enc b).2.2.2.2
  | 0, _, _, _, _, h => absurd h (by omega)
  | 1, p, prod, enc, b, _ => by
      have hg := cGroup_snd_ge w power prod enc (3 * p) 3 (p == 0) b
      simp only [cGroups]
      exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩
  | m + 2, p, prod, enc, b, _ => by
      exact cGroups_outs_lt w power (m + 1) (p + 1) (groupProd w.lx (p == 0) 3 b) (groupEnc w.lx (p == 0) 3 b)
        (cGroup w power prod enc (3 * p) 3 (p == 0) b).2 (by omega)

/-- **The codeword is complete**: digits below 4 summing to the target's exponent and encoding
`d0`'s preset value, chain values `xs`. -/
theorem cCodeword_complete {w : Wots} {power : Nat → V} (hrd : MemOK rd 64) {G : Nat} (hG : 0 < G)
    {target : E} {d0 : V} {b : Nat} {σ : Val} (hb : 0 < b) (hw : w.Below b) (hpw : ∀ s < 10, NB b (power s))
    (hd0 : NB b d0)
    (hmd : σ w.md = mdw (stepCount w.lx) true) (hc : w.Canon σ) (hpow : ∀ s < 10, σ (power s) = gen ^ s)
    {dig : Nat → Nat} (hdig : ∀ i, dig i < 4) {xs : Nat → E} (hxs : ∀ i, IsCanonical128 (xs i))
    (htarget : target = gen ^ (∑ i ∈ Finset.range (3 * G + 1), dig i))
    (hd : σ d0 = lit (∑ i ∈ Finset.range (3 * G + 1), dig i * 4 ^ i)) :
    Completes C rd b (cCodeword w power G target d0 b).2.1 (cCodeword w power G target d0 b).1 σ
      (fun σ' => ∀ i < 3 * G + 1, TipSet w σ' i (dig i) (xs i) ((cCodeword w power G target d0 b).2.2.getD i (.n 0, .n 0))) := by
  set ks : Nat → Nat := fun q => dig (3 * q) + 4 * dig (3 * q + 1) + 16 * dig (3 * q + 2) with hks_def
  set kl := dig (3 * G)
  have hks : ∀ q, ks q < 64 := fun q => by
    have := hdig (3 * q); have := hdig (3 * q + 1); have := hdig (3 * q + 2); simp only [hks_def]; omega
  have hcd : ∀ i < 3 * G + 1, codeDigit G ks kl i = dig i := by
    intro i hi
    by_cases h : i < 3 * G
    · obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ i = 3 * q + r := ⟨i / 3, i % 3, Nat.mod_lt _ (by norm_num), by omega⟩
      rw [codeDigit_group (by omega) hr]
      have := hdig (3 * q); have := hdig (3 * q + 1); have := hdig (3 * q + 2)
      simp only [hks_def, armDigit]
      interval_cases r <;> simp <;> omega
    · simp only [codeDigit, h, ↓reduceIte, kl]
      rw [show i = 3 * G by omega]
  have hsum : ∑ i ∈ Finset.range (3 * G + 1), dig i = ∑ q ∈ Finset.range G, digitSum (ks q) 3 + kl := by
    rw [← codeDigit_sum G ks kl]
    exact Finset.sum_congr rfl fun i hi => (hcd i (Finset.mem_range.mp hi)).symm
  have henc : ∑ i ∈ Finset.range (3 * G + 1), dig i * 4 ^ i =
      ∑ q ∈ Finset.range G, ks q * 4 ^ (3 * q) + kl * 4 ^ (3 * G) := by
    rw [← codeDigit_enc G ks kl fun q _ => hks q]
    exact Finset.sum_congr rfl fun i hi => by rw [hcd i (Finset.mem_range.mp hi)]
  simp only [cCodeword]
  set gs := cGroups w power G 0 (.n 0) (.n 0) b with hgs
  have hgsb := cGroups_snd_ge w power G 0 (.n 0) (.n 0) b
  rw [← hgs] at hgsb
  have hout := cGroups_outs_lt w power G 0 (.n 0) (.n 0) b hG
  rw [← hgs] at hout
  have htl := cGroups_tips_lt w power G 0 (.n 0) (.n 0) b
  rw [← hgs] at htl
  have hlen := cGroups_tips_length w power G 0 (.n 0) (.n 0) b
  rw [← hgs] at hlen
  set L := cGroup w power gs.2.2.2.1 gs.2.2.2.2 (3 * G) 1 false gs.2.1 with hL
  have hLb := cGroup_snd_ge w power gs.2.2.2.1 gs.2.2.2.2 (3 * G) 1 false gs.2.1
  rw [← hL] at hLb
  have h5 := groupStart_ge false gs.2.1
  have hA := cGroups_complete (C := C) (rd := rd) (w := w) (power := power) hrd (ks := ks) (xs := xs) G 0 (.n 0)
    (.n 0) b σ (fun _ => hG) hw ⟨0, hb, rfl⟩ ⟨0, hb, rfl⟩ hpw hmd hc hpow (fun q _ => by simpa using hks q) hxs
  rw [← hgs] at hA
  refine Completes.append (m := L.2) (P := fun σ' => (∀ q < G, ∀ r < 3, TipSet w σ' (3 * q + r)
      (armDigit (ks q) r) (xs (3 * q + r)) (gs.2.2.1.getD (3 * q + r) (.n 0, .n 0))) ∧
      TipSet w σ' (3 * G) kl (xs (3 * G)) (groupTips w.lx false gs.2.1 0) ∧
      σ' (groupProd w.lx false 1 gs.2.1) = target ∧ σ' (groupEnc w.lx false 1 gs.2.1) = σ d0 ∧
      Ext b L.2 σ σ') (by omega) (by omega) ?_ ?_ ?_
  · rw [valsList_append]
    have := cGroups_below G 0 (.n 0) (.n 0) b hw ⟨0, hb, rfl⟩ ⟨0, hb, rfl⟩ hpw
    rw [← hgs] at this
    exact (this.mono (by omega)).append
      (cGroup_below (by norm_num) (hw.mono (by omega)) ⟨hout.1, hout.2, fun s hs => (hpw s hs).mono (by omega)⟩)
  · have hgb := cGroups_below G 0 (.n 0) (.n 0) b hw ⟨0, hb, rfl⟩ ⟨0, hb, rfl⟩ hpw
    rw [← hgs] at hgb
    refine Completes.append (m := gs.2.1) hgsb (by omega) hgb hA.withExt ?_
    rintro σ1 he1 ⟨⟨htips1, hprod1, henc1⟩, -⟩
    have hk1 := hw.keep he1
    have hB := cGroup_complete (C := C) (rd := rd) (w := w) (power := power) (prodIn := gs.2.2.2.1)
      (encIn := gs.2.2.2.2) (first := 3 * G) (n := 1) (fold := false) (b := gs.2.1) (σ := σ1)
      (hrd.mono (by norm_num)) (by norm_num) (hw.mono hgsb) ⟨hout.1, hout.2, fun s hs => (hpw s hs).mono hgsb⟩
      (by rw [hk1.2.2.2, hmd]) (hc.congr hk1) (k := kl) (by have := hdig (3 * G); simp; omega)
      (xs := fun r => xs (3 * G + r)) (fun r _ => hxs _)
    refine hB.withExt.mono le_rfl le_rfl fun σ2 ⟨⟨_, htip2, hfold2⟩, he2⟩ => ⟨fun q hq r hr => ?_, ?_, ?_, ?_,
      he1.trans he2 hgsb (by omega)⟩
    · have hk2 := (hw.mono hgsb).keep he2
      obtain ⟨o1, o2⟩ := htl (3 * q + r) (by omega)
      have := (htips1 q hq r hr).congr hk2 (he2.below o1) (he2.below o2)
      simpa using this
    · have hk2 := (hw.mono hgsb).keep he2
      have := htip2 0 (by norm_num)
      simpa [armDigit, Nat.mod_eq_of_lt (hdig (3 * G)), kl] using this
    · unfold ArmFold at hfold2; unfold groupProd at hfold2 ⊢
      rw [hfold2.1, he2.below hout.1, hprod1, he2.below ((hpw _ (digitSum_lt_ten _ (by norm_num))).mono hgsb),
        he1.below (hpw _ (digitSum_lt_ten _ (by norm_num))),
        hpow _ (by rw [digitSum_one (hdig (3 * G))]; have := hdig (3 * G); omega), digitSum_one (hdig (3 * G)),
        htarget, hsum]
      simp only [↓reduceIte, Bool.false_eq_true, one_mul, pow_add, Nat.zero_add, kl]
    · unfold ArmFold at hfold2; unfold groupEnc at hfold2 ⊢
      rw [hfold2.2, he2.below hout.2, henc1, hd, henc]
      simp only [↓reduceIte, zero_add, Bool.false_eq_true]
      rw [(lit_sum_groups ks G fun q _ => hks q).1]
      have h2 := (lit_sum_groups ks G fun q _ => hks q).2
      have e : kl * 4 ^ (3 * G) = 2 ^ (6 * G) * kl := by
        have h4 : (4 : Nat) ^ (3 * G) = 2 ^ (6 * G) := by
          rw [show (4 : Nat) = 2 ^ 2 from rfl, ← pow_mul]; ring_nf
        rw [Nat.mul_comm, h4]
      rw [e, add_comm (∑ q ∈ Finset.range G, ks q * 4 ^ (3 * q)), lit_add_of_lt h2, add_comm]
  · rintro σ' he ⟨htips, htipL, hpr, hen, -⟩
    have he3 : Ext L.2 (L.2 + 1) σ' (Function.update σ' (.n L.2) target) := ext_update _ _ le_rfl (by omega)
    have hk3 := (hw.mono (show b ≤ L.2 by omega)).keep he3
    have hst := ws_lt_stride w.lx
    refine ⟨Function.update σ' (.n L.2) target, he3, fun i hi => ?_, fun next kret hn => ?_⟩
    · by_cases hi' : i < 3 * G
      · obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ i = 3 * q + r :=
          ⟨i / 3, i % 3, Nat.mod_lt _ (by norm_num), by omega⟩
        obtain ⟨o1, o2⟩ := htl (3 * q + r) (by omega)
        have := (htips q (by omega) r hr).congr hk3 (he3.below (NB.mono o1 (by omega)))
          (he3.below (NB.mono o2 (by omega)))
        rw [List.getD_append _ _ _ _ (by omega), ← hcd _ hi, codeDigit_group (by omega) hr]
        exact this
      · have hi3 : i = 3 * G := by omega
        subst hi3
        obtain ⟨o1, o2⟩ := groupTips_lt w.lx false gs.2.1 0 1 (by norm_num)
        have := htipL.congr hk3 (he3.below (NB.mono o1 (by omega))) (he3.below (NB.mono o2 (by omega)))
        rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
        simpa using this
    · have hpo : NB L.2 (groupProd w.lx false 1 gs.2.1) := ⟨_, by unfold groupProd at *; omega, rfl⟩
      have heo : NB L.2 (groupEnc w.lx false 1 gs.2.1) := ⟨_, by unfold groupEnc at *; omega, rfl⟩
      simp only [cst, holdsList_cons_atom, holdsList_nil, Atom.Holds]
      rw [he3.below hpo, he3.below heo, he3.below (NB.mono hd0 (by omega)), Function.update_self, hpr, hen,
        e_add_eq_zero_iff, e_add_eq_zero_iff, he.below hd0]
      exact ⟨rfl, rfl, rfl, hn⟩

theorem cCodeword_below {w : Wots} {power : Nat → V} {G : Nat} (hG : 0 < G) {target : E} {d0 : V} {b : Nat}
    (hb : 0 < b) (hw : w.Below b) (hpw : ∀ s < 10, NB b (power s)) (hd0 : NB b d0) :
    NumBelow (cCodeword w power G target d0 b).2.1 (Stmt.valsList (cCodeword w power G target d0 b).1) := by
  simp only [cCodeword]
  have hgsb := cGroups_snd_ge w power G 0 (.n 0) (.n 0) b
  have hout := cGroups_outs_lt w power G 0 (.n 0) (.n 0) b hG
  have hLb := cGroup_snd_ge w power (cGroups w power G 0 (.n 0) (.n 0) b).2.2.2.1
    (cGroups w power G 0 (.n 0) (.n 0) b).2.2.2.2 (3 * G) 1 false (cGroups w power G 0 (.n 0) (.n 0) b).2.1
  have h5 := groupStart_ge false (cGroups w power G 0 (.n 0) (.n 0) b).2.1
  rw [valsList_append, valsList_append]
  refine ((((cGroups_below G 0 (.n 0) (.n 0) b hw ⟨0, hb, rfl⟩ ⟨0, hb, rfl⟩ hpw).mono (by omega)).append
    ((cGroup_below (by norm_num) (hw.mono hgsb) ⟨hout.1, hout.2, fun s hs => (hpw s hs).mono hgsb⟩).mono (by omega))).append ?_)
  simp only [cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append, List.nil_append,
    List.append_nil]
  exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
    (.cons ⟨_, by omega, rfl⟩ (.cons (NB.mono hd0 (by omega)) (.nil _)))))

end
end LeanVM.Guest.B1.Sig
