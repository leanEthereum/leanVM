/-
  LeanVM.Guest.B1.Sig.SphincsBody

  The pieces of `verify_sig_lean_sphincs` around the forest (G:2525-2560, 2582-2605): the prologue
  (the message digest, the index and unused bits), the codeword lanes and the digest's assertions,
  the counter and the encoding hash, sound.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsDigest
public import LeanVM.Guest.B1.Sig.Steps

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The prologue -/

/-- What the prologue leaves for the index `N` and the unused bits `U`. -/
structure SPre (σ : Val) (N U : Nat) : Prop where
  md48 : σ (.n 2) = mdw 48 true
  md64 : σ (.n 3) = mdw 64 true
  ltN : N < 2 ^ 26
  ltU : U < 2 ^ 22
  bits : ∀ j < 26, σ (.n (19 + j)) = bitE (N.testBit j)
  nodes : ∀ l < 26, σ (.n (142 - 3 * l)) = eOfNat (N / 2 ^ l)
  bound : σ (.n 209) = eOfNat N + lit (U * 2 ^ 106)

theorem sPrologue_eq : sPrologue =
    [.atom (.load (.n 1) (.n 0) 1), cst 2 (mdw 48 true), cst 3 (mdw 64 true), cst 4 (word (tw 12) 0 0),
      .atom (.load (.n 5) (.n 0) 2), .atom (.load (.n 6) (.n 0) 3), cst 7 iv0, cst 8 iv1,
      cst 9 (mdw 64 false), b2s (.n 1) (.n 4) (.n 5) (.n 6) (.n 7) (.n 8) (.n 10) (.n 11) (.n 9),
      hintW "sp_rand" [.n 12], cst 13 (word 0 0 0), cst 14 (word 0 0 0), cst 15 (word 0 0 0),
      cst 16 (mdw 80 true), b2s (.n 12) (.n 13) (.n 14) (.n 15) (.n 10) (.n 11) (.n 17) (.n 18) (.n 16),
      .atom (.hint (.bits (.n 18) 0 26 (.stack ((List.range 26).map fun j => .n (19 + j)))))] ++
    (booleans 19 26 ++ (.atom (.hint (.bits (.n 18) 106 22 (.stack ((List.range 22).map fun j => .n (45 + j))))) ::
      (booleans 45 22 ++ (shifts 19 26 67 ++ (shifts 45 22 143 ++
        [cst 207 (word 0 (2 ^ 42) 0), mulS (.n 208) (.n 206) (.n 207), addS (.n 209) (.n 142) (.n 208)]))))) := by
  simp only [sPrologue, ivs, List.append_assoc, List.cons_append, List.nil_append]

/-- The unused bits' field. -/
theorem eOfNat_mul_unused {U : Nat} (hU : U < 2 ^ 22) : eOfNat U * word 0 (2 ^ 42) 0 = lit (U * 2 ^ 106) := by
  have h1 : U * 2 ^ 106 % 2 ^ 64 = 0 := by
    rw [show U * 2 ^ 106 = 2 ^ 64 * (2 ^ 42 * U) by ring]; exact Nat.mul_mod_right _ _
  have h2 : U * 2 ^ 106 / 2 ^ 64 % 2 ^ 64 = 2 ^ 42 * U := by
    rw [show U * 2 ^ 106 = 2 ^ 64 * (2 ^ 42 * U) by ring, Nat.mul_div_cancel_left _ (by positivity),
      Nat.mod_eq_of_lt (by omega)]
  rw [lit, h1, h2, word, word, eOfNat, mul_comm, ofLimbs_mul_ofK, ofBits_two_pow_mul (by omega)]
  simp [ofBits_zero]

/-- **The prologue is sound**: the message digest of the claim's message under some randomizer,
the index's bits and the unused bits pinned, the node indices, the bound's start. -/
theorem sPrologue_sound {σ : Val} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ sPrologue next kret) :
    LoadHolds rd (σ (.n 0)) 1 (σ (.n 1)) ∧ LoadHolds rd (σ (.n 0)) 2 (σ (.n 5)) ∧
      LoadHolds rd (σ (.n 0)) 3 (σ (.n 6)) ∧ IsCanonical128 (σ (.n 1)) ∧ IsCanonical128 (σ (.n 5)) ∧
      IsCanonical128 (σ (.n 6)) ∧
      (σ (.n 17), σ (.n 18)) = hcell [σ (.n 1), word (tw 12) 0 0, σ (.n 5), σ (.n 6), σ (.n 12)] ∧
      (∃ N U, SPre σ N U) ∧ next := by
  rw [sPrologue_eq] at h
  simp only [cst, b2s, hintW, holdsList_cons_atom, holdsList_append, Atom.Holds, true_and] at h
  obtain ⟨hl1, h2, h3, h4, hl5, hl6, h7, h8, h9, hc1, h13, h14, h15, h16, hc2, h⟩ := h
  rw [booleans_iff] at h
  obtain ⟨hbN, h⟩ := h
  rw [booleans_iff] at h
  obtain ⟨hbU, h⟩ := h
  set fN : Nat → Bool := fun j => decide (σ (.n (19 + j)) = 1)
  set fU : Nat → Bool := fun j => decide (σ (.n (45 + j)) = 1)
  have hN : bitsVal fN 26 < 2 ^ 26 := bitsVal_lt fN 26
  have hU : bitsVal fU 22 < 2 ^ 22 := bitsVal_lt fU 22
  have hbitsN : ∀ j < 26, σ (.n (19 + j)) = bitE ((bitsVal fN 26).testBit j) := fun j hj => by
    rw [testBit_bitsVal, decide_eq_true hj, Bool.true_and]
    exact bitE_of_mul_self (hbN j hj)
  have hbitsU : ∀ j < 22, σ (.n (45 + j)) = bitE ((bitsVal fU 22).testBit j) := fun j hj => by
    rw [testBit_bitsVal, decide_eq_true hj, Bool.true_and]
    exact bitE_of_mul_self (hbU j hj)
  obtain ⟨hshN, h⟩ := shifts_sound (by omega) (by omega) hN hbitsN h
  obtain ⟨hshU, h⟩ := shifts_sound (by omega) (by omega) hU hbitsU h
  simp only [mulS, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds] at h
  obtain ⟨h207, h208, h209, hn⟩ := h
  -- the digest
  rw [h4, h7, h8, h9] at hc1
  rw [h13, h14, h15, h16, word_zero] at hc2
  have hr : ([σ (.n 12)].flatMap cellBytes).length = 16 := by rw [length_flatMap_cellBytes']; rfl
  have hc2' : CompressCells ![σ (.n 12), 0, 0, 0] (σ (.n 10)) (σ (.n 11)) (σ (.n 17)) (σ (.n 18))
      (mdw (64 + ([σ (.n 12)].flatMap cellBytes).length) true) := by rw [hr]; exact hc2
  obtain ⟨hb0, -, -, ho⟩ := (compress_two_iff (blockBytes_one (σ (.n 12))) (by rw [hr]; omega)
    (by rw [hr]; omega)).mp ⟨hc1, hc2'⟩
  rw [fin4_canonical] at hb0
  refine ⟨hl1, hl5, hl6, hb0.1, hb0.2.2.1, hb0.2.2.2, ?_, ⟨bitsVal fN 26, bitsVal fU 22, h2, h3, hN, hU, hbitsN,
    fun l hl => ?_, ?_⟩, hn⟩
  · rw [ho, blockBytes_four, hcell, ← List.flatMap_append]
    rfl
  · have := hshN (25 - l) (by omega)
    rwa [show 67 + 3 * (25 - l) = 142 - 3 * l by omega, show 26 - 1 - (25 - l) = l by omega] at this
  · have hN0 := hshN 25 (by omega)
    have hU0 := hshU 21 (by omega)
    simp only [show 67 + 3 * 25 = 142 from rfl, show 26 - 1 - 25 = 0 from rfl, pow_zero, Nat.div_one] at hN0
    simp only [show 143 + 3 * 21 = 206 from rfl, show 22 - 1 - 21 = 0 from rfl, pow_zero, Nat.div_one] at hU0
    rw [h209, h208, h207, hN0, hU0, eOfNat_mul_unused hU]

/-! ## The codeword lanes -/

theorem div_pow_step (w X j : Nat) : X / 2 ^ (w * j) = 2 ^ w * (X / 2 ^ (w * (j + 1))) + X / 2 ^ (w * j) % 2 ^ w := by
  rw [show w * (j + 1) = w * j + w by ring, pow_add, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod _ _).symm

/-- A lane of eight bytes, Horner from the top byte. -/
theorem lane_step {q t : Nat} (hq : q < 2 ^ 56) (ht : t < 2 ^ 8) :
    eOfNat t + eOfNat q * word 256 0 0 = eOfNat (2 ^ 8 * q + t) := by
  rw [word_eq_eOfNat, show (256 : Nat) = 2 ^ 8 from rfl, mul_comm, eOfNat_two_pow_mul (by omega), add_comm,
    eOfNat_add_of_lt ht]

theorem lanes_val (t : Nat → Nat) (ht : ∀ k < 8, t k < 2 ^ 8) {σ : Val} (lane : Nat → V)
    (h0 : σ (lane 0) = eOfNat (t 7))
    (hs : ∀ k' < 7, σ (lane (k' + 1)) = eOfNat (t (6 - k')) + σ (lane k') * word 256 0 0) :
    ∀ k' ≤ 7, σ (lane k') = eOfNat ((∑ k ∈ Finset.range 8, t k * 2 ^ (8 * k)) / 2 ^ (8 * (7 - k'))) := by
  have hL := baseW_lt 8 8 ht
  intro k' hk'
  induction k' with
  | zero =>
      rw [h0]
      congr 1
      have hd := baseW_digit 8 8 ht 7 (by omega)
      rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hL))] at hd
      exact hd.symm
  | succ k' ih =>
      have hq : (∑ k ∈ Finset.range 8, t k * 2 ^ (8 * k)) / 2 ^ (8 * (7 - k')) < 2 ^ 56 :=
        Nat.div_lt_of_lt_mul (lt_of_lt_of_le hL (by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [hs k' (by omega), ih (by omega), lane_step hq (ht _ (by omega))]
      congr 1
      rw [div_pow_step 8 (∑ k ∈ Finset.range 8, t k * 2 ^ (8 * k)) (7 - (k' + 1)),
        baseW_digit 8 8 ht (7 - (k' + 1)) (by omega), show 7 - (k' + 1) + 1 = 7 - k' by omega,
        show 7 - (k' + 1) = 6 - k' by omega]

theorem sum16_split (t : Nat → Nat) :
    ∑ k ∈ Finset.range 16, t k * 2 ^ (8 * k) =
      ∑ k ∈ Finset.range 8, t k * 2 ^ (8 * k) + 2 ^ 64 * ∑ k ∈ Finset.range 8, t (8 + k) * 2 ^ (8 * k) := by
  rw [show 16 = 8 + 8 from rfl, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show 8 * (8 + k) = 64 + 8 * k by ring, pow_add]
  ring

/-- **The lanes are sound**: the sixteen codeword bytes, a byte each, are the digest's first cell,
and the bound its second. -/
theorem sLanes_sound {σ : Val} {wd : Nat → V} {bound : V} {b : Nat} {t : Nat → Nat} (ht : ∀ k < 16, t k < 2 ^ 8)
    (hwd : ∀ k < 16, σ (wd k) = eOfNat (t k)) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (sLanes wd bound b) next kret) :
    σ (.n 17) = lit (∑ k ∈ Finset.range 16, t k * 2 ^ (8 * k)) ∧ σ bound = σ (.n 18) ∧ next := by
  simp only [sLanes, holdsList_append] at h
  rw [holdsList_flatMap_range _ (fun _ => rfl)] at h
  obtain ⟨hb, h⟩ := h
  simp only [cst, mulS, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds] at h hb
  obtain ⟨hy, hm, ha, he17, he18, hn⟩ := h
  have h0 := lanes_val t (fun k hk => ht k (by omega)) (σ := σ)
    (fun k => if k = 0 then wd 7 else .n (b + 6 * (k - 1) + 2)) (by simp [hwd 7 (by omega)])
    (fun k' hk' => by
      obtain ⟨h1, h2, h3, -⟩ := hb k' hk'
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [h3, h2, h1, hwd _ (by omega), show 7 - (k' + 1) = 6 - k' by omega])
  have h1 := lanes_val (fun k => t (8 + k)) (fun k hk => ht _ (by omega)) (σ := σ)
    (fun k => if k = 0 then wd 15 else .n (b + 6 * (k - 1) + 5)) (by simp [hwd 15 (by omega)])
    (fun k' hk' => by
      obtain ⟨-, -, -, h4, h5, h6, -⟩ := hb k' hk'
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [h6, h5, h4, hwd _ (by omega), show 15 - (k' + 1) = 8 + (6 - k') by omega])
  have hL0 := baseW_lt 8 8 (d := t) (fun k hk => ht k (by omega))
  have hL1 := baseW_lt 8 8 (d := fun k => t (8 + k)) (fun k hk => ht _ (by omega))
  refine ⟨?_, (e_add_eq_zero_iff.mp he18), hn⟩
  rw [← e_add_eq_zero_iff.mp he17, ha, hm, hy]
  have e0 := h0 7 le_rfl
  have e1 := h1 7 le_rfl
  simp only [show ¬ ((7 : Nat) = 0) from by decide, ↓reduceIte, Nat.sub_self, Nat.mul_zero, pow_zero,
    Nat.div_one] at e0 e1
  simp only [show ¬ ((7 : Nat) = 0) from by decide, ↓reduceIte]
  have h64 : (2 : Nat) ^ (8 * 8) = 2 ^ 64 := rfl
  rw [h64] at hL0 hL1
  rw [e0, e1, word_y, mul_comm, eOfNat, eOfNat, ofK_add_y_mul_ofK, sum16_split, lit, word,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL0, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt hL0, Nat.zero_add, Nat.mod_eq_of_lt hL1, ofBits_zero]

/-! ## The counter -/

theorem leBytes_zero (k : Nat) : leBytes 0 k = List.replicate k 0 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [getElem_leBytes]

/-- A counter below `2^32` in a cell: its four bytes, then zeros. -/
theorem cellBytes_counter {C : Nat} (hC : C < 2 ^ 32) :
    cellBytes (eOfNat C) = leBytes C 4 ++ List.replicate 12 0 := by
  rw [cellBytes_eOfNat (by omega), show (16 : Nat) = 4 + 12 from rfl, ← leBytes_append,
    Nat.div_eq_of_lt (show C < 256 ^ 4 by norm_num; omega), leBytes_zero]

/-- **The counter is sound**: a counter below `2^32`, and the encoding digest of the forest key
`fk` and the counter's four bytes. -/
theorem sCounter_sound {σ : Val} {fk : V} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (sCounter fk b) next kret) :
    ∃ Cn < 2 ^ 32, σ (.n b) = eOfNat Cn ∧ σ (.n (b + 126 + 1)) = σ (.n 142) + word (tw 4) 0 0 ∧
      σ (.n (b + 126 + 5)) = (hb (cellBytes (σ (.n 1)) ++ cellBytes (σ (.n (b + 126 + 1))) ++ cellBytes (σ fk) ++
        leBytes Cn 4)).1 ∧ next := by
  simp only [sCounter, holdsList_append, hintW, mulS, holdsList_cons_atom, Atom.Holds, true_and, holdsList_nil] at h
  obtain ⟨hb0, h⟩ := h
  rw [holdsList_flatMap_range _ (fun _ => rfl)] at h
  obtain ⟨hblk, h⟩ := h
  simp only [cst, addS, ivs, b2s, holdsList_cons_atom, holdsList_nil, Atom.Holds] at h hblk
  obtain ⟨heq, he, he1, hiv0, hiv1, hmd, hc, hn⟩ := h
  -- the bits
  have hbool : ∀ j < 32, σ (.n (b + 1 + j)) * σ (.n (b + 1 + j)) = σ (.n (b + 1 + j)) := fun j hj => by
    rcases j with _ | j
    · exact hb0.symm
    · exact (hblk j (by omega)).1.symm
  set f : Nat → Bool := fun j => decide (σ (.n (b + 1 + j)) = 1)
  set Cn := bitsVal f 32
  have hCn : Cn < 2 ^ 32 := bitsVal_lt f 32
  have hbits : ∀ j < 32, σ (.n (b + 1 + j)) = bitE (Cn.testBit j) := fun j hj => by
    rw [testBit_bitsVal, decide_eq_true hj, Bool.true_and]
    exact bitE_of_mul_self (hbool j hj)
  -- Horner from the top bit
  have hh : ∀ i' ≤ 30, σ (.n (b + 33 + 3 * i' + 2)) = eOfNat (Cn / 2 ^ (30 - i')) := by
    intro i' hi'
    induction i' with
    | zero =>
        obtain ⟨-, h1, h2, h3, -⟩ := hblk 0 (by omega)
        simp only [↓reduceIte] at h2
        rw [h3, h2, h1, word_two, show b + 32 = b + 1 + 31 by omega, hbits 31 (by omega),
          top_bit (show Cn < 2 ^ (31 + 1) from hCn), show b + 32 - (0 + 1) = b + 1 + 30 by omega,
          hbits 30 (by omega), add_comm, shift_step (by omega)]
    | succ i' ih =>
        obtain ⟨-, h1, h2, h3, -⟩ := hblk (i' + 1) (by omega)
        simp only [Nat.add_one_ne_zero, ↓reduceIte] at h2
        rw [h3, h2, h1, word_two, show b + 33 + 3 * (i' + 1) - 1 = b + 33 + 3 * i' + 2 by omega, ih (by omega),
          show b + 32 - (i' + 1 + 1) = b + 1 + (30 - (i' + 1)) by omega, hbits _ (by omega), add_comm,
          show 30 - i' = 30 - (i' + 1) + 1 by omega, shift_step (by omega)]
  have hC : σ (.n b) = eOfNat Cn := by
    have := hh 30 le_rfl
    rw [show b + 33 + 3 * 30 + 2 = b + 125 by omega, Nat.sub_self, pow_zero, Nat.div_one] at this
    exact (e_add_eq_zero_iff.mp heq).symm.trans this
  refine ⟨Cn, hCn, hC, by rw [he1, he], ?_, hn⟩
  -- the encoding digest
  rw [hiv0, hiv1, hmd, hC] at hc
  have hr : (cellBytes (σ (.n 1)) ++ cellBytes (σ (.n (b + 126 + 1))) ++ cellBytes (σ fk) ++ leBytes Cn 4).length = 52 := by
    simp [length_cellBytes]
  have hc' : CompressCells ![σ (.n 1), σ (.n (b + 126 + 1)), σ fk, eOfNat Cn] iv0 iv1 (σ (.n (b + 126 + 5)))
      (σ (.n (b + 126 + 6)))
      (mdw (cellBytes (σ (.n 1)) ++ cellBytes (σ (.n (b + 126 + 1))) ++ cellBytes (σ fk) ++ leBytes Cn 4).length
        true) := by rw [hr]; exact hc
  obtain ⟨-, ho⟩ := (compress_final_iff (by rw [blockBytes_four, hr]; simp [cellBytes_counter hCn]) (by rw [hr]; omega)).mp hc'
  exact congrArg Prod.fst ho

end
end LeanVM.Guest.B1.Sig
