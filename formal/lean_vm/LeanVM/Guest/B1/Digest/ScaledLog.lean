/-
  LeanVM.Guest.B1.Digest.ScaledLog

  B1 for `scaled_log` (G:2706-2723; TRIAGE #59), the two specializations the claim lists call:
  `2^shift` times the exponent of a g-power below `2^16`, as a bit pattern.
-/

module

public import LeanVM.Guest.B1.Digest.Common

/-!
# `scaled_log`

`scaled_log__L{shift}(x, g_squares)`, `shift ∈ {6, 11}`: sixteen hinted bits, each pinned Boolean
by the write-once `bits[j] = b·b`, weighed into `value = Σ b_j·2^j` and multiplied into
`Π (1 + b_j·(g_squares[g^j] + 1))`, which must be `x`; the result is `value · 2^shift`. With the
table `g_squares[g^j] = g^(2^j)` (`SquaresAt`) the bits are those of the exponent of `x`
(`Bits.prod_gen_pow_of_bool`, `Bits.scaled_log_spec`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The squares table `g_squares[g^j] = g^(2^j)`, `j < 16`, at `p`. -/
def SquaresAt (rd : Reader) (p : E) : Prop := ∀ j < 16, LoadHolds rd p j (gen ^ 2 ^ j)

/-- **`scaled_log__L{shift}(x, g_squares)`**: `x = g^N`, `N < 2^16`, and the result is the bit
pattern of `2^shift · N`. -/
def Meaning_scaled_log (shift : ℕ) (args rets : List E) : Prop :=
  ∃ x gsq v, args = [x, gsq] ∧ rets = [v] ∧ ∃ N < 2 ^ 16, x = gen ^ N ∧ v = eOfNat (2 ^ shift * N)

/-! ## The template -/

/-- The running value after bit `j`. -/
def vIdx (j : ℕ) : ℕ := if j = 0 then 2 else 16 + 10 * j

/-- The running product after bit `j`. -/
def rIdx (j : ℕ) : ℕ := if j = 0 then 23 else 23 + 10 * j

/-- Bit `i + 1`. -/
def slIter (i : ℕ) : List Atom :=
  [.mul (.n (3 + i)) (.n (3 + i)) (.n (3 + i)), .const (.n (24 + 10 * i)) (word (2 ^ (i + 1)) 0 0),
   .mul (.n (25 + 10 * i)) (.n (3 + i)) (.n (24 + 10 * i)),
   .add (.n (vIdx (i + 1))) (.n (vIdx i)) (.n (25 + 10 * i)),
   .const (.n (27 + 10 * i)) (word 1 0 0), .load (.n (28 + 10 * i)) (.n 1) (i + 1),
   .const (.n (29 + 10 * i)) (word 1 0 0), .add (.n (30 + 10 * i)) (.n (28 + 10 * i)) (.n (29 + 10 * i)),
   .mul (.n (31 + 10 * i)) (.n (3 + i)) (.n (30 + 10 * i)),
   .add (.n (32 + 10 * i)) (.n (27 + 10 * i)) (.n (31 + 10 * i)),
   .mul (.n (rIdx (i + 1))) (.n (rIdx i)) (.n (32 + 10 * i))]

/-- The hint of the sixteen bits. -/
def slHint : Atom := .hint (.bitsExp (.n 0) 16 (.stack ((List.range 16).map (fun j => V.n (2 + j)))))

/-- `scaled_log__L{shift}`'s body. -/
def slBody (shift : ℕ) : List Stmt :=
  (slHint ::
    ([.mul (.n 2) (.n 2) (.n 2), .const (.n 18) (word 1 0 0), .load (.n 19) (.n 1) 0,
      .const (.n 20) (word 1 0 0), .add (.n 21) (.n 19) (.n 20), .mul (.n 22) (.n 2) (.n 21),
      .add (.n 23) (.n 18) (.n 22)] : List Atom) ++
    (List.range 15).flatMap slIter ++
    ([.assertEq (.n 173) (.n 0), .const (.n 174) (word (2 ^ shift) 0 0),
      .mul (.n 175) (.n 166) (.n 174)] : List Atom)).map .atom ++ [.ret [.n 175]]

set_option maxRecDepth 100000 in
theorem find_scaled_log_11 : coreProgram.find? "scaled_log__L11" =
    some ⟨"scaled_log__L11", [.n 0, .n 1], slBody 11⟩ :=
  Program.find?_of_indexOf? (j := 461) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_scaled_log_6 : coreProgram.find? "scaled_log__L6" =
    some ⟨"scaled_log__L6", [.n 0, .n 1], slBody 6⟩ :=
  Program.find?_of_indexOf? (j := 495) (by decide +kernel) rfl

/-! ## The running sums -/

/-- The running value over the bits `b`. -/
def slV (b : ℕ → E) : ℕ → E
  | 0 => b 0
  | j + 1 => slV b j + b (j + 1) * eOfNat (2 ^ (j + 1))

/-- The running product over the bits `b` and the table entries `gs`. -/
def slR (b gs : ℕ → E) : ℕ → E
  | 0 => 1 + b 0 * (gs 0 + 1)
  | j + 1 => slR b gs j * (1 + b (j + 1) * (gs (j + 1) + 1))

theorem slV_eq (b : ℕ → E) : ∀ j, j < 64 →
    slV b j = ∑ i ∈ Finset.range (j + 1), b i * coordBasis i
  | 0, _ => by simp [slV, coordBasis_of_lt (show 0 < 64 by omega), eOfNat_one]
  | j + 1, h => by
      rw [slV, slV_eq b j (by omega), Finset.sum_range_succ (n := j + 1), coordBasis_of_lt h]

theorem slR_eq (b gs : ℕ → E) : ∀ j,
    slR b gs j = ∏ i ∈ Finset.range (j + 1), (1 + b i * (gs i + 1))
  | 0 => by simp [slR]
  | j + 1 => by rw [slR, slR_eq b gs j, Finset.prod_range_succ (n := j + 1)]

/-! ## The relation -/

section
variable (x gsq : E) (b : ℕ → E) (shift : ℕ)

/-- The honest values of `scaled_log`. -/
def slVals (k : ℕ) : E :=
  let gs := fun j : ℕ => gen ^ 2 ^ j
  if k = 0 then x else if k = 1 then gsq else if k < 18 then b (k - 2) else
  if k < 24 then [1, gs 0, 1, gs 0 + 1, b 0 * (gs 0 + 1), slR b gs 0].getD (k - 18) 0 else
  if k < 174 then
    [eOfNat (2 ^ ((k - 24) / 10 + 1)), b ((k - 24) / 10 + 1) * eOfNat (2 ^ ((k - 24) / 10 + 1)),
      slV b ((k - 24) / 10 + 1), 1, gs ((k - 24) / 10 + 1), 1, gs ((k - 24) / 10 + 1) + 1,
      b ((k - 24) / 10 + 1) * (gs ((k - 24) / 10 + 1) + 1),
      1 + b ((k - 24) / 10 + 1) * (gs ((k - 24) / 10 + 1) + 1),
      slR b gs ((k - 24) / 10 + 1)].getD ((k - 24) % 10) 0 else
  if k = 174 then eOfNat (2 ^ shift) else slV b 15 * eOfNat (2 ^ shift)

theorem slVals_it (i r : ℕ) (hi : i < 15) (hr : r < 10) :
    slVals x gsq b shift (24 + 10 * i + r) =
      [eOfNat (2 ^ (i + 1)), b (i + 1) * eOfNat (2 ^ (i + 1)), slV b (i + 1), 1, gen ^ 2 ^ (i + 1), 1,
        gen ^ 2 ^ (i + 1) + 1, b (i + 1) * (gen ^ 2 ^ (i + 1) + 1),
        1 + b (i + 1) * (gen ^ 2 ^ (i + 1) + 1),
        slR b (fun j => gen ^ 2 ^ j) (i + 1)].getD r 0 := by
  unfold slVals
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_pos' (by omega), show (24 + 10 * i + r - 24) / 10 = i by omega,
    show (24 + 10 * i + r - 24) % 10 = r by omega]

theorem slVals_b (j : ℕ) (hj : j < 16) : slVals x gsq b shift (2 + j) = b j := by
  unfold slVals
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel_left]

theorem slVals_v (j : ℕ) (hj : j < 16) : slVals x gsq b shift (vIdx j) = slV b j := by
  rcases j with _ | i
  · exact slVals_b x gsq b shift 0 (by omega)
  · have := slVals_it x gsq b shift i 2 (by omega) (by omega)
    rw [show 24 + 10 * i + 2 = vIdx (i + 1) by simp [vIdx]; omega] at this
    simpa using this

theorem slVals_r (j : ℕ) (hj : j < 16) :
    slVals x gsq b shift (rIdx j) = slR b (fun j => gen ^ 2 ^ j) j := by
  rcases j with _ | i
  · simp [slVals, rIdx]
  · have := slVals_it x gsq b shift i 9 (by omega) (by omega)
    rw [show 24 + 10 * i + 9 = rIdx (i + 1) by simp [rIdx]; omega] at this
    simpa using this

end

theorem scaled_log_sem_iff (shift : ℕ) (hshift : shift ≤ 48) {C : CallRel} {rd : Reader}
    {gsq : E} (hT : SquaresAt rd gsq) (name : String) (x : E) (rets : List E) :
    Fn.Sem C rd ⟨name, [.n 0, .n 1], slBody shift⟩ [x, gsq] rets ↔
      ∃ v, rets = [v] ∧ ∃ N < 2 ^ 16, x = gen ^ N ∧ v = eOfNat (2 ^ shift * N) := by
  simp only [Fn.Sem, slBody, holdsList_atoms]
  simp only [holdsList_ret, List.forall_mem_cons, List.forall_mem_append, forall_mem_flatMap_range,
    slIter, Atom.Holds, forall_mem_nil_iff, and_true, slHint, true_and, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, ⟨⟨⟨hb0, h18, l19, h20, h21, h22, h23⟩, hit⟩, ha, h174, h175⟩, hr⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl⟩ := hp
    set b : ℕ → E := fun j => σ (.n (2 + j)) with hbdef
    have hb3 : ∀ i, σ (.n (3 + i)) = b (i + 1) := fun i => by
      simp only [hbdef]; rw [show 2 + (i + 1) = 3 + i by omega]
    have hbool : ∀ j < 16, b j * b j = b j := by
      intro j hj
      rcases j with _ | i
      · exact hb0.symm
      · rw [← hb3]; exact (hit i (by omega)).1.symm
    have key : ∀ j < 16, σ (.n (vIdx j)) = slV b j ∧
        σ (.n (rIdx j)) = slR b (fun j => gen ^ 2 ^ j) j := by
      intro j hj
      induction j with
      | zero =>
        refine ⟨rfl, ?_⟩
        show σ (.n 23) = 1 + b 0 * (gen ^ 2 ^ 0 + 1)
        rw [h23, h18, h22, h21, h20, loadHolds_unique l19 (hT 0 (by omega)), word_one]
      | succ i ih =>
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        obtain ⟨-, c24, m25, a26, c27, l28, c29, a30, m31, a32, m33⟩ := hit i (by omega)
        refine ⟨?_, ?_⟩
        · rw [a26, ih1, m25, c24, word_eq_eOfNat, slV, hb3]
        · rw [m33, ih2, a32, c27, m31, a30, c29, loadHolds_unique l28 (hT (i + 1) (by omega)),
            word_one, slR, hb3]
    have h173 : σ (.n 173) = σ (.n 0) := e_add_eq_zero_iff.mp ha
    have hprod := (key 15 (by omega)).2
    rw [show rIdx 15 = 173 from rfl, h173, slR_eq, prod_gen_pow_of_bool hbool] at hprod
    have hN := bitsVal_lt (fun j => decide (b j = 1)) 16
    have hsl := scaled_log_spec (n := 16) (shift := shift) (by omega) (by omega) (by omega)
      (by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)) hbool
      ((prod_gen_pow_of_bool hbool).trans rfl)
    refine ⟨σ (.n 175), hr.symm, _, hN, hprod, ?_⟩
    rw [h175, h174, show 166 = vIdx 15 from rfl, (key 15 (by omega)).1, slV_eq b 15 (by omega),
      word_eq_eOfNat, ← coordBasis_of_lt (by omega)]
    exact hsl.2
  · rintro ⟨v, rfl, N, hN, rfl, rfl⟩
    set b : ℕ → E := fun j => bitE (N.testBit j) with hbdef
    have hbool : ∀ j < 16, b j * b j = b j := fun j _ => bitE_mul_self _
    have hprod : ∏ j ∈ Finset.range 16, (1 + b j * (gen ^ 2 ^ j + 1)) = gen ^ N := by
      rw [prod_bitE_gen_pow, bitsVal_testBit hN]
    have hsl := scaled_log_spec (n := 16) (shift := shift) (by omega)
      (lt_of_lt_of_le hN (by decide)) (by omega)
      (by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)) hbool hprod
    have hv : ∀ i < 15, slVals (gen ^ N) gsq b shift (vIdx i) = slV b i := fun i hi =>
      slVals_v _ _ _ _ i (by omega)
    have hr' : ∀ i < 15, slVals (gen ^ N) gsq b shift (rIdx i) = slR b (fun j => gen ^ 2 ^ j) i :=
      fun i hi => slVals_r _ _ _ _ i (by omega)
    refine ⟨fun w => slVals (gen ^ N) gsq b shift w.idx, rfl,
      ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun i hi => ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    · exact (bitE_mul_self _).symm
    · simp [slVals, word_one]
    · show LoadHolds rd gsq 0 (slVals (gen ^ N) gsq b shift 19)
      simpa [slVals] using hT 0 (by omega)
    · simp [slVals, word_one]
    · simp [slVals]
    · simp [slVals]
    · simp [slVals, slR]
    · have e := slVals_it (gen ^ N) gsq b shift i
      have eb : slVals (gen ^ N) gsq b shift (3 + i) = b (i + 1) := by
        rw [show 3 + i = 2 + (i + 1) by omega]; exact slVals_b _ _ _ _ _ (by omega)
      dsimp only
      rw [eb, show 24 + 10 * i = 24 + 10 * i + 0 by rfl, e 0 hi (by omega),
        show 25 + 10 * i = 24 + 10 * i + 1 by omega, e 1 hi (by omega),
        show 27 + 10 * i = 24 + 10 * i + 3 by omega, e 3 hi (by omega),
        show 28 + 10 * i = 24 + 10 * i + 4 by omega, e 4 hi (by omega),
        show 29 + 10 * i = 24 + 10 * i + 5 by omega, e 5 hi (by omega),
        show 30 + 10 * i = 24 + 10 * i + 6 by omega, e 6 hi (by omega),
        show 31 + 10 * i = 24 + 10 * i + 7 by omega, e 7 hi (by omega),
        show 32 + 10 * i = 24 + 10 * i + 8 by omega, e 8 hi (by omega),
        slVals_v _ _ _ _ (i + 1) (by omega), slVals_v _ _ _ _ i (by omega),
        slVals_r _ _ _ _ (i + 1) (by omega), slVals_r _ _ _ _ i (by omega)]
      refine ⟨(bitE_mul_self _).symm, ?_, rfl, ?_, ?_, hT (i + 1) (by omega), ?_, rfl, rfl, rfl, ?_⟩
      all_goals simp only [List.getD_cons_succ, List.getD_cons_zero, slV, slR, word_eq_eOfNat,
        eOfNat_one]
    · show slVals (gen ^ N) gsq b shift (rIdx 15) + slVals (gen ^ N) gsq b shift 0 = 0
      rw [slVals_r _ _ _ _ 15 (by omega), slR_eq, hprod]
      simp [slVals, e_add_self]
    · simp [slVals, word_eq_eOfNat]
    · show slVals (gen ^ N) gsq b shift 175 = slVals (gen ^ N) gsq b shift (vIdx 15) *
        slVals (gen ^ N) gsq b shift 174
      rw [slVals_v _ _ _ _ 15 (by omega)]
      simp [slVals]
    · show [slVals (gen ^ N) gsq b shift 175] = _
      simp only [slVals]
      simp only [show ¬((175 : ℕ) = 0) by omega, show ¬((175 : ℕ) = 1) by omega,
        show ¬((175 : ℕ) < 18) by omega, show ¬((175 : ℕ) < 24) by omega,
        show ¬((175 : ℕ) < 174) by omega, show ¬((175 : ℕ) = 174) by omega, ↓reduceIte,
        List.cons.injEq, and_true]
      rw [slV_eq b 15 (by omega), ← coordBasis_of_lt (by omega)]
      exact hsl.2

/-- **`scaled_log__L11`**. -/
theorem scaled_log_11_iff {rd : Reader} {gsq : E} (hT : SquaresAt rd gsq) (x : E) (rets : List E) :
    coreProgram.Rel rd "scaled_log__L11" [x, gsq] rets ↔
      ∃ v, rets = [v] ∧ ∃ N < 2 ^ 16, x = gen ^ N ∧ v = eOfNat (2 ^ 11 * N) := by
  rw [rel_of_find find_scaled_log_11]
  exact scaled_log_sem_iff 11 (by omega) hT _ x rets

/-- **`scaled_log__L6`**. -/
theorem scaled_log_6_iff {rd : Reader} {gsq : E} (hT : SquaresAt rd gsq) (x : E) (rets : List E) :
    coreProgram.Rel rd "scaled_log__L6" [x, gsq] rets ↔
      ∃ v, rets = [v] ∧ ∃ N < 2 ^ 16, x = gen ^ N ∧ v = eOfNat (2 ^ 6 * N) := by
  rw [rel_of_find find_scaled_log_6]
  exact scaled_log_sem_iff 6 (by omega) hT _ x rets

end
end LeanVM.Guest.B1.Digest
