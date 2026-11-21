module

public import Quantum.Xmss.FlipCost

@[expose] public section

/-!
# The encoding cost of the selecting reads

A message-digest trial of key `(l, e)` reads its final `h` cell and selects when the trial's digest
`trunc128 (xi + v)` is a codeword. A selecting read flips a state into `Bad` only if the selected
digest is the output of another tail at `msg l e`, and that output is then a codeword. A key's
signer makes about `1 / ρ_c` trials, `ρ_c` the fraction of codeword digests, so the Enc cost of a
key is about `n_cw 2^-128 / ρ_c`, `n_cw` the tails at its message slot whose outputs are
codewords.

* **The codeword fraction** (`cwCount_eq`, `rhoCw_eq`): `cwCount = 323504418562481994618807509487594`
  of the `2^128` digests are codewords (both layers use the same codewords), the number of
  58-digit base-4 words with digit sum 106, counted by a kernel-checked recursion on the digits
  (`card_digitSum`, `digitRow_58_106`). So `rhoCw = cwCount / 2^128` and
  `2^-21 ≤ rhoCw < 2^-20` (`inv_two_pow_21_le_rhoCw`, `rhoCw_lt_inv_two_pow_20`). Every trial
  rate gives `cwCount * 2^960` codeword values (`card_codeword_trunc128`).
* **The codeword-restricted flip count** (`card_flip_readCw_le`, `flipCost_selectReadCw_le`): with
  the memory recording the selection only for codeword values (`cwSel`, `cwUpd`), at most
  `msgCwCount * 2^960` values flip a state, `msgCwCount` the `h` cells whose head-tail lies at
  `msg l e` and whose output is a codeword. The selecting-read term is
  `E ≤ C 2^-128 e` with `e` the weight of the selection reads (`selectReadCwE_le`). In a good
  database the counts of all keys add up to at most the message-slot cells
  (`sum_msgCwCount_le`, `msgSlotCount_le_size`).
* **Survival** (`survive_readH_le`, `survive_selectRead_le`): the outcomes of a trial that leave
  the key unselected weigh at most `w - ρ_c e + p + 2 √(ρ_c e p)`, with `w` the weight of the
  states where the key is unselected, `e` the weight of the selection reads and `p` the rest
  (`readPs`). The read certificate (`re_trace_read_le`, real-valued) applies with the event "key
  unselected": its flip operator is `-ρ_c` on the empty cells (`re_trace_eps_eq`).
* **One key** (`sum_trials_le`, `sum_cost_le`, `encCost_key_le`, `encCost_key_le_pow`): summing the
  survival bound over the trials telescopes, and Cauchy-Schwarz bounds the cross terms:
  `ρ_c ∑ e ≤ (√(w₀ + 2P) + √P)²` for every number of trials (in particular the signer's cap
  `2^32`), and the selecting reads' costs `E + p + 2 √(E p)` sum to at most
  `(√(C 2^-128 / ρ_c · (√(w₀ + 2P) + √P)²) + √P)²`, with `w₀` the weight reaching the first trial,
  `P` the total of the `p` terms and `C` a bound on `msgCwCount` on the key's selection reads; at
  most `(√(C 2^-107 (√(w₀ + 2P) + √P)²) + √P)²`.
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

namespace Quantum.Xmss

open HashSig LeanXmss

/-! ## The codeword count -/

/-- The words of one digit fewer, read at sum `s - d`, or `0` if `d > s`. -/
def rowPrev (l : List ℕ) (s d : ℕ) : ℕ := if d ≤ s then l.getD (s - d) 0 else 0

/-- One step of the digit-sum count: from the counts of `n`-digit base-4 words by digit sum to
those of `n + 1` digits. -/
def rowStep (l : List ℕ) : List ℕ :=
  (List.range (l.length + 3)).map fun s ↦ rowPrev l s 0 + rowPrev l s 1 + rowPrev l s 2 +
    rowPrev l s 3

/-- The counts of `n`-digit base-4 words by digit sum. -/
def digitRow : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => rowStep (digitRow n)

theorem digitRow_58_106 : (digitRow 58).getD 106 0 = 323504418562481994618807509487594 := by
  decide +kernel

theorem length_rowStep (l : List ℕ) : (rowStep l).length = l.length + 3 := by
  simp [rowStep]

theorem rowPrev_eq_zero {l : List ℕ} {s d : ℕ} (h : l.length + d ≤ s) : rowPrev l s d = 0 := by
  unfold rowPrev
  split_ifs
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  · rfl

theorem getD_rowStep (l : List ℕ) (s : ℕ) :
    (rowStep l).getD s 0 = rowPrev l s 0 + rowPrev l s 1 + rowPrev l s 2 + rowPrev l s 3 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hs : s < l.length + 3
  · rw [rowStep, List.getElem?_map, List.getElem?_range hs]
    rfl
  · rw [List.getElem?_eq_none (by rw [length_rowStep]; omega),
      rowPrev_eq_zero (show l.length + 0 ≤ s by omega),
      rowPrev_eq_zero (show l.length + 1 ≤ s by omega),
      rowPrev_eq_zero (show l.length + 2 ≤ s by omega),
      rowPrev_eq_zero (show l.length + 3 ≤ s by omega)]
    rfl

/-- **The digit-sum count**: `(digitRow n).getD s 0` words of `n` base-4 digits sum to `s`. -/
theorem card_digitSum (n s : ℕ) :
    (Finset.univ.filter fun w : Fin n → Fin 4 ↦ ∑ i, (w i).val = s).card =
      (digitRow n).getD s 0 := by
  induction n generalizing s with
  | zero =>
    rcases s with _ | s
    · simp [digitRow]
    · simp [digitRow]
  | succ n ih =>
    have hd : ∀ d : ℕ, (∑ w : Fin n → Fin 4, if d + ∑ i, (w i).val = s then 1 else 0) =
        rowPrev (digitRow n) s d := fun d ↦ by
      unfold rowPrev
      split_ifs with hds
      · rw [← ih, Finset.card_filter]
        exact Finset.sum_congr rfl fun w _ ↦ if_congr (by omega) rfl rfl
      · exact Finset.sum_eq_zero fun w _ ↦ ite_eq_right (by omega)
    rw [digitRow, getD_rowStep, Finset.card_filter, ← (Fin.consEquiv fun _ ↦ Fin 4).sum_comp,
      Fintype.sum_prod_type, Fin.sum_univ_four, ← hd 0, ← hd 1, ← hd 2, ← hd 3]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rfl

/-- The digits of a digest. -/
theorem digestDigits_val {n : ℕ} (d : Digest) (i : Fin n) :
    (digestDigits d i).val = d.toNat / 4 ^ i.val % 4 := by
  simp only [digestDigits, BitVec.val_toFin, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    winternitzBits, pow_mul]
  norm_num

/-- **A codeword, by its number**: below `4^58`, with base-4 digit sum 106. -/
theorem codeword_valid_iff (d : Digest) :
    Codeword.Valid d ↔ d.toNat < 4 ^ 58 ∧ ∑ i : Fin 58, d.toNat / 4 ^ i.val % 4 = 106 := by
  have h4 : (2 : ℕ) ^ (winternitzBits * chainCount) = 4 ^ 58 := by
    norm_num [winternitzBits, chainCount]
  refine Iff.and ?_ ?_
  · rw [h4, Nat.div_eq_zero_iff]
    simp
  · simp only [Codeword.sum, digestDigits_val]
    exact Iff.rfl

/-- The codeword digests. -/
def cwCount : ℕ := (Finset.univ.filter fun d : Digest ↦ Codeword.Valid d).card

theorem four_pow_lt : (4 : ℕ) ^ 58 < 2 ^ digestBits := by
  norm_num [digestBits]

/-- The number of a base-4 word, as a digest. -/
def wordDigest (w : Fin 58 → Fin 4) : Digest := BitVec.ofNat digestBits (finFunctionFinEquiv w)

theorem toNat_wordDigest (w : Fin 58 → Fin 4) :
    (wordDigest w).toNat = finFunctionFinEquiv w := by
  rw [wordDigest, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ((finFunctionFinEquiv w).isLt.trans four_pow_lt)]

/-- The base-4 word of a digest below `4^58`. -/
def digestWord (d : Digest) : Fin 58 → Fin 4 :=
  finFunctionFinEquiv.symm ⟨d.toNat % 4 ^ 58, Nat.mod_lt _ (by positivity)⟩

theorem digestWord_val (d : Digest) (i : Fin 58) :
    (digestWord d i).val = d.toNat % 4 ^ 58 / 4 ^ i.val % 4 := by
  rw [digestWord, finFunctionFinEquiv_symm_apply_val]

/-- **The codewords are the base-4 words of 58 digits with digit sum 106.** -/
def codewordEquiv : {d : Digest // Codeword.Valid d} ≃
    {w : Fin 58 → Fin 4 // ∑ i, (w i).val = 106} where
  toFun d := ⟨digestWord d.1, by
    obtain ⟨hlt, hsum⟩ := (codeword_valid_iff d.1).1 d.2
    simp only [digestWord_val, Nat.mod_eq_of_lt hlt]
    exact hsum⟩
  invFun w := ⟨wordDigest w.1, by
    rw [codeword_valid_iff, toNat_wordDigest]
    refine ⟨(finFunctionFinEquiv w.1).isLt, ?_⟩
    simp only [← finFunctionFinEquiv_symm_apply_val, Equiv.symm_apply_apply]
    exact w.2⟩
  left_inv d := by
    obtain ⟨hlt, -⟩ := (codeword_valid_iff d.1).1 d.2
    refine Subtype.ext (BitVec.eq_of_toNat_eq ?_)
    change (wordDigest (digestWord d.1)).toNat = d.1.toNat
    rw [toNat_wordDigest, digestWord, Equiv.apply_symm_apply]
    exact Nat.mod_eq_of_lt hlt
  right_inv w := by
    refine Subtype.ext ?_
    change digestWord (wordDigest w.1) = w.1
    rw [digestWord, Equiv.symm_apply_eq]
    apply Fin.ext
    change (wordDigest w.1).toNat % 4 ^ 58 = (finFunctionFinEquiv w.1 : ℕ)
    rw [toNat_wordDigest, Nat.mod_eq_of_lt (finFunctionFinEquiv w.1).isLt]

/-- The codewords are the words of 58 base-4 digits with digit sum 106. -/
theorem cwCount_eq_card_words :
    cwCount = (Finset.univ.filter fun w : Fin 58 → Fin 4 ↦ ∑ i, (w i).val = 106).card := by
  rw [cwCount, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr codewordEquiv

/-- **The number of codewords** among the `2^128` digests. -/
theorem cwCount_eq : cwCount = 323504418562481994618807509487594 := by
  rw [cwCount_eq_card_words, card_digitSum, digitRow_58_106]

/-- **The codeword fraction** `ρ_c`: the probability that a uniform digest is a codeword. -/
noncomputable def rhoCw : ℝ := cwCount / 2 ^ 128

theorem rhoCw_eq : rhoCw = 323504418562481994618807509487594 / 2 ^ 128 := by
  rw [rhoCw, cwCount_eq]
  norm_num

/-- **`ρ_c ≥ 2^-21`**, the best power of two below it (`rhoCw_lt_inv_two_pow_20`). -/
theorem inv_two_pow_21_le_rhoCw : (2 ^ 21 : ℝ)⁻¹ ≤ rhoCw := by
  rw [rhoCw_eq]
  norm_num

theorem rhoCw_lt_inv_two_pow_20 : rhoCw < (2 ^ 20 : ℝ)⁻¹ := by
  rw [rhoCw_eq]
  norm_num

theorem rhoCw_pos : 0 < rhoCw :=
  lt_of_lt_of_le (by norm_num) inv_two_pow_21_le_rhoCw

theorem inv_rhoCw_le : rhoCw⁻¹ ≤ 2 ^ 21 := by
  rw [inv_le_comm₀ rhoCw_pos (by norm_num)]
  exact inv_two_pow_21_le_rhoCw

/-- **Translated fibers**: if every fiber of `out` has `F` elements, the `v` with
`Qo (out (xi + v))` number `|Qo| F`. -/
theorem card_filter_out_add {A Y : Type} [Fintype A] [AddGroup A] [Fintype Y] [DecidableEq Y]
    {out : A → Y} {F : ℕ} (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card = F)
    (Qo : Y → Prop) [DecidablePred Qo] (xi : A) :
    (Finset.univ.filter fun v ↦ Qo (out (xi + v))).card = (Finset.univ.filter Qo).card * F := by
  have htr : (Finset.univ.filter fun v ↦ Qo (out (xi + v))).card =
      (Finset.univ.filter fun x ↦ Qo (out x)).card := by
    refine Finset.card_nbij' (xi + ·) (-xi + ·) ?_ ?_ ?_ ?_
    · intro v hv
      simpa using hv
    · intro v hv
      simpa using hv
    · intro v _
      simp
    · intro v _
      simp
  rw [htr, Finset.card_eq_sum_card_fiberwise (f := out) (t := Finset.univ.filter Qo)
    fun x hx ↦ by simpa using hx]
  rw [Finset.sum_congr rfl fun d hd ↦ ?_, Finset.sum_const, smul_eq_mul]
  rw [Finset.filter_filter, ← hF d]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  rintro rfl
  simpa using hd

/-- **Each trial rate gives `cwCount * 2^960` codeword values** of the read cell. -/
theorem card_codeword_trunc128 (xi : X) :
    (Finset.univ.filter fun v : X ↦ Codeword.Valid (trunc128 (xi + v))).card =
      cwCount * 2 ^ 960 := by
  -- `cwCount` is unfolded by `rw`: a kernel check of `cwCount * _` against the count would try to
  -- evaluate both to literals.
  rw [cwCount]
  exact card_filter_out_add (out := trunc128) (F := 2 ^ 960) (fun d ↦ card_fiber_trunc128 d)
    (fun d ↦ Codeword.Valid d) xi

end Quantum.Xmss

/-! ## Flip counts restricted by the output -/

namespace Quantum.Sponge

open Quantum

/-! ## A real-valued read certificate -/

section operator

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- **The read-port bound on weights, over the reals**: as `ofReal_trace_read_le`, without
truncating `ε = tr (P' F P' σ)` at `0`. A read that lowers the weight of `Q` on the states outside
`P` has `ε < 0`. -/
theorem re_trace_read_le (K : ι → Matrix n n ℂ) (hK : ∑ r, (K r)ᴴ * K r = 1)
    (Q P : Matrix n n ℂ) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) (hP : Pᴴ = P) (hPP : P * P = P)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    let F := ∑ r, (K r)ᴴ * Q * K r - Q
    ((∑ r, (K r)ᴴ * Q * K r) * σ).trace.re ≤
      (Q * σ).trace.re + ((1 - P) * F * (1 - P) * σ).trace.re + (P * σ).trace.re +
        2 * √(((1 - P) * F * P * F * (1 - P) * σ).trace.re * (P * σ).trace.re) := by
  intro F
  set w' := ((∑ r, (K r)ᴴ * Q * K r) * σ).trace.re
  set w := (Q * σ).trace.re
  set e := ((1 - P) * F * (1 - P) * σ).trace.re
  set e' := ((1 - P) * F * P * F * (1 - P) * σ).trace.re
  set p := (P * σ).trace.re
  have hPpos : P.PosSemidef := by
    rw [← hPP]
    nth_rewrite 1 [← hP]
    exact posSemidef_conjTranspose_mul_self P
  have hp : 0 ≤ p := hPpos.trace_mul_re_nonneg hσ
  have he' : 0 ≤ e' := by
    have hFh : Fᴴ = F := by
      simp only [F, conjTranspose_sub, conjTranspose_sum, conjTranspose_mul,
        conjTranspose_conjTranspose, hQ, Matrix.mul_assoc]
    have h : (1 - P) * F * P * F * (1 - P) = ((1 - P) * F * P) * ((1 - P) * F * P)ᴴ := by
      simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hP, hFh,
        Matrix.mul_assoc, ← Matrix.mul_assoc P P, hPP]
    rw [show e' = ((1 - P) * F * P * F * (1 - P) * σ).trace.re from rfl, h]
    exact (posSemidef_self_mul_conjTranspose _).trace_mul_re_nonneg hσ
  have hle : ∀ s : ℝ, 0 < s → w' - w - e + e' ≤ (1 + s) * p + (1 + s⁻¹) * e' := fun s hs ↦ by
    have h := (posSemidef_read_certificate K hK Q P hQ hQQ hP hPP hs).trace_mul_re_nonneg hσ
    rw [Matrix.sub_mul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, Complex.sub_re, Complex.add_re, Complex.add_re,
      Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul] at h
    change 0 ≤ w + e + s⁻¹ * e' + (1 + s) * p - w' at h
    nlinarith
  have hopt := Real.le_sq_sqrt_add_sqrt_of_forall hp he' hle
  rw [Real.sqrt_mul he']
  rw [add_sq, Real.sq_sqrt hp, Real.sq_sqrt he'] at hopt
  nlinarith [Real.sqrt_nonneg p, Real.sqrt_nonneg e']

end operator

/-! ## The diagonal of the flip operator on the empty cells -/

section core

variable {n Y R M0 : Type} [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y]
  [Fintype R] [DecidableEq R] [Fintype M0] [DecidableEq M0]
  {e : n ≃ Option Y × R} {act : R → Prop} {μ : R → M0} {τ : Option Y → R → R}
  {K : Option Y × M0 → Matrix n n ℂ} (S : Set n) [DecidablePred (· ∈ S)]
  (gd : R → Prop) [DecidablePred gd] [Nonempty Y]

/-- **The `ε` term of a cell read, exactly**: `re tr (P' F P' σ)` is the sum over the empty cells
of selected rests of the diagonal of `F`, `(∑ g) / N - 1_S`, times `σ_ss`. -/
theorem re_trace_eps_eq (h : CellRead e act μ τ K) (hgd : ∀ r, gd r → act r)
    (σ : Matrix n n ℂ) :
    ((1 - readP e gd) * flipOp K S * (1 - readP e gd) * σ).trace.re =
      ∑ s, if gd (e s).2 ∧ (e s).1 = none then
        ((∑ y, gw e τ S (some y) (e s).2) / Fintype.card Y - q0 e S (e s).2) * (σ s s).re
          else 0 := by
  rw [one_sub_readP, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [trace_mul_apply, Finset.sum_eq_single s]
  · rw [projE, mul_diagonal, diagonal_mul]
    by_cases hs : gd (e s).2 ∧ (e s).1 = none
    · rw [ite_eq_left hs, flipOp_diag S gd h hgd hs]
      simp only [pe, hs, and_self, ↓reduceIte, one_mul, mul_one, Complex.re_ofReal_mul]
    · simp [pe, hs]
  · intro t _ hts
    rw [projE, mul_diagonal, diagonal_mul]
    by_cases hs : gd (e s).2 ∧ (e s).1 = none
    · by_cases ht : gd (e t).2 ∧ (e t).1 = none
      · have hr : (e s).2 ≠ (e t).2 := fun hr ↦ hts (eq_of_rest hr (hs.2.trans ht.2.symm)).symm
        rw [flipOp_eq_zero S h (hgd _ ht.1) hr]
        simp
      · simp [pe, ht]
    · simp [pe, hs]
  · simp

end core

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] {Y M : Type} {π : Equiv.Perm (X × Z)} {out : X → Y}
  {tgt : Hw X Z → M → List X → Option Y} {N : ℕ}

open scoped Classical in
/-- The `h` cells of `U` whose head-tail satisfies `P` and whose output satisfies `Qo`. -/
noncomputable def tailOutCount (π : Equiv.Perm (X × Z)) (U : Dbs X Z) (out : X → Y)
    (P : List X → Prop) (Qo : Y → Prop) : ℕ :=
  (Finset.univ.filter fun z : Z ↦
    ∃ t xi w, P t ∧ IsHeadTail π U t z xi ∧ U.h z = some w ∧ Qo (out (xi + w))).card

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
theorem tailOutCount_le_tailCount (π : Equiv.Perm (X × Z)) (U : Dbs X Z) (out : X → Y)
    (P : List X → Prop) (Qo : Y → Prop) : tailOutCount π U out P Qo ≤ tailCount π U P := by
  classical
  unfold tailOutCount tailCount
  exact Finset.card_le_card fun z hz ↦ by
    obtain ⟨t, xi, w, hP, hi, hw, -⟩ := (Finset.mem_filter.1 hz).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, t, xi, w, hP, hi, hw⟩

omit [DecidableEq Z] in
open scoped Classical in
/-- **At most `tailOutCount * F` values flip a new target with an output in `Qo`**: as
`card_flips_le`, the values `v` with `Qo (out (xi + v))` for which a tail satisfying `P`, other
than `t₀`, reaches `out (xi + v)`; that tail's cell has an output in `Qo`. -/
theorem card_flips_out_le [DecidableEq Y] {U : Dbs X Z} (hG : Good π U) {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (P : List X → Prop)
    (Qo : Y → Prop) (t₀ : List X) (xi : X) :
    (Finset.univ.filter fun v : X ↦ Qo (out (xi + v)) ∧
      ∃ t, P t ∧ t ≠ t₀ ∧ Reaches π U out t (out (xi + v))).card ≤
        tailOutCount π U out P Qo * F := by
  let C := Finset.univ.filter fun z : Z ↦
    ∃ t xi w, P t ∧ IsHeadTail π U t z xi ∧ U.h z = some w ∧ Qo (out (xi + w))
  let S : Z → Finset X := fun z ↦ Finset.univ.filter fun v : X ↦ ∃ t xi' w,
    IsHeadTail π U t z xi' ∧ U.h z = some w ∧ out (xi + v) = out (xi' + w)
  have hsub : (Finset.univ.filter fun v : X ↦ Qo (out (xi + v)) ∧
      ∃ t, P t ∧ t ≠ t₀ ∧ Reaches π U out t (out (xi + v))) ⊆ C.biUnion S := by
    intro v hv
    obtain ⟨hQ, t, hP, -, z, xi', w, hi, hw, hy⟩ := (Finset.mem_filter.1 hv).2
    exact Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨Finset.mem_univ _, t, xi', w, hP, hi,
      hw, hy ▸ hQ⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, t, xi', w, hi, hw, hy⟩⟩
  have hS : ∀ z ∈ C, (S z).card ≤ F := by
    intro z _
    rcases Finset.eq_empty_or_nonempty (S z) with he | ⟨v0, hv0⟩
    · simp [he]
    obtain ⟨t0, xi0, w0, hi0, hw0, -⟩ := (Finset.mem_filter.1 hv0).2
    refine card_le_of_out_translate hF xi (out (xi0 + w0)) fun v hv ↦ ?_
    obtain ⟨t, xi', w, hi, hw, hy⟩ := (Finset.mem_filter.1 hv).2
    obtain ⟨rfl, rfl⟩ := hG.isHeadTail_unique hi hi0
    obtain rfl := Option.some_injective _ (hw.symm.trans hw0)
    exact hy
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul C S _ hS)

open scoped Classical in
/-- **A read of an `h` cell whose new targets are outputs in `Qo`**: as `card_flip_readH_le`,
when the memory `m' v` after reading `v` adds targets `out (xi + v)` only if
`Qo (out (xi + v))`, at most `tailOutCount * F` values flip a state outside the event into it. -/
theorem card_flip_readH_out_le [DecidableEq Y] {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) {D : DbReg X Z} {W : Hw X Z}
    {m : M} (hs : (D, W, m) ∉ HwTargetBad π out tgt N) {z : Z} (hW : W.1 z = none)
    (hD : D.1 z = none) (P : List X → Prop) (Qo : Y → Prop) (t₀ : List X) (xi : X)
    (m' : X → M)
    (hext : ∀ v t y, tgt W (m' v) t = some y →
      tgt W m t = some y ∨ (Qo (out (xi + v)) ∧ P t ∧ t ≠ t₀ ∧ y = out (xi + v)))
    (hhead : Good π (union W D) → ∀ v t xi', IsHeadTail π (union W D) t z xi' →
      tgt W (m' v) t = none) :
    (Finset.univ.filter fun v : X ↦ ∃ u : Option X,
      ((Function.update D.1 z u, D.2), W, m' v) ∈ HwTargetBad π out tgt N).card ≤
        tailOutCount π (union W D) out P Qo * F := by
  by_cases hN : dbGrade W ≤ N
  · have hG := (not_mem_targetBad_iff.1 (union_not_mem_of_not_mem_hwTargetBad hs hN)).1
    refine le_trans (Finset.card_le_card fun v hv ↦ ?_) (card_flips_out_le hG hF P Qo t₀ xi)
    obtain ⟨u, hu⟩ := (Finset.mem_filter.1 hv).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    by_contra hf
    exact not_mem_readH hs hW hD
      (Q := fun t y ↦ Qo (out (xi + v)) ∧ P t ∧ t ≠ t₀ ∧ y = out (xi + v)) (hext v)
      (fun t y ⟨hQ, hP, hne, hy⟩ hr ↦ hf ⟨hQ, t, hP, hne, hy ▸ hr⟩) (fun hG' ↦ hhead hG' v) u hu
  · rw [Finset.filter_false_of_mem fun v _ ⟨_, hu⟩ ↦ hN hu.1]
    simp

omit [Fintype X] [DecidableEq X] in
/-- **Exclusive predicates share the cells**: in a good database each cell has one head-tail, so
for predicates no tail satisfies twice, the counts add up to at most the cells of their union. -/
theorem sum_tailOutCount_le {κ : Type} [Fintype κ] {U : Dbs X Z} (hG : Good π U)
    (P : κ → List X → Prop) (hP : ∀ k k' t, P k t → P k' t → k = k') (Qo : Y → Prop) :
    ∑ k, tailOutCount π U out (P k) Qo ≤ tailCount π U fun t ↦ ∃ k, P k t := by
  classical
  unfold tailOutCount tailCount
  rw [← Finset.card_biUnion]
  · refine Finset.card_le_card fun z hz ↦ ?_
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 hz
    obtain ⟨t, xi, w, hPt, hi, hw, -⟩ := (Finset.mem_filter.1 hk).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, t, xi, w, ⟨k, hPt⟩, hi, hw⟩
  · intro k _ k' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨t, xi, w, hPt, hi, -, -⟩ := (Finset.mem_filter.1 hz).2
    obtain ⟨t', xi', w', hPt', hi', -, -⟩ := (Finset.mem_filter.1 hz').2
    obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hi'
    exact hne (hP k k' t hPt hPt')

end Quantum.Sponge

/-! ## Survival of a read -/

namespace Quantum.Sponge

open Quantum

section survive

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

/-- The states whose memory lies in `T`. -/
def memEvent (T : Set M) : Set (HwReg X Z M) := {s | s.2.2 ∈ T}

instance (T : Set M) [DecidablePred (· ∈ T)] :
    DecidablePred (· ∈ (memEvent T : Set (HwReg X Z M))) :=
  fun s ↦ inferInstanceAs (Decidable (s.2.2 ∈ T))

/-- **The memory event after a read with outcome `r`**: the read writes the memory
`upd r.2 r.1`, so the Kraus operator lands in the event or outside it. -/
theorem indProj_memEvent_mul [Nonempty X] (z : Z) (upd : M → Option X → M) (T : Set M)
    [DecidablePred (· ∈ T)] (r : Option X × M) :
    indProj (liftSet (memEvent T : Set (HwReg X Z M))) * hwReadKraus (.readH z upd) r =
      if upd r.2 r.1 ∈ T then hwReadKraus (.readH z upd) r else 0 := by
  change indProj (liftSet (memEvent T : Set (HwReg X Z M))) *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd r) =
    if upd r.2 r.1 ∈ T then (1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd r else 0
  ext ⟨⟨⟩, s'⟩ ⟨⟨⟩, s⟩
  rw [indProj, diagonal_mul]
  by_cases hK : ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd r) ((), s') ((), s) = 0
  · rw [hK, mul_zero]
    split_ifs
    · exact hK.symm
    · rfl
  have hm : s'.2.2 = upd r.2 r.1 := by
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, readKrausH, clsKraus_apply] at hK
    split_ifs at hK with hc
    · rw [hc.2]
    · exact absurd rfl hK
  have hind : ind (liftSet (memEvent T : Set (HwReg X Z M))) ((), s') =
      if upd r.2 r.1 ∈ T then 1 else 0 := by
    unfold ind
    by_cases hu : upd r.2 r.1 ∈ T
    · rw [ite_eq_left hu]
      exact ite_eq_left (show s'.2.2 ∈ T by rw [hm]; exact hu)
    · rw [ite_eq_right hu]
      exact ite_eq_right (show ¬ s'.2.2 ∈ T by rw [hm]; exact hu)
  rw [hind]
  split_ifs
  · simp
  · simp

/-- The weight of a basis event. -/
theorem re_trace_indProj_eq {n : Type} [Fintype n] [DecidableEq n] (S : Set n)
    [DecidablePred (· ∈ S)] (σ : Matrix n n ℂ) :
    (indProj S * σ).trace.re = ∑ s, if s ∈ S then (σ s s).re else 0 := by
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Matrix.diag_apply, indProj, diagonal_mul, Complex.re_ofReal_mul, ind]
  split_ifs <;> simp

/-- The trace splits into the states of `SR` and the rest. -/
theorem re_trace_eq_add (SR : HwReg X Z M → Prop) [DecidablePred SR]
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    σ.trace.re = (∑ q, if SR q.2 then (σ q q).re else 0) + (readPs SR * σ).trace.re := by
  rw [Matrix.trace, Matrix.trace, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, readPs, diagonal_mul]
  split_ifs <;> simp

theorem re_trace_readPs_nonneg (SR : HwReg X Z M → Prop) [DecidablePred SR]
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ (readPs SR * σ).trace.re := by
  rw [readPs, Matrix.trace, Complex.re_sum]
  refine Finset.sum_nonneg fun q _ ↦ ?_
  rw [Matrix.diag_apply, diagonal_mul]
  have hre : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  split_ifs <;> simp [hre]

/-- **Survival of a read of an `h` cell**: let the read keep the memory in `T` exactly for the
values outside `good`, a fraction `1 - ρ` of the cell's values, from every memory in `T`. Then the
outcomes that keep the memory in `T` weigh at most `w - ρ e + p + 2 √(ρ e p)`, with `w` the weight
of the memories in `T`, `e` the weight of the states of `SR` (cell empty and not hardwired, memory
in `T`) and `p = tr (P σ)` the rest. On an empty cell the outcome is uniform; the recorded cells
interfere through `p` only. -/
theorem survive_readH_le [Nonempty X] (z : Z) (upd : M → Option X → M) (T : Set M)
    [DecidablePred (· ∈ T)] (good : X → Prop) [DecidablePred good] {ρ : ℝ}
    (hρ : ((Finset.univ.filter good).card : ℝ) / Fintype.card X = ρ)
    (hupd : ∀ m ∈ T, ∀ v, upd m (some v) ∈ T ↔ ¬ good v)
    (SR : HwReg X Z M → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → s.1.1 z = none ∧ s.2.1.1 z = none ∧ s.2.2 ∈ T)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    (∑ r : Option X × M, if upd r.2 r.1 ∈ T then
        (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ).trace.re else 0) ≤
      (∑ q, if q.2.2.2 ∈ T then (σ q q).re else 0) -
        ρ * (∑ q, if SR q.2 then (σ q q).re else 0) + (readPs SR * σ).trace.re +
        2 * √(ρ * (∑ q, if SR q.2 then (σ q q).re else 0) * (readPs SR * σ).trace.re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  obtain ⟨es, hes⟩ : ∃ es : ℝ, es = ∑ q, if SR q.2 then (σ q q).re else 0 := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (readPs SR * σ).trace.re := ⟨_, rfl⟩
  rw [← hes, ← hp]
  have hp0 : 0 ≤ p := hp ▸ re_trace_readPs_nonneg SR hσ
  set U : Set (HwReg X Z M) := memEvent T
  have hQ : (indProj (liftSet U))ᴴ = indProj (liftSet U) ∧
      indProj (liftSet U) * indProj (liftSet U) = indProj (liftSet U) := by
    rw [← one_kronecker_hwProjector]
    exact one_kronecker_hwProjector_proj U
  /- The kept branches are the read followed by the memory event. -/
  have hLHS : (∑ r : Option X × M, if upd r.2 r.1 ∈ T then
      (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ).trace.re else 0) =
      ((∑ r : Option X × M, (hwReadKraus (.readH z upd) r)ᴴ * indProj (liftSet U) *
        hwReadKraus (.readH z upd) r) * σ).trace.re := by
    rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [Matrix.mul_assoc (hwReadKraus (.readH z upd) r)ᴴ, indProj_memEvent_mul]
    split_ifs
    · rw [MatrixMap.trace_conj_apply]
    · simp
  /- The read as a cell read, with `P` the projector off `SR`. -/
  set gd : RestH X M z → Prop := fun r ↦ SR ((splitH' z).symm (none, r)).2
  have : DecidablePred gd := fun r ↦ inferInstanceAs (Decidable (SR _))
  have hgd_iff : ∀ q, (gd (splitH' z q).2 ∧ (splitH' z q).1 = none) ↔ SR q.2 := fun q ↦ by
    constructor
    · rintro ⟨h1, h2⟩
      have h0 : q.2.1.1 z = none := h2
      simpa only [gd, splitH'_symm_none z q h0] using h1
    · intro hq
      have h0 := (hSR _ hq).1
      exact ⟨by simpa only [gd, splitH'_symm_none z q h0] using hq, h0⟩
  have hP : readPs SR = readP (splitH' z) gd := by
    unfold readPs readP pp
    congr 1
    funext q
    exact ite_cond_congr (propext (hgd_iff q)).symm
  have hgdact : ∀ r, gd r → actH z r := fun r h ↦ (hSR _ h).2.1
  have hcell := cellRead_readH (M := M) z upd
  /- On a state of `SR`, the outcome `y` keeps the memory in `T` iff it is not `good`. -/
  have hind : ∀ q : Unit × HwReg X Z M, SR q.2 → ∀ (a : Option X) (y : X),
      ind (liftSet U) ((splitH' z).symm (a, tauH z upd (some y) (splitH' z q).2)) =
        if good y then 0 else 1 := fun q hq a y ↦ by
    have key := hupd _ (hSR _ hq).2.2 y
    rw [splitH'_symm_tau]
    unfold ind
    split_ifs with h1 hv hv
    · exact absurd hv (key.1 h1)
    · rfl
    · rfl
    · exact absurd (key.2 hv) h1
  have hq0 : ∀ q : Unit × HwReg X Z M, SR q.2 → q0 (splitH' z) (liftSet U) (splitH' z q).2 = 1 :=
    fun q hq ↦ by
      rw [q0, splitH'_symm_none z q (hSR _ hq).1]
      unfold ind
      exact ite_eq_left (show q.2.2.2 ∈ T from (hSR _ hq).2.2)
  have hgw : ∀ q : Unit × HwReg X Z M, SR q.2 → ∀ y,
      gw (splitH' z) (tauH z upd) (liftSet U) (some y) (splitH' z q).2 =
        if good y then 0 else 1 := fun q hq y ↦ by
    unfold gw
    simp only [hind q hq]
    rw [← Finset.sum_mul, sum_cr_sq, one_mul]
  have hN : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  have hsum : (∑ y : X, if good y then (0 : ℝ) else 1) =
      Fintype.card X - (Finset.univ.filter good).card := by
    have h : ∀ y : X, (if good y then (0 : ℝ) else 1) = 1 - if good y then 1 else 0 :=
      fun y ↦ by split_ifs <;> norm_num
    rw [Finset.sum_congr rfl fun y _ ↦ h y, Finset.sum_sub_distrib, Finset.sum_boole,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  /- `ε = -ρ e`: the diagonal of the flip operator on a state of `SR` is `(1 - ρ) - 1`. -/
  have hε : ((1 - readPs SR) * flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r)
      (liftSet U) * (1 - readPs SR) * σ).trace.re = -(ρ * es) := by
    rw [hP, re_trace_eps_eq (liftSet U) gd hcell hgdact σ, hes, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [ite_cond_congr (propext (hgd_iff q))]
    by_cases hq : SR q.2
    · rw [ite_eq_left hq, ite_eq_left hq, hq0 q hq]
      simp only [hgw q hq]
      rw [hsum, sub_div, div_self hN.ne', hρ]
      ring
    · rw [ite_eq_right hq, ite_eq_right hq, mul_zero, neg_zero]
  /- `ε' ≤ ρ e`: only the `good` outcomes change the event. -/
  have hε' : ((1 - readPs SR) * flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r)
      (liftSet U) * readPs SR * flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r)
        (liftSet U) * (1 - readPs SR) * σ).trace.re ≤ ρ * es := by
    rw [hP]
    refine (re_trace_eps'_le (liftSet U) gd hcell hgdact hσ).trans ?_
    rw [hes, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [ite_cond_congr (propext (hgd_iff q))]
    by_cases hq : SR q.2
    · rw [ite_eq_left hq, ite_eq_left hq]
      refine mul_le_mul_of_nonneg_right ?_ (hre q)
      rw [← hρ]
      refine div_le_div_of_nonneg_right ((chw_le_card (liftSet U) _).trans
        (Nat.cast_le.2 (Finset.card_le_card fun y hy ↦ ?_))) hN.le
      obtain ⟨a, ha⟩ := (Finset.mem_filter.1 hy).2
      rw [hind q hq, hq0 q hq] at ha
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra hv
      exact ha (ite_eq_right hv)
    · rw [ite_eq_right hq, ite_eq_right hq, mul_zero]
  have hcert : ((∑ r : Option X × M, (hwReadKraus (.readH z upd) r)ᴴ * indProj (liftSet U) *
        hwReadKraus (.readH z upd) r) * σ).trace.re ≤
      (indProj (liftSet U) * σ).trace.re +
        ((1 - readPs SR) * flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r)
          (liftSet U) * (1 - readPs SR) * σ).trace.re + (readPs SR * σ).trace.re +
        2 * √(((1 - readPs SR) * flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r)
          (liftSet U) * readPs SR * flipOp (fun r : Option X × M ↦
            hwReadKraus (.readH z upd) r) (liftSet U) * (1 - readPs SR) * σ).trace.re *
          (readPs SR * σ).trace.re) :=
    re_trace_read_le (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r)
      (sum_readKrausH z upd) _ (readPs SR) hQ.1 hQ.2 (readPs_proj SR).1 (readPs_proj SR).2 hσ
  rw [hε, ← hp] at hcert
  have hsq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hε' hp0)
  have hw : (indProj (liftSet U) * σ).trace.re = ∑ q, if q.2.2.2 ∈ T then (σ q q).re else 0 :=
    re_trace_indProj_eq (liftSet U) σ
  rw [hLHS, ← hw]
  linarith

end survive

end Quantum.Sponge

namespace Quantum.Xmss

open Quantum Quantum.Sponge HashSig LeanXmss

variable {L : HonestTable} {N : ℕ}

/-! ## The codeword-restricted flip count -/

/-- The `h` cells of `U` whose head-tail lies at the message slot of key `e` of layer `l` and
whose output is a codeword: the tails at that slot that reach a codeword. -/
noncomputable def msgCwCount (L : HonestTable) (U : Dbs X Z) (l : Layer) (e : KeyIndex) : ℕ :=
  tailOutCount L.perm U trunc128 (fun t ↦ slotOf L.param t = some (.msg l e)) Codeword.Valid

theorem msgCwCount_le_msgCount (L : HonestTable) (U : Dbs X Z) (l : Layer) (e : KeyIndex) :
    msgCwCount L U l e ≤ msgCount L U l e :=
  tailOutCount_le_tailCount _ _ _ _ _

/-- The `h` cells of `U` whose head-tail lies at a message slot. -/
noncomputable def msgSlotCount (L : HonestTable) (U : Dbs X Z) : ℕ :=
  tailCount L.perm U fun t ↦ ∃ k : Layer × KeyIndex, slotOf L.param t = some (.msg k.1 k.2)

theorem msgSlotCount_le_size (L : HonestTable) (U : Dbs X Z) : msgSlotCount L U ≤ U.h.size :=
  tailCount_le_size _ _ _

/-- **The keys share the message-slot cells**: in a good database each cell has one head-tail,
at one slot, so the codeword counts of all keys add up to at most the message-slot cells. -/
theorem sum_msgCwCount_le {U : Dbs X Z} (hG : Good L.perm U) :
    ∑ k : Layer × KeyIndex, msgCwCount L U k.1 k.2 ≤ msgSlotCount L U := by
  have hP : ∀ (k k' : Layer × KeyIndex) (t : List X),
      slotOf L.param t = some (.msg k.1 k.2) → slotOf L.param t = some (.msg k'.1 k'.2) →
        k = k' := fun k k' t h h' ↦ by
    obtain ⟨h1, h2⟩ := Slot.msg.inj (Option.some.inj (h.symm.trans h'))
    exact Prod.ext h1 h2
  -- Named arguments: unifying the generic sum with this one would unfold `Finset.univ`.
  have h := sum_tailOutCount_le (κ := Layer × KeyIndex) (π := L.perm) (out := trunc128) hG
    (fun k t ↦ slotOf L.param t = some (.msg k.1 k.2)) hP Codeword.Valid
  exact h

/-- **The memory after a trial read** of key `(l, e)` with block `x`, rate `xi` and value `v`:
the selection if the digest is a codeword. -/
noncomputable def cwSel (m : Selections) (l : Layer) (e : KeyIndex) (x xi v : X) : Selections :=
  if Codeword.Valid (trunc128 (xi + v)) then m.select l e x (trunc128 (xi + v)) else m

/-- **The memory update of a trial read**: select a codeword digest of an unselected key. -/
noncomputable def cwUpd (l : Layer) (e : KeyIndex) (x xi : X) :
    Selections → Option X → Selections
  | m, some v => if m l e = none then cwSel m l e x xi v else m
  | m, none => m

theorem cwUpd_some (l : Layer) (e : KeyIndex) (x xi : X) (m : Selections) (v : X) :
    cwUpd l e x xi m (some v) = m ∨ cwUpd l e x xi m (some v) = cwSel m l e x xi v := by
  show (if m l e = none then cwSel m l e x xi v else m) = m ∨
    (if m l e = none then cwSel m l e x xi v else m) = cwSel m l e x xi v
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

theorem cwUpd_some_of_none (l : Layer) (e : KeyIndex) (x xi : X) {m : Selections}
    (hm : m l e = none) (v : X) : cwUpd l e x xi m (some v) = cwSel m l e x xi v :=
  ite_eq_left hm

/-- A trial of an unselected key leaves it unselected exactly when its digest is no codeword. -/
theorem cwSel_eq_none_iff {m : Selections} {l : Layer} {e : KeyIndex} (hm : m l e = none)
    (x xi v : X) : cwSel m l e x xi v l e = none ↔ ¬ Codeword.Valid (trunc128 (xi + v)) := by
  unfold cwSel
  split_ifs with hv
  · have h : m.select l e x (trunc128 (xi + v)) l e = some (x, trunc128 (xi + v)) := by
      simp only [Selections.select, Function.update_self]
    rw [h]
    exact iff_of_false (Option.some_ne_none _) (not_not.2 hv)
  · exact iff_of_true hm hv

open scoped Classical in
/-- **`card_flip_readCw_le`**: a trial read of key `(l, e)` that records the selection only for a
codeword digest flips a state outside `Bad` for at most `msgCwCount * 2^960` values of the read
cell: the flips are the codeword outputs of the other tails at `msg l e`. -/
theorem card_flip_readCw_le {D : DbReg X Z} {W : Hw X Z} {m : Selections} {z : Z} {l : Layer}
    {e : KeyIndex} {x xi : X} (hs : (D, W, m) ∉ Bad L N) (hr : SelectRead L D W m z l e x xi) :
    (Finset.univ.filter fun v : X ↦ ∃ u : Option X,
      ((Function.update D.1 z u, D.2), W, cwSel m l e x xi v) ∈ Bad L N).card ≤
        msgCwCount L (union W D) l e * 2 ^ 960 :=
  card_flip_readH_out_le card_fiber_trunc128_le hs hr.hw hr.hd
    (fun t ↦ slotOf L.param t = some (.msg l e)) Codeword.Valid (blocks (blockInput x)) xi
    (fun v ↦ cwSel m l e x xi v)
    (fun v t y ht ↦ by
      unfold cwSel at ht
      split_ifs at ht with hv
      · rcases xmssTgt_select ht with h | ⟨h1, h2, h3⟩
        · exact .inl h
        · exact .inr ⟨hv, h1, h2, h3⟩
      · exact .inl ht)
    (fun hG v t xi' hi ↦ by
      unfold cwSel
      split_ifs
      · exact selectRead_head_none hr hG hi
      · obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hr.head
        exact xmssTgt_msg_none hr.slot (Selections.toMemory_eq_none hr.hm))

open scoped Classical in
/-- **The flip cost of a codeword-selecting read**: as `flipCost_selectRead_le`, for a memory
update that keeps the memory or records the selection only for a codeword digest (`cwUpd`), with
`E = ∑_{SelectRead, ∉ Bad} msgCwCount · 2^960 / |X| · σ_ss`. -/
theorem flipCost_selectReadCw_le (z : Z) (l : Layer) (e : KeyIndex) (x xi : X)
    (upd : Selections → Option X → Selections)
    (hupd : ∀ m v, upd m (some v) = m ∨ upd m (some v) = cwSel m l e x xi v)
    {σ : Matrix (Unit × HwReg X Z Selections) (Unit × HwReg X Z Selections) ℂ}
    (hσ : σ.PosSemidef) :
    flipCost (Bad L N) (hwReadKraus (.readH z upd))
        (readPs fun s ↦ SelectRead L s.1 s.2.1 s.2.2 z l e x xi) σ ≤
      ENNReal.ofReal (∑ q, if SelectRead L q.2.1 q.2.2.1 q.2.2.2 z l e x xi ∧ q.2 ∉ Bad L N then
          ((msgCwCount L (union q.2.2.1 q.2.1) l e * 2 ^ 960 : ℕ) : ℝ) / Fintype.card X *
            (σ q q).re else 0) +
        ENNReal.ofReal ((readPs fun s ↦ SelectRead L s.1 s.2.1 s.2.2 z l e x xi) * σ).trace.re +
      2 * (ENNReal.ofReal (∑ q, if SelectRead L q.2.1 q.2.2.1 q.2.2.2 z l e x xi ∧
          q.2 ∉ Bad L N then ((msgCwCount L (union q.2.2.1 q.2.1) l e * 2 ^ 960 : ℕ) : ℝ) /
            Fintype.card X * (σ q q).re else 0) *
        ENNReal.ofReal ((readPs fun s ↦ SelectRead L s.1 s.2.1 s.2.2 z l e x xi) * σ).trace.re) ^
          (2⁻¹ : ℝ) := by
  refine flipCost_readH_le (Bad L N) z upd (fun m v ↦ cwSel m l e x xi v)
    (fun s ↦ SelectRead L s.1 s.2.1 s.2.2 z l e x xi)
    (fun s ↦ msgCwCount L (union s.2.1 s.1) l e * 2 ^ 960) ?_ hupd ?_ ?_ ?_ ?_ hσ
  · exact fun _ hs ↦ ⟨hs.hd, hs.hw⟩
  · exact fun _ u hs hS ↦ not_mem_bad_read_keep hS hs u
  · -- The filter's decidability instances differ syntactically from `card_flip_readCw_le`'s.
    intro s hs hS
    convert card_flip_readCw_le hS hs using 3
  · exact fun s u hs hS ↦ mem_hwTargetBad_fill hS hs.hd u s.2.2 fun _ _ ht ↦ ht
  · intro s u v hs hS
    unfold cwSel
    split_ifs
    · exact mem_hwTargetBad_fill hS hs.hd u _ fun _ _ ht ↦ xmssTgt_select_mono hs.hm ht
    · exact mem_hwTargetBad_fill hS hs.hd u s.2.2 fun _ _ ht ↦ ht

open scoped Classical in
/-- **The selecting-read term** of `flipCost_selectReadCw_le`: if `msgCwCount ≤ C` on the
selection reads of the support outside `Bad`, then `E ≤ C 2^-128 e`, with `e` the weight of the
selection reads. -/
theorem selectReadCwE_le (z : Z) (l : Layer) (e : KeyIndex) (x xi : X) (C : ℕ)
    {σ : Matrix (Unit × HwReg X Z Selections) (Unit × HwReg X Z Selections) ℂ}
    (hσ : σ.PosSemidef)
    (hC : ∀ q, SelectRead L q.2.1 q.2.2.1 q.2.2.2 z l e x xi → q.2 ∉ Bad L N → σ q q ≠ 0 →
      msgCwCount L (union q.2.2.1 q.2.1) l e ≤ C) :
    (∑ q, if SelectRead L q.2.1 q.2.2.1 q.2.2.2 z l e x xi ∧ q.2 ∉ Bad L N then
        ((msgCwCount L (union q.2.2.1 q.2.1) l e * 2 ^ 960 : ℕ) : ℝ) / Fintype.card X *
          (σ q q).re else 0) ≤
      C * (2 ^ 128)⁻¹ * ∑ q, if SelectRead L q.2.1 q.2.2.1 q.2.2.2 z l e x xi then
        (σ q q).re else 0 := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hC0 : (0 : ℝ) ≤ C * (2 ^ 128)⁻¹ := by positivity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases hq : SelectRead L q.2.1 q.2.2.1 q.2.2.2 z l e x xi
  · rw [ite_eq_left hq]
    by_cases hb : q.2 ∉ Bad L N
    · rw [ite_eq_left ⟨hq, hb⟩]
      by_cases hσq : σ q q = 0
      · rw [hσq, Complex.zero_re, mul_zero, mul_zero]
      refine mul_le_mul_of_nonneg_right ?_ (hre q)
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, two_pow_div_card_X]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (hC q hq hb hσq)) (by positivity)
    · rw [ite_eq_right fun h ↦ hb h.2]
      exact mul_nonneg hC0 (hre q)
  · rw [ite_eq_right fun h ↦ hq h.1, ite_eq_right hq, mul_zero]

/-! ## Survival of a trial -/

/-- `rhoCw`, as the fraction of codeword values of a trial cell. -/
theorem cwCount_mul_div_card_X : ((cwCount * 2 ^ 960 : ℕ) : ℝ) / Fintype.card X = rhoCw := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, two_pow_div_card_X, rhoCw,
    div_eq_mul_inv]

/-- The codeword values of a trial cell are a fraction `rhoCw` of its values. -/
theorem card_codeword_div_card_X (xi : X) :
    ((Finset.univ.filter fun v : X ↦ Codeword.Valid (trunc128 (xi + v))).card : ℝ) /
      Fintype.card X = rhoCw := by
  rw [card_codeword_trunc128, cwCount_mul_div_card_X]

/-- The memories whose key `(l, e)` has no selection. -/
def unselMem (l : Layer) (e : KeyIndex) : Set Selections := {m | m l e = none}

instance (l : Layer) (e : KeyIndex) : DecidablePred (· ∈ unselMem l e) :=
  fun m ↦ inferInstanceAs (Decidable (m l e = none))

open scoped Classical in
/-- **Survival of a trial read**: the outcomes of a trial of the unselected key `(l, e)` that
leave it unselected weigh at most `w - ρ_c e + p + 2 √(ρ_c e p)`, with `w` the weight of the
states where the key is unselected, `e` the weight of the selection reads `SR` (cell empty and not
hardwired, key unselected) and `p = tr (P σ)` the rest: on an empty cell the trial's digest is a
codeword with probability `rhoCw`. -/
theorem survive_selectRead_le (z : Z) (l : Layer) (e : KeyIndex) (x xi : X)
    (upd : Selections → Option X → Selections)
    (hupd : ∀ m v, m l e = none → upd m (some v) = cwSel m l e x xi v)
    (SR : HwReg X Z Selections → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → s.1.1 z = none ∧ s.2.1.1 z = none ∧ s.2.2 ∈ unselMem l e)
    {σ : Matrix (Unit × HwReg X Z Selections) (Unit × HwReg X Z Selections) ℂ}
    (hσ : σ.PosSemidef) :
    (∑ r : Option X × Selections, if upd r.2 r.1 ∈ unselMem l e then
        (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ).trace.re else 0) ≤
      (∑ q, if q.2.2.2 ∈ unselMem l e then (σ q q).re else 0) -
        rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) + (readPs SR * σ).trace.re +
        2 * √(rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) * (readPs SR * σ).trace.re) :=
  survive_readH_le z upd (unselMem l e) (fun v ↦ Codeword.Valid (trunc128 (xi + v)))
    (card_codeword_div_card_X xi)
    (fun m hm v ↦ by
      show upd m (some v) l e = none ↔ _
      rw [hupd m v hm]
      exact cwSel_eq_none_iff hm x xi v) SR hSR hσ

/-! ## One key: the trial sequence -/

/-- From `A ≤ w + P + 2 √A √P` to `A ≤ (√(w + 2P) + √P)²`. -/
theorem le_sq_of_le_add_sqrt {A P w : ℝ} (hA : 0 ≤ A) (hP : 0 ≤ P)
    (h : A ≤ w + P + 2 * (√A * √P)) : A ≤ (√(w + 2 * P) + √P) ^ 2 := by
  have hsA := Real.sq_sqrt hA
  have hsP := Real.sq_sqrt hP
  have h1 : (√A - √P) ^ 2 ≤ w + 2 * P := by nlinarith
  have h2 : √A ≤ √(w + 2 * P) + √P := by
    have := Real.abs_le_sqrt h1
    linarith [le_abs_self (√A - √P)]
  calc A = √A ^ 2 := hsA.symm
    _ ≤ (√(w + 2 * P) + √P) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2

/-- **The survival-weighted trial sum.** If the weight `w j` reaching trial `j` satisfies the
survival bound `w (j + 1) ≤ w j - ρ e j + p j + 2 √(ρ e j p j)` (`survive_selectRead_le`), then
for any number `J` of trials (the signer stops at `2^32`), `ρ ∑ e ≤ (√(w 0 + 2P) + √P)²` with
`P = ∑ p`: the geometric series `∑ (1 - ρ)^j ≤ 1 / ρ`, with the recorded cells' interference
summed by Cauchy-Schwarz. -/
theorem sum_trials_le {J : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (w e p : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (he : ∀ j, 0 ≤ e j) (hp : ∀ j, 0 ≤ p j)
    (hrec : ∀ j < J, w (j + 1) ≤ w j - ρ * e j + p j + 2 * √(ρ * e j * p j)) :
    ρ * ∑ j ∈ Finset.range J, e j ≤
      (√(w 0 + 2 * ∑ j ∈ Finset.range J, p j) + √(∑ j ∈ Finset.range J, p j)) ^ 2 := by
  have hρe : ∀ j, 0 ≤ ρ * e j := fun j ↦ mul_nonneg hρ (he j)
  have hsum : ∑ j ∈ Finset.range J, (w (j + 1) - w j) ≤
      ∑ j ∈ Finset.range J, (-(ρ * e j) + p j + 2 * (√(ρ * e j) * √(p j))) :=
    Finset.sum_le_sum fun j hj ↦ by
      have := hrec j (Finset.mem_range.1 hj)
      rw [Real.sqrt_mul (hρe j)] at this
      linarith
  rw [Finset.sum_range_sub, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.range J) hρe hp
  rw [← Finset.mul_sum] at hcs
  refine le_sq_of_le_add_sqrt (mul_nonneg hρ (Finset.sum_nonneg fun j _ ↦ he j))
    (Finset.sum_nonneg fun j _ ↦ hp j) ?_
  have := hw J
  nlinarith

/-- **The cost terms summed by Cauchy-Schwarz**: `∑ (E + p + 2 √(E p)) ≤ (√∑E + √∑p)²`. -/
theorem sum_cost_le (J : ℕ) (E p : ℕ → ℝ) (hE : ∀ j, 0 ≤ E j) (hp : ∀ j, 0 ≤ p j) :
    ∑ j ∈ Finset.range J, (ENNReal.ofReal (E j) + ENNReal.ofReal (p j) +
      2 * (ENNReal.ofReal (E j) * ENNReal.ofReal (p j)) ^ (2⁻¹ : ℝ)) ≤
    ENNReal.ofReal ((√(∑ j ∈ Finset.range J, E j) + √(∑ j ∈ Finset.range J, p j)) ^ 2) := by
  have hterm : ∀ j, ENNReal.ofReal (E j) + ENNReal.ofReal (p j) +
      2 * (ENNReal.ofReal (E j) * ENNReal.ofReal (p j)) ^ (2⁻¹ : ℝ) =
      ENNReal.ofReal (E j + p j + 2 * (√(E j) * √(p j))) := fun j ↦ by
    rw [← ENNReal.ofReal_mul (hE j), ENNReal.ofReal_rpow_inv_two, Real.sqrt_mul (hE j),
      ENNReal.ofReal_add (add_nonneg (hE j) (hp j)) (by positivity),
      ENNReal.ofReal_add (hE j) (hp j), ENNReal.ofReal_mul (by norm_num)]
    norm_num
  simp only [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ by have := hE j; have := hp j; positivity]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, add_sq,
    Real.sq_sqrt (Finset.sum_nonneg fun j _ ↦ hE j), Real.sq_sqrt (Finset.sum_nonneg fun j _ ↦ hp j)]
  have := Real.sum_sqrt_mul_sqrt_le (Finset.range J) hE hp
  nlinarith

/-- **The Enc cost of one key.** Let trial `j` of the key start from the state `σ_j`, with `w j`
the weight of its states where the key is unselected, `e j` the weight of its selection reads and
`p j` the rest (`readPs`), let the survival bounds hold (`survive_selectRead_le`, the reads between
two `h` reads keep the memory), and let the selecting read's term be `E j ≤ C 2^-128 e j`
(`selectReadCwE_le`, `C` bounding `msgCwCount` on the selection reads outside `Bad` of the key's
trials). Then the selecting reads' costs `E + p + 2 √(E p)` (`flipCost_selectReadCw_le`) over all
trials sum to at most `(√(C 2^-128 / ρ_c · (√(w 0 + 2P) + √P)²) + √P)²`, for any number of
trials. -/
theorem encCost_key_le {J : ℕ} {C : ℝ} (hC : 0 ≤ C) (w e p E : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (he : ∀ j, 0 ≤ e j) (hp : ∀ j, 0 ≤ p j) (hE0 : ∀ j, 0 ≤ E j)
    (hrec : ∀ j < J, w (j + 1) ≤ w j - rhoCw * e j + p j + 2 * √(rhoCw * e j * p j))
    (hE : ∀ j < J, E j ≤ C * (2 ^ 128)⁻¹ * e j) :
    ∑ j ∈ Finset.range J, (ENNReal.ofReal (E j) + ENNReal.ofReal (p j) +
      2 * (ENNReal.ofReal (E j) * ENNReal.ofReal (p j)) ^ (2⁻¹ : ℝ)) ≤
    ENNReal.ofReal ((√(C * (2 ^ 128)⁻¹ / rhoCw *
        (√(w 0 + 2 * ∑ j ∈ Finset.range J, p j) + √(∑ j ∈ Finset.range J, p j)) ^ 2) +
      √(∑ j ∈ Finset.range J, p j)) ^ 2) := by
  refine (sum_cost_le J E p hE0 hp).trans (ENNReal.ofReal_le_ofReal ?_)
  have hk : 0 ≤ C * (2 ^ 128 : ℝ)⁻¹ := by positivity
  have htr := sum_trials_le rhoCw_pos.le w e p hw he hp hrec
  have hEsum : ∑ j ∈ Finset.range J, E j ≤ C * (2 ^ 128)⁻¹ / rhoCw *
      (√(w 0 + 2 * ∑ j ∈ Finset.range J, p j) + √(∑ j ∈ Finset.range J, p j)) ^ 2 := by
    calc ∑ j ∈ Finset.range J, E j ≤ ∑ j ∈ Finset.range J, C * (2 ^ 128)⁻¹ * e j :=
          Finset.sum_le_sum fun j hj ↦ hE j (Finset.mem_range.1 hj)
      _ = C * (2 ^ 128)⁻¹ / rhoCw * (rhoCw * ∑ j ∈ Finset.range J, e j) := by
          rw [← Finset.mul_sum]
          field_simp [rhoCw_pos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left htr (div_nonneg hk rhoCw_pos.le)
  have hsq := Real.sqrt_le_sqrt hEsum
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- **The Enc cost of one key, with `ρ_c ≥ 2^-21`**: at most
`(√(C 2^-107 (√(w 0 + 2P) + √P)²) + √P)²`. -/
theorem encCost_key_le_pow {J : ℕ} {C : ℝ} (hC : 0 ≤ C) (w e p E : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (he : ∀ j, 0 ≤ e j) (hp : ∀ j, 0 ≤ p j) (hE0 : ∀ j, 0 ≤ E j)
    (hrec : ∀ j < J, w (j + 1) ≤ w j - rhoCw * e j + p j + 2 * √(rhoCw * e j * p j))
    (hE : ∀ j < J, E j ≤ C * (2 ^ 128)⁻¹ * e j) :
    ∑ j ∈ Finset.range J, (ENNReal.ofReal (E j) + ENNReal.ofReal (p j) +
      2 * (ENNReal.ofReal (E j) * ENNReal.ofReal (p j)) ^ (2⁻¹ : ℝ)) ≤
    ENNReal.ofReal ((√(C * (2 ^ 107)⁻¹ *
        (√(w 0 + 2 * ∑ j ∈ Finset.range J, p j) + √(∑ j ∈ Finset.range J, p j)) ^ 2) +
      √(∑ j ∈ Finset.range J, p j)) ^ 2) := by
  refine (encCost_key_le hC w e p E hw he hp hE0 hrec hE).trans (ENNReal.ofReal_le_ofReal ?_)
  have hk : C * (2 ^ 128 : ℝ)⁻¹ / rhoCw ≤ C * (2 ^ 107)⁻¹ := by
    rw [div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    calc (2 ^ 128 : ℝ)⁻¹ * rhoCw⁻¹ ≤ (2 ^ 128)⁻¹ * 2 ^ 21 :=
          mul_le_mul_of_nonneg_left inv_rhoCw_le (by positivity)
      _ = (2 ^ 107)⁻¹ := by norm_num
  have hsq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hk (sq_nonneg
    (√(w 0 + 2 * ∑ j ∈ Finset.range J, p j) + √(∑ j ∈ Finset.range J, p j))))
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

end Quantum.Xmss

end
