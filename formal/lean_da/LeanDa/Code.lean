module

public import LeanDa.Membership
public import LeanDa.Merkle
public import LeanDa.Defs

@[expose] public section

/-!
# LeanDA's code and its membership test

The erasure code (`leanDaErasureCode`): `r` payloads, each encoded by the systematic Reed-Solomon
encoder and cut into `128` cells; a matrix is in the code exactly when every row is a codeword
(`mem_code_iff`). The membership test accepts a matrix of codewords on every challenge
(`membershipCheckOpt_of_mem_code`), and the facts the straight-line argument reads of it and of
the nonce search's draws (`not_mem_code_row`, `mem_code_of_forall_check`, `selIdxFrom_spec`,
`prob_valid_accept_le`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

open PqDas OracleComp OracleSpec ENNReal

namespace LeanDa

/-! ## The code -/

/-- The first half of a codeword: its payload. -/
def firstHalf (w : Row) : Payload := fun a ↦ w (Fin.castLE (by norm_num) a)

theorem posRow_pos {r : ℕ} (i : Fin r) (j : Fin 128) : positionRow (cellPosition i j) = i :=
  Fin.ext (by simp only [positionRow, cellPosition]; omega)

theorem posCell_pos {r : ℕ} (i : Fin r) (j : Fin 128) : positionCell (cellPosition i j) = j :=
  Fin.ext (by simp only [positionCell, cellPosition]; omega)

theorem pos_posRow_posCell {r : ℕ} (p : Fin (r * 128)) : cellPosition (positionRow p) (positionCell p) = p :=
  Fin.ext (by simp only [positionRow, positionCell, cellPosition]; omega)

theorem rowOf_encodeMatrix {r : ℕ} (msg : Fin r → Payload) (i : Fin r) :
    matrixRow (encodeMatrix msg) i = encodeRow (msg i) := by
  funext b
  simp only [matrixRow, encodeMatrix, rowCell, posRow_pos, posCell_pos]
  congr 1
  exact Fin.ext (by simp only; omega)

theorem encodeMatrix_firstHalf {r : ℕ} (c : Fin (r * 128) → Cell) (h : ∀ i, matrixRow c i ∈ rsCode) :
    encodeMatrix (fun i ↦ firstHalf (matrixRow c i)) = c := by
  funext p s
  simp only [encodeMatrix, rowCell]
  rw [show firstHalf (matrixRow c (positionRow p)) =
      fun a ↦ matrixRow c (positionRow p) (Fin.castLE (by norm_num) a) from rfl, encodeRow_firstHalf (h _)]
  simp only [matrixRow]
  have h1 : (⟨(128 * (positionCell p : ℕ) + s) / 128, by omega⟩ : Fin 128) = positionCell p :=
    Fin.ext (by simp only; omega)
  have h2 : (⟨(128 * (positionCell p : ℕ) + s) % 128, by omega⟩ : Fin 128) = s :=
    Fin.ext (by simp only; omega)
  rw [h1, h2, pos_posRow_posCell]

/-- A matrix is a codeword when every row is. -/
theorem mem_code_iff {r : ℕ} (c : Fin (r * 128) → Cell) :
    c ∈ (leanDaErasureCode r).code ↔ ∀ i, matrixRow c i ∈ rsCode := by
  constructor
  · rintro ⟨msg, rfl⟩ i
    change matrixRow (encodeMatrix msg) i ∈ rsCode
    rw [rowOf_encodeMatrix]
    exact encodeRow_mem _
  · intro h
    exact ⟨fun i ↦ firstHalf (matrixRow c i), encodeMatrix_firstHalf c h⟩

/-! ## The membership test -/

theorem membershipCheck_iff {r : ℕ} (z : E) (c : Fin (r * 128) → Cell) :
    membershipCheck z c = true ↔ ∀ i, innerProduct (dualCodewordAt z) (matrixRow c i) = 0 :=
  decide_eq_true_iff

/-- Without a challenge, the check is on every challenge. -/
theorem membershipCheckOpt_none {r : ℕ} (c : Fin (r * 128) → Cell) :
    membershipCheckOpt none c = true ↔ ∀ z, membershipCheck z c = true :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

/-- **A codeword passes the check of every challenge, or of none.** -/
theorem membershipCheckOpt_of_mem_code {r : ℕ} {c : Fin (r * 128) → Cell}
    (hc : c ∈ (leanDaErasureCode r).code) (o : Option E) : membershipCheckOpt o c = true := by
  rw [mem_code_iff] at hc
  have h : ∀ z, membershipCheck z c = true := fun z ↦
    (membershipCheck_iff z c).mpr fun i ↦ dot_dual_eq_zero (hc i) z
  cases o with
  | none => exact (membershipCheckOpt_none c).mpr h
  | some z => exact h z

theorem card_K : Fintype.card K = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card]
  exact BF64.nat_card_bf64

theorem card_E : Fintype.card E = 2 ^ 128 := by
  rw [← Nat.card_eq_fintype_card, CompPoly.Extension.Ext.nat_card_ext]
  norm_num [LeanVM.Parameters.eParams]

/-! ### The label the nonce search selects

The nonce search reads only the proofs of work to choose its label (`selIdxFrom`), and returns that
label's challenge (`selectFrom_eq`). -/

/-- The proof of work of label `j`, zero past the labels. -/
def powAt (k : Fin nLabels → K) (j : ℕ) : K := if h : j < nLabels then k ⟨j, h⟩ else 0

/-- **The label the nonce search selects** from `nonce` with `fuel` nonces left, from the proofs
of work alone; none if no nonce is valid. -/
def selIdxFrom (k : Fin nLabels → K) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | nonce, fuel + 1 =>
    if powValid (powAt k (nonce + 1)).lane then some (nonce + 1) else selIdxFrom k (nonce + 1) fuel

theorem drawAt_snd (v : MembershipChallenge) (j : ℕ) :
    (drawAt v j).2 = powAt (fun j ↦ (v j).2) j := by
  unfold drawAt powAt
  split <;> rfl

theorem selectFrom_eq (v : MembershipChallenge) : ∀ fuel nonce,
    selectFrom v nonce fuel = (selIdxFrom (fun j ↦ (v j).2) nonce fuel).map fun j ↦ (drawAt v j).1
  | 0, _ => rfl
  | fuel + 1, nonce => by
    simp only [selectFrom, selIdxFrom, drawAt_snd]
    split
    · rfl
    · exact selectFrom_eq v fuel (nonce + 1)

/-- **The label the search selects**: past `nonce`, within the fuel, with a valid proof of work,
and every label between invalid. -/
theorem selIdxFrom_spec (k : Fin nLabels → K) : ∀ fuel nonce j, selIdxFrom k nonce fuel = some j →
    nonce < j ∧ j ≤ nonce + fuel ∧ powValid (powAt k j).lane = true ∧
      ∀ i, nonce < i → i < j → powValid (powAt k i).lane = false
  | 0, _, _, h => by cases h
  | fuel + 1, nonce, j, h => by
    simp only [selIdxFrom] at h
    split at h
    · next hv =>
      cases h
      exact ⟨by omega, by omega, hv, fun i h1 h2 ↦ by omega⟩
    · next hv =>
      obtain ⟨h1, h2, h3, h4⟩ := selIdxFrom_spec k fuel (nonce + 1) j h
      refine ⟨by omega, by omega, h3, fun i hi1 hi2 ↦ ?_⟩
      by_cases hi : i = nonce + 1
      · subst hi
        simpa using hv
      · exact h4 i (by omega) hi2

/-! ### The grind's draws -/

/-- A matrix that is not a codeword has a row that is not. -/
theorem not_mem_code_row {r : ℕ} {c : Fin (r * 128) → Cell} (h : c ∉ (leanDaErasureCode r).code) :
    ∃ i, matrixRow c i ∉ rsCode := by
  rw [mem_code_iff] at h
  push Not at h
  exact h

/-- **A matrix every challenge accepts is a codeword**: a row that is not a codeword is accepted
by at most `2^13 - 1 < |E|` challenges. -/
theorem mem_code_of_forall_check {r : ℕ} {c : Fin (r * 128) → Cell}
    (h : ∀ z : E, membershipCheck z c = true) : c ∈ (leanDaErasureCode r).code := by
  by_contra hc
  obtain ⟨i, hi⟩ := not_mem_code_row hc
  have hcard := card_acceptSet_le hi
  have hlt : (acceptSet (matrixRow c i)).card < Fintype.card E := by
    rw [card_E]; omega
  obtain ⟨z₀, -, hz₀⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := acceptSet (matrixRow c i)) (t := Finset.univ) (by rw [Finset.card_univ]; exact hlt)
  rw [mem_acceptSet] at hz₀
  exact hz₀ ((membershipCheck_iff z₀ c).mp (h z₀) i)

/-- A `K` word's lane determines it (the proof of work's lane). -/
theorem lane_injective : Function.Injective K.lane := fun _ _ h ↦
  BF64.toBitVec_injective (congrArg UInt64.toBitVec h)

/-- **Valid proofs of work**: at most `2^54` of the `2^64` lanes have `10` low zero bits. -/
theorem card_valid_le :
    (Finset.univ.filter fun k : K ↦ powValid k.lane = true).card ≤ 2 ^ 54 := by
  classical
  have hv : ∀ k : K, k ∈ Finset.univ.filter (fun k : K ↦ powValid k.lane = true) →
      k.lane.toNat % 2 ^ 10 = 0 := fun k hk ↦ by
    have := (Finset.mem_filter.mp hk).2
    unfold powValid membershipGrindingBits at this
    exact of_decide_eq_true this
  calc _ ≤ (Finset.range (2 ^ 54)).card := by
        refine Finset.card_le_card_of_injOn (fun k ↦ k.lane.toNat / 2 ^ 10) (fun k _ ↦ ?_)
          (fun a ha b hb hab ↦ ?_)
        · have := k.lane.toNat_lt
          show k.lane.toNat / 2 ^ 10 ∈ (Finset.range (2 ^ 54) : Set ℕ)
          rw [Finset.mem_coe, Finset.mem_range]
          omega
        · have ha' := hv a (Finset.mem_coe.mp ha)
          have hb' := hv b (Finset.mem_coe.mp hb)
          have hab' : a.lane.toNat / 2 ^ 10 = b.lane.toNat / 2 ^ 10 := hab
          have e : a.lane.toNat = b.lane.toNat := by
            have h1 := Nat.div_add_mod a.lane.toNat (2 ^ 10)
            have h2 := Nat.div_add_mod b.lane.toNat (2 ^ 10)
            omega
          exact lane_injective (UInt64.toNat_inj.mp e)
    _ = 2 ^ 54 := Finset.card_range _

/-- **A uniform draw has a valid proof of work and a challenge in `A`** with probability at most
`2^-10 · |A| / 2^128`: the two parts of a draw are independent. -/
theorem prob_valid_accept_le {A : Finset E} (hA : A.card ≤ 2 ^ 13 - 1) :
    Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[powValid x.2.lane = true ∧ x.1 ∈ A] ≤
      (2 ^ 13 - 1) / 2 ^ 138 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hf : (Finset.univ.filter fun x : Draw ↦ powValid x.2.lane = true ∧ x.1 ∈ A) =
      A ×ˢ (Finset.univ.filter fun k : K ↦ powValid k.lane = true) := by
    ext x
    simp [and_comm]
  rw [hf, Finset.card_product, Fintype.card_prod, card_E, card_K]
  have hV := card_valid_le
  calc ((A.card * (Finset.univ.filter fun k : K ↦ powValid k.lane = true).card : ℕ) : ℝ≥0∞) /
        ((2 ^ 128 * 2 ^ 64 : ℕ) : ℝ≥0∞)
      ≤ (((2 ^ 13 - 1) * 2 ^ 54 : ℕ) : ℝ≥0∞) / ((2 ^ 128 * 2 ^ 64 : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = (2 ^ 13 - 1) / 2 ^ 138 := by
        rw [show (2 ^ 128 * 2 ^ 64 : ℕ) = 2 ^ 54 * 2 ^ 138 by norm_num,
          show ((2 ^ 13 - 1) * 2 ^ 54 : ℕ) = 2 ^ 54 * (2 ^ 13 - 1) by ring, Nat.cast_mul,
          Nat.cast_mul, ENNReal.mul_div_mul_left _ _ (by simp) (by simp), ENNReal.natCast_sub]
        norm_num

/-- **A uniform draw's proof of work is valid**, and has a challenge in `A`, with the probability
of the one times `|A| / |E|`: the two parts of a draw are independent. -/
theorem prob_valid_accept_eq (A : Finset E) :
    Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[powValid x.2.lane = true ∧ x.1 ∈ A] =
      Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[powValid x.2.lane = true] * (A.card / Fintype.card E) := by
  classical
  rw [SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample]
  have hf : (Finset.univ.filter fun x : Draw ↦ powValid x.2.lane = true ∧ x.1 ∈ A) =
      A ×ˢ (Finset.univ.filter fun k : K ↦ powValid k.lane = true) := by
    ext x
    simp [and_comm]
  have hg : (Finset.univ.filter fun x : Draw ↦ powValid x.2.lane = true) =
      Finset.univ ×ˢ (Finset.univ.filter fun k : K ↦ powValid k.lane = true) := by
    ext x
    simp
  rw [hf, hg, Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_prod]
  have hE : (Fintype.card E : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hE' : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  push_cast
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl hE) (Or.inl hE')]
  calc ((Fintype.card E : ℝ≥0∞)⁻¹ * (Fintype.card K : ℝ≥0∞)⁻¹) *
        (A.card * (Finset.univ.filter fun k : K ↦ powValid k.lane = true).card)
      = ((Fintype.card E : ℝ≥0∞)⁻¹ * (Fintype.card K : ℝ≥0∞)⁻¹) *
        (Fintype.card E * (Finset.univ.filter fun k : K ↦ powValid k.lane = true).card) *
          ((Fintype.card E : ℝ≥0∞)⁻¹ * A.card) := by
        rw [show ((Fintype.card E : ℝ≥0∞)⁻¹ * (Fintype.card K : ℝ≥0∞)⁻¹) *
            (Fintype.card E * (Finset.univ.filter fun k : K ↦ powValid k.lane = true).card) *
            ((Fintype.card E : ℝ≥0∞)⁻¹ * A.card) =
            ((Fintype.card E : ℝ≥0∞)⁻¹ * (Fintype.card K : ℝ≥0∞)⁻¹) *
            ((Finset.univ.filter fun k : K ↦ powValid k.lane = true).card * A.card) *
            ((Fintype.card E : ℝ≥0∞) * (Fintype.card E : ℝ≥0∞)⁻¹) by ring,
          ENNReal.mul_inv_cancel hE hE', mul_one]
        ring
    _ = _ := rfl

end LeanDa
