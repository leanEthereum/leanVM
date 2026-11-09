module

public import LeanDa.Membership
public import LeanDa.Merkle
public import PqDas.Proof.PositionBinding
public import PqDas.Proof.CorollaryCodeBinding
public import LeanDa.Defs

@[expose] public section

/-!
# LeanDA in Wagner's framework

The building blocks of `PqDas`, instantiated with LeanDA (`LeanDa.Scheme`) for `r ≥ 1` rows:

* the erasure code `code r`: `r` payloads, each encoded by the systematic Reed-Solomon encoder
  and cut into `128` cells, a codeword being `r · 128` cells;
* the vector commitment `merkleVC r H`: the root of the tree of blob trees over the cells with
  hash `H`, cells opened by their paths in it. It is perfectly complete
  (`merkleVC_perfectlyComplete`), and its position binding reduces to finding an `H` collision
  through the explicit `merkleCollider` (`posBindingExp_le_hashCollisionExp`);
* the code checker `checker r`: the membership test, complete (`checker_complete`) and
  `(2^14 - 1) / 2^192`-sound over a uniform `z ∈ E` (`checker_sound`).

`leanDa r H ps` is the scheme with the hash `H` and an argument of knowledge `ps` for the relation
`Relation r H`: the cells commit to the root and pass the membership test on the challenge.

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
  have h1 : (⟨(256 * (positionCell p : ℕ) + s) / 256, by omega⟩ : Fin 128) = positionCell p :=
    Fin.ext (by simp only; omega)
  have h2 : (⟨(256 * (positionCell p : ℕ) + s) % 256, by omega⟩ : Fin 256) = s :=
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

/-! ## The code checker -/

theorem checker_check_iff {r : ℕ} (z : MembershipChallenge) (c : Fin (r * 128) → Cell) :
    (checker r).check z c = true ↔ membershipCheckOpt (selectChal z) c = true :=
  Iff.rfl

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

theorem checker_complete (r : ℕ) : (checker r).Complete (leanDaErasureCode r) :=
  fun _ hc _ ↦ membershipCheckOpt_of_mem_code hc _

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

theorem selIdxFrom_le (k : Fin nLabels → K) :
    ∀ fuel nonce j, selIdxFrom k nonce fuel = some j → j ≤ nonce + fuel
  | 0, _, _, h => by cases h
  | fuel + 1, nonce, j, h => by
    simp only [selIdxFrom] at h
    split at h
    · cases h; omega
    · have := selIdxFrom_le k fuel (nonce + 1) j h
      omega

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

/-- The label the nonce search selects from nonce `0`, label `0` if none. -/
def selIdx (k : Fin nLabels → K) : Fin nLabels :=
  ⟨(selIdxFrom k 0 nonceCount).getD 0, by
    rcases h : selIdxFrom k 0 nonceCount with _ | j
    · simp
    · have := selIdxFrom_le k nonceCount 0 j h
      simp only [Option.getD_some, nLabels]
      omega⟩

/-- **The deployed challenge of the draws is the selected label's challenge.** -/
theorem selectChal_some {v : MembershipChallenge} {z : E} (h : selectChal v = some z) :
    z = (v (selIdx fun j ↦ (v j).2)).1 := by
  rw [selectChal, selectFrom_eq] at h
  rcases hs : selIdxFrom (fun j ↦ (v j).2) 0 nonceCount with _ | j
  · rw [hs] at h; cases h
  · rw [hs] at h
    cases h
    have hj : j < nLabels := by
      have := selIdxFrom_le _ nonceCount 0 j hs
      simp only [nLabels]
      omega
    simp only [drawAt, hj, ↓reduceDIte, selIdx, hs, Option.getD_some]

/-- The functions whose value at `i` lies in `A`: `|A| · |F|^(|ι| - 1)` of them. -/
theorem card_filter_at {ι F : Type} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
    (i : ι) (A : Finset F) :
    (Finset.univ.filter fun l : ι → F ↦ l i ∈ A).card =
      A.card * Fintype.card F ^ (Fintype.card ι - 1) := by
  have h : (Finset.univ.filter fun l : ι → F ↦ l i ∈ A) =
      Fintype.piFinset fun j : ι ↦ if j = i then A else Finset.univ := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hl j
      split_ifs with hj
      · subst hj; exact hl
      · exact Finset.mem_univ _
    · intro hl
      simpa using hl i
  rw [h, Fintype.card_piFinset, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [↓reduceIte]
  congr 1
  rw [Finset.prod_congr rfl (g := fun _ ↦ Fintype.card F) fun j hj ↦ by
      simp [Finset.ne_of_mem_erase hj],
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- **The functions whose selected value lies in `A`**: for each choice of the second
components, which alone select the index, the first component there is free. -/
theorem card_filter_sel {N : ℕ} (sel : (Fin N → K) → Fin N) (A : Finset E) :
    (Finset.univ.filter fun v : Fin N → E × K ↦ (v (sel fun j ↦ (v j).2)).1 ∈ A).card =
      Fintype.card K ^ N * (A.card * Fintype.card E ^ (N - 1)) := by
  classical
  rw [← Fintype.card_subtype]
  let e : {v : Fin N → E × K // (v (sel fun j ↦ (v j).2)).1 ∈ A} ≃
      Σ k : Fin N → K, {a : Fin N → E // a (sel k) ∈ A} :=
    { toFun := fun v ↦ ⟨fun j ↦ (v.1 j).2, fun j ↦ (v.1 j).1, v.2⟩
      invFun := fun p ↦ ⟨fun j ↦ (p.2.1 j, p.1 j), p.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_subtype, card_filter_at, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

/-- **A uniform function's value at an index its second components select** has a uniform first
component: the probability that it lies in `A` is `|A| / |E|`. -/
theorem prob_sel_le {N : ℕ} (hN : 0 < N) (sel : (Fin N → K) → Fin N) (A : Finset E) :
    Pr{let v ← $ᵗ (Fin N → E × K)}[(v (sel fun j ↦ (v j).2)).1 ∈ A] ≤
      A.card / Fintype.card E := by
  rw [SampleableType.prEvent_uniformSample, card_filter_sel, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin]
  have hK : (Fintype.card K : ℝ≥0∞) ^ N * Fintype.card E ^ (N - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  have hK' : (Fintype.card K : ℝ≥0∞) ^ N * Fintype.card E ^ (N - 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  refine le_of_eq ?_
  push_cast
  rw [show (Fintype.card E : ℝ≥0∞) * Fintype.card K = Fintype.card K * Fintype.card E by ring,
    mul_pow, show (Fintype.card E : ℝ≥0∞) ^ N = Fintype.card E * Fintype.card E ^ (N - 1) by
      rw [← pow_succ', Nat.sub_add_cancel hN],
    show (Fintype.card K : ℝ≥0∞) ^ N * (A.card * Fintype.card E ^ (N - 1)) =
      A.card * (Fintype.card K ^ N * Fintype.card E ^ (N - 1)) by ring,
    show (Fintype.card K : ℝ≥0∞) ^ N * (Fintype.card E * Fintype.card E ^ (N - 1)) =
      Fintype.card E * (Fintype.card K ^ N * Fintype.card E ^ (N - 1)) by ring,
    ENNReal.mul_div_mul_right _ _ hK hK']

/-- **The membership test is `(2^14 - 1) / 2^128`-sound**: a fixed matrix that is not a codeword
passes for at most `2^14 - 1` of the `|E| = 2^128` values of the deployed challenge
(`membership.rs:12-15`), which the nonce search reads off one label of uniform draws: the label
it selects depends on the proofs of work alone (`selectChal_some`, `prob_sel_le`). Without a valid
nonce the check is on every challenge, which a non-codeword fails. -/
theorem checker_sound (r : ℕ) :
    (checker r).Sound (leanDaErasureCode r) ((2 ^ 14 - 1) / 2 ^ 128) := by
  intro c hc
  rw [mem_code_iff] at hc
  push Not at hc
  obtain ⟨i, hi⟩ := hc
  have hcard := card_acceptSet_le hi
  have hlt : (acceptSet (matrixRow c i)).card < Fintype.card E := by
    rw [card_E]; omega
  obtain ⟨z₀, -, hz₀⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := acceptSet (matrixRow c i)) (t := Finset.univ) (by rw [Finset.card_univ]; exact hlt)
  rw [mem_acceptSet] at hz₀
  calc Pr{let x ← (fun l ↦ (checker r).check l c) <$> ($ᵗ MembershipChallenge)}[x = true]
      = Pr{let l ← $ᵗ MembershipChallenge}[(checker r).check l c = true] := prEvent_map _ _ _
    _ ≤ Pr{let l ← $ᵗ MembershipChallenge}[
          (l (selIdx fun j ↦ (l j).2)).1 ∈ acceptSet (matrixRow c i)] :=
        prEvent_mono _ _ _ fun l hl ↦ by
          rw [checker_check_iff] at hl
          generalize hs : selectChal l = o at hl
          cases o with
          | none =>
            rw [membershipCheckOpt_none] at hl
            have h₀ : innerProduct (dualCodewordAt z₀) (matrixRow c i) = 0 :=
              (membershipCheck_iff z₀ c).mp (hl z₀) i
            exact (hz₀ h₀).elim
          | some z =>
            rw [membershipCheckOpt] at hl
            rw [← selectChal_some hs, mem_acceptSet]
            exact (membershipCheck_iff z c).mp hl i
    _ ≤ (acceptSet (matrixRow c i)).card / Fintype.card E :=
        prob_sel_le (by simp) selIdx _
    _ ≤ (2 ^ 14 - 1) / 2 ^ 128 := by
        rw [card_E, Nat.cast_pow, Nat.cast_ofNat]
        refine ENNReal.div_le_div_right ?_ _
        calc ((acceptSet (matrixRow c i)).card : ℝ≥0∞) ≤ ((2 ^ 14 - 1 : ℕ) : ℝ≥0∞) :=
              Nat.cast_le.mpr hcard
          _ = 2 ^ 14 - 1 := by rw [ENNReal.natCast_sub]; norm_num

/-! ## The vector commitment -/

theorem merkleVC_perfectlyComplete (r : ℕ) (H : List UInt8 → Common.DigestBytes) :
    (merkleVC r H).PerfectlyComplete :=
  fun _ _ c p ↦ verifyCell_openCell H c p

/-- **Position binding of the Merkle commitment**, by reduction to an `H` collision. -/
theorem posBindingExp_le_hashCollisionExp (r : ℕ) (H : List UInt8 → Common.DigestBytes)
    (A : VectorCommitment.PosBindingAdv Cell (r * 128) Unit Common.DigestBytes CellOpening) :
    Pr{let b ← (merkleVC r H).posBindingExp A}[b = true] ≤
      Pr{let b ← hashCollisionExp H (merkleCollider r H A)}[b = true] := by
  unfold VectorCommitment.posBindingExp hashCollisionExp merkleCollider merkleVC
  simp only [monad_norm]
  refine OracleComp.prEvent_bind_mono_of_support _ _ _ fun ⟨com, p, x, τ, x', τ'⟩ _ ↦ ?_
  simp only [Function.comp_apply]
  refine prEvent_pure_mono fun hwin ↦ ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin ⊢
  exact openingsCollision_spec H hwin.1.1 hwin.1.2 hwin.2

/-! ## The scheme -/

/-- **LeanDA in Wagner's random-oracle model**: his erasure code commitment from the code, the
Merkle commitment with the hash `H`, the membership test and an argument of knowledge `ps`, the
challenge a random oracle of the roots. His theorems for it are steps of the proofs of the end
statements, which are in the random-permutation model. -/
noncomputable def leanDa (r : ℕ) (H : List UInt8 → Common.DigestBytes) {Crs Proof : Type}
    (ps : WArgument r H Crs Proof) :=
  scheme (m := OracleComp (unifSpec + (Common.DigestBytes →ₒ MembershipChallenge)))
      (leanDaErasureCode r) (merkleVC r H)
    (checker r) ps

end LeanDa
