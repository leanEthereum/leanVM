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
    (checker r).check z c = true ↔ ∀ i, innerProduct (dualCodewordAt (z 1)) (matrixRow c i) = 0 :=
  decide_eq_true_iff

theorem checker_complete (r : ℕ) : (checker r).Complete (leanDaErasureCode r) := by
  intro c hc z
  rw [mem_code_iff] at hc
  exact (checker_check_iff z c).mpr fun i ↦ dot_dual_eq_zero (hc i) (z 1)

theorem card_E : Fintype.card E = 2 ^ 192 := by
  rw [← Nat.card_eq_fintype_card, BF64.nat_card_ext3]

/-- The challenges: `|E|² = 2^384`. -/
theorem card_challenges : Fintype.card MembershipChallenge = 2 ^ 192 * 2 ^ 192 := by
  rw [Fintype.card_fun, card_E, Fintype.card_fin, sq]

/-- The pairs whose component `1` satisfies `f`: `|F|` times as many as the values. Generic in
`F`: at `E`, a hypothesis `l ∈ Finset.univ.filter _` would unfold `Finset.univ`. -/
theorem card_filter_one {F : Type*} [Fintype F] [DecidableEq F] (f : F → Prop) [DecidablePred f] :
    (Finset.univ.filter fun l : Fin 2 → F ↦ f (l 1)).card =
      Fintype.card F * (Finset.univ.filter f).card := by
  have h : (Finset.univ.filter fun l : Fin 2 → F ↦ f (l 1)) =
      Fintype.piFinset fun j : Fin 2 ↦ if j = 1 then Finset.univ.filter f else Finset.univ := by
    ext l
    simp [Fintype.mem_piFinset, Fin.forall_fin_two]
  rw [h, Fintype.card_piFinset, Fin.prod_univ_two]
  simp

/-- **The membership test is `(2^14 - 1) / 2^192`-sound**: a fixed matrix that is not a codeword
passes for at most `2^14 - 1` of the `|E| = 2^192` values of the deployed challenge
(`membership.rs:12-14`), component `1` of the pair: the marginal of a uniform pair. -/
theorem checker_sound (r : ℕ) :
    (checker r).Sound (leanDaErasureCode r) ((2 ^ 14 - 1) / 2 ^ 192) := by
  intro c hc
  rw [mem_code_iff] at hc
  push Not at hc
  obtain ⟨i, hi⟩ := hc
  have hcard := card_acceptSet_le hi
  calc Pr{let x ← (fun l ↦ (checker r).check l c) <$> ($ᵗ MembershipChallenge)}[x = true]
      = Pr{let l ← $ᵗ MembershipChallenge}[(checker r).check l c = true] := prEvent_map _ _ _
    _ ≤ Pr{let l ← $ᵗ MembershipChallenge}[
          innerProduct (dualCodewordAt (l 1)) (matrixRow c i) = 0] :=
        prEvent_mono _ _ _ fun l hl ↦ (checker_check_iff l c).mp hl i
    _ = (Finset.univ.filter fun l : MembershipChallenge ↦
          innerProduct (dualCodewordAt (l 1)) (matrixRow c i) = 0).card /
          (Fintype.card MembershipChallenge : ℝ≥0∞) :=
        SampleableType.prEvent_uniformSample _
    _ ≤ (2 ^ 14 - 1) / 2 ^ 192 := by
        rw [card_filter_one (fun z ↦ innerProduct (dualCodewordAt z) (matrixRow c i) = 0),
          ← acceptSet, card_challenges, card_E, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat, ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ two_ne_zero)
            (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
        gcongr
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
