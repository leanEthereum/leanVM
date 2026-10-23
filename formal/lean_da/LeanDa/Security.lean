import LeanDa.Membership
import LeanDa.Merkle
import PqDas.Proof.PositionBinding
import PqDas.Proof.CorollaryCodeBinding

/-!
# LeanDA in Wagner's framework

The building blocks of `PqDas`, instantiated with LeanDA (`LeanDa.Scheme`) for `r ≥ 1` rows:

* the erasure code `code r`: `r` payloads, each encoded by the systematic Reed-Solomon encoder
  and cut into `128` cells, a codeword being `r · 128` cells;
* the vector commitment `merkleVC r H`: the root of the two Merkle trees over the cells with hash
  `H`, cells opened by their column-tree paths. It is perfectly complete
  (`merkleVC_perfectlyComplete`), and its position binding reduces to finding an `H` collision
  through the explicit `merkleCollider` (`posBindingExp_le_hashCollisionExp`);
* the code checker `checker r`: the membership test, complete (`checker_complete`) and
  `14 / 2^192`-sound over uniform `z ∈ E^14` (`checker_sound`).

`leanDa r H ps` is the scheme with the hash `H` and an argument of knowledge `ps` for the relation
`Relation r H`: the cells commit to the root and pass the membership test on the challenges.
-/

open PqDas OracleComp OracleSpec ENNReal

namespace LeanDa

/-! ## The code -/

/-- The first half of a codeword: its payload. -/
def firstHalf (w : Row) : Payload := fun a ↦ w (Fin.castLE (by norm_num) a)

theorem posRow_pos {r : ℕ} (i : Fin r) (j : Fin 128) : posRow (pos i j) = i :=
  Fin.ext (by simp only [posRow, pos]; omega)

theorem posCell_pos {r : ℕ} (i : Fin r) (j : Fin 128) : posCell (pos i j) = j :=
  Fin.ext (by simp only [posCell, pos]; omega)

theorem pos_posRow_posCell {r : ℕ} (p : Fin (r * 128)) : pos (posRow p) (posCell p) = p :=
  Fin.ext (by simp only [posRow, posCell, pos]; omega)

theorem rowOf_encodeMatrix {r : ℕ} (msg : Fin r → Payload) (i : Fin r) :
    rowOf (encodeMatrix msg) i = encodeRow (msg i) := by
  funext b
  simp only [rowOf, encodeMatrix, rowCell, posRow_pos, posCell_pos]
  congr 1
  exact Fin.ext (by simp only; omega)

theorem encodeMatrix_firstHalf {r : ℕ} (c : Fin (r * 128) → Cell) (h : ∀ i, rowOf c i ∈ rsCode) :
    encodeMatrix (fun i ↦ firstHalf (rowOf c i)) = c := by
  funext p s
  simp only [encodeMatrix, rowCell]
  rw [show firstHalf (rowOf c (posRow p)) =
      fun a ↦ rowOf c (posRow p) (Fin.castLE (by norm_num) a) from rfl, encodeRow_firstHalf (h _)]
  simp only [rowOf]
  have h1 : (⟨(256 * (posCell p : ℕ) + s) / 256, by omega⟩ : Fin 128) = posCell p :=
    Fin.ext (by simp only; omega)
  have h2 : (⟨(256 * (posCell p : ℕ) + s) % 256, by omega⟩ : Fin 256) = s :=
    Fin.ext (by simp only; omega)
  rw [h1, h2, pos_posRow_posCell]

/-- **LeanDA's erasure code**: `r` payloads, encoded row by row and cut into cells. -/
noncomputable def code (r : ℕ) : ErasureCode Payload Cell r (r * 128) := ⟨encodeMatrix⟩

/-- A matrix is a codeword when every row is. -/
theorem mem_code_iff {r : ℕ} (c : Fin (r * 128) → Cell) :
    c ∈ (code r).code ↔ ∀ i, rowOf c i ∈ rsCode := by
  constructor
  · rintro ⟨msg, rfl⟩ i
    change rowOf (encodeMatrix msg) i ∈ rsCode
    rw [rowOf_encodeMatrix]
    exact encodeRow_mem _
  · intro h
    exact ⟨fun i ↦ firstHalf (rowOf c i), encodeMatrix_firstHalf c h⟩

/-! ## The code checker -/

/-- The challenges of the membership test. -/
abbrev Challenges := Fin 14 → E

/-- **LeanDA's code checker**: the membership test on challenges `z ∈ E^14`. -/
noncomputable def checker (r : ℕ) : CodeChecker Cell (r * 128) Challenges := ⟨membershipCheck⟩

theorem checker_check_iff {r : ℕ} (z : Challenges) (c : Fin (r * 128) → Cell) :
    (checker r).check z c = true ↔ ∀ i, dot (dual z) (rowOf c i) = 0 :=
  decide_eq_true_iff

theorem checker_complete (r : ℕ) : (checker r).Complete (code r) := by
  intro c hc z
  rw [mem_code_iff] at hc
  exact (checker_check_iff z c).mpr fun i ↦ dot_dual_eq_zero (hc i) z

theorem card_challenges : Fintype.card Challenges = 2 ^ (192 * 14) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_fun, BF64.nat_card_ext3, Nat.card_fin, ← pow_mul]

/-- `a / (2^192)^14 ≤ 14 / 2^192` from `a ≤ 14 (2^192)^13`. -/
theorem div_le_fourteen_div {a : ℝ≥0∞} (h : a ≤ 14 * ((2 : ℝ≥0∞) ^ 192) ^ 13) :
    a / (2 : ℝ≥0∞) ^ (192 * 14) ≤ 14 / 2 ^ 192 := by
  have hq : (2 : ℝ≥0∞) ^ 192 ≠ 0 := by positivity
  have hq' : (2 : ℝ≥0∞) ^ 192 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [pow_mul]
  refine ENNReal.div_le_of_le_mul (h.trans_eq ?_)
  rw [show ((2 : ℝ≥0∞) ^ 192) ^ 14 = 2 ^ 192 * (2 ^ 192) ^ 13 by ring, ← mul_assoc,
    ENNReal.div_mul_cancel hq hq']

/-- **The membership test is `14 / 2^192`-sound**: a fixed matrix that is not a codeword passes
for at most a `14 / |E|` fraction of the challenges. -/
theorem checker_sound (r : ℕ) : (checker r).Sound (code r) (14 / 2 ^ 192) := by
  intro c hc
  rw [mem_code_iff] at hc
  push Not at hc
  obtain ⟨i, hi⟩ := hc
  have hcard := card_acceptSet_le hi
  rw [← Nat.card_eq_fintype_card (α := E), BF64.nat_card_ext3] at hcard
  calc Pr{let x ← (fun l ↦ (checker r).check l c) <$> ($ᵗ Challenges)}[x = true]
      = Pr{let l ← $ᵗ Challenges}[(checker r).check l c = true] := prEvent_map _ _ _
    _ ≤ Pr{let l ← $ᵗ Challenges}[dot (dual l) (rowOf c i) = 0] :=
        prEvent_mono _ _ _ fun l hl ↦ (checker_check_iff l c).mp hl i
    _ = (acceptSet (rowOf c i)).card / (Fintype.card Challenges : ℝ≥0∞) :=
        SampleableType.prEvent_uniformSample _
    _ ≤ 14 / 2 ^ 192 := by
        rw [card_challenges, Nat.cast_pow, Nat.cast_ofNat]
        refine div_le_fourteen_div ((Nat.cast_le (α := ℝ≥0∞)).mpr hcard |>.trans_eq ?_)
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat]

/-! ## The vector commitment -/

/-- **LeanDA's vector commitment** with hash `H`: the root of the two Merkle trees, cells opened
by their column-tree paths. It needs no key. -/
def merkleVC (r : ℕ) (H : List UInt8 → Digest) :
    VectorCommitment Cell (r * 128) Unit Digest Opening where
  setup := pure ()
  commit _ c := commitCells H c
  openAt _ c p := openCell H c p
  verify _ com p x τ := verifyCell H r com p x τ

theorem merkleVC_perfectlyComplete (r : ℕ) (H : List UInt8 → Digest) :
    (merkleVC r H).PerfectlyComplete :=
  fun _ _ c p ↦ verifyCell_openCell H c p

/-- The collision experiment for a hash function: a finder wins if it outputs two different
byte strings with the same hash. -/
def hashCollisionExp (H : List UInt8 → Digest) (B : ProbComp (List UInt8 × List UInt8)) :
    ProbComp Bool := do
  let (a, b) ← B
  return (decide (a ≠ b) && decide (H a = H b))

/-- **The reduction from position binding to a collision**: run the adversary and climb its two
openings (`openingsCollision`). -/
def merkleCollider (r : ℕ) (H : List UInt8 → Digest)
    (A : VectorCommitment.PosBindingAdv Cell (r * 128) Unit Digest Opening) :
    ProbComp (List UInt8 × List UInt8) := do
  let (_, p, x, τ, x', τ') ← A ()
  return openingsCollision H r p x τ x' τ'

/-- **Position binding of the Merkle commitment**, by reduction to an `H` collision. -/
theorem posBindingExp_le_hashCollisionExp (r : ℕ) (H : List UInt8 → Digest)
    (A : VectorCommitment.PosBindingAdv Cell (r * 128) Unit Digest Opening) :
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

/-- The relation the argument proves: the cells commit to the root and pass the membership test
on the challenges. -/
noncomputable abbrev Relation (r : ℕ) (H : List UInt8 → Digest) := schemeRel (merkleVC r H) (checker r)

/-- An argument of knowledge for `Relation r H`. -/
abbrev Argument (r : ℕ) (H : List UInt8 → Digest) (Crs Proof : Type) :=
  Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof (Relation r H)

/-- **LeanDA**: Wagner's erasure code commitment from the code, the Merkle commitment with the
hash `H`, the membership test and an argument of knowledge `ps`. -/
noncomputable def leanDa (r : ℕ) (H : List UInt8 → Digest) {Crs Proof : Type} (ps : Argument r H Crs Proof) :=
  scheme (m := OracleComp (unifSpec + (Digest →ₒ Challenges))) (code r) (merkleVC r H)
    (checker r) ps

end LeanDa
