module

public import Quantum.Sponge.Oracle.Hardwired.Runtime

@[expose] public section

/-!
# The graded event bound for the hardwired runtime

Let `S` be a set of states `(D, W, m)` of the hardwired register that is upward closed in the
databases for each classical datum `(W, m)` and does not contain the start `(∅, W₀, m₀)`. Then
for a program making at most `q` sponge calls and `K` read and program calls, if at its `n`-th
sponge call a fresh cell of a database below `n + K + 1` entries enters `S` with probability at
most `ε n`, and each read or program call raises the weight of `S` by at most `d σ` on its input
`σ`, the final weight of `S` is at most `(∑_{n < q} √(6 ε n) + √(∑ d))²`
(`eventWeight_spongeHardwiredRuntime_le`).

The sponge ports act on the block of `(W, m)` as `(1 - Π_W) O + Π_W (S_W ⊗ 1)`
(`spongeHardwired_U`), with `O` the compressed oracle, so their commutator with the event is
`(1 - Π_W) [Q, O]`, and the certificate of `spongeCompressed`
(`posSemidef_spongeCompressed_certificate`) bounds it on every block
(`posSemidef_spongeHardwired_certificate`). The classical steps are added up under one square root
by `rpow_inv_two_eventWeight_le_mixed`.
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

universe u v w

namespace Quantum.Sponge

open Quantum QuantumRuntime

/-! ## Projectors -/

section proj

variable {p n κ : Type*} [Fintype p] [DecidableEq p] [Fintype n] [DecidableEq n] [DecidableEq κ]

omit [Fintype p] [Fintype n] in
/-- The identity next to a label projector is the label projector of the second factor. -/
theorem one_kronecker_labelProjector (β : n → κ) (i : κ) :
    (1 : Matrix p p ℂ) ⊗ₖ (labelProjector β i : Matrix n n ℂ) =
      labelProjector (fun q : p × n ↦ β q.2) i := by
  ext ⟨a, c⟩ ⟨b, d⟩
  by_cases hab : a = b <;> by_cases hcd : c = d <;>
    simp [labelProjector, kroneckerMap_apply, hab, hcd]

omit [Fintype p] [DecidableEq p] in
/-- Label projectors commute. -/
theorem labelProjector_mul_comm {κ' : Type*} [DecidableEq κ'] (β : n → κ) (i : κ) (β' : n → κ')
    (i' : κ') :
    (labelProjector β i : Matrix n n ℂ) * labelProjector β' i' =
      labelProjector β' i' * labelProjector β i := by
  simp only [labelProjector, diagonal_mul_diagonal, mul_comm]

/-- **A masked port.** Let `U = L O + N`, with `L = labelProjector c false` a diagonal projector,
and `Q` commuting with `L` and `N`. Then `[Q, U] = L [Q, O]`, so a commutator certificate for `O`
is one for `U`. -/
theorem posSemidef_masked_certificate (c : n → Bool) (O N Q P : Matrix n n ℂ)
    (hQL : Q * labelProjector c false = labelProjector c false * Q) (hQN : Q * N = N * Q)
    {r : ℝ} (hcert : (r • (1 : Matrix n n ℂ) -
      ((Q * O - O * Q) * P)ᴴ * ((Q * O - O * Q) * P)).PosSemidef) :
    (r • (1 : Matrix n n ℂ) -
      ((Q * (labelProjector c false * O + N) - (labelProjector c false * O + N) * Q) * P)ᴴ *
        ((Q * (labelProjector c false * O + N) - (labelProjector c false * O + N) * Q) *
          P)).PosSemidef := by
  set L : Matrix n n ℂ := labelProjector c false
  set L' : Matrix n n ℂ := labelProjector c true
  set Y := (Q * O - O * Q) * P
  have hX : (Q * (L * O + N) - (L * O + N) * Q) * P = L * Y := by
    simp only [Y, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hQL, hQN, Matrix.mul_sub,
      Matrix.sub_mul]
    abel
  have hL : Lᴴ * L + L'ᴴ * L' = 1 := by
    simp only [L, L', labelProjector, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_add,
      ← diagonal_one]
    congr 1
    funext q
    cases hc : c q <;> simp [hc]
  have hY : r • (1 : Matrix n n ℂ) - (L * Y)ᴴ * (L * Y) =
      (r • 1 - Yᴴ * Y) + (L' * Y)ᴴ * (L' * Y) := by
    have h : Yᴴ * Y = Yᴴ * (Lᴴ * L + L'ᴴ * L') * Y := by rw [hL, Matrix.mul_one]
    rw [h]
    simp only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [hX, hY]
  exact hcert.add (posSemidef_conjTranspose_mul_self _)

end proj

/-! ## The sponge ports on blocks -/

section piForm

variable {A Y T : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype T] [DecidableEq T]

/-- The table oracle of a read that is fixed on the hardwired cells `w` is the table oracle of the
underlying read on the other query inputs, and the oracle unitary of the hardwired values on the
hardwired ones. -/
theorem tableOracle_getD (lk : T → A → Y) (w : A → Option Y) :
    tableOracle (fun t a ↦ (w a).getD (lk t a)) =
      labelProjector (fun q : (A × Y) × T ↦ (w q.1.1).isSome) false * tableOracle lk +
        (labelProjector (fun p : A × Y ↦ (w p.1).isSome) true *
          oracleUnitary fun a ↦ (w a).getD 0) ⊗ₖ (1 : Matrix T T ℂ) := by
  ext ⟨⟨a, y⟩, t⟩ ⟨⟨a', y'⟩, t'⟩
  simp only [Matrix.add_apply, labelProjector, diagonal_mul, kroneckerMap_apply,
    tableOracle_apply, tableOracleEquiv_apply, oracleEquiv_apply, oracleUnitary_apply,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases ha : a = a'
  · subst ha
    rcases Option.eq_none_or_eq_some (w a) with hw | ⟨v, hw⟩
    · simp [hw]
    · by_cases ht : t = t' <;> simp [hw, ht]
  · simp [ha]

/-- **The hardwired port, masked.** Conjugating by an involution `C` of the table register, the
table oracle of `(w a).getD (lk t a)` is `(1 - Π_w) (C T_lk C) + Π_w (S_w ⊗ 1)`. -/
theorem conj_tableOracle_getD (C : Matrix T T ℂ) (hCC : C * C = 1)
    (lk : T → A → Y) (w : A → Option Y) :
    ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) * tableOracle (fun t a ↦ (w a).getD (lk t a)) *
        ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) =
      labelProjector (fun q : (A × Y) × T ↦ (w q.1.1).isSome) false *
          (((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) * tableOracle lk *
            ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C)) +
        (labelProjector (fun p : A × Y ↦ (w p.1).isSome) true *
          oracleUnitary fun a ↦ (w a).getD 0) ⊗ₖ (1 : Matrix T T ℂ) := by
  set L : Matrix (A × Y) (A × Y) ℂ := labelProjector (fun p : A × Y ↦ (w p.1).isSome) false
  set N : Matrix (A × Y) (A × Y) ℂ := labelProjector (fun p : A × Y ↦ (w p.1).isSome) true *
    oracleUnitary fun a ↦ (w a).getD 0
  have hL : labelProjector (fun q : (A × Y) × T ↦ (w q.1.1).isSome) false =
      L ⊗ₖ (1 : Matrix T T ℂ) :=
    (labelProjector_kronecker_one (fun p : A × Y ↦ (w p.1).isSome) false).symm
  have h1 : ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) * (L ⊗ₖ (1 : Matrix T T ℂ)) =
      (L ⊗ₖ (1 : Matrix T T ℂ)) * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) := by
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_one]
  have h2 : ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) * (N ⊗ₖ (1 : Matrix T T ℂ)) *
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) = N ⊗ₖ (1 : Matrix T T ℂ) := by
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_one, hCC]
  rw [tableOracle_getD, hL, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, h1, h2]
  simp only [Matrix.mul_assoc]

end piForm

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

variable (X Z M) in
/-- Splitting the hardwired register next to a query register into the databases and the
classical data `(W, m)`. -/
def hwSplit (P : Type) : P × HwReg X Z M ≃ (P × DbReg X Z) × (Hw X Z × M) :=
  (Equiv.prodAssoc P (DbReg X Z) (Hw X Z × M)).symm

/-- Whether the query input of port `i` is a hardwired cell of `W`. -/
def hwMaskFn (W : Hw X Z) : (i : SpongePort) → spongeIn X Z i → Bool
  | .h => fun p ↦ (W.1 p.1).isSome
  | .k => fun p ↦ (W.2.1 p.1).isSome
  | .k' => fun p ↦ (W.2.2 p.1).isSome

variable [AddCommGroup X] [AddCommGroup Z]

/-- The oracle unitary of the hardwired values of port `i`, on its hardwired query inputs. -/
noncomputable def hwShift (W : Hw X Z) :
    (i : SpongePort) → Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ
  | .h => labelProjector (fun p : Z × X ↦ (W.1 p.1).isSome) true *
      oracleUnitary fun z ↦ (W.1 z).getD 0
  | .k => labelProjector (fun p : X × Z ↦ (W.2.1 p.1).isSome) true *
      oracleUnitary fun x ↦ (W.2.1 x).getD 0
  | .k' => labelProjector (fun p : X × Z ↦ (W.2.2 p.1).isSome) true *
      oracleUnitary fun x ↦ (W.2.2 x).getD 0

omit [AddCommGroup X] [AddCommGroup Z] in
/-- A port of the hardwired runtime acts block by block on the classical data. -/
theorem hwPort_eq_liftBlocks {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] (read : HwReg X Z M → A → Y) :
    hwPort read = liftBlocks (hwSplit X Z M (A × Y)) fun b ↦
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressDbs X Z) * tableOracle (fun D ↦ read (D, b)) *
        ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressDbs X Z) := by
  have h1 : liftBlocks (hwSplit X Z M (A × Y))
      (fun _ ↦ (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressDbs X Z) =
      (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M := by
    ext ⟨p, D, b⟩ ⟨p', D', b'⟩
    by_cases hb : b = b' <;>
      simp [liftBlocks, blockDiagonal_apply, hwSplit, compressReg, kroneckerMap_apply,
        Matrix.one_apply, hb]
  have h2 : liftBlocks (hwSplit X Z M (A × Y)) (fun b ↦ tableOracle fun D ↦ read (D, b)) =
      tableOracle read := by
    ext ⟨p, D, b⟩ ⟨p', D', b'⟩
    by_cases hb : b = b'
    · subst hb
      simp [liftBlocks, blockDiagonal_apply, hwSplit, tableOracle_apply]
    · simp [liftBlocks, blockDiagonal_apply, hwSplit, tableOracle_apply, hb]
  rw [show (fun b ↦ ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressDbs X Z) *
      tableOracle (fun D ↦ read (D, b)) * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressDbs X Z)) =
      (fun _ ↦ (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressDbs X Z) *
        (fun b ↦ tableOracle fun D ↦ read (D, b)) *
        (fun _ ↦ (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressDbs X Z) from rfl,
    liftBlocks_mul, liftBlocks_mul, h1, h2, hwPort]

/-- **The sponge ports on blocks.** On the block of `(W, m)`, port `i` is the compressed oracle on
the query inputs that are not hardwired in `W`, and the oracle unitary of the hardwired values on
the others. -/
theorem spongeHardwired_U (W₀ : Hw X Z) (m₀ : M) (i : SpongePort) :
    (spongeHardwired X Z W₀ m₀).U i = liftBlocks (hwSplit X Z M (spongeIn X Z i)) fun b ↦
      labelProjector (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1) false *
          (spongeCompressed X Z).U i +
        hwShift b.1 i ⊗ₖ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ) := by
  cases i
  · change hwPort _ = _
    rw [hwPort_eq_liftBlocks, spongeCompressed_U_h]
    congr 1
    funext b
    exact conj_tableOracle_getD (compressDbs X Z) compressDbs_mul_self
      (fun D : DbReg X Z ↦ D.1.lookup) b.1.1
  · change hwPort _ = _
    rw [hwPort_eq_liftBlocks, spongeCompressed_U_k]
    congr 1
    funext b
    exact conj_tableOracle_getD (compressDbs X Z) compressDbs_mul_self
      (fun D : DbReg X Z ↦ D.2.1.lookup) b.1.2.1
  · change hwPort _ = _
    rw [hwPort_eq_liftBlocks, spongeCompressed_U_k']
    congr 1
    funext b
    exact conj_tableOracle_getD (compressDbs X Z) compressDbs_mul_self
      (fun D : DbReg X Z ↦ D.2.2.lookup) b.1.2.2

/-- Every sponge port raises the grade of the databases by at most one. -/
theorem dbGrade_le_of_spongeHardwired_U_ne_zero (W₀ : Hw X Z) (m₀ : M) (i : SpongePort)
    (a a' : spongeIn X Z i) (s s' : HwReg X Z M)
    (h : (spongeHardwired X Z W₀ m₀).U i (a', s') (a, s) ≠ 0) :
    dbGrade s'.1 ≤ dbGrade s.1 + 1 := by
  rw [spongeHardwired_U] at h
  have key := dbGrade_le_of_spongeCompressed_U_ne_zero i a a' s.1 s'.1
  generalize (spongeCompressed X Z).U i = O at h key
  obtain ⟨D', b'⟩ := s'
  obtain ⟨D, b⟩ := s
  simp only [liftBlocks, submatrix_apply, hwSplit, Equiv.prodAssoc_symm_apply,
    blockDiagonal_apply] at h
  split_ifs at h with hb
  · rw [Matrix.add_apply, labelProjector, diagonal_mul, kroneckerMap_apply, Matrix.one_apply] at h
    by_cases hO : O (a', D') (a, D) = 0
    · rw [hO, mul_zero, zero_add] at h
      have h' := right_ne_zero_of_mul h
      split_ifs at h' with hD
      · have hD' : D' = D := hD
        subst hD'
        exact Nat.le_succ _
      · exact absurd rfl h'
    · exact key hO
  · exact absurd rfl h

/-! ## The certificate -/

/-- The projector of the hardwired register on an event. -/
noncomputable def hwProjector (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] :
    Matrix (HwReg X Z M) (HwReg X Z M) ℂ :=
  labelProjector (fun s : HwReg X Z M ↦ decide (s ∈ S)) true

/-- Membership in a slice is decidable when membership in the event is. -/
instance (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (W : Hw X Z) (m : M) :
    DecidablePred (· ∈ slice S W m) :=
  fun D ↦ inferInstanceAs (Decidable (((D.h, D.k, D.k'), W, m) ∈ S))

omit [Fintype M] [AddCommGroup X] [AddCommGroup Z] in
/-- The event projector next to a query register, block by block. -/
theorem one_kronecker_hwProjector_eq_liftBlocks (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (P : Type) [Fintype P] [DecidableEq P] :
    (1 : Matrix P P ℂ) ⊗ₖ hwProjector S = liftBlocks (hwSplit X Z M P) fun b ↦
      (1 : Matrix P P ℂ) ⊗ₖ dbsProjector (slice S b.1 b.2) := by
  ext ⟨a, D, b⟩ ⟨a', D', b'⟩
  by_cases hb : b = b' <;> by_cases hD : D = D' <;> by_cases ha : a = a' <;>
    simp [liftBlocks, blockDiagonal_apply, hwSplit, kroneckerMap_apply, hwProjector,
      dbsProjector, labelProjector, slice, DbReg.toDbs, hb, hD, ha]

/-- **The per-port certificate of the hardwired runtime**, at the `n`-th call, with rate `6 ε`:
upward closure and fresh bounds of every slice of the event. -/
theorem posSemidef_spongeHardwired_certificate (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (hup : ∀ W m, UpClosed (slice S W m)) {n : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤)
    (hε : ∀ W m, FreshBound (slice S W m) (n + 1) ε) (W₀ : Hw X Z) (m₀ : M) (i : SpongePort) :
    let U := (spongeHardwired X Z W₀ m₀).U i
    let Q := (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ hwProjector S
    let P : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ :=
      diagonal fun q ↦ if dbGrade q.2.1 ≤ n then (1 : ℂ) else 0
    ((6 * ε.toReal) •
        (1 : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ) -
      ((Q * U - U * Q) * P)ᴴ * ((Q * U - U * Q) * P)).PosSemidef := by
  intro U Q P
  let e := hwSplit X Z M (spongeIn X Z i)
  let Ub : Hw X Z × M →
      Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ := fun b ↦
    labelProjector (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1) false *
        (spongeCompressed X Z).U i +
      hwShift b.1 i ⊗ₖ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)
  let Qb : Hw X Z × M →
      Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ := fun b ↦
    (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ dbsProjector (slice S b.1 b.2)
  let Pb : Hw X Z × M →
      Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ := fun _ ↦
    diagonal fun q : spongeIn X Z i × DbReg X Z ↦ if dbGrade q.2 ≤ n then (1 : ℂ) else 0
  have hu : U = liftBlocks e Ub := spongeHardwired_U W₀ m₀ i
  have hq : Q = liftBlocks e Qb := one_kronecker_hwProjector_eq_liftBlocks S _
  have hp : P = liftBlocks e Pb := (liftBlocks_diagonal e _).symm
  have hb (b : Hw X Z × M) :
      ((6 * ε.toReal) • (1 : Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ) -
        (((Qb * Ub - Ub * Qb) * Pb) b)ᴴ * (((Qb * Ub - Ub * Qb) * Pb) b)).PosSemidef := by
    have hQL : Qb b * labelProjector (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1)
        false = labelProjector (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1) false *
          Qb b := by
      simp only [Qb, dbsProjector, one_kronecker_labelProjector]
      exact labelProjector_mul_comm _ _ _ _
    have hQN : Qb b * (hwShift b.1 i ⊗ₖ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) =
        (hwShift b.1 i ⊗ₖ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) * Qb b := by
      simp only [Qb, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    exact posSemidef_masked_certificate (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1)
      ((spongeCompressed X Z).U i) _ (Qb b) (Pb b) hQL hQN
      (posSemidef_spongeCompressed_certificate (slice S b.1 b.2) (hup b.1 b.2) hεtop
        (hε b.1 b.2) i)
  have hh := posSemidef_liftBlocks e hb
  change (liftBlocks e ((6 * ε.toReal) • 1 -
    (fun b ↦ (((Qb * Ub - Ub * Qb) * Pb) b)ᴴ) * ((Qb * Ub - Ub * Qb) * Pb))).PosSemidef at hh
  rw [liftBlocks_sub, liftBlocks_smul, liftBlocks_one] at hh
  change (_ - liftBlocks e ((fun b ↦ (((Qb * Ub - Ub * Qb) * Pb) b)ᴴ) *
    ((Qb * Ub - Ub * Qb) * Pb))).PosSemidef at hh
  rw [liftBlocks_mul, liftBlocks_adjoint, liftBlocks_mul, liftBlocks_sub, liftBlocks_mul,
    liftBlocks_mul, ← hq, ← hp, ← hu] at hh
  exact hh

/-! ## Grades -/

section grade

omit [Fintype X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z] [Fintype M] in
/-- A nonzero entry of a classical Kraus operator is a nonzero entry of its block. -/
theorem clsKraus_ne_zero {T B : Type} [DecidableEq B] {p : B → Prop} [DecidablePred p] {φ : B → B}
    {R : B → Matrix T T ℂ} {s s' : T × B} (h : clsKraus p φ R s' s ≠ 0) :
    R s.2 s'.1 s.1 ≠ 0 := by
  rw [clsKraus_apply] at h
  split_ifs at h
  · exact h
  · exact absurd rfl h

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z]
  [Fintype M] [DecidableEq M] in
theorem kronecker_one_ne_zero {m n : Type*} [DecidableEq n] {A : Matrix m m ℂ} {a a' : m}
    {b b' : n} (h : (A ⊗ₖ (1 : Matrix n n ℂ)) (a', b') (a, b) ≠ 0) : A a' a ≠ 0 ∧ b' = b := by
  rw [kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with hb
  · exact ⟨left_ne_zero_of_mul h, hb⟩
  · exact absurd (mul_zero _) h

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z]
  [Fintype M] [DecidableEq M] in
theorem one_kronecker_ne_zero {m n : Type*} [DecidableEq m] {A : Matrix n n ℂ} {a a' : m}
    {b b' : n} (h : ((1 : Matrix m m ℂ) ⊗ₖ A) (a', b') (a, b) ≠ 0) : a' = a ∧ A b' b ≠ 0 := by
  rw [kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with ha
  · exact ⟨ha, right_ne_zero_of_mul h⟩
  · exact absurd (zero_mul _) h

omit [DecidableEq X] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z] [Fintype M]
  [DecidableEq M] in
theorem dbGrade_le_of_sizes {D D' : DbReg X Z} (h₁ : D'.1.size ≤ D.1.size + 1)
    (h₂ : D'.2.1.size ≤ D.2.1.size + 1) (h₃ : D'.2.2.size ≤ D.2.2.size + 1) :
    dbGrade D' ≤ dbGrade D + 1 := by
  simp only [dbGrade]
  omega

omit [AddCommGroup X] [AddCommGroup Z] [Fintype M] in
/-- Every read port changes at most one database cell. -/
theorem dbGrade_le_of_hwReadKraus_ne_zero (c : HwRead X Z M) (r : c.Result) (u u' : Unit)
    (s s' : HwReg X Z M) (h : hwReadKraus c r (u', s') (u, s) ≠ 0) :
    dbGrade s'.1 ≤ dbGrade s.1 + 1 := by
  obtain ⟨⟨dh', dk', dk₂'⟩, b'⟩ := s'
  obtain ⟨⟨dh, dk, dk₂⟩, b⟩ := s
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at h
    have h₁ := clsKraus_ne_zero (one_kronecker_ne_zero h).2
    obtain ⟨h₂, h₃⟩ := kronecker_one_ne_zero h₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₃
    exact dbGrade_le_of_sizes (size_le_of_eq_off (cellRead_apply_ne_zero h₂)) (by simp)
      (by simp)
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at h
    have h₁ := clsKraus_ne_zero (one_kronecker_ne_zero h).2
    obtain ⟨rfl, h₂⟩ := one_kronecker_ne_zero h₁
    obtain ⟨h₃, rfl⟩ := kronecker_one_ne_zero h₂
    exact dbGrade_le_of_sizes (by simp) (size_le_of_eq_off (cellRead_apply_ne_zero h₃))
      (by simp)
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at h
    have h₁ := clsKraus_ne_zero (one_kronecker_ne_zero h).2
    obtain ⟨rfl, h₂⟩ := one_kronecker_ne_zero h₁
    obtain ⟨rfl, h₃⟩ := one_kronecker_ne_zero h₂
    exact dbGrade_le_of_sizes (by simp) (by simp)
      (size_le_of_eq_off (cellRead_apply_ne_zero h₃))

omit [AddCommGroup X] [AddCommGroup Z] [Fintype M] in
/-- Every program port changes at most one database cell. -/
theorem dbGrade_le_of_hwProgKraus_ne_zero (c : HwProg X Z) (r : c.Result) (u u' : Unit)
    (s s' : HwReg X Z M) (h : hwProgKraus c r (u', s') (u, s) ≠ 0) :
    dbGrade s'.1 ≤ dbGrade s.1 + 1 := by
  obtain ⟨⟨dh', dk', dk₂'⟩, b'⟩ := s'
  obtain ⟨⟨dh, dk, dk₂⟩, b⟩ := s
  cases c with
  | programH z v =>
    simp only [hwProgKraus, programKrausH] at h
    have h₁ := clsKraus_ne_zero (one_kronecker_ne_zero h).2
    obtain ⟨h₂, h₃⟩ := kronecker_one_ne_zero h₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₃
    exact dbGrade_le_of_sizes (size_le_of_eq_off (cellDiscard_apply_ne_zero h₂)) (by simp)
      (by simp)
  | programK x v =>
    simp only [hwProgKraus, programKrausK] at h
    have h₁ := clsKraus_ne_zero (one_kronecker_ne_zero h).2
    obtain ⟨rfl, h₂⟩ := one_kronecker_ne_zero h₁
    obtain ⟨h₃, rfl⟩ := kronecker_one_ne_zero h₂
    exact dbGrade_le_of_sizes (by simp) (size_le_of_eq_off (cellDiscard_apply_ne_zero h₃))
      (by simp)
  | programK' x v =>
    simp only [hwProgKraus, programKrausK'] at h
    have h₁ := clsKraus_ne_zero (one_kronecker_ne_zero h).2
    obtain ⟨rfl, h₂⟩ := one_kronecker_ne_zero h₁
    obtain ⟨rfl, h₃⟩ := one_kronecker_ne_zero h₂
    exact dbGrade_le_of_sizes (by simp) (by simp)
      (size_le_of_eq_off (cellDiscard_apply_ne_zero h₃))

/-- Every step of the hardwired runtime raises the grade of the databases by at most one. -/
theorem querySupportedOn_spongeHardwiredRuntime_step (W₀ : Hw X Z) (m₀ : M)
    (i : (hwSpec X Z M).Port) (r : (hwSpec X Z M).Result i) (t : ℕ)
    (σ : Matrix ((hwSpec X Z M).In i × (spongeHardwiredRuntime X Z W₀ m₀).D)
      ((hwSpec X Z M).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) ℂ)
    (hσ : QuerySupportedOn (fun q : (hwSpec X Z M).In i × (spongeHardwiredRuntime X Z W₀ m₀).D ↦
      dbGrade q.2.1) (Set.Iic t) σ) :
    QuerySupportedOn (fun q : (hwSpec X Z M).Out i × (spongeHardwiredRuntime X Z W₀ m₀).D ↦
      dbGrade q.2.1) (Set.Iic (t + 1))
        (((spongeHardwiredRuntime X Z W₀ m₀).step i).branch r σ) := by
  rcases i with (p | c) | c
  · exact (spongeHardwired X Z W₀ m₀).querySupportedOn_toRuntime_step
      (fun s : HwReg X Z M ↦ dbGrade s.1)
      (fun i a a' d d' h ↦ dbGrade_le_of_spongeHardwired_U_ne_zero W₀ m₀ i a a' d d' h) p r t σ hσ
  · have hb : ((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read W₀ m₀ c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      (dbGrade_le_of_hwReadKraus_ne_zero c r q.1 q'.1 q.2 q'.2 hK).trans
        (Nat.add_le_add_right hq 1)
  · have hb : ((spongeHardwiredRuntime X Z W₀ m₀).step (.inr c)).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog W₀ m₀ c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      (dbGrade_le_of_hwProgKraus_ne_zero c r q.1 q'.1 q.2 q'.2 hK).trans
        (Nat.add_le_add_right hq 1)

end grade

/-! ## The event bound -/

/-- Conjugating by a unitary keeps the trace. -/
theorem trace_conj_of_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (σ : Matrix n n ℂ) : (MatrixMap.conj U σ).trace = σ.trace := by
  rw [MatrixMap.trace_conj_apply, ← star_eq_conjTranspose, mem_unitaryGroup_iff'.mp hU,
    Matrix.one_mul]

/-- **One sponge call.** On inputs supported on grades at most `N`, with every slice of `S`
upward closed and with fresh bound `ε` below `N + 1`, a sponge port raises the square root of the
weight of `S` by at most `√(6 ε tr σ)`. -/
theorem rpow_inv_two_potential_spongeHardwired_le (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (hup : ∀ W m, UpClosed (slice S W m)) {N : ℕ} {ε : ℝ≥0∞}
    (hεtop : ε ≠ ⊤) (hε : ∀ W m, FreshBound (slice S W m) (N + 1) ε) (W₀ : Hw X Z) (m₀ : M)
    (i : SpongePort) {σ : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef)
    (hσg : QuerySupportedOn (fun q : spongeIn X Z i × HwReg X Z M ↦ dbGrade q.2.1) (Set.Iic N) σ) :
    QuantumRuntime.potential (hwProjector S)
        (MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U i) σ) ^ (2⁻¹ : ℝ) ≤
      QuantumRuntime.potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
        (6 * ε * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) := by
  set U := (spongeHardwired X Z W₀ m₀).U i
  set Q := (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ hwProjector S
  have hpot : ∀ τ : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ,
      QuantumRuntime.potential (hwProjector S) τ = ENNReal.ofReal (MatrixMap.conj Q τ).trace.re :=
    fun τ ↦ by rw [QuantumRuntime.potential, MatrixMap.amplifyLeft_conj]
  rw [hpot, hpot, ← LinearMap.comp_apply, ← MatrixMap.conj_mul,
    show Q * U = U * Q + (Q * U - U * Q) by abel]
  refine (MatrixMap.ofReal_trace_conj_add_rpow_le hσ _ _).trans (add_le_add (le_of_eq ?_) ?_)
  · rw [MatrixMap.conj_mul, LinearMap.comp_apply,
      trace_conj_of_mem_unitaryGroup ((spongeHardwired X Z W₀ m₀).unitary i)]
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    have hr0 : (0 : ℝ) ≤ 6 * ε.toReal := by positivity
    refine (ofReal_trace_conj_le_of_certificate _ _ hr0
      (posSemidef_spongeHardwired_certificate S hup hεtop hε W₀ m₀ i) hσ
      (hσg.conj_diagonal_eq_self fun q hq ↦ by simp [Set.mem_Iic.mp hq])).trans_eq ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hεtop]
    norm_num

/-- The classical costs on the ports of the hardwired runtime: zero on the sponge ports, `dR c` on
the read port `c` and `dP c` on the program port `c`. -/
def hwCost {D : Type} [Fintype D] (dR : HwRead X Z M → Matrix (Unit × D) (Unit × D) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × D) (Unit × D) ℂ → ℝ≥0∞) :
    ∀ i, Matrix ((hwSpec X Z M).In i × D) ((hwSpec X Z M).In i × D) ℂ → ℝ≥0∞
  | .inl (.inl _), _ => 0
  | .inl (.inr c), σ => dR c σ
  | .inr c, σ => dP c σ

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **The graded event bound for the hardwired runtime.** Let `S` be a set of states of the
hardwired register whose slices `slice S W m` are upward closed, without the start
`(∅, W₀, m₀)`. Let a program make at most `q` sponge calls and `K` classical calls, let a fresh
cell enter `S` with probability at most `ε n` at the `n`-th sponge call, for databases below
`n + K + 1` entries, and let every read call `c` raise the weight of `S` by at most `dR c σ` and
every program call `c` by at most `dP c σ`. Then `√w ≤ ∑_{n < q} √(6 ε n) + √(∑ d)`, where
`∑ d` sums the costs of the classical calls along the run. -/
theorem rpow_inv_two_eventWeight_spongeHardwiredRuntime_le (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (hup : ∀ W m, UpClosed (slice S W m)) (W₀ : Hw X Z) (m₀ : M)
    (hempty : ((Database.empty, Database.empty, Database.empty), W₀, m₀) ∉ S) {q K : ℕ}
    (ε : ℕ → ℝ≥0∞) (hεtop : ∀ n < q, ε n ≠ ⊤)
    (hε : ∀ n < q, ∀ W m, FreshBound (slice S W m) (n + K + 1) (ε n))
    (dR : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (hdR : ∀ c σ, σ.PosSemidef → ∑' r, QuantumRuntime.potential (hwProjector S)
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ QuantumRuntime.potential (hwProjector S) σ + dR c σ)
    (hdP : ∀ c σ, σ.PosSemidef → ∑' r, QuantumRuntime.potential (hwProjector S)
      (MatrixMap.conj (hwProgKraus c r) σ) ≤ QuantumRuntime.potential (hwProjector S) σ + dP c σ)
    (I : L.Interp) (x : QuantumComp L (hwSpec X Z M) W A)
    (hxq : IPFunctor.IFreeM.IsChargeBound x (portCharge fun i ↦ if hwCls i then 0 else 1) q)
    (hxK : IPFunctor.IFreeM.IsChargeBound x (portCharge fun i ↦ if hwCls i then 1 else 0) K)
    (ρ : SubState A) :
    (spongeHardwiredRuntime X Z W₀ m₀).eventWeight I (hwProjector S) x
        (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix) ^ (2⁻¹ : ℝ) ≤
      ∑ n ∈ Finset.range q, (6 * ε n) ^ (2⁻¹ : ℝ) +
        (spongeHardwiredRuntime X Z W₀ m₀).totalWeight I (hwCost dR dP) x
          (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix) ^ (2⁻¹ : ℝ) := by
  have hρ0 : (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).PosSemidef :=
    (ρ.prod (spongeHardwiredRuntime X Z W₀ m₀).init).posSemidef
  have htr : ENNReal.ofReal
      (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).trace.re ≤ 1 := by
    rw [← SubState.matrix_prod]
    exact ENNReal.ofReal_le_one.mpr (ρ.prod (spongeHardwiredRuntime X Z W₀ m₀).init).trace_re_le_one
  have hz : hwProjector S * (SubState.basis (((Database.empty, Database.empty, Database.empty),
      W₀, m₀) : HwReg X Z M)).matrix = 0 := by
    rw [hwProjector, labelProjector, SubState.matrix_basis]
    ext a b
    rw [diagonal_mul, Matrix.single_apply, Matrix.zero_apply]
    by_cases h : ((Database.empty, Database.empty, Database.empty), W₀, m₀) = a ∧
        ((Database.empty, Database.empty, Database.empty), W₀, m₀) = b
    · rcases h with ⟨rfl, rfl⟩
      simp [hempty]
    · simp [h]
  have hzero : QuantumRuntime.potential (hwProjector S)
      (ρ.matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
        W₀, m₀) : HwReg X Z M)).matrix) = 0 := by
    rw [QuantumRuntime.potential, MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply,
      ← mul_kronecker_mul, hz, kronecker_zero, Matrix.zero_mul, Matrix.trace_zero,
      Complex.zero_re, ENNReal.ofReal_zero]
  have hgrade : QuerySupportedOn (fun m : A × HwReg X Z M ↦ dbGrade m.2.1) (Set.Iic 0)
      (ρ.matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
        W₀, m₀) : HwReg X Z M)).matrix) := by
    intro m m' hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
    · exact False.elim (h rfl)
  have h := rpow_inv_two_eventWeight_le_mixed (spongeHardwiredRuntime X Z W₀ m₀) I
    (hwProjector S) hwCls
    (fun s : HwReg X Z M ↦ dbGrade s.1)
    (fun i r t σ hσ ↦ querySupportedOn_spongeHardwiredRuntime_step W₀ m₀ i r t σ hσ)
    (fun n ↦ 6 * ε n) (hwCost dR dP) q K (fun n hn i hi σ hσ hσg ↦ ?_) (fun i hi σ hσ ↦ ?_) x hxq
    hxK hρ0 hgrade
  · refine h.trans (add_le_add (Finset.sum_le_sum fun n _ ↦ ?_)
      (le_of_eq (congrArg (· ^ (2⁻¹ : ℝ)) ((congrArg (· + _) hzero).trans (zero_add _)))))
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc 6 * ε n * ENNReal.ofReal
          (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).trace.re ≤ 6 * ε n * 1 := by
          gcongr
      _ = 6 * ε n := mul_one _
  · rcases i with (p | c) | c
    · have hs : ∑' r : Unit, QuantumRuntime.potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inl p))).branch r σ) =
          QuantumRuntime.potential (hwProjector S)
            (MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U p) σ) := by
        rw [tsum_fintype, Fintype.sum_unique, spongeHardwiredRuntime_step_sponge]
        rfl
      exact (congrArg (· ^ (2⁻¹ : ℝ)) hs).trans_le
        (rpow_inv_two_potential_spongeHardwired_le S hup (hεtop n hn) (hε n hn) W₀ m₀ p hσ hσg)
    · exact absurd hi (by simp [hwCls])
    · exact absurd hi (by simp [hwCls])
  · rcases i with (p | c) | c
    · exact absurd hi (by simp [hwCls])
    · have hs : ∑' r : c.Result, QuantumRuntime.potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inr c))).branch r σ) =
          ∑' r : c.Result, QuantumRuntime.potential (hwProjector S)
            (MatrixMap.conj (hwReadKraus c r) σ) :=
        tsum_congr fun r ↦ by rw [spongeHardwiredRuntime_step_read]; rfl
      exact hs.trans_le (hdR c σ hσ)
    · have hs : ∑' r : c.Result, QuantumRuntime.potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inr c)).branch r σ) =
          ∑' r : c.Result, QuantumRuntime.potential (hwProjector S)
            (MatrixMap.conj (hwProgKraus c r) σ) :=
        tsum_congr fun r ↦ by rw [spongeHardwiredRuntime_step_prog]; rfl
      exact hs.trans_le (hdP c σ hσ)

/-- **The graded event bound**, squared: the final weight of `S` is at most
`(∑_{n < q} √(6 ε n) + √(∑ d))²`. -/
theorem eventWeight_spongeHardwiredRuntime_le (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (hup : ∀ W m, UpClosed (slice S W m)) (W₀ : Hw X Z) (m₀ : M)
    (hempty : ((Database.empty, Database.empty, Database.empty), W₀, m₀) ∉ S) {q K : ℕ}
    (ε : ℕ → ℝ≥0∞) (hεtop : ∀ n < q, ε n ≠ ⊤)
    (hε : ∀ n < q, ∀ W m, FreshBound (slice S W m) (n + K + 1) (ε n))
    (dR : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (hdR : ∀ c σ, σ.PosSemidef → ∑' r, QuantumRuntime.potential (hwProjector S)
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ QuantumRuntime.potential (hwProjector S) σ + dR c σ)
    (hdP : ∀ c σ, σ.PosSemidef → ∑' r, QuantumRuntime.potential (hwProjector S)
      (MatrixMap.conj (hwProgKraus c r) σ) ≤ QuantumRuntime.potential (hwProjector S) σ + dP c σ)
    (I : L.Interp) (x : QuantumComp L (hwSpec X Z M) W A)
    (hxq : IPFunctor.IFreeM.IsChargeBound x (portCharge fun i ↦ if hwCls i then 0 else 1) q)
    (hxK : IPFunctor.IFreeM.IsChargeBound x (portCharge fun i ↦ if hwCls i then 1 else 0) K)
    (ρ : SubState A) :
    (spongeHardwiredRuntime X Z W₀ m₀).eventWeight I (hwProjector S) x
        (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix) ≤
      (∑ n ∈ Finset.range q, (6 * ε n) ^ (2⁻¹ : ℝ) +
        (spongeHardwiredRuntime X Z W₀ m₀).totalWeight I (hwCost dR dP) x
          (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := ENNReal.rpow_le_rpow (rpow_inv_two_eventWeight_spongeHardwiredRuntime_le S hup W₀ m₀
    hempty ε hεtop hε dR dP hdR hdP I x hxq hxK ρ) (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

end Quantum.Sponge

end
