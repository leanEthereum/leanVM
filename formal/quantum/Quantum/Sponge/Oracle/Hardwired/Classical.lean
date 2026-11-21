module

public import Quantum.Sponge.Oracle.Hardwired.Average
public import Quantum.Sponge.Oracle.Hardwired.Read

@[expose] public section

/-!
# The read ports are classical reads of consistent functions

Against fixed functions `t` and hardwired cells `W`, a classical read of a cell returns the value
of `overwrite W t` there. `spongeFnReadRuntime t W₀ m₀` runs the sponge ports as the oracles of
`overwrite W t` and the read ports as these classical reads, with the same memory updates, on the
classical register `(W, m)` started at `(W₀, m₀)`. Runtime 1 (`spongeHardwiredReadRuntime`),
whose read ports measure a cell of the compressed databases in the decompressed basis, has the
law of the average over uniform `t` of these runs (`read_port_eq_classical_read`).

The proof extends that of `evalDistMap_hardwired_eq_avg`. Tabulating the functions and compressing
every cell intertwines runtime 1 with the purified runtime `hwPurRuntime`, which holds `t` in
superposition next to `(W, m)`: on the sponge ports as before, and on the read ports because the
read of a cell in the decompressed basis, conjugated by the compression, is the projector on the
value of the cell (`cellRead_mul_tabulate`). The rows of `t` intertwine the purified runtime with
the runs against `t`.
-/

open MeasureTheory Matrix
open scoped Kronecker ENNReal NNReal

universe u v w

namespace Quantum.Sponge

open Quantum

/-! ## Classical maps -/

section clsMap

variable {B : Type} [Fintype B] [DecidableEq B]

/-- The partial classical map that sends `b` with `p b` to `φ b` and annihilates the others. -/
def clsMap (p : B → Prop) [DecidablePred p] (φ : B → B) : Matrix B B ℂ :=
  Matrix.of fun b' b ↦ if p b ∧ b' = φ b then 1 else 0

/-- **Completeness of a family of classical maps.** If every `φ r` is injective on `p r` and every
state is accepted by exactly one `p r`, the classical maps form a complete family. -/
theorem sum_clsMap {ι : Type} [Fintype ι] (p : ι → B → Prop) [∀ r, DecidablePred (p r)]
    (φ : ι → B → B) (hφ : ∀ r b b', p r b → p r b' → φ r b = φ r b' → b = b')
    (hp : ∀ b, ∃! r, p r b) :
    ∑ r, ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsMap (p r) (φ r))ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsMap (p r) (φ r)) = 1 := by
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  rw [sum_kronecker_right]
  convert one_kronecker_one (α := ℂ) (m := Unit) (n := B) using 2
  ext b b''
  rw [Matrix.sum_apply]
  have hterm : ∀ r, ((clsMap (p r) (φ r))ᴴ * clsMap (p r) (φ r)) b b'' =
      if p r b ∧ b = b'' then 1 else 0 := fun r ↦ by
    simp only [Matrix.mul_apply, conjTranspose_apply, clsMap, of_apply]
    by_cases hb : p r b
    · rw [Finset.sum_eq_single (φ r b) (fun b' _ hb' ↦ by simp [hb']) (by simp)]
      by_cases h : p r b'' ∧ φ r b = φ r b''
      · obtain rfl := hφ r b b'' hb h.1 h.2
        simp [hb]
      · have hbb : b ≠ b'' := fun e ↦ h (e ▸ ⟨hb, rfl⟩)
        simp only [hb, true_and, ↓reduceIte, star_one, one_mul, h, hbb]
    · simp [hb]
  simp only [hterm]
  obtain ⟨r₀, hr₀, huniq⟩ := hp b
  rw [Finset.sum_eq_single r₀ (fun r _ hr ↦ by
    have : ¬ (p r b ∧ b = b'') := fun h ↦ hr (huniq r h.1)
    simp [this]) (by simp)]
  by_cases hb : b = b''
  · subst hb
    simp [hr₀]
  · simp [hb, Matrix.one_apply_ne hb]

/-- A classical Kraus operator next to an isometry `V₀`, intertwined with a classical map: if every
block `R b` sends `V₀` to `V₀` times the projector `g b`, then the classical Kraus operator of
`(p, φ, R)` intertwines `V₀ ⊗ 1` with the classical map of `p b ∧ g b t` and `(t, b) ↦ (t, φ b)`. -/
theorem clsKraus_mul_kronecker_one {T T' : Type} [Fintype T] [DecidableEq T] [Fintype T']
    [DecidableEq T'] (p : B → Prop) [DecidablePred p] (φ : B → B) (R : B → Matrix T T ℂ)
    (V₀ : Matrix T T' ℂ) (g : B → T' → Prop) [∀ b, DecidablePred (g b)]
    (hR : ∀ b, R b * V₀ = V₀ * diagonal fun t ↦ if g b t then (1 : ℂ) else 0) :
    clsKraus p φ R * (V₀ ⊗ₖ (1 : Matrix B B ℂ)) =
      (V₀ ⊗ₖ (1 : Matrix B B ℂ)) *
        clsMap (fun q : T' × B ↦ p q.2 ∧ g q.2 q.1) (fun q ↦ (q.1, φ q.2)) := by
  ext ⟨s', b'⟩ ⟨t, b⟩
  have hRb := congrFun (congrFun (hR b) s') t
  rw [Matrix.mul_apply, mul_diagonal] at hRb
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hL : ∀ s₁, ∑ b₁, clsKraus p φ R (s', b') (s₁, b₁) *
      (V₀ ⊗ₖ (1 : Matrix B B ℂ)) (s₁, b₁) (t, b) =
      if p b ∧ b' = φ b then R b s' s₁ * V₀ s₁ t else 0 := fun s₁ ↦ by
    rw [Finset.sum_eq_single b (fun b₁ _ hb₁ ↦ by
      simp [kroneckerMap_apply, Matrix.one_apply_ne hb₁]) (by simp)]
    simp only [clsKraus_apply, kroneckerMap_apply, Matrix.one_apply_eq, mul_one]
    split_ifs <;> simp
  have hR' : ∀ t₁, ∑ b₁, (V₀ ⊗ₖ (1 : Matrix B B ℂ)) (s', b') (t₁, b₁) *
      clsMap (fun q : T' × B ↦ p q.2 ∧ g q.2 q.1) (fun q ↦ (q.1, φ q.2)) (t₁, b₁) (t, b) =
      if t₁ = t ∧ p b ∧ g b t ∧ b' = φ b then V₀ s' t else 0 := fun t₁ ↦ by
    rw [Finset.sum_eq_single b' (fun b₁ _ hb₁ ↦ by
      simp [kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hb₁)]) (by simp)]
    simp only [clsMap, of_apply, kroneckerMap_apply, Matrix.one_apply_eq, mul_one,
      Prod.mk.injEq]
    by_cases h : p b ∧ g b t ∧ t₁ = t ∧ b' = φ b
    · obtain ⟨h₁, h₂, rfl, h₄⟩ := h
      simp [h₁, h₂, h₄]
    · have h' : ¬ (t₁ = t ∧ p b ∧ g b t ∧ b' = φ b) := fun h' ↦
        h ⟨h'.2.1, h'.2.2.1, h'.1, h'.2.2.2⟩
      simp only [h', ↓reduceIte, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
      intro h''
      exact (h (by tauto)).elim
  simp only [hL, hR']
  rw [Finset.sum_eq_single t (fun t₁ _ ht₁ ↦ by simp [ht₁]) (by simp)]
  by_cases hc : p b ∧ b' = φ b
  · have e : ∀ s₁, (if p b ∧ b' = φ b then R b s' s₁ * V₀ s₁ t else 0) =
        R b s' s₁ * V₀ s₁ t := fun s₁ ↦ by simp [hc]
    rw [Finset.sum_congr rfl fun s₁ _ ↦ e s₁, hRb]
    by_cases hg : g b t <;> simp [hg, hc]
  · have hc' : ¬ (t = t ∧ p b ∧ g b t ∧ b' = φ b) := fun h ↦ hc ⟨h.2.1, h.2.2.2⟩
    simp only [hc, ↓reduceIte, Finset.sum_const_zero, true_and]
    have hc'' : ¬ (p b ∧ g b t ∧ b' = φ b) := fun h ↦ hc ⟨h.1, h.2.2⟩
    simp only [hc'', ↓reduceIte]

end clsMap

/-! ## Reads of one database against tabulated functions -/

section cell

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]

omit [Fintype Y] in
/-- The projector on the databases whose cell `a` holds `o`, as a pi-tensor product. -/
theorem diagonal_cell_eq_piKron (a : A) (o : Option Y) :
    (diagonal fun D : Database A Y ↦ if D a = o then (1 : ℂ) else 0) =
      piKron (Function.update (fun _ ↦ (1 : Matrix (Option Y) (Option Y) ℂ)) a
        (diagonal fun u ↦ if u = o then 1 else 0)) := by
  ext D D'
  rw [piKron_apply, Fintype.prod_eq_mul_prod_compl a, Function.update_self]
  have hrest : ∏ x ∈ ({a}ᶜ : Finset A), Function.update
      (fun _ ↦ (1 : Matrix (Option Y) (Option Y) ℂ)) a
        (diagonal fun u ↦ if u = o then 1 else 0) x (D x) (D' x) =
      if ∀ x ∈ ({a}ᶜ : Finset A), D x = D' x then 1 else 0 := by
    by_cases h : ∀ x ∈ ({a}ᶜ : Finset A), D x = D' x
    · simp only [eq_true h, ↓reduceIte]
      refine Finset.prod_eq_one fun x hx ↦ ?_
      rw [Function.update_of_ne (by simpa using hx), h x hx, Matrix.one_apply_eq]
    · simp only [eq_false h, ↓reduceIte]
      simp only [not_forall] at h
      obtain ⟨x, hx, hne⟩ := h
      exact Finset.prod_eq_zero hx (by
        rw [Function.update_of_ne (by simpa using hx), Matrix.one_apply_ne hne])
  rw [hrest, diagonal_apply, diagonal_apply]
  by_cases hD : D = D'
  · subst hD
    simp
  · have hn : ¬ (D a = D' a ∧ ∀ x ∈ ({a}ᶜ : Finset A), D x = D' x) := fun h ↦
      hD (funext fun x ↦ by
        by_cases hx : x = a
        · exact hx ▸ h.1
        · exact h.2 x (by simpa using hx))
    simp only [hD, ↓reduceIte]
    by_cases ha : D a = D' a
    · have h2 : ¬ ∀ x ∈ ({a}ᶜ : Finset A), D x = D' x := fun h ↦ hn ⟨ha, h⟩
      simp only [eq_false h2, ↓reduceIte, mul_zero]
    · simp only [ha, ↓reduceIte, zero_mul]

variable [Nonempty Y]

/-- On the projector of one cell, compressing the cell is compressing every cell. -/
theorem compressAt_mul_diagonal_cell_mul_compressAt (a : A) (o : Option Y) :
    compressAt Y a * (diagonal fun D : Database A Y ↦ if D a = o then (1 : ℂ) else 0) *
        compressAt Y a =
      compressAll A Y * (diagonal fun D : Database A Y ↦ if D a = o then (1 : ℂ) else 0) *
        compressAll A Y := by
  rw [diagonal_cell_eq_piKron, compressAt, compressAll, piKron_mul, piKron_mul, piKron_mul,
    piKron_mul]
  congr 1
  funext x
  by_cases hx : x = a
  · subst hx
    simp
  · simp [hx, cellCompress_mul_self]

/-- **A read against tabulated functions.** Reading cell `a` in the decompressed basis with
outcome `o`, after tabulating and compressing a function `H`, projects on `o = (w a).getD (H a)`,
the value of `H` overwritten by the hardwired cells `w`. -/
theorem cellRead_mul_tabulate (w : Database A Y) (a : A) (o : Option Y) :
    cellRead w a o * (compressAll A Y * basisMatrix (Database.ofFun : (A → Y) → Database A Y)) =
      (compressAll A Y * basisMatrix (Database.ofFun : (A → Y) → Database A Y)) *
        diagonal fun H : A → Y ↦ if o = some ((w a).getD (H a)) then (1 : ℂ) else 0 := by
  rcases hw : w a with _ | v
  · have hr : cellRead w a o = compressAt Y a *
        (diagonal fun D : Database A Y ↦ if D a = o then (1 : ℂ) else 0) * compressAt Y a := by
      simp [cellRead, hw]
    have hP : (diagonal fun D : Database A Y ↦ if D a = o then (1 : ℂ) else 0) *
        basisMatrix (Database.ofFun : (A → Y) → Database A Y) =
          basisMatrix (Database.ofFun : (A → Y) → Database A Y) *
            diagonal fun H : A → Y ↦ if o = some (H a) then (1 : ℂ) else 0 := by
      ext D H
      rw [diagonal_mul, mul_diagonal, basisMatrix_apply]
      by_cases hD : D = Database.ofFun H
      · subst hD
        simp [Database.ofFun_apply, eq_comm]
      · simp [hD]
    simp only [Option.getD_none]
    set C := compressAll A Y
    set P := diagonal fun D : Database A Y ↦ if D a = o then (1 : ℂ) else 0
    set B := basisMatrix (Database.ofFun : (A → Y) → Database A Y)
    calc cellRead w a o * (C * B) = C * P * C * (C * B) := by
          rw [hr, compressAt_mul_diagonal_cell_mul_compressAt]
      _ = C * P * B := by
          rw [Matrix.mul_assoc (C * P) C (C * B), ← Matrix.mul_assoc C C B, compressAll_mul_self,
            Matrix.one_mul]
      _ = C * B * diagonal fun H : A → Y ↦ if o = some (H a) then (1 : ℂ) else 0 := by
          rw [Matrix.mul_assoc, hP, ← Matrix.mul_assoc]
  · have hr : cellRead w a o = if o = some v then 1 else 0 := by simp [cellRead, hw]
    have hd : (diagonal fun H : A → Y ↦ if o = some ((some v).getD (H a)) then (1 : ℂ) else 0) =
        if o = some v then 1 else 0 := by
      split_ifs with ho <;> simp [ho]
    rw [hd, hr]
    split_ifs
    · rw [Matrix.one_mul, Matrix.mul_one]
    · rw [Matrix.zero_mul, Matrix.mul_zero]

end cell

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z]

/-! ## Reads of the three databases -/

theorem tabulateDbs_eq_kronecker :
    tabulateDbs X Z = (compressAll Z X * basisMatrix Database.ofFun) ⊗ₖ
      ((compressAll X Z * basisMatrix Database.ofFun) ⊗ₖ
        (compressAll X Z * basisMatrix Database.ofFun)) := by
  rw [tabulateDbs, compressDbs, basisMatrix_ofFunDbs, ← mul_kronecker_mul, ← mul_kronecker_mul]

/-- The read of a cell of `h` against the tabulated functions. -/
theorem cellReadH_mul_tabulateDbs (W : Hw X Z) (z : Z) (o : Option X) :
    (cellRead W.1 z o ⊗ₖ (1 : Matrix (Database X Z × Database X Z) _ ℂ)) * tabulateDbs X Z =
      tabulateDbs X Z * diagonal fun t ↦ if o = some ((overwrite W t).1 z) then (1 : ℂ) else 0 := by
  have hd : (diagonal fun t : (Z → X) × (X → Z) × (X → Z) ↦
      if o = some ((overwrite W t).1 z) then (1 : ℂ) else 0) =
      (diagonal fun H : Z → X ↦ if o = some ((W.1 z).getD (H z)) then (1 : ℂ) else 0) ⊗ₖ
        (1 : Matrix ((X → Z) × (X → Z)) ((X → Z) × (X → Z)) ℂ) := by
    rw [← diagonal_one, diagonal_kronecker_diagonal]
    congr 1
    funext t
    simp only [overwrite, mul_one]
    by_cases ho : o = some ((W.1 z).getD (t.1 z)) <;> simp [ho]
  rw [hd, tabulateDbs_eq_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
    cellRead_mul_tabulate, Matrix.one_mul, Matrix.mul_one]

/-- The read of a cell of `k` against the tabulated functions. -/
theorem cellReadK_mul_tabulateDbs (W : Hw X Z) (x : X) (o : Option Z) :
    ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        (cellRead W.2.1 x o ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))) * tabulateDbs X Z =
      tabulateDbs X Z * diagonal fun t ↦
        if o = some ((overwrite W t).2.1 x) then (1 : ℂ) else 0 := by
  have hd : (diagonal fun t : (Z → X) × (X → Z) × (X → Z) ↦
      if o = some ((overwrite W t).2.1 x) then (1 : ℂ) else 0) =
      (1 : Matrix (Z → X) (Z → X) ℂ) ⊗ₖ
        ((diagonal fun H : X → Z ↦ if o = some ((W.2.1 x).getD (H x)) then (1 : ℂ) else 0) ⊗ₖ
          (1 : Matrix (X → Z) (X → Z) ℂ)) := by
    rw [← diagonal_one, ← diagonal_one, diagonal_kronecker_diagonal, diagonal_kronecker_diagonal]
    congr 1
    funext t
    simp only [overwrite, mul_one, one_mul]
    by_cases ho : o = some ((W.2.1 x).getD (t.2.1 x)) <;> simp [ho]
  rw [hd, tabulateDbs_eq_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
    ← mul_kronecker_mul, ← mul_kronecker_mul, cellRead_mul_tabulate, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

/-- The read of a cell of `k'` against the tabulated functions. -/
theorem cellReadK'_mul_tabulateDbs (W : Hw X Z) (x : X) (o : Option Z) :
    ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead W.2.2 x o)) * tabulateDbs X Z =
      tabulateDbs X Z * diagonal fun t ↦
        if o = some ((overwrite W t).2.2 x) then (1 : ℂ) else 0 := by
  have hd : (diagonal fun t : (Z → X) × (X → Z) × (X → Z) ↦
      if o = some ((overwrite W t).2.2 x) then (1 : ℂ) else 0) =
      (1 : Matrix (Z → X) (Z → X) ℂ) ⊗ₖ ((1 : Matrix (X → Z) (X → Z) ℂ) ⊗ₖ
        (diagonal fun H : X → Z ↦ if o = some ((W.2.2 x).getD (H x)) then (1 : ℂ) else 0)) := by
    rw [← diagonal_one, ← diagonal_one, diagonal_kronecker_diagonal, diagonal_kronecker_diagonal]
    congr 1
    funext t
    simp only [overwrite, one_mul]
    by_cases ho : o = some ((W.2.2 x).getD (t.2.2 x)) <;> simp [ho]
  rw [hd, tabulateDbs_eq_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
    ← mul_kronecker_mul, ← mul_kronecker_mul, cellRead_mul_tabulate, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

/-! ## Rows of the function register -/

section rows

variable {T B : Type} [Fintype T] [DecidableEq T] [Fintype B] [DecidableEq B]

/-- Reading the function register at `t` intertwines a classical map on `T × B` that keeps `T`
with its restriction to `t`. -/
theorem clsMap_mul_rowAt (t : T) (p : T × B → Prop) [DecidablePred p] (φ : B → B) :
    clsMap (fun u : Unit × B ↦ p (t, u.2)) (fun u ↦ (u.1, φ u.2)) *
        (rowAt t ⊗ₖ (1 : Matrix B B ℂ)) =
      (rowAt t ⊗ₖ (1 : Matrix B B ℂ)) * clsMap p (fun q ↦ (q.1, φ q.2)) := by
  ext ⟨u', b'⟩ ⟨t', b⟩
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single ((), b) ?_ (by simp),
    Finset.sum_eq_single (t, b') ?_ (by simp)]
  · by_cases ht : t' = t
    · subst ht
      by_cases hc : p (t', b) ∧ b' = φ b <;>
        simp [clsMap, rowAt, kroneckerMap_apply, hc, Prod.ext_iff]
    · simp [clsMap, rowAt, kroneckerMap_apply, ht, Ne.symm ht, Prod.ext_iff]
  · rintro ⟨t'', b''⟩ - hne
    simp only [kroneckerMap_apply, rowAt, of_apply, Matrix.one_apply]
    by_cases h : t'' = t ∧ b' = b''
    · obtain ⟨rfl, rfl⟩ := h
      exact absurd rfl hne
    · by_cases ht : t'' = t
      · have hb : ¬ b' = b'' := fun hb ↦ h ⟨ht, hb⟩
        simp [ht, hb]
      · simp [ht]
  · rintro ⟨u, b''⟩ - hne
    have hb : b'' ≠ b := fun h ↦ hne (by rw [h])
    simp [kroneckerMap_apply, Matrix.one_apply_ne hb]

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

omit [Fintype T] [Fintype B] in
/-- Reading the function register at `t` is the adjoint of inserting `t`. -/
theorem rowAt_kronecker_one_eq (t : T) :
    rowAt t ⊗ₖ (1 : Matrix B B ℂ) = (basisMatrix fun u : Unit × B ↦ (t, u.2))ᴴ := by
  ext ⟨u, b⟩ ⟨t', b'⟩
  by_cases ht : t' = t <;> by_cases hb : b = b' <;>
    simp [rowAt, kroneckerMap_apply, conjTranspose_apply, basisMatrix_apply, ht, hb, Prod.ext_iff,
      eq_comm]

/-- Reading the function register at `t` intertwines a table oracle on `T × B` with its restriction
to `t`. -/
theorem tableOracle_mul_rowAt (read : T × B → A → Y) (t : T) :
    tableOracle (fun u : Unit × B ↦ read (t, u.2)) *
        ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (rowAt t ⊗ₖ (1 : Matrix B B ℂ))) =
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (rowAt t ⊗ₖ (1 : Matrix B B ℂ))) *
        tableOracle read := by
  set g : Unit × B → T × B := fun u ↦ (t, u.2)
  set G := (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ basisMatrix g
  set T₁ := tableOracle read
  set T₂ := tableOracle fun u : Unit × B ↦ read (t, u.2)
  have hG : (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ (rowAt t ⊗ₖ (1 : Matrix B B ℂ)) = Gᴴ := by
    rw [rowAt_kronecker_one_eq, conjTranspose_kronecker, conjTranspose_one]
  have hT : T₁ * G = G * T₂ := tableOracle_mul_one_kronecker_basisMatrix fun _ ↦ rfl
  have hu₂ : T₂ * T₂ᴴ = 1 := mem_unitaryGroup_iff.mp
    (mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _))
  rw [hG]
  calc T₂ * Gᴴ = T₂ * Gᴴ * (T₁ᴴ * T₁) := by
        rw [conjTranspose_tableOracle_mul_self, Matrix.mul_one]
    _ = T₂ * (Gᴴ * T₁ᴴ) * T₁ := by simp only [Matrix.mul_assoc]
    _ = T₂ * (T₂ᴴ * Gᴴ) * T₁ := by rw [← conjTranspose_mul, ← conjTranspose_mul, hT]
    _ = Gᴴ * T₁ := by rw [← Matrix.mul_assoc, hu₂, Matrix.one_mul]

end rows

/-! ## The purified runtime with reads -/

variable (X Z M) in
/-- The functions next to the classical data. -/
abbrev FnReg := ((Z → X) × (X → Z) × (X → Z)) × Hw X Z × M

/-- Decidable equality of the function register, named so that instance search stays small. -/
instance (priority := high) FnReg.instDecidableEq : DecidableEq (FnReg X Z M) :=
  inferInstanceAs (DecidableEq (((Z → X) × (X → Z) × (X → Z)) × DbReg X Z × M))

/-- The function register is finite. -/
instance (priority := high) FnReg.instFintype : Fintype (FnReg X Z M) :=
  inferInstanceAs (Fintype (((Z → X) × (X → Z) × (X → Z)) × DbReg X Z × M))

/-- The Kraus operators of a read against the functions held in the register: the read returns
the value of `overwrite W t` at the cell. -/
noncomputable def purReadKraus : (c : HwRead X Z M) → c.Result →
    Matrix (Unit × FnReg X Z M) (Unit × FnReg X Z M) ℂ
  | .readH z upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ
      clsMap (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).1 z))
        (fun q ↦ (q.1, q.2.1, upd r.2 r.1))
  | .readK x upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ
      clsMap (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).2.1 x))
        (fun q ↦ (q.1, q.2.1, upd r.2 r.1))
  | .readK' x upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ
      clsMap (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).2.2 x))
        (fun q ↦ (q.1, q.2.1, upd r.2 r.1))

/-- The Kraus operators of a read against the fixed functions `t`. -/
noncomputable def fnReadKraus (t : (Z → X) × (X → Z) × (X → Z)) : (c : HwRead X Z M) → c.Result →
    Matrix (Unit × (Unit × Hw X Z × M)) (Unit × (Unit × Hw X Z × M)) ℂ
  | .readH z upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ
      clsMap (fun u : Unit × Hw X Z × M ↦ u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).1 z))
        (fun u ↦ (u.1, u.2.1, upd r.2 r.1))
  | .readK x upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ
      clsMap (fun u : Unit × Hw X Z × M ↦ u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).2.1 x))
        (fun u ↦ (u.1, u.2.1, upd r.2 r.1))
  | .readK' x upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ
      clsMap (fun u : Unit × Hw X Z × M ↦ u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).2.2 x))
        (fun u ↦ (u.1, u.2.1, upd r.2 r.1))

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The reads against the functions in the register form complete families. -/
theorem sum_purReadKraus (c : HwRead X Z M) :
    ∑ r, (purReadKraus c r)ᴴ * purReadKraus c r = 1 := by
  cases c with
  | readH z upd =>
    refine sum_clsMap _ _ (fun r q q' hq hq' he ↦ ?_) fun q ↦
      ⟨(some ((overwrite q.2.1 q.1).1 z), q.2.2), ⟨rfl, rfl⟩, fun r hr ↦ ?_⟩
    · obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
      exact Prod.ext h₁ (Prod.ext (Prod.mk.inj h₂).1 (hq.1.trans hq'.1.symm))
    · exact Prod.ext hr.2 hr.1.symm
  | readK x upd =>
    refine sum_clsMap _ _ (fun r q q' hq hq' he ↦ ?_) fun q ↦
      ⟨(some ((overwrite q.2.1 q.1).2.1 x), q.2.2), ⟨rfl, rfl⟩, fun r hr ↦ ?_⟩
    · obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
      exact Prod.ext h₁ (Prod.ext (Prod.mk.inj h₂).1 (hq.1.trans hq'.1.symm))
    · exact Prod.ext hr.2 hr.1.symm
  | readK' x upd =>
    refine sum_clsMap _ _ (fun r q q' hq hq' he ↦ ?_) fun q ↦
      ⟨(some ((overwrite q.2.1 q.1).2.2 x), q.2.2), ⟨rfl, rfl⟩, fun r hr ↦ ?_⟩
    · obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
      exact Prod.ext h₁ (Prod.ext (Prod.mk.inj h₂).1 (hq.1.trans hq'.1.symm))
    · exact Prod.ext hr.2 hr.1.symm

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The reads against fixed functions form complete families. -/
theorem sum_fnReadKraus (t : (Z → X) × (X → Z) × (X → Z)) (c : HwRead X Z M) :
    ∑ r, (fnReadKraus t c r)ᴴ * fnReadKraus t c r = 1 := by
  cases c with
  | readH z upd =>
    refine sum_clsMap _ _ (fun r q q' hq hq' he ↦ ?_) fun q ↦
      ⟨(some ((overwrite q.2.1 t).1 z), q.2.2), ⟨rfl, rfl⟩, fun r hr ↦ ?_⟩
    · obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
      exact Prod.ext h₁ (Prod.ext (Prod.mk.inj h₂).1 (hq.1.trans hq'.1.symm))
    · exact Prod.ext hr.2 hr.1.symm
  | readK x upd =>
    refine sum_clsMap _ _ (fun r q q' hq hq' he ↦ ?_) fun q ↦
      ⟨(some ((overwrite q.2.1 t).2.1 x), q.2.2), ⟨rfl, rfl⟩, fun r hr ↦ ?_⟩
    · obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
      exact Prod.ext h₁ (Prod.ext (Prod.mk.inj h₂).1 (hq.1.trans hq'.1.symm))
    · exact Prod.ext hr.2 hr.1.symm
  | readK' x upd =>
    refine sum_clsMap _ _ (fun r q q' hq hq' he ↦ ?_) fun q ↦
      ⟨(some ((overwrite q.2.1 t).2.2 x), q.2.2), ⟨rfl, rfl⟩, fun r hr ↦ ?_⟩
    · obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
      exact Prod.ext h₁ (Prod.ext (Prod.mk.inj h₂).1 (hq.1.trans hq'.1.symm))
    · exact Prod.ext hr.2 hr.1.symm

variable (X Z) in
/-- The purified oracle of the overwritten functions, next to the classical data started at
`(W₀, m₀)`: port `i` reads the functions overwritten by the hardwired cells in the register. -/
@[reducible]
noncomputable def hwPurified (W₀ : Hw X Z) (m₀ : M) :
    EmulatedOracle SpongePort (spongeIn X Z) where
  S := QReg.of (FnReg X Z M)
  init := (spongePurified X Z).init.prod (SubState.basis (W₀, m₀))
  U
    | .h => tableOracle fun q : FnReg X Z M ↦ (overwrite q.2.1 q.1).1
    | .k => tableOracle fun q : FnReg X Z M ↦ (overwrite q.2.1 q.1).2.1
    | .k' => tableOracle fun q : FnReg X Z M ↦ (overwrite q.2.1 q.1).2.2
  unitary
    | .h => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)
    | .k => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)
    | .k' => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)

variable (X Z) in
/-- The purified runtime with reads. -/
noncomputable def hwPurRuntime (W₀ : Hw X Z) (m₀ : M) : QuantumRuntime (hwReadSpec X Z M) :=
  ((hwPurified X Z W₀ m₀).toRuntime : QuantumRuntime (spongeSpec X Z)).extend
    (t := hwReadCmdSpec X Z M) fun c ↦ SubInstrument.ofKraus (purReadKraus c) (sum_purReadKraus c)

variable (X Z) in
/-- The oracles of the functions `overwrite W t`, with `W` read off the classical register
started at `(W₀, m₀)`. -/
@[reducible]
noncomputable def spongeFnHw (t : (Z → X) × (X → Z) × (X → Z)) (W₀ : Hw X Z) (m₀ : M) :
    EmulatedOracle SpongePort (spongeIn X Z) where
  S := QReg.of (Unit × Hw X Z × M)
  init := SubState.basis ((), W₀, m₀)
  U
    | .h => tableOracle fun u : Unit × Hw X Z × M ↦ (overwrite u.2.1 t).1
    | .k => tableOracle fun u : Unit × Hw X Z × M ↦ (overwrite u.2.1 t).2.1
    | .k' => tableOracle fun u : Unit × Hw X Z × M ↦ (overwrite u.2.1 t).2.2
  unitary
    | .h => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)
    | .k => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)
    | .k' => mem_unitaryGroup_iff'.mpr (conjTranspose_tableOracle_mul_self _)

variable (X Z) in
/-- **Classical reads against fixed functions.** The sponge ports answer with the oracles of
`overwrite W t`, and the read ports return the value of `overwrite W t` at the cell, updating the
memory as runtime 1 does; `W` and the memory live in the classical register started at
`(W₀, m₀)`. -/
noncomputable def spongeFnReadRuntime (t : (Z → X) × (X → Z) × (X → Z)) (W₀ : Hw X Z) (m₀ : M) :
    QuantumRuntime (hwReadSpec X Z M) :=
  ((spongeFnHw X Z t W₀ m₀).toRuntime : QuantumRuntime (spongeSpec X Z)).extend
    (t := hwReadCmdSpec X Z M) fun c ↦
      SubInstrument.ofKraus (fnReadKraus t c) (sum_fnReadKraus t c)

/-! ## Tabulation intertwines runtime 1 with the purified runtime -/

variable (X Z M) in
/-- Tabulating and compressing the functions, next to the classical data. -/
noncomputable def tabReg : Matrix (HwReg X Z M) (FnReg X Z M) ℂ :=
  tabulateDbs X Z ⊗ₖ (1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ)

theorem tabReg_eq : tabReg X Z M =
    compressReg X Z M * basisMatrix fun q : FnReg X Z M ↦ (ofFunDbs q.1, q.2) := by
  have hb : (basisMatrix fun q : FnReg X Z M ↦ (ofFunDbs q.1, q.2)) =
      basisMatrix ofFunDbs ⊗ₖ (1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ) := by
    ext ⟨D, b⟩ ⟨t, b'⟩
    by_cases hb : b = b' <;> simp [kroneckerMap_apply, basisMatrix_apply, hb]
  rw [tabReg, tabulateDbs, compressReg, hb, ← mul_kronecker_mul, Matrix.mul_one]

theorem conjTranspose_tabReg_mul_self : (tabReg X Z M)ᴴ * tabReg X Z M = 1 := by
  rw [tabReg, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    conjTranspose_tabulateDbs_mul_self, Matrix.one_mul, one_kronecker_one]

theorem conj_tabReg_init (W₀ : Hw X Z) (m₀ : M) :
    MatrixMap.conj (tabReg X Z M) (hwPurified X Z W₀ m₀).init.matrix =
      (spongeHardwired X Z W₀ m₀).init.matrix := by
  change MatrixMap.conj (tabulateDbs X Z ⊗ₖ (1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ))
      ((spongePurified X Z).init.matrix ⊗ₖ (SubState.basis (W₀, m₀)).matrix) =
    (SubState.basis (((Database.empty, Database.empty, Database.empty) : DbReg X Z), W₀,
      m₀)).matrix
  rw [conj_kronecker_kronecker, conj_tabulateDbs_init, MatrixMap.conj_apply, Matrix.one_mul,
    conjTranspose_one, Matrix.mul_one, ← SubState.matrix_prod, SubState.basis_prod_basis]

theorem spongeHardwired_U_mul_tabReg (W₀ : Hw X Z) (m₀ : M) (i : SpongePort) :
    (spongeHardwired X Z W₀ m₀).U i * (1 ⊗ₖ tabReg X Z M) =
      (1 ⊗ₖ tabReg X Z M) * (hwPurified X Z W₀ m₀).U i := by
  rw [tabReg_eq]
  cases i
  · exact conj_tableOracle_mul_one_kronecker
      (fun s : HwReg X Z M ↦ fun z ↦ (s.2.1.1 z).getD (s.1.1.lookup z))
      (fun q : FnReg X Z M ↦ (overwrite q.2.1 q.1).1) (compressReg X Z M) compressReg_mul_self
      (fun q : FnReg X Z M ↦ (ofFunDbs q.1, q.2)) fun q ↦ funext fun z ↦ by
        change (q.2.1.1 z).getD ((Database.ofFun q.1.1).lookup z) = (q.2.1.1 z).getD (q.1.1 z)
        rw [Database.lookup_ofFun]
  · exact conj_tableOracle_mul_one_kronecker
      (fun s : HwReg X Z M ↦ fun x ↦ (s.2.1.2.1 x).getD (s.1.2.1.lookup x))
      (fun q : FnReg X Z M ↦ (overwrite q.2.1 q.1).2.1) (compressReg X Z M) compressReg_mul_self
      (fun q : FnReg X Z M ↦ (ofFunDbs q.1, q.2)) fun q ↦ funext fun x ↦ by
        change (q.2.1.2.1 x).getD ((Database.ofFun q.1.2.1).lookup x) =
          (q.2.1.2.1 x).getD (q.1.2.1 x)
        rw [Database.lookup_ofFun]
  · exact conj_tableOracle_mul_one_kronecker
      (fun s : HwReg X Z M ↦ fun x ↦ (s.2.1.2.2 x).getD (s.1.2.2.lookup x))
      (fun q : FnReg X Z M ↦ (overwrite q.2.1 q.1).2.2) (compressReg X Z M) compressReg_mul_self
      (fun q : FnReg X Z M ↦ (ofFunDbs q.1, q.2)) fun q ↦ funext fun x ↦ by
        change (q.2.1.2.2 x).getD ((Database.ofFun q.1.2.2).lookup x) =
          (q.2.1.2.2 x).getD (q.1.2.2 x)
        rw [Database.lookup_ofFun]

theorem hwReadKraus_mul_tabReg (c : HwRead X Z M) (r : c.Result) :
    hwReadKraus c r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ tabReg X Z M) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ tabReg X Z M) * purReadKraus c r := by
  cases c with
  | readH z upd =>
    have key := clsKraus_mul_kronecker_one (fun b : Hw X Z × M ↦ b.2 = r.2)
      (fun b ↦ (b.1, upd r.2 r.1))
      (fun b ↦ cellRead b.1.1 z r.1 ⊗ₖ (1 : Matrix (Database X Z × Database X Z) _ ℂ))
      (tabulateDbs X Z) (fun b t ↦ r.1 = some ((overwrite b.1 t).1 z))
      fun b ↦ cellReadH_mul_tabulateDbs b.1 z r.1
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd r) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ tabReg X Z M) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ tabReg X Z M) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        clsMap (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).1 z))
          (fun q ↦ (q.1, q.2.1, upd r.2 r.1)))
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, tabReg]
    exact congrArg _ key
  | readK x upd =>
    have key := clsKraus_mul_kronecker_one (fun b : Hw X Z × M ↦ b.2 = r.2)
      (fun b ↦ (b.1, upd r.2 r.1))
      (fun b ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        (cellRead b.1.2.1 x r.1 ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ)))
      (tabulateDbs X Z) (fun b t ↦ r.1 = some ((overwrite b.1 t).2.1 x))
      fun b ↦ cellReadK_mul_tabulateDbs b.1 x r.1
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK x upd r) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ tabReg X Z M) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ tabReg X Z M) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        clsMap (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).2.1 x))
          (fun q ↦ (q.1, q.2.1, upd r.2 r.1)))
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, tabReg]
    exact congrArg _ key
  | readK' x upd =>
    have key := clsKraus_mul_kronecker_one (fun b : Hw X Z × M ↦ b.2 = r.2)
      (fun b ↦ (b.1, upd r.2 r.1))
      (fun b ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead b.1.2.2 x r.1))
      (tabulateDbs X Z) (fun b t ↦ r.1 = some ((overwrite b.1 t).2.2 x))
      fun b ↦ cellReadK'_mul_tabulateDbs b.1 x r.1
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK' x upd r) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ tabReg X Z M) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ tabReg X Z M) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        clsMap (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).2.2 x))
          (fun q ↦ (q.1, q.2.1, upd r.2 r.1)))
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, tabReg]
    exact congrArg _ key

/-! ## The main theorem -/

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **Runtime 1 is the purified runtime with reads.** -/
theorem evalDistMap_spongeHardwiredReadRuntime_eq_pur {γ : Type*} [MeasurableSpace γ]
    (W₀ : Hw X Z) (m₀ : M) (I : L.Interp) (x : QuantumComp L (hwReadSpec X Z M) W A)
    (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (spongeHardwiredReadRuntime X Z W₀ m₀).evalDistMap I x ρ f =
      (hwPurRuntime X Z W₀ m₀).evalDistMap I x ρ f := by
  have h : ∀ i r, ((spongeHardwiredReadRuntime X Z W₀ m₀).step i).branch r ∘ₗ
      (MatrixMap.conj (tabReg X Z M)).amplifyLeft ((hwReadSpec X Z M).In i) =
      (MatrixMap.conj (tabReg X Z M)).amplifyLeft ((hwReadSpec X Z M).Out i) ∘ₗ
        ((hwPurRuntime X Z W₀ m₀).step i).branch r := by
    rintro (i | c) r
    · change MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U i) ∘ₗ
          (MatrixMap.conj (tabReg X Z M)).amplifyLeft (spongeIn X Z i) =
        (MatrixMap.conj (tabReg X Z M)).amplifyLeft (spongeIn X Z i) ∘ₗ
          MatrixMap.conj ((hwPurified X Z W₀ m₀).U i)
      rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
        spongeHardwired_U_mul_tabReg]
    · have e₁ : ((spongeHardwiredReadRuntime X Z W₀ m₀).step (.inr c)).branch r =
          MatrixMap.conj (hwReadKraus c r) := hwReadStep_branch c r
      have e₂ : ((hwPurRuntime X Z W₀ m₀).step (.inr c)).branch r =
          MatrixMap.conj (purReadKraus c r) := rfl
      have key : MatrixMap.conj (hwReadKraus c r) ∘ₗ
          MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ tabReg X Z M) =
          MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ tabReg X Z M) ∘ₗ
            MatrixMap.conj (purReadKraus c r) := by
        rw [← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
        exact congrArg MatrixMap.conj (hwReadKraus_mul_tabReg c r)
      rw [e₁, e₂, MatrixMap.amplifyLeft_conj]
      exact key
  simp only [QuantumRuntime.evalDistMap]
  refine congrArg Measure.sum (funext fun p ↦ ?_)
  rw [QuantumRuntime.trace_jointPost_eq_of_simulation I (R₁ := hwPurRuntime X Z W₀ m₀)
    (R₂ := spongeHardwiredReadRuntime X Z W₀ m₀) h
    (MatrixMap.isTP_conj conjTranspose_tabReg_mul_self) (by exact conj_tabReg_init W₀ m₀) x ρ p]

variable (X Z M) in
/-- Reading the function register at `t`, next to the classical data. -/
def fnRow (t : (Z → X) × (X → Z) × (X → Z)) : Matrix (Unit × Hw X Z × M) (FnReg X Z M) ℂ :=
  rowAt t ⊗ₖ (1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ)

omit [AddCommGroup X] [AddCommGroup Z] in
theorem sum_conjTranspose_fnRow_mul_self :
    ∑ t, (fnRow X Z M t)ᴴ * fnRow X Z M t = 1 := by
  simp only [fnRow, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    Matrix.one_mul]
  rw [sum_kronecker_left, sum_conjTranspose_rowAt_mul_self, one_kronecker_one]

theorem conj_fnRow_init (t : (Z → X) × (X → Z) × (X → Z)) (W₀ : Hw X Z) (m₀ : M) :
    MatrixMap.conj (fnRow X Z M t) (hwPurified X Z W₀ m₀).init.matrix =
      (((Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0)⁻¹ : ℝ) : ℂ) •
        (spongeFnHw X Z t W₀ m₀).init.matrix := by
  change MatrixMap.conj (rowAt t ⊗ₖ (1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ))
      ((spongePurified X Z).init.matrix ⊗ₖ (SubState.basis (W₀, m₀)).matrix) =
    _ • (SubState.basis ((), W₀, m₀)).matrix
  have hU : (spongePurified X Z).init.matrix = (uniformFunctionState Z X).matrix ⊗ₖ
      ((uniformFunctionState X Z).matrix ⊗ₖ (uniformFunctionState X Z).matrix) := rfl
  rw [hU, conj_kronecker_kronecker, conj_rowAt_uniform, MatrixMap.conj_apply, Matrix.one_mul,
    conjTranspose_one, Matrix.mul_one, smul_kronecker, ← SubState.matrix_prod,
    SubState.basis_prod_basis]

omit [AddCommGroup X] [AddCommGroup Z] in
theorem fnReadKraus_mul_fnRow (t : (Z → X) × (X → Z) × (X → Z)) (c : HwRead X Z M)
    (r : c.Result) :
    fnReadKraus t c r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ fnRow X Z M t) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ fnRow X Z M t) * purReadKraus c r := by
  cases c with
  | readH z upd =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsMap
        (fun u : Unit × Hw X Z × M ↦ u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).1 z))
        (fun u ↦ (u.1, u.2.1, upd r.2 r.1))) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ fnRow X Z M t) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ fnRow X Z M t) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        clsMap (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).1 z))
          (fun q ↦ (q.1, q.2.1, upd r.2 r.1)))
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, fnRow]
    exact congrArg _ (clsMap_mul_rowAt t
      (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).1 z))
      fun b ↦ (b.1, upd r.2 r.1))
  | readK x upd =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsMap
        (fun u : Unit × Hw X Z × M ↦ u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).2.1 x))
        (fun u ↦ (u.1, u.2.1, upd r.2 r.1))) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ fnRow X Z M t) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ fnRow X Z M t) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        clsMap (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).2.1 x))
          (fun q ↦ (q.1, q.2.1, upd r.2 r.1)))
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, fnRow]
    exact congrArg _ (clsMap_mul_rowAt t
      (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).2.1 x))
      fun b ↦ (b.1, upd r.2 r.1))
  | readK' x upd =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsMap
        (fun u : Unit × Hw X Z × M ↦ u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).2.2 x))
        (fun u ↦ (u.1, u.2.1, upd r.2 r.1))) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ fnRow X Z M t) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ fnRow X Z M t) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        clsMap (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).2.2 x))
          (fun q ↦ (q.1, q.2.1, upd r.2 r.1)))
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, fnRow]
    exact congrArg _ (clsMap_mul_rowAt t
      (fun q : FnReg X Z M ↦ q.2.2 = r.2 ∧ r.1 = some ((overwrite q.2.1 q.1).2.2 x))
      fun b ↦ (b.1, upd r.2 r.1))

theorem fnRow_step_intertwine (t : (Z → X) × (X → Z) × (X → Z)) (W₀ : Hw X Z) (m₀ : M)
    (i : (hwReadSpec X Z M).Port) (r : (hwReadSpec X Z M).Result i) :
    ((spongeFnReadRuntime X Z t W₀ m₀).step i).branch r ∘ₗ
        (MatrixMap.conj (fnRow X Z M t)).amplifyLeft ((hwReadSpec X Z M).In i) =
      (MatrixMap.conj (fnRow X Z M t)).amplifyLeft ((hwReadSpec X Z M).Out i) ∘ₗ
        ((hwPurRuntime X Z W₀ m₀).step i).branch r := by
  rcases i with i | c
  · change MatrixMap.conj ((spongeFnHw X Z t W₀ m₀).U i) ∘ₗ
        (MatrixMap.conj (fnRow X Z M t)).amplifyLeft (spongeIn X Z i) =
      (MatrixMap.conj (fnRow X Z M t)).amplifyLeft (spongeIn X Z i) ∘ₗ
        MatrixMap.conj ((hwPurified X Z W₀ m₀).U i)
    rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
    congr 1
    cases i
    · exact tableOracle_mul_rowAt (fun q : FnReg X Z M ↦ (overwrite q.2.1 q.1).1) t
    · exact tableOracle_mul_rowAt (fun q : FnReg X Z M ↦ (overwrite q.2.1 q.1).2.1) t
    · exact tableOracle_mul_rowAt (fun q : FnReg X Z M ↦ (overwrite q.2.1 q.1).2.2) t
  · have e₁ : ((spongeFnReadRuntime X Z t W₀ m₀).step (.inr c)).branch r =
        MatrixMap.conj (fnReadKraus t c r) := rfl
    have e₂ : ((hwPurRuntime X Z W₀ m₀).step (.inr c)).branch r =
        MatrixMap.conj (purReadKraus c r) := rfl
    have key : MatrixMap.conj (fnReadKraus t c r) ∘ₗ
        MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ fnRow X Z M t) =
        MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ fnRow X Z M t) ∘ₗ
          MatrixMap.conj (purReadKraus c r) := by
      rw [← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
      exact congrArg MatrixMap.conj (fnReadKraus_mul_fnRow t c r)
    rw [e₁, e₂, MatrixMap.amplifyLeft_conj]
    exact key

/-- **The read ports are classical reads.** Every program over the sponge and read ports has the
same law against runtime 1 started at `(∅, W₀, m₀)` as on average over uniform functions `t`
against `spongeFnReadRuntime t W₀ m₀`, which answers the sponge ports with the oracles of
`overwrite W t` and the reads of a cell with the value of `overwrite W t` there. -/
theorem read_port_eq_classical_read {γ : Type*} [MeasurableSpace γ] (W₀ : Hw X Z) (m₀ : M)
    (I : L.Interp) (x : QuantumComp L (hwReadSpec X Z M) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (spongeHardwiredReadRuntime X Z W₀ m₀).evalDistMap I x ρ f =
      ∑ t : (Z → X) × (X → Z) × (X → Z), (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ •
        (spongeFnReadRuntime X Z t W₀ m₀).evalDistMap I x ρ f := by
  rw [evalDistMap_spongeHardwiredReadRuntime_eq_pur]
  refine (evalDistMap_eq_sum_of_rows (hwPurRuntime X Z W₀ m₀)
    (fun t ↦ spongeFnReadRuntime X Z t W₀ m₀) (fun t ↦ fnRow X Z M t)
    (fun _ ↦ (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0)⁻¹)
    (by exact sum_conjTranspose_fnRow_mul_self)
    (fun t i r ↦ by exact fnRow_step_intertwine t W₀ m₀ i r)
    (fun t ↦ by exact conj_fnRow_init t W₀ m₀) I x ρ f).trans ?_
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [ENNReal.coe_inv (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_natCast]

end Quantum.Sponge

end
