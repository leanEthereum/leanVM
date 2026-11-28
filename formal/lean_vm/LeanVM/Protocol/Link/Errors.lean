/-
  LeanVM.Protocol.Link.Errors

  The Schwartz-Zippel counts `verifyLink_sound` takes, from Hotwire's lemmas: a failed state link
  or lookup leaves the index side's batched error nonzero except on `max(W + 1, m + 3 + ν)/|E|` of
  the challenges, and a chunk that is not one-hot leaves the mirror certificate nonzero except on
  `(m + 3 + 2·w_max)/|E|`.
-/

module

public import LeanVM.Protocol.Link.Sample
public import LeanVM.Protocol.Hotwire.StateLink
public import LeanVM.Protocol.Hotwire.Lookup
public import LeanVM.Protocol.Hotwire.Mirror
import LeanVM.Parameters.Field

/-!
# The link's errors, counted

`verifyLink_sound` (`LeanVM.Protocol.Link.Sound`) takes the Schwartz-Zippel counts of its two cases
as hypotheses (`hA`, `hB`), over the challenges at their positions in the transcript. Here they are
proved from `StateLink.lean`, `Lookup.lean` and `Mirror.lean`, for challenges placed injectively
among the transcript's (`ι`), as `verify_link` draws each from its own position:

* **Batching by fresh coefficients** (`batchN`, `card_batchN_le`): `P_0 + Σ_i η_i·P_i`, the `η_i`
  variables of their own, is nonzero when one of the `P`s is, of degree at most `P_0`'s or one more
  than the `P_i`'s. The index side's claim batches the state link with the lookups this way, `η_mem` and `η_bc` its `η`s
  (`verify_link`'s `eta_mem`, `eta_bc`); in characteristic two the state identity's difference is
  its sum.
* **A lookup with no `μ`** (`identityPolyU`, `identityPolyU_ne_zero`): the program lookup weighs
  its one access per table by the row weight alone; `Lookup.lean`'s identity at `μ = 1` stays a
  nonzero polynomial of degree `m + 1 + ν` when the link fails.
* **The link's error** (`card_linkError_le`): if the state link or either lookup fails, the batched
  error `(scalarLhs − scalarRhs) + η_M·identity_M + η_P·identity_P` vanishes at no more than
  `max(W + 1, m + 3 + max(ν_M, ν_P))·|E|^(n−1)` of the `|E|^n` challenge vectors: the state link's
  defect carries no `η`, so only the lookups' degree gains one. This is the numerator `verify_link`
  grinds for, `max(m + 3 + bytecodeSlotBits, W + 1)` (`ν_P = bytecodeSlotBits`). The two lookups share the row
  weights `θ`, `τ`, as `verify_link`'s do.
* **The mirror certificate** (`card_mirror_le`): `card_batchedCert_eq_zero_le` at the challenges'
  positions, `m + 3 + 2·w_max`; over the tables (`card_mirrorTables_le`), each table's certificate
  under its own `θ_F`, at the prefix of `τ` its height takes and its columns' `ε`, as
  `verify_link`'s certificate weight sums them, still `m + 3 + 2·w_max`.
-/

namespace LeanVM.Protocol.Link

open LeanVM.Parameters LeanVM.Protocol.Hotwire Finset MvPolynomial

@[expose] public section

/-! ## Batching by fresh coefficients -/

section Batch

variable {τ ι : Type} [Fintype ι]

/-- `P_0 + Σ_i η_i·P_i`, the `η_i` new variables. -/
noncomputable def batchN (P0 : MvPolynomial τ E) (P : ι → MvPolynomial τ E) :
    MvPolynomial (τ ⊕ ι) E :=
  rename Sum.inl P0 + ∑ i, X (Sum.inr i) * rename Sum.inl (P i)

theorem eval_batchN (P0 : MvPolynomial τ E) (P : ι → MvPolynomial τ E) (x : τ ⊕ ι → E) :
    eval x (batchN P0 P) = eval (x ∘ Sum.inl) P0 + ∑ i, x (Sum.inr i) * eval (x ∘ Sum.inl) (P i) := by
  simp [batchN, eval_rename]

/-- The `η`s set to `c`: `P_0 + Σ_i c_i·P_i`. -/
theorem aeval_batchN (P0 : MvPolynomial τ E) (P : ι → MvPolynomial τ E) (c : ι → E) :
    aeval (Sum.elim X fun i ↦ C (c i)) (batchN P0 P) = P0 + ∑ i, C (c i) * P i := by
  simp [batchN, aeval_rename, Function.comp_def, aeval_X_left_apply]

/-- **Batching keeps a nonzero polynomial nonzero**: at `η = 0` the batch is `P_0`, at `η` the
indicator of `i` it is `P_0 + P_i`. -/
theorem batchN_ne_zero [DecidableEq ι] (P0 : MvPolynomial τ E) (P : ι → MvPolynomial τ E)
    (h : P0 ≠ 0 ∨ ∃ i, P i ≠ 0) : batchN P0 P ≠ 0 := by
  intro hz
  have key : ∀ c : ι → E, P0 + ∑ i, C (c i) * P i = 0 := fun c ↦ by
    rw [← aeval_batchN, hz, map_zero]
  have h0 : P0 = 0 := by simpa using key 0
  rcases h with h | ⟨i, hi⟩
  · exact h h0
  · refine hi ?_
    have := key (Pi.single i 1)
    rw [h0, zero_add, sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)] at this
    simpa using this

theorem totalDegree_batchN (P0 : MvPolynomial τ E) (P : ι → MvPolynomial τ E) {D0 D : ℕ}
    (h0 : P0.totalDegree ≤ D0) (h : ∀ i, (P i).totalDegree ≤ D) :
    (batchN P0 P).totalDegree ≤ max D0 (D + 1) := by
  refine (totalDegree_add _ _).trans (max_le_max ?_ ?_)
  · exact (totalDegree_rename_le _ _).trans h0
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, add_comm]
    exact Nat.add_le_add_right ((totalDegree_rename_le _ _).trans (h i)) 1

/-- **The batched count.** If `P_0` or some `P_i` is nonzero, `P_0` of total degree at most `D_0`
and the `P_i` at most `D`, the batch vanishes at no more than `max(D_0, D + 1)·|E|^(n−1)` of the
`|E|^n` challenge vectors, its variables placed injectively by `ι`. -/
theorem card_batchN_le [DecidableEq ι] [Fintype τ] [DecidableEq τ] {n : ℕ} (ιn : τ ⊕ ι → Fin n)
    (hι : Function.Injective ιn) (P0 : MvPolynomial τ E) (P : ι → MvPolynomial τ E)
    (h : P0 ≠ 0 ∨ ∃ i, P i ≠ 0) {D0 D : ℕ} (h0 : P0.totalDegree ≤ D0)
    (hd : ∀ i, (P i).totalDegree ≤ D) :
    (univ.filter fun v : Fin n → E ↦ eval (v ∘ ιn ∘ Sum.inl) P0 +
        ∑ i, v (ιn (Sum.inr i)) * eval (v ∘ ιn ∘ Sum.inl) (P i) = 0).card ≤
      max D0 (D + 1) * Fintype.card E ^ (n - 1) := by
  classical
  have h := card_eval_comp_le ιn hι (batchN P0 P) (batchN_ne_zero P0 P h)
    (totalDegree_batchN P0 P h0 hd)
  refine le_of_eq_of_le (congrArg card (filter_congr fun v _ ↦ ?_)) h
  rw [eval_batchN]
  rfl

end Batch

/-! ## A lookup with one access per table -/

/-! The program lookup's access carries no coefficient of its own: its weight is the row weight
`θ_F·eq(τ_F, u)` alone (`verify_link`'s pointer column `1`, `e·ω·(x_bc + fp·p_fp)`), one access per
table. `Lookup.lean`'s identity at `μ = 1` is then a polynomial in `(θ, τ, β)` that a failed link
still leaves nonzero, as long as each slot is its own table (`identityPolyU_ne_zero`): `θ` the
indicator of the failing slot's table picks it out. -/

section UnitMu

variable {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] {nT nC nD m W : ℕ}
  (L : Lookup E S Q nT nC nD m W) {G : Type}

/-- The variables of a lookup with no `μ`: `θ`, `τ` and the coordinate coefficients' `β`. -/
abbrev LookupVarU (G : Type) (nT m : ℕ) : Type := Fin nT ⊕ Fin m ⊕ G

/-- An access's coefficient `θ_F·eq(τ_F, u)` as a polynomial, zero when it is off. -/
noncomputable def coefPolyU (k : S) (u : ℕ) : MvPolynomial (LookupVarU G nT m) E :=
  if L.on k u then X (.inl (L.table k)) * rename (fun i ↦ .inr (.inl i)) (eqLowPoly m (L.height k) u)
  else 0

/-- `Σ_{k,u} coef·Σ_i γ_i·err(k, u)_i` at `μ = 1`, as a polynomial in `(θ, τ, β)`. -/
noncomputable def identityPolyU (Γ : Coeffs E G nC) : MvPolynomial (LookupVarU G nT m) E :=
  ∑ k, ∑ u ∈ range (2 ^ L.height k),
    coefPolyU L k u * ∑ i, rename (fun g ↦ .inr (.inr g)) (Γ.poly i) * C (L.err k u i)

omit [Fintype S] [DecidableEq S] [Fintype Q] in
theorem eval_coefPolyU (x : LookupVarU G nT m → E) (k : S) (u : ℕ) :
    eval x (coefPolyU (G := G) L k u) =
      L.coef (fun t ↦ x (.inl t)) (fun i ↦ x (.inr (.inl i))) (fun _ ↦ 1) k u := by
  unfold coefPolyU Lookup.coef
  split_ifs
  · simp only [map_mul, eval_X, eval_rename, eval_eqLowPoly, mul_one]
    rfl
  · simp

/-- The polynomial evaluates to the identity's left side at `μ = 1`. -/
theorem eval_identityPolyU (Γ : Coeffs E G nC) (x : LookupVarU G nT m → E) :
    eval x (identityPolyU L Γ) =
      L.identity (fun t ↦ x (.inl t)) (fun i ↦ x (.inr (.inl i))) (fun _ ↦ 1)
        (fun c ↦ eval (fun g ↦ x (.inr (.inr g))) (Γ.poly c)) := by
  rw [Lookup.identity_eq_sum_err]
  simp only [identityPolyU, map_sum, map_mul, eval_coefPolyU, eval_rename, eval_C]
  rfl

omit [Fintype S] [DecidableEq S] [Fintype Q] in
theorem totalDegree_coefPolyU (k : S) (u : ℕ) :
    (coefPolyU (G := G) L k u).totalDegree ≤ m + 1 := by
  unfold coefPolyU
  split_ifs
  · refine (totalDegree_mul _ _).trans ?_
    have h1 := (totalDegree_X (R := E) (.inl (L.table k) : LookupVarU G nT m)).le
    have h2 := (totalDegree_rename_le (fun i ↦ (.inr (.inl i) : LookupVarU G nT m))
      (eqLowPoly (F := E) m (L.height k) u)).trans totalDegree_eqLowPoly
    omega
  · simp

/-- The polynomial has total degree at most `m + 1 + ν`. -/
theorem totalDegree_identityPolyU (Γ : Coeffs E G nC) :
    (identityPolyU L Γ).totalDegree ≤ m + 1 + Γ.ν := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun k _ ↦ ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun u _ ↦ ?_)
  refine (totalDegree_mul _ _).trans (add_le_add (totalDegree_coefPolyU L k u) ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
  refine (totalDegree_mul _ _).trans ?_
  simpa [totalDegree_C] using (totalDegree_rename_le _ _).trans (Γ.degree_le i)

/-- **A failed lookup with no `μ` is a nonzero polynomial**, each slot its own table: at `θ` the
indicator of the failing slot's table, `τ` the Boolean point of the failing row and `β` a point
where the coefficients see that access's defect, it is that defect's combination. -/
theorem identityPolyU_ne_zero (Γ : Coeffs E G nC) (hinj : Function.Injective L.table)
    (hfail : ¬ L.LinkHolds) : identityPolyU L Γ ≠ 0 := by
  classical
  obtain ⟨k₀, u₀, hu₀, hon, hbad⟩ :
      ∃ k u, u < 2 ^ L.height k ∧ L.on k u = true ∧ L.err k u ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hfail fun k u hu hon ↦ (L.err_eq_zero_iff k u).mp (hall k u hu hon)
  obtain ⟨y, hy⟩ := Γ.separates _ hbad
  intro hz
  have h := congrArg (eval (Sum.elim (fun t ↦ if t = L.table k₀ then (1 : E) else 0)
    (Sum.elim (bitPt u₀) y))) hz
  rw [map_zero, eval_identityPolyU, Lookup.identity_eq_sum_err] at h
  simp only [Sum.elim_inl, Sum.elim_inr] at h
  rw [sum_eq_single_of_mem k₀ (mem_univ _) (fun k _ hk ↦ sum_eq_zero fun u _ ↦ by
    simp [Lookup.coef, hinj.ne hk])] at h
  rw [sum_eq_single_of_mem u₀ (mem_range.mpr hu₀) (fun u hu hne ↦ by
    simp [Lookup.coef, eqLow_bitPt (L.height_le k₀) (mem_range.mp hu) hu₀, hne])] at h
  simp only [Lookup.coef, hon, ite_true, eqLow_bitPt (L.height_le k₀) hu₀ hu₀, one_mul,
    mul_one] at h
  exact hy h

end UnitMu

/-! ## The link's error -/

section LinkError

/-- The challenges of the index side's error: the state link's `(ζ, γ_state)`, the row weights
`(θ, τ)` the lookups share, the memory lookup's `(μ, β)`, the program lookup's `β`, and the two
`η`s. -/
abbrev LinkVar (W k nT m : ℕ) (SM GM GP : Type) : Type :=
  ((Fin W ⊕ Fin k) ⊕ (Fin nT ⊕ Fin m) ⊕ (SM ⊕ GM) ⊕ GP) ⊕ Fin 2

variable {W k nT m : ℕ} {SM GM GP : Type}

/-- The memory lookup's variables among the link's: `θ`, `τ` the shared ones, `(μ, β)` its own. -/
def memoryVar : LookupVar SM GM nT m → (Fin W ⊕ Fin k) ⊕ (Fin nT ⊕ Fin m) ⊕ (SM ⊕ GM) ⊕ GP :=
  Sum.elim (fun t ↦ .inr (.inl (.inl t)))
    (Sum.elim (fun i ↦ .inr (.inl (.inr i))) fun x ↦ .inr (.inr (.inl x)))

theorem memoryVar_injective :
    Function.Injective (memoryVar (W := W) (k := k) (nT := nT) (m := m) (SM := SM) (GM := GM)
      (GP := GP)) := by
  rintro (a | a | a) (b | b | b) hab <;> simp [memoryVar] at hab ⊢ <;> exact hab

/-- The program lookup's variables among the link's: `θ`, `τ` the shared ones, `β` its own. -/
def programVar : LookupVarU GP nT m → (Fin W ⊕ Fin k) ⊕ (Fin nT ⊕ Fin m) ⊕ (SM ⊕ GM) ⊕ GP :=
  Sum.elim (fun t ↦ .inr (.inl (.inl t)))
    (Sum.elim (fun i ↦ .inr (.inl (.inr i))) fun g ↦ .inr (.inr (.inr g)))

theorem programVar_injective :
    Function.Injective (programVar (W := W) (k := k) (nT := nT) (m := m) (SM := SM) (GM := GM)
      (GP := GP)) := by
  rintro (a | a | a) (b | b | b) hab <;> simp [programVar] at hab ⊢ <;> exact hab

variable {R : Type} [Fintype R] {T : ℕ} {σ : R → Fin (2 ^ W)} {s s' : R → Fin k → E}
  {sInit sFin : Fin k → E}
  [Fintype SM] [DecidableEq SM] [Fintype GM] [DecidableEq GM] [Fintype GP] [DecidableEq GP]
  {SP QM QP : Type} [Fintype SP] [DecidableEq SP] [Fintype QM] [Fintype QP]
  {nCM nDM WM nCP nDP WP : ℕ}

/-- **The index side's error, counted** (the paper's case (b): `max(m + 3 + ν, W + 1)`, the `1` over
`η` on the lookups alone), in leanVM's form: the memory lookup weighs each access by its own `μ`, the program lookup by
the row weight alone, one access per table. If the state link (`StateLink.lean`'s `LinkHolds`, with
`T < 2^W`) or either lookup fails, the index side's batched error
`(scalarLhs − scalarRhs)(ζ, γ) + η_M·identity_M(θ, τ, μ, γ_M) + η_P·identity_P(θ, τ, 1, γ_P)`
vanishes at no more than `max(W + 1, m + 3 + max(ν_M, ν_P))·|E|^(n−1)` of the `|E|^n` challenge
vectors, its challenges placed injectively by `ι`. -/
theorem card_linkError_le (hT : T < 2 ^ W)
    (LM : Lookup E SM QM nT nCM nDM m WM) (ΓM : Coeffs E GM nCM)
    (LP : Lookup E SP QP nT nCP nDP m WP) (ΓP : Coeffs E GP nCP) (hP : Function.Injective LP.table)
    {n : ℕ} (ι : LinkVar W k nT m SM GM GP → Fin n) (hι : Function.Injective ι)
    (hfail : ¬ (LinkHolds T σ s s' sInit sFin ∧ LM.LinkHolds ∧ LP.LinkHolds)) :
    (univ.filter fun v : Fin n → E ↦
        (scalarLhs σ s s' (fun i ↦ v (ι (.inl (.inl (.inl i))))) (fun l ↦ v (ι (.inl (.inl (.inr l))))) -
          scalarRhs T sInit sFin (fun i ↦ v (ι (.inl (.inl (.inl i))))) (fun l ↦ v (ι (.inl (.inl (.inr l)))))) +
        v (ι (.inr 0)) * LM.identity (fun t ↦ v (ι (.inl (.inr (.inl (.inl t))))))
          (fun i ↦ v (ι (.inl (.inr (.inl (.inr i)))))) (fun q ↦ v (ι (.inl (.inr (.inr (.inl (.inl q)))))))
          (fun c ↦ eval (fun g ↦ v (ι (.inl (.inr (.inr (.inl (.inr g))))))) (ΓM.poly c)) +
        v (ι (.inr 1)) * LP.identity (fun t ↦ v (ι (.inl (.inr (.inl (.inl t))))))
          (fun i ↦ v (ι (.inl (.inr (.inl (.inr i)))))) (fun _ ↦ 1)
          (fun c ↦ eval (fun g ↦ v (ι (.inl (.inr (.inr (.inr g)))))) (ΓP.poly c)) = 0).card ≤
      max (W + 1) (m + 3 + max ΓM.ν ΓP.ν) * Fintype.card E ^ (n - 1) := by
  classical
  let P0 : MvPolynomial ((Fin W ⊕ Fin k) ⊕ (Fin nT ⊕ Fin m) ⊕ (SM ⊕ GM) ⊕ GP) E :=
    rename Sum.inl (defectPoly T σ s s' sInit sFin)
  let P : Fin 2 → MvPolynomial ((Fin W ⊕ Fin k) ⊕ (Fin nT ⊕ Fin m) ⊕ (SM ⊕ GM) ⊕ GP) E :=
    ![rename memoryVar (LM.identityPoly ΓM), rename programVar (identityPolyU LP ΓP)]
  have hne : P0 ≠ 0 ∨ ∃ i, P i ≠ 0 := by
    by_cases hS : LinkHolds T σ s s' sInit sFin
    · by_cases hM : LM.LinkHolds
      · have hPf : ¬ LP.LinkHolds := fun h ↦ hfail ⟨hS, hM, h⟩
        refine Or.inr ⟨1, fun h0 ↦ identityPolyU_ne_zero LP ΓP hP hPf ?_⟩
        exact rename_injective _ programVar_injective (h0.trans (map_zero _).symm)
      · refine Or.inr ⟨0, fun h0 ↦ LM.identityPoly_ne_zero ΓM hM ?_⟩
        exact rename_injective _ memoryVar_injective (h0.trans (map_zero _).symm)
    · exact Or.inl fun h0 ↦ defectPoly_ne_zero hS
        (rename_injective _ Sum.inl_injective (h0.trans (map_zero _).symm))
  have hD0 : P0.totalDegree ≤ W + 1 := (totalDegree_rename_le _ _).trans totalDegree_defectPoly
  have hD : ∀ i, (P i).totalDegree ≤ m + 2 + max ΓM.ν ΓP.ν := by
    intro i
    fin_cases i
    · exact (totalDegree_rename_le _ _).trans ((LM.totalDegree_identityPoly ΓM).trans (by omega))
    · exact (totalDegree_rename_le _ _).trans ((totalDegree_identityPolyU LP ΓP).trans (by omega))
  have h := card_batchN_le ι hι P0 P hne hD0 hD
  rw [show m + 2 + max ΓM.ν ΓP.ν + 1 = m + 3 + max ΓM.ν ΓP.ν by omega] at h
  refine le_of_eq_of_le (congrArg card (filter_congr fun v _ ↦ ?_)) h
  rw [Fin.sum_univ_two]
  simp only [P0, P, Matrix.cons_val_zero, Matrix.cons_val_one, eval_rename]
  rw [LM.eval_identityPoly ΓM, eval_identityPolyU LP ΓP, eval_defectPoly,
    scalarLhs_sub_scalarRhs hT, ← add_assoc]
  rfl

end LinkError

/-! ## The mirror certificate -/

/-- **The one-hot check, counted** (the paper's case (a)): if some chunk of a gated row is not
one-hot, the batched mirror certificate vanishes at no more than `(m + 3 + 2·w_max)·|E|^(n−1)` of
the `|E|^n` challenge vectors, its challenges `(θ, τ, ε, ν, ρ)` placed injectively by `ι`. -/
theorem card_mirror_le {m Q d : ℕ} (w : Fin d → ℕ) {n : ℕ} (ι : BatchVar m Q d w → Fin n)
    (hι : Function.Injective ι) (b : ℕ → Bool) (e : Fin Q → Fin d → ℕ → ℕ → E) {wmax : ℕ}
    (hw : ∀ i, w i ≤ wmax)
    (hbad : ∃ u < 2 ^ m, b u = true ∧ ∃ q i, ¬ ∃ σ < 2 ^ w i, OneHot (w i) (e q i u) σ) :
    (univ.filter fun v : Fin n → E ↦
        batchedCert b e (v (ι (Sum.inl ()))) (List.ofFn fun k ↦ v (ι (Sum.inr (Sum.inl k))))
          (fun q ↦ v (ι (Sum.inr (Sum.inr (Sum.inl q)))))
          (fun i ↦ v (ι (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
          (fun i ↦ List.ofFn fun h ↦ v (ι (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, h⟩)))))) = 0).card ≤
      (m + 3 + 2 * wmax) * Fintype.card E ^ (n - 1) := by
  classical
  have h := card_eval_comp_le ι hι (batchedPoly m w b e) (batchedPoly_ne_zero w b e hbad)
    (totalDegree_batchedPoly w b e hw)
  refine le_of_eq_of_le (congrArg card (filter_congr fun v _ ↦ ?_)) h
  rw [eval_batchedPoly]
  rfl

/-! ## The mirror certificate over the tables -/

section Tables

variable {nT m Qt d : ℕ} (w : Fin d → ℕ)

/-- The certificate's challenges over every table: `θ_F` per table, the row point `τ ∈ E^m` the
tables share by prefixes, `ε_q` per pointer column, the chunk coefficients `ν` and the index point's
parts `ρ_i`. -/
abbrev CertVar (nT m Qt d : ℕ) (w : Fin d → ℕ) : Type :=
  Fin nT ⊕ Fin m ⊕ Fin Qt ⊕ Fin d ⊕ (Σ i, Fin (w i))

/-- Table `F`'s certificate variables among every table's: its `θ_F`, the first `h` coordinates of
`τ`, its columns' `ε`. -/
def tableVar (F : Fin nT) {h QF : ℕ} (hh : h ≤ m) (col : Fin QF → Fin Qt) :
    BatchVar h QF d w → CertVar nT m Qt d w :=
  Sum.elim (fun _ ↦ .inl F) (Sum.elim (fun k ↦ .inr (.inl (Fin.castLE hh k)))
    (Sum.elim (fun q ↦ .inr (.inr (.inl (col q))))
      (Sum.elim (fun i ↦ .inr (.inr (.inr (.inl i)))) fun p ↦ .inr (.inr (.inr (.inr p))))))

theorem tableVar_injective (F : Fin nT) {h QF : ℕ} (hh : h ≤ m) {col : Fin QF → Fin Qt}
    (hcol : Function.Injective col) : Function.Injective (tableVar w F hh col) := by
  rintro (a | a | a | a | a) (b | b | b | b | b) hab <;> simp [tableVar] at hab ⊢ <;>
    first | exact hab | exact hcol hab

/-- The batched certificate is `θ` times the rest. -/
theorem batchedPoly_eq_X_mul {h QF : ℕ} (b : ℕ → Bool) (e : Fin QF → Fin d → ℕ → ℕ → E) :
    ∃ R, batchedPoly h w b e = X (Sum.inl ()) * R :=
  ⟨_, rfl⟩

/-- **The one-hot check over the tables, counted** (the paper's case (a) as `verify_link` weighs
it: each table's certificate under its own `θ_F`, its rows at the prefix of `τ` its height takes,
its pointer columns' `ε`, the shared `ν` and `ρ`). If some chunk of a gated row of some table is not
one-hot, `Σ_F θ_F·Σ_{u : b_F(u)} eq(τ_F, u)·Σ_q ε_q·Σ_i ν_i·cert` vanishes at no more than
`(m + 3 + 2·w_max)·|E|^(n−1)` of the `|E|^n` challenge vectors: at `θ_F = 0` off the failing
table, it is that table's certificate. -/
theorem card_mirrorTables_le (h : Fin nT → ℕ) (hh : ∀ F, h F ≤ m) (QF : Fin nT → ℕ)
    (col : ∀ F, Fin (QF F) → Fin Qt) (hcol : ∀ F, Function.Injective (col F))
    (b : Fin nT → ℕ → Bool) (e : ∀ F, Fin (QF F) → Fin d → ℕ → ℕ → E) {wmax : ℕ}
    (hw : ∀ i, w i ≤ wmax) {n : ℕ} (ι : CertVar nT m Qt d w → Fin n) (hι : Function.Injective ι)
    (hbad : ∃ F, ∃ u < 2 ^ h F, b F u = true ∧
      ∃ q i, ¬ ∃ σ < 2 ^ w i, OneHot (w i) (e F q i u) σ) :
    (univ.filter fun v : Fin n → E ↦ ∑ F, batchedCert (b F) (e F) (v (ι (.inl F)))
        (List.ofFn fun k : Fin (h F) ↦ v (ι (.inr (.inl (Fin.castLE (hh F) k)))))
        (fun q ↦ v (ι (.inr (.inr (.inl (col F q))))))
        (fun i ↦ v (ι (.inr (.inr (.inr (.inl i))))))
        (fun i ↦ List.ofFn fun k ↦ v (ι (.inr (.inr (.inr (.inr ⟨i, k⟩)))))) = 0).card ≤
      (m + 3 + 2 * wmax) * Fintype.card E ^ (n - 1) := by
  classical
  let P : MvPolynomial (CertVar nT m Qt d w) E :=
    ∑ F, rename (tableVar w F (hh F) (col F)) (batchedPoly (h F) w (b F) (e F))
  have hP : P ≠ 0 := by
    obtain ⟨F0, u0, hu0, hb0, hq⟩ := hbad
    have hne := batchedPoly_ne_zero w (b F0) (e F0) ⟨u0, hu0, hb0, hq⟩
    intro hz
    let f : CertVar nT m Qt d w → MvPolynomial (CertVar nT m Qt d w) E :=
      Sum.elim (fun F ↦ if F = F0 then X (.inl F) else 0) fun x ↦ X (.inr x)
    have h0 := congrArg (aeval f) hz
    rw [map_zero, map_sum, sum_eq_single F0] at h0
    · refine hne (rename_injective _ (tableVar_injective w F0 (hh F0) (hcol F0)) ?_)
      rw [map_zero, ← h0, aeval_rename]
      rw [DFunLike.congr_fun (aeval_unique (rename (R := E) (tableVar w F0 (hh F0) (col F0))))
        (batchedPoly (h F0) w (b F0) (e F0))]
      have hfg : (⇑(rename (R := E) (tableVar w F0 (hh F0) (col F0))) ∘ X) =
          f ∘ tableVar w F0 (hh F0) (col F0) := by
        funext x
        rcases x with x | x | x | x | x <;> simp [f, tableVar]
      rw [hfg]
    · intro F _ hF
      obtain ⟨R, hR⟩ := batchedPoly_eq_X_mul w (b F) (e F)
      rw [aeval_rename, hR, map_mul, aeval_X]
      simp [f, tableVar, hF]
    · simp
  have hD : P.totalDegree ≤ m + 3 + 2 * wmax := by
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun F _ ↦ ?_)
    refine (totalDegree_rename_le _ _).trans ((totalDegree_batchedPoly w (b F) (e F) hw).trans ?_)
    have := hh F
    omega
  have hc := card_eval_comp_le ι hι P hP hD
  refine le_of_eq_of_le (congrArg card (filter_congr fun v _ ↦ ?_)) hc
  simp only [P, map_sum, eval_rename, eval_batchedPoly]
  rfl

end Tables

end

end LeanVM.Protocol.Link
