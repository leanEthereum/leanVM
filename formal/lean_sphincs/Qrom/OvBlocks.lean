module

public import Qrom.Override
public import Qrom.Blocks

@[expose] public section

/-!
# Games that agree on a set of side states

Let `U` be a set of side states closed under predecessors: a side port that leads into `U` starts
in `U`. Two games (`Qrom.OvGame`) with the same overrides and transitions on `U` run every program,
against every function `G`, to the same joint post-states on the side states of `U`
(`Qrom.OvGame.conj_jointPost_eq_of_agreeOn`), and have the same query weights for weights that only
read the side states of `U` (`Qrom.OvGame.queryWeight_eq_of_agreeOn`). This is
`Qrom.conj_jointPost_eq_of_proj` for the projector onto `U`: the hash keeps the side state, and a
side port moves `s₀` to its successor, which lies in `U` only if `s₀` does.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

namespace OvGame

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]

/-- The projector onto the side states of `U`. -/
def sideProj (U : Set S) [DecidablePred (· ∈ U)] : Matrix (S × Unit) (S × Unit) ℂ :=
  diagonal fun t ↦ if t.1 ∈ U then 1 else 0

variable (U : Set S) [DecidablePred (· ∈ U)]

theorem sideProj_conjTranspose : (sideProj U)ᴴ = sideProj U := by
  rw [sideProj, diagonal_conjTranspose]
  congr 1
  funext t
  by_cases h : t.1 ∈ U <;> simp [h]

theorem sideProj_mul_self : sideProj U * sideProj U = sideProj U := by
  rw [sideProj, diagonal_mul_diagonal]
  congr 1
  funext t
  split_ifs <;> simp

theorem sideProj_eq_kronecker :
    sideProj U = diagonal (fun s : S ↦ if s ∈ U then (1 : ℂ) else 0) ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
  ext ⟨s, ⟨⟩⟩ ⟨s', ⟨⟩⟩
  by_cases h : s = s'
  · subst h
    simp [sideProj, kroneckerMap_apply]
  · simp [sideProj, kroneckerMap_apply, diagonal_apply_ne _ h,
      diagonal_apply_ne _ (fun e : (s, ()) = (s', ()) ↦ h (Prod.mk.inj e).1)]

/-- A table oracle keeps the table, so it commutes with a projector read off the table. -/
theorem tableOracle_comm_sideProj (read : S × Unit → X → Y) :
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ sideProj U) * tableOracle read =
      tableOracle read * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ sideProj U) := by
  ext ⟨m, t⟩ ⟨m', t'⟩
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (m, t), Finset.sum_eq_single (m', t')]
  · simp only [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, sideProj,
      diagonal_apply_eq, tableOracle_apply, tableOracleEquiv_apply, Prod.mk.injEq]
    by_cases h : t = t'
    · subst h
      ring
    · simp [h]
  · intro k _ hk
    obtain ⟨m₁, t₁⟩ := k
    simp only [kroneckerMap_apply, Matrix.one_apply, sideProj, diagonal_apply]
    by_cases h1 : m₁ = m'
    · by_cases h2 : t₁ = t'
      · exact absurd (by rw [h1, h2]) hk
      · simp [h2]
    · simp [h1]
  · simp
  · intro k _ hk
    obtain ⟨m₁, t₁⟩ := k
    simp only [kroneckerMap_apply, Matrix.one_apply, sideProj, diagonal_apply]
    by_cases h1 : m = m₁
    · by_cases h2 : t = t₁
      · exact absurd (by rw [h1, h2]) hk
      · simp [h2]
    · simp [h1]
  · simp

theorem sideProj_mul_tableOracle_mul_sideProj (read : S × Unit → X → Y) :
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ sideProj U) * tableOracle read *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ sideProj U) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ sideProj U) * tableOracle read := by
  calc _ = tableOracle read * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ sideProj U) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ sideProj U) := by rw [tableOracle_comm_sideProj]
    _ = tableOracle read * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ sideProj U) := by
        rw [Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.one_mul, sideProj_mul_self]
    _ = _ := (tableOracle_comm_sideProj U read).symm

/-- Two table oracles whose reads agree on the side states of `U` agree inside the projector. -/
theorem sideProj_mul_tableOracle_eq {read₁ read₂ : S × Unit → X → Y}
    (h : ∀ t, t.1 ∈ U → read₁ t = read₂ t) :
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ sideProj U) * tableOracle read₁ =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ sideProj U) * tableOracle read₂ := by
  ext ⟨m, t⟩ ⟨m', t'⟩
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (m, t), Finset.sum_eq_single (m, t)]
  · simp only [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, sideProj, diagonal_apply_eq,
      tableOracle_apply, tableOracleEquiv_apply, Prod.mk.injEq]
    by_cases hU : t.1 ∈ U
    · by_cases ht : t = t'
      · subst ht
        rw [h t hU]
      · simp [ht]
    · simp [hU]
  all_goals first
    | (intro k _ hk
       obtain ⟨m₁, t₁⟩ := k
       simp only [kroneckerMap_apply, Matrix.one_apply, sideProj, diagonal_apply]
       by_cases h1 : m = m₁
       · by_cases h2 : t = t₁
         · exact absurd (by rw [h1, h2]) hk
         · simp [h2]
       · simp [h1])
    | simp

variable (g₁ g₂ : OvGame X Y S P Res)

theorem diagonal_mul_single' (d : S → ℂ) (i j : S) (c : ℂ) :
    diagonal d * Matrix.single i j c = Matrix.single i j (d i * c) := by
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]

theorem single_mul_diagonal' (d : S → ℂ) (i j : S) (c : ℂ) :
    Matrix.single i j c * diagonal d = Matrix.single i j (c * d j) := by
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]

/-- The side Kraus operators inside the projector: `|s'⟩⟨s₀|` survives when `s'` lies in `U`. -/
theorem sideProj_mul_sideKraus (g : OvGame X Y S P Res) (j : P) (rs : Res j × S) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ sideProj U) * g.sideKraus Unit j rs =
      (if (g.trans j rs.2).2 ∈ U then (1 : ℂ) else 0) • g.sideKraus Unit j rs := by
  rw [sideKraus, sideProj_eq_kronecker, Matrix.mul_smul, ← mul_kronecker_mul, ← mul_kronecker_mul]
  simp only [Matrix.one_mul]
  rw [diagonal_mul_single']
  by_cases h : (g.trans j rs.2).2 ∈ U <;> simp [h]

theorem sideKraus_mul_sideProj (g : OvGame X Y S P Res) (j : P) (rs : Res j × S) :
    g.sideKraus Unit j rs * ((1 : Matrix Unit Unit ℂ) ⊗ₖ sideProj U) =
      (if rs.2 ∈ U then (1 : ℂ) else 0) • g.sideKraus Unit j rs := by
  rw [sideKraus, sideProj_eq_kronecker, Matrix.smul_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]
  simp only [Matrix.mul_one]
  rw [single_mul_diagonal']
  by_cases h : rs.2 ∈ U <;> simp [h]

/-- The Kraus operators of the sampled game. -/
noncomputable def sampKraus (g : OvGame X Y S P Res) (G : X → Y) :
    ∀ i : (ovSpec X Y S P Res).Port, (ovSpec X Y S P Res).Result i →
      Matrix ((ovSpec X Y S P Res).Out i × (S × Unit)) ((ovSpec X Y S P Res).In i × (S × Unit)) ℂ
  | .inl _ => fun _ ↦ tableOracle (fun t : S × Unit ↦ g.answer t.1 G)
  | .inr j => fun r ↦ g.sideKraus Unit j r

theorem sampled_branch (g : OvGame X Y S P Res) (G : X → Y) (i : (ovSpec X Y S P Res).Port)
    (r : (ovSpec X Y S P Res).Result i) :
    ((g.sampled G).step i).branch r = MatrixMap.conj (g.sampKraus G i r) := by
  rcases i with ⟨⟩ | j
  · exact SubInstrument.branch_ofIsometry_apply _ (conjTranspose_tableOracle_mul_self _) r
  · exact g.sideStep_branch Unit j r

variable {U} {g₁ g₂}

theorem sideKraus_leak (g : OvGame X Y S P Res) (hclosed : ∀ j s, (g.trans j s).2 ∈ U → s ∈ U)
    (j : P) (r : Res j × S) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ sideProj U) * g.sideKraus Unit j r =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ sideProj U) * g.sideKraus Unit j r *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ sideProj U) := by
  rw [sideProj_mul_sideKraus, Matrix.smul_mul, sideKraus_mul_sideProj, smul_smul]
  by_cases h : (g.trans j r.2).2 ∈ U
  · simp [h, hclosed j r.2 h]
  · simp [h]

theorem sideKraus_agree (hclosed₁ : ∀ j s, (g₁.trans j s).2 ∈ U → s ∈ U)
    (hclosed₂ : ∀ j s, (g₂.trans j s).2 ∈ U → s ∈ U)
    (htr : ∀ s ∈ U, ∀ j, (g₁.trans j s).2 ∈ U ∨ (g₂.trans j s).2 ∈ U →
      g₁.trans j s = g₂.trans j s) (j : P) (r : Res j × S) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ sideProj U) * g₁.sideKraus Unit j r =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ sideProj U) * g₂.sideKraus Unit j r := by
  rw [sideProj_mul_sideKraus, sideProj_mul_sideKraus]
  by_cases h0 : r.2 ∈ U
  · by_cases hU : (g₁.trans j r.2).2 ∈ U ∨ (g₂.trans j r.2).2 ∈ U
    · rw [sideKraus, sideKraus, htr r.2 h0 j hU]
    · push Not at hU
      simp [hU.1, hU.2]
  · have h1 : (g₁.trans j r.2).2 ∉ U := fun h ↦ h0 (hclosed₁ j r.2 h)
    have h2 : (g₂.trans j r.2).2 ∉ U := fun h ↦ h0 (hclosed₂ j r.2 h)
    simp [h1, h2]

theorem sampKraus_leak (g : OvGame X Y S P Res) (hclosed : ∀ j s, (g.trans j s).2 ∈ U → s ∈ U)
    (G : X → Y) (i : (ovSpec X Y S P Res).Port) (r : (ovSpec X Y S P Res).Result i) :
    ((1 : Matrix ((ovSpec X Y S P Res).Out i) ((ovSpec X Y S P Res).Out i) ℂ) ⊗ₖ sideProj U) *
        g.sampKraus G i r =
      ((1 : Matrix ((ovSpec X Y S P Res).Out i) ((ovSpec X Y S P Res).Out i) ℂ) ⊗ₖ sideProj U) *
        g.sampKraus G i r *
        ((1 : Matrix ((ovSpec X Y S P Res).In i) ((ovSpec X Y S P Res).In i) ℂ) ⊗ₖ sideProj U) := by
  rcases i with ⟨⟩ | j
  · exact (sideProj_mul_tableOracle_mul_sideProj U _).symm
  · exact sideKraus_leak g hclosed j r

theorem sampKraus_agree (hclosed₁ : ∀ j s, (g₁.trans j s).2 ∈ U → s ∈ U)
    (hclosed₂ : ∀ j s, (g₂.trans j s).2 ∈ U → s ∈ U) (hov : ∀ s ∈ U, g₁.ov s = g₂.ov s)
    (htr : ∀ s ∈ U, ∀ j, (g₁.trans j s).2 ∈ U ∨ (g₂.trans j s).2 ∈ U →
      g₁.trans j s = g₂.trans j s) (G : X → Y)
    (i : (ovSpec X Y S P Res).Port) (r : (ovSpec X Y S P Res).Result i) :
    ((1 : Matrix ((ovSpec X Y S P Res).Out i) ((ovSpec X Y S P Res).Out i) ℂ) ⊗ₖ sideProj U) *
        g₁.sampKraus G i r *
        ((1 : Matrix ((ovSpec X Y S P Res).In i) ((ovSpec X Y S P Res).In i) ℂ) ⊗ₖ sideProj U) =
      ((1 : Matrix ((ovSpec X Y S P Res).Out i) ((ovSpec X Y S P Res).Out i) ℂ) ⊗ₖ sideProj U) *
        g₂.sampKraus G i r *
        ((1 : Matrix ((ovSpec X Y S P Res).In i) ((ovSpec X Y S P Res).In i) ℂ) ⊗ₖ sideProj U) := by
  rw [← sampKraus_leak g₁ hclosed₁, ← sampKraus_leak g₂ hclosed₂]
  rcases i with ⟨⟩ | j
  · exact sideProj_mul_tableOracle_eq U fun t ht ↦ by
      funext x
      simp only [answer, hov t.1 ht]
  · exact sideKraus_agree hclosed₁ hclosed₂ htr j r

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **Agreement on `U` of the joint post-states.** -/
theorem conj_jointPost_eq_of_agreeOn (I : L.Interp)
    (hclosed₁ : ∀ j s, (g₁.trans j s).2 ∈ U → s ∈ U)
    (hclosed₂ : ∀ j s, (g₂.trans j s).2 ∈ U → s ∈ U) (hov : ∀ s ∈ U, g₁.ov s = g₂.ov s)
    (htr : ∀ s ∈ U, ∀ j, (g₁.trans j s).2 ∈ U ∨ (g₂.trans j s).2 ∈ U →
      g₁.trans j s = g₂.trans j s) (hinit : g₁.init = g₂.init) (G : X → Y)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (p : Σ u, W u) :
    (MatrixMap.conj (sideProj U)).amplifyLeft p.1 ((g₁.sampled G).jointPost I x ρ p).matrix =
      (MatrixMap.conj (sideProj U)).amplifyLeft p.1 ((g₂.sampled G).jointPost I x ρ p).matrix :=
  conj_jointPost_eq_of_proj I (g₁.sampled_branch G) (g₂.sampled_branch G)
    (sideProj_conjTranspose U) (sideProj_mul_self U) (sampKraus_leak g₁ hclosed₁ G)
    (sampKraus_leak g₂ hclosed₂ G) (sampKraus_agree hclosed₁ hclosed₂ hov htr G)
    (by simp [tabRuntime, sampled, hinit]) x ρ p

/-- **Agreement on `U` of the query weights.** -/
theorem queryWeight_eq_of_agreeOn (I : L.Interp)
    (hclosed₁ : ∀ j s, (g₁.trans j s).2 ∈ U → s ∈ U)
    (hclosed₂ : ∀ j s, (g₂.trans j s).2 ∈ U → s ∈ U) (hov : ∀ s ∈ U, g₁.ov s = g₂.ov s)
    (htr : ∀ s ∈ U, ∀ j, (g₁.trans j s).2 ∈ U ∨ (g₂.trans j s).2 ∈ U →
      g₁.trans j s = g₂.trans j s) (hinit : g₁.init = g₂.init) (G : X → Y)
    (w : ∀ i : (ovSpec X Y S P Res).Port, Matrix ((ovSpec X Y S P Res).In i × (S × Unit))
      ((ovSpec X Y S P Res).In i × (S × Unit)) ℂ → ℝ≥0∞)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (j : ℕ) :
    (g₁.sampled G).queryWeight I
        (fun i σ ↦ w i ((MatrixMap.conj (sideProj U)).amplifyLeft _ σ)) x
        (ρ.matrix ⊗ₖ (g₁.sampled G).init.matrix) j =
      (g₂.sampled G).queryWeight I
        (fun i σ ↦ w i ((MatrixMap.conj (sideProj U)).amplifyLeft _ σ)) x
        (ρ.matrix ⊗ₖ (g₂.sampled G).init.matrix) j :=
  queryWeight_eq_of_proj I (g₁.sampled_branch G) (g₂.sampled_branch G)
    (sideProj_conjTranspose U) (sideProj_mul_self U) (sampKraus_leak g₁ hclosed₁ G)
    (sampKraus_leak g₂ hclosed₂ G) (sampKraus_agree hclosed₁ hclosed₂ hov htr G)
    (by simp [tabRuntime, sampled, hinit]) w x ρ.matrix j

end OvGame

end Qrom
