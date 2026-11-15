module

public import Quantum.Sponge.Oracle.Hardwired
public import Quantum.Xmss.HonestTable

@[expose] public section

/-!
# Lazy sampling of the honest cells: G2 is runtime 1

The step from the uniform-function experiment G2 to runtime 1 (`spongeHardwiredReadRuntime`) of
the design (sections 2 and 7, slice S3). Conditioned on the honest data, the three random
functions are uniform off the honest cells and fixed on them.

The honest data is a function `P t` of the functions `t = (h, k, k')` that determines its cells:
`hw (P t)` is a set of hardwired cells with values, and `t'` agrees with `hw (P t)` exactly when
`P t' = P t` (`hP`). The cells are chosen adaptively (which cells are read depends on the values
read before), but the condition says that the data a run reads is a function of the values it
read, as `honestEval_congr` states for the honest hash. Sampling `t` uniformly is then sampling
the data from its law `tableLaw P` and `t` uniformly among the functions consistent with its
cells (`sum_uniform_eq_sum_tableLaw`).

* `evalDistMap_spongeFnReadRuntime_overwrite`: classical reads against `t` with hardwired cells
  `W` are classical reads against `overwrite W t` without hardwired cells (the classical register
  is relabeled block by block).
* `evalDistMap_avg_eq_tableLaw`: a program over the sponge ports and the read ports, chosen by the
  data `P t` and run against the classical reads of `t`, averaged over uniform `t`, has the law of
  the `tableLaw P`-mixture of runtime 1 started with the data's cells `hw b` hardwired.
  `evalDistMap_avg_eq_tableLaw_sponge`: the same for programs over the sponge ports only, against
  the oracles of `t`. `evalDistMap_avg_eq_avg_runtime1`: the mixture written as the average over
  uniform `t` of runtime 1 with the cells of `P t` hardwired.
* `readsHw R`: the cells of a list of sponge reads with their values; `honestEval_answeredBy`:
  every read of the honest evaluation is answered by its functions;
  `consistent_readsHw_honestEval_iff`: the honest evaluation satisfies `hP`.
* `spongeEvalDistMap_eq_tableLaw`: for the honest evaluation `honestEval t π x` of any hash-query
  computation (key generation in the game), the experiment averaged over uniform `t` is the
  mixture, over the law of the honest results and reads, of runtime 1 with the honest cells
  hardwired; the rest of the game (the adversary with the signer's honest reads, which are read
  ports, adaptive in the run) is the program `y`. `spongeEvalDistMap_eq_avg_runtime1`,
  `spongeEvalDistMap_eq_tableLaw_sponge`: the average form, and programs over the sponge ports.
-/

open MeasureTheory Matrix
open scoped Kronecker ENNReal NNReal

universe u v w

namespace Quantum.Sponge

open Quantum

/-! ## Classical maps intertwined by a classical map -/

section clsMap

variable {B : Type} [Fintype B] [DecidableEq B]

/-- Two classical maps intertwined by a third. -/
theorem clsMap_mul_clsMap {pF pE p : B → Prop} [DecidablePred pF] [DecidablePred pE]
    [DecidablePred p] {φF φE φ : B → B} (hp : ∀ b, (p b ∧ pF (φ b)) ↔ (pE b ∧ p (φE b)))
    (hφ : ∀ b, p b → pF (φ b) → φF (φ b) = φ (φE b)) :
    clsMap pF φF * clsMap p φ = clsMap p φ * clsMap pE φE := by
  ext b'' b
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (φ b) ?_ (by simp),
    Finset.sum_eq_single (φE b) ?_ (by simp)]
  · simp only [clsMap, of_apply, and_true]
    by_cases h₁ : p b ∧ pF (φ b)
    · obtain ⟨h₂, h₃⟩ := (hp b).mp h₁
      rw [hφ b h₁.1 h₁.2]
      simp [h₁.1, h₁.2, h₂, h₃]
    · have h₂ : ¬ (pE b ∧ p (φE b)) := fun h ↦ h₁ ((hp b).mpr h)
      by_cases hb : p b
      · have hF : ¬ pF (φ b) := fun h ↦ h₁ ⟨hb, h⟩
        by_cases hE : pE b
        · have hE' : ¬ p (φE b) := fun h ↦ h₂ ⟨hE, h⟩
          simp [hF, hE']
        · simp [hF, hE]
      · by_cases hE : pE b
        · have hE' : ¬ p (φE b) := fun h ↦ h₂ ⟨hE, h⟩
          simp [hb, hE']
        · simp [hb, hE]
  · intro b' _ hb'
    simp [clsMap, hb']
  · intro b' _ hb'
    simp [clsMap, hb']

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- A classical map intertwines two table oracles that agree along it. -/
theorem tableOracle_mul_one_kronecker_clsMap (p : B → Prop) [DecidablePred p] (φ : B → B)
    {readE readF : B → A → Y} (h : ∀ b, p b → readF (φ b) = readE b) :
    tableOracle readF * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ clsMap p φ) =
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ clsMap p φ) * tableOracle readE := by
  ext ⟨m', b'⟩ ⟨m, b⟩
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (m, φ b) ?_ (by simp),
    Finset.sum_eq_single (oracleEquiv (readE b) m, b) ?_ (by simp)]
  · simp only [kroneckerMap_apply, tableOracle_apply, tableOracleEquiv_apply, clsMap, of_apply,
      Matrix.one_apply_eq, and_true, one_mul]
    by_cases hb : p b
    · simp only [h b hb, hb, true_and, ite_true, mul_one, Prod.mk.injEq, Matrix.one_apply]
      by_cases hb' : b' = φ b
      · simp only [hb', and_true]
        split_ifs <;> simp
      · simp [hb']
    · simp [hb]
  · rintro ⟨m₁, b₁⟩ - hne
    have h₀ : tableOracle readE (m₁, b₁) (m, b) = 0 := by
      rw [tableOracle_apply]
      exact ite_eq_right_iff.mpr fun h ↦ absurd h hne
    rw [h₀, mul_zero]
  · rintro ⟨m₁, b₁⟩ - hne
    rw [kroneckerMap_apply]
    by_cases hm : m₁ = m
    · subst hm
      have : ¬ (p b ∧ b₁ = φ b) := fun h ↦ hne (by rw [h.2])
      simp [clsMap, this]
    · simp [Matrix.one_apply_ne hm]

/-- Conjugating a basis state by a classical map. -/
theorem conj_clsMap_single (p : B → Prop) [DecidablePred p] (φ : B → B) (s : B) :
    MatrixMap.conj (clsMap p φ) (Matrix.single s s (1 : ℂ)) =
      if p s then Matrix.single (φ s) (φ s) 1 else 0 := by
  ext a a'
  rw [MatrixMap.conj_apply, Matrix.mul_apply, Finset.sum_eq_single s ?_ (by simp)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single s ?_ (by simp)]
    · by_cases hs : p s
      · by_cases ha : a = φ s
        · subst ha
          by_cases ha' : a' = φ s
          · subst ha'
            simp [clsMap, conjTranspose_apply, hs]
          · simp [clsMap, conjTranspose_apply, hs, ha', Ne.symm ha']
        · simp [clsMap, hs, ha, Ne.symm ha]
      · simp [clsMap, hs]
    · intro j _ hj
      simp [Ne.symm hj]
  · intro j _ hj
    rw [Matrix.mul_apply]
    refine mul_eq_zero_of_left (Finset.sum_eq_zero fun k _ ↦ ?_) _
    simp [Ne.symm hj]

end clsMap

/-! ## Moving the hardwired cells into the functions -/

section relabel

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

variable (X Z) in
/-- No hardwired cells. -/
def hwEmpty : Hw X Z :=
  (Database.empty, Database.empty, Database.empty)

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem overwrite_hwEmpty (t : (Z → X) × (X → Z) × (X → Z)) : overwrite (hwEmpty X Z) t = t :=
  rfl

variable (X Z M) in
/-- Relabel the hardwired cells `ω` of the classical register as no hardwired cells. -/
def hwRelabel (ω : Hw X Z) : Matrix (Unit × Hw X Z × M) (Unit × Hw X Z × M) ℂ :=
  clsMap (fun u : Unit × Hw X Z × M ↦ u.2.1 = ω) fun u ↦ (u.1, hwEmpty X Z, u.2.2)

/-- The relabelings resolve the identity. -/
theorem sum_conjTranspose_hwRelabel_mul_self :
    ∑ ω, (hwRelabel X Z M ω)ᴴ * hwRelabel X Z M ω = 1 := by
  ext s s''
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, hwRelabel, clsMap, of_apply]
  rw [Finset.sum_eq_single s.2.1 ?_ (by simp)]
  · rw [Finset.sum_eq_single ((s.1, hwEmpty X Z, s.2.2) : Unit × Hw X Z × M) ?_ (by simp)]
    · by_cases h : s = s''
      · subst h
        simp
      · simp [Matrix.one_apply_ne h]
        intro h₁ h₂
        exact h (Prod.ext (Subsingleton.elim _ _) (Prod.ext h₁.symm h₂))
    · intro s' _ hs'
      simp [hs']
  · intro ω _ hω
    refine Finset.sum_eq_zero fun s' _ ↦ ?_
    simp [Ne.symm hω]

variable [AddCommGroup X] [AddCommGroup Z]

/-- The relabeling of the cells `ω` intertwines the classical reads against `t` with those against
`overwrite ω t` without hardwired cells. -/
theorem hwRelabel_step_intertwine (t : (Z → X) × (X → Z) × (X → Z)) (W₀ : Hw X Z) (m₀ : M)
    (ω : Hw X Z) (i : (hwReadSpec X Z M).Port) (r : (hwReadSpec X Z M).Result i) :
    ((spongeFnReadRuntime X Z (overwrite ω t) (hwEmpty X Z) m₀).step i).branch r ∘ₗ
        (MatrixMap.conj (hwRelabel X Z M ω)).amplifyLeft ((hwReadSpec X Z M).In i) =
      (MatrixMap.conj (hwRelabel X Z M ω)).amplifyLeft ((hwReadSpec X Z M).Out i) ∘ₗ
        ((spongeFnReadRuntime X Z t W₀ m₀).step i).branch r := by
  rcases i with i | c
  · change MatrixMap.conj ((spongeFnHw X Z (overwrite ω t) (hwEmpty X Z) m₀).U i) ∘ₗ
        (MatrixMap.conj (hwRelabel X Z M ω)).amplifyLeft (spongeIn X Z i) =
      (MatrixMap.conj (hwRelabel X Z M ω)).amplifyLeft (spongeIn X Z i) ∘ₗ
        MatrixMap.conj ((spongeFnHw X Z t W₀ m₀).U i)
    rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
    congr 1
    cases i
    · exact tableOracle_mul_one_kronecker_clsMap _ _ fun b hb ↦ by
        change (overwrite ω t).1 = (overwrite b.2.1 t).1
        rw [hb]
    · exact tableOracle_mul_one_kronecker_clsMap _ _ fun b hb ↦ by
        change (overwrite ω t).2.1 = (overwrite b.2.1 t).2.1
        rw [hb]
    · exact tableOracle_mul_one_kronecker_clsMap _ _ fun b hb ↦ by
        change (overwrite ω t).2.2 = (overwrite b.2.1 t).2.2
        rw [hb]
  · have e₁ : ((spongeFnReadRuntime X Z (overwrite ω t) (hwEmpty X Z) m₀).step (.inr c)).branch r =
        MatrixMap.conj (fnReadKraus (overwrite ω t) c r) := rfl
    have e₂ : ((spongeFnReadRuntime X Z t W₀ m₀).step (.inr c)).branch r =
        MatrixMap.conj (fnReadKraus t c r) := rfl
    have key : fnReadKraus (overwrite ω t) c r *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwRelabel X Z M ω) =
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwRelabel X Z M ω) * fnReadKraus t c r := by
      cases c with
      | readH z upd =>
        change ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsMap (fun u : Unit × Hw X Z × M ↦
            u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 (overwrite ω t)).1 z))
            (fun u ↦ (u.1, u.2.1, upd r.2 r.1))) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwRelabel X Z M ω) =
          ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwRelabel X Z M ω) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ
            clsMap (fun u : Unit × Hw X Z × M ↦
              u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).1 z))
              (fun u ↦ (u.1, u.2.1, upd r.2 r.1)))
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, hwRelabel]
        exact congrArg _ (clsMap_mul_clsMap
          (fun b ↦ ⟨fun ⟨h₀, h₁, h₂⟩ ↦ ⟨⟨h₁, h₀ ▸ h₂⟩, h₀⟩, fun ⟨⟨h₁, h₂⟩, h₀⟩ ↦ ⟨h₀, h₁, h₀ ▸ h₂⟩⟩)
          fun _ _ _ ↦ rfl)
      | readK x upd =>
        change ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsMap (fun u : Unit × Hw X Z × M ↦
            u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 (overwrite ω t)).2.1 x))
            (fun u ↦ (u.1, u.2.1, upd r.2 r.1))) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwRelabel X Z M ω) =
          ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwRelabel X Z M ω) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ
            clsMap (fun u : Unit × Hw X Z × M ↦
              u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).2.1 x))
              (fun u ↦ (u.1, u.2.1, upd r.2 r.1)))
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, hwRelabel]
        exact congrArg _ (clsMap_mul_clsMap
          (fun b ↦ ⟨fun ⟨h₀, h₁, h₂⟩ ↦ ⟨⟨h₁, h₀ ▸ h₂⟩, h₀⟩, fun ⟨⟨h₁, h₂⟩, h₀⟩ ↦ ⟨h₀, h₁, h₀ ▸ h₂⟩⟩)
          fun _ _ _ ↦ rfl)
      | readK' x upd =>
        change ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsMap (fun u : Unit × Hw X Z × M ↦
            u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 (overwrite ω t)).2.2 x))
            (fun u ↦ (u.1, u.2.1, upd r.2 r.1))) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwRelabel X Z M ω) =
          ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwRelabel X Z M ω) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ
            clsMap (fun u : Unit × Hw X Z × M ↦
              u.2.2 = r.2 ∧ r.1 = some ((overwrite u.2.1 t).2.2 x))
              (fun u ↦ (u.1, u.2.1, upd r.2 r.1)))
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, hwRelabel]
        exact congrArg _ (clsMap_mul_clsMap
          (fun b ↦ ⟨fun ⟨h₀, h₁, h₂⟩ ↦ ⟨⟨h₁, h₀ ▸ h₂⟩, h₀⟩, fun ⟨⟨h₁, h₂⟩, h₀⟩ ↦ ⟨h₀, h₁, h₀ ▸ h₂⟩⟩)
          fun _ _ _ ↦ rfl)
    have keyM : MatrixMap.conj (fnReadKraus (overwrite ω t) c r) ∘ₗ
        MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwRelabel X Z M ω) =
        MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwRelabel X Z M ω) ∘ₗ
          MatrixMap.conj (fnReadKraus t c r) := by
      rw [← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
      exact congrArg MatrixMap.conj key
    rw [e₁, e₂, MatrixMap.amplifyLeft_conj]
    exact keyM

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **Hardwired cells against fixed functions are the overwritten functions.** Classical reads
against `t` with the hardwired cells `W₀` have the law of classical reads against
`overwrite W₀ t` without hardwired cells. -/
theorem evalDistMap_spongeFnReadRuntime_overwrite {γ : Type*} [MeasurableSpace γ]
    (t : (Z → X) × (X → Z) × (X → Z)) (W₀ : Hw X Z) (m₀ : M) (I : L.Interp)
    (x : QuantumComp L (hwReadSpec X Z M) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (spongeFnReadRuntime X Z t W₀ m₀).evalDistMap I x ρ f =
      (spongeFnReadRuntime X Z (overwrite W₀ t) (hwEmpty X Z) m₀).evalDistMap I x ρ f := by
  refine (evalDistMap_eq_sum_of_rows (spongeFnReadRuntime X Z t W₀ m₀)
    (fun ω ↦ spongeFnReadRuntime X Z (overwrite ω t) (hwEmpty X Z) m₀)
    (fun ω ↦ hwRelabel X Z M ω) (fun ω ↦ if ω = W₀ then 1 else 0)
    (by exact sum_conjTranspose_hwRelabel_mul_self)
    (fun ω i r ↦ hwRelabel_step_intertwine t W₀ m₀ ω i r) (fun ω ↦ ?_) I x ρ f).trans ?_
  · change MatrixMap.conj (hwRelabel X Z M ω) (SubState.basis (((), W₀, m₀) :
        Unit × Hw X Z × M)).matrix =
      (((if ω = W₀ then 1 else 0 : ℝ≥0) : ℝ) : ℂ) •
        (SubState.basis (((), hwEmpty X Z, m₀) : Unit × Hw X Z × M)).matrix
    rw [SubState.matrix_basis, SubState.matrix_basis, hwRelabel, conj_clsMap_single]
    by_cases hω : ω = W₀
    · subst hω
      simp
    · simp [hω, Ne.symm hω]
  · rw [Finset.sum_eq_single W₀ (fun ω _ hω ↦ by simp [hω]) (by simp)]
    simp

end relabel

/-! ## The law of the honest data -/

section law

variable {T β : Type*} [Fintype T] [DecidableEq β]

/-- **The law of the honest data**: the probability that uniform `t` gives the data `b`. -/
noncomputable def tableLaw (P : T → β) (b : β) : ℝ≥0∞ :=
  ((Finset.univ.filter fun t ↦ P t = b).card : ℝ≥0∞) * (Fintype.card T : ℝ≥0∞)⁻¹

/-- The law is a probability distribution on the values of the data. -/
theorem sum_tableLaw [Nonempty T] (P : T → β) :
    ∑ b ∈ Finset.univ.image P, tableLaw P b = 1 := by
  simp only [tableLaw, ← Finset.sum_mul]
  rw [← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter, Finset.filter_true_of_mem
    fun t _ ↦ Finset.mem_image_of_mem P (Finset.mem_univ t), Finset.card_univ]
  exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

/-- **Lazy sampling.** If the data `P t` is determined by the values of `t` on its cells
(`C (P t) t'` exactly when `P t' = P t`), averaging over uniform `t` is averaging over the law of
the data, then over uniform `t` among those whose cells agree with it. -/
theorem sum_uniform_eq_sum_tableLaw {V : Type*} [AddCommMonoid V] [Module ℝ≥0∞ V] (P : T → β)
    (C : β → T → Prop) [∀ b, DecidablePred (C b)] (hP : ∀ t t', C (P t) t' ↔ P t' = P t)
    (G : T → β → V) :
    ∑ t, (Fintype.card T : ℝ≥0∞)⁻¹ • G t (P t) =
      ∑ b ∈ Finset.univ.image P, tableLaw P b •
        ∑ t ∈ Finset.univ.filter (C b), ((Finset.univ.filter (C b)).card : ℝ≥0∞)⁻¹ • G t b := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := P) (t := Finset.univ.image P)
    fun t _ ↦ Finset.mem_image_of_mem P (Finset.mem_univ t)]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  obtain ⟨t₀, -, rfl⟩ := Finset.mem_image.mp hb
  have hC : Finset.univ.filter (C (P t₀)) = Finset.univ.filter fun t ↦ P t = P t₀ := by
    ext t
    simp [hP]
  have hn : ((Finset.univ.filter fun t ↦ P t = P t₀).card : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨t₀, by simp⟩)
  rw [hC, tableLaw, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [(Finset.mem_filter.mp ht).2, smul_smul, mul_comm _ (Fintype.card T : ℝ≥0∞)⁻¹, mul_assoc,
    ENNReal.mul_inv_cancel hn (ENNReal.natCast_ne_top _), mul_one]

/-- A function of the data, averaged over uniform `t`, is averaged over the law of the data. -/
theorem sum_uniform_comp_eq_sum_tableLaw {V : Type*} [AddCommMonoid V] [Module ℝ≥0∞ V]
    (P : T → β) (H : β → V) :
    ∑ t, (Fintype.card T : ℝ≥0∞)⁻¹ • H (P t) =
      ∑ b ∈ Finset.univ.image P, tableLaw P b • H b := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := P) (t := Finset.univ.image P)
    fun t _ ↦ Finset.mem_image_of_mem P (Finset.mem_univ t)]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_congr rfl fun t ht ↦ by rw [(Finset.mem_filter.mp ht).2], Finset.sum_const,
    tableLaw, mul_smul, Nat.cast_smul_eq_nsmul]

end law

/-! ## G2 is runtime 1 -/

section runtime

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] {M : Type} [Fintype M] [DecidableEq M]
  {β : Type*} [DecidableEq β]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **G2 is runtime 1, with read ports.** Let the data `P t` determine its cells `hw (P t)`:
functions `t'` agree with `hw (P t)` exactly when `P t' = P t`. A program `y (P t)` over the
sponge and read ports, chosen by the data and run against the classical reads of `t`, averaged
over uniform `t`, has the law of the `tableLaw P`-mixture over the data `b` of runtime 1 started
with the cells `hw b` hardwired, running `y b`. -/
theorem evalDistMap_avg_eq_tableLaw {γ : Type*} [MeasurableSpace γ]
    (P : (Z → X) × (X → Z) × (X → Z) → β) (hw : β → Hw X Z)
    (hP : ∀ t t', Consistent (hw (P t)) t' ↔ P t' = P t) (m₀ : M) (I : L.Interp)
    (y : β → QuantumComp L (hwReadSpec X Z M) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    ∑ t, (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ •
        (spongeFnReadRuntime X Z t (hwEmpty X Z) m₀).evalDistMap I (y (P t)) ρ f =
      ∑ b ∈ Finset.univ.image P, tableLaw P b •
        (spongeHardwiredReadRuntime X Z (hw b) m₀).evalDistMap I (y b) ρ f := by
  rw [sum_uniform_eq_sum_tableLaw P (fun b ↦ Consistent (hw b)) hP
    fun t b ↦ (spongeFnReadRuntime X Z t (hwEmpty X Z) m₀).evalDistMap I (y b) ρ f]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [read_port_eq_classical_read]
  simp only [evalDistMap_spongeFnReadRuntime_overwrite _ (hw b)]
  rw [sum_overwrite_eq_sum_consistent (hw b)
    fun t ↦ (spongeFnReadRuntime X Z t (hwEmpty X Z) m₀).evalDistMap I (y b) ρ f]

/-- **G2 is runtime 1, sponge ports only.** As `evalDistMap_avg_eq_tableLaw`, for programs over
the sponge ports run against the oracles of `t`. -/
theorem evalDistMap_avg_eq_tableLaw_sponge {γ : Type*} [MeasurableSpace γ]
    (P : (Z → X) × (X → Z) × (X → Z) → β) (hw : β → Hw X Z)
    (hP : ∀ t t', Consistent (hw (P t)) t' ↔ P t' = P t) (m₀ : M) (I : L.Interp)
    (x : β → QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    ∑ t, (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ •
        (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap I (x (P t)) ρ f =
      ∑ b ∈ Finset.univ.image P, tableLaw P b •
        (spongeHardwiredReadRuntime X Z (hw b) m₀).evalDistMap I (x b).liftOrdinary ρ f := by
  rw [sum_uniform_eq_sum_tableLaw P (fun b ↦ Consistent (hw b)) hP
    fun t b ↦ (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap I (x b) ρ f]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [evalDistMap_hardwired_eq_avg_consistent]

omit [DecidableEq β] in
/-- **G2 is runtime 1, as an average over `t`**: `evalDistMap_avg_eq_tableLaw` with the mixture
over the law of the data written as the average over uniform `t` of runtime 1 started with the
cells of `P t` hardwired. -/
theorem evalDistMap_avg_eq_avg_runtime1 {γ : Type*} [MeasurableSpace γ]
    (P : (Z → X) × (X → Z) × (X → Z) → β) (hw : β → Hw X Z)
    (hP : ∀ t t', Consistent (hw (P t)) t' ↔ P t' = P t) (m₀ : M) (I : L.Interp)
    (y : β → QuantumComp L (hwReadSpec X Z M) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    ∑ t, (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ •
        (spongeFnReadRuntime X Z t (hwEmpty X Z) m₀).evalDistMap I (y (P t)) ρ f =
      ∑ t, (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ •
        (spongeHardwiredReadRuntime X Z (hw (P t)) m₀).evalDistMap I (y (P t)) ρ f := by
  classical
  rw [evalDistMap_avg_eq_tableLaw P hw hP m₀ I y ρ f, sum_uniform_comp_eq_sum_tableLaw P
    fun b ↦ (spongeHardwiredReadRuntime X Z (hw b) m₀).evalDistMap I (y b) ρ f]

end runtime

end Quantum.Sponge

namespace Quantum.Xmss

open Quantum Quantum.Sponge

/-! ## The cells of the honest reads -/

/-- The value a read gives to cell `z` of `h`. -/
def _root_.Quantum.Sponge.SpongeRead.atH {X Z : Type} [DecidableEq Z] (z : Z) :
    SpongeRead X Z → Option X
  | .h z' a => if z' = z then some a else none
  | _ => none

/-- The value a read gives to cell `x` of `k`. -/
def _root_.Quantum.Sponge.SpongeRead.atK {X Z : Type} [DecidableEq X] (x : X) :
    SpongeRead X Z → Option Z
  | .k x' a => if x' = x then some a else none
  | _ => none

/-- The value a read gives to cell `x` of `k'`. -/
def _root_.Quantum.Sponge.SpongeRead.atK' {X Z : Type} [DecidableEq X] (x : X) :
    SpongeRead X Z → Option Z
  | .k' x' a => if x' = x then some a else none
  | _ => none

/-- **The cells of a list of reads**, with the values read (the first read of each cell). -/
def readsHw (R : List (SpongeRead X Z)) : Hw X Z :=
  (fun z ↦ R.findSome? (SpongeRead.atH z), fun x ↦ R.findSome? (SpongeRead.atK x),
    fun x ↦ R.findSome? (SpongeRead.atK' x))

/-- Functions agree with hardwired cells when they have their values. -/
theorem consistent_iff_forall {W : Hw X Z} {t : SpongeKeys X Z} :
    Consistent W t ↔ (∀ z a, W.1 z = some a → t.1 z = a) ∧
      (∀ x a, W.2.1 x = some a → t.2.1 x = a) ∧ (∀ x a, W.2.2 x = some a → t.2.2 x = a) := by
  constructor
  · intro hc
    refine ⟨fun z a ha ↦ ?_, fun x a ha ↦ ?_, fun x a ha ↦ ?_⟩
    · have h := congrFun (congrArg Prod.fst hc) z
      change (W.1 z).getD (t.1 z) = t.1 z at h
      rw [ha] at h
      exact h.symm
    · have h := congrFun (congrArg (fun t : SpongeKeys X Z ↦ t.2.1) hc) x
      change (W.2.1 x).getD (t.2.1 x) = t.2.1 x at h
      rw [ha] at h
      exact h.symm
    · have h := congrFun (congrArg (fun t : SpongeKeys X Z ↦ t.2.2) hc) x
      change (W.2.2 x).getD (t.2.2 x) = t.2.2 x at h
      rw [ha] at h
      exact h.symm
  · rintro ⟨hh, hk, hk'⟩
    refine Prod.ext (funext fun z ↦ ?_) (Prod.ext (funext fun x ↦ ?_) (funext fun x ↦ ?_))
    · change (W.1 z).getD (t.1 z) = t.1 z
      cases hw : W.1 z with
      | none => rfl
      | some a => exact (hh z a hw).symm
    · change (W.2.1 x).getD (t.2.1 x) = t.2.1 x
      cases hw : W.2.1 x with
      | none => rfl
      | some a => exact (hk x a hw).symm
    · change (W.2.2 x).getD (t.2.2 x) = t.2.2 x
      cases hw : W.2.2 x with
      | none => rfl
      | some a => exact (hk' x a hw).symm

/-- **The cells of reads answered by `t₀`**: functions agree with them exactly when they answer
every read. -/
theorem consistent_readsHw_iff {R : List (SpongeRead X Z)} {t₀ : SpongeKeys X Z}
    (h₀ : ∀ e ∈ R, e.AnsweredBy t₀) {t : SpongeKeys X Z} :
    Consistent (readsHw R) t ↔ ∀ e ∈ R, e.AnsweredBy t := by
  rw [consistent_iff_forall]
  constructor
  · rintro ⟨hh, hk, hk'⟩ e he
    cases e with
    | h z a =>
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
        (List.findSome?_isSome_iff.mpr ⟨_, he, by simp [SpongeRead.atH]⟩ :
          (R.findSome? (SpongeRead.atH z)).isSome)
      obtain ⟨e', he', he'a⟩ := List.exists_of_findSome?_eq_some ha'
      cases e' with
      | h z' b =>
        simp only [SpongeRead.atH, Option.ite_none_right_eq_some, Option.some.injEq] at he'a
        obtain ⟨rfl, rfl⟩ := he'a
        exact Eq.trans (hh _ _ ha') (Eq.trans (Eq.symm (h₀ _ he')) (h₀ _ he))
      | k _ _ => simp [SpongeRead.atH] at he'a
      | k' _ _ => simp [SpongeRead.atH] at he'a
    | k x a =>
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
        (List.findSome?_isSome_iff.mpr ⟨_, he, by simp [SpongeRead.atK]⟩ :
          (R.findSome? (SpongeRead.atK x)).isSome)
      obtain ⟨e', he', he'a⟩ := List.exists_of_findSome?_eq_some ha'
      cases e' with
      | k x' b =>
        simp only [SpongeRead.atK, Option.ite_none_right_eq_some, Option.some.injEq] at he'a
        obtain ⟨rfl, rfl⟩ := he'a
        exact Eq.trans (hk _ _ ha') (Eq.trans (Eq.symm (h₀ _ he')) (h₀ _ he))
      | h _ _ => simp [SpongeRead.atK] at he'a
      | k' _ _ => simp [SpongeRead.atK] at he'a
    | k' x a =>
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
        (List.findSome?_isSome_iff.mpr ⟨_, he, by simp [SpongeRead.atK']⟩ :
          (R.findSome? (SpongeRead.atK' x)).isSome)
      obtain ⟨e', he', he'a⟩ := List.exists_of_findSome?_eq_some ha'
      cases e' with
      | k' x' b =>
        simp only [SpongeRead.atK', Option.ite_none_right_eq_some, Option.some.injEq] at he'a
        obtain ⟨rfl, rfl⟩ := he'a
        exact Eq.trans (hk' _ _ ha') (Eq.trans (Eq.symm (h₀ _ he')) (h₀ _ he))
      | h _ _ => simp [SpongeRead.atK'] at he'a
      | k _ _ => simp [SpongeRead.atK'] at he'a
  · intro h
    refine ⟨fun z a ha ↦ ?_, fun x a ha ↦ ?_, fun x a ha ↦ ?_⟩
    · obtain ⟨e, he, hea⟩ := List.exists_of_findSome?_eq_some ha
      cases e with
      | h z' b =>
        simp only [SpongeRead.atH, Option.ite_none_right_eq_some, Option.some.injEq] at hea
        obtain ⟨rfl, rfl⟩ := hea
        exact h _ he
      | k _ _ => simp [SpongeRead.atH] at hea
      | k' _ _ => simp [SpongeRead.atH] at hea
    · obtain ⟨e, he, hea⟩ := List.exists_of_findSome?_eq_some ha
      cases e with
      | k x' b =>
        simp only [SpongeRead.atK, Option.ite_none_right_eq_some, Option.some.injEq] at hea
        obtain ⟨rfl, rfl⟩ := hea
        exact h _ he
      | h _ _ => simp [SpongeRead.atK] at hea
      | k' _ _ => simp [SpongeRead.atK] at hea
    · obtain ⟨e, he, hea⟩ := List.exists_of_findSome?_eq_some ha
      cases e with
      | k' x' b =>
        simp only [SpongeRead.atK', Option.ite_none_right_eq_some, Option.some.injEq] at hea
        obtain ⟨rfl, rfl⟩ := hea
        exact h _ he
      | h _ _ => simp [SpongeRead.atK'] at hea
      | k _ _ => simp [SpongeRead.atK'] at hea

/-! ## The honest evaluation determines its cells -/

variable (π : Equiv.Perm (X × Z))

/-- Every read of the sponge on a message is answered by its functions. -/
theorem spongeReads_answeredBy (t : SpongeKeys X Z) (msg : List X) :
    ∀ e ∈ spongeReads π t.1 t.2.1 t.2.2 msg, e.AnsweredBy t := by
  induction msg using List.reverseRecOn with
  | nil => simp [spongeReads_nil]
  | append_singleton msg b ih =>
    intro e he
    rw [spongeReads_append_singleton, List.mem_append] at he
    rcases he with he | he
    · exact ih e he
    · simp only [roundReads, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> rfl

/-- Every read of the honest evaluation is answered by its functions. -/
theorem honestEval_answeredBy (t : SpongeKeys X Z) {α : Type}
    (x : OracleComp LeanXmss.HashSpec α) : ∀ e ∈ (honestEval t π x).2, e.AnsweredBy t := by
  intro e he
  rw [snd_honestEval, List.mem_flatMap] at he
  obtain ⟨input, -, he⟩ := he
  exact spongeReads_answeredBy π t _ e he

/-- **The honest evaluation is determined by the values of its cells**: functions agree with the
cells it reads under `t` exactly when they give the same evaluation and reads. -/
theorem consistent_readsHw_honestEval_iff {α : Type} (x : OracleComp LeanXmss.HashSpec α)
    (t t' : SpongeKeys X Z) :
    Consistent (readsHw (honestEval t π x).2) t' ↔ honestEval t' π x = honestEval t π x := by
  rw [consistent_readsHw_iff (honestEval_answeredBy π t x)]
  refine ⟨honestEval_congr π x, fun h ↦ ?_⟩
  rw [← h]
  exact honestEval_answeredBy π t' x

/-! ## G2 is runtime 1 for the honest evaluation -/

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {W : QReg → Type w}
  {A : QReg}

/-- **`spongeEvalDistMap_eq_tableLaw`: G2 is runtime 1.** Let the challenger first evaluate the
hash-query computation `x` honestly against `t` (key generation in the game: its result and its
reads, `honestEval t π x`), then run the program `y` chosen by that evaluation, over the sponge
ports and the read ports (the adversary, with the signer's honest reads as read ports, chosen
adaptively during the run), against the classical reads of `t`. Averaged over uniform `t`, this
has the law of the mixture, over the law `tableLaw` of the honest evaluation, of runtime 1
started with the honest cells and their values hardwired (`readsHw`), running `y`. -/
theorem spongeEvalDistMap_eq_tableLaw {γ : Type*} [MeasurableSpace γ] {α : Type} [DecidableEq α]
    (x : OracleComp LeanXmss.HashSpec α) (m₀ : M) (I : L.Interp)
    (y : α × List (SpongeRead X Z) → QuantumComp L (hwReadSpec X Z M) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
        (spongeFnReadRuntime X Z t (hwEmpty X Z) m₀).evalDistMap I (y (honestEval t π x)) ρ f =
      ∑ b ∈ Finset.univ.image (fun t ↦ honestEval t π x),
        tableLaw (fun t ↦ honestEval t π x) b •
          (spongeHardwiredReadRuntime X Z (readsHw b.2) m₀).evalDistMap I (y b) ρ f :=
  evalDistMap_avg_eq_tableLaw (fun t ↦ honestEval t π x) (fun b ↦ readsHw b.2)
    (consistent_readsHw_honestEval_iff π x) m₀ I y ρ f

/-- **G2 is runtime 1, as an average over `t`**: `spongeEvalDistMap_eq_tableLaw` with the mixture
written as the average over uniform `t` of runtime 1 started with the honest cells of `t`
hardwired. -/
theorem spongeEvalDistMap_eq_avg_runtime1 {γ : Type*} [MeasurableSpace γ] {α : Type}
    (x : OracleComp LeanXmss.HashSpec α) (m₀ : M) (I : L.Interp)
    (y : α × List (SpongeRead X Z) → QuantumComp L (hwReadSpec X Z M) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
        (spongeFnReadRuntime X Z t (hwEmpty X Z) m₀).evalDistMap I (y (honestEval t π x)) ρ f =
      ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
        (spongeHardwiredReadRuntime X Z (readsHw (honestEval t π x).2) m₀).evalDistMap I
          (y (honestEval t π x)) ρ f :=
  evalDistMap_avg_eq_avg_runtime1 (fun t ↦ honestEval t π x) (fun b ↦ readsHw b.2)
    (consistent_readsHw_honestEval_iff π x) m₀ I y ρ f

/-- **G2 is runtime 1, sponge ports only**: as `spongeEvalDistMap_eq_tableLaw` for a program over
the sponge ports (no further honest reads), run against the oracles of `t`. -/
theorem spongeEvalDistMap_eq_tableLaw_sponge {γ : Type*} [MeasurableSpace γ] {α : Type}
    [DecidableEq α] (x : OracleComp LeanXmss.HashSpec α) (m₀ : M) (I : L.Interp)
    (y : α × List (SpongeRead X Z) → QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
        (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap I (y (honestEval t π x)) ρ f =
      ∑ b ∈ Finset.univ.image (fun t ↦ honestEval t π x),
        tableLaw (fun t ↦ honestEval t π x) b •
          (spongeHardwiredReadRuntime X Z (readsHw b.2) m₀).evalDistMap I (y b).liftOrdinary ρ f :=
  evalDistMap_avg_eq_tableLaw_sponge (fun t ↦ honestEval t π x) (fun b ↦ readsHw b.2)
    (consistent_readsHw_honestEval_iff π x) m₀ I y ρ f

end Quantum.Xmss

end
