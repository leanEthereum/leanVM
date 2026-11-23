module

public import Quantum.Xmss.Hybrid.GradedMasked

@[expose] public section

/-!
# Lazy sampling of template programs

A template program (`Quantum.Xmss.Assembly.tmplSpec`) reads hidden values `v : (s : S) → D s`
through its reveal ports and its program ports. Realized at `v` (`realizeT`) and averaged over
uniform `v`, its run against runtime 2 with record ports (`runtimeR`, empty initial label) is the
run of the template itself against the *sampled runtime* (`sampledRuntime`).

**The sampled runtime.** Its register is `runtimeR`'s with a store of sampled values
(`Store D`, a partial function of the coordinates; `SReg`), started empty. A reveal of `T` from
the label `L` samples uniform values at the new coordinates `T \ L` (amplitude `cAmp`, outcomes
agreeing with the store on `T ∩ L`: `revAmp`), stores them (`swapIn`), records `T` and returns
the stored values on `T` (`revKS`); a program port is realized at the stored values (`fill`); the
sponge and read ports are runtime 2's. Every other port acts on runtime 2's register controlled
by the store (`ctrlK`).

**Proof.** The run at `v` embeds into the sampled register by `embV v` (the store of `v` on the
label: `storeOn`, isometry `embK`, map `embM`). On the sum over `v` of the embeddings of a lazy
family (ViewBy's `Lazy` in the memory label), every step of the sampled runtime is the sum of the
embeddings of the template runtime's steps (`sampStep_branch_sum_embM`): runtime 2's ports read
the store only where it agrees with `v` (a program port's coordinates are recorded, `Disc`; a
read keeps the label, `KeepsLab`), and a reveal's fresh values at `T \ L` are the average over
`v` there, on which the family does not depend (`sum_ite_restrictTo_eq`, `conj_revKS_sum_embM`).
By induction on the template (`run_sampled_sum_embM`), and since every embedding of the initial
register is the sampled runtime's (`embM_init`) and keeps the trace (`trace_embM`):

* `branch_run_sampled`: the run of the sampled runtime is the average over `v` of the embedded
  realized runs, leaf by leaf;
* `uavg_trace_jointPost_realizeT_eq_sampled`: the weight of every leaf is the average of its
  weights in the realized runs;
* `uavg_realizeT_outcome_eq_sampled`: the distribution of every observation of the leaf.

Hypotheses: the template reveals before it programs (`Disc y ∅`) and its reads keep the memory
label (`KeepsLab y`); leanXMSS's game satisfies both (`disc_gameT`, `keepsLab_gameT`). The initial
label is empty, the initial inner memory `m₀` arbitrary.
-/

open Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v w

namespace Quantum.Sig

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid Quantum.Xmss.Assembly

/-! ## Stores of sampled values -/

section store

variable {S : Type} [DecidableEq S] {D : S → Type}

/-- The sampled values: a value at some coordinates, none at the others. -/
abbrev Store (D : S → Type) : Type :=
  (s : S) → Option (D s)

/-- The store of the hidden values `v` on the coordinates `T`. -/
def storeOn (T : Finset S) (v : (s : S) → D s) : Store D :=
  fun s ↦ if s ∈ T then some (v s) else none

/-- Exchange `none` and `some a`, keep the other values: an involution. -/
def swapOpt {α : Type} [DecidableEq α] (a : α) : Option α → Option α
  | none => some a
  | some x => if x = a then none else some x

theorem swapOpt_swapOpt {α : Type} [DecidableEq α] (a : α) (o : Option α) :
    swapOpt a (swapOpt a o) = o := by
  cases o with
  | none => simp [swapOpt]
  | some x =>
    by_cases h : x = a
    · subst h
      simp [swapOpt]
    · simp [swapOpt, h]

variable [∀ s, DecidableEq (D s)]

/-- A reveal of `T` from the label `L` stores the values `w` at the new coordinates `T \ L`,
exchanging them with `none` so that the map is injective. -/
def swapIn (T L : Finset S) (w : RevealVals D T) (σ : Store D) : Store D :=
  fun s ↦ if h : s ∈ T ∧ s ∉ L then swapOpt (w ⟨s, h.1⟩) (σ s) else σ s

theorem swapIn_swapIn (T L : Finset S) (w : RevealVals D T) (σ : Store D) :
    swapIn T L w (swapIn T L w σ) = σ := by
  funext s
  by_cases h : s ∈ T ∧ s ∉ L
  · simp [swapIn, h, swapOpt_swapOpt]
  · simp only [swapIn, h, dite_false]

/-- The hidden values `v` with the values `w` at the coordinates `T \ L`. -/
def override (T L : Finset S) (w : RevealVals D T) (v : (s : S) → D s) : (s : S) → D s :=
  fun s ↦ if h : s ∈ T ∧ s ∉ L then w ⟨s, h.1⟩ else v s

/-- Revealing `T` from the store of `v` on `L` gives the store on `L ∪ T` of `v` overridden by the
revealed values. -/
theorem swapIn_storeOn (T L : Finset S) (w : RevealVals D T) (v : (s : S) → D s) :
    swapIn T L w (storeOn L v) = storeOn (L ∪ T) (override T L w v) := by
  funext s
  by_cases h : s ∈ T ∧ s ∉ L
  · obtain ⟨hT, hL⟩ := h
    simp [swapIn, storeOn, override, hT, hL, swapOpt]
  · by_cases hL : s ∈ L
    · simp [swapIn, storeOn, override, hL]
    · have hT : s ∉ T := fun hT ↦ h ⟨hT, hL⟩
      simp [swapIn, storeOn, hL, hT]

variable [∀ s, Nonempty (D s)]

/-- The values of a store, a fixed default where it holds none. -/
noncomputable def fill (σ : Store D) : (s : S) → D s :=
  fun s ↦ (σ s).getD (Classical.arbitrary _)

omit [∀ s, DecidableEq (D s)] in
theorem fill_storeOn_of_mem {T : Finset S} {v : (s : S) → D s} {s : S} (hs : s ∈ T) :
    fill (storeOn T v) s = v s := by
  simp [fill, storeOn, hs]

end store

/-! ## The sampled register -/

section register

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]

/-- Decidable equality of stores, named so that instance search stays small. -/
instance instDecidableEqStore : DecidableEq (Store D) :=
  inferInstanceAs (DecidableEq ((s : S) → Option (D s)))

/-- Stores are finite. -/
instance instFintypeStore : Fintype (Store D) :=
  inferInstanceAs (Fintype ((s : S) → Option (D s)))

variable (X Z S D M) in
/-- The register of the sampled runtime: that of `runtimeR` and a store. -/
abbrev SReg : Type :=
  HwReg X Z (Finset S × M) × Store D

/-- Decidable equality of the sampled register. -/
instance instDecidableEqSReg : DecidableEq (SReg X Z S D M) :=
  inferInstanceAs (DecidableEq (HwReg X Z (Finset S × M) × Store D))

/-- The sampled register is finite. -/
instance instFintypeSReg : Fintype (SReg X Z S D M) :=
  inferInstanceAs (Fintype (HwReg X Z (Finset S × M) × Store D))

omit [∀ s, DecidableEq (D s)] [DecidableEq M] in
/-- A sum over the sampled register beside `β`, as a sum over `runtimeR`'s register beside `β`
and over the stores. -/
theorem sum_sReg {β : Type} [Fintype β] {E : Type} [AddCommMonoid E]
    (f : β × SReg X Z S D M → E) :
    ∑ z, f z = ∑ q : β × HwReg X Z (Finset S × M), ∑ τ : Store D, f (q.1, (q.2, τ)) := by
  rw [← (Equiv.prodAssoc β (HwReg X Z (Finset S × M)) (Store D)).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The register of `runtimeR` at the hidden values `v`, with the store of `v` on its label. -/
def embV (v : (s : S) → D s) (d : HwReg X Z (Finset S × M)) : SReg X Z S D M :=
  (d, storeOn d.2.2.1 v)

/-- The isometry of `embV`. -/
def embK (v : (s : S) → D s) : Matrix (SReg X Z S D M) (HwReg X Z (Finset S × M)) ℂ :=
  Matrix.of fun p d ↦ if p = embV v d then 1 else 0

theorem embK_isometry (v : (s : S) → D s) :
    (embK (X := X) (Z := Z) (M := M) v)ᴴ * embK (X := X) (Z := Z) (M := M) v = 1 := by
  ext d d'
  simp only [mul_apply, conjTranspose_apply, embK, of_apply, one_apply]
  rw [Finset.sum_eq_single (embV v d)]
  · by_cases h : d = d'
    · subst h
      simp
    · have he : embV (X := X) (Z := Z) (M := M) v d ≠ embV v d' :=
        fun he ↦ h (congrArg Prod.fst he)
      simp [he, h]
  · intro p _ hp
    simp [hp]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-- Kraus operators controlled by the store: `K σ` on the store `σ`, which stays. -/
def ctrlK (K : Store D → Matrix (β × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ) :
    Matrix (β × SReg X Z S D M) (α × SReg X Z S D M) ℂ :=
  Matrix.of fun x y ↦ if x.2.2 = y.2.2 then K y.2.2 (x.1, x.2.1) (y.1, y.2.1) else 0

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [DecidableEq S]
  [∀ s, Fintype (D s)] [Fintype M] [DecidableEq M] [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] in
theorem conjTranspose_ctrlK
    (K : Store D → Matrix (β × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ) :
    (ctrlK K)ᴴ = ctrlK fun σ ↦ (K σ)ᴴ := by
  ext x y
  simp only [conjTranspose_apply, ctrlK, of_apply]
  by_cases h : x.2.2 = y.2.2
  · simp only [h, ↓reduceIte]
  · simp only [h, Ne.symm h, ↓reduceIte, star_zero]

omit [Fintype α] [DecidableEq α] [DecidableEq β] [Fintype γ] [DecidableEq γ] [DecidableEq M] in
theorem ctrlK_mul_ctrlK
    (K : Store D → Matrix (γ × HwReg X Z (Finset S × M)) (β × HwReg X Z (Finset S × M)) ℂ)
    (K' : Store D → Matrix (β × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ) :
    ctrlK K * ctrlK K' = ctrlK fun σ ↦ K σ * K' σ := by
  ext x y
  simp only [mul_apply, ctrlK, of_apply]
  rw [sum_sReg]
  by_cases h : x.2.2 = y.2.2
  · simp only [h, ↓reduceIte]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Finset.sum_eq_single y.2.2]
    · simp
    · intro τ _ hτ
      simp [hτ]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero fun q _ ↦ Finset.sum_eq_zero fun τ _ ↦ ?_
    by_cases hτ : τ = y.2.2
    · simp [hτ, h]
    · simp [hτ]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [DecidableEq S]
  [∀ s, Fintype (D s)] [Fintype M] [DecidableEq M] [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] in
theorem sum_ctrlK {ι : Type} [Fintype ι]
    (K : ι → Store D → Matrix (β × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ) :
    ∑ r, ctrlK (K r) = ctrlK fun σ ↦ ∑ r, K r σ := by
  ext x y
  simp only [Matrix.sum_apply, ctrlK, of_apply]
  split_ifs <;> simp

omit [∀ s, Fintype (D s)] [Fintype M] [Fintype α] in
theorem ctrlK_one :
    ctrlK (fun _ ↦ (1 : Matrix (α × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ)) =
      (1 : Matrix (α × SReg X Z S D M) (α × SReg X Z S D M) ℂ) := by
  ext ⟨a, d, σ⟩ ⟨a', d', σ'⟩
  simp only [ctrlK, of_apply, one_apply, Prod.mk.injEq]
  by_cases h : σ = σ'
  · subst h
    simp
  · simp [h]

omit [Fintype α] [DecidableEq β] in
/-- **Completeness of controlled Kraus operators.** -/
theorem sum_conjTranspose_ctrlK_mul_self {ι : Type} [Fintype ι]
    (K : ι → Store D → Matrix (β × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ)
    (hK : ∀ σ, ∑ r, (K r σ)ᴴ * K r σ = 1) :
    ∑ r, (ctrlK (K r))ᴴ * ctrlK (K r) = 1 := by
  simp only [conjTranspose_ctrlK, ctrlK_mul_ctrlK]
  rw [sum_ctrlK]
  simp only [hK]
  exact ctrlK_one

end register

/-! ## The sampled runtime -/

section sampled

/-- Two partial maps with amplitudes: the Gram entry vanishes unless both are defined and agree. -/
theorem sum_star_ite_mul_ite {ι κ : Type} [Fintype ι] [DecidableEq ι] (P : κ → Prop)
    [DecidablePred P] (f : κ → ι) (a : κ → ℂ) (k₁ k₂ : κ) :
    ∑ x, star (if P k₁ ∧ x = f k₁ then a k₁ else 0) * (if P k₂ ∧ x = f k₂ then a k₂ else 0) =
      if P k₁ ∧ P k₂ ∧ f k₁ = f k₂ then star (a k₁) * a k₂ else 0 := by
  rw [Finset.sum_eq_single (f k₁)]
  · by_cases h₁ : P k₁ <;> by_cases h₂ : P k₂ <;> by_cases he : f k₁ = f k₂ <;> simp [h₁, h₂, he]
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] [∀ s, Nonempty (D s)] {M : Type} [Fintype M] [DecidableEq M]

/-- The values on `T` that agree with `f` on `T ∩ L`. -/
def Agrees (T L : Finset S) (f : (s : S) → D s) (w : RevealVals D T) : Prop :=
  ∀ s : {s // s ∈ T}, s.1 ∈ L → w s = f s.1

instance (T L : Finset S) (f : (s : S) → D s) : DecidablePred (Agrees T L f) :=
  fun _ ↦ inferInstanceAs (Decidable (∀ _ : {s // s ∈ T}, _))

omit [Fintype S] [∀ s, Nonempty (D s)] in
/-- The values on `T` agreeing with `f` on `T ∩ L` are the values on `T \ L`. -/
theorem card_agrees (T L : Finset S) (f : (s : S) → D s) :
    Fintype.card {w // Agrees T L f w} = Fintype.card (RevealVals D (T \ L)) :=
  Fintype.card_congr
    { toFun := fun w s ↦ w.1 ⟨s.1, (Finset.mem_sdiff.mp s.2).1⟩
      invFun := fun u ↦ ⟨fun s ↦ if h : s.1 ∈ L then f s.1 else
          u ⟨s.1, Finset.mem_sdiff.mpr ⟨s.2, h⟩⟩, fun s hs ↦ by simp [hs]⟩
      left_inv := fun w ↦ by
        refine Subtype.ext (funext fun s ↦ ?_)
        by_cases hs : s.1 ∈ L
        · simp [hs, w.2 s hs]
        · simp [hs]
      right_inv := fun u ↦ funext fun s ↦ by
        simp [(Finset.mem_sdiff.mp s.2).2] }

/-- The inverse square root of the number of values on `T \ L`. -/
noncomputable def cAmp (T L : Finset S) : ℂ :=
  (((Real.sqrt (Fintype.card (RevealVals D (T \ L))))⁻¹ : ℝ) : ℂ)

omit [Fintype S] [∀ s, DecidableEq (D s)] in
theorem star_cAmp_mul_self (T L : Finset S) :
    star (cAmp (D := D) T L) * cAmp (D := D) T L =
      ((Fintype.card (RevealVals D (T \ L)) : ℂ))⁻¹ := by
  have hN : (0 : ℝ) < Fintype.card (RevealVals D (T \ L)) := Nat.cast_pos.mpr Fintype.card_pos
  rw [cAmp, show star ((((Real.sqrt (Fintype.card (RevealVals D (T \ L))))⁻¹ : ℝ) : ℂ)) =
      (((Real.sqrt (Fintype.card (RevealVals D (T \ L))))⁻¹ : ℝ) : ℂ) from
      Complex.conj_ofReal _, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hN.le,
    Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The amplitude of the outcome `w` of a reveal of `T` from the label `L` at the store `σ`:
`cAmp T L` if `w` agrees with the store on `T ∩ L`, zero otherwise. -/
noncomputable def revAmp (T L : Finset S) (σ : Store D) (w : RevealVals D T) : ℂ :=
  if Agrees T L (fill σ) w then cAmp (D := D) T L else 0

omit [Fintype S] in
theorem sum_star_revAmp_mul_self (T L : Finset S) (σ : Store D) :
    ∑ w, star (revAmp T L σ w) * revAmp T L σ w = 1 := by
  have hw : ∀ w, star (revAmp T L σ w) * revAmp T L σ w =
      if Agrees T L (fill σ) w then ((Fintype.card (RevealVals D (T \ L)) : ℂ))⁻¹ else 0 :=
    fun w ↦ by
      unfold revAmp
      split_ifs
      · exact star_cAmp_mul_self T L
      · simp
  simp only [hw]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, ← Fintype.card_subtype,
    card_agrees, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

omit [Fintype S] [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem agrees_fill_storeOn_iff (T L : Finset S) (v : (s : S) → D s) (w : RevealVals D T) :
    Agrees T L (fill (storeOn L v)) w ↔ Agrees T L v w :=
  forall_congr' fun s ↦ imp_congr_right fun hs ↦ by rw [fill_storeOn_of_mem hs]

/-- The register after a reveal of `T` from the memory `m`: the label grows by `T`. -/
def recU (T : Finset S) (m : Finset S × M) (d : HwReg X Z (Finset S × M)) :
    HwReg X Z (Finset S × M) :=
  (d.1, d.2.1, (m.1 ∪ T, m.2))

/-- The sampled reveal of `T` with outcome `r = (w, m)`: from the memory `m`, store the values `w`
at the new coordinates, record `T`, with amplitude `revAmp`. -/
noncomputable def revKS (T : Finset S) (r : RevealVals D T × (Finset S × M)) :
    Matrix (Unit × SReg X Z S D M) (Unit × SReg X Z S D M) ℂ :=
  Matrix.of fun x y ↦
    if y.2.1.2.2 = r.2 ∧ x = ((), (recU T r.2 y.2.1, swapIn T r.2.1 r.1 y.2.2)) then
      revAmp T r.2.1 y.2.2 r.1 else 0

/-- The sampled reveals form a complete family. -/
theorem sum_revKS (T : Finset S) :
    ∑ r, (revKS (X := X) (Z := Z) (D := D) (M := M) T r)ᴴ * revKS T r = 1 := by
  ext y₁ y₂
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, revKS, of_apply]
  simp only [sum_star_ite_mul_ite (fun p : (RevealVals D T × (Finset S × M)) ×
      (Unit × SReg X Z S D M) ↦ p.2.2.1.2.2 = p.1.2)
    (fun p ↦ ((), (recU T p.1.2 p.2.2.1, swapIn T p.1.2.1 p.1.1 p.2.2.2)))
    (fun p ↦ revAmp T p.1.2.1 p.2.2.2 p.1.1) (_, y₁) (_, y₂)]
  by_cases hy : y₁ = y₂
  · subst hy
    rw [one_apply_eq, Fintype.sum_prod_type]
    simp only [and_true, and_self, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    exact sum_star_revAmp_mul_self T _ _
  · rw [one_apply_ne hy]
    refine Finset.sum_eq_zero fun r _ ↦ ?_
    rw [ite_eq_right_iff]
    rintro ⟨h₁, h₂, he⟩
    refine absurd ?_ hy
    obtain ⟨u₁, d₁, σ₁⟩ := y₁
    obtain ⟨u₂, d₂, σ₂⟩ := y₂
    simp only [Prod.mk.injEq, recU, true_and] at he h₁ h₂
    obtain ⟨⟨he₁, he₂, -⟩, he₃⟩ := he
    have hσ : σ₁ = σ₂ := by
      rw [← swapIn_swapIn T r.2.1 r.1 σ₁, he₃, swapIn_swapIn]
    have hd : d₁ = d₂ := Prod.ext he₁ (Prod.ext he₂ (h₁.trans h₂.symm))
    rw [hσ, hd, Subsingleton.elim u₁ u₂]

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {good : LazyProg X Z S D → Prop}

variable (good) in
/-- The steps of the sampled runtime: runtime 2's Kraus operators on every store (a program port
realized at the stored values), and the sampled reveals. -/
noncomputable def sampStep (m₀ : Finset S × M) : ∀ i : (tmplSpec X Z S D M good).Port,
    SubInstrument ((tmplSpec X Z S D M good).In i × QReg.of (SReg X Z S D M))
      ((tmplSpec X Z S D M good).Out i × QReg.of (SReg X Z S D M))
      ((tmplSpec X Z S D M good).Result i)
  | .inl (.inl (.inl i)) => SubInstrument.ofKraus (α := Unit)
      (fun r ↦ ctrlK fun _ ↦ kraus2 X Z m₀ (.inl (.inl i)) r)
      (sum_conjTranspose_ctrlK_mul_self (fun (r : Unit) _ ↦ kraus2 X Z m₀ (.inl (.inl i)) r)
        fun _ ↦ (Fintype.sum_unique _).trans
          ((spongeHardwired X Z (hwEmpty X Z) m₀).conjTranspose_mul_self i))
  | .inl (.inl (.inr ⟨.readH z upd, _⟩)) => SubInstrument.ofKraus (α := Option X × (Finset S × M))
      (fun r ↦ ctrlK fun _ ↦ kraus2 X Z m₀ (.inl (.inr (.readH z upd))) r)
      (sum_conjTranspose_ctrlK_mul_self
        (fun (r : Option X × (Finset S × M)) _ ↦ kraus2 X Z m₀ (.inl (.inr (.readH z upd))) r)
        fun _ ↦ sum_readKrausH z upd)
  | .inl (.inl (.inr ⟨.readK x upd, _⟩)) => SubInstrument.ofKraus (α := Option Z × (Finset S × M))
      (fun r ↦ ctrlK fun _ ↦ kraus2 X Z m₀ (.inl (.inr (.readK x upd))) r)
      (sum_conjTranspose_ctrlK_mul_self
        (fun (r : Option Z × (Finset S × M)) _ ↦ kraus2 X Z m₀ (.inl (.inr (.readK x upd))) r)
        fun _ ↦ sum_readKrausK x upd)
  | .inl (.inl (.inr ⟨.readK' x upd, _⟩)) =>
    SubInstrument.ofKraus (α := Option Z × (Finset S × M))
      (fun r ↦ ctrlK fun _ ↦ kraus2 X Z m₀ (.inl (.inr (.readK' x upd))) r)
      (sum_conjTranspose_ctrlK_mul_self
        (fun (r : Option Z × (Finset S × M)) _ ↦ kraus2 X Z m₀ (.inl (.inr (.readK' x upd))) r)
        fun _ ↦ sum_readKrausK' x upd)
  | .inl (.inr ⟨.programH T c, _⟩) => SubInstrument.ofKraus (α := Option X × Option X)
      (fun r ↦ ctrlK fun σ ↦ kraus2 X Z m₀ (.inr ((LazyProg.programH T c).realize (fill σ))) r)
      (sum_conjTranspose_ctrlK_mul_self
        (fun (r : Option X × Option X) σ ↦
          kraus2 X Z m₀ (.inr ((LazyProg.programH T c).realize (fill σ))) r)
        fun _ ↦ sum_programKrausH _ _)
  | .inl (.inr ⟨.programK T c, _⟩) => SubInstrument.ofKraus (α := Option Z × Option Z)
      (fun r ↦ ctrlK fun σ ↦ kraus2 X Z m₀ (.inr ((LazyProg.programK T c).realize (fill σ))) r)
      (sum_conjTranspose_ctrlK_mul_self
        (fun (r : Option Z × Option Z) σ ↦
          kraus2 X Z m₀ (.inr ((LazyProg.programK T c).realize (fill σ))) r)
        fun _ ↦ sum_programKrausK _ _)
  | .inl (.inr ⟨.programK' T c, _⟩) => SubInstrument.ofKraus (α := Option Z × Option Z)
      (fun r ↦ ctrlK fun σ ↦ kraus2 X Z m₀ (.inr ((LazyProg.programK' T c).realize (fill σ))) r)
      (sum_conjTranspose_ctrlK_mul_self
        (fun (r : Option Z × Option Z) σ ↦
          kraus2 X Z m₀ (.inr ((LazyProg.programK' T c).realize (fill σ))) r)
        fun _ ↦ sum_programKrausK' _ _)
  | .inr T => SubInstrument.ofKraus (α := RevealVals D T × (Finset S × M)) (revKS T) (sum_revKS T)

variable (good) in
/-- **The sampled runtime.** The register of `runtimeR` (empty databases, nothing hardwired, empty
label, inner memory `m₀`) with an empty store. A reveal of `T` from the label `L` samples uniform
values at `T \ L`, stores them, records `T` and returns the stored values on `T`; a program port
is realized at the stored values; the other ports are runtime 2's. -/
@[reducible]
noncomputable def sampledRuntime (m₀ : M) : QuantumRuntime (tmplSpec X Z S D M good) where
  D := QReg.of (SReg X Z S D M)
  init := SubState.basis ((((Database.empty, Database.empty, Database.empty), hwEmpty X Z,
    ((∅ : Finset S), m₀)), fun _ ↦ none) : SReg X Z S D M)
  step := sampStep good (∅, m₀)

end sampled

/-! ## Matrices of partial maps -/

section conj

/-- Two Kraus operators agreeing on the columns that carry an operator give the same Kraus map
on it. -/
theorem conj_eq_of_cols {α β : Type*} [Fintype α] {K₁ K₂ : Matrix β α ℂ} (C : α → Prop)
    {X : Matrix α α ℂ} (hX : ∀ a b, X a b ≠ 0 → C a ∧ C b) (h : ∀ x a, C a → K₁ x a = K₂ x a) :
    MatrixMap.conj K₁ X = MatrixMap.conj K₂ X := by
  ext x y
  simp only [MatrixMap.conj_apply, mul_apply, conjTranspose_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases hab : X a b = 0
  · simp [hab]
  · rw [h x a (hX a b hab).1, h y b (hX a b hab).2]

/-- A Kraus map reads an operator only on the columns where the Kraus operator is nonzero. -/
theorem conj_congr_of_cols {α β : Type*} [Fintype α] (K : Matrix β α ℂ) {X X' : Matrix α α ℂ}
    (h : ∀ a b, (∃ x, K x a ≠ 0) → (∃ y, K y b ≠ 0) → X a b = X' a b) :
    MatrixMap.conj K X = MatrixMap.conj K X' := by
  ext x y
  simp only [MatrixMap.conj_apply, mul_apply, conjTranspose_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases ha : K x a = 0
  · simp [ha]
  by_cases hb : K y b = 0
  · simp [hb]
  rw [h a b ⟨x, ha⟩ ⟨y, hb⟩]

theorem conj_smul_apply {α β : Type*} [Fintype α] (c : ℂ) (K : Matrix β α ℂ) (X : Matrix α α ℂ) :
    MatrixMap.conj (c • K) X = (star c * c) • MatrixMap.conj K X := by
  simp only [MatrixMap.conj_apply, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, mul_comm]

end conj

/-! ## Embedding the runs at fixed hidden values -/

section embed

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]

/-- `id_A ⊗ embK v`: an operator of runtime 2's register beside `A`, with the store of `v` on
its label. -/
noncomputable def embM (A : Type) [Fintype A] [DecidableEq A] (v : (s : S) → D s) :
    MatrixMap (A × HwReg X Z (Finset S × M)) (A × SReg X Z S D M) :=
  (MatrixMap.conj (embK v)).amplifyLeft A

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [∀ s, Fintype (D s)] in
theorem embM_eq_conj (v : (s : S) → D s) :
    embM (X := X) (Z := Z) (M := M) α v = MatrixMap.conj ((1 : Matrix α α ℂ) ⊗ₖ embK v) :=
  MatrixMap.amplifyLeft_conj _

theorem trace_embM (v : (s : S) → D s) (ρ : Matrix (α × HwReg X Z (Finset S × M))
    (α × HwReg X Z (Finset S × M)) ℂ) : (embM α v ρ).trace = ρ.trace := by
  rw [embM_eq_conj]
  refine MatrixMap.isTP_conj ?_ ρ
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
    embK_isometry, one_kronecker_one]

omit [Fintype β] [DecidableEq β] in
theorem mul_one_kron_embK_apply (K : Matrix β (α × SReg X Z S D M) ℂ) (v : (s : S) → D s)
    (x : β) (p : α × HwReg X Z (Finset S × M)) :
    (K * ((1 : Matrix α α ℂ) ⊗ₖ embK (X := X) (Z := Z) (M := M) v)) x p =
      K x (p.1, embV v p.2) := by
  rw [mul_apply, Finset.sum_eq_single (p.1, embV v p.2)]
  · simp [kroneckerMap_apply, embK]
  · intro y _ hy
    have h0 : ((1 : Matrix α α ℂ) ⊗ₖ embK (X := X) (Z := Z) (M := M) v) y p = 0 := by
      simp only [kroneckerMap_apply, embK, of_apply, one_apply]
      by_cases h1 : y.1 = p.1
      · have h2 : y.2 ≠ embV v p.2 := fun h2 ↦ hy (Prod.ext h1 h2)
        simp [h2]
      · simp [h1]
    rw [h0, mul_zero]
  · simp

omit [DecidableEq β] [∀ s, Fintype (D s)] [Fintype β] in
theorem one_kron_embK_mul_apply (K : Matrix (α × HwReg X Z (Finset S × M)) β ℂ)
    (v : (s : S) → D s) (x : α × SReg X Z S D M) (q : β) :
    (((1 : Matrix α α ℂ) ⊗ₖ embK (X := X) (Z := Z) (M := M) v) * K) x q =
      if x.2.2 = storeOn x.2.1.2.2.1 v then K (x.1, x.2.1) q else 0 := by
  rw [mul_apply, Finset.sum_eq_single (x.1, x.2.1)]
  · have hiff : x.2 = embV v x.2.1 ↔ x.2.2 = storeOn x.2.1.2.2.1 v :=
      ⟨fun he ↦ congrArg Prod.snd he, fun h ↦ Prod.ext rfl h⟩
    simp only [kroneckerMap_apply, embK, of_apply, one_apply_eq, one_mul, hiff]
    split_ifs <;> simp
  · intro y _ hy
    simp only [kroneckerMap_apply, embK, of_apply, one_apply]
    by_cases h1 : x.1 = y.1
    · have he : x.2 ≠ embV v y.2 := fun he ↦ hy (Prod.ext h1.symm (congrArg Prod.fst he).symm)
      simp [he]
    · simp [h1]
  · simp

/-- **A controlled Kraus map on an embedded operator.** If `K'` keeps the label and `K` at the store
of `v` on the label agrees with `K'` on the columns satisfying `C`, the controlled Kraus map of
`K` acts on the embedding of an operator carried by those columns as `K'` before the
embedding. -/
theorem conj_ctrlK_embM
    (K : Store D → Matrix (β × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ)
    (K' : Matrix (β × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ)
    (v : (s : S) → D s) (C : HwReg X Z (Finset S × M) → Prop)
    (hlab : ∀ b d' a d, K' (b, d') (a, d) ≠ 0 → d'.2.2.1 = d.2.2.1)
    (hK : ∀ x a d, C d → K (storeOn d.2.2.1 v) x (a, d) = K' x (a, d))
    (X : Matrix (α × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ)
    (hX : ∀ p q, X p q ≠ 0 → C p.2 ∧ C q.2) :
    MatrixMap.conj (ctrlK K) (embM α v X) = embM β v (MatrixMap.conj K' X) := by
  rw [embM_eq_conj, embM_eq_conj]
  have e₁ : MatrixMap.conj (ctrlK K) (MatrixMap.conj ((1 : Matrix α α ℂ) ⊗ₖ embK v) X) =
      MatrixMap.conj (ctrlK K * ((1 : Matrix α α ℂ) ⊗ₖ embK v)) X := by
    rw [MatrixMap.conj_mul]
    rfl
  have e₂ : MatrixMap.conj ((1 : Matrix β β ℂ) ⊗ₖ embK v) (MatrixMap.conj K' X) =
      MatrixMap.conj (((1 : Matrix β β ℂ) ⊗ₖ embK v) * K') X := by
    rw [MatrixMap.conj_mul]
    rfl
  rw [e₁, e₂]
  refine conj_eq_of_cols (fun p ↦ C p.2) hX fun x p hp ↦ ?_
  rw [mul_one_kron_embK_apply, one_kron_embK_mul_apply]
  obtain ⟨a, d⟩ := p
  simp only [ctrlK, of_apply, embV]
  rw [hK _ a d hp]
  by_cases h0 : K' (x.1, x.2.1) (a, d) = 0
  · simp [h0]
  · rw [hlab _ _ _ _ h0]

end embed

/-! ## Uniform sampling of a block of coordinates -/

section fiber

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)]

/-- Exchange the values `a` and `b` at the coordinates `L`: an involution. -/
def swapL (L : Finset S) (a b : RevealVals D L) (v : (s : S) → D s) : (s : S) → D s :=
  fun s ↦ if h : s ∈ L then Equiv.swap (a ⟨s, h⟩) (b ⟨s, h⟩) (v s) else v s

omit [Fintype S] [∀ s, Fintype (D s)] in
theorem swapL_swapL (L : Finset S) (a b : RevealVals D L) (v : (s : S) → D s) :
    swapL L a b (swapL L a b v) = v :=
  funext fun s ↦ by by_cases h : s ∈ L <;> simp [swapL, h]

omit [Fintype S] [∀ s, Fintype (D s)] in
theorem restrictTo_swapL_eq_iff (L : Finset S) (a b : RevealVals D L) (v : (s : S) → D s) :
    restrictTo L (swapL L a b v) = b ↔ restrictTo L v = a := by
  have key : ∀ s : {s // s ∈ L},
      restrictTo L (swapL L a b v) s = Equiv.swap (a s) (b s) (v s.1) := fun s ↦ by
    simp [restrictTo, swapL, s.2]
  constructor
  · intro h
    funext s
    have hs := congrFun h s
    rw [key, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hs
    exact hs
  · intro h
    funext s
    rw [key]
    have hs : v s.1 = a s := congrFun h s
    rw [hs, Equiv.swap_apply_left]

/-- **Averaging over a block of coordinates.** For a function that does not depend on the
coordinates `L`, the sum over the hidden values with prescribed values `u` on `L` is the average
of the full sum over the values on `L`. -/
theorem sum_ite_restrictTo_eq [∀ s, Nonempty (D s)] {E : Type*} [AddCommGroup E] [Module ℂ E]
    (L : Finset S)
    (u : RevealVals D L) (F : ((s : S) → D s) → E)
    (hF : ∀ v v', (∀ s, s ∉ L → v s = v' s) → F v = F v') :
    ∑ v, (if restrictTo L v = u then F v else 0) =
      ((Fintype.card (RevealVals D L) : ℂ))⁻¹ • ∑ v, F v := by
  have hfib : ∀ u', ∑ v, (if restrictTo L v = u' then F v else 0) =
      ∑ v, (if restrictTo L v = u then F v else 0) := fun u' ↦ by
    let e : ((s : S) → D s) ≃ ((s : S) → D s) :=
      ⟨swapL L u' u, swapL L u' u, swapL_swapL L u' u, swapL_swapL L u' u⟩
    rw [← e.sum_comp (fun v ↦ if restrictTo L v = u then F v else 0)]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have hv : F (swapL L u' u v) = F v :=
      hF _ _ fun s hs ↦ by simp [swapL, hs]
    show _ = (if restrictTo L (swapL L u' u v) = u then F (swapL L u' u v) else 0)
    rw [hv]
    exact if_congr (restrictTo_swapL_eq_iff L u' u v).symm rfl rfl
  have htot : ∑ v, F v = ∑ u' : RevealVals D L, ∑ v, (if restrictTo L v = u' then F v else 0) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [htot, Finset.sum_congr rfl fun u' _ ↦ hfib u', Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

end fiber

/-! ## The sampled steps on embedded families -/

section core

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] [∀ s, Nonempty (D s)] {M : Type} [Fintype M] [DecidableEq M]

omit [Fintype S] [∀ s, Nonempty (D s)] [Fintype M] in
theorem recKraus_apply (T : Finset S) (m : Finset S × M) (y x : Unit × HwReg X Z (Finset S × M)) :
    recKraus (X := X) (Z := Z) T m y x = if x.2.2.2 = m ∧ y.2 = recU T m x.2 then 1 else 0 := by
  rcases y with ⟨⟨⟩, d', b'⟩
  rcases x with ⟨⟨⟩, d, b⟩
  simp only [recKraus, kroneckerMap_apply, one_apply_eq, one_mul, clsKraus_apply, recU,
    Prod.mk.injEq]
  by_cases hm : b.2 = m
  · subst hm
    by_cases hd : d' = d
    · subst hd
      simp
    · simp [hd]
  · simp [hm]

/-- **A sampled reveal after the embedding at `v`** is, up to its amplitude, the record port
followed by the embedding at `v` overridden by the revealed values. -/
theorem revKS_mul_one_kron_embK (T : Finset S) (w : RevealVals D T) (m : Finset S × M)
    (v : (s : S) → D s) :
    revKS T (w, m) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ embK (X := X) (Z := Z) (M := M) v) =
      (if Agrees T m.1 v w then cAmp (D := D) T m.1 else 0) •
        (((1 : Matrix Unit Unit ℂ) ⊗ₖ embK (X := X) (Z := Z) (M := M) (override T m.1 w v)) *
          recKraus T m) := by
  ext x ⟨u, d⟩
  rw [mul_one_kron_embK_apply, Matrix.smul_apply, one_kron_embK_mul_apply, recKraus_apply]
  simp only [revKS, of_apply, embV, smul_eq_mul]
  by_cases hm : d.2.2 = m
  · subst hm
    rw [swapIn_storeOn]
    simp only [revAmp, agrees_fill_storeOn_iff]
    obtain ⟨⟨⟩, xd, xσ⟩ := x
    by_cases hx : xd = recU T d.2.2 d
    · subst hx
      by_cases hσ : xσ = storeOn (d.2.2.1 ∪ T) (override T d.2.2.1 w v)
      · subst hσ
        simp [recU]
      · simp [recU, hσ]
    · simp [hx]
  · simp [hm]

/-- **The sampled reveal on an embedded lazy family**: the average over the hidden values of the
reveal at `v` after the embedding at `v`. The values sampled at the new coordinates `T \ L` are
uniform, as the hidden values there are, on which the family does not depend. -/
theorem conj_revKS_sum_embM (T : Finset S) (r : RevealVals D T × (Finset S × M))
    (ρ : ((s : S) → D s) →
      Matrix (Unit × HwReg X Z (Finset S × M)) (Unit × HwReg X Z (Finset S × M)) ℂ)
    (hρ : Lazy (fun p : Unit × HwReg X Z (Finset S × M) ↦ p.2.2.2.1) ρ) :
    MatrixMap.conj (revKS T r) (∑ v, embM Unit v (ρ v)) =
      ∑ v, embM Unit v (MatrixMap.conj (revealKraus T v r) (ρ v)) := by
  obtain ⟨w, m⟩ := r
  let u : RevealVals D (T \ m.1) := fun s ↦ w ⟨s.1, (Finset.mem_sdiff.mp s.2).1⟩
  let F : ((s : S) → D s) → Matrix (Unit × SReg X Z S D M) (Unit × SReg X Z S D M) ℂ := fun v ↦
    if Agrees T m.1 v w then embM Unit (override T m.1 w v) (MatrixMap.conj (recKraus T m) (ρ v))
      else 0
  have hF : ∀ v v', (∀ s, s ∉ T \ m.1 → v s = v' s) → F v = F v' := fun v v' hvv ↦ by
    have hA : Agrees T m.1 v w ↔ Agrees T m.1 v' w :=
      forall_congr' fun s ↦ imp_congr_right fun hs ↦ by
        rw [hvv s.1 fun h ↦ (Finset.mem_sdiff.mp h).2 hs]
    have ho : override T m.1 w v = override T m.1 w v' := funext fun s ↦ by
      unfold override
      split_ifs with h
      · rfl
      · exact hvv s fun hs ↦ h (Finset.mem_sdiff.mp hs)
    have hY : MatrixMap.conj (recKraus (X := X) (Z := Z) T m) (ρ v) =
        MatrixMap.conj (recKraus T m) (ρ v') :=
      conj_congr_of_cols _ fun a b ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
        rw [recKraus_apply] at hx hy
        have ha : a.2.2.2 = m := (ite_ne_right_iff.mp hx).1.1
        have hb : b.2.2.2 = m := (ite_ne_right_iff.mp hy).1.1
        refine hρ a b v v' fun s hs ↦ hvv s fun hs' ↦ (Finset.mem_sdiff.mp hs').2 ?_
        change s ∈ a.2.2.2.1 ∪ b.2.2.2.1 at hs
        rw [ha, hb, Finset.union_self] at hs
        exact hs
    simp only [F, hA, ho, hY]
  have hL : MatrixMap.conj (revKS T (w, m)) (∑ v, embM Unit v (ρ v)) =
      ((Fintype.card (RevealVals D (T \ m.1)) : ℂ))⁻¹ • ∑ v, F v := by
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have e₁ : MatrixMap.conj (revKS T (w, m)) (embM Unit v (ρ v)) =
        MatrixMap.conj (revKS T (w, m) *
          ((1 : Matrix Unit Unit ℂ) ⊗ₖ embK (X := X) (Z := Z) (M := M) v)) (ρ v) := by
      rw [embM_eq_conj, MatrixMap.conj_mul]
      rfl
    have e₂ : MatrixMap.conj (((1 : Matrix Unit Unit ℂ) ⊗ₖ
          embK (X := X) (Z := Z) (M := M) (override T m.1 w v)) * recKraus T m) (ρ v) =
        embM Unit (override T m.1 w v) (MatrixMap.conj (recKraus T m) (ρ v)) := by
      rw [embM_eq_conj, MatrixMap.conj_mul]
      rfl
    rw [e₁, revKS_mul_one_kron_embK, conj_smul_apply, e₂]
    simp only [F]
    split_ifs
    · rw [star_cAmp_mul_self]
    · simp
  have hR : ∑ v, embM Unit v (MatrixMap.conj (revealKraus T v (w, m)) (ρ v)) =
      ∑ v, (if restrictTo (T \ m.1) v = u then F v else 0) := by
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    by_cases hw : w = restrictTo T v
    · have hA : Agrees T m.1 v w := fun s _ ↦ congrFun hw s
      have hu : restrictTo (T \ m.1) v = u :=
        funext fun s ↦ (congrFun hw ⟨s.1, (Finset.mem_sdiff.mp s.2).1⟩).symm
      have ho : override T m.1 w v = v := funext fun s ↦ by
        unfold override
        split_ifs with h
        · exact congrFun hw ⟨s, h.1⟩
        · rfl
      have hK : revealKraus (X := X) (Z := Z) (M := M) T v (w, m) = recKraus T m :=
        ite_eq_left hw
      rw [hK, ite_eq_left hu]
      simp only [F, ite_eq_left hA, ho]
    · have hK : revealKraus (X := X) (Z := Z) (M := M) T v (w, m) = 0 := ite_eq_right hw
      rw [hK, MatrixMap.conj_zero, LinearMap.zero_apply, map_zero]
      split_ifs with hu
      · have hA : ¬ Agrees T m.1 v w := fun hA ↦ hw (funext fun s ↦ by
          by_cases hs : s.1 ∈ m.1
          · exact hA s hs
          · exact (congrFun hu ⟨s.1, Finset.mem_sdiff.mpr ⟨s.2, hs⟩⟩).symm)
        simp only [F, ite_eq_right hA]
      · rfl
  rw [hL, hR, sum_ite_restrictTo_eq (T \ m.1) u F hF]

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {good : LazyProg X Z S D → Prop}

/-- **The sampled steps on embedded lazy families.** For a port that keeps the label (a read) and
a lazy family carried by the states labelled above the port's coordinates, a step of the sampled
runtime on the sum of the embeddings is the sum of the embeddings of the template steps. -/
theorem sampStep_branch_sum_embM (m₀ : Finset S × M) (i : (tmplSpec X Z S D M good).Port)
    (hi : portKeeps good i) (r : (tmplSpec X Z S D M good).Result i)
    (ρ : ((s : S) → D s) → Matrix ((tmplSpec X Z S D M good).In i × HwReg X Z (Finset S × M))
      ((tmplSpec X Z S D M good).In i × HwReg X Z (Finset S × M)) ℂ)
    (hρ : Lazy (fun p : (tmplSpec X Z S D M good).In i × HwReg X Z (Finset S × M) ↦ p.2.2.2.1) ρ)
    (hs : ∀ v, SuppAt (fun p : (tmplSpec X Z S D M good).In i × HwReg X Z (Finset S × M) ↦
      p.2.2.2.1) (tmplNeed good i) (ρ v)) :
    (sampStep good m₀ i).branch r (∑ v, embM _ v (ρ v)) =
      ∑ v, embM _ v ((tmplStep m₀ v i).branch r (ρ v)) := by
  rcases i with ((i | ⟨c, hc⟩) | ⟨p, hp⟩) | T
  · rw [map_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    show MatrixMap.conj (ctrlK fun _ ↦ kraus2 X Z m₀ (.inl (.inl i)) r) (embM _ v (ρ v)) =
      embM _ v (((runtime2 X Z m₀).step (.inl (.inl i))).branch r (ρ v))
    rw [runtime2_branch m₀ (.inl (.inl i)) r]
    exact conj_ctrlK_embM _ _ v (fun _ ↦ True)
      (fun _ _ _ _ h ↦ congrArg (fun q ↦ q.2.1)
        (spongeHardwired_U_ne_zero_snd (hwEmpty X Z) m₀ i h))
      (fun _ _ _ _ ↦ rfl) _ fun _ _ _ ↦ ⟨trivial, trivial⟩
  · rw [map_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rcases c with ⟨z, upd⟩ | ⟨x, upd⟩ | ⟨x, upd⟩
    · show MatrixMap.conj (ctrlK fun _ ↦ kraus2 X Z m₀ (.inl (.inr (.readH z upd))) r)
          (embM _ v (ρ v)) =
        embM _ v (((runtime2 X Z m₀).step (.inl (.inr (.readH z upd)))).branch r (ρ v))
      rw [runtime2_branch m₀ (.inl (.inr (.readH z upd))) r]
      exact conj_ctrlK_embM _ _ v (fun _ ↦ True)
        (fun _ _ _ _ h ↦ hwReadKraus_ne_zero_keeps (c := .readH z upd) hi r h) (fun _ _ _ _ ↦ rfl) _
        fun _ _ _ ↦ ⟨trivial, trivial⟩
    · show MatrixMap.conj (ctrlK fun _ ↦ kraus2 X Z m₀ (.inl (.inr (.readK x upd))) r)
          (embM _ v (ρ v)) =
        embM _ v (((runtime2 X Z m₀).step (.inl (.inr (.readK x upd)))).branch r (ρ v))
      rw [runtime2_branch m₀ (.inl (.inr (.readK x upd))) r]
      exact conj_ctrlK_embM _ _ v (fun _ ↦ True)
        (fun _ _ _ _ h ↦ hwReadKraus_ne_zero_keeps (c := .readK x upd) hi r h) (fun _ _ _ _ ↦ rfl) _
        fun _ _ _ ↦ ⟨trivial, trivial⟩
    · show MatrixMap.conj (ctrlK fun _ ↦ kraus2 X Z m₀ (.inl (.inr (.readK' x upd))) r)
          (embM _ v (ρ v)) =
        embM _ v (((runtime2 X Z m₀).step (.inl (.inr (.readK' x upd)))).branch r (ρ v))
      rw [runtime2_branch m₀ (.inl (.inr (.readK' x upd))) r]
      exact conj_ctrlK_embM _ _ v (fun _ ↦ True)
        (fun _ _ _ _ h ↦ hwReadKraus_ne_zero_keeps (c := .readK' x upd) hi r h)
        (fun _ _ _ _ ↦ rfl) _
        fun _ _ _ ↦ ⟨trivial, trivial⟩
  · rw [map_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    cases p with
    | programH T c =>
      show MatrixMap.conj (ctrlK fun σ ↦
          kraus2 X Z m₀ (.inr ((LazyProg.programH T c).realize (fill σ))) r) (embM _ v (ρ v)) =
        embM _ v (((runtime2 X Z m₀).step (.inr ((LazyProg.programH T c).realize v))).branch r
          (ρ v))
      rw [runtime2_branch m₀ (.inr ((LazyProg.programH T c).realize v)) r]
      exact conj_ctrlK_embM _ _ v (fun d ↦ T ⊆ d.2.2.1)
        (fun _ _ _ _ h ↦ by rw [hwProgKraus_ne_zero_snd ((LazyProg.programH T c).realize v) r h])
        (fun _ _ _ hd ↦ by
          simp only [LazyProg.realize]
          rw [restrictTo_eq fun s hs ↦ fill_storeOn_of_mem (hd hs)])
        _ (hs v)
    | programK T c =>
      show MatrixMap.conj (ctrlK fun σ ↦
          kraus2 X Z m₀ (.inr ((LazyProg.programK T c).realize (fill σ))) r) (embM _ v (ρ v)) =
        embM _ v (((runtime2 X Z m₀).step (.inr ((LazyProg.programK T c).realize v))).branch r
          (ρ v))
      rw [runtime2_branch m₀ (.inr ((LazyProg.programK T c).realize v)) r]
      exact conj_ctrlK_embM _ _ v (fun d ↦ T ⊆ d.2.2.1)
        (fun _ _ _ _ h ↦ by rw [hwProgKraus_ne_zero_snd ((LazyProg.programK T c).realize v) r h])
        (fun _ _ _ hd ↦ by
          simp only [LazyProg.realize]
          rw [restrictTo_eq fun s hs ↦ fill_storeOn_of_mem (hd hs)])
        _ (hs v)
    | programK' T c =>
      show MatrixMap.conj (ctrlK fun σ ↦
          kraus2 X Z m₀ (.inr ((LazyProg.programK' T c).realize (fill σ))) r) (embM _ v (ρ v)) =
        embM _ v (((runtime2 X Z m₀).step (.inr ((LazyProg.programK' T c).realize v))).branch r
          (ρ v))
      rw [runtime2_branch m₀ (.inr ((LazyProg.programK' T c).realize v)) r]
      exact conj_ctrlK_embM _ _ v (fun d ↦ T ⊆ d.2.2.1)
        (fun _ _ _ _ h ↦ by rw [hwProgKraus_ne_zero_snd ((LazyProg.programK' T c).realize v) r h])
        (fun _ _ _ hd ↦ by
          simp only [LazyProg.realize]
          rw [restrictTo_eq fun s hs ↦ fill_storeOn_of_mem (hd hs)])
        _ (hs v)
  · exact conj_revKS_sum_embM T r ρ hρ

end core

/-! ## Runs of templates against the sampled runtime -/

section run

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] [∀ s, Nonempty (D s)] {M : Type} [Fintype M] [DecidableEq M]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {good : LazyProg X Z S D → Prop} {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w}

omit [∀ s, Nonempty (D s)] [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- Sums over the hidden values commute with summable sums of embedded operators. -/
theorem tsum_sum_embM {ι : Type*} {α : Type} [Fintype α] [DecidableEq α]
    (f : ((s : S) → D s) → ι →
      Matrix (α × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ)
    (hf : ∀ v, Summable (f v)) :
    ∑' b, ∑ v, embM α v (f v b) = ∑ v, embM α v (∑' b, f v b) := by
  rw [Summable.tsum_finsetSum fun v _ ↦ (embM α v).summable_comp (hf v)]
  exact Finset.sum_congr rfl fun v _ ↦ ((embM α v).map_tsum (hf v)).symm

omit [∀ s, Nonempty (D s)] [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- A family of maps on embedded lazy families, framed by a remainder register `E`. -/
theorem amplify_sum_embM {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (Φs : MatrixMap (α × SReg X Z S D M) (β × SReg X Z S D M))
    (Φ : ((s : S) → D s) →
      MatrixMap (α × HwReg X Z (Finset S × M)) (β × HwReg X Z (Finset S × M)))
    (P : Matrix (α × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ → Prop)
    (h : ∀ ρ : ((s : S) → D s) →
        Matrix (α × HwReg X Z (Finset S × M)) (α × HwReg X Z (Finset S × M)) ℂ,
      Lazy (fun p : α × HwReg X Z (Finset S × M) ↦ p.2.2.2.1) ρ → (∀ v, P (ρ v)) →
        Φs (∑ v, embM α v (ρ v)) = ∑ v, embM β v (Φ v (ρ v)))
    (E : Type) [Fintype E] [DecidableEq E]
    (σ : ((s : S) → D s) → Matrix ((α × HwReg X Z (Finset S × M)) × E)
      ((α × HwReg X Z (Finset S × M)) × E) ℂ)
    (hσ : Lazy (fun p : (α × HwReg X Z (Finset S × M)) × E ↦ p.1.2.2.2.1) σ)
    (hP : ∀ v e e', P ((σ v).submatrix (·, e) (·, e'))) :
    Φs.amplify E (∑ v, (embM α v).amplify E (σ v)) =
      ∑ v, (embM β v).amplify E ((Φ v).amplify E (σ v)) := by
  ext ⟨b, e⟩ ⟨b', e'⟩
  have hsub : (∑ v, (embM (X := X) (Z := Z) (M := M) α v).amplify E (σ v)).submatrix
      (·, e) (·, e') = ∑ v, embM α v ((σ v).submatrix (·, e) (·, e')) := by
    ext x y
    simp only [submatrix_apply, Matrix.sum_apply, MatrixMap.amplify_apply]
  have key := h (fun v ↦ (σ v).submatrix (·, e) (·, e'))
    (fun x y v v' hv ↦ hσ (x, e) (y, e') v v' hv) fun v ↦ hP v e e'
  simp only [MatrixMap.amplify_apply, Matrix.sum_apply]
  rw [hsub, key, Matrix.sum_apply]
  rfl

/-- **A call of the sampled runtime on embedded lazy families**: the sum of the embeddings of
the calls of the template runtime, for a port that keeps the label, called on states labelled
above its coordinates. -/
theorem queryStep_sum_embM (m₀ : M) {A : QReg} (i : (tmplSpec X Z S D M good).Port)
    (hi : portKeeps good i) (E : QReg) (ℓ : A ≃ (tmplSpec X Z S D M good).In i × E)
    (r : (tmplSpec X Z S D M good).Result i)
    (ρ : ((s : S) → D s) →
      Matrix (A × HwReg X Z (Finset S × M)) (A × HwReg X Z (Finset S × M)) ℂ)
    (hρ : Lazy (fun p : A × HwReg X Z (Finset S × M) ↦ p.2.2.2.1) ρ)
    (hs : ∀ v, CallSupp (fun d : QReg.of (HwReg X Z (Finset S × M)) ↦ d.2.2.1) (tmplNeed good) i E
      ((SubInstrument.relabel (queryEquivIn ℓ (QReg.of (HwReg X Z (Finset S × M))))).branch ()
        (ρ v))) :
    ((sampledRuntime good m₀).queryStep i E ℓ).branch r (∑ v, embM A v (ρ v)) =
      ∑ v, embM _ v (((famRuntime (initHw X Z ((∅ : Finset S), m₀))
        (tmplStep (good := good) ((∅ : Finset S), m₀)) v).queryStep i E ℓ).branch r (ρ v)) := by
  rw [QuantumRuntime.queryStep_branch_apply (R := sampledRuntime good m₀) i E ℓ r]
  refine Eq.trans ?_ (Finset.sum_congr rfl fun v _ ↦ congrArg (embM _ v)
    (QuantumRuntime.queryStep_branch_apply (R := famRuntime (initHw X Z ((∅ : Finset S), m₀))
      (tmplStep (good := good) ((∅ : Finset S), m₀)) v) i E ℓ r (ρ v)).symm)
  have hin : ∀ v, (SubInstrument.relabel (queryEquivIn ℓ (QReg.of (SReg X Z S D M)))).branch ()
      (embM A v (ρ v)) = (embM _ v).amplify E
        ((SubInstrument.relabel (queryEquivIn ℓ (QReg.of (HwReg X Z (Finset S × M))))).branch ()
          (ρ v)) := fun v ↦
    LinearMap.congr_fun (intertwines_relabel_queryEquivIn (MatrixMap.conj (embK v)) ℓ ()) (ρ v)
  have hout : ∀ v (X' : Matrix (((tmplSpec X Z S D M good).Out i × HwReg X Z (Finset S × M)) × E)
      (((tmplSpec X Z S D M good).Out i × HwReg X Z (Finset S × M)) × E) ℂ),
      (SubInstrument.relabel (queryEquivOut ((tmplSpec X Z S D M good).Out i)
        (QReg.of (SReg X Z S D M)) E)).branch () ((embM _ v).amplify E X') =
      embM _ v ((SubInstrument.relabel (queryEquivOut ((tmplSpec X Z S D M good).Out i)
        (QReg.of (HwReg X Z (Finset S × M))) E)).branch () X') := fun v X' ↦
    LinearMap.congr_fun (intertwines_relabel_queryEquivOut (MatrixMap.conj (embK v)) _ E ()) X'
  rw [map_sum]
  simp only [hin, DSubInstrument.branch_frame_apply]
  rw [amplify_sum_embM _ _ _ (sampStep_branch_sum_embM _ i hi r) E _
    (lazy_relabel _ (fun _ ↦ rfl) hρ) fun v e e' a b hab ↦ hs v (a, e) (b, e') hab, map_sum]
  simp only [hout]

/-- **The run of a template against the sampled runtime on embedded lazy families.** For a
template whose reads keep the label (`KeepsLab`), run from a lazy family whose calls are presented
states labelled above the ports' coordinates, the run against the sampled runtime of the sum of
the embeddings is the sum of the embeddings of the runs against the template runtime. -/
theorem run_sampled_sum_embM (m₀ : M) {A : QReg} (y : QuantumComp L (tmplSpec X Z S D M good) Ω A) :
    ∀ (ρ : ((s : S) → D s) →
      Matrix (A × HwReg X Z (Finset S × M)) (A × HwReg X Z (Finset S × M)) ℂ),
      Lazy (fun p : A × HwReg X Z (Finset S × M) ↦ p.2.2.2.1) ρ → KeepsLab y →
      (∀ v, (famRuntime (initHw X Z ((∅ : Finset S), m₀))
        (tmplStep (good := good) ((∅ : Finset S), m₀)) v).ForallQueries I
          (CallSupp (fun d : QReg.of (HwReg X Z (Finset S × M)) ↦ d.2.2.1) (tmplNeed good)) y
          (ρ v)) →
      ∀ p : Σ u, Ω u, ((sampledRuntime good m₀).run I y).branch p (∑ v, embM A v (ρ v)) =
        ∑ v, embM p.1 v (((famRuntime (initHw X Z ((∅ : Finset S), m₀))
          (tmplStep (good := good) ((∅ : Finset S), m₀)) v).run I y).branch p (ρ v)) := by
  induction y using QuantumComp.inductionOn with
  | pure _ x =>
    intro ρ _ _ _ p
    simp only [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, x⟩
    · subst hp
      simp only [DSubInstrument.branch_ret_self, LinearMap.id_apply]
    · simp only [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply, map_zero,
        Finset.sum_const_zero]
  | primBind _ o k ih =>
    intro ρ hρ hy hsupp p
    simp only [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    have hstep : ∀ b, ((I o).frame (QReg.of (SReg X Z S D M))).branch b
        (∑ v, embM _ v (ρ v)) =
        ∑ v, embM _ v (((I o).frame (QReg.of (HwReg X Z (Finset S × M)))).branch b (ρ v)) :=
      fun b ↦ by
        rw [map_sum]
        exact Finset.sum_congr rfl fun v _ ↦ LinearMap.congr_fun
          (DSubInstrument.Intertwines.frame_amplifyLeft (I o) (MatrixMap.conj (embK v)) b) (ρ v)
    simp only [hstep]
    rw [tsum_congr fun b ↦ ih b
      (fun v ↦ ((I o).frame (QReg.of (HwReg X Z (Finset S × M)))).branch b (ρ v))
      (lazy_amplify (lab := fun d : HwReg X Z (Finset S × M) ↦ d.2.2.1) _ hρ)
      ((keepsLab_primBind o k).mp hy b)
      (fun v ↦ (forallQueries_primBind_iff I o k _).mp (hsupp v) b)
      p]
    exact tsum_sum_embM _ fun v ↦ (((I o).frame _).isCPTNIFamily.comp_eval
      (fun b ↦ ((famRuntime (initHw X Z ((∅ : Finset S), m₀))
        (tmplStep (good := good) ((∅ : Finset S), m₀)) v).run I (k b)).isCPTNIFamily)
      p).summable_apply (ρ v)
  | queryBind _ i E ℓ k ih =>
    intro ρ hρ hy hsupp p
    obtain ⟨hi, hk⟩ := (keepsLab_queryBind i E ℓ k).mp hy
    have hs := fun v ↦ ((forallQueries_queryBind_iff I i E ℓ k _).mp (hsupp v)).1
    simp only [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    simp only [queryStep_sum_embM m₀ i hi E ℓ _ ρ hρ hs]
    rw [tsum_congr fun r ↦ ih r _ (lazy_queryStep (stepLazy_tmplStep _) i E ℓ r hρ hs) (hk r)
      (fun v ↦ ((forallQueries_queryBind_iff I i E ℓ k _).mp (hsupp v)).2 r) p]
    exact tsum_sum_embM _ fun v ↦ (((famRuntime (initHw X Z ((∅ : Finset S), m₀))
      (tmplStep (good := good) ((∅ : Finset S), m₀)) v).queryStep i E ℓ).isCPTNIFamily.comp_eval
      (fun r ↦ ((famRuntime (initHw X Z ((∅ : Finset S), m₀))
        (tmplStep (good := good) ((∅ : Finset S), m₀)) v).run I (k r)).isCPTNIFamily)
      p).summable_apply (ρ v)

end run

/-! ## Averaged realizations are runs against the sampled runtime -/

section average

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] [∀ s, Nonempty (D s)] {M : Type} [Fintype M] [DecidableEq M]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {good : LazyProg X Z S D → Prop} {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w}

omit [∀ s, Fintype (D s)] [∀ s, Nonempty (D s)] [AddCommGroup X] [AddCommGroup Z] [Nonempty X]
  [Nonempty Z] in
theorem conj_embK_single (v : (s : S) → D s) (d : HwReg X Z (Finset S × M)) :
    MatrixMap.conj (embK v) (Matrix.single d d 1) =
      Matrix.single (embV (X := X) (Z := Z) (M := M) v d) (embV v d) (1 : ℂ) := by
  ext x y
  simp only [MatrixMap.conj_apply, mul_apply, conjTranspose_apply, embK, of_apply, single_apply]
  rw [Finset.sum_eq_single d (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
  rw [Finset.sum_eq_single d (fun a _ ha ↦ by simp [Ne.symm ha]) (by simp)]
  by_cases hx : x = embV v d <;> by_cases hy : y = embV v d <;> simp [hx, hy, eq_comm]

omit [∀ s, Fintype (D s)] [∀ s, Nonempty (D s)] [AddCommGroup X] [AddCommGroup Z] [Nonempty X]
  [Nonempty Z] in
/-- **The initial states agree**: the embedding at any `v` of runtime 2's initial register with an
empty label is the sampled runtime's initial register. -/
theorem embM_init (m₀ : M) {α : Type} [Fintype α] [DecidableEq α] (ρ : Matrix α α ℂ)
    (v : (s : S) → D s) :
    embM α v (ρ ⊗ₖ (initHw X Z ((∅ : Finset S), m₀)).matrix) =
      ρ ⊗ₖ Matrix.single ((((Database.empty, Database.empty, Database.empty), hwEmpty X Z,
        ((∅ : Finset S), m₀)), fun _ ↦ none) : SReg X Z S D M)
        ((((Database.empty, Database.empty, Database.empty), hwEmpty X Z,
        ((∅ : Finset S), m₀)), fun _ ↦ none) : SReg X Z S D M) 1 := by
  have he : embV (X := X) (Z := Z) (M := M) v
      (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, ((∅ : Finset S), m₀))) =
      (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, ((∅ : Finset S), m₀)),
        fun _ ↦ none) :=
    Prod.ext rfl (funext fun s ↦ by simp [embV, storeOn])
  rw [embM, MatrixMap.amplifyLeft_kronecker, initHw, SubState.matrix_basis, conj_embK_single, he]

/-- **The run against the sampled runtime is the average of the realized runs, embedded.** For a
template that reveals before it programs and whose reads keep the label, from `ρ` beside the
initial registers. -/
theorem branch_run_sampled (m₀ : M) {A : QReg} (y : QuantumComp L (tmplSpec X Z S D M good) Ω A)
    (hdisc : Disc y ∅) (hkeep : KeepsLab y) (ρ : Matrix A A ℂ) (p : Σ u, Ω u) :
    ((sampledRuntime good m₀).run I y).branch p
        (ρ ⊗ₖ (sampledRuntime good m₀).init.matrix) =
      ((Fintype.card ((s : S) → D s) : ℂ))⁻¹ • ∑ v, embM p.1 v
        (((runtimeR ((∅ : Finset S), m₀)).run I (realizeT v y)).branch p
          (ρ ⊗ₖ (initHw X Z ((∅ : Finset S), m₀)).matrix)) := by
  have h := run_sampled_sum_embM I m₀ y (fun _ ↦ ρ ⊗ₖ (initHw X Z ((∅ : Finset S), m₀)).matrix)
    (lazy_const _ _) hkeep (fun v ↦ forallQueries_of_disc I _ v y ∅ hdisc _ (suppAt_empty _ _)) p
  simp only [embM_init, Finset.sum_const, Finset.card_univ] at h
  rw [map_nsmul] at h
  have h2 := congrArg (((Fintype.card ((s : S) → D s) : ℂ))⁻¹ • ·) h
  simp only at h2
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul] at h2
  refine h2.trans (congrArg _ (Finset.sum_congr rfl fun v _ ↦ congrArg (embM p.1 v) ?_))
  exact (branch_run_realizeT I _ v y _ p).symm

/-- **Lazy sampling, leaf by leaf.** The weight of a leaf in the run of the sampled runtime is the
average over uniform hidden values of its weight in the realized runs against `runtimeR`. -/
theorem uavg_trace_jointPost_realizeT_eq_sampled (m₀ : M) {A : QReg}
    (y : QuantumComp L (tmplSpec X Z S D M good) Ω A) (hdisc : Disc y ∅) (hkeep : KeepsLab y)
    (ρ : SubState A) (p : Σ u, Ω u) :
    uavg (fun v ↦ ENNReal.ofReal
        ((runtimeR ((∅ : Finset S), m₀)).jointPost I (realizeT v y) ρ p).matrix.trace.re) =
      ENNReal.ofReal ((sampledRuntime good m₀).jointPost I y ρ p).matrix.trace.re := by
  have key : ((sampledRuntime good m₀).jointPost I y ρ p).matrix.trace =
      ((Fintype.card ((s : S) → D s) : ℂ))⁻¹ *
        ∑ v, ((runtimeR ((∅ : Finset S), m₀)).jointPost I (realizeT v y) ρ p).matrix.trace := by
    rw [matrix_jointPost, branch_run_sampled I m₀ y hdisc hkeep, trace_smul, trace_sum,
      smul_eq_mul]
    exact congrArg _ (Finset.sum_congr rfl fun v _ ↦ trace_embM v _)
  have hc : ((Fintype.card ((s : S) → D s) : ℂ))⁻¹ =
      (((Fintype.card ((s : S) → D s) : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [key, hc, Complex.re_ofReal_mul, Complex.re_sum,
    ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)),
    ENNReal.ofReal_sum_of_nonneg fun v _ ↦
      ((runtimeR ((∅ : Finset S), m₀)).jointPost I (realizeT v y) ρ p).trace_re_nonneg,
    ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr Fintype.card_pos), ENNReal.ofReal_natCast]
  rfl

/-- **Lazy sampling of template programs** (`uavg_realizeT_outcome_eq_sampled`). The outcome
distribution of any observation `f` of a template's leaf, averaged over uniform hidden values
of the realized runs against runtime 2 with record ports (empty initial label), is that of the
template run against the sampled runtime. The template reveals before it programs (`Disc y ∅`)
and its reads keep the memory label (`KeepsLab y`). -/
theorem uavg_realizeT_outcome_eq_sampled (m₀ : M) {A : QReg}
    (y : QuantumComp L (tmplSpec X Z S D M good) Ω A) (hdisc : Disc y ∅) (hkeep : KeepsLab y)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ] (f : (Σ u, Ω u) → γ) {s : Set γ}
    (hs : MeasurableSet s) :
    uavg (fun v ↦ (runtimeR ((∅ : Finset S), m₀)).evalDistMap I (realizeT v y) ρ f s) =
      (sampledRuntime good m₀).evalDistMap I y ρ f s := by
  simp only [evalDistMap_apply _ _ _ _ _ hs]
  rw [uavg, ← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun p ↦ ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  exact congrArg (· * s.indicator 1 (f p))
    (uavg_trace_jointPost_realizeT_eq_sampled I m₀ y hdisc hkeep ρ p)

end average

end Quantum.Sig

end
