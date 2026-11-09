module

public import Qrom.Hiding

@[expose] public section

/-!
# The protected mass, averaged over the hidden data

Let the second game depend on hidden data `h : K → Z`, revealed key by key: in side state `s` the
game reads only the keys `rev s`, and the side ports only grow `rev`. If, for every side state `s`,
input `x` and values of the revealed keys, at most a fraction `ε` of the values of the other keys
protect `x`, then the protected mass of every call, summed over `h`, is at most `ε` times its
total mass (`Qrom.OvGame.sum_queryWeight_protMass_le`).

The mass splits by side state. On the side state `s`, the run depends on `h` only through the
revealed keys (`Qrom.OvGame.queryWeight_eq_of_agreeOn` on the side states `s'` with
`rev s' ⊆ rev s`), so the protected indicator can be averaged over the other keys first.
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

/-! ## Masses of one side state -/

/-- The mass of a hash call on the inputs `x` with `Q x` in side state `s`. -/
noncomputable def massSH (s : S) (Q : X → Prop) [DecidablePred Q]
    (σ : Matrix ((X × Y) × (S × Unit)) ((X × Y) × (S × Unit)) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ p, if p.2.1 = s ∧ Q p.1.1 then (σ p p).re else 0)

/-- The same mass for every port; side ports carry none. -/
noncomputable def massS (s : S) (Q : X → Prop) [DecidablePred Q] :
    ∀ i : (ovSpec X Y S P Res).Port,
      Matrix ((ovSpec X Y S P Res).In i × (S × Unit)) ((ovSpec X Y S P Res).In i × (S × Unit)) ℂ →
        ℝ≥0∞
  | .inl _ => massSH s Q
  | .inr _ => fun _ ↦ 0

theorem diag_re_nonneg {n : Type*} [Fintype n] {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (p : n) :
    0 ≤ (σ p p).re :=
  (RCLike.nonneg_iff.mp (hσ.diag_nonneg (i := p))).1

/-- The protected mass is the sum over the side states of their protected masses. -/
theorem protMassH_eq_sum (Prot : S → X → Prop) [∀ s, DecidablePred (Prot s)]
    {σ : Matrix ((X × Y) × (S × Unit)) ((X × Y) × (S × Unit)) ℂ} (hσ : σ.PosSemidef) :
    protMassH Prot σ = ∑ s, massSH s (Prot s) σ := by
  rw [protMassH, protDiag, Matrix.trace]
  simp only [Matrix.diag, Matrix.diagonal_mul, ite_mul, one_mul, zero_mul, Complex.re_sum]
  simp only [apply_ite Complex.re, Complex.zero_re, massSH]
  rw [← ENNReal.ofReal_sum_of_nonneg fun s _ ↦ Finset.sum_nonneg fun p _ ↦ by
    split_ifs
    · exact diag_re_nonneg hσ p
    · exact le_rfl]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_eq_single p.2.1]
  · by_cases h : Prot p.2.1 p.1.1 <;> simp [h]
  · intro s _ hs
    simp [Ne.symm hs]
  · simp

/-- The mass of a side state is unchanged by projecting onto a set that contains it. -/
theorem massSH_proj (U : Set S) [DecidablePred (· ∈ U)] (s : S) (hs : s ∈ U) (Q : X → Prop)
    [DecidablePred Q] (σ : Matrix ((X × Y) × (S × Unit)) ((X × Y) × (S × Unit)) ℂ) :
    massSH s Q ((MatrixMap.conj (sideProj U)).amplifyLeft (X × Y) σ) = massSH s Q σ := by
  rw [MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply, massSH, massSH]
  congr 1
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases h : p.2.1 = s ∧ Q p.1.1
  · rw [ite_eq_left h, ite_eq_left h]
    have hp : p.2.1 ∈ U := h.1 ▸ hs
    obtain ⟨m, t⟩ := p
    rw [Matrix.mul_apply, Finset.sum_eq_single (m, t)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (m, t)]
      · simp [kroneckerMap_apply, sideProj, hp]
      · intro k _ hk
        simp only [kroneckerMap_apply, sideProj, Matrix.one_apply, diagonal_apply]
        by_cases h1 : k.1 = m
        · by_cases h2 : k.2 = t
          · exact absurd (Prod.ext h1 h2) hk
          · simp [Ne.symm h2]
        · simp [Ne.symm h1]
      · simp
    · intro k _ hk
      by_cases h1 : m = k.1
      · by_cases h2 : t = k.2
        · exact absurd (Prod.ext h1.symm h2.symm) hk
        · simp [kroneckerMap_apply, sideProj, diagonal_apply_ne _ h2]
      · simp [kroneckerMap_apply, h1]
    · simp
  · simp only [h, ↓reduceIte]

/-- Averaging the predicate: if at most a fraction `ε` of the `b` make `x` satisfy `Q b`, the
masses of `Q b`, summed over `b`, are at most `ε |B|` times the mass of the side state. -/
theorem sum_massSH_le {B : Type*} [Fintype B] (s : S) (Q : B → X → Prop)
    [∀ b, DecidablePred (Q b)] {ε : ℝ} (hε0 : 0 ≤ ε) (hQ : ∀ x, ((Finset.univ.filter fun b ↦ Q b x).card : ℝ) ≤
      ε * Fintype.card B)
    {σ : Matrix ((X × Y) × (S × Unit)) ((X × Y) × (S × Unit)) ℂ} (hσ : σ.PosSemidef) :
    ∑ b, massSH s (Q b) σ ≤ ENNReal.ofReal (ε * Fintype.card B) * massSH s (fun _ ↦ True) σ := by
  have hε : 0 ≤ ε * Fintype.card B := mul_nonneg hε0 (Nat.cast_nonneg _)
  simp only [massSH]
  rw [← ENNReal.ofReal_sum_of_nonneg fun b _ ↦ Finset.sum_nonneg fun p _ ↦ by
    split_ifs
    · exact diag_re_nonneg hσ p
    · exact le_rfl, ← ENNReal.ofReal_mul hε]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ ↦ ?_
  by_cases hs : p.2.1 = s
  · simp only [hs, true_and, and_true, ↓reduceIte]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hQ p.1.1) (diag_re_nonneg hσ p) |>.trans_eq (by ring)
  · simp [hs]

/-- The masses of the side states add up to the trace. -/
theorem sum_massSH_true {σ : Matrix ((X × Y) × (S × Unit)) ((X × Y) × (S × Unit)) ℂ}
    (hσ : σ.PosSemidef) : ∑ s, massSH s (fun _ : X ↦ True) σ = ENNReal.ofReal σ.trace.re := by
  simp only [massSH, and_true]
  rw [← ENNReal.ofReal_sum_of_nonneg fun s _ ↦ Finset.sum_nonneg fun p _ ↦ by
    split_ifs
    · exact diag_re_nonneg hσ p
    · exact le_rfl]
  congr 1
  rw [Finset.sum_comm, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_eq_single p.2.1 (fun s _ hs ↦ by simp [Ne.symm hs]) (by simp)]
  simp

/-! ## Averaging over the hidden data -/

section hidden

variable {K Z : Type} [Fintype K] [DecidableEq K] [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable (rev : S → Finset K)

/-- Splitting the hidden data along the keys revealed in `s`. -/
def splitE (s : S) : (K → Z) ≃ ({k // k ∈ rev s} → Z) × ({k // k ∉ rev s} → Z) :=
  Equiv.piEquivPiSubtypeProd (· ∈ rev s) (fun _ ↦ Z)

theorem splitE_symm_agree (s : S) (a : {k // k ∈ rev s} → Z) (b b' : {k // k ∉ rev s} → Z) :
    ∀ k ∈ rev s, (splitE rev s).symm (a, b) k = (splitE rev s).symm (a, b') k := by
  intro k hk
  simp [splitE, Equiv.piEquivPiSubtypeProd, hk]

/-- The side states whose revealed keys are among those of `s`. -/
def belowF (s : S) : Finset S := Finset.univ.filter fun s' ↦ rev s' ⊆ rev s

/-- The same, as a set. -/
abbrev below (s : S) : Set S := ↑(belowF rev s)

theorem mem_below {s s' : S} : s' ∈ below rev s ↔ rev s' ⊆ rev s := by
  simp [below, belowF]

theorem massS_factor (s : S) (Q : X → Prop) [DecidablePred Q] :
    massS (P := P) (Res := Res) (Y := Y) s Q = fun i σ ↦
      massS s Q i ((MatrixMap.conj (sideProj (below rev s))).amplifyLeft _ σ) := by
  funext i σ
  rcases i with ⟨⟩ | j
  · exact (massSH_proj (below rev s) s ((mem_below rev).mpr subset_rfl) Q σ).symm
  · rfl

variable (g : (K → Z) → OvGame X Y S P Res)
  (Prot : (K → Z) → S → X → Prop) [∀ h s, DecidablePred (Prot h s)]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **The protected mass of one side state, averaged over the hidden data.** -/
theorem sum_queryWeight_massS_le
    (hmono : ∀ h j s, rev s ⊆ rev ((g h).trans j s).2)
    (hlocal : ∀ h h' s, (∀ k ∈ rev s, h k = h' k) →
      (g h).ov s = (g h').ov s ∧ ∀ j, (g h).trans j s = (g h').trans j s)
    (hinit : ∀ h h', (g h).init = (g h').init) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hprot : ∀ s x a, ((Finset.univ.filter fun b ↦ Prot ((splitE rev s).symm (a, b)) s x).card : ℝ) ≤
      ε * Fintype.card ({k // k ∉ rev s} → Z))
    (I : L.Interp) (G : X → Y) (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A)
    (j : ℕ) (s : S) :
    ∑ h, ((g h).sampled G).queryWeight I (massS s (Prot h s)) x
        (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j ≤
      ENNReal.ofReal ε * ∑ h, ((g h).sampled G).queryWeight I (massS s fun _ ↦ True) x
        (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j := by
  set e := splitE rev s
  have hagree : ∀ a b b' (w : ∀ i : (ovSpec X Y S P Res).Port, Matrix ((ovSpec X Y S P Res).In i ×
      (S × Unit)) ((ovSpec X Y S P Res).In i × (S × Unit)) ℂ → ℝ≥0∞),
      ((g (e.symm (a, b))).sampled G).queryWeight I
          (fun i σ ↦ w i ((MatrixMap.conj (sideProj (below rev s))).amplifyLeft _ σ)) x
          (ρ.matrix ⊗ₖ ((g (e.symm (a, b))).sampled G).init.matrix) j =
        ((g (e.symm (a, b'))).sampled G).queryWeight I
          (fun i σ ↦ w i ((MatrixMap.conj (sideProj (below rev s))).amplifyLeft _ σ)) x
          (ρ.matrix ⊗ₖ ((g (e.symm (a, b'))).sampled G).init.matrix) j := by
    intro a b b' w
    have hag : ∀ s' ∈ below rev s, ∀ k ∈ rev s', e.symm (a, b) k = e.symm (a, b') k :=
      fun s' hs' k hk ↦ splitE_symm_agree rev s a b b' k ((mem_below rev).mp hs' hk)
    exact queryWeight_eq_of_agreeOn I
      (fun j' s' h ↦ (mem_below rev).mpr ((hmono _ j' s').trans ((mem_below rev).mp h)))
      (fun j' s' h ↦ (mem_below rev).mpr ((hmono _ j' s').trans ((mem_below rev).mp h)))
      (fun s' hs' ↦ (hlocal _ _ s' (hag s' hs')).1) (fun s' hs' ↦ (hlocal _ _ s' (hag s' hs')).2)
      (hinit _ _) G w x ρ j
  obtain ⟨b₀⟩ : Nonempty ({k // k ∉ rev s} → Z) := inferInstance
  have hrun : ∀ a b (Q : X → Prop) [DecidablePred Q],
      ((g (e.symm (a, b))).sampled G).queryWeight I (massS s Q) x
          (ρ.matrix ⊗ₖ ((g (e.symm (a, b))).sampled G).init.matrix) j =
        ((g (e.symm (a, b₀))).sampled G).queryWeight I (massS s Q) x
          (ρ.matrix ⊗ₖ ((g (e.symm (a, b₀))).sampled G).init.matrix) j := by
    intro a b Q _
    rw [massS_factor rev s Q]
    exact hagree a b b₀ _
  rw [← e.symm.sum_comp, ← e.symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  simp only [hrun a _ (fun _ ↦ True)]
  calc ∑ b, ((g (e.symm (a, b))).sampled G).queryWeight I (massS s (Prot (e.symm (a, b)) s)) x
        (ρ.matrix ⊗ₖ ((g (e.symm (a, b))).sampled G).init.matrix) j
      = ∑ b, ((g (e.symm (a, b₀))).sampled G).queryWeight I (massS s (Prot (e.symm (a, b)) s)) x
          (ρ.matrix ⊗ₖ ((g (e.symm (a, b₀))).sampled G).init.matrix) j :=
        Finset.sum_congr rfl fun b _ ↦ hrun a b _
    _ = ((g (e.symm (a, b₀))).sampled G).queryWeight I
          (fun i σ ↦ ∑' b, massS s (Prot (e.symm (a, b)) s) i σ) x
          (ρ.matrix ⊗ₖ ((g (e.symm (a, b₀))).sampled G).init.matrix) j := by
        have ht := QuantumRuntime.tsum_queryWeight ((g (e.symm (a, b₀))).sampled G) I
          (fun b ↦ massS (P := P) (Res := Res) (Y := Y) s (Prot (e.symm (a, b)) s)) x
          (ρ.matrix ⊗ₖ ((g (e.symm (a, b₀))).sampled G).init.matrix) j
        rw [tsum_fintype] at ht
        exact ht
    _ ≤ ((g (e.symm (a, b₀))).sampled G).queryWeight I
          (fun i σ ↦ ENNReal.ofReal (ε * Fintype.card ({k // k ∉ rev s} → Z)) *
            massS s (fun _ ↦ True) i σ) x
          (ρ.matrix ⊗ₖ ((g (e.symm (a, b₀))).sampled G).init.matrix) j := by
        refine QuantumRuntime.queryWeight_mono _ I (fun i σ hσ ↦ ?_) x
          (ρ.prod ((g (e.symm (a, b₀))).sampled G).init).posSemidef j
        rcases i with ⟨⟩ | j'
        · rw [tsum_fintype]
          exact sum_massSH_le s (fun b ↦ Prot (e.symm (a, b)) s) hε0 (hprot s · a) hσ
        · simp [massS]
    _ = ENNReal.ofReal ε * ∑ _b : {k // k ∉ rev s} → Z,
          ((g (e.symm (a, b₀))).sampled G).queryWeight I (massS s fun _ ↦ True) x
            (ρ.matrix ⊗ₖ ((g (e.symm (a, b₀))).sampled G).init.matrix) j := by
        rw [QuantumRuntime.queryWeight_const_mul, Finset.sum_const, nsmul_eq_mul,
          ENNReal.ofReal_mul hε0, ENNReal.ofReal_natCast, Finset.card_univ]
        ring

/-- **The protected mass, averaged over the hidden data.** -/
theorem sum_queryWeight_protMass_le
    (hmono : ∀ h j s, rev s ⊆ rev ((g h).trans j s).2)
    (hlocal : ∀ h h' s, (∀ k ∈ rev s, h k = h' k) →
      (g h).ov s = (g h').ov s ∧ ∀ j, (g h).trans j s = (g h').trans j s)
    (hinit : ∀ h h', (g h).init = (g h').init) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hprot : ∀ s x a, ((Finset.univ.filter fun b ↦ Prot ((splitE rev s).symm (a, b)) s x).card : ℝ) ≤
      ε * Fintype.card ({k // k ∉ rev s} → Z))
    (I : L.Interp) (G : X → Y) (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A)
    (j : ℕ) :
    ∑ h, ((g h).sampled G).queryWeight I (protMass (Prot h)) x
        (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j ≤
      ENNReal.ofReal ε * ∑ h, ((g h).sampled G).queryWeight I
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) x (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j := by
  have hsplit : ∀ h, ((g h).sampled G).queryWeight I (protMass (Prot h)) x
      (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j =
      ∑ s, ((g h).sampled G).queryWeight I (massS s (Prot h s)) x
        (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j := by
    intro h
    have ht := QuantumRuntime.tsum_queryWeight ((g h).sampled G) I
      (fun s ↦ massS (P := P) (Res := Res) (Y := Y) s (Prot h s)) x
      (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j
    rw [tsum_fintype] at ht
    rw [ht]
    refine QuantumRuntime.queryWeight_congr _ I (fun i σ hσ ↦ ?_) x
      (ρ.prod ((g h).sampled G).init).posSemidef j
    rcases i with ⟨⟩ | j'
    · rw [tsum_fintype]
      exact protMassH_eq_sum (Prot h) hσ
    · simp [protMass, massS]
  have htr : ∀ h, ∑ s, ((g h).sampled G).queryWeight I (massS s fun _ ↦ True) x
      (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j ≤
      ((g h).sampled G).queryWeight I (fun _ σ ↦ ENNReal.ofReal σ.trace.re) x
        (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j := by
    intro h
    have ht := QuantumRuntime.tsum_queryWeight ((g h).sampled G) I
      (fun s ↦ massS (P := P) (Res := Res) (Y := Y) s fun _ ↦ True) x
      (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j
    rw [tsum_fintype] at ht
    rw [ht]
    refine QuantumRuntime.queryWeight_mono _ I (fun i σ hσ ↦ ?_) x
      (ρ.prod ((g h).sampled G).init).posSemidef j
    rcases i with ⟨⟩ | j'
    · rw [tsum_fintype]
      exact (sum_massSH_true hσ).le
    · simp [massS]
  simp only [hsplit]
  rw [Finset.sum_comm]
  calc ∑ s, ∑ h, ((g h).sampled G).queryWeight I (massS s (Prot h s)) x
        (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j
      ≤ ∑ s, ENNReal.ofReal ε * ∑ h, ((g h).sampled G).queryWeight I (massS s fun _ ↦ True) x
          (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j :=
        Finset.sum_le_sum fun s _ ↦
          sum_queryWeight_massS_le rev g Prot hmono hlocal hinit hε0 hprot I G x ρ j s
    _ = ENNReal.ofReal ε * ∑ h, ∑ s, ((g h).sampled G).queryWeight I (massS s fun _ ↦ True) x
          (ρ.matrix ⊗ₖ ((g h).sampled G).init.matrix) j := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := by gcongr with h; exact htr h

end hidden

end OvGame

end Qrom
