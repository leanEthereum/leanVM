module

public import Qrom.SideEvents

@[expose] public section

/-!
# Reading a protected input

Averaged over the hidden data, the weight of the leaves `p` whose output set `out p` contains an
input protected at the final side state is at most `k ε` times the total weight, when every output
set has at most `k` inputs and at most a fraction `ε` of the unrevealed values protect any input
(`Qrom.OvGame.sum_sideW_protHit_le`). On the side state `s`, the joint post-state depends on the
hidden data only through the keys revealed in `s` (`Qrom.OvGame.conj_jointPost_eq_of_agreeOn`), so
the protected indicator averages over the others first.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum Quantum.MatrixMap

namespace OvGame

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The weight of the side state `s` in a joint operator. -/
noncomputable def blockW {B : Type*} [Fintype B] (s : S) (J : Matrix (B × (S × Unit)) (B × (S × Unit)) ℂ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (∑ b, (J (b, (s, ())) (b, (s, ()))).re)

theorem one_kronecker_diagonal {B T : Type*} [Fintype B] [DecidableEq B] [DecidableEq T]
    (d : T → ℂ) :
    (1 : Matrix B B ℂ) ⊗ₖ diagonal d = diagonal fun q : B × T ↦ d q.2 := by
  ext ⟨b, t⟩ ⟨b', t'⟩
  rcases eq_or_ne b b' with rfl | hb
  · rcases eq_or_ne t t' with rfl | ht
    · simp [kroneckerMap_apply]
    · simp [kroneckerMap_apply, ht]
  · simp [kroneckerMap_apply, hb]

theorem conj_diagonal_apply_self {T : Type*} [Fintype T] [DecidableEq T] (d : T → ℂ)
    (J : Matrix T T ℂ) (q : T) :
    (MatrixMap.conj (diagonal d) J) q q = d q * J q q * star (d q) := by
  rw [MatrixMap.conj_apply, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

theorem trace_conj_evProj_eq {B : Type*} [Fintype B] [DecidableEq B] (e : S → Bool)
    {J : Matrix (B × (S × Unit)) (B × (S × Unit)) ℂ} (hJ : J.PosSemidef) :
    ENNReal.ofReal (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ evProj e) J).trace.re =
      ∑ s, if e s then blockW s J else 0 := by
  have hdiag : ∀ q, 0 ≤ (J q q).re := fun q ↦ (RCLike.nonneg_iff.mp (hJ.diag_nonneg (i := q))).1
  have hentry : ∀ q : B × (S × Unit), (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ evProj e) J) q q =
      if e q.2.1 then J q q else 0 := by
    intro q
    rw [evProj, one_kronecker_diagonal, conj_diagonal_apply_self]
    by_cases h : e q.2.1 <;> simp [h]
  rw [Matrix.trace, Complex.re_sum]
  simp only [Matrix.diag, hentry]
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]
  simp only [Fintype.univ_punit, Finset.sum_singleton]
  rw [ENNReal.ofReal_sum_of_nonneg fun s _ ↦ Finset.sum_nonneg fun b _ ↦ by
    split_ifs
    · exact hdiag _
    · simp]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases h : e s
  · simp [h, blockW]
  · simp [h]

/-- The weight of a side state is unchanged by projecting onto a set that contains it. -/
theorem blockW_proj {B : Type*} [Fintype B] [DecidableEq B] (U : Set S) [DecidablePred (· ∈ U)]
    (s : S) (hs : s ∈ U) (J : Matrix (B × (S × Unit)) (B × (S × Unit)) ℂ) :
    blockW s ((MatrixMap.conj (sideProj U)).amplifyLeft B J) = blockW s J := by
  rw [MatrixMap.amplifyLeft_conj, sideProj, one_kronecker_diagonal, blockW, blockW]
  congr 1
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [conj_diagonal_apply_self]
  simp [hs]

section hidden

variable {K Z : Type} [Fintype K] [DecidableEq K] [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable (rev : S → Finset K) (g : (K → Z) → OvGame X Y S P Res)
  (Prot : (K → Z) → S → X → Prop) [∀ h s, DecidablePred (Prot h s)]

theorem sideW_eq_sum (g' : OvGame X Y S P Res) (G : X → Y) (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (ev : (Σ u, W u) → S → Bool) :
    sideW g' G I x ρ ev =
      ∑' p, ∑ s, if ev p s then blockW s ((g'.sampled G).jointPost I x ρ p).matrix else 0 :=
  tsum_congr fun p ↦ trace_conj_evProj_eq (ev p) ((g'.sampled G).jointPost I x ρ p).posSemidef

/-- **Reading a protected input.** -/
theorem sum_sideW_protHit_le
    (hmono : ∀ h j s, rev s ⊆ rev ((g h).trans j s).2)
    (hlocal : ∀ h h' s, (∀ k ∈ rev s, h k = h' k) → (g h).ov s = (g h').ov s)
    (hlocalTr : ∀ h h' j s, (∀ k ∈ rev ((g h).trans j s).2, h k = h' k) →
      (g h).trans j s = (g h').trans j s)
    (hinit : ∀ h h', (g h).init = (g h').init) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hprot : ∀ s x a, ((Finset.univ.filter fun b ↦ Prot ((splitE rev s).symm (a, b)) s x).card : ℝ) ≤
      ε * Fintype.card ({k // k ∉ rev s} → Z))
    (I : L.Interp) (G : X → Y) (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A)
    (out : (Σ u, W u) → Finset X) (k : ℕ) (hout : ∀ p, (out p).card ≤ k) :
    ∑ h, sideW (g h) G I x ρ (fun p s ↦ decide (∃ z ∈ out p, Prot h s z)) ≤
      ENNReal.ofReal (k * ε) * ∑ h, sideW (g h) G I x ρ (fun _ _ ↦ true) := by
  simp only [sideW_eq_sum]
  rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable),
    ← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  simp only [↓reduceIte]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun h s ↦ blockW s _), Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  set e := splitE rev s
  have hagree : ∀ a b b', blockW s (((g (e.symm (a, b))).sampled G).jointPost I x ρ p).matrix =
      blockW s (((g (e.symm (a, b'))).sampled G).jointPost I x ρ p).matrix := by
    intro a b b'
    have hj := conj_jointPost_eq_of_agreeOn (U := below rev s) I
      (fun j' s' h ↦ (mem_below rev).mpr ((hmono _ j' s').trans ((mem_below rev).mp h)))
      (fun j' s' h ↦ (mem_below rev).mpr ((hmono _ j' s').trans ((mem_below rev).mp h)))
      (agree_below rev g hlocal hlocalTr (splitE_symm_agree rev s a b b')).1
      (agree_below rev g hlocal hlocalTr (splitE_symm_agree rev s a b b')).2
      (hinit _ _) G x ρ p
    rw [← blockW_proj (below rev s) s ((mem_below rev).mpr subset_rfl), hj,
      blockW_proj (below rev s) s ((mem_below rev).mpr subset_rfl)]
  obtain ⟨b₀⟩ : Nonempty ({k // k ∉ rev s} → Z) := inferInstance
  rw [← e.symm.sum_comp, ← e.symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  simp only [hagree a _ b₀]
  have hcount : ((Finset.univ.filter fun b ↦ ∃ z ∈ out p, Prot (e.symm (a, b)) s z).card : ℝ) ≤
      k * ε * Fintype.card ({k // k ∉ rev s} → Z) := by
    calc ((Finset.univ.filter fun b ↦ ∃ z ∈ out p, Prot (e.symm (a, b)) s z).card : ℝ)
        ≤ ∑ z ∈ out p, ((Finset.univ.filter fun b ↦ Prot (e.symm (a, b)) s z).card : ℝ) := by
          rw [← Nat.cast_sum]
          refine Nat.cast_le.mpr ((Finset.card_le_card fun b hb ↦ ?_).trans Finset.card_biUnion_le)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
          obtain ⟨z, hz, hp⟩ := hb
          exact Finset.mem_biUnion.mpr ⟨z, hz, by simpa using hp⟩
      _ ≤ ∑ _z ∈ out p, ε * Fintype.card ({k // k ∉ rev s} → Z) :=
          Finset.sum_le_sum fun z _ ↦ hprot s z a
      _ ≤ k * ε * Fintype.card ({k // k ∉ rev s} → Z) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hout p) (by positivity)
  calc ∑ b, (if decide (∃ z ∈ out p, Prot (e.symm (a, b)) s z) then
        blockW s (((g (e.symm (a, b₀))).sampled G).jointPost I x ρ p).matrix else 0)
      = ((Finset.univ.filter fun b ↦ ∃ z ∈ out p, Prot (e.symm (a, b)) s z).card : ℝ≥0∞) *
          blockW s (((g (e.symm (a, b₀))).sampled G).jointPost I x ρ p).matrix := by
        simp only [decide_eq_true_eq]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (k * ε * Fintype.card ({k // k ∉ rev s} → Z)) *
          blockW s (((g (e.symm (a, b₀))).sampled G).jointPost I x ρ p).matrix := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hcount
    _ = ENNReal.ofReal (k * ε) * ∑ _b : {k // k ∉ rev s} → Z,
          blockW s (((g (e.symm (a, b₀))).sampled G).jointPost I x ρ p).matrix := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, Finset.card_univ]
        ring

end hidden

end OvGame

end Qrom
