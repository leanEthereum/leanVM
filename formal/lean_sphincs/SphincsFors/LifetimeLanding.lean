import SphincsFors.Landing
import SphincsFors.SecurityDigest

/-!
The kept view of a digest (its local index in the pruned subtree and all 24 FORS selectors), and
the law of a fresh uniform digest that lands: landing with a kept view in a set costs exactly the
reciprocal number of subtrees times the uniform probability of that set.
-/

namespace SphincsFors.Lifetime

set_option exponentiation.threshold 512

open OracleComp OracleSpec ENNReal Concrete

variable [Params]

abbrev KeptDigestView := Fin (2 ^ subtreeHeight) × (IndexGroup → FtsLeaf)

/-- The local index and the 24 FORS coordinates, defined even for a rejected global index. -/
def localFullView (view : FullDigestView) : KeptDigestView :=
  (⟨view.1.val % 2 ^ subtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩, view.2)

def keptViewEquiv (parameter : PublicParameter) :
    KeptDigestView ≃ {view : FullDigestView // Landed parameter view.1} where
  toFun view := ⟨((keptLeafEquiv parameter view.1).val, view.2),
    (keptLeafEquiv parameter view.1).property⟩
  invFun view := localFullView view.val
  left_inv view := by
    apply Prod.ext
    · exact (keptLeafEquiv parameter).left_inv view.1
    · rfl
  right_inv view := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ((keptLeafEquiv parameter).right_inv ⟨view.val.1, view.property⟩)
    · rfl

theorem local_keptView (parameter : PublicParameter) (view : KeptDigestView) :
    localFullView (keptViewEquiv parameter view).val = view :=
  (keptViewEquiv parameter).left_inv view

def keptFilteredEquiv (parameter : PublicParameter) (P : KeptDigestView → Prop) :
    {view : KeptDigestView // P view} ≃
      {view : FullDigestView // Landed parameter view.1 ∧ P (localFullView view)} where
  toFun view := ⟨(keptViewEquiv parameter view.val).val,
    (keptViewEquiv parameter view.val).property, by simpa only [local_keptView] using view.property⟩
  invFun view := ⟨localFullView view.val, view.property.2⟩
  left_inv view := by apply Subtype.ext; exact local_keptView parameter view.val
  right_inv view := by
    exact Subtype.ext (congrArg
      (fun v : {view : FullDigestView // Landed parameter view.1} => v.val)
      ((keptViewEquiv parameter).right_inv ⟨view.val, view.property.1⟩))

theorem fullDigestView_card_factor :
    Fintype.card FullDigestView = 2 ^ (totalHeight - subtreeHeight) *
      Fintype.card KeptDigestView := by
  simp only [FullDigestView, KeptDigestView, Fintype.card_prod, Fintype.card_fin,
    mul_assoc, ← subtree_size_mul]

def localDigestView (digest : MessageDigest) : KeptDigestView :=
  localFullView (fullDigestView digest)

/-- Joint event factorization: acceptance only costs the reciprocal number of subtrees. -/
theorem probEvent_landed_localDigest (parameter : PublicParameter)
    (P : KeptDigestView → Prop) [DecidablePred P] :
    Pr[fun digest => Landed parameter (digestIndex digest) ∧ P (localDigestView digest) |
      ($ᵗ MessageDigest : ProbComp MessageDigest)] =
        ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ *
          Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  change Pr[(fun view : FullDigestView => Landed parameter view.1 ∧ P (localFullView view)) ∘
    fullDigestView | _] = _
  rw [← probEvent_map, probEvent_congr' (fun _ _ => Iff.rfl) evalDist_fullDigestView_uniform]
  rw [probEvent_uniformSample, probEvent_uniformSample, ← Fintype.card_subtype,
    ← Fintype.card_subtype, ← Fintype.card_congr (keptFilteredEquiv parameter P),
    fullDigestView_card_factor, Nat.cast_mul]
  simp only [div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  ring

end SphincsFors.Lifetime
