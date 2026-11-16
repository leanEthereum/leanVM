module

public import Quantum.Sphincs.Hybrid.DigestStage

@[expose] public section

/-!
# The `H_msg` paths' rates apart from the randomizer and `SK.seed`-keyed rates

The template programs `H_msg` paths at every randomizer, so their first blocks' rates must avoid
the randomizer stage's and the `SK.seed`-keyed rates for every randomizer value, not only the
staged ones.

* `sepCell P s`: the randomizer-stage and `SK.seed`-keyed first blocks; `HRateSep x`: every
  `H_msg` path at every root and randomizer has a rate apart from them, in `schemeSplit`'s
  coordinates.
* `card_mul_card_filter_rate_cross_le`: two families of points, pairwise distinct across, share a
  rate after a uniform permutation for at most `|A| |B| / |X|` of the permutations.
* `hRateSep_frac_le_keccak`: at most `2^-318` of the tables fail `HRateSep`.
* `hRateSep_table`: `HRateSep` read on the table's own keys, `π`, `PK.seed`, `SK.seed` and `SK.prf`.
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer MasterSeed)
open Quantum.Xmss (X Z trunc128)
open Quantum.Xmss.Hybrid (rateOf)
open Quantum.Sphincs.Hybrid

namespace Quantum.Sphincs.Assembly

/-! ## Rate collisions across two families of points, over abstract index types -/

/-- A pointwise implication between zero-one indicators (instances by unification). -/
theorem ite_one_le_ite_one {p q : Prop} {_ : Decidable p} {_ : Decidable q} (h : p → q) :
    (if p then 1 else 0 : ℕ) ≤ if q then 1 else 0 := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left (h hp)]
  · rw [ite_eq_right hp]
    exact Nat.zero_le _

/-- **Two families of points rarely share a rate after a uniform permutation**: for `p a ≠ q b`,
the rates of `π (p a)` and `π (q b)` meet for at most `|A| |B| / |X|` of the permutations. -/
theorem card_mul_card_filter_rate_cross_le {A B : Type*} [Fintype A] [Fintype B]
    (p : A → X × Z) (q : B → X × Z) (hpq : ∀ a b, p a ≠ q b) :
    Fintype.card X *
        (Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ∃ a b, (π (p a)).1 = (π (q b)).1).card ≤
      Fintype.card (Equiv.Perm (X × Z)) * (Fintype.card A * Fintype.card B) := by
  have hle : ∀ π : Equiv.Perm (X × Z),
      (if ∃ a b, (π (p a)).1 = (π (q b)).1 then 1 else 0) ≤
        ∑ ab : A × B, (if (π (p ab.1)).1 = (π (q ab.2)).1 then 1 else 0) := by
    intro π
    by_cases h : ∃ a b, (π (p a)).1 = (π (q b)).1
    · obtain ⟨a, b, hab⟩ := h
      rw [ite_eq_left ⟨a, b, hab⟩]
      calc 1 = (if (π (p (a, b).1)).1 = (π (q (a, b).2)).1 then 1 else 0) :=
            (ite_eq_left hab).symm
        _ ≤ _ := Finset.single_le_sum (f := fun ab : A × B ↦
            (if (π (p ab.1)).1 = (π (q ab.2)).1 then 1 else 0))
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (a, b))
    · rw [ite_eq_right h]
      exact Nat.zero_le _
  have hab : ∀ ab : A × B, Fintype.card X * ∑ π : Equiv.Perm (X × Z),
      (if (π (p ab.1)).1 = (π (q ab.2)).1 then 1 else 0) ≤ Fintype.card (Equiv.Perm (X × Z)) := by
    intro ab
    rw [← Finset.card_filter]
    exact Quantum.Xmss.Hybrid.card_mul_card_filter_rate_eq_le (hpq ab.1 ab.2)
  rw [Finset.card_filter]
  calc Fintype.card X * ∑ π : Equiv.Perm (X × Z),
        (if ∃ a b, (π (p a)).1 = (π (q b)).1 then 1 else 0)
      ≤ Fintype.card X * ∑ π : Equiv.Perm (X × Z), ∑ ab : A × B,
          (if (π (p ab.1)).1 = (π (q ab.2)).1 then 1 else 0) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun π _ ↦ hle π)
    _ = ∑ ab : A × B, Fintype.card X * ∑ π : Equiv.Perm (X × Z),
          (if (π (p ab.1)).1 = (π (q ab.2)).1 then 1 else 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _ab : A × B, Fintype.card (Equiv.Perm (X × Z)) := Finset.sum_le_sum fun ab _ ↦ hab ab
    _ = Fintype.card (Equiv.Perm (X × Z)) * (Fintype.card A * Fintype.card B) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod, mul_comm]

/-! ## The separation -/

/-- The randomizer-stage and `SK.seed`-keyed first blocks. -/
def sepCell (P : PublicParameter) (s : Secret) : Message ⊕ SkIdx → X :=
  Sum.elim (fun M ↦ rCell M P s.2) (skCell P s.1)

/-- Every `H_msg` path at every root and randomizer has a rate apart from them. -/
def HRateSep (x : Pub × Secret) : Prop :=
  ∀ (a : DLab) (R : Randomizer) (b : Message ⊕ SkIdx),
    rateOf x.1.1.1.2.1 x.1.1.2 (dLabCell a (pubParam x.1) R) ≠
      rateOf x.1.1.1.2.1 x.1.1.2 (sepCell (pubParam x.1) x.2 b)

/-- An `H_msg` path's input point at the coordinates other than `π`. -/
def hPt (r : SpongeKeys X Z × PubSlots × Secret) (aR : DLab × Randomizer) : X × Z :=
  (dLabCell aR.1 (trunc128 r.2.1.2.1) aR.2, r.1.2.1 (dLabCell aR.1 (trunc128 r.2.1.2.1) aR.2))

/-- A randomizer-stage or `SK.seed`-keyed input point at the coordinates other than `π`. -/
def sPt (r : SpongeKeys X Z × PubSlots × Secret) (b : Message ⊕ SkIdx) : X × Z :=
  (sepCell (trunc128 r.2.1.2.1) r.2.2 b, r.1.2.1 (sepCell (trunc128 r.2.1.2.1) r.2.2 b))

theorem hPt_ne_sPt (r : SpongeKeys X Z × PubSlots × Secret) (aR : DLab × Randomizer)
    (b : Message ⊕ SkIdx) : hPt r aR ≠ sPt r b := by
  intro h
  have h1 : dLabCell aR.1 (trunc128 r.2.1.2.1) aR.2 = sepCell (trunc128 r.2.1.2.1) r.2.2 b :=
    congrArg Prod.fst h
  rcases b with M | b
  · exact rCell_ne_dLabCell M _ _ aR.1 _ aR.2 h1.symm
  · exact skCell_ne_dLabCell _ _ b aR.1 _ aR.2 h1.symm

theorem rateOf_dLabCell_coordPi (π : Equiv.Perm (X × Z)) (r : SpongeKeys X Z × PubSlots × Secret)
    (a : DLab) (R : Randomizer) :
    rateOf (coordPi (π, r)).1.1.1.2.1 (coordPi (π, r)).1.1.2
      (dLabCell a (pubParam (coordPi (π, r)).1) R) = (π (hPt r (a, R))).1 :=
  rfl

theorem rateOf_sepCell_coordPi (π : Equiv.Perm (X × Z)) (r : SpongeKeys X Z × PubSlots × Secret)
    (b : Message ⊕ SkIdx) :
    rateOf (coordPi (π, r)).1.1.1.2.1 (coordPi (π, r)).1.1.2
      (sepCell (pubParam (coordPi (π, r)).1) (coordPi (π, r)).2 b) = (π (sPt r b)).1 :=
  rfl

theorem exists_of_not_hRateSep (π : Equiv.Perm (X × Z)) (r : SpongeKeys X Z × PubSlots × Secret)
    (h : ¬HRateSep (coordPi (π, r))) : ∃ aR b, (π (hPt r aR)).1 = (π (sPt r b)).1 := by
  simp only [HRateSep, ne_eq, not_forall, not_not] at h
  obtain ⟨a, R, b, h⟩ := h
  exact ⟨(a, R), b, (rateOf_dLabCell_coordPi π r a R).symm.trans
    (h.trans (rateOf_sepCell_coordPi π r b))⟩

open scoped Classical in
/-- The indicator of `¬HRateSep` (named: sums of it are compared syntactically). -/
noncomputable def notSepInd (x : Pub × Secret) : ℕ :=
  if ¬HRateSep x then 1 else 0

theorem notSepInd_coordPi_le (π : Equiv.Perm (X × Z)) (r : SpongeKeys X Z × PubSlots × Secret)
    {_ : Decidable (∃ aR b, (π (hPt r aR)).1 = (π (sPt r b)).1)} :
    notSepInd (coordPi (π, r)) ≤
      if ∃ aR b, (π (hPt r aR)).1 = (π (sPt r b)).1 then 1 else 0 :=
  ite_one_le_ite_one (exists_of_not_hRateSep π r)

/-- **Averaged over `π`**: at most `|DLab × Randomizer| |Message ⊕ SkIdx| / |X|` of the
coordinates fail `HRateSep`. -/
theorem card_mul_sum_notSepInd_le :
    Fintype.card X * ∑ x : Pub × Secret, notSepInd x ≤
      Fintype.card (Pub × Secret) *
        (Fintype.card (DLab × Randomizer) * Fintype.card (Message ⊕ SkIdx)) := by
  refine Quantum.Xmss.Hybrid.card_mul_sum_equiv_prod_le coordPi _ _ notSepInd fun r ↦ ?_
  refine le_trans (Nat.mul_le_mul_left _ ?_)
    (card_mul_card_filter_rate_cross_le (hPt r) (sPt r) (hPt_ne_sPt r))
  rw [Finset.card_filter]
  exact Finset.sum_le_sum fun π _ ↦ notSepInd_coordPi_le π r

set_option exponentiation.threshold 4096 in
theorem card_dLab_randomizer : Fintype.card (DLab × Randomizer) = 2 ^ 513 := by
  simp only [DLab, Fintype.card_prod, Fintype.card_fin, Quantum.Xmss.Hybrid.R0.card_bitVec_eq]
  norm_num [HashSig.digestBits, digestCallCount]

theorem card_sepIdx_le : Fintype.card (Message ⊕ SkIdx) ≤ 2 ^ 256 + 2 ^ 44 := by
  rw [Fintype.card_sum, card_message]
  exact Nat.add_le_add_left card_skIdx_le _

set_option exponentiation.threshold 4096 in
/-- `|DLab × Randomizer| |Message ⊕ SkIdx| / |X| ≤ 2^-318`. -/
theorem hRateSepTerm_le_keccak :
    ((Fintype.card (DLab × Randomizer) * Fintype.card (Message ⊕ SkIdx) : ℕ) : ℝ≥0∞) /
        Fintype.card X ≤ ENNReal.ofReal (1 / 2 ^ 318) := by
  have hK := Nat.mul_le_mul card_dLab_randomizer.le card_sepIdx_le
  refine (ENNReal.div_le_div_right (Nat.cast_le.mpr hK) _).trans ?_
  rw [Quantum.Xmss.Hybrid.R0.card_rate,
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

open scoped Classical in
/-- **At most `2^-318` of the tables fail `HRateSep`.** -/
theorem hRateSep_frac_le_keccak :
    (Fintype.card Tab : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun t : Tab ↦ ¬HRateSep (schemeSplit t)).card : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / 2 ^ 318) := by
  have hsum : (Finset.univ.filter fun t : Tab ↦ ¬HRateSep (schemeSplit t)).card =
      ∑ t : Tab, notSepInd (schemeSplit t) := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun _ _ ↦ rfl
  have hc : Fintype.card X * ∑ t : Tab, notSepInd (schemeSplit t) ≤
      Fintype.card Tab *
        (Fintype.card (DLab × Randomizer) * Fintype.card (Message ⊕ SkIdx)) :=
    Quantum.Xmss.Hybrid.card_mul_sum_equiv_le schemeSplit notSepInd _ _ card_mul_sum_notSepInd_le
  rw [hsum]
  have h := Quantum.Xmss.Hybrid.natCast_le_mul_div_of_mul_le Fintype.card_ne_zero hc
  have hN : (Fintype.card Tab : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine (mul_le_mul' le_rfl h).trans ?_
  rw [ENNReal.inv_mul_cancel_left hN (ENNReal.natCast_ne_top _)]
  exact hRateSepTerm_le_keccak

/-- **The separation on the table**: when the hidden capacities are distinct, `HRateSep` at
`schemeSplit t` separates the `H_msg` rates from the randomizer and `SK.seed`-keyed rates of the
table's own keys, `π`, `PK.seed`, `SK.seed` and `SK.prf`. -/
theorem hRateSep_table {t : Tab}
    (hinj : Function.Injective (posOf (schemeSplit t).1 (schemeSplit t).2))
    (h : HRateSep (schemeSplit t)) (a : DLab) (R : Randomizer) :
    (∀ M, rateOf t.1.keys.2.1 t.1.perm (dLabCell a t.1.publicSeed R) ≠
        rateOf t.1.keys.2.1 t.1.perm (rCell M t.1.publicSeed t.1.prfKey)) ∧
      ∀ b, rateOf t.1.keys.2.1 t.1.perm (dLabCell a t.1.publicSeed R) ≠
        rateOf t.1.keys.2.1 t.1.perm (skCell t.1.publicSeed t.1.secretSeed b) := by
  have hP := (schemeSplit_transfer t hinj).1
  have hk : (schemeSplit t).1.1.1.2.1 = t.1.keys.2.1 := congrArg Prod.fst (schemeSplit_keys_snd t)
  have h' : ∀ b, rateOf t.1.keys.2.1 t.1.perm (dLabCell a t.1.publicSeed R) ≠
      rateOf t.1.keys.2.1 t.1.perm
        (sepCell t.1.publicSeed (t.1.secretSeed, t.1.prfKey) b) := by
    intro b
    have hb := h a R b
    rwa [hP, hk, schemeSplit_perm, schemeSplit_snd] at hb
  exact ⟨fun M ↦ h' (Sum.inl M), fun b ↦ h' (Sum.inr b)⟩

end Quantum.Sphincs.Assembly

end
