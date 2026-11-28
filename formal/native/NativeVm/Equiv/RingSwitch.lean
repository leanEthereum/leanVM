module

public import NativeVm.Model.RingSwitch
public import NativeVm.Equiv.Folds
public import NativeVm.Equiv.LayoutSpec
public import NativeVm.Equiv.Transcript
public import Statement.Verifier.Lib

/-!
# Phase 7a: ring switching, the model against the statement

The map's arithmetic is the statement's through `EW.toE` (`toE_frobenius8`, `toE_ringPsi`,
`toE_ringTarget`, `toList_map_ringCoefficients`, `toE_ringWeight`), each a fold carried through the
map (`foldl_hom`). `Sim.ringSwitch`: the model's `ringSwitch` returns the target and the weight's
point and coefficients where the statement returns the target and the weight as a function; they
are related by `RingSwitchRel`, the target equal and `ringWeight` at the point and coefficients
the function at every point. `ringSwitchClaim_rel`: the claim `ringSwitchClaim` makes of them is
the statement's (`StackClaimW.Rel`), the `.ring` weight's `StackWeight.eval` the statement's
`eqAbove · ringWeight`.
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-! ## The map's arithmetic -/

theorem toE_frobenius8 (v : EW) (p : ℕ) :
    (Model.frobenius8 v p).toE = Verifier.frobenius8 v.toE p :=
  EW.toE_sqIter _ _

theorem toE_ringPsi (v : EW) (g : Array EW) :
    (Model.ringPsi v g).toE = Verifier.ringPsi v.toE (g.toList.map EW.toE) := by
  unfold Model.ringPsi Verifier.ringPsi
  rw [← Array.foldl_toList]
  have h := foldl_hom (fun p : EW × EW ↦ (p.1.toE, p.2.toE)) EW.toE
    (f := fun (acc : EW × EW) gB ↦ (acc.1 + gB * acc.2, acc.2 * acc.2))
    (g := fun (acc : E × E) gB ↦ (acc.1 + gB * acc.2, acc.2 * acc.2))
    (fun a b ↦ by simp) g.toList (0, v)
  simpa using congrArg Prod.fst h

theorem toE_ringTarget (s f g : Array EW) :
    (Model.ringTarget s f g).toE =
      Verifier.ringTarget (s.toList.map EW.toE) (f.toList.map EW.toE) (g.toList.map EW.toE) := by
  unfold Model.ringTarget Verifier.ringTarget
  dsimp only
  rw [← Array.foldl_toList]
  have h := foldl_hom (fun p : EW × EW ↦ (p.1.toE, p.2.toE)) id
    (f := fun (acc : EW × EW) p ↦
      let z := Model.frobenius8 acc.2 1
      (acc.1 + f.getD p 0 * Model.frobenius8 (Model.polyEval (s.map (Model.ringPsi · g)) z) p, z))
    (g := fun (acc : E × E) p ↦
      let z := Verifier.frobenius8 acc.2 1
      (acc.1 + (f.toList.map EW.toE).getD p 0 * Verifier.frobenius8
        (Verifier.polyEval ((s.toList.map EW.toE).map (Verifier.ringPsi · (g.toList.map EW.toE))) z)
        p, z))
    (fun a p ↦ by
      simp only [EW.toE_add, EW.toE_mul, toE_frobenius8, toE_polyEval, id]
      rw [getD_map EW.toE f p 0, EW.toE_zero, Array.toList_map, List.map_map, List.map_map]
      simp only [Function.comp_def, toE_ringPsi])
    ((Array.range Verifier.ringMapWidth).reverse.toList) (0, gen)
  simpa [toE_gen] using congrArg Prod.fst h

theorem toList_map_ringCoefficients (f g : Array EW) :
    (Model.ringCoefficients f g).toList.map EW.toE =
      Verifier.ringCoefficients (f.toList.map EW.toE) (g.toList.map EW.toE) := by
  unfold Model.ringCoefficients Verifier.ringCoefficients
  rw [← Array.foldl_toList]
  have h := foldl_hom (fun p : Array EW × Array EW ↦ (p.1.toList.map EW.toE, p.2.toList.map EW.toE))
    EW.toE
    (f := fun (acc : Array EW × Array EW) fP ↦
      (acc.1 ++ acc.2.map (fP * ·), acc.2.map (Model.frobenius8 · 1)))
    (g := fun (acc : List E × List E) fP ↦
      (acc.1 ++ acc.2.map (fP * ·), acc.2.map (Verifier.frobenius8 · 1)))
    (fun a b ↦ by simp [Function.comp_def, toE_frobenius8]) f.toList (#[], g)
  simpa using congrArg Prod.fst h

theorem toE_ringWeight (r rPrime c : Array EW) :
    (Model.ringWeight r rPrime c).toE =
      Verifier.ringWeight (r.toList.map EW.toE) (rPrime.toList.map EW.toE) (c.toList.map EW.toE) := by
  unfold Model.ringWeight Verifier.ringWeight
  rw [← Array.foldl_toList]
  have inner : ∀ (v : Array EW) (c : EW),
      ((v.zip rPrime).foldl (fun product (value, challenge) ↦
        product * (1 + value + challenge)) c).toE =
      (List.zip (v.toList.map EW.toE) (rPrime.toList.map EW.toE)).foldl
        (fun product (value, challenge) ↦ product * (1 + value + challenge)) c.toE := by
    intro v c
    rw [← Array.foldl_toList, Array.toList_zip, List.zip_map]
    exact foldl_hom EW.toE (Prod.map EW.toE EW.toE) (fun a b ↦ by simp) _ c
  have h := foldl_hom (fun p : EW × Array EW ↦ (p.1.toE, p.2.toList.map EW.toE)) EW.toE
    (f := fun (acc : EW × Array EW) c ↦
      ((acc.1 + (acc.2.zip rPrime).foldl
        (fun product (value, challenge) ↦ product * (1 + value + challenge)) c),
        acc.2.map fun value ↦ value * value))
    (g := fun (acc : E × List E) c ↦
      ((acc.1 + (List.zip acc.2 (rPrime.toList.map EW.toE)).foldl
        (fun product (value, challenge) ↦ product * (1 + value + challenge)) c),
        acc.2.map fun value ↦ value * value))
    (fun a b ↦ Prod.ext (by simp only [EW.toE_add, inner]) (by simp [Function.comp_def]))
    c.toList (0, r)
  simpa using congrArg Prod.fst h

/-! ## The phase -/

/-- What `ringSwitch` returns against the statement's: the target, and the weight's point and
coefficients evaluating as the weight at every point. -/
def RingSwitchRel (a : EW × Array EW × Array EW) (b : E × (List E → E)) : Prop :=
  a.1.toE = b.1 ∧ ∀ x : Array EW, (Model.ringWeight a.2.1 x a.2.2).toE = b.2 (x.toList.map EW.toE)

/-- **Phase 7a.** -/
theorem Sim.ringSwitch {point s : Array EW} {point' s' : List E}
    (hp : point.toList.map EW.toE = point') (hs : s.toList.map EW.toE = s') :
    Sim (Model.ringSwitch point s) (Verifier.ringSwitch point' s') RingSwitchRel := by
  unfold Model.ringSwitch Verifier.ringSwitch
  refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
  refine Sim.bind (Sim.sampleChallenges _) fun ch ch' ⟨hch, _⟩ ↦ ?_
  refine Sim.pure ⟨?_, fun x ↦ ?_⟩
  · simp only
    rw [toE_ringTarget, hs, Array.toList_extract, Array.toList_extract]
    subst hch
    simp only [List.extract_eq_take_drop, List.map_take, List.map_drop, Nat.sub_zero,
      List.drop_zero]
    rw [List.take_of_length_le (l := List.drop _ _) (by simp)]
  · simp only
    rw [toE_ringWeight, hp, toList_map_ringCoefficients]
    subst hch
    simp only [Array.toList_extract, List.extract_eq_take_drop, List.map_take, List.map_drop,
      Nat.sub_zero, List.drop_zero]
    rw [List.take_of_length_le (l := List.drop _ _) (by simp)]

/-! ## The claim -/

theorem LayoutW.placement_toSpec (l : LayoutW) (c : ℕ) : l.placement c = l.toSpec.placement c := by
  simp [LayoutW.placement, Verifier.Layout.placement, LayoutW.toSpec]

theorem toE_eqAbove (p : Verifier.Placement) (x : Array EW) :
    (Model.eqAbove p x).toE = p.eqAbove (x.toList.map EW.toE) := by
  unfold Model.eqAbove Verifier.Placement.eqAbove
  rw [toE_eqEval, toList_map_selectorPoint, Array.toList_extract]
  simp only [List.extract_eq_take_drop]
  rw [List.take_of_length_le (l := List.drop _ _) (by simp), List.map_drop, List.length_map,
    Array.length_toList]

/-- **The ring-switched claim** is the statement's. -/
theorem ringSwitchClaim_rel (layout : LayoutW) {a : EW × Array EW × Array EW}
    {b : E × (List E → E)} (h : RingSwitchRel a b) :
    StackClaimW.Rel (Model.ringSwitchClaim layout a.1 a.2.1 a.2.2)
      (Verifier.ringSwitchClaim layout.toSpec b.1 b.2) := by
  refine ⟨fun x ↦ ?_, h.1⟩
  simp only [Model.ringSwitchClaim, Verifier.ringSwitchClaim, StackWeight.eval]
  rw [EW.toE_mul, toE_eqAbove, h.2, Array.toList_extract, LayoutW.placement_toSpec]
  simp [List.extract_eq_take_drop, List.map_take]

end NativeVm.Equiv
