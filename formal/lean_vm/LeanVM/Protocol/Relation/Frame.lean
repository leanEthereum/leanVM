/-
  LeanVM.Protocol.Relation.Frame

  A fixed proposition carried through a specification: doom that already holds for a reason the
  phase does not touch stays doom.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Bind
public import LeanVM.Protocol.Verifier.Deferred

/-!
# Carrying a fixed reason for doom

The assembly's doom on a candidate stack is a disjunction: the part of the relation the current
phase checks fails, or another part does, which a later phase checks. `Spec.orConst` carries the
other part, a proposition `C` fixed before the phase runs, through a specification: from
`Pre ∨ C` to `Post ∨ C`. Where `C` holds, doom holds throughout and the potential is the
follower's lead (`Spec.constDoom`), within `εmax` when that lead is.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters VerifierProgram

@[expose] public section

variable {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop} {Post : α → List Ev → Prop}
  {εmax L T : ENNReal}

/-- **Doom throughout**: any program, doom always, the potential the follower's lead. -/
noncomputable def Spec.constDoom (Q : α → List Ev → Prop) (hQ : ∀ a h, Q a h)
    (hT : T ≤ εmax) (hTL : min 1 T ≤ L) : Spec p Pre Q εmax L T where
  D _ _ := True
  V _ _ := min 1 T
  le_one _ _ := min_le_left _ _
  start_D _ _ := trivial
  start_V _ _ := hTL
  read := by intros; trivial
  readPacked := by intros; trivial
  grind := by intros; trivial
  commit := by intros; trivial
  sample := by
    intros
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
  samplePacked := by intros; exact (avgPk_const _ _).le
  query := by intros; exact le_rfl
  moveEnd := by intro _ _ _ _ _ _ hD; exact absurd trivial hD
  retEnd := by intro _ _ _ _ _ hD; exact absurd trivial hD
  retDoom := by intros; exact le_rfl
  post := by intros; exact hQ _ _
  bound := by
    intros
    calc (2 : ENNReal)⁻¹ ^ _ * min 1 T ≤ 1 * T := by
          gcongr
          · exact pow_le_one₀ (by simp) (by norm_num)
          · exact min_le_right _ _
      _ ≤ εmax := by rw [one_mul]; exact hT

open Classical in
/-- **A fixed reason for doom, carried**: from `Pre ∨ C` to `Post ∨ C`. -/
noncomputable def Spec.orConst (S : Spec p Pre Post εmax L T) (C : Prop) (hT : T ≤ εmax)
    (hTL : min 1 T ≤ L) :
    Spec p (fun h ↦ Pre h ∨ C) (fun a h ↦ Post a h ∨ C) εmax L T :=
  (Spec.ite (c := C) (p₁ := p) (p₂ := p)
    (fun hC ↦ Spec.constDoom (Pre := fun h ↦ Pre h ∨ C) _ (fun _ _ ↦ Or.inr hC) hT hTL)
    (fun hC ↦ S.mono (fun _ h ↦ h.resolve_right hC) (fun _ _ h ↦ Or.inl h) le_rfl le_rfl
      le_rfl)).congr (ite_self p)

/-- A local run that ends at a return of `a` is a run that returns `a`. -/
theorem returns_of_after : ∀ {p : VerifierProgram α} {l : List Ev} {a : α},
    p.after l = some (.ret a) → VerifierProgram.Returns p a
  | p, [], a, h => by
    simp only [after, Option.some.injEq] at h
    subst h
    exact .ret a
  | .ret _, _ :: _, _, h => by simp [after] at h
  | .fail, _ :: _, _, h => by simp [after] at h
  | .read k, e :: es, a, h => by
    cases e <;> simp only [after, reduceCtorEq] at h
    exact .read _ (returns_of_after h)
  | .sample k, e :: es, a, h => by
    cases e <;> simp only [after, reduceCtorEq] at h
    exact .sample _ (returns_of_after h)
  | .readPacked n k, e :: es, a, h => by
    cases e <;> simp only [after, reduceCtorEq] at h
    split_ifs at h with hl
    exact .readPacked n _ hl (returns_of_after h)
  | .samplePacked n k, e :: es, a, h => by
    cases e <;> simp only [after, reduceCtorEq] at h
    split_ifs at h with hl
    exact .samplePacked n _ hl (returns_of_after h)
  | .grind b k, e :: es, a, h => by
    cases e <;> simp only [after, reduceCtorEq] at h
    split_ifs at h
    exact .grind b (returns_of_after h)
  | .commit ht w k, e :: es, a, h => by
    cases e <;> simp only [after, reduceCtorEq] at h
    split_ifs at h
    exact .commit ht w (returns_of_after h)
  | .query i ps k, e :: es, a, h => by
    cases e <;> simp only [after, reduceCtorEq] at h
    exact .query i ps _ (returns_of_after h)

/-- **A return invariant**: what every return value of the program satisfies joins the
postcondition. -/
def Spec.retInv (S : Spec p Pre Post εmax L T) (Q : α → Prop)
    (hQ : ∀ a, VerifierProgram.Returns p a → Q a) :
    Spec p Pre (fun a h ↦ Post a h ∧ Q a) εmax L T :=
  { S with post := fun hl ha hD ↦ ⟨S.post hl ha hD, hQ _ (returns_of_after ha)⟩ }

end

end LeanVM.Protocol.Compile
