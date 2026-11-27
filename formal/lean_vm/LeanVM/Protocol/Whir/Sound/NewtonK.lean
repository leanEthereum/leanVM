/-
  LeanVM.Protocol.Whir.Sound.NewtonK

  One-error Newton decoding with its nodes in `K`.
-/

module

public import LeanVM.Protocol.Whir.Sound.Newton
import LeanVM.Parameters.Field
public import Statement.Field

/-!
# Newton decoding with nodes in `K`

The decoder's nodes are domain points, in `K`: the Newton form evaluated with products in `E × K`
(`nEvalK`), the nodal values and their inverses in `K` (`nodalK`), the error's node located with
a product by a `K` element (`decode1K`). Each is the decoder over `E` on the nodes lifted
(`nEvalK_eq`, `nFormK_eq`, `decode1K_eq`).
-/

namespace LeanVM.Protocol.Whir.Sound.Newton

open LeanVM.Parameters

@[expose] public section

theorem ofK_inv (a : K) : ofK a⁻¹ = (ofK a)⁻¹ := map_inv₀ (algebraMap K E) a

theorem ofK_listProd (l : List K) : ofK l.prod = (l.map ofK).prod := map_list_prod (algebraMap K E) l

/-- The Newton form evaluated, nodes and point in `K`. -/
def nEvalK : List K → List E → K → E
  | x :: xs, a :: as, z =>
    let r := nEvalK xs as z
    let t := ofK (z - x) * r
    a + t
  | [], a :: _, _ => a
  | _, [], _ => 0

/-- `∏ (z − x_i)` in `K`. -/
def nodalK (xs : List K) (z : K) : K := (xs.map fun x ↦ z - x).prod

/-- One point added, its node in `K` (`E` has characteristic two: `y − P(x) = y + P(x)`). -/
def nStepK (st : List K × List E) (p : K × E) : List K × List E :=
  let e := nEvalK st.1 st.2 p.1
  let y := p.2 + e
  let c := ofK (nodalK st.1 p.1)⁻¹
  (st.1 ++ [p.1], st.2 ++ [y * c])

/-- The Newton coefficients, nodes in `K`. -/
def nFormK (pts : List (K × E)) : List K × List E := pts.foldl nStepK ([], [])

/-- The points with their nodes lifted to `E`. -/
def liftPts (pts : List (K × E)) : List (E × E) := pts.map fun p ↦ (ofK p.1, p.2)

theorem nEvalK_eq : ∀ (xs : List K) (as : List E) (z : K),
    nEvalK xs as z = nEval (xs.map ofK) as (ofK z)
  | x :: xs, a :: as, z => by
    rw [nEvalK, List.map_cons, nEval, nEvalK_eq xs as z, ofK_sub]
  | [], a :: _, _ => rfl
  | [], [], _ => rfl
  | _ :: _, [], _ => rfl

theorem nodalK_eq (xs : List K) (z : K) : ofK (nodalK xs z) = nodal (xs.map ofK) (ofK z) := by
  unfold nodalK nodal
  rw [ofK_listProd, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ ↦ ?_
  simp [ofK_sub]

theorem nFormK_eq (pts : List (K × E)) :
    nForm (liftPts pts) = ((nFormK pts).1.map ofK, (nFormK pts).2) := by
  unfold nForm nFormK liftPts
  induction pts using List.reverseRecOn with
  | nil => rfl
  | append_singleton pts p ih =>
    rw [List.map_append, List.foldl_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, nStep, nStepK,
      List.map_append, nEvalK_eq, ofK_inv, nodalK_eq, CharTwo.sub_eq_add]

/-- The points but the first at the node `x` with `a_{d+2}·(x − x_{d+2}) = a_{d+1}`. -/
def dropLoc (d : ℕ) (f : List K × List E) (pts : List (K × E)) : List (K × E) :=
  let a2 := f.2.getD (d + 2) 0
  let a1 := f.2.getD (d + 1) 0
  let x2 := (pts.getD (d + 2) (0, 0)).1
  pts.eraseIdx (pts.findIdx fun p ↦
    let u := ofK (p.1 - x2)
    let v := a2 * u
    decide (v = a1))

/-- **One-error decoding, nodes in `K`.** -/
def decode1K (d : ℕ) (pts : List (K × E)) : Option (List K × List E) :=
  let f := nFormK pts
  let a2 := f.2.getD (d + 2) 0
  let a1 := f.2.getD (d + 1) 0
  if a2 = 0 then
    if a1 = 0 then some f else none
  else
    let pts' := dropLoc d f pts
    let f' := nFormK pts'
    if pts'.length = d + 2 ∧ f'.2.getD (d + 1) 0 = 0 then some f' else none

theorem length_liftPts (pts : List (K × E)) : (liftPts pts).length = pts.length := by
  simp [liftPts]

theorem decode1K_eq (d : ℕ) (pts : List (K × E)) :
    decode1 d (liftPts pts) = (decode1K d pts).map fun f ↦ (f.1.map ofK, f.2) := by
  have hx2 : ((liftPts pts).getD (d + 2) (0, 0)).1 = ofK ((pts.getD (d + 2) (0, 0)).1) := by
    unfold liftPts
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases pts[d + 2]? with
    | none => exact (map_zero (algebraMap K E)).symm
    | some q => rfl
  have hfind : ∀ (a2 a1 : E), (liftPts pts).findIdx (fun p ↦
      decide (a2 * (p.1 - ofK ((pts.getD (d + 2) (0, 0)).1)) = a1)) =
      pts.findIdx (fun p ↦ decide (a2 * ofK (p.1 - (pts.getD (d + 2) (0, 0)).1) = a1)) := by
    intro a2 a1
    unfold liftPts
    rw [List.findIdx_map]
    refine congrArg (List.findIdx · pts) (funext fun p ↦ ?_)
    simp only [Function.comp_apply, ofK_sub]
  have herase : ∀ i, (liftPts pts).eraseIdx i = liftPts (pts.eraseIdx i) := fun i ↦ by
    unfold liftPts
    rw [List.eraseIdx_map]
  set a2 := (nFormK pts).2.getD (d + 2) 0
  set a1 := (nFormK pts).2.getD (d + 1) 0
  have hf := nFormK_eq pts
  unfold decode1 decode1K dropLoc
  dsimp only
  rw [hf]
  dsimp only
  by_cases h2 : a2 = 0
  · rw [ite_eq_left h2, ite_eq_left h2]
    by_cases h1 : a1 = 0
    · rw [ite_eq_left h1, ite_eq_left h1]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h1]
      rfl
  · rw [ite_eq_right h2, ite_eq_right h2, hx2, hfind, herase, nFormK_eq, length_liftPts]
    by_cases h3 : (pts.eraseIdx (pts.findIdx fun p ↦ decide (a2 * ofK (p.1 -
        (pts.getD (d + 2) (0, 0)).1) = a1))).length = d + 2 ∧ (nFormK (pts.eraseIdx
          (pts.findIdx fun p ↦ decide (a2 * ofK (p.1 - (pts.getD (d + 2) (0, 0)).1) = a1)))).2.getD
          (d + 1) 0 = 0
    · rw [ite_eq_left h3, ite_eq_left h3]
      rfl
    · rw [ite_eq_right h3, ite_eq_right h3]
      rfl

end
end LeanVM.Protocol.Whir.Sound.Newton
