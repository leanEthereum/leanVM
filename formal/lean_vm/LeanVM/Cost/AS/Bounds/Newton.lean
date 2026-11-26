module

public import LeanVM.Cost.Bounds.Leaves
public import LeanVM.Cost.Bounds.Layout
public import LeanVM.Cost.AS.Top
import all LeanVM.Protocol.Whir.Sound.NewtonK

/-!
# Bounds: one-error Newton decoding

* `nEvalK_go_cost`: the Newton form of `L` nodes evaluated, `206·L + 11`;
* `nodalK_cost`: `57·L + 16`; `nStepK_cost`: one point added to a form of `L` nodes,
  `285·L + 3077`;
* `nFormK_cost`: the Newton form of `k` points, `(285·k + 3091)·k + 11`;
* **`decode1K_cost`**: one-error decoding of `d + 3` points, at most `600·(d+3)² + 8000·(d+3) +
  10000`.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound.Newton

public section

variable (P : MachineProgram)

theorem nEvalK_go_cost
    (hP : Includes P Auto.LeanVM.Protocol.Whir.Sound.Newton.nEvalK.c268.costDeps) :
    ∀ (xs : List K) (as : List E) (z : K),
      machineCost P Auto.LeanVM.Protocol.Whir.Sound.Newton.nEvalK.c268.costIdx
        [encodeValue xs, encodeValue as, encodeValue z] ≤ 206 * xs.length + 11
  | [], as, z => by
    rw [Auto.LeanVM.Protocol.Whir.Sound.Newton.nEvalK.c268.costEq P hP]
    cases as <;> simp
  | x :: xs, [], z => by
    rw [Auto.LeanVM.Protocol.Whir.Sound.Newton.nEvalK.c268.costEq P hP]
    simp
  | x :: xs, a :: as, z => by
    rw [Auto.LeanVM.Protocol.Whir.Sound.Newton.nEvalK.c268.costEq P hP]
    have := nEvalK_go_cost hP xs as z
    simp only [List.length_cons]
    omega

theorem nodalK_cost (hP : Includes P nodalKC.costDeps) (xs : List K) (z : K) :
    machineCost P nodalKC.costIdx [encodeValue xs, encodeValue z] ≤ 57 * xs.length + 16 := by
  rw [nodalKC.costEq P hP]
  have hm := map_cost P (by includes) (fun x ↦ z - x) (.closure nodalKC.lam0.costIdx [encodeValue z])
    (fun x ↦ RunsApp.of_spec (nodalKC.lam0.costSpec P (by includes) z x)) 4 xs
    (fun x _ ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append, nodalKC.lam0.costEq P (by includes)]
      simp)
  have hp : machineCost P Auto.List.prod.c264.costIdx [encodeValue (xs.map fun x ↦ z - x)] ≤
      40 * xs.length + 7 := by
    rw [Auto.List.prod.c264.costEq P (by includes)]
    have := foldr_cost P (by includes) (· * ·) (.closure Auto.List.prod.c264.lam0.costIdx [])
      (fun a b ↦ RunsApp.of_spec (Auto.List.prod.c264.lam0.costSpec P (by includes) a b)) 29 1
      (xs.map fun x ↦ z - x) (fun a _ b ↦ by
        rw [appCost_fn, List.nil_append, Auto.List.prod.c264.lam0.costEq P (by includes)]
        simp)
    simp only [List.length_map] at this
    omega
  omega

theorem nStepK_cost (hP : Includes P nStepKC.costDeps) (st : List K × List E) (p : K × E)
    (hst : st.2.length = st.1.length) :
    machineCost P nStepKC.costIdx [encodeValue st, encodeValue p] ≤ 285 * st.1.length + 3077 := by
  rw [nStepKC.costEq P hP]
  have h1 := nEvalK_go_cost P (by includes) st.1 st.2 p.1
  have h2 := nodalK_cost P (by includes) st.1 p.1
  have h3 := invK_cost P (by includes) (nodalK st.1 p.1)
  have h4 := append_cost P (by includes) st.1 [p.1]
  have h5 := append_cost P (by includes) st.2
    [(p.2 + nEvalK st.1 st.2 p.1) * ofK (nodalK st.1 p.1)⁻¹]
  omega

theorem nFormK_cost (hP : Includes P nFormKC.costDeps) (pts : List (K × E)) :
    machineCost P nFormKC.costIdx [encodeValue pts] ≤ (285 * pts.length + 3091) * pts.length + 11 := by
  rw [nFormKC.costEq P hP]
  have := listFoldl_le' P (by includes) nStepK (.closure nFormKC.lam0.costIdx [])
    (fun st p ↦ RunsApp.of_spec (nFormKC.lam0.costSpec P (by includes) st p))
    (285 * pts.length + 3080)
    (fun st l ↦ st.2.length = st.1.length ∧ st.1.length + l.length = pts.length)
    (fun st b l hJ ↦ by
      refine ⟨⟨by simp [nStepK, hJ.1], by simp [nStepK]; simp at hJ; omega⟩, ?_⟩
      rw [appCost_fn, List.length_nil, Nat.add_zero, List.nil_append,
        nFormKC.lam0.costEq P (by includes)]
      have := nStepK_cost P (by includes) st b hJ.1
      have h := hJ.2
      simp only [List.length_cons] at h
      nlinarith)
    pts ([], []) ⟨rfl, by simp⟩
  nlinarith

theorem eraseIdx_cost (hP : Includes P Auto.List.eraseIdx.c272.costDeps) {α : Type}
    [MachineEncoding α] : ∀ (l : List α) (i : ℕ), i < 2 ^ 64 →
      machineCost P Auto.List.eraseIdx.c272.costIdx [encodeValue l, encodeValue i] ≤ 19 * l.length + 10
  | [], i, _ => by rw [Auto.List.eraseIdx.c272.costEq P hP]; simp
  | x :: l, 0, _ => by rw [Auto.List.eraseIdx.c272.costEq P hP]; simp [limbCount]
  | x :: l, i + 1, hi => by
    rw [Auto.List.eraseIdx.c272.costEq P hP, limbs_of_lt hi]
    have := eraseIdx_cost hP l i (by omega)
    simp only [List.length_cons]
    omega

theorem length_dropLoc (d : ℕ) (f : List K × List E) (pts : List (K × E)) :
    (dropLoc d f pts).length ≤ pts.length := by
  unfold dropLoc
  rw [List.length_eraseIdx]
  split <;> omega

theorem dropLoc_cost (hP : Includes P dropLocC.costDeps) (d : ℕ) (f : List K × List E)
    (pts : List (K × E)) (hd : d + 3 < 2 ^ 63) (hl : pts.length < 2 ^ 63) :
    machineCost P dropLocC.costIdx [encodeValue d, encodeValue f, encodeValue pts] ≤
      225 * pts.length + 45 * d + 250 := by
  rw [dropLocC.costEq P hP, limbs_of_lt (by omega : d + 2 < 2 ^ 64),
    limbs_of_lt (by omega : d + 1 < 2 ^ 64), limbs_of_lt (by omega : d < 2 ^ 64)]
  have g1 := getD_cost_idx P (by includes) f.2 (d + 2) 0 (by omega)
  have g2 := getD_cost_idx P (by includes) f.2 (d + 1) 0 (by omega)
  have g3 := getD_cost_idx P (by includes) pts (d + 2) (0, 0) (by omega)
  have hf := findIdxGo_cost P (by includes) _ (.closure dropLocC.lam0.costIdx
      [encodeValue (pts.getD (d + 2) (0, 0)).1, encodeValue (f.2.getD (d + 2) 0),
        encodeValue (f.2.getD (d + 1) 0)])
    (fun p ↦ RunsApp.of_spec (dropLocC.lam0.costSpec P (by includes) _ _ _ p)) 192 pts 0
    (by omega) (fun p _ ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        dropLocC.lam0.costEq P (by includes)]
      simp only [List.length_cons, List.length_nil]
      split_ifs <;> omega)
  simp only [max_self]
  have he := eraseIdx_cost P (by includes) pts (List.findIdx (fun p ↦
      decide (f.2.getD (d + 2) 0 * ofK (p.1 - (pts.getD (d + 2) (0, 0)).1) = f.2.getD (d + 1) 0))
      pts) (by
    have := List.findIdx_le_length (p := fun p : K × E ↦
      decide (f.2.getD (d + 2) 0 * ofK (p.1 - (pts.getD (d + 2) (0, 0)).1) = f.2.getD (d + 1) 0))
      (xs := pts)
    omega)
  omega

theorem decode1K_cost (hP : Includes P decode1KC.costDeps) (d : ℕ) (pts : List (K × E))
    (hl : pts.length = d + 3) (hd : d + 3 < 2 ^ 63) :
    machineCost P decode1KC.costIdx [encodeValue d, encodeValue pts] ≤
      600 * (d + 3) ^ 2 + 8000 * (d + 3) + 10000 := by
  rw [decode1KC.costEq P hP, limbs_of_lt (by omega : d + 2 < 2 ^ 64),
    limbs_of_lt (by omega : d + 1 < 2 ^ 64), limbs_of_lt (by omega : d < 2 ^ 64)]
  have hq := length_dropLoc d (nFormK pts) pts
  rw [limbs_of_lt (by omega : (dropLoc d (nFormK pts) pts).length < 2 ^ 64)]
  have n1 := nFormK_cost P (by includes) pts
  have n2 := nFormK_cost P (by includes) (dropLoc d (nFormK pts) pts)
  have dl := dropLoc_cost P (by includes) d (nFormK pts) pts hd (by omega)
  have ln := length_cost P (by includes) (dropLoc d (nFormK pts) pts) (by omega)
  have g1 := getD_cost_idx P (by includes) (nFormK pts).2 (d + 2) 0 (by omega)
  have g2 := getD_cost_idx P (by includes) (nFormK pts).2 (d + 1) 0 (by omega)
  have g3 := getD_cost_idx P (by includes) (nFormK (dropLoc d (nFormK pts) pts)).2 (d + 1) 0
    (by omega)
  have hn2 : (285 * (dropLoc d (nFormK pts) pts).length + 3091) *
      (dropLoc d (nFormK pts) pts).length + 11 ≤ (285 * (d + 3) + 3091) * (d + 3) + 11 := by
    rw [hl] at hq
    have := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 285 hq) 3091) hq
    omega
  rw [hl] at n1 dl
  have n2' := n2.trans hn2
  have hS : 2 * ((285 * (d + 3) + 3091) * (d + 3)) + 1818 * (d + 3) ≤
      600 * (d + 3) ^ 2 + 8000 * (d + 3) := by nlinarith
  simp only [max_self]
  split_ifs <;> linarith

end

end LeanVM.Cost.Bounds.AS
