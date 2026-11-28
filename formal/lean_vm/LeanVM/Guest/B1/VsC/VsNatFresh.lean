/-
  LeanVM.Guest.B1.VsC.VsNatFresh

  The overlay's fact `VsFresh x.rd1 x.rd0` from the fresh loads' cells at the evaluation memory's valuation.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcSpec

/-!
# The overlay's fresh loads

`Hon.fresh : VsFresh x.rd1 x.rd0 x.w x.args` asks the fresh loads to read alike on `rd1` and `rd0` at `rd1`'s
valuation, while the phases know `rd0`'s (`x.σ0`). **`vsFresh_swap`**: the congruence is symmetric, since no fresh
load's pointer is a temporary (`freshLoads_ptr`, from `congL`) and the branches' selectors are none, so
`VsFresh rd rd'` gives `VsFresh rd' rd`. **`VsCtx.fresh_of_avoid`**: `VsFresh x.rd1 x.rd0` from `VsAvoid x`, every
fresh load's cell at `x.σ0` off the overlay's twelve cells `x.base 13 + j`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd

@[expose] public section

/-- A block's fresh loads read alike on `rd` and `rd'`, at `rd`'s valuation. -/
def FreshAt (rd rd' : Reader) (w : ℕ → E) (args : List E) (c : ℕ) (ss : List Stmt) : Prop :=
  ∀ a ∈ freshLoads c ss, ∀ d p off, a = .load d p off →
    rdAt rd (vsVal rd w args p) off = rdAt rd' (vsVal rd w args p) off

theorem vsFresh_iff {rd rd' : Reader} {w : ℕ → E} {args : List E} :
    VsFresh rd rd' w args ↔ FreshAt rd rd' w args 6 vsAf ∧
      (vsVal rd w args (.n 234) ≠ 0 → FreshAt rd rd' w args 235 vsI1f) ∧ FreshAt rd rd' w args 240 vsB ∧
      (vsVal rd w args (.n 471) = 0 → FreshAt rd rd' w args 472 vsI2z) ∧
      (vsVal rd w args (.n 471) ≠ 0 → FreshAt rd rd' w args 477 vsI2n) ∧ FreshAt rd rd' w args 482 vsC :=
  Iff.rfl

/-- **No fresh load's pointer is a temporary** in a block the congruence takes. -/
theorem freshLoads_ptr {rc : List (V × V)} : ∀ {c : ℕ} {ss : List Stmt}, congL rc c ss = true →
    ∀ a ∈ freshLoads c ss, ∀ d p off, a = .load d p off → tIdx rc p.idx = false
  | _, [], _, a, ha, _, _, _, _ => absurd ha (by simp [freshLoads])
  | c, s :: ss, h, a, ha, d, p, off, e => by
    simp only [congL, Bool.and_eq_true] at h
    simp only [freshLoads, List.mem_append] at ha
    rcases ha with ha | ha
    · subst e
      cases s with
      | atom b =>
        cases b with
        | load d' p' off' =>
          simp only [freshHd] at ha
          split_ifs at ha
          · simp only [List.mem_singleton, Atom.load.injEq] at ha
            obtain ⟨rfl, rfl, rfl⟩ := ha
            have h1 := h.1
            simp [congS, atomUses] at h1
            exact h1.2
          · simp at ha
        | _ => simp [freshHd] at ha
      | _ => simp [freshHd] at ha
    · exact freshLoads_ptr h.2 a ha d p off e

/-- **The congruence is symmetric**: fresh loads reading alike at `rd`'s valuation read alike at `rd'`'s. -/
theorem vsFresh_swap {rd rd' : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6)
    (hf : VsFresh rd rd' w args) : VsFresh rd' rd w args := by
  obtain ⟨cA, cI1, cB, cI2z, cI2n, cC, t234, t471⟩ := vsCong_parts
  have hv : ∀ v : V, tIdx vsRcs v.idx = false → vsVal rd' w args v = vsVal rd w args v :=
    fun v h => (vsVal_congr ha hf h).symm
  have sw : ∀ {c : ℕ} {ss : List Stmt}, congL vsRcs c ss = true → FreshAt rd rd' w args c ss →
      FreshAt rd' rd w args c ss := fun hc h a hm d p off e => by
    rw [hv p (freshLoads_ptr hc a hm d p off e)]
    exact (h a hm d p off e).symm
  have e234 : vsVal rd' w args (.n 234) = vsVal rd w args (.n 234) := hv _ t234
  have e471 : vsVal rd' w args (.n 471) = vsVal rd w args (.n 471) := hv _ t471
  obtain ⟨fA, fI1, fB, fI2z, fI2n, fC⟩ := vsFresh_iff.mp hf
  refine vsFresh_iff.mpr ⟨sw cA fA, fun h => sw cI1 (fI1 (e234 ▸ h)), sw cB fB, fun h => sw cI2z (fI2z (e471 ▸ h)),
    fun h => sw cI2n (fI2n (e471 ▸ h)), sw cC fC⟩

/-! ## The overlay -/

/-- A block's fresh loads' cells at the valuation `σ` lie off the overlay's twelve cells from `b`. -/
def AvoidAt (σ : Val) (b : ℕ) (c : ℕ) (ss : List Stmt) : Prop :=
  ∀ a ∈ freshLoads c ss, ∀ d p off, a = .load d p off →
    ∀ j < 12, addressOfIndex (b + j) ≠ (σ p).limb 0 * addressOfIndex off

/-- **No fresh load of `verify_sub` reads the overlay's cells** (`.n 19`'s twelve words), at the evaluation
memory's valuation, each branch's arm when taken. -/
def VsCtx.VsAvoid (x : VsCtx) : Prop :=
  AvoidAt x.σ0 (x.base 13) 6 vsAf ∧ (x.σ0 (.n 234) ≠ 0 → AvoidAt x.σ0 (x.base 13) 235 vsI1f) ∧
    AvoidAt x.σ0 (x.base 13) 240 vsB ∧ (x.σ0 (.n 471) = 0 → AvoidAt x.σ0 (x.base 13) 472 vsI2z) ∧
    (x.σ0 (.n 471) ≠ 0 → AvoidAt x.σ0 (x.base 13) 477 vsI2n) ∧ AvoidAt x.σ0 (x.base 13) 482 vsC

/-- `rdSet` leaves every address none of its cells names. -/
theorem rdSet_off {rd : Reader} {cells : List (ℕ × E)} {A : K} (h : ∀ q ∈ cells, addressOfIndex q.1 ≠ A) :
    rdSet rd cells A = rd A := by
  unfold rdSet
  rw [show cells.find? (fun q => decide (addressOfIndex q.1 = A)) = none from
    List.find?_eq_none.mpr fun q hq he => h q hq (of_decide_eq_true he)]
  rfl

/-- **`Hon.fresh` from the fresh loads' cells** at `x.σ0`. -/
theorem VsCtx.fresh_of_avoid {x : VsCtx} (h : x.VsAvoid) : VsFresh x.rd1 x.rd0 x.w x.args := by
  have ha : x.args.length = 6 := rfl
  refine vsFresh_swap ha ?_
  have av : ∀ {c : ℕ} {ss : List Stmt}, AvoidAt x.σ0 (x.base 13) c ss → FreshAt x.rd0 x.rd1 x.w x.args c ss :=
    fun hA a hm d p off e => by
      unfold rdAt
      have e' : x.rd0 ((vsVal x.rd0 x.w x.args p).limb 0 * addressOfIndex off) =
          x.rd1 ((vsVal x.rd0 x.w x.args p).limb 0 * addressOfIndex off) := rdSet_off fun q hq => by
        simp only [VsCtx.cells19, vsCells19, List.mem_map, List.mem_range] at hq
        obtain ⟨j, hj, rfl⟩ := hq
        exact hA a hm d p off e j hj
      rw [e']
  obtain ⟨fA, fI1, fB, fI2z, fI2n, fC⟩ := h
  exact vsFresh_iff.mpr ⟨av fA, fun h' => av (fI1 h'), av fB, fun h' => av (fI2z h'), fun h' => av (fI2n h'),
    av fC⟩

end
end LeanVM.Guest.B1.VsC
