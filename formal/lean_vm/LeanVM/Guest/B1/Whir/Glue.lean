/-
  LeanVM.Guest.B1.Whir.Glue

  A level's claims glued into the running sumcheck: the template's glue blocks against the
  Spec's `glue`.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.Folds

/-!
# The glue (G:1628-1646, V:1775-1783)

`osOodGlue_sound`: the out-of-domain claim's value and intro reread from `ood` (`y`, `c0`, `c2`),
the scalar `lam` stored, the running quadratic and claim plus `lam` times them, the next scalar
`lam²`. `osGlue_sound`: the level's batch plus `beta` times the intro `c0, c1, c2` and the sum.
`glue_one`, `glue_two`: the Spec's `glue` of one and of two claims.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **The out-of-domain claim glued** with `lam`. -/
theorem osOodGlue_sound {lvl lam : ℕ} {s : OsSt} (h : AllOk C rd σ (osOodGlue lvl lam s).1) :
    ∃ y c0 c2 : E,
      LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 1) y ∧
      LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 2) c0 ∧
      LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 3) c2 ∧
      LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots) (σ (.n lam)) ∧
      (osOodGlue lvl lam s).2.quad σ =
        [σ (.n s.c) + σ (.n lam) * c0, σ (.n s.b) + σ (.n lam) * (y + c2),
          σ (.n s.a) + σ (.n lam) * c2] ∧
      σ (.n (osOodGlue lvl lam s).2.t) = σ (.n s.t) + σ (.n lam) * y ∧
      σ (.n (s.k + 12)) = σ (.n lam) * σ (.n lam) := by
  simp only [osOodGlue, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h
  obtain ⟨ly, lc2, lsc, lc0, m3, a4, a5, m6, a7, m8, a9, m10, a11, m12⟩ := h
  refine ⟨_, _, _, ly, lc0, lc2, lsc, ?_, ?_, m12⟩
  · simp only [OsSt.quad, osOodGlue, a4, m3, a7, m6, a5, a9, m8]
  · simp only [osOodGlue, a11, m10]

/-- **The level's batch glued** with `beta`. -/
theorem osGlue_sound {beta v c0 c1 c2 : ℕ} {s : OsSt} (h : AllOk C rd σ (osGlue beta v c0 c1 c2 s).1) :
    (osGlue beta v c0 c1 c2 s).2.quad σ =
        [σ (.n s.c) + σ (.n beta) * σ (.n c0), σ (.n s.b) + σ (.n beta) * σ (.n c1),
          σ (.n s.a) + σ (.n beta) * σ (.n c2)] ∧
      σ (.n (osGlue beta v c0 c1 c2 s).2.t) = σ (.n s.t) + σ (.n beta) * σ (.n v) := by
  simp only [osGlue, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h
  obtain ⟨m0, a1, m2, a3, m4, a5, m6, a7⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [OsSt.quad, osGlue, a1, m0, a3, m2, a5, m4]
  · simp only [osGlue, a7, m6]

/-- The Spec's `glue` of one claim. -/
theorem glue_one (lam : E) (s : WhirStateT) (v : E) (i : List E) (w : List E → E) :
    glueT lam s [(v, i, w)] =
      { s with quad := List.zipWith (fun q x ↦ q + 1 * lam * x) s.quad i,
               target := s.target + 1 * lam * v,
               glued := s.glued ++ [⟨1 * lam, s.folds.length, w⟩] } := rfl

/-- The Spec's `glue` of two claims. -/
theorem glue_two (lam : E) (s : WhirStateT) (v v' : E) (i i' : List E) (w w' : List E → E) :
    glueT lam s [(v, i, w), (v', i', w')] =
      { s with quad := List.zipWith (fun q x ↦ q + 1 * lam * lam * x)
                 (List.zipWith (fun q x ↦ q + 1 * lam * x) s.quad i) i',
               target := s.target + 1 * lam * v + 1 * lam * lam * v',
               glued := s.glued ++ [⟨1 * lam, s.folds.length, w⟩,
                 ⟨1 * lam * lam, s.folds.length, w'⟩] } := by
  simp [glueT]

end
end LeanVM.Guest.B1.Whir
