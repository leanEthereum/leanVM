/-
  LeanVM.Compiler.CompileChecked

  The back end with the completeness conditions inside: `lowerProgram`, then the decidable
  per-function checks the whole-program completeness theorems take, an error naming the first
  function that fails one.
-/

module

public import LeanVM.Compiler.Compile
public import LeanVM.Compiler.Complete.Program

/-!
# The checked back end

`compileChecked p` is `lowerProgram p` when every function of `p` passes `fnCheck`, and an error
naming the first function that does not and the check it fails otherwise. The checks are the
components of `Complete.FnConds`: scoped (`scopedB`), no direct self call (`noSelfCallB`), a loop
helper exactly when named one (`isLoopName`), and the temporaries of its placement apart
(`tmpsApartB`, at every placement of its name).

`compileChecked_ok`: a program the checked back end accepts is compiled (`lowerProgram`) and its
every function passes `FnConds` in every world over it, so the whole-program completeness
theorems need no separate per-function hypothesis.

Not among the checks: a pointer discipline and a load-safety check. The pointer discipline is
decidable and the guest passes it, but it does not give `Tree.Placed` (a run with pointers stored
in memory can be valid only because two pointers coincide), and `Tree.LoadsIn` is not decided by
the program (loads at offsets the prover chooses). Both stay hypotheses of the end theorem;
`lake exe guest-ptrcheck` measures them on the guest.
-/

namespace LeanVM.Compiler

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The per-function checks** of `tf` in a program placed as `pls`: `none` if it passes them,
else the function and the first check it fails. -/
def fnCheck (pls : List Placed) (tf : TracedFn) : Option String :=
  if !Complete.scopedB tf then
    some s!"{tf.core.name}: not scoped ({match Complete.scopedE tf with | .error e => e | .ok _ => ""})"
  else if !Complete.noSelfCallB tf then some s!"{tf.core.name}: calls itself"
  else if isLoopName tf.core.name != tf.core.loop then
    some s!"{tf.core.name}: a loop helper by its name but not by its source, or the converse"
  else if !(pls.all fun pf => pf.fn.name != tf.core.name || Complete.tmpsApartB tf pf) then
    some s!"{tf.core.name}: its placement's temporaries are not apart"
  else none

/-- **The checked back end**: the labelled code and the jump table slots of `lowerProgram`, if
every function passes `fnCheck`. -/
def compileChecked (p : List TracedFn) : Except String (List Lowered × Array KVal) :=
  match lowerProgram p with
  | .error e => .error e
  | .ok r =>
    match placeProgram p with
    | .error e => .error e
    | .ok (pls, _) =>
      match p.findSome? (fnCheck pls) with
      | some e => .error e
      | none => .ok r

theorem fnCheck_none {pls : List Placed} {tf : TracedFn} (h : fnCheck pls tf = none) :
    Complete.scopedB tf = true ∧ Complete.noSelfCallB tf = true ∧
      isLoopName tf.core.name = tf.core.loop ∧
      ∀ pf ∈ pls, pf.fn.name = tf.core.name → Complete.tmpsApartB tf pf = true := by
  unfold fnCheck at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  rename_i h1 h2 h3 h4
  simp only [Bool.not_eq_true', Bool.not_eq_false, bne_iff_ne, ne_eq, not_not] at h1 h2 h3
  simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at h4
  refine ⟨h1, h2, h3, fun pf hpf hn => ?_⟩
  rcases h4 pf hpf with h | h
  · exact absurd hn h
  · exact h

/-- **What the checked back end gives**: the code is `lowerProgram`'s, and in every world over
the program every function passes the per-function completeness conditions. -/
theorem compileChecked_ok {p : List TracedFn} {r : List Lowered × Array KVal}
    (h : compileChecked p = .ok r) :
    lowerProgram p = .ok r ∧
      ∀ {κ₀ : ℕ} (W : World κ₀), W.p = p → ∀ tf ∈ W.p, Complete.FnConds W tf := by
  unfold compileChecked at h
  split at h
  · exact absurd h (by simp)
  rename_i r' hl
  split at h
  · exact absurd h (by simp)
  rename_i pls t hpp
  split at h
  · exact absurd h (by simp)
  rename_i hf
  cases h
  refine ⟨hl, fun W hW tf htf => ?_⟩
  subst hW
  obtain ⟨hs, hn, hlp, ht⟩ := fnCheck_none (List.findSome?_eq_none_iff.mp hf tf htf)
  have hpl : W.placed = pls := by simp [World.placed, hpp]
  exact ⟨hs, hn, hlp, fun pf hpa => ht pf (hpl ▸ hpa.1) hpa.2⟩

theorem fnCheck_none_of {pls : List Placed} {tf : TracedFn} (hs : Complete.scopedB tf = true)
    (hn : Complete.noSelfCallB tf = true) (hlp : isLoopName tf.core.name = tf.core.loop)
    (ht : ∀ pf ∈ pls, pf.fn.name = tf.core.name → Complete.tmpsApartB tf pf = true) :
    fnCheck pls tf = none := by
  have ha : (pls.all fun pf => pf.fn.name != tf.core.name || Complete.tmpsApartB tf pf) = true := by
    rw [List.all_eq_true]
    intro pf hpf
    by_cases h : pf.fn.name = tf.core.name
    · simp [ht pf hpf h]
    · simp [h]
  unfold fnCheck
  rw [hs, hn, hlp, ha]
  simp

/-- **The checked back end accepts exactly** the programs `lowerProgram` compiles whose every
function passes the per-function conditions. -/
theorem compileChecked_of {κ₀ : ℕ} (W : World κ₀) {r : List Lowered × Array KVal}
    (hl : lowerProgram W.p = .ok r) (hC : ∀ tf ∈ W.p, Complete.FnConds W tf) :
    compileChecked W.p = .ok r := by
  have hpp : ∃ t, placeProgram W.p = .ok (W.placed, t) := by
    unfold lowerProgram at hl
    cases h : placeProgram W.p with
    | error e => rw [h] at hl; exact absurd hl (by simp)
    | ok q => exact ⟨q.2, by simp [World.placed, h]⟩
  obtain ⟨t, hpp⟩ := hpp
  have hf : W.p.findSome? (fnCheck W.placed) = none := by
    rw [List.findSome?_eq_none_iff]
    intro tf htf
    have c := hC tf htf
    exact fnCheck_none_of c.isScoped c.noSelf c.loopNamed fun pf hpf hn => c.tmps pf ⟨hpf, hn⟩
  simp only [compileChecked, hl, hpp, hf]

/-- A world's code is the checked back end's, padded to its size: `World.Compiled`. -/
theorem compiled_of_checked {κ₀ : ℕ} {W : World κ₀}
    (h : compileChecked W.p = .ok (W.fns, W.slots))
    (hs : (assemble W.fns W.slots).size = 2 ^ W.logSize) : W.Compiled :=
  ⟨(compileChecked_ok h).1, hs⟩

end
end LeanVM.Compiler
