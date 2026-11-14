module

public import LeanVM.Guest.Mode.HintsData
public import LeanVM.Prover.ExecuteMem

/-!
# The executor's hints are the advice's

The executor tabulates the advice's hints by pc (`Ctx.of`): at a pc of the program, its hints are the
advice's there (`ctx_hints`), the advice's pcs increasing. With `HintsOk` (`Pack/*/ModeH`), at each
offset of a function, the mode walk's hints are the executor's at its pc (`ctx_hintsOk`), for the
guest's advice (`Data.adviceHints`, the parse of `Data.adviceText`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Semantics LeanVM.Prover.Exec

public section

theorem foldl_set_other {pc : ℕ} : ∀ (l : List (ℕ × List Hint)) (a : Array (List Hint)),
    (∀ p ∈ l, p.1 ≠ pc) → (l.foldl (fun hs p ↦ hs.setIfInBounds p.1 p.2) a)[pc]? = a[pc]?
  | [], _, _ => rfl
  | (k, v) :: l, a, h => by
    rw [List.foldl_cons, foldl_set_other l _ fun p hp ↦ h p (List.mem_cons_of_mem _ hp),
      Array.getElem?_setIfInBounds]
    exact ite_eq_right_of_eq_false _ _ (eq_false (h _ (List.mem_cons_self ..)))

theorem foldl_set_hints {pc : ℕ} : ∀ (l : List (ℕ × List Hint)) (a : Array (List Hint)),
    pcsIncr l = true → pc < a.size → a[pc]? = some [] →
      ((l.foldl (fun hs p ↦ hs.setIfInBounds p.1 p.2) a)[pc]?).getD [] = hintsAt l pc
  | [], _, _, _, ha => by rw [List.foldl_nil, ha]; rfl
  | (k, v) :: l, a, hs, hpc, ha => by
    rw [List.foldl_cons]
    by_cases hk : k = pc
    · subst hk
      rw [foldl_set_other l _ fun p hp ↦ by have := pcsIncr_lt hs p hp; simp only at this; omega,
        Array.getElem?_setIfInBounds_self_of_lt hpc]
      unfold hintsAt; simp
    · rw [hintsAt_cons_ne hk]
      exact foldl_set_hints l _ (pcsIncr_tail hs) (by simpa using hpc)
        (by rw [Array.getElem?_setIfInBounds, ite_eq_right_of_eq_false _ _ (eq_false hk), ha])

/-- **The executor's hints at a pc are the advice's.** -/
theorem ctx_hints {prog : LeanIsaProgram} {adv : Advice} {C : Ctx} (h : Ctx.of prog adv = .ok C)
    (hs : pcsIncr adv.hints = true) {pc : ℕ} (hpc : pc < 2 ^ prog.logSize) :
    (C.hints[pc]?).getD [] = hintsAt adv.hints pc := by
  simp only [Ctx.of, bind_ok, pure_ok] at h
  obtain ⟨ops, -, rfl⟩ := h
  exact foldl_set_hints _ _ hs (by simpa using hpc)
    (by rw [Array.getElem?_replicate, ite_eq_left_of_eq_true _ _ (eq_true hpc)])

theorem adviceHints_incr : pcsIncr Data.adviceHints = true := by decide +kernel

/-- **The mode walk reads the executor's hints**: at each offset of a function whose hints are the
guest's advice's, those at its pc, the executor run on that advice. -/
theorem ctx_hintsOk {prog : LeanIsaProgram} {adv : Advice} {C : Ctx} (h : Ctx.of prog adv = .ok C)
    (ha : adv.hints = Data.adviceHints) {F : Fun} (hF : HintsOk F Data.adviceHints) {i : ℕ}
    (hi : i < F.len) (hpc : F.entry + i < 2 ^ prog.logSize) :
    (F.hints.get i).getD [] = (C.hints[F.entry + i]?).getD [] := by
  rw [hF i hi, ctx_hints h (ha ▸ adviceHints_incr) hpc, ha]

end

end LeanVM.Guest.Mode
