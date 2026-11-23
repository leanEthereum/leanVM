module

public import LeanVM.Guest.Mode.Abs

/-!
# A function's hints by offset

The executor reads the advice's hints by pc (`Advice.hints`, `Ctx.of`), the advice's hints at a pc
being its first entry there (`hintsAt`). The guest's advice is given by function (`Data.adviceFns`:
each function's entry, length and entries, `flatFns` the whole), its functions' pcs in order
(`fnsOk`); `hintsAt_fns` reads a function's hints from its own entries.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest.Exec
open LeanVM.Prover.Exec (Hint BitsDest)

@[expose] public section

deriving instance DecidableEq for LeanVM.Prover.Exec.BitsDest
deriving instance DecidableEq for LeanVM.Prover.Exec.Hint

/-- The advice's hints at pc `pc`: its first entry there. -/
def hintsAt (adv : List (ℕ × List Hint)) (pc : ℕ) : List Hint :=
  match adv.find? (·.1 == pc) with
  | some p => p.2
  | none => []

/-- The pcs of the entries strictly increase. -/
def pcsIncr : List (ℕ × List Hint) → Bool
  | a :: b :: l => a.1 < b.1 && pcsIncr (b :: l)
  | _ => true

/-- The advice by function, flattened. -/
def flatFns (fs : List (ℕ × ℕ × List (ℕ × List Hint))) : List (ℕ × List Hint) := (fs.map (·.2.2)).flatten

/-- Each function's entries are in its pcs, from `lo` on, increasing, the functions in order. -/
def fnsOk : List (ℕ × ℕ × List (ℕ × List Hint)) → ℕ → Bool
  | [], _ => true
  | (e, n, l) :: fs, lo => lo ≤ e && l.all (fun p ↦ e ≤ p.1 && p.1 < e + n) && fnsOk fs (e + n)

end

public section

theorem hintsAt_cons_ne {pc x : ℕ} {h : List Hint} {sl : List (ℕ × List Hint)} (hx : pc ≠ x) :
    hintsAt ((pc, h) :: sl) x = hintsAt sl x := by
  unfold hintsAt
  rw [List.find?_cons_of_neg (by simpa using hx)]

theorem pcsIncr_tail {a : ℕ × List Hint} {l : List (ℕ × List Hint)} (h : pcsIncr (a :: l) = true) :
    pcsIncr l = true := by
  match l, h with
  | [], _ => rfl
  | b :: l, h => simp only [pcsIncr, Bool.and_eq_true] at h; exact h.2

theorem pcsIncr_lt : ∀ {a : ℕ × List Hint} {l : List (ℕ × List Hint)}, pcsIncr (a :: l) = true →
    ∀ p ∈ l, a.1 < p.1
  | _, [], _, _, hp => by cases hp
  | a, b :: l, h, p, hp => by
    simp only [pcsIncr, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact lt_trans h.1 (pcsIncr_lt h.2 p hp)

theorem hintsAt_append {x : ℕ} (l₁ l₂ : List (ℕ × List Hint)) (h : ∀ p ∈ l₁, p.1 ≠ x) :
    hintsAt (l₁ ++ l₂) x = hintsAt l₂ x := by
  unfold hintsAt
  rw [List.find?_append, List.find?_eq_none.mpr (fun p hp ↦ by simpa using h p hp), Option.none_or]

theorem hintsAt_append_of_lt {x : ℕ} (l₁ l₂ : List (ℕ × List Hint)) (h : ∀ p ∈ l₂, x < p.1) :
    hintsAt (l₁ ++ l₂) x = hintsAt l₁ x := by
  unfold hintsAt
  rw [List.find?_append]
  cases h1 : l₁.find? (·.1 == x) with
  | some p => rfl
  | none =>
    rw [Option.none_or, List.find?_eq_none.mpr (fun p hp ↦ by have := h p hp; simp; omega)]

theorem fnsOk_ge : ∀ {fs : List (ℕ × ℕ × List (ℕ × List Hint))} {lo : ℕ}, fnsOk fs lo = true →
    ∀ p ∈ flatFns fs, lo ≤ p.1
  | [], _, _, p, hp => by simp [flatFns] at hp
  | (e, n, l) :: fs, lo, h, p, hp => by
    simp only [fnsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    simp only [flatFns, List.map_cons, List.flatten_cons, List.mem_append] at hp
    rcases hp with hp | hp
    · have := (h.1.2 p hp); omega
    · have := fnsOk_ge h.2 p hp; omega

theorem fnsOk_mem : ∀ {fs : List (ℕ × ℕ × List (ℕ × List Hint))} {lo : ℕ}, fnsOk fs lo = true →
    ∀ {d}, d ∈ fs → lo ≤ d.1 ∧ ∀ p ∈ d.2.2, d.1 ≤ p.1 ∧ p.1 < d.1 + d.2.1
  | [], _, _, _, hd => by cases hd
  | (e, n, l) :: fs, lo, h, d, hd => by
    simp only [fnsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨h.1.1, fun p hp ↦ by have := h.1.2 p hp; simpa using this⟩
    · have := fnsOk_mem h.2 hd; exact ⟨by omega, this.2⟩

/-- **The advice's hints at a function's pcs are its own entries'.** -/
theorem hintsAt_fns : ∀ {fs : List (ℕ × ℕ × List (ℕ × List Hint))} {lo : ℕ}, fnsOk fs lo = true →
    ∀ {d}, d ∈ fs → ∀ {x}, d.1 ≤ x → x < d.1 + d.2.1 → hintsAt (flatFns fs) x = hintsAt d.2.2 x
  | [], _, _, _, hd, _, _, _ => by cases hd
  | (e, n, l) :: fs, lo, h, d, hd, x, h1, h2 => by
    have h' := h
    simp only [fnsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
    show hintsAt (l ++ flatFns fs) x = _
    rcases List.mem_cons.mp hd with rfl | hd
    · have h2' : x < e + n := h2
      exact hintsAt_append_of_lt _ _ fun p hp ↦ by have := fnsOk_ge h'.2 p hp; omega
    · rw [hintsAt_append _ _ fun p hp ↦ by
        have := h'.1.2 p hp; have := (fnsOk_mem h'.2 hd).1; omega]
      exact hintsAt_fns h'.2 hd h1 h2

end

end LeanVM.Guest.Mode
