module

public import LeanVM.Guest.Mode.Hints

/-!
# A long function's hints, checked in parts

`hintsOk_of_fn` checks a function's hints against the advice in one `hintsChk` over all its offsets,
too costly for the longest functions. `HParts` cuts the check at offsets and at the advice's entries
there: each part is one `hintsChk` over its offsets and its entries (`List.drop`, `List.take` of the
function's), checked in a module of its own; `hintsOk_of_parts` chains them (`hintsChk_append`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest.Exec
open LeanVM.Prover.Exec (Hint)

@[expose] public section

/-- The parts of a function's hints check from entry `c` and offset `o`: each ends at an entry and an
offset `(c', o')`, the last at the function's length `n`. -/
def HParts (t : Trie (List Hint)) (e : ℕ) (l : List (ℕ × List Hint)) (n : ℕ) :
    ℕ → ℕ → List (ℕ × ℕ) → Prop
  | c, o, [] => hintsChk t e (l.drop c) o (n - o) = true
  | c, o, (c', o') :: ws => c ≤ c' ∧ o ≤ o' ∧ o' ≤ n ∧
      hintsChk t e ((l.drop c).take (c' - c)) o (o' - o) = true ∧ HParts t e l n c' o' ws

end

public section

/-- Two checks, the second from the offset the first ends at: the check of both entries' lists. -/
theorem hintsChk_append {t : Trie (List Hint)} {e : ℕ} :
    ∀ {m : ℕ} {l₁ l₂ : List (ℕ × List Hint)} {i n : ℕ}, hintsChk t e l₁ i m = true →
      hintsChk t e l₂ (i + m) n = true → hintsChk t e (l₁ ++ l₂) i (m + n) = true
  | 0, l₁, l₂, i, n, h₁, h₂ => by
    rw [hintsChk_zero, List.isEmpty_iff] at h₁
    subst h₁
    simpa using h₂
  | m + 1, [], l₂, i, n, h₁, h₂ => by
    rw [hintsChk_nil] at h₁
    simp only [Bool.and_eq_true] at h₁
    rw [List.nil_append, show m + 1 + n = (m + n) + 1 by omega]
    cases l₂ with
    | nil =>
      rw [hintsChk_nil, h₁.1, Bool.true_and]
      have := hintsChk_append (l₂ := []) h₁.2 (by rwa [show i + 1 + m = i + (m + 1) by omega])
      simpa using this
    | cons p l₂ =>
      obtain ⟨pc, hs⟩ := p
      have hr := hintsChk_range h₂ (pc, hs) (List.mem_cons_self ..)
      rw [hintsChk_cons, ite_eq_right_of_eq_false _ _ (eq_false (by simp only at hr; omega)), h₁.1,
        Bool.true_and]
      have := hintsChk_append (l₂ := (pc, hs) :: l₂) h₁.2
        (by rwa [show i + 1 + m = i + (m + 1) by omega])
      simpa using this
  | m + 1, (pc, hs) :: l₁, l₂, i, n, h₁, h₂ => by
    rw [List.cons_append, show m + 1 + n = (m + n) + 1 by omega, hintsChk_cons]
    rw [hintsChk_cons] at h₁
    have h₂' : hintsChk t e l₂ (i + 1 + m) n = true := by rwa [show i + 1 + m = i + (m + 1) by omega]
    split_ifs at h₁ ⊢ with hpc
    · simp only [Bool.and_eq_true] at h₁ ⊢
      exact ⟨h₁.1, hintsChk_append h₁.2 h₂'⟩
    · simp only [Bool.and_eq_true] at h₁ ⊢
      exact ⟨h₁.1, by simpa using hintsChk_append (l₁ := (pc, hs) :: l₁) h₁.2 h₂'⟩

theorem hparts_nil {t : Trie (List Hint)} {e : ℕ} {l : List (ℕ × List Hint)} {n c o : ℕ}
    (h : hintsChk t e (l.drop c) o (n - o) = true) : HParts t e l n c o [] := h

theorem hparts_cons {t : Trie (List Hint)} {e : ℕ} {l : List (ℕ × List Hint)} {n c o c' o' : ℕ}
    {ws : List (ℕ × ℕ)} (h1 : c ≤ c') (h2 : o ≤ o') (h3 : o' ≤ n)
    (h4 : hintsChk t e ((l.drop c).take (c' - c)) o (o' - o) = true) (h5 : HParts t e l n c' o' ws) :
    HParts t e l n c o ((c', o') :: ws) := ⟨h1, h2, h3, h4, h5⟩

/-- **The parts give the check** from entry `c` and offset `o` on. -/
theorem hintsChk_of_parts {t : Trie (List Hint)} {e : ℕ} {l : List (ℕ × List Hint)} {n : ℕ} :
    ∀ {ws : List (ℕ × ℕ)} {c o : ℕ}, HParts t e l n c o ws → hintsChk t e (l.drop c) o (n - o) = true
  | [], _, _, h => h
  | (c', o') :: ws, c, o, ⟨hc, ho, hn, h1, h2⟩ => by
    have ih := hintsChk_of_parts h2
    have e1 : l.drop c = (l.drop c).take (c' - c) ++ l.drop c' := by
      conv_lhs => rw [← List.take_append_drop (c' - c) (l.drop c)]
      rw [List.drop_drop, Nat.add_sub_cancel' hc]
    rw [e1, show n - o = (o' - o) + (n - o') by omega]
    exact hintsChk_append h1 (by rwa [Nat.add_sub_cancel' ho])

/-- **A function's hints are the advice's**, its check in parts. -/
theorem hintsOk_of_parts {F : Fun} {fs : List (ℕ × ℕ × List (ℕ × List Hint))} {j : ℕ}
    {d : ℕ × ℕ × List (ℕ × List Hint)} {ws : List (ℕ × ℕ)} (hfs : fnsOk fs 0 = true) (hj : fs[j]? = some d)
    (h : (F.entry == d.1 && F.len == d.2.1 && pcsIncr d.2.2) = true)
    (hp : HParts F.hints F.entry d.2.2 F.len 0 0 ws) : HintsOk F (flatFns fs) := by
  refine hintsOk_of_fn hfs hj ?_
  have := hintsChk_of_parts hp
  rw [List.drop_zero, Nat.sub_zero] at this
  simp only [fnChk, h, this, Bool.and_self]

end

end LeanVM.Guest.Mode
