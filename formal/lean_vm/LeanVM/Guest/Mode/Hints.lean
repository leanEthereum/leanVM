module

public import LeanVM.Guest.Mode.Abs

/-!
# A function's hints are the advice's

The mode walk reads a function's hints by offset (`Fun.hints`); the executor reads the advice's by pc
(`Advice.hints`, `Ctx.of`). `HintsOk F adv` says they agree at every offset of the function, the
advice's hints at a pc being its first entry there (`hintsAt`). The guest's advice is given by
function (`Data.adviceFns`: each function's entry, length and entries, `flatFns` the whole), its
functions' pcs in order (`fnsOk`); `hintsOk_of_fn` decides `HintsOk` from a function's own entries,
checked against the trie offset by offset (`hintsChk`).
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

/-- The function's hints at each of its offsets are the advice's at its pc. -/
def HintsOk (F : Fun) (adv : List (ℕ × List Hint)) : Prop :=
  ∀ i < F.len, (F.hints.get i).getD [] = hintsAt adv (F.entry + i)

/-- The advice by function, flattened. -/
def flatFns (fs : List (ℕ × ℕ × List (ℕ × List Hint))) : List (ℕ × List Hint) := (fs.map (·.2.2)).flatten

/-- Each function's entries are in its pcs, from `lo` on, increasing, the functions in order. -/
def fnsOk : List (ℕ × ℕ × List (ℕ × List Hint)) → ℕ → Bool
  | [], _ => true
  | (e, n, l) :: fs, lo => lo ≤ e && l.all (fun p ↦ e ≤ p.1 && p.1 < e + n) && fnsOk fs (e + n)

/-- The trie's hints at offsets `i` to below `i + n` are the entries `sl`, in order, at pcs `e + i`
on, and no other. Written with the recursor, for the kernel. -/
noncomputable def hintsChk (t : Trie (List Hint)) (e : ℕ) (sl : List (ℕ × List Hint)) (i n : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ List (ℕ × List Hint) → ℕ → Bool) (fun sl _ ↦ sl.isEmpty)
    (fun _ ih sl i ↦ match sl with
      | [] => ((t.get i).getD []).isEmpty && ih [] (i + 1)
      | (pc, h) :: sl' =>
        bif pc == e + i then decide ((t.get i).getD [] = h) && ih sl' (i + 1)
        else ((t.get i).getD []).isEmpty && ih ((pc, h) :: sl') (i + 1)) n sl i

/-- The function's entries `d` (its entry, length and hints by pc) and the trie agree. -/
noncomputable def fnChk (F : Fun) (d : ℕ × ℕ × List (ℕ × List Hint)) : Bool :=
  F.entry == d.1 && F.len == d.2.1 && pcsIncr d.2.2 && hintsChk F.hints F.entry d.2.2 0 F.len

end

public section

theorem hintsChk_zero (t : Trie (List Hint)) (e : ℕ) (sl : List (ℕ × List Hint)) (i : ℕ) :
    hintsChk t e sl i 0 = sl.isEmpty := rfl

theorem hintsChk_nil (t : Trie (List Hint)) (e i n : ℕ) :
    hintsChk t e [] i (n + 1) = (((t.get i).getD []).isEmpty && hintsChk t e [] (i + 1) n) := rfl

theorem hintsChk_cons (t : Trie (List Hint)) (e pc : ℕ) (h : List Hint) (sl : List (ℕ × List Hint))
    (i n : ℕ) : hintsChk t e ((pc, h) :: sl) i (n + 1) =
      if pc = e + i then decide ((t.get i).getD [] = h) && hintsChk t e sl (i + 1) n
      else ((t.get i).getD []).isEmpty && hintsChk t e ((pc, h) :: sl) (i + 1) n := by
  show (bif pc == e + i then _ else _) = _
  by_cases hp : pc = e + i
  · rw [show (pc == e + i) = true from beq_iff_eq.mpr hp, ite_eq_left_of_eq_true _ _ (eq_true hp)]; rfl
  · rw [show (pc == e + i) = false from beq_eq_false_iff_ne.mpr hp, ite_eq_right_of_eq_false _ _ (eq_false hp)]; rfl

theorem hintsChk_range {t : Trie (List Hint)} {e : ℕ} :
    ∀ {n : ℕ} {sl : List (ℕ × List Hint)} {i : ℕ}, hintsChk t e sl i n = true →
      ∀ p ∈ sl, e + i ≤ p.1 ∧ p.1 < e + i + n
  | 0, sl, i, h, p, hp => by
    rw [hintsChk_zero, List.isEmpty_iff] at h
    subst h; cases hp
  | n + 1, [], i, _, p, hp => by cases hp
  | n + 1, (pc, hs) :: sl, i, h, p, hp => by
    rw [hintsChk_cons] at h
    split_ifs at h with hpc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨by simp [hpc], by simp [hpc]⟩
      · have := hintsChk_range h.2 p hp; omega
    · simp only [Bool.and_eq_true] at h
      have := hintsChk_range h.2 p hp; omega

theorem hintsAt_cons_ne {pc x : ℕ} {h : List Hint} {sl : List (ℕ × List Hint)} (hx : pc ≠ x) :
    hintsAt ((pc, h) :: sl) x = hintsAt sl x := by
  unfold hintsAt
  rw [List.find?_cons_of_neg (by simpa using hx)]

theorem hintsAt_of_lt {x : ℕ} : ∀ {sl : List (ℕ × List Hint)}, (∀ p ∈ sl, x < p.1) → hintsAt sl x = []
  | [], _ => rfl
  | (pc, h) :: sl, hl => by
    rw [hintsAt_cons_ne (by have := hl _ (List.mem_cons_self ..); simp at this; omega)]
    exact hintsAt_of_lt fun p hp ↦ hl p (List.mem_cons_of_mem _ hp)

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

/-- **The check is sound**: at each offset, the trie's hints are the entries'. -/
theorem hintsChk_sound {t : Trie (List Hint)} {e : ℕ} :
    ∀ {n : ℕ} {sl : List (ℕ × List Hint)} {i : ℕ}, pcsIncr sl = true → hintsChk t e sl i n = true →
      ∀ j, i ≤ j → j < i + n → (t.get j).getD [] = hintsAt sl (e + j)
  | 0, _, _, _, _, j, h1, h2 => by omega
  | n + 1, [], i, _, h, j, h1, h2 => by
    rw [hintsChk_nil] at h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · rw [h.1]; rfl
    · exact hintsChk_sound rfl h.2 j h1 (by omega)
  | n + 1, (pc, hs) :: sl, i, hinc, h, j, h1, h2 => by
    rw [hintsChk_cons] at h
    split_ifs at h with hpc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · rw [h.1]; unfold hintsAt; rw [List.find?_cons_of_pos (by simp [hpc])]
      · rw [hintsAt_cons_ne (by omega)]
        exact hintsChk_sound (pcsIncr_tail hinc) h.2 j h1 (by omega)
    · simp only [Bool.and_eq_true, List.isEmpty_iff] at h
      have hr := hintsChk_range h.2 (pc, hs) (List.mem_cons_self ..)
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · rw [h.1, hintsAt_of_lt]
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simp only at hr ⊢; omega
        · have := pcsIncr_lt hinc p hp; simp only at hr this; omega
      · exact hintsChk_sound hinc h.2 j h1 (by omega)

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

/-- **A function's hints are the advice's**, from the check of its own entries. -/
theorem hintsOk_of_fn {F : Fun} {fs : List (ℕ × ℕ × List (ℕ × List Hint))} {j : ℕ}
    {d : ℕ × ℕ × List (ℕ × List Hint)} (hfs : fnsOk fs 0 = true) (hj : fs[j]? = some d)
    (h : fnChk F d = true) : HintsOk F (flatFns fs) := by
  simp only [fnChk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨he, hn⟩, hinc⟩, hc⟩ := h
  intro i hi
  rw [hintsChk_sound hinc hc i (Nat.zero_le _) (by omega),
    hintsAt_fns hfs (List.mem_of_getElem? hj) (by omega) (by omega), he]

end

end LeanVM.Guest.Mode
