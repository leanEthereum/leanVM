/-
  LeanVM.Protocol.EndToEnd.Front.FlockMech

  The mechanism of the front phases' specifications: doom as "no candidate is alive", prover
  moves keeping it, a challenge escaping it with the union bound over the candidates, and the
  loops of reads and samples of the verifier program.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Leaves
public import LeanVM.Protocol.EndToEnd.Front.PubEscape

/-!
# Doom over candidates

The front phases' doom is that no candidate of the level-0 commitment is *alive*: no candidate is
in the phase's ArkLib knowledge state at the decoded transcript (`Doomed C A h`, `C h` the
candidates the history `h` binds). Along a phase's local run the history gains no commitment, and
the candidates do not change (`Stable`).

* `doomRead`, `doomReadN`: a prover's scalars keep doom, with the alive predicate unchanged (the
  ArkLib phase's `toFun_next` is applied where the next challenge is bounded, not at the read).
* `doomSample`: a challenge escapes doom with average at most `L₀ · e` when it escapes for each
  candidate with average at most `e` (the ArkLib phase's worst-case per-challenge bound) and there
  are at most `L₀` candidates.
* `doomSampleN`: `n` challenges in a row, the alive predicate on the challenges so far, with
  per-challenge bounds `e i`: lead `Σ_i L₀ · e i` plus the follower's.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile
open scoped ENNReal

@[expose] public section

variable {β : Type}

/-- No candidate the history binds is alive. -/
def Doomed (C : List Ev → Set β) (A : β → Prop) (h : List Ev) : Prop := ∀ q ∈ C h, ¬ A q

/-- The candidates a history binds do not change along a run with no commitment. -/
def Stable (C : List Ev → Set β) : Prop := ∀ h₀ l, commits l = [] → C (h₀ ++ l) = C h₀

/-- The commitments of a concatenation are the concatenation of the commitments. -/
theorem commits_append : ∀ h l : List Ev, commits (h ++ l) = commits h ++ commits l
  | [], _ => rfl
  | Ev.commit ht w word :: h, l => by
    rw [List.cons_append]
    simp only [commits, commits_append h l, List.cons_append]
  | Ev.read _ :: h, l => commits_append h l
  | Ev.sample _ :: h, l => commits_append h l
  | Ev.grind _ :: h, l => commits_append h l
  | Ev.query _ :: h, l => commits_append h l

/-- **Candidates read off the commitments are stable**: a run with no commitment does not change
them. For the leanVM program, the candidates of the level-0 commitment (`Candidates`, at the word
of commitment `0`) are of this form. -/
theorem stable_of_commits (f : List (ℕ × ℕ × Word) → Set β) : Stable fun h ↦ f (commits h) := by
  intro h₀ l hl
  simp only [commits_append, hl, List.append_nil]

/-- Doom for a predicate gives doom for a stronger one. -/
theorem Doomed.mono {C : List Ev → Set β} {A A' : β → Prop} {h : List Ev}
    (hd : Doomed C A h) (hA : ∀ q, A' q → A q) : Doomed C A' h :=
  fun q hq ha ↦ hd q hq (hA q ha)

/-- Doom is the same after a run with no commitment. -/
theorem Doomed.append {C : List Ev → Set β} (hst : Stable C) {A : β → Prop} {h₀ l : List Ev}
    (hl : commits l = []) : Doomed C A (h₀ ++ l) ↔ Doomed C A h₀ := by
  unfold Doomed
  rw [hst h₀ l hl]

/-- The average over a challenge of the indicator of an event, as the calculus counts it. -/
theorem card_filter_eq_avgE (p : E → Prop) [DecidablePred p] :
    (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter p).card : ℝ≥0∞) =
      avgE fun c ↦ indE (p c) := by
  rw [avgE_indE_eq_prEvent, SampleableType.prEvent_uniformSample, div_eq_mul_inv, mul_comm]

variable {C : List Ev → Set β} {εmax T : ℝ≥0∞}

/-! ## Reads -/

/-- A prover's scalar keeps doom. -/
noncomputable def doomRead (hst : Stable C) (A : β → Prop) (hT : T ≤ εmax) :
    Spec Prog.readE (Doomed C A) (fun _ h ↦ Doomed C A h) εmax 0 T :=
  Spec.readE (fun _ _ hd ↦ (Doomed.append hst rfl).mpr hd) hT

/-- `n` prover scalars keep doom; the lead is `0` after at least one. -/
noncomputable def doomReadN (hst : Stable C) (A : β → Prop) (hT : T ≤ εmax) :
    (n : ℕ) → Spec (Prog.readN (n + 1)) (Doomed C A)
      (fun xs h ↦ xs.length = n + 1 ∧ Doomed C A h) εmax 0 T
  | 0 => (doomRead hst A hT).bind' fun x ↦
      (Spec.ret (Post := fun xs h ↦ xs = [] ∧ Doomed C A h) []).mono
        (fun _ hd ↦ ⟨rfl, hd⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind' fun xs ↦
          (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl
            le_rfl le_rfl
  | n + 1 => (doomRead hst A (zero_le.trans (zero_le.trans le_rfl))).mono (fun _ h ↦ h)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind' fun x ↦
        (doomReadN hst A hT n).bind' fun xs ↦
          (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl
            le_rfl le_rfl

/-! ## Samples -/

variable [Finite β] {L₀ : ℕ}

/-- **A challenge escapes doom** with average at most `L₀ · e`: for each candidate not alive, the
challenge makes it alive with average at most `e`. -/
noncomputable def doomSample (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (A : β → Prop) (A' : E → β → Prop) (e : ℝ≥0∞)
    (hesc : ∀ q, ¬ A q → avgE (fun c ↦ indE (A' c q)) ≤ e) :
    Spec Prog.sampleE (Doomed C A) (fun c h ↦ Doomed C (A' c) h) εmax (L₀ * e + T) T := by
  classical
  refine Spec.sampleE (L₀ * e) fun h₀ hd ↦ ?_
  rw [card_filter_eq_avgE]
  refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
    (avgE_indE_exists_le (Set.toFinite (C h₀)) (hcard h₀) (P := fun q c ↦ A' c q)
      fun q hq ↦ hesc q (hd q hq))
  rw [Doomed.append hst rfl] at hc
  by_contra hn
  exact hc fun q hq ha ↦ hn ⟨q, hq, ha⟩

/-- **`n` challenges in a row**, the alive predicate on the challenges drawn so far after `acc`:
each challenge escapes with average at most `e` of the number drawn before it. -/
noncomputable def doomSampleN (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (A : List E → β → Prop) (e : ℕ → ℝ≥0∞)
    (hesc : ∀ acc q, ¬ A acc q → avgE (fun c ↦ indE (A (acc ++ [c]) q)) ≤ e acc.length) :
    (n : ℕ) → (acc : List E) →
      Spec (Prog.sampleN n) (Doomed C (A acc))
        (fun l h ↦ l.length = n ∧ Doomed C (A (acc ++ l)) h) εmax
        ((∑ i ∈ Finset.range n, L₀ * e (acc.length + i)) + T) T
  | 0, acc => (Spec.ret []).mono (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h) le_rfl
      (by simp) le_rfl
  | n + 1, acc =>
    ((doomSample (εmax := εmax) (T := (∑ i ∈ Finset.range n, L₀ * e (acc.length + 1 + i)) + T)
        hst hcard (A acc) (fun c ↦ A (acc ++ [c])) (e acc.length)
        (fun q hq ↦ hesc acc q hq)).bind' fun c ↦
      (doomSampleN hst hcard A e hesc n (acc ++ [c])).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
        (by simp [add_assoc]) le_rfl |>.bind' fun cs ↦
          (Spec.ret (c :: cs)).mono (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
      (by
        rw [Finset.sum_range_succ', add_zero, ← add_assoc, add_comm (L₀ * e acc.length)]
        gcongr with i hi
        exact le_of_eq (by rw [add_assoc, add_comm 1 i]))
      le_rfl

end
end LeanVM.Protocol.EndToEnd.Front
