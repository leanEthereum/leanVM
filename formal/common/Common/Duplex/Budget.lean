module

public import Common.Duplex.Chal

@[expose] public section

/-!
# The probability of a collision

A fresh answer of the simulator is uniform, or a fixed challenge with a uniform rest; its
capacity hits one of the at most `2 · #log + 2` capacities seen with probability at most that many
times `εc`, the largest probability of a capacity (`step_bad_le`). Over a run with at most `N`
calls of `F`, a collision occurs with probability at most `N · (2N · εc)` (`prob_bad_le`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Common
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace Common.SeedDuplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W] [Fintype Root] [Nonempty Z]
  {D : DuplexSpec Msg Dg St Root Z W Cp n}

/-- The distribution of a fresh answer against the table `g`. -/
noncomputable def freshDist (D : DuplexSpec Msg Dg St Root Z W Cp n) (g : Tab Root Z n)
    (s : SimSt Dg St Root n) (x : St) : ProbComp St :=
  match progLbl D s x with
  | some (r, j) => (fun w ↦ D.build (g.at r j, w)) <$> ($ᵗ W : ProbComp W)
  | none => ($ᵗ St : ProbComp St)

theorem tab_F_run_fresh (g : Tab Root Z n) (x : St) (s : SimSt Dg St Root n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) (hc : GFree c) (hx : s.answer x = none) :
    (tabImpl D g (.inr (.inr x))).run (s, c) =
      (fun y ↦ (y, (s.record D x y (progLbl D s x), c))) <$> freshDist D g s x := by
  rw [tabImpl, foldWith_run]
  simp only [simImpl, StateT.run_mk, hx, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure]
  unfold freshAns freshDist progLbl
  split
  · next r j hrj =>
    simp only [hrj]
    split_ifs with hu
    · simp [simulateQ_eagerImpl_liftM, map_eq_bind_pure_comp]
    · simp only [map_eq_bind_pure_comp]
      simp
      erw [tabOuter_G_run]
      simp only [hc (r, j), Option.getD_none, pure_bind]
      erw [simulateQ_eagerImpl_liftM]
      simp [Functor.map_map]
  · next hrj =>
    simp only [hrj]
    simp [simulateQ_eagerImpl_liftM, map_eq_bind_pure_comp]

theorem pr_capW_mem_le {εc : ℝ≥0∞}
    (hcap : ∀ c, Pr{let w ← ($ᵗ W : ProbComp W)}[D.capW w = c] ≤ εc) (F : Finset Cp) :
    Pr{let w ← ($ᵗ W : ProbComp W)}[D.capW w ∈ F] ≤ F.card * εc := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    calc Pr{let w ← ($ᵗ W : ProbComp W)}[D.capW w ∈ insert a F]
        = Pr{let w ← ($ᵗ W : ProbComp W)}[D.capW w = a ∨ D.capW w ∈ F] := by
          simp [Finset.mem_insert]
      _ ≤ εc + F.card * εc := (prEvent_or_le _ _ _).trans (add_le_add (hcap a) ih)
      _ = (insert a F).card * εc := by
          rw [Finset.card_insert_of_notMem ha]; push_cast; ring

/-- The capacity of a fresh answer hits a finite set with probability at most its size times
`εc`. -/
theorem pr_fresh_cap_le {εc : ℝ≥0∞}
    (hcap : ∀ c, Pr{let w ← ($ᵗ W : ProbComp W)}[D.capW w = c] ≤ εc) (g : Tab Root Z n)
    (s : SimSt Dg St Root n) (x : St) (F : Finset Cp) :
    Pr{let y ← freshDist D g s x}[D.cap y ∈ F] ≤ F.card * εc := by
  unfold freshDist
  split
  · rw [prEvent_map]
    simpa [Function.comp_def, DuplexSpec.cap] using pr_capW_mem_le hcap F
  · have h := (uniform_build D).prEvent_eq (fun y ↦ D.cap y ∈ F)
    rw [← h]
    simp only [prEvent_norm]
    have e : ∀ a w, D.cap (D.build (a, w)) = D.capW w := fun a w ↦ by simp [DuplexSpec.cap]
    simp only [e]
    rw [OracleComp.prEvent_bind_const]
    exact pr_capW_mem_le hcap F

/-- Calls of `F`, one each. -/
def fCalls : (Rom2 Msg Dg St).Domain → ℕ
  | .inr (.inr _) => 1
  | _ => 0

theorem card_forb_le (s : SimSt Dg St Root n) : (forb D s).card ≤ 2 * s.log.length + 1 := by
  unfold forb
  refine (List.toFinset_card_le _).trans ?_
  simp only [List.length_append, List.length_map]
  rcases s.x0 <;> simp <;> omega

/-- **The collision budget**: a run of the table world with at most `N` calls of `F` ends with
a collision with probability at most `N · (2N · εc)`. -/
theorem prob_bad_le {εc : ℝ≥0∞}
    (hcap : ∀ c, Pr{let w ← ($ᵗ W : ProbComp W)}[D.capW w = c] ≤ εc) (g : Tab Root Z n)
    {α : Type} (X : OracleComp (Rom2 Msg Dg St) α) (N : ℕ)
    (hX : QueryCostAtMost X (fCalls (Msg := Msg) (Dg := Dg) (St := St)) N) :
    Pr{let z ← (simulateQ (tabImpl D g) X).run
        ((SimSt.init : SimSt Dg St Root n), (∅ : (GSpec Msg Dg Root Z n).QueryCache))}[
        z.2.1.bad = true] ≤ N * (2 * N * εc) := by
  classical
  have h := prEvent_run_bad_le (tabImpl D g) (fun sc ↦ sc.1.bad = true) (fun sc ↦ GFree sc.2)
    fCalls (fun sc ↦ sc.1.log.length) N (2 * N * εc)
    (fun t sc h z hz ↦ gfree_step g t sc h hz) ?_ ?_ X N hX
    ((SimSt.init : SimSt Dg St Root n), (∅ : (GSpec Msg Dg Root Z n).QueryCache))
    (fun _ ↦ rfl) (by simp [SimSt.init])
  · simpa [SimSt.init] using h
  · intro t sc hc z hz
    obtain ⟨s, c⟩ := sc
    rcases t with k | m | x
    · rw [tab_coin D g k s c hz]; simp
    · obtain ⟨-, h⟩ := tab_H D g m s c hz
      rw [h]; split_ifs <;> simp
    · rcases tab_F D g x s c hc hz with ⟨-, h⟩ | ⟨-, h, -⟩
      · rw [h]; simp
      · rw [h]; simp [log_record, fCalls]
  · intro t sc hc hb hN
    obtain ⟨s, c⟩ := sc
    simp only at hb hN
    rcases t with k | m | x
    · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_) zero_le
      rw [tab_coin D g k s c hz]; simpa using hb
    · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_) zero_le
      obtain ⟨-, h⟩ := tab_H D g m s c hz
      rw [h]; split_ifs <;> simpa using hb
    · rcases ha : s.answer x with _ | y
      · rw [tab_F_run_fresh g x s c hc ha, prEvent_map]
        simp only [bad_record, Bool.not_eq_true] at hb ⊢
        simp only [hb, Bool.false_or, decide_eq_true_eq]
        refine (pr_fresh_cap_le hcap g s x _).trans ?_
        have h2 : s.log.length + 1 ≤ N := hN
        have hcard : (insert (D.cap x) (forb D s)).card ≤ 2 * N := by
          have := card_forb_le (D := D) s
          have := Finset.card_insert_le (D.cap x) (forb D s)
          omega
        have hcard' : ((insert (D.cap x) (forb D s)).card : ℝ≥0∞) ≤ 2 * N := by
          exact_mod_cast hcard
        simp only [fCalls, Nat.cast_one, one_mul]
        gcongr
      · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_) zero_le
        rcases tab_F D g x s c hc hz with ⟨-, h⟩ | ⟨ha', -, -⟩
        · rw [h]; simpa using hb
        · rw [ha] at ha'; cases ha'

end Common.SeedDuplex
