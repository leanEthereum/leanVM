/-
  LeanVM.Guest.B1.Place.LrPure

  `level_residual`'s loops place nothing; a pure callee's size before the memory; a free window
  of addresses.
-/

module

public import LeanVM.Guest.B1.Place.Lr

/-!
# `level_residual`'s loops, pure

* `lrLoop1_pureIn`, `lrLoop2_pureIn`: the batches' loop with `residual_batch`, and the rest's
  loop, place nothing and call only each other.
* `relAtIn_pure_uniform`: a pure callee whose relation holds on the memory kept on its words
  `Lk`, on every memory defined below `2^κ` holding them, is placed there by trees of one size.
* `exists_free_window`: `L` consecutive addresses missing a list of `m` addresses, when
  `(m + 1)·L` addresses exist.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## Purity -/

theorem lrPureList_eq_all (S : List String) :
    ∀ l : List Stmt, Stmt.pureList S l = l.all (Stmt.pure S)
  | [] => rfl
  | s :: l => by simp [Stmt.pureList, lrPureList_eq_all S l]

theorem lrResQ_mem (pos bd row vo : ℕ) : ∀ (n t pe k : ℕ), ∀ s ∈ (osResQ pos bd row vo n t pe k).1,
    ∃ a, s = .atom a ∧ atomUnplaced a = true
  | 0, _, _, _, s, hs => by simp [osResQ] at hs
  | n + 1, t, pe, k, s, hs => by
    simp only [osResQ, List.cons_append, List.mem_cons, List.nil_append] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | hs
    all_goals first
      | exact ⟨_, rfl, rfl⟩
      | exact lrResQ_mem pos bd row vo n (t + 1) (k + 5) (k + 6) s hs

theorem lrResQuery_pure (S : List String) (pos bd row vo n k : ℕ) :
    ∀ s ∈ (osResQuery pos bd row vo n k).1, Stmt.pure S s = true := by
  intro s hs
  simp only [osResQuery, List.cons_append, List.nil_append, List.mem_cons] at hs
  rcases hs with rfl | rfl | hs
  · rfl
  · rfl
  · obtain ⟨a, rfl, ha⟩ := lrResQ_mem pos bd row vo _ _ _ _ s hs; exact ha

theorem lrResSteps_pure (S : List String) (pp bd row vo ncols mu : ℕ) :
    ∀ (js : List ℕ) (h k : ℕ), ∀ s ∈ (osResSteps pp bd row vo ncols mu js h k).1,
      Stmt.pure S s = true
  | [], _, _, s, hs => by simp [osResSteps] at hs
  | j :: js, h, k, s, hs => by
    simp only [osResSteps, osResStep, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    rcases hs with ((rfl | hs) | rfl | rfl) | hs
    · rfl
    · exact lrResQuery_pure S _ _ _ _ _ _ s hs
    · rfl
    · rfl
    · exact lrResSteps_pure S pp bd row vo ncols mu js _ _ s hs

theorem rbBody_pure (S : List String) (cols : ℕ) : Stmt.pureList S (rbBody cols) = true := by
  rw [lrPureList_eq_all, rbBody_chain]
  simp only [List.all_append, List.all_eq_true.mpr (lrResSteps_pure S _ _ _ _ _ _ _ _ _)]
  rfl

theorem lrLoop1Body_pure (cols : ℕ) (name : String) :
    Stmt.pureList [name, rbName cols] (lrLoop1Body cols name) = true := by
  rw [lrPureList_eq_all]
  simp [lrLoop1Body, osLoopTail, Stmt.pure, atomUnplaced]

theorem lrLoop2Body_pure (cols : ℕ) (name : String) :
    Stmt.pureList [name] (lrLoop2Body cols name) = true := by
  rw [lrPureList_eq_all, lrIter2Body_eq, osLoopTail_split]
  simp only [lrIter2A, List.all_append, List.all_eq_true.mpr (lrResQuery_pure [name] _ _ _ _ _ _)]
  simp [osLoopTailA, Stmt.pure, atomUnplaced]

/-- **The batches' loop and `residual_batch` place nothing.** -/
theorem lrLoop1_pureIn {cols : ℕ} {loop : String} (hl : FnIs loop (osParams 6) (lrLoop1Body cols loop))
    (hrb : FnIs (rbName cols) (osParams 4) (rbBody cols)) :
    coreProgram.PureIn [loop, rbName cols] := by
  intro g hg fn hf
  obtain ⟨fl, hfl, -, hbl⟩ := hl
  obtain ⟨fr, hfr, -, hbr⟩ := hrb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · rw [hfl] at hf; cases hf; rw [hbl]; exact lrLoop1Body_pure _ _
  · rw [hfr] at hf; cases hf; rw [hbr]; exact rbBody_pure _ _

/-- **The rest's loop places nothing.** -/
theorem lrLoop2_pureIn {cols : ℕ} {loop : String} (hl : FnIs loop (osParams 6) (lrLoop2Body cols loop)) :
    coreProgram.PureIn [loop] := by
  intro g hg fn hf
  obtain ⟨fl, hfl, -, hbl⟩ := hl
  rw [List.mem_singleton] at hg
  subst hg
  rw [hfl] at hf; cases hf; rw [hbl]; exact lrLoop2Body_pure _ _

/-! ## A pure callee, one size on every memory -/

/-- **A pure callee on the words `Lk`, one size**: its relation on every memory defined below
`2^κ` holding `Lk`, kept on `Lk`, places it on all of them by trees of one size. -/
theorem relAtIn_pure_uniform {S : List String} (hS : coreProgram.PureIn S) {g : String} (hg : g ∈ S)
    (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {Lk : Layout} {args rets : List E}
    (h : ∀ rd, LowDef κ rd → MemL rd Lk →
      coreProgram.Rel (Main.restrict rd (RegionL Lk)) g args rets) :
    ∃ n, ∀ fp rd, LowDef κ rd → MemL rd Lk →
      RelAtIn coreProgram fs cert rd (RegionL Lk) (fun _ ↦ False) fp n g args rets := by
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lk
  swap
  · exact ⟨0, fun fp rd hl hL ↦ absurd ⟨rd, hl, hL⟩ hex⟩
  obtain ⟨rd1, hl1, h1⟩ := hex
  have hsupp := Main.restrict_supp' rd1 (RegionL Lk)
  obtain ⟨n, hn⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg
    (Main.relIn_of_rel_supp coreProgram_wf hsupp (h rd1 hl1 h1))
  refine ⟨n, fun fp rd _ hL ↦ hn fp rd (fun i hi ↦ ?_) (fun A hA ↦ ?_)⟩
  · rw [Main.memL_agree hL h1 i hi, Main.restrict_of ⟨i, rfl, hi⟩]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi⟩ := hsupp _ _ hv
    rw [Main.memL_agree hL h1 i hi, ← Main.restrict_of (rd := rd1) (S := RegionL Lk) ⟨i, rfl, hi⟩, hv]
    rfl

/-! ## A free window -/

/-- **`L` consecutive addresses missing `As`**, below the group's order. -/
theorem exists_free_window (As : List K) {L : ℕ} (hL0 : 0 < L)
    (hL : (As.length + 1) * L ≤ 2 ^ 64 - 1) :
    ∃ c, c + L ≤ 2 ^ 64 - 1 ∧ ∀ t < L, addressOfIndex (c + t) ∉ As := by
  classical
  by_contra hne
  push Not at hne
  have hf : ∀ k ∈ Finset.range (As.length + 1), ∃ t < L, addressOfIndex (k * L + t) ∈ As := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    exact hne (k * L) (le_trans (by nlinarith) hL)
  choose! τ hτ hτm using hf
  have hlt : ∀ k ∈ Finset.range (As.length + 1), k * L + τ k < 2 ^ 64 - 1 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have := hτ k hk
    nlinarith
  have hinj : Set.InjOn (fun k ↦ addressOfIndex (k * L + τ k))
      (↑(Finset.range (As.length + 1)) : Set ℕ) := by
    intro a ha b hb hab
    have e := gpow_injOn (Set.mem_Iio.mpr (hlt a ha)) (Set.mem_Iio.mpr (hlt b hb)) hab
    have da : (a * L + τ a) / L = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL0, Nat.div_eq_of_lt (hτ a ha), Nat.zero_add]
    have db : (b * L + τ b) / L = b := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL0, Nat.div_eq_of_lt (hτ b hb), Nat.zero_add]
    rw [← da, ← db, e]
  have hc := Finset.card_le_card_of_injOn _ (fun k hk ↦ List.mem_toFinset.mpr (hτm k hk)) hinj
  rw [Finset.card_range] at hc
  have := List.toFinset_card_le As
  omega

end
end LeanVM.Guest.B1
