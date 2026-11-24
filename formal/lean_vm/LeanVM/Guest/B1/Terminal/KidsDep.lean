/-
  LeanVM.Guest.B1.Terminal.KidsDep

  Callees whose words depend on the earlier callees' results, placed: `kidsFromIn_of_kidsD` for a list of
  callees each a function of the results before it.
-/

module

public import LeanVM.Guest.B1.Tables.FlatAt

/-!
# Dependent callees, placed

A flat body's callees are placed one after another (`kidsFromIn_of_kidsD`), each `CompleteAtD` on
words fixed beforehand. When a callee reads what an earlier callee returns (`column_selector`
the tables `selector_tables` returns, the terminal the buffers `certify_placement` returns), its
arguments and words depend on the earlier results. `KidD`: a callee as a function of the results
before it; `kidsAt ks prev outs`: the callees on the results `outs`.
`kidsAt`, `outsL` and their lemmas place them, each callee reading the caller's words, its buffers, and the
buffers the earlier callees return (`RegionsOk`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- A callee, as a function of the results of the callees before it. -/
abbrev KidD : Type := List (List E × Layout) → Kid

/-- The callees on the results `outs`, the results before them `prev`. -/
def kidsAt : List KidD → List (List E × Layout) → List (List E × Layout) → List Kid
  | k :: ks, prev, o :: os => k prev :: kidsAt ks (prev ++ [o]) os
  | _, _, _ => []

/-- The buffers the entered callees return. -/
def outsL : List Kid → List (List E × Layout) → Layout
  | k :: ks, o :: os => (if k.taken = true then o.2 else []) ++ outsL ks os
  | _, _ => []

theorem memL_outsL {rd : Reader} : ∀ {ks : List Kid} {outs : List (List E × Layout)} {L : Layout},
    OutsIn ks outs L → MemL rd L → MemL rd (outsL ks outs)
  | k :: ks, o :: os, L, ⟨h, hs⟩, hL => by
    intro q hq
    simp only [outsL, List.mem_append] at hq
    rcases hq with hq | hq
    · by_cases ht : k.taken = true
      · rw [ite_pos' ht] at hq; exact hL q (h ht q hq)
      · rw [ite_neg' ht] at hq; simp at hq
    · exact memL_outsL hs hL q hq
  | [], _, _, _, _ => fun q hq => by simp [outsL] at hq
  | _ :: _, [], _, _, _ => fun q hq => by simp [outsL] at hq

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- A statement other than an `ite`. -/
def notIteB : Stmt → Bool
  | .ite _ _ _ => false
  | _ => true

/-- Without `ite`, the walk's loads are the statements' loads. -/
theorem filterMap_of_loadsEv {σ : Val} : ∀ {pre : List Stmt}, pre.all notIteB = true →
    ∀ {q : V × ℕ}, q ∈ pre.flatMap (loadsEv σ) → q ∈ pre.filterMap Stmt.loadS
  | [], _, _, h => by simp at h
  | s :: pre, hni, q, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hni
    rw [List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · cases s with
      | ite c z n => simp [notIteB] at hni
      | _ =>
        simp only [loadsEv, Option.mem_toList] at h
        simp [h]
    · have := filterMap_of_loadsEv hni.2 h
      cases hs : Stmt.loadS s <;> simp [hs, this]

/-! ## The callees by position -/

/-- No callee (a default). -/
def noKid : KidD := fun _ => ⟨"", false, [], [], fun _ _ => True⟩

/-- No frame (a default). -/
def noCall : Call := ⟨"", [], [], false⟩

/-- Callee `j` on the results before it. -/
def kidAt (ks : List KidD) (prev outs : List (List E × Layout)) (j : ℕ) : Kid :=
  ks.getD j noKid (prev ++ outs.take j)

theorem kidAt_succ (k : KidD) (ks : List KidD) (prev : List (List E × Layout)) (o : List E × Layout)
    (os : List (List E × Layout)) (j : ℕ) :
    kidAt (k :: ks) prev (o :: os) (j + 1) = kidAt ks (prev ++ [o]) os j := by
  simp [kidAt, List.take_succ_cons]

theorem kidAt_zero (k : KidD) (ks : List KidD) (prev outs : List (List E × Layout)) :
    kidAt (k :: ks) prev outs 0 = k prev := by
  simp [kidAt]

/-- **Callees reading the earlier callees' results, by position**: callee `j`'s words lie in `R`,
`Dacc` or an earlier entered callee's result. -/
theorem regionsOk_kidsAt {R : ℕ → Prop} : ∀ (ks : List KidD) (prev outs : List (List E × Layout))
    (Dacc : ℕ → Prop),
    (∀ j, j < ks.length → j < outs.length → (kidAt ks prev outs j).taken = true → ∀ i,
      RegionL (kidAt ks prev outs j).Lin i → R i ∨ Dacc i ∨
        ∃ m < j, (kidAt ks prev outs m).taken = true ∧ RegionL (outs.getD m ([], [])).2 i) →
    RegionsOk R Dacc (kidsAt ks prev outs) outs
  | [], _, _, _, _ => trivial
  | _ :: _, _, [], _, _ => trivial
  | k :: ks, prev, o :: os, Dacc, h => by
    refine ⟨fun ht i hi => ?_, regionsOk_kidsAt ks (prev ++ [o]) os _ fun j hj ho ht i hi => ?_⟩
    · have := h 0 (by simp) (by simp) (by rwa [kidAt_zero]) i (by rwa [kidAt_zero])
      rcases this with h1 | h1 | ⟨m, hm, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
      · omega
    · have := h (j + 1) (by simp; omega) (by simp; omega) (by rwa [kidAt_succ])
        i (by rwa [kidAt_succ])
      rcases this with h1 | h1 | ⟨m, hm, hmt, hmi⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl (Or.inl h1))
      · rcases m with _ | m
        · rw [kidAt_zero] at hmt
          exact Or.inr (Or.inl (Or.inr ⟨hmt, by simpa using hmi⟩))
        · rw [kidAt_succ] at hmt
          exact Or.inr (Or.inr ⟨m, by omega, hmt, by simpa using hmi⟩)

/-- The callees' words, by position. -/
theorem memL_lins_kidsAt {rd : Reader} : ∀ (ks : List KidD) (prev outs : List (List E × Layout)),
    (∀ j, j < ks.length → j < outs.length → MemL rd (kidAt ks prev outs j).Lin) →
    MemL rd (Kid.lins (kidsAt ks prev outs))
  | [], _, _, _ => fun q hq => by simp [kidsAt, Kid.lins] at hq
  | _ :: _, _, [], _ => fun q hq => by simp [kidsAt, Kid.lins] at hq
  | k :: ks, prev, o :: os, h => by
    intro q hq
    simp only [kidsAt, Kid.lins, List.flatMap_cons, List.mem_append] at hq
    rcases hq with hq | hq
    · have := h 0 (by simp) (by simp)
      rw [kidAt_zero] at this
      exact this q hq
    · exact memL_lins_kidsAt ks (prev ++ [o]) os (fun j hj ho => by
        have := h (j + 1) (by simp; omega) (by simp; omega)
        rwa [kidAt_succ] at this) q hq

/-- An entered callee's result, by position. -/
theorem outsOk_at : ∀ {ks : List KidD} {prev outs : List (List E × Layout)},
    OutsOk (kidsAt ks prev outs) outs → ∀ m, m < ks.length → m < outs.length →
      (kidAt ks prev outs m).taken = true →
      (kidAt ks prev outs m).Out (outs.getD m ([], [])).1 (outs.getD m ([], [])).2
  | [], _, _, _, m, hm, _, _ => absurd hm (by simp)
  | _ :: _, _, [], _, m, _, hm, _ => absurd hm (by simp)
  | k :: ks, prev, o :: os, ⟨h0, hs⟩, m, hm, ho, ht => by
    rcases m with _ | m
    · rw [kidAt_zero] at ht ⊢
      exact h0 ht
    · rw [kidAt_succ] at ht ⊢
      simpa using outsOk_at hs m (by simp at hm; omega) (by simp at ho; omega) ht

/-- An entered callee's result is in `outsL`, by position. -/
theorem memL_outsL_at {rd : Reader} : ∀ {ks : List KidD} {prev outs : List (List E × Layout)},
    MemL rd (outsL (kidsAt ks prev outs) outs) → ∀ m, m < ks.length → m < outs.length →
      (kidAt ks prev outs m).taken = true → MemL rd (outs.getD m ([], [])).2
  | [], _, _, _, m, hm, _, _ => absurd hm (by simp)
  | _ :: _, _, [], _, m, _, hm, _ => absurd hm (by simp)
  | k :: ks, prev, o :: os, h, m, hm, ho, ht => by
    simp only [kidsAt, outsL] at h
    obtain ⟨h1, h2⟩ := Main.memL_append.mp h
    rcases m with _ | m
    · rw [kidAt_zero] at ht
      rw [ite_pos' ht] at h1
      simpa using h1
    · rw [kidAt_succ] at ht
      simpa using memL_outsL_at h2 m (by simp at hm; omega) (by simp at ho; omega) ht

/-- **The frames match the callees, by position.** -/
theorem callsMatch_kidsAt {σ : Val} : ∀ (cs : List Call) (ks : List KidD)
    (prev outs : List (List E × Layout)), cs.length = ks.length → ks.length = outs.length →
    (∀ j, j < cs.length → (cs.getD j noCall).f = (kidAt ks prev outs j).f ∧
      (cs.getD j noCall).taken = (kidAt ks prev outs j).taken ∧
      ((kidAt ks prev outs j).taken = true →
        (cs.getD j noCall).args.map σ = (kidAt ks prev outs j).args ∧
          (cs.getD j noCall).rets.map σ = (outs.getD j ([], [])).1)) →
    CallsMatch σ cs (kidsAt ks prev outs) outs
  | [], [], _, [], _, _, _ => trivial
  | c :: cs, k :: ks, prev, o :: os, h1, h2, h => by
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, kidAt_zero] at h0
    refine ⟨h0.1, h0.2.1, fun ht => ?_, callsMatch_kidsAt cs ks (prev ++ [o]) os (by simpa using h1)
      (by simpa using h2) fun j hj => ?_⟩
    · simpa using h0.2.2 ht
    · have := h (j + 1) (by simp; omega)
      simp only [List.getD_cons_succ, kidAt_succ] at this
      simpa using this
  | [], _ :: _, _, _, h1, _, _ => absurd h1 (by simp)
  | _ :: _, [], _, _, h1, _, _ => absurd h1 (by simp)
  | [], [], _, _ :: _, _, h2, _ => absurd h2 (by simp)
  | _ :: _, _ :: _, _, [], _, h2, _ => absurd h2 (by simp)

end
end LeanVM.Guest.B1
