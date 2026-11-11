/-
  LeanVM.Guest.B1.Place.KidsNames

  A flat body's frames: their callees are its call statements', and their bound is the statements'.
-/

module

public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Place.OsCalls
public import LeanVM.Guest.B1.Place.OsBos

/-!
# A flat body's frames, against its call statements

`kid_mem_callees`: each frame of a flat block (`Stmt.callSF σ`, a dispatch at its selector's
callee) names a callee of one of its call statements (`Stmt.calleesS`). `kids_bound_le`: its
frames' larger of frame and bound is at most the statements' costliest callees' (`osCallB`).
`osKids_names`, `osKids_bound`: for `open_stacked`'s body (`osCalleeNames`, `osKidsB`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

theorem dispatch_name_mem {σ : Val} {x : V} {fs : List String} {a r : List V}
    (h : DispOk σ (.dispatch x fs a r)) : fs.getD (logG (σ x)) "" ∈ fs := by
  obtain ⟨j, hj, hj64, hx⟩ := h
  rw [hx, logG_spec hj64, List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

/-- **A frame of a flat block names a callee of its call statements.** -/
theorem kid_mem_callees {σ : Val} : ∀ {pre : List Stmt}, (∀ s ∈ pre, DispOk σ s) →
    ∀ c ∈ (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ),
      c.f ∈ (pre.filterMap Stmt.calleesS).flatten
  | [], _, c, hc => by simp at hc
  | s :: pre, hdo, c, hc => by
    have ih := kid_mem_callees (pre := pre) (fun s' hs' ↦ hdo s' (List.mem_cons_of_mem _ hs')) c
    match s with
    | .atom _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      simpa [Stmt.calleesS] using ih hc
    | .ret _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      simpa [Stmt.calleesS] using ih hc
    | .ite .. =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      simpa [Stmt.calleesS] using ih hc
    | .match_ .. =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      simpa [Stmt.calleesS] using ih hc
    | .call f a r =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, List.map_cons,
        List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp [Stmt.calleesS, Main.mkCall]
      · simpa [Stmt.calleesS] using Or.inr (ih hc)
    | .callIf cv f a =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, List.map_cons,
        List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp [Stmt.calleesS, Main.mkCall]
      · simpa [Stmt.calleesS] using Or.inr (ih hc)
    | .dispatch x fs a r =>
      simp only [List.filterMap_cons, Stmt.callSF, List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp only [Stmt.calleesS, List.filterMap_cons, List.flatten_cons, List.mem_append]
        exact Or.inl (dispatch_name_mem (hdo _ (List.mem_cons_self ..)))
      · simpa [Stmt.calleesS] using Or.inr (ih hc)

/-- **A flat block's frames' bound** is at most its call statements' costliest callees'. -/
theorem kids_bound_le {σ : Val} (fs Bk : String → ℕ) : ∀ {pre : List Stmt}, (∀ s ∈ pre, DispOk σ s) →
    (((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)).map fun c ↦ max (fs c.f) (Bk c.f)).sum ≤
      ((pre.filterMap Stmt.calleesS).map (osCallB fs Bk)).sum
  | [], _ => by simp
  | s :: pre, hdo => by
    have ih := kids_bound_le fs Bk (pre := pre) fun s' hs' ↦ hdo s' (List.mem_cons_of_mem _ hs')
    match s with
    | .atom _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, Stmt.calleesS]; exact ih
    | .ret _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, Stmt.calleesS]; exact ih
    | .ite .. =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, Stmt.calleesS]; exact ih
    | .match_ .. =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, Stmt.calleesS]; exact ih
    | .call f a r =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, Stmt.calleesS, List.map_cons,
        List.sum_cons, Main.mkCall]
      exact Nat.add_le_add (le_osCallB (List.mem_singleton_self f)) ih
    | .callIf cv f a =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, Stmt.calleesS, List.map_cons,
        List.sum_cons, Main.mkCall]
      exact Nat.add_le_add (le_osCallB (List.mem_singleton_self f)) ih
    | .dispatch x fs' a r =>
      simp only [List.filterMap_cons, Stmt.callSF, Stmt.calleesS, List.map_cons, List.sum_cons,
        Main.mkCall]
      exact Nat.add_le_add (le_osCallB (dispatch_name_mem (hdo _ (List.mem_cons_self ..)))) ih

theorem osBody_calleesS (c : OsCfg) :
    (osBody c).filterMap Stmt.calleesS = (osBodyAc c).filterMap Stmt.calleesS := by
  rw [osBody_splitC, List.filterMap_append]
  simp [Stmt.calleesS]

/-- **`open_stacked`'s frames name its callees.** -/
theorem osKids_names {σ : Val} {c : OsCfg} (hdo : ∀ s ∈ osBodyAc c, DispOk σ s) :
    ∀ c' ∈ ((osBodyAc c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ), c'.f ∈ osCalleeNames c :=
  fun c' hc' ↦ by
    unfold osCalleeNames osCallees
    rw [osBody_calleesS]
    exact kid_mem_callees hdo c' hc'

/-- **`open_stacked`'s frames within its calls' bound.** -/
theorem osKids_bound {σ : Val} {c : OsCfg} (fs Bk : String → ℕ) (hdo : ∀ s ∈ osBodyAc c, DispOk σ s) :
    ((((osBodyAc c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ)).map
      fun c' ↦ max (fs c'.f) (Bk c'.f)).sum ≤ osKidsB fs Bk c := by
  unfold osKidsB osCallees
  rw [osBody_calleesS]
  exact kids_bound_le fs Bk hdo

end
end LeanVM.Guest.B1
