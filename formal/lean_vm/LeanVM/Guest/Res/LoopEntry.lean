/-
  LeanVM.Guest.Res.LoopEntry

  What `entL` gives on a path: every call of a loop helper starts its counter at `g^0` or `g^1`.
-/

module

public import LeanVM.Guest.Res.LoopDefs
public import LeanVM.Guest.Memory.StaticSound

/-!
# Loop entries on a path

`entL_sound`: on a path of a block passing `entL`, its events holding, every call event of a loop
helper (entered or not) has as first argument a value `g^0` or `g^1`, given the values `cs` it
starts from are.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A value `g^0` or `g^1`. -/
def Start (u : E) : Prop := u = ofK (addressOfIndex 0) ∨ u = ofK (addressOfIndex 1)

/-- An event's call of a loop helper starts its counter at `g^0` or `g^1`. -/
def EntryEv (σ : Val) (ev : Ev) : Prop :=
  ∀ c, ev.call? = some c → isLoopName c.f = true → ∃ a rest, c.args = a :: rest ∧ Start (σ a)

section

variable {σ : Val} {rd : Reader}

theorem constsAdd_ok {cs : List V} (hcs : ∀ v ∈ cs, Start (σ v)) {s : Stmt} {es : List Ev}
    (hw : walk1 σ s = .fall es) (hh : HoldsAll rd σ es) : ∀ v ∈ constsAdd cs s, Start (σ v) := by
  intro v hv
  cases s with
  | atom a =>
    cases a with
    | const x w =>
      simp only [constsAdd] at hv
      split_ifs at hv with hk
      · rcases List.mem_cons.mp hv with rfl | hv
        · simp only [walk1, Out.fall.injEq] at hw
          subst hw
          have hx : σ v = w := hh _ List.mem_cons_self
          rw [Bool.or_eq_true] at hk
          rcases hk with hk | hk
          · exact Or.inl (hx.trans (constOk_spec hk).1)
          · exact Or.inr (hx.trans (constOk_spec hk).1)
        · exact hcs v hv
      · exact hcs v hv
    | _ => exact hcs v hv
  | _ => exact hcs v hv

theorem argOk_sound {cs : List V} (hcs : ∀ v ∈ cs, Start (σ v)) {f : String} {args : List V}
    (h : argOk cs f args = true) (hl : isLoopName f = true) : ∃ a rest, args = a :: rest ∧ Start (σ a) := by
  simp only [argOk, hl, Bool.not_true, Bool.false_or] at h
  match args, h with
  | a :: rest, h => exact ⟨a, rest, rfl, hcs a (of_decide_eq_true h)⟩

mutual
theorem entL_sound {nr : Bool} : ∀ (ss : List Stmt) {cs : List V}, entL nr cs ss = true →
    (∀ v ∈ cs, Start (σ v)) → HoldsAll rd σ (walk σ ss).evs → ∀ ev ∈ (walk σ ss).evs, EntryEv σ ev
  | [], _, _, _, _, _, hev => by simp [walk, Out.evs] at hev
  | s :: ss, cs, he, hcs, hh, ev, hev => by
    simp only [entL, Bool.and_eq_true] at he
    rw [walk] at hh hev
    have hrest : ∀ es1 es2, walk1 σ s = .fall es1 → (walk σ ss).evs = es2 →
        HoldsAll rd σ (es1 ++ es2) → ev ∈ es1 ++ es2 → EntryEv σ ev := fun es1 es2 h1 h2 hh' hev' ↦ by
      have hh1 : HoldsAll rd σ es1 := fun e h ↦ hh' e (List.mem_append_left _ h)
      rcases List.mem_append.mp hev' with hev' | hev'
      · exact entS_sound s he.1 hcs (by rw [h1]; exact hh1) ev (by rw [h1]; exact hev')
      · exact entL_sound ss he.2 (constsAdd_ok hcs h1 hh1)
          (by rw [h2]; exact fun e h ↦ hh' e (List.mem_append_right _ h)) ev (by rw [h2]; exact hev')
    rcases h1 : walk1 σ s with es1 | ⟨es1, vs⟩ | _
    · rw [h1] at hh hev
      simp only [Out.seq] at hh hev
      rcases h2 : walk σ ss with es2 | ⟨es2, vs2⟩ | _
      · rw [h2] at hh hev
        exact hrest es1 es2 h1 (by rw [h2]; rfl) hh hev
      · rw [h2] at hh hev
        exact hrest es1 es2 h1 (by rw [h2]; rfl) hh hev
      · rw [h2] at hev; simp [Out.pre, Out.evs] at hev
    · rw [h1] at hh hev
      simp only [Out.seq] at hh hev
      exact entS_sound s he.1 hcs (by rw [h1]; exact hh) ev (by rw [h1]; exact hev)
    · rw [h1] at hev; simp [Out.seq, Out.evs] at hev

theorem entS_sound {nr : Bool} : ∀ (s : Stmt) {cs : List V}, entS nr cs s = true →
    (∀ v ∈ cs, Start (σ v)) → HoldsAll rd σ (walk1 σ s).evs → ∀ ev ∈ (walk1 σ s).evs, EntryEv σ ev
  | .atom a, _, _, _, _, ev, hev => by
    simp only [walk1, Out.evs, List.mem_singleton] at hev
    subst hev; intro c hc; cases hc
  | .ite c z n, cs, he, hcs, hh, ev, hev => by
    simp only [entS, Bool.and_eq_true] at he
    rw [walk1] at hh hev
    have hpre : ∀ o : Out, (∀ e ∈ o.evs, e.Holds rd σ → EntryEv σ e) → HoldsAll rd σ (o.pre [.inK c]).evs →
        ev ∈ (o.pre [.inK c]).evs → EntryEv σ ev := fun o ho hh' hev' ↦ by
      rcases o with es | ⟨es, vs⟩ | _ <;>
        simp only [Out.pre, Out.evs, List.singleton_append, List.mem_cons] at hh' hev' ho ⊢
      · rcases hev' with rfl | hev'
        · intro c' hc'; cases hc'
        · exact ho ev hev' (hh' ev (List.mem_cons_of_mem _ hev'))
      · rcases hev' with rfl | hev'
        · intro c' hc'; cases hc'
        · exact ho ev hev' (hh' ev (List.mem_cons_of_mem _ hev'))
      · exact absurd hev' List.not_mem_nil
    have hsub : ∀ o : Out, HoldsAll rd σ (o.pre [.inK c]).evs → HoldsAll rd σ o.evs := fun o hh' e he' ↦ by
      rcases o with es | ⟨es, vs⟩ | _ <;> simp only [Out.pre, Out.evs] at hh' he' ⊢
      · exact hh' e (List.mem_cons_of_mem _ he')
      · exact hh' e (List.mem_cons_of_mem _ he')
      · cases he'
    split_ifs at hh hev
    · exact hpre _ (fun e he' _ ↦ entL_sound z he.1 hcs (hsub _ hh) e he') hh hev
    · exact hpre _ (fun e he' _ ↦ entL_sound n he.2 hcs (hsub _ hh) e he') hh hev
  | .match_ x arms, _, he, hcs, hh, ev, hev => by
    rw [walk1] at hh hev
    exact entA_sound x arms 0 he hcs hh ev hev
  | .call f args rets, _, he, hcs, _, ev, hev => by
    simp only [walk1, Out.evs, List.mem_singleton] at hev
    subst hev
    intro c hc hl
    simp only [Ev.call?, Option.some.injEq] at hc
    subst hc
    exact argOk_sound hcs he hl
  | .callIf c f args, _, he, hcs, _, ev, hev => by
    simp only [walk1, Out.evs, List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl
    · intro c' hc'; cases hc'
    · intro c' hc' hl
      split_ifs at hc' <;> simp only [Ev.call?, Option.some.injEq] at hc' <;> subst hc' <;>
        exact argOk_sound hcs he hl
  | .dispatch x fs args rets, _, he, _, _, ev, hev => by
    rw [walk1] at hev
    rcases pick_cases (σ := σ) (x := x) (a := args) (r := rets) fs 0 with h | ⟨g, hg, h⟩
    · rw [h] at hev; cases hev
    · rw [h] at hev
      simp only [Out.evs, List.mem_singleton] at hev
      subst hev
      intro c hc hl
      simp only [Ev.call?, Option.some.injEq] at hc
      subst hc
      simp only [entS, List.all_eq_true, Bool.not_eq_true'] at he
      rw [he g hg] at hl; cases hl
  | .ret vs, _, _, _, _, ev, hev => by simp [walk1, Out.evs] at hev

theorem entA_sound {nr : Bool} (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {cs : List V},
    entA nr cs arms = true → (∀ v ∈ cs, Start (σ v)) → HoldsAll rd σ (walkArms σ x j arms).evs →
      ∀ ev ∈ (walkArms σ x j arms).evs, EntryEv σ ev
  | [], _, _, _, _, _, ev, hev => by simp [walkArms, Out.evs] at hev
  | a :: as, j, _, he, hcs, hh, ev, hev => by
    simp only [entA, Bool.and_eq_true] at he
    rw [walkArms] at hh hev
    split_ifs at hh hev
    · exact entL_sound a he.1 hcs hh ev hev
    · exact entA_sound x as (j + 1) he.2 hcs hh ev hev
end

end

end

end LeanVM.Guest.Res
