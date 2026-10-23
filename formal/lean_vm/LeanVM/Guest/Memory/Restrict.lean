/-
  LeanVM.Guest.Memory.Restrict

  A reader restricted to a region, and the loads of a tree valid on it: they read the region; a
  pure function's tree reads what its memory holds, so it is placed anywhere.
-/

module

public import LeanVM.Guest.Memory.Retemp

/-!
# Restricted readers

`restrict rd S` reads `rd` at the addresses `g^i` with `S i` and nothing elsewhere. A tree valid on
a reader that reads nothing outside `R` loads from `R` only (`loadsR_of_supp`), so a relation
proved on the restriction of a memory to the regions a function's honest words lie in is a
relation loading from those regions (`relIn_of_rel_supp`). A pure function's valid tree reads what
its memory holds (`eqns_read_pure`), so its relation on such a reader is placed anywhere, of one
size, on every memory extending it (`relAtIn_uniform_of_supp`). Also the `filterMap`s of events
over appends (`calls_append`, `allocs_append`, ...) and `mem_calls_taken`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

open Classical in
/-- `rd` at the addresses `g^i` with `S i`, nothing elsewhere. -/
noncomputable def restrict (rd : Reader) (S : ℕ → Prop) : Reader := fun A =>
  if ∃ i, A = gpow i ∧ S i then rd A else none

theorem restrict_supp {rd : Reader} {S : ℕ → Prop} {A : K} {v : E} (h : restrict rd S A = some v) :
    ∃ i, A = gpow i ∧ S i := by
  unfold restrict at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem restrict_of {rd : Reader} {S : ℕ → Prop} {A : K} (h : ∃ i, A = gpow i ∧ S i) :
    restrict rd S A = rd A := by
  unfold restrict; simp only [h, ↓reduceIte]

theorem loadHolds_restrict {rd : Reader} {S : ℕ → Prop} {p : E} {k : ℕ} {v : E}
    (h : LoadHolds rd p k v) (hS : ∃ i, p.limb 0 * gpow k = gpow i ∧ S i) :
    LoadHolds (restrict rd S) p k v :=
  ⟨h.1, by rw [restrict_of hS]; exact h.2⟩

section Supp

variable {P : Core.Program} {rd : Reader} {R : ℕ → Prop}

theorem loads_of_supp (hR : ∀ A v, rd A = some v → ∃ i, A = gpow i ∧ R i) {σ : Val} {es : List Ev}
    (hes : ∀ e ∈ es, e.Holds rd σ) : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ R i := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  match e, he, hea with
  | .atom (.load d p off), he, hea =>
    simp only [Ev.loadAddr?, Option.some.injEq] at hea
    subst hea
    exact hR _ _ (hes _ he).2

mutual
/-- **A tree valid on a reader that reads nothing outside `R` loads from `R`.** -/
theorem loadsR_of_supp (hR : ∀ A v, rd A = some v → ∃ i, A = gpow i ∧ R i) :
    ∀ (t : Tree) {args rets : List E}, t.Valid P rd args rets → t.LoadsR P R
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩ => by
      rw [Tree.LoadsR, events_node hf hw]
      exact ⟨loads_of_supp hR hes, loadsRKids_of_supp hR kids σ (calls es) hk⟩
  | .phantom .., _, _, h => h.elim

/-- `loadsR_of_supp` for the callees. -/
theorem loadsRKids_of_supp (hR : ∀ A v, rd A = some v → ∃ i, A = gpow i ∧ R i) :
    ∀ (ks : List Tree) (σ : Val) (cs : List Call), Tree.KidsValid P rd σ cs ks → Tree.LoadsRKids P R ks
  | [], _, _, _ => by rw [Tree.LoadsRKids]; trivial
  | k :: ks, σ, c :: cs, ⟨_, hc, hks⟩ => by
      rw [Tree.LoadsRKids]
      refine ⟨?_, loadsRKids_of_supp hR ks σ cs hks⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact loadsR_of_supp hR k hc
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        rw [Tree.LoadsR]; trivial
  | _ :: _, _, [], h => h.elim
end

/-- **A relation on a reader that reads nothing outside `R` loads from `R`.** -/
theorem relIn_of_rel_supp (hP : P.Wf) (hR : ∀ A v, rd A = some v → ∃ i, A = gpow i ∧ R i)
    {f : String} {args rets : List E} (h : P.Rel rd f args rets) : P.RelIn rd R f args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.Rel.tree hP h
  exact ⟨t, hn, hv, hb, loadsR_of_supp hR t hv⟩

theorem restrict_supp' (rd : Reader) (S : ℕ → Prop) :
    ∀ A v, restrict rd S A = some v → ∃ i, A = gpow i ∧ S i :=
  fun _ _ h => restrict_supp h

end Supp

/-! ## Pure functions -/

section Uniform

variable {P : Core.Program} {rd0 : Reader} {S : List String}

theorem atomEqns_read_pure {σ : Val} : ∀ (a : Atom), atomUnplaced a = true → a.Holds rd0 σ →
    ∀ q ∈ atomEqns σ a, rd0 q.1 = some q.2
  | .load .., _, h, q, hq => by rw [List.mem_singleton.mp hq]; exact h.2
  | .rangeCheck .., _, h, q, hq => by
      simp only [atomEqns, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact h.1.2
      · exact h.2.2.2
  | .frameAddr .., hu, _, _, _ => by simp [atomUnplaced] at hu
  | .const .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .add .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .mul .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .copy .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .assertEq .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .assertNe .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .assertInK .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .blake2s .., _, _, _, hq => (List.not_mem_nil hq).elim
  | .hint _, _, _, _, hq => (List.not_mem_nil hq).elim

mutual
/-- **A valid tree of a pure function reads what its memory holds**, every equation. -/
theorem eqns_read_pure (hS : P.PureIn S) : ∀ (t : Tree) {args rets : List E},
    t.Valid P rd0 args rets → t.name ∈ S → ∀ q ∈ t.eqns P, rd0 q.1 = some q.2
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩, hn, q, hq => by
      have hpure : ∀ e ∈ es, e.pure S := by
        have := walk_pure (σ := σ) fn.body (hS f hn fn hf)
        rwa [hw] at this
      rw [eqns_node hf hw] at hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨e, he, hqe⟩ := List.mem_flatMap.mp hq
        match e, he, hqe with
        | .atom a, he, hqe => exact atomEqns_read_pure a (hpure _ he) (hes _ he) q hqe
      · exact eqnsKids_read_pure hS kids σ (calls es) hk (calls_pure hpure) q hq
  | .phantom .., _, _, h, _, _, _ => h.elim

/-- `eqns_read_pure` for the callees. -/
theorem eqnsKids_read_pure (hS : P.PureIn S) : ∀ (ks : List Tree) (σ : Val) (cs : List Call),
    Tree.KidsValid P rd0 σ cs ks → (∀ c ∈ cs, c.f ∈ S) → ∀ q ∈ Tree.eqnsKids P ks, rd0 q.1 = some q.2
  | [], _, _, _, _, q, hq => by simp [Tree.eqnsKids] at hq
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hS', q, hq => by
      rw [Tree.eqnsKids] at hq
      rcases List.mem_append.mp hq with hq | hq
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact eqns_read_pure hS k hc (hn ▸ hS' c List.mem_cons_self) q hq
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          simp [Tree.eqns] at hq
      · exact eqnsKids_read_pure hS ks σ cs hks (fun c' h => hS' c' (List.mem_cons_of_mem _ h)) q hq
  | _ :: _, _, [], h, _, _, _ => h.elim
end

/-- **A pure function's relation on a reader reading nothing outside `R`, uniformly**: one size,
placed anywhere, on every memory extending that reader. -/
theorem relAtIn_uniform_of_supp (fs : String → ℕ) (cert : String → V → ℕ) (hP : P.Wf)
    (hS : P.PureIn S) {g : String} (hg : g ∈ S) {R : ℕ → Prop}
    (hR : ∀ A v, rd0 A = some v → ∃ i, A = gpow i ∧ R i) {args rets : List E}
    (h : P.Rel rd0 g args rets) :
    ∃ n, ∀ fp (rd : Reader), (∀ A v, rd0 A = some v → rd A = some v) →
      RelAtIn P fs cert rd R (fun _ => False) fp n g args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.Rel.tree hP h
  refine ⟨t.total fs, fun fp rd hext => ?_⟩
  have hv' := hv.transfer t fun q hq => hext _ _ (eqns_read_pure hS t hv (hn ▸ hg) q hq)
  exact ⟨t, hn, hv', hb, placed_of_pure hS t hv hb (hn ▸ hg) fp, rfl,
    loadsIn_of_loadsR t R fp (loadsR_of_supp hR t hv), fun _ h => h.elim⟩

end Uniform

/-! ## Events -/

theorem mem_calls_taken {es : List Ev} {c : Call} (hc : c ∈ calls es) (ht : c.taken = true) :
    Ev.call c.f c.args c.rets ∈ es := by
  obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
  cases e with
  | call f args rets => simp only [Ev.call?, Option.some.injEq] at hce; subst hce; exact he
  | skip f args => simp only [Ev.call?, Option.some.injEq] at hce; subst hce; simp at ht
  | atom _ => simp [Ev.call?] at hce
  | inK _ => simp [Ev.call?] at hce

theorem allocs_append (σ : Val) (a b : List Ev) : allocs σ (a ++ b) = allocs σ a ++ allocs σ b :=
  List.filterMap_append
theorem allocDsts_append (a b : List Ev) : allocDsts (a ++ b) = allocDsts a ++ allocDsts b :=
  List.filterMap_append
theorem addrs_append (a b : List Ev) : addrs (a ++ b) = addrs a ++ addrs b := List.filterMap_append
theorem runs_append (a b : List Ev) : runs (a ++ b) = runs a ++ runs b := List.filterMap_append
theorem calls_append (a b : List Ev) : calls (a ++ b) = calls a ++ calls b := List.filterMap_append
theorem loadAddrs_append (σ : Val) (a b : List Ev) : loadAddrs σ (a ++ b) = loadAddrs σ a ++ loadAddrs σ b :=
  List.filterMap_append

end
end LeanVM.Guest.Memory
