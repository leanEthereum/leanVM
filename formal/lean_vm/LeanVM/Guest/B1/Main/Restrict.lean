/-
  LeanVM.Guest.B1.Main.Restrict

  A reader restricted to a region, and the loads of a tree valid on it: they read the region.
-/

module

public import LeanVM.Guest.Memory.Regions
public import LeanVM.Guest.B1.Main.Basic

/-!
# Restricted readers

`restrict rd S` reads `rd` at the addresses `g^i` with `S i` and nothing elsewhere. A tree valid on
a reader that reads nothing outside `R` loads from `R` only (`loadsR_of_supp`), so a relation
proved on the restriction of a memory to the regions a function's honest words lie in is a
relation loading from those regions (`relIn_of_rel_supp`), the pointer safety the honest memory
needs.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

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

/-! ## Layouts -/

/-- Buffers at `g^b` holding `xs`. -/
abbrev Layout : Type := List (ℕ × List E)

/-- The memory holds a layout. -/
def MemL (rd : Reader) (L : Layout) : Prop := ∀ q ∈ L, ReadsAt rd (ofK (gpow q.1)) q.2

/-- The addresses of a layout. -/
def RegionL (L : Layout) (i : ℕ) : Prop := ∃ q ∈ L, q.1 ≤ i ∧ i < q.1 + q.2.length

theorem addr_ofK (b k : ℕ) : (ofK (gpow b)).limb 0 * gpow k = gpow (b + k) := by
  rw [limb_ofK]; exact (pow_add _ _ _).symm

theorem memL_append {rd : Reader} {L L' : Layout} : MemL rd (L ++ L') ↔ MemL rd L ∧ MemL rd L' := by
  simp only [MemL, List.mem_append]
  exact ⟨fun h => ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩,
    fun h q hq => hq.elim (h.1 q) (h.2 q)⟩

theorem memL_nil {rd : Reader} : MemL rd [] ↔ True := by simp [MemL]

theorem memL_cons {rd : Reader} {q : ℕ × List E} {L : Layout} :
    MemL rd (q :: L) ↔ ReadsAt rd (ofK (gpow q.1)) q.2 ∧ MemL rd L := by
  simp only [MemL, List.mem_cons, forall_eq_or_imp]

/-- **A layout held survives restricting the memory to it.** -/
theorem memL_restrict {rd : Reader} {L : Layout} {S : ℕ → Prop} (h : MemL rd L)
    (hS : ∀ i, RegionL L i → S i) : MemL (restrict rd S) L := fun q hq k hk =>
  loadHolds_restrict (h q hq k hk) ⟨q.1 + k, addr_ofK _ _, hS _ ⟨q, hq, by omega, by omega⟩⟩

/-- **Two memories holding a layout agree on it.** -/
theorem memL_agree {rd rd' : Reader} {L : Layout} (h : MemL rd L) (h' : MemL rd' L) :
    ∀ i, RegionL L i → rd (gpow i) = rd' (gpow i) := by
  rintro i ⟨q, hq, h1, h2⟩
  have a := (h q hq (i - q.1) (by omega)).2
  have b := (h' q hq (i - q.1) (by omega)).2
  rw [addr_ofK, show q.1 + (i - q.1) = i by omega] at a b
  rw [a, b]

/-! ## Reading a layout's buffers -/

theorem readsAt_append' {rd : Reader} {p : E} {xs ys : List E} :
    ReadsAt rd p (xs ++ ys) ↔ ReadsAt rd p xs ∧ ReadsAt rd (p * gen ^ xs.length) ys := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := h k (by simp; omega)
      rwa [List.getElem_append_left hk] at this
    · have := h (xs.length + k) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simp only [Nat.add_sub_cancel_left] at this
      rw [loadHolds_mul_gen_pow]; exact this
  · rintro ⟨h1, h2⟩ k hk
    rcases Nat.lt_or_ge k xs.length with hk' | hk'
    · rw [List.getElem_append_left hk']; exact h1 k hk'
    · rw [List.getElem_append_right hk']
      have := h2 (k - xs.length) (by simp at hk; omega)
      rw [loadHolds_mul_gen_pow, show xs.length + (k - xs.length) = k by omega] at this
      exact this

theorem readsAt_flatMap_of {α : Type} {rd : Reader} {f : α → List E} {w : ℕ} :
    ∀ (l : List α) {p : E}, (∀ a ∈ l, (f a).length = w) → ReadsAt rd p (l.flatMap f) →
      ∀ c (hc : c < l.length), ReadsAt rd (p * gen ^ (w * c)) (f l[c])
  | [], _, _, _, c, hc => absurd hc (by simp)
  | a :: l, p, hw, h, c, hc => by
    rw [List.flatMap_cons, readsAt_append'] at h
    rcases c with _ | c
    · simpa using h.1
    · have := readsAt_flatMap_of l (fun b hb => hw b (List.mem_cons_of_mem _ hb)) h.2 c
        (by simpa using hc)
      rw [hw a List.mem_cons_self, mul_assoc, ← pow_add, show w + w * c = w * (c + 1) by ring]
        at this
      simpa using this

theorem readsAt_range_flatMap {rd : Reader} {p : E} {m w : ℕ} {f : ℕ → List E}
    (hw : ∀ c < m, (f c).length = w) (h : ReadsAt rd p ((List.range m).flatMap f)) :
    ∀ c < m, ∀ k < w, LoadHolds rd p (w * c + k) ((f c).getD k 0) := by
  intro c hc k hk
  have := readsAt_flatMap_of (List.range m) (fun a ha => hw a (List.mem_range.mp ha)) h c
    (by simpa using hc)
  simp only [List.getElem_range] at this
  rw [← loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ (by rw [hw c hc]; exact hk)]
  exact this k (by rw [hw c hc]; exact hk)

/-! ## Pure subtrees, uniformly -/

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

end
end LeanVM.Guest.B1.Main
