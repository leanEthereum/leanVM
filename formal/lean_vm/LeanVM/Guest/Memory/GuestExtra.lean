/-
  LeanVM.Guest.Memory.GuestExtra

  The deployed guest's hint-only cells (`Bridge.extraOf`) are fresh, and each names one value:
  `ExtraFresh` and the value premise of `extra_read`, from a kernel check over the functions'
  data.
-/

module

public import LeanVM.Guest.Memory.DischargeE
public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.B2C.KFacts

/-!
# The guest's hint-only cells

`refExtra f` is function `f`'s hint-only cells, its alignment's (`Bridge.extraOf`). An instance's
frame cells (`B2C.C`) are its temporaries' and named values' certificate cells, its frame runs'
cells, its fixed cells, call sites' and table jumps' cells (`Bridge.plumbCells`), its chained
`match`es' targets and, in `main`, the jump table (`cells_static`). `extraOk j`, checked by the
kernel for every function (`extraOk_all`): a function with hint-only cells is not `main`, has no
frame run, its cells are distinct, past the header, in the frame, no certificate cell and none of
`plumbAll`, and each value its body names at such an index is the one of that index. So the cells
are fresh (`extraFresh_guest`) and name one value (`extraUses_guest`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B2C

@[expose] public section

/-- **The hint-only cells of each function**, its alignment's. -/
noncomputable def refExtra (f : String) : List (ℕ × ℕ) := Bridge.extraOf ((idxOf f).getD 0)

/-- An atom that is no frame run. -/
def noRun : Core.Atom → Bool
  | .frameAddr .. => false
  | _ => true

/-- The cells a frame of function `j` holds beyond its values': its plumbing and its chained
`match`es' targets. -/
noncomputable def plumbAll (j : ℕ) : List ℕ := Bridge.plumbCells (plumbOf j) ++ (plumbOf j).chains.flatMap (·.2.2.1)

/-- Hint-only cells `ex` of function `j` are fresh and name one value each: none, or `j` is not
`main`, has no frame run among `atoms`, its cells are distinct, past the header, in the frame of
`n` cells, none of `locs` or `plumb`, and each value of `uses` at such an index is the one of its
index. -/
def extraOkB (ex : List (ℕ × ℕ)) (j : ℕ) (locs plumb : List ℕ) (n : ℕ) (atoms : List Core.Atom)
    (uses : List V) : Bool :=
  ex.isEmpty || (!(j == 1) && atoms.all noRun && decide (ex.map (·.2)).Nodup &&
    ex.all (fun p ↦ Nat.ble 2 p.2 && Nat.blt p.2 n && !locs.contains p.2 && !plumb.contains p.2) &&
    uses.all fun v ↦ (ex.lookup v.idx).isNone || v == ⟨[], 0, v.idx⟩)

/-- Function `j`'s hint-only cells are fresh and name one value each. -/
noncomputable def extraOk (j : ℕ) : Bool :=
  extraOkB (Bridge.extraOf j) j (certOf j).locs (plumbAll j) (fsN j) (lAtoms (coreOf j).body)
    (Stmt.usesList (coreOf j).body)

/-- **Every function's hint-only cells are fresh.** -/
theorem extraOk_all : ∀ j < nFns, extraOk j = true := by decide +kernel

theorem extraOf_zero : Bridge.extraOf 0 = [] := by decide +kernel

/-- What `extraOkB` says of a function with hint-only cells. -/
structure ExtraSpec (ex : List (ℕ × ℕ)) (j : ℕ) (locs plumb : List ℕ) (n : ℕ) (atoms : List Core.Atom)
    (uses : List V) : Prop where
  main : j ≠ 1
  run : ∀ a ∈ atoms, noRun a = true
  nodup : (ex.map (·.2)).Nodup
  cell : ∀ p ∈ ex, 2 ≤ p.2 ∧ p.2 < n ∧ p.2 ∉ locs ∧ p.2 ∉ plumb
  uses : ∀ v ∈ uses, ∀ c, ex.lookup v.idx = some c → v = ⟨[], 0, v.idx⟩

theorem extraOkB_spec {ex : List (ℕ × ℕ)} {j : ℕ} {locs plumb : List ℕ} {n : ℕ} {atoms : List Core.Atom}
    {uses : List V} (h : extraOkB ex j locs plumb n atoms uses = true) (hne : ex ≠ []) :
    ExtraSpec ex j locs plumb n atoms uses := by
  unfold extraOkB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, decide_eq_true_eq, Nat.ble_eq, Nat.blt_eq, List.contains_eq_mem, decide_eq_false_iff_not,
    Option.isNone_iff_eq_none, beq_iff_eq] at h
  rcases h with h | ⟨⟨⟨⟨hj, hr⟩, hnd⟩, hc⟩, hu⟩
  · exact absurd h hne
  · refine ⟨hj, hr, hnd, fun p hp ↦ ?_, fun v hv c hc' ↦ ?_⟩
    · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc p hp
      exact ⟨h1, h2, h3, h4⟩
    · rcases hu v hv with h | h
      · rw [h] at hc'; cases hc'
      · exact h

theorem getD_mem {l : List ℕ} {i : ℕ} (h : 2 ≤ l.getD i 0) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD] at h ⊢
  cases hi : l[i]? with
  | none => rw [hi] at h; simp at h
  | some x => exact List.mem_of_getElem? hi

/-- **A frame's cells**, past the header, are certificate cells or its function's plumbing. -/
theorem cells_static {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {j : ℕ}
    (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) (hj1 : j ≠ 1)
    (hrun : ∀ a ∈ lAtoms (coreOf j).body, noRun a = true) {q : ℕ × E} (hq : q ∈ C I) :
    q.1 ∈ (certOf j).locs ∨ q.1 ∈ plumbAll j := by
  obtain ⟨-, -, -, -, -, -, -, hcert, -, -⟩ := fn_of_idx hj
  rw [C_node ht hj] at hq
  obtain ⟨hq, h2, -⟩ := mem_frameE hq
  have hval : ∀ vs, q ∈ valE f σ vs → q.1 ∈ (certOf j).locs := fun vs hv ↦ by
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hv
    simp only [hcert] at h2 ⊢
    exact getD_mem h2
  simp only [nodeE, List.mem_append] at hq
  rcases hq with ((((((hq | hq) | hq) | hq) | hq) | hq) | hq) | hq
  · exact Or.inl (hval _ hq)
  · exfalso
    obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp hq
    split at hq
    · rename_i p r rs
      obtain ⟨j', hj', ha⟩ := events_atom ht he
      rw [hj] at hj'
      cases hj'
      exact absurd (hrun _ ha) (by simp [noRun])
    · cases hq
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    exact Or.inr (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map_of_mem hx))))
  · exact Or.inl (hval _ hq)
  · obtain ⟨c, -, hq⟩ := List.mem_flatMap.mp hq
    split at hq
    · rename_i s hs
      have hsm := List.mem_of_find?_eq_some hs
      have hin : ∀ x ∈ [s.q, s.tgt], x ∈ plumbAll j := fun x hx ↦
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨s, hsm, hx⟩)))
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact Or.inr (hin _ (by simp))
      · split at hq
        · cases hq
        · simp only [List.mem_singleton] at hq
          subst hq
          exact Or.inr (hin _ (by simp))
    · cases hq
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact Or.inr (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem ha)))
  · obtain ⟨ch, hch, hq⟩ := List.mem_flatMap.mp hq
    unfold chainE at hq
    obtain ⟨x, hx, hxq⟩ := List.mem_filterMap.mp hq
    split at hxq
    · cases hxq
      have : x.1 ∈ ch.2.2.1 := by
        rw [← List.zipIdx_map_fst 0 ch.2.2.1]
        exact List.mem_map_of_mem hx
      exact Or.inr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ch, hch, this⟩))
    · cases hxq
  · simp [hj1] at hq

/-- **The deployed guest's hint-only cells are fresh.** -/
theorem extraFresh_guest (hdr : E × E) (T : Tree) : ExtraFresh coreProgram fs cert H C hdr T refExtra where
  cell I _ f σ bufs kids hIt p hp := by
    cases hj : idxOf f with
    | none => simp [refExtra, hj, extraOf_zero] at hp
    | some j =>
      have hp' : p ∈ Bridge.extraOf j := by simpa [refExtra, hj] using hp
      obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -, hlt⟩ := fn_of_idx hj
      have S := extraOkB_spec (extraOk_all _ hlt) (List.ne_nil_of_mem hp')
      obtain ⟨h2, hn, hloc, hpl⟩ := S.cell p hp'
      refine ⟨h2, by rw [hfs]; exact hn, fun q hq he ↦ ?_, fun t _ he ↦ ?_⟩
      · rcases cells_static hIt hj S.main S.run hq with h | h
        · exact hloc (he ▸ h)
        · exact hpl (he ▸ h)
      · rw [hcert] at he
        exact hloc (he ▸ getD_mem (he ▸ h2))
  inj f p hp p' hp' he := by
    cases hj : idxOf f with
    | none => simp [refExtra, hj, extraOf_zero] at hp
    | some j =>
      have hpj : p ∈ Bridge.extraOf j := by simpa [refExtra, hj] using hp
      have hpj' : p' ∈ Bridge.extraOf j := by simpa [refExtra, hj] using hp'
      obtain ⟨-, -, -, -, -, -, -, -, -, hlt⟩ := fn_of_idx hj
      have S := extraOkB_spec (extraOk_all _ hlt) (List.ne_nil_of_mem hpj)
      exact List.inj_on_of_nodup_map S.nodup hpj hpj' he

/-- A value an instance's path names is one of its function's body. -/
theorem uses_events {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {v : V}
    (hv : v ∈ ((Tree.node f σ bufs kids).events coreProgram).flatMap Ev.uses) :
    ∃ j, idxOf f = some j ∧ v ∈ Stmt.usesList (coreOf j).body := by
  obtain ⟨e, he, hve⟩ := List.mem_flatMap.mp hv
  unfold Tree.events at he
  simp only [Tree.name, Tree.val] at he
  cases hj : idxOf f with
  | none =>
    rw [find?_none (by unfold idxOf at hj; exact Option.map_eq_none_iff.mp hj)] at he
    cases he
  | some j =>
    obtain ⟨i, rfl, hi, -, hf, hc, -⟩ := fn_of_idx hj
    rw [hf] at he
    simp only at he
    have hw := walk_within (σ := σ) coreProgram[i].body
    split at he
    · rename_i es vs hwe
      rw [hwe] at hw
      exact ⟨_, rfl, by rw [hc]; exact hw.1 e he v hve⟩
    · cases he

/-- **Each value a path names at a hint-only index is the one of that index.** -/
theorem extraUses_guest : ∀ f σ bufs kids, ∀ v ∈ ((Tree.node f σ bufs kids).events coreProgram).flatMap Ev.uses,
    ∀ c, (refExtra f).lookup v.idx = some c → v = ⟨[], 0, v.idx⟩ := by
  intro f σ bufs kids v hv c hc
  obtain ⟨j, hj, hu⟩ := uses_events hv
  have hc' : (Bridge.extraOf j).lookup v.idx = some c := by simpa [refExtra, hj] using hc
  obtain ⟨-, -, -, -, -, -, -, -, -, hlt⟩ := fn_of_idx hj
  have hne : Bridge.extraOf j ≠ [] := fun h ↦ by rw [h] at hc'; cases hc'
  exact (extraOkB_spec (extraOk_all _ hlt) hne).uses v hu c hc'

end

end LeanVM.Guest.Memory
