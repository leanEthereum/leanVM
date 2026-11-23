/-
  LeanVM.Guest.Count.VsOsLeaf

  The check of an arm's callee (`leafOkB`) gives its words bound on the arguments the arm passes it
  (`leafOkB_sound`).
-/

module

public import LeanVM.Guest.Count.VsOsDefs

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest LeanVM.Guest.Data LeanVM.Guest.B1.Whir

@[expose] public section

theorem alook_mem : ∀ {k e : ℕ} {l : List (ℕ × ℕ)}, alook k l = some e → (k, e) ∈ l
  | _, _, [], h => by simp [alook] at h
  | k, e, q :: l, h => by
      simp only [alook] at h
      split_ifs at h with hq
      · cases h; rw [← hq]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (alook_mem h)

/-- **A certificate's bound at an assignment** bounds the words of a tree on arguments `g^e` there. -/
theorem statAtB_sound {f : String} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : wcertOf f = .stat pre b ks) {asg : List (ℕ × ℕ)} {B : ℕ} (h : statAtB pre b asg B = true)
    {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (ha : ∀ q ∈ asg, args.getD q.1 0 = ofK (addressOfIndex q.2)) :
    t.total B2C.fs ≤ B := by
  simp only [statAtB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hord, hpre⟩, hcs⟩, hle⟩ := h
  have hexp : ∀ k e, alook k asg = some e → argExp args k = e := fun k e he => by
    have hm := alook_mem he
    rw [argExp, ha _ hm, logG_ofK (hord _ hm)]
  have hP : ArgsPre pre args := by
    intro q hq
    have hq' := hpre q hq
    cases he : alook q.1 asg with
    | none => rw [he] at hq'; cases hq'
    | some e =>
      rw [he] at hq'
      have hm := alook_mem he
      exact ⟨e, hq', hord _ hm, ha _ hm⟩
  have hmap : (b.cs.map fun q => q.2 * argExp args q.1) = b.cs.map fun q => q.2 * (alook q.1 asg).getD 0 :=
    List.map_congr_left fun q hq => by
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (hcs q hq)
      simp only [hexp _ _ he, he, Option.getD_some]
  have hev : b.eval args = affAt asg b := by rw [Aff.eval, affAt, hmap]
  exact (fs_total_le_of_stat hcf hn hv hb hP).trans (hev ▸ hle)

/-- **What an arm passes a callee is one of its assignments.** -/
theorem osAsgs_sound {m : ℕ} {f : String} {args : List E} (h : B1.osArgsOk m f args) :
    ∃ a ∈ osAsgs m f, ∀ q ∈ a, args.getD q.1 0 = ofK (addressOfIndex q.2) := by
  unfold B1.osArgsOk at h
  unfold osAsgs
  split_ifs at h ⊢
  · obtain ⟨r, hr, l, hl, hf, h9⟩ := h
    refine ⟨[(9, (osLvR m r l).squeezes)], List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
      List.mem_filterMap.mpr ⟨l, List.mem_range.mpr hl, ite_eq_left hf⟩⟩, ?_⟩
    simpa using h9
  · obtain ⟨r, hr, l, hl, hf, h4, h5⟩ := h
    refine ⟨_, List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
      List.mem_filterMap.mpr ⟨l, List.mem_range.mpr hl, ite_eq_left hf⟩⟩, ?_⟩
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact h4
    · exact h5
  · exact ⟨[], List.mem_singleton_self _, by simp⟩

/-- **An arm's checked callee within `wSBos`** on the arguments the arm passes it. -/
theorem leafOkB_sound {m : ℕ} {f : String} (h : leafOkB m f = true) :
    TotalLeOn coreProgram B2C.fs f (B1.osArgsOk m f) (fun _ => wSBos f) := by
  intro rd t args rets hn hpre hv hb
  simp only [leafOkB, Bool.and_eq_true] at h
  obtain ⟨hnm, hk⟩ := h
  have hc := wcertOf_of_idx (wNameB_spec hnm)
  obtain ⟨a, ha, hargs⟩ := osAsgs_sound hpre
  rcases hw : wcertJ (wIdx f) with _ | ⟨pre, b, ks⟩ | _
  · simp only [hw, Bool.false_eq_true] at hk
  · simp only [hw, List.all_eq_true] at hk
    exact statAtB_sound (hc.trans hw) (hk a ha) hn hv hb hargs
  · simp only [hw, Bool.false_eq_true] at hk

end
end LeanVM.Guest.Count
