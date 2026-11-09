/-
  LeanVM.Guest.B2C.KFacts

  The temporaries' and the frame runs' cells in `C` (`End.KFactsAll`'s `cert_lt`, `cert_inj`,
  `tmp`, `run`), from the sharing check's lists, and the checker's facts assembled (`kFactsAll`).
-/

module

public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.B2C.KRetemp
public import LeanVM.Guest.B2C.ArmsFresh
public import LeanVM.Guest.B2C.RunsFit
public import LeanVM.Guest.B2C.Shared
public import LeanVM.Guest.Sound
public import LeanVM.Guest.EndComplete

/-!
# Frame runs in the cells

The sharing check confirms, per atom and window, that every range check's temporaries and every
frame run's values are listed with their cells (`Plumb.tmps`, `Plumb.runs`), and once per function
that the lists hold one value per cell, in the frame, the runs' cells no temporary's
(`FnStatic`, `fnStatic`). So the temporaries' cells lie in the frame past the header
(`kfacts_cert_lt`) and are distinct (`kfacts_cert_inj`), and since a frame's candidates start with
its temporaries' and `dedupC` keeps the first at each cell, a temporary's cell holds only it
(`kfacts_tmp`). A frame run's cell holds its value in `C I`: it is the first candidate at its
cell, no temporary's being there and the runs' candidates agreeing (`run_kfact`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

section Static

theorem shareOk_of {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) : ShareOk j := Shared.all j h1 h2

end Static

/-! ## The temporaries' cells -/

section Temps

private theorem temps_none {f : String} (h : idxOf f = none) : coreProgram.temps f = [] := by
  unfold idxOf at h
  rw [Option.map_eq_none_iff] at h
  rw [Program.temps, find?_none h]

private theorem temps_some {f : String} {j : ℕ} (h : idxOf f = some j) :
    ∃ i, j = i + 1 ∧ i < coreProgram.length ∧ coreProgram.temps f = Stmt.tmpsList (coreOf j).body ∧
      fs f = fsN j ∧ ∀ v, cert f v = (certOf j).locs.getD v.idx 0 := by
  obtain ⟨i, rfl, hi, -, hfind, hcore, hfs, hcert, -, -⟩ := fn_of_idx h
  exact ⟨i, rfl, hi, by rw [Program.temps, hfind, hcore], hfs, hcert⟩

/-- **The temporaries' cells lie in the frame past the header** (`FnStatic.tmp`, `tmpsIn`). -/
theorem kfacts_cert_lt : ∀ f, ∀ t ∈ coreProgram.temps f, 2 ≤ cert f t ∧ cert f t < fs f := by
  intro f t ht
  cases hj : idxOf f with
  | none => rw [temps_none hj] at ht; cases ht
  | some j =>
    obtain ⟨i, rfl, hi, htm, hfs, hcert⟩ := temps_some hj
    rw [htm] at ht
    have FS := fnStatic_of hj
    obtain ⟨-, hmem⟩ := FS.tmp t ht
    have := FS.tmpsIn _ hmem
    rw [hcert, hfs]
    exact this

/-- **Distinct temporaries have distinct cells** (`FnStatic.tmp`, `tmpsFun`). -/
theorem kfacts_cert_inj : ∀ f, ∀ t ∈ coreProgram.temps f, ∀ t' ∈ coreProgram.temps f,
    cert f t = cert f t' → t = t' := by
  intro f t ht t' ht' he
  cases hj : idxOf f with
  | none => rw [temps_none hj] at ht; cases ht
  | some j =>
    obtain ⟨i, rfl, hi, htm, -, hcert⟩ := temps_some hj
    rw [htm] at ht ht'
    have FS := fnStatic_of hj
    obtain ⟨h1, hm⟩ := FS.tmp t ht
    obtain ⟨h1', hm'⟩ := FS.tmp t' ht'
    rw [hcert, hcert] at he
    have hidx := FS.tmpsFun _ hm _ hm' he
    simp only at hidx
    rw [h1, h1', hidx]

/-- **A temporary's cell holds only it**, in every instance of a re-chosen tree. -/
theorem kfacts_tmp (hdr : E × E) (T : Tree) :
    ∀ ν, ∀ I' ∈ honestInsts coreProgram fs H hdr (T.retemp coreProgram fs ν 0), ∀ f σ bufs kids,
      I'.t = .node f σ bufs kids → ∀ t ∈ coreProgram.temps f, ∀ q ∈ C I', q.1 = cert f t →
        q.2 = σ t := by
  intro ν I' _ f σ bufs kids ht t htm q hq hqt
  cases hj : idxOf f with
  | none => rw [temps_none hj] at htm; cases htm
  | some j =>
    rw [C_node ht hj, nodeE_split, frameE_append] at hq
    have hlt := kfacts_cert_lt f t htm
    have hmem := dedupC_first hq ⟨(cert f t, σ t), List.mem_filter.mpr
      ⟨List.mem_map_of_mem (f := fun v => (cert f v, σ v)) htm, by
        simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact hlt⟩, hqt.symm⟩
    obtain ⟨hq1, -⟩ := List.mem_filter.mp hmem
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hq1
    obtain rfl := kfacts_cert_inj f t' ht' t htm hqt
    rfl

end Temps


/-! ## Frame runs in the cells -/

section Run

theorem nodeE_tmpsRuns (j : ℕ) (f : String) (σ : Val) (I : Inst) :
    ∃ R, nodeE j f σ I = (valE f σ (coreProgram.temps f) ++ runsE f σ (I.t.events coreProgram)) ++ R :=
  ⟨_, by simp only [nodeE, List.append_assoc]; rfl⟩

/-- An atom of a node's path is an atom of its function's body. -/
theorem events_atom {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) {a : Core.Atom} (ha : Ev.atom a ∈ I.t.events coreProgram) :
    ∃ j, idxOf f = some j ∧ a ∈ lAtoms (coreOf j).body := by
  rw [ht] at ha
  unfold Tree.events at ha
  simp only [Tree.name, Tree.val] at ha
  cases hj : idxOf f with
  | none =>
    have : coreProgram.indexOf? f = none := by
      unfold idxOf at hj; exact Option.map_eq_none_iff.mp hj
    rw [find?_none this] at ha; cases ha
  | some j =>
    obtain ⟨i, rfl, hi, -, hf, hc, -⟩ := fn_of_idx hj
    rw [hf] at ha
    simp only at ha
    cases hw : walk σ coreProgram[i].body with
    | ret es vs =>
      rw [hw] at ha
      refine ⟨_, rfl, ?_⟩
      rw [hc]
      exact walk_atoms _ (by rw [hw]; exact ha)
    | fall es => rw [hw] at ha; cases ha
    | stuck => rw [hw] at ha; cases ha

/-- **A frame run's cells hold its values**, at no temporary's cell. -/
theorem run_kfact {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) {p r : V} {rs : List V}
    (he : Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events coreProgram) (k : ℕ) (hk : k < (r :: rs).length) :
    (cert f r + k, σ (r :: rs)[k]) ∈ C I ∧ ∀ t ∈ coreProgram.temps f, cert f r + k ≠ cert f t := by
  obtain ⟨j, hj, ha⟩ := events_atom ht he
  obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
  have hcJ : ∀ v, cert f v = cellJ (i + 1) v := fun v ↦ hcert v
  have FS := fnStatic_of hj
  obtain ⟨-, -, hrun⟩ := FS.run p r rs ha k hk
  rw [← hcJ] at hrun
  have hnt : ∀ t ∈ coreProgram.temps f, cert f r + k ≠ cert f t := fun t ht' he' ↦ by
    obtain ⟨j', hj', htl⟩ := temps_of ht'
    rw [hj] at hj'; cases hj'
    obtain ⟨-, hl⟩ := FS.tmp t htl
    rw [← hcJ] at hl
    exact FS.runsTmp _ hrun _ hl (by rw [← he'])
  refine ⟨?_, hnt⟩
  have hin := FS.runsIn _ hrun
  obtain ⟨R, hR⟩ := nodeE_tmpsRuns (i + 1) f σ I
  rw [C_node ht hj, hR, frameE_append]
  refine dedupC_mem ?_ fun x hx hxe ↦ ?_
  · simp only [List.mem_filter, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
    refine ⟨List.mem_append_right _ ?_, hin.1, by rw [hfs]; exact hin.2⟩
    simp only [runsE, List.mem_flatMap]
    exact ⟨_, he, List.mem_mapIdx.mpr ⟨k, hk, rfl⟩⟩
  · simp only [List.mem_filter, List.mem_append] at hx
    rcases hx.1 with hx | hx
    · simp only [valE, List.mem_map] at hx
      obtain ⟨t, ht', rfl⟩ := hx
      exact absurd hxe.symm (hnt t ht')
    · obtain ⟨p', r', rs', he', k', hk', rfl⟩ := mem_runsE hx
      obtain ⟨j', hj', ha'⟩ := events_atom ht he'
      rw [hj] at hj'; cases hj'
      obtain ⟨hv', -, hrun'⟩ := FS.run p' r' rs' ha' k' hk'
      obtain ⟨hv, -, -⟩ := FS.run p r rs ha k hk
      rw [← hcJ] at hrun'
      simp only at hxe
      rw [hxe] at hrun'
      have := FS.runsFun _ hrun' _ hrun rfl
      simp only at this
      rw [hv', hv, this, hxe]

/-- **`KFacts.run`** for every tree. -/
theorem kfacts_run (hdr : E × E) (T : Tree) :
    ∀ I ∈ honestInsts coreProgram fs H hdr T, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
      ∀ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events coreProgram →
        ∀ (k : ℕ) (hk : k < (r :: rs).length), (cert f r + k, σ (r :: rs)[k]) ∈ C I ∧
          ∀ t ∈ coreProgram.temps f, cert f r + k ≠ cert f t :=
  fun _ _ _ _ _ _ ht _ _ _ he k hk ↦ run_kfact ht he k hk

end Run

/-- **The checker's facts for every tree of `main`.** -/
theorem kFactsAll : End.KFactsAll fs H C cert := fun hdr T _ ↦
  ⟨cellsOk_C _, fun _ ↦ cellsOk_C _, kfacts_cert_lt, kfacts_cert_inj, kfacts_run hdr T, kfacts_tmp hdr T,
    kfacts_keep_all hdr T⟩

end
end LeanVM.Guest.B2C
