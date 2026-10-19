/-
  LeanVM.Guest.B2C.KFacts

  The frame runs' cells in `C` (`End.KFactsAll`'s `run`), from the sharing check's lists, and
  checker K's facts assembled (`kFactsAll`).
-/

module

public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.B2C.KRetemp
public import LeanVM.Guest.B2C.ArmsFresh
public import LeanVM.Guest.B2C.KTemps
public import LeanVM.Guest.B2C.Static
public import LeanVM.Guest.B2C.Shared
public import LeanVM.Guest.Sound

/-!
# Frame runs in the cells

The sharing check confirms, per atom and window, that every range check's temporaries and every
frame run's values are listed with their cells (`Plumb.tmps`, `Plumb.runs`), and once per function
that the lists hold one value per cell, in the frame, the runs' cells no temporary's
(`FnStatic`, `fnStatic`). So a frame run's cell holds its value in `C I`: it is the first candidate
at its cell, no temporary's being there and the runs' candidates agreeing (`run_kfact`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

section Static

theorem shareOk_of {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) : ShareOk j := Shared.all j h1 h2

theorem fnStatic_of {f : String} {j : ℕ} (hj : idxOf f = some j) : FnStatic j := by
  obtain ⟨i, rfl, -, -, -, -, -, -, h1, h2⟩ := fn_of_idx hj
  exact fnStatic (shareOk_of h1 h2) (End.winOk_of h1 h2)

end Static


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

/-- **Checker K's facts for every tree of `main`.** -/
theorem kFactsAll : End.KFactsAll fs H C cert := fun hdr T _ ↦
  ⟨cellsOk_C _, fun _ ↦ cellsOk_C _, kfacts_cert_lt, kfacts_cert_inj, kfacts_run hdr T, kfacts_tmp hdr T,
    kfacts_keep_all hdr T⟩

end
end LeanVM.Guest.B2C
