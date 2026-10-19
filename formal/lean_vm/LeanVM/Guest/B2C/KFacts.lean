/-
  LeanVM.Guest.B2C.KFacts

  The frame runs' cells in `C` (`End.KFactsAll`'s `run`), from the sharing check's lists.
-/

module

public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.B2C.KRetemp
public import LeanVM.Guest.B2C.ShareSound
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

/-! ## The certificate's lists -/

section Lists

theorem listed_spec {l : List (ℕ × ℕ)} {v : V} {c : ℕ} (h : listed l v c = true) :
    v = V.n v.idx ∧ (v.idx, c) ∈ l := by
  simp only [listed, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, nbeq_iff] at h
  obtain ⟨h1, p, hp, h2, h3⟩ := h
  refine ⟨h1, ?_⟩
  rw [← h2, ← h3]; exact hp

theorem runListed_spec {loc : Loc} {l : List (ℕ × ℕ)} {base : ℕ} :
    ∀ (k : ℕ) (vs : List V), runListed loc l base k vs = true →
      ∀ (m : ℕ) (hm : m < vs.length), loc.cell vs[m] = base + k + m ∧
        listed l vs[m] (base + k + m) = true
  | _, [], _, _, hm => absurd hm (by simp)
  | k, v :: vs, h, m, hm => by
    simp only [runListed, Bool.and_eq_true, nbeq_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases m with
    | zero => exact ⟨by simpa using h1, by simpa using h2⟩
    | succ m =>
      obtain ⟨e1, e2⟩ := runListed_spec (k + 1) vs h3 m (by simpa using hm)
      exact ⟨by simp only [List.getElem_cons_succ]; rw [e1]; omega,
        by simp only [List.getElem_cons_succ]; rw [show base + k + (m + 1) = base + (k + 1) + m by omega];
          exact e2⟩

theorem getF_byCell : ∀ (l : List (ℕ × ℕ)) (t : Exec.Trie ℕ) {c v : ℕ},
    getF (l.foldl (fun t p ↦ setF p.1 envDepth t p.2) t) c = some v → (∃ p ∈ l, p.2 = c ∧ p.1 = v) ∨
      getF t c = some v
  | [], _, _, _, h => Or.inr h
  | p :: l, t, c, v, h => by
    rcases getF_byCell l _ h with ⟨q, hq, h1, h2⟩ | h
    · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩
    · rcases getF_setF h with ⟨rfl, rfl⟩ | h
      · exact Or.inl ⟨p, List.mem_cons_self, rfl, rfl⟩
      · exact Or.inr h

theorem listedT_spec {l : List (ℕ × ℕ)} {v : V} {c : ℕ} (h : listedT (byCell l) v c = true) :
    v = V.n v.idx ∧ (v.idx, c) ∈ l := by
  simp only [listedT, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  rcases getF_byCell l .nil h.2 with ⟨p, hp, h1, h2⟩ | h'
  · rw [← h1, ← h2]; exact hp
  · simp [getF_eq] at h'

theorem pairsOk_spec {l : List (ℕ × ℕ)} {n : ℕ} (h : pairsOk l n = true) :
    (∀ p ∈ l, 2 ≤ p.2 ∧ p.2 < n) ∧ ∀ p ∈ l, ∀ q ∈ l, p.2 = q.2 → p.1 = q.1 := by
  simp only [pairsOk, Exec.Trie.seq_eq, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq,
    Nat.blt_eq] at h
  refine ⟨fun p hp ↦ (h p hp).2, fun p hp q hq he ↦ ?_⟩
  have h1 := (h p hp).1.1
  have h2 := (h q hq).1.1
  rw [he, h2] at h1
  exact (Option.some.inj h1).symm

end Lists

/-! ## A body by windows -/

section Windows

theorem lAtoms_append : ∀ (a b : List Stmt), lAtoms (a ++ b) = lAtoms a ++ lAtoms b
  | [], b => by simp [lAtoms]
  | s :: a, b => by simp only [List.cons_append, lAtoms, lAtoms_append a b, List.append_assoc]

mutual
/-- An atom's values are its statement's. -/
theorem uses_of_sAtoms : ∀ (s : Stmt) {a : Core.Atom}, a ∈ sAtoms s → ∀ v ∈ atomUses a, v ∈ Stmt.uses s
  | .atom a', a, h, v, hv => by
      simp only [sAtoms, List.mem_singleton] at h; subst h; exact hv
  | .ite c z n, a, h, v, hv => by
      simp only [sAtoms, List.mem_append] at h
      simp only [Stmt.uses, List.mem_cons, List.mem_append]
      rcases h with h | h
      · exact Or.inr (Or.inl (uses_of_lAtoms z h v hv))
      · exact Or.inr (Or.inr (uses_of_lAtoms n h v hv))
  | .match_ x arms, a, h, v, hv => by
      simp only [sAtoms] at h
      simp only [Stmt.uses, List.mem_cons]
      exact Or.inr (uses_of_aAtoms arms h v hv)
  | .call .., _, h, _, _ => by simp [sAtoms] at h
  | .callIf .., _, h, _, _ => by simp [sAtoms] at h
  | .dispatch .., _, h, _, _ => by simp [sAtoms] at h
  | .ret _, _, h, _, _ => by simp [sAtoms] at h

theorem uses_of_lAtoms : ∀ (ss : List Stmt) {a : Core.Atom}, a ∈ lAtoms ss → ∀ v ∈ atomUses a,
    v ∈ Stmt.usesList ss
  | [], _, h, _, _ => by simp [lAtoms] at h
  | s :: ss, a, h, v, hv => by
      simp only [lAtoms, List.mem_append] at h
      simp only [Stmt.usesList, List.mem_append]
      rcases h with h | h
      · exact Or.inl (uses_of_sAtoms s h v hv)
      · exact Or.inr (uses_of_lAtoms ss h v hv)

theorem uses_of_aAtoms : ∀ (arms : List (List Stmt)) {a : Core.Atom}, a ∈ aAtoms arms → ∀ v ∈ atomUses a,
    v ∈ Stmt.usesArms arms
  | [], _, h, _, _ => by simp [aAtoms] at h
  | b :: as, a, h, v, hv => by
      simp only [aAtoms, List.mem_append] at h
      simp only [Stmt.usesArms, List.mem_append]
      rcases h with h | h
      · exact Or.inl (uses_of_lAtoms b h v hv)
      · exact Or.inr (uses_of_aAtoms as h v hv)
end

variable {j : ℕ}

/-- **What a body's statements name, some window's do.** -/
theorem mem_windows {α : Type} (g : List Stmt → List α) (hg : ∀ a b, g (a ++ b) = g a ++ g b)
    (hS : ShareOk j) {x : α} : ∀ k i, i + k = (snapsOf j).length →
      x ∈ g (fromW (coreOf j).body (snapsOf j) i) → ∃ i', i' ≤ (snapsOf j).length ∧
        x ∈ g (stmtsW (coreOf j).body (snapsOf j) i') := by
  obtain ⟨-, h0, -, -⟩ := shareWin_spec (hS 0 (Nat.zero_le _))
  obtain ⟨-, -, hmono, -, -⟩ := h0 rfl
  intro k
  induction k with
  | zero =>
    intro i hi hx
    rw [fromW_last (by omega)] at hx
    exact ⟨i, by omega, hx⟩
  | succ k ih =>
    intro i hi hx
    have hiN : i < (snapsOf j).length := by omega
    rw [fromW_split hiN (snapsOk_spec hmono hiN).1, hg, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ⟨i, hiN.le, hx⟩
    · exact ih (i + 1) (by omega) hx

theorem fromW_zero (body : List Stmt) (snaps : List Snap) : fromW body snaps 0 = body := by
  simp only [fromW, startW, beq_self_eq_true, Bool.cond_true, List.drop_zero]

end Windows

/-! ## What the check gives statically -/

section Static

/-- **What the sharing check gives statically** of function `j`: its temporaries and runs as
listed, the lists one value per cell in the frame, runs apart from temporaries. -/
structure FnStatic (j : ℕ) : Prop where
  tmp : ∀ t ∈ Stmt.tmpsList (coreOf j).body, t = V.n t.idx ∧ (t.idx, cellJ j t) ∈ (plumbOf j).tmps
  tmpsIn : ∀ p ∈ (plumbOf j).tmps, 2 ≤ p.2 ∧ p.2 < fsN j
  tmpsFun : ∀ p ∈ (plumbOf j).tmps, ∀ q ∈ (plumbOf j).tmps, p.2 = q.2 → p.1 = q.1
  run : ∀ p r rs, Atom.frameAddr p (r :: rs) ∈ lAtoms (coreOf j).body → ∀ (k : ℕ)
    (hk : k < (r :: rs).length), (r :: rs)[k] = V.n (r :: rs)[k].idx ∧
      cellJ j (r :: rs)[k] = cellJ j r + k ∧ ((r :: rs)[k].idx, cellJ j r + k) ∈ (plumbOf j).runs
  runsIn : ∀ p ∈ (plumbOf j).runs, 2 ≤ p.2 ∧ p.2 < fsN j
  runsFun : ∀ p ∈ (plumbOf j).runs, ∀ q ∈ (plumbOf j).runs, p.2 = q.2 → p.1 = q.1
  runsTmp : ∀ p ∈ (plumbOf j).runs, ∀ q ∈ (plumbOf j).tmps, q.2 ≠ p.2

theorem fnStatic {j : ℕ} {G : Glob} {f : CompiledFn} {main : Bool} (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G f (coreOf j) (certOf j) main i = true) : FnStatic j := by
  have hcont := cont_of hchk
  obtain ⟨-, h0, -, -⟩ := shareWin_spec (hS 0 (Nat.zero_le _))
  obtain ⟨-, hlists, hsn, -, -⟩ := h0 rfl
  have hA : ∀ i ≤ (snapsOf j).length, ∀ v c, (locW (certOf j) (winW (snapsOf j) i)).get? v.idx = some c →
      cellJ j v = c := fun i hi v c h ↦
    locW_get hcont (winW_le hsn hi) (checkWin_parts (hchk _ (winW_le hsn hi))).2 rfl (shareWin_spec (hS i hi)).1 h
  simp only [listsOk, Exec.Trie.seq_eq, natSeq_eq, Bool.and_eq_true, List.all_eq_true] at hlists
  obtain ⟨⟨⟨⟨⟨-, ht⟩, hr⟩, hrt⟩, -⟩, -⟩ := hlists
  obtain ⟨htIn, htFun⟩ := pairsOk_spec ht
  obtain ⟨hrIn, hrFun⟩ := pairsOk_spec hr
  -- a window's facts on its atoms
  have hwin : ∀ i ≤ (snapsOf j).length, (∀ a ∈ lAtoms (stmtsW (coreOf j).body (snapsOf j) i),
      atomListed (locW (certOf j) (winW (snapsOf j) i)) (byCell (plumbOf j).tmps) (plumbOf j) a = true) ∧
      FitV (locW (certOf j) (winW (snapsOf j) i)) (cellJ j) (Stmt.usesList (stmtsW (coreOf j).body (snapsOf j) i) ++
        Stmt.tmpsList (stmtsW (coreOf j).body (snapsOf j) i)) := fun i hi ↦ by
    obtain ⟨-, -, hval, m, hsw, -⟩ := shareWin_spec (hS i hi)
    exact ⟨swL_listed _ hsw, fitV_of (hA i hi) hval⟩
  refine ⟨fun t htm ↦ ?_, htIn, htFun, fun p r rs ha k hk ↦ ?_, hrIn, hrFun, fun p hp q hq he ↦ ?_⟩
  · obtain ⟨i, hi, htm⟩ := mem_windows Stmt.tmpsList tmpsList_append hS _ 0 (Nat.zero_add _)
      (by rw [fromW_zero]; exact htm)
    obtain ⟨hl, hfit⟩ := hwin i hi
    obtain ⟨a, ha, hta⟩ := tmpsList_atoms _ htm
    have hc := (hfit t (List.mem_append_right _ htm)).2
    have hla := hl a ha
    cases a with
    | rangeCheck x y t1 t2 k =>
      simp only [atomTmps, List.mem_cons, List.not_mem_nil, or_false] at hta
      simp only [atomListed, Bool.and_eq_true] at hla
      rcases hta with rfl | rfl
      · have := listedT_spec hla.1; rw [hc] at this; exact this
      · have := listedT_spec hla.2; rw [hc] at this; exact this
    | _ => simp [atomTmps] at hta
  · obtain ⟨i, hi, ha⟩ := mem_windows lAtoms lAtoms_append hS _ 0 (Nat.zero_add _)
      (by rw [fromW_zero]; exact ha)
    obtain ⟨hl, hfit⟩ := hwin i hi
    have hla := hl _ ha
    simp only [atomListed] at hla
    obtain ⟨e1, e2⟩ := runListed_spec 0 (r :: rs) hla k hk
    obtain ⟨e3, e4⟩ := listed_spec e2
    have hu : ∀ v ∈ r :: rs, (locW (certOf j) (winW (snapsOf j) i)).cell v = cellJ j v := fun v hv ↦
      (hfit v (List.mem_append_left _ (uses_of_lAtoms _ ha v (List.mem_cons_of_mem _ hv)))).2
    rw [hu _ (List.getElem_mem hk), hu r List.mem_cons_self, Nat.add_zero] at e1
    rw [hu r List.mem_cons_self, Nat.add_zero] at e4
    exact ⟨e3, e1, e4⟩
  · have := hrt p hp
    simp only [Bool.not_eq_true', bitN_eq, tmpCells] at this
    have hin : (bitsOf ((plumbOf j).tmps.map Prod.snd)).testBit p.2 = true :=
      (testBit_bitsOf _ _).mpr (List.mem_map.mpr ⟨q, hq, he⟩)
    rw [this] at hin; cases hin

theorem shareOk_of {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) : ShareOk j := Shared.all j h1 h2

theorem fnStatic_of {f : String} {j : ℕ} (hj : idxOf f = some j) : FnStatic j := by
  obtain ⟨i, rfl, -, -, -, -, -, -, h1, h2⟩ := fn_of_idx hj
  exact fnStatic (shareOk_of h1 h2) (End.winOk_of h1 h2)

theorem temps_of {f : String} {t : V} (ht : t ∈ coreProgram.temps f) :
    ∃ j, idxOf f = some j ∧ t ∈ Stmt.tmpsList (coreOf j).body := by
  unfold Program.temps at ht
  cases hj : idxOf f with
  | none =>
    have : coreProgram.indexOf? f = none := by
      unfold idxOf at hj; exact Option.map_eq_none_iff.mp hj
    rw [find?_none this] at ht; cases ht
  | some j =>
    obtain ⟨i, rfl, hi, -, hf, hc, -⟩ := fn_of_idx hj
    rw [hf] at ht
    exact ⟨i + 1, rfl, by rw [hc]; exact ht⟩

end Static

/-! ## Frame runs in the cells -/

section Run

theorem nodeE_tmpsRuns (j : ℕ) (f : String) (σ : Val) (I : Inst) :
    ∃ R, nodeE j f σ I = (valE f σ (coreProgram.temps f) ++ runsE f σ (I.t.events coreProgram)) ++ R :=
  ⟨_, by simp only [nodeE, List.append_assoc]⟩

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

theorem mem_runsE {f : String} {σ : Val} {es : List Ev} {x : ℕ × E} (h : x ∈ runsE f σ es) :
    ∃ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ es ∧ ∃ k, ∃ hk : k < (r :: rs).length,
      x = (cert f r + k, σ (r :: rs)[k]) := by
  simp only [runsE, List.mem_flatMap] at h
  obtain ⟨e, he, hx⟩ := h
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨p, _ | ⟨r, rs⟩⟩ | _⟩ | _ | _ | _ <;>
    simp only [List.not_mem_nil] at hx
  obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hx
  exact ⟨p, r, rs, he, k, hk, rfl⟩

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

end Run

end
end LeanVM.Guest.B2C
