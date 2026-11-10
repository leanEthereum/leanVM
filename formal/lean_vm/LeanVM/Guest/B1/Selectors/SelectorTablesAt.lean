/-
  LeanVM.Guest.B1.Selectors.SelectorTablesAt

  `selector_tables` is complete in the uniform placed form (`CompleteAtD`): its buffer at the bump
  allocator's position, returned.
-/

module

public import LeanVM.Guest.B1.Selectors.SelectorTablesComplete
public import LeanVM.Guest.B1.Tables.FlatAtT

/-!
# `selector_tables`, placed (TRIAGE G #69)

At frame pointer `fp` the buffer lies at `ese = fp + fs "selector_tables"` (`512` words); the
function returns its pointer, and its returned layout is `stOwn` there (`stOut`).
`selector_tables_completeAt`: `CompleteAtD` on the point's runs `stLin`, by `completeAt_flatOutD`
on the honest valuation `stVal` (`st_sholds`), every load in the point's runs or the buffer;
`selector_tables_completeAtB` the same within its frame and buffer (`CompleteAtDTB`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- What `selector_tables` returns: its buffer's pointer, and the buffer holding `stOwn`. -/
def stOut (ept ept1 : ℕ) (p p1 : List E) : List E → Layout → Prop := fun rets L =>
  ∃ ese : ℕ, rets = [ofK (addressOfIndex ese)] ∧ L = stOwn ept ept1 ese p p1

theorem st_flat : stPre.all Stmt.flat = true := by decide +kernel

theorem st_addrs : stPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem st_allocs : stPre.filterMap Main.Stmt.allocSz = [(.n 2, .inl 512)] := by
  decide +kernel

theorem st_not_loop : coreProgram.loop "selector_tables" = false := by decide +kernel

set_option maxRecDepth 10000 in
/-- **`selector_tables` is complete, placed**: on the point's runs, at every frame pointer, its
buffer at the bump allocator's position, returned. -/
theorem selector_tables_completeAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (ept ept1 : ℕ) (p p1 : List E) (hl : p.length = 32) (hl1 : p1.length = 32) :
    CompleteAtD fs cert k "selector_tables" (stLin ept ept1 p p1) [ofK (addressOfIndex ept), ofK
        (addressOfIndex ept1)]
      (stOut ept ept1 p p1) := by
  obtain ⟨fn, hf, hp, hb⟩ := stFound
  set f := "selector_tables"
  have hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s)
      [stEqWords (stVal ept ept1 (fp + fs f) p p1)] [512] := by
    intro fp; simp [stEqWords]
  have hbuf : ∀ fp, bufL (fp + fs f) [512] [stEqWords (stVal ept ept1 (fp + fs f) p p1)] =
      stOwn ept ept1 (fp + fs f) p p1 := by
    intro fp; simp [bufL, bases, stOwn]
  refine completeAt_flatOutD (fs := fs) (cert := cert) hf st_not_loop k (stLin ept ept1 p p1) _
    (fun fp ↦ [ofK (addressOfIndex (fp + fs f))]) _ hb st_flat st_addrs
    [512] (fun fp ↦ [stEqWords (stVal ept ept1 (fp + fs f) p p1)])
    hown (fun fp ↦ ⟨_, rfl, hbuf fp⟩) (fun _ ↦ []) (fun _ _ h ↦ absurd h (by simp))
    (fun _ _ h ↦ absurd h (by simp)) (fun _ _ _ _ _ h ↦ absurd h (by simp)) ?_
  intro fp outs ho rd _ hB hLin
  obtain ⟨e0, e1⟩ := stVal_param ept ept1 (fp + fs f) p p1
  obtain ⟨e2, e291⟩ := stVal_bufs ept ept1 (fp + fs f) p p1
  rw [hbuf fp] at hB
  have hm : MemLay rd (stOwn ept ept1 (fp + fs f) p p1 ++ stLin ept ept1 p p1) :=
    memLay_append.mpr ⟨hB, hLin⟩
  have hat := st_sholds ept ept1 (fp + fs f) p p1 hl hl1 rd hm
  have hkind : ∀ s ∈ stPre, stKind s = true := fun s hs ↦ List.all_eq_true.mp st_kinds s hs
  have hatom : ∀ s ∈ stPre, ∃ a, s = .atom a := by
    intro s hs
    rcases stKind_cases (hkind s hs) with ⟨_, h⟩ | ⟨_, _, h | h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;>
      exact ⟨_, h⟩
  refine ⟨stVal ept ept1 (fp + fs f) p p1, by rw [hp]; simp only [List.map_cons,
    List.map_nil, e0, e1], fun s hs ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := hatom s hs
    exact True.intro
  · rw [hb]
    refine holdsList_straight stPre _ _ _ hat ?_
    simp [e291]
  · rw [st_allocs]; rfl
  · rw [st_allocs]; simp [bases, e2]
  · have : stPre.filterMap (Stmt.callSF (stVal ept ept1 (fp + fs f) p p1)) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro s hs
      obtain ⟨a, rfl⟩ := hatom s hs
      rfl
    rw [this]
    match outs, ho with
    | [], _ => exact True.intro
  · rw [flatMap_loadsEv _ stPre (by decide +kernel)]
    intro q hq
    obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
    rcases stKind_cases (hkind s hs) with ⟨_, rfl⟩ | ⟨d, o, h | h, ho⟩ | ⟨o, rfl, ho, -⟩ |
      ⟨a, rfl, ha⟩
    · simp [Stmt.loadS] at hq
    · subst h; simp only [Stmt.loadS, Option.some.injEq] at hq; subst hq
      exact ⟨ept + o, by rw [e0, tb_addr_ofK], Or.inl ⟨(ept, p), by simp [stLin], by omega,
        by simp [hl]; omega⟩⟩
    · subst h; simp only [Stmt.loadS, Option.some.injEq] at hq; subst hq
      exact ⟨ept1 + o, by rw [e1, tb_addr_ofK], Or.inl ⟨(ept1, p1), by simp [stLin], by omega,
        by simp [hl1]; omega⟩⟩
    · simp only [Stmt.loadS, Option.some.injEq] at hq; subst hq
      refine ⟨fp + fs f + o, by rw [e2, tb_addr_ofK], Or.inr ?_⟩
      rw [hbuf fp]
      exact ⟨_, List.mem_cons_self, by omega, by simp [stEqWords]; omega⟩
    · cases a <;> simp [Stmt.loadS, pureB] at hq ha


set_option maxRecDepth 10000 in
/-- **`selector_tables` is complete within its frame and buffer**: on the point's runs, at every
frame pointer, its buffer at the bump allocator's position, returned. -/
theorem selector_tables_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (ept ept1 : ℕ) (p p1 : List E) (hl : p.length = 32) (hl1 : p1.length = 32) :
    CompleteAtDTB fs cert k "selector_tables" (stLin ept ept1 p p1) [ofK (addressOfIndex ept), ofK (addressOfIndex ept1)]
      (stOut ept ept1 p p1) (fun _ ↦ True)
      (fs "selector_tables" + [512].sum) := by
  obtain ⟨fn, hf, hp, hb⟩ := stFound
  set f := "selector_tables"
  have hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s)
      [stEqWords (stVal ept ept1 (fp + fs f) p p1)] [512] := by
    intro fp; simp [stEqWords]
  have hbuf : ∀ fp, bufL (fp + fs f) [512] [stEqWords (stVal ept ept1 (fp + fs f) p p1)] =
      stOwn ept ept1 (fp + fs f) p p1 := by
    intro fp; simp [bufL, bases, stOwn]
  refine (completeAt_flatOutDTB (fs := fs) (cert := cert) hf st_not_loop k (stLin ept ept1 p p1) _
    (fun fp ↦ [ofK (addressOfIndex (fp + fs f))]) _ hb st_flat st_addrs
    [512] (fun fp ↦ [stEqWords (stVal ept ept1 (fp + fs f) p p1)])
    hown (fun fp ↦ ⟨_, rfl, hbuf fp⟩) (fun _ ↦ []) (fun _ ↦ True) [] [] 0 (fun _ ↦ trivial) (fun _ ↦ le_rfl)
    (fun _ ↦ le_rfl) (fun _ _ h ↦ absurd h (by simp)) (fun _ _ _ _ _ h ↦ absurd h (by simp)) ?_).mono
    (by simp) fun _ _ ↦ trivial
  intro fp outs ho rd _ hB hLin
  obtain ⟨e0, e1⟩ := stVal_param ept ept1 (fp + fs f) p p1
  obtain ⟨e2, e291⟩ := stVal_bufs ept ept1 (fp + fs f) p p1
  rw [hbuf fp] at hB
  have hm : MemLay rd (stOwn ept ept1 (fp + fs f) p p1 ++ stLin ept ept1 p p1) :=
    memLay_append.mpr ⟨hB, hLin⟩
  have hat := st_sholds ept ept1 (fp + fs f) p p1 hl hl1 rd hm
  have hkind : ∀ s ∈ stPre, stKind s = true := fun s hs ↦ List.all_eq_true.mp st_kinds s hs
  have hatom : ∀ s ∈ stPre, ∃ a, s = .atom a := by
    intro s hs
    rcases stKind_cases (hkind s hs) with ⟨_, h⟩ | ⟨_, _, h | h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;>
      exact ⟨_, h⟩
  refine ⟨stVal ept ept1 (fp + fs f) p p1, by rw [hp]; simp only [List.map_cons,
    List.map_nil, e0, e1], fun s hs ↦ ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · obtain ⟨a, rfl⟩ := hatom s hs
    exact True.intro
  · rw [hb]
    refine holdsList_straight stPre _ _ _ hat ?_
    simp [e291]
  · rw [st_allocs]; rfl
  · rw [st_allocs]; simp [bases, e2]
  · have : stPre.filterMap (Stmt.callSF (stVal ept ept1 (fp + fs f) p p1)) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro s hs
      obtain ⟨a, rfl⟩ := hatom s hs
      rfl
    simp only [flatCalls, this, List.map_nil]
    match outs, ho with
    | [], _ => exact True.intro
  · rw [flatMap_loadsEv _ stPre (by decide +kernel)]
    intro q hq
    obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
    rcases stKind_cases (hkind s hs) with ⟨_, rfl⟩ | ⟨d, o, h | h, ho⟩ | ⟨o, rfl, ho, -⟩ |
      ⟨a, rfl, ha⟩
    · simp [Stmt.loadS] at hq
    · subst h; simp only [Stmt.loadS, Option.some.injEq] at hq; subst hq
      exact ⟨ept + o, by rw [e0, tb_addr_ofK], Or.inl ⟨(ept, p), by simp [stLin], by omega,
        by simp [hl]; omega⟩⟩
    · subst h; simp only [Stmt.loadS, Option.some.injEq] at hq; subst hq
      exact ⟨ept1 + o, by rw [e1, tb_addr_ofK], Or.inl ⟨(ept1, p1), by simp [stLin], by omega,
        by simp [hl1]; omega⟩⟩
    · simp only [Stmt.loadS, Option.some.injEq] at hq; subst hq
      refine ⟨fp + fs f + o, by rw [e2, tb_addr_ofK], Or.inr ?_⟩
      rw [hbuf fp]
      exact ⟨_, List.mem_cons_self, by omega, by simp [stEqWords]; omega⟩
    · cases a <;> simp [Stmt.loadS, pureB] at hq ha

end
end LeanVM.Guest.B1.Tables
