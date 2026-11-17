/-
  LeanVM.Guest.Compiled.Obl.Guest

  The guest's obligations: every function's, from the analysis, the `ext` sites' checks and two
  named facts about the core program.
-/

module

public import LeanVM.Compiler.Sound.Obl.World
public import LeanVM.Guest.Compiled.Obl.Gkr
public import LeanVM.Guest.Compiled.Obl.Eval.All

/-!
# The guest's obligations

The guest's `World.U` is `guestU`: the table's bounds (`guestTab`), relation `0` the exponent
table with its window section, relation `1` the window table, the path windows and the bounded
words read (`guestRel`), and the `ext` functions' relations (`guestX`). With it:

* the analysis accepts every function but `verify_sub` and those of `guestXIdx`, by kernel
  evaluation (`guest_chk`, from `Eval/E00` on, put together in `Eval/All`);
* it accepts `verify_sub` with B1's bounds on `dims_g` and `kappa_base` and its window table as
  facts (`evalVs`), which `VsFacts` states over the core program;
* the functions of `guestXIdx` have their obligations by the analysis with `ext` sites and B1's
  facts on their bodies (`guestX_obl`: `Obl.Gkr`, `Obl.Walk`, `Obl.Lq`, `Obl.Os`, their checks
  evaluated in `Eval/XMain`, `Eval/XLoop0`, `Eval/XLoop1`, `Eval/XLq`, `Eval/XOs0`, `Eval/XOs1`);
* `exponent_tables` returns the exponent table and its window section (`ExpPost`, over the core
  program).

`guest_obligations_of` gives `W.Obligations tf` for every function of a compiled program whose
core is `coreProgram` and whose `U` is `guestU`, from `ExpPost` and `VsFacts`. Neither mentions a
certificate: they are B1's theorems' statements (`Obl/GuestB1.lean`). The guest's tables and the
runs of the evaluations (`Obl/GuestXTab.lean`, `Obl/Eval/`, `xTab`, `guestXIdx`, `vsIdx`) are
written by `lake exe guest-oblgen`; this file names functions by stable name only.
-/

namespace LeanVM.Guest.Compiled.Obl

open LeanVM.Compiler LeanVM.Compiler.Obl LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`exponent_tables` returns the exponent table and its window section** (B1-a's
`exponent_tables_holds`). -/
def ExpPost : Prop :=
  ∀ (rd : Reader) (a r : List E), coreProgram.Rel rd "exponent_tables" a r →
    B1.ExpTables rd ((a ++ r).getD 0 0) ∧ B1.ExpWinTab rd ((a ++ r).getD 0 0)

/-- **`verify_sub`'s facts** (B1-d's `vsDimsKnown0_holds`, `vsKnown_holds`, `vsTabsT_holds`): on a
memory of `2^κ` words, `minLogMem ≤ κ ≤ maxLogMem`, over the exponent table and its window section
at its argument `4`, its first `i` statements put the bounds and relation `vsFacts` lists at `i`. -/
def VsFacts : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ σ : Val,
    B1.ExpTables L.read (σ (.n 4)) ∧ B1.ExpWinTab L.read (σ (.n 4)) →
    ∀ p ∈ vsFacts, Stmt.HoldsList (coreProgram.Rel L.read) L.read σ
      ((coreProgram.getD vsIdx default).body.take p.1) True (fun _ => True) →
      p.2.Holds guestRel L.read σ

/-! ## The evaluations, assembled -/

theorem guest_chk {j : Nat} (hj : j < core_count%) (hs : guestSkip j = false) :
    chkFn guestTab (coreProgram.getD j default) = true := by
  have := List.all_eq_true.mp guest_chk_all j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  rw [hs, Bool.false_or] at this
  exact this

/-- The functions of `guestXIdx` are the families'. -/
theorem guestX_cover : guestXIdx.all (fun j => j == idx% verify_bus_gkr ||
    j == idx% verify_bus_gkr_loop0 || mainTab.any (·.1 == j) ||
    loopTab.any (·.1 == j) || lqTab.any (·.1 == j) || osTab.any (·.1 == j)) = true := by
  decide +kernel

/-- **The obligations of the functions of `guestXIdx`.** -/
theorem guestX_obl : ∀ j ∈ guestXIdx, OblFn (coreProgram.getD j default) := by
  intro j hj
  have := List.all_eq_true.mp guestX_cover j hj
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at this
  rcases this with ((((rfl | rfl) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
  · exact gkrBus_obl
  · exact gkrLoop_obl
  · exact main_obl (mainTab_ok e he)
  · exact loop_obl (loopTab_ok e he)
  · exact lq_obl (lqTab_ok e he)
  · exact os_obl (osTab_ok e he)

/-! ## The table's postconditions and relations -/

/-- A signature with an `xpost` is `exponent_tables`'. -/
theorem sig_xpost {f : String} (h : (guestTab.sig f).xpost ≠ []) :
    f = "exponent_tables" ∧ (guestTab.sig f).xpost = [(0, 0)] := by
  unfold Tab.sig at h ⊢
  cases hf : guestTab.sigs.find? (fun p => Obl.nameKey p.1 == Obl.nameKey f) with
  | none =>
    simp only [hf] at h
    exact absurd rfl h
  | some p =>
    simp only [hf] at h ⊢
    have hk := List.find?_some hf
    rw [beq_iff_eq] at hk
    obtain ⟨he, hx⟩ := guestTab_xpost p (List.mem_of_find?_eq_some hf) h
    exact ⟨(nameKey_inj hk).symm.trans he, hx⟩

/-- A signature with a postcondition is one of `postNames`'. -/
theorem sig_post {f : String} (h : (guestTab.sig f).post ≠ []) : f ∈ postNames := by
  unfold Tab.sig at h
  cases hf : guestTab.sigs.find? (fun p => Obl.nameKey p.1 == Obl.nameKey f) with
  | none =>
    simp only [hf] at h
    exact absurd rfl h
  | some p =>
    simp only [hf] at h
    have hk := List.find?_some hf
    rw [beq_iff_eq] at hk
    rw [← nameKey_inj hk]
    exact guestTab_post p (List.mem_of_find?_eq_some hf) h

theorem skip_post {j : Nat} (hs : guestSkip j = true) :
    (coreProgram.getD j default).name ∉ postNames := by
  have hm : j ∈ vsIdx :: guestXIdx := by
    simp only [guestSkip, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hs
    rcases hs with rfl | hs
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hs
  have := List.all_eq_true.mp skip_names j hm
  intro h
  have hc : postNames.contains (coreProgram.getD j default).name = true := List.contains_iff_mem.mpr h
  rw [show coreProgram.getD j default = Data.coreFunctions.getD j default from rfl] at hc
  rw [hc] at this
  exact absurd this (by decide)

theorem getD_of_mem {l : List Fn} {fn : Fn} (h : fn ∈ l) :
    ∃ j < l.length, l.getD j default = fn := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨j, hj, by simp [List.getD_eq_getElem?_getD, hj]⟩

/-! ## The guest's obligations -/

variable {κ : ℕ} {W : World κ}

/-- **The guest's obligations**: every function of a compiled program whose core is the guest's
and whose precondition is `guestU` has its obligations, on a memory of `2^κ` words,
`minLogMem ≤ κ ≤ maxLogMem`, given that `exponent_tables` returns the exponent table and B1's
facts in `verify_sub`. -/
theorem guest_obligations_of (hW : W.Compiled) (hcore : W.p.map (·.core) = coreProgram)
    (hκ : minLogMem ≤ κ ∧ κ ≤ maxLogMem) (hU : W.U = guestU W.L.read) (hexp : ExpPost)
    (hvs : VsFacts) : ∀ tf ∈ W.p, W.Obligations tf := by
  have hκ32 : κ ≤ 32 := hκ.2.trans maxLogMem_le
  have hW' : W.core = coreProgram := hcore
  have hU' : W.U = UOf guestTab guestRel guestX W.L.read := hU
  have hlen : coreProgram.length = core_count% := core_length
  have hxp : ∀ f a r, W.core.Rel W.L.read f a r →
      XPost guestRel W.L.read (guestTab.sig f) (a ++ r) := by
    intro f a r h p hp _
    by_cases hx : (guestTab.sig f).xpost = []
    · rw [hx] at hp
      exact absurd hp List.not_mem_nil
    obtain ⟨rfl, he⟩ := sig_xpost hx
    rw [he, List.mem_singleton] at hp
    subst hp
    rw [hW'] at h
    exact ⟨fun _ => hexp _ a r h, fun h1 => absurd h1 (by decide), fun h1 => absurd h1 (by decide),
      fun h1 => absurd h1 (by decide)⟩
  have hP : ∀ fn ∈ W.core, (guestTab.sig fn.name).post ≠ [] → chkFn guestTab fn = true := by
    intro fn hfn hpost
    rw [hW'] at hfn
    obtain ⟨j, hj, rfl⟩ := getD_of_mem hfn
    cases hs : guestSkip j with
    | true => exact absurd (sig_post hpost) (skip_post hs)
    | false => exact guest_chk (hlen ▸ hj) hs
  have hpost := World.post_of_chk hW guestTab_pows hκ32 hU' hP hxp
  have hC : CallsOk W.L.read W.C := fun f a r h => by
    obtain ⟨h1, h2⟩ := World.C_spec hW h
    rw [hU] at h2
    exact ⟨hW' ▸ h1, h2, hpost f a r h⟩
  intro tf htf
  have hmem : tf.core ∈ coreProgram := hcore ▸ List.mem_map_of_mem htf
  obtain ⟨j, hj, hjeq⟩ := getD_of_mem hmem
  by_cases hr : j ∈ guestXIdx
  · intro fp _ hpre
    rw [← World.params_vf hW htf fp, hU] at hpre
    have h := guestX_obl j hr κ W.L hκ.1 hκ.2 W.C (W.vf tf.core.name fp) hC
    rw [hjeq] at h
    rw [hU]
    exact h hpre
  by_cases hv : j = vsIdx
  · subst hv
    refine World.obligations_of_chkF hW guestTab_pows hκ32 hU' hP hxp htf (facts := vsFacts)
      (by rw [← hjeq]; exact evalVs) ?_
    intro σ hpre p hp hl
    rw [← hjeq] at hpre hl
    obtain ⟨hname, hparams⟩ := vs_fn
    have hex : B1.ExpTables W.L.read (σ (.n 4)) ∧ B1.ExpWinTab W.L.read (σ (.n 4)) := by
      have := hpre.1.2.2 (4, 0) (by rw [show coreProgram.getD vsIdx default =
        Data.coreFunctions.getD vsIdx default from rfl, hname, vs_xpre]; exact List.mem_singleton_self _)
        (by rw [show coreProgram.getD vsIdx default = Data.coreFunctions.getD vsIdx default from rfl,
          hparams]; simp)
      rw [show coreProgram.getD vsIdx default = Data.coreFunctions.getD vsIdx default from rfl,
        hparams] at this
      exact this.1 rfl
    exact hvs W.L hκ.1 hκ.2 σ hex p hp (hW' ▸ hl)
  · have hs : guestSkip j = false := by
      simp only [guestSkip, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      refine ⟨hv, ?_⟩
      cases hc : guestXIdx.contains j with
      | false => rfl
      | true => exact absurd (List.contains_iff_mem.mp hc) hr
    exact World.obligations_of_chk hW guestTab_pows hκ32 hU' hP hxp htf
      (by rw [← hjeq]; exact guest_chk (hlen ▸ hj) hs)

end
end LeanVM.Guest.Compiled.Obl
