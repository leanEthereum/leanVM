/-
  LeanVM.Guest.Backend.Sound.Obl.Guest

  The guest's obligations: every function's, from the analysis and named facts about the core
  program.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.World
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E00
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E01
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E02
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E03
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E04
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E05
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E06
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E07
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E08
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E09
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E10
public import LeanVM.Guest.Backend.Sound.Obl.Eval.Misc
public import LeanVM.Guest.CoreData

/-!
# The guest's obligations

The guest's `World.U` is `guestU Ex X`: the table's bounds (`guestTab`), relation `0` the exponent
table `Ex`, and for `verify_bus_gkr_loop0` (the one function marked `ext`) a further precondition
`X`. With it:

* the analysis accepts every function but `verify_sub` and the `92` of `guestRestIdx`, by kernel
  evaluation (`guest_chk`, from `Eval/E00` to `Eval/E10`);
* it accepts `verify_sub` with B1's bounds on `dims_g` and `kappa_base` as facts (`evalVs`), which
  `VsFacts Ex` states over the core program;
* `exponent_tables` returns the exponent table (`ExpPost Ex`, over the core program);
* the obligations of the `92` others are `RestObl Ex X`, each function's `OblCore`: its
  obligations under every call relation within the core program's that meets the callees'
  preconditions, at every valuation meeting its own.

`guest_obligations_of` gives `W.Obligations tf` for every function of a compiled program whose
core is `coreProgram` and whose `U` is `guestU Ex X`, from those three named facts. None mentions
a certificate: `VsFacts` and `ExpPost` are B1's theorems' statements (`Obl/GuestB1.lean`),
`RestObl` is what remains.
-/

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The guest's relations**: tag `0` is the exponent table `Ex`. -/
def guestRel (Ex : Reader → E → Prop) : Nat → Reader → E → Prop := fun t rd v => t = 0 → Ex rd v

/-- **The guest's precondition** (`World.U`): the table's, the exponent table `Ex`, and `X` for
the function marked `ext`. -/
def guestU (Ex : Reader → E → Prop) (X : Reader → String → List E → Prop) (rd : Reader) :
    String → List E → Prop :=
  UOf guestTab (guestRel Ex) X rd

/-- **`exponent_tables` returns the exponent table** (B1-a's `exponent_tables_holds`). -/
def ExpPost (Ex : Reader → E → Prop) : Prop :=
  ∀ (rd : Reader) (a r : List E), coreProgram.Rel rd "exponent_tables" a r → Ex rd ((a ++ r).getD 0 0)

/-- **`verify_sub`'s facts** (B1-d's `vsDimsKnown0_holds`, `vsKnown_holds`): on a memory of
`2^κ` words, `minLogMem ≤ κ ≤ maxLogMem`, over the exponent table at its argument `4`, its first
`i` statements put the bounds `vsFacts` lists at `i`. -/
def VsFacts (Ex : Reader → E → Prop) : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ σ : Val, Ex L.read (σ (.n 4)) →
    ∀ p ∈ vsFacts, Stmt.HoldsList (coreProgram.Rel L.read) L.read σ
      ((coreProgram.getD vsIdx default).body.take p.1) True (fun _ => True) →
      p.2.Holds (guestRel Ex) guestTab L.read σ

/-- **A guest function's obligations, over the core program**: on a memory of `2^κ` words,
`minLogMem ≤ κ ≤ maxLogMem`, for every call relation within the core program's whose calls meet
their callees' preconditions, at every valuation meeting the function's precondition. -/
def OblCore (Ex : Reader → E → Prop) (X : Reader → String → List E → Prop) (g : Fn) : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ (C : CallRel) (σ : Val),
    (∀ f a r, C f a r → coreProgram.Rel L.read f a r ∧ guestU Ex X L.read f a) →
    guestU Ex X L.read g.name (g.params.map σ) →
    OblList C (guestU Ex X L.read) L.read σ g.body True

/-- **What remains**: the obligations of the functions of `guestRestIdx`. -/
def RestObl (Ex : Reader → E → Prop) (X : Reader → String → List E → Prop) : Prop :=
  ∀ j ∈ guestRestIdx, OblCore Ex X (coreProgram.getD j default)

theorem nameKey_inj {s t : String} (h : nameKey s = nameKey t) : s = t := by
  unfold nameKey at h
  have h1 : s.toByteArray.data.toList = t.toByteArray.data.toList :=
    (List.map_injective_iff.mpr fun _ _ hab => UInt8.toNat_inj.mp hab) h
  have h2 : s.toByteArray = t.toByteArray := by
    have := Array.toList_inj.mp h1
    cases hs : s.toByteArray
    cases ht : t.toByteArray
    rw [hs, ht] at this
    simp only at this
    rw [this]
  exact String.toByteArray_inj.mp h2

/-- A signature with an `xpost` is `exponent_tables`'. -/
theorem sig_xpost {f : String} (h : (guestTab.sig f).xpost ≠ []) :
    f = "exponent_tables" ∧ (guestTab.sig f).xpost = [(0, 0)] := by
  unfold Tab.sig at h ⊢
  cases hf : guestTab.sigs.find? (fun p => nameKey p.1 == nameKey f) with
  | none =>
    simp only [hf] at h
    exact absurd rfl h
  | some p =>
    simp only [hf] at h ⊢
    have hk := List.find?_some hf
    rw [beq_iff_eq] at hk
    obtain ⟨he, hx⟩ := guestTab_xpost p (List.mem_of_find?_eq_some hf) h
    exact ⟨(nameKey_inj hk).symm.trans he, hx⟩

/-- **The analysis accepts every guest function it does not skip.** -/
theorem guest_chk {j : Nat} (hj : j < 1601) (hs : guestSkip j = false) :
    chkFn guestTab (coreProgram.getD j default) = true := by
  have key : ∀ {a n : Nat}, (List.range' a n).all (fun j =>
      guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true → a ≤ j →
      j < a + n → chkFn guestTab (coreProgram.getD j default) = true := by
    intro a n h h1 h2
    have := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
    rw [hs, Bool.false_or] at this
    exact this
  by_cases h0 : j < 11
  · exact key evalE00 (by omega) (by omega)
  by_cases h1 : j < 12
  · exact key evalE01 (by omega) (by omega)
  by_cases h2 : j < 36
  · exact key evalE02 (by omega) (by omega)
  by_cases h3 : j < 37
  · exact key evalE03 (by omega) (by omega)
  by_cases h4 : j < 335
  · exact key evalE04 (by omega) (by omega)
  by_cases h5 : j < 346
  · exact key evalE05 (by omega) (by omega)
  by_cases h6 : j < 600
  · exact key evalE06 (by omega) (by omega)
  by_cases h7 : j < 850
  · exact key evalE07 (by omega) (by omega)
  by_cases h8 : j < 1100
  · exact key evalE08 (by omega) (by omega)
  by_cases h9 : j < 1350
  · exact key evalE09 (by omega) (by omega)
  · exact key evalE10 (by omega) (by omega)

theorem skip_post' {j : Nat} (hs : guestSkip j = true) :
    (guestTab.sig (coreProgram.getD j default).name).post = [] := by
  have hm : j ∈ vsIdx :: guestRestIdx := by
    simp only [guestSkip, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hs
    rcases hs with rfl | hs
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hs
  have := List.all_eq_true.mp skip_post j hm
  exact List.isEmpty_iff.mp this

theorem getD_of_mem {l : List Fn} {fn : Fn} (h : fn ∈ l) :
    ∃ j < l.length, l.getD j default = fn := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨j, hj, by simp [List.getD_eq_getElem?_getD, hj]⟩

variable {κ : ℕ} {W : World κ} {Ex : Reader → E → Prop} {X : Reader → String → List E → Prop}

/-- **The guest's obligations**: every function of a compiled program whose core is the guest's
and whose precondition is `guestU Ex X` has its obligations, on a memory of `2^κ` words,
`minLogMem ≤ κ ≤ maxLogMem`, given that `exponent_tables` returns the exponent table, B1's facts
in `verify_sub`, and the obligations of the functions the analysis does not discharge. -/
theorem guest_obligations_of (hW : W.Compiled) (hcore : W.p.map (·.core) = coreProgram)
    (hκ : minLogMem ≤ κ ∧ κ ≤ maxLogMem) (hU : W.U = guestU Ex X W.L.read) (hexp : ExpPost Ex)
    (hvs : VsFacts Ex) (hrest : RestObl Ex X) : ∀ tf ∈ W.p, W.Obligations tf := by
  have hκ32 : κ ≤ 32 := hκ.2.trans (by decide)
  have hW' : W.core = coreProgram := hcore
  have hU' : W.U = UOf guestTab (guestRel Ex) X W.L.read := hU
  have hxp : ∀ f a r, W.core.Rel W.L.read f a r →
      XPost (guestRel Ex) W.L.read (guestTab.sig f) (a ++ r) := by
    intro f a r h p hp hl
    by_cases hx : (guestTab.sig f).xpost = []
    · rw [hx] at hp
      exact absurd hp List.not_mem_nil
    obtain ⟨rfl, he⟩ := sig_xpost hx
    rw [he, List.mem_singleton] at hp
    subst hp
    intro _
    rw [hW'] at h
    exact hexp _ a r h
  have hP : ∀ fn ∈ W.core, (guestTab.sig fn.name).post ≠ [] → chkFn guestTab fn = true := by
    intro fn hfn hpost
    rw [hW'] at hfn
    obtain ⟨j, hj, rfl⟩ := getD_of_mem hfn
    have hj' : j < 1601 := by
      rw [show coreProgram = Data.coreFunctions from rfl, core_length] at hj
      exact hj
    cases hs : guestSkip j with
    | true => exact absurd (skip_post' hs) hpost
    | false => exact guest_chk hj' hs
  intro tf htf
  have hmem : tf.core ∈ coreProgram := hcore ▸ List.mem_map_of_mem htf
  obtain ⟨j, hj, hjeq⟩ := getD_of_mem hmem
  have hj' : j < 1601 := by
    rw [show coreProgram = Data.coreFunctions from rfl, core_length] at hj
    exact hj
  by_cases hr : j ∈ guestRestIdx
  · intro fp _ hpre
    rw [← World.params_vf hW htf fp, hU] at hpre
    have h := hrest j hr W.L hκ.1 hκ.2 W.C (W.vf tf.core.name fp) (fun f a r h => by
      obtain ⟨h1, h2⟩ := World.C_spec hW h
      rw [hU] at h2
      exact ⟨hW' ▸ h1, h2⟩)
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
    have hex : Ex W.L.read (σ (.n 4)) := by
      have := hpre.1.2.2 (4, 0) (by rw [show coreProgram.getD vsIdx default =
        Data.coreFunctions.getD vsIdx default from rfl, hname, vs_xpre]; exact List.mem_singleton_self _)
        (by rw [show coreProgram.getD vsIdx default = Data.coreFunctions.getD vsIdx default from rfl,
          hparams]; simp)
      rw [show coreProgram.getD vsIdx default = Data.coreFunctions.getD vsIdx default from rfl,
        hparams] at this
      exact this rfl
    exact hvs W.L hκ.1 hκ.2 σ hex p hp (hW' ▸ hl)
  · have hs : guestSkip j = false := by
      simp only [guestSkip, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      refine ⟨hv, ?_⟩
      cases hc : guestRestIdx.contains j with
      | false => rfl
      | true => exact absurd (List.contains_iff_mem.mp hc) hr
    exact World.obligations_of_chk hW guestTab_pows hκ32 hU' hP hxp htf
      (by rw [← hjeq]; exact guest_chk hj' hs)

end
end LeanVM.Guest.Backend.Obl
