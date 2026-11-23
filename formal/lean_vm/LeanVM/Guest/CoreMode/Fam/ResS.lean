/-
  LeanVM.Guest.CoreMode.Fam.ResS

  The residuals at the honest frames by family: the selectors' bounds from the instance's path,
  names free, the other families and the listed certificates as hypotheses.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResT
public import LeanVM.Guest.CoreMode.Fam.SelDefs
public import LeanVM.Guest.CoreMode.Fam.RefAll

/-!
# The residuals by family

An honest frame (`TopAt`) is a `node` instance whose path returns and whose events hold on the
reference memory (`TopAt.events`: the tree is valid on any memory covering its writes,
`Covers.valid`); a frame cell named on the path, the frame holds it (`TopAt.cell`).

A nonzero divisor at a parameter (`nzB`) holds there (`nzPar_top`): the frame holds the
parameter, a loop helper's counter is a power of `g` (`TopAt.ctr`, `Res.insts_ctr`), and a listed
parameter is nonzero at every honest instance (`NzVal`, B1's).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (ltSelB allV scanFr_sound scanHp_sound allV_get)
open LeanVM.Prover.Exec

@[expose] public section

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **An honest frame's path, its events holding on the reference memory.** -/
theorem TopAt.events (t : TopAt A r K i e j) (hr : r.Ok) : ∃ vs, walk e.σ (coreOf j).body = .ret (e.pre ++ e.es) vs ∧
    FrameHolds r.img j e.I.fp e.σ (e.pre ++ e.es) vs e.I.kidFps e.I.hdr ∧
    ∀ ev ∈ e.pre ++ e.es, ev.Holds r.img.read e.σ := by
  obtain ⟨vs, hw, hF⟩ := t.path
  rw [← t.fn] at hw
  refine ⟨vs, hw, hF, ?_⟩
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  have hv := Covers.valid hH.toHonest hXh.covers
  obtain ⟨f, bufs, kids, hn⟩ := t.node
  rcases insts_good r.T _ r.hdr hv e.I t.inst with ⟨args, rets, hval⟩ | ⟨_, _, hph⟩
  · rw [hn] at hval
    unfold Tree.Valid at hval
    obtain ⟨fn, hf, -, es', vs', hw', -, hes, -⟩ := hval
    obtain ⟨i', rfl, hi', -, hfi, hc, -⟩ := fn_of_idx t.idx
    rw [hn] at hfi
    simp only [Tree.name] at hfi
    obtain rfl : fn = coreProgram[i'] := Option.some.inj (hf.symm.trans hfi)
    rw [← hc, hw] at hw'
    obtain ⟨rfl, -⟩ := Out.ret.inj hw'
    exact hes
  · rw [hn] at hph; cases hph

/-- The frame holds each value the path names, at its cell inside the frame. -/
theorem TopAt.cell (t : TopAt A r K i e j) (hr : r.Ok) {vs : List V}
    (hF : FrameHolds r.img j e.I.fp e.σ (e.pre ++ e.es) vs e.I.kidFps e.I.hdr) {x : V}
    (hx : x ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs) (h2 : 2 ≤ cellJ j x) (hlt : cellJ j x < fsN j) :
    refMem r.img (e.I.fp + cellJ j x) = e.σ x := by
  have hκ := logMemorySize_le_28 (e := r.exec) hr.size
  have hb := t.fb
  exact ((refRd_img hκ r.img) _ _ (by omega) (hF.val x hx h2 hlt)).2

/-- An atom on the path names its uses. -/
theorem namedOf_atom {ps : List V} {es : List Ev} {vs : List V} {a : Atom} {x : V} (ha : Ev.atom a ∈ es)
    (hx : x ∈ atomUses a) : x ∈ namedOf ps es vs :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ha, hx⟩))

/-- **A loop helper's counter at an honest frame is a power of `g`** (`Res.insts_ctr`). -/
theorem TopAt.ctr (t : TopAt A r K i e j) (hr : r.Ok) (hl : (coreOf j).loop = true) :
    ∃ p0 prest e', (coreOf j).params = p0 :: prest ∧ e.σ p0 = ofK (addressOfIndex e') := by
  obtain ⟨rd, hH, -⟩ := hr.honest
  obtain ⟨f, bufs, kids, hn⟩ := t.node
  obtain ⟨i', rfl, hi', -, hfi, hc, -⟩ := fn_of_idx t.idx
  rw [hn] at hfi
  simp only [Tree.name] at hfi
  rw [hc] at hl ⊢
  have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
  have hroot : Res.CtrOk coreProgram B2C.fs (r.T.total B2C.fs + 1) r.T := by
    intro f' σ' _ _ fn' hT' hg hl'
    have := (progOk_guest.loop f' fn' hg hl').1
    have hn' := hr.name
    rw [hT'] at hn'
    simp only [Tree.name] at hn'
    subst hn'
    exact absurd this (by decide)
  obtain ⟨p0, prest, e1, hps, hσ0, -⟩ := Res.insts_ctr hfs progOk_guest r.T _ r.hdr hH.valid le_rfl hroot e.I t.inst
    f e.σ bufs kids _ hn hfi hl
  exact ⟨p0, prest, e1, hps, hσ0⟩

end

/-- **A value nonzero at every honest instance of a function** (B1's). -/
def NzVal (f : String) (v : V) : Prop :=
  ∀ r : Ref, r.Ok → ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ σ bufs kids,
    I.t = .node f σ bufs kids → σ v ≠ 0

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **A nonzero divisor at a parameter at an honest frame**: the loop counter, a power of `g`, or a
parameter `NzVal` gives. -/
theorem nzPar_top (t : TopAt A r K i e j) (hr : r.Ok) {nzs : List (String × V)} (hnz : ∀ p ∈ nzs, NzVal p.1 p.2)
    {o : ℕ} (h : Res.nzB nzs j o = true) : RRes (refMem r.img) e.I.fp (.nz o) := by
  simp only [Res.nzB, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h2, hlt⟩, ⟨v, hv, rfl, hv'⟩ | ⟨⟨f, v⟩, hp, ⟨hf, rfl⟩, ht⟩⟩ := h
  swap
  · -- a listed value a top-level atom names
    obtain ⟨vs, hw, hF, -⟩ := t.events hr
    obtain ⟨a, ha, hva⟩ := Res.topUses_sound ht hw
    show refMem r.img (e.I.fp + cellJ j v) ≠ 0
    rw [t.cell hr hF (namedOf_atom ha hva) h2 hlt]
    obtain ⟨f', bufs, kids, hn⟩ := t.node
    obtain ⟨i', rfl, hi', hname, -, hc, -⟩ := fn_of_idx t.idx
    simp only at hf
    rw [hc, hname, hn] at hf
    subst hf
    exact hnz _ hp r hr e.I t.inst e.σ bufs kids hn
  obtain ⟨vs, -, hF, -⟩ := t.events hr
  show refMem r.img (e.I.fp + cellJ j v) ≠ 0
  rw [t.cell hr hF (List.mem_append_left _ (List.mem_append_left _ hv)) h2 hlt]
  rcases hv' with hc | hl
  · unfold Res.ctrOf at hc
    by_cases hl : (coreOf j).loop = true
    · rw [ite_eq_left hl] at hc
      obtain ⟨p0, prest, e', hps, hσ⟩ := t.ctr hr hl
      rw [hps, List.head?_cons, Option.some.injEq] at hc
      subst hc
      rw [hσ]
      exact Mode.ofK_gpow_ne_zero _
    · rw [ite_eq_right hl] at hc; cases hc
  · obtain ⟨f, bufs, kids, hn⟩ := t.node
    obtain ⟨i', rfl, hi', hname, -, hc, -⟩ := fn_of_idx t.idx
    rw [hc, hname, hn] at hl
    exact hnz _ hl r hr e.I t.inst e.σ bufs kids hn

end

/-! ## Splits -/

section

variable {M : ℕ → E} {fp : ℕ}

end

end

end LeanVM.Guest.EndExec
