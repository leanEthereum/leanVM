/-
  LeanVM.Guest.EndExecResNz

  `ResTrack` for certificates whose residuals are listed parameters' nonzero values, on b2c's aligned
  honest tree.
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.CoreMode.Fam.NzOnly

/-!
# The nonzero residuals at the tree track's frames

The bus era's `Fam/ResS.nzPar_top` and `Assemble.resTop_nzOnly` on the tree track (`RefTrack`) of
b2c's aligned tree. At a state of the track at an offset of a certificate, the top frame is an
honest instance (`Bridge.RefOk.framesA`) of the function the certificate enters (`EntIdx`,
`fnOf_entry_inj`), whose frame holds each value its path names at its cell (`FrameHolds.val`). A
nonzero divisor at a parameter (`Res.nzB`) holds there (`nzPar_inst`): a loop helper's counter is a
power of `g` (`inst_ctrW`), and a listed value is nonzero at every honest instance (`NzValA`).
`resTrack_nzOnly`: `ResTrack` at certificates whose residuals are such (`Res.NzOnly`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl alignAt alignAt_step entOf)
open LeanVM.Prover.Exec

@[expose] public section

/-- **A value nonzero at every honest instance of a function**, on b2c's aligned tree. -/
def NzValA (al : String → Bool) (D : Ref → RefD) (f : String) (v : V) : Prop :=
  ∀ r, RefH (layB al) (D r) r → r.Ok → ∀ I ∈ instsR al D r, ∀ σ bufs kids,
    I.t = .node f σ bufs kids → σ v ≠ 0

end

public section

variable {al : String → Bool} {D : Ref → RefD} {A : String → FnAl} {R : Ref → Prop}

/-- An atom on the path names its uses. -/
theorem namedOf_atomA {ps : List V} {es : List Ev} {vs : List V} {a : Atom} {x : V} (ha : Ev.atom a ∈ es)
    (hx : x ∈ atomUses a) : x ∈ B2C.namedOf ps es vs :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ha, hx⟩))

/-- **A nonzero divisor at a parameter at an honest instance**: the loop counter, a power of `g`, or
a value `NzValA` gives. -/
theorem nzPar_inst {r : Ref} (hR : RefH (layB al) (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Memory.Tree} (ht : I.t = .node f σ bufs kids) {j : ℕ}
    (hj : idxOf f = some j) {es : List Ev} {vs : List V} (hw : walk σ (coreOf j).body = .ret es vs)
    {nzs : List (String × V)} (hnz : ∀ p ∈ nzs, NzValA al D p.1 p.2) {o : ℕ} (h : Res.nzB nzs j o = true) :
    RRes (refMem r.img) I.fp (.nz o) := by
  have hF := inst_frameA hR hI ht hj hw
  have hfb := inst_fbA hR hr hI ht hj
  have hcell : ∀ x ∈ B2C.namedOf (coreOf j).params es vs, 2 ≤ cellJ j x → cellJ j x < fsN j →
      refMem r.img (I.fp + cellJ j x) = σ x := fun x hx h2 hlt ↦
    (ref_readA hr (by omega) (hF.val x hx h2 hlt)).2
  obtain ⟨i', rfl, hi', hname, hfind, hc, -⟩ := fn_of_idx hj
  simp only [Res.nzB, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h2, hlt⟩, ⟨v, hv, rfl, hv'⟩ | ⟨⟨f', v⟩, hp, ⟨hf, rfl⟩, ht'⟩⟩ := h
  swap
  · -- a listed value a top-level atom names
    obtain ⟨a, ha, hva⟩ := Res.topUses_sound ht' hw
    show refMem r.img (I.fp + cellJ _ v) ≠ 0
    rw [hcell v (namedOf_atomA ha hva) h2 hlt]
    simp only at hf
    rw [hc, hname] at hf
    subst hf
    exact hnz _ hp r hR hr I hI σ bufs kids ht
  show refMem r.img (I.fp + cellJ _ v) ≠ 0
  rw [hcell v (List.mem_append_left _ (List.mem_append_left _ hv)) h2 hlt]
  rcases hv' with hctr | hl
  · unfold Res.ctrOf at hctr
    by_cases hl : (coreOf (i' + 1)).loop = true
    · simp only [hl, ↓reduceIte] at hctr
      rw [hc] at hl hctr
      obtain ⟨p0, prest, e', hps, hσ⟩ := inst_ctrW hR hI ht hfind hl
      rw [hps, List.head?_cons, Option.some.injEq] at hctr
      subst hctr
      rw [hσ]
      exact Mode.ofK_gpow_ne_zero _
    · simp [hl] at hctr
  · rw [hc, hname] at hl
    exact hnz _ hl r hR hr I hI σ bufs kids ht

/-- **`ResTrack` at certificates whose residuals are listed parameters' nonzero values**, each listed
value nonzero at every honest instance. -/
theorem resTrack_nzOnly {Ks Ks0 : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env}
    (certs : ModeCerts Ks0 Km E0) (hsub : ∀ K ∈ Ks, K ∈ Ks0)
    (hH : HintHyps (layB al) D A) (hRH : ∀ r, R r → RefH (layB al) (D r) r) (hEI : EntIdx A)
    {nzs : List (String × V)} (hok : ∀ K ∈ Ks, Res.NzOnly nzs K) (hnz : ∀ p ∈ nzs, NzValA al D p.1 p.2) :
    ResTrack (layB al) D A R Ks := by
  intro r hR0 hr K hK i hi fp done e st htr x hx _
  have hR := hRH r hR0
  obtain ⟨f, hf, hcode, hentry, -⟩ := certs.fn K (hsub K hK)
  have hif : i < f.instructionCount := by
    rw [← CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem hf), ← hcode]; exact hi
  obtain ⟨e', st', hst, hE, hfp, hat⟩ := htr.top
  obtain ⟨rfl, rfl⟩ := List.cons.inj hst
  -- the frame's function is `K`'s
  have hentK : entOf A e.I.t.name = K.F.entry := by
    obtain ⟨off, hpcoff, p, hal, -⟩ := hat
    obtain ⟨cf, hcf, hcentry, hlen⟩ := hH.layout _ _ hE.find
    obtain ⟨ins, -, -, -, -, hins, -⟩ :=
      alignAt_step (hH.progAl.ok _ _ hE.find) (show alignAt _ _ _ _ off = some p from hal)
    have hoff : off < cf.instructionCount := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hins).1 hlen
    rw [hcentry] at hpcoff
    have heq : cf.entryPc = f.entryPc := by
      rcases le_total cf.entryPc f.entryPc with h1 | h1
      · exact (consecutive_entry functions_consecutive cf hcf f hf h1 (by omega)).symm
      · exact consecutive_entry functions_consecutive f hf cf hcf h1 (by omega)
    rw [hcentry, heq, hentry]
  obtain ⟨j, hj⟩ := B2C.idxOf_of_find hE.find
  have hjK : (fnOf j).entryPc = K.F.entry := by rw [← hEI _ _ hj, hentK]
  obtain ⟨-, -, -, -, -, -, -, -, -, hjn⟩ := fn_of_idx hj
  rcases hok K hK with h0 | ⟨j0, hj0, hent0, hall⟩
  · rw [h0] at hx
    simp [Exec.Trie.get] at hx
  obtain rfl : j = j0 := fnOf_entry_inj hjn hj0 (hjK.trans hent0.symm)
  cases hg : K.F.res.get i with
  | none => rw [hg] at hx; cases hx
  | some l =>
    rw [hg, Option.getD_some] at hx
    have hfx := List.all_eq_true.mp (Res.allV_get hall hg) x hx
    obtain ⟨rd, hHa, -, hcov⟩ := hR.coversR
    obtain ⟨hI, j', bufs, kids, vs, hj', hIt, hfn, hw, -⟩ :=
      Bridge.RefOk.framesA hR.name hHa hcov htr e List.mem_cons_self
    obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
    rw [← hfp]
    cases x with
    | nz o => exact nzPar_inst hR hr hI hIt hj (by rw [hfn]; exact hw) hnz hfx
    | name o => trivial
    | lt a b => simp [Res.nzOnlyB] at hfx
    | sub a bs => simp [Res.nzOnlyB] at hfx

end

end LeanVM.Guest.EndExec
