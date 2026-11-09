/-
  LeanVM.Guest.B1.VerifySub.C.Ctab

  `verify_sub`'s `c_table` (G:3454-3463), honestly: a kernel-checked pass on the evaluated
  valuation, the table's cells checked against `ringCoefficients`' monomials as they are recorded.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Calls

/-!
# `c_table`, honestly

`ctStepH S`: `ctStep` (the soundness pass) checking, in addition, that a read is not a store of
`S`, a product's operands are older than its value, and a cell recorded in the table is
`specEV` of its offset. `ctRunH_good`: on a valuation satisfying the block's equations (`Good`),
with the challenges at `664` and `ringCoefficients`' monomials at `665` in memory, every value the
pass records is its monomial, every recorded cell is `specEV`'s, and the block holds.
`vsCtabT_complete`: with `ring_switch_target`'s call in `C`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

/-- One atom of the honest pass. -/
def ctStepH (S : List Atom) (st : CtSt) : Stmt → Option CtSt
  | .atom (.const d c) =>
      if eEqb c (word 1 0 0) then some ⟨(d, List.replicate 6 0) :: st.vars, st.mem⟩ else none
  | .atom (.load d p off) =>
      if p = .n 664 then
        if off < 6 ∧ Atom.load d p off ∉ S then some ⟨(d, evUnit off) :: st.vars, st.mem⟩ else none
      else if p = .n 665 then
        match st.mem.lookup off with
        | some e => if Atom.load d p off ∉ S then some ⟨(d, e) :: st.vars, st.mem⟩ else none
        | none =>
          match st.vars.lookup d with
          | some e => if e = specEV off ∧ off < 64 then some ⟨st.vars, (off, e) :: st.mem⟩ else none
          | none => none
      else none
  | .atom (.mul d a b) =>
      if a.idx < d.idx ∧ b.idx < d.idx then
        match st.vars.lookup a, st.vars.lookup b with
        | some ea, some eb => some ⟨(d, evAdd ea eb) :: st.vars, st.mem⟩
        | _, _ => none
      else none
  | _ => none

/-- The honest pass over a block. -/
def ctRunH (S : List Atom) : CtSt → List Stmt → Option CtSt
  | st, [] => some st
  | st, s :: ss =>
      match ctStepH S st s with
      | some st' => ctRunH S st' ss
      | none => none

/-- **The pass on `c_table`, honestly**, by the kernel. -/
theorem ctH_check : (ctRunH vsSL ⟨[], []⟩ ctPre).isSome = true := by decide +kernel

/-- Every recorded value is its monomial, every recorded cell `specEV`'s. -/
def CtOkH (chs : List E) (σ : Val) (st : CtSt) : Prop :=
  (∀ p ∈ st.vars, σ p.1 = evVal chs p.2 ∧ p.2.length = 6) ∧
    ∀ p ∈ st.mem, p.2 = specEV p.1 ∧ p.1 < 64

variable {rd : Reader} {w : ℕ → E} {σ : Val}

theorem ctStepH_good {S : List Atom} {chs : List E} (hcl : chs.length = 6)
    (hc : ReadsAt rd (σ (.n 664)) chs)
    (hW : ∀ k < 64, LoadHolds rd (σ (.n 665)) k (evVal chs (specEV k)))
    {st st' : CtSt} {a : Atom} (hs : ctStepH S st (.atom a) = some st') (hok : CtOkH chs σ st)
    (hg : Good rd S w σ a) : CtOkH chs σ st' ∧ a.Holds rd σ := by
  obtain ⟨hv, hm⟩ := hok
  match a, hs with
  | .const d c, hs =>
    simp only [ctStepH] at hs
    split at hs
    · rename_i hc1
      cases hs
      simp only [Good] at hg
      refine ⟨⟨fun p hp ↦ ?_, hm⟩, hg⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · rw [hg, eEqb_sound hc1, word_one, evVal_zero]; exact ⟨rfl, by simp⟩
      · exact hv p hp
    · cases hs
  | .load d p off, hs =>
    simp only [ctStepH] at hs
    simp only [Good] at hg
    split at hs
    · rename_i hp
      subst hp
      split at hs
      · rename_i hoff
        cases hs
        have hl := hc off (by omega)
        have e : σ d = chs.getD off 0 := by
          rw [hg.resolve_left hoff.2, rdAt, hl.2, List.getD_eq_getElem _ _ (by omega)]; rfl
        refine ⟨⟨fun q hq ↦ ?_, hm⟩, ?_⟩
        · rcases List.mem_cons.1 hq with rfl | hq
          · exact ⟨by rw [e, evVal_unit chs hoff.1], by simp [evUnit]⟩
          · exact hv q hq
        · show LoadHolds rd _ _ _
          rw [e, List.getD_eq_getElem _ _ (by omega)]; exact hl
      · cases hs
    · split at hs
      · rename_i _ hp
        subst hp
        split at hs
        · rename_i e he
          split at hs
          · rename_i hS
            cases hs
            obtain ⟨hes, hlt⟩ := hm _ (lookup_mem he)
            simp only at hes hlt
            have hl := hW off hlt
            have ed : σ d = evVal chs e := by
              rw [hg.resolve_left hS, rdAt, hl.2, hes]; rfl
            refine ⟨⟨fun q hq ↦ ?_, hm⟩, ?_⟩
            · rcases List.mem_cons.1 hq with rfl | hq
              · exact ⟨ed, by rw [hes]; simp [specEV]⟩
              · exact hv q hq
            · show LoadHolds rd _ _ _
              rw [ed, hes]; exact hl
          · cases hs
        · split at hs
          · rename_i e he
            split at hs
            · rename_i hck
              cases hs
              obtain ⟨hve, hel⟩ := hv _ (lookup_mem he)
              refine ⟨⟨hv, fun q hq ↦ ?_⟩, ?_⟩
              · rcases List.mem_cons.1 hq with rfl | hq
                · exact hck
                · exact hm q hq
              · show LoadHolds rd _ _ _
                rw [hve, hck.1]; exact hW off hck.2
            · cases hs
          · cases hs
      · cases hs
  | .mul d x y, hs =>
    simp only [ctStepH] at hs
    split at hs
    · rename_i hidx
      split at hs
      · rename_i ea eb hx hy
        cases hs
        simp only [Good] at hg
        rw [ite_eq_left_of_eq_true _ _ (eq_true hidx)] at hg
        obtain ⟨hvx, hlx⟩ := hv _ (lookup_mem hx)
        obtain ⟨hvy, hly⟩ := hv _ (lookup_mem hy)
        refine ⟨⟨fun q hq ↦ ?_, hm⟩, hg⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · exact ⟨by rw [hg, hvx, hvy, evVal_add chs hlx hly], evAdd_length hlx hly⟩
        · exact hv q hq
      · cases hs
    · cases hs

/-- **The honest pass is sound**: every statement of the block holds. -/
theorem ctRunH_good {S : List Atom} {chs : List E} (hcl : chs.length = 6)
    (hc : ReadsAt rd (σ (.n 664)) chs)
    (hW : ∀ k < 64, LoadHolds rd (σ (.n 665)) k (evVal chs (specEV k))) {C : CallRel}
    {kret : List E → Prop} :
    ∀ {st st' : CtSt} {ss : List Stmt}, ctRunH S st ss = some st' → CtOkH chs σ st →
      (∀ s ∈ ss, GoodS rd S w σ s) → ∀ {next : Prop}, next → Stmt.HoldsList C rd σ ss next kret
  | st, st', [], hr, hok, hg, next, hn => hn
  | st, st', s :: ss, hr, hok, hg, next, hn => by
    simp only [ctRunH] at hr
    split at hr
    · rename_i st1 h1
      match s, h1 with
      | .atom a, h1 =>
        obtain ⟨hok1, hh⟩ := ctStepH_good hcl hc hW h1 hok (hg _ List.mem_cons_self)
        exact ⟨hh, ctRunH_good hcl hc hW hr hok1 (fun t ht ↦ hg t (List.mem_cons_of_mem _ ht)) hn⟩
      | .call _ _ _, h1 => simp [ctStepH] at h1
      | .callIf _ _ _, h1 => simp [ctStepH] at h1
      | .ite _ _ _, h1 => simp [ctStepH] at h1
      | .match_ _ _, h1 => simp [ctStepH] at h1
      | .dispatch _ _ _ _, h1 => simp [ctStepH] at h1
      | .ret _, h1 => simp [ctStepH] at h1
    · cases hr

theorem ctPre_noNe : ctPre.all noNeB = true := by decide +kernel

variable {args : List E}

/-- **`c_table` and `ring_switch_target`'s call, honestly.** -/
theorem vsCtabT_complete (hl : args.length = 6) {chs : List E} (hcl : chs.length = 6)
    (hc : ReadsAt rd (vsσ rd w args (.n 664)) chs)
    (hW : ReadsAt rd (vsσ rd w args (.n 665)) (ringCoefficients chs)) {C : CallRel}
    (hC : C "ring_switch_target" [vsσ rd w args (.n 648), vsσ rd w args (.n 664)]
      [vsσ rd w args (.n 1091)])
    {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList C rd (vsσ rd w args) vsCtabT next kret := by
  have hW' : ∀ k < 64, LoadHolds rd (vsσ rd w args (.n 665)) k (evVal chs (specEV k)) := by
    intro k hk
    rw [← ringCoefficients_getElem hcl hk]
    exact hW k _
  have hG : ∀ s ∈ ctPre, GoodS rd vsSL w (vsσ rd w args) s := fun s hs ↦ by
    have hm : s ∈ vsCtabT := by rw [vsCtabT_eq]; exact List.mem_append_left _ hs
    have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 617) (blk := vsCtabT)
      (by decide +kernel) hm)
    rwa [fixNe_of_noNe (List.all_eq_true.mp ctPre_noNe s hs)] at h
  obtain ⟨st, hst⟩ := Option.isSome_iff_exists.1 ctH_check
  rw [vsCtabT_eq, holdsList_append]
  refine ctRunH_good hcl hc hW' hst ⟨fun _ h ↦ absurd h (by simp), fun _ h ↦ absurd h (by simp)⟩
    hG ?_
  simp only [Stmt.HoldsList, Stmt.Holds, vsCall, List.map_cons, List.map_nil]
  exact ⟨hC, hn⟩

end
end LeanVM.Guest.B1.VerifySub
