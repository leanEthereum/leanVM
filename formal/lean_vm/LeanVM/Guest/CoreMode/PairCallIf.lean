/-
  LeanVM.Guest.CoreMode.PairCallIf

  The pairing at a call's `JUMP`, the call a `call` or a `callIf` returning to the next offset.
-/

module

public import LeanVM.Guest.CoreMode.PairJumpC

/-!
# The pairing at a call or a conditional call

`pair_callAny`: at a `JUMP` never zero, not forward, not a return, through a cell that is neither the
own frame's nor a next frame's, the pairing takes it by its head statement, a `call` (`pair_callC`'s
conclusion) or a `callIf` at a site returning to the next offset: the rest at the next offset, the
events up to the call its hints' atoms and reads, then the condition, the call entered or skipped,
atoms writing nothing.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Bridge
open LeanVM.Guest.Check (getF)

@[expose] public section

theorem fwdOff_succ (X : AlignCtx) (i : ℕ) : X.fwdOff i (X.entry + i + 1) = some (i + 1) := by
  have h1 : Nat.blt (Nat.add X.entry i) (X.entry + i + 1) = true := Nat.blt_eq.mpr (by simp)
  have h2 : Nat.sub (X.entry + i + 1) X.entry = i + 1 := by simp only [Nat.sub_eq]; omega
  simp only [AlignCtx.fwdOff, h1, h2, Bool.cond_true]
  rfl

variable {H : HCert}

/-- **At a call or a conditional call** (a `JUMP` never zero, not forward, not a return, through a
cell neither the own frame's nor a next frame's): the pairing takes it by its head statement, at a
site `of` to the callee of entry `od`'s pc, the rest at the site's return offset: a `call`, the
events up to it its hints' atoms and reads, then the call, then atoms writing nothing; or a `callIf`
on the jump's condition cell, returning to the next offset, the events up to it its hints' atoms and
reads, then the condition, the call entered or skipped, atoms writing nothing. -/
theorem pair_callAny {X : AlignCtx} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hok : pairOk X H O S body code d = true) {i : ℕ} {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos) {oc od of : ℕ}
    (hci : code[i]? = some (.jump oc od of)) (hz : X.zeroAt oc = false) (hf : fwdJ X i oc od of = false)
    (hnr : ¬ (od = 0 ∧ of = 1)) (hm : X.main = false) (hsf : X.selfAt of = false)
    (hnx : ∀ t f, X.pcAt od = some t → X.entOk t f = true → X.nextAt of = false)
    (hctrl : ∀ s ∈ stmtsOf body, NoD s) :
    ∃ f args rets s t o pos', X.siteAt of args rets = some s ∧ X.pcAt od = some t ∧ X.entOk t f = true ∧
      X.fwdOff i s.r = some o ∧ pairAt (PairCtx.ofH X H O S) body code d o = some pos' ∧
      ∃ as : List Atom, List.Forall₂ (Pairs X) (as.filter flowAtom)
        (((d.2.2.lookup (X.entry + i)).getD []).filter isaFlowHint) ∧
      ((∀ {sigOf : String → HSig} {rd : Reader} {ws0 : List E} {σ : Val} {pre es : List Ev} {vs : List V},
        walk σ pos = .ret es vs → ReadsOkC sigOf H rd σ ws0 (pre ++ es) →
        ∃ (evs : List Ev) (cs : List Atom) (es' : List Ev),
          es = evs ++ Ev.call f args rets :: (cs.map Ev.atom ++ es') ∧ walk σ pos' = .ret es' vs ∧
          (∀ a ∈ cs, stopL a = false) ∧ (∀ a ∈ as, Ev.atom a ∈ evs) ∧
          ∀ x, WrittenC sigOf H rd σ ws0 (pre ++ evs) x → WrittenC sigOf H rd σ ws0 pre x ∨
            ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x) ∨
       ∃ c, X.locAt c.idx = oc ∧ rets = [] ∧
        ∀ {sigOf : String → HSig} {rd : Reader} {ws0 : List E} {σ : Val} {pre es : List Ev} {vs : List V},
        walk σ pos = .ret es vs → ReadsOkC sigOf H rd σ ws0 (pre ++ es) →
        ∃ (evs : List Ev) (cs : List Atom) (es' : List Ev),
          es = evs ++ Ev.inK c :: (if σ c = 0 then Ev.skip f args else Ev.call f args []) ::
            (cs.map Ev.atom ++ es') ∧
          walk σ pos' = .ret es' vs ∧ (∀ a ∈ cs, stopL a = false) ∧ (∀ a ∈ as, Ev.atom a ∈ evs) ∧
          ∀ x, WrittenC sigOf H rd σ ws0 (pre ++ evs) x → WrittenC sigOf H rd σ ws0 pre x ∨
            ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x) := by
  obtain ⟨as, bs, z, zs, tabs, r, hpos, hzpos, hq, hbs, hpairs, -, hzsok, hr, h1, h2, -⟩ := pair_jump hok hat hci
  have hh := headH_of hr hz hf
  obtain ⟨st, ss, hcur, hna⟩ := headH_stmt hh
  have hs : st ∈ stmtsOf body := zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
  have hqa : ∀ a ∈ as ++ bs, a ∉ as.filter flowAtom → stopS H.readT a = false := by
    intro a ha hn
    rcases List.mem_append.mp ha with ha | ha
    · cases hfa : flowAtom a
      · exact hq a ha hfa
      · exact absurd (List.mem_filter.mpr ⟨ha, hfa⟩) hn
    · exact hbs a ha
  have hX : (PairCtx.ofH X H O S).X = X := rfl
  cases st with
  | atom a => exact absurd rfl (hna a)
  | ret vs' =>
    obtain ⟨-, -, h3⟩ := headH_ret hh hcur
    rw [hX, hm] at h3
    exact absurd h3 hnr
  | ite c zb nb =>
    have h3 := (headH_ite hh hcur).2.1
    rw [hX, hsf] at h3
    cases h3
  | match_ x arms =>
    simp only [headStepH, hcur, hX, hsf, Bool.and_false, Bool.cond_false] at hh
    cases hh
  | dispatch x fs args rets => exact absurd rfl (hctrl _ hs x fs args rets)
  | call f args rets =>
    obtain ⟨-, s, t, c, o, hsite, ht, he, hc, ho, rfl⟩ := headH_call hh hcur
    have hat' := h2 (o, c) List.mem_cons_self
    refine ⟨f, args, rets, s, t, o, c.pos, hsite, ht, he, ho, hat', as, hpairs,
      Or.inl fun {sigOf rd ws0 σ pre es vs} hp hrw ↦ ?_⟩
    obtain ⟨cs, hcs, hcpos, -⟩ := normG_pos _ _ hc
    rw [hpos, hzpos, Zip.pos_head hcur, hcpos, ← List.append_assoc, ← List.map_append] at hp
    obtain ⟨es1, hes1, rfl⟩ := walk_atoms_ret hp
    rw [walk_call_cons] at hes1
    obtain ⟨es2, hes2, rfl⟩ := pre_eq_ret hes1
    obtain ⟨es3, hes3, rfl⟩ := walk_atoms_ret hes2
    refine ⟨(as ++ bs).map Ev.atom, cs, es3, by simp, hes3, hcs, fun a ha ↦ by simp [ha], fun x hx ↦ ?_⟩
    rcases written_extendC (fs := as.filter flowAtom) (rest := Ev.call f args rets :: (cs.map Ev.atom ++ es3))
        (by simpa [List.append_assoc] using hrw) hqa hx with h | ⟨a, ha, hwa⟩
    · exact Or.inl h
    · rw [List.mem_filter] at ha
      exact Or.inr ⟨a, ha.1, ha.2, by simp [ha.1], hwa⟩
  | callIf c f args =>
    obtain ⟨hloc, t, ca, ht, he, hca, rfl, hcase⟩ := headH_callIf hh hcur
    obtain ⟨s, hsite, hsr⟩ : ∃ s, X.siteAt of args [] = some s ∧ s.r = X.entry + i + 1 := by
      rcases hcase with ⟨h, -⟩ | ⟨-, h⟩
      · rw [hX, hnx t f ht he] at h; cases h
      · exact h
    refine ⟨f, args, [], s, t, i + 1, ca.pos, hsite, ht, he, by rw [hsr]; exact fwdOff_succ X i, h1 ca rfl, as,
      hpairs, Or.inr ⟨c, hloc, rfl, fun {sigOf rd ws0 σ pre es vs} hp hrw ↦ ?_⟩⟩
    obtain ⟨cs, hcs, hcpos, -⟩ := normG_pos _ _ hca
    rw [hpos, hzpos, Zip.pos_head hcur, hcpos, ← List.append_assoc, ← List.map_append] at hp
    obtain ⟨es1, hes1, rfl⟩ := walk_atoms_ret hp
    rw [walk_callIf_cons] at hes1
    obtain ⟨es2, hes2, rfl⟩ := pre_eq_ret hes1
    obtain ⟨es3, hes3, rfl⟩ := walk_atoms_ret hes2
    refine ⟨(as ++ bs).map Ev.atom, cs, es3, by simp, hes3, hcs, fun a ha ↦ by simp [ha], fun x hx ↦ ?_⟩
    rcases written_extendC (fs := as.filter flowAtom)
        (rest := Ev.inK c :: (if σ c = 0 then Ev.skip f args else Ev.call f args []) :: (cs.map Ev.atom ++ es3))
        (by simpa [List.append_assoc] using hrw) hqa hx with h | ⟨a, ha, hwa⟩
    · exact Or.inl h
    · rw [List.mem_filter] at ha
      exact Or.inr ⟨a, ha.1, ha.2, by simp [ha.1], hwa⟩

end

end LeanVM.Guest.CoreMode
