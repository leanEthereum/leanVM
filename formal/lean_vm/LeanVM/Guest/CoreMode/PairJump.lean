/-
  LeanVM.Guest.CoreMode.PairJump

  The pairing's jumps: what a `JUMP` the pass accepted is, by its condition and target cells or by
  the head statement past its reads, and the path's events from the position it jumps from to the
  position of the side the run takes.
-/

module

public import LeanVM.Guest.CoreMode.PairHeap
public import LeanVM.Guest.Bridge.AlignJump
public import LeanVM.Guest.Bridge.StepRule

/-!
# The pairing's jumps

`Bridge/AlignJump.lean`'s lemmas for the pairing's pass (`jumpStepH`, `headStepH`), for any body:

* what a jump passed (`jumpH_zero`, `jumpH_fwd`, `headH_ite`, `headH_ret`, `headH_call`, `headH_callIf`,
  `headH_dispatch`; `jumpH_match` is `PairSound`'s), and that the head statement past the reads is one
  of these (`headH_stmt`);
* the position at a jump (`pair_jump`): its hints' atoms, then the reads before the head statement,
  then the head's zipper, with the successors the pass records;
* the side the run takes, by positions (`side_ite`, `side_arm`): the path's events from the head
  statement to the side's normalized position are the branch's condition and atoms that write nothing,
  so they add nothing to `Written`.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Bridge
open LeanVM.Guest.Check (getF)

public section

variable {P : PairCtx} {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {z zs : Zip}
  {r : Option Zip × List (ℕ × Zip)}

/-! ## What a jump passed -/

/-- A jump on a constant `0`: never taken, the zipper falling through. -/
theorem jumpH_zero (h : jumpStepH P i oc od of tabs z zs = some r) (hz : P.X.zeroAt oc = true) : r = (some z, []) := by
  simp only [jumpStepH, hz, Bool.cond_true, Option.some.injEq] at h
  exact h.symm

/-- A forward jump in the frame to a constant pc: the zipper at the target. -/
theorem jumpH_fwd (h : jumpStepH P i oc od of tabs z zs = some r) (hzero : P.X.zeroAt oc = false)
    (hfwd : fwdJ P.X i oc od of = true) :
    P.X.nzAt oc = true ∧ P.X.selfAt of = true ∧ ∃ t o, P.X.pcAt od = some t ∧ P.X.fwdOff i t = some o ∧
      r = (none, [(o, z)]) := by
  have hf := hfwd
  simp only [fwdJ, Bool.and_eq_true] at hf
  simp only [jumpStepH, hzero, hfwd, Bool.cond_false, Bool.cond_true] at h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨hf.1.1, hf.1.2, t, o, ht, ho, rfl⟩

theorem headH_of (h : jumpStepH P i oc od of tabs z zs = some r) (hzero : P.X.zeroAt oc = false)
    (hfwd : fwdJ P.X i oc od of = false) : headStepH P i oc od of tabs zs = some r := by
  simpa only [jumpStepH, hzero, hfwd, Bool.cond_false] using h

/-- **The head statement** a jump steps by: none of an atom. -/
theorem headH_stmt (h : headStepH P i oc od of tabs zs = some r) :
    ∃ s ss, zs.cur = s :: ss ∧ ∀ a, s ≠ .atom a := by
  rcases hc : zs.cur with _ | ⟨s, ss⟩
  · simp [headStepH, hc] at h
  · refine ⟨s, ss, rfl, fun a ha ↦ ?_⟩
    subst ha
    simp [headStepH, hc] at h

/-- A branch: on its condition's cell, the zero side falling through, the other at the target. -/
theorem headH_ite {c : V} {zb nb ss : List Stmt} (h : headStepH P i oc od of tabs zs = some r)
    (hz : zs.cur = .ite c zb nb :: ss) :
    P.X.locAt c.idx = oc ∧ P.X.selfAt of = true ∧ ∃ t cz cn o, P.X.pcAt od = some t ∧
      P.nL (zs.enter (.ite c zb nb) ss 0) = some cz ∧ P.nL (zs.enter (.ite c zb nb) ss 1) = some cn ∧
      P.X.fwdOff i t = some o ∧ r = (some cz, [(o, cn)]) := by
  simp only [headStepH, hz] at h
  cases hb : (Nat.beq (P.X.locAt c.idx) oc && P.X.selfAt of) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
  · cases h
  simp only [Bool.and_eq_true, Nat.beq_eq] at hb
  refine ⟨hb.1, hb.2, ?_⟩
  split at h
  · rename_i t cz cn ht hcz hcn
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨t, cz, cn, o, ht, hcz, hcn, ho, rfl⟩
  · cases h

/-- A return: `main`'s the halting jump, any other's `od = 0`, `of = 1`; nothing falls through. -/
theorem headH_ret {vs : List V} {ss : List Stmt} (h : headStepH P i oc od of tabs zs = some r)
    (hz : zs.cur = .ret vs :: ss) :
    r = (none, []) ∧ P.X.nzAt oc = true ∧
      (if P.X.main then P.X.selfAt of = true ∧ P.X.pcAt od = some P.X.halt else od = 0 ∧ of = 1) := by
  simp only [headStepH, hz] at h
  cases hm : P.X.main <;> simp only [hm, Bool.cond_true, Bool.cond_false] at h
  · cases hb : (P.X.nzAt oc && Nat.beq od 0 && Nat.beq of 1) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
    · cases h
    cases h
    simp only [Bool.and_eq_true, Nat.beq_eq] at hb
    exact ⟨rfl, hb.1.1, by simpa using ⟨hb.1.2, hb.2⟩⟩
  · cases hb : (P.X.nzAt oc && P.X.selfAt of && P.X.pcAt od == some P.X.halt) <;>
      simp only [hb, Bool.cond_true, Bool.cond_false] at h
    · cases h
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact ⟨rfl, hb.1.1, by simpa using ⟨hb.1.2, hb.2⟩⟩

/-- A call site: the callee's entry the destination, the rest at the site's return pc. -/
theorem headH_call {f : String} {args rets : List V} {ss : List Stmt} (h : headStepH P i oc od of tabs zs = some r)
    (hz : zs.cur = .call f args rets :: ss) :
    P.X.nzAt oc = true ∧ ∃ s t c o, P.X.siteAt of args rets = some s ∧ P.X.pcAt od = some t ∧ P.X.entOk t f = true ∧
      P.nL (zs.next ss) = some c ∧ P.X.fwdOff i s.r = some o ∧ r = (none, [(o, c)]) := by
  simp only [headStepH, hz] at h
  split at h
  · rename_i s t c hs ht hc
    cases he : (P.X.nzAt oc && P.X.entOk t f) <;> simp only [he, Bool.cond_true, Bool.cond_false] at h
    · cases h
    simp only [Bool.and_eq_true] at he
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨he.1, s, t, c, o, hs, ht, he.2, hc, ho, rfl⟩
  · cases h

/-- A conditional call: on its condition's cell, the callee's entry the destination, the rest falling
through, at a site returning to the next offset or a loop's tail call before the closing `ret []`. -/
theorem headH_callIf {c : V} {f : String} {args : List V} {ss : List Stmt} (h : headStepH P i oc od of tabs zs = some r)
    (hz : zs.cur = .callIf c f args :: ss) :
    P.X.locAt c.idx = oc ∧ ∃ t ca, P.X.pcAt od = some t ∧ P.X.entOk t f = true ∧ P.nL (zs.next ss) = some ca ∧
      r = (some ca, []) ∧ ((P.X.nextAt of = true ∧ retNil ca.pos = true) ∨
        (P.X.nextAt of = false ∧ ∃ s, P.X.siteAt of args [] = some s ∧ s.r = P.X.entry + i + 1)) := by
  simp only [headStepH, hz] at h
  cases hb : Nat.beq (P.X.locAt c.idx) oc <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
  · cases h
  refine ⟨Nat.beq_eq.mp hb, ?_⟩
  split at h
  · rename_i t ca ht hca
    cases he : P.X.entOk t f <;> simp only [he, Bool.cond_true, Bool.cond_false] at h
    · cases h
    cases hn : P.X.nextAt of <;> simp only [hn, Bool.cond_true, Bool.cond_false] at h
    · split at h
      · rename_i s hs
        cases hsr : Nat.beq s.r (P.X.entry + i + 1) <;> simp only [hsr, Bool.cond_true, Bool.cond_false] at h
        · cases h
        cases h
        exact ⟨t, ca, ht, he, hca, rfl, Or.inr ⟨rfl, s, hs, Nat.beq_eq.mp hsr⟩⟩
      · cases h
    · cases hrn : retNil ca.pos <;> simp only [hrn, Bool.cond_true, Bool.cond_false] at h
      · cases h
      cases h
      exact ⟨t, ca, ht, he, hca, rfl, Or.inl ⟨rfl, hrn⟩⟩
  · cases h

/-- A dispatch: on a nonzero constant, its site's target cell the destination, the rest at the site's
return pc. -/
theorem headH_dispatch {x : V} {fs : List String} {args rets : List V} {ss : List Stmt}
    (h : headStepH P i oc od of tabs zs = some r) (hz : zs.cur = .dispatch x fs args rets :: ss) :
    P.X.nzAt oc = true ∧ od ≠ 0 ∧ ∃ s c o, P.X.siteAt of args rets = some s ∧ s.tgt = od ∧
      P.nL (zs.next ss) = some c ∧ P.X.fwdOff i s.r = some o ∧ r = (none, [(o, c)]) := by
  simp only [headStepH, hz] at h
  split at h
  · rename_i s c hs hc
    cases he : (P.X.nzAt oc && Nat.beq s.tgt od && !Nat.beq od 0) <;>
      simp only [he, Bool.cond_true, Bool.cond_false] at h
    · cases h
    simp only [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at he
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨he.1.1, fun h0 ↦ by simp [h0] at he, s, c, o, hs, he.1.2, hc, ho, rfl⟩
  · cases h

/-! ## The position at a jump -/

variable {X : AlignCtx} {H : HCert} {O S : Exec.Trie Unit} {body : List Stmt} {code : List OffsetInstruction}
  {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}

/-- An offset the pass reaches is one of the code's. -/
theorem pairAt_lt (hok : pairOk X H O S body code d = true) {o : ℕ} {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d o = some pos) : o < code.length := by
  obtain ⟨ins, -, -, hins, -⟩ := pairAt_step hok hat
  exact (List.getElem?_eq_some_iff.mp hins).1

/-- **Past an instruction other than a jump**: the next offset's position, after atoms. -/
theorem pair_next (hok : pairOk X H O S body code d = true) {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos)
    (hnj : ∀ oc od of, code[i]? ≠ some (.jump oc od of)) :
    ∃ (pos' : List Stmt) (bs : List Atom), pairAt (PairCtx.ofH X H O S) body code d (i + 1) = some pos' ∧
      pos = bs.map Stmt.atom ++ pos' := by
  obtain ⟨ins, z, as, hins, -, hpos, -, -, hcase⟩ := pairAt_step hok hat
  rcases hcase with ⟨-, ⟨o1, o2, o3, bs, dv, pv, off, cs, pos', -, hz, -, -, -, hat', -⟩ | ⟨hat', -⟩⟩ |
    ⟨oc, od, of, -, rfl, -⟩
  · exact ⟨pos', as ++ bs ++ .load dv pv off :: cs, hat', by rw [hpos, hz]; simp⟩
  · exact ⟨z.pos, as, hat', hpos⟩
  · exact absurd hins (hnj oc od of)

/-- **At a jump the pass reaches**: its hints' atoms (the flow ones compiling its flow hints), the
reads before the head statement, the jump's step from there, its successors recorded. -/
theorem pair_jump (hok : pairOk X H O S body code d = true) {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos) (hins : code[i]? = some (.jump oc od of)) :
    ∃ (as bs : List Atom) (z zs : Zip) (tabs : List (ℕ × Zip × ℕ)) (r : Option Zip × List (ℕ × Zip)),
      pos = as.map Stmt.atom ++ z.pos ∧ z.pos = bs.map Stmt.atom ++ zs.pos ∧
      (∀ a ∈ as, flowAtom a = false → stopS H.readT a = false) ∧ (∀ a ∈ bs, stopS H.readT a = false) ∧
      List.Forall₂ (Pairs X) (as.filter flowAtom) (((d.2.2.lookup (X.entry + i)).getD []).filter isaFlowHint) ∧
      ZOk body z ∧ ZOk body zs ∧
      jumpStepH (PairCtx.ofH X H O S) i oc od of tabs z zs = some r ∧
      (∀ z1 ∈ r.1, pairAt (PairCtx.ofH X H O S) body code d (i + 1) = some z1.pos) ∧
      (∀ p ∈ r.2, pairAt (PairCtx.ofH X H O S) body code d p.1 = some p.2.pos) ∧
      ∀ x arms ss a, zs.cur = .match_ x arms :: ss → X.zeroAt oc = false →
        fwdJ X i oc od of = false → getF X.arms od = some a →
        ∀ j < arms.length, ∃ t, getF X.jt (a.2 + j) = some t ∧ X.entry + i < t ∧ ∃ c',
          (PairCtx.ofH X H O S).nL (zs.enter (.match_ x arms) ss j) = some c' ∧
          pairAt (PairCtx.ofH X H O S) body code d (t - X.entry) = some c'.pos := by
  obtain ⟨ins, z, as, hins', hzok, hpos, hq, hpairs, hcase⟩ := pairAt_step hok hat
  rw [hins] at hins'
  cases hins'
  rcases hcase with ⟨hnj, -⟩ | ⟨oc', od', of', zs, heq, -, -, hzs, hzsok, ⟨bs, hzpos, hbs⟩, tabs, r, hr, h1, h2, h3⟩
  · exact absurd rfl (hnj oc od of)
  simp only [OffsetInstruction.jump.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨as, bs, z, zs, tabs, r, hpos, hzpos, hq, hbs, hpairs, hzok, hzsok, hr, h1, h2, h3⟩

/-! ## The events on the way, by positions -/

variable {σ : Val}

/-- **A branch's side, by positions**: the path from the head `ite` is its condition, then the side
its valuation picks entered. -/
theorem side_ite {c : V} {zb nb ss : List Stmt} (hz : zs.cur = .ite c zb nb :: ss) {es : List Ev} {vs : List V}
    (hp : walk σ zs.pos = .ret es vs) :
    ∃ es', es = .inK c :: es' ∧ walk σ (zs.enter (.ite c zb nb) ss (if σ c = 0 then 0 else 1)).pos = .ret es' vs := by
  rw [Zip.pos_head hz, walk_ite_cons] at hp
  obtain ⟨es', hes', rfl⟩ := pre_eq_ret hp
  refine ⟨es', rfl, ?_⟩
  rw [Zip.enter_pos]
  by_cases h0 : σ c = 0 <;> simp only [h0, ↓reduceIte] at hes' ⊢ <;> simpa [subBlock] using hes'

/-- **A `match`'s arm, by positions**: the path from the head `match` is the arm its selector picks
entered, the selector `g^k`. -/
theorem side_arm {x : V} {arms : List (List Stmt)} {ss : List Stmt} (hz : zs.cur = .match_ x arms :: ss)
    {es : List Ev} {vs : List V} (hp : walk σ zs.pos = .ret es vs) :
    ∃ k < arms.length, σ x = ofK (g ^ k) ∧ walk σ (zs.enter (.match_ x arms) ss k).pos = .ret es vs := by
  rw [Zip.pos_head hz, walk_match_cons] at hp
  obtain ⟨k, hk, hxk, hwa⟩ := walkArms_take arms 0 (seq_ne_stuck hp)
  refine ⟨k, hk, by simpa [addressOfIndex] using hxk, ?_⟩
  rw [Zip.enter_pos, walk_append]
  rw [hwa] at hp
  simpa [subBlock, List.getD_eq_getElem?_getD, hk] using hp

end

end LeanVM.Guest.CoreMode
