/-
  LeanVM.Guest.CoreMode.PairLoopC

  The pairing at the jumps of a loop helper whose body has calls: its calls, its tail call, its return.
-/

module

public import LeanVM.Guest.CoreMode.PairLoop

/-!
# The pairing at a loop helper's jumps, its body with calls

For a body whose statements are atoms, calls, conditional calls and returns (`loopStmtC`), each
conditional call's condition at no cell of a nonzero constant: at a `JUMP` on a nonzero constant
(`pair_callLC`), the pairing takes it by a `call` (`pair_callC`'s conclusion, with the statement);
at the tail `JUMP` (its condition no nonzero constant, `pair_tailLC`), by a `callIf`, as
`pair_tailL`; at the return jump (`pair_retLC`), `pair_retC`'s conclusion.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Bridge
open LeanVM.Guest.Check (getF)

@[expose] public section

/-- A statement of a loop helper's body with calls: an atom, a call, a conditional call, a return, a branch
or a `match`. -/
def loopStmtC : Stmt → Bool
  | .atom _ | .call .. | .callIf .. | .ret _ | .ite .. | .match_ .. => true
  | _ => false

variable {H : HCert}

/-- **At a loop's tail `JUMP`** (its condition no constant, through a next-frame cell, not to pc cell
`0`), the body's statements atoms, calls, conditional calls and returns: `pair_tailL`'s conclusion. -/
theorem pair_tailLC {X : AlignCtx} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hok : pairOk X H O S body code d = true) {i : ℕ} {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos) {oc od of : ℕ}
    (hci : code[i]? = some (.jump oc od of)) (hz : X.zeroAt oc = false) (hnz : X.nzAt oc = false)
    (hsf : X.selfAt of = false) (hnx : X.nextAt of = true) (hod : od ≠ 0)
    (hst : ∀ s ∈ stmtsOf body, loopStmtC s = true) :
    ∃ c f args pos', Stmt.callIf c f args ∈ stmtsOf body ∧ X.locAt c.idx = oc ∧
      pairAt (PairCtx.ofH X H O S) body code d (i + 1) = some pos' ∧ retNil pos' = true ∧
      ∃ as : List Atom, List.Forall₂ (Pairs X) (as.filter flowAtom)
        (((d.2.2.lookup (X.entry + i)).getD []).filter isaFlowHint) ∧
      ∀ {sigOf : String → HSig} {rd : Reader} {ws0 : List E} {σ : Val} {pre es : List Ev} {vs : List V},
        walk σ pos = .ret es vs → ReadsAt sigOf H rd σ ws0 pre es →
        ∃ (evs : List Ev) (cs : List Atom) (es' : List Ev),
          es = evs ++ Ev.inK c :: (if σ c = 0 then Ev.skip f args else Ev.call f args []) :: (cs.map Ev.atom ++ es') ∧
          walk σ pos' = .ret es' vs ∧ (∀ a ∈ cs, stopL a = false) ∧ (∀ a ∈ as, Ev.atom a ∈ evs) ∧
          (∀ e ∈ evs, EvM sigOf rd σ e) ∧ ∀ x, WrittenC sigOf H rd σ ws0 (pre ++ evs) x → WrittenC sigOf H rd σ ws0 pre x ∨
            ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x := by
  obtain ⟨as, bs, z, zs, tabs, r, hpos, hzpos, hq, hbs, hpairs, -, hzsok, hr, h1, -, -⟩ := pair_jump hok hat hci
  have hf : fwdJ X i oc od of = false := by simp [fwdJ, hsf]
  have hh := headH_of hr hz hf
  obtain ⟨st, ss, hcur, hna⟩ := headH_stmt hh
  have hs : st ∈ stmtsOf body := zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
  have hl := hst st hs
  obtain ⟨c, f, args, rfl⟩ : ∃ c f args, st = .callIf c f args := by
    cases st with
    | atom a => exact absurd rfl (hna a)
    | callIf c f args => exact ⟨c, f, args, rfl⟩
    | call f args rets =>
      have h2 := (headH_call hh hcur).1
      simp only [PairCtx.ofH] at h2
      rw [hnz] at h2; cases h2
    | ret vs' =>
      obtain ⟨-, -, h3⟩ := headH_ret hh hcur
      cases hmm : (PairCtx.ofH X H O S).X.main <;> simp only [hmm, Bool.false_eq_true, ↓reduceIte] at h3
      · exact absurd h3.1 hod
      · have h4 : X.selfAt of = true := h3.1
        rw [hsf] at h4
        cases h4
    | ite c z n => simp [headStepH, hcur, PairCtx.ofH, hsf] at hh
    | match_ x arms => simp [headStepH, hcur, PairCtx.ofH, hsf] at hh
    | _ => simp [loopStmtC] at hl
  obtain ⟨hloc, t, ca, -, -, hca, rfl, hcase⟩ := headH_callIf hh hcur
  have hrn : retNil ca.pos = true := by
    rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · simp only [PairCtx.ofH] at h; rw [hnx] at h; cases h
  refine ⟨c, f, args, ca.pos, hs, hloc, h1 ca rfl, hrn, as, hpairs, fun {sigOf rd ws0 σ pre es vs} hp hrw ↦ ?_⟩
  obtain ⟨cs, hcs, hcpos, -⟩ := normG_pos _ _ hca
  rw [hpos, hzpos, Zip.pos_head hcur, hcpos, ← List.append_assoc, ← List.map_append] at hp
  obtain ⟨es1, hes1, rfl⟩ := walk_atoms_ret hp
  rw [walk_callIf_cons] at hes1
  obtain ⟨es2, hes2, rfl⟩ := pre_eq_ret hes1
  obtain ⟨es3, hes3, rfl⟩ := walk_atoms_ret hes2
  refine ⟨(as ++ bs).map Ev.atom, cs, es3, by simp, hes3, hcs, fun a ha ↦ by simp [ha], evM_atoms _, fun x hx ↦ ?_⟩
  have hqa : ∀ a ∈ as ++ bs, a ∉ as.filter flowAtom → stopS H.readT a = false := by
    intro a ha hn
    rcases List.mem_append.mp ha with ha | ha
    · cases hfa : flowAtom a
      · exact hq a ha hfa
      · exact absurd (List.mem_filter.mpr ⟨ha, hfa⟩) hn
    · exact hbs a ha
  rcases written_extendC (fs := as.filter flowAtom)
      (rest := Ev.inK c :: (if σ c = 0 then Ev.skip f args else Ev.call f args []) :: (cs.map Ev.atom ++ es3))
      (by simpa [List.append_assoc] using hrw) hqa hx with h | ⟨a, ha, hwa⟩
  · exact Or.inl h
  · rw [List.mem_filter] at ha
    exact Or.inr ⟨a, ha.1, ha.2, by simp [ha.1], hwa⟩

/-- **At a return jump** (`od = 0`, `of = 1`, never zero, not forward, cell `0` no constant pc) of a
body of atoms, calls, conditional calls and returns: `pair_retC`'s conclusion. -/
theorem pair_retLC {X : AlignCtx} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hok : pairOk X H O S body code d = true) {i : ℕ} {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos) {oc : ℕ}
    (hci : code[i]? = some (.jump oc 0 1)) (hz : X.zeroAt oc = false) (hsf : X.selfAt 1 = false)
    (h0 : X.pcAt 0 = none) (hst : ∀ s ∈ stmtsOf body, loopStmtC s = true)
    {sigOf : String → HSig} {rd : Reader} {ws0 : List E} {σ : Val}
    {pre es : List Ev} {vs : List V} (hp : walk σ pos = .ret es vs) (hrw : ReadsAt sigOf H rd σ ws0 pre es) :
    ∃ as : List Atom, List.Forall₂ (Pairs X) (as.filter flowAtom) (((d.2.2.lookup (X.entry + i)).getD []).filter isaFlowHint) ∧
      ∀ x, WrittenC sigOf H rd σ ws0 (pre ++ es) x → WrittenC sigOf H rd σ ws0 pre x ∨
        ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ es ∧ Writes σ a x := by
  obtain ⟨as, bs, z, zs, tabs, r, hpos, hzpos, hq, hbs, hpairs, -, hzsok, hr, -, -, -⟩ := pair_jump hok hat hci
  have hf : fwdJ X i oc 0 1 = false := by simp [fwdJ, hsf]
  have hh := headH_of hr hz hf
  obtain ⟨st, ss, hcur, hna⟩ := headH_stmt hh
  have hs : st ∈ stmtsOf body := zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
  have hl := hst st hs
  obtain ⟨vs', rfl⟩ : ∃ vs', st = .ret vs' := by
    cases st with
    | atom a => exact absurd rfl (hna a)
    | callIf c f args =>
      obtain ⟨-, t, -, ht, -⟩ := headH_callIf hh hcur
      simp only [PairCtx.ofH] at ht
      rw [h0] at ht; cases ht
    | call f args rets =>
      obtain ⟨-, s, t, c', o', -, ht, -⟩ := headH_call hh hcur
      simp only [PairCtx.ofH] at ht
      rw [h0] at ht; cases ht
    | ret vs' => exact ⟨vs', rfl⟩
    | ite c z n => simp [headStepH, hcur, PairCtx.ofH, hsf] at hh
    | match_ x arms => simp [headStepH, hcur, PairCtx.ofH, hsf] at hh
    | _ => simp [loopStmtC] at hl
  refine ⟨as, hpairs, ?_⟩
  rw [hpos, hzpos, ← List.append_assoc, ← List.map_append] at hp
  obtain ⟨es', hes', rfl⟩ := walk_atoms_ret hp
  rw [Zip.pos_head hcur, walk_ret_cons] at hes'
  simp only [Out.ret.injEq] at hes'
  obtain ⟨rfl, -⟩ := hes'
  obtain ⟨-, -, -, hW⟩ := atoms_writtenC (fs := as.filter flowAtom) (ss := zs.pos) (pre := pre)
    (es := (as ++ bs).map Ev.atom ++ []) (vs := vs) hp hrw (fun a ha hn ↦ by
        rcases List.mem_append.mp ha with ha | ha
        · cases hfa : flowAtom a
          · exact hq a ha hfa
          · exact absurd (List.mem_filter.mpr ⟨ha, hfa⟩) hn
        · exact hbs a ha)
  intro x hx
  rcases hW x (by simpa using hx) with h | ⟨a, ha, hwa⟩
  · exact Or.inl h
  · rw [List.mem_filter] at ha
    exact Or.inr ⟨a, ha.1, ha.2, by simp [ha.1], hwa⟩

/-- **At a call** (a `JUMP` on a nonzero constant, not forward, not a return) of a body of atoms,
calls, conditional calls (on no cell of a nonzero constant) and returns: `pair_callC`'s conclusion,
and the `call` among the body's statements. -/
theorem pair_callLC {X : AlignCtx} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hok : pairOk X H O S body code d = true) {i : ℕ} {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos) {oc od of : ℕ}
    (hci : code[i]? = some (.jump oc od of)) (hz : X.zeroAt oc = false) (hnz : X.nzAt oc = true)
    (hf : fwdJ X i oc od of = false) (hnr : ¬ (od = 0 ∧ of = 1)) (hm : X.main = false) (hsf : X.selfAt of = false)
    (hst : ∀ s ∈ stmtsOf body, loopStmtC s = true)
    (hcif : ∀ c f args, Stmt.callIf c f args ∈ stmtsOf body → X.nzAt (X.locAt c.idx) = false) :
    ∃ f args rets s t o pos', Stmt.call f args rets ∈ stmtsOf body ∧ X.siteAt of args rets = some s ∧
      X.pcAt od = some t ∧ X.entOk t f = true ∧
      X.fwdOff i s.r = some o ∧ pairAt (PairCtx.ofH X H O S) body code d o = some pos' ∧
      ∃ as : List Atom, List.Forall₂ (Pairs X) (as.filter flowAtom)
        (((d.2.2.lookup (X.entry + i)).getD []).filter isaFlowHint) ∧
      ∀ {sigOf : String → HSig} {rd : Reader} {ws0 : List E} {σ : Val} {pre es : List Ev} {vs : List V},
        walk σ pos = .ret es vs → ReadsAt sigOf H rd σ ws0 pre es →
        ∃ (evs : List Ev) (cs : List Atom) (es' : List Ev), es = evs ++ Ev.call f args rets :: (cs.map Ev.atom ++ es') ∧
          walk σ pos' = .ret es' vs ∧
          (∀ a ∈ cs, stopL a = false) ∧ (∀ a ∈ as, Ev.atom a ∈ evs) ∧
          (∀ e ∈ evs, EvM sigOf rd σ e) ∧ ∀ x, WrittenC sigOf H rd σ ws0 (pre ++ evs) x → WrittenC sigOf H rd σ ws0 pre x ∨
            ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x := by
  obtain ⟨ins, z, as, hins, -, hpos, hq, hpairs, hcase⟩ := pairAt_step hok hat
  rw [hci] at hins
  cases hins
  rcases hcase with ⟨hnj, -⟩ | ⟨oc', od', of', zs, heq, -, -, -, hzs, ⟨bs, hzpos, hbs⟩, tabs, r, hr, -, h2, -⟩
  · exact absurd rfl (hnj oc od of)
  simp only [OffsetInstruction.jump.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hr' := hr
  unfold jumpStepH at hr
  simp only [PairCtx.ofH, hz, hf, Bool.cond_false] at hr
  rcases hcur : zs.cur with _ | ⟨st, ss⟩
  · simp [headStepH, hcur] at hr
  have hs : st ∈ stmtsOf body := zok_stmts hzs (by rw [Bridge.Zip.pos_head hcur]; exact List.mem_cons_self)
  obtain ⟨f, args, rets, rfl⟩ : ∃ f args rets, st = .call f args rets := by
    cases st with
    | atom a => simp [headStepH, hcur] at hr
    | ret vs' =>
      simp only [headStepH, hcur, hm, Bool.and_eq_true, Nat.beq_eq, Bool.cond_eq_ite] at hr
      split_ifs at hr <;> simp_all
    | ite c z n => simp [headStepH, hcur, hsf] at hr
    | match_ x arms => simp [headStepH, hcur, hsf] at hr
    | callIf c f args =>
      have hh := headH_of hr' hz hf
      have hloc := (headH_callIf hh hcur).1
      simp only [PairCtx.ofH] at hloc
      have := hcif c f args hs
      rw [hloc, hnz] at this
      cases this
    | dispatch x fs args rets => exact absurd (hst _ hs) (by simp [loopStmtC])
    | call f args rets => exact ⟨f, args, rets, rfl⟩
  simp only [headStepH, hcur] at hr
  rcases hsite : X.siteAt of args rets with _ | s
  · simp [hsite] at hr
  rcases hpt : X.pcAt od with _ | t
  · simp [hsite, hpt] at hr
  rcases hc : (PairCtx.ofH X H O S).nL (zs.next ss) with _ | c
  · simp [PairCtx.ofH] at hc; simp [hsite, hpt, hc] at hr
  simp only [PairCtx.ofH] at hc
  simp only [hsite, hpt, hc, Bool.cond_eq_ite, Bool.and_eq_true] at hr
  split_ifs at hr with hh
  · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hr
    have hat' := h2 (o, c) List.mem_cons_self
    obtain ⟨cs, hcs, hcpos, -⟩ := normG_pos _ _ hc
    refine ⟨f, args, rets, s, t, o, c.pos, hs, hsite, rfl, hh.2, ho, hat', as, hpairs,
      fun {sigOf rd ws0 σ pre es vs} hp hrw ↦ ?_⟩
    rw [hpos, hzpos, Bridge.Zip.pos_head hcur, hcpos, ← List.append_assoc, ← List.map_append] at hp
    obtain ⟨es1, hes1, rfl⟩ := walk_atoms_ret hp
    rw [Bridge.walk_call_cons] at hes1
    obtain ⟨es2, hes2, rfl⟩ := pre_eq_ret hes1
    obtain ⟨es3, hes3, rfl⟩ := walk_atoms_ret hes2
    refine ⟨(as ++ bs).map Ev.atom, cs, es3, by simp, hes3, hcs, fun a ha ↦ by simp [ha], evM_atoms _, fun x hx ↦ ?_⟩
    have hqa : ∀ a ∈ as ++ bs, a ∉ as.filter flowAtom → stopS H.readT a = false := by
      intro a ha hn
      rcases List.mem_append.mp ha with ha | ha
      · cases hfa : flowAtom a
        · exact hq a ha hfa
        · exact absurd (List.mem_filter.mpr ⟨ha, hfa⟩) hn
      · exact hbs a ha
    rcases written_extendC (fs := as.filter flowAtom) (rest := Ev.call f args rets :: (cs.map Ev.atom ++ es3))
        (by simpa [List.append_assoc] using hrw) hqa hx with h | ⟨a, ha, hwa⟩
    · exact Or.inl h
    · rw [List.mem_filter] at ha
      exact Or.inr ⟨a, ha.1, ha.2, by simp [ha.1], hwa⟩

end

end LeanVM.Guest.CoreMode
