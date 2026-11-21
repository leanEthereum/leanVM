/-
  LeanVM.Guest.CoreMode.PairLoop

  The pairing at a loop helper's tail call and return.
-/

module

public import LeanVM.Guest.CoreMode.PairJumpC

/-!
# The pairing at a loop helper's jumps

For a body whose statements are atoms, calls, conditional calls, returns, branches and `match`es
(`loopStmtC`): at a `JUMP` through a next-frame cell
(`pair_tailL`), the pairing takes it by a `callIf`, the next offset's position a closing `ret []`, the
events to there its hints' atoms and reads, the condition, the call entered or skipped, atoms writing
nothing; at a return jump (`pair_retL`), `pair_retC`'s conclusion.
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
`0`), the body's statements atoms, calls, conditional calls, returns, branches and `match`es, its condition at no nonzero constant's
cell: the pairing takes it by a `callIf` of the body, the next offset's position the closing `ret []`,
the events to there its hints' atoms and reads, the condition, the call entered or skipped, atoms writing nothing. -/
theorem pair_tailL {X : AlignCtx} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hok : pairOk X H O S body code d = true) {i : ℕ} {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos) {oc od of : ℕ}
    (hci : code[i]? = some (.jump oc od of)) (hz : X.zeroAt oc = false) (hnz : X.nzAt oc = false)
    (hsf : X.selfAt of = false) (hnx : X.nextAt of = true) (hod : od ≠ 0)
    (hst : ∀ s ∈ stmtsOf body, loopStmtC s = true) :
    ∃ c f args pos', Stmt.callIf c f args ∈ stmtsOf body ∧ X.locAt c.idx = oc ∧
      (∃ t, X.pcAt od = some t ∧ X.entOk t f = true) ∧
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
  obtain ⟨hloc, t, ca, hpt, hent, hca, rfl, hcase⟩ := headH_callIf hh hcur
  have hrn : retNil ca.pos = true := by
    rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · simp only [PairCtx.ofH] at h; rw [hnx] at h; cases h
  refine ⟨c, f, args, ca.pos, hs, hloc, ⟨t, hpt, hent⟩, h1 ca rfl, hrn, as, hpairs,
    fun {sigOf rd ws0 σ pre es vs} hp hrw ↦ ?_⟩
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
body of atoms, calls, conditional calls, returns, branches and `match`es: `pair_retC`'s conclusion. -/
theorem pair_retL {X : AlignCtx} {O S : Exec.Trie Unit} {body : List Stmt}
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

end

end LeanVM.Guest.CoreMode
