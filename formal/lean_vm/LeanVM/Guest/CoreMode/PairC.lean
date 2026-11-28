/-
  LeanVM.Guest.CoreMode.PairC

  The pairing by positions over the heap check with calls: `PairHeap`'s facts with `WrittenC` and
  `ReadsOkC`, and the pairing at a call.
-/

module

public import LeanVM.Guest.CoreMode.PairHeap
public import LeanVM.Guest.CoreMode.HeapC
public import LeanVM.Guest.Bridge.JumpCellsSound
public import LeanVM.Guest.Bridge.AlignJump

/-!
# The pairing over `WrittenC`

`pairAt_step`'s cases (`PairHeap.lean`) for a path whose events' needs are written before them in the sense
of the check with calls (`ReadsOkC`), the written cells `WrittenC` (a call's callee guarantees count): atoms
that are no stores add only what is written already (`written_extendC`, `atoms_writtenC`), a `DEREF` at an
offset of the oracle reads a cell written before it (`pair_readC`), a fall-through's next split
(`pair_fallC`), the return (`pair_retC`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Bridge
open LeanVM.Guest.Exec (natSeq natSeq_eq)
open LeanVM.Guest.Check (getF)

public section

variable {sigOf : String → HSig} {H : HCert} {rd : Reader} {σ : Val} {ws0 : List E}

theorem writtenC_append {a b : List Ev} {x : K} (h : WrittenC sigOf H rd σ ws0 (a ++ b) x) :
    WrittenC sigOf H rd σ ws0 a x ∨ ∃ e ∈ b, EvW sigOf rd σ e x := by
  rcases h with h | ⟨e, he, hw⟩
  · exact Or.inl (Or.inl h)
  · rcases List.mem_append.mp he with he | he
    · exact Or.inl (Or.inr ⟨e, he, hw⟩)
    · exact Or.inr ⟨e, he, hw⟩

theorem writtenC_left {a b : List Ev} {x : K} (h : WrittenC sigOf H rd σ ws0 a x) :
    WrittenC sigOf H rd σ ws0 (a ++ b) x := by
  rcases h with h | ⟨e, he, hw⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, List.mem_append_left _ he, hw⟩

/-- **Atoms that are no stores add nothing to `WrittenC`** on a path whose needs are written before
them, but those among `fs`. -/
theorem written_extendC {fs : List Atom} : ∀ {as : List Atom} {pre rest : List Ev},
    ReadsAt sigOf H rd σ ws0 pre (as.map Ev.atom ++ rest) → (∀ a ∈ as, a ∉ fs → stopS H.readT a = false) →
      ∀ {x : K}, WrittenC sigOf H rd σ ws0 (pre ++ as.map Ev.atom) x → WrittenC sigOf H rd σ ws0 pre x ∨
        ∃ a ∈ fs, Writes σ a x
  | [], pre, _, _, _, x, hx => Or.inl (by simpa using hx)
  | a :: as, pre, rest, hrw, hq, x, hx => by
    have hrw' : ReadsAt sigOf H rd σ ws0 (pre ++ [Ev.atom a]) (as.map Ev.atom ++ rest) :=
      ReadsAt.shift (X := [Ev.atom a]) hrw fun e he ↦ by rw [List.mem_singleton.mp he]; trivial
    have hx' : WrittenC sigOf H rd σ ws0 ((pre ++ [Ev.atom a]) ++ as.map Ev.atom) x := by
      simpa [List.append_assoc] using hx
    rcases written_extendC hrw' (fun b hb hn ↦ hq b (List.mem_cons_of_mem _ hb) hn) hx' with h | h
    · rcases writtenC_append h with h | ⟨e, he, hw⟩
      · exact Or.inl h
      · rw [List.mem_singleton] at he
        subst he
        by_cases hf : a ∈ fs
        · exact Or.inr ⟨a, hf, hw⟩
        · exact Or.inl (ReadsAt.head (es := as.map Ev.atom ++ rest) hrw
            x (reads_of_writes (hq a List.mem_cons_self hf) hw))
    · exact Or.inr h

/-- **Atoms on the path add to `WrittenC` only what those among `fs` write.** -/
theorem atoms_writtenC {fs as : List Atom} {ss : List Stmt} {pre es : List Ev} {vs : List V}
    (hp : walk σ (as.map Stmt.atom ++ ss) = .ret es vs) (hrw : ReadsAt sigOf H rd σ ws0 pre es)
    (hq : ∀ a ∈ as, a ∉ fs → stopS H.readT a = false) :
    ∃ es', walk σ ss = .ret es' vs ∧ es = as.map Ev.atom ++ es' ∧
      ∀ x, WrittenC sigOf H rd σ ws0 (pre ++ as.map Ev.atom) x → WrittenC sigOf H rd σ ws0 pre x ∨
        ∃ a ∈ fs, Writes σ a x := by
  obtain ⟨es', hes', rfl⟩ := walk_atoms_ret hp
  exact ⟨es', hes', rfl, fun x hx ↦ written_extendC (rest := es') (by simpa [List.append_assoc] using hrw) hq hx⟩

/-- **At an offset of the oracle, the heap cell its `DEREF` reads is written**, over `WrittenC`. -/
theorem pair_readC {X : AlignCtx} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hok : pairOk X H O S body code d = true) {i : ℕ} {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos) {o1 o2 o3 : ℕ}
    (hins : code[i]? = some (.deref o1 o2 o3 .cell)) (hO : hasP O i = true) (hjt : jtd X o1 o2 o3 = false)
    {pre es : List Ev} {vs : List V} (hp : walk σ pos = .ret es vs)
    (hrw : ReadsAt sigOf H rd σ ws0 pre es) :
    ∃ (as : List Atom) (dv pv : V) (off : ℕ),
      List.Forall₂ (Pairs X) (as.filter flowAtom) (((d.2.2.lookup (X.entry + i)).getD []).filter isaFlowHint) ∧
      cellsAt X o1 o2 o3 dv pv off = true ∧ (H.readWit dv pv off).isSome ∧ Ev.atom (.load dv pv off) ∈ es ∧
      (WrittenC sigOf H rd σ ws0 pre (cellAt σ pv off) ∨
        ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ es ∧ Writes σ a (cellAt σ pv off)) := by
  obtain ⟨ins, z, as, hins', -, hpos, hq, hpairs, hcase⟩ := pairAt_step hok hat
  rw [hins] at hins'
  cases hins'
  rcases hcase with ⟨-, ⟨o1', o2', o3', bs, dv, pv, off, cs, pos', heq, hz, hb, -, hcell, -, hO', -⟩ | ⟨-, -, hO'⟩⟩ |
    ⟨oc, od, of, -, heq, -⟩
  · simp only [OffsetInstruction.deref.injEq] at heq
    obtain ⟨rfl, rfl, rfl, -⟩ := heq
    have hrd : (H.readWit dv pv off).isSome = true := by rw [← hO', hO]
    rw [hpos, hz, ← List.append_assoc, ← List.map_append] at hp
    obtain ⟨es1, hes1, rfl⟩ := walk_atoms_ret hp
    rw [walk_atom_cons] at hes1
    obtain ⟨es2, -, rfl⟩ := pre_eq_ret hes1
    refine ⟨as, dv, pv, off, hpairs, hcell, hrd, by simp, ?_⟩
    have hR : Reads H σ (.load dv pv off) (cellAt σ pv off) := ⟨hrd, rfl⟩
    have hw := hrw ((as ++ bs).map Ev.atom) (.atom (.load dv pv off)) es2 (by simp) (evM_atoms _) _ hR
    have hqa : ∀ a ∈ as ++ bs, a ∉ as.filter flowAtom → stopS H.readT a = false := by
      intro a ha hn
      rcases List.mem_append.mp ha with ha | ha
      · cases hfa : flowAtom a
        · exact hq a ha hfa
        · exact absurd (List.mem_filter.mpr ⟨ha, hfa⟩) hn
      · exact hb a ha
    rcases written_extendC (fs := as.filter flowAtom) (rest := Ev.atom (.load dv pv off) :: es2)
        (by simpa [List.append_assoc] using hrw) hqa hw with h | ⟨a, ha, hwa⟩
    · exact Or.inl h
    · rw [List.mem_filter] at ha
      exact Or.inr ⟨a, ha.1, ha.2, by simp [ha.1], hwa⟩
  · rcases hO' with hO' | ⟨o1', o2', o3', heq, hj⟩
    · simp [hO] at hO'
    · simp only [OffsetInstruction.deref.injEq] at heq
      obtain ⟨rfl, rfl, rfl, -⟩ := heq
      simp [hjt] at hj
  · cases heq

/-- **Past an instruction other than a jump**, over `WrittenC`. -/
theorem pair_fallC {X : AlignCtx} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hok : pairOk X H O S body code d = true) {i : ℕ} {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos)
    (hnj : ∀ oc od of, code[i]? ≠ some (.jump oc od of)) :
    ∃ pos', pairAt (PairCtx.ofH X H O S) body code d (i + 1) = some pos' ∧ ∃ as : List Atom,
      List.Forall₂ (Pairs X) (as.filter flowAtom) (((d.2.2.lookup (X.entry + i)).getD []).filter isaFlowHint) ∧
      ∀ {σ : Val} {pre es : List Ev} {vs : List V}, walk σ pos = .ret es vs →
        ReadsAt sigOf H rd σ ws0 pre es →
        ∃ evs es', es = evs ++ es' ∧ walk σ pos' = .ret es' vs ∧ (∀ e ∈ evs, EvM sigOf rd σ e) ∧
          ∀ x, WrittenC sigOf H rd σ ws0 (pre ++ evs) x →
          WrittenC sigOf H rd σ ws0 pre x ∨ (∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x) ∨
          ∃ (o1 o2 o3 : ℕ) (dv pv : V) (off : ℕ), code[i]? = some (.deref o1 o2 o3 .cell) ∧ hasP S i = true ∧
            cellsAt X o1 o2 o3 dv pv off = true ∧ Ev.atom (.load dv pv off) ∈ evs ∧ x = cellAt σ pv off := by
  obtain ⟨ins, z, as, hins, -, hpos, hq, hpairs, hcase⟩ := pairAt_step hok hat
  rcases hcase with ⟨-, hc⟩ | ⟨oc, od, of, -, rfl, -⟩
  swap
  · exact absurd hins (hnj oc od of)
  have hfs : ∀ a ∈ as, a ∉ as.filter flowAtom → stopS H.readT a = false := fun a ha hn ↦ by
    cases hfa : flowAtom a
    · exact hq a ha hfa
    · exact absurd (List.mem_filter.mpr ⟨ha, hfa⟩) hn
  have hflow : ∀ {σ : Val} {x : K} {evs : List Ev}, (∀ a ∈ as, Ev.atom a ∈ evs) →
      (∃ a ∈ as.filter flowAtom, Writes σ a x) → ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x :=
    fun hin ⟨a, ha, hw⟩ ↦ by
      rw [List.mem_filter] at ha; exact ⟨a, ha.1, ha.2, hin a ha.1, hw⟩
  rcases hc with ⟨o1, o2, o3, bs, dv, pv, off, cs, pos', rfl, hz, hb, hcs, hcell, hat', -, hS⟩ | ⟨hat', -, -⟩
  · refine ⟨pos', hat', as, hpairs, fun {σ pre es vs} hp hrw ↦ ?_⟩
    have hp' : walk σ ((as ++ bs ++ .load dv pv off :: cs).map Stmt.atom ++ pos') = .ret es vs := by
      rw [← hp, hpos, hz]; simp [List.append_assoc]
    by_cases hr : (H.readWit dv pv off).isSome
    · obtain ⟨es', hes', rfl, hW⟩ := atoms_writtenC (fs := as.filter flowAtom) hp' hrw (fun a ha hn ↦ by
        simp only [List.mem_append, List.mem_cons] at ha
        rcases ha with (ha | ha) | rfl | ha
        · exact hfs a ha hn
        · exact hb a ha
        · simp only [HCert.readWit] at hr
          simp [stopS, flowAtom, isLoad, isRead, hr]
        · exact stopS_of_stopL (hcs a ha))
      refine ⟨(as ++ bs ++ .load dv pv off :: cs).map Ev.atom, es', rfl, hes', evM_atoms _, fun x hx ↦ ?_⟩
      rcases hW x hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (hflow (fun a ha ↦ by simp [ha]) h))
    · obtain ⟨es', hes', rfl, hW⟩ := atoms_writtenC (fs := as.filter flowAtom ++ [.load dv pv off]) hp' hrw
        (fun a ha hn ↦ by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hn
          rcases ha with (ha | ha) | ha | ha
          · exact hfs a ha hn.1
          · exact hb a ha
          · exact absurd ha hn.2
          · exact stopS_of_stopL (hcs a ha))
      refine ⟨(as ++ bs ++ .load dv pv off :: cs).map Ev.atom, es', rfl, hes', evM_atoms _, fun x hx ↦ ?_⟩
      rcases hW x hx with h | ⟨a, ha, hwa⟩
      · exact Or.inl h
      · rcases List.mem_append.mp ha with ha | ha
        · exact Or.inr (Or.inl (hflow (fun a ha ↦ by simp [ha]) ⟨a, ha, hwa⟩))
        · rw [List.mem_singleton] at ha
          subst ha
          exact Or.inr (Or.inr ⟨o1, o2, o3, dv, pv, off, hins, by simpa [hr] using hS, hcell, by simp, hwa⟩)
  · refine ⟨z.pos, hat', as, hpairs, fun {σ pre es vs} hp hrw ↦ ?_⟩
    rw [hpos] at hp
    obtain ⟨es', hes', rfl, hW⟩ := atoms_writtenC (fs := as.filter flowAtom) hp hrw hfs
    refine ⟨as.map Ev.atom, es', rfl, hes', evM_atoms _, fun x hx ↦ ?_⟩
    rcases hW x hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (hflow (fun a ha ↦ by simp [ha]) h))

/-! ## Bodies of atoms, calls and one return -/

/-- **At a return jump** (`od = 0`, `of = 1`, never zero, not forward, cell `0` no constant pc) of
a body of atoms, calls and returns, the events past the position write nothing new but its flow
hints' atoms. -/
theorem pair_retC {X : AlignCtx} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hok : pairOk X H O S body code d = true) {i : ℕ} {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos) {oc : ℕ}
    (hci : code[i]? = some (.jump oc 0 1)) (hz : X.zeroAt oc = false) (hf : fwdJ X i oc 0 1 = false)
    (h0 : X.pcAt 0 = none) (hsf : X.selfAt 1 = false)
    {pre es : List Ev} {vs : List V} (hp : walk σ pos = .ret es vs) (hrw : ReadsAt sigOf H rd σ ws0 pre es) :
    ∃ as : List Atom, List.Forall₂ (Pairs X) (as.filter flowAtom) (((d.2.2.lookup (X.entry + i)).getD []).filter isaFlowHint) ∧
      (∀ e ∈ es, EvM sigOf rd σ e) ∧ ∀ x, WrittenC sigOf H rd σ ws0 (pre ++ es) x → WrittenC sigOf H rd σ ws0 pre x ∨
        ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ es ∧ Writes σ a x := by
  obtain ⟨ins, z, as, hins, -, hpos, hq, hpairs, hcase⟩ := pairAt_step hok hat
  rw [hci] at hins
  cases hins
  rcases hcase with ⟨hnj, -⟩ | ⟨oc', od', of', zs, heq, -, -, -, hzs, ⟨bs, hzpos, hbs⟩, tabs, r, hr, -⟩
  · exact absurd rfl (hnj oc 0 1)
  simp only [OffsetInstruction.jump.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hhead : ∃ vs' ss, zs.cur = .ret vs' :: ss := by
    unfold jumpStepH at hr
    simp only [PairCtx.ofH, hz, hf, Bool.cond_false] at hr
    rcases hcur : zs.cur with _ | ⟨s, ss⟩
    · simp [headStepH, hcur] at hr
    · cases s with
      | atom a => simp [headStepH, hcur] at hr
      | ret vs' => exact ⟨vs', ss, rfl⟩
      | call f args rets =>
        simp only [headStepH, hcur, h0] at hr
        split at hr <;> simp_all
      | ite c z n => simp [headStepH, hcur, hsf] at hr
      | match_ x arms => simp [headStepH, hcur, hsf] at hr
      | callIf c f args => simp [headStepH, hcur, h0] at hr
      | dispatch x fs args rets =>
        simp only [headStepH, hcur] at hr
        split at hr <;> simp_all
  obtain ⟨vs', ss, hcur⟩ := hhead
  refine ⟨as, hpairs, ?_⟩
  rw [hpos, hzpos, ← List.append_assoc, ← List.map_append] at hp
  obtain ⟨es', hes', rfl⟩ := walk_atoms_ret hp
  rw [Bridge.Zip.pos_head hcur, Bridge.walk_ret_cons] at hes'
  simp only [Out.ret.injEq] at hes'
  obtain ⟨rfl, -⟩ := hes'
  obtain ⟨-, -, -, hW⟩ := atoms_writtenC (fs := as.filter flowAtom) (ss := zs.pos) (pre := pre)
    (es := (as ++ bs).map Ev.atom ++ []) (vs := vs) hp hrw (fun a ha hn ↦ by
        rcases List.mem_append.mp ha with ha | ha
        · cases hfa : flowAtom a
          · exact hq a ha hfa
          · exact absurd (List.mem_filter.mpr ⟨ha, hfa⟩) hn
        · exact hbs a ha)
  refine ⟨evM_app (evM_atoms _) evM_nil, fun x hx ↦ ?_⟩
  rcases hW x (by simpa using hx) with h | ⟨a, ha, hwa⟩
  · exact Or.inl h
  · rw [List.mem_filter] at ha
    exact Or.inr ⟨a, ha.1, ha.2, by simp [ha.1], hwa⟩

end

end LeanVM.Guest.CoreMode
