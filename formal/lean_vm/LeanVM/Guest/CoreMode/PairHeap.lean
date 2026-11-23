/-
  LeanVM.Guest.CoreMode.PairHeap

  The pairing by positions and what it gives the heap facts: at each offset the path's events
  before its position are those whose instructions have run, so at a `DEREF` the oracle names the
  heap cell it reads is written before it.
-/

module

public import LeanVM.Guest.CoreMode.PairSound
public import LeanVM.Guest.Bridge.Track
public import LeanVM.Guest.Bridge.Prefix

/-!
# The pairing by positions

`pairAt_step`: at an offset the pass reaches, its position is the atoms its hints consume (the flow ones compiling its flow hints one for one; the others not stores, `stopS`), then either

* a `DEREF o1 o2 o3 .cell` consuming a `load` at its cells past reads (the oracle: offset in `O` iff a read, in `S` iff a store), the next offset at the position past it and atoms that write nothing;
* another instruction, the next offset at the same position, the offset in neither `O` nor `S`;
* a jump from the position past its reads, the offset in neither, its successors recorded as `Bridge.alignAt_step`'s.

What it gives the heap facts (`formal/notes/core-mode.md`, `CoreAt`), the frame's events split at the position (`walk σ pos = .ret es vs`, the events before it `pre`), is `PairC.lean`'s: atoms that are no stores (`stopS`) add no address to what is written but those written already (`written_extendC`); at an offset in `O`, its `DEREF` reads the cell of a read `load` at its cells (`pair_readC`); past an instruction other than a jump, the next offset's split is the events of this one's hints, its `load` and atoms that write nothing (`pair_fallC`); and at a jump, the events up to the position it jumps from are its hints' and reads (`pair_jump`, `PairJump.lean`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Bridge
open LeanVM.Guest.Exec (natSeq natSeq_eq)
open LeanVM.Guest.Check (getF)

public section

/-! ## Normalization and steps, by positions -/

/-- The head of a zipper, if an atom, is one `stop` keeps. -/
@[expose] def HeadStop (stop : Atom → Bool) (z : Zip) : Prop := ∀ a ss, z.cur = .atom a :: ss → stop a = true

/-- **The normalization skips the atoms `stop` rejects**: the position is theirs, then the normalized
one's. -/
theorem normG_pos (stop : Atom → Bool) : ∀ (f : ℕ) {z z' : Zip}, normG stop f z = some z' →
    ∃ as : List Atom, (∀ a ∈ as, stop a = false) ∧ z.pos = as.map Stmt.atom ++ z'.pos ∧ HeadStop stop z'
  | 0, _, _, h => by simp [normG] at h
  | f + 1, z, z', h => by
    rw [normG_succ] at h
    obtain ⟨up, k, cur⟩ := z
    cases cur with
    | cons s ss =>
      cases s
      case atom a =>
        simp only [normStepG] at h
        cases hf : stop a <;> simp only [hf, natSeq_eq, Bool.cond_false, Bool.cond_true] at h
        · obtain ⟨as, h1, h2, h3⟩ := normG_pos stop f h
          refine ⟨a :: as, fun b hb ↦ ?_, ?_, h3⟩
          · rcases List.mem_cons.mp hb with rfl | hb
            · exact hf
            · exact h1 b hb
          · rw [Zip.pos_cons, h2]; rfl
        · cases h
          refine ⟨[], by simp, rfl, fun b ss' hb ↦ ?_⟩
          simp only [List.cons.injEq, Stmt.atom.injEq] at hb
          rw [← hb.1]; exact hf
      all_goals
        simp only [normStepG, Option.some.injEq] at h
        subst h
        exact ⟨[], by simp, rfl, fun b ss' hb ↦ by simp at hb⟩
    | nil =>
      cases up with
      | nil =>
        simp only [normStepG, Option.some.injEq] at h
        subst h
        exact ⟨[], by simp, rfl, fun b ss' hb ↦ by simp at hb⟩
      | cons e up =>
        obtain ⟨k', c, ss⟩ := e
        simp only [normStepG, natSeq_eq] at h
        obtain ⟨as, h1, h2, h3⟩ := normG_pos stop f h
        exact ⟨as, h1, by rw [← h2]; simp [Zip.pos], h3⟩

theorem stopS_of_stopL {R : Exec.Trie (List (ℕ × ℕ × Wit))} {a : Atom} (h : stopL a = false) : stopS R a = false := by
  simp only [stopL, Bool.or_eq_false_iff] at h
  simp [stopS, h.1, h.2]

theorem flow_of_stopS {R : Exec.Trie (List (ℕ × ℕ × Wit))} {a : Atom} (h : stopS R a = false) : flowAtom a = false := by
  simp only [stopS, Bool.or_eq_false_iff] at h
  exact h.1

/-- **The hints at an offset consume their atoms**: the position is atoms then the one after the
hints, the flow ones compiling the flow hints one for one, the others no stores. -/
theorem hintsStepH_pos (P : PairCtx) : ∀ (hs : List Prover.Exec.Hint) {z z' : Zip}, hintsStepH P hs z = some z' →
    ∃ as : List Atom, z.pos = as.map Stmt.atom ++ z'.pos ∧ (∀ a ∈ as, flowAtom a = false → stopS P.R a = false) ∧
      List.Forall₂ (Pairs P.X) (as.filter flowAtom) (hs.filter isaFlowHint)
  | [], _, _, h => by cases h; exact ⟨[], rfl, by simp, by simp⟩
  | hd :: hs, z, z', h => by
    change hintStepH P (hintsStepH P hs) hd z = some z' at h
    simp only [hintStepH, Bool.cond_eq_ite] at h
    split at h
    · rename_i hfl
      obtain ⟨z1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨as1, ha1, hp1, hs1⟩ := normG_pos _ _ h1
      split at h
      · rename_i hc ss heq
        split at h
        · rename_i hcomp
          obtain ⟨z2, h2, h3⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨as2, ha2, hp2, -⟩ := normG_pos _ _ h2
          obtain ⟨as3, hp3, hq3, hf3⟩ := hintsStepH_pos P hs h3
          have hflow : flowAtom (.hint hc) = true := by
            have := hs1 _ _ heq
            simpa [stopS, isLoad] using this
          refine ⟨as1 ++ .hint hc :: (as2 ++ as3), ?_, ?_, ?_⟩
          · obtain ⟨up, k, cur⟩ := z1
            simp only at heq
            subst heq
            simp only [Zip.next_eq] at hp2
            rw [hp1, Zip.pos_cons, hp2, hp3]
            simp [List.map_append, List.append_assoc]
          · intro a ha hfa
            rcases List.mem_append.mp ha with ha | ha
            · exact ha1 a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · rw [hflow] at hfa; cases hfa
            rcases List.mem_append.mp ha with ha | ha
            · exact stopS_of_stopL (ha2 a ha)
            · exact hq3 a ha hfa
          · have hf1 : as1.filter flowAtom = [] :=
              List.filter_eq_nil_iff.mpr fun a ha ↦ by simp [flow_of_stopS (ha1 a ha)]
            have hf2 : as2.filter flowAtom = [] :=
              List.filter_eq_nil_iff.mpr fun a ha ↦ by
                simp [flow_of_stopS (stopS_of_stopL (R := P.R) (ha2 a ha))]
            rw [List.filter_append, hf1, List.nil_append, List.filter_cons_of_pos hflow, List.filter_append, hf2,
              List.nil_append, List.filter_cons_of_pos hfl]
            exact List.Forall₂.cons ⟨hc, rfl, hcomp⟩ hf3
        · cases h
      · cases h
    · rename_i hfl
      obtain ⟨as, h1, h2, h3⟩ := hintsStepH_pos P hs h
      refine ⟨as, h1, h2, ?_⟩
      rw [List.filter_cons_of_neg hfl]
      exact h3

/-- **A `DEREF`'s scan by positions**: reads (and atoms between that are no heap events), the `load`
at its cells, atoms that are no heap events, then the position after. -/
theorem scan_pos (P : PairCtx) (o1 o2 o3 : ℕ) : ∀ (f : ℕ) {z : Zip} {r : Zip × Bool}, scan P o1 o2 o3 f z = some r →
    ∃ (bs : List Atom) (d p : V) (off : ℕ) (cs : List Atom),
      z.pos = bs.map Stmt.atom ++ .atom (.load d p off) :: (cs.map Stmt.atom ++ r.1.pos) ∧
      (∀ a ∈ bs, stopS P.R a = false) ∧ (∀ a ∈ cs, stopL a = false) ∧ cellsAt P.X o1 o2 o3 d p off = true ∧
      r.2 = isRead P.R (.load d p off)
  | 0, _, _, h => by simp [scan] at h
  | f + 1, z, r, h => by
    change scanStep P o1 o2 o3 (scan P o1 o2 o3 f) z = some r at h
    simp only [scanStep, Bool.cond_eq_ite] at h
    split at h
    · rename_i d p off ss heq
      have hz : z.pos = .atom (.load d p off) :: (z.next ss).pos := by
        obtain ⟨up, k, cur⟩ := z
        simp only at heq
        subst heq
        rw [Zip.pos_cons, Zip.next_eq]
      split at h
      · rename_i hc
        obtain ⟨z', h1, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨cs, hcs, hp, -⟩ := normG_pos _ _ h1
        exact ⟨[], d, p, off, cs, by rw [hz, ← hp]; rfl, by simp, hcs, hc, rfl⟩
      · split at h
        · rename_i hrd
          obtain ⟨z1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨cs1, hcs1, hp1, -⟩ := normG_pos _ _ h1
          obtain ⟨bs, d', p', off', cs, hp2, hb, hc, hcell, hr⟩ := scan_pos P o1 o2 o3 f h2
          refine ⟨.load d p off :: (cs1 ++ bs), d', p', off', cs, ?_, ?_, hc, hcell, hr⟩
          · rw [hz, hp1, hp2]; simp [List.map_append, List.append_assoc]
          · intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · simp [stopS, flowAtom, isLoad, hrd]
            rcases List.mem_append.mp ha with ha | ha
            · exact stopS_of_stopL (hcs1 a ha)
            · exact hb a ha
        · cases h
    · cases h

theorem kindOk_some {P : PairCtx} {i : ℕ} {b : Bool} (h : P.kindOk i (some b) = true) :
    hasP P.O i = b ∧ hasP P.S i = !b := by
  cases b <;> simp_all [PairCtx.kindOk]

theorem kindOk_none {P : PairCtx} {i : ℕ} (h : P.kindOk i none = true) : hasP P.O i = false ∧ hasP P.S i = false := by
  simp_all [PairCtx.kindOk]

/-- **An instruction other than a jump, by positions**: a `DEREF` of mode `cell` consuming the `load`
at its cells past reads, the oracle naming it a read or a store; or nothing, the oracle naming
neither. -/
theorem plainStep_pos {P : PairCtx} {i : ℕ} {ins : OffsetInstruction} {z z' : Zip} (h : plainStep P i ins z = some z') :
    (∃ (o1 o2 o3 : ℕ) (bs : List Atom) (d p : V) (off : ℕ) (cs : List Atom), ins = .deref o1 o2 o3 .cell ∧
      z.pos = bs.map Stmt.atom ++ .atom (.load d p off) :: (cs.map Stmt.atom ++ z'.pos) ∧
      (∀ a ∈ bs, stopS P.R a = false) ∧ (∀ a ∈ cs, stopL a = false) ∧ cellsAt P.X o1 o2 o3 d p off = true ∧
      hasP P.O i = isRead P.R (.load d p off) ∧ hasP P.S i = !isRead P.R (.load d p off)) ∨
    (z' = z ∧ hasP P.S i = false ∧ (hasP P.O i = false ∨
      ∃ o1 o2 o3, ins = .deref o1 o2 o3 .cell ∧ jtd P.X o1 o2 o3 = true)) := by
  unfold plainStep at h
  split at h
  · rename_i o1 o2 o3
    split at h
    · rename_i z1 b hs
      simp only [Bool.cond_eq_ite] at h
      split at h
      · rename_i hk
        cases h
        obtain ⟨bs, d, p, off, cs, hp, hb, hc, hcell, hr⟩ := scan_pos P o1 o2 o3 _ hs
        simp only at hr hp
        subst hr
        exact Or.inl ⟨o1, o2, o3, bs, d, p, off, cs, rfl, hp, hb, hc, hcell, kindOk_some hk⟩
      · cases h
    · simp only [Bool.cond_eq_ite] at h
      split at h
      · rename_i hk
        cases h
        rcases Bool.or_eq_true_iff.mp hk with hk | hk
        · exact Or.inr ⟨rfl, (kindOk_none hk).2, Or.inl (kindOk_none hk).1⟩
        · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
          exact Or.inr ⟨rfl, hk.2, Or.inr ⟨o1, o2, o3, rfl, hk.1⟩⟩
      · cases h
  · simp only [Bool.cond_eq_ite] at h
    split at h
    · rename_i hk; cases h; exact Or.inr ⟨rfl, (kindOk_none hk).2, Or.inl (kindOk_none hk).1⟩
    · cases h

/-! ## The pairing at an offset -/

/-- **The pairing at an offset it reaches**, by positions (see the module doc). -/
theorem pairAt_step {X : AlignCtx} {H : HCert} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hok : pairOk X H O S body code d = true) {i : ℕ} {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos) :
    ∃ ins z, ∃ as : List Atom, code[i]? = some ins ∧ ZOk body z ∧ pos = as.map Stmt.atom ++ z.pos ∧
      (∀ a ∈ as, flowAtom a = false → stopS H.readT a = false) ∧
      List.Forall₂ (Pairs X) (as.filter flowAtom) (((d.2.2.lookup (X.entry + i)).getD []).filter isaFlowHint) ∧
      (((∀ oc od of, ins ≠ .jump oc od of) ∧
        ((∃ (o1 o2 o3 : ℕ) (bs : List Atom) (dv pv : V) (off : ℕ) (cs : List Atom) (pos' : List Stmt),
            ins = .deref o1 o2 o3 .cell ∧
            z.pos = bs.map Stmt.atom ++ .atom (.load dv pv off) :: (cs.map Stmt.atom ++ pos') ∧
            (∀ a ∈ bs, stopS H.readT a = false) ∧ (∀ a ∈ cs, stopL a = false) ∧
            cellsAt X o1 o2 o3 dv pv off = true ∧
            pairAt (PairCtx.ofH X H O S) body code d (i + 1) = some pos' ∧
            hasP O i = (H.readWit dv pv off).isSome ∧ hasP S i = !(H.readWit dv pv off).isSome) ∨
          (pairAt (PairCtx.ofH X H O S) body code d (i + 1) = some z.pos ∧ hasP S i = false ∧
            (hasP O i = false ∨ ∃ o1 o2 o3, ins = .deref o1 o2 o3 .cell ∧ jtd X o1 o2 o3 = true)))) ∨
      ∃ oc od of zs, ins = .jump oc od of ∧ hasP O i = false ∧ hasP S i = false ∧
        (PairCtx.ofH X H O S).nS z = some zs ∧ ZOk body zs ∧
        (∃ bs : List Atom, z.pos = bs.map Stmt.atom ++ zs.pos ∧ ∀ a ∈ bs, stopS H.readT a = false) ∧
        ∃ tabs r, jumpStepH (PairCtx.ofH X H O S) i oc od of tabs z zs = some r ∧
          (∀ z1 ∈ r.1, pairAt (PairCtx.ofH X H O S) body code d (i + 1) = some z1.pos) ∧
          (∀ p ∈ r.2, pairAt (PairCtx.ofH X H O S) body code d p.1 = some p.2.pos) ∧
          ∀ x arms ss a, zs.cur = .match_ x arms :: ss → X.zeroAt oc = false →
            fwdJ X i oc od of = false → getF X.arms od = some a →
            ∀ j < arms.length, ∃ t, getF X.jt (a.2 + j) = some t ∧ X.entry + i < t ∧ ∃ c',
              (PairCtx.ofH X H O S).nL (zs.enter (.match_ x arms) ss j) = some c' ∧
              pairAt (PairCtx.ofH X H O S) body code d (t - X.entry) = some c'.pos) := by
  obtain ⟨hpre, l, hl⟩ := pairOk_iff.mp hok
  set P := PairCtx.ofH X H O S with hP
  have hlk : (l.lookup i).map Zip.pos = some pos := by
    simpa only [pairAt, hl, Option.bind_some] using hat
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hlk
  obtain ⟨ins, z0, z, hins, hcok, hz0, hz, hzok, hcase⟩ := pairRun_step (P := P) hpre hl (mem_of_lookup hc)
  obtain ⟨as1, ha1, hp1, -⟩ := normG_pos _ _ hz0
  obtain ⟨as2, hp2, hq2, hf2⟩ := hintsStepH_pos P _ hz
  refine ⟨ins, z, as1 ++ as2, hins, hzok, ?_, ?_, ?_, ?_⟩
  · rw [hp1, hp2, List.map_append, List.append_assoc]
  · intro a ha hfa
    rcases List.mem_append.mp ha with ha | ha
    · exact stopS_of_stopL (ha1 a ha)
    · exact hq2 a ha hfa
  · have hf : as1.filter flowAtom = [] :=
      List.filter_eq_nil_iff.mpr fun a ha ↦ by simp [flow_of_stopS (stopS_of_stopL (R := P.R) (ha1 a ha))]
    rw [List.filter_append, hf, List.nil_append]
    exact hf2
  rcases hcase with ⟨oc, od, of, zs, tabs, r, rfl, hk, hzs, hr, h1, h2, h3⟩ | ⟨hnj, z', hz', harr⟩
  · have hzsok : ZOk body zs := P.nS_ok hzok hzs
    obtain ⟨bs, hbs, hpz, -⟩ := normG_pos _ _ hzs
    have hout : OutOk body r := jumpStepH_ok P i oc od of tabs hzok hzsok hr
    refine Or.inr ⟨oc, od, of, zs, rfl, (kindOk_none hk).1, (kindOk_none hk).2, hzs, hzsok, ⟨bs, hpz, hbs⟩, tabs, r, hr,
      fun z1 hz1 ↦ pairAt_of_arr hpre hl (h1 z1 hz1) (hout.1 z1 hz1),
      fun p hp ↦ pairAt_of_arr hpre hl (h2 p hp) (hout.2 p hp), ?_⟩
    intro x arms ss a hzc hzero hfwd ha j hj
    obtain ⟨t, c', ht, hc', harr, hlt⟩ := h3 x arms ss a hzc hzero hfwd ha j hj
    exact ⟨t, ht, hlt, c', hc', pairAt_of_arr hpre hl harr (P.nL_ok (hzsok.enter hzc j) hc')⟩
  · have hz'ok : ZOk body z' := plainStep_ok P i ins hzok hz'
    have hat' := pairAt_of_arr hpre hl harr hz'ok
    refine Or.inl ⟨hnj, ?_⟩
    rcases plainStep_pos hz' with ⟨o1, o2, o3, bs, dv, pv, off, cs, rfl, hpz, hb, hcs, hcell, hO, hS⟩ |
      ⟨rfl, hO, hS⟩
    · exact Or.inl ⟨o1, o2, o3, bs, dv, pv, off, cs, z'.pos, rfl, hpz, hb, hcs, hcell, hat', hO, hS⟩
    · exact Or.inr ⟨hat', hO, hS⟩

/-! ## Heap facts -/

/-- **An atom that is no store writes only what it reads**: a read's cell; any other writes nothing. -/
theorem reads_of_writes {H : HCert} {σ : Val} {a : Atom} (hq : stopS H.readT a = false) {x : K}
    (hw : Writes σ a x) : Reads H σ a x := by
  cases a with
  | load d p off =>
    simp only [stopS, flowAtom, isLoad, isRead, Bool.false_or, Bool.true_and, Bool.not_eq_false'] at hq
    exact ⟨hq, hw⟩
  | hint h =>
    have hf : coreFlow h = false := by simpa [stopS, flowAtom, isLoad] using hq
    cases h <;> simp_all [coreFlow, Writes, hintHeap]
  | _ => exact absurd hw (by simp [Writes])

/-- Atoms that are no heap events write nothing. -/
theorem no_writes_of_stopL {σ : Val} {a : Atom} (h : stopL a = false) {x : K} : ¬ Writes σ a x := by
  intro hw
  have hS : stopS (.nil : Exec.Trie (List (ℕ × ℕ × Wit))) a = false := stopS_of_stopL h
  have hr := reads_of_writes (H := { sig := HSig.empty, reads := [], res := [] }) (by simpa [HCert.readT] using hS) hw
  cases a with
  | load d p off => simp [stopL, isLoad] at h
  | hint h' => simp [Reads] at hr; split at hr <;> simp_all [stopL, flowAtom, coreFlow]
  | _ => simp [Reads] at hr

/-- Atoms, then statements: the path is the atoms', then the statements'. -/
theorem walk_atoms_ret {σ : Val} {as : List Atom} {ss : List Stmt} {es : List Ev} {vs : List V}
    (h : walk σ (as.map Stmt.atom ++ ss) = .ret es vs) : ∃ es', walk σ ss = .ret es' vs ∧ es = as.map Ev.atom ++ es' := by
  rw [Bridge.walk_atoms] at h
  exact pre_eq_ret h

end

end LeanVM.Guest.CoreMode
