/-
  LeanVM.Guest.CoreMode.PairSound

  What the pairing pass gives at each offset it reaches: the offset's hints consume its position's
  head flow hint atoms past reads, a `DEREF` consumes the `load` at its cells past reads, the oracle
  names the reads' offsets and the stores', and the position after its instruction is recorded at
  each successor.
-/

module

public import LeanVM.Guest.CoreMode.PairRun
public import LeanVM.Guest.Bridge.AlignSound
public import LeanVM.Guest.Bridge.Align

/-!
# The pairing pass's soundness

`Bridge/AlignSound.lean`'s argument for the heap-aware pass, its pending list, hint and table lemmas reused: every arrival pending or falling in at a state is recorded (`pairGo_arr`), each recorded offset was visited at a state of the pass whose invariant (`PInvH`) holds (`pairGo_visit`), so at an offset the pass reaches (`pairRun_step`) the hints consume the normalized position's head flow hint atoms, the instruction steps from there, and what it hands on is recorded at its successors. By positions (`pairAt_step`): the position at an offset is the atoms its hints consume (the flow ones compiling them one for one, the others no store: `stopS`), then either a `DEREF` consuming a `load` at its cells past reads, the oracle naming it a read or a store, the next offset at the position past it; or nothing, the next offset at the same position, the oracle naming neither; or a jump from the position past its reads, its successors' positions recorded.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Bridge
open LeanVM.Guest.Exec (natSeq natSeq_eq)
open LeanVM.Guest.Check (getF)

public section

/-! ## A step's shape -/

/-- **A visit**: the zipper normalized, its hints consumed, then a jump from the position past its
reads, or another instruction. -/
theorem visitH_eq {P : PairCtx} {ins : OffsetInstruction} {i i' : ℕ} {h1 : List Prover.Exec.Hint}
    {hs' : List (ℕ × List Prover.Exec.Hint)} {rest : List (ℕ × Zip)} {tabs : List (ℕ × Zip × ℕ)} {c : Zip}
    {p : St × Option (ℕ × Zip)} (h : visitH P ins i i' h1 hs' rest tabs c = some p) :
    ∃ z0 z, P.nL c = some z0 ∧ hintsStepH P h1 z0 = some z ∧
      ((∃ oc od of zs r, ins = .jump oc od of ∧ P.kindOk i none = true ∧ P.nS z = some zs ∧
          jumpStepH P i oc od of tabs z zs = some r ∧
          p = (⟨i', hs', r.1, mergeP r.2 rest, tabReg P.X i ins zs r.2 tabs⟩, some (i, c))) ∨
        ((∀ oc od of, ins ≠ .jump oc od of) ∧ ∃ z', plainStep P i ins z = some z' ∧
          p = (⟨i', hs', some z', rest, tabs⟩, some (i, c)))) := by
  simp only [visitH] at h
  obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨z1, hz1, hz⟩ := Option.bind_eq_some_iff.mp hz
  refine ⟨z1, z, hz1, hz, ?_⟩
  cases ins
  case jump oc od of h =>
    dsimp only at h
    simp only [Bool.cond_eq_ite] at h
    split at h
    · rename_i hk
      obtain ⟨zs, hzs, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Or.inl ⟨oc, od, of, zs, q, rfl, hk, hzs, hq, rfl⟩
    · cases h
  all_goals
    rename_i h
    dsimp only at h
    obtain ⟨z', hz', rfl⟩ := Option.map_eq_some_iff.mp h
    exact Or.inr ⟨fun _ _ _ h ↦ (by cases h), z', hz', rfl⟩

/-- A visit's result, uniformly: the next offset, the hints left, what falls through, the arrivals
merged into the rest, the tables. -/
theorem visitH_shape {P : PairCtx} {ins : OffsetInstruction} {i i' : ℕ} {h1 : List Prover.Exec.Hint}
    {hs' : List (ℕ × List Prover.Exec.Hint)} {rest : List (ℕ × Zip)} {tabs : List (ℕ × Zip × ℕ)} {c : Zip}
    {p : St × Option (ℕ × Zip)} (h : visitH P ins i i' h1 hs' rest tabs c = some p) :
    ∃ cur tg tabs', p = (⟨i', hs', cur, mergeP tg rest, tabs'⟩, some (i, c)) := by
  obtain ⟨z0, z, hz0, hz, h'⟩ := visitH_eq h
  rcases h' with ⟨oc, od, of, zs, r, hins, hk, hzs, hr, hp⟩ | ⟨hnj, z', hz', hp⟩
  · exact ⟨_, _, _, hp⟩
  · exact ⟨some z', [], tabs, hp⟩

/-- **A step of the pass**: offset `i` not reached, or reached with the zipper falling in or the
first arrival, every arrival there of its cursor. -/
theorem stepIH_eq {P : PairCtx} {ins : OffsetInstruction} {st : St} {p : St × Option (ℕ × Zip)}
    (h : stepIH P ins st = some p) :
    (st.cur = none ∧ (spanP st.i st.pend).1 = [] ∧
      p = (⟨st.i + 1, (hintsAt (Nat.add P.X.entry st.i) st.hs).2, none, (spanP st.i st.pend).2, st.tabs⟩, none)) ∨
    ∃ c, (st.cur = some c ∨ (st.cur = none ∧ ∃ q ∈ (spanP st.i st.pend).1, q.2 = c)) ∧
      allKey (spanP st.i st.pend).1 c = true ∧
      visitH P ins st.i (st.i + 1) (hintsAt (Nat.add P.X.entry st.i) st.hs).1 (hintsAt (Nat.add P.X.entry st.i) st.hs).2
        (spanP st.i st.pend).2 st.tabs c = some p := by
  unfold stepIH at h
  rw [natSeq_eq] at h
  generalize spanP st.i st.pend = S at h ⊢
  generalize hintsAt (Nat.add P.X.entry st.i) st.hs = H at h ⊢
  obtain ⟨here, rest⟩ := S
  obtain ⟨h1, hs'⟩ := H
  simp only [Bool.cond_eq_ite] at h
  cases hcur : st.cur with
  | some c =>
    simp only [hcur] at h
    split at h
    · exact Or.inr ⟨c, Or.inl rfl, by assumption, h⟩
    · cases h
  | none =>
    simp only [hcur] at h
    cases here with
    | nil => cases h; exact Or.inl ⟨rfl, rfl, rfl⟩
    | cons q qs =>
      simp only at h
      split at h
      · exact Or.inr ⟨q.2, Or.inr ⟨rfl, q, List.mem_cons_self, rfl⟩, by assumption, h⟩
      · cases h

theorem stepIH_i {P : PairCtx} {ins : OffsetInstruction} {st : St} {p : St × Option (ℕ × Zip)}
    (h : stepIH P ins st = some p) : p.1.i = st.i + 1 := by
  rcases stepIH_eq h with ⟨-, -, rfl⟩ | ⟨c, -, -, hv⟩
  · rfl
  · obtain ⟨_, _, _, rfl⟩ := visitH_shape hv
    rfl

/-- A step records at most its own offset. -/
theorem stepIH_rec {P : PairCtx} {ins : OffsetInstruction} {st : St} {p : St × Option (ℕ × Zip)}
    (h : stepIH P ins st = some p) : ∀ e ∈ p.2, e.1 = st.i := by
  rcases stepIH_eq h with ⟨-, -, rfl⟩ | ⟨c, -, -, hv⟩
  · simp
  · obtain ⟨_, _, _, rfl⟩ := visitH_shape hv
    simp

/-! ## Every arrival is recorded -/

/-- **What is pending or falls in at a state is recorded**, the pass ending with nothing pending. -/
theorem pairGo_arr (P : PairCtx) : ∀ (code : List OffsetInstruction) {st st' : St} {acc acc' : List (ℕ × Zip)},
    pairGo P code st acc = some (st', acc') → st'.cur = none → st'.pend = [] →
      (∀ e ∈ acc, e ∈ acc') ∧ (∀ p ∈ st.pend, Arr acc' p.1 p.2) ∧ (∀ z ∈ st.cur, Arr acc' st.i z)
  | [], st, st', acc, acc', h, hc, hp => by
    simp only [pairGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun e he ↦ he, ?_, ?_⟩ <;> simp [hc, hp]
  | ins :: code, st, st', acc, acc', h, hc, hp => by
    rw [pairGo_cons] at h
    obtain ⟨p, hp1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hacc, hpend, hcur⟩ := pairGo_arr P code h hc hp
    have hrec : ∀ e ∈ p.2, e ∈ acc' := fun e he ↦ hacc e (List.mem_append_left _ (Option.mem_toList.mpr he))
    refine ⟨fun e he ↦ hacc e (List.mem_append_right _ he), ?_, ?_⟩
    · intro q hq
      rcases stepIH_eq hp1 with ⟨-, hhere, rfl⟩ | ⟨c, -, hall, hv⟩
      · rcases spanP_split st.i st.pend hq with ⟨h1, -⟩ | h1
        · rw [hhere] at h1; simp at h1
        · exact hpend q h1
      · obtain ⟨_, _, _, rfl⟩ := visitH_shape hv
        rcases spanP_split st.i st.pend hq with ⟨h1, h2⟩ | h1
        · exact ⟨c, h2 ▸ hrec _ rfl, (allKey_iff.mp hall q h1).symm⟩
        · exact hpend q (mem_mergeP _ _ (Or.inr h1))
    · intro z hz
      rcases stepIH_eq hp1 with ⟨hcn, -, -⟩ | ⟨c, hc', -, hv⟩
      · rw [hcn] at hz; cases hz
      · obtain ⟨z0, z1, hz0, hz1, hcase⟩ := visitH_eq hv
        rcases hc' with hc' | ⟨hcn, -⟩
        · rw [hc'] at hz
          cases hz
          rcases hcase with ⟨oc, od, of, zs, r, hins, hk, hzs, hr, hpe⟩ | ⟨hnj, z', hz', hpe⟩
          · exact ⟨_, hrec _ (by rw [hpe]; rfl), rfl⟩
          · exact ⟨_, hrec _ (by rw [hpe]; rfl), rfl⟩
        · rw [hcn] at hz; cases hz

/-! ## The pass's invariant -/

/-- A table jump's arms from `z` through the table at `base`: each arm's target, past `m`, pending
with the arm's zipper. -/
@[expose] def ArmsInH (P : PairCtx) (pend : List (ℕ × Zip)) (base : ℕ) (z : Zip) (m : ℕ) : Prop :=
  ∃ x arms ss, z.cur = .match_ x arms :: ss ∧ ∀ j < arms.length, ∃ t c, getF P.X.jt (base + j) = some t ∧
    P.nL (z.enter (.match_ x arms) ss j) = some c ∧ m ≤ t - P.X.entry ∧ (t - P.X.entry, c) ∈ pend

/-- **Each table jump registered has its arms pending** until its least target. -/
@[expose] def TabInvH (P : PairCtx) (st : St) : Prop :=
  ∀ t ∈ st.tabs, st.i ≤ t.2.2 → ArmsInH P st.pend t.1 t.2.1 t.2.2

/-- The pass's invariant. -/
structure PInvH (P : PairCtx) (body : List Stmt) (hs0 : List (ℕ × List Prover.Exec.Hint)) (st : St) : Prop where
  ok : StOk body hs0 st
  tab : TabInvH P st
  hs : HsInv P.X hs0 st

theorem armZsH_arr (P : PairCtx) (i : ℕ) (z : Zip) (s : Stmt) (ss : List Stmt) (base : ℕ) :
    ∀ (as : List (List Stmt)) (j : ℕ) {l : List (ℕ × Zip)}, armZsH P i z s ss base j as = some l →
      ∀ k < as.length, ∃ t c, getF P.X.jt (base + (j + k)) = some t ∧ P.nL (z.enter s ss (j + k)) = some c ∧
        (t - P.X.entry, c) ∈ l ∧ P.X.entry + i < t
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | _ :: as, j, l, h, k, hk => by
    simp only [armZsH] at h
    split at h
    · rename_i t c ht hc
      split at h
      · rename_i o l' ho hl
        cases h
        cases k with
        | zero =>
          refine ⟨t, c, ht, hc, ?_, (fwdOff_eq ho).2⟩
          rw [← (fwdOff_eq ho).1]
          exact List.mem_cons_self
        | succ k =>
          obtain ⟨t', c', h1, h2, h3, h4⟩ := armZsH_arr P i z s ss base as (j + 1) hl k (by simpa using hk)
          refine ⟨t', c', by rw [← h1]; congr 1; omega, by rw [← h2]; congr 2; omega, List.mem_cons_of_mem _ h3, h4⟩
      · cases h
    · cases h

/-- A `match`'s table jump not skipped, not a forward jump in the frame: the arrivals are its arms'. -/
theorem jumpH_match {P : PairCtx} {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {z zs : Zip} {x : V}
    {arms : List (List Stmt)} {ss : List Stmt} {a : ℕ × ℕ} {r : Option Zip × List (ℕ × Zip)}
    (h : jumpStepH P i oc od of tabs z zs = some r) (hz : zs.cur = .match_ x arms :: ss)
    (hzero : P.X.zeroAt oc = false) (hfwd : fwdJ P.X i oc od of = false) (ha : getF P.X.arms od = some a) :
    P.X.nzAt oc = true ∧ P.X.selfAt of = true ∧ a.1 = x.idx ∧
      ((tabHit tabs a.2 zs i = true ∧ r = (none, [])) ∨
        (tabHit tabs a.2 zs i = false ∧ armZsH P i zs (.match_ x arms) ss a.2 0 arms = some r.2 ∧ r.1 = none)) := by
  simp only [jumpStepH, hzero, hfwd, Bool.cond_false, headStepH, hz] at h
  cases hs : (P.X.nzAt oc && P.X.selfAt of) <;> simp only [hs, Bool.cond_true, Bool.cond_false, ha] at h
  · cases h
  simp only [Bool.and_eq_true] at hs
  cases hx : Nat.beq a.1 x.idx <;> simp only [hx, Bool.cond_true, Bool.cond_false] at h
  · cases h
  refine ⟨hs.1, hs.2, Nat.beq_eq.mp hx, ?_⟩
  cases ht : tabHit tabs a.2 zs i <;> simp only [ht, Bool.cond_true, Bool.cond_false] at h
  · obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Or.inr ⟨rfl, hl, rfl⟩
  · cases h; exact Or.inl ⟨rfl, rfl⟩

theorem tabInvH_keep {P : PairCtx} {st : St} (h : TabInvH P st) {pend' : List (ℕ × Zip)}
    (hp : ∀ q ∈ (spanP st.i st.pend).2, q ∈ pend') {t : ℕ × Zip × ℕ} (ht : t ∈ st.tabs) (hle : st.i + 1 ≤ t.2.2) :
    ArmsInH P pend' t.1 t.2.1 t.2.2 := by
  obtain ⟨x, arms, ss, hz, hj⟩ := h t ht (by omega)
  refine ⟨x, arms, ss, hz, fun j hjl ↦ ?_⟩
  obtain ⟨tg, c, h1, h2, h3, h4⟩ := hj j hjl
  refine ⟨tg, c, h1, h2, h3, hp _ ?_⟩
  rcases spanP_split st.i st.pend h4 with ⟨-, he⟩ | h5
  · simp only at he; omega
  · exact h5

/-- **A step keeps the pass's invariant.** -/
theorem stepIH_inv {P : PairCtx} {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} {ins : OffsetInstruction}
    {st : St} {p : St × Option (ℕ × Zip)} (h : PInvH P body hs0 st) (hp : stepIH P ins st = some p) :
    PInvH P body hs0 p.1 ∧ p.1.i = st.i + 1 := by
  obtain ⟨hok, hi⟩ := stepIH_ok P ins h.ok hp
  refine ⟨⟨hok, ?_, ?_⟩, hi⟩
  · rcases stepIH_eq hp with ⟨-, -, rfl⟩ | ⟨c, -, -, hv⟩
    · intro t ht hle
      exact tabInvH_keep h.tab (fun q hq ↦ hq) ht hle
    · obtain ⟨z0, z, hz0, hz, hcase⟩ := visitH_eq hv
      rcases hcase with ⟨oc, od, of, zs, r, rfl, -, -, hr, rfl⟩ | ⟨-, z', -, rfl⟩
      · intro t ht hle
        rcases tabReg_mem ht with ht | ⟨oc', od', of', x, arms, ss, a, hins, hz, hne, hf, ha, rfl⟩
        · exact tabInvH_keep h.tab (fun q hq ↦ mem_mergeP _ _ (Or.inr hq)) ht hle
        · simp only [OffsetInstruction.jump.injEq] at hins
          obtain ⟨rfl, rfl, rfl⟩ := hins
          have hzero : P.X.zeroAt oc = false := by
            cases hz0 : P.X.zeroAt oc
            · rfl
            · simp only [jumpStepH, hz0, Bool.cond_true, Option.some.injEq] at hr
              subst hr
              exact absurd rfl hne
          obtain ⟨-, -, -, hc⟩ := jumpH_match hr hz hzero hf ha
          rcases hc with ⟨-, rfl⟩ | ⟨-, hl, -⟩
          · exact absurd rfl hne
          refine ⟨x, arms, ss, hz, fun j hj ↦ ?_⟩
          obtain ⟨t, c, h1, h2, h3, -⟩ := armZsH_arr P _ zs _ ss a.2 arms 0 hl j hj
          simp only [Nat.zero_add] at h1 h2
          exact ⟨t, c, h1, h2, minOff_le _ h3, mem_mergeP _ _ (Or.inl h3)⟩
      · intro t ht hle
        exact tabInvH_keep h.tab (fun q hq ↦ hq) ht hle
  · refine hsInv_step h.hs _ hi ?_
    rcases stepIH_eq hp with ⟨-, -, rfl⟩ | ⟨c, -, -, hv⟩
    · rfl
    · obtain ⟨_, _, _, rfl⟩ := visitH_shape hv
      rfl

/-! ## Each recorded offset was visited -/

/-- **Each offset recorded was visited at a state of the pass**, the rest of the pass from the
state after it. -/
theorem pairGo_visit (P : PairCtx) {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} :
    ∀ (code : List OffsetInstruction) {st st' : St} {acc acc' : List (ℕ × Zip)}, PInvH P body hs0 st →
      pairGo P code st acc = some (st', acc') → ∀ e ∈ acc', e ∈ acc ∨
        ∃ sti ins p rc acc1, PInvH P body hs0 sti ∧ st.i ≤ sti.i ∧ code.drop (sti.i - st.i) = ins :: rc ∧
          stepIH P ins sti = some p ∧ p.2 = some e ∧ pairGo P rc p.1 acc1 = some (st', acc')
  | [], st, st', acc, acc', _, h, e, he => by
    simp only [pairGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Or.inl he
  | ins :: code, st, st', acc, acc', hI, h, e, he => by
    rw [pairGo_cons] at h
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hI', hi⟩ := stepIH_inv hI hp
    rcases pairGo_visit P code hI' h e he with he | ⟨sti, ins', q, rc, acc1, h1, h2, h3, h4, h5, h6⟩
    · rcases List.mem_append.mp he with he | he
      · exact Or.inr ⟨st, ins, p, code, _, hI, le_rfl, by simp, hp, Option.mem_toList.mp he, h⟩
      · exact Or.inl he
    · refine Or.inr ⟨sti, ins', q, rc, acc1, h1, by omega, ?_, h4, h5, h6⟩
      rw [show sti.i - st.i = (sti.i - p.1.i) + 1 by omega, List.drop_succ_cons]
      exact h3

/-! ## What the pass gives -/

/-- What an offset's instruction does from the zipper `z` past its hints, the recorded offsets `l`: a
jump from `z` past its reads, its successors recorded, a `match`'s table jump reaching every arm; or
another instruction, its zipper after recorded at the next offset. -/
@[expose] def InsOk (P : PairCtx) (l : List (ℕ × Zip)) (i : ℕ) (ins : OffsetInstruction) (z : Zip) : Prop :=
  (∃ oc od of zs tabs r, ins = .jump oc od of ∧ P.kindOk i none = true ∧ P.nS z = some zs ∧
      jumpStepH P i oc od of tabs z zs = some r ∧ (∀ z1 ∈ r.1, Arr l (i + 1) z1) ∧ (∀ p ∈ r.2, Arr l p.1 p.2) ∧
      ∀ x arms ss a, zs.cur = .match_ x arms :: ss → P.X.zeroAt oc = false →
        fwdJ P.X i oc od of = false → getF P.X.arms od = some a →
        ∀ j < arms.length, ∃ t c', getF P.X.jt (a.2 + j) = some t ∧
          P.nL (zs.enter (.match_ x arms) ss j) = some c' ∧ Arr l (t - P.X.entry) c' ∧ P.X.entry + i < t) ∨
    ((∀ oc od of, ins ≠ .jump oc od of) ∧ ∃ z', plainStep P i ins z = some z' ∧ Arr l (i + 1) z')

/-- **The pairing at a reached offset**: its hints consume the normalized position's head flow hint
atoms, its instruction steps from there, what it hands on recorded. -/
theorem pairRun_step {P : PairCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : alignPre P.X d = true) {l : List (ℕ × Zip)}
    (h : pairRun P body code d = some l) {i : ℕ} {c : Zip} (hc : (i, c) ∈ l) :
    ∃ ins z0 z, code[i]? = some ins ∧ ZOk body c ∧ P.nL c = some z0 ∧
      hintsStepH P ((d.2.2.lookup (P.X.entry + i)).getD []) z0 = some z ∧ ZOk body z ∧ InsOk P l i ins z := by
  simp only [pairRun] at h
  obtain ⟨⟨st', acc'⟩, hgo, hend⟩ := Option.bind_eq_some_iff.mp h
  simp only [alignEnd, Bool.cond_eq_ite, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff] at hend
  split at hend
  swap
  · cases hend
  rename_i hce
  obtain ⟨hcn, hpn⟩ := hce
  cases hend
  simp only [alignPre, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.ble_eq] at hpre
  obtain ⟨⟨⟨-, -⟩, hup⟩, hge⟩ := hpre
  have hI0 : PInvH P body d.2.2 ⟨0, d.2.2, some (Zip.init body), [], []⟩ :=
    ⟨⟨⟨0, rfl⟩, by simpa using zOk_init body, by simp, by simp⟩, by simp [TabInvH],
      ⟨[], rfl, by simp, fun q hq ↦ by simpa using hge q hq, hup⟩⟩
  rcases pairGo_visit P code hI0 hgo (i, c) hc with he | ⟨sti, ins, p, rc, acc1, hI, -, hdrop, hp, hp2, hrest⟩
  · simp at he
  obtain ⟨hacc, hpend, hcur⟩ := pairGo_arr P rc hrest hcn hpn
  rcases stepIH_eq hp with ⟨-, -, rfl⟩ | ⟨c', hc', hall, hv⟩
  · cases hp2
  obtain ⟨_, _, _, hpe⟩ := visitH_shape hv
  have hci : (i, c) = (sti.i, c') := by rw [hpe] at hp2; exact (Option.some.inj hp2).symm
  simp only [Prod.mk.injEq] at hci
  obtain ⟨rfl, rfl⟩ := hci
  obtain ⟨z0, z, hz0, hz, hcase⟩ := visitH_eq hv
  have hcok : ZOk body c := by
    rcases hc' with hc' | ⟨-, q, hq, hqc⟩
    · exact hI.ok.cur c (by simp [hc'])
    · exact hqc ▸ hI.ok.pend q ((spanP_mem _ _).1 hq)
  have hzok : ZOk body z := hintsStepH_ok P _ (P.nL_ok hcok hz0) hz
  have hins : code[sti.i]? = some ins := by
    rw [← List.head?_drop, Nat.sub_zero] at *
    rw [hdrop]; rfl
  refine ⟨ins, z0, z, hins, hcok, hz0, by rw [← hsInv_lookup hI.hs]; exact hz, hzok, ?_⟩
  rcases hcase with ⟨oc, od, of, zs, r, rfl, hk, hzs, hr, rfl⟩ | ⟨hnj, z', hz', rfl⟩
  · refine Or.inl ⟨oc, od, of, zs, sti.tabs, r, rfl, hk, hzs, hr, fun z1 hz1 ↦ hcur z1 hz1,
      fun q hq ↦ hpend q (mem_mergeP _ _ (Or.inl hq)), ?_⟩
    intro x arms ss a hzc hzero hfwd ha j hj
    obtain ⟨-, -, hx, hcase⟩ := jumpH_match hr hzc hzero hfwd ha
    have hzsok : ZOk body zs := P.nS_ok hzok hzs
    rcases hcase with ⟨hhit, -⟩ | ⟨-, hl, -⟩
    · simp only [tabHit, List.any_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hhit
      obtain ⟨t, ht, ⟨hb, hk⟩, hlt⟩ := hhit
      obtain ⟨x', arms', ss', hz', hj'⟩ := hI.tab t ht (by omega)
      have hteq : t.2.1 = zs := ZOk.eq_of_key (hI.ok.tabs t ht) hzsok (keyEq_iff.mp hk)
      rw [hteq, hzc] at hz'
      simp only [List.cons.injEq, Stmt.match_.injEq] at hz'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hz'
      obtain ⟨tg, c', h1, h2, h3, h4⟩ := hj' j hj
      rw [hb, hteq] at *
      refine ⟨tg, c', h1, h2, hpend (tg - P.X.entry, c') (mem_mergeP _ _ (Or.inr ?_)), by omega⟩
      rcases spanP_split sti.i sti.pend h4 with ⟨-, he⟩ | h5
      · simp only at he; omega
      · exact h5
    · obtain ⟨t, c', h1, h2, h3, h4⟩ := armZsH_arr P _ zs _ ss a.2 arms 0 hl j hj
      simp only [Nat.zero_add] at h1 h2
      exact ⟨t, c', h1, h2, hpend _ (mem_mergeP _ _ (Or.inl h3)), h4⟩
  · exact Or.inr ⟨hnj, z', hz', hcur z' rfl⟩

/-! ## The record -/

/-- The pass records each offset once, the later first. -/
theorem pairGo_desc (P : PairCtx) : ∀ (code : List OffsetInstruction) {st st' : St} {acc acc' : List (ℕ × Zip)},
    pairGo P code st acc = some (st', acc') → acc.Pairwise (fun a b ↦ b.1 < a.1) → (∀ e ∈ acc, e.1 < st.i) →
      acc'.Pairwise (fun a b ↦ b.1 < a.1)
  | [], _, _, _, _, h, hp, _ => by
    simp only [pairGo, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact hp
  | ins :: code, st, st', acc, acc', h, hp, hlt => by
    rw [pairGo_cons] at h
    obtain ⟨p, hp1, h⟩ := Option.bind_eq_some_iff.mp h
    have hi := stepIH_i hp1
    have hr := stepIH_rec hp1
    refine pairGo_desc P code h ?_ fun e he ↦ ?_
    · rw [List.pairwise_append]
      refine ⟨?_, hp, fun a ha b hb ↦ ?_⟩
      · cases hq : p.2 <;> simp
      · rw [hr a (Option.mem_toList.mp ha)]; exact hlt b hb
    · rcases List.mem_append.mp he with he | he
      · rw [hr e (Option.mem_toList.mp he)]; omega
      · have := hlt e he; omega

theorem pairRun_desc {P : PairCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {l : List (ℕ × Zip)} (h : pairRun P body code d = some l) :
    l.Pairwise (fun a b ↦ b.1 < a.1) := by
  simp only [pairRun] at h
  obtain ⟨⟨st', acc'⟩, hgo, hend⟩ := Option.bind_eq_some_iff.mp h
  simp only [alignEnd, Bool.cond_eq_ite] at hend
  split at hend
  · cases hend; exact pairGo_desc P code hgo (by simp) (by simp)
  · cases hend

/-- **An arrival recorded is the position there**, the zippers their cursors'. -/
theorem pairAt_of_arr {P : PairCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : alignPre P.X d = true) {l : List (ℕ × Zip)}
    (h : pairRun P body code d = some l) {o : ℕ} {z : Zip} (ha : Arr l o z) (hz : ZOk body z) :
    pairAt P body code d o = some z.pos := by
  obtain ⟨c, hc, hk⟩ := ha
  obtain ⟨-, -, -, -, hcok, -⟩ := pairRun_step hpre h hc
  simp only [pairAt, h, Option.bind_some, lookup_of_desc (pairRun_desc h) hc, Option.map_some,
    ZOk.eq_of_key hcok hz hk]

theorem pairOk_iff {X : AlignCtx} {H : HCert} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} :
    pairOk X H O S body code d = true ↔
      alignPre X d = true ∧ ∃ l, pairRun (PairCtx.ofH X H O S) body code d = some l := by
  rw [pairOk, PairCtx.seq_eq]
  change (alignPre X d && (pairRun (PairCtx.ofH X H O S) body code d).isSome) = true ↔ _
  simp only [Bool.and_eq_true, Option.isSome_iff_exists]

/-- **Offset `0` is the body.** -/
theorem pairAt_zero {X : AlignCtx} {H : HCert} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (h : pairOk X H O S body code d = true) : pairAt (PairCtx.ofH X H O S) body code d 0 = some body := by
  obtain ⟨hpre, l, hl⟩ := pairOk_iff.mp h
  set P := PairCtx.ofH X H O S
  cases code with
  | nil => simp [pairRun, pairGo, alignEnd, Zip.init] at hl
  | cons ins code =>
    have hl' := hl
    simp only [pairRun] at hl'
    obtain ⟨⟨st', acc'⟩, hgo, hend⟩ := Option.bind_eq_some_iff.mp hl'
    rw [pairGo_cons] at hgo
    obtain ⟨p, hp, hgo⟩ := Option.bind_eq_some_iff.mp hgo
    have hp2 : p.2 = some (0, Zip.init body) := by
      rcases stepIH_eq hp with ⟨h0, -, -⟩ | ⟨c, hc, -, hv⟩
      · simp at h0
      · obtain ⟨_, _, _, rfl⟩ := visitH_shape hv
        rcases hc with hc | ⟨hc, -⟩
        · simp only [Option.some.injEq] at hc
          rw [← hc]
        · simp at hc
    have hmem : (0, Zip.init body) ∈ l := by
      obtain ⟨hacc, -, -⟩ := pairGo_arr P code hgo (by
        simp only [alignEnd, Bool.cond_eq_ite, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff] at hend
        split at hend
        · rename_i hh; exact hh.1
        · cases hend) (by
        simp only [alignEnd, Bool.cond_eq_ite, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff] at hend
        split at hend
        · rename_i hh; exact hh.2
        · cases hend)
      have hacc' : acc' = l := by
        simp only [alignEnd, Bool.cond_eq_ite] at hend
        split at hend
        · exact Option.some.inj hend
        · cases hend
      rw [← hacc']
      exact hacc _ (by rw [hp2]; simp)
    simp only [pairAt, hl, Option.bind_some, lookup_of_desc (pairRun_desc hl) hmem, Option.map_some]
    simp [Zip.pos, Zip.init]

end

end LeanVM.Guest.CoreMode
