/-
  LeanVM.Guest.Bridge.AlignSound

  What the alignment pass gives at each offset it reaches: the offset's hints consume its position's head flow hint atoms, and the position after its instruction is recorded at each successor, the table jumps a registered one skips among them.
-/

module

public import LeanVM.Guest.Bridge.Align

/-!
# The alignment pass's soundness

`Arr l o z`: offset `o` is recorded in `l` with the cursor of `z`. An arrival leaves the pending list only at its offset, against the cursor recorded there (`allKey`), and the pass ends with nothing pending, so every arrival pending or falling in at a state is recorded (`go_arr`). Each recorded offset was visited at a state of the pass (`go_visit`), whose invariant (`PInv`) holds: its zippers their cursors' (`StOk`), its hints the advice's past the earlier pcs (`HsInv`), and each table jump registered with its arms' arrivals still pending until its least target (`TabInv`; a forward jump in the frame registers nothing, `tabReg`).

`alignRun_step`: at an offset the pass reaches with zipper `c`, the hints at its pc (`lookup`) consume the normalized position's head flow hint atoms, its instruction steps from there, the zipper falling through is recorded at the next offset, every arrival at its target, and a `match`'s table jump reaches every arm at the jump table's targets, whether it registered the jump or skipped it as registered.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (natSeq natSeq_eq)
open LeanVM.Guest.Check (getF)

public section

/-- **Offset `o` recorded in `l` with the cursor of `z`.** -/
@[expose] def Arr (l : List (ℕ × Zip)) (o : ℕ) (z : Zip) : Prop := ∃ c, (o, c) ∈ l ∧ c.key = z.key

/-! ## The pending list -/

theorem spanP_split (i : ℕ) : ∀ (l : List (ℕ × Zip)) {p : ℕ × Zip}, p ∈ l →
    (p ∈ (spanP i l).1 ∧ p.1 = i) ∨ p ∈ (spanP i l).2
  | [], _, h => by simp at h
  | a :: l, p, h => by
    change (p ∈ (bif Nat.beq a.1 i then (match spanP i l with | (h, t) => (a :: h, t)) else ([], a :: l)).1 ∧ _) ∨
      p ∈ (bif Nat.beq a.1 i then (match spanP i l with | (h, t) => (a :: h, t)) else ([], a :: l)).2
    have ih := fun hp ↦ spanP_split i l (p := p) hp
    cases hb : Nat.beq a.1 i <;> simp only [Bool.cond_true, Bool.cond_false]
    · exact Or.inr h
    · generalize spanP i l = S at ih ⊢
      obtain ⟨hh, t⟩ := S
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl ⟨List.mem_cons_self, Nat.beq_eq.mp hb⟩
      · rcases ih h with ⟨h1, h2⟩ | h1
        · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
        · exact Or.inr h1

theorem mem_insP (a : ℕ × Zip) : ∀ (l : List (ℕ × Zip)) {p : ℕ × Zip}, p = a ∨ p ∈ l → p ∈ insP a l
  | [], p, h => by
    rcases h with rfl | h
    · exact List.mem_singleton_self _
    · simp at h
  | b :: l, p, h => by
    change p ∈ (bif Nat.blt b.1 a.1 then b :: insP a l else a :: b :: l)
    cases hb : Nat.blt b.1 a.1 <;> simp only [Bool.cond_true, Bool.cond_false]
    · rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h
    · rcases h with h | h
      · exact List.mem_cons_of_mem _ (mem_insP a l (Or.inl h))
      · rcases List.mem_cons.mp h with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_insP a l (Or.inr h))

theorem mem_mergeP : ∀ (as l : List (ℕ × Zip)) {p : ℕ × Zip}, p ∈ as ∨ p ∈ l → p ∈ mergeP as l
  | [], _, _, h => h.elim (fun h ↦ by simp at h) id
  | a :: as, l, p, h => by
    change p ∈ insP a (mergeP as l)
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact mem_insP _ _ (Or.inl rfl)
      · exact mem_insP _ _ (Or.inr (mem_mergeP as l (Or.inl h)))
    · exact mem_insP _ _ (Or.inr (mem_mergeP as l (Or.inr h)))

theorem minOff_le : ∀ (tg : List (ℕ × Zip)) {p : ℕ × Zip}, p ∈ tg → minOff tg ≤ p.1
  | [], _, h => by simp at h
  | a :: tg, p, h => by
    change Nat.min a.1 (minOff tg) ≤ p.1
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.min_le_left _ _
    · exact (Nat.min_le_right _ _).trans (minOff_le tg h)

theorem allKey_iff {here : List (ℕ × Zip)} {c : Zip} : allKey here c = true ↔ ∀ p ∈ here, p.2.key = c.key := by
  simp [allKey, List.all_eq_true, keyEq_iff]

/-! ## A step's shape -/

theorem visit_eq {X : AlignCtx} {ins : OffsetInstruction} {i i' : ℕ} {h1 : List Prover.Exec.Hint}
    {hs' : List (ℕ × List Prover.Exec.Hint)} {rest : List (ℕ × Zip)} {tabs : List (ℕ × Zip × ℕ)} {c : Zip}
    {p : St × Option (ℕ × Zip)} (h : visit X ins i i' h1 hs' rest tabs c = some p) :
    ∃ z0 z r, normZ X.fuel c = some z0 ∧ hintsStep X h1 z0 = some z ∧ insStep X i ins tabs z = some r ∧
      p = (⟨i', hs', r.1, mergeP r.2 rest, tabReg X i ins z r.2 tabs⟩, some (i, c)) := by
  simp only [visit] at h
  obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨z1, hz1, hz⟩ := Option.bind_eq_some_iff.mp hz
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨z1, z, q, hz1, hz, hq, rfl⟩

/-- **A step of the pass**: offset `i` not reached, or reached with the zipper falling in or the
first arrival, every arrival there of its cursor. -/
theorem stepI_eq {X : AlignCtx} {ins : OffsetInstruction} {st : St} {p : St × Option (ℕ × Zip)}
    (h : stepI X ins st = some p) :
    (st.cur = none ∧ (spanP st.i st.pend).1 = [] ∧
      p = (⟨st.i + 1, (hintsAt (Nat.add X.entry st.i) st.hs).2, none, (spanP st.i st.pend).2, st.tabs⟩, none)) ∨
    ∃ c, (st.cur = some c ∨ (st.cur = none ∧ ∃ q ∈ (spanP st.i st.pend).1, q.2 = c)) ∧
      allKey (spanP st.i st.pend).1 c = true ∧
      visit X ins st.i (st.i + 1) (hintsAt (Nat.add X.entry st.i) st.hs).1 (hintsAt (Nat.add X.entry st.i) st.hs).2
        (spanP st.i st.pend).2 st.tabs c = some p := by
  unfold stepI at h
  rw [natSeq_eq] at h
  generalize spanP st.i st.pend = S at h ⊢
  generalize hintsAt (Nat.add X.entry st.i) st.hs = H at h ⊢
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

/-! ## Every arrival is recorded -/

/-- **What is pending or falls in at a state is recorded**, the pass ending with nothing pending. -/
theorem go_arr (X : AlignCtx) : ∀ (code : List OffsetInstruction) {st st' : St} {acc acc' : List (ℕ × Zip)},
    alignGo X code st acc = some (st', acc') → st'.cur = none → st'.pend = [] →
      (∀ e ∈ acc, e ∈ acc') ∧ (∀ p ∈ st.pend, Arr acc' p.1 p.2) ∧ (∀ z ∈ st.cur, Arr acc' st.i z)
  | [], st, st', acc, acc', h, hc, hp => by
    simp only [alignGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun e he ↦ he, ?_, ?_⟩ <;> simp [hc, hp]
  | ins :: code, st, st', acc, acc', h, hc, hp => by
    rw [alignGo_cons] at h
    obtain ⟨p, hp1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hacc, hpend, hcur⟩ := go_arr X code h hc hp
    have hrec : ∀ e ∈ p.2, e ∈ acc' := fun e he ↦ hacc e (List.mem_append_left _ (Option.mem_toList.mpr he))
    refine ⟨fun e he ↦ hacc e (List.mem_append_right _ he), ?_, ?_⟩
    · intro q hq
      rcases stepI_eq hp1 with ⟨-, hhere, rfl⟩ | ⟨c, -, hall, hv⟩
      · rcases spanP_split st.i st.pend hq with ⟨h1, -⟩ | h1
        · rw [hhere] at h1; simp at h1
        · exact hpend q h1
      · obtain ⟨z0, z, r, -, -, -, rfl⟩ := visit_eq hv
        rcases spanP_split st.i st.pend hq with ⟨h1, h2⟩ | h1
        · exact ⟨c, h2 ▸ hrec _ rfl, (allKey_iff.mp hall q h1).symm⟩
        · exact hpend q (mem_mergeP _ _ (Or.inr h1))
    · intro z hz
      rcases stepI_eq hp1 with ⟨hcn, -, -⟩ | ⟨c, hc', -, hv⟩
      · rw [hcn] at hz; cases hz
      · obtain ⟨z0, z', r, -, -, -, rfl⟩ := visit_eq hv
        rcases hc' with hc' | ⟨hcn, -⟩
        · rw [hc'] at hz
          cases hz
          exact ⟨_, hrec _ rfl, rfl⟩
        · rw [hcn] at hz; cases hz

/-! ## The pass's invariant -/

/-- A table jump's arms from `z` through the table at `base`: each arm's target, past `m`, pending
with the arm's zipper. -/
@[expose] def ArmsIn (X : AlignCtx) (pend : List (ℕ × Zip)) (base : ℕ) (z : Zip) (m : ℕ) : Prop :=
  ∃ x arms ss, z.cur = .match_ x arms :: ss ∧ ∀ j < arms.length, ∃ t c, getF X.jt (base + j) = some t ∧
    normZ X.fuel (z.enter (.match_ x arms) ss j) = some c ∧ m ≤ t - X.entry ∧ (t - X.entry, c) ∈ pend

/-- **Each table jump registered has its arms pending** until its least target. -/
@[expose] def TabInv (X : AlignCtx) (st : St) : Prop :=
  ∀ t ∈ st.tabs, st.i ≤ t.2.2 → ArmsIn X st.pend t.1 t.2.1 t.2.2

/-- **The hints left are the advice's past the pcs before the state's**, by increasing pc. -/
@[expose] def HsInv (X : AlignCtx) (hs0 : List (ℕ × List Prover.Exec.Hint)) (st : St) : Prop :=
  ∃ pre, hs0 = pre ++ st.hs ∧ (∀ q ∈ pre, q.1 < X.entry + st.i) ∧ (∀ q ∈ st.hs, X.entry + st.i ≤ q.1) ∧
    pcsUp st.hs = true

/-- The pass's invariant. -/
structure PInv (X : AlignCtx) (body : List Stmt) (hs0 : List (ℕ × List Prover.Exec.Hint)) (st : St) : Prop where
  ok : StOk body hs0 st
  tab : TabInv X st
  hs : HsInv X hs0 st

theorem pcsUp_lt : ∀ {a : ℕ × List Prover.Exec.Hint} {l : List (ℕ × List Prover.Exec.Hint)},
    pcsUp (a :: l) = true → ∀ q ∈ l, a.1 < q.1
  | _, [], _, q, hq => by simp at hq
  | a, b :: l, h, q, hq => by
    simp only [pcsUp, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact h.1.trans (pcsUp_lt h.2 q hq)

theorem pcsUp_tail {a : ℕ × List Prover.Exec.Hint} {l : List (ℕ × List Prover.Exec.Hint)}
    (h : pcsUp (a :: l) = true) : pcsUp l = true := by
  cases l with
  | nil => rfl
  | cons b l => simp only [pcsUp, Bool.and_eq_true] at h; exact h.2

theorem hsInv_step {X : AlignCtx} {hs0 : List (ℕ × List Prover.Exec.Hint)} {st : St} (h : HsInv X hs0 st)
    (st' : St) (hi : st'.i = st.i + 1) (hh : st'.hs = (hintsAt (Nat.add X.entry st.i) st.hs).2) :
    HsInv X hs0 st' := by
  obtain ⟨pre, rfl, hpre, hge, hup⟩ := h
  unfold HsInv
  rw [hi]
  cases hd : st.hs with
  | nil =>
    rw [hd] at hh
    refine ⟨pre, by rw [hh]; rfl, fun q hq ↦ by have := hpre q hq; omega, by simp [hh, hintsAt], ?_⟩
    rw [hh]; rfl
  | cons a t =>
    rw [hd] at hh hge hup
    obtain ⟨p, q⟩ := a
    change st'.hs = (bif Nat.beq p (Nat.add X.entry st.i) then (q, t) else ([], (p, q) :: t)).2 at hh
    have hp := hge (p, q) List.mem_cons_self
    cases hb : Nat.beq p (Nat.add X.entry st.i) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at hh
    · have hne : p ≠ X.entry + st.i := fun e ↦ by simp [e] at hb
      refine ⟨pre, by rw [hh], fun q hq ↦ by have := hpre q hq; omega, ?_, by rw [hh]; exact hup⟩
      rw [hh]
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · simp only at hp ⊢; omega
      · have := pcsUp_lt hup r hr; simp only at hp this; omega
    · have he : p = X.entry + st.i := Nat.beq_eq.mp hb
      refine ⟨pre ++ [(p, q)], by rw [hh, List.append_assoc]; rfl, fun r hr ↦ ?_, ?_, ?_⟩
      · rcases List.mem_append.mp hr with hr | hr
        · have := hpre r hr; omega
        · rw [List.mem_singleton.mp hr]; simp only; omega
      · rw [hh]
        intro r hr
        have := pcsUp_lt hup r hr
        simp only at this
        omega
      · rw [hh]; exact pcsUp_tail hup

/-- **The hints at the state's pc are the advice's there.** -/
theorem hsInv_lookup {X : AlignCtx} {hs0 : List (ℕ × List Prover.Exec.Hint)} {st : St} (h : HsInv X hs0 st) :
    (hintsAt (Nat.add X.entry st.i) st.hs).1 = (hs0.lookup (X.entry + st.i)).getD [] := by
  obtain ⟨pre, rfl, hpre, hge, hup⟩ := h
  have hl : ∀ (pre : List (ℕ × List Prover.Exec.Hint)), (∀ q ∈ pre, q.1 < X.entry + st.i) →
      (pre ++ st.hs).lookup (X.entry + st.i) = st.hs.lookup (X.entry + st.i) := by
    intro pre hpre
    induction pre with
    | nil => rfl
    | cons a pre ih =>
      have ha := hpre a List.mem_cons_self
      rw [List.cons_append, List.lookup, show (X.entry + st.i == a.1) = false by simp; omega]
      exact ih fun q hq ↦ hpre q (List.mem_cons_of_mem _ hq)
  rw [hl pre hpre]
  cases hd : st.hs with
  | nil => rfl
  | cons a t =>
    rw [hd] at hge hup
    obtain ⟨p, q⟩ := a
    change (bif Nat.beq p (Nat.add X.entry st.i) then (q, t) else ([], (p, q) :: t)).1 = _
    cases hb : Nat.beq p (Nat.add X.entry st.i) <;> simp only [Bool.cond_true, Bool.cond_false]
    · have hne : p ≠ X.entry + st.i := fun e ↦ by simp [e] at hb
      have hp := hge (p, q) List.mem_cons_self
      have hnone : ((p, q) :: t).lookup (X.entry + st.i) = none := by
        rw [List.lookup_eq_none_iff]
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · simp only [bne_iff_ne, ne_eq]; omega
        · have := pcsUp_lt hup r hr; simp only at hp this; simp only [bne_iff_ne, ne_eq]; omega
      rw [hnone]; rfl
    · have he : p = X.entry + st.i := Nat.beq_eq.mp hb
      rw [List.lookup, show (X.entry + st.i == p) = true by simp [he]]
      rfl

/-! ## Table jumps -/

theorem fwdOff_eq {X : AlignCtx} {i t o : ℕ} (h : X.fwdOff i t = some o) : o = t - X.entry ∧ X.entry + i < t := by
  simp only [AlignCtx.fwdOff, Bool.cond_eq_ite, natSeq_eq] at h
  split at h
  · rename_i hb
    exact ⟨(Option.some.inj h).symm, Nat.blt_eq.mp hb⟩
  · cases h

theorem armZs_arr (X : AlignCtx) (i : ℕ) (z : Zip) (s : Stmt) (ss : List Stmt) (base : ℕ) :
    ∀ (as : List (List Stmt)) (j : ℕ) {l : List (ℕ × Zip)}, armZs X i z s ss base j as = some l →
      ∀ k < as.length, ∃ t c, getF X.jt (base + (j + k)) = some t ∧ normZ X.fuel (z.enter s ss (j + k)) = some c ∧
        (t - X.entry, c) ∈ l ∧ X.entry + i < t
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | _ :: as, j, l, h, k, hk => by
    simp only [armZs] at h
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
          obtain ⟨t', c', h1, h2, h3, h4⟩ := armZs_arr X i z s ss base as (j + 1) hl k (by simpa using hk)
          refine ⟨t', c', by rw [← h1]; congr 1; omega, by rw [← h2]; congr 2; omega, List.mem_cons_of_mem _ h3, h4⟩
      · cases h
    · cases h

/-- A `match`'s table jump not skipped, not a forward jump in the frame: the arrivals are its arms'. -/
theorem jump_match {X : AlignCtx} {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {z : Zip} {x : V}
    {arms : List (List Stmt)} {ss : List Stmt} {a : ℕ × ℕ} {r : Option Zip × List (ℕ × Zip)}
    (h : insStep X i (.jump oc od of) tabs z = some r) (hz : z.cur = .match_ x arms :: ss)
    (hzero : X.zeroAt oc = false) (hfwd : fwdJ X i oc od of = false) (ha : getF X.arms od = some a) :
    X.nzAt oc = true ∧ X.selfAt of = true ∧ a.1 = x.idx ∧
      ((tabHit tabs a.2 z i = true ∧ r = (none, [])) ∨
        (tabHit tabs a.2 z i = false ∧ armZs X i z (.match_ x arms) ss a.2 0 arms = some r.2 ∧ r.1 = none)) := by
  simp only [insStep, jumpStep, hzero, hfwd, Bool.cond_false, headStep, hz] at h
  cases hs : (X.nzAt oc && X.selfAt of) <;> simp only [hs, Bool.cond_true, Bool.cond_false, ha] at h
  · cases h
  simp only [Bool.and_eq_true] at hs
  cases hx : Nat.beq a.1 x.idx <;> simp only [hx, Bool.cond_true, Bool.cond_false] at h
  · cases h
  refine ⟨hs.1, hs.2, Nat.beq_eq.mp hx, ?_⟩
  cases ht : tabHit tabs a.2 z i <;> simp only [ht, Bool.cond_true, Bool.cond_false] at h
  · obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Or.inr ⟨rfl, hl, rfl⟩
  · cases h; exact Or.inl ⟨rfl, rfl⟩

theorem tabReg_mem {X : AlignCtx} {i : ℕ} {ins : OffsetInstruction} {z : Zip} {tg : List (ℕ × Zip)}
    {tabs : List (ℕ × Zip × ℕ)} {t : ℕ × Zip × ℕ} (h : t ∈ tabReg X i ins z tg tabs) :
    t ∈ tabs ∨ ∃ oc od of x arms ss a, ins = .jump oc od of ∧ z.cur = .match_ x arms :: ss ∧ tg ≠ [] ∧
      fwdJ X i oc od of = false ∧ getF X.arms od = some a ∧ t = (a.2, z, minOff tg) := by
  unfold tabReg at h
  cases ins with
  | jump oc od of =>
    cases hz : z.cur with
    | nil => simp only [hz] at h; exact Or.inl h
    | cons s ss =>
      cases s with
      | match_ x arms =>
        cases tg with
        | nil => simp only [hz] at h; exact Or.inl h
        | cons p ps =>
          simp only [hz] at h
          cases hf : fwdJ X i oc od of <;> simp only [hf, Bool.cond_true, Bool.cond_false] at h
          · cases ha : getF X.arms od with
            | none => simp only [ha] at h; exact Or.inl h
            | some a =>
              simp only [ha] at h
              rcases List.mem_cons.mp h with rfl | h
              · exact Or.inr ⟨oc, od, of, x, arms, ss, a, rfl, rfl, by simp, hf, ha, rfl⟩
              · exact Or.inl h
          · exact Or.inl h
      | _ => simp only [hz] at h; exact Or.inl h
  | _ => exact Or.inl h

/-! ## The invariant kept -/

theorem tabInv_keep {X : AlignCtx} {st : St} (h : TabInv X st) {pend' : List (ℕ × Zip)}
    (hp : ∀ q ∈ (spanP st.i st.pend).2, q ∈ pend') {t : ℕ × Zip × ℕ} (ht : t ∈ st.tabs) (hle : st.i + 1 ≤ t.2.2) :
    ArmsIn X pend' t.1 t.2.1 t.2.2 := by
  obtain ⟨x, arms, ss, hz, hj⟩ := h t ht (by omega)
  refine ⟨x, arms, ss, hz, fun j hjl ↦ ?_⟩
  obtain ⟨tg, c, h1, h2, h3, h4⟩ := hj j hjl
  refine ⟨tg, c, h1, h2, h3, hp _ ?_⟩
  rcases spanP_split st.i st.pend h4 with ⟨-, he⟩ | h5
  · simp only at he; omega
  · exact h5

/-- **A step keeps the pass's invariant.** -/
theorem stepI_inv {X : AlignCtx} {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} {ins : OffsetInstruction}
    {st : St} {p : St × Option (ℕ × Zip)} (h : PInv X body hs0 st) (hp : stepI X ins st = some p) :
    PInv X body hs0 p.1 ∧ p.1.i = st.i + 1 := by
  obtain ⟨hok, hi⟩ := stepI_ok X ins h.ok hp
  refine ⟨⟨hok, ?_, ?_⟩, hi⟩
  · rcases stepI_eq hp with ⟨-, -, rfl⟩ | ⟨c, -, -, hv⟩
    · intro t ht hle
      exact tabInv_keep h.tab (fun q hq ↦ hq) ht hle
    · obtain ⟨z0, z, r, -, -, hr, rfl⟩ := visit_eq hv
      intro t ht hle
      rcases tabReg_mem ht with ht | ⟨oc, od, of, x, arms, ss, a, rfl, hz, hne, hf, ha, rfl⟩
      · exact tabInv_keep h.tab (fun q hq ↦ mem_mergeP _ _ (Or.inr hq)) ht hle
      · have hzero : X.zeroAt oc = false := by
          cases hz0 : X.zeroAt oc
          · rfl
          · simp only [insStep, jumpStep, hz0, Bool.cond_true, Option.some.injEq] at hr
            subst hr
            exact absurd rfl hne
        obtain ⟨-, -, -, hc⟩ := jump_match hr hz hzero hf ha
        rcases hc with ⟨-, rfl⟩ | ⟨-, hl, -⟩
        · exact absurd rfl hne
        refine ⟨x, arms, ss, hz, fun j hj ↦ ?_⟩
        obtain ⟨t, c, h1, h2, h3, -⟩ := armZs_arr X _ z _ ss a.2 arms 0 hl j hj
        simp only [Nat.zero_add] at h1 h2
        exact ⟨t, c, h1, h2, minOff_le _ h3, mem_mergeP _ _ (Or.inl h3)⟩
  · refine hsInv_step h.hs _ hi ?_
    rcases stepI_eq hp with ⟨-, -, rfl⟩ | ⟨c, -, -, hv⟩
    · rfl
    · obtain ⟨z0, z, r, -, -, -, rfl⟩ := visit_eq hv
      rfl

/-! ## Each recorded offset was visited -/

/-- **Each offset recorded was visited at a state of the pass**, the rest of the pass from the
state after it. -/
theorem go_visit (X : AlignCtx) {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} :
    ∀ (code : List OffsetInstruction) {st st' : St} {acc acc' : List (ℕ × Zip)}, PInv X body hs0 st →
      alignGo X code st acc = some (st', acc') → ∀ e ∈ acc', e ∈ acc ∨
        ∃ sti ins p rc acc1, PInv X body hs0 sti ∧ st.i ≤ sti.i ∧ code.drop (sti.i - st.i) = ins :: rc ∧
          stepI X ins sti = some p ∧ p.2 = some e ∧ alignGo X rc p.1 acc1 = some (st', acc')
  | [], st, st', acc, acc', _, h, e, he => by
    simp only [alignGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Or.inl he
  | ins :: code, st, st', acc, acc', hI, h, e, he => by
    rw [alignGo_cons] at h
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hI', hi⟩ := stepI_inv hI hp
    rcases go_visit X code hI' h e he with he | ⟨sti, ins', q, rc, acc1, h1, h2, h3, h4, h5, h6⟩
    · rcases List.mem_append.mp he with he | he
      · exact Or.inr ⟨st, ins, p, code, _, hI, le_rfl, by simp, hp, Option.mem_toList.mp he, h⟩
      · exact Or.inl he
    · refine Or.inr ⟨sti, ins', q, rc, acc1, h1, by omega, ?_, h4, h5, h6⟩
      rw [show sti.i - st.i = (sti.i - p.1.i) + 1 by omega, List.drop_succ_cons]
      exact h3

/-! ## What the pass gives -/

/-- **The alignment at a reached offset**: its hints consume the normalized position's head flow
hint atoms, its instruction steps from there, what falls through is recorded at the next offset,
each arrival at its target, and a `match`'s table jump reaches every arm, registered or skipped. -/
theorem alignRun_step {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : alignPre X d = true) {l : List (ℕ × Zip)}
    (h : alignRun X body code d = some l) {i : ℕ} {c : Zip} (hc : (i, c) ∈ l) :
    ∃ ins z0 z tabs r, code[i]? = some ins ∧ ZOk body c ∧ normZ X.fuel c = some z0 ∧
      hintsStep X ((d.2.2.lookup (X.entry + i)).getD []) z0 = some z ∧ ZOk body z ∧
      insStep X i ins tabs z = some r ∧ (∀ z1 ∈ r.1, Arr l (i + 1) z1) ∧ (∀ p ∈ r.2, Arr l p.1 p.2) ∧
      ∀ oc od of x arms ss a, ins = .jump oc od of → z.cur = .match_ x arms :: ss → X.zeroAt oc = false →
        fwdJ X i oc od of = false → getF X.arms od = some a →
        ∀ j < arms.length, ∃ t c', getF X.jt (a.2 + j) = some t ∧
          normZ X.fuel (z.enter (.match_ x arms) ss j) = some c' ∧ Arr l (t - X.entry) c' ∧ X.entry + i < t := by
  simp only [alignRun] at h
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
  have hI0 : PInv X body d.2.2 ⟨0, d.2.2, some (Zip.init body), [], []⟩ :=
    ⟨⟨⟨0, rfl⟩, by simpa using zOk_init body, by simp, by simp⟩, by simp [TabInv],
      ⟨[], rfl, by simp, fun q hq ↦ by simpa using hge q hq, hup⟩⟩
  rcases go_visit X code hI0 hgo (i, c) hc with he | ⟨sti, ins, p, rc, acc1, hI, -, hdrop, hp, hp2, hrest⟩
  · simp at he
  obtain ⟨hacc, hpend, hcur⟩ := go_arr X rc hrest hcn hpn
  obtain ⟨hI', hi'⟩ := stepI_inv hI hp
  rcases stepI_eq hp with ⟨-, -, rfl⟩ | ⟨c', hc', hall, hv⟩
  · cases hp2
  obtain ⟨z0, z, r, hz0, hz, hr, rfl⟩ := visit_eq hv
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  have hcok : ZOk body c' := by
    rcases hc' with hc' | ⟨-, q, hq, hqc⟩
    · exact hI.ok.cur c' (by simp [hc'])
    · exact hqc ▸ hI.ok.pend q ((spanP_mem _ _).1 hq)
  have hzok : ZOk body z := hintsStep_ok X _ (normZ_ok _ hcok hz0) hz
  refine ⟨ins, z0, z, sti.tabs, r, ?_, hcok, hz0, ?_, hzok, hr, ?_, ?_, ?_⟩
  · rw [← List.head?_drop, Nat.sub_zero] at *
    rw [hdrop]; rfl
  · rw [← hsInv_lookup hI.hs]; exact hz
  · intro z1 hz1
    exact hcur z1 hz1
  · intro q hq
    exact hpend q (mem_mergeP _ _ (Or.inl hq))
  · intro oc od of x arms ss a hins hzc hzero hfwd ha j hj
    subst hins
    obtain ⟨-, -, hx, hcase⟩ := jump_match hr hzc hzero hfwd ha
    rcases hcase with ⟨hhit, -⟩ | ⟨-, hl, -⟩
    · simp only [tabHit, List.any_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hhit
      obtain ⟨t, ht, ⟨hb, hk⟩, hlt⟩ := hhit
      obtain ⟨x', arms', ss', hz', hj'⟩ := hI.tab t ht (by omega)
      have hteq : t.2.1 = z := ZOk.eq_of_key (hI.ok.tabs t ht) hzok (keyEq_iff.mp hk)
      rw [hteq, hzc] at hz'
      simp only [List.cons.injEq, Stmt.match_.injEq] at hz'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hz'
      obtain ⟨tg, c', h1, h2, h3, h4⟩ := hj' j hj
      rw [hb, hteq] at *
      refine ⟨tg, c', h1, h2, hpend (tg - X.entry, c') (mem_mergeP _ _ (Or.inr ?_)), by omega⟩
      rcases spanP_split sti.i sti.pend h4 with ⟨-, he⟩ | h5
      · simp only at he; omega
      · exact h5
    · obtain ⟨t, c', h1, h2, h3, h4⟩ := armZs_arr X _ z _ ss a.2 arms 0 hl j hj
      simp only [Nat.zero_add] at h1 h2
      exact ⟨t, c', h1, h2, hpend _ (mem_mergeP _ _ (Or.inl h3)), h4⟩


/-! ## Positions -/

/-- The head of a normalized zipper, if an atom, is a flow hint atom. -/
@[expose] def HeadFlow (z : Zip) : Prop := ∀ a ss, z.cur = .atom a :: ss → flowAtom a = true

theorem Zip.pos_cons (up : List (ℕ × ℕ × List Stmt)) (k : ℕ) (s : Stmt) (ss : List Stmt) :
    Zip.pos ⟨up, k, s :: ss⟩ = s :: Zip.pos ⟨up, k + 1, ss⟩ := rfl

/-- **The normalization skips atoms that pop nothing**: the position is theirs, then the normalized
one's. -/
theorem normZ_pos : ∀ (f : ℕ) {z z' : Zip}, normZ f z = some z' →
    ∃ as : List Atom, (∀ a ∈ as, flowAtom a = false) ∧ z.pos = as.map Stmt.atom ++ z'.pos ∧ HeadFlow z'
  | 0, _, _, h => by simp [normZ] at h
  | f + 1, z, z', h => by
    rw [normZ_succ] at h
    obtain ⟨up, k, cur⟩ := z
    cases cur with
    | cons s ss =>
      cases s
      case atom a =>
        simp only [normStep] at h
        cases hf : flowAtom a <;> simp only [hf, natSeq_eq, Bool.cond_false, Bool.cond_true] at h
        · obtain ⟨as, h1, h2, h3⟩ := normZ_pos f h
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
        simp only [normStep, Option.some.injEq] at h
        subst h
        exact ⟨[], by simp, rfl, fun b ss' hb ↦ by simp at hb⟩
    | nil =>
      cases up with
      | nil =>
        simp only [normStep, Option.some.injEq] at h
        subst h
        exact ⟨[], by simp, rfl, fun b ss' hb ↦ by simp at hb⟩
      | cons e up =>
        obtain ⟨k', c, ss⟩ := e
        simp only [normStep, natSeq_eq] at h
        obtain ⟨as, h1, h2, h3⟩ := normZ_pos f h
        exact ⟨as, h1, by rw [← h2]; simp [Zip.pos], h3⟩

/-- A hint atom of the frame's flow compiling an ISA flow hint. -/
@[expose] def Pairs (X : AlignCtx) (a : Atom) (h : Prover.Exec.Hint) : Prop :=
  ∃ hc, a = .hint hc ∧ compiles X.locAt hc h = true

/-- **The hints at an offset consume their atoms**: the position is atoms then the one after the
hints, the flow ones compiling the flow hints one for one. -/
theorem hintsStep_pos (X : AlignCtx) : ∀ (hs : List Prover.Exec.Hint) {z z' : Zip}, HeadFlow z →
    hintsStep X hs z = some z' → ∃ as : List Atom, z.pos = as.map Stmt.atom ++ z'.pos ∧
      List.Forall₂ (Pairs X) (as.filter flowAtom) (hs.filter isaFlowHint) ∧ HeadFlow z'
  | [], _, _, hz, h => by cases h; exact ⟨[], rfl, by simp, hz⟩
  | hd :: hs, z, z', hz, h => by
    change hintStep X (hintsStep X hs) hd z = some z' at h
    simp only [hintStep, Bool.cond_eq_ite] at h
    split at h
    · rename_i hfl
      split at h
      · rename_i hc ss heq
        split at h
        · rename_i hcomp
          obtain ⟨z1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨as1, ha1, hp1, hf1⟩ := normZ_pos _ h1
          obtain ⟨as2, hp2, hf2, hz2⟩ := hintsStep_pos X hs hf1 h2
          have hflow : flowAtom (.hint hc) = true := hz _ _ heq
          refine ⟨.hint hc :: (as1 ++ as2), ?_, ?_, hz2⟩
          · obtain ⟨up, k, cur⟩ := z
            simp only at heq
            subst heq
            rw [Zip.pos_cons, List.map_cons, List.map_append, List.cons_append, List.append_assoc, ← hp2, ← hp1,
              Zip.next_eq]
          · have hf : as1.filter flowAtom = [] := List.filter_eq_nil_iff.mpr fun a ha ↦ by simp [ha1 a ha]
            rw [List.filter_cons_of_pos hflow, List.filter_append, hf, List.nil_append,
              List.filter_cons_of_pos hfl]
            exact List.Forall₂.cons ⟨hc, rfl, hcomp⟩ hf2
        · cases h
      · cases h
    · rename_i hfl
      obtain ⟨as, h1, h2, h3⟩ := hintsStep_pos X hs hz h
      refine ⟨as, h1, ?_, h3⟩
      rw [List.filter_cons_of_neg hfl]
      exact h2

/-! ## The record -/

theorem stepI_i {X : AlignCtx} {ins : OffsetInstruction} {st : St} {p : St × Option (ℕ × Zip)}
    (h : stepI X ins st = some p) : p.1.i = st.i + 1 := by
  rcases stepI_eq h with ⟨-, -, rfl⟩ | ⟨c, -, -, hv⟩
  · rfl
  · obtain ⟨z0, z, r, -, -, -, rfl⟩ := visit_eq hv
    rfl

/-- The pass records each offset once, the later first. -/
theorem alignGo_desc (X : AlignCtx) : ∀ (code : List OffsetInstruction) {st st' : St} {acc acc' : List (ℕ × Zip)},
    alignGo X code st acc = some (st', acc') → acc.Pairwise (fun a b ↦ b.1 < a.1) → (∀ e ∈ acc, e.1 < st.i) →
      acc'.Pairwise (fun a b ↦ b.1 < a.1)
  | [], _, _, _, _, h, hp, _ => by
    simp only [alignGo, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact hp
  | ins :: code, st, st', acc, acc', h, hp, hlt => by
    rw [alignGo_cons] at h
    obtain ⟨p, hp1, h⟩ := Option.bind_eq_some_iff.mp h
    have hi := stepI_i hp1
    have hr := stepI_rec X ins hp1
    refine alignGo_desc X code h ?_ fun e he ↦ ?_
    · rw [List.pairwise_append]
      refine ⟨?_, hp, fun a ha b hb ↦ ?_⟩
      · cases hq : p.2 <;> simp
      · rw [hr a (Option.mem_toList.mp ha)]; exact hlt b hb
    · rcases List.mem_append.mp he with he | he
      · rw [hr e (Option.mem_toList.mp he)]; omega
      · have := hlt e he; omega

theorem lookup_of_desc : ∀ {l : List (ℕ × Zip)}, l.Pairwise (fun a b ↦ b.1 < a.1) → ∀ {o : ℕ} {c : Zip},
    (o, c) ∈ l → l.lookup o = some c
  | [], _, _, _, h => by simp at h
  | a :: l, hp, o, c, h => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp h with rfl | h
    · simp [List.lookup]
    · have := hp.1 _ h
      rw [List.lookup, show (o == a.1) = false by simp only at this; simp; omega]
      exact lookup_of_desc hp.2 h

theorem mem_of_lookup : ∀ {l : List (ℕ × Zip)} {o : ℕ} {c : Zip}, l.lookup o = some c → (o, c) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | ⟨k, b⟩ :: l, o, c, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he
      cases h
      have : o = k := by simpa using he
      rw [this]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- **An arrival recorded is the position there**, the zippers their cursors'. -/
theorem alignAt_of_arr {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : alignPre X d = true) {l : List (ℕ × Zip)}
    (h : alignRun X body code d = some l) {o : ℕ} {z : Zip} (ha : Arr l o z) (hz : ZOk body z) :
    alignAt X body code d o = some z.pos := by
  obtain ⟨c, hc, hk⟩ := ha
  obtain ⟨-, -, -, -, -, -, hcok, -⟩ := alignRun_step hpre h hc
  have hdesc : l.Pairwise (fun a b ↦ b.1 < a.1) := by
    simp only [alignRun] at h
    obtain ⟨⟨st', acc'⟩, hgo, hend⟩ := Option.bind_eq_some_iff.mp h
    simp only [alignEnd, Bool.cond_eq_ite] at hend
    split at hend
    · cases hend; exact alignGo_desc X code hgo (by simp) (by simp)
    · cases hend
  simp only [alignAt, h, Option.bind_some, lookup_of_desc hdesc hc, Option.map_some, ZOk.eq_of_key hcok hz hk]

/-- **The alignment at an offset it reaches**, by positions: the position there is the atoms its
hints consume (the flow ones compiling them one for one) and those that pop nothing, then the
position its instruction steps from; what falls through is the next offset's position, each arrival
its target's, and a `match`'s table jump's arms their targets'. -/
theorem alignAt_step {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hok : alignOk X body code d = true) {i : ℕ}
    {pos : List Stmt} (hat : alignAt X body code d i = some pos) :
    ∃ ins z tabs r, ∃ as : List Atom, code[i]? = some ins ∧ ZOk body z ∧ pos = as.map Stmt.atom ++ z.pos ∧
      List.Forall₂ (Pairs X) (as.filter flowAtom) (((d.2.2.lookup (X.entry + i)).getD []).filter isaFlowHint) ∧
      HeadFlow z ∧ insStep X i ins tabs z = some r ∧
      (∀ z1 ∈ r.1, alignAt X body code d (i + 1) = some z1.pos) ∧
      (∀ p ∈ r.2, alignAt X body code d p.1 = some p.2.pos) ∧
      ∀ oc od of x arms ss a, ins = .jump oc od of → z.cur = .match_ x arms :: ss → X.zeroAt oc = false →
        fwdJ X i oc od of = false → getF X.arms od = some a →
        ∀ j < arms.length, ∃ t, getF X.jt (a.2 + j) = some t ∧ X.entry + i < t ∧ ∃ c',
          normZ X.fuel (z.enter (.match_ x arms) ss j) = some c' ∧ alignAt X body code d (t - X.entry) = some c'.pos := by
  rw [alignOk, AlignCtx.seq_eq] at hok
  change (alignPre X d && (alignRun X body code d).isSome) = true at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hpre, hrun⟩ := hok
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hrun
  have hlk : (l.lookup i).map Zip.pos = some pos := by
    simpa only [alignAt, hl, Option.bind_some] using hat
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hlk
  obtain ⟨ins, z0, z, tabs, r, hins, hcok, hz0, hz, hzok, hr, h1, h2, h3⟩ := alignRun_step hpre hl (mem_of_lookup hc)
  obtain ⟨as1, ha1, hp1, hf1⟩ := normZ_pos _ hz0
  obtain ⟨as2, hp2, hf2, hzf⟩ := hintsStep_pos X _ hf1 hz
  have hout : (∀ c ∈ r.1, ZOk body c) ∧ ∀ p ∈ r.2, ZOk body p.2 := insStep_ok X i ins tabs hzok hr
  refine ⟨ins, z, tabs, r, as1 ++ as2, hins, hzok, ?_, ?_, hzf, hr,
    fun z1 hz1 ↦ alignAt_of_arr hpre hl (h1 z1 hz1) (hout.1 z1 hz1),
    fun p hp ↦ alignAt_of_arr hpre hl (h2 p hp) (hout.2 p hp), ?_⟩
  · rw [hp1, hp2, List.map_append, List.append_assoc]
  · have hf : as1.filter flowAtom = [] := List.filter_eq_nil_iff.mpr fun a ha ↦ by simp [ha1 a ha]
    rw [List.filter_append, hf, List.nil_append]
    exact hf2
  · intro oc od of x arms ss a hi hzc hzero hfwd ha j hj
    obtain ⟨t, c', ht, hc', harr, hlt⟩ := h3 oc od of x arms ss a hi hzc hzero hfwd ha j hj
    exact ⟨t, ht, hlt, c', hc', alignAt_of_arr hpre hl harr (normZ_ok _ (hzok.enter hzc j) hc')⟩

end

end LeanVM.Guest.Bridge
