/-
  LeanVM.Guest.Bridge.AlignRun

  The alignment pass's invariants: every zipper it carries is its cursor's (`ZOk`), its hints a suffix of the advice's, what it records apart from the rest; so a long function's pass, checked in windows from named states, is the whole pass (`alignOk_of_chain`).
-/

module

public import LeanVM.Guest.Bridge.AlignDefs

/-!
# The alignment pass's invariants

`ZOk body z`: the zipper is its cursor's, `zipOf body` of its key. The pass's steps keep it: past the head (`ZOk.next`), into a sub-block (`ZOk.enter`), the normalization (`normZ_ok`), the hints (`hintsStep_ok`), the jumps (`jumpStep_ok`), so each state of the pass has it (`StOk`, `stepI_ok`). Two zippers so with one cursor are one (`ZOk.eq_of_keyEq`).

What the pass records is apart from the rest (`St.noAcc`, `stepI_noAcc`, `alignGo_noAcc`), so a state is its name rebuilt (`stOfK_keyOfSt`), and the windows of a chain of named states (`Chain`) compose to the whole pass: `alignOk_of_chain`.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (natSeq natSeq_eq)

public section

/-! ## Zippers -/

/-- The cursors of a zipper's enclosing levels. -/
abbrev upKeys (up : List (ℕ × ℕ × List Stmt)) : List (ℕ × ℕ) := up.map fun e ↦ (e.1, e.2.1)

/-- **The zipper is its cursor's.** -/
def ZOk (body : List Stmt) (z : Zip) : Prop := z = zipOf body (upKeys z.up) z.k

theorem zOk_iff {body : List Stmt} {z : Zip} :
    ZOk body z ↔ z.up = zUp body (upKeys z.up) ∧ z.cur = (blockAt body (upKeys z.up)).drop z.k := by
  obtain ⟨up, k, cur⟩ := z
  simp only [ZOk, zipOf, Zip.mk.injEq, true_and]

theorem zOk_init (body : List Stmt) : ZOk body (Zip.init body) := by
  simp [ZOk, Zip.init, zipOf, zUp, blockAt]

theorem zOk_zipOf (body : List Stmt) (up : List (ℕ × ℕ)) (k : ℕ) : ZOk body (zipOf body up k) := by
  have h : upKeys (zUp body up) = up := by
    induction up with
    | nil => rfl
    | cons a up ih => obtain ⟨k', c⟩ := a; simp [zUp, ih]
  simp [ZOk, zipOf, h]

theorem Zip.next_eq (z : Zip) (ss : List Stmt) : z.next ss = ⟨z.up, z.k + 1, ss⟩ := by
  simp [Zip.next, natSeq_eq]

theorem ZOk.next {body : List Stmt} {z : Zip} (h : ZOk body z) {s : Stmt} {ss : List Stmt}
    (hc : z.cur = s :: ss) : ZOk body (z.next ss) := by
  rw [zOk_iff] at h ⊢
  rw [Zip.next_eq]
  refine ⟨h.1, ?_⟩
  simp only
  rw [← List.drop_drop, ← h.2, hc]
  rfl

theorem ZOk.enter {body : List Stmt} {z : Zip} (h : ZOk body z) {s : Stmt} {ss : List Stmt}
    (hc : z.cur = s :: ss) (c : ℕ) : ZOk body (z.enter s ss c) := by
  rw [zOk_iff] at h ⊢
  have hd : (blockAt body (upKeys z.up)).drop z.k = s :: ss := h.2 ▸ hc
  have hg : (blockAt body (upKeys z.up)).getD z.k default = s := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_drop, hd]; rfl
  have hs : (blockAt body (upKeys z.up)).drop (z.k + 1) = ss := by
    rw [← List.drop_drop, hd]; rfl
  simp only [Zip.enter, List.map_cons, zUp, blockAt, hg, hs, List.drop_zero, and_true]
  exact congrArg _ h.1

/-- **One cursor, one zipper.** -/
theorem ZOk.eq_of_key {body : List Stmt} {a b : Zip} (ha : ZOk body a) (hb : ZOk body b)
    (h : a.key = b.key) : a = b := by
  simp only [Zip.key, Prod.mk.injEq] at h
  calc a = zipOf body (upKeys a.up) a.k := ha
    _ = zipOf body (upKeys b.up) b.k := by simp only [upKeys]; rw [h.1, h.2]
    _ = b := hb.symm

theorem upEq_iff : ∀ {a b : List (ℕ × ℕ × List Stmt)}, Zip.upEq a b = true ↔ upKeys a = upKeys b
  | [], [] => by simp [Zip.upEq]
  | [], _ :: _ => by simp [Zip.upEq]
  | _ :: _, [] => by simp [Zip.upEq]
  | x :: a, y :: b => by
    simp only [Zip.upEq, Bool.and_eq_true, Nat.beq_eq, upEq_iff, List.map_cons, List.cons.injEq,
      Prod.mk.injEq]

theorem keyEq_iff {a b : Zip} : Zip.keyEq a b = true ↔ a.key = b.key := by
  simp [Zip.keyEq, Zip.key, upEq_iff, and_comm]

/-! ## The normalization -/

theorem normZ_succ (f : ℕ) (z : Zip) : normZ (f + 1) z = normStep (normZ f) z := rfl

theorem normZ_ok {body : List Stmt} : ∀ (f : ℕ) {z z' : Zip}, ZOk body z → normZ f z = some z' → ZOk body z'
  | 0, _, _, _, h => by simp [normZ] at h
  | f + 1, z, z', hz, h => by
    rw [normZ_succ] at h
    obtain ⟨up, k, cur⟩ := z
    cases cur with
    | cons s ss =>
      cases s
      case atom a =>
        simp only [normStep] at h
        cases hf : flowAtom a <;> simp only [hf, natSeq_eq] at h
        · have hn := hz.next (z := ⟨up, k, .atom a :: ss⟩) rfl
          rw [Zip.next_eq] at hn
          exact normZ_ok f hn h
        · cases h; exact hz
      all_goals (simp only [normStep, Option.some.injEq] at h; subst h; exact hz)
    | nil =>
      cases up with
      | nil => simp only [normStep, Option.some.injEq] at h; cases h; exact hz
      | cons e up =>
        obtain ⟨k', c, ss⟩ := e
        simp only [normStep, natSeq_eq] at h
        refine normZ_ok f ?_ h
        rw [zOk_iff] at hz ⊢
        simp only [List.map_cons, zUp, List.cons.injEq, Prod.mk.injEq, true_and] at hz
        exact ⟨hz.1.2, hz.1.1⟩

/-! ## The steps -/

/-- What a step hands on keeps the zippers their cursors'. -/
@[expose] def OutOk (body : List Stmt) (r : Option Zip × List (ℕ × Zip)) : Prop :=
  (∀ c ∈ r.1, ZOk body c) ∧ ∀ p ∈ r.2, ZOk body p.2

theorem hintsStep_ok {body : List Stmt} (X : AlignCtx) :
    ∀ (hs : List Prover.Exec.Hint) {z z' : Zip}, ZOk body z → hintsStep X hs z = some z' → ZOk body z'
  | [], _, _, hz, h => by cases h; exact hz
  | hd :: hs, z, z', hz, h => by
    change hintStep X (hintsStep X hs) hd z = some z' at h
    simp only [hintStep, Bool.cond_eq_ite] at h
    split at h
    · split at h
      · rename_i heq
        split at h
        · obtain ⟨z1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
          exact hintsStep_ok X hs (normZ_ok _ (hz.next heq) h1) h2
        · cases h
      · cases h
    · exact hintsStep_ok X hs hz h

theorem armZs_ok {body : List Stmt} (X : AlignCtx) (i : ℕ) {z : Zip} {s : Stmt} {ss : List Stmt}
    (hz : ZOk body z) (hc : z.cur = s :: ss) (base : ℕ) :
    ∀ (as : List (List Stmt)) (j : ℕ) {l : List (ℕ × Zip)}, armZs X i z s ss base j as = some l →
      ∀ p ∈ l, ZOk body p.2
  | [], _, _, h => by cases h; simp
  | _ :: as, j, l, h => by
    simp only [armZs] at h
    split at h
    · rename_i hn
      split at h
      · rename_i l' _ hl
        cases h
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact normZ_ok _ (hz.enter hc j) hn
        · exact armZs_ok X i hz hc base as (j + 1) hl p hp
      · cases h
    · cases h

theorem headStep_ok {body : List Stmt} (X : AlignCtx) (i oc od of : ℕ) (tabs : List (ℕ × Zip × ℕ)) {z : Zip}
    {r : Option Zip × List (ℕ × Zip)} (hz : ZOk body z) (h : headStep X i oc od of tabs z = some r) : OutOk body r := by
  simp only [headStep, Bool.cond_eq_ite] at h
  split at h
  all_goals rename_i heq
  all_goals (repeat' split at h)
  all_goals (try cases h)
  all_goals (try (obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h))
  all_goals refine ⟨fun c hc ↦ ?_, fun p hp ↦ ?_⟩
  all_goals (try simp only [Option.mem_def, Option.some.injEq, reduceCtorEq] at hc)
  all_goals (try simp only [List.mem_cons, List.not_mem_nil, or_false] at hp)
  all_goals (try subst hc)
  all_goals (try subst hp)
  all_goals first
    | exact armZs_ok X i hz heq _ _ 0 ho p hp
    | (apply normZ_ok _ (hz.next heq); assumption)
    | (apply normZ_ok _ (hz.enter heq 0); assumption)
    | (apply normZ_ok _ (hz.enter heq 1); assumption)

theorem jumpStep_ok {body : List Stmt} (X : AlignCtx) (i oc od of : ℕ) (tabs : List (ℕ × Zip × ℕ)) {z : Zip}
    {r : Option Zip × List (ℕ × Zip)} (hz : ZOk body z) (h : jumpStep X i oc od of tabs z = some r) : OutOk body r := by
  simp only [jumpStep, Bool.cond_eq_ite] at h
  split at h
  · cases h; exact ⟨by simpa using hz, by simp⟩
  split at h
  · obtain ⟨t, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨by simp, by simpa using hz⟩
  · exact headStep_ok X i oc od of tabs hz h

theorem insStep_ok {body : List Stmt} (X : AlignCtx) (i : ℕ) (ins : OffsetInstruction) (tabs : List (ℕ × Zip × ℕ)) {z : Zip}
    {r : Option Zip × List (ℕ × Zip)} (hz : ZOk body z) (h : insStep X i ins tabs z = some r) : OutOk body r := by
  cases ins
  case jump oc od of => exact jumpStep_ok X i oc od of tabs hz h
  all_goals (cases h; exact ⟨by simpa using hz, by simp⟩)

/-! ## The pass's states -/

/-- **A state of the pass from the advice's hints `hs`**: its hints a suffix of them, its zippers
their cursors'. -/
structure StOk (body : List Stmt) (hs : List (ℕ × List Prover.Exec.Hint)) (st : St) : Prop where
  hs : ∃ n, st.hs = hs.drop n
  cur : ∀ z ∈ st.cur, ZOk body z
  pend : ∀ p ∈ st.pend, ZOk body p.2
  tabs : ∀ t ∈ st.tabs, ZOk body t.2.1

theorem insP_mem (a : ℕ × Zip) : ∀ (l : List (ℕ × Zip)) {p : ℕ × Zip}, p ∈ insP a l → p = a ∨ p ∈ l
  | [], p, h => by simp [insP] at h; exact Or.inl h
  | b :: l, p, h => by
    change p ∈ (bif Nat.blt b.1 a.1 then b :: insP a l else a :: b :: l) at h
    cases hb : Nat.blt b.1 a.1 <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr List.mem_cons_self
      · rcases insP_mem a l h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mergeP_mem : ∀ (as l : List (ℕ × Zip)) {p : ℕ × Zip}, p ∈ mergeP as l → p ∈ as ∨ p ∈ l
  | [], _, _, h => Or.inr h
  | a :: as, l, p, h => by
    change p ∈ insP a (mergeP as l) at h
    rcases insP_mem a _ h with rfl | h
    · exact Or.inl List.mem_cons_self
    · rcases mergeP_mem as l h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

theorem spanP_mem (i : ℕ) : ∀ (l : List (ℕ × Zip)) {p : ℕ × Zip},
    (p ∈ (spanP i l).1 → p ∈ l) ∧ (p ∈ (spanP i l).2 → p ∈ l)
  | [], _ => by simp [spanP]
  | a :: l, p => by
    change (p ∈ (bif Nat.beq a.1 i then (match spanP i l with | (h, t) => (a :: h, t)) else ([], a :: l)).1 → _) ∧
      (p ∈ (bif Nat.beq a.1 i then (match spanP i l with | (h, t) => (a :: h, t)) else ([], a :: l)).2 → _)
    have ih := spanP_mem i l (p := p)
    cases hb : Nat.beq a.1 i <;> simp only [Bool.cond_true, Bool.cond_false]
    · simp
    · generalize spanP i l = S at ih ⊢
      obtain ⟨h, t⟩ := S
      simp only [List.mem_cons] at ih ⊢
      exact ⟨fun h' ↦ h'.elim Or.inl fun h' ↦ Or.inr (ih.1 h'), fun h' ↦ Or.inr (ih.2 h')⟩

theorem hintsAt_suffix (pc : ℕ) (hs : List (ℕ × List Prover.Exec.Hint)) {n : ℕ} {l : List (ℕ × List Prover.Exec.Hint)}
    (h : l = hs.drop n) : ∃ m, (hintsAt pc l).2 = hs.drop m := by
  subst h
  cases hd : hs.drop n with
  | nil => exact ⟨n, by simp [hintsAt, hd]⟩
  | cons a t =>
    obtain ⟨p, q⟩ := a
    change ∃ m, (bif Nat.beq p pc then (q, t) else ([], (p, q) :: t)).2 = hs.drop m
    cases Nat.beq p pc
    · exact ⟨n, by simp [hd]⟩
    · refine ⟨n + 1, ?_⟩
      simp only [Bool.cond_true]
      rw [← List.drop_drop, hd]; rfl

theorem tabReg_ok {body : List Stmt} (X : AlignCtx) (i : ℕ) (ins : OffsetInstruction) {z : Zip} (hz : ZOk body z)
    (tg : List (ℕ × Zip)) {tabs : List (ℕ × Zip × ℕ)} (ht : ∀ t ∈ tabs, ZOk body t.2.1) :
    ∀ t ∈ tabReg X i ins z tg tabs, ZOk body t.2.1 := by
  simp only [tabReg, Bool.cond_eq_ite]
  split
  · split
    · exact ht
    split
    · intro t ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact hz
      · exact ht t ht'
    · exact ht
  · exact ht

theorem visit_ok {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} (X : AlignCtx)
    (ins : OffsetInstruction) (i i' : ℕ) (h1 : List Prover.Exec.Hint) (hs' : List (ℕ × List Prover.Exec.Hint))
    (rest : List (ℕ × Zip)) (tabs : List (ℕ × Zip × ℕ)) {c : Zip} {r : St × Option (ℕ × Zip)}
    (hhs : ∃ n, hs' = hs0.drop n) (hrest : ∀ p ∈ rest, ZOk body p.2) (htabs : ∀ t ∈ tabs, ZOk body t.2.1)
    (hc : ZOk body c) (h : visit X ins i i' h1 hs' rest tabs c = some r) : StOk body hs0 r.1 ∧ r.1.i = i' := by
  simp only [visit] at h
  obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨z1, hz1, hz⟩ := Option.bind_eq_some_iff.mp hz
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  have hzok := hintsStep_ok X h1 (normZ_ok _ hc hz1) hz
  have hout := insStep_ok X i ins tabs hzok hq
  refine ⟨⟨hhs, hout.1, fun p hp ↦ ?_, tabReg_ok X i ins hzok _ htabs⟩, rfl⟩
  rcases mergeP_mem _ _ hp with hp | hp
  · exact hout.2 p hp
  · exact hrest p hp

/-- **A step keeps a state of the pass**, its offset the next. -/
theorem stepI_ok {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} (X : AlignCtx)
    (ins : OffsetInstruction) {st : St} {r : St × Option (ℕ × Zip)} (hst : StOk body hs0 st)
    (h : stepI X ins st = some r) : StOk body hs0 r.1 ∧ r.1.i = st.i + 1 := by
  unfold stepI at h
  rw [natSeq_eq] at h
  obtain ⟨n, hn⟩ := hst.hs
  have hsuf := hintsAt_suffix (Nat.add X.entry st.i) hs0 hn
  have hsp : ∀ p, _ := fun p ↦ spanP_mem st.i st.pend (p := p)
  generalize hS : spanP st.i st.pend = S at h hsp
  generalize hH : hintsAt (Nat.add X.entry st.i) st.hs = H at h hsuf
  obtain ⟨here, rest⟩ := S
  obtain ⟨h1, hs'⟩ := H
  have hrest : ∀ p ∈ rest, ZOk body p.2 := fun p hp ↦ hst.pend p ((hsp p).2 hp)
  simp only [Bool.cond_eq_ite] at h
  split at h
  · split at h
    · exact visit_ok X ins _ _ h1 hs' rest _ hsuf hrest hst.tabs (hst.cur _ (by simp_all)) h
    · cases h
  · cases h
    exact ⟨⟨hsuf, by simp, hrest, hst.tabs⟩, rfl⟩
  · split at h
    · exact visit_ok X ins _ _ h1 hs' rest _ hsuf hrest hst.tabs
        (hst.pend _ ((hsp _).1 (by simp_all))) h
    · cases h

theorem alignGo_cons (X : AlignCtx) (ins : OffsetInstruction) (code : List OffsetInstruction) (st : St)
    (acc : List (ℕ × Zip)) :
    alignGo X (ins :: code) st acc = (stepI X ins st).bind fun p ↦ alignGo X code p.1 (p.2.toList ++ acc) := rfl

theorem alignGo_append (X : AlignCtx) : ∀ (c1 c2 : List OffsetInstruction) (st : St) (acc : List (ℕ × Zip)),
    alignGo X (c1 ++ c2) st acc = (alignGo X c1 st acc).bind fun p ↦ alignGo X c2 p.1 p.2
  | [], _, _, _ => rfl
  | ins :: c1, c2, st, acc => by
    rw [List.cons_append, alignGo_cons, alignGo_cons, Option.bind_assoc]
    congr 1
    funext p
    exact alignGo_append X c1 c2 _ _

/-- **What the pass records is apart from the rest.** -/
theorem alignGo_acc (X : AlignCtx) : ∀ (c : List OffsetInstruction) (st : St) (acc : List (ℕ × Zip)),
    alignGo X c st acc = (alignGo X c st []).map fun p ↦ (p.1, p.2 ++ acc)
  | [], _, _ => by simp [alignGo]
  | ins :: c, st, acc => by
    rw [alignGo_cons, alignGo_cons, Option.map_bind]
    congr 1
    funext p
    simp only [Function.comp_apply]
    rw [alignGo_acc X c _ (p.2.toList ++ acc), alignGo_acc X c _ (p.2.toList ++ []), Option.map_map]
    congr 1
    funext q
    simp

theorem alignGo_ok {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} (X : AlignCtx) :
    ∀ (c : List OffsetInstruction) {st st' : St} {acc acc' : List (ℕ × Zip)}, StOk body hs0 st →
      alignGo X c st acc = some (st', acc') → StOk body hs0 st' ∧ st'.i = st.i + c.length
  | [], _, _, _, _, hst, h => by
    simp only [alignGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hst, rfl⟩
  | ins :: c, st, st', acc, acc', hst, h => by
    rw [alignGo_cons] at h
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hp1, hpi⟩ := stepI_ok X ins hst hp
    obtain ⟨h1, h2⟩ := alignGo_ok X c hp1 h
    exact ⟨h1, by rw [h2, hpi, List.length_cons]; omega⟩

/-! ## Windows -/

theorem lenTR_eq {α : Type} : ∀ (l : List α) (n : ℕ), lenTR l n = l.length + n
  | [], n => by simp [lenTR]
  | _ :: l, n => by simp only [lenTR, natSeq_eq, lenTR_eq l, List.length_cons]; omega

theorem zipOf_key {body : List Stmt} {z : Zip} (h : ZOk body z) : zipOf body z.key.1 z.key.2 = z := h.symm

/-- **A state is its name rebuilt.** -/
theorem stOfK_keyOfSt {body : List Stmt} {hs : List (ℕ × List Prover.Exec.Hint)} {st : St}
    (h : StOk body hs st) : stOfK body hs (keyOfSt hs st) = st := by
  obtain ⟨i, shs, cur, pend, tabs⟩ := st
  obtain ⟨⟨n, hn⟩, hcur, hpend, htabs⟩ := h
  simp only at hn hcur hpend htabs
  simp only [stOfK, keyOfSt, St.mk.injEq, true_and, lenTR_eq, Nat.add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · subst hn
    rw [List.length_drop]
    by_cases hle : n ≤ hs.length
    · rw [show hs.length - (hs.length - n) = n by omega]
    · rw [show hs.length - n = 0 by omega, Nat.sub_zero, List.drop_length,
        List.drop_eq_nil_of_le (by omega)]
  · cases cur with
    | none => rfl
    | some z => simp only [Option.map_some, Option.some.injEq]; exact zipOf_key (hcur z rfl)
  · rw [List.map_map]
    conv_rhs => rw [← List.map_id pend]
    exact List.map_congr_left fun p hp ↦ by simp only [Function.comp_apply, id]; rw [zipOf_key (hpend p hp)]
  · rw [List.map_map]
    conv_rhs => rw [← List.map_id tabs]
    exact List.map_congr_left fun t ht ↦ by simp only [Function.comp_apply, id]; rw [zipOf_key (htabs t ht)]

theorem AlignCtx.seq_eq {β : Type} (X : AlignCtx) (k : AlignCtx → β) : X.seq k = k X := by
  obtain ⟨loc, locOk, extra, entry, main, stat, sites, arms, pows, jt, ents, halt, len, fuel⟩ := X
  simp only [AlignCtx.seq, Exec.Trie.seq_eq, natSeq_eq]

/-- **A chain of named states**: each window of the pass from one to the next, the last at the end. -/
@[expose] def Chain (X : AlignCtx) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : KSt → List KSt → Prop
  | K, [] => chainEnd code K = true
  | K, K' :: ks => winOk X body code d K K' = true ∧ Chain X body code d K' ks

theorem chain_go {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} :
    ∀ (ks : List KSt) (K : KSt) (st : St) (acc : List (ℕ × Zip)), Chain X body code d K ks →
      StOk body d.2.2 st → stOfK body d.2.2 K = st →
      ((alignGo X (code.drop K.i) st acc).bind fun p ↦ alignEnd p.1 p.2).isSome
  | [], K, st, acc, hc, _, hk => by
    simp only [Chain, chainEnd, Bool.and_eq_true, Nat.beq_eq, Option.isNone_iff_eq_none,
      List.isEmpty_iff, lenTR_eq, Nat.add_zero] at hc
    obtain ⟨⟨hi, hcur⟩, hpend⟩ := hc
    subst hk
    rw [hi, List.drop_length]
    simp [alignGo, alignEnd, stOfK, hcur, hpend]
  | K' :: ks, K, st, acc, hc, hst, hk => by
    obtain ⟨hw, hc⟩ := hc
    rw [winOk, AlignCtx.seq_eq, decide_eq_true_eq, hk] at hw
    obtain ⟨⟨st1, acc1⟩, h1, hK⟩ := Option.map_eq_some_iff.mp hw
    obtain ⟨hst1, hi1⟩ := alignGo_ok X _ hst h1
    have hKi : K'.i = st1.i := by rw [← hK]; rfl
    have hsi : st.i = K.i := by rw [← hk]; rfl
    have hlen := List.length_take_le (K'.i - K.i) (code.drop K.i)
    have hle : K.i ≤ K'.i := by omega
    have hsplit : code.drop K.i = (code.drop K.i).take (K'.i - K.i) ++ code.drop K'.i := by
      conv_lhs => rw [← List.take_append_drop (K'.i - K.i) (code.drop K.i)]
      rw [List.drop_drop, show K.i + (K'.i - K.i) = K'.i by omega]
    rw [hsplit, alignGo_append, alignGo_acc, h1]
    simp only [Option.map_some, Option.bind_some]
    exact chain_go ks K' st1 (acc1 ++ acc) hc hst1 (by rw [← hK]; exact stOfK_keyOfSt hst1)

/-- **A chain of windows is the whole pass.** -/
theorem alignOk_of_chain {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : alignPre X d = true) {ks : List KSt}
    (hc : Chain X body code d ⟨0, 0, some ([], 0), [], []⟩ ks) : alignOk X body code d = true := by
  rw [alignOk, AlignCtx.seq_eq]
  change (alignPre X d && (alignRun X body code d).isSome) = true
  rw [hpre, Bool.true_and]
  have h0 : stOfK body d.2.2 ⟨0, 0, some ([], 0), [], []⟩ = ⟨0, d.2.2, some (Zip.init body), [], []⟩ := by
    simp [stOfK, zipOf, zUp, blockAt, Zip.init]
  have hst : StOk body d.2.2 ⟨0, d.2.2, some (Zip.init body), [], []⟩ :=
    ⟨⟨0, rfl⟩, by simpa using zOk_init body, by simp, by simp⟩
  have := chain_go ks _ _ [] hc hst h0
  simpa [alignRun] using this

end

end LeanVM.Guest.Bridge
