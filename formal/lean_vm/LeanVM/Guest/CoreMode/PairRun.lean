/-
  LeanVM.Guest.CoreMode.PairRun

  The pairing pass's invariants: every zipper it carries is its cursor's, its hints a suffix of the
  advice's, what it records apart from the rest; so a long function's pass, checked in windows from
  named states, is the whole pass (`pairOk_of_chainS`, `PairSlice.lean`).
-/

module

public import LeanVM.Guest.CoreMode.PairDefs
public import LeanVM.Guest.Bridge.AlignRun

/-!
# The pairing pass's invariants

`Bridge/AlignRun.lean`'s for the heap-aware pass: each step keeps the zippers their cursors' (`Bridge.ZOk`: `normG_ok`, `hintsStepH_ok`, `scan_ok`, `plainStep_ok`, `jumpStepH_ok`), so each state of the pass is a `Bridge.StOk` (`stepIH_ok`), and the pass over code split in two is the pass over the first part, then over the rest from where it ended (`pairGo_append`), which `PairSlice.lean`'s windows compose by (`pairOk_of_chainS`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Bridge
open LeanVM.Guest.Exec (natSeq natSeq_eq)

public section

/-! ## The normalization -/

theorem normG_succ (stop : Atom → Bool) (f : ℕ) (z : Zip) : normG stop (f + 1) z = normStepG stop (normG stop f) z :=
  rfl

theorem normG_ok {body : List Stmt} (stop : Atom → Bool) :
    ∀ (f : ℕ) {z z' : Zip}, ZOk body z → normG stop f z = some z' → ZOk body z'
  | 0, _, _, _, h => by simp [normG] at h
  | f + 1, z, z', hz, h => by
    rw [normG_succ] at h
    obtain ⟨up, k, cur⟩ := z
    cases cur with
    | cons s ss =>
      cases s
      case atom a =>
        simp only [normStepG] at h
        cases hf : stop a <;> simp only [hf, natSeq_eq] at h
        · have hn := hz.next (z := ⟨up, k, .atom a :: ss⟩) rfl
          rw [Zip.next_eq] at hn
          exact normG_ok stop f hn h
        · cases h; exact hz
      all_goals (simp only [normStepG, Option.some.injEq] at h; subst h; exact hz)
    | nil =>
      cases up with
      | nil => simp only [normStepG, Option.some.injEq] at h; cases h; exact hz
      | cons e up =>
        obtain ⟨k', c, ss⟩ := e
        simp only [normStepG, natSeq_eq] at h
        refine normG_ok stop f ?_ h
        rw [zOk_iff] at hz ⊢
        simp only [List.map_cons, zUp, List.cons.injEq, Prod.mk.injEq, true_and] at hz
        exact ⟨hz.1.2, hz.1.1⟩

theorem PairCtx.nL_ok {body : List Stmt} (P : PairCtx) {z z' : Zip} (hz : ZOk body z) (h : P.nL z = some z') :
    ZOk body z' :=
  normG_ok _ _ hz h

theorem PairCtx.nS_ok {body : List Stmt} (P : PairCtx) {z z' : Zip} (hz : ZOk body z) (h : P.nS z = some z') :
    ZOk body z' :=
  normG_ok _ _ hz h

/-! ## The steps -/

theorem hintsStepH_ok {body : List Stmt} (P : PairCtx) :
    ∀ (hs : List Prover.Exec.Hint) {z z' : Zip}, ZOk body z → hintsStepH P hs z = some z' → ZOk body z'
  | [], _, _, hz, h => by cases h; exact hz
  | hd :: hs, z, z', hz, h => by
    change hintStepH P (hintsStepH P hs) hd z = some z' at h
    simp only [hintStepH, Bool.cond_eq_ite] at h
    split at h
    · obtain ⟨z1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      have hz1 := P.nS_ok hz h1
      split at h
      · rename_i heq
        split at h
        · obtain ⟨z2, h2, h3⟩ := Option.bind_eq_some_iff.mp h
          exact hintsStepH_ok P hs (P.nL_ok (hz1.next heq) h2) h3
        · cases h
      · cases h
    · exact hintsStepH_ok P hs hz h

theorem scan_ok {body : List Stmt} (P : PairCtx) (o1 o2 o3 : ℕ) :
    ∀ (f : ℕ) {z : Zip} {r : Zip × Bool}, ZOk body z → scan P o1 o2 o3 f z = some r → ZOk body r.1
  | 0, _, _, _, h => by simp [scan] at h
  | f + 1, z, r, hz, h => by
    change scanStep P o1 o2 o3 (scan P o1 o2 o3 f) z = some r at h
    simp only [scanStep, Bool.cond_eq_ite] at h
    split at h
    · rename_i d p off ss heq
      split at h
      · obtain ⟨z', h1, rfl⟩ := Option.map_eq_some_iff.mp h
        exact P.nL_ok (hz.next heq) h1
      · split at h
        · obtain ⟨z', h1, h2⟩ := Option.bind_eq_some_iff.mp h
          exact scan_ok P o1 o2 o3 f (P.nL_ok (hz.next heq) h1) h2
        · cases h
    · cases h

theorem plainStep_ok {body : List Stmt} (P : PairCtx) (i : ℕ) (ins : OffsetInstruction) {z z' : Zip}
    (hz : ZOk body z) (h : plainStep P i ins z = some z') : ZOk body z' := by
  unfold plainStep at h
  split at h
  · split at h
    · rename_i z1 b hs
      simp only [Bool.cond_eq_ite] at h
      split at h
      · cases h; exact scan_ok P _ _ _ _ hz hs
      · cases h
    · simp only [Bool.cond_eq_ite] at h
      split at h
      · cases h; exact hz
      · cases h
  · simp only [Bool.cond_eq_ite] at h
    split at h
    · cases h; exact hz
    · cases h

theorem armZsH_ok {body : List Stmt} (P : PairCtx) (i : ℕ) {z : Zip} {s : Stmt} {ss : List Stmt}
    (hz : ZOk body z) (hc : z.cur = s :: ss) (base : ℕ) :
    ∀ (as : List (List Stmt)) (j : ℕ) {l : List (ℕ × Zip)}, armZsH P i z s ss base j as = some l →
      ∀ p ∈ l, ZOk body p.2
  | [], _, _, h => by cases h; simp
  | _ :: as, j, l, h => by
    simp only [armZsH] at h
    split at h
    · rename_i hn
      split at h
      · rename_i l' _ hl
        cases h
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact P.nL_ok (hz.enter hc j) hn
        · exact armZsH_ok P i hz hc base as (j + 1) hl p hp
      · cases h
    · cases h

theorem headStepH_ok {body : List Stmt} (P : PairCtx) (i oc od of : ℕ) (tabs : List (ℕ × Zip × ℕ)) {z : Zip}
    {r : Option Zip × List (ℕ × Zip)} (hz : ZOk body z) (h : headStepH P i oc od of tabs z = some r) :
    OutOk body r := by
  simp only [headStepH, Bool.cond_eq_ite] at h
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
    | exact armZsH_ok P i hz heq _ _ 0 ho p hp
    | (apply P.nL_ok (hz.next heq); assumption)
    | (apply P.nL_ok (hz.enter heq 0); assumption)
    | (apply P.nL_ok (hz.enter heq 1); assumption)

theorem jumpStepH_ok {body : List Stmt} (P : PairCtx) (i oc od of : ℕ) (tabs : List (ℕ × Zip × ℕ)) {z zs : Zip}
    {r : Option Zip × List (ℕ × Zip)} (hz : ZOk body z) (hzs : ZOk body zs)
    (h : jumpStepH P i oc od of tabs z zs = some r) : OutOk body r := by
  simp only [jumpStepH, Bool.cond_eq_ite] at h
  split at h
  · cases h; exact ⟨by simpa using hz, by simp⟩
  split at h
  · obtain ⟨t, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨by simp, by simpa using hz⟩
  · exact headStepH_ok P i oc od of tabs hzs h

/-! ## The pass's states -/

theorem visitH_ok {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} (P : PairCtx)
    (ins : OffsetInstruction) (i i' : ℕ) (h1 : List Prover.Exec.Hint) (hs' : List (ℕ × List Prover.Exec.Hint))
    (rest : List (ℕ × Zip)) (tabs : List (ℕ × Zip × ℕ)) {c : Zip} {r : St × Option (ℕ × Zip)}
    (hhs : ∃ n, hs' = hs0.drop n) (hrest : ∀ p ∈ rest, ZOk body p.2) (htabs : ∀ t ∈ tabs, ZOk body t.2.1)
    (hc : ZOk body c) (h : visitH P ins i i' h1 hs' rest tabs c = some r) : StOk body hs0 r.1 ∧ r.1.i = i' := by
  simp only [visitH] at h
  obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨z1, hz1, hz⟩ := Option.bind_eq_some_iff.mp hz
  have hzok := hintsStepH_ok P h1 (P.nL_ok hc hz1) hz
  cases ins
  case jump oc od of h =>
    dsimp only at h
    simp only [Bool.cond_eq_ite] at h
    split at h
    · obtain ⟨zs, hzs, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
      have hzsok := P.nS_ok hzok hzs
      have hout := jumpStepH_ok P i oc od of tabs hzok hzsok hq
      refine ⟨⟨hhs, hout.1, fun p hp ↦ ?_, tabReg_ok P.X i _ hzsok _ htabs⟩, rfl⟩
      rcases mergeP_mem _ _ hp with hp | hp
      · exact hout.2 p hp
      · exact hrest p hp
    · cases h
  all_goals
    rename_i h
    dsimp only at h
    obtain ⟨z', hz', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨⟨hhs, by simpa using plainStep_ok P i _ hzok hz', hrest, htabs⟩, rfl⟩

/-- **A step keeps a state of the pass**, its offset the next. -/
theorem stepIH_ok {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} (P : PairCtx)
    (ins : OffsetInstruction) {st : St} {r : St × Option (ℕ × Zip)} (hst : StOk body hs0 st)
    (h : stepIH P ins st = some r) : StOk body hs0 r.1 ∧ r.1.i = st.i + 1 := by
  unfold stepIH at h
  rw [natSeq_eq] at h
  obtain ⟨n, hn⟩ := hst.hs
  have hsuf := hintsAt_suffix (Nat.add P.X.entry st.i) hs0 hn
  have hsp : ∀ p, _ := fun p ↦ spanP_mem st.i st.pend (p := p)
  generalize hS : spanP st.i st.pend = S at h hsp
  generalize hH : hintsAt (Nat.add P.X.entry st.i) st.hs = H at h hsuf
  obtain ⟨here, rest⟩ := S
  obtain ⟨h1, hs'⟩ := H
  have hrest : ∀ p ∈ rest, ZOk body p.2 := fun p hp ↦ hst.pend p ((hsp p).2 hp)
  simp only [Bool.cond_eq_ite] at h
  split at h
  · split at h
    · exact visitH_ok P ins _ _ h1 hs' rest _ hsuf hrest hst.tabs (hst.cur _ (by simp_all)) h
    · cases h
  · cases h
    exact ⟨⟨hsuf, by simp, hrest, hst.tabs⟩, rfl⟩
  · split at h
    · exact visitH_ok P ins _ _ h1 hs' rest _ hsuf hrest hst.tabs
        (hst.pend _ ((hsp _).1 (by simp_all))) h
    · cases h

theorem pairGo_cons (P : PairCtx) (ins : OffsetInstruction) (code : List OffsetInstruction) (st : St)
    (acc : List (ℕ × Zip)) :
    pairGo P (ins :: code) st acc = (stepIH P ins st).bind fun p ↦ pairGo P code p.1 (p.2.toList ++ acc) := rfl

theorem pairGo_append (P : PairCtx) : ∀ (c1 c2 : List OffsetInstruction) (st : St) (acc : List (ℕ × Zip)),
    pairGo P (c1 ++ c2) st acc = (pairGo P c1 st acc).bind fun p ↦ pairGo P c2 p.1 p.2
  | [], _, _, _ => rfl
  | ins :: c1, c2, st, acc => by
    rw [List.cons_append, pairGo_cons, pairGo_cons, Option.bind_assoc]
    congr 1
    funext p
    exact pairGo_append P c1 c2 _ _

/-- **What the pass records is apart from the rest.** -/
theorem pairGo_acc (P : PairCtx) : ∀ (c : List OffsetInstruction) (st : St) (acc : List (ℕ × Zip)),
    pairGo P c st acc = (pairGo P c st []).map fun p ↦ (p.1, p.2 ++ acc)
  | [], _, _ => by simp [pairGo]
  | ins :: c, st, acc => by
    rw [pairGo_cons, pairGo_cons, Option.map_bind]
    congr 1
    funext p
    simp only [Function.comp_apply]
    rw [pairGo_acc P c _ (p.2.toList ++ acc), pairGo_acc P c _ (p.2.toList ++ []), Option.map_map]
    congr 1
    funext q
    simp

theorem pairGo_ok {body : List Stmt} {hs0 : List (ℕ × List Prover.Exec.Hint)} (P : PairCtx) :
    ∀ (c : List OffsetInstruction) {st st' : St} {acc acc' : List (ℕ × Zip)}, StOk body hs0 st →
      pairGo P c st acc = some (st', acc') → StOk body hs0 st' ∧ st'.i = st.i + c.length
  | [], _, _, _, _, hst, h => by
    simp only [pairGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hst, rfl⟩
  | ins :: c, st, st', acc, acc', hst, h => by
    rw [pairGo_cons] at h
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hp1, hpi⟩ := stepIH_ok P ins hst hp
    obtain ⟨h1, h2⟩ := pairGo_ok P c hp1 h
    exact ⟨h1, by rw [h2, hpi, List.length_cons]; omega⟩

/-! ## Windows -/

theorem PairCtx.seq_eq {β : Type} (P : PairCtx) (k : PairCtx → β) : P.seq k = k P := by
  obtain ⟨X, R, O, S⟩ := P
  simp only [PairCtx.seq, AlignCtx.seq_eq, Exec.Trie.seq_eq]

/-- **A chain of named states**: each window of the pass from one to the next, the last at the end. -/
@[expose] def ChainH (X : AlignCtx) (H : HCert) (O S : Exec.Trie Unit) (body : List Stmt)
    (code : List OffsetInstruction) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : KSt → List KSt → Prop
  | K, [] => chainEnd code K = true
  | K, K' :: ks => winOkH X H O S body code d K K' = true ∧ ChainH X H O S body code d K' ks

end

end LeanVM.Guest.CoreMode
