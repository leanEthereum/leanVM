/-
  LeanVM.Guest.B2C.Chain

  The chained `match`es' table targets apart: a static check, window by window, and its soundness
  (`ChainApart`).
-/

module

public import LeanVM.Guest.B2C.Frame
public import LeanVM.Guest.B2C.CplComp
public import LeanVM.Guest.B2C.Table
public import LeanVM.Guest.B2C.ChainDefs

/-!
# The chained `match`es' targets apart

A chained `match` (`Plumb.chains`, entries `(p, x, ts, y, b)`: top-level statement `p` is the
`match` on `V.n x`, arm `k` ends in the table jump through cell `ts[k]` into the arms of the
`match` on `V.n y` at statement `p + 1`, read from the table at `b`) has its targets in cells
other arms use for values. `ChainApart j` says no value a path names is at the target of the
arm the path takes. It follows from a static check:

* `chainFn j`: the chains in increasing statement order with pairwise disjoint targets, each
  target apart from the fixed, temporaries', runs', call sites' and `match` targets' cells,
  statement `p` the `match` on `V.n x` with one arm per target, statement `p + 1` the `match`
  on `V.n y`, each of whose slots `b + e` the jump table holds;
* `chainWin j i`, window by window of the soundness certificate: every value a top-level
  statement uses is in no chain's targets, but that the values arm `k` of a chained `match`
  uses may lie at its own chain's other targets, not at `ts[k]`; the parameters in none.

A path through statement `p` that takes arm `k` names the values the other statements and arm `k`
use (`named_chain`), so none is at `ts[k]` (`chainApart_of`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check LeanVM.Guest.Exec

@[expose] public section

/-! ## The static facts -/

theorem testBit_bitsOf' {l : List ℕ} {c : ℕ} (h : (bitsOf l).testBit c = true) : c ∈ l :=
  (testBit_bitsOf l c).mp h

/-- Two chains in increasing order, the later one's targets not the earlier one's. -/
def ChR (a b : Chain) : Prop := a.1 < b.1 ∧ ∀ t ∈ b.2.2.1, t ∉ a.2.2.1

theorem chainsPw_spec : ∀ {l : List Chain}, chainsPw l = true → l.Pairwise ChR
  | [], _ => List.Pairwise.nil
  | ch :: rest, h => by
    simp only [chainsPw, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
    refine List.Pairwise.cons (fun ch' hc ↦ ⟨(h.1 ch' hc).1, fun t ht hm ↦ ?_⟩) (chainsPw_spec h.2)
    have := (h.1 ch' hc).2 t ht
    rw [mem_bitsOf hm] at this
    cases this

theorem pw_mem {R : Chain → Chain → Prop} : ∀ {l : List Chain}, l.Pairwise R → ∀ {x y : Chain},
    x ∈ l → y ∈ l → x = y ∨ R x y ∨ R y x
  | [], _, _, _, hx, _ => absurd hx List.not_mem_nil
  | a :: l, h, x, y, hx, hy => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hx with ex | ex <;> rcases List.mem_cons.mp hy with ey | ey
    · exact Or.inl (ex.trans ey.symm)
    · rw [ex]; exact Or.inr (Or.inl (h1 _ ey))
    · rw [ey]; exact Or.inr (Or.inr (h1 _ ex))
    · exact pw_mem h2 ex ey

/-- Chains at one statement are one; chains at two have no target in common. -/
theorem chain_apart {l : List Chain} (h : l.Pairwise ChR) {x y : Chain} (hx : x ∈ l) (hy : y ∈ l) :
    (x.1 = y.1 → x = y) ∧ (x.1 ≠ y.1 → ∀ t ∈ x.2.2.1, t ∉ y.2.2.1) := by
  rcases pw_mem h hx hy with rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ ↦ rfl, fun hne ↦ absurd rfl hne⟩
  · exact ⟨fun he ↦ absurd he (by omega), fun _ t ht hm ↦ h2 t hm ht⟩
  · exact ⟨fun he ↦ absurd he (by omega), fun _ t ht hm ↦ h2 t ht hm⟩

/-! ## A window's check -/

section Win

variable {j : ℕ} {loc : CLoc}

/-- What the check of top-level statement `s` gives. -/
def SGood (j s : ℕ) (st : Stmt) : Prop :=
  ∀ ch ∈ (plumbOf j).chains, (ch.1 ≠ s → ∀ v ∈ Stmt.uses st, cellJ j v ∉ ch.2.2.1) ∧
    (ch.1 = s → ∃ arms : List (List Stmt), st = .match_ (V.n ch.2.1) arms ∧ ∀ (k : ℕ) a t, arms[k]? = some a →
      ch.2.2.1[k]? = some t → ∀ v ∈ Stmt.usesList a, cellJ j v ≠ t)

theorem avoidL_spec (hl : LocOk j loc) {F : ℕ} {vs : List V} (h : avoidL loc F vs = true) :
    ∀ v ∈ vs, F.testBit (cellJ j v) = false := by
  intro v hv
  have := List.all_eq_true.mp h v hv
  split at this
  · rename_i c hc
    rw [hl v c hc]; simpa using this
  · cases this

theorem avoidA_spec (hl : LocOk j loc) {F own t : ℕ} {vs : List V} (h : avoidA loc F own t vs = true) :
    ∀ v ∈ vs, F.testBit (cellJ j v) = false ∨ (own.testBit (cellJ j v) = true ∧ cellJ j v ≠ t) := by
  intro v hv
  have := List.all_eq_true.mp h v hv
  split at this
  · rename_i c hc
    rw [hl v c hc]
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · cases this

theorem chainArms_spec (hl : LocOk j loc) {F own : ℕ} : ∀ {arms : List (List Stmt)} {ts : List ℕ},
    chainArms loc F own arms ts = true → arms.length = ts.length ∧ ∀ (k : ℕ) a t, arms[k]? = some a →
      ts[k]? = some t → ∀ v ∈ Stmt.usesList a,
        F.testBit (cellJ j v) = false ∨ (own.testBit (cellJ j v) = true ∧ cellJ j v ≠ t)
  | [], [], _ => ⟨rfl, fun _ _ _ h ↦ by simp at h⟩
  | [], _ :: _, h => by simp [chainArms] at h
  | _ :: _, [], h => by simp [chainArms] at h
  | a :: as, t :: ts, h => by
    simp only [chainArms, Bool.and_eq_true] at h
    obtain ⟨hl', hk⟩ := chainArms_spec hl h.2
    refine ⟨by simp [hl'], fun k a' t' ha ht ↦ ?_⟩
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha ht
      subst ha; subst ht
      exact avoidA_spec hl h.1
    | succ k => exact hk k a' t' (by simpa using ha) (by simpa using ht)

theorem chain_mem_usesArms {v : V} : ∀ {arms : List (List Stmt)}, v ∈ Stmt.usesArms arms →
    ∃ (k : ℕ) (a : List Stmt), arms[k]? = some a ∧ v ∈ Stmt.usesList a
  | [], hv => by simp [Stmt.usesArms] at hv
  | a :: as, hv => by
    simp only [Stmt.usesArms, List.mem_append] at hv
    rcases hv with hv | hv
    · exact ⟨0, a, rfl, hv⟩
    · obtain ⟨k, a', h1, h2⟩ := chain_mem_usesArms hv
      exact ⟨k + 1, a', by simpa using h1, h2⟩

/-- **A top-level statement's check.** -/
theorem chainStmt_spec (hl : LocOk j loc) (hpw : (plumbOf j).chains.Pairwise ChR) {s : ℕ} {st : Stmt}
    (h : chainStmt (plumbOf j).chains loc (bitsOf ((plumbOf j).chains.flatMap (·.2.2.1))) s st = true) :
    SGood j s st := by
  have hF : ∀ ch ∈ (plumbOf j).chains, ∀ c, (bitsOf ((plumbOf j).chains.flatMap (·.2.2.1))).testBit c =
      false → c ∉ ch.2.2.1 := fun ch hch c hc hm ↦ by
    rw [mem_bitsOf (List.mem_flatMap.mpr ⟨ch, hch, hm⟩)] at hc; cases hc
  unfold SGood
  unfold chainStmt at h
  split at h
  · rename_i hn
    intro ch hch
    have hne : ch.1 ≠ s := fun he ↦ by
      have := List.find?_eq_none.mp hn ch hch
      simp [he] at this
    exact ⟨fun _ v hv ↦ hF ch hch _ (avoidL_spec hl h v hv), fun he ↦ absurd he hne⟩
  · rename_i ch0 hf
    have hch0 := List.mem_of_find?_eq_some hf
    have hs0 : ch0.1 = s := by simpa [Nat.beq_eq] using List.find?_some hf
    split at h
    · rename_i x arms
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hx, hxa⟩, harms⟩ := h
      obtain ⟨-, hk⟩ := chainArms_spec hl harms
      intro ch hch
      have AP := chain_apart hpw hch hch0
      refine ⟨fun hne v hv ↦ ?_, fun he ↦ ?_⟩
      · -- another chain's targets: the selector apart from all, an arm's values from all but its own
        simp only [Stmt.uses, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hF ch hch _ (avoidL_spec hl hxa _ List.mem_cons_self)
        · obtain ⟨k, a, hka, hva⟩ := chain_mem_usesArms hv
          have hlen := (chainArms_spec hl harms).1
          have hkt : k < ch0.2.2.1.length := by
            rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hka).1
          rcases hk k a _ hka (List.getElem?_eq_getElem hkt) v hva with hb | ⟨hb, -⟩
          · exact hF ch hch _ hb
          · exact fun hm ↦ AP.2 (by rw [hs0]; exact hne) _ hm (testBit_bitsOf' hb)
      · obtain rfl := AP.1 (by rw [he, hs0])
        refine ⟨arms, by rw [hx], fun k a t ha ht v hv ↦ ?_⟩
        rcases hk k a t ha ht v hv with hb | ⟨-, hb⟩
        · exact fun he' ↦ hF ch hch _ hb (he' ▸ List.mem_of_getElem? ht)
        · exact hb
    · cases h

theorem chainStmts_spec (hl : LocOk j loc) (hpw : (plumbOf j).chains.Pairwise ChR) :
    ∀ {s : ℕ} {ss : List Stmt},
      chainStmts (plumbOf j).chains loc (bitsOf ((plumbOf j).chains.flatMap (·.2.2.1))) s ss = true →
      ∀ q st, ss[q]? = some st → SGood j (s + q) st
  | _, [], _, _, _, h => by simp at h
  | s, st :: ss, h, q, st', hq => by
    simp only [chainStmts, Bool.and_eq_true] at h
    cases q with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
      subst hq
      exact chainStmt_spec hl hpw h.1
    | succ q =>
      have := chainStmts_spec hl hpw h.2 q st' (by simpa using hq)
      rwa [Nat.add_assoc, Nat.add_comm 1 q] at this

end Win

/-! ## The windows cover the body -/

/-- **The windows' statements are the body's**: a property of each window's statements at their
places in the body holds of every statement of the body. -/
theorem cover_windows {C : Cert} {cf : Core.Fn} (P : ℕ → Stmt → Prop)
    (h : ∀ i ≤ C.cuts.length, ∀ q st, (C.stmtsAt cf i)[q]? = some st → P ((C.cutAt i).start + q) st) :
    ∀ s st, cf.body[s]? = some st → P s st := by
  have key : ∀ k i, i + k = C.cuts.length → ∀ s st, (C.cutAt i).start ≤ s → cf.body[s]? = some st →
      P s st := by
    intro k
    induction k with
    | zero =>
      intro i hi s st hs hb
      have hbf : Nat.blt i C.cuts.length = false := by
        cases h' : Nat.blt i C.cuts.length
        · rfl
        · simp only [Nat.blt_eq] at h'; omega
      have hq : (C.stmtsAt cf i)[s - (C.cutAt i).start]? = some st := by
        simp only [Cert.stmtsAt, hbf, Bool.cond_false, List.getElem?_drop]
        rwa [Nat.add_sub_cancel' hs]
      have := h i (by omega) _ st hq
      rwa [Nat.add_sub_cancel' hs] at this
    | succ k ih =>
      intro i hi s st hs hb
      have hlt : i < C.cuts.length := by omega
      by_cases hsb : s < (C.cutAt (i + 1)).start
      · have hq : (C.stmtsAt cf i)[s - (C.cutAt i).start]? = some st := by
          have hbt : Nat.blt i C.cuts.length = true := by simp only [Nat.blt_eq]; exact hlt
          simp only [Cert.stmtsAt, hbt, Bool.cond_true]
          rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_cancel' hs]
          exact hb
        have := h i hlt.le _ st hq
        rwa [Nat.add_sub_cancel' hs] at this
      · exact ih (i + 1) (by omega) s st (by omega) hb
  exact fun s st hb ↦ key C.cuts.length 0 (by omega) s st (Nat.zero_le _) hb

/-! ## A path through a chained `match` -/

section Path

variable {σ : Val}

theorem walkArms_at {x : V} : ∀ (arms : List (List Stmt)) (j k : ℕ) (hk : k < arms.length),
    σ x = ofK (addressOfIndex (j + k)) → j + k < 2 ^ 64 - 1 → walkArms σ x j arms = walk σ arms[k]
  | [], _, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | a :: as, j, 0, _, hx, _ => by
    unfold walkArms
    split_ifs with h
    · rfl
    · exact absurd (by simpa using hx) h
  | a :: as, j, k + 1, hk, hx, hlt => by
    unfold walkArms
    split_ifs with h
    · have := gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
        (ofK_injective (h.symm.trans hx))
      omega
    · rw [walkArms_at as (j + 1) k (by simpa using hk) (by rw [hx]; congr 2; omega) (by omega)]
      rfl

theorem walkArms_sel {x : V} : ∀ (arms : List (List Stmt)) (j : ℕ), walkArms σ x j arms ≠ .stuck →
    ∃ e < arms.length, σ x = ofK (addressOfIndex (j + e))
  | [], _, h => absurd rfl h
  | a :: as, j, h => by
    unfold walkArms at h
    split_ifs at h with hx
    · exact ⟨0, by simp, by simpa using hx⟩
    · obtain ⟨e, he, hx'⟩ := walkArms_sel as (j + 1) h
      exact ⟨e + 1, by simpa using he, by rw [hx']; congr 2; omega⟩

theorem mem_usesList {v : V} : ∀ {l : List Stmt}, v ∈ Stmt.usesList l →
    ∃ (s : ℕ) (st : Stmt), l[s]? = some st ∧ v ∈ Stmt.uses st
  | [], hv => by simp [Stmt.usesList] at hv
  | a :: l, hv => by
    simp only [Stmt.usesList, List.mem_append] at hv
    rcases hv with hv | hv
    · exact ⟨0, a, rfl, hv⟩
    · obtain ⟨s, st, h1, h2⟩ := mem_usesList hv
      exact ⟨s + 1, st, by simpa using h1, h2⟩

/-- **The values a path through a chained `match`'s arm `k` names**: the parameters, the other
statements' and arm `k`'s. -/
theorem named_chain {body : List Stmt} {es : List Ev} {vs : List V} {p k : ℕ} {x : V}
    {arms : List (List Stmt)} {pv : List V} (hw : walk σ body = .ret es vs)
    (hp : body[p]? = some (.match_ x arms)) (hk : k < arms.length)
    (hx : σ x = ofK (addressOfIndex k)) (hk64 : k < 2 ^ 64 - 1) :
    ∀ v ∈ namedOf pv es vs, v ∈ pv ∨ (∃ s st, s ≠ p ∧ body[s]? = some st ∧ v ∈ Stmt.uses st) ∨
      v ∈ Stmt.usesList arms[k] := by
  have hplt : p < body.length := (List.getElem?_eq_some_iff.mp hp).1
  have hsplit : body = body.take p ++ (Stmt.match_ x arms :: body.drop (p + 1)) := by
    conv_lhs => rw [← List.take_append_drop p body]
    rw [List.drop_eq_getElem_cons hplt, (List.getElem?_eq_some_iff.mp hp).2]
  have hw' : walk σ (body.take p ++ (arms[k] ++ body.drop (p + 1))) = .ret es vs := by
    rw [hsplit, walk_appendC, walk] at hw
    rw [walk_appendC, walk_appendC]
    rwa [walk1, walkArms_at arms 0 k hk (by simpa using hx) (by omega)] at hw
  have hwi := walk_within (σ := σ) (body.take p ++ (arms[k] ++ body.drop (p + 1)))
  rw [hw'] at hwi
  obtain ⟨h1, -, h3⟩ := hwi
  have hin : ∀ v, v ∈ Stmt.usesList (body.take p ++ (arms[k] ++ body.drop (p + 1))) →
      (∃ s st, s ≠ p ∧ body[s]? = some st ∧ v ∈ Stmt.uses st) ∨ v ∈ Stmt.usesList arms[k] := by
    intro v hv
    simp only [usesList_append, List.mem_append] at hv
    rcases hv with hv | hv | hv
    · obtain ⟨s, st, h1, h2⟩ := mem_usesList hv
      have hs : s < p := by
        have := (List.getElem?_eq_some_iff.mp h1).1
        simp only [List.length_take] at this; omega
      refine Or.inl ⟨s, st, by omega, ?_, h2⟩
      rw [List.getElem?_take_of_lt hs] at h1; exact h1
    · exact Or.inr hv
    · obtain ⟨s, st, h1, h2⟩ := mem_usesList hv
      rw [List.getElem?_drop] at h1
      exact Or.inl ⟨p + 1 + s, st, by omega, h1, h2⟩
  intro v hv
  simp only [namedOf, List.mem_append, List.mem_flatMap] at hv
  rcases hv with (hv | ⟨e, he, hv⟩) | hv
  · exact Or.inl hv
  · exact Or.inr (hin v (h1 e he v hv))
  · exact Or.inr (hin v (h3 v hv))

theorem lastOkC_cons' {s : Stmt} {l : List Stmt} (hl : lastOkC (s :: l) = true) (hs : ∀ vs, s ≠ .ret vs) :
    Stmt.noRet s = true ∧ lastOkC l = true := by
  cases l with
  | nil => cases s <;> simp_all [lastOkC]
  | cons s' l' => cases s <;> simp_all [lastOkC]

theorem lastOkC_take : ∀ {l : List Stmt} {n : ℕ} {st : Stmt}, lastOkC l = true → l[n]? = some st →
    (∀ vs, st ≠ .ret vs) → Stmt.noRetList (l.take (n + 1)) = true
  | [], _, _, _, h, _ => by simp at h
  | s :: l, 0, st, hl, h, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [Stmt.noRetList, (lastOkC_cons' hl hs).1]
  | s :: l, n + 1, st, hl, h, hs => by
    have hs' : ∀ vs, s ≠ .ret vs := by
      rintro vs rfl
      cases l with
      | nil => simp at h
      | cons s' l' => simp [lastOkC, Stmt.noRet] at hl
    have hl' := lastOkC_cons' hl hs'
    simp only [List.take_succ_cons, Stmt.noRetList, hl'.1, Bool.true_and]
    exact lastOkC_take hl'.2 (by simpa using h) hs

end Path

/-! ## Soundness -/

/-- **The chains' checks give `ChainApart`.** -/
theorem chainApart_of {j : ℕ} (hok : CplOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin glob (fnOf j) (coreOf j) (certOf j) (j == 1) i = true)
    (hc : ChainOk j) : ChainApart j := by
  obtain ⟨hfn, hwin⟩ := hc
  by_cases hnil : (plumbOf j).chains = []
  · exact ⟨fun ch hch ↦ by simp [hnil] at hch, fun ch hch ↦ by simp [hnil] at hch,
      fun _ _ _ _ ch hch ↦ by simp [hnil] at hch, fun _ _ _ _ ch hch ↦ by simp [hnil] at hch,
      fun _ ↦ hnil⟩
  have hne : (plumbOf j).chains.isEmpty = false := by simpa using hnil
  simp only [chainFn, Bool.and_eq_true, List.all_eq_true] at hfn
  obtain ⟨hpw', hall⟩ := hfn
  have hpw := chainsPw_spec hpw'
  have hcont := cont_of hchk
  -- each window's check, at the certificate's cells
  have hW : ∀ i ≤ (certOf j).cuts.length,
      (i = 0 → ∀ v ∈ (coreOf j).params, (bitsOf ((plumbOf j).chains.flatMap (·.2.2.1))).testBit
        (cellJ j v) = false) ∧
      ∀ q st, ((certOf j).stmtsAt (coreOf j) i)[q]? = some st →
        SGood j (((certOf j).cutAt i).start + q) st := by
    intro i hi
    have h := hwin i hi
    simp only [chainWin, hne, Bool.false_or, Bool.and_eq_true, natSeq_eq, CLoc.seq_eq] at h
    obtain ⟨hb, hpar, hst⟩ := h
    have hl : LocOk j (clocW (certOf j) i) := fun v c h ↦
      clocW_get hcont hi (checkWin_cpl (hchk i hi)).2.1 rfl hb h
    refine ⟨fun h0 ↦ ?_, chainStmts_spec hl hpw hst⟩
    subst h0
    simp only [show Nat.beq 0 0 = true from rfl, Bool.cond_true] at hpar
    exact avoidL_spec hl hpar
  have hS : ∀ s st, (coreOf j).body[s]? = some st → SGood j s st :=
    cover_windows (C := certOf j) (cf := coreOf j) (SGood j) (fun i hi ↦ (hW i hi).2)
  have hFt : ∀ ch ∈ (plumbOf j).chains, ∀ t ∈ ch.2.2.1,
      (bitsOf ((plumbOf j).chains.flatMap (·.2.2.1))).testBit t = true :=
    fun ch hch t ht ↦ mem_bitsOf (List.mem_flatMap.mpr ⟨ch, hch, ht⟩)
  -- each chain's statements
  have hM : ∀ ch ∈ (plumbOf j).chains, ∃ arms arms', (coreOf j).body[ch.1]? = some (.match_ (V.n ch.2.1) arms) ∧
      (coreOf j).body[ch.1 + 1]? = some (.match_ (V.n ch.2.2.2.1) arms') ∧
      arms.length = ch.2.2.1.length ∧ ch.2.2.1.length ≤ 65536 ∧
      (∀ e < arms'.length, ∃ pc, glob.jt.get (ch.2.2.2.2 + e) = some pc) ∧
      ∀ t ∈ ch.2.2.1, (fixedBits j).testBit t = false := by
    intro ch hch
    obtain ⟨⟨hfx, hle⟩, h⟩ := hall ch hch
    split at h
    · rename_i x arms y arms' h1 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq, List.all_eq_true, List.mem_range,
        Option.isSome_iff_exists] at h
      obtain ⟨⟨⟨hx, hy⟩, hl⟩, hjt⟩ := h
      exact ⟨arms, arms', by rw [h1, hx], by rw [h2, hy], hl, by simpa using hle, hjt,
        fun t ht ↦ by simpa using hfx t ht⟩
    · cases h
  refine ⟨fun ch hch t ht ↦ ?_, fun ch hch ch' hch' t ht ht' ↦ ?_, fun σ es vs hw ch hch k t hkt hk v hv ↦ ?_,
    fun σ es vs hw ch hch k t hkt hk ↦ ?_, fun hj ↦ ?_⟩
  · -- the targets apart from the fixed cells
    obtain ⟨-, -, -, -, -, -, -, hfx⟩ := hM ch hch
    have hb := hfx t ht
    unfold fixedBits at hb
    have hn : t ∈ (plumbOf j).stat.map Prod.fst ++ (plumbOf j).tmps.map Prod.snd ++
        (plumbOf j).runs.map Prod.snd ++ siteCells (plumbOf j) ++ (plumbOf j).arms.map (·.2.1) → False :=
      fun hm ↦ by rw [mem_bitsOf hm] at hb; cases hb
    exact ⟨fun q hq he ↦ hn (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_map.mpr ⟨q, hq, he⟩))))),
      fun p hp he ↦ hn (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, he⟩))))),
      fun p hp he ↦ hn (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨p, hp, he⟩)))),
      fun hm ↦ hn (List.mem_append_left _ (List.mem_append_right _ hm)),
      fun a ha he ↦ hn (List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, he⟩))⟩
  · -- chains with a common target are one
    by_cases he : ch.1 = ch'.1
    · rw [(chain_apart hpw hch hch').1 he]
    · exact absurd ht' ((chain_apart hpw hch hch').2 he t ht)
  · -- on the path through arm `k`, no value at `ts[k]`
    obtain ⟨arms, -, hp, -, hlen, hl64, -, -⟩ := hM ch hch
    have hkl : k < ch.2.2.1.length := (List.getElem?_eq_some_iff.mp hkt).1
    have hka : k < arms.length := by omega
    rcases named_chain hw hp hka hk (by omega) v hv with hv | ⟨s, st, hs, hb, hv⟩ | hv
    · -- a parameter
      intro he
      have := (hW 0 (Nat.zero_le _)).1 rfl v hv
      rw [he, hFt ch hch t (List.mem_of_getElem? hkt)] at this
      cases this
    · exact fun he ↦ ((hS s st hb ch hch).1 (fun h ↦ hs h.symm) v hv) (he ▸ List.mem_of_getElem? hkt)
    · obtain ⟨arms0, hst, harm⟩ := (hS ch.1 _ hp ch hch).2 rfl
      simp only [Stmt.match_.injEq, true_and] at hst
      subst hst
      exact harm k arms[k] t (List.getElem?_eq_getElem hka) hkt v hv
  · -- the next selector picks a slot of the next table
    obtain ⟨arms, arms', hp, hp1, -, -, hjt, -⟩ := hM ch hch
    have hnr := lastOkC_take (lastBody hok hchk) hp (fun vs h ↦ by cases h)
    have hp1lt : ch.1 + 1 < (coreOf j).body.length := (List.getElem?_eq_some_iff.mp hp1).1
    have hsplit : (coreOf j).body = (coreOf j).body.take (ch.1 + 1) ++
        (Stmt.match_ (V.n ch.2.2.2.1) arms' :: (coreOf j).body.drop (ch.1 + 2)) := by
      conv_lhs => rw [← List.take_append_drop (ch.1 + 1) (coreOf j).body]
      rw [List.drop_eq_getElem_cons hp1lt, (List.getElem?_eq_some_iff.mp hp1).2]
    rw [hsplit, walk_appendC, walk] at hw
    rcases walk_noRetC _ hnr with ⟨es1, h1⟩ | h1 <;> rw [h1] at hw
    · have hns : walkArms σ (V.n ch.2.2.2.1) 0 arms' ≠ .stuck := fun h ↦ by
        rw [walk1, h] at hw; simp [Out.seq, Out.pre] at hw
      obtain ⟨e, he, hy⟩ := walkArms_sel arms' 0 hns
      obtain ⟨pc, hpc⟩ := hjt e he
      exact ⟨e, pc, by simpa using hy, hpc⟩
    · simp [Out.seq] at hw
  · subst hj
    have := mainSmall
    simp only [mainSmallB, Bool.and_eq_true, List.isEmpty_iff] at this
    exact this.2

end
end LeanVM.Guest.B2C
