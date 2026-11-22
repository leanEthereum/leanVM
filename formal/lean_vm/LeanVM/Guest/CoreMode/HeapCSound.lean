/-
  LeanVM.Guest.CoreMode.HeapCSound

  The heap check with calls and loops is sound on the path: every event's needs are written
  before it, and the guarantees at return are written.
-/

module

public import LeanVM.Guest.CoreMode.HeapCStmt
public import LeanVM.Guest.CoreMode.Fam.LoopTree

/-!
# The heap check with calls and loops is sound

`heapOkC_sound`: for a function passing `heapOkC`, a valuation `σ` whose path returns, its events
holding and each entered call's callee guarantees' runs having their exponents, given its entry
facts (`EntryF`: its preconditions' runs' exponents, its termination facts) and its residuals
(`ResF`): every event's needs are written before it (`ReadsOkC`) and its guarantees at return are
written (`PostOkC`).

The proof follows `heapOk_sound`'s (`HeapSound.lean`): the pass's state is valid on the path
(`StOk rd W`: the environment's monomials are the values' words, the scope's cells and runs written in
`W`, the runs' exponents existing), `W` the preconditions and the writes so far; a witness of a cell
or a run gives it written (`ptOk_ok`, `rnOk_ok`, by `ptRun_ok` and `runRun_ok` from the run's
exponents and the facts); a signature at a site is the cells and runs at the slots' words
(`instC_ok`, `MsOk`). A loop's tail (`tailC_ok`) splits on its condition: entered, the next
iteration's guarantees at its words (`EvW`, the same cells when not over the counter, the run from
one further); not entered, the next counter is the end (`Res.loop_path`).

Its parts, in order: words, exponents, runs and monomials at a site (`HeapCRun.lean`), the pass's invariant
(`HeapCInv.lean`), covered events and each statement's pass (`HeapCStmt.lean`); here blocks and joins, a loop's
tail and the function.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq natSeq_eq)
open LeanVM.Guest.Check (getF setF getF_eq setF_eq)

public section

/-! ## Blocks -/

section Pass

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} {σ : Val} {rd : Reader}

theorem pick_cases (x : V) (args rets : List V) : ∀ (fs : List String) (j : ℕ),
    pick σ x args rets j fs = .stuck ∨ ∃ g ∈ fs, pick σ x args rets j fs = .fall [.call g args rets]
  | [], _ => Or.inl rfl
  | g :: fs, j => by
    unfold pick
    split_ifs
    · exact Or.inr ⟨g, List.mem_cons_self, rfl⟩
    · rcases pick_cases x args rets fs (j + 1) with h | ⟨g', hg', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', h⟩

theorem pick_idx (x : V) (args rets : List V) : ∀ (fs : List String) (j : ℕ),
    pick σ x args rets j fs = .stuck ∨ ∃ i, ∃ hi : i < fs.length, σ x = ofK (addressOfIndex (j + i)) ∧
      pick σ x args rets j fs = .fall [.call fs[i] args rets]
  | [], _ => Or.inl rfl
  | g :: fs, j => by
    unfold pick
    split_ifs with hx
    · exact Or.inr ⟨0, by simp, by simpa using hx, rfl⟩
    · rcases pick_idx x args rets fs (j + 1) with h | ⟨i, hi, hx', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i + 1, by simpa using hi, by rw [show j + (i + 1) = j + 1 + i by omega]; exact hx',
          by simpa using h⟩

/-! ### Joins -/

/-- A block returning at its top level never falls through. -/
theorem endsRet_walk : ∀ (ss : List Stmt), endsRet ss = true → ∀ es, walk σ ss ≠ .fall es
  | [], h, _, _ => by simp [endsRet] at h
  | s :: ss, h, es, hw => by
    rw [walk] at hw
    cases s with
    | ret vs => simp [walk1, Out.seq] at hw
    | _ =>
      simp only [endsRet] at h
      cases h1 : walk1 σ _ with
      | fall es1 =>
        rw [h1, Out.seq] at hw
        cases h2 : walk σ ss with
        | fall es2 => exact endsRet_walk ss h es2 h2
        | ret => rw [h2] at hw; simp [Out.pre] at hw
        | stuck => rw [h2] at hw; simp [Out.pre] at hw
      | ret => rw [h1] at hw; simp [Out.seq] at hw
      | stuck => rw [h1] at hw; simp [Out.seq] at hw

theorem endsRet_false {ss : List Stmt} {es : List Ev} (h : walk σ ss = .fall es) : endsRet ss = false := by
  cases he : endsRet ss with
  | false => rfl
  | true => exact absurd h (endsRet_walk ss he es)

theorem rng_mem {α : Type} {t : Trie α} : ∀ {lo n : ℕ} {p : ℕ × α}, p ∈ rng t lo n → getF t p.1 = some p.2
  | _, 0, _, h => by simp [rng] at h
  | lo, n + 1, p, h => by
    simp only [rng] at h
    cases hg : getF t lo with
    | none => rw [hg] at h; exact rng_mem h
    | some a =>
      rw [hg] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hg
      · exact rng_mem h

/-- **A join's entries hold** where those of a block that can fall through do. -/
theorem joinE_ok {α : Type} {beq : α → α → Bool} (hbeq : ∀ a b, beq a b = true → a = b) {Q : α → Prop}
    {ls : List (Bool × List (ℕ × α))} {l : List (ℕ × α)} (hl : (false, l) ∈ ls) (hq : ∀ p ∈ l, Q p.2) :
    ∀ p ∈ joinE beq ls, Q p.2 := by
  intro p hp
  unfold joinE at hp
  have hf : (false, l) ∈ ls.filter fun l ↦ !l.1 := List.mem_filter.mpr ⟨hl, rfl⟩
  generalize ls.filter (fun l ↦ !l.1) = F at hp hf
  cases F with
  | nil => simp at hf
  | cons l0 rest =>
    obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
    rcases List.mem_cons.mp hf with h0 | hr
    · rw [← h0] at hp1
      exact hq p hp1
    · obtain ⟨q, hq', hb⟩ := List.any_eq_true.mp (List.all_eq_true.mp hp2 _ hr)
      rw [← hbeq _ _ hb]
      exact hq q hq'

theorem insL_ok {α : Type} {Q : α → Prop} : ∀ {l : List (ℕ × α)} {t : Trie α}, (∀ k a, getF t k = some a → Q a) →
    (∀ p ∈ l, Q p.2) → ∀ k a, getF (insL l t) k = some a → Q a
  | [], _, ht, _, k, a, h => ht k a h
  | p :: l, t, ht, hl, k, a, h => by
    simp only [insL, Trie.seq_eq] at h
    refine insL_ok (fun k' a' h' ↦ ?_) (fun p' hp' ↦ hl p' (List.mem_cons_of_mem _ hp')) k a h
    rcases Check.getF_setF h' with ⟨-, rfl⟩ | h'
    · exact hl p List.mem_cons_self
    · exact ht k' a' h'

/-- **The state after a join is valid** where the state before is and the end of a block taken that
falls through is. -/
theorem joinSt_ok {W : K → Prop} {st s : CSt} {bs : List (Bool × CSt × CSt)} (hs : StOk rd W σ st)
    {b : Bool × CSt × CSt} (hb : b ∈ bs) (hb1 : b.1 = false) (hbs : StOk rd W σ b.2.2) :
    StOk rd W σ (joinSt bs st s) := by
  have hm : ∀ {α : Type} (g : Bool × CSt × CSt → List (ℕ × α)),
      (false, g b) ∈ bs.map fun b ↦ (b.1, g b) := fun g ↦ List.mem_map.mpr ⟨b, hb, by rw [hb1]⟩
  have h1 : ScOk W σ (insL (joinE CCell.beq (bs.map fun b ↦ (b.1, rng b.2.2.sc b.2.1.n (b.2.2.n - b.2.1.n)))) st.sc) :=
    insL_ok (Q := fun c : CCell ↦ W (c.addr σ)) hs.sc (joinE_ok (Q := fun c : CCell ↦ W (c.addr σ)) (fun _ _ h ↦ CCell.beq_eq h)
      (hm fun b ↦ rng b.2.2.sc b.2.1.n (b.2.2.n - b.2.1.n)) fun p hp ↦ hbs.sc _ _ (rng_mem hp))
  have h2 : RsOk W σ (insL (joinE PRun.beq (bs.map fun b ↦ (b.1, rng b.2.2.rs b.2.1.nr (b.2.2.nr - b.2.1.nr))))
      st.rs) :=
    insL_ok (Q := fun R : PRun ↦ RunF W (vw σ) R.base R.stride R.lo R.hi) hs.rs (joinE_ok (Q := fun R : PRun ↦ RunF W (vw σ) R.base R.stride R.lo R.hi) (fun _ _ h ↦ PRun.beq_eq h)
      (hm fun b ↦ rng b.2.2.rs b.2.1.nr (b.2.2.nr - b.2.1.nr)) fun p hp ↦ hbs.rs _ _ (rng_mem hp))
  have h3 : PfOk rd W σ (insL (joinE pfBeq (bs.map fun b ↦ (b.1, rng b.2.2.pf b.2.1.n (b.2.2.n - b.2.1.n)))) st.pf) :=
    insL_ok (Q := fun p : CCell × List ℕ ↦ ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W x) hs.pf (joinE_ok (Q := fun p : CCell × List ℕ ↦ ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W x) (fun _ _ h ↦ pfBeq_eq h)
      (hm fun b ↦ rng b.2.2.pf b.2.1.n (b.2.2.n - b.2.1.n)) fun p hp ↦ hbs.pf _ _ (rng_mem hp))
  have h4 : PrOk rd W σ (insL (joinE prBeq (bs.map fun b ↦ (b.1, rng b.2.2.pr b.2.1.nr (b.2.2.nr - b.2.1.nr))))
      st.pr) :=
    insL_ok (Q := fun p : PRun × List ℕ ↦ ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W x)
      hs.pr (joinE_ok (Q := fun p : PRun × List ℕ ↦ ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W x) (fun _ _ h ↦ prBeq_eq h) (hm fun b ↦ rng b.2.2.pr b.2.1.nr (b.2.2.nr - b.2.1.nr))
      fun p hp ↦ hbs.pr _ _ (rng_mem hp))
  unfold joinSt
  exact ⟨hs.env, h1, h2, hs.ad, hs.sv, hs.src, h3, h4, hs.cd, hs.eqs, hs.dq⟩

/-- A call, then a block: the call's needs, then the block's pass from the state after it. -/
theorem blockC_call {W : K → Prop} (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ))
    {g : String} {args rets : List V} {ss : List Stmt} {st1 st' : CSt}
    (hreq : CallReq sigOf H rd σ W g args)
    (hpost : EvM sigOf rd σ (.call g args rets) →
      StOk rd (fun x ↦ W x ∨ EvW sigOf rd σ (.call g args rets) x) σ st1)
    (hss : ∀ {W' : K → Prop}, (∀ c ∈ H.sig.pre, W' (c.addr σ)) → StOk rd W' σ st1 →
      BlockC sigOf H σ rd (f.params.map σ) W' (walk σ ss) st') :
    BlockC sigOf H σ rd (f.params.map σ) W ((Out.fall [.call g args rets]).seq (walk σ ss)) st' := by
  refine blockC_seq (W1 := fun _ x ↦ W x ∨ EvW sigOf rd σ (.call g args rets) x)
    ⟨fun es hw _ ↦ ?_, fun es vs hw _ ↦ by simp at hw⟩ fun es hw hh ↦ ?_
  · simp only [Out.fall.injEq] at hw
    subst hw
    exact covC_single hreq
  · simp only [Out.fall.injEq] at hw
    subst hw
    exact ⟨fun x hx ↦ hx.imp_right fun hx ↦ ⟨_, List.mem_singleton_self _, hx⟩,
      hss (fun c hc ↦ Or.inl (hpre c hc)) (hpost (hh _ List.mem_cons_self).2)⟩

mutual
/-- **The pass over a block, on the path.** -/
theorem chkC_ok {X : CX} (hX : XOk sigOf H rd f σ X) : ∀ (ss : List Stmt) {st st' : CSt} {W : K → Prop},
    (∀ c ∈ H.sig.pre, W (c.addr σ)) → chkC X ss st = some st' → StOk rd W σ st →
      BlockC sigOf H σ rd (f.params.map σ) W (walk σ ss) st'
  | [], st, st', W, _, h, hs => by
    simp only [chkC, Option.some.injEq] at h
    subst h
    refine ⟨⟨fun es hw _ ↦ ?_, fun es vs hw _ ↦ by simp [walk] at hw⟩, fun es hw _ ↦ ?_⟩
    · simp only [walk, Out.fall.injEq] at hw
      subst hw
      exact covC_nil W
    · simp only [walk, Out.fall.injEq] at hw
      subst hw
      exact hs.mono fun _ ↦ Or.inl
  | .atom a :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases ha : atomC X st a with
    | none => rw [ha] at h; cases h
    | some st1 =>
      rw [ha] at h
      simp only [CSt.seq_eq] at h
      rw [walk]
      refine blockC_seq (W1 := fun _ x ↦ W x ∨ Writes σ a x)
        ⟨fun es hw hh ↦ ?_, fun es vs hw _ ↦ by simp [walk1] at hw⟩ fun es hw hh ↦ ?_
      · simp only [walk1, Out.fall.injEq] at hw
        subst hw
        exact covC_single (atomC_ok hX hpre ha hs (hh _ List.mem_cons_self)).1
      · simp only [walk1, Out.fall.injEq] at hw
        subst hw
        obtain ⟨-, hs1⟩ := atomC_ok hX hpre ha hs (hh _ List.mem_cons_self).1
        exact ⟨fun x hx ↦ hx.imp_right fun hx ↦ ⟨.atom a, List.mem_singleton_self _, hx⟩,
          chkC_ok hX ss (fun c hc ↦ Or.inl (hpre c hc)) h hs1⟩
  | .ite c z n :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : chkC (X.ext (czero c)) z (zeroEq st c) with
    | none => rw [h1] at h; cases h
    | some s1 =>
      simp only [h1] at h
      cases h2 : chkC (X.ext (cnz c)) n (st.cnt s1) with
      | none => simp [h2] at h
      | some s2 =>
        simp only [h2, CSt.seq_eq] at h
        rw [walk]
        refine blockC_seq (W1 := fun es x ↦ W x ∨ EW sigOf rd σ es x) ?_ fun es hw hh ↦
          ⟨fun x hx ↦ hx, chkC_ok hX ss (fun c hc ↦ Or.inl (hpre c hc)) h ?_⟩
        · simp only [walk1]
          refine outC_pre ?_ c
          by_cases hc : σ c = 0
          · rw [ite_eq_left hc]
            exact (chkC_ok (hX.ext (czero_ok hc)) z hpre h1 (zeroEq_ok hs hc)).1
          · rw [ite_eq_right hc]
            exact (chkC_ok (hX.ext (cnz_ok hc)) n hpre h2 (hs.cnt s1)).1
        · have hW : ∀ es', es = [Ev.inK c] ++ es' → ∀ x, (W x ∨ EW sigOf rd σ es' x) → W x ∨ EW sigOf rd σ es x :=
            fun es' he x hx ↦ by rw [he]; exact hx.imp_right ew_append_right
          simp only [walk1] at hw
          by_cases hc : σ c = 0
          · rw [ite_eq_left hc] at hw
            cases hz : walk σ z with
            | fall es' =>
              rw [hz] at hw
              simp only [Out.pre, Out.fall.injEq] at hw
              subst hw
              exact joinSt_ok (hs.mono fun _ ↦ Or.inl) List.mem_cons_self (endsRet_false hz)
                (((chkC_ok (hX.ext (czero_ok hc)) z hpre h1 (zeroEq_ok hs hc)).2 es' hz (evsOk_append hh).2).mono
                  (hW es' rfl))
            | ret => rw [hz] at hw; simp [Out.pre] at hw
            | stuck => rw [hz] at hw; simp [Out.pre] at hw
          · rw [ite_eq_right hc] at hw
            cases hn : walk σ n with
            | fall es' =>
              rw [hn] at hw
              simp only [Out.pre, Out.fall.injEq] at hw
              subst hw
              exact joinSt_ok (hs.mono fun _ ↦ Or.inl) (List.mem_cons_of_mem _ List.mem_cons_self) (endsRet_false hn)
                (((chkC_ok (hX.ext (cnz_ok hc)) n hpre h2 (hs.cnt s1)).2 es' hn (evsOk_append hh).2).mono
                  (hW es' rfl))
            | ret => rw [hn] at hw; simp [Out.pre] at hw
            | stuck => rw [hn] at hw; simp [Out.pre] at hw
  | .match_ x arms :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : chkArmsC X x 0 arms st with
    | none => rw [h1] at h; cases h
    | some bs =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      rw [walk]
      obtain ⟨ho, hb⟩ := chkArmsC_ok hX x arms hpre h1 hs
      refine blockC_seq (W1 := fun es x ↦ W x ∨ EW sigOf rd σ es x) ho fun es hw hh ↦
        ⟨fun x hx ↦ hx, chkC_ok hX ss (fun c hc ↦ Or.inl (hpre c hc)) h ?_⟩
      obtain ⟨b, hb, hb1, hbs⟩ := hb es hw hh
      exact joinSt_ok (hs.mono fun _ ↦ Or.inl) hb hb1 hbs
  | .call g args rets :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : callC X st g args rets with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      rw [walk]
      obtain ⟨hreq, hpost⟩ := callC_ok hX hpre hs h1
      exact blockC_call hpre hreq hpost fun hp hs' ↦ chkC_ok hX ss hp h hs'
  | .callIf c g args :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : callIfC X st c g args with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      obtain ⟨hreq, hs1⟩ := callIfC_ok hX hpre hs h1
      rw [walk]
      refine blockC_seq (W1 := fun es x ↦ W x ∨ EW sigOf rd σ es x)
        ⟨fun es hw _ ↦ ?_, fun es vs hw _ ↦ by simp [walk1] at hw⟩ fun es hw _ ↦ ?_
      swap
      · simp only [walk1, Out.fall.injEq] at hw
        subst hw
        exact ⟨fun x hx ↦ hx, chkC_ok hX ss (fun c hc ↦ Or.inl (hpre c hc)) h hs1⟩
      simp only [walk1, Out.fall.injEq] at hw
      subst hw
      show CovC sigOf H rd σ W ([Ev.inK c] ++ [_])
      refine covC_append (covC_single trivial) fun _ ↦ covC_single ?_
      by_cases hc : σ c = 0
      · rw [ite_eq_left hc]; trivial
      · rw [ite_eq_right hc]; exact ReqOk.mono (e := .call g args []) (fun _ ↦ Or.inl) (hreq hc)
  | .dispatch x fs args rets :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : dispC X st x fs args rets with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      rw [walk]
      simp only [walk1]
      rcases pick_idx x args rets fs 0 with hp | ⟨i, hi, hx, hp⟩
      · rw [hp]
        exact ⟨⟨fun es hw _ ↦ by simp [Out.seq] at hw, fun es vs hw _ ↦ by simp [Out.seq] at hw⟩,
          fun es hw _ ↦ by simp [Out.seq] at hw⟩
      · rw [hp]
        obtain ⟨hreq, hpost⟩ := dispC_ok hX hpre hs h1 i hi (by simpa using hx)
        exact blockC_call hpre hreq hpost fun hp hs' ↦ chkC_ok hX ss hp h hs'
  | .ret vs :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases hr : retC X st vs with
    | false => rw [hr] at h; cases h
    | true =>
      refine ⟨⟨fun es hw _ ↦ by simp [walk, walk1, Out.seq] at hw, fun es vs' hw _ ↦ ?_⟩,
        fun es hw _ ↦ by simp [walk, walk1, Out.seq] at hw⟩
      simp only [walk, walk1, Out.seq, Out.ret.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨covC_nil W, fun _ ↦ (retC_ok hX hpre hs hr).mono fun _ ↦ Or.inl⟩

/-- **The pass over the arms, on the path**: the outcome's, and, falling through, an arm that can fall
through whose end state is valid. -/
theorem chkArmsC_ok {X : CX} (hX : XOk sigOf H rd f σ X) (x : V) : ∀ {j : ℕ} (arms : List (List Stmt)) {st : CSt}
    {bs : List (Bool × CSt × CSt)} {W : K → Prop},
    (∀ c ∈ H.sig.pre, W (c.addr σ)) → chkArmsC X x j arms st = some bs → StOk rd W σ st →
      OutC sigOf H σ rd (f.params.map σ) W (walkArms σ x j arms) ∧
        ∀ es, walkArms σ x j arms = .fall es → EvsOk sigOf rd σ es →
          ∃ b ∈ bs, b.1 = false ∧ StOk rd (fun y ↦ W y ∨ EW sigOf rd σ es y) σ b.2.2
  | j, [], _, _, _, _, _, _ => ⟨⟨fun es hw _ ↦ by simp [walkArms] at hw, fun es vs hw _ ↦ by simp [walkArms] at hw⟩,
      fun es hw _ ↦ by simp [walkArms] at hw⟩
  | j, a :: as, st, bs, W, hpre, h, hs => by
    simp only [chkArmsC] at h
    cases h1 : chkC (X.ext (carm x j)) a st with
    | none => rw [h1] at h; cases h
    | some s1 =>
      simp only [h1] at h
      cases h2 : chkArmsC X x (j + 1) as (st.cnt s1) with
      | none => rw [h2] at h; cases h
      | some l =>
        simp only [h2, Option.some.injEq] at h
        subst h
        rw [walkArms]
        split_ifs with hxj
        · refine ⟨(chkC_ok (hX.ext (carm_ok hxj)) a hpre h1 hs).1, fun es hw hh ↦
            ⟨_, List.mem_cons_self, endsRet_false hw, ?_⟩⟩
          exact (chkC_ok (hX.ext (carm_ok hxj)) a hpre h1 hs).2 es hw hh
        · obtain ⟨ho, hb⟩ := chkArmsC_ok hX x as hpre h2 (hs.cnt s1)
          refine ⟨ho, fun es hw hh ↦ ?_⟩
          obtain ⟨b, hb, hb1, hbs⟩ := hb es hw hh
          exact ⟨b, List.mem_cons_of_mem _ hb, hb1, hbs⟩
end

end Pass

/-! ## A loop's tail -/

section Tail

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} {σ : Val} {rd : Reader} {W : K → Prop}

theorem CIdx.beq_eq : ∀ {a b : CIdx}, CIdx.beq a b = true → a = b
  | .num a, .num b, h => by rw [Nat.eq_of_beq_eq_true h]
  | .val a, .val b, h => by rw [Nat.eq_of_beq_eq_true h]
  | .mono a, .mono b, h => by rw [CCell.beq_eq h]
  | .num _, .val _, h => by simp [CIdx.beq] at h
  | .val _, .num _, h => by simp [CIdx.beq] at h
  | .num _, .mono _, h => by simp [CIdx.beq] at h
  | .mono _, .num _, h => by simp [CIdx.beq] at h
  | .val _, .mono _, h => by simp [CIdx.beq] at h
  | .mono _, .val _, h => by simp [CIdx.beq] at h

theorem slotW_cons_ne {a a' : E} {l : List E} {b : ℕ} (hb : b ≠ 0) : slotW (a :: l) b = slotW (a' :: l) b := by
  cases b with
  | zero => exact absurd rfl hb
  | succ b => rfl

theorem valW_cons_noSlot0 {c : CCell} (hc : noSlot0 c = true) (a a' : E) (l : List E) :
    c.valW (slotW (a :: l)) = c.valW (slotW (a' :: l)) := by
  refine valW_congr fun b hb ↦ slotW_cons_ne ?_
  have := List.all_eq_true.mp hc b hb
  simp only [Bool.not_eq_true'] at this
  exact Nat.ne_of_beq_eq_false this

theorem idx_cons_noSlot0 {i : CIdx} (hi : noSlot0I i = true) (a a' : E) (l : List E) :
    (idxC i).valW (slotW (a :: l)) = (idxC i).valW (slotW (a' :: l)) := by
  cases i with
  | num n => rfl
  | val v =>
    rw [idxC, valW_baseC, valW_baseC]
    simp only [noSlot0I, Bool.not_eq_true'] at hi
    exact slotW_cons_ne (Nat.ne_of_beq_eq_false hi)
  | mono c => exact valW_cons_noSlot0 hi a a' l

theorem set_cons_noSlot0 {r : CRun} (hr : noSlot0R r = true) (a a' : E) (l : List E) {x : K} :
    r.Set (slotW (a :: l)) x ↔ r.Set (slotW (a' :: l)) x := by
  simp only [noSlot0R, Bool.and_eq_true] at hr
  exact runSet_congr (valW_cons_noSlot0 hr.1.1 a a' l) (idx_cons_noSlot0 hr.1.2 a a' l)
    (idx_cons_noSlot0 hr.2 a a' l)

theorem endOf_noSlot0 {ei : CIdx} {endc : Option ℕ} (h : endOf ei = some endc) : noSlot0I ei = true := by
  cases ei with
  | num => rfl
  | val v =>
    cases v with
    | zero => simp [endOf] at h
    | succ v => rfl
  | mono => simp [endOf] at h

theorem tailP_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {mp mx : List CCell} {ws wx : List E} (hmp : MsOk (vw σ) mp (slotW ws)) (hmx : MsOk (vw σ) mx (slotW wx))
    {ex : Bool} : ∀ {cs : List CCell} {wl wl' : List Wit}, tailP X st mp mx ex cs wl = some wl' →
      ∀ c ∈ cs, W (c.addrW (slotW ws)) ∨ (ex = true ∧ noSlot0 c = true ∧ W (c.addrW (slotW wx)))
  | [], _, _, _, c, hc => by simp at hc
  | c :: cs, [], _, h, _, _ => by simp [tailP] at h
  | c :: cs, w :: wl, wl', h, c0, hc0 => by
    simp only [tailP] at h
    obtain ⟨hb, h⟩ := cond_some h
    rcases List.mem_cons.mp hc0 with rfl | hc0
    · rcases Bool.or_eq_true_iff.mp hb with h1 | h1
      · left
        split at h1
        · rename_i c' hi
          have := ptOk_ok hX hpre hs h1
          rwa [addr_eq, CCell.addrW, instC_ok hmp hi] at this
        · cases h1
      · simp only [Bool.and_eq_true] at h1
        obtain ⟨⟨h1, h2⟩, h3⟩ := h1
        refine Or.inr ⟨h1, h2, ?_⟩
        split at h3
        · rename_i c' hi
          have := ptOk_ok hX hpre hs h3
          rwa [addr_eq, CCell.addrW, instC_ok hmx hi] at this
        · cases h3
    · exact tailP_ok hX hpre hs hmp hmx h c0 hc0

theorem tailR_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {mp mx : List CCell} {ws wx : List E} (hmp : MsOk (vw σ) mp (slotW ws)) (hmx : MsOk (vw σ) mx (slotW wx))
    {ex : Bool} {ei : CIdx} : ∀ {rs : List CRun} {wl wl' : List Wit}, tailR X st mp mx ex ei rs wl = some wl' →
      ∀ r ∈ rs, r.F W (slotW ws) ∨ (ex = true ∧ noSlot0R r = true ∧ r.F W (slotW wx)) ∨
        (r.lo = .val 0 ∧ r.hi = ei ∧ noSlot0 r.base = true ∧ ∃ b m0, instC mp r.base = some b ∧
          nth mp 0 = some m0 ∧ W ((b.mul (m0.pow r.stride)).addr σ))
  | [], _, _, _, r, hr => by simp at hr
  | r :: rs, [], _, h, _, _ => by simp [tailR] at h
  | r :: rs, w :: wl, wl', h, r0, hr0 => by
    simp only [tailR] at h
    cases hb : tailR1 X st mp mx ex ei r w with
    | false =>
      rw [hb, Bool.cond_false] at h
      obtain ⟨he, h⟩ := cond_some h
      simp only [Bool.and_eq_true] at he
      cases hq : instR mx r with
      | none => rw [hq] at h; cases h
      | some q =>
        simp only [hq] at h
        cases hw : runOk X st q (w :: wl) with
        | none => simp [hw] at h
        | some wl1 =>
          simp only [hw] at h
          rcases List.mem_cons.mp hr0 with rfl | hr0
          · exact Or.inr (Or.inl ⟨he.1, he.2, (instR_runF hmx hq).mp (runOk_ok hX hpre hs hw)⟩)
          · exact tailR_ok hX hpre hs hmp hmx h r0 hr0
    | true =>
      rw [hb, Bool.cond_true] at h
      unfold tailR1 at hb
      rcases List.mem_cons.mp hr0 with rfl | hr0
      · rcases Bool.or_eq_true_iff.mp hb with h1 | h1
        · rcases Bool.or_eq_true_iff.mp h1 with h1 | h1
          · left
            split at h1
            · rename_i q hi
              exact (instR_runF hmp hi).mp (rnOk_ok hX hs h1)
            · cases h1
          · simp only [Bool.and_eq_true] at h1
            obtain ⟨⟨h1, h2⟩, h3⟩ := h1
            refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
            split at h3
            · rename_i q hi
              exact (instR_runF hmx hi).mp (rnOk_ok hX hs h3)
            · cases h3
        · simp only [Bool.and_eq_true] at h1
          obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h1
          refine Or.inr (Or.inr ⟨CIdx.beq_eq e1, CIdx.beq_eq e2, e3, ?_⟩)
          split at e4
          · rename_i b m0 hb' hm
            exact ⟨b, m0, hb', hm, ptOk_ok hX hpre hs e4⟩
          · cases e4
      · exact tailR_ok hX hpre hs hmp hmx h r0 hr0

theorem tailPP_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {mp mx : List CCell} {ws wx : List E} (hmp : MsOk (vw σ) mp (slotW ws)) (hmx : MsOk (vw σ) mx (slotW wx))
    {ex : Bool} : ∀ {ps : List (CCell × List ℕ)} {wl wl' : List Wit}, tailPP X st mp mx ex ps wl = some wl' →
      ∀ p ∈ ps, (∀ x, PtrSet rd (p.1.addrW (slotW ws)) p.2 x → W x) ∨
        (ex = true ∧ noSlot0 p.1 = true ∧ ∀ x, PtrSet rd (p.1.addrW (slotW wx)) p.2 x → W x)
  | [], _, _, _, p, hp => by simp at hp
  | p :: ps, wl, wl', h, p0, hp0 => by
    simp only [tailPP] at h
    have key : ∀ {ms : List CCell} {w' : List E}, MsOk (vw σ) ms (slotW w') → ∀ {wl1 : List Wit},
        (match instC ms p.1 with
          | some c => ptrOk X st c p.2 wl
          | none => none) = some wl1 → ∀ x, PtrSet rd (p.1.addrW (slotW w')) p.2 x → W x := by
      intro ms w' hms wl1 h1
      cases hi : instC ms p.1 with
      | none => rw [hi] at h1; cases h1
      | some c =>
        rw [hi] at h1
        exact fun x hx ↦ ptrOk_ok hX hpre hs h1 x ((ptrSet_inst hms hi).mpr hx)
    split at h
    · next wl1 h1 =>
      rcases List.mem_cons.mp hp0 with rfl | hp0
      · exact Or.inl (key hmp h1)
      · exact tailPP_ok hX hpre hs hmp hmx h p0 hp0
    · cases hb : (ex && noSlot0 p.1) with
      | false => rw [hb] at h; cases h
      | true =>
        rw [hb, Bool.cond_true] at h
        simp only [Bool.and_eq_true] at hb
        split at h
        · next c hi =>
          split at h
          · next wl2 h2 =>
            have h2' : (match instC mx p.1 with
                | some c => ptrOk X st c p.2 wl
                | none => none) = some wl2 := by rw [hi]; exact h2
            rcases List.mem_cons.mp hp0 with rfl | hp0
            · exact Or.inr ⟨hb.1, hb.2, key hmx h2'⟩
            · exact tailPP_ok hX hpre hs hmp hmx h p0 hp0
          · cases h
        · cases h

theorem tailPR_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {mp mx : List CCell} {ws wx : List E} (hmp : MsOk (vw σ) mp (slotW ws)) (hmx : MsOk (vw σ) mx (slotW wx))
    {ex : Bool} {ei : CIdx} : ∀ {ps : List (CRun × List ℕ)} {wl wl' : List Wit},
      tailPR X st mp mx ex ei ps wl = some wl' →
      ∀ p ∈ ps, (∀ a, p.1.Set (slotW ws) a → ∀ x, PtrSet rd a p.2 x → W x) ∨
        (ex = true ∧ noSlot0R p.1 = true ∧ ∀ a, p.1.Set (slotW wx) a → ∀ x, PtrSet rd a p.2 x → W x) ∨
        (p.1.lo = .val 0 ∧ p.1.hi = ei ∧ noSlot0 p.1.base = true ∧ ∃ b m0, instC mp p.1.base = some b ∧
          nth mp 0 = some m0 ∧ ∀ x, PtrSet rd ((b.mul (m0.pow p.1.stride)).addr σ) p.2 x → W x)
  | [], _, _, _, p, hp => by simp at hp
  | p :: ps, wl, wl', h, p0, hp0 => by
    simp only [tailPR] at h
    have key : ∀ {ms : List CCell} {w' : List E}, MsOk (vw σ) ms (slotW w') → ∀ {wl1 : List Wit},
        (match instR ms p.1 with
          | some q => ptrROk X st q p.2 wl
          | none => none) = some wl1 → ∀ a, p.1.Set (slotW w') a → ∀ x, PtrSet rd a p.2 x → W x := by
      intro ms w' hms wl1 h1
      cases hi : instR ms p.1 with
      | none => rw [hi] at h1; cases h1
      | some q =>
        rw [hi] at h1
        exact fun a ha ↦ ptrROk_ok hX hpre hs h1 a ((instR_set hms hi).mpr ha)
    split at h
    · next wl1 h1 =>
      rcases List.mem_cons.mp hp0 with rfl | hp0
      · exact Or.inl (key hmp h1)
      · exact tailPR_ok hX hpre hs hmp hmx h p0 hp0
    · split at h
      · next wl2 h2 =>
        cases hb : (ex && noSlot0R p.1) with
        | false => rw [hb] at h2; cases h2
        | true =>
          rw [hb, Bool.cond_true] at h2
          simp only [Bool.and_eq_true] at hb
          rcases List.mem_cons.mp hp0 with rfl | hp0
          · exact Or.inr (Or.inl ⟨hb.1, hb.2, key hmx h2⟩)
          · exact tailPR_ok hX hpre hs hmp hmx h p0 hp0
      · cases hb : (CIdx.beq p.1.lo (.val 0) && CIdx.beq p.1.hi ei && noSlot0 p.1.base) with
        | false => rw [hb] at h; cases h
        | true =>
          rw [hb, Bool.cond_true] at h
          simp only [Bool.and_eq_true] at hb
          obtain ⟨⟨e1, e2⟩, e3⟩ := hb
          split at h
          · next b m0 hib hm0 =>
            split at h
            · next wl3 h3 =>
              rcases List.mem_cons.mp hp0 with rfl | hp0
              · exact Or.inr (Or.inr ⟨CIdx.beq_eq e1, CIdx.beq_eq e2, e3, b, m0, hib, hm0,
                  ptrOk_ok hX hpre hs h3⟩)
              · exact tailPR_ok hX hpre hs hmp hmx h p0 hp0
            · cases h
          · cases h

/-- **A loop's tail**: after its body (`W`, the state `st`), its tail call `callIf c self (i' :: ps)` and
its `ret []`, the guarantees written: by the path; or, entered, by the next iteration (a guarantee not
over the counter is its own instance there), not entered, by the path at the exit (the next counter
is the end); or a run `[counter, end)` accumulated: the counter's point by the path, the rest by the
next iteration, none at the exit. -/
theorem tailC_ok (hX : XOk sigOf H rd f σ X) (hself : sigOf f.name = H.sig) (hrm : H.sig.retM = [])
    (hpv : H.sig.postV = []) (hre : H.sig.retEq = []) (hpq : H.sig.postQ = [])
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ))
    {st : CSt} (hs : StOk rd W σ st) {ei : CIdx} (hterm : (CIdx.val 0, ei) ∈ H.sig.term) {endc : Option ℕ}
    (hend : endOf ei = some endc) {m : ℕ} (hpar : f.params = (List.range m).map V.n)
    (hover : idxOver m ei = true) {ps : List V} (hps : f.params = V.n 0 :: ps) {c i' : V}
    (hi' : σ i' = σ (V.n 0) * ofK (addressOfIndex 1))
    (hc : σ c = σ (V.n 0) * ofK (addressOfIndex 1) + Res.endVal σ f endc)
    (h : tailC X st (i' :: ps) ei = true) :
    PostW0 sigOf H rd σ (f.params.map σ)
      (fun x ↦ W x ∨ EW sigOf rd σ [.inK c, if σ c = 0 then .skip f.name (i' :: ps) else .call f.name (i' :: ps) []] x)
      [] := by
  set e : Ev := if σ c = 0 then .skip f.name (i' :: ps) else .call f.name (i' :: ps) [] with he
  have hws0' : f.params.map σ = σ (V.n 0) :: ps.map σ := by rw [hps, List.map_cons]
  have hm0 : 0 < m := by
    have := congrArg List.length (hpar.symm.trans hps)
    simp at this
    omega
  have hslot : ∀ b < m, slotW (f.params.map σ) b = vw σ b := fun b hb ↦ by
    rw [hpar, List.map_map]; exact slotW_params hb
  have hei : (idxC ei).valW (slotW (f.params.map σ)) = (idxC ei).valW (vw σ) := by
    cases ei with
    | num n => rfl
    | val v => rw [idxC, valW_baseC, valW_baseC]; exact hslot v (by simpa [idxOver] using hover)
    | mono => simp [endOf] at hend
  have hendv : Res.endVal σ f endc = (idxC ei).valW (vw σ) := by
    cases ei with
    | num n =>
      simp only [endOf, Option.some.injEq] at hend
      subst hend
      rw [idxC, valW_const]
      rfl
    | val v =>
      cases v with
      | zero => simp [endOf] at hend
      | succ v =>
        cases v with
        | succ => simp [endOf] at hend
        | zero =>
          simp only [endOf, Option.some.injEq] at hend
          subst hend
          have hm : 1 < m := by simpa [idxOver] using hover
          obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
          rw [idxC, valW_baseC]
          simp only [Res.endVal, hpar, List.range_succ_eq_map, List.map_cons, List.map_map]
          rfl
    | mono => simp [endOf] at hend
  have hexit : σ c = 0 → σ (V.n 0) * ofK (addressOfIndex 1) = (idxC ei).valW (vw σ) := fun h0 ↦ by
    rw [← hendv]
    exact CoreMode.char2_eq (by rw [← hc, h0])
  have hcall : σ c ≠ 0 → ∀ x, PostSet rd H.sig ((i' :: ps).map σ) x →
      EW sigOf rd σ [.inK c, e] x := fun h0 x hx ↦ by
    refine ⟨e, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    rw [he, ite_eq_right h0]
    simp only [EvW]
    rw [hself, List.append_nil]
    exact hx
  unfold tailC at h
  cases hmp : monos st.env X.params with
  | none => simp [hmp] at h
  | some mp =>
    cases ht : getF X.T st.nt with
    | none => simp [hmp, ht] at h
    | some wl =>
      cases hmi : monoOf st.env i' with
      | none => simp [hmp, ht, hmi] at h
      | some mi =>
        simp only [hmp, ht, hmi] at h
        obtain ⟨hmp', hlp⟩ := monos_ok hs.env _ mp hmp
        rw [hX.params] at hmp' hlp
        have hmx := msOk_setNth (n := 1) hmp' (by simpa using hlp) (show mi.valW (vw σ) = σ i' by
          rw [← val_eq, ← monoOf_ok hs.env hmi])
        have hwx0 : ei = .val 1 → σ c = 0 → slotW (setNth (f.params.map σ) 1 (σ i')) = slotW (f.params.map σ) :=
          fun he1 h0 ↦ funext fun b ↦ by
            rw [slotW_setNth]
            split_ifs with hb
            · obtain ⟨rfl, -⟩ := hb
              rw [hi', hexit h0, he1, idxC, valW_baseC]
              exact (hslot 1 (by subst he1; simpa [idxOver] using hover)).symm
            · rfl
        -- a run `[counter, end)`: the counter's cell, or, entered, the next iteration's run
        have hacc : ∀ (r : CRun) (b m0 : CCell), r.lo = .val 0 → r.hi = ei → noSlot0 r.base = true →
            instC mp r.base = some b → nth mp 0 = some m0 → ∀ a, r.Set (slotW (f.params.map σ)) a →
            a = (b.mul (m0.pow r.stride)).addr σ ∨ (σ c ≠ 0 ∧ r.Set (slotW ((i' :: ps).map σ)) a) := by
          intro r b m0 hlo hhi hnb hb hm0' a ha
          have hl0 : (idxC r.lo).valW (slotW (f.params.map σ)) = vw σ 0 := by
            rw [hlo, idxC, valW_baseC]; exact hslot 0 hm0
          have hh0 : (idxC r.hi).valW (slotW (f.params.map σ)) = (idxC ei).valW (vw σ) := by
            rw [hhi]; exact hei
          obtain ⟨ylo, yhi, j, hylo, hyhi, h3, h4, rfl⟩ := ha
          rw [hl0] at hylo
          rw [hh0] at hyhi
          have hcap := (rep_spec hyhi).1
          rcases Nat.eq_or_lt_of_le h3 with rfl | h3
          · left
            have hb' := instC_ok hmp' hb
            have hm0'' := hmp' 0 m0 hm0'
            have hcell : (b.mul (m0.pow r.stride)).addr σ =
                (r.base.valW (slotW (f.params.map σ)) * ofK (addressOfIndex (r.stride * ylo))).limb 0 := by
              rw [addr_eq, CCell.addrW, valW_mul, valW_pow, hb', hm0'', hslot 0 hm0, (rep_spec hylo).2,
                ← ofK_pow']
              simp only [addressOfIndex, ← pow_mul, mul_comm]
            exact hcell.symm
          · by_cases h0 : σ c = 0
            · exfalso
              have hx := hexit h0
              rw [show σ (V.n 0) = vw σ 0 from rfl, (rep_spec hylo).2, ← ofK_mul', addressOfIndex,
                addressOfIndex, ← pow_add, ← addressOfIndex] at hx
              rw [← hx, rep_of (by omega), Option.some.injEq] at hyhi
              omega
            · refine Or.inr ⟨h0, ylo + 1, yhi, j, ?_, ?_, by omega, h4, ?_⟩
              · rw [hlo, idxC, valW_baseC, List.map_cons]
                show rep (σ i') = some (ylo + 1)
                rw [hi']
                exact rep_succ hylo (by omega)
              · rw [hhi, List.map_cons, idx_cons_noSlot0 (endOf_noSlot0 hend) (σ i') (σ (V.n 0)), ← hws0',
                  hei]
                exact hyhi
              · rw [List.map_cons, valW_cons_noSlot0 hnb (σ i') (σ (V.n 0)), ← hws0']
        cases hp : tailP X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) X.sig.post wl with
        | none => simp [hp] at h
        | some wl1 =>
          simp only [hp] at h
          cases hr : tailR X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) ei X.sig.postR wl1 with
          | none => simp [hr] at h
          | some wl2 =>
          simp only [hr] at h
          cases hpp : tailPP X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) X.sig.postP wl2 with
          | none => simp [hpp] at h
          | some wl3 =>
          simp only [hpp] at h
          cases hpr : tailPR X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) ei X.sig.postPR wl3 with
          | none => simp [hpr] at h
          | some wl'' =>
            have hNN : H.sig.postN = [] ∧ H.sig.postRN = [] := by
              rw [hpr] at h
              rcases wl'' with _ | ⟨_, _⟩
              · simp only [Bool.and_eq_true, List.isEmpty_iff] at h
                rw [← hX.sig]; exact h
              · simp at h
            rw [hX.sig] at hp hr hpp hpr
            have HP := tailP_ok hX hpre hs hmp' hmx hp
            have HR := tailR_ok hX hpre hs hmp' hmx hr
            have HPP := tailPP_ok hX hpre hs hmp' hmx hpp
            have HPR := tailPR_ok hX hpre hs hmp' hmx hpr
            unfold PostW0
            rw [List.map_nil, List.append_nil]
            refine ⟨⟨fun c0 hc0 ↦ ?_, fun r hr0 ↦ ?_⟩, ptrOk_of (fun p hp0 ↦ ?_) (fun p hp0 ↦ ?_),
              fun k c hkc ↦ (by rw [hrm] at hkc; cases hkc), fun i m h ↦ (by rw [hpv] at h; cases h),
              fun p h ↦ (by rw [hre] at h; cases h), fun x ⟨p, h, _⟩ ↦ (by rw [hpq] at h; cases h), by
                rw [hNN.1, hNN.2]; exact ⟨fun _ hc ↦ (by cases hc), fun _ hr ↦ (by cases hr)⟩⟩
            · rcases HP c0 hc0 with h1 | ⟨hex, hns, h1⟩
              · exact Or.inl h1
              · have hei1 : ei = .val 1 := CIdx.beq_eq hex
                by_cases h0 : σ c = 0
                · exact Or.inl (by rw [← hwx0 hei1 h0]; exact h1)
                · refine Or.inr (hcall h0 _ (Or.inl (Or.inl ⟨c0, hc0, ?_⟩)))
                  rw [CCell.addrW, CCell.addrW, hws0', List.map_cons, valW_cons_noSlot0 hns]
            · rcases HR r hr0 with h1 | ⟨hex, hns, h1⟩ | ⟨hlo, hhi, hnb, b, m0, hb, hm0', h1⟩
              · exact h1.mono fun _ ↦ Or.inl
              · have hei1 := CIdx.beq_eq hex
                by_cases h0 : σ c = 0
                · rw [← hwx0 hei1 h0]; exact h1.mono fun _ ↦ Or.inl
                · refine fun x hx ↦ Or.inr (hcall h0 x (Or.inl (Or.inr ⟨r, hr0, ?_⟩)))
                  rw [List.map_cons]
                  rw [hws0'] at hx
                  exact (set_cons_noSlot0 hns _ _ _).mp hx
              · intro x hx
                rcases hacc r b m0 hlo hhi hnb hb hm0' x hx with rfl | ⟨h0, hx'⟩
                · exact Or.inl h1
                · exact Or.inr (hcall h0 _ (Or.inl (Or.inr ⟨r, hr0, hx'⟩)))
            · rcases HPP p hp0 with h1 | ⟨hex, hns, h1⟩
              · exact fun x hx ↦ Or.inl (h1 x hx)
              · have hei1 : ei = .val 1 := CIdx.beq_eq hex
                by_cases h0 : σ c = 0
                · exact fun x hx ↦ Or.inl (h1 x (by rw [hwx0 hei1 h0]; exact hx))
                · refine fun x hx ↦ Or.inr (hcall h0 x (Or.inr (Or.inl (Or.inl ⟨p, hp0, ?_⟩))))
                  rw [CCell.addrW, List.map_cons, valW_cons_noSlot0 hns _ (σ (V.n 0)), ← hws0']
                  exact hx
            · rcases HPR p hp0 with h1 | ⟨hex, hns, h1⟩ | ⟨hlo, hhi, hnb, b, m0, hb, hm0', h1⟩
              · exact fun a ha x hx ↦ Or.inl (h1 a ha x hx)
              · have hei1 := CIdx.beq_eq hex
                by_cases h0 : σ c = 0
                · exact fun a ha x hx ↦ Or.inl (h1 a (by rw [hwx0 hei1 h0]; exact ha) x hx)
                · refine fun a ha x hx ↦ Or.inr (hcall h0 x (Or.inr (Or.inl (Or.inr ⟨p, hp0, a, ?_, hx⟩))))
                  rw [List.map_cons]
                  rw [hws0'] at ha
                  exact (set_cons_noSlot0 hns _ _ _).mp ha
              · intro a ha x hx
                rcases hacc p.1 b m0 hlo hhi hnb hb hm0' a ha with rfl | ⟨h0, ha'⟩
                · exact Or.inl (h1 x hx)
                · exact Or.inr (hcall h0 x (Or.inr (Or.inl (Or.inr ⟨p, hp0, a, ha', hx⟩))))

end Tail

/-! ## The function -/

section Main

/-- A precondition's address at the parameters' words (then any words) is its address at the values
`V.n b`. -/
theorem addr_pre {σ : Val} {f : Fn} {pre : List CCell} (hpar : f.params = (List.range f.params.length).map V.n)
    (hpov : preOver f.params.length pre = true) {c : CCell} (hc : c ∈ pre) (ws : List E) :
    c.addrW (slotW (f.params.map σ ++ ws)) = c.addr σ := by
  have hv : c.valW (vw σ) = c.valW (slotW (f.params.map σ ++ ws)) := valW_congr fun b hb ↦ by
    have := Nat.blt_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp hpov c hc) b hb)
    rw [slotW_append, ite_eq_left (by rw [List.length_map]; exact this), hpar, List.map_map]
    exact (slotW_params this).symm
  rw [addr_eq, CCell.addrW, CCell.addrW, hv]

theorem loopBody_of {fn : Fn} {pre : List Stmt} {a b : Stmt} (h : fn.body = pre ++ [a, b]) : loopBody fn = pre := by
  simp [loopBody, h]

theorem idxOver_val {σ : Val} {f : Fn} {m : ℕ} (hpar : f.params = (List.range m).map V.n) {i : CIdx}
    (h : idxOver m i = true) : (idxC i).valW (slotW (f.params.map σ)) = (idxC i).valW (vw σ) := by
  cases i with
  | num n => rfl
  | val v =>
    rw [idxC, valW_baseC, valW_baseC, hpar, List.map_map]
    exact slotW_params (by simpa [idxOver] using h)
  | mono c =>
    rw [idxC]
    refine valW_congr fun b hb ↦ ?_
    have := List.all_eq_true.mp h b hb
    rw [hpar, List.map_map]
    exact slotW_params (Nat.blt_eq.mp this)

theorem paramEnv_get : ∀ (m k : ℕ) (c : CCell), getF (paramEnv m) k = some c → c = baseC k
  | 0, k, c, h => by simp [paramEnv, getF_nil] at h
  | m + 1, k, c, h => by
    simp only [paramEnv, Trie.seq_eq, id] at h
    rcases Check.getF_setF h with ⟨rfl, rfl⟩ | h
    · rfl
    · exact paramEnv_get m k c h

theorem paramEnv_ok (σ : Val) (m : ℕ) : EnvOk σ (paramEnv m) := fun k c h ↦ by
  rw [paramEnv_get m k c h, val_baseC]

/-- The own ghosts' monomials name the own ghost words. -/
theorem ghostMs_ok (σ : Val) (G : HSig) : MsOk (vw σ) (ghostMs G.ghosts) (slotW (ownG G σ)) := by
  intro b m hb
  rw [nth_eq, ghostMs, List.getElem?_map] at hb
  by_cases h : b < G.ghosts
  · simp only [List.getElem?_range h, Option.map_some, Option.some.injEq] at hb
    subst hb
    unfold slotW ownG
    simp [List.getD_eq_getElem?_getD, List.getElem?_range h, valW_baseC]
  · rw [List.getElem?_eq_none (by simpa using h)] at hb
    cases hb

theorem initC_ok {X : CX} {σ : Val} {rd : Reader} {st0 : CSt} (h : initC X = some st0) :
    StOk rd (fun x ↦ PreSet rd X.sig (X.params.map σ ++ ownG X.sig σ) x) σ st0 := by
  unfold initC at h
  cases hd : dersOk X.ders with
  | false => simp [hd] at h
  | true =>
  simp only [hd, Bool.not_true, Bool.cond_false] at h
  rw [Trie.seq_eq] at h
  cases hm : monos (paramEnv X.params.length) X.params with
  | none => simp [hm] at h
  | some mp =>
    simp only [hm] at h
    cases h1 : instPP (mp ++ ghostMs X.sig.ghosts) X.sig.preP with
    | none => simp [h1] at h
    | some pps =>
      cases hr : instAllR (mp ++ ghostMs X.sig.ghosts) X.sig.preR with
      | none => simp [h1, hr] at h
      | some rs =>
        cases h2 : instPRL (mp ++ ghostMs X.sig.ghosts) X.sig.prePR with
        | none => simp [h1, hr, h2] at h
        | some prs =>
          simp only [h1, hr, h2, Option.some.injEq] at h
          subst h
          obtain ⟨hmp0, hlp⟩ := monos_ok (paramEnv_ok σ _) _ mp hm
          have hmp := msOk_append hmp0 (ghostMs_ok σ X.sig) (by simpa using hlp)
          refine pushPRL_ok (pushRL_ok (pushPL_ok ⟨paramEnv_ok σ _, fun n c h ↦ by simp [getF_nil] at h,
            fun r R h ↦ by simp [getF_nil] at h, fun k p h ↦ by simp [getF_nil] at h,
            fun n p h ↦ by simp [getF_nil] at h, fun n p h ↦ by simp [getF_nil] at h,
            fun n p h ↦ by simp [getF_nil] at h, fun n p h ↦ by simp [getF_nil] at h, fun e he ↦ by simp at he,
            fun p hp ↦ by simp at hp, fun p hp ↦ by simp at hp⟩ (fun _ h ↦ h)
            fun p hp x hx ↦ ?_) (fun _ h ↦ h) fun q hq ↦ ?_) (fun _ h ↦ h) fun p hp a ha x hx ↦ ?_
          · obtain ⟨p0, hp0, hi, he⟩ := instPP_ok h1 p hp
            refine Or.inr (Or.inl ⟨p0, hp0, ?_⟩)
            rw [← he]
            exact (ptrSet_inst hmp hi).mp hx
          · obtain ⟨r, hr0, hi⟩ := instAllR_ok hr q hq
            exact (instR_runF hmp hi).mpr fun x hx ↦ Or.inl (Or.inr ⟨r, hr0, hx⟩)
          · obtain ⟨p0, hp0, hi, he⟩ := instPRL_ok h2 p hp
            refine Or.inr (Or.inr ⟨p0, hp0, a, (instR_set hmp hi).mp ha, ?_⟩)
            rw [← he]
            exact hx

/-- A loop helper's path, its tail's events named: its body's, the tail's guard, then its tail call. -/
theorem walk_tail {σ : Val} {pre : List Stmt} {c i' : V} {g : String} {ps : List V} {es1 : List Ev}
    (h : walk σ pre = .fall es1) :
    walk σ (pre ++ [.callIf c g (i' :: ps), .ret []]) =
      .ret (es1 ++ [.inK c, if σ c = 0 then .skip g (i' :: ps) else .call g (i' :: ps) []]) [] := by
  rw [walk_append, h]
  simp [walk, walk1, Out.seq, Out.pre]

/-- **A top-level atom before the first `ret` is on every path that returns.** -/
theorem topAtoms_on_path {σ : Val} : ∀ {body : List Stmt} {es : List Ev} {vs : List V},
    walk σ body = .ret es vs → ∀ a ∈ topAtoms body, Ev.atom a ∈ es
  | [], _, _, _, a, ha => by simp [topAtoms] at ha
  | s :: ss, es, vs, h, a, ha => by
    unfold topAtoms at ha
    cases hn : Memory.Stmt.noRet s with
    | false => rw [hn] at ha; simp at ha
    | true =>
      rw [hn, Bool.cond_true] at ha
      rw [walk] at h
      rcases walk1_noRet (σ := σ) s hn with ⟨es1, h1⟩ | h1
      · rw [h1] at h
        simp only [Out.seq] at h
        cases h2 : walk σ ss with
        | fall _ => rw [h2] at h; simp [Out.pre] at h
        | stuck => rw [h2] at h; simp [Out.pre] at h
        | ret es2 vs2 =>
          rw [h2] at h
          simp only [Out.pre, Out.ret.injEq] at h
          obtain ⟨rfl, -⟩ := h
          have ih := topAtoms_on_path h2 a
          cases s with
          | atom b =>
            simp only at ha
            rcases List.mem_cons.mp ha with rfl | ha
            · simp only [walk1, Out.fall.injEq] at h1
              subst h1
              exact List.mem_append_left _ List.mem_cons_self
            · exact List.mem_append_right _ (ih ha)
          | ite _ _ _ => exact List.mem_append_right _ (ih ha)
          | match_ _ _ => exact List.mem_append_right _ (ih ha)
          | call _ _ _ => exact List.mem_append_right _ (ih ha)
          | callIf _ _ _ => exact List.mem_append_right _ (ih ha)
          | dispatch _ _ _ _ => exact List.mem_append_right _ (ih ha)
          | ret _ => simp [Memory.Stmt.noRet] at hn
      · rw [h1] at h; simp [Out.seq] at h

theorem getF_keysT : ∀ (l : List ℕ) (t : Trie Unit) {k : ℕ}, (getF (keysT l t) k).isSome = true →
    k ∈ l ∨ (getF t k).isSome = true
  | [], _, _, h => Or.inr h
  | a :: l, t, k, h => by
    rw [keysT, Trie.seq_eq] at h
    rcases getF_keysT l _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
      rcases Check.getF_setF hu with ⟨rfl, -⟩ | hu
      · exact Or.inl List.mem_cons_self
      · exact Or.inr (by rw [hu]; rfl)

/-- **The frame run cells a certificate guarantees at return**: each a cell of a `frameAddr` among the atoms,
its value defined by one of them, or past a nonempty run. -/
theorem faOk_spec {as : List Atom} : ∀ {fas : List (ℕ × ℕ)}, faOk as (dstKeys as) fas = true →
    ∀ p ∈ fas, (∃ run v, Atom.frameAddr (V.n p.1) run ∈ as ∧ run[p.2]? = some v ∧ ∃ a ∈ as, v ∈ atomDst a) ∨
      ∃ run, Atom.frameAddr (V.n p.1) run ∈ as ∧ run ≠ [] ∧ run.length ≤ p.2
  | [], _, p, hp => by simp at hp
  | (kp, i) :: l, h, p, hp => by
    simp only [faOk, Bool.and_eq_true, List.any_eq_true] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨a, ha, hfa⟩ := h.1
      cases a with
      | frameAddr q run =>
        simp only [faAt, Bool.and_eq_true, Bool.or_eq_true] at hfa
        obtain ⟨hq, hv⟩ := hfa
        cases hqn : vnum q with
        | none => rw [hqn] at hq; cases hq
        | some k =>
          rw [hqn] at hq
          have hk : k = kp := Nat.eq_of_beq_eq_true hq
          subst hk
          rw [vnum_eq hqn] at ha
          rcases hv with hv | hv
          · left
            cases hri : run[i]? with
            | none => rw [hri] at hv; cases hv
            | some v =>
              simp only [hri] at hv
              cases hvn : vnum v with
              | none => simp only [hvn] at hv; cases hv
              | some k' =>
                simp only [hvn] at hv
                rcases getF_keysT _ _ hv with hm | hm
                · obtain ⟨v', hv', hv'n⟩ := List.mem_filterMap.mp hm
                  obtain ⟨a', ha', hva'⟩ := List.mem_flatMap.mp hv'
                  refine ⟨run, v, ha, hri, a', ha', ?_⟩
                  rw [vnum_eq hvn, ← vnum_eq hv'n]
                  exact hva'
                · simp [getF_nil] at hm
          · right
            simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, Nat.ble_eq] at hv
            exact ⟨run, ha, hv.1, hv.2⟩
      | _ => simp [faAt] at hfa
    · exact faOk_spec h.2 p hp

/-- No frame run cell guaranteed (`HCert.fas` empty), none among them. -/
theorem noFAX {H : HCert} (hn : H.fas = []) {σ : Val} {x : K} : ¬ FAX H σ x := by
  rintro ⟨p, hp, -⟩
  rw [hn] at hp
  cases hp

/-- The frame run cells the certificate guarantees at return are frame run cells of the path. -/
theorem fax_faw {σ : Val} {H : HCert} {f : Fn} {es : List Ev} {vs : List V}
    (hfa : faOk (topAtoms f.body) (dstKeys (topAtoms f.body)) H.fas = true) (hw : walk σ f.body = .ret es vs)
    {x : K} (h : FAX H σ x) : FAW σ H.fas es x := by
  obtain ⟨p, hp, rfl⟩ := h
  rcases faOk_spec hfa p hp with ⟨run, v, hfr, hv, a, ha, hva⟩ | ⟨run, hfr, hne, hle⟩
  · exact Or.inl ⟨V.n p.1, run, p.2, v, topAtoms_on_path hw _ hfr, hv, ⟨a, topAtoms_on_path hw _ ha, hva⟩, rfl⟩
  · exact Or.inr ⟨p.1, p.2, run, hp, topAtoms_on_path hw _ hfr, hne, hle, rfl⟩

/-- **The heap check with calls and loops is sound, call by call**: on a path of a function passing `heapOkC`
that returns, its events holding, given its entry facts and its residuals, every event's needs are written before
it once the calls before it have their callees' returned words (`ReadsOkP`), and, every call having them, its
guarantees are written at return. A loop helper's own signature is `sigOf`'s for its name. -/
theorem out_seq_assocC : ∀ (o k l : Out), (o.seq k).seq l = o.seq (k.seq l)
  | .fall es, .fall es', l => by cases l <;> simp [Out.seq, Out.pre, List.append_assoc]
  | .fall es, .ret es' vs, l => by simp [Out.seq, Out.pre]
  | .fall es, .stuck, l => by simp [Out.seq, Out.pre]
  | .ret es vs, k, l => by simp [Out.seq]
  | .stuck, k, l => by simp [Out.seq]

theorem walk_appendC (σ : Val) : ∀ (l l' : List Stmt), walk σ (l ++ l') = (walk σ l).seq (walk σ l')
  | [], l' => by
      rw [List.nil_append, walk]
      cases walk σ l' <;> simp [Out.seq, Out.pre]
  | s :: l, l' => by rw [List.cons_append, walk, walk, walk_appendC σ l l', out_seq_assocC]

theorem out_pre_seqC (es : List Ev) : ∀ (o k : Out), (o.pre es).seq k = (o.seq k).pre es
  | .fall es', k => by cases k <;> simp [Out.seq, Out.pre, List.append_assoc]
  | .ret es' vs, k => by simp [Out.seq, Out.pre]
  | .stuck, k => by simp [Out.seq, Out.pre]

theorem out_seq_nilC : ∀ (o : Out), o.seq (.fall []) = o
  | .fall es => by simp [Out.seq, Out.pre]
  | .ret _ _ => rfl
  | .stuck => rfl

/-- **The body the pass reads walks as the body**: an `ite`'s continuation in each branch is one walk. -/
theorem walk_dupB (σ : Val) (ds : List ℕ) : ∀ ss : List Stmt, walk σ (dupB ds ss) = walk σ ss
  | [] => rfl
  | s :: ss => by
    cases s with
    | ite c z n =>
      simp only [dupB]
      cases dupC ds c with
      | false => simp only [Bool.cond_false, walk, walk_dupB σ ds ss]
      | true =>
        simp only [Bool.cond_true, walk, walk1, walk_appendC, out_seq_nilC]
        rw [out_pre_seqC]
        split_ifs <;> rfl
    | atom a => simp only [dupB, walk, walk_dupB σ ds ss]
    | match_ x arms => simp only [dupB, walk, walk_dupB σ ds ss]
    | call g args rets => simp only [dupB, walk, walk_dupB σ ds ss]
    | callIf c g args => simp only [dupB, walk, walk_dupB σ ds ss]
    | dispatch x fs args rets => simp only [dupB, walk, walk_dupB σ ds ss]
    | ret vs => simp only [dupB, walk, walk_dupB σ ds ss]

theorem walk_bodyC (σ : Val) (ds : List ℕ) (ss : List Stmt) : walk σ (bodyC ds ss) = walk σ ss := by
  unfold bodyC
  cases ds.isEmpty
  · exact walk_dupB σ ds ss
  · rfl

theorem heapOkC_soundP {pows : PowTree} (hp : pows.Ok) {sigOf : String → HSig} {f : Fn} {H : HCert}
    (hok : heapOkC pows sigOf f H = true) (hself : sigOf f.name = H.sig) {σ : Val} {rd : Reader}
    {es : List Ev} {vs : List V} (hw : walk σ f.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hE : EntryF H (f.params.map σ)) (hR : ResF H σ) (hD : DerOk H rd σ) (hG : GwOk H.sig rd σ) :
    ReadsOkP sigOf H rd σ (f.params.map σ) es ∧ ((∀ e ∈ es, EvM sigOf rd σ e) →
      (PostOkC sigOf H rd σ (f.params.map σ) es vs ∧ (H.fas = [] → PostOkW sigOf H rd σ (f.params.map σ) es vs)) ∧
      RetMOk H.sig (f.params.map σ) (vs.map σ) ∧ RetVOk rd H.sig (f.params.map σ ++ vs.map σ) ∧
      RetEqOk H.sig (f.params.map σ ++ vs.map σ)) := by
  unfold heapOkC at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨hpar, hpov⟩, hto⟩, -⟩, hfa⟩, hc⟩ := hok
  simp only [Trie.seq_eq] at hc
  have hpar' : f.params = (List.range f.params.length).map V.n := by
    rw [List.range_eq_range']; exact paramsN_eq _ 0 hpar
  generalize hXdef : (⟨pows, H.readT, trieFrom H.sig.pre 0 .nil, trieFrom H.calls 0 .nil, trieFrom H.rets 0 .nil,
    trieFrom H.res 0 .nil, keysT H.divs .nil, keysT H.hvs .nil, H.gargs, sigOf, H.sig, f.params, [],
    keysT H.eqs .nil, H.fas, H.ders⟩ : CX) = X at hc
  have hX : XOk sigOf H rd f σ X := by
    subst hXdef
    exact { R := rfl
            pre := fun k c h ↦ (getF_trieFrom _ _ _ h).resolve_right (by simp [getF_nil])
            pows := hp
            sigOf := rfl
            ga := rfl
            sig := rfl
            params := rfl
            res := fun i c h ↦ (getF_trieFrom _ _ _ h).resolve_right (by simp [getF_nil])
            term := fun q hq ↦ by
              have ho := List.all_eq_true.mp hto q hq
              simp only [Bool.and_eq_true] at ho
              exact (ltF_congr (idxOver_val hpar' ho.1) (idxOver_val hpar' ho.2)).mp (hE q hq)
            resF := hR
            path := fun c hc ↦ by simp at hc
            fas := rfl
            ders := rfl
            der := hD
            gw := hG }
  set W0 : K → Prop := fun x ↦ PreSet rd H.sig (f.params.map σ ++ ownG H.sig σ) x with hW0
  have hpreW : ∀ c ∈ H.sig.pre, W0 (c.addr σ) := fun c hc ↦
    Or.inl (Or.inl ⟨c, hc, addr_pre hpar' hpov hc _⟩)
  have fin : CovC sigOf H rd σ W0 es → ((∀ e ∈ es, EvM sigOf rd σ e) →
      PostW sigOf H rd σ (f.params.map σ) (fun x ↦ W0 x ∨ EW sigOf rd σ es x) vs) →
      ReadsOkP sigOf H rd σ (f.params.map σ) es ∧ ((∀ e ∈ es, EvM sigOf rd σ e) →
        (PostOkC sigOf H rd σ (f.params.map σ) es vs ∧
          (H.fas = [] → PostOkW sigOf H rd σ (f.params.map σ) es vs)) ∧
        RetMOk H.sig (f.params.map σ) (vs.map σ) ∧ RetVOk rd H.sig (f.params.map σ ++ vs.map σ) ∧
          RetEqOk H.sig (f.params.map σ ++ vs.map σ)) :=
    fun h1 h2 ↦ ⟨fun es1 e es2 he hm ↦ h1 es1 e es2 he hm, fun hM ↦
      ⟨⟨⟨(h2 hM).1.mono fun x hx ↦ hx.imp_right (fax_faw hfa hw),
        fun x hx ↦ ((h2 hM).2.1 x hx).imp_right (fax_faw hfa hw),
        fun x hx ↦ ((h2 hM).2.2.2.2.2.1 x hx).imp_right (fax_faw hfa hw),
        (h2 hM).2.2.2.2.2.2.mono fun x hx ↦ hx.imp_right (fax_faw hfa hw)⟩,
        fun hn ↦ ⟨(h2 hM).1.mono fun x hx ↦ hx.resolve_right (noFAX hn),
          fun x hx ↦ ((h2 hM).2.1 x hx).resolve_right (noFAX hn),
          fun x hx ↦ ((h2 hM).2.2.2.2.2.1 x hx).resolve_right (noFAX hn),
          (h2 hM).2.2.2.2.2.2.mono fun x hx ↦ hx.resolve_right (noFAX hn)⟩⟩,
      (h2 hM).2.2.1, (h2 hM).2.2.2.1, (h2 hM).2.2.2.2.1⟩⟩
  cases hi : initC X with
  | none => simp [hi] at hc
  | some st0 =>
    simp only [hi] at hc
    have hs0 : StOk rd W0 σ st0 := by
      have := initC_ok (X := X) (σ := σ) (rd := rd) hi
      rwa [hX.sig, hX.params] at this
    split at hc
    · obtain ⟨st', hst⟩ := Option.isSome_iff_exists.mp hc
      have hw' : walk σ (bodyC H.dups f.body) = .ret es vs := by rw [walk_bodyC]; exact hw
      exact fin ((chkC_ok hX _ hpreW hst hs0).1.2 es vs hw' hh).1
        fun hM ↦ ((chkC_ok hX _ hpreW hst hs0).1.2 es vs hw' hh).2 (evsOk_of hh hM)
    · rename_i ei hterm
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨⟨hrm, hpv⟩, hre⟩, hpq⟩, hc⟩ := hc
      have hrm : H.sig.retM = [] := List.isEmpty_iff.mp hrm
      have hpv : H.sig.postV = [] := List.isEmpty_iff.mp hpv
      have hre : H.sig.retEq = [] := List.isEmpty_iff.mp hre
      have hpq : H.sig.postQ = [] := List.isEmpty_iff.mp hpq
      unfold loopC at hc
      split at hc
      · rename_i endc c0 g args rest hend hrev
        split at hc
        · rename_i pre hls
          split at hc
          · rename_i st1 hst1
            split at hc
            · rename_i st2 hst2
              obtain ⟨c, i', p0, prest, hps, hbody, -, -⟩ := loopShape_spec hls
              have hlb := loopBody_of hbody
              -- the tail's statement, read off the reversed body
              have htl : Stmt.callIf c0 g args = .callIf c f.name (i' :: prest) := by
                have := congrArg List.reverse hbody
                rw [hrev] at this
                simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
                  List.cons_append, List.cons.injEq] at this
                exact this.2.1
              simp only [Stmt.callIf.injEq] at htl
              obtain ⟨h1, h2, h3⟩ := htl
              subst c0 g args
              -- the parameters
              have hp0 : p0 = V.n 0 ∧ f.params = V.n 0 :: prest := by
                have h1 := hpar'.symm.trans hps
                cases hm : f.params.length with
                | zero => rw [hm] at h1; simp at h1
                | succ k =>
                  rw [hm, List.range_succ_eq_map, List.map_cons] at h1
                  obtain ⟨h2, -⟩ := List.cons.inj h1
                  exact ⟨h2.symm, by rw [hps, ← h2]⟩
              obtain ⟨rfl, hps'⟩ := hp0
              -- the path
              obtain ⟨p0', prest', c', i'', es1, hps2, hw1, hes, hi'', hc''⟩ :=
                Res.loop_path (rd := rd) (by rw [hlb]; exact hls) hw hh
              rw [hlb] at hw1
              have hw2 := walk_tail (c := c) (g := f.name) (i' := i') (ps := prest) hw1
              rw [← hbody, hw] at hw2
              simp only [Out.ret.injEq] at hw2
              obtain ⟨hes2, rfl⟩ := hw2
              rw [hps', List.cons.injEq] at hps2
              obtain ⟨rfl, rfl⟩ := hps2
              rw [hes2] at hes
              simp only [List.append_cancel_left_eq, List.cons.injEq, Ev.inK.injEq, and_true] at hes
              obtain ⟨rfl, hee⟩ := hes
              have hi'eq : i'' = i' := by
                split_ifs at hee <;>
                  simp only [Ev.skip.injEq, Ev.call.injEq, List.cons.injEq, true_and, and_true] at hee <;>
                  exact hee.symm
              subst hi'eq
              subst hes2
              -- the body, then the tail
              have hh1 := (holds_append hh).1
              have hb1 := chkC_ok (rd := rd) hX pre hpreW hst1 hs0
              have hcov1 := hb1.1.1 es1 hw1 hh1
              have hpre1 : ∀ c ∈ H.sig.pre, (fun x ↦ W0 x ∨ EW sigOf rd σ es1 x) (c.addr σ) :=
                fun c hc ↦ Or.inl (hpreW c hc)
              have htl := fun hm1 : (∀ e ∈ es1, EvM sigOf rd σ e) ↦
                callIfC_ok hX hpre1 (hb1.2 es1 hw1 (evsOk_of hh1 hm1)) hst2
              have hterm' : (CIdx.val 0, ei) ∈ H.sig.term := by rw [hterm]; exact List.mem_singleton_self _
              have hover : idxOver f.params.length ei = true := by
                have := List.all_eq_true.mp hto _ hterm'
                simp only [Bool.and_eq_true] at this
                exact this.2
              refine fin (covC_append hcov1 fun hm1 ↦ ?_) fun hM ↦ PostW0.toW (((tailC_ok hX hself hrm hpv hre hpq
                (fun c hc ↦ Or.inl (hpre1 c hc)) (htl fun e he ↦ hM e (List.mem_append_left _ he)).2 hterm' hend
                hpar' hover hps' hi'' hc'' hc)).mono fun x hx ↦ ?_)
              · show CovC sigOf H rd σ _ ([Ev.inK c] ++ [_])
                refine covC_append (covC_single trivial) fun _ ↦ covC_single ?_
                split_ifs with h0
                · trivial
                · exact ReqOk.mono (fun _ ↦ Or.inl) ((htl hm1).1 h0)
              · rcases hx with ((hx | hx) | hx) | hx
                · exact Or.inl hx
                · exact Or.inr (ew_append_left hx)
                · exact Or.inr (ew_append_right hx)
                · exact Or.inr (ew_append_right hx)
            · cases hc
          · cases hc
        · cases hc
      · cases hc
    · cases hc

/-- **The heap check with calls and loops is sound**: on a path of a function passing `heapOkC` that
returns, its events holding and each entered call's callee guarantees' runs having their exponents,
given its entry facts and its residuals, every event's needs are written before it and its
guarantees are written at return. A loop helper's own signature is `sigOf`'s for its name. -/
theorem heapOkC_sound {pows : PowTree} (hp : pows.Ok) {sigOf : String → HSig} {f : Fn} {H : HCert}
    (hok : heapOkC pows sigOf f H = true) (hself : sigOf f.name = H.sig) {σ : Val} {rd : Reader}
    {es : List Ev} {vs : List V} (hw : walk σ f.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hM : ∀ e ∈ es, EvM sigOf rd σ e) (hE : EntryF H (f.params.map σ)) (hR : ResF H σ) (hD : DerOk H rd σ)
    (hG : GwOk H.sig rd σ) :
    ReadsOkC sigOf H rd σ (f.params.map σ) es ∧ PostOkC sigOf H rd σ (f.params.map σ) es vs ∧
      RetMOk H.sig (f.params.map σ) (vs.map σ) ∧ RetVOk rd H.sig (f.params.map σ ++ vs.map σ) ∧
      RetEqOk H.sig (f.params.map σ ++ vs.map σ) :=
  have h := heapOkC_soundP hp hok hself hw hh hE hR hD hG
  ⟨readsOkC_of_P h.1 hM, (h.2 hM).1.1, (h.2 hM).2⟩

/-- `heapOkC_sound` with no frame run cell guaranteed (`HCert.fas` empty): the guarantees written by the
events. -/
theorem heapOkC_soundW {pows : PowTree} (hp : pows.Ok) {sigOf : String → HSig} {f : Fn} {H : HCert}
    (hok : heapOkC pows sigOf f H = true) (hself : sigOf f.name = H.sig) {σ : Val} {rd : Reader}
    {es : List Ev} {vs : List V} (hw : walk σ f.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hM : ∀ e ∈ es, EvM sigOf rd σ e) (hE : EntryF H (f.params.map σ)) (hR : ResF H σ) (hD : DerOk H rd σ)
    (hG : GwOk H.sig rd σ) (hn : H.fas = []) : PostOkW sigOf H rd σ (f.params.map σ) es vs :=
  ((heapOkC_soundP hp hok hself hw hh hE hR hD hG).2 hM).1.2 hn

end Main

/-- **Constant preconditions** (`main`'s public input cells): a precondition of a signature whose preconditions
are cells only, each constant (`⟨[], k⟩`), is the address `g^k` of one of them, whatever the words. -/
theorem preSet_const {rd : Reader} {G : HSig} {ws : List E} {x : K} (hR : G.preR = []) (hP : G.preP = [])
    (hPR : G.prePR = []) (hc : ∀ c ∈ G.pre, c.bases = []) (h : PreSet rd G ws x) :
    ∃ c ∈ G.pre, x = addressOfIndex c.off := by
  rcases h with (⟨c, hc', rfl⟩ | ⟨r, hr, -⟩) | (⟨p, hp, -⟩ | ⟨p, hp, -⟩)
  · refine ⟨c, hc', ?_⟩
    rw [CCell.addrW, valW_nil (by simp [hc c hc'])]
    simp
  · rw [hR] at hr; cases hr
  · rw [hP] at hp; cases hp
  · rw [hPR] at hp; cases hp

/-! ## `heapOk`'s statement -/

end

end LeanVM.Guest.CoreMode
