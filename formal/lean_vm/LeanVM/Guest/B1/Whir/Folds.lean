/-
  LeanVM.Guest.B1.Whir.Folds

  The template's sumcheck rounds (`opening_fold` calls) run the Spec's `foldRounds`.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.Flat
public import LeanVM.Guest.B1.Whir.Run
public import LeanVM.Guest.B1.Opening.Meaning

/-!
# The fold rounds (TRIAGE G #35, #42)

The guest's running values, read through a valuation `σ` (`OsSt.F`, `OsSt.cur`, `OsSt.quad`):
the sponge it carries (its five capacity cells, the two scalars waiting), the cursor
`cb·g^co`, the running quadratic. `osFold_sound`: one `opening_fold` call (its meaning,
`MeaningOpeningFold`) squeezes the challenge, folds the quadratic and reads the next one;
`osFolds_sound`: `n` of them run `foldRounds n` (V:1750) on the Spec's state whose quadratic is the
guest's, reading the words at the cursor, the challenges stored at `p·g^off`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The running values through a valuation -/

/-- The capacity cells. -/
def OsSt.fsv (σ : Val) (st : OsSt) : List E := st.fs.map fun i ↦ σ (.n i)

/-- The sponge the guest carries: the capacity and the two waiting scalars. -/
def OsSt.F (σ : Val) (st : OsSt) : Fs :=
  ⟨st.fsv σ, [(σ (.n st.w0), dsObserve), (σ (.n st.w1), dsObserve)]⟩

/-- The cursor: its base value times `g^co`. -/
def OsSt.cur (σ : Val) (st : OsSt) : E := σ (.n st.cb) * gen ^ st.co

/-- The running quadratic. -/
def OsSt.quad (σ : Val) (st : OsSt) : List E := [σ (.n st.c), σ (.n st.b), σ (.n st.a)]

/-! ## One round -/

/-- What one fold round leaves: the challenge squeezed from the carried sponge, the next
quadratic's two words read at the cursor and waiting, the folded claim. -/
structure FoldOut (σ : Val) (st st' : OsSt) (d0 d2 : E) : Prop where
  fs : st'.fs.length = 5
  sponge : st'.F σ = ⟨(st.F σ).squeeze.2.cap, [(d0, dsObserve), (d2, dsObserve)]⟩
  cur : st'.cur σ = st.cur σ * gen ^ 2
  claim : σ (.n st'.t) = polyEval (st.quad σ) (st.F σ).squeeze.1
  quad : st'.quad σ = [d0, σ (.n st'.t) + d2, d2]

theorem fold_args (st : OsSt) (hfs : st.fs.length = 5) :
    ∃ f0 f1 f2 f3 f4, st.fs = [f0, f1, f2, f3, f4] := by
  match h : st.fs, hfs with
  | [f0, f1, f2, f3, f4], _ => exact ⟨f0, f1, f2, f3, f4, rfl⟩

/-- **One `opening_fold` call** (G:1216-1229): the challenge squeezed from the carried sponge,
the claim folded, the next quadratic read at the cursor; the challenge stored at `p·g^off`. -/
theorem osFold_sound (hC : ∀ args rets, C "opening_fold" args rets → MeaningOpeningFold rd args rets)
    {p off : ℕ} {st : OsSt} (hfs : st.fs.length = 5) (hco : st.co < u128Bound)
    (hok : AllOk C rd σ (osFold p off st).1) :
    ∃ d0 d2 : E, ReadsAt rd (st.cur σ) [d0, d2] ∧ FoldOut σ st (osFold p off st).2 d0 d2 ∧
      LoadHolds rd (σ (.n p)) off (st.F σ).squeeze.1 := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fold_args st hfs
  have hF : st.F σ = ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)],
      [(σ (.n st.w0), dsObserve), (σ (.n st.w1), dsObserve)]⟩ := by
    simp [OsSt.F, OsSt.fsv, hf]
  unfold osFold at hok ⊢
  rw [allOk_append] at hok
  obtain ⟨hm, hok⟩ := hok
  have hcv := osMat_val hco hm
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, hf, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, osRun, List.range_succ, List.range_zero,
    Nat.add_zero] at hok
  obtain ⟨hcall, hst, hb⟩ := hok
  obtain ⟨-, d0, d2, hrd, hret⟩ := hC _ _ hcall
  rw [← hF] at hret
  simp only [Fs.squeeze, capOf, List.cons_append, List.nil_append, List.cons.injEq] at hret
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, -⟩ := hret
  rw [hcv] at hrd e5
  have hS1 : (st.F σ).squeeze.1 = σ (.n ((osMat st.cb st.co st.k).2.2 + 9)) := by
    simp only [Fs.squeeze, e9]
  refine ⟨d0, d2, hrd, ⟨by simp, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [OsSt.F, OsSt.fsv, List.map_cons, List.map_nil, Fs.squeeze, capOf, e0, e1, e2, e3,
      e4, e7, e8]
  · simp only [OsSt.cur, pow_zero, mul_one]
    exact e5
  · rw [e6]
    simp only [OsSt.quad, polyEval, List.foldr_cons, List.foldr_nil, Fs.squeeze]
    ring
  · simp only [OsSt.quad]
    rw [hb, e7, e8, e6]
  · rw [hS1]; exact hst

/-! ## Reading words in order -/

/-- Words read from `p`, then from past them. -/
theorem readsAt_append {rd : Reader} {p : E} {xs ys : List E} (h1 : ReadsAt rd p xs)
    (h2 : ReadsAt rd (p * gen ^ xs.length) ys) : ReadsAt rd p (xs ++ ys) := by
  intro k hk
  by_cases h : k < xs.length
  · rw [List.getElem_append_left h]; exact h1 k h
  · rw [List.getElem_append_right (by omega)]
    have := h2 (k - xs.length) (by simp at hk; omega)
    rwa [loadHolds_mul_gen_pow, Nat.add_sub_cancel' (by omega)] at this

/-- The words read from `p`, the first ones. -/
theorem readsAt_left {rd : Reader} {p : E} {xs ys : List E} (h : ReadsAt rd p (xs ++ ys)) :
    ReadsAt rd p xs := fun k hk ↦ by
  have := h k (by simp; omega)
  rwa [List.getElem_append_left hk] at this

/-! ## The Spec's round -/

theorem sumE_single (x : E) : sumE [x] = x := by simp [sumE]

/-- **One round of `foldRounds`** on the carried sponge with the challenge's squeeze, the next
quadratic's two words read. -/
theorem foldRounds_succ_run (F : Fs) (ws : WhirStateT) (lf : List E) (d0 d2 : E) {n : ℕ}
    {xs : List E} {a : WhirStateT × List E} {F' : Fs}
    (h : RunsTo (foldRoundsT n
        { ws with
          target := polyEval ws.quad F.squeeze.1
          quad := [d0, polyEval ws.quad F.squeeze.1 + d2, d2]
          folds := ws.folds ++ [F.squeeze.1] }
        (lf ++ [F.squeeze.1])) ⟨F.squeeze.2.cap, [(d0, dsObserve), (d2, dsObserve)]⟩ xs a F') :
    RunsTo (foldRoundsT (n + 1) ws lf) F (d0 :: d2 :: xs) a F' := by
  have hs := runsTo_sampleE F
  have hr0 := runsTo_readE F.squeeze.2 d0
  have hr1 := runsTo_readN (F.squeeze.2.absorb d0 dsObserve) [d2]
  have hab : (F.squeeze.2.absorb d0 dsObserve).absorbAll [d2] dsObserve =
      ⟨F.squeeze.2.cap, [(d0, dsObserve), (d2, dsObserve)]⟩ := by
    simp [Fs.absorbAll, Fs.absorb, Fs.squeeze, rateScalars]
  rw [hab] at hr1
  have hq : RunsTo (sumcheckRoundPoly 3 (polyEval ws.quad F.squeeze.1) none) F.squeeze.2 [d0, d2]
      [d0, polyEval ws.quad F.squeeze.1 + d2, d2]
      ⟨F.squeeze.2.cap, [(d0, dsObserve), (d2, dsObserve)]⟩ := by
    have := hr0.bind (f := fun c ↦ do
        let tail ← VerifierProgram.readScalars 1
        return c :: (polyEval ws.quad F.squeeze.1 + sumE tail) :: tail)
      (hr1.bind (f := fun tail ↦ (pure (d0 :: (polyEval ws.quad F.squeeze.1 + sumE tail) :: tail) :
        VerifierProgram (List E))) (runsTo_ret _ _))
    simpa [sumcheckRoundPoly, sumE_single] using this
  have := hs.bind (f := fun c ↦ do
      let quad ← sumcheckRoundPoly 3 (polyEval ws.quad c) none
      foldRoundsT n { ws with target := polyEval ws.quad c, quad := quad, folds := ws.folds ++ [c] }
        (lf ++ [c])) (hq.bind (f := fun quad ↦ foldRoundsT n { ws with
          target := polyEval ws.quad F.squeeze.1, quad := quad,
          folds := ws.folds ++ [F.squeeze.1] }
          (lf ++ [F.squeeze.1])) h)
  simpa [foldRoundsT] using this

/-! ## The rounds -/

/-- **The template's `n` rounds run `foldRounds n`** from the Spec's state whose claim and
quadratic are the guest's: the `2n` words at the cursor read, the challenges stored from
`p·g^off`, the Spec's state the guest's after them. -/
theorem osFolds_sound (hC : ∀ args rets, C "opening_fold" args rets → MeaningOpeningFold rd args rets)
    (p : ℕ) : ∀ (n off : ℕ) (st : OsSt) (ws : WhirStateT) (lf : List E), st.fs.length = 5 →
      st.co < u128Bound → ws.quad = st.quad σ → ws.target = σ (.n st.t) →
      AllOk C rd σ (osFolds p off n st).1 →
      ∃ xs chs : List E, xs.length = 2 * n ∧ chs.length = n ∧ ReadsAt rd (st.cur σ) xs ∧
        RunsTo (foldRoundsT n ws lf) (st.F σ) xs
          ({ ws with
              target := σ (.n (osFolds p off n st).2.t)
              quad := (osFolds p off n st).2.quad σ
              folds := ws.folds ++ chs }, lf ++ chs)
          ((osFolds p off n st).2.F σ) ∧
        (osFolds p off n st).2.cur σ = st.cur σ * gen ^ (2 * n) ∧
        (osFolds p off n st).2.fs.length = 5 ∧
        (n = 0 ∨ (osFolds p off n st).2.co = 0) ∧
        ∀ j (hj : j < chs.length), LoadHolds rd (σ (.n p)) (off + j) chs[j]
  | 0, off, st, ws, lf, hfs, _, hq, ht, _ => by
    refine ⟨[], [], rfl, rfl, readsAt_nil _ _, ?_, by simp [osFolds], hfs, Or.inl rfl,
      fun j hj ↦ by simp at hj⟩
    have hr : RunsTo (foldRoundsT 0 ws lf) (st.F σ) [] (ws, lf) (st.F σ) := runsTo_ret _ _
    refine RunsTo.of_eq hr rfl rfl ?_ rfl
    obtain ⟨t, q, f, g⟩ := ws
    simp only at ht hq
    simp [ht, hq, osFolds]
  | n + 1, off, st, ws, lf, hfs, hco, hq, ht, hok => by
    simp only [osFolds] at hok ⊢
    rw [allOk_append] at hok
    obtain ⟨d0, d2, hrd, ho, hst⟩ := osFold_sound hC hfs hco hok.1
    set st1 := (osFold p off st).2
    have hco1 : st1.co < u128Bound := by simp [st1, osFold, u128Bound]
    obtain ⟨xs, chs, hxl, hcl, hrds, hrun, hcur, hfs', hco', hld⟩ := osFolds_sound hC p n (off + 1)
      st1
        { ws with
          target := polyEval ws.quad (st.F σ).squeeze.1
          quad := [d0, polyEval ws.quad (st.F σ).squeeze.1 + d2, d2]
          folds := ws.folds ++ [(st.F σ).squeeze.1] }
        (lf ++ [(st.F σ).squeeze.1]) ho.fs hco1
      (by rw [ho.quad, ho.claim, hq]) (by rw [ho.claim, hq]) hok.2
    refine ⟨d0 :: d2 :: xs, (st.F σ).squeeze.1 :: chs, by simp [hxl]; ring, by simp [hcl], ?_, ?_,
      ?_, hfs', Or.inr ?_, ?_⟩
    · have := readsAt_append hrd (ys := xs)
        (by rw [show [d0, d2].length = 2 from rfl, ← ho.cur]; exact hrds)
      simpa using this
    · have hr := foldRounds_succ_run (st.F σ) ws lf d0 d2 (n := n) (by rw [← ho.sponge]; exact hrun)
      refine RunsTo.of_eq hr rfl rfl ?_ rfl
      simp only [List.append_assoc, List.singleton_append]
    · rw [hcur, ho.cur, mul_assoc, ← pow_add]; ring_nf
    · rcases hco' with h | h
      · subst h; simp [st1, osFolds, osFold]
      · exact h
    · intro j hj
      rcases j with _ | j
      · simpa using hst
      · have := hld j (by simpa using hj)
        rw [show off + 1 + j = off + (j + 1) by ring] at this
        simpa using this

end
end LeanVM.Guest.B1.Whir
