module

public import LeanVM.Guest.Complete.AggFree
public import LeanVM.Guest.Complete.Agg.Loop0
public import LeanVM.Guest.Complete.Agg.Loop1
public import LeanVM.Guest.Complete.Agg.Loop2
public import LeanVM.Guest.Complete.Agg.Loop3
public import LeanVM.Guest.B1.Sumcheck.Batch

/-!
# `aggregate_claims`' loops complete

A loop free of witness hints whose block holds at every counter below `m` completes from its guard's
call `[1, g^m, …]` (`loop_callCompletes`, from `loopF_complete` and `callCompletes_free`), popping
nothing, every node exact. `agg_loop{0,1,2,3}_completes`: `aggregate_claims`' four loops, on
memories where each child's words of its block (`a{0,1,2,3}_block`) hold. `agg_bs_completes`: the
batching sumcheck completes where its meaning holds (`batch_sumcheck_holds`).
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.Da

@[expose] public section

/-- **A free loop completes from its guard's call** when its block holds at every counter. -/
theorem loop_callCompletes (hwf : coreProgram.Wf) {k : ℕ} {f : String} {j : ℕ}
    (hidx : coreProgram.indexOf? f = some j) (hok : loopShapeF (coreProgram.getD j default) f = true)
    (hfree : NoWitG f ∧ ExactFreeG f) {rest : List E} {m : ℕ} (hm : 0 < m) {Pre : Reader → Prop}
    (hblk : ∀ rd, Pre rd → ∀ i < m, LoopBlock rd (coreProgram.getD j default) (gen ^ i) (gen ^ m) rest) :
    CallCompletes k f (1 :: gen ^ m :: rest) [] Pre FreePost :=
  callCompletes_free hwf hfree.1 hfree.2 fun rd _ hp => by
    have := loopF_complete (rd := rd) (find_of_idx hidx) hok rfl (hblk rd hp) 0 hm
    rwa [pow_zero] at this

/-- `aggregate_claims_loop0`'s words: at child `c`, its row holds the sponge `st c` and the next
row the sponge after the child's words, the pointer tables the child's claims, and the child's
words are in memory. -/
def A0Pre (m : ℕ) (st : ℕ → Fs) (absorb cfresh lfT ccarried lcT cpi : E) (rd : Reader) : Prop :=
  ∀ c < m, ReadsAt rd (absorb * (gen ^ c) ^ 13) (rowW (st c)) ∧
    ReadsAt rd (absorb * (gen ^ c) ^ 13 * gen ^ 13)
      (rowW ((st c).absorbAll (l25Words rd cpi cfresh ccarried (gen ^ c)) dsObserve)) ∧
    LoadHolds rd (lfT * gen ^ c) 0 (cfresh * (gen ^ c) ^ 55) ∧
    LoadHolds rd (lcT * gen ^ c) 0 (ccarried * (gen ^ c) ^ 26) ∧
    (∀ o < 2, ∃ v, LoadHolds rd (cpi * (gen ^ c) ^ 2) o v) ∧
    (∀ o < 55, ∃ v, LoadHolds rd (cfresh * (gen ^ c) ^ 55) o v) ∧
    ∀ o < 26, ∃ v, LoadHolds rd (ccarried * (gen ^ c) ^ 26) o v

/-- **`aggregate_claims_loop0` completes**, each row's sponge with four waiting scalars. -/
theorem agg_loop0_completes (hwf : coreProgram.Wf) (k : ℕ) {m : ℕ} (hm : 0 < m) (st : ℕ → Fs)
    (hst : ∀ c < m, StOk (st c) ∧ (st c).pend.length = 4) (absorb cfresh lfT ccarried lcT cpi : E) :
    CallCompletes k name% «aggregate_claims_loop0» (1 :: gen ^ m :: [absorb, cfresh, lfT, ccarried, lcT, cpi])
      [] (A0Pre m st absorb cfresh lfT ccarried lcT cpi) FreePost :=
  loop_callCompletes hwf l25_idx a0_shape.1 agg_loop0_free hm fun _ hp c hc =>
    have h := hp c hc
    a0_block (hst c hc).1 (hst c hc).2 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
      h.2.2.2.2.2.2

/-- `aggregate_claims_loop1`'s words: at child `c`, the fresh claim's pointer, `eq_col`'s and the
claim's values, and the folded value. -/
def A1Pre (m : ℕ) (lfT eqc fvT : E) (rd : Reader) : Prop :=
  ∀ c < m, ∃ pf, LoadHolds rd (lfT * gen ^ c) 0 pf ∧ (∀ j < 36, ∃ v, LoadHolds rd eqc j v) ∧
    (∀ j < 36, ∃ v, LoadHolds rd pf (19 + j) v) ∧ LoadHolds rd (fvT * gen ^ c) 0 (fvAcc rd eqc pf 36)

/-- **`aggregate_claims_loop1` completes.** -/
theorem agg_loop1_completes (hwf : coreProgram.Wf) (k : ℕ) {m : ℕ} (hm : 0 < m) (lfT eqc fvT : E) :
    CallCompletes k name% «aggregate_claims_loop1» (1 :: gen ^ m :: [lfT, eqc, fvT]) []
      (A1Pre m lfT eqc fvT) FreePost :=
  loop_callCompletes hwf a1_idx a1_shape.1 agg_loop1_free hm fun _ hp c hc =>
    have ⟨_, h1, h2, h3, h4⟩ := hp c hc
    a1_block h1 h2 h3 h4

/-- `aggregate_claims_loop2`'s words: at child `c`, its record and the next, the claims' pointers,
the folded value and the carried claim's value. -/
def A2Pre (m : ℕ) (chainT lfT lcT lamSq fvT lam : E) (rd : Reader) : Prop :=
  ∀ c < m, ∃ pf pc fv cv pw acc : E, ReadsAt rd (chainT * (gen ^ c) ^ 2) [pw, acc] ∧
    ReadsAt rd (chainT * (gen ^ c) ^ 2 * gen ^ 2) [pw * lamSq, acc + pw * (fv + lam * cv)] ∧
    LoadHolds rd (lfT * gen ^ c) 0 pf ∧ LoadHolds rd (lcT * gen ^ c) 0 pc ∧
    LoadHolds rd (fvT * gen ^ c) 0 fv ∧ LoadHolds rd pc 25 cv

/-- **`aggregate_claims_loop2` completes.** -/
theorem agg_loop2_completes (hwf : coreProgram.Wf) (k : ℕ) {m : ℕ} (hm : 0 < m)
    (chainT lfT lcT lamSq fvT lam : E) :
    CallCompletes k name% «aggregate_claims_loop2» (1 :: gen ^ m :: [chainT, lfT, lcT, lamSq, fvT, lam])
      [] (A2Pre m chainT lfT lcT lamSq fvT lam) FreePost :=
  loop_callCompletes hwf a2_idx a2_shape.1 agg_loop2_free hm fun _ hp c hc =>
    have ⟨_, _, _, _, _, _, h1, h2, h3, h4, h5, h6⟩ := hp c hc
    a2_block h1 h2 h3 h4 h5 h6

/-- `aggregate_claims_loop3`'s words: at child `c`, the claims' pointers and points, `bc_point1`,
the child's power of `λ`, its weight and the next. -/
def A3Pre (m : ℕ) (lfT lcT pt1 chainT wT eqc lam : E) (rd : Reader) : Prop :=
  ∀ c < m, ∃ pf pc pw w0 : E, LoadHolds rd (lfT * gen ^ c) 0 pf ∧ LoadHolds rd (lcT * gen ^ c) 0 pc ∧
    (∀ j < 19, ∃ v, LoadHolds rd pf j v) ∧ (∀ j < 25, ∃ v, LoadHolds rd pc j v) ∧
    (∀ j < 25, ∃ v, LoadHolds rd pt1 j v) ∧
    LoadHolds rd (chainT * (gen ^ c) ^ 2) 0 pw ∧ LoadHolds rd (wT * gen ^ c) 0 w0 ∧
    LoadHolds rd (wT * gen ^ c) 1 (w0 + pw *
      (eqEval (memRun rd pf 19) ((memRun rd pt1 19).map (1 + ·)) * eqc +
        lam * eqEval (memRun rd pc 25) ((memRun rd pt1 25).map (1 + ·))))

/-- **`aggregate_claims_loop3` completes.** -/
theorem agg_loop3_completes (hwf : coreProgram.Wf) (k : ℕ) {m : ℕ} (hm : 0 < m)
    (lfT lcT pt1 chainT wT eqc lam : E) :
    CallCompletes k name% «aggregate_claims_loop3» (1 :: gen ^ m :: [lfT, lcT, pt1, chainT, wT, eqc, lam])
      [] (A3Pre m lfT lcT pt1 chainT wT eqc lam) FreePost :=
  loop_callCompletes hwf a3_idx a3_shape.1 agg_loop3_free hm fun _ hp c hc =>
    have ⟨_, _, _, _, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp c hc
    a3_block h1 h2 h3 h4 h5 h6 h7 h8

/-- **The batching sumcheck completes** where its meaning holds. -/
theorem agg_bs_completes (hwf : coreProgram.Wf) (k : ℕ) (args rets : List E) :
    CallCompletes k "batch_sumcheck__L25" args rets
      (fun rd => MeaningBatchSumcheck 25 rd args rets) FreePost :=
  callCompletes_free hwf agg_bs_free.1 agg_bs_free.2 fun rd _ hp =>
    (batch_sumcheck_holds rd args rets).mpr hp

end
end LeanVM.Guest.Complete.Agg
