module

public import LeanVM.Guest.Complete.Agg.W2
public import LeanVM.Guest.Complete.Agg.W46
public import LeanVM.Guest.Complete.Agg.Calls
public import LeanVM.Guest.Complete.Agg.SumcheckR
public import LeanVM.Guest.Complete.Agg.Wrap
public import LeanVM.Guest.Memory.GuestWf
public import LeanVM.Guest.Complete.EndBound

/-!
# `aggregate_claims`' windows composed

At the honest data (`aRd0`, `aOrc`, `aWo`), `aggregate_claims`' eleven windows compose: the runs by
`runHypT_w{0,2,4,6,8,10}`, the guarded loops by `winsHypT_cif_of_atEvery` from
`agg_loop{0,1,2,3}_atEvery`, the sumcheck by `winsHypT_call_of_atEvery` from `agg_bs_atEvery`. What
is left is `AggLeftAt`: each callee's precondition on the memories with `main`'s words and the own
words, each callee's region in `main`'s or the own data, and the final condition (the node's pops
and exactness). `aggWinHyp_of_left`: `AggWinHyp` from it; `agg_fieldB_of_left`: `AggFieldHypB` from
it on every inner node.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete LeanVM.Guest.B1.Digest
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The memories the callees run on: `main`'s and the own words. -/
def APre (al : String → Bool) (s : NodeStatement) (w : NodeWitness) (cover : List E) (c : ℕ) (rd : Reader) : Prop :=
  MainPreA al s w cover rd ∧ HoldsWords rd (aWo s w c)

/-- The own data and `main`'s region. -/
def AReg (al : String → Bool) (s : NodeStatement) (w : NodeWitness) (cover : List E) (c fp : ℕ) (i : ℕ) : Prop :=
  mainR al (mainCounts s w) i ∨
    ownData B2C.cert fp c "aggregate_claims" (aBufs w.children.length) (aEs (aV al s w cover c)) i

/-- **What is left of `aggregate_claims` at the node `(s, w)`, frame `fp` and cursor `c`**: the
loops' and the sumcheck's preconditions on `APre`, their regions in `AReg`, and the final condition. -/
structure AggLeftAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) (cover : List E)
    (fp c : ℕ) : Prop where
  pre0 : ∀ rd, APre al s w cover c rd → ∀ j < w.children.length,
    A0PreA (absSt w.children.length (aCs w)) (aB c w.children.length 3) (mBase (mainCounts s w) 5 + 0)
      (mBase (mainCounts s w) 6 + 0) (aB c w.children.length 1) (mBase (mainCounts s w) 7 + 0)
      (aB c w.children.length 2) rd j
  reg0 : ∀ j < w.children.length, ∀ i, A0Reg (aB c w.children.length 3) (mBase (mainCounts s w) 5 + 0)
    (mBase (mainCounts s w) 6 + 0) (aB c w.children.length 1) (mBase (mainCounts s w) 7 + 0)
    (aB c w.children.length 2) j i → AReg al s w cover c fp i
  pre1 : ∀ rd, APre al s w cover c rd → ∀ j < w.children.length,
    LoadHolds rd (ptrAt (aB c w.children.length 1) * gen ^ j) 0 (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) ∧
      (∀ i < 36, ∃ v, LoadHolds rd (ptrAt (aB c w.children.length 5 + 62)) i v) ∧
      (∀ i < 36, ∃ v, LoadHolds rd (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) (19 + i) v) ∧
      LoadHolds rd (ptrAt (aB c w.children.length 6) * gen ^ j) 0
        (fvAcc rd (ptrAt (aB c w.children.length 5 + 62)) (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) 36)
  reg1 : ∀ j < w.children.length, ∀ i, A1Reg (aB c w.children.length 1) (aB c w.children.length 5 + 62)
    (mBase (mainCounts s w) 6 + 55 * j) (aB c w.children.length 6) j i → AReg al s w cover c fp i
  pre2 : ∀ rd, APre al s w cover c rd → ∀ j < w.children.length, ∃ pf fv cv pw acc : E,
    ReadsAt rd (ptrAt (aB c w.children.length 7) * (gen ^ j) ^ 2) [pw, acc] ∧
    ReadsAt rd (ptrAt (aB c w.children.length 7) * (gen ^ j) ^ 2 * gen ^ 2)
      [pw * aV al s w cover c (.n 155), acc + pw * (fv + aV al s w cover c (.n 78) * cv)] ∧
    LoadHolds rd (ptrAt (aB c w.children.length 1) * gen ^ j) 0 pf ∧
    LoadHolds rd (ptrAt (aB c w.children.length 2) * gen ^ j) 0 (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) ∧
    LoadHolds rd (ptrAt (aB c w.children.length 6) * gen ^ j) 0 fv ∧
    LoadHolds rd (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) 25 cv
  reg2 : ∀ j < w.children.length, ∀ i, A2Reg (aB c w.children.length 7) (aB c w.children.length 1)
    (aB c w.children.length 2) (aB c w.children.length 6) (mBase (mainCounts s w) 7 + 26 * j) j i →
    AReg al s w cover c fp i
  bs : ∀ rd, APre al s w cover c rd →
    MeaningBatchSumcheck 25 rd ([V.n 230, .n 231, .n 232, .n 233, .n 234, .n 460, .n 457, .n 458, .n 5].map
      (aV al s w cover c)) ([V.n 461, .n 462, .n 463, .n 464, .n 465, .n 466].map (aV al s w cover c))
  regbs : ∀ i, bsReg (aB c w.children.length 0 + 1) (aB c w.children.length 8) i → AReg al s w cover c fp i
  pre3 : ∀ rd, APre al s w cover c rd → ∀ j < w.children.length, ∃ pw w0 : E,
    LoadHolds rd (ptrAt (aB c w.children.length 1) * gen ^ j) 0 (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) ∧
    LoadHolds rd (ptrAt (aB c w.children.length 2) * gen ^ j) 0 (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) ∧
    (∀ i < 19, ∃ v, LoadHolds rd (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) i v) ∧
    (∀ i < 25, ∃ v, LoadHolds rd (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) i v) ∧
    (∀ i < 25, ∃ v, LoadHolds rd (ptrAt (aB c w.children.length 9)) i v) ∧
    LoadHolds rd (ptrAt (aB c w.children.length 7) * (gen ^ j) ^ 2) 0 pw ∧
    LoadHolds rd (ptrAt (aB c w.children.length 10) * gen ^ j) 0 w0 ∧
    LoadHolds rd (ptrAt (aB c w.children.length 10) * gen ^ j) 1 (w0 + pw *
      (eqEval (memRun rd (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) 19)
        ((memRun rd (ptrAt (aB c w.children.length 9)) 19).map (1 + ·)) * aV al s w cover c (.n 565) +
        aV al s w cover c (.n 78) * eqEval (memRun rd (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) 25)
          ((memRun rd (ptrAt (aB c w.children.length 9)) 25).map (1 + ·))))
  reg3 : ∀ j < w.children.length, ∀ i, A3Reg (aB c w.children.length 1) (aB c w.children.length 2)
    (aB c w.children.length 10) (aB c w.children.length 7) (mBase (mainCounts s w) 6 + 55 * j)
    (mBase (mainCounts s w) 7 + 26 * j) (aB c w.children.length 9) j i → AReg al s w cover c fp i
  post : ∀ st : St, (∀ rd, st.O rd → HoldsWords rd (aWo s w c)) →
    st.Qs = [FreePost, FreePost, FreePost, FreePost, FreePost] →
    AggK k (MainPreA al s w cover) (PopsPost (Prover.batchPushes w.batchingHints)) (aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w))) st

theorem runHypT_of_eq {k : ℕ} {σ0 : Val} {o : ℕ → E} {a : ℕ} {Own R D : ℕ → Prop} {Pre O : Reader → Prop}
    {as as' : List Atom} (h : as = as') (h' : RunHypT k σ0 o a Own R D Pre O as') :
    RunHypT k σ0 o a Own R D Pre O as := h ▸ h'

theorem aB_eqs (c m : ℕ) : aB c m 4 = c + 51 + m + m + 13 * (m + 1) ∧ aB c m 7 = aB c m 4 + 6 + 126 + m ∧
    aB c m 8 = aB c m 7 + 2 * (m + 1) ∧ aB c m 9 = aB c m 8 + 25 := by
  have h := fun j (hj : j + 1 < 11) => aB_succ c m j hj
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  have h5 := h 5 (by norm_num)
  have h6 := h 6 (by norm_num)
  have h7 := h 7 (by norm_num)
  have h8 := h 8 (by norm_num)
  have b0 : aB c m 0 = c := rfl
  simp only [aBufs, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceAdd, Nat.zero_add] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}

set_option linter.all false in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **`aggregate_claims`' windows' hypotheses from what is left**, at the honest data. -/
theorem aggWinHyp_of_left (hk : 11 ≤ k) (hr : NodeRelation guestBytecode guestSeed s w) (hd : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w) (hne : w.children ≠ [])
    (hcv : cover.length = (mainCounts s w).sx + (mainCounts s w).ss) {fp c : ℕ}
    (hlo : mLo al (mainCounts s w) ≤ fp) (hfc : fp + B2C.fs "aggregate_claims" ≤ c) (hc : c < 2 ^ 62)
    (H : AggLeftAt al k s w cover fp c) :
    AggWinHyp al k (aggArgs al (mainCounts s w)) (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost (Prover.batchPushes w.batchingHints)) fp c := by
  have hn : w.children.length ≤ 16 := hd.atMostSixteenChildren
  have hm0 : w.children.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
  have hm34 : w.children.length < 2 ^ 34 := by omega
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  have cc := claimCells_of hr hok
  have hmw := mainLists_length hcv cc.fresh cc.carried cc.own
  have hloc : mLo al (mainCounts s w) ≤ c := by omega
  have hA : allocs (aV al s w cover c) (aEs (aV al s w cover c)) = aBufs w.children.length :=
    aAllocs (aggArgs_length _ _) hm34 rfl
  obtain ⟨e4, e7, e8, e9⟩ := aB_eqs c w.children.length
  have v0 : aV al s w cover c (.n 0) = gen ^ w.children.length := aV_param (by norm_num)
  obtain ⟨p6, p8, p9, p30, -, p235, p440, p449, p458, p467, p568⟩ :=
    aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  obtain ⟨v29', v448', -⟩ := aVal_sizes (rd0 := aRd0 al s w cover c) (o := aOrc w c)
    (aggArgs_length al (mainCounts s w)) (m := w.children.length) rfl
  have v29 : aV al s w cover c (.n 29) = gen ^ (13 * (w.children.length + 1)) := v29'
  have v448 : aV al s w cover c (.n 448) = gen ^ (2 * (w.children.length + 1)) := v448'
  have one : ∀ {d : ℕ}, Atom.const (.n d) (word 1 0) ∈ atomsOf aggP → aV al s w cover c (.n d) = gen ^ 0 :=
    fun h => by rw [show aV al s w cover c _ = _ from aGood_const (aggArgs_length _ _) h, word_one, pow_zero]
  have guard : ∀ {d x : ℕ}, Atom.const (.n x) (word 1 0) ∈ atomsOf aggP → Atom.add (.n d) (.n x) (.n 0) ∈ atomsOf aggP →
      aV al s w cover c (.n d) = word 1 0 + gen ^ w.children.length := fun hx ha => by
    rw [show aV al s w cover c (.n _) = aV al s w cover c (.n _) + aV al s w cover c (.n 0) from aV_good ha,
      show aV al s w cover c _ = _ from aGood_const (aggArgs_length _ _) hx, v0]
  have pa : ∀ i < 6, aV al s w cover c (.n i) = (aggArgs al (mainCounts s w)).getD i 0 := fun i hi => aV_param hi
  -- the runs' sizes
  have s0 : (allocs (aV al s w cover c) ((atomsOf ((aggP.drop 0).take 42)).map Memory.Ev.atom)).sum =
      51 + w.children.length + w.children.length + 13 * (w.children.length + 1) := by
    rw [allocs_mapAtom, aW_allocK.1]
    simp only [List.map_cons, List.map_nil, allocSz, v0, v29]
    rw [logG_gen_pow (by omega), logG_gen_pow (by omega)]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have s2 : (allocs (aV al s w cover c) ((atomsOf ((aggP.drop 43).take 433)).map Memory.Ev.atom)).sum =
      6 + 126 + w.children.length := by
    rw [allocs_mapAtom, aW_allocK.2.1]
    simp only [List.map_cons, List.map_nil, allocSz, v0]
    rw [logG_gen_pow (by omega)]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have s4 : (allocs (aV al s w cover c) ((atomsOf ((aggP.drop 477).take 11)).map Memory.Ev.atom)).sum =
      2 * (w.children.length + 1) := by
    rw [allocs_mapAtom, aW_allocK.2.2.1]
    simp only [List.map_cons, List.map_nil, allocSz, v448]
    rw [logG_gen_pow (by omega)]
    simp
  have s6 : (allocs (aV al s w cover c) ((atomsOf ((aggP.drop 489).take 6)).map Memory.Ev.atom)).sum = 25 := by
    rw [allocs_mapAtom, aW_allocK.2.2.2.1]
    simp [allocSz]
  -- the calls' arguments
  have a1 : ([.n 33, .n 0, .n 30, .n 2, .n 8, .n 3, .n 9, .n 1] : List V).map (aV al s w cover c) =
      gen ^ 0 :: gen ^ w.children.length :: [ptrAt (aB c w.children.length 3), ptrAt (mBase (mainCounts s w) 6 + 0),
        ptrAt (aB c w.children.length 1), ptrAt (mBase (mainCounts s w) 7 + 0), ptrAt (aB c w.children.length 2),
        ptrAt (mBase (mainCounts s w) 5 + 0)] := by
    simp only [List.map_cons, List.map_nil]
    rw [one (d := 33) (w0_mem _ (by simp [w0A])), v0, p30, p8, p9, pa 2 (by norm_num), pa 3 (by norm_num), pa 1 (by norm_num)]
    rfl
  have v444 : aV al s w cover c (.n 444) = gen ^ 62 :=
    (show aV al s w cover c _ = _ from aGood_const (aggArgs_length _ _) (mem_tail (by simp [w2Tail]))).trans word_g62
  have v445 : aV al s w cover c (.n 445) = ptrAt (aB c w.children.length 5 + 62) := by
    rw [show aV al s w cover c (.n 445) = aV al s w cover c (.n 235) * aV al s w cover c (.n 444) from
      aGood_mul (aggArgs_length _ _) (mem_tail (by simp [w2Tail])) (by norm_num) (by norm_num), p235, v444,
      ptrAt_mul_gen_pow]
  have a3 : ([.n 443, .n 0, .n 8, .n 445, .n 440] : List V).map (aV al s w cover c) =
      gen ^ 0 :: gen ^ w.children.length :: [ptrAt (aB c w.children.length 1), ptrAt (aB c w.children.length 5 + 62),
        ptrAt (aB c w.children.length 6)] := by
    simp only [List.map_cons, List.map_nil]
    rw [one (d := 443) (mem_tail (by simp [w2Tail])), v0, p8, v445, p440]
  have a5 : ([.n 454, .n 0, .n 449, .n 8, .n 9, .n 155, .n 440, .n 78] : List V).map (aV al s w cover c) =
      gen ^ 0 :: gen ^ w.children.length :: [ptrAt (aB c w.children.length 7), ptrAt (aB c w.children.length 1),
        ptrAt (aB c w.children.length 2), aV al s w cover c (.n 155), ptrAt (aB c w.children.length 6),
        aV al s w cover c (.n 78)] := by
    simp only [List.map_cons, List.map_nil]
    rw [one (d := 454) (w46_mem.1 _ (by simp [w4A])), v0, p449, p8, p9, p440]
  have a9 : ([.n 572, .n 0, .n 8, .n 9, .n 467, .n 449, .n 568, .n 565, .n 78] : List V).map (aV al s w cover c) =
      gen ^ 0 :: gen ^ w.children.length :: [ptrAt (aB c w.children.length 1), ptrAt (aB c w.children.length 2),
        ptrAt (aB c w.children.length 9), ptrAt (aB c w.children.length 7), ptrAt (aB c w.children.length 10),
        aV al s w cover c (.n 565), aV al s w cover c (.n 78)] := by
    simp only [List.map_cons, List.map_nil]
    rw [one (d := 572) (w8_mem _ (by simp [w8A, w8T])), v0, p8, p9, p467, p449, p568]
  have v460 : aV al s w cover c (.n 460) = ptrAt (aB c w.children.length 0 + 1) := by
    rw [show aV al s w cover c (.n 460) = aV al s w cover c (.n 6) * aV al s w cover c (.n 459) from
      aGood_mul (aggArgs_length _ _) (w46_mem.2.1 _ (by simp [w6A])) (by norm_num) (by norm_num), p6,
      show aV al s w cover c (.n 459) = word 2 0 from aGood_const (aggArgs_length _ _) (w46_mem.2.1 _ (by simp [w6A])),
      word_gen, ← pow_one gen, ptrAt_mul_gen_pow]
  have g5 : (([V.n 230, .n 231, .n 232, .n 233, .n 234, .n 460, .n 457, .n 458, .n 5] : List V).map
      (aV al s w cover c)).getD 5 0 = ptrAt (aB c w.children.length 0 + 1) := by
    simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero]; exact v460
  have g7 : (([V.n 230, .n 231, .n 232, .n 233, .n 234, .n 460, .n 457, .n 458, .n 5] : List V).map
      (aV al s w cover c)).getD 7 0 = ptrAt (aB c w.children.length 8) := by
    simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero]; exact p458
  have glen : (([V.n 230, .n 231, .n 232, .n 233, .n 234, .n 460, .n 457, .n 458, .n 5] : List V).map
      (aV al s w cover c)).length = 9 := by simp
  have hbs := agg_bs_atEveryB (al := al) (k := k) (Pre := APre al s w cover c) (T := 2 ^ 61) (β := 0) coreProgram_wf
    glen g5 g7 H.bs
  have hB : ∀ f, lpBlk B2C.fs f w.children.length + 0 ≤ 2 ^ 51 := fun f => by
    have := lpBlk_le16 f w.children.length
    have : w.children.length * 2 ^ 16 ≤ 16 * 2 ^ 16 := Nat.mul_le_mul_right _ hn
    omega
  have hB' : ∀ f, lpBlk B2C.fs f w.children.length ≤ 2 ^ 21 := fun f => by
    have := lpBlk_le16 f w.children.length
    have : w.children.length * 2 ^ 16 ≤ 16 * 2 ^ 16 := Nat.mul_le_mul_right _ hn
    omega
  have hk0 : (aSt0 (aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w))) (aWo s w c) c).kc =
      c + (aBufs w.children.length).sum := by
    show c + (allocs (aV al s w cover c) (aEs (aV al s w cover c))).sum = _
    rw [hA]
  have hsum : (aBufs w.children.length).sum ≤ 2 ^ 10 := by simp only [aBufs, List.sum_cons, List.sum_nil]; omega
  refine ⟨aRd0 al s w cover c, aOrc w c, aWo s w c, ?_, ?_⟩
  · show WordsInA (aWo s w c) (fp + 2) (fp + B2C.fs "aggregate_claims") c
      (c + (allocs (aV al s w cover c) (aEs (aV al s w cover c))).sum)
    rw [hA]; exact aWo_in hl _ _ _
  have s0' : (allocs (aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w))) ((atomsOf ((aggP.drop 0).take 42)).map Memory.Ev.atom)).sum =
      51 + w.children.length + w.children.length + 13 * (w.children.length + 1) := s0
  have s2' : (allocs (aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w))) ((atomsOf ((aggP.drop 43).take 433)).map Memory.Ev.atom)).sum =
      6 + 126 + w.children.length := s2
  have s4' : (allocs (aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w))) ((atomsOf ((aggP.drop 477).take 11)).map Memory.Ev.atom)).sum =
      2 * (w.children.length + 1) := s4
  have s6' : (allocs (aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w))) ((atomsOf ((aggP.drop 489).take 6)).map Memory.Ev.atom)).sum = 25 := s6
  have hA0 : allocs (aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w)))
      (aEs (aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w)))) = aBufs w.children.length := hA
  rw [hA0]
  unfold wAgg
  -- aW0
  refine ⟨?_, ?_⟩
  · exact runHypT_of_eq w0_eq (runHypT_w0 hr hne hn rfl (fun _ h => h))
  -- aW1: aggregate_claims_loop0
  refine winsHypT_cif_of_atEveryE (n := w.children.length) hm34
    (guard (d := 32) (x := 31) (w0_mem _ (by simp [w0A])) (w0_mem _ (by simp [w0A]))) a1
    (by simp only [List.length_cons, List.length_nil, Nat.reduceAdd]; decide +kernel)
    (fun _ => agg_loop0_atEvery (Pre := APre al s w cover c) (T := 2 ^ 61) (β := 0) hm34 hm0 H.pre0 H.reg0)
    (by norm_num) (hB _) (Nat.zero_le _)
    (fun i h => Or.inl h) (fun rd h => h) (fun _ k1 hk1 => ?_) (fun h0 => absurd h0 hm0)
  -- aW2
  refine ⟨?_, ?_⟩
  · exact runHypT_of_eq w2_eq (runHypT_w2 hr hne hc hn hloc hmw hk (by show c + _ = _; rw [s0', e4]; omega) (fun _ h => h.1))
  -- aW3: aggregate_claims_loop1
  refine winsHypT_cif_of_atEveryE (n := w.children.length) hm34
    (guard (d := 442) (x := 441) (mem_tail (by simp [w2Tail])) (mem_tail (by simp [w2Tail]))) a3
    (by simp only [List.length_cons, List.length_nil, Nat.reduceAdd]; decide +kernel)
    (fun _ => agg_loop1_atEvery (Pre := APre al s w cover c) (T := 2 ^ 61) (β := 0)
      (qs := fun j => mBase (mainCounts s w) 6 + 55 * j) hm34 hm0 H.pre1 H.reg1) (by norm_num) (hB _) (Nat.zero_le _)
    (fun i h => Or.inl h) (fun rd h => ⟨h.1, h.2.1⟩) (fun _ k3 hk3 => ?_) (fun h0 => absurd h0 hm0)
  -- aW4
  refine ⟨?_, ?_⟩
  · exact runHypT_of_eq w46_eq.1 (runHypT_w4 hr hne hn (by show c + _ + _ = _; rw [s0', s2', e7, e4]; omega) (fun _ h => h.1.1))
  -- aW5: aggregate_claims_loop2
  refine winsHypT_cif_of_atEveryE (n := w.children.length) hm34
    (guard (d := 453) (x := 452) (w46_mem.1 _ (by simp [w4A])) (w46_mem.1 _ (by simp [w4A]))) a5
    (by simp only [List.length_cons, List.length_nil, Nat.reduceAdd]; decide +kernel)
    (fun _ => agg_loop2_atEvery (Pre := APre al s w cover c) (T := 2 ^ 61) (β := 0)
      (ipc := fun j => mBase (mainCounts s w) 7 + 26 * j) hm34 hm0 H.pre2 H.reg2) (by norm_num) (hB _) (Nat.zero_le _)
    (fun i h => Or.inl h) (fun rd h => ⟨h.1, h.2.1.1⟩) (fun _ k5 hk5 => ?_) (fun h0 => absurd h0 hm0)
  -- aW6
  refine ⟨?_, ?_⟩
  · exact runHypT_of_eq w46_eq.2 (runHypT_w6 hr hne hc hn (by show c + _ + _ + _ = _; rw [s0', s2', s4', e8, e7, e4]; omega)
        (fun _ h => h.1.1.1))
  -- aW7: batch_sumcheck__L25
  refine winsHypT_call_of_atEveryE rfl rfl rfl hbs (by norm_num)
    (by have := fs_lt16 "batch_sumcheck__L25"; omega) (Nat.zero_le _) (fun i h => Or.inl (H.regbs i h))
    (fun rd h => ⟨h.1, h.2.1.1.1⟩) (fun k7 hk7 => ?_)
  -- aW8
  refine ⟨?_, ?_⟩
  · exact runHypT_of_eq w8_eq (runHypT_w8 hr hne hc hn (by show c + _ + _ + _ + _ = _; rw [s0', s2', s4', s6', e9, e8, e7, e4]; omega)
        (fun _ h => h.1.1.1.1))
  -- aW9: aggregate_claims_loop3
  refine winsHypT_cif_of_atEveryE (n := w.children.length) hm34
    (guard (d := 571) (x := 570) (w8_mem _ (by simp [w8A, w8T])) (w8_mem _ (by simp [w8A, w8T]))) a9
    (by simp only [List.length_cons, List.length_nil, Nat.reduceAdd]; decide +kernel)
    (fun _ => agg_loop3_atEvery (Pre := APre al s w cover c) (T := 2 ^ 61) (β := 0)
      (ipf := fun j => mBase (mainCounts s w) 6 + 55 * j)
      (ipc := fun j => mBase (mainCounts s w) 7 + 26 * j) hm34 hm0 H.pre3 H.reg3) (by norm_num) (hB _) (Nat.zero_le _)
    (fun i h => Or.inl h) (fun rd h => ⟨h.1, h.2.1.1.1.1⟩) (fun _ k9 hk9 => ?_) (fun h0 => absurd h0 hm0)
  -- aW10 and the final condition
  refine ⟨?_, ?_⟩
  · exact runHypT_of_eq w10_eq (runHypT_w10 hr hne (fresh_len hok) hc hn (fun _ h => h.1.1.1.1.1))
  refine ⟨fun hc60 => ?_, H.post _ (fun _ h => h.1.1.1.1.1) rfl⟩
  dsimp only at hk1 hk3 hk5 hk7 hk9 ⊢
  rw [hk0] at hk1
  have b0 := allocBase_le (al name% «aggregate_claims_loop0») (c + (aBufs w.children.length).sum)
  have b1 := allocBase_le (al name% «aggregate_claims_loop1») k1
  have b2 := allocBase_le (al name% «aggregate_claims_loop2») k3
  have b3 := allocBase_le (al "batch_sumcheck__L25") k5
  have b4 := allocBase_le (al name% «aggregate_claims_loop3») k7
  have l0 := hB' name% «aggregate_claims_loop0»
  have l1 := hB' name% «aggregate_claims_loop1»
  have l2 := hB' name% «aggregate_claims_loop2»
  have l3 := hB' name% «aggregate_claims_loop3»
  have f7 := fs_lt16 "batch_sumcheck__L25"
  have h1 := hk1 (by omega)
  have h3 := hk3 (by omega)
  have h5 := hk5 (by omega)
  have h7 := hk7 (by omega)
  have h9 := hk9 (by omega)
  omega

/-- **`AggFieldHypB` from what is left** on every inner node, frame and cursor. -/
theorem agg_fieldB_of_left (hk : 11 ≤ k)
    (H : ∀ (s : NodeStatement) (w : NodeWitness) (cover : List E), NodeRelation guestBytecode guestSeed s w →
      DeployedLimits s w → ChildrenOk guestBytecode guestSeed w → w.children ≠ [] →
      cover.length = (mainCounts s w).sx + (mainCounts s w).ss →
      ∀ fp c, mLo al (mainCounts s w) ≤ fp → fp + B2C.fs "aggregate_claims" ≤ c → c < 2 ^ 62 →
        AggLeftAt al k s w cover fp c) :
    AggFieldHypB al k := fun s w cover hr hd hok hne hcv fp c hlo hfc hc =>
  aggWinHyp_of_left hk hr hd hok hne hcv hlo hfc hc (H s w cover hr hd hok hne hcv fp c hlo hfc hc)

end

end
end LeanVM.Guest.Complete.Agg
