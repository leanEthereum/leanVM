module

public import LeanVM.Guest.Complete.Agg.Field
public import LeanVM.Guest.Complete.PopSkel
public import LeanVM.Guest.Complete.MainRunFacts
public import LeanVM.Guest.Complete.MainFinal
public import LeanVM.Guest.Memory.RetempExactA

/-!
# `aggregate_claims`' pops

`aggP` is straight, its skeleton the heap witness `bc_sumcheck_msgs`, `bc_star_hint`, then five callees (`aggP_skel`), every callee entered (its loops' guards `1 + g^m ≠ 0`, `aggP_conds`).
The callees pop nothing (`kOk_free`), so the node pops `bc_msgs`' words, `aLists 0` on a memory with
the own words, and `bc_star_hint`'s `finalBytecodeValue`: `Prover.batchPushes`. `aggPost_of_exact`:
`AggPostAt` from the node's exactness alone (`AggExactAt`).
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 200000 in
theorem aggP_straight : aggP.all Stmt.straight = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem aggP_skel : aggP.flatMap stmtSkel = [.wit "bc_sumcheck_msgs" (.heap (.n 6) 0 51),
    .wit "bc_star_hint" (.stack [.n 7]), .kid, .kid, .kid, .kid, .kid] := by decide +kernel

set_option maxRecDepth 200000 in
theorem aggP_conds : (aggP.filterMap Stmt.callS).map (·.1) =
    [some (.n 32), some (.n 442), some (.n 453), none, some (.n 571)] := by decide +kernel

theorem aTL_free : aTL.lookup (.n 6) = none ∧ aTL.lookup (.n 7) = none := by decide

theorem walk_agg (σ : Val) : walk σ (Fn.body fn% «aggregate_claims») = .ret (aggP.flatMap (slEvs σ)) [] := by
  rw [agg_shape]; exact walk_straight σ [] aggP aggP_straight

theorem aEs_eq (σ : Val) : aEs σ = aggP.flatMap (slEvs σ) := by
  rw [aEs, walk_straight_fall σ aggP aggP_straight]; rfl

/-- `aggregate_claims`' node is exact on the memories with `main`'s and the own words, at the valuation
its temporaries read from the memory. -/
def AggExactAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) (cover : List E) (c : ℕ) :
    Prop :=
  ∀ rd, LowDef k rd → MainPreA al s w cover rd → HoldsWords rd (aWo s w c) →
    ExactAt coreProgram rd "aggregate_claims"
      (over aTL (aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w))) rd)

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem agg_guards (hne : w.children ≠ []) (hd : DeployedLimits s w) :
    aV al s w cover c (.n 32) ≠ 0 ∧ aV al s w cover c (.n 442) ≠ 0 ∧ aV al s w cover c (.n 453) ≠ 0 ∧
      aV al s w cover c (.n 571) ≠ 0 := by
  have hn : w.children.length ≤ 16 := hd.atMostSixteenChildren
  have hm0 : w.children.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
  have v0 : aV al s w cover c (.n 0) = gen ^ w.children.length := aV_param (by norm_num)
  have guard : ∀ {d x : ℕ}, Atom.const (.n x) (word 1 0) ∈ atomsOf aggP → Atom.add (.n d) (.n x) (.n 0) ∈ atomsOf aggP →
      aV al s w cover c (.n d) ≠ 0 := fun hx ha => by
    rw [show aV al s w cover c (.n _) = aV al s w cover c (.n _) + aV al s w cover c (.n 0) from aV_good ha,
      show aV al s w cover c _ = _ from aGood_const (aggArgs_length _ _) hx, v0]
    exact fun h => hm0 ((guard_eq_zero_iff (by omega)).mp h)
  exact ⟨guard (d := 32) (x := 31) (w0_mem _ (by simp [w0A])) (w0_mem _ (by simp [w0A])),
    guard (d := 442) (x := 441) (mem_tail (by simp [w2Tail])) (mem_tail (by simp [w2Tail])),
    guard (d := 453) (x := 452) (w46_mem.1 _ (by simp [w4A])) (w46_mem.1 _ (by simp [w4A])),
    guard (d := 571) (x := 570) (w8_mem _ (by simp [w8A, w8T])) (w8_mem _ (by simp [w8A, w8T]))⟩

/-- **`aggregate_claims`' callees are all entered and pop nothing**, on a valuation whose loops' guards
are nonzero. -/
theorem agg_kOk {σ : Val} (g1 : σ (.n 32) ≠ 0) (g2 : σ (.n 442) ≠ 0) (g3 : σ (.n 453) ≠ 0) (g4 : σ (.n 571) ≠ 0)
    (rd : Reader) :
    KOk rd [FreePost, FreePost, FreePost, FreePost, FreePost] ((calls (aEs σ)).map Call.taken) [[], [], [], [], []] := by
  rw [aEs_eq, straight_taken _ aggP aggP_straight, aggP_conds]
  simp only [List.map_cons, List.map_nil, takenOf, g1, g2, g3, g4, ne_eq, not_false_eq_true, decide_true]
  exact kOk_free (kOk_free (kOk_free (kOk_free (kOk_free trivial))))

/-- **`bc_msgs`' words** on a memory with the own words. -/
theorem msgs_words (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ []) {rd : Reader}
    (hO : HoldsWords rd (aWo s w c)) :
    Dest.words rd (aV al s w cover c) (.heap (.n 6) 0 51) = Batch.lambdaGrindNonceCells w.batchingHints ++
      w.batchingHints.sumcheckMessages.flatMap Batch.sumcheckRoundCells := by
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  obtain ⟨p6, -⟩ := aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  obtain ⟨hq0, hlen0⟩ := aWo_get (c := c) hl (j := 0) (by norm_num)
  have e0 : (aLists s w).getD 0 [] = Batch.lambdaGrindNonceCells w.batchingHints ++
      w.batchingHints.sumcheckMessages.flatMap Batch.sumcheckRoundCells := rfl
  have h51 : ((aLists s w).getD 0 []).length = 51 := by rw [hlen0]; simp [aBufs]
  rw [← e0]
  refine List.ext_getElem (by simp only [Dest.words, List.length_map, List.length_range]; exact h51.symm)
    fun k h1 h2 => ?_
  simp only [Dest.words, List.getElem_map, List.getElem_range, p6, addr_ptr, Nat.zero_add]
  rw [holds_run hO hq0 h2]
  simp only [Option.getD_some]
  exact List.getD_eq_getElem _ _ _

set_option maxRecDepth 20000 in
/-- **`AggK` on any valuation** whose callees are all entered and pop nothing, from the node's two
witness entries and its exactness. -/
theorem aggK_of {k : ℕ} {Pre : Reader → Prop} {P : List Pop} {σ : Val} {st : St}
    (hQs : st.Qs = [FreePost, FreePost, FreePost, FreePost, FreePost])
    (g1 : σ (.n 32) ≠ 0) (g2 : σ (.n 442) ≠ 0) (g3 : σ (.n 453) ≠ 0) (g4 : σ (.n 571) ≠ 0)
    (hpop : ∀ rd, st.O rd → [("bc_sumcheck_msgs", Dest.words rd (over aTL σ rd) (.heap (.n 6) 0 51)),
      ("bc_star_hint", [over aTL σ rd (.n 7)])] = P)
    (hx : ∀ rd, LowDef k rd → Pre rd → st.O rd → ExactAt coreProgram rd "aggregate_claims" (over aTL σ rd)) :
    AggK k Pre (PopsPost P) σ st := by
  intro rd hlow hP hOr ts hv hq
  rw [hQs] at hq
  have hk := kOk_kids (agg_kOk g1 g2 g3 g4 rd) hv hq
  refine ⟨?_, Tree.every_node.mpr ⟨hx rd hlow hP hOr, hk.2⟩⟩
  rw [Tree.pops_node find_agg (walk_agg _), splice_skel, straight_skel aggP aggP_straight, aggP_skel]
  refine sameStreams_trans (skelPops_streams rd _ _ hk.1) (sameStreams_of_eq ?_)
  simp only [skelPops, List.headD_cons, List.tail_cons, List.nil_append]
  rw [← hpop rd hOr]
  rfl

theorem agg_v7 : aV al s w cover c (.n 7) = w.batchingHints.finalBytecodeValue :=
  (aV_good agg_star_mem (.n 7) (by simp)).trans rfl

theorem agg_e6 (rd : Reader) : ∀ v ∈ destUses (.heap (.n 6) 0 51),
    over aTL (aV al s w cover c) rd v = aV al s w cover c v := by
  intro v hv
  simp [destUses] at hv
  subst hv
  exact over_eq aTL_free.1

/-- **The node's two witness entries** are `Prover.batchPushes`. -/
theorem agg_pop (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ []) {rd : Reader}
    (hO : HoldsWords rd (aWo s w c)) :
    [("bc_sumcheck_msgs", Dest.words rd (over aTL (aV al s w cover c) rd) (.heap (.n 6) 0 51)),
      ("bc_star_hint", [over aTL (aV al s w cover c) rd (.n 7)])] = Prover.batchPushes w.batchingHints := by
  rw [destWords_congr (agg_e6 rd), msgs_words hr hne hO, over_eq aTL_free.2, agg_v7]
  rfl

theorem aV_eq : aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w)) = aV al s w cover c := rfl

set_option linter.all false in
set_option maxRecDepth 20000 in
/-- **`aggregate_claims`' final condition from its exactness.** -/
theorem aggPost_of_exact (hr : NodeRelation guestBytecode guestSeed s w) (hd : DeployedLimits s w)
    (hne : w.children ≠ []) (hx : AggExactAt al k s w cover c) : AggPostAt al k s w cover c := by
  intro st hO hQs
  rw [aV_eq]
  have hg := agg_guards (al := al) (cover := cover) (c := c) hne hd
  exact aggK_of (σ := aV al s w cover c) hQs hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 (fun rd hOr => agg_pop hr hne (hO rd hOr))
    fun rd hlow hP hOr => hx rd hlow hP (hO rd hOr)

end

/-- The node's exactness on every inner node and cursor below `2^62`. -/
def AggExactHyp (al : String → Bool) (k : ℕ) : Prop :=
  ∀ (s : NodeStatement) (w : NodeWitness) (cover : List E), NodeRelation guestBytecode guestSeed s w →
    DeployedLimits s w → ChildrenOk guestBytecode guestSeed w → w.children ≠ [] →
    cover.length = (mainCounts s w).sx + (mainCounts s w).ss → ∀ c, c < 2 ^ 62 → AggExactAt al k s w cover c

theorem aggPostHyp_of_exact {al : String → Bool} {k : ℕ} (H : AggExactHyp al k) : AggPostHyp al k :=
  fun s w cover hr hd hok hne hcv c hc => aggPost_of_exact hr hd hne (H s w cover hr hd hok hne hcv c hc)

/-- **`MainCalleesOpenAt.agg` at `alW`, `17`, from the node's exactness.** -/
theorem agg_field_alW_of_exact (H : AggExactHyp alW 17) {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hr : NodeRelation guestBytecode guestSeed s w) (hd : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w)
    (hcv : cover.length = (mainCounts s w).sx + (mainCounts s w).ss) :
    w.children ≠ [] → AtEveryB alW 17 "aggregate_claims"
      [gen ^ (mainCounts s w).nc, mPtr (mainCounts s w) 5 0, mPtr (mainCounts s w) 6 0, mPtr (mainCounts s w) 7 0,
        mPtr (mainCounts s w) 9 0, ptrAt (mGS alW (mainCounts s w) + winTabAt)] []
      (mainR alW (mainCounts s w)) (MainPreA alW s w cover) (PopsPost (Prover.batchPushes w.batchingHints))
      (B2C.fs "aggregate_claims") (mLo alW (mainCounts s w)) (2 ^ 60) (2 ^ 40) :=
  agg_field_alW (aggPostHyp_of_exact H) hr hd hok hcv

end
end LeanVM.Guest.Complete.Agg
