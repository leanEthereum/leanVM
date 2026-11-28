/-
  LeanVM.Guest.Complete.MainLeafAgg

  `main`'s leaf or aggregate branch at the honest oracle, and what is left past it.
-/

module

public import LeanVM.Guest.Complete.MainMidTail
import LeanVM.Guest.Complete.Agg.Batched
import LeanVM.Guest.B1.Main.Final

/-!
# The leaf or aggregate branch

The selector `.n 423` is `g^n_children + 1`, zero exactly on a leaf (`mOrc_423_zero`). A leaf
(`wLeaf`) stores its deferred claim, `25` zeros and the hinted value (`HasZeroPoint`), at
`defer_stmt` (`runHypT_leaf`); an inner node (`wAgg`) calls `aggregate_claims` (`MainCalleesAt.agg`)
on the window table at `g_squares · g^WIN_TAB_AT`. `leafAgg_hyp`: the branch keeps `PreInv` at
`mTop`, the posts gaining `qAgg w`.

`MainPostAt al k s w cover`: `mPost`'s hypotheses from every state with `PreInv … (mTop m)
(qPre s w ++ qDa w ++ [qIf nc (PopsPost (mKidPushes s w))] ++ qAgg w)`, ending in `MainHypAt`'s final
condition. `mainTailAt_of_post`, `MainPostFromCallees`,
`mainWinHypFromCallees_of_post : MainPostFromCallees al k → MainWinHypFromCallees al k`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier

@[expose] public section

/-- The aggregate branch's post: the batching's pushes on an inner node. -/
def qAgg (w : NodeWitness) : List (Reader → Tree → Prop) :=
  if w.children = [] then [] else [PopsPost (Prover.batchPushes w.batchingHints)]

/-- A store of the leaf's deferred claim: `defer_stmt[i] = …`. -/
def leafLoad : Atom → Bool
  | .load (.n _) (.n 421) i => decide (i < 26)
  | _ => false

/-- The value a leaf store writes: a zero constant before the last cell, the hinted value at it. -/
noncomputable def leafVal : Atom → Bool
  | .load (.n d) (.n 421) i =>
    (decide (i < 25) && decide (Atom.const (.n d) (word 0 0) ∈ atomsOf mLeaf)) || (decide (i = 25) && decide (d = 424))
  | _ => true

set_option maxRecDepth 200000 in
theorem leaf_atoms :
    (atomsOf ((mLeaf.drop 0).take 52)).all (fun x => noHeapB x && (trivPM x || leafLoad x)) = true ∧
      allocDsts ((atomsOf ((mLeaf.drop 0).take 52)).map Ev.atom) = [] ∧
      (atomsOf ((mLeaf.drop 0).take 52)).filter isAllocA = [] ∧
      (atomsOf ((mLeaf.drop 0).take 52)).all leafVal = true ∧
      Atom.hint (.witness "leaf_defer" (.stack [.n 424])) ∈ atomsOf mLeaf := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem agg_atoms :
    (atomsOf ((mAgg.drop 0).take 2)).all (fun x => plainRunB x && trivPM x) = true ∧
      Atom.const (.n 450) (word 365917469723852800 0) ∈ atomsOf mAgg ∧
      Atom.mul (.n 451) (.n 51) (.n 450) ∈ atomsOf mAgg ∧
      Atom.const (.n 422) (word 1 0) ∈ atomsOf mMid ∧ Atom.add (.n 423) (.n 6) (.n 422) ∈ atomsOf mMid ∧
      Atom.hint (.alloc (.n 421) 26) ∈ atomsOf mMid := by
  decide +kernel

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd0 : Reader}
  {R : ℕ → Prop} {es : List Ev}

theorem mOrc_423 : mVal rd0 (mOrc al s w) (.n 423) = word 1 0 + gen ^ (mainCounts s w).nc := by
  obtain ⟨-, -, -, k422, a423, -⟩ := agg_atoms
  have c6 := (mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)).2.2.2.2.2.2.1
  have e : mVal rd0 (mOrc al s w) (.n 423) = mVal rd0 (mOrc al s w) (.n 6) + mVal rd0 (mOrc al s w) (.n 422) :=
    mMid_good a423
  rw [e, show mVal rd0 (mOrc al s w) (.n 422) = word 1 0 from mMid_good k422, c6, add_comm]

theorem mOrc_421 : mVal rd0 (mOrc al s w) (.n 421) = ptrAt (mBase (mainCounts s w) 9 + 0) :=
  mMid_good agg_atoms.2.2.2.2.2

/-- **The selector is zero exactly on a leaf.** -/
theorem mOrc_423_zero (hn : (mainCounts s w).nc ≤ 16) :
    mVal rd0 (mOrc al s w) (.n 423) = 0 ↔ (mainCounts s w).nc = 0 := by
  rw [mOrc_423]; exact guard_eq_zero_iff (by omega)

theorem mOrc_423_inK : IsInK (mVal rd0 (mOrc al s w) (.n 423)) := by
  rw [mOrc_423, word_one]
  exact isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK _)

/-- **A leaf's deferred claim**: `25` zeros and its value. -/
theorem leaf_cells (hr : NodeRelation guestBytecode guestSeed s w) (h : w.children = []) :
    s.deferredClaim.cells = List.replicate 25 0 ++ [s.deferredClaim.bytecodeValue] := by
  have hb := hr.2.2.2
  simp only [DeferredClaimBatched, h, ↓reduceIte, DeferredBytecodeClaim.HasZeroPoint,
    Agg.guest_deferredVariableCount] at hb
  rw [DeferredBytecodeClaim.cells, hb]

set_option linter.unusedSimpArgs false in
/-- **A leaf's stores** of its deferred claim at `defer_stmt`. -/
theorem runHypT_leaf {a : ℕ} {D : ℕ → Prop} {O : Reader → Prop} (h0 : mVal rd0 (mOrc al s w) (.n 423) = 0)
    (hcells : s.deferredClaim.cells = List.replicate 25 0 ++ [s.deferredClaim.bytecodeValue])
    (hO : ∀ rd, O rd → HoldsWords rd (mainWords s w cover)) :
    RunHypT k (mVal rd0 (mOrc al s w)) (mOrc al s w) a
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R D (mainPreR s) O
      (atomsOf ((mLeaf.drop 0).take 52)) := by
  obtain ⟨hall, hdst, hal, hval, hwit⟩ := leaf_atoms
  have hg := mVal_goodLeaf (rd := rd0) (w := mOrc al s w) h0
  have hq : ∀ x ∈ atomsOf ((mLeaf.drop 0).take 52), noHeapB x = true ∧ (trivPM x = true ∨ leafLoad x = true) :=
    fun x hx => by
      have := List.all_eq_true.mp hall x hx
      simpa only [Bool.and_eq_true, Bool.or_eq_true] using this
  have hstore : ∀ x, leafLoad x = true → ∃ d i, i < 26 ∧ x = .load (.n d) (.n 421) i := by
    intro x hx
    match x, hx with
    | .load (.n d) (.n 421) i, hx =>
      simp only [leafLoad, decide_eq_true_eq] at hx
      exact ⟨d, i, hx, rfl⟩
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, bt⟩ := mBase_eqs (mainCounts s w)
  have h2 := fs_main_ge
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdst, allocs_atoms, hal]; rfl
  · intro A hA
    obtain ⟨x, hx, hl⟩ := loadAddr_mem hA
    rcases (hq x hx).2 with ht | ht
    · exfalso
      cases x with
      | load d p off => simp [trivPM] at ht
      | _ => simp [Ev.loadAddr?] at hl
    · obtain ⟨d, i, hi, rfl⟩ := hstore x ht
      simp only [Ev.loadAddr?, Option.some.injEq, mOrc_421] at hl
      rw [Main.addr_ofK] at hl
      exact ⟨_, hl.symm, Or.inl (own_main (by omega) (by omega))⟩
  · rw [heapHintAddrs_noHeap (List.all_eq_true.mpr fun x hx => (hq x hx).1)]
    intro A hA; simp at hA
  · intro x hx
    rcases (hq x hx).2 with ht | ht
    · exact pureT_triv ht
    · obtain ⟨d, i, hi, rfl⟩ := hstore x ht
      trivial
  · intro rd _ _ hOr x hx
    rcases (hq x hx).2 with ht | ht
    · exact memT_triv ht
    · obtain ⟨d, i, hi, rfl⟩ := hstore x ht
      have hv := List.all_eq_true.mp hval _ hx
      simp only [leafVal, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hv
      have r9 := (main_runs (hO rd hOr)).2.2.2.2.2
      rw [hcells] at r9
      show LoadHolds rd _ i _
      rw [mOrc_421, Nat.add_zero]
      have hL := r9 i (by simp; omega)
      rcases hv with ⟨hi', hc⟩ | ⟨rfl, rfl⟩
      · have e : mVal rd0 (mOrc al s w) (.n d) = 0 :=
          (show mVal rd0 (mOrc al s w) (.n d) = word 0 0 from hg _ (atom_mem_of_atomsOf hc)).trans word_zero
        rw [e]
        rwa [List.getElem_append_left (by simp; omega), List.getElem_replicate] at hL
      · have e : mVal rd0 (mOrc al s w) (.n 424) = s.deferredClaim.bytecodeValue := hg _ (atom_mem_of_atomsOf hwit) (.n 424) List.mem_cons_self
        rw [e]
        simpa using hL

/-- **The leaf or aggregate branch's hypotheses** keep the invariant at `mTop`, the posts gaining
`qAgg w`. -/
theorem leafAgg_hyp {st : St} {K : St → Prop} {Qs : List (Reader → Tree → Prop)}
    (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hcl : MainCalleesAt al k s w cover) (hst : PreInv al s w cover (mTop (mainCounts s w)) Qs st)
    (hrest : ∀ st', PreInv al s w cover (mTop (mainCounts s w)) (Qs ++ qAgg w) st' → K st') :
    IteHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) (.n 423) wLeaf wAgg st K := by
  have hn := nc_le hlim
  have hO : ∀ rd, st.O rd → HoldsWords rd (mainWords s w cover) := fun rd h => (hst.hO rd h).1
  refine ⟨mOrc_423_inK, fun h0 => ?_, fun h0 => ?_⟩
  · have hch : w.children = [] := List.eq_nil_of_length_eq_zero ((mOrc_423_zero hn).mp h0)
    unfold wLeaf mLeaf_w0
    refine winsHypT_runI (a' := mTop (mainCounts s w)) hst ?_ (runHypT_leaf h0 (leaf_cells hr hch) hO)
      fun st1 hst1 => ?_
    · rw [allocs_atoms, leaf_atoms.2.2.1]; rfl
    rw [WinsHypT]
    refine hrest st1 ?_
    have e : qAgg w = [] := by simp [qAgg, hch]
    rw [e, List.append_nil]; exact hst1
  · have hch : w.children ≠ [] := fun h => h0 ((mOrc_423_zero hn).mpr (by
      show w.children.length = 0; rw [h]; rfl))
    obtain ⟨ht, k450, m451, -⟩ := agg_atoms
    have hg := mVal_goodAgg (rd := rd0) (w := mOrc al s w) h0
    have c6 := (mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)).2.2.2.2.2.2.1
    obtain ⟨-, m398, m399, m400, -, -⟩ := mid1_mem
    have h51 : mVal rd0 (mOrc al s w) (.n 51) = mOrc al s w 51 :=
      mPre_call_rets (by unfold wPre mPre_w1; exact List.mem_cons_of_mem _ List.mem_cons_self) (.n 51)
        List.mem_cons_self
    have g451 : Good rd0 (storesOf 450 mAgg) (mOrc al s w) (mVal rd0 (mOrc al s w)) (.mul (.n 451) (.n 51) (.n 450)) :=
      hg _ (atom_mem_of_atomsOf m451)
    have h451 : mVal rd0 (mOrc al s w) (.n 451) = ptrAt (mGS al (mainCounts s w) + winTabAt) := by
      rw [good_mul g451 (by norm_num) (by norm_num), h51,
        show mVal rd0 (mOrc al s w) (.n 450) = word 365917469723852800 0 from hg _ (atom_mem_of_atomsOf k450), word_g178]
      exact ptrAt_mul_pow _ _
    unfold wAgg mAgg_w0 mAgg_w1
    refine winsHypT_runI (a' := mTop (mainCounts s w)) hst (by rw [plainTriv_allocs ht, Nat.add_zero])
      (plainTriv_runHypT ht) fun st1 hst1 => ?_
    refine winsHypT_callI hst1 rfl ?_ rfl (hcl.agg hch) (by norm_num) (fs_add_le _) fun st2 hst2 => ?_
    · show [mVal rd0 (mOrc al s w) (.n 6), mVal rd0 (mOrc al s w) (.n 398), mVal rd0 (mOrc al s w) (.n 399),
        mVal rd0 (mOrc al s w) (.n 400), mVal rd0 (mOrc al s w) (.n 421), mVal rd0 (mOrc al s w) (.n 451)] = _
      rw [c6, mMid_good m398, mMid_good m399, mMid_good m400, mOrc_421, h451]
      rfl
    rw [WinsHypT]
    refine hrest st2 ?_
    have e : qAgg w = [PopsPost (Prover.batchPushes w.batchingHints)] := by simp [qAgg, hch]
    rw [e]; exact hst2

end

/-! ## What is left past the branch -/

/-- **`mPost`'s windows** at the honest oracle, from where the leaf or aggregate branch ends. -/
def MainPostAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) (cover : List E) : Prop :=
  ∀ st, PreInv al s w cover (mTop (mainCounts s w))
      (qPre s w ++ qDa w ++ [qIf (mainCounts s w).nc (PopsPost (mKidPushes s w))] ++ qAgg w) st →
    WinsHypT B2C.fs al B2C.cert k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs (mEs (mVal (mRd0 s w cover) (mOrc al s w))))
      (· < 2) (mainPreR s) wPost st fun st => ∀ rd, LowDef k rd → mainPreR s rd → st.O rd → ∀ ts,
        Tree.KidsValid coreProgram rd (over mTL (mVal (mRd0 s w cover) (mOrc al s w)) rd)
          (calls (mEs (mVal (mRd0 s w cover) (mOrc al s w)))) ts →
        KidsPost rd st.Qs (calls (mEs (mVal (mRd0 s w cover) (mOrc al s w)))) ts →
        mainPostR s w rd (.node "main" (over mTL (mVal (mRd0 s w cover) (mOrc al s w)) rd) (mainCounts s w).bufs ts)

theorem mainTailAt_of_post {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w) (hcl : MainCalleesAt al k s w cover)
    (h : MainPostAt al k s w cover) : MainTailAt al k s w cover :=
  fun _ hst => leafAgg_hyp hr hlim hcl hst fun st' h' => h st' h'

/-- **What is left of `main`'s window past its leaf or aggregate branch**, on every node and every
coverage table the callees' fields hold on. -/
def MainPostFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  17 ≤ k → k ≤ 23 → MainCalleesA al k → VsCompleteHypA al k guestBytecode guestSeed →
    ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w →
      ChildrenOk guestBytecode guestSeed w → ∀ cover : List E,
        cover.length = (mainCounts s w).sx + (mainCounts s w).ss → MainCalleesAt al k s w cover →
        MainPostAt al k s w cover

theorem mainWinHypFromCallees_of_post {al : String → Bool} {k : ℕ} (h : MainPostFromCallees al k) :
    MainWinHypFromCallees al k :=
  mainWinHypFromCallees_of_tail fun hk hk' hc hvs s w hr hlim hok cover hlen hat =>
    mainTailAt_of_post hr hlim hat (h hk hk' hc hvs s w hr hlim hok cover hlen hat)

end
end LeanVM.Guest.Complete
