/-
  LeanVM.Guest.Complete.MainMidTail

  `mMid` at the honest oracle: its last run, and what is left of `MainMidAt` past it.
-/

module

public import LeanVM.Guest.Complete.MainKids
import LeanVM.Guest.Complete.ClaimCells

/-!
# `mMid`'s last run

`mMid_w2`: `written[n_children]` read back as the slots' count (`kidBase_all`, `slots_eq_cov`, on
the evaluation memory `mRd0`, `mRd0_holds`), `da_pick`'s range check against `n_children` and its
`assertEq` (`daPick_le`, `daPick_of_nd`), `defer_stmt`'s `HeapBuf` at `mBase m 9`: `winsHypT_mid2`
keeps `PreInv` from `mBase m 9` to `mTop`.

`MainTailAt al k s w cover`: the leaf or aggregate branch's and `mPost`'s hypotheses from every state
with `PreInv … (mTop m) (qPre s w ++ qDa w ++ [qIf nc (PopsPost (mKidPushes s w))])`, ending in
`MainHypAt`'s final condition. `mainMidAt_of_tail`, `MainTailFromCallees`,
`mainWinHypFromCallees_of_tail : MainTailFromCallees al k → MainWinHypFromCallees al k`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The evaluation memory -/

theorem fs_main_ge : 2 ≤ B2C.fs "main" := by
  rw [B2C.fs_main]; unfold B2C.mainFrame; decide +kernel

theorem mTop_lt {s : NodeStatement} {w : NodeWitness} (hb : (mainCounts s w).sx + (mainCounts s w).ss < 2 ^ 19)
    (hn : (mainCounts s w).nc ≤ 16) : mTop (mainCounts s w) < 2 ^ 64 - 1 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, bt⟩ := mBase_eqs (mainCounts s w)
  have := fs_main_lt
  omega

/-- **The evaluation memory holds `main`'s words.** -/
theorem mRd0_holds {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs)
    (hb : (mainCounts s w).sx + (mainCounts s w).ss < 2 ^ 19) (hn : (mainCounts s w).nc ≤ 16) :
    HoldsWords (mRd0 s w cover) (mainWords s w cover) := by
  obtain ⟨hin, hd⟩ := mainWords_in hl
  have h2 := fs_main_ge
  have ht := mTop_lt hb hn
  have hall := holdsWords_rdW (W := (0, Prover.digestCells (statementDigest guestSeed s)) :: mainWords s w cover)
    (List.pairwise_cons.mpr ⟨fun q hq => Or.inl (by
      have := (hin q hq).1
      simp only [Prover.digestCells, List.length_cons, List.length_nil]; omega), hd⟩) (fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · simp [Prover.digestCells]
      · have := (hin q hq).2
        omega)
  exact fun q hq => hall q (List.mem_cons_of_mem _ hq)

theorem rdAt_of_loadHolds {rd : Reader} {p v : E} {off : ℕ} (h : LoadHolds rd p off v) : rdAt rd p off = v := by
  rw [rdAt, h.2]; rfl

/-! ## The DA pick -/

theorem daPick_le (s : NodeStatement) (w : NodeWitness) : Prover.daPick s w ≤ (mainCounts s w).nc := by
  show _ ≤ w.children.length
  unfold Prover.daPick
  split
  · exact le_rfl
  · cases h : List.findIdx? (fun c => c.statement.claims.daDigest == s.claims.daDigest) w.children with
    | none => simp
    | some i =>
      simp only [Option.getD_some]
      exact le_of_lt (List.findIdx?_eq_some_iff_getElem.mp h).1

theorem daPick_of_nd {s : NodeStatement} {w : NodeWitness} (h : (mainCounts s w).nd = 1) :
    Prover.daPick s w = (mainCounts s w).nc := by
  show _ = w.children.length
  unfold Prover.daPick
  have hs : w.daMatrix.isSome = true := by
    cases hm : w.daMatrix with
    | none => simp [mainCounts, hm] at h
    | some _ => rfl
  simp [hs]

/-! ## The run -/

set_option maxRecDepth 200000 in
theorem mid2_shape : atomsOf ((mMid.drop 12).take 16) =
    [.mul (.n 408) (.n 403) (.n 6), .load (.n 409) (.n 408) 0, .assertEq (.n 409) (.n 24),
      .hint (.witness "da_pick" (.stack [.n 410])), .rangeCheck (.n 410) (.n 411) (.n 412) (.n 413) (.n 6),
      .add (.n 414) (.n 410) (.n 6), .const (.n 415) (word 1 0), .add (.n 416) (.n 7) (.n 415),
      .mul (.n 417) (.n 414) (.n 416), .const (.n 418) (word 0 0), .assertEq (.n 417) (.n 418),
      .mul (.n 419) (.n 410) (.n 410), .mul (.n 420) (.n 380) (.n 419), .hint (.alloc (.n 421) 26),
      .const (.n 422) (word 1 0), .add (.n 423) (.n 6) (.n 422)] := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem mid2_mem : Atom.mul (.n 408) (.n 403) (.n 6) ∈ atomsOf mMid ∧ Atom.load (.n 409) (.n 408) 0 ∈ atomsOf mMid ∧
    Atom.load (.n 409) (.n 408) 0 ∉ storesOf 398 mMid ∧
    Atom.hint (.witness "da_pick" (.stack [.n 410])) ∈ atomsOf mMid ∧
    Atom.rangeCheck (.n 410) (.n 411) (.n 412) (.n 413) (.n 6) ∈ atomsOf mMid ∧
    Atom.add (.n 414) (.n 410) (.n 6) ∈ atomsOf mMid ∧ Atom.const (.n 415) (word 1 0) ∈ atomsOf mMid ∧
    Atom.add (.n 416) (.n 7) (.n 415) ∈ atomsOf mMid ∧ Atom.mul (.n 417) (.n 414) (.n 416) ∈ atomsOf mMid ∧
    Atom.const (.n 418) (word 0 0) ∈ atomsOf mMid := by
  decide +kernel

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}

/-- `mMid_w2`'s values on the honest oracle. -/
theorem mid2_vals (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs) :
    mVal (mRd0 s w cover) (mOrc al s w) (.n 408) = ptrAt (mBase (mainCounts s w) 8 + 0 + (mainCounts s w).nc) ∧
      mVal (mRd0 s w cover) (mOrc al s w) (.n 409) = mVal (mRd0 s w cover) (mOrc al s w) (.n 24) ∧ mVal (mRd0 s w cover) (mOrc al s w) (.n 410) = gen ^ Prover.daPick s w ∧
      mVal (mRd0 s w cover) (mOrc al s w) (.n 411) = gen ^ ((mainCounts s w).nc - Prover.daPick s w) ∧
      mVal (mRd0 s w cover) (mOrc al s w) (.n 417) = (gen ^ Prover.daPick s w + gen ^ (mainCounts s w).nc) * (gen ^ (mainCounts s w).nd + 1) ∧
      mVal (mRd0 s w cover) (mOrc al s w) (.n 418) = 0 := by
  obtain ⟨m408, m409, n409, m410, mrc, m414, m415, m416, m417, m418⟩ := mid2_mem
  obtain ⟨-, -, -, -, -, -, c6, c7⟩ := mOrc_counts (al := al) (s := s) (w := w) (rd := mRd0 s w cover)
  obtain ⟨-, -, v24, -⟩ := mOrc_sizes (al := al) (s := s) (w := w) (rd := mRd0 s w cover)
  obtain ⟨-, -, -, -, m403, -⟩ := mid1_mem
  have h403 : mVal (mRd0 s w cover) (mOrc al s w) (.n 403) = mOrc al s w 403 := mMid_good m403
  have s408 : mVal (mRd0 s w cover) (mOrc al s w) (.n 408) = ptrAt (mBase (mainCounts s w) 8 + 0 + (mainCounts s w).nc) := by
    rw [good_mul (mMid_good m408) (by norm_num) (by norm_num), h403, c6]
    exact ptrAt_mul_pow _ _
  have s410 : mVal (mRd0 s w cover) (mOrc al s w) (.n 410) = gen ^ Prover.daPick s w := mMid_good m410 (.n 410) List.mem_cons_self
  refine ⟨s408, ?_, s410, ?_, ?_, ?_⟩
  · have hg : Good (mRd0 s w cover) (storesOf 398 mMid) (mOrc al s w) (mVal (mRd0 s w cover) (mOrc al s w)) (.load (.n 409) (.n 408) 0) := mMid_good m409
    rcases hg with hg | hg
    · exact (n409 hg).elim
    have hH := (main_runs (mRd0_holds hl (slots_lt hr hlim) (nc_le hlim))).2.2.2.2.1
    have hL := loadHolds_run (c := (mainCounts s w).nc) (j := 0) hH (by simp)
    rw [hg, v24, s408, Nat.add_zero, rdAt_of_loadHolds hL]
    simp only [List.getElem_map, List.getElem_range, Nat.add_zero]
    rw [show (mainCounts s w).nc = w.children.length from rfl, kidBase_all, slots_eq_cov hr]
  · rw [good_rc_div (mMid_good mrc) (by norm_num), c6, s410]
    exact gen_pow_div (daPick_le s w)
  · rw [good_mul (mMid_good m417) (by norm_num) (by norm_num), mMid_good m414, mMid_good m416, s410, c6, c7,
      show mVal (mRd0 s w cover) (mOrc al s w) (.n 415) = word 1 0 from mMid_good m415, word_one]
  · rw [show mVal (mRd0 s w cover) (mOrc al s w) (.n 418) = word 0 0 from mMid_good m418, word_zero]


set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
/-- **`mMid`'s last run** at the honest oracle, from `defer_stmt`'s base `mBase m 9`. -/
theorem runHypT_mid2 {R D : ℕ → Prop} {O : Reader → Prop} {es : List Ev} (hk : 17 ≤ k)
    (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs)
    (hO : ∀ rd, O rd → HoldsWords rd (mainWords s w cover)) :
    RunHypT k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w) (mBase (mainCounts s w) 9)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R D (mainPreR s) O
      (atomsOf ((mMid.drop 12).take 16)) ∧
    mBase (mainCounts s w) 9 + (allocs (mVal (mRd0 s w cover) (mOrc al s w))
      ((atomsOf ((mMid.drop 12).take 16)).map Ev.atom)).sum = mTop (mainCounts s w) := by
  obtain ⟨s408, s409, s410, s411, s417, s418⟩ := mid2_vals (al := al) hr hlim hl
  obtain ⟨-, -, v24, -⟩ := mOrc_sizes (al := al) (s := s) (w := w) (rd := mRd0 s w cover)
  have hn := nc_le hlim
  have hdp := daPick_le s w
  have hnd := nd_le s w
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, bt⟩ := mBase_eqs (mainCounts s w)
  have h2 := fs_main_ge
  have o421 : mOrc al s w 421 = mPtr (mainCounts s w) 9 0 := rfl
  have p409 : PureT (mVal (mRd0 s w cover) (mOrc al s w)) (.assertEq (.n 409) (.n 24)) := by
    show _ + _ = 0
    rw [s409]; exact CharTwo.add_self_eq_zero _
  have prc : PureT (mVal (mRd0 s w cover) (mOrc al s w)) (.rangeCheck (.n 410) (.n 411) (.n 412) (.n 413) (.n 6)) :=
    pureT_rc s410 s411
  have p417 : PureT (mVal (mRd0 s w cover) (mOrc al s w)) (.assertEq (.n 417) (.n 418)) := by
    show _ + _ = 0
    rw [s417, s418, add_zero]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hnd with h0 | h1
    · rw [h0, pow_zero, CharTwo.add_self_eq_zero, mul_zero]
    · rw [daPick_of_nd h1, CharTwo.add_self_eq_zero, zero_mul]
  have m409 : ∀ rd, O rd → MemT rd (mVal (mRd0 s w cover) (mOrc al s w)) (.load (.n 409) (.n 408) 0) := by
    intro rd hOr
    show LoadHolds rd _ 0 _
    have hL := loadHolds_run (c := (mainCounts s w).nc) (j := 0) (main_runs (hO rd hOr)).2.2.2.2.1 (by simp)
    simp only [List.getElem_map, List.getElem_range, Nat.add_zero] at hL
    have e : gen ^ kidBase w (mainCounts s w).nc = gen ^ ((mainCounts s w).sx + (mainCounts s w).ss) := by
      rw [show (mainCounts s w).nc = w.children.length from rfl, kidBase_all, slots_eq_cov hr]
    rw [e] at hL
    rw [s408, s409, v24, Nat.add_zero]
    exact hL
  have mrc : ∀ rd, LowDef k rd →
      MemT rd (mVal (mRd0 s w cover) (mOrc al s w)) (.rangeCheck (.n 410) (.n 411) (.n 412) (.n 413) (.n 6)) := by
    intro rd hLd
    have h17 : (2 : ℕ) ^ 17 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have e17 : (2 : ℕ) ^ 17 = 131072 := by norm_num
    exact memT_rc s410 s411 (hLd _ (by omega)) (hLd _ (by omega))
  rw [mid2_shape]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [allocDsts, allocs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil,
      Ev.allocDst?, Ev.alloc?, bases, V.idx, o421, mPtr, Nat.add_zero]
  · intro A hA
    simp only [loadAddrs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, Ev.loadAddr?,
      List.mem_cons, List.not_mem_nil, or_false, s408] at hA
    rw [Main.addr_ofK] at hA
    exact ⟨_, hA, Or.inl (own_main (by omega) (by omega))⟩
  · rw [heapHintAddrs_noHeap (by decide)]
    intro A hA; simp at hA
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pureT_triv rfl
    · trivial
    · exact p409
    · exact pureT_triv rfl
    · exact prc
    · exact pureT_triv rfl
    · exact pureT_triv rfl
    · exact pureT_triv rfl
    · exact pureT_triv rfl
    · exact pureT_triv rfl
    · exact p417
    · exact pureT_triv rfl
    · exact pureT_triv rfl
    · exact pureT_triv rfl
    · exact pureT_triv rfl
    · exact pureT_triv rfl
  · intro rd hLd _ hOr x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact memT_triv rfl
    · exact m409 rd hOr
    · trivial
    · exact memT_triv rfl
    · exact mrc rd hLd
    · exact memT_triv rfl
    · exact memT_triv rfl
    · exact memT_triv rfl
    · exact memT_triv rfl
    · exact memT_triv rfl
    · trivial
    · exact memT_triv rfl
    · exact memT_triv rfl
    · exact memT_triv rfl
    · exact memT_triv rfl
    · exact memT_triv rfl

  · simp only [allocs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, Ev.alloc?,
      List.sum_cons, List.sum_nil]
    omega

/-- **`mMid`'s last run** keeps the invariant, from `mBase m 9` to `mTop`. -/
theorem winsHypT_mid2 {R : ℕ → Prop} {es : List Ev} {ws : List W1} {st : St} {K : St → Prop}
    {Qs : List (Reader → Tree → Prop)} (hk : 17 ≤ k) (hr : NodeRelation guestBytecode guestSeed s w)
    (hlim : DeployedLimits s w) (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs)
    (hst : PreInv al s w cover (mBase (mainCounts s w) 9) Qs st)
    (hrest : ∀ st', PreInv al s w cover (mTop (mainCounts s w)) Qs st' →
      WinsHypT B2C.fs al B2C.cert k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w)
        (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) ws st' K) :
    WinsHypT B2C.fs al B2C.cert k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) (mMid_w2 :: ws) st K := by
  obtain ⟨h1, ha⟩ := runHypT_mid2 (al := al) (R := R) (D := st.D) (O := st.O) (es := es) hk hr hlim hl
    fun rd h => (hst.hO rd h).1
  unfold mMid_w2
  exact winsHypT_runI hst ha h1 hrest

end

/-! ## What is left past `mMid` -/

/-- **`main`'s windows past `mMid`** at the honest oracle, from where `mMid` ends. -/
def MainTailAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) (cover : List E) : Prop :=
  ∀ st, PreInv al s w cover (mTop (mainCounts s w))
      (qPre s w ++ qDa w ++ [qIf (mainCounts s w).nc (PopsPost (mKidPushes s w))]) st →
    IteHypT B2C.fs al B2C.cert k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs (mEs (mVal (mRd0 s w cover) (mOrc al s w))))
      (· < 2) (mainPreR s) (.n 423) wLeaf wAgg st fun s4 =>
    WinsHypT B2C.fs al B2C.cert k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs (mEs (mVal (mRd0 s w cover) (mOrc al s w))))
      (· < 2) (mainPreR s) wPost s4 fun st => ∀ rd, LowDef k rd → mainPreR s rd → st.O rd → ∀ ts,
        Tree.KidsValid coreProgram rd (over mTL (mVal (mRd0 s w cover) (mOrc al s w)) rd)
          (calls (mEs (mVal (mRd0 s w cover) (mOrc al s w)))) ts →
        KidsPost rd st.Qs (calls (mEs (mVal (mRd0 s w cover) (mOrc al s w)))) ts →
        mainPostR s w rd (.node "main" (over mTL (mVal (mRd0 s w cover) (mOrc al s w)) rd) (mainCounts s w).bufs ts)

/-- **`MainMidAt` from `mMid`'s windows and what is left past them.** -/
theorem mainMidAt_of_tail {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hk : 17 ≤ k) (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w) (hvs : VsCompleteHypA al k guestBytecode guestSeed)
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs) (hcl : MainCalleesAt al k s w cover)
    (h : MainTailAt al k s w cover) : MainMidAt al k s w cover := by
  intro st hst
  have cc := claimCells_of hr hok
  unfold wMid
  exact winsHypT_mid0 (nc_le hlim) hst fun _ h1 => winsHypT_mid1 hk hr hlim hok hvs cc hl hcl h1 fun _ h2 =>
    winsHypT_mid2 hk hr hlim hl h2 fun st3 h3 => by rw [WinsHypT]; exact h st3 h3

/-- **What is left of `main`'s window past `mMid`**, on every node and every coverage table the
callees' fields hold on. -/
def MainTailFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  17 ≤ k → k ≤ 23 → MainCalleesA al k → VsCompleteHypA al k guestBytecode guestSeed →
    ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w →
      ChildrenOk guestBytecode guestSeed w → ∀ cover : List E,
        cover.length = (mainCounts s w).sx + (mainCounts s w).ss → MainCalleesAt al k s w cover →
        MainTailAt al k s w cover

theorem mainWinHypFromCallees_of_tail {al : String → Bool} {k : ℕ} (h : MainTailFromCallees al k) :
    MainWinHypFromCallees al k :=
  mainWinHypFromCallees_of_mid fun hk hk' hc hvs s w hr hlim hok cover hlen hat => by
    have cc := claimCells_of hr hok
    exact mainMidAt_of_tail hk hr hlim hok hvs (mainLists_length hlen cc.fresh cc.carried cc.own) hat
      (h hk hk' hc hvs s w hr hlim hok cover hlen hat)

end
end LeanVM.Guest.Complete
