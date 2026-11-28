/-
  LeanVM.Guest.Complete.MainPostWins

  `mPost` at the honest oracle: the picked DA digest, the own statement's digest, the header.
-/

module

public import LeanVM.Guest.Complete.MainLeafAgg
import LeanVM.Guest.Complete.ClaimCells
import LeanVM.Guest.B1.Main.Digests

/-!
# `mPost`'s windows

`mPost_w0` loads `da_digests[da_pick]`: the node's published DA digest (`daPick_cells`, from
`DaDigestHeld`: the checked matrix's claim, zero, or the first child holding it). `mPost_w1` calls
`statement_digest` on the claim lists' digests, it and `defer_stmt` (`statement_digest_callAtA`,
`statementDigest_parts`). `mPost_w2` checks the header against the returns. `wPost_hyp`: from
`PreInv … (mTop m) Qs`, `mPost`'s windows' hypotheses, ending in a state whose posts are
`Qs ++ [FreePost]` and whose `O` gives `main`'s words.

`MainFinalAt al k s w cover`: the final condition, `main`'s pops against `honestPushes` and every
node exact, from the callees' posts. `mainPostAt_of_final`, `MainFinalFromCallees`,
`mainWinHypFromCallees_of_final : MainFinalFromCallees al k → MainWinHypFromCallees al k`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The picked DA digest -/

theorem digestCells_zero : Prover.digestCells zeroDigest = [0, 0] := by decide +kernel

set_option linter.unusedSimpArgs false in
/-- **The picked DA digest is the node's**: a child's at `da_pick < n`, the own cells at `n`. -/
theorem daPick_cases {s : NodeStatement} {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w) :
    (∃ h : Prover.daPick s w < w.children.length,
      (w.children[Prover.daPick s w]'h).statement.claims.daDigest = s.claims.daDigest) ∨
    (Prover.daPick s w = w.children.length ∧ ownDaCells w = Prover.digestCells s.claims.daDigest) := by
  have hd := hr.2.1
  unfold DaDigestHeld at hd
  unfold Prover.daPick
  cases hm : w.daMatrix with
  | some p =>
    obtain ⟨c, mw⟩ := p
    rw [hm] at hd
    right
    simp only [hm, Option.isSome_some, Bool.true_or, ↓reduceIte, true_and]
    simp only [ownDaCells, hm, hd.1]
  | none =>
    rw [hm] at hd
    by_cases hz : s.claims.daDigest = zeroDigest
    · right
      simp only [hm, Option.isSome_none, hz, beq_self_eq_true, Bool.or_true, ↓reduceIte, true_and]
      simp only [ownDaCells, hm, digestCells_zero]
    · have hz' : (s.claims.daDigest == zeroDigest) = false := by simpa using hz
      simp only [hm, Option.isSome_none, hz', Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      rcases hd with hd | ⟨ch, hch, he⟩
      · exact (hz hd).elim
      cases hf : List.findIdx? (fun c => c.statement.claims.daDigest == s.claims.daDigest) w.children with
      | none =>
        have := List.findIdx?_eq_none_iff.mp hf ch hch
        simp [he] at this
      | some i =>
        left
        obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        simp only [Option.getD_some]
        exact ⟨hi, by simpa using hp⟩

/-- **`da_digests[da_pick]` holds the node's DA digest** on a memory holding `main`'s words. -/
theorem daPick_cells {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd : Reader}
    (hr : NodeRelation guestBytecode guestSeed s w) (h : HoldsWords rd (mainWords s w cover)) :
    ReadsAt rd (ptrAt (mBase (mainCounts s w) 4 + 2 * Prover.daPick s w))
      (Prover.digestCells s.claims.daDigest) := by
  have r4 := (main_runs h).1
  rcases daPick_cases hr with ⟨hi, he⟩ | ⟨he, ho⟩
  · have := readsAt_block (n := 2) (fun a _ => rfl) (readsAt_append'.mp r4).1 hi
    rwa [he] at this
  · have h2 := (readsAt_append'.mp r4).2
    rw [dFlat_length, ptrAt_mul_pow, ho] at h2
    rw [he]; exact h2

/-! ## The evaluation memory's header -/

theorem mRd0_header {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs)
    (hb : (mainCounts s w).sx + (mainCounts s w).ss < 2 ^ 19) (hn : (mainCounts s w).nc ≤ 16) :
    mainPreR s (mRd0 s w cover) := by
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
  have h0 := hall _ List.mem_cons_self
  have e : ofK (addressOfIndex 0) = (1 : E) := by rw [← Value.gen_pow_eq_ofK, pow_zero]
  rw [e] at h0
  exact h0

/-! ## The atoms -/

set_option maxRecDepth 200000 in
theorem post_shapes : atomsOf ((mPost.drop 0).take 2) = [.load (.n 452) (.n 420) 0, .load (.n 453) (.n 420) 1] ∧
    atomsOf ((mPost.drop 3).take 6) = [.const (.n 456) (word 1 0), .load (.n 457) (.n 456) 0,
      .assertEq (.n 457) (.n 454), .const (.n 458) (word 2 0), .load (.n 459) (.n 458) 0,
      .assertEq (.n 459) (.n 455)] := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem post_mem : Atom.load (.n 452) (.n 420) 0 ∈ atomsOf mPost ∧ Atom.load (.n 452) (.n 420) 0 ∉ storesOf 452 mPost ∧
    Atom.load (.n 453) (.n 420) 1 ∈ atomsOf mPost ∧ Atom.load (.n 453) (.n 420) 1 ∉ storesOf 452 mPost ∧
    Atom.const (.n 456) (word 1 0) ∈ atomsOf mPost ∧ Atom.load (.n 457) (.n 456) 0 ∈ atomsOf mPost ∧
    Atom.load (.n 457) (.n 456) 0 ∉ storesOf 452 mPost ∧ Atom.const (.n 458) (word 2 0) ∈ atomsOf mPost ∧
    Atom.load (.n 459) (.n 458) 0 ∈ atomsOf mPost ∧ Atom.load (.n 459) (.n 458) 0 ∉ storesOf 452 mPost ∧
    Atom.mul (.n 419) (.n 410) (.n 410) ∈ atomsOf mMid ∧ Atom.mul (.n 420) (.n 380) (.n 419) ∈ atomsOf mMid := by
  decide +kernel

theorem post_call_mem :
    W1.call (.call "statement_digest" [.n 26, .n 27, .n 54, .n 55, .n 56, .n 57, .n 452, .n 453, .n 421]
      [.n 454, .n 455]) ∈ wPost := List.mem_cons_of_mem _ List.mem_cons_self

theorem pre_cld_mem : W1.call (.call "claim_list_digest" [.n 52, .n 0] [.n 54, .n 55]) ∈ wPre ∧
    W1.call (.call "claim_list_digest" [.n 53, .n 3] [.n 56, .n 57]) ∈ wPre := by
  unfold wPre mPre_w3 mPre_w4
  exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))⟩

theorem mPost_good {rd : Reader} {w : ℕ → E} {a : Atom} (h : a ∈ atomsOf mPost) :
    Good rd (storesOf 452 mPost) w (mVal rd w) a :=
  mVal_goodPost (.atom a) (atom_mem_of_atomsOf h)

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}

/-- `mPost`'s values on the honest oracle. -/
theorem post_vals (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs) :
    mVal (mRd0 s w cover) (mOrc al s w) (.n 420) =
        ptrAt (mBase (mainCounts s w) 4 + 0 + (Prover.daPick s w + Prover.daPick s w)) ∧
      [mVal (mRd0 s w cover) (mOrc al s w) (.n 452), mVal (mRd0 s w cover) (mOrc al s w) (.n 453)] =
        Prover.digestCells s.claims.daDigest ∧
      mVal (mRd0 s w cover) (mOrc al s w) (.n 456) = 1 ∧ mVal (mRd0 s w cover) (mOrc al s w) (.n 458) = gen ∧
      mVal (mRd0 s w cover) (mOrc al s w) (.n 457) = mVal (mRd0 s w cover) (mOrc al s w) (.n 454) ∧
      mVal (mRd0 s w cover) (mOrc al s w) (.n 459) = mVal (mRd0 s w cover) (mOrc al s w) (.n 455) := by
  obtain ⟨m452, n452, m453, n453, m456, m457, n457, m458, m459, n459, m419, m420⟩ := post_mem
  have hrets := mVal_goodPost (rd := mRd0 s w cover) (w := mOrc al s w) _ (by rw [← wPost_flat]; exact mem_flat_call post_call_mem)
  have s410 := (mid2_vals (al := al) hr hlim hl).2.2.1
  have s419 : mVal (mRd0 s w cover) (mOrc al s w) (.n 419) = gen ^ (Prover.daPick s w + Prover.daPick s w) :=
    pmul (good_mul (mMid_good m419) (by norm_num) (by norm_num)) s410 s410
  have s420 : mVal (mRd0 s w cover) (mOrc al s w) (.n 420) =
      ptrAt (mBase (mainCounts s w) 4 + 0 + (Prover.daPick s w + Prover.daPick s w)) := by
    rw [good_mul (mMid_good m420) (by norm_num) (by norm_num), s419, mOrc_380]
    exact ptrAt_mul_pow _ _
  have hH := mRd0_holds hl (slots_lt hr hlim) (nc_le hlim)
  have hP := daPick_cells (cover := cover) hr hH
  have e2 : 2 * Prover.daPick s w = 0 + (Prover.daPick s w + Prover.daPick s w) := by omega
  rw [e2, ← Nat.add_assoc] at hP
  have s456 : mVal (mRd0 s w cover) (mOrc al s w) (.n 456) = 1 :=
    (show mVal (mRd0 s w cover) (mOrc al s w) (.n 456) = word 1 0 from mPost_good m456).trans word_one
  have s458 : mVal (mRd0 s w cover) (mOrc al s w) (.n 458) = gen :=
    (show mVal (mRd0 s w cover) (mOrc al s w) (.n 458) = word 2 0 from mPost_good m458).trans word_gen
  have hhd := mRd0_header (s := s) (w := w) (cover := cover) hl (slots_lt hr hlim) (nc_le hlim)
  have r454 : mVal (mRd0 s w cover) (mOrc al s w) (.n 454) = (digestHalves (statementDigest guestSeed s)).1 :=
    hrets (.n 454) List.mem_cons_self
  have r455 : mVal (mRd0 s w cover) (mOrc al s w) (.n 455) = (digestHalves (statementDigest guestSeed s)).2 :=
    hrets (.n 455) (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨s420, ?_, s456, s458, ?_, ?_⟩
  · have g452 : Good (mRd0 s w cover) (storesOf 452 mPost) (mOrc al s w) (mVal (mRd0 s w cover) (mOrc al s w))
        (.load (.n 452) (.n 420) 0) := mPost_good m452
    have g453 : Good (mRd0 s w cover) (storesOf 452 mPost) (mOrc al s w) (mVal (mRd0 s w cover) (mOrc al s w))
        (.load (.n 453) (.n 420) 1) := mPost_good m453
    rcases g452 with g452 | g452
    · exact (n452 g452).elim
    rcases g453 with g453 | g453
    · exact (n453 g453).elim
    rw [g452, g453, s420, rdAt_of_loadHolds (hP 0 (by simp [Prover.digestCells])),
      rdAt_of_loadHolds (hP 1 (by simp [Prover.digestCells]))]
    rfl
  · have g457 : Good (mRd0 s w cover) (storesOf 452 mPost) (mOrc al s w) (mVal (mRd0 s w cover) (mOrc al s w))
        (.load (.n 457) (.n 456) 0) := mPost_good m457
    rcases g457 with g457 | g457
    · exact (n457 g457).elim
    rw [g457, s456, rdAt_of_loadHolds (hhd 0 (by simp [Prover.digestCells])), r454]
    rfl
  · have g459 : Good (mRd0 s w cover) (storesOf 452 mPost) (mOrc al s w) (mVal (mRd0 s w cover) (mOrc al s w))
        (.load (.n 459) (.n 458) 0) := mPost_good m459
    rcases g459 with g459 | g459
    · exact (n459 g459).elim
    have h1 := (loadHolds_mul_gen_pow _ 1 1 0 _).mpr (hhd 1 (by simp [Prover.digestCells]))
    rw [one_mul, pow_one] at h1
    rw [g459, s458, rdAt_of_loadHolds h1, r455]
    rfl


set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
/-- **`mPost`'s windows' hypotheses** from `PreInv … (mTop m) Qs`, to a state whose posts gain
`statement_digest`'s `FreePost` and whose `O` gives `main`'s words. -/
theorem wPost_hyp {es : List Ev} {st : St} {K : St → Prop} {Qs : List (Reader → Tree → Prop)}
    (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w)
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs)
    (hst : PreInv al s w cover (mTop (mainCounts s w)) Qs st)
    (hrest : ∀ st', st'.Qs = Qs ++ [FreePost] → (∀ rd, st'.O rd → HoldsWords rd (mainWords s w cover)) → K st') :
    WinsHypT B2C.fs al B2C.cert k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) (· < 2) (mainPreR s) wPost st K := by
  obtain ⟨s420, s452, s456, s458, s457, s459⟩ := post_vals (al := al) hr hlim hl
  have e452 : mVal (mRd0 s w cover) (mOrc al s w) (.n 452) = (digestHalves s.claims.daDigest).1 := by
    simp only [Prover.digestCells, List.cons.injEq] at s452; exact s452.1
  have e453 : mVal (mRd0 s w cover) (mOrc al s w) (.n 453) = (digestHalves s.claims.daDigest).2 := by
    simp only [Prover.digestCells, List.cons.injEq] at s452; exact s452.2.1
  have cc := claimCells_of hr hok
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, bt⟩ := mBase_eqs (mainCounts s w)
  have h2 := fs_main_ge
  have hdp := daPick_le s w
  have hn := nc_le hlim
  obtain ⟨t0, t2⟩ := post_shapes
  have hrets := mVal_goodPost (rd := mRd0 s w cover) (w := mOrc al s w) _
    (by rw [← wPost_flat]; exact mem_flat_call post_call_mem)
  have r454 : mVal (mRd0 s w cover) (mOrc al s w) (.n 454) = (digestHalves (statementDigest guestSeed s)).1 :=
    hrets (.n 454) List.mem_cons_self
  have r455 : mVal (mRd0 s w cover) (mOrc al s w) (.n 455) = (digestHalves (statementDigest guestSeed s)).2 :=
    hrets (.n 455) (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨-, -, -, -, -, mfs⟩ := mid1_mem
  have h26 : mVal (mRd0 s w cover) (mOrc al s w) (.n 26) = mOrc al s w 26 := mPre_good mfs (.n 26) List.mem_cons_self
  have h27 : mVal (mRd0 s w cover) (mOrc al s w) (.n 27) = mOrc al s w 27 :=
    mPre_good mfs (.n 27) (List.mem_cons_of_mem _ List.mem_cons_self)
  have h54 : mVal (mRd0 s w cover) (mOrc al s w) (.n 54) = mOrc al s w 54 :=
    mPre_call_rets pre_cld_mem.1 (.n 54) List.mem_cons_self
  have h55 : mVal (mRd0 s w cover) (mOrc al s w) (.n 55) = mOrc al s w 55 :=
    mPre_call_rets pre_cld_mem.1 (.n 55) (List.mem_cons_of_mem _ List.mem_cons_self)
  have h56 : mVal (mRd0 s w cover) (mOrc al s w) (.n 56) = mOrc al s w 56 :=
    mPre_call_rets pre_cld_mem.2 (.n 56) List.mem_cons_self
  have h57 : mVal (mRd0 s w cover) (mOrc al s w) (.n 57) = mOrc al s w 57 :=
    mPre_call_rets pre_cld_mem.2 (.n 57) (List.mem_cons_of_mem _ List.mem_cons_self)
  have p0 : (1 : E) = ptrAt 0 := by rw [ptrAt, ← Value.gen_pow_eq_ofK, pow_zero]
  have p1 : gen = ptrAt 1 := by rw [ptrAt, ← Value.gen_pow_eq_ofK, pow_one]
  unfold wPost mPost_w0 mPost_w1 mPost_w2
  rw [WinsHypT]
  refine ⟨?_, ?_⟩
  · -- `da_digests[da_pick]`
    rw [t0]
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro A hA
      simp only [loadAddrs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, Ev.loadAddr?,
        List.mem_cons, List.not_mem_nil, or_false, s420] at hA
      rcases hA with rfl | rfl <;> rw [Main.addr_ofK] <;> exact ⟨_, rfl, Or.inl (own_main (by omega) (by omega))⟩
    · rw [heapHintAddrs_noHeap (by decide)]
      intro A hA; simp at hA
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> trivial
    · intro rd _ _ hOr x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      have hP := daPick_cells hr (hst.hO rd hOr).1
      rw [show 2 * Prover.daPick s w = 0 + (Prover.daPick s w + Prover.daPick s w) by omega, ← Nat.add_assoc] at hP
      rcases hx with rfl | rfl
      · show LoadHolds rd _ 0 _
        rw [s420, e452]; exact hP 0 (by simp [Prover.digestCells])
      · show LoadHolds rd _ 1 _
        rw [s420, e453]; exact hP 1 (by simp [Prover.digestCells])
  · -- `statement_digest`
    rw [WinsHypT]
    refine ⟨"statement_digest", FreePost, B2C.fs "statement_digest",
      allocBase (al "statement_digest") st.kc + B2C.fs "statement_digest",
      fun i => mBase (mainCounts s w) 9 + 0 ≤ i ∧ i < mBase (mainCounts s w) 9 + 0 + 26, fun _ => False,
      fun _ => True, rfl, fun i hi => Or.inl (Or.inr (own_main (by omega) (by omega))), ?_, fun _ => by
        dsimp only
        have h0 := stepB_ge
        have h1 := Memory.allocBase_le (al "statement_digest") st.kc
        have h2 := B2C.fs_lt "statement_digest"
        omega, ?_⟩
    · refine statement_digest_callAtA coreProgram_wf k rfl ?_ ?_ _ _
      · simp only [argsOf, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero]
        exact mOrc_421
      · rintro rd ⟨-, hOr⟩
        have hW := (hst.hO rd hOr).1
        simp only [argsOf, retsOf, List.map_cons, List.map_nil]
        rw [h26, h27, h54, h55, h56, h57, e452, e453, mOrc_421, r454, r455, Nat.add_zero]
        refine ⟨s.deferredClaim.cells, cc.own, (main_runs hW).2.2.2.2.2, ?_⟩
        have hsd : statementDigest guestSeed s = keccak256 (Digest.stmtBytes [mOrc al s w 26, mOrc al s w 27, mOrc al s w 54,
            mOrc al s w 55, mOrc al s w 56, mOrc al s w 57, (digestHalves s.claims.daDigest).1,
            (digestHalves s.claims.daDigest).2] s.deferredClaim.cells) :=
          statementDigest_parts (digestBytes_of_cells rfl) (digestBytes_of_cells rfl) (digestBytes_of_cells rfl)
            (digestBytes_of_cells rfl) rfl
        rw [← hsd]
        rfl
    · -- the header
      rw [WinsHypT, t2]
      refine ⟨⟨rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro A hA
        simp only [loadAddrs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, Ev.loadAddr?,
          List.mem_cons, List.not_mem_nil, or_false, s456, s458] at hA
        rcases hA with rfl | rfl
        · rw [p0, Main.addr_ofK]; exact ⟨_, rfl, Or.inr (Or.inl (by norm_num))⟩
        · rw [p1, Main.addr_ofK]; exact ⟨_, rfl, Or.inr (Or.inl (by norm_num))⟩
      · rw [heapHintAddrs_noHeap (by decide)]
        intro A hA; simp at hA
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · exact pureT_triv rfl
        · trivial
        · show _ + _ = 0
          rw [s457]; exact CharTwo.add_self_eq_zero _
        · exact pureT_triv rfl
        · trivial
        · show _ + _ = 0
          rw [s459]; exact CharTwo.add_self_eq_zero _
      · intro rd _ hp _ x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · trivial
        · show LoadHolds rd _ 0 _
          rw [s456, s457, r454]; exact hp 0 (by simp [Prover.digestCells])
        · trivial
        · trivial
        · show LoadHolds rd _ 0 _
          rw [s458, s459, r455]
          have := (loadHolds_mul_gen_pow rd 1 1 0 _).mpr (hp 1 (by simp [Prover.digestCells]))
          rwa [one_mul, pow_one] at this
        · trivial
      · rw [WinsHypT]
        exact hrest _ (by show st.Qs ++ [FreePost] = _; rw [hst.hQ]) fun rd h => (hst.hO rd h.1).1

end

/-! ## What is left: the final condition -/

/-- **`main`'s final condition** at the honest oracle, on every state `mPost` ends in (its posts the
callees', `O` giving `main`'s words): `main`'s pops the honest pushes stream by stream, every node
exact. -/
def MainFinalAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) (cover : List E) : Prop :=
  ∀ st : St, st.Qs = qPre s w ++ qDa w ++ [qIf (mainCounts s w).nc (PopsPost (mKidPushes s w))] ++ qAgg w ++
      [FreePost] → (∀ rd, st.O rd → HoldsWords rd (mainWords s w cover)) →
    ∀ rd, LowDef k rd → mainPreR s rd → st.O rd → ∀ ts,
      Tree.KidsValid coreProgram rd (over mTL (mVal (mRd0 s w cover) (mOrc al s w)) rd)
        (calls (mEs (mVal (mRd0 s w cover) (mOrc al s w)))) ts →
      KidsPost rd st.Qs (calls (mEs (mVal (mRd0 s w cover) (mOrc al s w)))) ts →
      mainPostR s w rd (.node "main" (over mTL (mVal (mRd0 s w cover) (mOrc al s w)) rd) (mainCounts s w).bufs ts)

theorem mainPostAt_of_final {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w)
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs) (h : MainFinalAt al k s w cover) :
    MainPostAt al k s w cover :=
  fun _ hst => wPost_hyp hr hlim hok hl hst h

/-- **What is left of `main`'s window**: its final condition on every node and every coverage table the
callees' fields hold on. -/
def MainFinalFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  17 ≤ k → k ≤ 23 → MainCalleesA al k → VsCompleteHypA al k guestBytecode guestSeed →
    ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w →
      ChildrenOk guestBytecode guestSeed w → ∀ cover : List E,
        cover.length = (mainCounts s w).sx + (mainCounts s w).ss → MainCalleesAt al k s w cover →
        MainFinalAt al k s w cover

theorem mainWinHypFromCallees_of_final {al : String → Bool} {k : ℕ} (h : MainFinalFromCallees al k) :
    MainWinHypFromCallees al k :=
  mainWinHypFromCallees_of_post fun hk hk' hc hvs s w hr hlim hok cover hlen hat => by
    have cc := claimCells_of hr hok
    exact mainPostAt_of_final hr hlim hok (mainLists_length hlen cc.fresh cc.carried cc.own)
      (h hk hk' hc hvs s w hr hlim hok cover hlen hat)

/-- **`main`'s window from its callees and its final condition.** -/
theorem mainWindowFromCallees_of_final {al : String → Bool} {k : ℕ} (h : MainFinalFromCallees al k) :
    MainWindowFromCallees al k :=
  mainWindowFromCallees_of_hyp (mainWinHypFromCallees_of_final h)

end
end LeanVM.Guest.Complete
