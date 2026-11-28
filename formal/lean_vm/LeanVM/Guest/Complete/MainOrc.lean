/-
  LeanVM.Guest.Complete.MainOrc

  `main`'s honest oracle, its sizes on the forward valuation, and its `HeapBuf`s.
-/

module

public import LeanVM.Guest.Complete.MainWins
public import LeanVM.Guest.Complete.MainRunFacts
public import LeanVM.Guest.Complete.MainWords
import LeanVM.Guest.B1.Main.Plan
import LeanVM.Guest.Complete.CoverageEq
import LeanVM.Guest.BatchConsts

/-!
# `main`'s honest oracle and buffers

* **The oracle.** `mOrc al s w`: the counts `g^n` at `.n 0 ..< .n 8`, the seed's halves, the exponent
  tables' pointer (`exponent_tables`' return), the `HeapBuf` pointers at `main`'s buffers' bases, the
  claim lists' digests, `da_verify`'s returns (`daRets`), `g^daPick`, a leaf's bytecode value and the
  statement's digest. `mRd0 s w cover`: the memory holding `main`'s words and the header, and nothing
  else.
* **Sizes.** On `mVal rd (mOrc al s w)`, the `HeapBuf` sizes are `g^` of `MainCounts.bufs`
  (`mOrc_sizes`), and `main`'s events allocate exactly `MainCounts.bufs` (`mAllocs`), the slots below
  `2^19` and at most `16` children (`slots_lt`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

noncomputable section

/-! ## The oracle -/

/-- `da_verify`'s returns: the checked claim's root halves and challenge, or zeros. -/
def daRets (w : NodeWitness) : List E :=
  match w.daMatrix with
  | some (c, _) => Prover.digestCells c.daRoot ++ [c.membershipChallenge]
  | none => [0, 0, 0]

/-- **`main`'s honest oracle**: what its hints, `HeapBuf`s and callees give. -/
def mOrc (al : String → Bool) (s : NodeStatement) (w : NodeWitness) (i : ℕ) : E :=
  let m := mainCounts s w
  match i with
  | 0 => gen ^ m.nlx
  | 1 => gen ^ m.nxd
  | 2 => gen ^ m.nrx
  | 3 => gen ^ m.nls
  | 4 => gen ^ m.nsd
  | 5 => gen ^ m.nrs
  | 6 => gen ^ m.nc
  | 7 => gen ^ m.nd
  | 26 => (digestHalves guestSeed).1
  | 27 => (digestHalves guestSeed).2
  | 51 => ptrAt (mGS al m)
  | 52 => mPtr m 0 0
  | 53 => mPtr m 1 0
  | 54 => (digestHalves (claimListDigest xmssPublicKeyBytes s.claims.xmss)).1
  | 55 => (digestHalves (claimListDigest xmssPublicKeyBytes s.claims.xmss)).2
  | 56 => (digestHalves (claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs)).1
  | 57 => (digestHalves (claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs)).2
  | 64 => mPtr m 2 0
  | 66 => mPtr m 3 0
  | 380 => mPtr m 4 0
  | 385 => (daRets w).getD 0 0
  | 386 => (daRets w).getD 1 0
  | 387 => (daRets w).getD 2 0
  | 398 => mPtr m 5 0
  | 399 => mPtr m 6 0
  | 400 => mPtr m 7 0
  | 403 => mPtr m 8 0
  | 410 => gen ^ Prover.daPick s w
  | 421 => mPtr m 9 0
  | 424 => s.deferredClaim.bytecodeValue
  | 454 => (digestHalves (statementDigest guestSeed s)).1
  | 455 => (digestHalves (statementDigest guestSeed s)).2
  | _ => 0

/-- **The evaluation memory**: `main`'s words and the header's digest at `0`, `1`, nothing else. -/
def mRd0 (s : NodeStatement) (w : NodeWitness) (cover : List E) : Reader :=
  rdW ((0, Prover.digestCells (statementDigest guestSeed s)) :: mainWords s w cover)

/-! ## The bounds -/

/-- **The slots** are below `2^19` on a node within the deployed limits. -/
theorem slots_lt {s : NodeStatement} {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w)
    (hl : DeployedLimits s w) : (mainCounts s w).sx + (mainCounts s w).ss < 2 ^ 19 := by
  have h1 := B1.Main.planSlots_eq (s := s) (w := w) hr.1
  have h2 := B1.Main.coverage_eq s w
  have h3 := coverageSlots_lt_of_budget hl.withinMemoryBudget
  have ex : (xPlan s w).duplicates = (B1.Main.xPlan s w).duplicates := (coveragePlan_eq _ _ _).1
  have es : (sPlan s w).duplicates = (B1.Main.sPlan s w).duplicates := (coveragePlan_eq _ _ _).1
  have ex' : (mainCounts s w).nxd = (B1.Main.xPlan s w).duplicates.length := congrArg List.length ex
  have es' : (mainCounts s w).nsd = (B1.Main.sPlan s w).duplicates.length := congrArg List.length es
  simp only [List.length_append] at h2
  have e1 : (mainCounts s w).nlx = s.claims.xmss.length := rfl
  have e2 : (mainCounts s w).nls = s.claims.sphincs.length := rfl
  show (mainCounts s w).nlx + (mainCounts s w).nxd + ((mainCounts s w).nls + (mainCounts s w).nsd) < 2 ^ 19
  omega

/-- At most `16` children. -/
theorem nc_le {s : NodeStatement} {w : NodeWitness} (hl : DeployedLimits s w) : (mainCounts s w).nc ≤ 16 :=
  hl.children_le_sixteen

/-! ## `main`'s events -/

theorem allocs_slEvs (σ : Val) : ∀ ss : List Stmt, ss.all Stmt.straight = true →
    allocs σ (ss.flatMap (slEvs σ)) = (atomsOf ss).filterMap fun a => Ev.alloc? σ (.atom a)
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := allocs_slEvs σ ss h.2
    rw [List.flatMap_cons]
    unfold allocs at ih ⊢
    rw [List.filterMap_append, ih]
    cases s with
    | atom a =>
      simp only [slEvs, atomsOf, List.filterMap_cons, List.filterMap_nil]
      cases Ev.alloc? σ (.atom a) <;> rfl
    | call f args rets => rfl
    | callIf c f args =>
      simp only [slEvs, atomsOf]
      split <;> rfl
    | _ => simp [Stmt.straight] at h

/-- An atom allocating a `HeapBuf`. -/
def isAllocA : Atom → Bool
  | .hint (.alloc _ _) => true
  | .hint (.allocDyn _ _) => true
  | _ => false

theorem filterMap_alloc (σ : Val) : ∀ as : List Atom,
    as.filterMap (fun a => Ev.alloc? σ (.atom a)) = (as.filter isAllocA).filterMap fun a => Ev.alloc? σ (.atom a)
  | [] => rfl
  | a :: as => by
    have ih := filterMap_alloc σ as
    by_cases ha : isAllocA a = true
    · simp only [List.filter_cons_of_pos ha, List.filterMap_cons, ih]
    · have hn : Ev.alloc? σ (.atom a) = none := by
        cases a with
        | hint h => cases h <;> first | rfl | simp [isAllocA] at ha
        | _ => rfl
      simp only [List.filter_cons_of_neg ha, List.filterMap_cons, hn]
      exact ih

set_option maxRecDepth 200000 in
theorem main_straight : mPre.all Stmt.straight = true ∧ mDa.all Stmt.straight = true ∧
    mDaZ.all Stmt.straight = true ∧ mMid.all Stmt.straight = true ∧ mLeaf.all Stmt.straight = true ∧
    mAgg.all Stmt.straight = true ∧ mPost.all Stmt.straight = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem main_allocAtoms :
    (atomsOf mPre).filter isAllocA = [.hint (.allocDyn (.n 52) (.n 29)), .hint (.allocDyn (.n 53) (.n 31)),
      .hint (.allocDyn (.n 64) (.n 24)), .hint (.alloc (.n 66) 256), .hint (.allocDyn (.n 380) (.n 34))] ∧
    (atomsOf mMid).filter isAllocA = [.hint (.allocDyn (.n 398) (.n 35)), .hint (.allocDyn (.n 399) (.n 44)),
      .hint (.allocDyn (.n 400) (.n 50)), .hint (.allocDyn (.n 403) (.n 402)), .hint (.alloc (.n 421) 26)] ∧
    (atomsOf mDa).filter isAllocA = [] ∧ (atomsOf mDaZ).filter isAllocA = [] ∧
    (atomsOf mLeaf).filter isAllocA = [] ∧ (atomsOf mAgg).filter isAllocA = [] ∧
    (atomsOf mPost).filter isAllocA = [] := by
  decide +kernel

/-- **`main`'s events**: its straight parts' and its taken arms'. -/
theorem mEs_eq (σ : Val) : mEs σ = mPre.flatMap (slEvs σ) ++ .inK (.n 384) ::
    ((if σ (.n 384) = 0 then mDa else mDaZ).flatMap (slEvs σ) ++ (mMid.flatMap (slEvs σ) ++ .inK (.n 423) ::
      ((if σ (.n 423) = 0 then mLeaf else mAgg).flatMap (slEvs σ) ++ mPost.flatMap (slEvs σ)))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := main_straight
  have hz : (if σ (.n 384) = 0 then mDa else mDaZ).all Stmt.straight = true := by
    split
    · exact h2
    · exact h3
  have hl : (if σ (.n 423) = 0 then mLeaf else mAgg).all Stmt.straight = true := by
    split
    · exact h5
    · exact h6
  have i1 : walk σ [.ite (.n 384) mDa mDaZ] =
      .fall (.inK (.n 384) :: (if σ (.n 384) = 0 then mDa else mDaZ).flatMap (slEvs σ)) := by
    rw [walk_singleC, walk1, ← apply_ite (walk σ), walk_straight_fall σ _ hz]
    rfl
  have i2 : walk σ [.ite (.n 423) mLeaf mAgg] =
      .fall (.inK (.n 423) :: (if σ (.n 423) = 0 then mLeaf else mAgg).flatMap (slEvs σ)) := by
    rw [walk_singleC, walk1, ← apply_ite (walk σ), walk_straight_fall σ _ hl]
    rfl
  rw [mEs, mainSs, walk_append, walk_append, walk_append, walk_append, walk_straight_fall σ _ h1, i1,
    walk_straight_fall σ _ h4, i2, walk_straight_fall σ _ h7]
  simp [Out.seq, Out.pre, outEvs]

/-- **`main`'s `HeapBuf` sizes** on a valuation, from its size words. -/
theorem mAllocs_eq (σ : Val) : allocs σ (mEs σ) =
    [logG (σ (.n 29)), logG (σ (.n 31)), logG (σ (.n 24)), 256, logG (σ (.n 34)), logG (σ (.n 35)),
      logG (σ (.n 44)), logG (σ (.n 50)), logG (σ (.n 402)), 26] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := main_straight
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := main_allocAtoms
  have hz : allocs σ ((if σ (.n 384) = 0 then mDa else mDaZ).flatMap (slEvs σ)) = [] := by
    split
    · rw [allocs_slEvs σ _ h2, filterMap_alloc σ (atomsOf mDa), a3]; rfl
    · rw [allocs_slEvs σ _ h3, filterMap_alloc σ (atomsOf mDaZ), a4]; rfl
  have hl : allocs σ ((if σ (.n 423) = 0 then mLeaf else mAgg).flatMap (slEvs σ)) = [] := by
    split
    · rw [allocs_slEvs σ _ h5, filterMap_alloc σ (atomsOf mLeaf), a5]; rfl
    · rw [allocs_slEvs σ _ h6, filterMap_alloc σ (atomsOf mAgg), a6]; rfl
  have app : ∀ es es', allocs σ (es ++ es') = allocs σ es ++ allocs σ es' := fun _ _ => List.filterMap_append
  have ck : ∀ c es, allocs σ (.inK c :: es) = allocs σ es := fun _ _ => rfl
  rw [mEs_eq, app, ck, app, hz, app, ck, app, hl, allocs_slEvs σ _ h1, filterMap_alloc σ (atomsOf mPre), a1,
    allocs_slEvs σ _ h4, filterMap_alloc σ (atomsOf mMid), a2, allocs_slEvs σ _ h7,
    filterMap_alloc σ (atomsOf mPost), a7]
  rfl

set_option maxRecDepth 200000 in
theorem main_callCounts : (mPre.filterMap Stmt.callS).length = 7 ∧ (mDa.filterMap Stmt.callS).length = 1 ∧
    (mDaZ.filterMap Stmt.callS).length = 0 ∧ (mMid.filterMap Stmt.callS).length = 1 ∧
    (mLeaf.filterMap Stmt.callS).length = 0 ∧ (mAgg.filterMap Stmt.callS).length = 1 ∧
    (mPost.filterMap Stmt.callS).length = 1 := by
  decide +kernel

/-- **`main` calls at most `11` callees** on every valuation. -/
theorem mCalls_le (σ : Val) : (calls (mEs σ)).length ≤ 12 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := main_straight
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := main_callCounts
  have app : ∀ es es', calls (es ++ es') = calls es ++ calls es' := fun _ _ => List.filterMap_append
  have ck : ∀ c es, calls (.inK c :: es) = calls es := fun _ _ => rfl
  have hn : ∀ pre : List Stmt, pre.all Stmt.straight = true →
      (calls (pre.flatMap (slEvs σ))).length = (pre.filterMap Stmt.callS).length := fun pre h => by
    rw [(straight_parts σ pre h).2.2.2, List.length_map]
  have hz : (calls ((if σ (.n 384) = 0 then mDa else mDaZ).flatMap (slEvs σ))).length ≤ 1 := by
    split
    · rw [hn _ h2, c2]
    · rw [hn _ h3, c3]; omega
  have hl : (calls ((if σ (.n 423) = 0 then mLeaf else mAgg).flatMap (slEvs σ))).length ≤ 1 := by
    split
    · rw [hn _ h5, c5]; omega
    · rw [hn _ h6, c6]
  rw [mEs_eq]
  simp only [app, ck, List.length_append]
  rw [hn _ h1, hn _ h4, hn _ h7, c1, c4, c7]
  omega

/-! ## The sizes on the forward valuation -/

theorem good_mul {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d x y : ℕ}
    (h : Good rd S w σ (.mul (.n d) (.n x) (.n y))) (hx : x < d) (hy : y < d) : σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [Good] at h
  split at h
  · exact h
  · rename_i hne
    exact (hne ⟨hx, hy⟩).elim

theorem pow_eq_of {σ : Val} {d : V} {a b : ℕ} (h : σ d = gen ^ a) (e : a = b) : σ d = gen ^ b := e ▸ h

theorem pmul {σ : Val} {d x y : V} {a b : ℕ} (h : σ d = σ x * σ y) (hx : σ x = gen ^ a) (hy : σ y = gen ^ b) :
    σ d = gen ^ (a + b) := by
  rw [h, hx, hy, pow_add]

set_option maxRecDepth 200000 in
theorem mSizes_mem1 :
    Atom.mul (.n 22) (.n 0) (.n 1) ∈ atomsOf mPre ∧ Atom.mul (.n 23) (.n 3) (.n 4) ∈ atomsOf mPre ∧
      Atom.mul (.n 24) (.n 22) (.n 23) ∈ atomsOf mPre ∧ Atom.mul (.n 28) (.n 22) (.n 22) ∈ atomsOf mPre ∧
      Atom.mul (.n 29) (.n 28) (.n 28) ∈ atomsOf mPre ∧ Atom.mul (.n 30) (.n 23) (.n 23) ∈ atomsOf mPre ∧
      Atom.mul (.n 31) (.n 30) (.n 30) ∈ atomsOf mPre := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem mSizes_mem2 :
    Atom.const (.n 32) (word 2 0) ∈ atomsOf mPre ∧ Atom.mul (.n 33) (.n 6) (.n 32) ∈ atomsOf mPre ∧
      Atom.mul (.n 34) (.n 33) (.n 33) ∈ atomsOf mPre ∧ Atom.mul (.n 35) (.n 6) (.n 6) ∈ atomsOf mPre := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem mSizes_mem3 :
    Atom.mul (.n 36) (.n 6) (.n 6) ∈ atomsOf mPre ∧ Atom.mul (.n 37) (.n 36) (.n 6) ∈ atomsOf mPre ∧
      Atom.mul (.n 38) (.n 37) (.n 37) ∈ atomsOf mPre ∧ Atom.mul (.n 39) (.n 38) (.n 38) ∈ atomsOf mPre ∧
      Atom.mul (.n 40) (.n 39) (.n 6) ∈ atomsOf mPre := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem mSizes_mem4 :
    Atom.mul (.n 41) (.n 40) (.n 40) ∈ atomsOf mPre ∧ Atom.mul (.n 42) (.n 41) (.n 6) ∈ atomsOf mPre ∧
      Atom.mul (.n 43) (.n 42) (.n 42) ∈ atomsOf mPre ∧ Atom.mul (.n 44) (.n 43) (.n 6) ∈ atomsOf mPre := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem mSizes_mem5 :
    Atom.mul (.n 45) (.n 6) (.n 6) ∈ atomsOf mPre ∧ Atom.mul (.n 46) (.n 45) (.n 6) ∈ atomsOf mPre ∧
      Atom.mul (.n 47) (.n 46) (.n 46) ∈ atomsOf mPre ∧ Atom.mul (.n 48) (.n 47) (.n 47) ∈ atomsOf mPre := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem mSizes_mem6 :
    Atom.mul (.n 49) (.n 48) (.n 6) ∈ atomsOf mPre ∧ Atom.mul (.n 50) (.n 49) (.n 49) ∈ atomsOf mPre ∧
      Atom.const (.n 401) (word 2 0) ∈ atomsOf mMid ∧ Atom.mul (.n 402) (.n 6) (.n 401) ∈ atomsOf mMid := by
  decide +kernel

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {rd : Reader}

/-- `main`'s counts on its honest oracle. -/
theorem mOrc_counts :
    mVal rd (mOrc al s w) (.n 0) = gen ^ (mainCounts s w).nlx ∧
      mVal rd (mOrc al s w) (.n 1) = gen ^ (mainCounts s w).nxd ∧
      mVal rd (mOrc al s w) (.n 2) = gen ^ (mainCounts s w).nrx ∧
      mVal rd (mOrc al s w) (.n 3) = gen ^ (mainCounts s w).nls ∧
      mVal rd (mOrc al s w) (.n 4) = gen ^ (mainCounts s w).nsd ∧
      mVal rd (mOrc al s w) (.n 5) = gen ^ (mainCounts s w).nrs ∧
      mVal rd (mOrc al s w) (.n 6) = gen ^ (mainCounts s w).nc ∧
      mVal rd (mOrc al s w) (.n 7) = gen ^ (mainCounts s w).nd :=
  ⟨mVal_meta (by norm_num), mVal_meta (by norm_num), mVal_meta (by norm_num), mVal_meta (by norm_num),
    mVal_meta (by norm_num), mVal_meta (by norm_num), mVal_meta (by norm_num), mVal_meta (by norm_num)⟩

/-- **`main`'s size words** on its honest oracle: the slots, and `g^` of each `HeapBuf`'s size. -/
theorem mOrc_sizes :
    mVal rd (mOrc al s w) (.n 22) = gen ^ (mainCounts s w).sx ∧ mVal rd (mOrc al s w) (.n 23) = gen ^ (mainCounts s w).ss ∧
      mVal rd (mOrc al s w) (.n 24) = gen ^ ((mainCounts s w).sx + (mainCounts s w).ss) ∧
      mVal rd (mOrc al s w) (.n 29) = gen ^ (4 * (mainCounts s w).sx) ∧
      mVal rd (mOrc al s w) (.n 31) = gen ^ (4 * (mainCounts s w).ss) ∧
      mVal rd (mOrc al s w) (.n 34) = gen ^ (2 * ((mainCounts s w).nc + 1)) ∧
      mVal rd (mOrc al s w) (.n 35) = gen ^ (2 * (mainCounts s w).nc) ∧
      mVal rd (mOrc al s w) (.n 44) = gen ^ (55 * (mainCounts s w).nc) ∧
      mVal rd (mOrc al s w) (.n 50) = gen ^ (26 * (mainCounts s w).nc) ∧
      mVal rd (mOrc al s w) (.n 402) = gen ^ ((mainCounts s w).nc + 1) := by
  obtain ⟨c0, c1, -, c3, c4, -, c6, -⟩ := mOrc_counts (al := al) (s := s) (w := w) (rd := rd)
  obtain ⟨m22, m23, m24, m28, m29, m30, m31⟩ := mSizes_mem1
  obtain ⟨k32, m33, m34, m35⟩ := mSizes_mem2
  obtain ⟨m36, m37, m38, m39, m40⟩ := mSizes_mem3
  obtain ⟨m41, m42, m43, m44⟩ := mSizes_mem4
  obtain ⟨m45, m46, m47, m48⟩ := mSizes_mem5
  obtain ⟨m49, m50, k401, m402⟩ := mSizes_mem6
  have gm : ∀ {d x y : ℕ}, Atom.mul (.n d) (.n x) (.n y) ∈ atomsOf mPre → x < d → y < d →
      mVal rd (mOrc al s w) (.n d) = mVal rd (mOrc al s w) (.n x) * mVal rd (mOrc al s w) (.n y) := fun h hx hy => good_mul (mPre_good h) hx hy
  have g1 : mVal rd (mOrc al s w) (.n 32) = gen ^ 1 := by rw [pow_one, ← word_gen]; exact mPre_good k32
  have g401 : mVal rd (mOrc al s w) (.n 401) = gen ^ 1 := by rw [pow_one, ← word_gen]; exact mMid_good k401
  have v22 := pmul (gm m22 (by norm_num) (by norm_num)) c0 c1
  have v23 := pmul (gm m23 (by norm_num) (by norm_num)) c3 c4
  have v24 := pmul (gm m24 (by norm_num) (by norm_num)) v22 v23
  have v28 := pmul (gm m28 (by norm_num) (by norm_num)) v22 v22
  have v29 := pmul (gm m29 (by norm_num) (by norm_num)) v28 v28
  have v30 := pmul (gm m30 (by norm_num) (by norm_num)) v23 v23
  have v31 := pmul (gm m31 (by norm_num) (by norm_num)) v30 v30
  have v33 := pmul (gm m33 (by norm_num) (by norm_num)) c6 g1
  have v34 := pmul (gm m34 (by norm_num) (by norm_num)) v33 v33
  have v35 := pmul (gm m35 (by norm_num) (by norm_num)) c6 c6
  have v36 := pmul (gm m36 (by norm_num) (by norm_num)) c6 c6
  have v37 := pmul (gm m37 (by norm_num) (by norm_num)) v36 c6
  have v38 := pmul (gm m38 (by norm_num) (by norm_num)) v37 v37
  have v39 := pmul (gm m39 (by norm_num) (by norm_num)) v38 v38
  have v40 := pmul (gm m40 (by norm_num) (by norm_num)) v39 c6
  have v41 := pmul (gm m41 (by norm_num) (by norm_num)) v40 v40
  have v42 := pmul (gm m42 (by norm_num) (by norm_num)) v41 c6
  have v43 := pmul (gm m43 (by norm_num) (by norm_num)) v42 v42
  have v44 := pmul (gm m44 (by norm_num) (by norm_num)) v43 c6
  have v45 := pmul (gm m45 (by norm_num) (by norm_num)) c6 c6
  have v46 := pmul (gm m46 (by norm_num) (by norm_num)) v45 c6
  have v47 := pmul (gm m47 (by norm_num) (by norm_num)) v46 v46
  have v48 := pmul (gm m48 (by norm_num) (by norm_num)) v47 v47
  have v49 := pmul (gm m49 (by norm_num) (by norm_num)) v48 c6
  have v50 := pmul (gm m50 (by norm_num) (by norm_num)) v49 v49
  have v402 := pmul (good_mul (mMid_good m402) (by norm_num) (by norm_num)) c6 g401
  have u : ∀ {d : V} {a b : ℕ}, mVal rd (mOrc al s w) d = gen ^ a →
      a = b → mVal rd (mOrc al s w) d = gen ^ b := fun h e => pow_eq_of h e
  refine ⟨v22, v23, u v24 ?_, u v29 ?_, u v31 ?_, u v34 ?_, u v35 ?_, u v44 ?_, u v50 ?_, v402⟩ <;>
    (try simp only [MainCounts.sx, MainCounts.ss]) <;> omega

/-- **`main` allocates its `HeapBuf`s** on its honest oracle, the slots below `2^19` and at most `16`
children. -/
theorem mAllocs (hb : (mainCounts s w).sx + (mainCounts s w).ss < 2 ^ 19) (hn : (mainCounts s w).nc ≤ 16) :
    allocs (mVal rd (mOrc al s w)) (mEs (mVal rd (mOrc al s w))) = (mainCounts s w).bufs := by
  obtain ⟨-, -, v24, v29, v31, v34, v35, v44, v50, v402⟩ := mOrc_sizes (al := al) (s := s) (w := w) (rd := rd)
  have L : ∀ e, e < 2 ^ 19 * 64 → logG (gen ^ e) = e := fun e he => logG_gen_pow (by omega)
  have l1 := L (4 * (mainCounts s w).sx) (by omega)
  have l2 := L (4 * (mainCounts s w).ss) (by omega)
  have l3 := L ((mainCounts s w).sx + (mainCounts s w).ss) (by omega)
  have l4 := L (2 * ((mainCounts s w).nc + 1)) (by omega)
  have l5 := L (2 * (mainCounts s w).nc) (by omega)
  have l6 := L (55 * (mainCounts s w).nc) (by omega)
  have l7 := L (26 * (mainCounts s w).nc) (by omega)
  have l8 := L ((mainCounts s w).nc + 1) (by omega)
  rw [mAllocs_eq, v24, v29, v31, v34, v35, v44, v50, v402, l1, l2, l3, l4, l5, l6, l7, l8]
  rfl

end

end
end
end LeanVM.Guest.Complete
