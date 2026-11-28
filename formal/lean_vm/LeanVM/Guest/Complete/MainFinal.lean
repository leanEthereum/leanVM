/-
  LeanVM.Guest.Complete.MainFinal

  `main`'s final condition: its pops the honest pushes stream by stream, every node exact.
-/

module

public import LeanVM.Guest.Complete.MainPostWins
public import LeanVM.Guest.Complete.PopSkel
import LeanVM.Guest.Memory.SelArm

/-!
# `main`'s final condition

`main`'s body is straight but for its two branches, so under any valuation it falls through with
`mainEvs σ` (`walk_mainSs`), its skeleton `mainItems` (`mainEvs_skel`): `meta`, `fs_seed`, seven
callees, `da_verify` when the matrix is checked, the children's loop, `da_pick`, `leaf_defer` on a
leaf or `aggregate_claims`, `statement_digest`. Its callees pop `mainPs s w` (`kOk_main`, from the
posts of `mPre`'s, the DA branch's, the children's loop's, the batching's windows), so `main`'s
pops are `honestPushes` with `da_verify`'s and `da_pick`'s entries moved past the children's and the
leaf's or batching's, streams none of those name (`main_reorder`, `kidPushes_names`). `main` has no
computed hint, so it is exact on every valuation (`exactAt_main`).

`mainFinalAt`, `mainFinalFromCallees : MainFinalFromCallees al k`, and so
`mainWindowFromCallees : MainWindowFromCallees al k`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `main`'s events -/

set_option maxRecDepth 200000 in
theorem main_parts_straight : mPre.all Stmt.straight = true ∧ mDa.all Stmt.straight = true ∧
    mDaZ.all Stmt.straight = true ∧ mMid.all Stmt.straight = true ∧ mLeaf.all Stmt.straight = true ∧
    mAgg.all Stmt.straight = true ∧ mPost.all Stmt.straight = true := by
  decide +kernel

/-- `main`'s events before its `ret []` under `σ`, each branch on its taken arm. -/
noncomputable def mainEvs (σ : Val) : List Ev :=
  mPre.flatMap (slEvs σ) ++ (.inK (.n 384) :: (if σ (.n 384) = 0 then mDa else mDaZ).flatMap (slEvs σ)) ++
    mMid.flatMap (slEvs σ) ++ (.inK (.n 423) :: (if σ (.n 423) = 0 then mLeaf else mAgg).flatMap (slEvs σ)) ++
    mPost.flatMap (slEvs σ)

theorem walk_app_fall {σ : Val} {xs ys : List Stmt} {es es' : List Ev} (h : walk σ xs = .fall es)
    (h' : walk σ ys = .fall es') : walk σ (xs ++ ys) = .fall (es ++ es') := by
  rw [Memory.walk_append, h, h']; rfl

theorem walk_ite_straight (σ : Val) {c : V} {z n : List Stmt} (hz : z.all Stmt.straight = true)
    (hn : n.all Stmt.straight = true) :
    walk σ [.ite c z n] = .fall (.inK c :: (if σ c = 0 then z else n).flatMap (slEvs σ)) := by
  by_cases h : σ c = 0
  · simp only [walk, walk1, ite_eq_left h, walk_straight_fall σ z hz, Out.pre, Out.seq, List.append_nil,
      List.singleton_append]
  · simp only [walk, walk1, ite_eq_right h, walk_straight_fall σ n hn, Out.pre, Out.seq, List.append_nil,
      List.singleton_append]

theorem walk_mainSs (σ : Val) : walk σ mainSs = .fall (mainEvs σ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := main_parts_straight
  unfold mainSs
  exact walk_app_fall (walk_app_fall (walk_app_fall (walk_app_fall (walk_straight_fall σ _ h1)
    (walk_ite_straight σ h2 h3)) (walk_straight_fall σ _ h4)) (walk_ite_straight σ h5 h6))
    (walk_straight_fall σ _ h7)

theorem walk_main (σ : Val) : walk σ (fn% «main»).body = .ret (mainEvs σ) [] := by
  rw [main_body, Memory.walk_append, walk_mainSs]
  simp [walk, walk1, Out.seq, Out.pre]

theorem mEs_mainEvs (σ0 : Val) : mEs σ0 = mainEvs σ0 := by
  rw [mEs, walk_mainSs]; rfl

/-! ## Its skeleton and its calls -/

set_option maxRecDepth 200000 in
theorem main_skels :
    mPre.flatMap stmtSkel = [.wit "meta" (.stack ((List.range 8).map V.n)), .wit "fs_seed" (.stack [.n 26, .n 27]),
      .kid, .kid, .kid, .kid, .kid, .kid, .kid] ∧
    mDa.flatMap stmtSkel = [.kid] ∧ mDaZ.flatMap stmtSkel = [] ∧
    mMid.flatMap stmtSkel = [.kid, .wit "da_pick" (.stack [.n 410])] ∧
    mLeaf.flatMap stmtSkel = [.wit "leaf_defer" (.stack [.n 424])] ∧ mAgg.flatMap stmtSkel = [.kid] ∧
    mPost.flatMap stmtSkel = [.kid] := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem main_conds :
    (mPre.filterMap Stmt.callS).map (·.1) =
      [none, none, none, some (.n 59), some (.n 62), some (.n 375), some (.n 378)] ∧
    (mDa.filterMap Stmt.callS).map (·.1) = [none] ∧ (mDaZ.filterMap Stmt.callS).map (·.1) = [] ∧
    (mMid.filterMap Stmt.callS).map (·.1) = [some (.n 406)] ∧ (mLeaf.filterMap Stmt.callS).map (·.1) = [] ∧
    (mAgg.filterMap Stmt.callS).map (·.1) = [none] ∧ (mPost.filterMap Stmt.callS).map (·.1) = [none] := by
  decide +kernel

/-- `main`'s skeleton: whether it checks a matrix, whether it is a leaf. -/
def mainItems (da leaf : Bool) : List PItem :=
  [.wit "meta" (.stack ((List.range 8).map V.n)), .wit "fs_seed" (.stack [.n 26, .n 27]),
    .kid, .kid, .kid, .kid, .kid, .kid, .kid] ++ cond da [.kid] [] ++
    [.kid, .wit "da_pick" (.stack [.n 410])] ++
    cond leaf [.wit "leaf_defer" (.stack [.n 424])] [.kid] ++ [.kid]

theorem mainEvs_skel (σ : Val) :
    (mainEvs σ).flatMap evSkel = mainItems (decide (σ (.n 384) = 0)) (decide (σ (.n 423) = 0)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := main_parts_straight
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := main_skels
  have ea : ((if σ (.n 384) = 0 then mDa else mDaZ).flatMap (slEvs σ)).flatMap evSkel =
      cond (decide (σ (.n 384) = 0)) [.kid] [] := by
    by_cases ha : σ (.n 384) = 0
    · rw [ite_eq_left ha, decide_eq_true ha, straight_skel _ h2, s2]; rfl
    · rw [ite_eq_right ha, decide_eq_false ha, straight_skel _ h3, s3]; rfl
  have eb : ((if σ (.n 423) = 0 then mLeaf else mAgg).flatMap (slEvs σ)).flatMap evSkel =
      cond (decide (σ (.n 423) = 0)) [.wit "leaf_defer" (.stack [.n 424])] [.kid] := by
    by_cases hb : σ (.n 423) = 0
    · rw [ite_eq_left hb, decide_eq_true hb, straight_skel _ h5, s5]; rfl
    · rw [ite_eq_right hb, decide_eq_false hb, straight_skel _ h6, s6]; rfl
  simp only [mainEvs, List.flatMap_append, List.flatMap_cons, evSkel, List.nil_append, straight_skel _ h1,
    straight_skel _ h4, straight_skel _ h7, s1, s4, s7, ea, eb, mainItems]

theorem mainEvs_taken (σ : Val) : (calls (mainEvs σ)).map Call.taken =
    [true, true, true, takenOf σ (some (.n 59)), takenOf σ (some (.n 62)), takenOf σ (some (.n 375)),
      takenOf σ (some (.n 378))] ++ (if σ (.n 384) = 0 then [true] else []) ++ [takenOf σ (some (.n 406))] ++
      (if σ (.n 423) = 0 then [] else [true]) ++ [true] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := main_parts_straight
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := main_conds
  have hc : ∀ (es es' : List Ev), calls (es ++ es') = calls es ++ calls es' := fun _ _ => List.filterMap_append
  have hk : ∀ (c : V) (es : List Ev), calls (.inK c :: es) = calls es := fun _ _ => rfl
  have ea : (calls ((if σ (.n 384) = 0 then mDa else mDaZ).flatMap (slEvs σ))).map Call.taken =
      if σ (.n 384) = 0 then [true] else [] := by
    by_cases ha : σ (.n 384) = 0
    · rw [ite_eq_left ha, ite_eq_left ha, straight_taken σ _ h2, c2]; rfl
    · rw [ite_eq_right ha, ite_eq_right ha, straight_taken σ _ h3, c3]; rfl
  have eb : (calls ((if σ (.n 423) = 0 then mLeaf else mAgg).flatMap (slEvs σ))).map Call.taken =
      if σ (.n 423) = 0 then [] else [true] := by
    by_cases hb : σ (.n 423) = 0
    · rw [ite_eq_left hb, ite_eq_left hb, straight_taken σ _ h5, c5]; rfl
    · rw [ite_eq_right hb, ite_eq_right hb, straight_taken σ _ h6, c6]; rfl
  simp only [mainEvs, hc, hk, List.map_append, straight_taken σ _ h1, c1, straight_taken σ _ h4, c4,
    straight_taken σ _ h7, c7, ea, eb, List.map_cons, List.map_nil, takenOf]

/-! ## Exactness: `main` has no computed hint -/

set_option maxRecDepth 200000 in
theorem main_noComputed : Stmt.blockNextOk isComputed (fun _ _ => false) (fn% «main»).body = true := by
  decide +kernel

theorem exactAt_main (rd : Reader) (σ : Val) : ExactAt coreProgram rd "main" σ := by
  refine exactAt_of_walk find_main (walk_main σ) fun e he => ?_
  have hp := walk_partnered (σ := σ) _ main_noComputed
  rw [walk_main] at hp
  cases e with
  | atom a =>
    cases hc : isComputed a with
    | false => exact exact_of_not_computed hc
    | true =>
      obtain ⟨b, -, hq⟩ := hp a he hc
      simp at hq
  | _ => trivial

/-! ## The callees' lists -/

/-- The DA branch's list: `da_verify`'s on a checked matrix. -/
def daPs (w : NodeWitness) : List (List Pop) :=
  match w.daMatrix with
  | some (c, mw) => [Prover.daHints c mw]
  | none => []

/-- The batching's list on an inner node. -/
def aggPs (w : NodeWitness) : List (List Pop) :=
  if w.children = [] then [] else [Prover.batchPushes w.batchingHints]

/-- **The lists `main`'s callees pop**, in call order. -/
def mainPs (s : NodeStatement) (w : NodeWitness) : List (List Pop) :=
  [[], Prover.listPushes "claims" (s.claims.xmss.map xCells), Prover.listPushes "claims" (s.claims.sphincs.map sCells),
    (xPlan s w).duplicates.map (fun c => ("dup_claims", xCells c)),
    (sPlan s w).duplicates.map (fun c => ("dup_claims", sCells c)),
    (w.xmssSignatures.zip (xPlan s w).directSlots).flatMap (fun cs =>
      ("raw_index", [Prover.count cs.2]) :: Prover.xmssHints cs.1.1.1 cs.1.1.2 cs.1.2),
    (w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap (fun cs =>
      ("sp_raw_index", [Prover.count cs.2]) :: Prover.sphincsHints cs.1.1.1 cs.1.1.2 cs.1.2)] ++
  daPs w ++ [mKidPushes s w] ++ aggPs w ++ [[]]

/-- A guarded callee, entered exactly when its count is nonzero, its list empty at zero. -/
theorem kOk_qIf {rd : Reader} {σ : Val} {c : V} {n : ℕ} {P : List Pop} {Qs : List (Reader → Tree → Prop)}
    {bs : List Bool} {Ps : List (List Pop)} (hc : σ c = word 1 0 + gen ^ n) (hn : n < 2 ^ 34)
    (h0 : n = 0 → P = []) (h : KOk rd Qs bs Ps) :
    KOk rd (qIf n (PopsPost P) :: Qs) (takenOf σ (some c) :: bs) (P :: Ps) := by
  refine ⟨fun hb t ht => ?_, ⟨fun hb => h0 ?_, h⟩⟩
  · have hn0 : n ≠ 0 := fun h0' => by
      simp only [takenOf, hc, decide_eq_true_eq] at hb
      exact hb ((guard_eq_zero_iff hn).mpr h0')
    simpa only [qIf, hn0, ↓reduceIte] using ht
  · simp only [takenOf, hc, decide_eq_false_iff_not, not_not] at hb
    exact (guard_eq_zero_iff hn).mp hb

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness}

theorem kOk_da {rd rd0 : Reader} :
    KOk rd (qDa w) (if mVal rd0 (mOrc al s w) (.n 384) = 0 then [true] else []) (daPs w) := by
  cases hm : w.daMatrix with
  | none =>
    have h : mVal rd0 (mOrc al s w) (.n 384) ≠ 0 := by
      rw [Ne, mOrc_384_zero]; simp [mainCounts, hm]
    simp only [qDa, daPs, hm, ite_eq_right h]
    trivial
  | some p =>
    obtain ⟨c, mw⟩ := p
    have h : mVal rd0 (mOrc al s w) (.n 384) = 0 := by
      rw [mOrc_384_zero]; simp [mainCounts, hm]
    simp only [qDa, daPs, hm, ite_eq_left h]
    exact kOk_pops trivial

theorem kOk_agg (hlim : DeployedLimits s w) {rd rd0 : Reader} :
    KOk rd (qAgg w) (if mVal rd0 (mOrc al s w) (.n 423) = 0 then [] else [true]) (aggPs w) := by
  by_cases hc : w.children = []
  · have h : mVal rd0 (mOrc al s w) (.n 423) = 0 :=
      (mOrc_423_zero (nc_le hlim)).mpr (by simp [mainCounts, hc])
    simp only [qAgg, aggPs, ite_eq_left hc, ite_eq_left h]
    trivial
  · have h : mVal rd0 (mOrc al s w) (.n 423) ≠ 0 := fun h =>
      hc (List.eq_nil_of_length_eq_zero ((mOrc_423_zero (nc_le hlim)).mp h))
    simp only [qAgg, aggPs, ite_eq_right hc, ite_eq_right h]
    exact kOk_pops trivial

/-- **`main`'s callees pop `mainPs s w`**, from their posts. -/
theorem kOk_main (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w) {rd rd0 : Reader} :
    KOk rd (qPre s w ++ qDa w ++ [qIf (mainCounts s w).nc (PopsPost (mKidPushes s w))] ++ qAgg w ++ [FreePost])
      ([true, true, true, takenOf (mVal rd0 (mOrc al s w)) (some (.n 59)),
        takenOf (mVal rd0 (mOrc al s w)) (some (.n 62)), takenOf (mVal rd0 (mOrc al s w)) (some (.n 375)),
        takenOf (mVal rd0 (mOrc al s w)) (some (.n 378))] ++
        (if mVal rd0 (mOrc al s w) (.n 384) = 0 then [true] else []) ++
        [takenOf (mVal rd0 (mOrc al s w)) (some (.n 406))] ++
        (if mVal rd0 (mOrc al s w) (.n 423) = 0 then [] else [true]) ++ [true])
      (mainPs s w) := by
  have hb := slots_lt hr hlim
  have hn := nc_le hlim
  obtain ⟨hdx, hds⟩ := dups_lt hr hlim
  have hraw := raw_le_slots hr
  obtain ⟨g59, g62, g375, g378, g406⟩ := mVal_guards (rd := rd0) (w := mOrc al s w)
  have bx : (mainCounts s w).nrx < 2 ^ 34 :=
    lt_of_le_of_lt (by omega : (mainCounts s w).nrx ≤ (mainCounts s w).sx + (mainCounts s w).ss) (lt_trans hb (by norm_num))
  have bs : (mainCounts s w).nrs < 2 ^ 34 :=
    lt_of_le_of_lt (by omega : (mainCounts s w).nrs ≤ (mainCounts s w).sx + (mainCounts s w).ss) (lt_trans hb (by norm_num))
  unfold mainPs
  refine kOk_append (kOk_append (kOk_append (kOk_append ?_ kOk_da) ?_) (kOk_agg hlim)) (kOk_free trivial)
  · unfold qPre
    refine kOk_free (kOk_pops (kOk_pops (kOk_qIf (g59.trans rfl) (lt_trans hdx (by norm_num)) ?_
      (kOk_qIf (g62.trans rfl) (lt_trans hds (by norm_num)) ?_
      (kOk_qIf (g375.trans rfl) bx ?_ (kOk_qIf (g378.trans rfl) bs ?_ trivial))))))
    · intro h
      have h' : (xPlan s w).duplicates = [] := List.eq_nil_of_length_eq_zero h
      simp [h']
    · intro h
      have h' : (sPlan s w).duplicates = [] := List.eq_nil_of_length_eq_zero h
      simp [h']
    · intro h
      have h' : w.xmssSignatures = [] := List.eq_nil_of_length_eq_zero h
      simp [h']
    · intro h
      have h' : w.sphincsSignatures = [] := List.eq_nil_of_length_eq_zero h
      simp [h']
  · refine kOk_qIf (g406.trans rfl) (lt_of_le_of_lt hn (by norm_num)) (fun h => ?_) trivial
    have h' : w.children = [] := List.eq_nil_of_length_eq_zero h
    simp [mKidPushes, h']

end

/-! ## The values `main` pops -/

set_option maxRecDepth 200000 in
theorem mTL_free : mTL.lookup (.n 0) = none ∧ mTL.lookup (.n 1) = none ∧ mTL.lookup (.n 2) = none ∧
    mTL.lookup (.n 3) = none ∧ mTL.lookup (.n 4) = none ∧ mTL.lookup (.n 5) = none ∧ mTL.lookup (.n 6) = none ∧
    mTL.lookup (.n 7) = none ∧ mTL.lookup (.n 26) = none ∧ mTL.lookup (.n 27) = none ∧
    mTL.lookup (.n 410) = none ∧ mTL.lookup (.n 424) = none := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem main_wit_mem : Atom.hint (.witness "da_pick" (.stack [.n 410])) ∈ atomsOf mMid ∧
    Atom.hint (.witness "fs_seed" (.stack [.n 26, .n 27])) ∈ atomsOf mPre ∧
    Atom.hint (.witness "leaf_defer" (.stack [.n 424])) ∈ atomsOf mLeaf := by
  decide +kernel

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {rd rd0 : Reader}

/-- `main`'s counts, as `meta` pops them. -/
def metaCells (s : NodeStatement) (w : NodeWitness) : List E :=
  [Prover.count s.claims.xmss.length, Prover.count (xPlan s w).duplicates.length,
    Prover.count w.xmssSignatures.length, Prover.count s.claims.sphincs.length,
    Prover.count (sPlan s w).duplicates.length, Prover.count w.sphincsSignatures.length,
    Prover.count w.children.length, Prover.count ((w.daMatrix.map fun _ => 1).getD 0)]

theorem meta_words :
    (Dest.stack ((List.range 8).map V.n)).words rd (over mTL (mVal rd0 (mOrc al s w)) rd) = metaCells s w := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, -⟩ := mTL_free
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)
  have e : (List.range 8).map V.n = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] := rfl
  rw [e]
  simp only [Dest.words, List.map_cons, List.map_nil, over_eq t0, over_eq t1, over_eq t2, over_eq t3, over_eq t4,
    over_eq t5, over_eq t6, over_eq t7, c0, c1, c2, c3, c4, c5, c6, c7]
  rfl

theorem seed_words :
    (Dest.stack [.n 26, .n 27]).words rd (over mTL (mVal rd0 (mOrc al s w)) rd) = Prover.digestCells guestSeed := by
  obtain ⟨-, -, -, -, -, -, -, -, t26, t27, -⟩ := mTL_free
  have m := main_wit_mem.2.1
  have e26 : mVal rd0 (mOrc al s w) (.n 26) = mOrc al s w 26 := mPre_good m (.n 26) (by simp)
  have e27 : mVal rd0 (mOrc al s w) (.n 27) = mOrc al s w 27 := mPre_good m (.n 27) (by simp)
  simp only [Dest.words, List.map_cons, List.map_nil, over_eq t26, over_eq t27, e26, e27]
  rfl

theorem pick_words :
    (Dest.stack [.n 410]).words rd (over mTL (mVal rd0 (mOrc al s w)) rd) = [Prover.count (Prover.daPick s w)] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, t410, -⟩ := mTL_free
  have e : mVal rd0 (mOrc al s w) (.n 410) = mOrc al s w 410 := mMid_good main_wit_mem.1 (.n 410) (by simp)
  simp only [Dest.words, List.map_cons, List.map_nil, over_eq t410, e]
  rfl

theorem leaf_words (h : mVal rd0 (mOrc al s w) (.n 423) = 0) :
    (Dest.stack [.n 424]).words rd (over mTL (mVal rd0 (mOrc al s w)) rd) = [s.deferredClaim.bytecodeValue] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, t424⟩ := mTL_free
  have e : mVal rd0 (mOrc al s w) (.n 424) = s.deferredClaim.bytecodeValue :=
    mVal_goodLeaf h _ (atom_mem_of_atomsOf main_wit_mem.2.2) (.n 424) List.mem_cons_self
  simp only [Dest.words, List.map_cons, List.map_nil, over_eq t424, e]

end

/-! ## The stream names -/

/-- The streams a child's pushes name. -/
def kidNames : List String :=
  ["child_meta", "signers_split", "child_mono", "child_claim_gap", "child_claim_index", "child_defer", "child_da",
    "stream_chunks", "stream", "table_logs", "link_shape", "stk_group_order", "split_values", "merkle_leaf_rows",
    "merkle_children", "merkle_caps", "merkle_cap_active"]

/-- The streams the DA check and its pick name. -/
def daNames : List String := ["da_challenge", "da_n_blobs", "da_symbols", "da_pick"]

/-- The streams a leaf's or the batching's pushes name. -/
def leafNames : List String := ["leaf_defer", "bc_sumcheck_msgs", "bc_star_hint"]

theorem names_append {N : List String} {l l' : List Pop} (h : ∀ p ∈ l, p.1 ∈ N) (h' : ∀ p ∈ l', p.1 ∈ N) :
    ∀ p ∈ l ++ l', p.1 ∈ N := fun p hp => by
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

theorem childSlotPushes_names (os : List ℕ) : ∀ p ∈ Prover.childSlotPushes os, p.1 ∈ kidNames := by
  intro p hp
  unfold Prover.childSlotPushes at hp
  split_ifs at hp
  · simp at hp
  · simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | rfl | ⟨_, -, rfl⟩ <;> simp [kidNames]
  · simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | rfl | ⟨_, -, rfl⟩ <;> simp [kidNames]

theorem levelHints_names (first : Bool) (depth count : ℕ) (phase : List LeanVM.Protocol.Compile.Opening) :
    ∀ p ∈ Prover.levelHints first depth count phase, p.1 ∈ kidNames := by
  intro p hp
  simp only [Prover.levelHints, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with ⟨x, -, hx⟩ | rfl | rfl
  · obtain ⟨o, steps, r⟩ := x
    rcases hx with rfl | rfl <;> simp [kidNames]
  · simp [kidNames]
  · simp [kidNames]

theorem merkleHints_names : ∀ (first : Bool) (qs : List (ℕ × List ℕ)) (ps : List (List LeanVM.Protocol.Compile.Opening)),
    ∀ p ∈ Prover.merkleHints first qs ps, p.1 ∈ kidNames
  | first, (d, pos) :: rest, ph :: phs => by
      intro p hp
      rw [Prover.merkleHints, List.mem_append] at hp
      rcases hp with hp | hp
      · exact levelHints_names first d pos.length ph p hp
      · exact merkleHints_names false rest phs p hp
  | _, [], _ => by intro p hp; simp [Prover.merkleHints] at hp
  | _, _ :: _, [] => by intro p hp; simp [Prover.merkleHints] at hp

theorem childHints_names (bc : List K) (seed : Digest) (c : Child) :
    ∀ p ∈ Prover.childHints bc seed c, p.1 ∈ kidNames := by
  unfold Prover.childHints
  split
  · simp
  · dsimp only
    refine names_append (names_append (names_append (names_append (names_append ?_ ?_) ?_) ?_) ?_)
      (merkleHints_names _ _ _)
    · simp [kidNames]
    · intro p hp
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      simp [kidNames]
    · simp [kidNames]
    · simp [Prover.stackHints, kidNames]
    · simp [kidNames]

theorem kidPushes_names (s : NodeStatement) (w : NodeWitness) : ∀ p ∈ mKidPushes s w, p.1 ∈ kidNames := by
  intro p hp
  obtain ⟨⟨⟨c, xs⟩, ss⟩, -, hp⟩ := List.mem_flatMap.mp hp
  exact names_append (names_append (names_append
    (fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · simp [kidNames]
      · exact childSlotPushes_names xs q hq)
    (childSlotPushes_names ss)) (by simp [kidNames])) (childHints_names _ _ c) p hp

theorem daHints_names (c : DaClaim) (mw : LeanVM.Da.MatrixWitness) : ∀ p ∈ Prover.daHints c mw, p.1 ∈ daNames := by
  intro p hp
  simp only [Prover.daHints, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap,
    List.mem_map] at hp
  rcases hp with (rfl | rfl) | ⟨_, -, _, -, rfl⟩ <;> simp [daNames]

theorem kid_not_da : ∀ a ∈ kidNames, a ∉ daNames := by decide

theorem leaf_not_da : ∀ a ∈ leafNames, a ∉ daNames := by decide

/-! ## The reordering -/

/-- **`main`'s order to `honestPushes`'**: the DA check's entries past the children's, and the DA
check's and its pick's past the leaf's or batching's, streams apart. -/
theorem main_reorder {X DA K L : List Pop} {pk : Pop} (hKD : ∀ p ∈ DA, ∀ q ∈ K, p.1 ≠ q.1)
    (hLD : ∀ p ∈ DA ++ [pk], ∀ q ∈ L, p.1 ≠ q.1) :
    SameStreams (X ++ DA ++ (K ++ [pk]) ++ L) (X ++ K ++ L ++ DA ++ [pk]) := by
  have s1 : SameStreams (DA ++ K ++ ([pk] ++ L)) (K ++ DA ++ ([pk] ++ L)) :=
    SameStreams.append (sameStreams_append_comm hKD) (fun _ => rfl)
  have s2 : SameStreams (K ++ ((DA ++ [pk]) ++ L)) (K ++ (L ++ (DA ++ [pk]))) :=
    SameStreams.append (fun _ => rfl) (sameStreams_append_comm hLD)
  have e1 : X ++ DA ++ (K ++ [pk]) ++ L = X ++ (DA ++ K ++ ([pk] ++ L)) := by simp only [List.append_assoc]
  have e2 : K ++ DA ++ ([pk] ++ L) = K ++ ((DA ++ [pk]) ++ L) := by simp only [List.append_assoc]
  have e3 : X ++ K ++ L ++ DA ++ [pk] = X ++ (K ++ (L ++ (DA ++ [pk]))) := by simp only [List.append_assoc]
  rw [e1, e3]
  exact SameStreams.append (fun _ => rfl) (sameStreams_trans s1 (by rw [e2]; exact s2))

/-! ## `honestPushes` in `main`'s blocks -/

/-- `honestPushes` up to the children's: the counts, the seed, the claim lists, the duplicates, the raw
signatures. -/
def mPreX (s : NodeStatement) (w : NodeWitness) : List Pop :=
  [("meta", metaCells s w), ("fs_seed", Prover.digestCells guestSeed)] ++
    Prover.listPushes "claims" (s.claims.xmss.map xCells) ++ Prover.listPushes "claims" (s.claims.sphincs.map sCells) ++
    ((xPlan s w).duplicates.map xCells ++ (sPlan s w).duplicates.map sCells).map (("dup_claims", ·)) ++
    (w.xmssSignatures.zip (xPlan s w).directSlots).flatMap (fun (c, slot) ↦
      ("raw_index", [Prover.count slot]) :: Prover.xmssHints c.1.1 c.1.2 c.2) ++
    (w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap (fun (c, slot) ↦
      ("sp_raw_index", [Prover.count slot]) :: Prover.sphincsHints c.1.1 c.1.2 c.2)

/-- The leaf's deferred value or the batching's pushes. -/
def mLA (s : NodeStatement) (w : NodeWitness) : List Pop :=
  if w.children = [] then [("leaf_defer", [s.deferredClaim.bytecodeValue])] else Prover.batchPushes w.batchingHints

/-- The checked matrix's DA hints. -/
def mDA (w : NodeWitness) : List Pop := (w.daMatrix.map (fun c ↦ Prover.daHints c.1 c.2)).getD []

theorem honest_eq (s : NodeStatement) (w : NodeWitness) :
    Prover.honestPushes guestBytecode guestSeed s w =
      mPreX s w ++ mKidPushes s w ++ mLA s w ++ mDA w ++ [("da_pick", [Prover.count (Prover.daPick s w)])] :=
  rfl

theorem mPreX_eq (s : NodeStatement) (w : NodeWitness) :
    mPreX s w = [("meta", metaCells s w), ("fs_seed", Prover.digestCells guestSeed)] ++
      Prover.listPushes "claims" (s.claims.xmss.map xCells) ++ Prover.listPushes "claims" (s.claims.sphincs.map sCells) ++
      (xPlan s w).duplicates.map (fun c => ("dup_claims", xCells c)) ++
      (sPlan s w).duplicates.map (fun c => ("dup_claims", sCells c)) ++
      (w.xmssSignatures.zip (xPlan s w).directSlots).flatMap (fun cs =>
        ("raw_index", [Prover.count cs.2]) :: Prover.xmssHints cs.1.1.1 cs.1.1.2 cs.1.2) ++
      (w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap (fun cs =>
        ("sp_raw_index", [Prover.count cs.2]) :: Prover.sphincsHints cs.1.1.1 cs.1.1.2 cs.1.2) := by
  rw [mPreX, List.map_append, List.map_map, List.map_map, List.append_assoc _ (List.map _ _) (List.map _ _)]
  rfl

/-! ## The final condition -/

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}

/-- **`main`'s skeleton on its callees' lists is `honestPushes`, stream by stream.** -/
theorem main_streams (hlim : DeployedLimits s w) {rd rd0 : Reader} :
    SameStreams (skelPops rd (over mTL (mVal rd0 (mOrc al s w)) rd)
        (mainItems (decide (mVal rd0 (mOrc al s w) (.n 384) = 0)) (decide (mVal rd0 (mOrc al s w) (.n 423) = 0)))
        (mainPs s w))
      (mPreX s w ++ mKidPushes s w ++ mLA s w ++ mDA w ++ [("da_pick", [Prover.count (Prover.daPick s w)])]) := by
  have hKD : ∀ p ∈ mDA w, ∀ q ∈ mKidPushes s w, p.1 ≠ q.1 := by
    intro p hp q hq he
    have hq' := kidPushes_names s w q hq
    rw [← he] at hq'
    unfold mDA at hp
    cases hm : w.daMatrix with
    | none => simp [hm] at hp
    | some cm =>
      rw [hm] at hp
      exact kid_not_da _ hq' (daHints_names cm.1 cm.2 p hp)
  have hLD : ∀ p ∈ mDA w ++ [("da_pick", [Prover.count (Prover.daPick s w)])], ∀ q ∈ mLA s w, p.1 ≠ q.1 := by
    intro p hp q hq he
    have hq' : q.1 ∈ leafNames := by
      unfold mLA at hq
      split_ifs at hq
      · simp only [List.mem_singleton] at hq; subst hq; simp [leafNames]
      · simp only [Prover.batchPushes, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl <;> simp [leafNames]
    have hp' : p.1 ∈ daNames := by
      rcases List.mem_append.mp hp with hp | hp
      · unfold mDA at hp
        cases hm : w.daMatrix with
        | none => simp [hm] at hp
        | some cm => rw [hm] at hp; exact daHints_names cm.1 cm.2 p hp
      · rw [List.mem_singleton] at hp; subst hp; simp [daNames]
    rw [he] at hp'
    exact leaf_not_da _ hq' hp'
  refine sameStreams_trans (sameStreams_of_eq ?_) (main_reorder hKD hLD)
  rw [mPreX_eq]
  cases hm : w.daMatrix with
  | none =>
    have h384 : decide (mVal rd0 (mOrc al s w) (.n 384) = 0) = false := by
      rw [decide_eq_false_iff_not, mOrc_384_zero]; simp [mainCounts, hm]
    by_cases hc : w.children = []
    · have h0 : mVal rd0 (mOrc al s w) (.n 423) = 0 := (mOrc_423_zero (nc_le hlim)).mpr (by simp [mainCounts, hc])
      simp only [h384, decide_eq_true h0, mainItems, mainPs, daPs, aggPs, mDA, mLA, hm, ite_eq_left hc, Bool.cond_true,
        Bool.cond_false, Option.map_none, Option.getD_none, List.cons_append, List.nil_append,
        List.append_assoc, List.append_nil, skelPops, List.headD_cons, List.tail_cons, meta_words, seed_words,
        pick_words, leaf_words h0]
    · have h0 : mVal rd0 (mOrc al s w) (.n 423) ≠ 0 := fun h =>
        hc (List.eq_nil_of_length_eq_zero ((mOrc_423_zero (nc_le hlim)).mp h))
      simp only [h384, decide_eq_false h0, mainItems, mainPs, daPs, aggPs, mDA, mLA, hm, ite_eq_right hc,
        Bool.cond_false, Option.map_none, Option.getD_none, List.cons_append, List.nil_append,
        List.append_assoc, List.append_nil, skelPops, List.headD_cons, List.tail_cons, meta_words, seed_words,
        pick_words]
  | some cm =>
    obtain ⟨c, mw⟩ := cm
    have h384 : decide (mVal rd0 (mOrc al s w) (.n 384) = 0) = true := by
      rw [decide_eq_true_iff, mOrc_384_zero]; simp [mainCounts, hm]
    by_cases hc : w.children = []
    · have h0 : mVal rd0 (mOrc al s w) (.n 423) = 0 := (mOrc_423_zero (nc_le hlim)).mpr (by simp [mainCounts, hc])
      simp only [h384, decide_eq_true h0, mainItems, mainPs, daPs, aggPs, mDA, mLA, hm, ite_eq_left hc, Bool.cond_true,
        Option.map_some, Option.getD_some, List.cons_append, List.nil_append,
        List.append_assoc, List.append_nil, skelPops, List.headD_cons, List.tail_cons, meta_words, seed_words,
        pick_words, leaf_words h0]
    · have h0 : mVal rd0 (mOrc al s w) (.n 423) ≠ 0 := fun h =>
        hc (List.eq_nil_of_length_eq_zero ((mOrc_423_zero (nc_le hlim)).mp h))
      simp only [h384, decide_eq_false h0, mainItems, mainPs, daPs, aggPs, mDA, mLA, hm, ite_eq_right hc, Bool.cond_true,
        Bool.cond_false, Option.map_some, Option.getD_some, List.cons_append, List.nil_append,
        List.append_assoc, List.append_nil, skelPops, List.headD_cons, List.tail_cons, meta_words, seed_words,
        pick_words]

/-- `main`'s callees pop `mainPs s w` on the state `mPost` ends in. -/
theorem main_kOk_at (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w) {st : St}
    (hQs : st.Qs = qPre s w ++ qDa w ++ [qIf (mainCounts s w).nc (PopsPost (mKidPushes s w))] ++ qAgg w ++
      [FreePost]) (rd : Reader) :
    KOk rd st.Qs ((calls (mEs (mVal (mRd0 s w cover) (mOrc al s w)))).map Call.taken) (mainPs s w) := by
  rw [hQs, mEs_mainEvs, mainEvs_taken]
  exact kOk_main hr hlim

/-- `main`'s node pops its skeleton's entries. -/
theorem main_pops_eq (rd : Reader) (σ : Val) (bufs : List ℕ) (ts : List Tree) :
    (Memory.Tree.node "main" σ bufs ts).pops coreProgram rd =
      skelPops rd σ (mainItems (decide (σ (.n 384) = 0)) (decide (σ (.n 423) = 0))) (Tree.popsKids coreProgram rd ts) := by
  rw [Tree.pops_node find_main (walk_main σ), splice_skel, mainEvs_skel]

/-- **`main`'s final condition** on every node within the deployed limits. -/
theorem mainFinalAt (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w) :
    MainFinalAt al k s w cover := by
  have hK := fun (st : St) => main_kOk_at (al := al) (cover := cover) (st := st) hr hlim
  unfold MainFinalAt
  -- a hypothesis naming `calls (mEs …)` makes the elaborator evaluate `main`'s walk
  generalize calls (mEs (mVal (mRd0 s w cover) (mOrc al s w))) = cs at hK ⊢
  intro st hQs _ rd _ _ _ ts hv hq
  have hk := kOk_kids (hK st hQs rd) hv hq
  refine ⟨?_, Tree.every_node.mpr ⟨exactAt_main rd _, hk.2⟩⟩
  rw [main_pops_eq]
  refine sameStreams_trans (skelPops_streams rd _ _ hk.1) ?_
  rw [over_eq main_sel_tmp.1, over_eq main_sel_tmp.2, honest_eq]
  exact main_streams hlim

/-- **`main`'s final condition from its callees.** -/
theorem mainFinalFromCallees : MainFinalFromCallees al k :=
  fun _ _ _ _ _ _ hr hlim _ _ _ _ => mainFinalAt hr hlim

/-- **`main`'s window from its callees.** -/
theorem mainWindowFromCallees : MainWindowFromCallees al k :=
  mainWindowFromCallees_of_final mainFinalFromCallees

end

end
end LeanVM.Guest.Complete
