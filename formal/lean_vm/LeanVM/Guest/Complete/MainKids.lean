/-
  LeanVM.Guest.Complete.MainKids

  `mMid`'s children's loop at the honest oracle: `main_loop4`'s hypotheses from `main`'s callees.
-/

module

public import LeanVM.Guest.Complete.MainMidWins
import LeanVM.Guest.Complete.CoverageEq
import LeanVM.Guest.B1.Main.Digests

/-!
# `mMid`'s children's loop

`main_loop4` (`__loop4_main`) at `main`'s honest layout: its pointers `mKidP` (`written` at
`mBase m 8`, the tables at `mBase m 0`, `1`, the coverage at `mBase m 2`, the carried claims at
`mBase m 7`, the DA digests at `mBase m 4`, the children's digests at `mBase m 5`, the fresh claims
at `mBase m 6`, the exponent tables at `mGS`), its data `mKidD` (child `c` of the witness).
`mKidHyps`: `KidHyps` from `MainCalleesAt.kidx`, `.kids`, `VsCompleteHypA` and `ChildrenOk`, past
the exponent tables (`mLo`). `kidPushes_eq`: the loop's pops are `honestPushes`' children's part
`mKidPushes`. `winsHypT_mid1`: the guarded call `mMid_w1` keeps `PreInv`, its post
`qIf nc (PopsPost (mKidPushes s w))`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

noncomputable section

/-! ## The loop's data -/

/-- `main_loop4`'s pointers at `main`'s honest layout. -/
def mKidP (al : String → Bool) (s : NodeStatement) (w : NodeWitness) : KidPtrs where
  n := (mainCounts s w).nc
  W := mBase (mainCounts s w) 8 + 0
  TX := mBase (mainCounts s w) 0 + 0
  CV := mBase (mainCounts s w) 2 + 0
  sx := (mainCounts s w).sx
  TS := mBase (mainCounts s w) 1 + 0
  SC := mBase (mainCounts s w) 2 + (mainCounts s w).sx
  ss := (mainCounts s w).ss
  CC := mBase (mainCounts s w) 7 + 0
  DD := mBase (mainCounts s w) 4 + 0
  PI := mBase (mainCounts s w) 5 + 0
  GS := mGS al (mainCounts s w)
  CF := mBase (mainCounts s w) 6 + 0
  seed := guestSeed

/-- Child `c` of the node, `ch0` past the last. -/
def mKid (w : NodeWitness) (ch0 : Child) (c : ℕ) : Child := w.children.getD c ch0

/-- `main_loop4`'s data: child `c`'s parts. -/
def mKidD (s : NodeStatement) (w : NodeWitness) (ch0 : Child) : KidData where
  child := mKid w ch0
  base := kidBase w
  nx c := (mKid w ch0 c).statement.claims.xmss.length
  ns c := (mKid w ch0 c).statement.claims.sphincs.length
  dx c := digestHalves (claimListDigest xmssPublicKeyBytes (mKid w ch0 c).statement.claims.xmss)
  ds c := digestHalves (claimListDigest Sphincs.PublicKey.toBytes (mKid w ch0 c).statement.claims.sphincs)
  da c := digestHalves (mKid w ch0 c).statement.claims.daDigest
  defer c := (mKid w ch0 c).statement.deferredClaim.cells
  px c := Prover.childSlotPushes ((xPlan s w).childSlots.getD c [])
  ps c := Prover.childSlotPushes ((sPlan s w).childSlots.getD c [])

/-- **`honestPushes`' children's part.** -/
def mKidPushes (s : NodeStatement) (w : NodeWitness) : List Pop :=
  ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots).flatMap (fun ((c, xs), ss) ↦
    ("child_meta", [Prover.count c.statement.claims.xmss.length, Prover.count c.statement.claims.sphincs.length]) ::
      Prover.childSlotPushes xs ++ Prover.childSlotPushes ss ++
      [("child_defer", c.statement.deferredClaim.cells), ("child_da", Prover.digestCells c.statement.claims.daDigest)] ++
      Prover.childHints guestBytecode guestSeed c)

theorem mKid_eq {w : NodeWitness} {ch0 : Child} {c : ℕ} (hc : c < w.children.length) :
    mKid w ch0 c = w.children[c] :=
  List.getD_eq_getElem _ _ hc

/-! ## The write counts -/

theorem kidBase_succ (w : NodeWitness) {c : ℕ} (hc : c < w.children.length) :
    kidBase w (c + 1) = kidBase w c +
      (w.children[c].statement.claims.xmss.length + w.children[c].statement.claims.sphincs.length) := by
  unfold kidBase
  rw [List.take_add_one, List.getElem?_eq_getElem hc]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.add_assoc]

theorem kidBase_le (w : NodeWitness) : ∀ {c d : ℕ}, c ≤ d → kidBase w c ≤ kidBase w d := by
  intro c d h
  induction d with
  | zero => rw [Nat.le_zero.mp h]
  | succ d ih =>
    rcases Nat.lt_or_ge d (c) with hd | hd
    · rw [show c = d + 1 by omega]
    · refine le_trans (ih hd) ?_
      by_cases hl : d < w.children.length
      · rw [kidBase_succ w hl]; exact Nat.le_add_right _ _
      · unfold kidBase
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- A child's claim counts are at most the slots. -/
theorem kid_counts_le {s : NodeStatement} {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w)
    {c : ℕ} (hc : c < w.children.length) :
    w.children[c].statement.claims.xmss.length ≤ (mainCounts s w).sx + (mainCounts s w).ss ∧
      w.children[c].statement.claims.sphincs.length ≤ (mainCounts s w).sx + (mainCounts s w).ss := by
  have h1 := kidBase_succ w hc
  have h2 := kidBase_le w (show c + 1 ≤ w.children.length by omega)
  rw [kidBase_all, ← slots_eq_cov hr] at h2
  omega

/-! ## The layout -/

theorem mBase_eqs (m : MainCounts) :
    mBase m 0 = B2C.fs "main" ∧ mBase m 1 = mBase m 0 + 4 * m.sx ∧ mBase m 2 = mBase m 1 + 4 * m.ss ∧
      mBase m 3 = mBase m 2 + (m.sx + m.ss) ∧ mBase m 4 = mBase m 3 + 256 ∧
      mBase m 5 = mBase m 4 + 2 * (m.nc + 1) ∧ mBase m 6 = mBase m 5 + 2 * m.nc ∧
      mBase m 7 = mBase m 6 + 55 * m.nc ∧ mBase m 8 = mBase m 7 + 26 * m.nc ∧
      mBase m 9 = mBase m 8 + (m.nc + 1) ∧ mTop m = mBase m 9 + 26 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [mBase, mTop, MainCounts.bufs, bases]
  omega

theorem mTop_le_mGS (al : String → Bool) (m : MainCounts) : mTop m ≤ mGS al m :=
  le_trans (le_allocBase _ _) (Nat.le_add_right _ _)

/-! ## `main`'s runs on a memory -/

theorem main_runs {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd : Reader}
    (h : HoldsWords rd (mainWords s w cover)) :
    ReadsAt rd (ptrAt (mBase (mainCounts s w) 4))
        (w.children.flatMap (fun ch => Prover.digestCells ch.statement.claims.daDigest) ++ ownDaCells w) ∧
      ReadsAt rd (ptrAt (mBase (mainCounts s w) 5))
        (w.children.flatMap fun ch => Prover.digestCells (statementDigest guestSeed ch.statement)) ∧
      ReadsAt rd (ptrAt (mBase (mainCounts s w) 6)) (w.children.flatMap (·.freshClaim.cells)) ∧
      ReadsAt rd (ptrAt (mBase (mainCounts s w) 7)) (w.children.flatMap (·.statement.deferredClaim.cells)) ∧
      ReadsAt rd (ptrAt (mBase (mainCounts s w) 8))
        ((List.range ((mainCounts s w).nc + 1)).map fun c => gen ^ kidBase w c) ∧
      ReadsAt rd (ptrAt (mBase (mainCounts s w) 9)) s.deferredClaim.cells := by
  have m : ∀ x, x ∈ mainWords s w cover → ReadsAt rd (ptrAt x.1) x.2 := h
  simp only [mainWords] at m
  refine ⟨m (mBase (mainCounts s w) 4, _) ?_, m (mBase (mainCounts s w) 5, _) ?_, m (mBase (mainCounts s w) 6, _) ?_,
    m (mBase (mainCounts s w) 7, _) ?_, m (mBase (mainCounts s w) 8, _) ?_, m (mBase (mainCounts s w) 9, _) ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))))))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))))))

/-- A run's cell `c + j`, as a load at offset `j` from `c`. -/
theorem loadHolds_run {rd : Reader} {b c j : ℕ} {xs : List E} (h : ReadsAt rd (ptrAt b) xs)
    (hc : c + j < xs.length) : LoadHolds rd (ptrAt (b + c)) j xs[c + j] := by
  rw [← ptrAt_mul_pow, loadHolds_mul_gen_pow]
  exact h (c + j) hc

/-- The `c`-th block of `n` cells of a run of uniform blocks. -/
theorem readsAt_block {α : Type} {rd : Reader} {b n c : ℕ} {f : α → List E} {l : List α}
    (hf : ∀ a ∈ l, (f a).length = n) (h : ReadsAt rd (ptrAt b) (l.flatMap f)) (hc : c < l.length) :
    ReadsAt rd (ptrAt (b + n * c)) (f l[c]) := by
  have := B1.Main.readsAt_flatMap_of l hf h c hc
  rwa [ptrAt_mul_pow] at this

/-! ## The loop's hypotheses -/

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}

theorem mKid_pre (ch0 : Child) (cc : ClaimCells s w) {rd : Reader} (hp : MainPreA al s w cover rd) :
    KidPre (mKidP al s w) (mKidD s w ch0) rd := by
  intro c hc
  have hc' : c < w.children.length := hc
  have hnc : (mainCounts s w).nc = w.children.length := rfl
  obtain ⟨r4, r5, r6, r7, r8, -⟩ := main_runs hp.1
  have e := mKid_eq (ch0 := ch0) hc'
  simp only [mKidP, mKidD, e, Nat.add_zero]
  have hb := kidBase_succ w hc'
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨hp.2.1, hp.2.2.1⟩, ?_⟩
  · have := loadHolds_run (j := 0) r8 (c := c) (by simp; omega)
    simpa using this
  · have := loadHolds_run (j := 1) r8 (c := c) (by simp; omega)
    simp only [List.getElem_map, List.getElem_range] at this
    rw [hb, pow_add, pow_add] at this
    exact this
  · exact readsAt_block (fun a ha => cc.carried a ha) r7 hc'
  · exact readsAt_block (n := 2) (fun a _ => rfl) (readsAt_append'.mp r4).1 hc'
  · exact readsAt_block (n := 2) (fun a _ => rfl) r5 hc'
  · exact readsAt_block (fun a ha => cc.fresh a ha) r6 hc'

/-- **`main_loop4`'s hypotheses** at `main`'s honest layout, past the exponent tables. -/
theorem mKidHyps (hk : 17 ≤ k) (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w) (hvs : VsCompleteHypA al k guestBytecode guestSeed)
    (cc : ClaimCells s w) (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs)
    (hcl : MainCalleesAt al k s w cover) (ch0 : Child) :
    KidHyps al k guestBytecode (mKidP al s w) (mKidD s w ch0) (mainR al (mainCounts s w))
      (MainPreA al s w cover) (mLo al (mainCounts s w)) := by
  have hn := nc_le hlim
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, bt⟩ := mBase_eqs (mainCounts s w)
  have hgs := mTop_le_mGS al (mainCounts s w)
  have hnc : (mainCounts s w).nc = w.children.length := rfl
  refine ⟨lt_of_le_of_lt hn (by norm_num), ?_, ?_, ?_, ?_, hvs, le_rfl, ?_, ?_, fun rd hp => mKid_pre ch0 cc hp,
    ?_, ?_⟩
  · intro c hc rd hL hp
    have hc' : c < w.children.length := hc
    obtain ⟨h1, h2⟩ := kid_counts_le hr hc'
    simp only [mKidD, mKid_eq hc']
    exact ⟨count_def hk hl h1 hL hp.1, count_def hk hl h2 hL hp.1⟩
  · intro c hc
    have hc' : c < w.children.length := hc
    simp only [mKidD, mKid_eq hc']
    exact cc.carried _ (List.getElem_mem hc')
  · intro c hc
    have hc' : c < w.children.length := hc
    simp only [mKidP, mKidD, mKid_eq hc']
    exact statementDigest_parts (digestBytes_of_cells rfl) (digestBytes_of_cells rfl) (digestBytes_of_cells rfl)
      (digestBytes_of_cells rfl) rfl
  · intro c hc
    have hc' : c < w.children.length := hc
    simp only [mKidP, mKidD, mKid_eq hc']
    exact vsChildOk_of_acceptable (hok _ (List.getElem_mem hc'))
  · intro c hc
    have hc' : c < w.children.length := hc
    simp only [mKidP, mKidD, mKid_eq hc', cc.fresh _ (List.getElem_mem hc')]
    have : 55 * c + 55 ≤ 55 * (mainCounts s w).nc := by omega
    unfold mLo; omega
  · intro c hc i hi
    have hc' : c < (mainCounts s w).nc := hc
    simp only [KidCells, vsRegion, mKidP, mKidD, mKid_eq (show c < w.children.length from hc),
      cc.fresh _ (List.getElem_mem (show c < w.children.length from hc))] at hi
    unfold mainR
    have h26 : 26 * c + 26 ≤ 26 * (mainCounts s w).nc := by omega
    have h55 : 55 * c + 55 ≤ 55 * (mainCounts s w).nc := by omega
    have h2 : 2 * c + 2 ≤ 2 * ((mainCounts s w).nc + 1) := by omega
    rcases hi with h | h | h | h | h | h | h <;> omega
  · intro c hc fp cur hfp hfc
    have hc' : c < w.children.length := hc
    obtain ⟨e, hb, he⟩ := hcl.kidx c hc' fp cur hfp hfc
    refine ⟨e, hb, ?_⟩
    simp only [mKidD, mKid_eq hc']
    exact he
  · intro c hc fp cur hfp hfc
    have hc' : c < w.children.length := hc
    obtain ⟨e, hb, he⟩ := hcl.kids c hc' fp cur hfp hfc
    refine ⟨e, hb, ?_⟩
    simp only [mKidD, mKid_eq hc']
    exact he

/-! ## The loop's pops -/

theorem flatMap_range'_eq {α β : Type} (f : ℕ → List β) (g : α → List β) :
    ∀ (l : List α) (j : ℕ), (∀ i (hi : i < l.length), f (j + i) = g l[i]) →
      (List.range' j l.length).flatMap f = l.flatMap g
  | [], _, _ => rfl
  | a :: l, j, h => by
    rw [List.length_cons, List.range'_succ, List.flatMap_cons, List.flatMap_cons, ← flatMap_range'_eq f g l (j + 1)
      fun i hi => by rw [show j + 1 + i = j + (i + 1) by omega]; exact h (i + 1) (by simp; omega)]
    congr 1
    exact h 0 (by simp)

/-- **The loop's pops are `honestPushes`' children's part.** -/
theorem kidPushes_eq (al : String → Bool) (s : NodeStatement) (w : NodeWitness) (ch0 : Child) :
    (List.range' 0 ((mKidP al s w).n - 0)).flatMap (kidPush guestBytecode (mKidP al s w) (mKidD s w ch0)) =
      mKidPushes s w := by
  have hx : (xPlan s w).childSlots.length = w.children.length := by
    have := congrArg List.length (B1.Main.plan_children_lengths s.claims.xmss (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss)))
    simp only [List.length_map] at this
    rw [xPlan, (coveragePlan_eq _ _ _).2.2]; exact this
  have hs : (sPlan s w).childSlots.length = w.children.length := by
    have := congrArg List.length (B1.Main.plan_children_lengths s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs)))
    simp only [List.length_map] at this
    rw [sPlan, (coveragePlan_eq _ _ _).2.2]; exact this
  have hlen : ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots).length = w.children.length := by
    simp [hx, hs]
  unfold mKidPushes
  rw [Nat.sub_zero, show (mKidP al s w).n = _ from hlen.symm]
  refine flatMap_range'_eq _ _ _ 0 fun i hi => ?_
  have hi' : i < w.children.length := by omega
  simp only [List.getElem_zip, Nat.zero_add, kidPush, mKidD, mKid_eq hi', mKidP,
    List.getD_eq_getElem _ _ (show i < (xPlan s w).childSlots.length by omega),
    List.getD_eq_getElem _ _ (show i < (sPlan s w).childSlots.length by omega), List.append_assoc,
    List.cons_append, List.nil_append]
  rfl


/-! ## The guarded call -/

set_option maxRecDepth 200000 in
theorem mid1_mem : Atom.const (.n 407) (word 1 0) ∈ atomsOf mMid ∧
    Atom.hint (.allocDyn (.n 398) (.n 35)) ∈ atomsOf mMid ∧ Atom.hint (.allocDyn (.n 399) (.n 44)) ∈ atomsOf mMid ∧
    Atom.hint (.allocDyn (.n 400) (.n 50)) ∈ atomsOf mMid ∧ Atom.hint (.allocDyn (.n 403) (.n 402)) ∈ atomsOf mMid ∧
    Atom.hint (.witness "fs_seed" (.stack [.n 26, .n 27])) ∈ atomsOf mPre := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem loop4_takes : coreProgram.Takes "__loop4_main" 16 = true := by decide +kernel

/-- **`mMid`'s children's loop** keeps the invariant, its post the children's pushes when taken. -/
theorem winsHypT_mid1 {rd0 : Reader} {R : ℕ → Prop} {es : List Ev} {ws : List W1} {st : St} {K : St → Prop}
    {a : ℕ} {Qs : List (Reader → Tree → Prop)} (hk : 17 ≤ k) (hr : NodeRelation guestBytecode guestSeed s w)
    (hlim : DeployedLimits s w) (hok : ChildrenOk guestBytecode guestSeed w)
    (hvs : VsCompleteHypA al k guestBytecode guestSeed) (cc : ClaimCells s w)
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs) (hcl : MainCalleesAt al k s w cover)
    (hst : PreInv al s w cover a Qs st)
    (hrest : ∀ st', PreInv al s w cover a (Qs ++ [qIf (mainCounts s w).nc (PopsPost (mKidPushes s w))]) st' →
      WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w)
        (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) ws st' K) :
    WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) (mMid_w1 :: ws) st K := by
  have hn := nc_le hlim
  obtain ⟨-, -, -, -, g406⟩ := mVal_guards (rd := rd0) (w := mOrc al s w)
  obtain ⟨-, -, -, -, -, -, c6, -⟩ := mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)
  obtain ⟨v22, v23, -⟩ := mOrc_sizes (al := al) (s := s) (w := w) (rd := rd0)
  obtain ⟨k407, m398, m399, m400, m403, mfs⟩ := mid1_mem
  have h407 : mVal rd0 (mOrc al s w) (.n 407) = 1 := by rw [← word_one]; exact mMid_good k407
  have h398 : mVal rd0 (mOrc al s w) (.n 398) = mOrc al s w 398 := mMid_good m398
  have h399 : mVal rd0 (mOrc al s w) (.n 399) = mOrc al s w 399 := mMid_good m399
  have h400 : mVal rd0 (mOrc al s w) (.n 400) = mOrc al s w 400 := mMid_good m400
  have h403 : mVal rd0 (mOrc al s w) (.n 403) = mOrc al s w 403 := mMid_good m403
  have h26 : mVal rd0 (mOrc al s w) (.n 26) = mOrc al s w 26 := mPre_good mfs (.n 26) List.mem_cons_self
  have h27 : mVal rd0 (mOrc al s w) (.n 27) = mOrc al s w 27 :=
    mPre_good mfs (.n 27) (List.mem_cons_of_mem _ List.mem_cons_self)
  have h51 : mVal rd0 (mOrc al s w) (.n 51) = mOrc al s w 51 :=
    mPre_call_rets (by unfold wPre mPre_w1; exact List.mem_cons_of_mem _ List.mem_cons_self) (.n 51)
      List.mem_cons_self
  unfold mMid_w1
  refine winsHypT_cifI (n := (mainCounts s w).nc) (args := kidArgs (mKidP al s w) 0)
    (B := kidBlock (mainCounts s w).nc) hst (lt_of_le_of_lt hn (by norm_num)) (g406.trans rfl) ?_
    (by exact loop4_takes) ?_ (Tc := 2 ^ 58) (β := 2 ^ 46) le_rfl (kidBlock_add_le hn) hrest
  · show [mVal rd0 (mOrc al s w) (.n 407), mVal rd0 (mOrc al s w) (.n 6), mVal rd0 (mOrc al s w) (.n 403),
      mVal rd0 (mOrc al s w) (.n 52), mVal rd0 (mOrc al s w) (.n 64), mVal rd0 (mOrc al s w) (.n 22),
      mVal rd0 (mOrc al s w) (.n 53), mVal rd0 (mOrc al s w) (.n 65), mVal rd0 (mOrc al s w) (.n 23),
      mVal rd0 (mOrc al s w) (.n 400), mVal rd0 (mOrc al s w) (.n 380), mVal rd0 (mOrc al s w) (.n 26),
      mVal rd0 (mOrc al s w) (.n 27), mVal rd0 (mOrc al s w) (.n 398), mVal rd0 (mOrc al s w) (.n 51),
      mVal rd0 (mOrc al s w) (.n 399)] = _
    rw [h407, c6, h403, w52, mOrc_64, v22, w53, mOrc_65, v23, h400, mOrc_380, h26, h27, h398, h51, h399]
    simp only [kidArgs, mKidP, pow_zero]
    rfl
  · intro hn0 fp cur hfp hfc
    obtain ⟨ch0, -⟩ : ∃ ch0, ch0 ∈ w.children := List.exists_mem_of_ne_nil _ fun h => hn0 (by
      show w.children.length = 0; rw [h]; rfl)
    obtain ⟨e, hb, he⟩ := kidL_callAtA coreProgram_wf (mKidHyps hk hr hlim hok hvs cc hl hcl ch0) 0
      (Nat.pos_of_ne_zero hn0) fp cur hfc (le_trans hfp (le_trans (Nat.le_add_right _ _) hfc))
    have hP : ((mKidP al s w).n - 0) * kidB ≤ 16 * kidB := Nat.mul_le_mul_right _ (by rw [Nat.sub_zero]; exact hn)
    have hK := kidB_eq
    refine ⟨e, fun hc => by have := hb (by omega); omega,
      he.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h) fun rd t _ h => ?_⟩
    rw [KidPost, kidPushes_eq] at h
    exact h

end

end
end
end LeanVM.Guest.Complete
