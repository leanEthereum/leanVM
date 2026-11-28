/-
  LeanVM.Guest.Complete.MainPreChain

  `mPre`'s windows chained at the honest oracle: from `main`'s first state to the state before its DA
  branch.
-/

module

public import LeanVM.Guest.Complete.MainPreWins
public import LeanVM.Guest.Complete.MainDup

/-!
# `mPre`'s windows, chained

`PreInv al s w cover a Qs st`: the state of `main`'s windows past the exponent tables, its `HeapBuf`
cursor `a`, its callees' cursor past the tables, the tables claimed, `main`'s words and the tables held,
the callees' posts `Qs`. Each window keeps it (`winsHypT_runI`, `winsHypT_callI`, `winsHypT_cifI`, a
guarded callee's post `qIf n P`: `P` when taken). The windows `w5`, `w7`, `w11` are trivial runs,
`w6`, `w8` the duplicates' loops (`mainDupx`, `mainDups`), `w10`, `w12` the raw signatures' loops
(`MainCalleesAt.rawx`, `.raws`, `lx_tags` at `σ 323 ..< 374`), `w13` `da_digests`' `HeapBuf`.

`wPre_hyp`: on a node with `NodeRelation` and `DeployedLimits`, from `main`'s first state, `mPre`'s
windows' hypotheses, ending in a state with `PreInv … (mBase m 5) (qPre s w)`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- A guarded callee's post: `P` when its count `n` is nonzero, its phantom's otherwise. -/
def qIf (n : ℕ) (P : Reader → Tree → Prop) : Reader → Tree → Prop :=
  if n = 0 then fun _ _ => True else P

/-- **The state of `main`'s windows past the exponent tables.** -/
structure PreInv (al : String → Bool) (s : NodeStatement) (w : NodeWitness) (cover : List E) (a : ℕ)
    (Qs : List (Reader → Tree → Prop)) (st : St) : Prop where
  ha : st.a = a
  hlo : mLo al (mainCounts s w) ≤ st.kc
  hD : ∀ i, mGS al (mainCounts s w) ≤ i → i < mGS al (mainCounts s w) + expTabLen → st.D i
  hO : ∀ rd, st.O rd → HoldsWords rd (mainWords s w cover) ∧ ExpTables rd (ptrAt (mGS al (mainCounts s w))) ∧
    ExpWinTab rd (ptrAt (mGS al (mainCounts s w)))
  hQ : st.Qs = Qs

theorem ptrAt_mul_pow (q m : ℕ) : ptrAt q * gen ^ m = ptrAt (q + m) := by
  rw [Value.gen_pow_eq_ofK, ptrAt, ptrAt, ← gpow_add']; exact (map_mul (algebraMap K E) _ _).symm

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd0 : Reader}
  {R : ℕ → Prop} {es : List Ev}


/-! ## The steps keeping the invariant -/

/-- **A run keeps the invariant**, its cursor past its allocations. -/
theorem winsHypT_runI {as : List Atom} {ws : List W1} {st : St} {K : St → Prop} {a a' : ℕ}
    {Qs : List (Reader → Tree → Prop)} (hst : PreInv al s w cover a Qs st)
    (ha : a + (allocs (mVal rd0 (mOrc al s w)) (as.map Ev.atom)).sum = a')
    (h1 : RunHypT k (mVal rd0 (mOrc al s w)) (mOrc al s w) a (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R st.D (mainPreR s) st.O as)
    (hrest : ∀ st', PreInv al s w cover a' Qs st' →
      WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w) (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) ws st' K) :
    WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w) (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) (.run as :: ws) st K := by
  rw [WinsHypT]
  refine ⟨by rw [hst.ha]; exact h1, hrest _ ⟨?_, hst.hlo, hst.hD, hst.hO, hst.hQ⟩⟩
  show st.a + _ = a'
  rw [hst.ha]; exact ha

/-- The invariant after a call ending past its block. -/
theorem preInv_call {st : St} {a ec B : ℕ} {g : String} {Qs : List (Reader → Tree → Prop)}
    {P : Reader → Tree → Prop} (hst : PreInv al s w cover a Qs st) (hec : allocBase (al g) st.kc + B ≤ ec) :
    PreInv al s w cover a (Qs ++ [P])
      ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False, st.Qs ++ [P]⟩ :=
  ⟨hst.ha, le_trans hst.hlo (le_trans (le_allocBase _ _) (le_trans (Nat.le_add_right _ _) hec)),
    fun i h1 h2 => Or.inl (hst.hD i h1 h2), fun rd h => hst.hO rd h.1, by
      show st.Qs ++ [P] = _; rw [hst.hQ]⟩

/-- **A call of `main`'s callee keeps the invariant**, from its `AtEvery` field. -/
theorem winsHypT_callI {s0 : Stmt} {g : String} {ws : List W1} {st : St} {K : St → Prop} {a : ℕ}
    {Qs : List (Reader → Tree → Prop)} {args rets : List E} {Post : Reader → Tree → Prop} {B Tc β : ℕ}
    (hst : PreInv al s w cover a Qs st) (he : Enters (mVal rd0 (mOrc al s w)) g s0) (ha : (argsOf s0).map (mVal rd0 (mOrc al s w)) = args)
    (hr : (retsOf s0).map (mVal rd0 (mOrc al s w)) = rets)
    (h : AtEveryB al k g args rets (mainR al (mainCounts s w)) (MainPreA al s w cover) Post B
      (mLo al (mainCounts s w)) Tc β) (hTc : 2 ^ 58 ≤ Tc) (hβ : B + β ≤ 2 ^ 51)
    (hrest : ∀ st', PreInv al s w cover a (Qs ++ [Post]) st' →
      WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w) (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) ws st' K) :
    WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w) (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) (.call s0 :: ws) st K :=
  winsHypT_call_of_atEvery' he ha hr h hTc hβ (le_trans hst.hlo (le_allocBase _ _)) (hR_main hst.hD)
    (hP_main hst.hO) fun _ hec => hrest _ (preInv_call hst hec)

/-- **A guarded call of `main`'s callee keeps the invariant**, from its `AtEvery` field when taken. -/
theorem winsHypT_cifI {c : V} {g : String} {as : List V} {ws : List W1} {st : St} {K : St → Prop} {a : ℕ}
    {Qs : List (Reader → Tree → Prop)} {n : ℕ} {args : List E} {Post : Reader → Tree → Prop} {B Tc β : ℕ}
    (hst : PreInv al s w cover a Qs st) (hn : n < 2 ^ 34) (hc : (mVal rd0 (mOrc al s w)) c = word 1 0 + gen ^ n)
    (ha : as.map (mVal rd0 (mOrc al s w)) = args) (htk : coreProgram.Takes g args.length = true)
    (h : n ≠ 0 → AtEveryB al k g args [] (mainR al (mainCounts s w)) (MainPreA al s w cover) Post B
      (mLo al (mainCounts s w)) Tc β) (hTc : 2 ^ 58 ≤ Tc) (hβ : B + β ≤ 2 ^ 51)
    (hrest : ∀ st', PreInv al s w cover a (Qs ++ [qIf n Post]) st' →
      WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w) (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) ws st' K) :
    WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w) (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) (.cif c g as :: ws) st K := by
  refine winsHypT_cif_of_atEvery' hn hc ha htk h hTc hβ (le_trans hst.hlo (le_allocBase _ _)) (hR_main hst.hD)
    (hP_main hst.hO) (fun hn0 _ hec => hrest _ ?_) (fun hn0 => hrest _ ?_)
  · have e : qIf n Post = Post := by simp only [qIf, hn0, ↓reduceIte]
    rw [e]; exact preInv_call hst hec
  · have e : qIf n Post = fun _ _ => True := by simp only [qIf, hn0, ↓reduceIte]
    rw [e]
    exact ⟨hst.ha, le_trans hst.hlo (le_trans (le_allocBase _ _) (Nat.le_add_right _ _)), hst.hD, hst.hO,
      by show st.Qs ++ _ = _; rw [hst.hQ]⟩

/-! ## The values the windows read -/

set_option maxRecDepth 200000 in
theorem mPre_chain_mem :
    Atom.const (.n 60) (word 1 0) ∈ atomsOf mPre ∧ Atom.const (.n 63) (word 1 0) ∈ atomsOf mPre ∧
      Atom.const (.n 376) (word 1 0) ∈ atomsOf mPre ∧ Atom.const (.n 379) (word 1 0) ∈ atomsOf mPre ∧
      Atom.hint (.allocDyn (.n 64) (.n 24)) ∈ atomsOf mPre ∧ Atom.mul (.n 65) (.n 64) (.n 22) ∈ atomsOf mPre ∧
      Atom.hint (.allocDyn (.n 380) (.n 34)) ∈ atomsOf mPre := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem mPre_tags_mem :
    (List.range 51).all (fun j => decide (Atom.const (.n (323 + j)) (word (lxTagVals.getD j 0) 0) ∈ atomsOf mPre)) =
      true := by
  decide +kernel

theorem lxTagVals_length : lxTagVals.length = 51 := by decide

theorem mOrc_one {v : V} (h : Atom.const v (word 1 0) ∈ atomsOf mPre) : (mVal rd0 (mOrc al s w)) v = 1 := by
  rw [← word_one]; exact mPre_good h

theorem mOrc_64 : (mVal rd0 (mOrc al s w)) (.n 64) = mPtr (mainCounts s w) 2 0 := mPre_good mPre_chain_mem.2.2.2.2.1

theorem mOrc_380 : (mVal rd0 (mOrc al s w)) (.n 380) = mPtr (mainCounts s w) 4 0 := mPre_good mPre_chain_mem.2.2.2.2.2.2

theorem mOrc_65 : (mVal rd0 (mOrc al s w)) (.n 65) = mPtr (mainCounts s w) 2 (mainCounts s w).sx := by
  have e : (mVal rd0 (mOrc al s w)) (.n 65) = (mVal rd0 (mOrc al s w)) (.n 64) * (mVal rd0 (mOrc al s w)) (.n 22) := good_mul (mPre_good mPre_chain_mem.2.2.2.2.2.1)
    (by norm_num) (by norm_num)
  rw [e, mOrc_64, (mOrc_sizes (al := al) (s := s) (w := w) (rd := rd0)).1]
  simp only [mPtr, Nat.add_zero, ptrAt_mul_pow]

theorem mOrc_tags : ((List.range 51).map fun j => V.n (323 + j)).map (mVal rd0 (mOrc al s w)) = lxTagWords := by
  apply List.ext_getElem (by simp [lxTagWords, lxTagVals_length])
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  have hm := List.all_eq_true.mp mPre_tags_mem j (List.mem_range.mpr h1)
  simp only [decide_eq_true_eq] at hm
  simp only [List.getElem_map, List.getElem_range, lxTagWords]
  rw [mPre_good hm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [lxTagVals_length]; exact h1),
    Option.getD_some]

/-! ## The windows -/

theorem plainTriv_runHypT {σ0 : Val} {w' : ℕ → E} {a : ℕ} {Own R' D : ℕ → Prop} {Pre O : Reader → Prop}
    {as : List Atom} (h : as.all (fun x => plainRunB x && trivPM x) = true) :
    RunHypT k σ0 w' a Own R' D Pre O as := by
  have hq : ∀ x ∈ as, plainRunB x = true ∧ trivPM x = true := fun x hx => by
    simpa only [Bool.and_eq_true] using List.all_eq_true.mp h x hx
  exact runHypT_plain (List.all_eq_true.mpr fun x hx => (hq x hx).1) (fun x hx => pureT_triv (hq x hx).2)
    fun _ _ _ _ x hx => memT_triv (hq x hx).2

theorem plainTriv_allocs {σ0 : Val} {as : List Atom} (h : as.all (fun x => plainRunB x && trivPM x) = true) :
    (allocs σ0 (as.map Ev.atom)).sum = 0 := by
  rw [(plain_fields (σ := σ0) (List.all_eq_true.mpr fun x hx => by
    have := List.all_eq_true.mp h x hx
    simp only [Bool.and_eq_true] at this
    exact this.1)).2.1]
  rfl

set_option maxRecDepth 200000 in
theorem pre_triv :
    (atomsOf ((mPre.drop 44).take 3)).all (fun x => plainRunB x && trivPM x) = true ∧
      (atomsOf ((mPre.drop 48).take 3)).all (fun x => plainRunB x && trivPM x) = true ∧
      (atomsOf ((mPre.drop 622).take 3)).all (fun x => plainRunB x && trivPM x) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem w13_shape : atomsOf ((mPre.drop 626).take 5) =
    [.hint (.allocDyn (.n 380) (.n 34)), .mul (.n 381) (.n 6) (.n 6), .mul (.n 382) (.n 380) (.n 381),
      .const (.n 383) (word 2 0), .add (.n 384) (.n 7) (.n 383)] := by
  decide +kernel

theorem mBase_four (m : MainCounts) : mBase m 4 = mBase m 3 + 256 := by
  simp [mBase, MainCounts.bufs, bases]

theorem mBase_five (m : MainCounts) : mBase m 5 = mBase m 4 + 2 * (m.nc + 1) := by
  simp [mBase, MainCounts.bufs, bases]

set_option linter.unusedSimpArgs false in
/-- **`da_digests`' `HeapBuf`** (`w13`) at `mBase m 4`. -/
theorem runHypT_w13 {D : ℕ → Prop} {O : Reader → Prop} (hn : (mainCounts s w).nc ≤ 16) :
    RunHypT k (mVal rd0 (mOrc al s w)) (mOrc al s w) (mBase (mainCounts s w) 4) (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R D (mainPreR s) O (atomsOf ((mPre.drop 626).take 5)) ∧
      mBase (mainCounts s w) 4 + (allocs (mVal rd0 (mOrc al s w)) ((atomsOf ((mPre.drop 626).take 5)).map Ev.atom)).sum =
        mBase (mainCounts s w) 5 := by
  rw [w13_shape]
  obtain ⟨-, -, -, -, -, v34, -⟩ := mOrc_sizes (al := al) (s := s) (w := w) (rd := rd0)
  have l : logG (gen ^ (2 * ((mainCounts s w).nc + 1))) = 2 * ((mainCounts s w).nc + 1) := logG_gen_pow (by omega)
  have o380 : mOrc al s w 380 = mPtr (mainCounts s w) 4 0 := rfl
  constructor
  · refine runHypT_triv (as := [.hint (.allocDyn (.n 380) (.n 34)), .mul (.n 381) (.n 6) (.n 6),
      .mul (.n 382) (.n 380) (.n 381), .const (.n 383) (word 2 0), .add (.n 384) (.n 7) (.n 383)]) (by decide) ?_
    simp only [allocDsts, allocs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil,
      Ev.allocDst?, Ev.alloc?, v34, l, bases, V.idx, o380, mPtr, Nat.add_zero]
  · simp only [allocs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, Ev.alloc?, v34, l]
    simp [mBase_five]

/-! ## The chain -/

/-- `mPre`'s callees' posts, in order. -/
def qPre (s : NodeStatement) (w : NodeWitness) : List (Reader → Tree → Prop) :=
  [FreePost, PopsPost (Prover.listPushes "claims" (s.claims.xmss.map xCells)),
    PopsPost (Prover.listPushes "claims" (s.claims.sphincs.map sCells)),
    qIf (mainCounts s w).nxd (PopsPost ((xPlan s w).duplicates.map fun c => ("dup_claims", xCells c))),
    qIf (mainCounts s w).nsd (PopsPost ((sPlan s w).duplicates.map fun c => ("dup_claims", sCells c))),
    qIf (mainCounts s w).nrx (PopsPost ((w.xmssSignatures.zip (xPlan s w).directSlots).flatMap fun cs =>
      ("raw_index", [Prover.count cs.2]) :: Prover.xmssHints cs.1.1.1 cs.1.1.2 cs.1.2)),
    qIf (mainCounts s w).nrs (PopsPost ((w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap fun cs =>
      ("sp_raw_index", [Prover.count cs.2]) :: Prover.sphincsHints cs.1.1.1 cs.1.1.2 cs.1.2))]

theorem w10_args : mPre_w10 = .cif (.n 375) "__loop2_main"
    ([.n 376, .n 2, .n 22, .n 64, .n 52] ++ (List.range 51).map fun j => V.n (323 + j)) := rfl

set_option maxRecDepth 200000 in
theorem pre_takes : coreProgram.Takes "__loop0_main" 4 = true ∧ coreProgram.Takes "__loop1_main" 4 = true ∧
    coreProgram.Takes "__loop2_main" 56 = true ∧ coreProgram.Takes "__loop3_main" 7 = true := by
  decide +kernel

/-- **`mPre`'s windows' hypotheses** at `main`'s honest oracle, from its first state to a state with the
invariant at `mBase m 5` and the posts `qPre s w`. -/
theorem wPre_hyp {K : St → Prop} (hk : 17 ≤ k) (hr : NodeRelation guestBytecode guestSeed s w)
    (hlim : DeployedLimits s w) (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs)
    (hcl : MainCalleesAt al k s w cover)
    (hrest : ∀ st, PreInv al s w cover (mBase (mainCounts s w) 5) (qPre s w) st → K st) :
    WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w) (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) wPre
      ⟨B2C.fs "main", mTop (mainCounts s w), fun rd => HoldsWords rd (mainWords s w cover), fun _ => False, []⟩ K := by
  have hb := slots_lt hr hlim
  have hn := nc_le hlim
  obtain ⟨hdx, hds⟩ := dups_lt hr hlim
  obtain ⟨c0, c1, c2, c3, c4, c5, -, -⟩ := mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)
  obtain ⟨v22, v23, -, v29, v31, -⟩ := mOrc_sizes (al := al) (s := s) (w := w) (rd := rd0)
  obtain ⟨g59, g62, g375, g378, -⟩ := mVal_guards (rd := rd0) (w := mOrc al s w)
  obtain ⟨k60, k63, k376, k379, -⟩ := mPre_chain_mem
  obtain ⟨t5, t7, t11⟩ := pre_triv
  obtain ⟨tk0, tk1, tk2, tk3⟩ := pre_takes
  have hraw := raw_le_slots hr
  have w0s := (plain_fields (σ := (mVal rd0 (mOrc al s w))) w0_shape.1).2.1
  unfold wPre mPre_w0 mPre_w1 mPre_w2 mPre_w3 mPre_w4 mPre_w5 mPre_w6 mPre_w7 mPre_w8 mPre_w9 mPre_w11 mPre_w12
    mPre_w13
  -- w0
  rw [WinsHypT]
  refine ⟨runHypT_w0 hk hr hlim hl, ?_⟩
  -- w1
  refine winsHypT_w1 rfl ?_
  -- w2
  have hst2 : PreInv al s w cover (B2C.fs "main") [FreePost] ⟨B2C.fs "main" + (allocs (mVal rd0 (mOrc al s w))
      ((atomsOf ((mPre.drop 0).take 39)).map Ev.atom)).sum, mLo al (mainCounts s w),
      fun rd => HoldsWords rd (mainWords s w cover) ∧ (ExpTables rd (ptrAt (mGS al (mainCounts s w))) ∧
        ExpWinTab rd (ptrAt (mGS al (mainCounts s w)))),
      fun i => False ∨ (mGS al (mainCounts s w) ≤ i ∧ i < mGS al (mainCounts s w) + expTabLen),
      [] ++ [FreePost]⟩ :=
    ⟨by show _ + _ = _; rw [w0s]; rfl, le_rfl, fun i h1 h2 => Or.inr ⟨h1, h2⟩,
      fun rd h => ⟨h.1, h.2.1, h.2.2⟩, rfl⟩
  have l1 : logG (gen ^ (4 * (mainCounts s w).sx)) = 4 * (mainCounts s w).sx := logG_gen_pow (by omega)
  have l2 : logG (gen ^ (4 * (mainCounts s w).ss)) = 4 * (mainCounts s w).ss := logG_gen_pow (by omega)
  refine winsHypT_runI (a' := mBase (mainCounts s w) 2) hst2 ?_ (runHypT_w2 hb) fun st3 hst3 => ?_
  · rw [w2_shape, mBase_two]
    simp only [allocs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, Ev.alloc?, v29, v31,
      l1, l2, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc]
  -- w3, w4
  refine winsHypT_w3 hcl hst3.hlo hst3.hD hst3.hO fun _ hec => ?_
  have hst4 := preInv_call (P := PopsPost (Prover.listPushes "claims" (s.claims.xmss.map xCells))) hst3 hec
  refine winsHypT_w4 hcl hst4.hlo hst4.hD hst4.hO fun _ hec => ?_
  have hst5 := preInv_call (P := PopsPost (Prover.listPushes "claims" (s.claims.sphincs.map sCells))) hst4 hec
  -- w5
  refine winsHypT_runI (a' := mBase (mainCounts s w) 2) hst5 (by rw [plainTriv_allocs t5, Nat.add_zero]) (plainTriv_runHypT t5) fun st6 hst6 => ?_
  -- w6
  refine winsHypT_cifI (n := (mainCounts s w).nxd) hst6 (lt_trans hdx (by norm_num)) (g59.trans rfl) ?_ (by exact tk0)
    (mainDupx (lt_trans hdx (by norm_num))) (by norm_num) (loopBlock_add_le _ hdx) fun st7 hst7 => ?_
  · show [(mVal rd0 (mOrc al s w)) (.n 60), (mVal rd0 (mOrc al s w)) (.n 1), (mVal rd0 (mOrc al s w)) (.n 52), (mVal rd0 (mOrc al s w)) (.n 0)] = _
    rw [mOrc_one k60, c1, w52, c0]
  -- w7
  refine winsHypT_runI (a' := mBase (mainCounts s w) 2) hst7 (by rw [plainTriv_allocs t7, Nat.add_zero]) (plainTriv_runHypT t7) fun st8 hst8 => ?_
  -- w8
  refine winsHypT_cifI (n := (mainCounts s w).nsd) hst8 (lt_trans hds (by norm_num)) (g62.trans rfl) ?_ (by exact tk1)
    (mainDups (lt_trans hds (by norm_num))) (by norm_num) (loopBlock_add_le _ hds) fun st9 hst9 => ?_
  · show [(mVal rd0 (mOrc al s w)) (.n 63), (mVal rd0 (mOrc al s w)) (.n 4), (mVal rd0 (mOrc al s w)) (.n 53), (mVal rd0 (mOrc al s w)) (.n 3)] = _
    rw [mOrc_one k63, c4, w53, c3]
  -- w9
  have hO9 : ∀ rd, st9.O rd → HoldsWords rd (mainWords s w cover) := fun rd h => (hst9.hO rd h).1
  refine winsHypT_runI (a' := mBase (mainCounts s w) 4) hst9 ?_ (runHypT_w9 hb hO9) fun st10 hst10 => ?_
  · obtain ⟨-, -, hfil⟩ := w9_shape
    obtain ⟨-, -, v24, -⟩ := mOrc_sizes (al := al) (s := s) (w := w) (rd := rd0)
    have l3 : logG (gen ^ ((mainCounts s w).sx + (mainCounts s w).ss)) = (mainCounts s w).sx + (mainCounts s w).ss :=
      logG_gen_pow (by omega)
    rw [allocs_atoms, hfil]
    simp only [List.filterMap_cons, List.filterMap_nil, Ev.alloc?, v24, l3, List.sum_cons, List.sum_nil]
    rw [mBase_four, mBase_three, mBase_two]
    omega
  -- w10
  rw [w10_args]
  refine winsHypT_cifI (n := (mainCounts s w).nrx) hst10
    (lt_of_le_of_lt (by omega : (mainCounts s w).nrx ≤ (mainCounts s w).sx + (mainCounts s w).ss)
      (lt_trans hb (by norm_num))) (g375.trans rfl) ?_ (by exact tk2)
    hcl.rawx (by norm_num) (loopBlock_add_le _ (lt_of_le_of_lt (by omega) hb)) fun st11 hst11 => ?_
  · rw [List.map_append, mOrc_tags]
    show [(mVal rd0 (mOrc al s w)) (.n 376), (mVal rd0 (mOrc al s w)) (.n 2), (mVal rd0 (mOrc al s w)) (.n 22), (mVal rd0 (mOrc al s w)) (.n 64), (mVal rd0 (mOrc al s w)) (.n 52)] ++ lxTagWords = _
    rw [mOrc_one k376, c2, v22, mOrc_64, w52]
  -- w11
  refine winsHypT_runI (a' := mBase (mainCounts s w) 4) hst11 (by rw [plainTriv_allocs t11, Nat.add_zero]) (plainTriv_runHypT t11) fun st12 hst12 => ?_
  -- w12
  refine winsHypT_cifI (n := (mainCounts s w).nrs) hst12
    (lt_of_le_of_lt (by omega : (mainCounts s w).nrs ≤ (mainCounts s w).sx + (mainCounts s w).ss)
      (lt_trans hb (by norm_num))) (g378.trans rfl) ?_ (by exact tk3)
    hcl.raws (by norm_num) (loopBlock_add_le _ (lt_of_le_of_lt (by omega) hb)) fun st13 hst13 => ?_
  · show [(mVal rd0 (mOrc al s w)) (.n 379), (mVal rd0 (mOrc al s w)) (.n 5), (mVal rd0 (mOrc al s w)) (.n 23), (mVal rd0 (mOrc al s w)) (.n 65), (mVal rd0 (mOrc al s w)) (.n 2), (mVal rd0 (mOrc al s w)) (.n 53), (mVal rd0 (mOrc al s w)) (.n 66)] = _
    rw [mOrc_one k379, c5, v23, mOrc_65, c2, w53, w9_ptr]
    rfl
  -- w13
  obtain ⟨h13, a13⟩ := runHypT_w13 (al := al) (s := s) (w := w) (rd0 := rd0) (k := k) (R := R) (es := es)
    (D := st13.D) (O := st13.O) hn
  refine winsHypT_runI hst13 a13 h13 fun st14 hst14 => ?_
  rw [WinsHypT]
  exact hrest st14 hst14

end

end
end LeanVM.Guest.Complete
