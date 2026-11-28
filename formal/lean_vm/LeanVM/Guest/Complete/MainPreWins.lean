/-
  LeanVM.Guest.Complete.MainPreWins

  `mPre`'s first windows at the honest oracle: the exponent tables' call, the claim tables' `HeapBuf`s.
-/

module

public import LeanVM.Guest.Complete.MainBytes

/-!
# `mPre`'s first windows

* `runHypT_triv`: a run of trivial atoms with no heap hint (`noHeapB`, `trivPM`) from its `HeapBuf`
  pointers alone.
* `mPre_call_rets`: a call statement of `mPre` returns the oracle's words on the forward valuation.
* `winsHypT_w1`: the call of `exponent_tables` (`mPre_w1`) at the cursor `mTop`, by
  `exponent_tables_callAtA`, the next state's cursor `mLo`, its tables at `mGS` given and claimed.
* `runHypT_w2`: the claim tables' `HeapBuf`s (`mPre_w2`) at `mBase m 0`, `mBase m 1`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- **A run of trivial atoms** with no heap hint, from its `HeapBuf` pointers. -/
theorem runHypT_triv {k : ℕ} {σ0 : Val} {w : ℕ → E} {a : ℕ} {Own R D : ℕ → Prop} {Pre O : Reader → Prop}
    {as : List Atom} (h : as.all (fun x => noHeapB x && trivPM x) = true)
    (hb : (allocDsts (as.map Ev.atom)).map (fun v => w v.idx) =
      (bases a (allocs σ0 (as.map Ev.atom))).map (fun b => ofK (addressOfIndex b))) :
    RunHypT k σ0 w a Own R D Pre O as := by
  have hq : ∀ x ∈ as, noHeapB x = true ∧ trivPM x = true := fun x hx => by
    simpa only [Bool.and_eq_true] using List.all_eq_true.mp h x hx
  refine ⟨hb, ?_, ?_, fun x hx => pureT_triv (hq x hx).2, fun _ _ _ _ x hx => memT_triv (hq x hx).2⟩
  · intro A hA
    obtain ⟨x, hx, hl⟩ := loadAddr_mem hA
    exfalso
    have ht := (hq x hx).2
    cases x with
    | load d p off => simp [trivPM] at ht
    | _ => simp [Ev.loadAddr?] at hl
  · rw [heapHintAddrs_noHeap (List.all_eq_true.mpr fun x hx => (hq x hx).1)]
    intro A hA
    simp at hA

theorem mem_flat_call {s : Stmt} {ws : List W1} (h : W1.call s ∈ ws) : s ∈ flatW1 ws :=
  List.mem_flatMap.mpr ⟨_, h, List.mem_cons_self⟩

/-- **A call of `mPre` returns the oracle's words** on the forward valuation. -/
theorem mPre_call_rets {rd : Reader} {o : ℕ → E} {g : String} {args rets : List V}
    (h : W1.call (.call g args rets) ∈ wPre) : ∀ v ∈ rets, mVal rd o v = o v.idx := by
  have hm := mem_flat_call h
  rw [wPre_flat] at hm
  exact mVal_goodPre _ hm

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {rd0 : Reader}
  {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **The exponent tables' call** at the cursor `mTop`: the next state's cursor `mLo`, the tables at `mGS`
held and claimed, its post `FreePost`. -/
theorem winsHypT_w1 {ws : List W1} {st : St} {K : St → Prop} (hkc : st.kc = mTop (mainCounts s w))
    (hrest : WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w) Own R Pre ws
      ⟨st.a, mLo al (mainCounts s w),
        fun rd => st.O rd ∧ (ExpTables rd (ptrAt (mGS al (mainCounts s w))) ∧
          ExpWinTab rd (ptrAt (mGS al (mainCounts s w)))),
        fun i => st.D i ∨ (mGS al (mainCounts s w) ≤ i ∧ i < mGS al (mainCounts s w) + expTabLen),
        st.Qs ++ [FreePost]⟩ K) :
    WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w) Own R Pre
      (.call (.call "exponent_tables" [] [.n 51]) :: ws) st K := by
  have h51 : mVal rd0 (mOrc al s w) (.n 51) = ptrAt (mGS al (mainCounts s w)) :=
    mPre_call_rets (by unfold wPre mPre_w1; exact List.mem_cons_of_mem _ List.mem_cons_self) (.n 51)
      List.mem_cons_self
  have hc := exponent_tables_callAtA (fs := B2C.fs) (al := al) (cert := B2C.cert) coreProgram_wf k
    (allocBase (al "exponent_tables") st.kc) (mGS al (mainCounts s w)) (fun _ => False)
  rw [WinsHypT]
  have hend : st.kc < stepT → mLo al (mainCounts s w) ≤ st.kc + stepB := fun _ => by
    have h0 := stepB_ge
    have h1 := Memory.allocBase_le (al "exponent_tables") (mTop (mainCounts s w))
    have h2 := B2C.fs_lt "exponent_tables"
    have h3 : expTabLen < 2 ^ 40 := by decide
    rw [hkc]; unfold mLo mGS; omega
  refine ⟨"exponent_tables", FreePost, B2C.fs "exponent_tables", mLo al (mainCounts s w), fun _ => False, _, _, rfl,
    fun _ h => h.elim, ?_, hend, hrest⟩
  have e : (retsOf (.call "exponent_tables" [] [.n 51])).map (mVal rd0 (mOrc al s w)) =
      [ptrAt (mGS al (mainCounts s w))] := by
    show [mVal rd0 (mOrc al s w) (.n 51)] = _
    rw [h51]
  rw [e]
  have hm : mGS al (mainCounts s w) = allocBase (al "exponent_tables") st.kc + B2C.fs "exponent_tables" := by
    rw [hkc]; rfl
  rw [← hm]
  exact hc.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ _ _ h => h)

set_option maxRecDepth 200000 in
theorem w2_shape : atomsOf ((mPre.drop 40).take 2) =
    [.hint (.allocDyn (.n 52) (.n 29)), .hint (.allocDyn (.n 53) (.n 31))] := by
  decide +kernel

set_option linter.unusedSimpArgs false in
/-- **The claim tables' `HeapBuf`s** at `mBase m 0`, `mBase m 1`. -/
theorem runHypT_w2 {D : ℕ → Prop} {O : Reader → Prop}
    (hb : (mainCounts s w).sx + (mainCounts s w).ss < 2 ^ 19) :
    RunHypT k (mVal rd0 (mOrc al s w)) (mOrc al s w) (B2C.fs "main") Own R D Pre O
      (atomsOf ((mPre.drop 40).take 2)) := by
  rw [w2_shape]
  refine runHypT_triv (by decide) ?_
  obtain ⟨-, -, -, v29, v31, -⟩ := mOrc_sizes (al := al) (s := s) (w := w) (rd := rd0)
  have l1 : logG (gen ^ (4 * (mainCounts s w).sx)) = 4 * (mainCounts s w).sx := logG_gen_pow (by omega)
  have l2 : logG (gen ^ (4 * (mainCounts s w).ss)) = 4 * (mainCounts s w).ss := logG_gen_pow (by omega)
  have o52 : mOrc al s w 52 = mPtr (mainCounts s w) 0 0 := rfl
  have o53 : mOrc al s w 53 = mPtr (mainCounts s w) 1 0 := rfl
  simp only [allocDsts, allocs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil,
    Ev.allocDst?, Ev.alloc?, v29, v31, l1, l2, bases, V.idx, o52, o53, mPtr, mBase_zero, mBase_one,
    Nat.add_zero]


/-! ## The claim lists' digests -/

/-- **A callee's region is in `main`'s window's**: `main`'s buffers are its own data, the tables claimed. -/
theorem hR_main {cert : String → V → ℕ} {m : MainCounts} {es : List Ev} {D : ℕ → Prop}
    (hD : ∀ i, mGS al m ≤ i → i < mGS al m + expTabLen → D i) :
    ∀ i, mainR al m i → (R i ∨ ownData cert 0 (B2C.fs "main") "main" m.bufs es i) ∨ D i := by
  rintro i (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inl (Or.inr (own_main h1 h2))
  · exact Or.inr (hD i h1 h2)

/-- **`MainPreA` on the window's memories**: the header from `mainPreR`, the rest from the state. -/
theorem hP_main {cover : List E} {O : Reader → Prop}
    (hO : ∀ rd, O rd → HoldsWords rd (mainWords s w cover) ∧ ExpTables rd (ptrAt (mGS al (mainCounts s w))) ∧
      ExpWinTab rd (ptrAt (mGS al (mainCounts s w)))) :
    ∀ rd, mainPreR s rd ∧ O rd → MainPreA al s w cover rd :=
  fun rd h => ⟨(hO rd h.2).1, (hO rd h.2).2.1, (hO rd h.2).2.2, h.1⟩

theorem w52 : mVal rd0 (mOrc al s w) (.n 52) = mPtr (mainCounts s w) 0 0 :=
  mPre_good (a := .hint (.allocDyn (.n 52) (.n 29)))
    (List.mem_of_mem_filter (by rw [main_allocAtoms.1]; exact List.mem_cons_self))

theorem w53 : mVal rd0 (mOrc al s w) (.n 53) = mPtr (mainCounts s w) 1 0 :=
  mPre_good (a := .hint (.allocDyn (.n 53) (.n 31)))
    (List.mem_of_mem_filter (by rw [main_allocAtoms.1]; exact List.mem_cons_of_mem _ List.mem_cons_self))

/-- **The leanXMSS claim list's digest** (`mPre_w3`) from `MainCalleesAt.clx`. -/
theorem winsHypT_w3 {cover : List E} {es : List Ev} {ws : List W1} {st : St} {K : St → Prop}
    (hcl : MainCalleesAt al k s w cover) (hlo : mLo al (mainCounts s w) ≤ st.kc)
    (hD : ∀ i, mGS al (mainCounts s w) ≤ i → i < mGS al (mainCounts s w) + expTabLen → st.D i)
    (hO : ∀ rd, st.O rd → HoldsWords rd (mainWords s w cover) ∧ ExpTables rd (ptrAt (mGS al (mainCounts s w))) ∧
      ExpWinTab rd (ptrAt (mGS al (mainCounts s w))))
    (hrest : ∀ ec, allocBase (al "claim_list_digest") st.kc + B2C.fs "claim_list_digest" ≤ ec →
      WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w)
        (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) ws
        ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
          st.Qs ++ [PopsPost (Prover.listPushes "claims" (s.claims.xmss.map xCells))]⟩ K) :
    WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s)
      (.call (.call "claim_list_digest" [.n 52, .n 0] [.n 54, .n 55]) :: ws) st K := by
  have hr := mPre_call_rets (rd := rd0) (o := mOrc al s w)
    (by unfold wPre; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  refine winsHypT_call_of_atEvery' rfl ?_ ?_ hcl.clx (by norm_num) (fs_add_le _) (le_trans hlo (le_allocBase _ _)) (hR_main hD) (hP_main hO) hrest
  · show [mVal rd0 (mOrc al s w) (.n 52), mVal rd0 (mOrc al s w) (.n 0)] = _
    rw [w52, (mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)).1]
  · show [mVal rd0 (mOrc al s w) (.n 54), mVal rd0 (mOrc al s w) (.n 55)] = _
    rw [hr _ List.mem_cons_self, hr _ (List.mem_cons_of_mem _ List.mem_cons_self)]
    rfl

/-- **The leanSPHINCS claim list's digest** (`mPre_w4`) from `MainCalleesAt.csp`. -/
theorem winsHypT_w4 {cover : List E} {es : List Ev} {ws : List W1} {st : St} {K : St → Prop}
    (hcl : MainCalleesAt al k s w cover) (hlo : mLo al (mainCounts s w) ≤ st.kc)
    (hD : ∀ i, mGS al (mainCounts s w) ≤ i → i < mGS al (mainCounts s w) + expTabLen → st.D i)
    (hO : ∀ rd, st.O rd → HoldsWords rd (mainWords s w cover) ∧ ExpTables rd (ptrAt (mGS al (mainCounts s w))) ∧
      ExpWinTab rd (ptrAt (mGS al (mainCounts s w))))
    (hrest : ∀ ec, allocBase (al "claim_list_digest") st.kc + B2C.fs "claim_list_digest" ≤ ec →
      WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w)
        (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) ws
        ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
          st.Qs ++ [PopsPost (Prover.listPushes "claims" (s.claims.sphincs.map sCells))]⟩ K) :
    WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s)
      (.call (.call "claim_list_digest" [.n 53, .n 3] [.n 56, .n 57]) :: ws) st K := by
  have hr := mPre_call_rets (rd := rd0) (o := mOrc al s w)
    (by
      unfold wPre
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))
  refine winsHypT_call_of_atEvery' rfl ?_ ?_ hcl.csp (by norm_num) (fs_add_le _) (le_trans hlo (le_allocBase _ _)) (hR_main hD) (hP_main hO) hrest
  · show [mVal rd0 (mOrc al s w) (.n 53), mVal rd0 (mOrc al s w) (.n 3)] = _
    rw [w53, (mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)).2.2.2.1]
  · show [mVal rd0 (mOrc al s w) (.n 56), mVal rd0 (mOrc al s w) (.n 57)] = _
    rw [hr _ List.mem_cons_self, hr _ (List.mem_cons_of_mem _ List.mem_cons_self)]
    rfl

end

end
end LeanVM.Guest.Complete
