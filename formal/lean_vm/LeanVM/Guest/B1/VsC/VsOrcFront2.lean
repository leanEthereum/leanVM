/-
  LeanVM.Guest.B1.VsC.VsOrcFront2

  The front's hypotheses at the honest oracle: the `HeapBuf` bases, the callees' returns, the node's words.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcHonest

/-!
# The front at the honest oracle

`FrontHyp`'s fields that name the oracle, the memory or the node's cells, at `w = vsW rd1 args cur p ret`
(`VsOrcHonest.lean`) and the start state `vsSt0 σ0 cur Wo`:

* the `HeapBuf` bases (`hwA`, `hw6 … hw9`, `hw55`, `hw56`, `hw112`) are `vsRule`'s, bumped from `cur` by
  `vsAllocSz p` (`vsBaseF`, `vsW_buf`);
* the callees' returns (`hw94`, `hw101`, `hret`) are `ret`'s, by `vsW_ret`, from `FrontRet` (the front's
  callees' honest returns, constant rules);
* what the memory reads (`r0`, `hO`) from the front's runs `frontWords` held on the evaluation memory and
  among the node's words `Wo`;
* the node's cells (`hOwn`, `hO6 … hO9`) from `allocs σ0 (vsEs σ0) = vsAllocSz p` (`vsOwn_at`), the
  exponent tables in the region (`hRq`) and from the precondition (`rq`, `hPre`).

**`frontHyp_honest`** assembles them with `FrontNum` (`frontNum_of_child`). **`vsVal_409_of_front`**: the
link's width word `.n 409 = g^wd` from `FrontHyp`, which `Ph4Hyp` asks.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Bases -/

theorem bases_lengthF : ∀ (b : ℕ) (l : List ℕ), (bases b l).length = l.length
  | _, [] => rfl
  | b, s :: l => by rw [bases, List.length_cons, bases_lengthF (b + s) l, List.length_cons]

theorem bases_getD : ∀ (b : ℕ) (l : List ℕ) (j : ℕ), j < l.length → (bases b l).getD j 0 = b + (l.take j).sum
  | _, [], _, h => absurd h (by simp)
  | b, s :: l, 0, _ => by simp [bases]
  | b, s :: l, j + 1, h => by
    rw [bases, List.getD_cons_succ, bases_getD (b + s) l j (by simpa using h), List.take_succ_cons,
      List.sum_cons, Nat.add_assoc]

/-- **A `HeapBuf`'s cells are its node's own data.** -/
theorem ownData_vsBuf {cert : String → V → ℕ} {fp b : ℕ} {f : String} {bufs : List ℕ} {es : List Ev} {j i : ℕ}
    (hj : j < bufs.length) (hi : i < bufs.getD j 0) : ownData cert fp b f bufs es ((bases b bufs).getD j 0 + i) := by
  refine Or.inl ⟨(bufs[j], (bases b bufs)[j]'(by rw [bases_lengthF]; exact hj)), ?_, ?_, ?_⟩
  · rw [List.mem_iff_getElem]
    exact ⟨j, by simp [bases_lengthF, hj], by simp⟩
  · dsimp only
    rw [List.getD_eq_getElem _ _ (by rw [bases_lengthF]; exact hj)]; omega
  · dsimp only
    rw [List.getD_eq_getElem _ _ (by rw [bases_lengthF]; exact hj)]
    rw [List.getD_eq_getElem _ _ hj] at hi; omega

/-- `verify_sub`'s `j`-th `HeapBuf` base from `cur`. -/
def vsBaseF (cur p j : ℕ) : ℕ := (bases cur (vsAllocSz p)).getD j 0

theorem vsAllocSz_lengthF (p : ℕ) : (vsAllocSz p).length = 24 := rfl

theorem vsBaseF_eq (cur p j : ℕ) (hj : j < 24) : vsBaseF cur p j = cur + ((vsAllocSz p).take j).sum :=
  bases_getD cur _ j (by rw [vsAllocSz_lengthF]; exact hj)

theorem vsBaseF_0 (cur p : ℕ) : vsBaseF cur p 0 = cur := by simp [vsBaseF, vsAllocSz, vsSz0, bases]

theorem vsAllocSz_take_sum (p j : ℕ) (hj : j ≤ 21) :
    ((vsAllocSz p).take j).sum = ((vsSz0 ++ [256 * p, 6, 8]).take j).sum := by
  simp only [vsAllocSz]
  congr 1
  rw [show vsSz0 ++ [256 * p, 6, 8, 16, 64, 64] = (vsSz0 ++ [256 * p, 6, 8]) ++ [16, 64, 64] by simp,
    List.take_append_of_le_length (by simp [vsSz0]; omega)]

theorem vsBaseF_1 (cur p : ℕ) : vsBaseF cur p 1 = cur + 6 := by
  rw [vsBaseF_eq _ _ _ (by norm_num), vsAllocSz_take_sum _ _ (by norm_num)]
  simp only [vsSz0, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil]
  omega

theorem vsBaseF_2 (cur p : ℕ) : vsBaseF cur p 2 = cur + 162 := by
  rw [vsBaseF_eq _ _ _ (by norm_num), vsAllocSz_take_sum _ _ (by norm_num)]
  simp only [vsSz0, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil]
  omega

theorem vsBaseF_3 (cur p : ℕ) : vsBaseF cur p 3 = cur + 186 := by
  rw [vsBaseF_eq _ _ _ (by norm_num), vsAllocSz_take_sum _ _ (by norm_num)]
  simp only [vsSz0, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil]
  omega

theorem vsBaseF_13 (cur p : ℕ) : vsBaseF cur p 13 = cur + 639 := by
  rw [vsBaseF_eq _ _ _ (by norm_num), vsAllocSz_take_sum _ _ (by norm_num)]
  simp only [vsSz0, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil]
  omega

theorem vsBaseF_18 (cur p : ℕ) : vsBaseF cur p 18 = cur + 824 := by
  rw [vsBaseF_eq _ _ _ (by norm_num), vsAllocSz_take_sum _ _ (by norm_num)]
  simp only [vsSz0, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil]
  omega

theorem vsBaseF_19 (cur p : ℕ) : vsBaseF cur p 19 = cur + (824 + 256 * p) := by
  rw [vsBaseF_eq _ _ _ (by norm_num), vsAllocSz_take_sum _ _ (by norm_num)]
  simp only [vsSz0, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil]
  omega

theorem vsBaseF_20 (cur p : ℕ) : vsBaseF cur p 20 = cur + (824 + 256 * p) + 6 := by
  rw [vsBaseF_eq _ _ _ (by norm_num), vsAllocSz_take_sum _ _ (by norm_num)]
  simp only [vsSz0, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil]
  omega

/-- `verify_sub`'s own cells at a placement whose `HeapBuf`s are `vsAllocSz p`. -/
theorem vsOwn_at {fp cur p : ℕ} {σ0 : Val} (hal : allocs σ0 (vsEs σ0) = vsAllocSz p) {j b n i : ℕ} (hj : j < 24)
    (hb : vsBaseF cur p j = b) (hn : (vsAllocSz p).getD j 0 = n) (hi : i < n) : vsOwn fp cur σ0 (b + i) := by
  show ownData B2C.cert fp cur "verify_sub" (allocs σ0 (vsEs σ0)) (vsEs σ0) (b + i)
  rw [hal, ← hb]
  exact ownData_vsBuf (by rw [vsAllocSz_lengthF]; exact hj) (by rw [hn]; exact hi)

/-! ## The honest oracle's words -/

/-- An index `vsRule` hands to `ret`. -/
abbrev VsRetIdx (i : ℕ) : Prop :=
  i ∉ vsAllocIdx ∧ i ≠ 42 ∧ ¬(512 ≤ i ∧ i ≤ 516) ∧ ¬(581 ≤ i ∧ i ≤ 586) ∧ ¬(2943 ≤ i ∧ i ≤ 2947)

section
variable {rd1 : Reader} {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E}

theorem vsW_buf (ha : args.length = 6) (hr : CausalRule ret) {j i : ℕ} (hj : j < 24) (hi : vsAllocIdx.getD j 0 = i) :
    vsW rd1 args cur p ret i = ptrAt (vsBaseF cur p j) := hi ▸ vsW_alloc ha hr hj

theorem vsW_ret' (ha : args.length = 6) (hr : CausalRule ret) {i : ℕ} (hi : VsRetIdx i) :
    vsW rd1 args cur p ret i = ret i fun j => vsVal rd1 (vsW rd1 args cur p ret) args (.n j) :=
  vsW_ret ha hr hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2

/-- The `HeapBuf` bases `vsFront_wins` asks (`hwA`). -/
theorem vsW_hwA (ha : args.length = 6) (hr : CausalRule ret) :
    [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 55].map (vsW rd1 args cur p ret) =
      (bases cur (vsSz0 ++ [256 * p])).map (fun b => ofK (addressOfIndex b)) := by
  have e1 : ([6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 55] : List ℕ) =
      vsAllocIdx.take 19 := rfl
  have e2 : bases cur (vsSz0 ++ [256 * p]) = (bases cur (vsAllocSz p)).take 19 := by
    rw [show vsAllocSz p = (vsSz0 ++ [256 * p]) ++ [6, 8, 16, 64, 64] by simp [vsAllocSz],
      bases_append cur (vsSz0 ++ [256 * p]) [6, 8, 16, 64, 64], List.take_left' (by rw [bases_lengthF]; rfl)]
  rw [e1, e2]
  apply List.ext_getElem
  · simp [bases_lengthF, vsAllocIdx, vsAllocSz_lengthF]
  · intro i h1 _
    have hi : i < 19 := by simpa [vsAllocIdx] using h1
    simp only [List.getElem_map, List.getElem_take]
    have e := vsW_alloc (rd1 := rd1) (cur := cur) (p := p) ha hr (j := i) (by omega)
    rw [List.getD_eq_getElem _ _ (by simp [vsAllocIdx]; omega),
      List.getD_eq_getElem _ _ (by rw [bases_lengthF, vsAllocSz_lengthF]; omega)] at e
    exact e

end

/-! ## The front's runs -/

/-- **The front's runs**: the stream at `cur + 824`, the row counts after it, the heights at `cur`, the
eight-word buffer, the table sizes' bits at `cur + 6`, the cycle count's bits at `cur + 162`, the link's
shape at `cur + 186`. -/
def frontWords (cur p : ℕ) (ws : List E) (m : ℕ) (h Rr : ℕ → ℕ) (n wd : ℕ) (flag f4 : E) : Words :=
  [(cur + 824, ws), (cur + (824 + 256 * p), rowsW Rr), (cur, heightsW h),
    (cur + (824 + 256 * p) + 6, 1 :: gen ^ m :: heightsW h)] ++
    (List.range 6).map (fun t => (cur + 6 + 26 * t, tsBitsW (Rr t) (h t))) ++
    [(cur + 162, cbL (Rr 0 + Rr 1 + Rr 2 + Rr 3 + Rr 4 + Rr 5)), (cur + 186, [gen ^ n, gen ^ wd, flag, f4])]

theorem frontReads_of_holds {rd : Reader} {cur p : ℕ} {ws : List E} {m : ℕ} {h Rr : ℕ → ℕ} {n wd : ℕ}
    {flag f4 : E} (H : HoldsWords rd (frontWords cur p ws m h Rr n wd flag f4)) :
    FrontReads rd cur p ws cur (cur + 6) (cur + 162) (cur + 186) m h Rr n wd flag f4 where
  stream := H (cur + 824, ws) (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))
  sizes := H (cur + (824 + 256 * p), rowsW Rr) (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  heights := H (cur, heightsW h) (List.mem_append_left _ (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  logs := H (cur + (824 + 256 * p) + 6, 1 :: gen ^ m :: heightsW h) (List.mem_append_left _ (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  bits := fun t ht => H (cur + 6 + 26 * t, tsBitsW (Rr t) (h t))
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)))
  cycles := H (cur + 162, cbL (Rr 0 + Rr 1 + Rr 2 + Rr 3 + Rr 4 + Rr 5)) (List.mem_append_right _ List.mem_cons_self)
  shape := H (cur + 186, [gen ^ n, gen ^ wd, flag, f4]) (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-! ## The front's callees' returns -/

/-- **The front's callees' honest returns**, as `ret`'s rules: `g_power_of_word`'s `g^r` and `g^m`, the six
`table_size`s'. -/
structure FrontRet (ret : ℕ → (ℕ → E) → E) (r m : ℕ) (h Rr : ℕ → ℕ) : Prop where
  r94 : ∀ σ, ret 94 σ = gen ^ r
  r101 : ∀ σ, ret 101 σ = gen ^ m
  rts : ∀ t < 6, ∀ σ, ret (tsRet t) σ = gen ^ Rr t ∧ ret (tsRet t + 1) σ = tsLeadW (Rr t) (h t) ∧
    ret (tsRet t + 2) σ = tsRestW (Rr t) (h t)

/-- The precondition's exponent tables. -/
theorem vsPreA_exp {seed : Digest} {c : Child} {qt qo : ℕ} {rd : Reader} (h : vsPreA seed c qt qo rd) :
    ExpTables rd (ptrAt qt) ∧ ExpWinTab rd (ptrAt qt) := h.1

theorem expTabLen_eq : expTabLen = 2226 := rfl

/-! ## The front's hypotheses -/

/-- **`FrontHyp` at the honest oracle**: its numbers (`FrontNum`), the front's callees' returns as `ret`'s
rules, own cells containing the buffers `[cur, cur + Σ vsAllocSz p)`, a state from `cur` whose words hold the
front's runs, the evaluation memory with the precondition and the front's runs. -/
theorem frontHyp_honest {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    {rd0 rd1 : Reader} {seed : Digest} {c : Child} {qt qo nc cur p r m n wd : ℕ} {flag f4 : E} {ws : List E}
    {h Rr : ℕ → ℕ} {ret : ℕ → (ℕ → E) → E} {Own : ℕ → Prop} {st : St}
    (hN : FrontNum p r m n wd flag ws h Rr) (hr : CausalRule ret) (hR : FrontRet ret r m h Rr)
    (hown : ∀ i, cur ≤ i → i < cur + (vsAllocSz p).sum → Own i) (hsa : st.a = cur)
    (hP0 : vsPreA seed c qt qo rd0)
    (H0 : HoldsWords rd0 (frontWords cur p ws m h Rr n wd flag f4))
    (hWo : ∀ rd, st.O rd → HoldsWords rd (frontWords cur p ws m h Rr n wd flag f4)) :
    FrontHyp fs al cert k rd0 (vsW rd1 (vsArgs seed c (ptrAt qt) (ptrAt qo)) cur p ret)
      (vsArgs seed c (ptrAt qt) (ptrAt qo)) Own (vsRegion qt qo nc) (vsPreA seed c qt qo)
      st p r m n wd cur (cur + 6) (cur + 162) (cur + 186) qt flag f4 ws h Rr := by
  rcases st with ⟨a, kc, O, D, Qs⟩
  dsimp only at hsa
  subst a
  have ha : (vsArgs seed c (ptrAt qt) (ptrAt qo)).length = 6 := rfl
  have hsum : (vsAllocSz p).sum = 982 + 256 * p := by
    simp only [vsAllocSz, vsSz0, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]; omega
  have own : ∀ i, cur ≤ i → i < cur + 982 + 256 * p → Own i := fun i h1 h2 => hown i h1 (by omega)
  have rt : ∀ {i : ℕ} {v : E}, VsRetIdx i → (∀ σ, ret i σ = v) →
      vsW rd1 (vsArgs seed c (ptrAt qt) (ptrAt qo)) cur p ret i = v := fun hi hv =>
    (vsW_ret' ha hr hi).trans (hv _)
  exact {
    hp1 := hN.hp1, hp := hN.hp, hws := hN.hws, hw7r := hN.hw7r, hw0m := hN.hw0m, hws56 := hN.hws56,
    hr1 := hN.hr1, hr4 := hN.hr4, hm1 := hN.hm1, h24 := hN.h24, hR := hN.hR, hl := hN.hl, h9 := hN.h9,
    hl5 := hN.hl5, hht := hN.hht, hn := hN.hn, hw19 := hN.hw19, hw24 := hN.hw24, hmw := hN.hmw, hN := hN.hN,
    hflag := hN.hflag,
    hw42 := vsW_42 ha hr,
    hwA := vsW_hwA ha hr,
    hw6 := (vsW_buf ha hr (j := 0) (by norm_num) rfl).trans (congrArg ptrAt (vsBaseF_0 cur p)),
    hw7 := (vsW_buf ha hr (j := 1) (by norm_num) rfl).trans (congrArg ptrAt (vsBaseF_1 cur p)),
    hw8 := (vsW_buf ha hr (j := 2) (by norm_num) rfl).trans (congrArg ptrAt (vsBaseF_2 cur p)),
    hw9 := (vsW_buf ha hr (j := 3) (by norm_num) rfl).trans (congrArg ptrAt (vsBaseF_3 cur p)),
    hw55 := (vsW_buf ha hr (j := 18) (by norm_num) rfl).trans (congrArg ptrAt (vsBaseF_18 cur p)),
    hw56 := (vsW_buf ha hr (j := 19) (by norm_num) rfl).trans (congrArg ptrAt (vsBaseF_19 cur p)),
    hw112 := (vsW_buf ha hr (j := 20) (by norm_num) rfl).trans (congrArg ptrAt (vsBaseF_20 cur p)),
    hw94 := rt (by decide) hR.r94,
    hw101 := rt (by decide) hR.r101,
    hret := fun t ht => by
      have hi : VsRetIdx (tsRet t) ∧ VsRetIdx (tsRet t + 1) ∧ VsRetIdx (tsRet t + 2) := by
        interval_cases t <;> decide
      exact ⟨rt hi.1 fun σ => (hR.rts t ht σ).1, rt hi.2.1 fun σ => (hR.rts t ht σ).2.1,
        rt hi.2.2 fun σ => (hR.rts t ht σ).2.2⟩,
    h4 := vsVal_param ha (i := 4) (by norm_num),
    r0 := frontReads_of_holds H0,
    rq := (vsPreA_exp hP0).1,
    hO := fun rd hrd => frontReads_of_holds (hWo rd hrd),
    hOwn := fun i h1 h2 => by dsimp only at h1 h2; exact own i (by omega) (by omega),
    hO6 := fun j hj => own _ (by omega) (by omega),
    hO7 := fun j hj => own _ (by omega) (by omega),
    hO8 := fun j hj => own _ (by omega) (by omega),
    hO9 := fun j hj => own _ (by omega) (by omega),
    hRq := fun j hj => by unfold vsRegion; left; rw [expTabLen_eq]; omega,
    hPre := fun rd h => (vsPreA_exp h).1 }

/-! ## The link's width word -/

/-- **`.n 409 = g^wd`, `.n 410 = flag`** from the front's hypotheses (`vsB0_runHyp`'s values). -/
theorem vsVal_409_410_of_front {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    {rd0 : Reader} {w : ℕ → E} {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop} {st : St}
    {p r m n wd b6 b7 b8 b9 qt : ℕ} {flag f4 : E} {ws : List E} {h Rr : ℕ → ℕ} (ha : args.length = 6)
    (H : FrontHyp fs al cert k rd0 w args Own R Pre st p r m n wd b6 b7 b8 b9 qt flag f4 ws h Rr) :
    vsVal rd0 w args (.n 409) = gen ^ wd ∧ vsVal rd0 w args (.n 410) = flag := by
  obtain ⟨h216, h224⟩ := vsVal_216 (rd0 := rd0) (w := w) ha Rr fun t ht => (H.hret t ht).1
  have h101 : vsVal rd0 w args (.n 101) = gen ^ m :=
    (vsVal_call_ret ha vsW5_eq (.n 101) (List.mem_singleton_self _)).trans H.hw101
  obtain ⟨v115, v116, v117, v118, v119, v120, -⟩ :=
    vsW6_vals (rd0 := rd0) (w := w) (args := args) ha H.hw6 H.hw56 (bs := rowsW Rr) (by simp [rowsW])
      H.r0.heights H.r0.sizes
  have hv : ∀ t < 6, vsVal rd0 w args (.n (115 + t)) = gen ^ h t := by
    intro t ht
    interval_cases t
    exacts [v115, v116, v117, v118, v119, v120]
  have hn24 : n ≤ 24 := by obtain ⟨t, ht, rfl⟩ := H.hn; exact H.h24 t ht
  have V := (vsB0_runHyp (k := 6) (Own := fun _ => True) (R := fun _ => True)
    (Pre := fun _ => False) (a := 0) (D := fun _ => False) (O := fun _ => False) le_rfl ha h h216 h224 hv h101
    H.h4 H.hw8 H.hw9 H.hht H.hn hn24 H.hw19 H.hw24 H.hmw H.hN H.r0.cycles H.r0.shape H.rq
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ h => h.elim)
    (fun _ h => h.elim))
  exact ⟨V.2.2.1, V.2.2.2.1⟩

/-- **`.n 409 = g^wd`** from the front's hypotheses, which `Ph4Hyp` asks. -/
theorem vsVal_409_of_front {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    {rd0 : Reader} {w : ℕ → E} {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop} {st : St}
    {p r m n wd b6 b7 b8 b9 qt : ℕ} {flag f4 : E} {ws : List E} {h Rr : ℕ → ℕ} (ha : args.length = 6)
    (H : FrontHyp fs al cert k rd0 w args Own R Pre st p r m n wd b6 b7 b8 b9 qt flag f4 ws h Rr) :
    vsVal rd0 w args (.n 409) = gen ^ wd :=
  (vsVal_409_410_of_front ha H).1

end
end LeanVM.Guest.B1.VsC
