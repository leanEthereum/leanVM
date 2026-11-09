/-
  LeanVM.Guest.B1.VerifySub.H.Sec

  The sections' data (`VsSecData`) of `verify_sub`'s honest valuation on an honest child: the
  memory holding the own buffers and the caller's words, the callees' results the honest ones.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Vals
public import LeanVM.Guest.B1.VerifySub.H.Kids

/-!
# The sections' data, honestly

`vsSec`: with the own buffers' honest words (`ChildSegs.ownW`) at the pointers `bs`, the exponent
tables and the child's fixed cells at `lpE`, `sqE`, `outE`, the memory defined below `2^κ`
(`κ ≥ 16`) and the callees' results the honest ones (`g_power_of_word`'s, `verify_tables`',
`verify_keccak`'s, the stack's log), the honest valuation on the oracle `vsW bs outs` has the
sections' data: `vsCPre_complete` applies.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

theorem readsAt_getD' {rd : Reader} {p : E} {xs : List E} {k : ℕ} (h : ReadsAt rd p xs)
    (hk : k < xs.length) : LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

variable {rd : Reader} {args : List E}

theorem vsRetVars_runs : (∀ i < 9, (vsRetVars.getD 5 []).getD i 0 = 626 + i) ∧
    (∀ i < 10, (vsRetVars.getD 6 []).getD i 0 = 636 + i) ∧
    (∀ i < 8, (vsRetVars.getD 7 []).getD i 0 = 651 + i) ∧
    (∀ i < 5, (vsRetVars.getD 11 []).getD i 0 = 1700 + i) := by decide

theorem vsRetVars_lens : (vsRetVars.getD 5 []).length = 9 ∧ (vsRetVars.getD 6 []).length = 10 ∧
    (vsRetVars.getD 7 []).length = 8 ∧ (vsRetVars.getD 11 []).length = 5 := by decide

set_option maxRecDepth 100000 in
theorem vs_e124 (hl : args.length = 6) {w : ℕ → E} {lir : ℕ}
    (e122 : vsσ rd w args (.n 120) = gen ^ lir) (h1 : 1 ≤ lir) :
    vsσ rd w args (.n 122) = gen ^ (lir - 1) := by
  have hG := vsSizesT_good (rd := rd) (w := w) hl
  have g1 := hG (vsMul 120 122 121) (by
    rw [vsSizesT]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have g2 := hG (vsConst 121 (word 2 0 0)) (by
    rw [vsSizesT]; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp only [vsMul, vsConst, GoodS] at g1 g2
  simp only [Good] at g2
  rw [good_mul_old (by decide) g1, e122, g2, word_gen]
  have : gen ^ lir = gen ^ (lir - 1) * gen := by rw [← pow_succ, Nat.sub_add_cancel h1]
  rw [this, mul_assoc, mul_inv_cancel₀ gen_ne_zero, mul_one]

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem stream_length (S : ChildSegs bytecode seed c) : 10 ≤ c.proof.stream.length := by
  have := S.hrowsL
  rw [S.hstream]; simp; omega

theorem rows_eq : ∃ a b c d e f, S.rowsN = [a, b, c, d, e, f] := by
  match h : S.rowsN, S.hrowsL with
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩

theorem words_getD7 : S.words.getD 7 0 = eOfNat S.rate := by
  obtain ⟨a, b, c, d, e, f, hr⟩ := S.rows_eq
  simp [ChildSegs.words, hr]

theorem words_getD_rows {i : ℕ} (hi : i < 6) :
    S.words.getD (i + 1) 0 = (S.rowsN.map eOfNat).getD i 0 := by
  obtain ⟨a, b, c, d, e, f, hr⟩ := S.rows_eq
  interval_cases i <;> simp [ChildSegs.words, hr]

theorem poolW_length (hbl : bytecode.length = 2 ^ 23) : S.H.poolW.length = 167 := by
  obtain ⟨hok, hx, -, hlen⟩ := S.H_run hbl
  have h1 := hok.hx5
  have h2 := hok.hxR
  have hf : S.H.evsT.flatten.length = 159 := by
    have := congrArg List.length hx
    simp only [List.length_append, h1, h2] at this
    omega
  simp [Tables.VtHonest.poolW, Tables.VtHonest.pcW, h1, hf]

theorem rchs_length : S.rchs.length = 6 := by
  have := congrArg (fun p ↦ p.1.length) S.hchs
  simp only [squeezeN_len] at this
  simp [ChildSegs.rchs, ← this]

theorem s7_eta (hbl : bytecode.length = 2 ^ 23) : S.s7 = ⟨S.s7.cap, []⟩ := by
  have h := S.runK
  rw [S.hlayout, (S.lanes hbl).1, (S.lanes hbl).2.1, (S.H_run hbl).2.2.1] at h
  obtain ⟨K, hK⟩ := keccakSeg_capOf h (S.runK' hbl).2.2.2.2
  rw [hK]

theorem vs_ofK_add (a b : ℕ) : ofK (addressOfIndex (a + b)) = ofK (addressOfIndex a) * gen ^ b := by
  rw [gen_pow_eq_ofK, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, pow_add]

theorem stream_pool_lt (hbl : bytecode.length = 2 ^ 23) {j : ℕ} (h162 : j < 164) :
    10 + S.xsG.length + (5 + (3 * S.H.n + (j - 5))) < c.proof.stream.length := by
  obtain ⟨hok, hx, -, hlen⟩ := S.H_run hbl
  have := S.hstream
  have h := congrArg List.length this
  simp only [List.length_append, List.length_cons, List.length_map, S.hrowsL, List.length_nil] at h
  omega

/-- **The tables' evaluations in the stream**: past the announced words, the root, the GKR's words,
the five framework words and the rounds', the evaluations are `claim_pool`'s words `5 ..< 164`. -/
theorem stream_pool (hbl : bytecode.length = 2 ^ 23) {j : ℕ} (h5 : 5 ≤ j) (h162 : j < 164) :
    (vsStreamW c.proof.stream).getD (10 + S.xsG.length + (5 + (3 * S.H.n + (j - 5)))) 0 =
      S.H.poolW.getD j 0 := by
  obtain ⟨hok, hx, -, -⟩ := S.H_run hbl
  have h1 := hok.hx5
  have h2 := hok.hxR
  have hf : S.H.evsT.flatten.length = 159 := by
    have := congrArg List.length hx
    simp only [List.length_append, h1, h2] at this
    have := (S.H_run hbl).2.2.2
    omega
  have hw : (eOfNat S.logMem :: S.rowsN.map eOfNat ++ [eOfNat S.rate] ++ [S.x0, S.x1]).length = 10 := by
    simp [S.hrowsL]
  have e : c.proof.stream = (eOfNat S.logMem :: S.rowsN.map eOfNat ++ [eOfNat S.rate] ++ [S.x0, S.x1]) ++
      S.xsG ++ (S.H.xs5 ++ S.H.xsR ++ S.H.evsT.flatten) ++ (S.xsK ++ S.xsW) := by
    rw [S.hstream, ← hx]; simp only [List.append_assoc]
  have hlt := S.stream_pool_lt hbl h162
  rw [vsStreamW, List.getD_append _ _ _ _ hlt, e, List.getD_append _ _ _ _ (by
      simp only [List.length_append, hw, h1, h2, hf]; omega),
    List.getD_append_right _ _ _ _ (by simp only [List.length_append, hw]; omega)]
  simp only [List.length_append, hw]
  rw [show 10 + S.xsG.length + (5 + (3 * S.H.n + (j - 5))) - (10 + S.xsG.length) =
      S.H.xs5.length + S.H.xsR.length + (j - 5) by rw [h1, h2]; omega,
    List.getD_append_right _ _ _ _ (by simp only [List.length_append]; omega)]
  simp only [List.length_append, Nat.add_sub_cancel_left]
  rw [Tables.VtHonest.poolW, List.getD_append _ _ _ _ (by simp only [List.length_append, h1, hf]; omega),
    List.getD_append_right _ _ _ _ (by omega), h1]

theorem s6_capOf (hbl : bytecode.length = 2 ^ 23) : S.s6.cap = S.H.s3.squeeze.2.cap := by
  obtain ⟨hok, -, -, -⟩ := S.H_run hbl
  exact (Tables.vt_spec hok).2.2.2

theorem root_cells : (digestHalves S.root) = (S.x0, S.x1) := digestScalars_digestOfScalars S.hroot

end ChildSegs

set_option maxRecDepth 100000 in
/-- **The sections' data of the honest valuation on an honest child.** -/
theorem vsSec {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) {sqE outE : ℕ}
    (hargs : args = [(digestHalves (statementDigest seed c.statement)).1,
      (digestHalves (statementDigest seed c.statement)).2, (digestHalves seed).1,
      (digestHalves seed).2, ofK (addressOfIndex sqE), ofK (addressOfIndex outE)])
    (bs : List ℕ) (outs : List (List E × Main.Layout)) {κ : ℕ} (hκ : 16 ≤ κ) (hlow : LowDef κ rd)
    (hmem : ∀ i < 13, ReadsAt rd (ofK (addressOfIndex (bs.getD i 0))) (S.ownW.getD i []))
    (hsq : ReadsAt rd (ofK (addressOfIndex sqE)) expTableWords)
    (hfx : ReadsAt rd (ofK (addressOfIndex outE)) (DeferredClaim.cells c.freshClaim))
    (o0 : (outs.getD 0 ([], [])).1 = [gen ^ S.rate])
    (o1 : (outs.getD 1 ([], [])).1 = [gen ^ S.logMem])
    (o6 : (outs.getD 6 ([], [])).1 = S.vtRetsOf bs)
    (o7 : (outs.getD 7 ([], [])).1 =
      S.s7.cap ++ [ofK (addressOfIndex (S.cK bs)) * gen ^ S.xsK.length, S.word, S.m0])
    (o10 : (outs.getD 10 ([], [])).1 = [gen ^ max 15 (log2Ceil (Tables.stackTotal S.kappas))]) :
    ∃ D : VsSecData rd (vsW bs outs) args,
      D.vals = (fun i ↦ S.H.poolW.getD (vsKept i) 0) ∧ D.lir = S.rate ∧ D.logMem = S.logMem ∧
      D.hs = S.hs ∧ D.m = S.μs ∧ D.r = S.rate ∧
      D.τg = gen ^ S.τ ∧ VsFrontH S rd (vsσ rd (vsW bs outs) args) ∧
      vsσ rd (vsW bs outs) args (.n 1111) = S.lam ∧
      S.s8 = ⟨[vsσ rd (vsW bs outs) args (.n 754), vsσ rd (vsW bs outs) args (.n 755),
        vsσ rd (vsW bs outs) args (.n 756), vsσ rd (vsW bs outs) args (.n 757),
        vsσ rd (vsW bs outs) args (.n 758)], []⟩ ∧
      vsσ rd (vsW bs outs) args (.n 658) = S.m0 ∧ vsChs (vsσ rd (vsW bs outs) args) = S.chs := by
  have hl : args.length = 6 := by rw [hargs]; rfl
  have ptr : ∀ i < 13, vsσ rd (vsW bs outs) args (.n (vsAllocVars.getD i 0)) =
      ofK (addressOfIndex (bs.getD i 0)) := fun i hi ↦ vs_alloc_ptr hl bs outs hi
  have ret : ∀ j < 13, ∀ k < (vsRetVars.getD j []).length,
      vsσ rd (vsW bs outs) args (.n ((vsRetVars.getD j []).getD k 0)) =
        (outs.getD j ([], [])).1.getD k 0 := fun j hj k hk ↦ vs_ret_val hl bs outs hj hk
  have m : ∀ i < 13, ReadsAt rd (vsσ rd (vsW bs outs) args (.n (vsAllocVars.getD i 0)))
      (S.ownW.getD i []) := fun i hi ↦ by rw [ptr i hi]; exact hmem i hi
  have par : ∀ i < 6, vsσ rd (vsW bs outs) args (.n i) = args.getD i 0 :=
    fun i hi ↦ vsC_param hl hi
  have hsl := S.hs_length
  have hh := S.hh29 hbl
  -- the stream
  have mS : ReadsAt rd (vsσ rd (vsW bs outs) args (.n 25)) (vsStreamW c.proof.stream) :=
    m 1 (by norm_num)
  have hsl10 := S.stream_length
  have hws : ∀ i < 10, LoadHolds rd (vsσ rd (vsW bs outs) args (.n 25)) i
      (c.proof.stream.getD i 0) := fun i hi ↦ by
    have := readsAt_getD' mS (k := i) (by simp [vsStreamW]; omega)
    rwa [vsStreamW, List.getD_append _ _ _ _ (by omega)] at this
  have F := vsH_spec hbl S hargs hws
  obtain ⟨hw8, hx8, hx9⟩ := S.stream_getD
  generalize hσ : vsσ rd (vsW bs outs) args = σ at *
  -- the callees' results
  have e122 : σ (.n 120) = gen ^ S.rate := by
    have := ret 0 (by norm_num) 0 (by decide); rw [o0] at this; exact this
  have e130 : σ (.n 128) = gen ^ S.logMem := by
    have := ret 1 (by norm_num) 0 (by decide); rw [o1] at this; exact this
  obtain ⟨K7, hK7⟩ := S.s7_capOf hbl
  have e651 : ∀ i < 5, σ (.n (651 + i)) = (capOf K7).getD i 0 := fun i hi ↦ by
    have := ret 7 (by norm_num) i (by rw [vsRetVars_lens.2.2.1]; omega)
    rw [vsRetVars_runs.2.2.1 i (by omega), o7, hK7,
      List.getD_append _ _ _ _ (by simp [capOf]; omega)] at this
    exact this
  have e870 : σ (.n 658) = S.m0 := by
    have := ret 7 (by norm_num) 7 (by decide)
    rw [vsRetVars_runs.2.2.1 7 (by norm_num), o7, hK7] at this
    exact this
  have e856 : σ (.n 643) = c.freshClaim.bytecodeValue := by
    have := ret 6 (by norm_num) 7 (by decide)
    rw [vsRetVars_runs.2.1 7 (by norm_num), o6] at this
    exact this
  have e1890 : σ (.n 1684) = gen ^ S.μs := by
    have := ret 10 (by norm_num) 0 (by decide)
    rw [o10] at this
    simp only [vsRetVars, List.getD_cons_zero, List.getD_cons_succ] at this
    rw [this, ChildSegs.μs, S.hlayout, stackLog_eq hbl]
    rfl
  -- the memory's words
  have hcount : S.hs.map Hints.count = S.hs.map (gen ^ ·) :=
    List.map_congr_left fun x hx ↦ count_eq_gen (by have := hh x hx; omega)
  have hdims : ReadsAt rd (σ (.n 127)) (gen ^ S.logMem :: S.hs.map Hints.count) := m 3 (by norm_num)
  have hkb : ReadsAt rd (σ (.n 139)) (1 :: gen ^ S.logMem :: S.hs.map Hints.count) :=
    m 4 (by norm_num)
  have hexp : ExpTables rd (σ (.n 4)) := by
    rw [par 4 (by norm_num), hargs]
    refine (expTables_iff_words _ _).2 fun o ho ↦ ?_
    exact readsAt_getD' hsq (by simpa [expTableWords, length_etWordsN] using ho)
  -- the bus challenges
  have mA : ReadsAt rd (σ (.n 346)) S.alphas := m 6 (by norm_num)
  have hA4 : vsAlphas σ = S.alphas := F.halphas
  have mA' : ReadsAt rd (σ (.n 346)) (vsAlphas σ) := by rw [hA4]; exact mA
  have mF : ReadsAt rd (σ (.n 427)) (eqKernel (vsAlphas σ)) := by
    rw [hA4]; exact m 7 (by norm_num)
  -- `dims_g[6]`
  have hd6 : LoadHolds rd (σ (.n 127)) 6 (gen ^ S.τ) := by
    have := readsAt_getD' hdims (k := 6) (by simp [hsl])
    rw [show (gen ^ S.logMem :: S.hs.map Hints.count).getD 6 0 = Hints.count (S.hs.getD 5 0) by
      rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp [hsl]), List.getElem_map,
        List.getD_eq_getElem _ _ (by omega)]] at this
    rw [count_eq_gen (by have := (S.τ_bounds hbl).2.1; unfold ChildSegs.τ at this; omega)] at this
    exact this
  -- the copies of `verify_keccak`'s capacity
  have hcp := (vsCallsT_complete (rd := rd) (w := vsW bs outs) (C := fun _ _ _ ↦ True)
    (next := True) (kret := fun _ ↦ True) hl (τg := gen ^ S.τ) (by rw [hσ]; exact hd6) trivial
    trivial trivial trivial).2.2.2.1
  rw [hσ] at hcp
  have hc871 : ∀ i < 5, IsCanonical128 (σ (.n (659 + i))) := fun i hi ↦ by
    rw [hcp i hi, e651 i hi]
    exact Tables.tb_capOf_canonical _ _ (by
      rw [List.getD_eq_getElem _ _ (by simp [capOf]; omega)]; exact List.getElem_mem _)
  -- the ring map
  have hM := vsH_maps (rd := rd) (w := vsW bs outs) hl (by rw [hσ]; exact hc871)
  rw [hσ] at hM
  have hs7 : (⟨[σ (.n 659), σ (.n 660), σ (.n 661), σ (.n 662), σ (.n 663)], []⟩ : Fs) = S.s7 := by
    have hc := fun i (hi : i < 5) ↦ (hcp i hi).trans (e651 i hi)
    have h0 : σ (.n 659) = cellsOfState K7 false 8 := hc 0 (by norm_num)
    have h1 : σ (.n 660) = cellsOfState K7 false 9 := hc 1 (by norm_num)
    have h2 : σ (.n 661) = cellsOfState K7 false 10 := hc 2 (by norm_num)
    have h3 : σ (.n 662) = cellsOfState K7 false 11 := hc 3 (by norm_num)
    have h4 : σ (.n 663) = cellsOfState K7 false 12 := hc 4 (by norm_num)
    rw [S.s7_eta hbl, hK7, h0, h1, h2, h3, h4]
    rfl
  have hchs := S.hchs
  rw [← hs7, hM.1] at hchs
  simp only [Prod.mk.injEq] at hchs
  obtain ⟨ech, es8⟩ := hchs
  -- the batching challenge
  have hL := vsH_lam (rd := rd) (w := vsW bs outs) hl (by rw [hσ]; exact hM.2)
  rw [hσ] at hL
  have elam : σ (.n 1111) = S.lam := by
    rw [ChildSegs.lam, ← es8, hL]
  -- the fixed cells
  have hfx' : ReadsAt rd (σ (.n 5)) (S.point.take 19 ++ S.alphas ++ [c.freshClaim.bytecodeValue]) := by
    rw [par 5 (by norm_num), hargs]
    have := hfx
    rw [DeferredClaim.cells, S.fresh_eq hbl] at this
    exact this
  have hμ := S.μ_bounds hbl
  have hpl := (S.runG' hbl).2.2.1
  have hal : S.alphas.length = 4 := by
    have := congrArg List.length hA4; simpa [vsAlphas] using this.symm
  refine ⟨{
    hl := hl
    hc4 := fun i hi ↦ by
      have c1 := digest_canonical (statementDigest seed c.statement)
      have c2 := digest_canonical seed
      rw [hargs]
      interval_cases i
      · exact c1.1
      · exact c1.2
      · exact c2.1
      · exact c2.2
    ws := c.proof.stream
    hws := fun i hi ↦ by rw [hσ]; exact hws i (by omega)
    hrows := fun i hi ↦ by
      rw [hσ, hw8 (i + 1) (by omega), S.words_getD_rows hi]
      exact readsAt_getD' (m 2 (by norm_num)) (by simp [S.hrowsL]; omega)
    hcap22 := by rw [hσ]; exact F.hcap22
    κ := κ
    hκ6 := by omega
    hlow := hlow
    lir := S.rate
    logMem := S.logMem
    hl1 := S.hr1
    hl4 := S.hr4
    hm16 := S.h16
    hm32 := S.h32
    e112 := by rw [hσ]; have := F.hx 7 (by norm_num); rw [hw8 7 (by norm_num), S.words_getD7] at this; exact this
    e29 := by rw [hσ]; have := F.hx 0 (by norm_num); rw [hw8 0 (by norm_num)] at this; exact this
    e122 := by rw [hσ]; exact e122
    e130 := by rw [hσ]; exact e130
    hs := S.hs
    hsl := hsl
    hh := hh
    hdims := by rw [hσ]; exact hdims
    hkb := by rw [hσ]; exact hkb
    hcount := hcount
    hexp := by rw [hσ]; exact hexp
    hin := by rw [hσ]; exact F.hin
    x0 := S.x0
    x1 := S.x1
    hw8 := by rw [hσ, ← hx8]; exact hws 8 (by norm_num)
    hw9 := by rw [hσ, ← hx9]; exact hws 9 (by norm_num)
    hz := by rw [hσ]; exact F.hz
    hcap532 := by rw [hσ]; exact F.hc532
    hA := fun k hk ↦ by
      rw [hσ]
      have := readsAt_getD' mA' (k := k) (by simp [vsAlphas]; omega)
      interval_cases k <;> exact this
    a0 := σ (.n 366)
    a1 := σ (.n 386)
    a2 := σ (.n 406)
    a3 := σ (.n 426)
    ha := by rw [hσ]; exact mA'
    hfp := by rw [hσ]; exact mF
    hcap628 := by rw [hσ]; exact F.hc628
    τg := gen ^ S.τ
    hd6 := by rw [hσ]; exact hd6
    hcap871 := by rw [hσ]; exact hc871
    hM := fun k hk ↦ by
      rw [hσ]
      have mC : ReadsAt rd (σ (.n 664)) S.rchs := m 11 (by norm_num)
      have := readsAt_getD' mC (k := k) (by rw [S.rchs_length]; omega)
      rw [ChildSegs.rchs, ← ech] at this
      interval_cases k
      · show LoadHolds rd (σ (.n 664)) 0 (σ (.n 658)); rw [e870]; exact this
      all_goals exact this
    chs := S.rchs
    hcl := S.rchs_length
    hchs := by rw [hσ]; exact m 11 (by norm_num)
    hct := by rw [hσ]; exact m 12 (by norm_num)
    hcap966 := by rw [hσ]; exact hM.2
    vals := fun i ↦ S.H.poolW.getD (vsKept i) 0
    hpool := fun i hi ↦ by
      rw [hσ]
      have hk := vsKept_lt hi
      show LoadHolds rd (σ (.n (vsClaimAt (vsKept i)).1)) (vsClaimAt (vsKept i)).2
        (S.H.poolW.getD (vsKept i) 0)
      unfold vsClaimAt
      split
      · rename_i hj
        have e645 : σ (.n 645) = ofK (addressOfIndex (bs.getD 1 0 + (10 + S.xsG.length))) * gen ^ 5 *
            gen ^ (3 * S.H.n) := by
          have := ret 6 (by norm_num) 9 (by rw [vsRetVars_lens.2.1]; omega)
          rw [vsRetVars_runs.2.1 9 (by norm_num), o6, ChildSegs.vtRetsOf_getD9, ChildSegs.cT_eq] at this
          exact this
        have key : LoadHolds rd (σ (.n 25)) ((10 + S.xsG.length) + (5 + (3 * S.H.n + (vsKept i - 5))))
            (S.H.poolW.getD (vsKept i) 0) := by
          rw [← S.stream_pool hbl hj.1 hj.2]
          refine readsAt_getD' mS ?_
          have := S.stream_pool_lt hbl hj.2
          simp only [vsStreamW, List.length_append, List.length_replicate]
          omega
        rw [e645, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow, ChildSegs.vs_ofK_add,
          loadHolds_mul_gen_pow, ← ptr 1 (by norm_num)]
        exact key
      · have mP : ReadsAt rd (σ (.n 6)) S.H.poolW := m 0 (by norm_num)
        exact readsAt_getD' mP (by rw [S.poolW_length hbl]; exact hk)
    m := S.μs
    r := S.rate
    hm22 := S.hmu22
    hm28 := S.hmu28
    hr1 := S.hr1
    hr4 := S.hr4
    e1890 := by rw [hσ]; exact e1890
    e124 := vs_e124 hl (by rw [hσ]; exact e122) S.hr1
    zs := fun k ↦ S.point.getD k 0
    al := fun k ↦ S.alphas.getD k 0
    hzeta := fun k hk ↦ by
      rw [hσ]
      have mZ : ReadsAt rd (σ (.n 310)) S.point := m 5 (by norm_num)
      exact readsAt_getD' mZ (by rw [hpl]; omega)
    halpha := fun k hk ↦ by rw [hσ]; exact readsAt_getD' mA (by omega)
    hout := fun k hk ↦ by
      rw [hσ]
      have := readsAt_getD' hfx' (k := k) (by
        simp only [List.length_append, List.length_take, List.length_cons, List.length_nil, hpl, hal]
        omega)
      rw [List.append_assoc, List.getD_append _ _ _ _ (by simp only [List.length_take, hpl]; omega),
        List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk, ← List.getD_eq_getElem?_getD]
        at this
      exact this
    hout' := fun k hk ↦ by
      rw [hσ]
      have := readsAt_getD' hfx' (k := 19 + k) (by
        simp only [List.length_append, List.length_take, List.length_cons, List.length_nil, hpl, hal]
        omega)
      rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_take, hpl, hal]; omega),
        List.getD_append_right _ _ _ _ (by simp only [List.length_take, hpl]; omega)] at this
      simpa [hpl, show min 19 S.μ = 19 by omega] using this
    hout23 := by
      rw [hσ, e856]
      have := readsAt_getD' hfx' (k := 23) (by
        simp only [List.length_append, List.length_take, List.length_cons, List.length_nil, hpl, hal]
        omega)
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_take, hpl, hal]; omega)] at this
      simpa [hpl, hal, show min 19 S.μ = 19 by omega] using this }, ?_⟩
  subst hσ
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, F, elam, es8.symm, e870, ech⟩

end
end LeanVM.Guest.B1.VerifySub
