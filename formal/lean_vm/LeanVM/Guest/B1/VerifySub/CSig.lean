/-
  LeanVM.Guest.B1.VerifySub.CSig

  `verify_sub`'s honest valuation on an honest child: what the body needs of the memory and the
  oracle (`VsSecData`), from the child's segments, the own buffers and the callees' results.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Body
public import LeanVM.Guest.B1.VerifySub.H.Outs
public import LeanVM.Guest.B1.VerifySub.H.Own
public import LeanVM.Guest.B1.VerifySub.H.Lin
public import LeanVM.Guest.B1.VerifySub.H.KFacts
public import LeanVM.Guest.B1.VerifySub.H.KidsB
public import LeanVM.Guest.B1.VerifySub.H.Sig

/-!
# The honest valuation's data

On an honest child (`S : ChildSegs`), with the own buffers `S.ownW` at the bump allocator's
bases `bs`, the caller's words `Lin` (the exponent tables at `sqE`, the deferred claim's cells
at `outE`) and the callees' results `outs` (`VsOuts`) in memory, the oracle `vsW S.gw bs outs`
(allocations at `bs`, returns from `outs`) gives `VsSecData` (`vs_sig`): the stream's words, the
buffers' honest words and the callees' powers of `g`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- `verify_sub`'s arguments: the statement's and the seed's digests, the exponent tables'
pointer, the deferred claim's. -/
noncomputable def vsArgs (seed : Digest) (c : Child) (sqE outE : ℕ) : List E :=
  [(digestHalves (statementDigest seed c.statement)).1,
    (digestHalves (statementDigest seed c.statement)).2, (digestHalves seed).1,
    (digestHalves seed).2, ptr sqE, ptr outE]

theorem vsW_a {gw : E × E} {bs : List ℕ} {outs : List (List E × Main.Layout)} {i a : ℕ} (hi : i < 15)
    (ha : vsAllocVars.getD i 0 = a) : vsW gw bs outs a = ptr (bs.getD i 0) := by
  rw [← ha]; exact vsW_alloc gw bs outs hi

theorem vsW_r {gw : E × E} {bs : List ℕ} {outs : List (List E × Main.Layout)} {j k a : ℕ} (hj : j < 14)
    (hk : k < (vsRetVars.getD j []).length) (ha : (vsRetVars.getD j []).getD k 0 = a) :
    vsW gw bs outs a = (outs.getD j ([], [])).1.getD k 0 := by
  rw [← ha]; exact vsW_ret gw bs outs hj hk

theorem vs_ptr_add (a b : ℕ) : ptr (a + b) = ptr a * gen ^ b := by
  rw [ptr, ptr, gen_pow_eq_ofK, ← ofK_mul, Parameters.addressOfIndex, Parameters.addressOfIndex,
    Parameters.addressOfIndex, pow_add]

theorem vs_streamW_length (st : List E) : Coverage.childStreamCap ≤ (vsStreamW st).length := by
  simp only [vsStreamW, List.length_append, List.length_replicate]
  omega

theorem vs_rdgL {rd : Reader} {p : E} {xs : List E} {k : ℕ} (h : ReadsAt rd p xs)
    (hk : k < xs.length) : ∃ v, LoadHolds rd p k v := ⟨_, h k hk⟩

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem hs_length : S.hs.length = 6 := heights_length6 S.rowsN S.hrowsL

/-- The stream buffer's first words: the sizes, the root's two, the out-of-domain nonce. -/
theorem stream_words (hbl : bytecode.length = 2 ^ 23) :
    (vsStreamW c.proof.stream).take 8 = sizeWords S.logMem S.rowsN S.rate ∧
      (vsStreamW c.proof.stream).getD 0 0 = eOfNat S.logMem ∧
      (vsStreamW c.proof.stream).getD 7 0 = eOfNat S.rate ∧
      (vsStreamW c.proof.stream).getD 8 0 = S.x0 ∧ (vsStreamW c.proof.stream).getD 9 0 = S.x1 ∧
      (vsStreamW c.proof.stream).getD 10 0 = S.oodN := by
  obtain ⟨a, b, c', d, e, f, hr⟩ : ∃ a b c d e f, S.rowsN = [a, b, c, d, e, f] := by
    have := S.hrowsL
    match h : S.rowsN, this with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  rw [S.stream_eq hbl]
  simp [sizeWords, hr]

/-- The stream buffer's words at offsets `1 .. 6`: the row counts. -/
theorem stream_rows (hbl : bytecode.length = 2 ^ 23) {i : ℕ} (hi : i < 6) :
    (vsStreamW c.proof.stream).getD (i + 1) 0 = (S.rowsN.map eOfNat).getD i 0 := by
  rw [S.stream_eq hbl]
  simp only [sizeWords, List.append_assoc, List.cons_append, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ (by simp [S.hrowsL]; omega)]

/-- The stack's log, as `log2_ceil_in_the_exponent` returns it. -/
theorem μs_eq (hbl : bytecode.length = 2 ^ 23) :
    S.μs = max 16 (log2Ceil (Tables.stackTotal S.kappas)) := by
  show S.layout.stackLog = _
  rw [S.hlayout, stackLog_eq hbl]
  rfl

/-- `kappa_base`'s words as powers of `g`. -/
theorem kb_pow (hbl : bytecode.length = 2 ^ 23) {s : ℕ} (hs : s < 8) :
    (1 :: gen ^ S.logMem :: S.hs.map Hints.count).getD s 0 =
      gen ^ ([0, S.logMem] ++ S.hs).getD s 0 := by
  rw [S.hs_count hbl]
  rcases s with _ | _ | s
  · simp
  · simp
  · have h6 : s < S.hs.length := by rw [S.hs_length]; omega
    simp only [List.getD_cons_succ, List.cons_append, List.nil_append]
    rw [List.getD_eq_getElem _ _ (by simpa using h6), List.getElem_map,
      List.getD_eq_getElem _ _ h6]

end ChildSegs

/-- **The honest valuation's data on an honest child.** -/
theorem vs_sig {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (b sqE outE : ℕ) {Lin : Main.Layout}
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredBytecodeClaim.cells c.freshClaim) ∈ Lin)
    {outs : List (List E × Main.Layout)} (O : VsOuts S (bases b (vsSizes)) sqE outs)
    {rd : Reader} {κ : ℕ} (hκ : 14 ≤ κ) (hlow : LowDef κ rd)
    (hB : Main.MemL rd (bufL b (vsSizes) S.ownW)) (hL : Main.MemL rd Lin) :
    Nonempty (VsSecData rd (vsW S.gw (bases b (vsSizes)) outs) (vsArgs seed c sqE outE)) := by
  set bs := bases b (vsSizes) with hbs
  set w := vsW S.gw bs outs with hw
  have own : ∀ i < 15, ReadsAt rd (ptr (bs.getD i 0)) (S.ownW.getD i []) :=
    fun i hi ↦ hB _ (vs_own_mem S b hi)
  have hd := S.d_bounds hbl
  have hhs := S.hs_lt33 hbl
  have wa : ∀ {i a : ℕ}, i < 15 → vsAllocVars.getD i 0 = a → w a = ptr (bs.getD i 0) :=
    fun hi ha ↦ vsW_a hi ha
  have wr : ∀ {j k a : ℕ}, j < 14 → k < (vsRetVars.getD j []).length →
      (vsRetVars.getD j []).getD k 0 = a → w a = (outs.getD j ([], [])).1.getD k 0 :=
    fun hj hk ha ↦ vsW_r hj hk ha
  -- the stream
  have hS : ReadsAt rd (w 25) (vsStreamW c.proof.stream) := by
    rw [wa (i := 1) (a := 25) (by norm_num) rfl]; exact own 1 (by norm_num)
  have hSl := vs_streamW_length c.proof.stream
  have hSl' : 8192 ≤ (vsStreamW c.proof.stream).length := hSl
  -- the sizes
  have h64 : w 64 = gen ^ S.rate := by
    rw [wr (j := 0) (k := 0) (a := 64) (by norm_num) (by decide) rfl, O.o0]; rfl
  have h72 : w 72 = gen ^ S.logMem := by
    rw [wr (j := 1) (k := 0) (a := 72) (by norm_num) (by decide) rfl, O.o1]; rfl
  have hdims : ReadsAt rd (w 71) (w 72 :: S.hs.map Hints.count) := by
    rw [wa (i := 3) (a := 71) (by norm_num) rfl, h72]; exact own 3 (by norm_num)
  have hkb : ReadsAt rd (w 83) (1 :: w 72 :: S.hs.map Hints.count) := by
    rw [wa (i := 4) (a := 83) (by norm_num) rfl, h72]; exact own 4 (by norm_num)
  -- the push blocks' squares
  have hsq0 := hL (sqE, expTabAllWords) (hexp _ (by unfold vsExpLin; exact List.mem_singleton_self _))
  have hsq : ReadsAt rd (ptr sqE) expTabAllWords := by dsimp only at hsq0; exact hsq0
  have hpush : ∀ bk < 54, ∃ v, LoadHolds rd
      ((vsArgs seed c sqE outE).getD 4 0 * (1 :: w 72 :: S.hs.map Hints.count).getD
        (Tables.blockKappaSrc.getD bk 0) 0) (Tables.blockKappaAdj bk) v := by
    intro bk hbk
    have hsrc : Tables.blockKappaSrc.getD bk 0 < 8 := blockKappaSrc_lt bk (by show bk < 153; omega)
    have he := kbase_le hhs (S.h30.trans (by norm_num)) (Tables.blockKappaSrc.getD bk 0)
    have hadj : Tables.blockKappaAdj bk ≤ 19 := by unfold Tables.blockKappaAdj; split <;> omega
    have h0 : Tables.blockKappaAdj bk ≠ 0 → Tables.blockKappaSrc.getD bk 0 = 0 := push_adj bk hbk
    rw [h72, S.kb_pow hbl hsrc, show (vsArgs seed c sqE outE).getD 4 0 = ptr sqE from rfl]
    simp only [loadHolds_mul_gen_pow]
    refine vs_rdgL hsq ?_
    rw [length_expTabAllWords]
    by_cases ha : Tables.blockKappaAdj bk = 0
    · omega
    · rw [h0 ha]; simp; omega
  -- the depths
  have h253 : w 253 = gen ^ S.d := by
    rw [wr (j := 2) (k := 0) (a := 253) (by norm_num) (by decide) rfl, O.o2, S.d_eq hbl]; simp
  have h276 : w 276 = gen ^ S.μs := by
    rw [wr (j := 4) (k := 0) (a := 276) (by norm_num) (by decide) rfl, O.o4, S.μs_eq hbl]; rfl
  -- `ood_value`
  have hood : ∃ v, LoadHolds rd (w 361) 0 v := by
    rw [wa (i := 7) (a := 361) (by norm_num) rfl]
    exact vs_rdgL (xs := [S.oodV]) (own 7 (by norm_num)) (by simp)
  -- `fp_w`
  have o7 := O.o6
  have hfpw : ReadsAt rd (w 386) (w 364 :: ((vsFpwFs w).squeezeN 15).1) := by
    have e313 : w 364 = challengeOf S.busSt := by
      rw [wr (j := 6) (k := 0) (a := 364) (by norm_num) (by decide) rfl, o7, Keccak.challengeOf_cells]; rfl
    have eF : vsFpwFs w = ⟨capOf S.busSt, []⟩ := by
      simp only [vsFpwFs]
      rw [wr (j := 6) (k := 2) (a := 366) (by norm_num) (by decide) rfl,
        wr (j := 6) (k := 3) (a := 367) (by norm_num) (by decide) rfl,
        wr (j := 6) (k := 4) (a := 368) (by norm_num) (by decide) rfl,
        wr (j := 6) (k := 5) (a := 369) (by norm_num) (by decide) rfl,
        wr (j := 6) (k := 6) (a := 370) (by norm_num) (by decide) rfl, o7]
      rfl
    rw [wa (i := 8) (a := 386) (by norm_num) rfl, e313, eF]
    have h8 : ReadsAt rd (ptr (bs.getD 8 0)) S.wb.1 := own 8 (by norm_num)
    rwa [(S.bus_inv hbl).2.2.1] at h8
  -- `col_eval_words`, in the stream
  obtain ⟨hOk, -, -, hxl⟩ := S.H_run hbl
  have hcol : ∀ k < 153, ∃ v, LoadHolds rd (w 617) k v := by
    intro k hk
    have hT : ReadsAt rd (ptr (S.cT bs)) S.xsT := subOf_memL hB (S.sub_xsT b hbl)
    rw [wr (j := 9) (k := 9) (a := 617) (by norm_num) (by decide) rfl, O.o9]
    simp only [Tables.VtHonest.retsH, Fs.squeeze, capOf, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    rw [show ofK (addressOfIndex (S.vtB bs sqE (S.leavesB (outs.take 9))).cur) = ptr (S.cT bs) from rfl,
      mul_assoc, mul_assoc, ← pow_succ', ← pow_add]
    simp only [loadHolds_mul_gen_pow]
    exact vs_rdgL hT (by rw [hxl]; show 13 + (3 * S.nT + 1) + k < _; omega)
  -- `claim_pool`
  have hpool : ∀ k ∈ [0, 1, 2, 3, 157, 158], ∃ v, LoadHolds rd (w 6) k v := by
    intro k hk
    rw [wa (i := 0) (a := 6) (by norm_num) rfl]
    have hl : S.H.poolW.length = 159 := by
      simp only [Tables.VtHonest.poolW, Tables.VtHonest.pcW, List.length_append,
        List.length_replicate, List.length_map, hOk.hx4]
      rfl
    refine vs_rdgL (xs := S.H.poolW) (own 0 (by norm_num)) ?_
    rw [hl]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  -- the ring map's nonce, challenges and `c_table`
  have o11 := O.o10
  have hnonce : LoadHolds rd (w 630) 0 S.ringN := by
    rw [wr (j := 10) (k := 5) (a := 630) (by norm_num) (by decide) rfl, o11]
    simp only [capOf, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
    have h := S.sub_stream b (P := sizeWords S.logMem S.rowsN S.rate ++ [S.x0, S.x1] ++
      [S.oodN, S.oodV] ++ [S.busN] ++ S.xsG ++ S.xsT ++ S.xsK) (X := [S.ringN])
      (R := S.xsW ++ streamPad c.proof.stream) (by rw [S.stream_eq hbl, streamPad]; simp)
    have hr := subOf_memL hB h 0 (by simp)
    simp only [List.length_append, S.sizeWords_length, List.length_cons, List.length_nil] at hr
    rw [show vb bs 1 + (8 + 2 + 2 + 1 + S.xsG.length + S.xsT.length + S.xsK.length) =
      S.cK bs + S.xsK.length by simp only [ChildSegs.cK, ChildSegs.cT, ChildSegs.cG]; omega,
      show ofK (addressOfIndex (S.cK bs + S.xsK.length)) = ptr (S.cK bs) * gen ^ S.xsK.length
        from vs_ptr_add _ _] at hr
    exact hr
  have hK : vsKCap w = capOf S.s6.perm := by
    simp only [vsKCap]
    rw [wr (j := 10) (k := 0) (a := 625) (by norm_num) (by decide) rfl,
      wr (j := 10) (k := 1) (a := 626) (by norm_num) (by decide) rfl,
      wr (j := 10) (k := 2) (a := 627) (by norm_num) (by decide) rfl,
      wr (j := 10) (k := 3) (a := 628) (by norm_num) (by decide) rfl,
      wr (j := 10) (k := 4) (a := 629) (by norm_num) (by decide) rfl, o11]
    rfl
  have hR : vsRchs (vsKCap w) S.ringN = S.rchs := by
    rw [hK]
    show challengeOf _ :: _ = challengeOf S.ringSt :: _
    rw [S.ringSt_eq hbl]
    rfl
  -- the deferred claim
  have hfresh := S.fresh_eq hbl
  have h580 : w 615 = S.H.bv := by
    rw [wr (j := 9) (k := 7) (a := 615) (by norm_num) (by decide) rfl, O.o9]
    simp only [Tables.VtHonest.retsH, Fs.squeeze, capOf, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
  obtain ⟨-, -, -, -, hzl, -⟩ := S.gkr_inv hbl
  -- the inlined grinds' words
  have hl : (vsArgs seed c sqE outE).length = 6 := rfl
  have hws : ∀ k < 11, LoadHolds rd (w 25) k ((vsStreamW c.proof.stream).getD k 0) :=
    fun k hk ↦ vs_rdg hS (by omega)
  obtain ⟨st8, -, -, st8', st9, st10⟩ := S.stream_words hbl
  have hroot := vs_rootFs (rd := rd) (w := w) hl (ws := vsStreamW c.proof.stream) (by omega)
    (fun k hk ↦ hws k (by omega))
  rw [vs_seedCap (rd := rd) (w := w) hl (seed := seed) (pi := statementDigest seed c.statement)
    rfl rfl rfl rfl, st8, st8', st9, show (⟨capOf (keccakF1600 (seedInput seed (statementDigest seed
    c.statement))), []⟩ : Fs) = seedFs seed (statementDigest seed c.statement) from rfl,
    ← S.sR_eq] at hroot
  have hOod : vsOodSt rd w (vsArgs seed c sqE outE) ((vsStreamW c.proof.stream).getD 10 0) =
      S.oodSt := by
    rw [vsOodSt, ← hroot, st10]; rfl
  have hMap : vsMapSt (vsKCap w) S.ringN = S.ringSt := by rw [hK, S.ringSt_eq hbl]; rfl
  exact ⟨{
    hl := rfl
    κ := κ
    hκ := hκ
    hlow := hlow
    ws := vsStreamW c.proof.stream
    hwl := by omega
    hws := fun k hk ↦ vs_rdg hS (by omega)
    hrows := fun i hi ↦ by
      rw [S.stream_rows hbl hi, wa (i := 2) (a := 26) (by norm_num) rfl]
      exact vs_rdg (xs := S.rowsN.map eOfNat) (own 2 (by norm_num)) (by simp [S.hrowsL]; omega)
    rate := S.rate
    logMem := S.logMem
    hr1 := S.hr1
    hr4 := S.hr4
    hlm1 := S.hlm1
    hlm30 := S.h30
    h64 := h64
    h72 := h72
    hsW := S.hs.map Hints.count
    hsWl := by simp [S.hs_length]
    hdims := hdims
    hkb := hkb
    hpush := hpush
    d := S.d
    m := S.μs
    hd20 := by omega
    hd33 := by omega
    hm20 := S.hmu20
    hm30 := S.hmu30
    h253 := h253
    h276 := h276
    hood := hood
    hfpw := hfpw
    hcol := hcol
    hpool := hpool
    nonce := S.ringN
    hnonce := hnonce
    hmaps := by
      rw [hR, wa (i := 13) (a := 918) (by norm_num) rfl]; exact own 13 (by norm_num)
    hct := by
      rw [hR, wa (i := 14) (a := 919) (by norm_num) rfl]; exact own 14 (by norm_num)
    zs := S.rG.2.1
    hzl := by omega
    hz := by rw [wa (i := 5) (a := 254) (by norm_num) rfl]; exact own 5 (by norm_num)
    al := S.H.slots
    hall := S.slots_length
    hal := by rw [wa (i := 10) (a := 605) (by norm_num) rfl]; exact own 10 (by norm_num)
    hout := by
      have h := hL _ hout
      rw [hfresh] at h
      rw [h580]
      exact h
    hwt := winTabs_vsExp fun q hq ↦ hL q (hexp q hq)
    hgw1 := fun j hj ↦ by rw [hOod]; exact vsW_win1 _ _ _ j hj
    hpow1 := by rw [hOod]; exact S.oodPow
    hgw2 := fun j hj ↦ by rw [hMap]; exact vsW_win2 _ _ _ j hj
    hpow2 := by rw [hMap]; exact S.ringPow }⟩

/-! ## The allocations -/

/-- **The allocations' sizes**: the fifteen buffers. -/
theorem vs_alloc_sizes {rd : Reader} {w : ℕ → E} {args : List E} :
    (vsCPre.filterMap Main.Stmt.allocSz).map
        (fun x ↦ x.2.elim id fun s ↦ logG (vsσ rd w args s)) = vsSizes := by
  rw [vs_allocs]
  rfl

theorem vs_allocVars_w : ∀ a ∈ vsAllocVars, a ∈ vsWVars := by
  have h : vsAllocVars.all (fun a ↦ vsWVars.contains a) = true := by decide +kernel
  intro a ha
  simpa using List.all_eq_true.mp h a ha

theorem vs_allocFst : (vsCPre.filterMap Main.Stmt.allocSz).map Prod.fst = vsAllocVars.map V.n := by
  rw [vs_allocs]; rfl

/-- **The allocations' bases**: the oracle's pointers. -/
theorem vs_alloc_bases {rd : Reader} {args : List E} (hl : args.length = 6) (gw : E × E) (bs : List ℕ)
    (outs : List (List E × Main.Layout)) (hbs : bs.length = 15) :
    ((vsCPre.filterMap Main.Stmt.allocSz).map Prod.fst).map (vsσ rd (vsW gw bs outs) args) =
      bs.map (fun x ↦ ofK (addressOfIndex x)) := by
  rw [vs_allocFst, List.map_map]
  apply List.ext_getElem (by rw [List.length_map, List.length_map, hbs]; rfl)
  intro i h1 h2
  have hi : i < 15 := by rw [List.length_map] at h1; exact h1
  rw [List.getElem_map, List.getElem_map, Function.comp_apply,
    vs_w hl (by rw [← List.getD_eq_getElem _ 0]; exact vs_allocVars_w _ (vsAllocVars_idx i hi).1),
    ← List.getD_eq_getElem _ 0, vsW_alloc gw bs outs hi, List.getD_eq_getElem _ _ (by omega)]

end
end LeanVM.Guest.B1.VerifySub
