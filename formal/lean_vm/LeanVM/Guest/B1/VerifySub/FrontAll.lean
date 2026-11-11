/-
  LeanVM.Guest.B1.VerifySub.FrontAll

  `verify_sub` up to its three calls, assembled: what its first statements establish.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.VerifySub.Mid
public import LeanVM.Guest.B1.VerifySub.Ctab
public import LeanVM.Guest.B1.VerifySub.Tail
public import LeanVM.Guest.B1.Tables.InterfaceC
public import LeanVM.Guest.B1.Bits.AssertCanonical

/-!
# The front of `verify_sub`, assembled

`vs_front`: the statements from the seed to the calls of `verify_bus_gkr`, `verify_tables` and
`verify_keccak` (G:3331-3436), under their callees' statements, establish `VsFront`: the seed,
the announced words absorbed, the root, the bus challenges and `β`, the rate and the memory's
log, the rows and heights certified by `verify_tables` (`dims_g`, `kb` and `kappa_base` on them),
the bus depth, the GKR's and the tables' runs and outputs, and `verify_keccak`'s call.

`verify_bus_gkr` needs `g_bus_mu ≠ 1`, which the push total gives once `verify_tables` has
certified the heights: `verify_tables` is first applied at the empty point when `g_bus_mu = 1`
(its precondition then holds), which contradicts the push total.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The push total of the memory's log `m` and the heights `hs`. -/
def pushTotal (m : ℕ) (hs : List ℕ) : ℕ := ((List.range 54).map fun b ↦ 2 ^ pushKappa m hs b).sum

/-- The bus challenges' values. -/
def vsAlphas (σ : Val) : List E := [σ (.n 366), σ (.n 386), σ (.n 406), σ (.n 426)]

/-- **What `verify_sub`'s front establishes.** -/
structure VsFront (bytecode : List K) (C : CallRel) (rd : Reader) (σ : Val) : Type where
  seed : Digest
  pi : Digest
  hseed : (σ (.n 2), σ (.n 3)) = digestHalves seed
  hpi : (σ (.n 0), σ (.n 1)) = digestHalves pi
  hcap0 : [σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)] =
    capOf (keccakF1600 (seedInput seed pi))
  h10 : σ (.n 8) = 0
  h11 : σ (.n 9) = 0
  h12 : σ (.n 10) = 0
  h13 : σ (.n 11) = 0
  hw : ∀ i < 8, WordAt rd σ i (vsX i)
  hrw : ∀ i < 6, LoadHolds rd (σ (.n 26)) i (σ (.n (vsX (i + 1))))
  w8 : WordAt rd σ 8 324
  w9 : WordAt rd σ 9 334
  hc537 : IsCanonical128 (σ (.n 324))
  hc547 : IsCanonical128 (σ (.n 334))
  hab8 : (⟨[σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)], []⟩ : Fs).absorbAll
      (vsWords σ) dsObserve =
    ⟨[σ (.n 75), σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79)],
      [(σ (.n 80), dsObserve), (σ (.n 90), dsObserve), (σ (.n 100), dsObserve),
        (σ (.n 110), dsObserve)]⟩
  habR : (((⟨[σ (.n 75), σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79)],
      [(σ (.n 80), dsObserve), (σ (.n 90), dsObserve), (σ (.n 100), dsObserve),
        (σ (.n 110), dsObserve)]⟩ : Fs).absorb (σ (.n 324)) dsObserve).absorb (σ (.n 334))
      dsObserve) =
    ⟨[σ (.n 319), σ (.n 320), σ (.n 321), σ (.n 322), σ (.n 323)],
      [(σ (.n 324), dsObserve), (σ (.n 334), dsObserve)]⟩
  halpha : (⟨[σ (.n 319), σ (.n 320), σ (.n 321), σ (.n 322), σ (.n 323)],
      [(σ (.n 324), dsObserve), (σ (.n 334), dsObserve)]⟩ : Fs).squeezeN 4 =
    (vsAlphas σ, ⟨[σ (.n 415), σ (.n 416), σ (.n 417), σ (.n 418), σ (.n 419)], []⟩)
  hbeta : (⟨[σ (.n 415), σ (.n 416), σ (.n 417), σ (.n 418), σ (.n 419)], []⟩ : Fs).squeeze =
    (σ (.n 623), ⟨[σ (.n 612), σ (.n 613), σ (.n 614), σ (.n 615), σ (.n 616)], []⟩)
  halphaR : ReadsAt rd (σ (.n 346)) (vsAlphas σ)
  hfpw : ReadsAt rd (σ (.n 427)) (eqKernel (vsAlphas σ))
  lir : ℕ
  logMem : ℕ
  hl1 : 1 ≤ lir
  hl4 : lir ≤ 4
  e112 : σ (.n 110) = eOfNat lir
  e124 : σ (.n 122) = gen ^ (lir - 1)
  hlm1 : 1 ≤ logMem
  hm32 : logMem ≤ 32
  e29 : σ (.n 27) = eOfNat logMem
  e130 : σ (.n 128) = gen ^ logMem
  rowsN : List ℕ
  hrowsL : rowsN.length = 6
  hrows : ReadsAt rd (σ (.n 26)) (rowsN.map eOfNat)
  hdims : ReadsAt rd (σ (.n 127)) (gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·))
  hh33 : ∀ h ∈ Tables.tableHeightsOf rowsN, h < 33
  hkb : ReadsAt rd (σ (.n 139)) (1 :: gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·))
  hkbv : ∀ s < 8, σ (.n (140 + s)) = gen ^ (([0, logMem] ++ Tables.tableHeightsOf rowsN).getD s 0)
  e522 : σ (.n 309) = gen ^ log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN))
  hdep : log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) < 33
  xsG : List E
  r : E × List E × List E
  capG : List E
  hxsG : ReadsAt rd (σ (.n 25) * gen ^ 10) xsG
  hrunG : RunsTo (Tables.gkrPhase (log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN))))
    ⟨[σ (.n 612), σ (.n 613), σ (.n 614), σ (.n 615), σ (.n 616)], []⟩ xsG r ⟨capG, []⟩
  hptL : r.2.1.length = log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN))
  hvL : r.2.2.length = 3
  hzeta : ReadsAt rd (σ (.n 310)) r.2.1
  hretG : [σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630), σ (.n 631), σ (.n 632),
    σ (.n 633), σ (.n 634)] = capG ++ [σ (.n 25) * gen ^ 10 * gen ^ xsG.length] ++ r.2.2
  xsT : List E
  capT : List E
  bus : BusResult
  claims : List ColumnClaim
  hxsT : ReadsAt rd (σ (.n 631)) xsT
  hrunT : ∀ ev, Tables.BytecodeAt ev bytecode
      (r.2.1.take (Tables.layoutOf bytecode logMem rowsN).logBytecode ++ vsAlphas σ) (σ (.n 643)) →
    RunsTo (Tables.tablesSeg ev (Tables.layoutOf bytecode logMem rowsN) pi (vsAlphas σ) (σ (.n 623))
      r.2.1 r.2.2) ⟨[σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630)], []⟩ xsT
      (bus, claims) ⟨capT, []⟩
  hclaimsL : claims.length = Tables.nClaims
  hpool : ReadsAt rd (σ (.n 6)) ((claims.take Tables.nBusClaims).map (·.value))
  hcew : ReadsAt rd (σ (.n 645))
    (((claims.drop Tables.nBusClaims).take Tables.nColEvals).map (·.value))
  hpoolPI : ReadsAt rd (σ (.n 6) * gen ^ Tables.nPooled) ((claims.drop Tables.nPooled).map (·.value))
  hctx : Tables.TCtx rd (Tables.layoutOf bytecode logMem rowsN) bus claims
    [σ (.n 310), σ (.n 635), σ (.n 644), σ (.n 309), σ (.n 642)]
  hcapT : [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640)] = capT
  e854 : σ (.n 641) = σ (.n 631) * gen ^ xsT.length
  l858 : LoadHolds rd (σ (.n 127)) 6 (σ (.n 646))
  e862 : σ (.n 650) = σ (.n 645) * word 237494511599616 0 0
  hkc : C "verify_keccak" [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640), σ (.n 641),
      σ (.n 646), σ (.n 635), σ (.n 650), σ (.n 647), σ (.n 648)]
    [σ (.n 651), σ (.n 652), σ (.n 653), σ (.n 654), σ (.n 655), σ (.n 656), σ (.n 657), σ (.n 658)]
  hcopy : ∀ i < 5, σ (.n (659 + i)) = σ (.n (651 + i))

theorem gSquares_of_exp {rd : Reader} {sq : E} (h : ExpTables rd sq) :
    ReadsAt rd sq Tables.gSquaresList := by
  intro k hk
  simp only [Tables.gSquaresList, List.length_map, List.length_range] at hk
  simpa [Tables.gSquaresList] using h.1 k hk

/-- What `verify_tables` reads of the exponent table: the squares, the rank keys, the sides. -/
theorem expTablesAt_of {rd : Reader} {sq : E} (h : ExpTables rd sq) : Tables.ExpTablesAt rd sq := by
  refine ⟨gSquares_of_exp h, fun k hk ↦ ?_, fun gi hgi ↦ ?_⟩
  · simp only [Tables.rankKeysList, List.length_map, List.length_range] at hk
    rw [loadHolds_mul_gen_pow]
    simpa [Tables.rankKeysList] using h.2.2.1 k hk
  · simp only [Tables.sideTabList, List.length_map, List.length_range] at hgi
    rw [loadHolds_mul_gen_pow]
    simp only [Tables.sideTabList, List.getElem_map, List.getElem_range]
    have h0 := fun gi (h1 : gi < 9) ↦ h.2.2.2 0 (by decide) gi (by simp [sideGroupStart]) (by
      simpa [sideGroupStart] using h1)
    have h1 := fun gi (h1 : 9 ≤ gi) (h2 : gi < 18) ↦ h.2.2.2 1 (by decide) gi (by
      simpa [sideGroupStart] using h1) (by simpa [sideGroupStart] using h2)
    have h2 := fun gi (h1 : 18 ≤ gi) (h2 : gi < 24) ↦ h.2.2.2 2 (by decide) gi (by
      simpa [sideGroupStart] using h1) (by simpa [sideGroupStart] using h2)
    interval_cases gi
    all_goals first
      | exact h0 _ (by decide)
      | exact h1 _ (by decide) (by decide)
      | exact h2 _ (by decide) (by decide)

theorem readsAt_ext {rd : Reader} {p : E} {xs ys : List E} (hl : xs.length = ys.length)
    (hx : ReadsAt rd p xs) (hy : ReadsAt rd p ys) : xs = ys :=
  List.ext_getElem hl fun k h1 h2 ↦ loadHolds_unique (hx k h1) (hy k h2)

theorem pushTotal_ge (m : ℕ) (hs : List ℕ) : 2 ^ m ≤ pushTotal m hs := by
  unfold pushTotal
  have : 2 ^ pushKappa m hs 1 ∈ (List.range 54).map fun b ↦ 2 ^ pushKappa m hs b :=
    List.mem_map.2 ⟨1, by simp, rfl⟩
  have h1 : pushKappa m hs 1 = m := by simp [pushKappa, Tables.blockKappaSrc, Tables.blockKappaAdj]
  rw [h1] at this
  exact List.le_sum_of_mem this


theorem vsPushT_noRet : Stmt.noRetList vsPushT = true := by decide +kernel

/-- The rows certified by a `verify_tables` call, at any point its precondition admits. -/
theorem tables_heights {bytecode : List K} {rd : Reader} {pi : Digest} {logMem : ℕ}
    {alphas point values : List E} {σ : Val}
    (hT : Tables.TablesOut bytecode pi logMem alphas point values rd
      [σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630), σ (.n 631), σ (.n 0), σ (.n 1),
        σ (.n 310), σ (.n 309), σ (.n 127), σ (.n 26), σ (.n 4), σ (.n 427), σ (.n 623), σ (.n 6),
        σ (.n 635), σ (.n 632), σ (.n 633), σ (.n 634)]
      [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640), σ (.n 641), σ (.n 642),
        σ (.n 643), σ (.n 644), σ (.n 645)]) :
    ∃ rowsN : List ℕ, rowsN.length = 6 ∧
      ReadsAt rd (σ (.n 127)) (gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·)) ∧
      ∀ h ∈ Tables.tableHeightsOf rowsN, h < 33 := by
  obtain ⟨-, -, rowsN, -, -, hl, -, hd, hh, -⟩ := hT
  exact ⟨rowsN, hl, hd, hh⟩

theorem tableHeights_length (rowsN : List ℕ) (h : rowsN.length = 6) :
    (Tables.tableHeightsOf rowsN).length = 6 := by
  simp [Tables.tableHeightsOf, h, tableLogFloors]

/-- **`verify_sub`'s front.** -/
theorem vs_front {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ) {C : CallRel}
    (hC : CallRel.Le C (coreProgram.Rel L.read)) (bytecode : List K)
    (hgkr : Tables.verify_bus_gkr_SpecC L.read C) (htab : Tables.verify_tables_SpecC bytecode L.read C)
    {σ : Val} {next : Prop} {kret : List E → Prop}
    (hexp : ExpTables L.read (σ (.n 4)))
    (h : Stmt.HoldsList C L.read σ (vsHeadT ++ vsReadsT ++ vsSizesT ++ vsPushT ++
      vsRootsT ++ vsAlphasT ++ vsFpwT ++ vsCallsT) next kret) :
    Nonempty (VsFront bytecode C L.read σ) ∧ next := by
  simp only [holdsList_append] at h
  obtain ⟨h10, h11, h12, h13, hk, h⟩ := vsHeadT_holds h
  obtain ⟨seed, pi, hseed, hpi, hcap0⟩ := vs_seed hk h10 h11 h12 h13
  obtain ⟨hw, hrw, hk50, h⟩ := vsReadsT_holds h
  obtain ⟨lir, logMem, hl1, hl4, e112, e124, hlm1, hm32, e29, e130, ds, hdsL, hdims0, hkb0, hkbv0,
    h⟩ := vsSizesT_holds hκ L hC h
  obtain ⟨hP, h⟩ := (holdsList_noRet vsPushT vsPushT_noRet _ _).1 h
  obtain ⟨hk649, w8, w9, ca1, ca2, h⟩ := vsRootsT_holds h
  obtain ⟨halpha, halphaR, h⟩ := vsAlphasT_holds h10 h11 h12 h13 w8 w9 h
  obtain ⟨hfpw, h⟩ := vsFpwT_holds (alphas := vsAlphas σ) rfl halphaR h
  obtain ⟨hbeta, h⟩ := vsSqzT_holds h10 h11 h12 h13 h
  obtain ⟨e838, cg, ct, l858, e862, ck, hcopy, hn⟩ := vsCallsT_holds h
  have hc537 := ((assert_canonical_holds L.read _ _).1 (hC _ _ _ ca1)).1
  have hc547 := ((assert_canonical_holds L.read _ _).1 (hC _ _ _ ca2)).1
  have ct' : C "verify_tables" [σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630),
      σ (.n 631), σ (.n 0), σ (.n 1), σ (.n 310), σ (.n 309), σ (.n 127), σ (.n 26), σ (.n 4),
      σ (.n 427), σ (.n 623), σ (.n 6), σ (.n 635), σ (.n 632), σ (.n 633), σ (.n 634)]
      [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640), σ (.n 641), σ (.n 642),
        σ (.n 643), σ (.n 644), σ (.n 645)] := ct
  have hTA : ∀ point : List E, ReadsAt L.read (σ (.n 310)) point →
      σ (.n 309) = gen ^ point.length → point.length < 33 →
      Tables.TablesOut bytecode pi logMem (vsAlphas σ) point [σ (.n 632), σ (.n 633), σ (.n 634)]
        L.read _ _ := fun point hp hg hl ↦ htab pi logMem (vsAlphas σ) point _ _ _
      (by
        simp only [Tables.TablesPre]
        exact ⟨hpi, hp, hg, hl, hlm1, hm32, ⟨ds, hdsL, hdims0⟩, expTablesAt_of hexp, rfl,
          hfpw, trivial⟩) ct'
  -- the push total, once the heights are certified
  have hpush : ∀ rowsN : List ℕ, rowsN.length = 6 →
      ReadsAt L.read (σ (.n 127)) (gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·)) →
      (∀ h ∈ Tables.tableHeightsOf rowsN, h < 33) →
      ds = (Tables.tableHeightsOf rowsN).map (gen ^ ·) ∧
      σ (.n 309) = gen ^ log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) ∧
        log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) < 34 := by
    intro rowsN hrl hd hh
    have eds : ds = (Tables.tableHeightsOf rowsN).map (gen ^ ·) := by
      have := readsAt_ext (by simp [hdsL, tableHeights_length rowsN hrl]) hdims0 hd
      simpa using this
    subst eds
    obtain ⟨e, b, -⟩ := vsPushT_holds hκ hκ6 L hC hexp hh hm32
      (fun s hs ↦ by rw [hkbv0 s hs, kbase_getD (tableHeights_length rowsN hrl) hs]) hP
    exact ⟨rfl, e, b⟩
  have hpos : ∀ rowsN : List ℕ, 0 < log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) :=
    fun rowsN ↦ lt_log2Ceil_iff.2 (lt_of_lt_of_le (by
      have := Nat.one_lt_two_pow_iff.2 (show logMem ≠ 0 by omega)
      simpa using this) (pushTotal_ge logMem _))
  have hne : σ (.n 309) ≠ 1 := by
    intro h1
    obtain ⟨rowsN, hrl, hd, hh⟩ := tables_heights (hTA [] (fun k hk ↦ absurd hk (by simp))
      (by rw [h1, List.length_nil, pow_zero]) (by simp))
    obtain ⟨-, e, b⟩ := hpush rowsN hrl hd hh
    rw [h1, ← pow_zero gen] at e
    have := gen_pow_inj (by norm_num) (by omega) e
    have := hpos rowsN
    omega
  obtain ⟨depth, xsG, r, capG, hgmu, hdlt, hxsG, hrunG, hptL, hvL, hzeta, hretG⟩ :=
    hgkr _ _ (by simpa using hne) cg
  have hretG' : [σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630), σ (.n 631)] ++
      [σ (.n 632), σ (.n 633), σ (.n 634)] = (capG ++ [σ (.n 625) * gen ^ xsG.length]) ++ r.2.2 :=
    hretG
  obtain ⟨hret1, hvals⟩ := List.append_inj' hretG' (by rw [hvL]; rfl)
  rw [show [σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630), σ (.n 631)] =
    [σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630)] ++ [σ (.n 631)] from rfl] at hret1
  obtain ⟨hcapG, h844⟩ := List.append_inj' hret1 rfl
  simp only [List.cons.injEq, and_true] at h844
  have hT := hTA r.2.1 hzeta (by rw [hptL]; exact hgmu) (by rw [hptL]; exact hdlt)
  obtain ⟨xsT, capT, rowsN, bus, claims, hrl, hrows, hdims, hh, hxsT, hrunT, hcl, hpool, hcew,
    hpoolPI, hctx, hcapT, e854⟩ := hT
  obtain ⟨eds, e522, hlt⟩ := hpush rowsN hrl hdims hh
  have edep : depth = log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) :=
    gen_pow_inj (by omega) (by omega) (hgmu.symm.trans e522)
  have hkbv : ∀ s < 8, σ (.n (140 + s)) =
      gen ^ (([0, logMem] ++ Tables.tableHeightsOf rowsN).getD s 0) := fun s hs ↦ by
    rw [hkbv0 s hs, eds, kbase_getD (tableHeights_length rowsN hrl) hs]
  rw [eds] at hkb0
  rw [edep] at hrunG hptL hdlt
  refine ⟨⟨VsFront.mk
    (seed := seed) (pi := pi) (hseed := hseed) (hpi := hpi) (hcap0 := hcap0) (h10 := h10)
    (h11 := h11) (h12 := h12) (h13 := h13) (hw := hw) (hrw := hrw) (w8 := w8) (w9 := w9)
    (hc537 := hc537)
    (hc547 := hc547) (hab8 := vs_absorb8 hw hk50) (habR := vs_absorbRoot hw hk649)
    (halpha := halpha) (hbeta := hbeta) (halphaR := halphaR) (hfpw := hfpw) (lir := lir)
    (logMem := logMem) (hl1 := hl1) (hl4 := hl4) (e112 := e112) (e124 := e124) (hlm1 := hlm1)
    (hm32 := hm32) (e29 := e29) (e130 := e130) (rowsN := rowsN) (hrowsL := hrl) (hrows := hrows)
    (hdims := hdims) (hh33 := hh) (hkb := hkb0) (hkbv := hkbv) (e522 := e522) (hdep := hdlt)
    (xsG := xsG) (r := r) (capG := capG) (hxsG := (by rw [← e838]; exact hxsG)) (hrunG := ?_)
    (hptL := hptL) (hvL := hvL) (hzeta := hzeta)
    (hretG := (by rw [← e838]; exact hretG')) (xsT := xsT) (capT := capT)
    (bus := bus) (claims := claims) (hxsT := hxsT) (hrunT := ?_) (hclaimsL := hcl)
    (hpool := hpool) (hcew := hcew) (hpoolPI := hpoolPI) (hctx := hctx) (hcapT := hcapT)
    (e854 := e854) (l858 := l858) (e862 := e862) (hkc := ck) (hcopy := hcopy)⟩, hn⟩
  · exact hrunG
  · rw [← hvals]; exact hrunT

end
end LeanVM.Guest.B1.VerifySub
