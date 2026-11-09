/-
  LeanVM.Guest.B1.VerifySub.SoundOf

  **`verify_sub` is sound**, given `verify_tables`' soundness: a run of its body gives a child
  proof, read off its valuation, the memory and the frame map, that the deferring verifier accepts.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.VerifySub.Back
public import LeanVM.Guest.B1.VerifySub.Body
public import LeanVM.Guest.B1.VerifySub.Stack
public import LeanVM.Guest.B1.VerifySub.Dispatch
public import LeanVM.Guest.B1.VerifySub.Stream
public import LeanVM.Guest.B1.Terminal.Holds
public import LeanVM.Guest.B1.Ring.Target
public import LeanVM.Guest.B1.Selectors.ColumnSelector
public import LeanVM.Guest.B1.Selectors.SelectorTables
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
public import LeanVM.Guest.B1.Main.SoundV
public import LeanVM.Guest.B1.Tables.InterfaceC
public import LeanVM.Guest.B1.Gkr.Holds
public import LeanVM.Guest.B1.Placement.Certify
public import LeanVM.Guest.B1.VerifySub.Gw
public import LeanVM.Guest.B1.VerifySub.TermGlue

/-!
# `verify_sub` is sound

`verify_sub_sound_w_of`: given `verify_tables`' soundness on memory images of at most `2^32` words
(`htab`, `Tables.verify_tables_Spec`), for a bytecode of `2^23` words, on a memory image of at most `2^32` words,
under any call relation below `coreProgram.Rel` that unfolds at the frame map `V`, a run of
`verify_sub`'s body with the exponent table at its argument `4` returns nothing, and the
deferring verifier accepts the child proof `vsPiOf L.read σ V` for the statement at its
arguments: `Main.SubSoundW bytecode vsPiOf`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The announced words are the memory's log, the rows and the rate, as integer words. -/
theorem vsWords_eq {bytecode : List K} {C : CallRel} {rd : Reader} {σ : Val}
    (F : VsFront bytecode C rd σ) :
    vsWords σ = eOfNat F.logMem :: F.rowsN.map eOfNat ++ [eOfNat F.lir] := by
  have hr : [σ (.n 37), σ (.n 47), σ (.n 57), σ (.n 80), σ (.n 90), σ (.n 100)] =
      F.rowsN.map eOfNat := by
    refine readsAt_ext (by simp [F.hrowsL]) (fun k hk ↦ ?_) F.hrows
    simp only [List.length_cons, List.length_nil] at hk
    have := F.hrw k hk
    interval_cases k <;> exact this
  rw [vsWords, ← hr, ← F.e29, ← F.e112]
  rfl


theorem stackClaims_values (L : Layout) (claims : List ColumnClaim) (out : ColumnClaim)
    (rp sl chs : List E) : (stackClaims L claims [out] rp sl chs).map (·.2) =
      polyEval (sl.map (phiMap · chs)) gen :: ((notLanes claims).map (·.value) ++ [out.value]) := by
  simp [stackClaims, ringSwitchClaim, ColumnClaim.stackClaim, notLanes]

theorem stackClaims_length (L : Layout) (claims : List ColumnClaim) (out : ColumnClaim)
    (rp sl chs : List E) :
    (stackClaims L claims [out] rp sl chs).length = (notLanes claims).length + 2 := by
  simp [stackClaims, notLanes]

theorem stackClaims_weight (L : Layout) (claims : List ColumnClaim) (out : ColumnClaim)
    (rp sl chs : List E) (lam : E) (x : List E) :
    dot (powers lam (stackClaims L claims [out] rp sl chs).length)
        ((stackClaims L claims [out] rp sl chs).map fun c ↦ c.1 x) =
      stackWeight L (openedClaims claims [out]) rp (ringCoefficients chs) lam x := rfl

theorem runsWith_whirOpen_target {μ r : ℕ} {t t' : E} (h : t = t') {s s' : Fs} {xs : List E}
    {os : List (List Opening)} {roots roots' : List (Digest × ℕ × ℕ)} {w : B1.Whir.WhirEnd}
    (hr : B1.Whir.RunsWith (B1.Whir.whirOpen μ r t) s xs os roots w s' roots') :
    B1.Whir.RunsWith (B1.Whir.whirOpen μ r t') s xs os roots w s' roots' := h ▸ hr

/-- **`verify_sub` is sound**, given `verify_tables`' soundness, its child proof read off its
valuation, the memory and the frame map. -/
theorem verify_sub_sound_w_of (bytecode : List K)
    (htab : bytecode.length = 2 ^ 23 → ∀ {κ : ℕ}, κ ≤ 32 → ∀ (L : MemoryImage κ),
      Tables.verify_tables_Spec bytecode L.read) :
    Main.SubSoundW bytecode vsPiOf := by
  intro hbl κ L hκ C V hU hLe σ rets hb hpre
  have hexp : ExpTables L.read (σ (.n 4)) := by
    simpa [VerifySubPre, vs_params] using hpre
  rw [show Fn.body Data.core18 = vsT from vs_body, vsT_split, holdsList_append] at hb
  obtain ⟨hF0, hR⟩ := (holdsList_noRet vsFrontT vsFrontT_noRet _ _).1 hb
  have hz := hF0
  simp only [vsFrontT, holdsList_append] at hz
  obtain ⟨h10, h11, h12, h13, -, -⟩ := vsHeadT_holds hz
  -- the memory holds at least `64` words (the coefficients' table)
  have hκ6 : 6 ≤ κ := by
    have hR' := hR
    rw [holdsList_append, holdsList_append] at hR'
    obtain ⟨-, hmR, hR'⟩ := vsMapsT_holds h10 h11 h12 h13 hR'
    obtain ⟨hct, -⟩ := vsCtabT_holds (chs := σ (.n 658) :: vsChs σ) rfl hmR hR'
    have := mem_size hκ L (n := 64) (by norm_num) (fun j hj ↦
      ⟨_, hct j (by simp [ringCoefficients, kBits]; omega)⟩)
    by_contra hlt
    have : 2 ^ κ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨⟨F⟩, -⟩ := vs_front hκ hκ6 L hLe bytecode
    (Tables.verify_bus_gkr_SpecC_of hLe (Tables.verify_bus_gkr_holds hκ L))
    (Tables.verify_tables_SpecC_of hLe (htab hbl hκ L)) hexp hF0
  have hctx := F.hctx
  simp only [Tables.TCtx] at hctx
  obtain ⟨chis0, hbp, hgmu, -, -, -, hcl, hcol, -⟩ := hctx
  obtain ⟨hmaps, hchR, hct, hrstC, hlam, h1884, h1886, hcp, hl2, e1892, r1, e1901, r2, hdisp,
    hterm, hd1, hd2, hd3, hkret⟩ :=
    vs_back h10 h11 h12 h13 hcol (claimAt_reads hcl F.hpool F.hcew F.hpoolPI) hR
  refine ⟨hkret.symm, ?_⟩
  -- the output lanes
  obtain ⟨chis, hchiR, hτc, hlcol, hlpt, hout, hl25⟩ := vs_lanes hbl F
  have hτ9 := tau_ge F.hrowsL
  have hτ28 : vsTau F.rowsN ≤ 28 := by
    have := tau_lt F.hrowsL F.hh29
    show (Tables.tableHeightsOf F.rowsN).getD 5 0 ≤ 28
    omega
  have hsL := tableHeights_length _ F.hrowsL
  have htg : σ (.n 646) = gen ^ vsTau F.rowsN := by
    refine loadHolds_unique F.l858 ?_
    have h6 := F.hdims 6 (by simp [hsL])
    have e6 : (gen ^ F.logMem :: (Tables.tableHeightsOf F.rowsN).map (gen ^ ·))[6]'(by simp [hsL]) =
        gen ^ vsTau F.rowsN := by
      simp only [List.getElem_cons_succ, List.getElem_map, vsTau]
      rw [List.getD_eq_getElem _ _ (by rw [hsL]; omega)]
    rw [e6] at h6
    exact h6
  -- `verify_keccak`
  have hk := verify_keccak_holds L.read _ _ (hLe _ _ _ F.hkc)
  simp only [MeaningVerifyKeccak] at hk
  obtain ⟨xsK, op, point, slices, capK, word, m0, hxsK, hrunK, hop, hpoint, hsl, hopL, hpointL,
    hslL, hretK⟩ :=
    hk (vsTau F.rowsN) chis ((lanesOf F.claims).map (·.value)) hτ9 hτ28 htg hτc hchiR
      (by simp [hl25]) (by rw [F.e862, word_g107]; exact hout)
  have hretK' : [σ (.n 651), σ (.n 652), σ (.n 653), σ (.n 654), σ (.n 655)] ++
      [σ (.n 656), σ (.n 657), σ (.n 658)] = capK ++ [σ (.n 641) * gen ^ xsK.length, word, m0] :=
    hretK
  obtain ⟨hcapK, hK3⟩ := List.append_inj' hretK' rfl
  simp only [List.cons.injEq, and_true] at hK3
  obtain ⟨e868, e869, e870⟩ := hK3
  -- the ring switch's target
  have hrt := ring_switch_target_holds L.read _ _ (hLe _ _ _ hrstC)
  simp only [MeaningRingTarget] at hrt
  obtain ⟨s', ch', hs'L, hch'L, hs'R, hch'R, hr1303⟩ := hrt
  have ech' : ch' = σ (.n 658) :: vsChs σ := readsAt_ext (by rw [hch'L]; rfl) hch'R hchR
  simp only [List.cons.injEq, and_true] at hr1303
  -- the stack
  obtain ⟨hμ22, hμ28, hcand, hP, hKB⟩ :=
    vs_stack hκ hκ6 L hLe (Tables.certify_placement_holds hκ L) hbl F hexp hcp hl2 e1892 r1 e1901 r2
  -- the opening
  obtain ⟨root, hroot⟩ := digest_of_canonical F.hc537 F.hc547
  obtain ⟨w, s10, roots', hxsW, hrunW, hwL, pt, pt1, hretsW, hptR, hpt1R⟩ :=
    vs_dispatch (osSoundW_of hκ hU hLe) hμ22 hμ28 F.hl1 F.hl4 hcand hdisp hroot
  simp only [List.cons.injEq, and_true] at hretsW
  obtain ⟨e1906, e1907, e1908, e1909, e1910⟩ := hretsW
  -- the bus point
  have hbpL : F.bus.point.length ≤ 40 := by
    have hle := mem_size_le hκ L hbp
    have := gen_pow_inj (by omega) (lt_trans F.hdep (by norm_num)) (hgmu.symm.trans F.e522)
    have := F.hdep
    omega
  -- the terminal
  obtain ⟨-, hTacc⟩ := check_opening_terminal_holds Tables.column_selector_holds
    Tables.selector_tables_holds hκ L _ _ (hLe _ _ _ hterm)
  have hacc := hTacc (Tables.layoutOf bytecode F.logMem F.rowsN) F.bus F.claims
    ⟨qkeccak, op, word⟩ (σ (.n 1111)) point (ringCoefficients (σ (.n 658) :: vsChs σ)) w.point (by
      simp only [TermPre]
      refine ⟨termCtx_of_tctx F.hctx, hP, hKB, layoutOf_placements hbl _ _, layoutOf_stackLog hbl _ _, hμ28,
        show 1 ≤ F.logMem by have := F.hm16; omega, F.hm32, hbpL, hsL, F.hh29, F.e130, htg, F.hkb,
        gTabs_of_exp hexp, trivial, trivial, hopL, hop, hpointL, hpoint, by simp [ringCoefficients, kBits],
        hct, hwL, ?_, ?_⟩
      · rw [padPoint, hwL, e1907]; exact hptR
      · rw [padPoint, hwL, List.map_append, List.map_replicate, add_zero, e1908]; exact hpt1R)
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hacc
  -- the terminal's check, as `whirOpen`'s acceptance
  have hAcc : w.Accepts fun x ↦ dot (powers (σ (.n 1111))
      (stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) F.claims [⟨qkeccak, op, word⟩] point
        slices (m0 :: vsChs σ)).length)
      ((stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) F.claims [⟨qkeccak, op, word⟩] point
        slices (m0 :: vsChs σ)).map fun c ↦ c.1 x) := by
    unfold B1.Whir.WhirEnd.Accepts
    beta_reduce
    rw [stackClaims_weight, ← e870, ← e1909, ← e1910, ← e1906]
    exact hacc
  -- the batched target
  have es' : s' = slices := readsAt_ext (by rw [hs'L, hslL]; rfl) hs'R hsl
  have htarget : σ (.n 1681) = dot (powers (σ (.n 1111))
      (stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) F.claims [⟨qkeccak, op, word⟩] point
        slices (m0 :: vsChs σ)).length)
      ((stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) F.claims [⟨qkeccak, op, word⟩] point
        slices (m0 :: vsChs σ)).map (·.2)) := by
    rw [stackClaims_values, stackClaims_length, h1886, hr1303, es', ech', ← e870, ← e869]
  -- the runs
  obtain ⟨level, rest, hcfg⟩ := cfg_cons hμ22 hμ28 F.hl1 F.hl4
  have h1 := readSizes_runsTo hbl F.hm16 F.hm32 F.hrowsL F.hh29 F.hl1 F.hl4 hμ28
    (⟨[σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)], []⟩ : Fs)
  rw [← vsWords_eq F, F.hab8] at h1
  have hroot' : digestFromHalves (σ (.n 324), σ (.n 334)) = some root := by
    rw [hroot]; exact digestOfScalars_digestScalars root
  have h3 : (((⟨[σ (.n 75), σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79)],
      [(σ (.n 80), dsObserve), (σ (.n 90), dsObserve), (σ (.n 100), dsObserve),
        (σ (.n 110), dsObserve)]⟩ : Fs).absorb (σ (.n 324)) dsObserve).absorb (σ (.n 334))
        dsObserve).squeezeN busBits =
      (vsAlphas σ, ⟨[σ (.n 415), σ (.n 416), σ (.n 417), σ (.n 418), σ (.n 419)], []⟩) := by
    rw [F.habR]; exact F.halpha
  have h5 := F.hrunG
  rw [F.capG_eq, show log2Ceil (pushTotal F.logMem (Tables.tableHeightsOf F.rowsN)) =
    (busLayout [0, F.logMem, (Tables.layoutOf bytecode F.logMem F.rowsN).logBytecode]
      (Tables.layoutOf bytecode F.logMem F.rowsN).push).depth from
    (pushDepth_eq hbl F.logMem F.rowsN F.hrowsL).symm] at h5
  have h6 := F.hrunT (claimedBytecodeValue (vsFixed σ F.r.2.1)) (by
    rw [logBytecode_eq hbl]; exact bytecodeAt_claimed bytecode _ _)
  rw [← F.hcapT] at h6
  have hne : lanesOf F.claims ≠ [] := by intro h; rw [h] at hl25; simp at hl25
  have hhd : ((lanesOf F.claims).headD default).point = chis.take (vsTau F.rowsN) := by
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    have hc : c ∈ lanesOf F.claims := by rw [hcs]; exact List.mem_cons_self
    rw [hcs]
    exact hlpt c hc
  have h7 : (lanesOf F.claims).map (·.column) = keccakOutputColumns ∧
      ∀ c ∈ lanesOf F.claims, c.point = ((lanesOf F.claims).headD default).point :=
    ⟨hlcol, fun c hc ↦ by rw [hlpt c hc, hhd]⟩
  have h8 : RunsTo (keccakSeg ((Tables.layoutOf bytecode F.logMem F.rowsN).tableLogHeights.getD
      opKeccak 0) ((lanesOf F.claims).headD default).point ((lanesOf F.claims).map (·.value)))
      ⟨[σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640)], []⟩ xsK
      (([⟨qkeccak, op, word⟩], point, slices), m0) ⟨capK, []⟩ := by
    rw [hhd]; exact hrunK
  have hcopy : [σ (.n 651), σ (.n 652), σ (.n 653), σ (.n 654), σ (.n 655)] =
      [σ (.n 659), σ (.n 660), σ (.n 661), σ (.n 662), σ (.n 663)] := by
    rw [F.hcopy 0 (by omega), F.hcopy 1 (by omega), F.hcopy 2 (by omega), F.hcopy 3 (by omega),
      F.hcopy 4 (by omega)]
  have h9 : (⟨capK, []⟩ : Fs).squeezeN 5 =
      (vsChs σ, ⟨[σ (.n 754), σ (.n 755), σ (.n 756), σ (.n 757), σ (.n 758)], []⟩) := by
    rw [← hcapK, hcopy]; exact hmaps
  have h11 := runsWith_whirOpen_target htarget hrunW
  have hacc' := deferred_accepts (c := vsFixed σ F.r.2.1) (s0 := ⟨[σ (.n 20), σ (.n 21), σ (.n 22),
    σ (.n 23), σ (.n 24)], []⟩) ⟨F.hcap0.symm, rfl⟩ h1 hcfg hroot' h3 F.hbeta h5 h6 h7 h8 h9 hlam
    h11 hAcc
  -- the decoded proof
  have hcand28 : B1.Whir.candidate (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog F.lir < 28 := by
    unfold B1.Whir.candidate; have := F.hl4; omega
  have hidx : dispatchIdx (σ (.n 1695)) =
      B1.Whir.candidate (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog F.lir :=
    dispatchIdx_eq hcand28 (by rw [hcand, gen_pow_eq_ofK])
  have hπ : vsPiOf L.read σ V = ⟨vsWords σ ++ [σ (.n 324), σ (.n 334)] ++ F.xsG ++ F.xsT ++ xsK ++
      (vsOsW L.read V (B1.Whir.candidate (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog F.lir)
        (vsOsArgs σ) (vsOsRets σ)).1,
      (vsOsW L.read V (B1.Whir.candidate (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog F.lir)
        (vsOsArgs σ) (vsOsRets σ)).2⟩ := by
    simp only [vsPiOf, piOfW, hidx]
    rw [vs_stream hκ L F hxsK e868]
  -- the statement
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), rfl, F.seed, F.pi,
    vsFixed σ F.r.2.1, F.hseed, F.hpi, ?_, ?_, ?_⟩
  · have := F.hptL
    have := depth_ge (logMem := F.logMem) hsL
    show (F.r.2.1.take 19 ++ vsAlphas σ).length = 23
    rw [List.length_append, List.length_take, min_eq_left (by omega)]
    rfl
  · have hd20 := depth_ge (logMem := F.logMem) hsL
    have hrl := F.hptL
    simp only [Node.DeferredClaim.cells, vsFixed]
    rw [readsAt_append, readsAt_append, List.length_take, min_eq_left (by omega)]
    refine ⟨⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩, fun k hk ↦ ?_⟩
    · have hk' : k < 19 := by simp at hk; omega
      obtain ⟨v, h523, h6⟩ := hd1 k hk'
      rw [loadHolds_unique h523 (F.hzeta k (by omega))] at h6
      simpa using h6
    · rw [loadHolds_mul_gen_pow]
      obtain ⟨v, h559, h6⟩ := hd2 k (by simpa [vsAlphas] using hk)
      rw [loadHolds_unique h559 (F.halphaR k hk)] at h6
      exact h6
    · simp only [List.length_cons, List.length_nil] at hk
      obtain rfl : k = 0 := by omega
      rw [List.length_append, List.length_take, min_eq_left (by omega),
        show (vsAlphas σ).length = 4 from rfl, loadHolds_mul_gen_pow]
      exact hd3
  · rw [hπ]
    simp only [vsOsW, vsOsArgs, vsOsRets]
    exact hacc'

end
end LeanVM.Guest.B1.VerifySub
