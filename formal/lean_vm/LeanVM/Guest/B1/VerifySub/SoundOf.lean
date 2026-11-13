/-
  LeanVM.Guest.B1.VerifySub.SoundOf

  **`verify_sub` is sound**, given `open_stacked`'s soundness with its witness: a run of its body
  gives a child proof, read off its valuation, the memory and the frame map, that the deferring
  verifier accepts.
-/

module

public import LeanVM.Guest.B1.VerifySub.SoundFront
public import LeanVM.Guest.B1.VerifySub.Ctab
public import LeanVM.Guest.B1.VerifySub.Lam
public import LeanVM.Guest.B1.VerifySub.Lanes
public import LeanVM.Guest.B1.VerifySub.Dispatch
public import LeanVM.Guest.B1.VerifySub.Stream
public import LeanVM.Guest.B1.VerifySub.TermGlue
public import LeanVM.Guest.B1.VerifySub.Accept
public import LeanVM.Guest.B1.VerifySub.Body
public import LeanVM.Guest.B1.Terminal.Holds
public import LeanVM.Guest.B1.Ring.Target
public import LeanVM.Guest.B1.Selectors.ColumnSelector
public import LeanVM.Guest.B1.Selectors.SelectorTables
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.B1.Main.Interface
public import LeanVM.Guest.B1.Main.Frames

/-!
# `verify_sub` is sound

`verify_sub_sound_of`: given `open_stacked`'s soundness with its witness
(`Whir.open_stacked_sound_w_Spec Whir.open_stacked_osW`, S1a's), for a bytecode of `2^23` words,
on a memory image of at most `2^32` words, under any call relation below `coreProgram.Rel` that
unfolds at the frame map `V`, a run of `verify_sub`'s body under `VerifySubPre` returns nothing,
and the deferring verifier accepts the child proof `vsPiOf L.read σ V` for the statement at its
arguments (`Main.SubSoundW bytecode vsPiOf`, unfolded).

The front (`vs_front`) gives the phases up to `tablesSeg`; here `verify_keccak`'s meaning and the
output lanes give `keccakPhaseClaims`' run, the ring map's grind and challenges `ringSwitch`'s,
`λ` and the target, the dispatch `open_stacked`'s, and the terminal its check, which together are
`verifyStackedOpening`'s run (`deferred_accepts`). The decoded proof's words are the stream's up to
the cursor handed to `open_stacked`, then `open_stacked`'s.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem runsTo_require_true {c : Prop} [Decidable c] (h : c) (s : Fs) :
    RunsTo (VerifierProgram.require c) s [] () s := by
  rw [require_true h]; exact runsTo_ret () s

/-- **The stacked opening runs**, given its batching challenge's squeeze, `open_stacked`'s run of
`whirOpen` on the batched target and the terminal's check. -/
theorem runsWith_stacked {m lir : ℕ} {claims : List StackClaim} (hlen : claims.length ≤ 512)
    {s s1 s2 : Fs} {lam : E} (hs : s.squeeze = (lam, s1)) {xs : List E}
    {os : List (List Opening)} {roots roots' : List (Digest × ℕ × ℕ)} {w : Whir.WhirEnd}
    (hW : Whir.RunsWith (Whir.whirOpen m lir (dot (powers lam claims.length) (claims.map (·.2))))
      s1 xs os roots w s2 roots')
    (hacc : w.Accepts fun x ↦ dot (powers lam claims.length) (claims.map fun c ↦ c.1 x)) :
    Whir.RunsWith (verifyStackedOpening m lir claims) s xs os roots () s2 roots' := by
  have e : verifyStackedOpening m lir claims =
      (VerifierProgram.require (claims.length ≤ maxStackedClaims)).bind fun _ ↦
        VerifierProgram.sampleChallenge.bind fun lam ↦
          (Whir.whirOpen m lir (dot (powers lam claims.length) (claims.map (·.2)))).bind fun w ↦
            VerifierProgram.require (w.Accepts fun x ↦ dot (powers lam claims.length)
              (claims.map fun c ↦ c.1 x)) := by
    simp only [verifyStackedOpening, Whir.verifyWhir_split, VerifierProgram.bind_eq]
  rw [e]
  have hsam : RunsTo VerifierProgram.sampleChallenge s [] lam s1 := by
    have := runsTo_sampleE s
    rw [hs] at this
    exact this
  have h3 : Whir.RunsWith ((Whir.whirOpen m lir (dot (powers lam claims.length)
      (claims.map (·.2)))).bind fun w ↦ VerifierProgram.require (w.Accepts fun x ↦
        dot (powers lam claims.length) (claims.map fun c ↦ c.1 x))) s1 (xs ++ []) (os ++ []) roots
      () s2 roots' :=
    Whir.RunsWith.bind' hW (Whir.RunsTo.withRoots (runsTo_require_true hacc s2) roots')
  have h2 : Whir.RunsWith (VerifierProgram.sampleChallenge.bind fun lam' ↦
      (Whir.whirOpen m lir (dot (powers lam' claims.length) (claims.map (·.2)))).bind fun w ↦
        VerifierProgram.require (w.Accepts fun x ↦ dot (powers lam' claims.length)
          (claims.map fun c ↦ c.1 x))) s ([] ++ (xs ++ [])) ([] ++ (os ++ [])) roots () s2 roots' :=
    Whir.RunsWith.bind' (Whir.RunsTo.withRoots hsam roots) h3
  have h := Whir.RunsWith.bind' (f := fun _ ↦ VerifierProgram.sampleChallenge.bind fun lam' ↦
      (Whir.whirOpen m lir (dot (powers lam' claims.length) (claims.map (·.2)))).bind fun w ↦
        VerifierProgram.require (w.Accepts fun x ↦ dot (powers lam' claims.length)
          (claims.map fun c ↦ c.1 x)))
    (Whir.RunsTo.withRoots (runsTo_require_true (c := claims.length ≤ maxStackedClaims)
      (by unfold maxStackedClaims; omega) s) roots) h2
  exact Whir.RunsWith.of_eq h rfl (by simp) (by simp) rfl rfl rfl rfl

/-- **`keccakPhaseClaims` runs**: the output lanes' check, then the Keccak reduction's run. -/
theorem keccakPhase_runs {layout : Layout} {claims : List ColumnClaim} {τ : ℕ} {pt : List E}
    (hτL : layout.tableLogHeights.getD opKeccak 0 = τ)
    (hcol : (claims.filter fun c ↦ c.column ∈ keccakOutputColumns).map (·.column) =
      keccakOutputColumns)
    (hpt : ∀ c ∈ claims.filter (fun c ↦ c.column ∈ keccakOutputColumns), c.point = pt)
    (hhead : ((claims.filter fun c ↦ c.column ∈ keccakOutputColumns).headD default).point = pt)
    {s s' : Fs} {xs : List E} {outs : List ColumnClaim} {point slices : List E}
    (h : RunsTo (verifyKeccak τ pt
      ((claims.filter fun c ↦ c.column ∈ keccakOutputColumns).map (·.value))) s xs
      (outs, point, slices) s') :
    RunsTo (keccakPhaseClaims layout claims) s xs
      (claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++ outs, point, slices) s' := by
  unfold keccakPhaseClaims
  refine sz_runsTo_require_bind ⟨hcol, fun c hc ↦ (hpt c hc).trans hhead.symm⟩ ?_
  dsimp only
  rw [hτL, hhead]
  have hb := RunsTo.bind (f := fun x ↦ (pure (claims.filter (fun c ↦ c.column ∉
    keccakOutputColumns) ++ x.1, x.2.1, x.2.2) : VerifierProgram _)) h (runsTo_ret _ _)
  rw [List.append_nil] at hb
  exact hb

/-- The pooled claims the opening batches: all but the `25` output lanes'. -/
theorem filter_lanes_length {claims : List ColumnClaim}
    (hcol : claims.map (·.column) = Tables.claimColumns) :
    (claims.filter fun c ↦ c.column ∉ keccakOutputColumns).length = 134 := by
  have h : (claims.filter fun c ↦ c.column ∉ keccakOutputColumns).length =
      (Tables.claimColumns.filter fun x ↦ x ∉ keccakOutputColumns).length := by
    rw [← hcol, List.filter_map, List.length_map]
    rfl
  rw [h]
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- **`verify_sub` is sound**, given `open_stacked`'s soundness with its witness, its child proof
read off its valuation, the memory and the frame map. -/
theorem verify_sub_sound_of (hos : Whir.open_stacked_sound_w_Spec Whir.open_stacked_osW)
    (bytecode : List K) (hbl : bytecode.length = 2 ^ bytecodeVars) {κ : ℕ} (L : MemoryImage κ)
    (hκ : κ ≤ 32) (C : CallRel) (V : FrameMap) (hU : UnfoldsV L.read C V)
    (hLe : CallRel.Le C (coreProgram.Rel L.read)) (σ : Val) (rets : List E)
    (hb : Stmt.HoldsList C L.read σ (Fn.body fn% «verify_sub») False (fun rs ↦ rs = rets))
    (hpre : VerifySubPre L.read ((fn% «verify_sub»).params.map σ)) :
    rets = [] ∧ Main.VerifySubOut bytecode L.read ((fn% «verify_sub»).params.map σ) (vsPiOf L.read
        σ V) := by
  obtain ⟨hexp, hwin⟩ : ExpTables L.read (σ (.n 4)) ∧ ExpWinTab L.read (σ (.n 4)) := by
    simpa [VerifySubPre, vs_params] using hpre
  have hκw := winTab_kappa hκ L hwin
  have hbl' : bytecode.length = 2 ^ 23 := hbl
  rw [show Fn.body fn% «verify_sub» = vsT from vs_body] at hb
  obtain ⟨⟨F⟩, hb⟩ := vs_front hκ L hLe hbl' hexp hwin hb
  simp only [vsBackT, holdsList_append] at hb
  have hHL := tableHeights_length F.rowsN F.hrowsL
  -- the tables' context
  have hctx := F.hctx
  obtain ⟨chis, hbpR, hgmu, hchi, -, -, -, hcol, hpts⟩ := hctx
  have hpts' : ∀ j (p : List E), (F.claims.map (·.point))[j]? = some p →
      (j < Tables.nPooled → p.length = Tables.claimLowDim F.logMem (Tables.tableHeightsOf F.rowsN) j) ∧
      (Tables.nBusClaims ≤ j → j < Tables.nPooled → p = chis.take p.length) :=
    fun j p hp ↦ ⟨(hpts j p hp).1, (hpts j p hp).2.2.1⟩
  obtain ⟨hlcol, hlpt, hhead, hl25, hlR⟩ := lanes_facts F.hcl hcol hpts' F.hcew
  -- `((Tables.tableHeightsOf F.rowsN).getD 5 0) ≤ |chis|`, from the first output lane's claim
  have hτc : ((Tables.tableHeightsOf F.rowsN).getD 5 0) ≤ chis.length := by
    have h105 : 105 < (F.claims.map (·.point)).length := by simp [F.hcl]
    obtain ⟨hl, -, ht, -⟩ := hpts 105 _ (List.getElem?_eq_getElem h105)
    have hsrc : Tables.claimKappaSrc.getD 105 0 = 7 := by decide +kernel
    have hcd : Tables.claimLowDim (Tables.layoutOf bytecode F.logMem F.rowsN).logMemory
        (Tables.layoutOf bytecode F.logMem F.rowsN).tableLogHeights 105 = ((Tables.tableHeightsOf F.rowsN).getD 5 0) := by
      rw [layoutOf_heights]
      unfold Tables.claimLowDim
      rw [hsrc]
      simp [Tables.claimKappaAdj]
    have e1 := hl (by decide)
    have e2 := congrArg List.length (ht (by decide) (by decide))
    rw [hcd] at e1
    rw [List.length_take] at e2
    omega
  -- `verify_keccak`
  have hK := verify_keccak_holds hκ hκw L (grind_check_holds 3 (by decide)) _ _ (hLe _ _ _ F.hkc)
  have hτ9 := tau_ge F.hrowsL
  have hτ28 : (Tables.tableHeightsOf F.rowsN).getD 5 0 ≤ 28 := by
    have := tau_le_of_kappasBelow (tableHeights_length _ F.hrowsL) F.hKB
    omega
  obtain ⟨xsK, op, point, slices, word, s', hxsK, hrunK, hpend, hzv, hpt, hslR, hopL, hptL, hslL,
      hretK⟩ :=
    hK (by rw [F.h589]; exact winTabs_of hwin) ((Tables.tableHeightsOf F.rowsN).getD 5 0) chis _ hτ9 (by omega) F.h583 hτc hchi hl25
      (by rw [F.h587]; exact hlR)
  obtain ⟨hcapK, hK2⟩ := List.append_inj' (show [σ (.n 590), σ (.n 591), σ (.n 592), σ (.n 593),
    σ (.n 594)] ++ [σ (.n 595), σ (.n 596)] = _ from hretK) rfl
  simp only [List.cons.injEq, and_true] at hK2
  obtain ⟨e595, e596⟩ := hK2
  -- `keccakPhaseClaims`
  have h6 : RunsTo (keccakPhaseClaims (Tables.layoutOf bytecode F.logMem F.rowsN) F.claims)
      ⟨[σ (.n 573), σ (.n 574), σ (.n 575), σ (.n 576), σ (.n 577)], []⟩ xsK
      (F.claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++ [⟨qkeccak, op, word⟩],
        point, slices) s' := by
    have hτL : (Tables.layoutOf bytecode F.logMem F.rowsN).tableLogHeights.getD opKeccak 0 = ((Tables.tableHeightsOf F.rowsN).getD 5 0) := by
      rw [layoutOf_heights]; rfl
    exact keccakPhase_runs hτL hlcol hlpt hhead hrunK
  -- the ring map
  obtain ⟨chs, hchL, hchV, h847, h602, hRS, hb⟩ :=
    vsMapsT_holds hκ hκw L hLe hwin F.h8 F.h9 F.h10 F.h11 (s := s') (by rw [hpend]; rfl) hcapK hb
  obtain ⟨hct, hrst, hb⟩ := vsCtabT_holds hchL hchV hb
  obtain ⟨sl', ch', hsl'L, hch'L, hsl'R, hch'R, hrt⟩ := ring_switch_target_holds L.read _ _ (hLe _ _ _ hrst)
  have esl : sl' = slices := readsAt_ext (by rw [hsl'L, hslL]; rfl) hsl'R hslR
  have ech : ch' = chs := readsAt_ext (by rw [hch'L, hchL]; rfl) hch'R h847
  rw [esl, ech] at hrt
  simp only [List.cons.injEq, and_true] at hrt
  have hcoL : (ringCoefficients (chs.take ringMapWidth) (chs.drop ringMapWidth)).length = kBits := by
    rw [ringCoefficients_eq (by simp [hchL, ringMapWidth])]
    simp [List.length_flatMap, hchL, ringMapWidth, kBits]
  -- the batching
  obtain ⟨hlam, htarget, hb⟩ := vsLamT_holds F.h8 F.h9 F.h10 F.h11 F.hcl hcol F.hpool F.hcew F.hpiv F.hv hb
  -- the tail
  obtain ⟨hrets, h1928, h1930, hopen, hterm, hd1, hd2, hd3⟩ :=
    vsTailT_holds F.hst20 F.hst30 F.h278 hb
  -- the opening
  have hroot : (σ (.n 268), σ (.n 271)) = digestHalves (digestFromHalves (σ (.n 268), σ (.n 271))) :=
    (digestScalars_digestOfScalars _).symm
  obtain ⟨w, s'', roots', hxsW, hW, hwL, pt, pt1, hretW, hptR, hpt1R⟩ :=
    vs_dispatch hos hκ hκw L hU hLe F.hst20 F.hst30 F.hl1 F.hl4
      (by rw [F.h66, Whir.rateSel, gen_pow_eq_ofK]) hroot
      (by rw [h1930]; exact winTabs_of hwin) hopen
  simp only [vsOsRets, List.cons.injEq, and_true] at hretW
  obtain ⟨e1931, e1932, e1933, e1934, e1935⟩ := hretW
  -- the terminal
  obtain ⟨-, hTacc⟩ := check_opening_terminal_holds Tables.column_selector_holds
    Tables.selector_tables_holds hκ L _ _ (hLe _ _ _ hterm)
  have hbusL : F.bus.point.length = busDepth (Tables.layoutOf bytecode F.logMem F.rowsN) := by
    have := hgmu.symm.trans F.h253
    exact gen_pow_inj (by have := mem_size_le hκ L hbpR; omega) (by have := F.hdep34; omega) this
  have hacc := hTacc (Tables.layoutOf bytecode F.logMem F.rowsN) F.bus F.claims ⟨qkeccak, op, word⟩ (σ (.n 1375)) point
    (ringCoefficients (chs.take ringMapWidth) (chs.drop ringMapWidth)) F.z w.point (by
      refine ⟨termCtx_of_tctx F.hctx, F.hP, F.hKB, layoutOf_placements hbl' _ _,
        layoutOf_stackLog hbl' _ _, F.hst30, F.hm1,
        by have := F.hm30; have e : (Tables.layoutOf bytecode F.logMem F.rowsN).logMemory = F.logMem := rfl
           omega,
        by rw [hbusL]; have := F.hdep34; omega, hHL, fun x hx ↦ by have := F.hh31 x hx; omega, F.h72, F.h583, F.hkb, gTabs_of_exp hexp, rfl,
        rfl, hopL, hzv, hptL, hpt, hcoL, hct, hwL, ?_, ?_, F.hzL, F.hz,
        F.h276⟩
      · rw [e1932, padPoint, hwL]; exact hptR
      · rw [e1933, padPoint, hwL, List.map_append, List.map_replicate, add_zero]; exact hpt1R)
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hacc
  -- the stacked opening's claims
  set kc1 := F.claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++ [⟨qkeccak, op, word⟩]
    with hkc1
  set rs : E × (List E → E) := (ringTarget slices (chs.take ringMapWidth) (chs.drop ringMapWidth),
    fun r ↦ ringWeight point r (ringCoefficients (chs.take ringMapWidth) (chs.drop ringMapWidth)))
    with hrs
  set ood : StackClaim := (fun x ↦ eqEval F.z x, F.v) with hood
  have hcl8 : (stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) kc1 rs.1 rs.2 ood).length = 137 := by
    have := filter_lanes_length hcol
    simp only [decide_not] at this
    rw [hkc1]
    simp [stackClaims, this]
  have hW' : Whir.RunsWith (Whir.whirOpen (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog F.lir (dot (powers (σ (.n 1375))
      (stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) kc1 rs.1 rs.2 ood).length) ((stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) kc1 rs.1 rs.2 ood).map (·.2))))
      ⟨[σ (.n 1370), σ (.n 1371), σ (.n 1372), σ (.n 1373), σ (.n 1374)], []⟩
      (vsOsW L.read V ((Tables.layoutOf bytecode F.logMem F.rowsN).stackLog - Whir.minOpenLog) F.lir (vsOsArgs σ) (vsOsRets σ)).1
      (vsOsW L.read V ((Tables.layoutOf bytecode F.logMem F.rowsN).stackLog - Whir.minOpenLog) F.lir (vsOsArgs σ) (vsOsRets σ)).2
      [(digestFromHalves (σ (.n 268), σ (.n 271)), Whir.stackShape (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog F.lir)] w s''
      roots' := by
    have hvals : (stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) kc1 rs.1 rs.2 ood).map
        (·.2) = σ (.n 1361) :: ((F.claims.filter (fun c ↦ c.column ∉ keccakOutputColumns)).map
          (·.value) ++ [σ (.n 596), F.v]) := by
      rw [hkc1, hrs, hood, hrt, e596]
      simp only [stackClaims, ringSwitchClaim, ColumnClaim.stackClaim, List.map_cons,
        List.map_append, List.map_map, Function.comp_def, List.map_nil, List.cons_append,
        List.append_assoc, List.nil_append]
    have ht : dot (powers (σ (.n 1375)) (stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN)
        kc1 rs.1 rs.2 ood).length) ((stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) kc1
        rs.1 rs.2 ood).map (·.2)) = σ (.n 1917) := by
      rw [hvals, hcl8, htarget]
    rw [ht]; exact hW
  have hAcc : w.Accepts fun x ↦ dot (powers (σ (.n 1375)) (stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) kc1 rs.1 rs.2 ood).length)
      ((stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) kc1 rs.1 rs.2 ood).map fun c ↦ c.1 x) := by
    unfold Whir.WhirEnd.Accepts
    have e : (fun x ↦ dot (powers (σ (.n 1375)) (stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) kc1 rs.1 rs.2 ood).length)
        ((stackClaims (Tables.layoutOf bytecode F.logMem F.rowsN) kc1 rs.1 rs.2 ood).map fun c ↦ c.1 x)) =
        stackWeight (Tables.layoutOf bytecode F.logMem F.rowsN) (openedClaims F.claims [⟨qkeccak, op, word⟩]) point
          (ringCoefficients (chs.take ringMapWidth) (chs.drop ringMapWidth)) F.z (σ (.n 1375)) := by
      funext x
      simp [stackWeight, stackClaims, openedClaims, kc1, rs, ood, ringSwitchClaim]
    rw [e, ← e1934, ← e1935, ← e1931]
    exact hacc
  have h8 := runsWith_stacked (m := (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog) (lir := F.lir) (by omega) hlam hW' hAcc
  -- the runs
  obtain ⟨level, rest, hcfg⟩ := cfg_cons F.hst20 F.hst30 F.hl1 F.hl4
  have h1 := readSizes_runsTo hbl' F.hm1 F.hm30 F.hrowsL F.hh31 F.hl1 F.hl4 F.hst30
    (⟨[σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)], []⟩ : Fs)
  rw [← F.hwords, F.habs1] at h1
  have hacc' := deferred_accepts (c := ⟨F.bus.bytecodePoint, σ (.n 580)⟩)
    (s0 := ⟨[σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)], []⟩) ⟨F.hcap0.symm, rfl, rfl⟩
    h1 hcfg (σ (.n 268)) (σ (.n 271)) (by rw [F.habs2]; exact F.hO) (by have := F.hdep34; omega)
    F.hB F.hG F.hT h6 (hRS point slices) h8
  -- the decoded proof
  have hcand : (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog - Whir.minOpenLog < 11 := by
    have := F.hst30; have : Whir.minOpenLog = 20 := rfl; omega
  have hidx : dispatchIdx (σ (.n 278)) = (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog - Whir.minOpenLog :=
    dispatchIdx_eq hcand (by rw [F.h278, gen_pow_eq_ofK])
  -- the stream before the opening
  have e320 : σ (.n 320) = σ (.n 25) * gen ^ 13 := by rw [F.h320, F.h312]; ring
  have e567 : σ (.n 567) = σ (.n 25) * gen ^ (13 + F.xsG.length) := by rw [F.h567, e320]; ring
  have e578 : σ (.n 578) = σ (.n 25) * gen ^ (13 + F.xsG.length + F.xsT.length) := by
    rw [F.h578, e567]; ring
  have e595' : σ (.n 595) = σ (.n 25) * gen ^ (13 + F.xsG.length + F.xsT.length + xsK.length) := by
    rw [e595, e578]; ring
  have r11 : ReadsAt L.read (σ (.n 25)) (vsWords σ ++ [σ (.n 268), σ (.n 271)] ++ [σ (.n 283)]) := by
    intro k hk
    simp only [vsWords, List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact (F.hw 0 (by decide)).1
    · exact (F.hw 1 (by decide)).1
    · exact (F.hw 2 (by decide)).1
    · exact (F.hw 3 (by decide)).1
    · exact (F.hw 4 (by decide)).1
    · exact (F.hw 5 (by decide)).1
    · exact (F.hw 6 (by decide)).1
    · exact (F.hw 7 (by decide)).1
    · exact F.w268.1
    · exact F.w271.1
    · exact F.hn283
  have r13 : ReadsAt L.read (σ (.n 25))
      (vsWords σ ++ [σ (.n 268), σ (.n 271)] ++ [σ (.n 283)] ++ [F.v, F.nn]) := by
    refine readsAt_append.2 ⟨r11, fun k hk ↦ ?_⟩
    rw [show (vsWords σ ++ [σ (.n 268), σ (.n 271)] ++ [σ (.n 283)]).length = 11 from rfl,
      ← F.h312]
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact F.hv312
    · exact F.hnn
  have rG := readsAt_append.2 ⟨r13, by
    rw [show (vsWords σ ++ [σ (.n 268), σ (.n 271)] ++ [σ (.n 283)] ++ [F.v, F.nn]).length = 13
      from rfl, ← e320]; exact F.hxsG⟩
  have rT := readsAt_append.2 ⟨rG, by
    rw [List.length_append, show (vsWords σ ++ [σ (.n 268), σ (.n 271)] ++ [σ (.n 283)] ++
      [F.v, F.nn]).length = 13 from rfl, ← e567]; exact F.hxsT⟩
  have rK := readsAt_append.2 ⟨rT, by
    rw [List.length_append, List.length_append, show (vsWords σ ++ [σ (.n 268), σ (.n 271)] ++
      [σ (.n 283)] ++ [F.v, F.nn]).length = 13 from rfl, ← e578]; exact hxsK⟩
  have rR := (readsAt_append (ys := [σ (.n 602)])).2 ⟨rK, by
    rw [List.length_append, List.length_append, List.length_append, show (vsWords σ ++
      [σ (.n 268), σ (.n 271)] ++ [σ (.n 283)] ++ [F.v, F.nn]).length = 13 from rfl, ← e595']
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    exact h602⟩
  have hstream := readsAt_cursor (q := σ (.n 1919)) hκ L rR (by
    rw [h1928, e595']
    simp only [List.length_append, List.length_cons, List.length_nil,
      show (vsWords σ).length = 8 from rfl]
    ring_nf) (by simp)
  -- the deferred claim
  have hdep := F.hdep19
  have hrL := F.hrL
  have htake : (F.r.2.1.take 19).length = 19 := by rw [List.length_take]; omega
  have hcells : ReadsAt L.read (σ (.n 5))
      (Node.DeferredClaim.cells (⟨F.bus.bytecodePoint, σ (.n 580)⟩ : BytecodeClaim)) := by
    show ReadsAt L.read (σ (.n 5)) (F.bus.bytecodePoint ++ [σ (.n 580)])
    rw [F.hbp]
    refine readsAt_append.2 ⟨readsAt_append.2 ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩, fun k hk ↦ ?_⟩
    · rw [htake] at hk
      obtain ⟨w', h254, h5⟩ := hd1 k hk
      rw [List.getElem_take]
      rwa [loadHolds_unique h254 (F.hzeta k (by omega))] at h5
    · rw [htake, loadHolds_mul_gen_pow]
      have hk4 : k < 4 := by rw [F.hslL] at hk; exact hk
      obtain ⟨w', h570, h5⟩ := hd2 k hk4
      rwa [loadHolds_unique h570 (F.hsl k hk)] at h5
    · simp only [List.length_cons, List.length_nil] at hk
      obtain rfl : k = 0 := by omega
      rw [List.length_append, htake, F.hslL, loadHolds_mul_gen_pow]
      exact hd3
  -- the statement
  refine ⟨hrets, σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), rfl, F.seed, F.pi,
    ⟨F.bus.bytecodePoint, σ (.n 580)⟩, F.hseed, F.hpi, ?_, hcells, ?_⟩
  · show (F.bus.bytecodePoint).length = 23
    rw [F.hbp, List.length_append, htake, F.hslL]; rfl
  · have hπ : vsPiOf L.read σ V = ⟨vsWords σ ++ [σ (.n 268), σ (.n 271)] ++ [σ (.n 283), F.v] ++
        [F.nn] ++ F.xsG ++ F.xsT ++ xsK ++ [σ (.n 602)] ++
        (vsOsW L.read V ((Tables.layoutOf bytecode F.logMem F.rowsN).stackLog - Whir.minOpenLog) F.lir (vsOsArgs σ) (vsOsRets σ)).1,
        (vsOsW L.read V ((Tables.layoutOf bytecode F.logMem F.rowsN).stackLog - Whir.minOpenLog) F.lir (vsOsArgs σ) (vsOsRets σ)).2⟩ := by
      have hrate : rateOf (σ (.n 66)) = F.lir := by
        rw [show σ (.n 66) = Whir.rateSel F.lir by rw [F.h66, Whir.rateSel, gen_pow_eq_ofK],
          rateOf_eq F.hl1 F.hl4]
      simp only [vsPiOf, piOfW, hidx, hrate, hstream, List.append_assoc, List.cons_append,
        List.nil_append]
    rw [hπ]
    exact hacc'

end
end LeanVM.Guest.B1.VerifySub
