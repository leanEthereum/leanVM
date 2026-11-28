/-
  LeanVM.Guest.B1.VsC.VsHonEcPf

  `verify_sub`'s pinned ends at the honest context: each chosen call exists, so the honest context has every
  pinned call and the steps.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonEc
public import LeanVM.Guest.B1.VsC.VsHonCalls
public import LeanVM.Guest.B1.VsC.VsOrcPh35

/-!
# The pinned ends, chosen: their calls

Each `VsCtx.ec*` is `Classical.epsilon` of its call at native closed forms with its end bound; the callee's bounded
completeness (`VsCalleesEndU`, `VsCalleesEndU.row_sideE`, `openCallEnd_nat`) gives one, so the choice satisfies it
(`ec4_spec` … `osPick_spec`). **`VsCtx.ecPart`** (`open_stacked`'s bounded completeness `hO` a hypothesis, `openStackedEndA_17` at `alW`, whose module cannot be imported beside `VsOrcMem`): at the honest context `{ x with ec := x.ecOf …, ret := R bp bp1 }`
with `bp := x.bpOf …`, `bp1 := x.bp1Of …`, `EcIn` at every `ec`, `bp`, `bp1` gives `EcFacts`: the calls at the
guest's values (the closed forms rewritten by `EcIn`'s equalities), `ec 12`, the steps.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link LeanVM.Guest.B1.Stack
open LeanVM.Guest.B1.Link
open LeanVM.Prover.Exec (allocBase)
open LeanVM.Guest.B1.VerifySub (keccakTauMin keccakTauMax qkeccakVarsCap)

@[expose] public section

attribute [local semireducible] VsCtx.lay

theorem ecC_le {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {args rets : List E} {R D : ℕ → Prop} {Out Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B fp c e : ℕ}
    (h : CallAtA fs al cert k f args rets R D Out Pre Post B fp c e) : c ≤ e := by
  obtain ⟨_, _, h, _⟩ := h
  exact h

namespace VsCtx

variable {x : VsCtx} {N : NatOpen} {op point : List E} {kw : E}

/-! ## The context's numbers -/

theorem ecSum : (vsAllocSz x.p).sum = 982 + 256 * x.p := vsAllocSz_sum x.p
theorem ecB4 : x.base 4 = x.cur + 190 := base_c 4 190 (by norm_num) (by decide)
theorem ecB6 : x.base 6 = x.cur + 373 := base_c 6 373 (by norm_num) (by decide)
theorem ecB9 : x.base 9 = x.cur + 458 := base_c 9 458 (by norm_num) (by decide)
theorem ecB10 : x.base 10 = x.cur + 482 := base_c 10 482 (by norm_num) (by decide)
theorem ecB13 : x.base 13 = x.cur + 639 := base_c 13 639 (by norm_num) (by decide)
theorem ecB14 : x.base 14 = x.cur + 651 := base_c 14 651 (by norm_num) (by decide)
theorem ecB15 : x.base 15 = x.cur + 729 := base_c 15 729 (by norm_num) (by decide)
theorem ecB18 : x.base 18 = x.cur + 824 := base_c 18 824 (by norm_num) (by decide)

/-- The window tables lie below the cursor. -/
theorem ecTabs (hok : x.Ok) : x.qt + 178 + 2 ^ winTabBits ≤ x.cur := by
  have h1 := hok.ht
  have h2 := hok.hfc
  have e : expTabLen = 2226 := expTabLen_eq
  have e2 : 2 ^ winTabBits = 2048 := rfl
  omega

theorem ecHU : VsCalleesEndU B2C.fs x.al B2C.cert 17 := vsCalleesEndU_b2c (by norm_num)

/-- The tabs pointer. -/
theorem ecTabsPtr (qt : ℕ) : ptrAt qt * word 365917469723852800 0 = ptrAt (qt + 178) := tabs_ptr qt

theorem ecPtr_ne (q : ℕ) : ptrAt q ≠ 0 := by
  rw [ptrAt_eq_pow]; exact pow_ne_zero _ Value.gen_ne_zero

/-- The native layout facts at the context. -/
theorem ecLay (hok : x.Ok) (hN : N.Ok x.seed x.c) :
    x.lay = N.layout ∧ x.nF = natF3 x.seed x.c N.layout.stackLog ∧ 19 ≤ x.wdS ∧ x.wdS ≤ 24 ∧ x.nS ≤ 24 ∧
      N.L.chunks.width = x.wdS ∧ linkRows x.lay = x.nS ∧ linkQVars x.lay = 6 := by
  have hlay : x.lay = N.layout := VsCtx.lay_nat hN
  obtain ⟨layout, r, hann, -, hF⟩ := frontNum_of_child hok.child
  have hl2 : x.lay = layout := VsCtx.lay_of hann
  have htab : x.lay.tables = tables := by rw [hl2]; exact announced_tables hann
  have hw19 : 19 ≤ x.wdS := by rw [VsCtx.wdS, hl2]; exact hF.hw19
  have hw24 : x.wdS ≤ 24 := by rw [VsCtx.wdS, hl2]; exact hF.hw24
  have hn24 : x.nS ≤ 24 := by
    rw [VsCtx.nS, hl2]; obtain ⟨t, ht, e⟩ := hF.hn; rw [← e]; exact hF.h24 t ht
  have hch := hN.hL.chunks
  rw [← hlay] at hch
  refine ⟨hlay, VsCtx.nF_nat hN, hw19, hw24, hn24, ?_, rfl, VerifySub.linkQVars_tables htab⟩
  rw [VerifySub.chunks_width hch]; rfl

/-! ## Each choice's call -/

theorem ec4_spec (hok : x.Ok) :
    CsCall B2C.fs x.al B2C.cert 17 x.lay x.qt (x.base 20) x.fpc x.ec4 ∧
      x.ec4 ≤ x.fpc + B2C.fs "certify_stack" + 2 ^ 20 :=
  Classical.epsilon_spec (cs_of ecHU hok)

theorem ec4_ge (hok : x.Ok) : x.cur + (vsAllocSz x.p).sum ≤ x.ec4 := by
  have h := ec4_spec hok
  unfold CsCall at h
  have := ecC_le h.1
  have := x.le_fpc
  omega

theorem fpspOf_ge (e : ℕ) : e ≤ x.fpspOf e :=
  le_trans (le_trans le_leafEnd le_leafEnd) (le_allocBase _ _)

/-- `squeeze_packed`'s call at any frame past the buffers, on any capacity. -/
theorem sp_ex (hok : x.Ok) (f0 f1 f2 f3 f4 : E) {fp : ℕ} (hfp : x.cur + (vsAllocSz x.p).sum ≤ fp) :
    ∃ e, SpCall B2C.fs x.al B2C.cert 17 f0 f1 f2 f3 f4 (ptrAt (x.base 4 + 1)) x.pk fp e ∧
      e ≤ fp + B2C.fs "squeeze_packed" + 2 ^ 21 := by
  obtain ⟨layout, r, hann, hS, hN⟩ := frontNum_of_child hok.child
  have hlay : x.lay = layout := VsCtx.lay_of hann
  have hn24 : hMax x.lay ≤ 24 := by
    rw [hlay]; obtain ⟨t, ht, e⟩ := hN.hn; rw [← e]; exact hN.h24 t ht
  have hw19 : 19 ≤ widthOf x.lay := by rw [hlay]; exact hN.hw19
  have hw24 : widthOf x.lay ≤ 24 := by rw [hlay]; exact hN.hw24
  obtain ⟨hp64, -⟩ := vsPk hn24 hw19 hw24
  have hpk19 : 8 * x.pk ≤ 152 := by
    have := chal_fits hn24 hw19 hw24
    have h153 : guest_const% LINK_CHAL_CAP = 153 := rfl
    rw [h153] at this
    unfold VsCtx.pk; omega
  have hsum := x.ecSum
  have b4 := x.ecB4
  obtain ⟨e, hb, hc⟩ := ecHU.squeeze_packed f0 f1 f2 f3 f4 (ptrAt (x.base 4 + 1)) x.pk fp hp64 (by
      intro q hq t ht
      simp only [List.mem_singleton] at hq
      subst hq
      dsimp only at ht
      rw [Link.pkSqueeze_length] at ht
      exact ⟨x.base 4 + 1 + t, by omega, B1.Main.addr_ofK _ _⟩)
  exact ⟨e, hc, hb⟩

theorem ec6_spec (hok : x.Ok) :
    SpCall B2C.fs x.al B2C.cert 17 ((N.L.cap1 x.lay x.nF).getD 0 0) ((N.L.cap1 x.lay x.nF).getD 1 0)
      ((N.L.cap1 x.lay x.nF).getD 2 0) ((N.L.cap1 x.lay x.nF).getD 3 0) ((N.L.cap1 x.lay x.nF).getD 4 0)
      (ptrAt (x.base 4 + 1)) x.pk (x.fpspOf x.ec4) (x.ec6 N) ∧
    x.ec6 N ≤ x.fpspOf x.ec4 + B2C.fs "squeeze_packed" + 2 ^ 21 :=
  Classical.epsilon_spec (sp_ex hok _ _ _ _ _ (le_trans (ec4_ge hok) (fpspOf_ge (x := x) x.ec4)))

theorem ec6_ge (hok : x.Ok) : x.cur + (vsAllocSz x.p).sum ≤ x.ec6 N := by
  have h := (ec6_spec (N := N) hok).1
  unfold SpCall at h
  have := ecC_le h
  have := ec4_ge hok
  have := fpspOf_ge (x := x) x.ec4
  omega

/-- The stream's link words end at the packed message, inside buffer `18`. -/
theorem natBm_le (h : x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p) :
    x.natBm N.L + 144 ≤ x.cur + (vsAllocSz x.p).sum := by
  have := x.ecSum
  have := x.ecB18
  omega

theorem ec7_ex (hok : x.Ok) (hN : N.Ok x.seed x.c) (hc2 : (N.L.cap2 x.lay x.nF).length = 5)
    (hin : x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p) :
    ∃ e, LrCall B2C.fs x.al B2C.cert 17 ((N.L.cap2 x.lay x.nF).getD 0 0) ((N.L.cap2 x.lay x.nF).getD 1 0)
      ((N.L.cap2 x.lay x.nF).getD 2 0) ((N.L.cap2 x.lay x.nF).getD 3 0) ((N.L.cap2 x.lay x.nF).getD 4 0)
      (ptrAt x.sI) x.clI (ptrAt (x.base 6)) (ptrAt x.qt * word 365917469723852800 0) (x.natLI N.L) N.L.wsI.length
      (ph7Fp B2C.fs x.al x.wdS (x.ec6 N)) e ∧
    e ≤ ph7Fp B2C.fs x.al x.wdS (x.ec6 N) + B2C.fs "link_rounds__L1_L0" + 2 ^ 21 := by
  obtain ⟨hlay, hnF, hw19, hw24, -, hwd, -, -⟩ := ecLay hok hN
  have hL := hN.hL
  rw [← hnF, ← hlay] at hL
  have hl5 := list5 hc2
  have hlen : (x.natLI N.L).length = x.wdS := by
    simp only [VsCtx.natLI, LinkNat.chainI, natChain_length, hwd]
  have hcur : (chainLast ⟨[(N.L.cap2 x.lay x.nF).getD 0 0, (N.L.cap2 x.lay x.nF).getD 1 0,
      (N.L.cap2 x.lay x.nF).getD 2 0, (N.L.cap2 x.lay x.nF).getD 3 0, (N.L.cap2 x.lay x.nF).getD 4 0],
      ptrAt x.sI, x.clI⟩ (x.natLI N.L)).cur = ptrAt x.sI * gen ^ N.L.wsI.length := by
    rw [← hl5, VsCtx.natLI, LinkNat.chainI, natChain_cur, ← hL.lenI]
  have hfp : x.ec6 N ≤ ph7Fp B2C.fs x.al x.wdS (x.ec6 N) := by
    unfold ph7Fp; exact le_trans le_leafEnd (le_allocBase _ _)
  have g6 := ec6_ge (N := N) hok
  have hsum := x.ecSum
  have b6 := x.ecB6
  have b18 := x.ecB18
  have ht := ecTabs hok
  have hbm : x.natBm N.L = x.sI + N.L.wsI.length + 1 + N.L.wsR.length + N.L.wsC.length := rfl
  have hsI : x.sI = x.base 18 + 13 := rfl
  have harr : lrArrays (ptrAt x.sI) (ptrAt (x.base 6)) (ptrAt x.qt * word 365917469723852800 0) N.L.wsI.length
      (x.natLI N.L).length = ([(x.sI, N.L.wsI.length), (x.base 6, x.wdS), (x.qt + 178, 2 ^ winTabBits)]).map
        fun q => (ptrAt q.1, q.2) := by
    rw [ecTabsPtr, hlen]; rfl
  obtain ⟨e, hb, hc⟩ := ecHU.rounds_L1_L0 _ _ _ _ _ (ptrAt x.sI) x.clI (ptrAt (x.base 6))
    (ptrAt x.qt * word 365917469723852800 0) (x.natLI N.L) N.L.wsI.length (ph7Fp B2C.fs x.al x.wdS (x.ec6 N))
    (by omega) (ecPtr_ne _) hcur (by
      rw [harr]
      refine ptrsBelow_idx fun q hq => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> dsimp only <;> omega)
  exact ⟨e, hc, hb⟩

theorem ec7_spec (hok : x.Ok) (hN : N.Ok x.seed x.c) (hc2 : (N.L.cap2 x.lay x.nF).length = 5)
    (hin : x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p) :
    LrCall B2C.fs x.al B2C.cert 17 ((N.L.cap2 x.lay x.nF).getD 0 0) ((N.L.cap2 x.lay x.nF).getD 1 0)
      ((N.L.cap2 x.lay x.nF).getD 2 0) ((N.L.cap2 x.lay x.nF).getD 3 0) ((N.L.cap2 x.lay x.nF).getD 4 0)
      (ptrAt x.sI) x.clI (ptrAt (x.base 6)) (ptrAt x.qt * word 365917469723852800 0) (x.natLI N.L) N.L.wsI.length
      (ph7Fp B2C.fs x.al x.wdS (x.ec6 N)) (x.ec7 N) ∧
    x.ec7 N ≤ ph7Fp B2C.fs x.al x.wdS (x.ec6 N) + B2C.fs "link_rounds__L1_L0" + 2 ^ 21 :=
  Classical.epsilon_spec (ec7_ex hok hN hc2 hin)

theorem ec7_ge (hok : x.Ok) (hN : N.Ok x.seed x.c) (hc2 : (N.L.cap2 x.lay x.nF).length = 5)
    (hin : x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p) :
    x.cur + (vsAllocSz x.p).sum ≤ x.ec7 N := by
  have h := (ec7_spec hok hN hc2 hin).1
  unfold LrCall at h
  have := ecC_le h
  have := ec6_ge (N := N) hok
  have : x.ec6 N ≤ ph7Fp B2C.fs x.al x.wdS (x.ec6 N) := by
    unfold ph7Fp; exact le_trans le_leafEnd (le_allocBase _ _)
  omega

theorem ec9_ex (hok : x.Ok) (hN : N.Ok x.seed x.c) (hc2 : (N.L.cap2 x.lay x.nF).length = 5)
    (hc4 : (N.L.cap4 x.lay x.nF).length = 5)
    (hin : x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p) :
    ∃ e, LrsCall B2C.fs x.al B2C.cert 17 (chunkCount x.wdS) ((N.L.cap4 x.lay x.nF).getD 0 0)
      ((N.L.cap4 x.lay x.nF).getD 1 0) ((N.L.cap4 x.lay x.nF).getD 2 0) ((N.L.cap4 x.lay x.nF).getD 3 0)
      ((N.L.cap4 x.lay x.nF).getD 4 0) (ptrAt (x.natB772 N.L + 1)) (chainLast ⟨[], 0, 0⟩ (x.natLI N.L)).cl
      (ptrAt (x.base 9)) (ptrAt (x.base 10)) (ptrAt x.qt * word 365917469723852800 0) (x.natLR N.L) (x.natLC N.L)
      N.L.wsR.length N.L.wsC.length
      (allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec7 N))) e ∧
    e ≤ allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec7 N)) +
      B2C.fs (lrsNames.getD (chunkCount x.wdS - 6) "") + 2 ^ 23 := by
  obtain ⟨hlay, hnF, hw19, hw24, hn24, hwd, hnS, hq6⟩ := ecLay hok hN
  have hL := hN.hL
  rw [← hnF, ← hlay] at hL
  obtain ⟨hntR, hntC, hgR, hgC⟩ := natLink_counts hL.chunks (by rw [show linkWidth x.lay = x.wdS from rfl]; exact hw19)
    (by rw [show linkWidth x.lay = x.wdS from rfl]; exact hw24) rfl
  rw [show linkWidth x.lay = x.wdS from rfl] at hntR hntC hgR hgC
  have hl5 := list5 hc4
  obtain ⟨hcc6, hcc9⟩ := chunkCount_bounds hw19 hw24
  have hR0 : linkRows x.lay ≠ 0 := by
    obtain ⟨layout, r, hann, -, hF⟩ := frontNum_of_child hok.child
    have hl2 : x.lay = layout := VsCtx.lay_of hann
    have h5 : 9 ≤ layout.tableLogHeights.getD 5 0 := hF.h9
    have h55 : layout.tableLogHeights.getD 5 0 ≤ hMax layout := hF.hht 5 (by norm_num)
    rw [hl2, ← hMax_eq_linkRows]; omega
  set st : RSt := ⟨[(N.L.cap4 x.lay x.nF).getD 0 0, (N.L.cap4 x.lay x.nF).getD 1 0, (N.L.cap4 x.lay x.nF).getD 2 0,
    (N.L.cap4 x.lay x.nF).getD 3 0, (N.L.cap4 x.lay x.nF).getD 4 0], ptrAt (x.natB772 N.L + 1),
    (chainLast ⟨[], 0, 0⟩ (x.natLI N.L)).cl⟩ with hst
  have hne2 : x.natLR N.L ≠ [] := natChain_ne hR0 _ _
  have hcR : (chainLast st (x.natLR N.L)).cur = ptrAt (x.natB772 N.L + 1) * gen ^ N.L.wsR.length := by
    rw [hst, ← hl5, VsCtx.natLR, LinkNat.chainR, natChain_cur, ← hL.lenR]
  have eR0 : chainLast ⟨[], 0, 0⟩ (x.natLR N.L) = chainLast st (x.natLR N.L) := chainLast_ne hne2 _ _
  have hne3 : x.natLC N.L ≠ [] := natChain_ne (by rw [hq6]; omega) _ _
  have hcC : (chainLast (chainLast st (x.natLR N.L)) (x.natLC N.L)).cur =
      (chainLast st (x.natLR N.L)).cur * gen ^ N.L.wsC.length := by
    rw [chainLast_ne hne3 _ ⟨(N.L.endR x.lay x.nF).cap, (chainLast ⟨[], 0, 0⟩ (x.natLR N.L)).cur,
      (chainLast ⟨[], 0, 0⟩ (x.natLR N.L)).cl⟩, VsCtx.natLC, LinkNat.chainC, natChain_cur, ← hL.lenC, eR0]
  have hlR : (x.natLR N.L).length = x.nS := by
    simp only [VsCtx.natLR, LinkNat.chainR, natChain_length, hnS]
  have hlC : (x.natLC N.L).length = 6 := by
    simp only [VsCtx.natLC, LinkNat.chainC, natChain_length, hq6]
  have g7 := ec7_ge hok hN hc2 hin
  have hfp : x.ec7 N ≤ allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec7 N)) := by
    unfold ph8End
    exact le_trans (le_trans (le_allocBase _ _) (Nat.le_add_right _ _))
      (le_trans (le_trans (le_allocBase _ _) (Nat.le_add_right _ _)) (le_allocBase _ _))
  have hsum := x.ecSum
  have b9 := x.ecB9
  have b10 := x.ecB10
  have b18 := x.ecB18
  have ht := ecTabs hok
  have hbm : x.natBm N.L = x.natB772 N.L + 1 + N.L.wsR.length + N.L.wsC.length := rfl
  have harr : lrsArrays (ptrAt (x.natB772 N.L + 1)) (chainLast st (x.natLR N.L)).cur (ptrAt (x.base 9))
      (ptrAt (x.base 10)) (ptrAt x.qt * word 365917469723852800 0) N.L.wsR.length N.L.wsC.length
      (x.natLR N.L).length = ([(x.natB772 N.L + 1, N.L.wsR.length), (x.natB772 N.L + 1 + N.L.wsR.length,
        N.L.wsC.length), (x.base 9, x.nS), (x.base 10, 6), (x.qt + 178, 2 ^ winTabBits)]).map
        fun q => (ptrAt q.1, q.2) := by
    rw [hcR, ecTabsPtr, hlR, ptrAt_add]; rfl
  obtain ⟨e, hb, hc⟩ := (ecHU (x := x)).row_sideE fs_lt16 (chunkCount x.wdS) hcc6 hcc9 _ _ _ _ _
    (ptrAt (x.natB772 N.L + 1)) (chainLast ⟨[], 0, 0⟩ (x.natLI N.L)).cl (ptrAt (x.base 9)) (ptrAt (x.base 10))
    (ptrAt x.qt * word 365917469723852800 0) (x.natLR N.L) (x.natLC N.L) N.L.wsR.length N.L.wsC.length
    (allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec7 N)))
    (by omega) hlC (ecPtr_ne _) hcR hcC (by
      rw [harr]
      refine ptrsBelow_idx fun q hq => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
  exact ⟨e, hc, hb⟩

theorem ec9_spec (hok : x.Ok) (hN : N.Ok x.seed x.c) (hc2 : (N.L.cap2 x.lay x.nF).length = 5)
    (hc4 : (N.L.cap4 x.lay x.nF).length = 5)
    (hin : x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p) :
    LrsCall B2C.fs x.al B2C.cert 17 (chunkCount x.wdS) ((N.L.cap4 x.lay x.nF).getD 0 0)
      ((N.L.cap4 x.lay x.nF).getD 1 0) ((N.L.cap4 x.lay x.nF).getD 2 0) ((N.L.cap4 x.lay x.nF).getD 3 0)
      ((N.L.cap4 x.lay x.nF).getD 4 0) (ptrAt (x.natB772 N.L + 1)) (chainLast ⟨[], 0, 0⟩ (x.natLI N.L)).cl
      (ptrAt (x.base 9)) (ptrAt (x.base 10)) (ptrAt x.qt * word 365917469723852800 0) (x.natLR N.L) (x.natLC N.L)
      N.L.wsR.length N.L.wsC.length
      (allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec7 N))) (x.ec9 N) ∧
    x.ec9 N ≤ allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec7 N)) +
      B2C.fs (lrsNames.getD (chunkCount x.wdS - 6) "") + 2 ^ 23 :=
  Classical.epsilon_spec (ec9_ex hok hN hc2 hc4 hin)

theorem ec9_ge (hok : x.Ok) (hN : N.Ok x.seed x.c) (hc2 : (N.L.cap2 x.lay x.nF).length = 5)
    (hc4 : (N.L.cap4 x.lay x.nF).length = 5)
    (hin : x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p) :
    x.cur + (vsAllocSz x.p).sum ≤ x.ec9 N := by
  have h := (ec9_spec hok hN hc2 hc4 hin).1
  unfold LrsCall at h
  have := ecC_le h
  have := ec7_ge hok hN hc2 hin
  have : x.ec7 N ≤ allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec7 N)) := by
    unfold ph8End
    exact le_trans (le_trans (le_allocBase _ _) (Nat.le_add_right _ _))
      (le_trans (le_trans (le_allocBase _ _) (Nat.le_add_right _ _)) (le_allocBase _ _))
  omega

theorem fp13_ge : x.ec9 N ≤ x.fp13 N := by
  unfold fp13 ec12 ph11End
  exact le_trans (le_trans le_leafEnd (le_trans le_leafEnd le_leafEnd))
    (le_trans (tpKc_ge _ _ _ _ _) (le_allocBase _ _))

/-- The stream's words from `o`, `n` of them, have length `n` inside buffer `18`. -/
theorem ecSw_len (hbw : x.bw.map List.length = vsAllocSz x.p) {bm o n : ℕ} (h1 : x.base 18 ≤ bm)
    (h2 : bm + o + n ≤ x.base 18 + 256 * x.p) : (x.sw bm o n).length = n := by
  have hl : (x.bw.getD 18 []).length = 256 * x.p := VsCtx.lenbw hbw (j := 18) (by norm_num)
  simp only [sw, List.length_take, List.length_drop, hl]
  omega

theorem ec13_ex (hok : x.Ok) (hN : N.Ok x.seed x.c) (hc2 : (N.L.cap2 x.lay x.nF).length = 5)
    (hc4 : (N.L.cap4 x.lay x.nF).length = 5) (hbw : x.bw.map List.length = vsAllocSz x.p)
    (hbmIn : x.base 18 ≤ x.natBm N.L ∧ x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p)
    (hchw : N.L.chunks.width ≤ 24) (hchd : 89 + x.nS + x.wdS + N.L.chunks.d ≤ 153)
    (hsh : (natRow x N.L).shifts.length = 12)
    (hid : LtIdentity N.L.chunks (x.ltσN N) (N.L.endC x.lay x.nF).cl ((x.bw.getD 6 []).take N.L.chunks.width)
      (x.sw (x.natBm N.L) 80 64) (natRow x N.L).shifts
      (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take N.L.chunks.d)) :
    ∃ e, LtCall B2C.fs x.al B2C.cert 17 x.wdS (x.ltσN N) (N.L.endC x.lay x.nF).cl (x.base 6) (x.natBm N.L)
      (x.base 13) (x.base 4 + 89 + x.nS + x.wdS) ((x.bw.getD 6 []).take N.L.chunks.width)
      (x.sw (x.natBm N.L) 80 64) (natRow x N.L).shifts (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take N.L.chunks.d)
      (x.fp13 N) e ∧
    e ≤ x.fp13 N + B2C.fs (ltNames.getD (x.wdS - 19) "") + 2 ^ 21 := by
  obtain ⟨hlay, hnF, hw19, hw24, -, hwd, -, -⟩ := ecLay hok hN
  have hch : Chunks.new x.wdS = some N.L.chunks := by
    have h := hN.hL.chunks
    rwa [← hlay] at h
  have := hchw
  have l6 : (x.bw.getD 6 []).length = 24 := VsCtx.lenbw hbw (j := 6) (by norm_num)
  have l4 : (x.bw.getD 4 []).length = 153 := VsCtx.lenbw hbw (j := 4) (by norm_num)
  have g9 := ec9_ge hok hN hc2 hc4 hbmIn.2
  have g13 := fp13_ge (x := x) (N := N)
  have hsum := x.ecSum
  have b4 := x.ecB4
  have b6 := x.ecB6
  have b13 := x.ecB13
  have b18 := x.ecB18
  have hbm := hbmIn
  obtain ⟨e, hb, hc⟩ := ecHU.terminal x.wdS hw19 hw24 N.L.chunks hch (ptrAt (x.base 6)) (ptrAt (x.natBm N.L))
    (x.ltσN N (.n 2846)) (ptrAt (x.base 13)) (x.ltσN N (.n 2891)) (ptrAt (x.base 4 + 89 + x.nS + x.wdS))
    (x.ltσN N (.n 2890)) (N.L.endC x.lay x.nF).cl ((x.bw.getD 6 []).take N.L.chunks.width)
    (x.sw (x.natBm N.L) 80 64) (natRow x N.L).shifts (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take N.L.chunks.d)
    (x.fp13 N) (by simp only [List.length_take, l6]; omega) (ecSw_len hbw hbmIn.1 (by omega)) hsh
    (by simp only [List.length_take, List.length_drop, l4]; omega) hid (by
      rw [ltIdx_ptr]
      refine ptrsBelow_idx fun q hq => ?_
      simp only [ltIdx, List.mem_cons, List.not_mem_nil, or_false] at hq
      have hrs : ((x.bw.getD 6 []).take N.L.chunks.width).length ≤ 24 := by simp only [List.length_take, l6]; omega
      have hnu : (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take N.L.chunks.d).length ≤ N.L.chunks.d := by
        simp only [List.length_take]; omega
      rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
  exact ⟨e, hc, hb⟩

theorem ec13_spec (hok : x.Ok) (hN : N.Ok x.seed x.c) (hc2 : (N.L.cap2 x.lay x.nF).length = 5)
    (hc4 : (N.L.cap4 x.lay x.nF).length = 5) (hbw : x.bw.map List.length = vsAllocSz x.p)
    (hbmIn : x.base 18 ≤ x.natBm N.L ∧ x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p)
    (hchw : N.L.chunks.width ≤ 24) (hchd : 89 + x.nS + x.wdS + N.L.chunks.d ≤ 153)
    (hsh : (natRow x N.L).shifts.length = 12)
    (hid : LtIdentity N.L.chunks (x.ltσN N) (N.L.endC x.lay x.nF).cl ((x.bw.getD 6 []).take N.L.chunks.width)
      (x.sw (x.natBm N.L) 80 64) (natRow x N.L).shifts
      (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take N.L.chunks.d)) :
    LtCall B2C.fs x.al B2C.cert 17 x.wdS (x.ltσN N) (N.L.endC x.lay x.nF).cl (x.base 6) (x.natBm N.L)
      (x.base 13) (x.base 4 + 89 + x.nS + x.wdS) ((x.bw.getD 6 []).take N.L.chunks.width)
      (x.sw (x.natBm N.L) 80 64) (natRow x N.L).shifts (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take N.L.chunks.d)
      (x.fp13 N) (x.ec13 N) ∧
    x.ec13 N ≤ x.fp13 N + B2C.fs (ltNames.getD (x.wdS - 19) "") + 2 ^ 21 :=
  Classical.epsilon_spec (ec13_ex hok hN hc2 hc4 hbw hbmIn hchw hchd hsh hid)

theorem vkW_1076 (bm : ℕ) (pm : List E) : vkW bm pm 1076 = ptrAt bm := by simp [vkW]

theorem ec14_ex (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p)
    (hbmIn : x.base 18 ≤ x.natBm N.L ∧ x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p)
    (h13 : x.cur + (vsAllocSz x.p).sum ≤ x.ec13 N)
    (hτ0 : keccakTauMin ≤ x.hgS 5) (hτ1 : x.hgS 5 ≤ keccakTauMax)
    (hcar : ∃ sp, (⟨[(x.natPm N.L).getD 1 0, (x.natPm N.L).getD 2 0, (x.natPm N.L).getD 3 0,
      (x.natPm N.L).getD 4 0, (x.natPm N.L).getD 5 0], []⟩ : Fs).Carries sp)
    (hrun : RunsTo (verifyKeccak (x.hgS 5) ((x.bw.getD 9 []).take (x.hgS 5)) (x.sw (x.natBm N.L) 55 25))
      ⟨[(x.natPm N.L).getD 1 0, (x.natPm N.L).getD 2 0, (x.natPm N.L).getD 3 0, (x.natPm N.L).getD 4 0,
        (x.natPm N.L).getD 5 0], []⟩ (x.sw (x.natBm N.L) 144 N.xs.length)
      ([⟨qkeccak, op, kw⟩], point, (x.bw.getD 15 []).take 64) N.s')
    (hpend : N.s'.pend.length = rateScalars) (hopl : op.length ≤ qkeccakVarsCap)
    (hptl : qkeccakVarsCap + point.length ≤ (vsAllocSz x.p).getD 14 0) :
    ∃ e, VkCall B2C.fs x.al B2C.cert 17 (vkW (x.natBm N.L) (x.natPm N.L)) (x.base 9) (x.base 14) (x.base 15) x.qt
      (x.hgS 5) (x.bw.getD 9 []) (x.sw (x.natBm N.L) 55 25) (x.sw (x.natBm N.L) 144 N.xs.length) op point
      ((x.bw.getD 15 []).take 64) kw N.s' (allocBase (x.al "verify_keccak") (x.ec13 N)) e ∧
    e ≤ allocBase (x.al "verify_keccak") (x.ec13 N) + B2C.fs "verify_keccak" + 2 ^ 24 := by
  have l9 : (x.bw.getD 9 []).length = 24 := VsCtx.lenbw hbw (j := 9) (by norm_num)
  have l15 : (x.bw.getD 15 []).length = 64 := VsCtx.lenbw hbw (j := 15) (by norm_num)
  have h14 : (vsAllocSz x.p).getD 14 0 = 78 := rfl
  have hmax : keccakTauMax = 24 := rfl
  have hcap : qkeccakVarsCap = 39 := rfl
  have hsum := x.ecSum
  have b9 := x.ecB9
  have b14 := x.ecB14
  have b15 := x.ecB15
  have b18 := x.ecB18
  have ht := ecTabs hok
  have hbm := hbmIn
  have hfp := le_allocBase (x.al "verify_keccak") (x.ec13 N)
  have harr := vkIdx_ptr (x.natBm N.L) (x.base 9) (x.base 14) (x.base 15) x.qt (x.sw (x.natBm N.L) 144 N.xs.length)
    (x.bw.getD 9 []) op point
  rw [← vkW_1076 (x.natBm N.L) (x.natPm N.L)] at harr
  have hxs := ecSw_len hbw hbmIn.1 (o := 144) (n := N.xs.length) (by omega)
  obtain ⟨e, hb, hc⟩ := ecHU.verify_keccak (vkW (x.natBm N.L) (x.natPm N.L) 1288)
    (vkW (x.natBm N.L) (x.natPm N.L) 1289) (vkW (x.natBm N.L) (x.natPm N.L) 1290)
    (vkW (x.natBm N.L) (x.natPm N.L) 1291) (vkW (x.natBm N.L) (x.natPm N.L) 1292)
    (vkW (x.natBm N.L) (x.natPm N.L) 1076 * word 21299200 0) (ptrAt (x.base 9))
    (vkW (x.natBm N.L) (x.natPm N.L) 1076 * word 36028797018963968 0) (ptrAt (x.base 14)) (ptrAt (x.base 15))
    (ptrAt x.qt * word 365917469723852800 0) (x.hgS 5) (x.bw.getD 9 [])
    (x.sw (x.natBm N.L) 55 25) (x.sw (x.natBm N.L) 144 N.xs.length) op point ((x.bw.getD 15 []).take 64) kw N.s'
    (allocBase (x.al "verify_keccak") (x.ec13 N)) hτ0 hτ1 (by rw [l9]; omega)
    (ecSw_len hbw hbmIn.1 (by omega)) hcar hrun hpend (by simp only [List.length_take, l15]; omega) (by
      rw [harr]
      refine ptrsBelow_idx fun q hq => ?_
      simp only [vkIdx, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
  exact ⟨e, hc, hb⟩

theorem ec15_ex (h14 : x.cur + (vsAllocSz x.p).sum ≤ x.ec14 N op point kw)
    (hs64 : (rsW N.ks N.L.msg (ringRho N.S)).length = kBits)
    (hc16 : (ringF N.S ++ ringG N.S).length = 2 * ringMapWidth) :
    ∃ e, RtCall B2C.fs x.al B2C.cert 17 x.a1 (rsW N.ks N.L.msg (ringRho N.S)) (ringF N.S ++ ringG N.S)
      (allocBase (x.al "ring_switch_target") (x.ec14 N op point kw)) e ∧
    e ≤ allocBase (x.al "ring_switch_target") (x.ec14 N op point kw) + B2C.fs "ring_switch_target" + 2 ^ 20 := by
  have hsum := x.ecSum
  have hfp := le_allocBase (x.al "ring_switch_target") (x.ec14 N op point kw)
  have hk : kBits = 64 := rfl
  have hr : ringMapWidth = 8 := rfl
  have ha1 : x.a1 = x.cur + (824 + 256 * x.p) + 14 := rfl
  obtain ⟨e, hb, hc⟩ := ecHU.ring_switch_target (ptrAt (x.a1 + 80)) (ptrAt x.a1) (rsW N.ks N.L.msg (ringRho N.S))
    (ringF N.S ++ ringG N.S) (allocBase (x.al "ring_switch_target") (x.ec14 N op point kw)) hs64 hc16 (by
      have e : [(ptrAt (x.a1 + 80), kBits), (ptrAt x.a1, 2 * ringMapWidth)] =
          ([(x.a1 + 80, kBits), (x.a1, 2 * ringMapWidth)]).map fun q => (ptrAt q.1, q.2) := rfl
      rw [e]
      refine ptrsBelow_idx fun q hq => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> dsimp only <;> omega)
  exact ⟨e, hc, hb⟩

theorem osPick_ex (hO : ∀ m, m ≤ 14 → OpenStackedEndA B2C.fs x.al B2C.cert 17 m) (hN : N.Ok x.seed x.c)
    (hbmIn : x.base 18 ≤ x.natBm N.L ∧ x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p)
    (kc : ℕ) : ∃ t : ℕ × ℕ × ℕ, x.OsBody N (x.natBm N.L) N.xs.length kc t.1 t.2.1 t.2.2 := by
  obtain ⟨bp, bp1, e, h⟩ := VsCtx.openCallEnd_nat (x := x) hO hN hbmIn.1 hbmIn.2 kc
  exact ⟨(bp, bp1, e), h⟩

theorem ec14_spec (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p)
    (hbmIn : x.base 18 ≤ x.natBm N.L ∧ x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p)
    (h13 : x.cur + (vsAllocSz x.p).sum ≤ x.ec13 N)
    (hτ0 : keccakTauMin ≤ x.hgS 5) (hτ1 : x.hgS 5 ≤ keccakTauMax)
    (hcar : ∃ sp, (⟨[(x.natPm N.L).getD 1 0, (x.natPm N.L).getD 2 0, (x.natPm N.L).getD 3 0,
      (x.natPm N.L).getD 4 0, (x.natPm N.L).getD 5 0], []⟩ : Fs).Carries sp)
    (hrun : RunsTo (verifyKeccak (x.hgS 5) ((x.bw.getD 9 []).take (x.hgS 5)) (x.sw (x.natBm N.L) 55 25))
      ⟨[(x.natPm N.L).getD 1 0, (x.natPm N.L).getD 2 0, (x.natPm N.L).getD 3 0, (x.natPm N.L).getD 4 0,
        (x.natPm N.L).getD 5 0], []⟩ (x.sw (x.natBm N.L) 144 N.xs.length)
      ([⟨qkeccak, op, kw⟩], point, (x.bw.getD 15 []).take 64) N.s')
    (hpend : N.s'.pend.length = rateScalars) (hopl : op.length ≤ qkeccakVarsCap)
    (hptl : qkeccakVarsCap + point.length ≤ (vsAllocSz x.p).getD 14 0) :
    VkCall B2C.fs x.al B2C.cert 17 (vkW (x.natBm N.L) (x.natPm N.L)) (x.base 9) (x.base 14) (x.base 15) x.qt
      (x.hgS 5) (x.bw.getD 9 []) (x.sw (x.natBm N.L) 55 25) (x.sw (x.natBm N.L) 144 N.xs.length) op point
      ((x.bw.getD 15 []).take 64) kw N.s' (allocBase (x.al "verify_keccak") (x.ec13 N)) (x.ec14 N op point kw) ∧
    x.ec14 N op point kw ≤ allocBase (x.al "verify_keccak") (x.ec13 N) + B2C.fs "verify_keccak" + 2 ^ 24 :=
  Classical.epsilon_spec (ec14_ex hok hbw hbmIn h13 hτ0 hτ1 hcar hrun hpend hopl hptl)

theorem ec15_spec (h14 : x.cur + (vsAllocSz x.p).sum ≤ x.ec14 N op point kw)
    (hs64 : (rsW N.ks N.L.msg (ringRho N.S)).length = kBits)
    (hc16 : (ringF N.S ++ ringG N.S).length = 2 * ringMapWidth) :
    RtCall B2C.fs x.al B2C.cert 17 x.a1 (rsW N.ks N.L.msg (ringRho N.S)) (ringF N.S ++ ringG N.S)
      (allocBase (x.al "ring_switch_target") (x.ec14 N op point kw)) (x.ec15 N op point kw) ∧
    x.ec15 N op point kw ≤
      allocBase (x.al "ring_switch_target") (x.ec14 N op point kw) + B2C.fs "ring_switch_target" + 2 ^ 20 :=
  Classical.epsilon_spec (ec15_ex h14 hs64 hc16)

theorem osPick_spec (hO : ∀ m, m ≤ 14 → OpenStackedEndA B2C.fs x.al B2C.cert 17 m) (hN : N.Ok x.seed x.c)
    (hbmIn : x.base 18 ≤ x.natBm N.L ∧ x.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.base 18 + 256 * x.p) :
    x.OsBody N (x.natBm N.L) N.xs.length (x.ec15 N op point kw) (x.osPick N op point kw).1
      (x.osPick N op point kw).2.1 (x.osPick N op point kw).2.2 :=
  Classical.epsilon_spec (osPick_ex hO hN hbmIn _)

end VsCtx

/-! ## The calls at the guest's values -/

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}

theorem ltCall_σ {wd : ℕ} {σ σ' : Val} {claim : E} {b12 b1076 b19 bnu : ℕ} {rs sl shs nus : List E} {fp e : ℕ}
    (h1 : σ (.n 2846) = σ' (.n 2846)) (h2 : σ (.n 2891) = σ' (.n 2891)) (h3 : σ (.n 2890) = σ' (.n 2890))
    (h : LtCall fs al cert k wd σ claim b12 b1076 b19 bnu rs sl shs nus fp e) :
    LtCall fs al cert k wd σ' claim b12 b1076 b19 bnu rs sl shs nus fp e := by
  unfold LtCall at h ⊢
  rw [← h1, ← h2, ← h3]
  exact h

theorem vkCall_w {w w' : ℕ → E} {b15 b20 b21 qt τ : ℕ} {chis outs xs op point slices : List E} {kw : E} {s' : Fs}
    {fp e : ℕ} (h6 : w 1076 = w' 1076) (h0 : w 1288 = w' 1288) (h1 : w 1289 = w' 1289) (h2 : w 1290 = w' 1290)
    (h3 : w 1291 = w' 1291) (h4 : w 1292 = w' 1292)
    (h : VkCall fs al cert k w b15 b20 b21 qt τ chis outs xs op point slices kw s' fp e) :
    VkCall fs al cert k w' b15 b20 b21 qt τ chis outs xs op point slices kw s' fp e := by
  unfold VkCall at h ⊢
  rw [← h6, ← h0, ← h1, ← h2, ← h3, ← h4]
  exact h

end

theorem getD5 {a b c d e : E} {l : List E} (h : [a, b, c, d, e] = l) :
    l.getD 0 0 = a ∧ l.getD 1 0 = b ∧ l.getD 2 0 = c ∧ l.getD 3 0 = d ∧ l.getD 4 0 = e := by
  subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem le21_22 {a e : ℕ} (h : e ≤ a + 2 ^ 21) : e ≤ a + 2 ^ 22 := by omega

/-! ## The honest context's pinned calls -/

namespace VsCtx

/-- **`verify_sub`'s pinned ends at the honest context**: with the ends `x.ecOf …` and the returns `R bp bp1` at
`open_stacked`'s chosen point buffers, every pinned call `HonParts` and `D3.Ok` take, and the steps, from `EcIn`
at every `ec`, `bp`, `bp1`. -/
theorem ecPart (x : VsCtx) (hO : ∀ m, m ≤ 14 → OpenStackedEndA B2C.fs x.al B2C.cert 17 m) (hok : x.Ok) {N : NatOpen} (hN : N.Ok x.seed x.c)
    (R : ℕ → ℕ → ℕ → (ℕ → E) → E) (op point : List E) (kw : E)
    (hin : ∀ ec bp bp1, EcIn { x with ec := ec, ret := R bp bp1 } N op point kw) :
    ∃ ec bp bp1, EcFacts { x with ec := ec, ret := R bp bp1 } N op point kw bp bp1 := by
  refine ⟨x.ecOf N op point kw, x.bpOf N op point kw, x.bp1Of N op point kw, ?_⟩
  have H := hin (x.ecOf N op point kw) (x.bpOf N op point kw) (x.bp1Of N op point kw)
  have zok : x.skel.Ok := ⟨hok.child, hok.ht, hok.ho, hok.hfc, hok.pre, hok.hcur⟩
  have zN : N.Ok x.skel.seed x.skel.c := hN
  have zO : ∀ m, m ≤ 14 → OpenStackedEndA B2C.fs x.skel.al B2C.cert 17 m := hO
  have hc2 : (N.L.cap2 x.skel.lay x.skel.nF).length = 5 := (congrArg List.length H.g1).symm
  have hc4 : (N.L.cap4 x.skel.lay x.skel.nF).length = 5 := (congrArg List.length H.g2).symm
  have hbw : x.skel.bw.map List.length = vsAllocSz x.skel.p := H.hbw
  have hbm : x.skel.base 18 ≤ x.skel.natBm N.L ∧
      x.skel.natBm N.L + 144 + N.xs.length + 1 + N.ws.length ≤ x.skel.base 18 + 256 * x.skel.p := H.hbmIn
  have hsh : (natRow x.skel N.L).shifts.length = 12 := by
    have h := congrArg List.length H.sec.shifts
    rw [List.length_map, VsCtx.cells19_length] at h
    exact h.symm
  have hid : LtIdentity N.L.chunks (x.skel.ltσN N) (N.L.endC x.skel.lay x.skel.nF).cl
      ((x.skel.bw.getD 6 []).take N.L.chunks.width) (x.skel.sw (x.skel.natBm N.L) 80 64) (natRow x.skel N.L).shifts
      (((x.skel.bw.getD 4 []).drop (89 + x.skel.nS + x.skel.wdS)).take N.L.chunks.d) := by
    have h := H.hid
    unfold LtIdentity at h ⊢
    rw [H.w1077, H.sec.coef, H.sec.certW, H.sec.rest, H.sec.shifts] at h
    exact h
  have p0 := H.hpm 0 (by norm_num)
  have p1 := H.hpm 1 (by norm_num)
  have p2 := H.hpm 2 (by norm_num)
  have p3 := H.hpm 3 (by norm_num)
  have p4 := H.hpm 4 (by norm_num)
  simp only [Nat.add_zero, Nat.reduceAdd] at p0 p1 p2 p3 p4
  have hcar := H.hcar
  have hrun := H.hrun
  rw [p0, p1, p2, p3, p4] at hcar hrun
  have s4 := ec4_spec zok
  have s6 := ec6_spec (N := N) zok
  have s7 := ec7_spec zok zN hc2 hbm.2
  have s9 := ec9_spec zok zN hc2 hc4 hbm.2
  have s13 := ec13_spec zok zN hc2 hc4 hbw hbm H.hchw H.hchd hsh hid
  have g13 : x.skel.cur + (vsAllocSz x.skel.p).sum ≤ x.skel.ec13 N := by
    have h := s13.1
    unfold LtCall at h
    have := ecC_le h
    have := ec9_ge zok zN hc2 hc4 hbm.2
    have := fp13_ge (x := x.skel) (N := N)
    omega
  have s14 := ec14_spec (op := op) (point := point) (kw := kw) zok hbw hbm g13 H.hτ0 H.hτ1 hcar hrun H.hpend
    H.hopl H.hptl
  have g14 : x.skel.cur + (vsAllocSz x.skel.p).sum ≤ x.skel.ec14 N op point kw := by
    have h := s14.1
    unfold VkCall at h
    have := ecC_le h
    have := le_allocBase (x.skel.al "verify_keccak") (x.skel.ec13 N)
    omega
  have s15 := ec15_spec g14 H.hs64 H.hc16
  have s16 := osPick_spec (op := op) (point := point) (kw := kw) zO zN hbm
  obtain ⟨k0, k1, k2, k3, k4⟩ := getD5 H.cap1
  obtain ⟨c0, c1, c2, c3, c4⟩ := getD5 H.g1
  obtain ⟨d0, d1, d2, d3, d4⟩ := getD5 H.g2
  set y : VsCtx := { x with ec := x.ecOf N op point kw, ret := R (x.bpOf N op point kw) (x.bp1Of N op point kw) }
    with hy
  have sp : SpCall B2C.fs y.al B2C.cert 17 ((N.L.cap1 y.lay y.nF).getD 0 0) ((N.L.cap1 y.lay y.nF).getD 1 0)
      ((N.L.cap1 y.lay y.nF).getD 2 0) ((N.L.cap1 y.lay y.nF).getD 3 0) ((N.L.cap1 y.lay y.nF).getD 4 0)
      (ptrAt (y.base 4 + 1)) y.pk y.fpsp (y.ec 6) := s6.1
  rw [k0, k1, k2, k3, k4] at sp
  have crd : LrCall B2C.fs y.al B2C.cert 17 ((N.L.cap2 y.lay y.nF).getD 0 0) ((N.L.cap2 y.lay y.nF).getD 1 0)
      ((N.L.cap2 y.lay y.nF).getD 2 0) ((N.L.cap2 y.lay y.nF).getD 3 0) ((N.L.cap2 y.lay y.nF).getD 4 0)
      (ptrAt y.sI) y.clI (ptrAt (y.base 6)) (ptrAt y.qt * word 365917469723852800 0) (y.natLI N.L) N.L.wsI.length
      (ph7Fp B2C.fs y.al y.wdS (y.ec 6)) (y.ec 7) := s7.1
  rw [c0, c1, c2, c3, c4, ← H.g3, ← H.gcl] at crd
  have crs : LrsCall B2C.fs y.al B2C.cert 17 (chunkCount y.wdS) ((N.L.cap4 y.lay y.nF).getD 0 0)
      ((N.L.cap4 y.lay y.nF).getD 1 0) ((N.L.cap4 y.lay y.nF).getD 2 0) ((N.L.cap4 y.lay y.nF).getD 3 0)
      ((N.L.cap4 y.lay y.nF).getD 4 0) (ptrAt (y.natB772 N.L + 1)) (chainLast ⟨[], 0, 0⟩ (y.natLI N.L)).cl
      (ptrAt (y.base 9)) (ptrAt (y.base 10)) (ptrAt y.qt * word 365917469723852800 0) (y.natLR N.L) (y.natLC N.L)
      N.L.wsR.length N.L.wsC.length
      (allocBase (y.al (lrsNames.getD (chunkCount y.wdS - 6) "")) (ph8End B2C.fs y.al y.wdS (y.ec 7))) (y.ec 9) := s9.1
  rw [d0, d1, d2, d3, d4, ← H.g773] at crs
  have lt : LtCall B2C.fs y.al B2C.cert 17 y.wdS (y.ltσN N) (N.L.endC y.lay y.nF).cl (y.base 6) (y.natBm N.L)
      (y.base 13) (y.base 4 + 89 + y.nS + y.wdS) ((y.bw.getD 6 []).take N.L.chunks.width)
      (y.sw (y.natBm N.L) 80 64) (natRow y N.L).shifts (((y.bw.getD 4 []).drop (89 + y.nS + y.wdS)).take N.L.chunks.d)
      (allocBase (y.al (ltNames.getD (y.wdS - 19) "")) (tpKc B2C.fs y.al y.hgS 5 (y.ec 12))) (y.ec 13) := s13.1
  rw [← H.w1077, ← H.sec.shifts] at lt
  have vk : VkCall B2C.fs y.al B2C.cert 17 (vkW (y.natBm N.L) (y.natPm N.L)) (y.base 9) (y.base 14) (y.base 15) y.qt
      (y.hgS 5) (y.bw.getD 9 []) (y.sw (y.natBm N.L) 55 25) (y.sw (y.natBm N.L) 144 N.xs.length) op point
      ((y.bw.getD 15 []).take 64) kw N.s' (allocBase (y.al "verify_keccak") (y.ec 13)) (y.ec 14) := s14.1
  obtain ⟨o1, o2, o3, o4⟩ := s16
  refine ⟨s4.1, sp, ⟨crd, crs⟩, rfl, ?_, ?_, s15.1, o1, o2, o3, ?_⟩
  · exact ltCall_σ H.sec.coef.symm H.sec.certW.symm H.sec.rest.symm lt
  · exact vkCall_w (by rw [vkW_1076, H.w1076]) p0.symm p1.symm p2.symm p3.symm p4.symm vk
  · exact ⟨s4.2, le21_22 s6.2, le21_22 s7.2, s9.2, rfl, le21_22 s13.2, s14.2, s15.2, o4⟩

end VsCtx

end
end LeanVM.Guest.B1.VsC
