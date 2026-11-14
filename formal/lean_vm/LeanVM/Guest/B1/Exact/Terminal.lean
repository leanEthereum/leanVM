/-
  LeanVM.Guest.B1.Exact.Terminal

  `check_opening_terminal` complete within its bound by a tree within its weights and exact at every node: its column
  selectors by `cs_completeAtDTBRE`, its other callees exact on every valid tree.
-/

module

public import LeanVM.Guest.B1.Terminal.TermWeight
public import LeanVM.Guest.B1.Exact.ColumnSelector
public import LeanVM.Guest.B1.Exact.RsEqRun
public import LeanVM.Guest.B1.VerifySub.CompleteBTE

/-!
# The terminal, every node exact

`termKids_completeBE`: `termKids_completeB` by trees exact on the memory (`termPsE`): the column selectors by
`cs_completeAtDTBRE`, the prefix chains, `check_opening_terminal_loop0`, `selector_tables` and `ring_switch_weight`
(`rsw_exactOk`) exact on every valid tree (`KidsDepB.toE`). `check_opening_terminal_completeAtBWE`:
`check_opening_terminal_completeAtBW` by a tree also exact (`completeAt_flatDepRBPR`, the terminal's own body without a
computed hint); `ChildSegs.term_kidBWE`: so on an honest child.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem eqc_exactFree : ExactFreeG "eq_prefix_chain" :=
  exactFreeG_of (j := idx% «eq_prefix_chain») (by decide +kernel)

theorem l15_exactFree : ExactFreeG name% «check_opening_terminal_loop0» :=
  exactFreeG_of (j := idx% «check_opening_terminal_loop0») (by decide +kernel)

theorem st_exactFree : ExactFreeG "selector_tables" :=
  exactFreeG_of (j := idx% «selector_tables») (by decide +kernel)

/-- The terminal's own computed hints are pinned by the next atom: it has none. -/
theorem term_pinned : Stmt.blockNextOk isComputed pinsInverse (fn% «check_opening_terminal»).body = true := by
  decide +kernel

/-- Every node of a tree exact on the memory. -/
def everyE : Reader → Tree → Prop := fun rd t => t.Every (ExactAt coreProgram rd)

/-- **The terminal's callees' predicates**: every tree exact on the memory. -/
def termPsE : List (Reader → Tree → Prop) :=
  (List.replicate 4 everyE ++ List.replicate Tables.nCommittedCols everyE) ++ List.replicate 3 everyE

theorem termPsE_every (rd : Reader) : ∀ P ∈ termPsE.map (· rd), ∀ t, P t → t.Every (ExactAt coreProgram rd) := by
  intro P hP t hPt
  simp only [termPsE, List.map_append, List.map_replicate, List.mem_append, List.mem_replicate] at hP
  rcases hP with (⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩ <;> exact hPt

theorem KidsDepB.split {κ : ℕ} : ∀ {ks ks' : List KidD} {Bs Bs' : List ℕ}, ks.length = Bs.length →
    KidsDepB fs cert κ (ks ++ ks') (Bs ++ Bs') → KidsDepB fs cert κ ks Bs ∧ KidsDepB fs cert κ ks' Bs'
  | [], _, [], _, _, h => ⟨trivial, h⟩
  | _ :: _, _, _ :: _, _, hl, ⟨h, hs⟩ =>
    let ⟨a, b⟩ := KidsDepB.split (by simpa using hl) hs
    ⟨⟨h, a⟩, b⟩
  | [], _, _ :: _, _, hl, _ => by simp at hl
  | _ :: _, _, [], _, hl, _ => by simp at hl

theorem KidsDepBPR.append {κ : ℕ} : ∀ {ks ks' : List KidD} {Bs Bs' : List ℕ} {Ps Ps' : List (Reader → Tree → Prop)},
    KidsDepBPR fs cert κ ks Bs Ps → KidsDepBPR fs cert κ ks' Bs' Ps' →
      KidsDepBPR fs cert κ (ks ++ ks') (Bs ++ Bs') (Ps ++ Ps')
  | [], _, [], _, [], _, _, h' => h'
  | _ :: _, _, _ :: _, _, _ :: _, _, ⟨h, hs⟩, h' => ⟨h, KidsDepBPR.append hs h'⟩
  | [], _, _ :: _, _, _, _, h, _ | [], _, [], _, _ :: _, _, h, _ | _ :: _, _, [], _, _, _, h, _
  | _ :: _, _, _ :: _, _, [], _, h, _ => by simp [KidsDepBPR] at h

/-- **Callees within their bounds, each exact on every valid tree**, are within them by trees exact on the memory. -/
theorem KidsDepB.toE {κ : ℕ} : ∀ {ks : List KidD} {Bs : List ℕ}, KidsDepB fs cert κ ks Bs →
    (∀ k ∈ ks, ∀ pv, (k pv).taken = true → ExactOk (k pv).f) →
    KidsDepBPR fs cert κ ks Bs (List.replicate ks.length everyE)
  | [], [], _, _ => trivial
  | k :: ks, b :: Bs, ⟨h, hs⟩, hE =>
    ⟨fun pv => ⟨fun ht => (((h pv).1 ht).toDTB.toR.andEvery
        (everyOn_exactOk (hE k List.mem_cons_self pv ht))).mono le_rfl fun _ _ h => h.2, (h pv).2⟩,
      KidsDepB.toE hs fun k' hk' => hE k' (List.mem_cons_of_mem _ hk')⟩
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp [KidsDepB] at h

theorem kidsDepBPR_replicate {κ : ℕ} {b : ℕ} {P : Reader → Tree → Prop} : ∀ {ks : List KidD},
    (∀ k ∈ ks, ∀ pv, ((k pv).taken = true →
        CompleteAtDTBR fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out P b) ∧
      ((k pv).taken = false → fs (k pv).f ≤ b)) →
    KidsDepBPR fs cert κ ks (List.replicate ks.length b) (List.replicate ks.length P)
  | [], _ => trivial
  | k :: _, h => ⟨h k List.mem_cons_self, kidsDepBPR_replicate fun k' hk' => h k' (List.mem_cons_of_mem _ hk')⟩

theorem namedP_zipWith : ∀ (ns : List String) (Bs : List ℕ) (Ps : List (Tree → Prop)),
    ns.length = Bs.length → ns.length = Ps.length →
    List.Forall₂ (fun T T' => ∀ t, T t → T' t) (namedP fs ns Bs Ps) (List.zipWith (Budget.NamedWithin fs) ns Bs)
  | [], [], [], _, _ => by simp [namedP]
  | n :: ns, b :: Bs, P :: Ps, h1, h2 =>
    .cons (fun _ h => h.1) (namedP_zipWith ns Bs Ps (by simpa using h1) (by simpa using h2))
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ | [], [], _ :: _, _, h | _ :: _, _ :: _, [], _, h => by simp at h

/-- **The column selectors, each within `Bcs` by a tree exact on the memory.** -/
theorem selKids_E (κ : ℕ) (hκ : 6 ≤ κ) (D : TermData) (hxl : D.x.length ≤ 32) {Bcs : ℕ}
    (hKC : ∀ c < Tables.nCommittedCols, D.KC.getD c 0 < 31)
    (hOF : ∀ c < Tables.nCommittedCols, D.OF.getD c 0 < 2 ^ 32 ∧ 2 ^ D.KC.getD c 0 ∣ D.OF.getD c 0)
    (hCsF : ∀ κ' < 31, fs (Tables.lName "column_selector" κ') ≤ Bcs) :
    KidsDepBPR fs cert κ ((List.range Tables.nCommittedCols).map (selKid D))
      (List.replicate Tables.nCommittedCols Bcs) (List.replicate Tables.nCommittedCols everyE) := by
  have hpl : (p1Of D.x).length = 40 := p1Of_length (by simp only [termPointCap]; omega)
  have hpt : (padPoint D.x).length = 40 := padPoint_length (by simp only [termPointCap]; omega)
  have h : KidsDepBPR fs cert κ ((List.range Tables.nCommittedCols).map (selKid D))
      (List.replicate ((List.range Tables.nCommittedCols).map (selKid D)).length Bcs)
      (List.replicate ((List.range Tables.nCommittedCols).map (selKid D)).length everyE) := by
    refine kidsDepBPR_replicate fun k hk pv => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
    rw [List.mem_range] at hc
    refine ⟨fun ht => ?_, fun _ => hCsF _ (hKC c hc)⟩
    have hst : Tables.stOut D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x) (stRes pv).1 (stRes pv).2 :=
      @of_decide_eq_true _ (Classical.propDecidable _) ht
    obtain ⟨ese, h1, h2⟩ := hst
    have hL : (selKid D c pv).Lin =
        csLin D.B.pt D.B.pt1 ese (D.B.gsq + 34) (pt32 D.x) (pt132 D.x) := by
      show @ite _ _ (Classical.propDecidable _) _ _ = _
      rw [@ite_pos' _ _ (Classical.propDecidable _) _ _ ⟨ese, h1, h2⟩, h2]; rfl
    have ha : (selKid D c pv).args = [gen ^ D.OF.getD c 0, ofK (addressOfIndex ese), ofK
        (addressOfIndex (D.B.gsq + 34))] := by
      show [_, (stRes pv).1.getD 0 0, _] = _
      rw [h1]; rfl
    rw [hL, ha]
    exact (cs_completeAtDTBRE κ (by omega) (hKC c hc) (hOF c hc).1 (hOF c hc).2
      (by simp [pt32]; omega) (by simp [pt132]; omega)).mono (hCsF _ (hKC c hc)) fun _ _ h => h
  rwa [List.length_map, List.length_range] at h

/-- **The terminal's callees, within `termBs` by trees exact on the memory** (`termKids_completeB`). -/
theorem termKids_completeBE (κ : ℕ) (hκ : 6 ≤ κ) (Lin : Main.Layout) (D : TermData) (b0 : ℕ)
    (hreg : ∀ i, TermRegion D.B D.zs.length D.chis.length D.τ D.ood.length i → RegionL Lin i)
    (hzl : D.zs.length ≤ 34) (hcl : D.chis.length ≤ 34) (hxl : D.x.length ≤ 32)
    (hτ : D.τ + 6 ≤ 34) (hol : D.outPt.length = D.τ + 6) (hrl : D.ringPoint.length = D.τ + 6)
    (hcf : D.coeffs.length = 64) (hgmu : D.gmu = gen ^ D.zs.length)
    (hgz : D.gzcn = gen ^ D.chis.length) (hglm : D.glm = gen ^ D.m) (hgtau : D.gtau = gen ^ D.τ)
    (hm1 : 1 ≤ D.m) (hm : D.m ≤ 32) (hKC : ∀ c < Tables.nCommittedCols, D.KC.getD c 0 < 31)
    (hOF : ∀ c < Tables.nCommittedCols, D.OF.getD c 0 < 2 ^ 32 ∧ 2 ^ D.KC.getD c 0 ∣ D.OF.getD c 0)
    (hrd : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex D.B.zeta)) D.zs ∧
      ReadsAt rd (ofK (addressOfIndex D.B.chi)) D.chis ∧ ReadsAt rd (ofK (addressOfIndex D.B.zv))
          D.outPt ∧
      ReadsAt rd (ofK (addressOfIndex D.B.pt1)) (p1Of D.x))
    (hodl : D.ood.length ≤ 30) (hgm : D.gm = gen ^ D.ood.length)
    (hrdO : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex D.B.oz)) D.ood)
    {Beqc K15 Bcs Brs : ℕ} (hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ => Beqc)
    (hL15 : TotalLeOn coreProgram fs name% «check_opening_terminal_loop0» LoopPre
      fun a => logG (a.getD 1 0) * K15 + fs name% «check_opening_terminal_loop0»)
    (hCsF : ∀ κ' < 31, fs (Tables.lName "column_selector" κ') ≤ Bcs)
    (hrs : ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a => a.getD 3 0 = gen ^ c)
      fun _ => Brs) :
    KidsDepBPR fs cert κ (termKids Lin D b0) (termBs fs Beqc K15 Bcs Brs) termPsE := by
  have h := termKids_completeB (fs := fs) (cert := cert) κ hκ Lin D b0 hreg hzl hcl hxl hτ hol hrl hcf hgmu hgz hglm hgtau hm1 hm hKC hOF hrd
    hodl hgm hrdO hEqc hL15 hCsF hrs
  unfold termKids termBs at h
  obtain ⟨hAB, hC⟩ := KidsDepB.split (by simp) h
  obtain ⟨hA, -⟩ := KidsDepB.split (by simp) hAB
  unfold termKids termBs termPsE
  refine KidsDepBPR.append (KidsDepBPR.append (KidsDepB.toE hA ?_) (selKids_E κ hκ D hxl hKC hOF hCsF))
    (KidsDepB.toE hC ?_)
  · intro k hk pv _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact .free eqc_exactFree
    · exact .free eqc_exactFree
    · exact .free l15_exactFree
    · exact .free st_exactFree
  · intro k hk pv _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact .free eqc_exactFree
    · exact rsw_exactOk
    · exact .free eqc_exactFree

theorem check_opening_terminal_completeAtBWE (κ : ℕ) (hκ : 6 ≤ κ) (B : TermBases)
    (Lin : Main.Layout)
    {layout : Layout} {bus : BusResult} {claims : List ColumnClaim} {out : ColumnClaim} {lam : E}
    {ringPoint coeffs oodPoint x : List E} {rm gmu gzcn glm gtau lamCl inner yr target gm : E} {nc : ℕ}
    (hnc : nc ≤ 40) (hgz : gzcn = gen ^ nc)
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → TermPre rd layout bus claims out lam ringPoint coeffs
      oodPoint x (termArgs B rm gmu gzcn glm gtau lamCl inner yr target gm))
    (hreg : ∀ i, TermRegion B bus.point.length nc (layout.tableLogHeights.getD opKeccak 0)
      layout.stackLog i → RegionL Lin i)
    (hbus : bus.point.length ≤ 34)
    (hfin : (inner + stackWeight layout (openedClaims claims [out]) ringPoint coeffs oodPoint lam x) *
      yr = target)
    {Beqc K15 Bcs Brs : ℕ} (hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ => Beqc)
    (hL15 : TotalLeOn coreProgram fs name% «check_opening_terminal_loop0» LoopPre
      fun a => logG (a.getD 1 0) * K15 + fs name% «check_opening_terminal_loop0»)
    (hCsF : ∀ κ' < 31, fs (Tables.lName "column_selector" κ') ≤ Bcs)
    (hrs : ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a => a.getD 3 0 = gen ^ c)
      fun _ => Brs)
    {ι : Type} (ω : ι → String → ℕ) (Weqc W15 Wst Wcs Wrsw : ι → ℕ)
    (hEqcW : ∀ i, WeightLe coreProgram (ω i) "eq_prefix_chain" fun _ => Weqc i)
    (hStW : ∀ i, WeightLe coreProgram (ω i) "selector_tables" fun _ => Wst i)
    (hCsW : ∀ i, ∀ κ' < 31, WeightLe coreProgram (ω i) (Tables.lName "column_selector" κ')
      fun _ => Wcs i)
    (h15W : ∀ i (rd : Reader) (t : Tree) (args rets : List E),
        t.name = name% «check_opening_terminal_loop0» →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ (32 * K15 + fs name% «check_opening_terminal_loop0») → t.weight (ω i) ≤ W15 i)
    (hrswW : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = "ring_switch_weight" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ fs "ring_switch_weight" + 2240 + Brs → t.weight (ω i) ≤ Wrsw i) :
    CompleteAtDTBR fs cert κ "check_opening_terminal" Lin
      (termArgs B rm gmu gzcn glm gtau lamCl inner yr target gm) (Returns [])
      (fun rd t => (∀ i, Budget.WeighsLe coreProgram (ω i)
        (ω i "check_opening_terminal" + (termWs Weqc W15 Wst Wcs Wrsw i).sum) t) ∧ t.Every (ExactAt coreProgram rd))
      (fs "check_opening_terminal" + 177 + 4 * Beqc + (32 * K15 + fs
          name% «check_opening_terminal_loop0») +
        (fs "selector_tables" + 512) + 94 * Bcs + (fs "ring_switch_weight" + 2240 + Brs)) := by
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  swap
  · intro fp
    exact ⟨0, [], [], [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd0, hl0, hm0⟩ := hex
  have P0 := hpre rd0 hl0 hm0
  simp only [TermPre, termArgs] at P0
  obtain ⟨hT, hPC, -, hP, hSL, hSL30, hlm1, hlm32, hbus40, hHL, -, hglm, hgtau, -, -, -, -, hopl,
    -, hrpl, -, hcfl, -, hxl, -, -, hodl, -, hgm⟩ := P0
  have hSL28 : layout.stackLog ≤ 32 := by omega
  obtain ⟨chis, -, hgmu, hchR, hgzc, hchL, -⟩ := hT
  obtain ⟨hkap, -⟩ := hPC
  have hncl : chis.length = nc := gen_pow_inj_le (by omega) (by omega) (hgzc.symm.trans hgz)
  subst hncl
  have hchis : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex B.chi)) chis :=
    fun rd _ hm => readsAt_transfer hm0 hm hchR fun k hk => hreg _ (by simp only [TermRegion]; omega)
  set kappas := columnKappas layout.logMemory Tables.guestLogBytecode layout.tableLogHeights
    with hkdef
  set KC := Tables.committedKappas kappas with hKCdef
  set τ := layout.tableLogHeights.getD opKeccak 0 with hτ
  have hLdef : layout.stackLog = max Whir.minLogStack (stackOffsets KC).2 := by
    rw [hSL, placementsOf_snd]
  have hKClen : KC.length = Tables.nCommittedCols := Tables.committedKappas_length _ hkap
  have hK : ∀ c < Tables.nCommittedCols, KC.getD c 0 ≤ layout.stackLog := fun c hc ↦ by
    have := size_le_stackOffsets KC (i := c) (by omega); rw [hLdef]; omega
  have hO : ∀ c, (stackOffsets KC).1.getD c 0 < 2 ^ layout.stackLog := fun c ↦
    lt_of_lt_of_le (stackOffsets_lt KC c) (Nat.pow_le_pow_right (by decide) (by rw [hLdef]; omega))
  have hk5 : kappas.take 5 = [layout.logMemory, layout.logMemory, layout.logMemory,
      Tables.guestLogBytecode, τ + 6] := kappas_small hHL
  have hK4 : KC.getD 4 0 = τ + 6 := by
    rw [committedKappas_small hkap (by decide), ← getD_take_nat (n := 5) (by decide), hk5]; rfl
  have hK4L := hK 4 (by decide)
  rw [hK4] at hK4L
  have hxl40 : x.length ≤ termPointCap := by simp only [termPointCap]; omega
  set D := termD B layout bus out ringPoint coeffs x chis oodPoint rm gmu gzcn glm gtau gm lamCl
    with hD
  have hst : ∀ rd, LowDef κ rd → MemL rd Lin →
      MemL rd (Tables.stLin B.pt B.pt1 (pt32 x) (pt132 x)) := fun rd hl hm q hq => by
    have P := hpre rd hl hm
    simp only [TermPre, termArgs] at P
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpt, hpt1, -⟩ := P
    simp only [Tables.stLin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact readsAt_take hpt 32
    · exact readsAt_take hpt1 32
  have f1 : D.τ + 6 ≤ 34 := by show τ + 6 ≤ 34; omega
  have f2 : D.ringPoint.length = D.τ + 6 := by
    show ringPoint.length = τ + 6; rw [hrpl, Tables.qkeccakSlotBits_eq]
  have f3 : D.coeffs.length = 64 := by show coeffs.length = 64; rw [hcfl]; rfl
  have f4 : D.x.length ≤ 32 := by show x.length ≤ 32; omega
  have f5 : D.outPt.length = D.τ + 6 := by
    show out.point.length = τ + 6; rw [hopl, Tables.qkeccakSlotBits_eq]
  have f7 : D.chis.length ≤ 34 := by show chis.length ≤ 34; omega
  have f8 : D.ood.length ≤ 30 := by show oodPoint.length ≤ 30; omega
  have f9 : D.gm = gen ^ D.ood.length := by show gm = gen ^ oodPoint.length; rw [hgm, hodl]
  have hreg' : ∀ i, TermRegion D.B D.zs.length D.chis.length D.τ D.ood.length i → RegionL Lin i := by
    show ∀ i, TermRegion B bus.point.length chis.length τ oodPoint.length i → RegionL Lin i
    rw [hodl]; exact hreg
  have hKC31 : ∀ c < Tables.nCommittedCols, D.KC.getD c 0 < 31 := fun c hc => by
    have := hK c hc; show KC.getD c 0 < 31; omega
  refine (completeAt_flatDepRBPR find_term term_not_loop κ Lin _ [] term_body' term_flat term_addrs
    (by decide +kernel)
    [35, 35, 35, 41, 31] (fun _ => termOwn D) (fun _ => ?_)
    (fun fp => termKids Lin D (fp + fs "check_opening_terminal")) (termNames D)
    (termBs fs Beqc K15 Bcs Brs) termPsE (fun _ _ => True) (fun fp => termKids_names Lin D _)
    (fun fp => ?_)
    (fun fp outs _ => termKids_regions Lin D _ hreg' f1 f2 f3 f4 outs)
    (fun fp outs _ rd hl hB hLin hLo => ?_) (fun fp outs hlen' ho rd hl hB hLin _ => ?_)).monoV
    (le_of_eq ?_) fun rd t rets hv ⟨hF, _⟩ =>
      ⟨fun i rd' _ _ hv' hb => term_weight_le ω Weqc W15 Wst Wcs Wrsw hEqcW hStW hCsW h15W hrswW hKC31
        (flatShape_mono hF (namedP_zipWith _ _ _ (by simp [termNames, termBs, Tables.nCommittedCols])
          (by simp [termNames, termPsE, Tables.nCommittedCols]))) hv' hb i,
        flatShape_every find_term term_pinned hF hv (namedP_every _ _ _ (termPsE_every rd))⟩
  · simp only [termOwn, List.forall₂_cons, eqChain_length, piW_length,
      List.Forall₂.nil, and_true]
    have hol : out.point.length = τ + 6 := by rw [hopl, Tables.qkeccakSlotBits_eq]
    show bus.point.length + 1 ≤ 35 ∧ chis.length + 1 ≤ 35 ∧ layout.logMemory + 1 ≤ 35 ∧
      out.point.length + 1 ≤ 41 ∧ oodPoint.length + 1 ≤ 31
    omega
  · refine termKids_completeBE κ hκ Lin D _ hreg' hbus f7 f4 f1 f5 f2 f3 hgmu hgzc hglm hgtau hlm1
      hlm32 hKC31 (fun c hc => ?_)
      (fun rd hl hm => ?_) f8 f9 (fun rd hl hm => ?_) hEqc hL15 hCsF hrs
    · exact ⟨lt_of_lt_of_le (hO c) (Nat.pow_le_pow_right (by decide) hSL28),
        dvd_stackOffset KC (by omega)⟩
    · have P := hpre rd hl hm
      simp only [TermPre, termArgs] at P
      obtain ⟨⟨chis', hzR, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hoz, -, -, -, -, -,
        -, hpt1, -⟩ := P
      exact ⟨hzR, hchis rd hl hm, hoz, hpt1⟩
    · have P := hpre rd hl hm
      simp only [TermPre, termArgs] at P
      exact P.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · have P := hpre rd hl hLin
    simp only [TermPre, termArgs] at P
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hgt, -, -, -, -, -, hrp, -, hct, -, -, hpt1, -⟩ :=
      P
    refine termKids_mem Lin D _ outs hB hLin hLo (hst rd hl hLin) ?_ fun q hq => ?_
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      rw [ofK_gpow_mul_gen] at hgt
      exact reads_of_gTabs hgt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · show ReadsAt rd (ofK (addressOfIndex (B.zv + 39))) ringPoint
      rw [← ofK_gpow_mul_gen]; exact hrp
    · exact readsAt_take hpt1 _
    · exact hct
  · obtain ⟨σ, hσ⟩ := term_sigma B Lin (fp + fs "check_opening_terminal") outs rd (hpre rd hl hLin)
      (hchis rd hl hLin) hgzc (by omega) hreg hbus hfin (by rw [hlen', termKids_length]) ho hB
    exact ⟨σ, trivial, hσ⟩
  · rw [termBs_sum]
    simp only [List.sum_cons, List.sum_nil]
    omega



namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **The terminal on an honest child, entered, within `termBound` by a tree within its weights and exact.** -/
theorem term_kidBWE (hbl : bytecode.length = 2 ^ 23) {κ : ℕ} (hκ : 6 ≤ κ) (W : VsWordsOs fs)
    (bs : List ℕ) (sqE : ℕ) (pv : List (List E × Main.Layout))
    (ht : ((S.kids bs sqE).getD 15 noKid pv).taken = true) :
    CompleteAtDTBR fs cert κ ((S.kids bs sqE).getD 15 noKid pv).f
      ((S.kids bs sqE).getD 15 noKid pv).Lin ((S.kids bs sqE).getD 15 noKid pv).args
      ((S.kids bs sqE).getD 15 noKid pv).Out
      (fun rd t ↦ (∀ op, Budget.WeighsLe coreProgram (W.ωv op) (termWB W.toVsWords op) t) ∧
        t.Every (ExactAt coreProgram rd))
      (termBound fs W.Beqc W.K15 W.Bcs W.Brs) :=
  S.term_via hbl bs sqE pv ht (fun f L a O ↦ CompleteAtDTBR fs cert κ f L a O
    (fun rd t ↦ (∀ op, Budget.WeighsLe coreProgram (W.ωv op) (termWB W.toVsWords op) t) ∧
      t.Every (ExactAt coreProgram rd))
    (termBound fs W.Beqc W.K15 W.Bcs W.Brs)) fun Lin B hpre hreg ↦
    check_opening_terminal_completeAtBWE κ hκ B Lin (nc := S.nT) (by have := S.nT_le hbl; omega) rfl
      (fun rd _ hm ↦ hpre rd hm) hreg (S.bus_point_le34 hbl) (S.fin hbl) W.hEqc W.hL15 W.hCsF
      W.hrs W.ωv W.Weqc W.W15 W.Wst W.Wcs W.Wrsw W.hEqcW W.hStW W.hCsW W.h15W W.hrswW

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
