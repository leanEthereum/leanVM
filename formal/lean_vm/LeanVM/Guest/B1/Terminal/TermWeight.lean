/-
  LeanVM.Guest.B1.Terminal.TermWeight

  `check_opening_terminal` complete, placed, within its bound, by a tree within its weights: its
  callees by name within their words (`completeAt_flatDepRBT`), each callee's weight by its
  certificate or, `check_opening_terminal_loop0`'s and `ring_switch_weight`'s, by its words.
-/

module

public import LeanVM.Guest.B1.Terminal.TermCompleteB
public import LeanVM.Guest.B1.Terminal.KidsDepBT
public import LeanVM.Guest.Budget.Weighs
public import LeanVM.Guest.Data.NameStrings

/-!
# The terminal within its weights

`termNames D`: the terminal's callees' names, in call order (the column selectors' by the columns'
sizes `D.KC`). `termWs`: their weight bounds. `term_weight_le`: a node of `Budget.FlatShape` for
`termNames`, `termBs` weighs at most its frame's weight and `termWs` at each `ω i`.
`check_opening_terminal_completeAtBW`: `check_opening_terminal_completeAtB` by a tree within those
weights.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The terminal's callees' names**, in call order. -/
def termNames (D : TermData) : List String :=
  ["eq_prefix_chain", "eq_prefix_chain", name% «check_opening_terminal_loop0», "selector_tables"] ++
    (List.range Tables.nCommittedCols).map (fun c => Tables.lName "column_selector" (D.KC.getD c 0)) ++
    ["eq_prefix_chain", "ring_switch_weight", "eq_prefix_chain"]

/-- **The terminal's callees' weight bounds**, in call order. -/
def termWs {ι : Type} (Weqc W15 Wst Wcs Wrsw : ι → ℕ) (i : ι) : List ℕ :=
  [Weqc i, Weqc i, W15 i, Wst i] ++ List.replicate Tables.nCommittedCols (Wcs i) ++ [Weqc i, Wrsw i, Weqc i]

theorem forall₂_append' {α β : Type} {R : α → β → Prop} : ∀ {l1 l3 : List α} {l2 l4 : List β},
    List.Forall₂ R l1 l2 → List.Forall₂ R l3 l4 → List.Forall₂ R (l1 ++ l3) (l2 ++ l4)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, .cons h1 h2, h => .cons h1 (forall₂_append' h2 h)

theorem termKids_names (Lin : Main.Layout) (D : TermData) (b0 : ℕ) :
    List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (termKids Lin D b0) (termNames D) := by
  unfold termKids termNames
  refine forall₂_append' (forall₂_append' ?_ ?_) ?_
  · exact .cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) .nil)))
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun _ _ _ => rfl
  · exact .cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) .nil))

/-- **The terminal's node weighs at most** its frame's weight and `termWs` at each `ω i`. -/
theorem term_weight_le {ι : Type} (ω : ι → String → ℕ) (Weqc W15 Wst Wcs Wrsw : ι → ℕ)
    (hEqcW : ∀ i, WeightLe coreProgram (ω i) "eq_prefix_chain" fun _ => Weqc i)
    (hStW : ∀ i, WeightLe coreProgram (ω i) "selector_tables" fun _ => Wst i)
    (hCsW : ∀ i, ∀ κ' < 31, WeightLe coreProgram (ω i) (Tables.lName "column_selector" κ')
      fun _ => Wcs i)
    {K15 Brs Beqc Bcs : ℕ}
    (h15W : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = name% «check_opening_terminal_loop0» →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ (32 * K15 + fs name% «check_opening_terminal_loop0») → t.weight (ω i) ≤ W15 i)
    (hrswW : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = "ring_switch_weight" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ fs "ring_switch_weight" + 2240 + Brs → t.weight (ω i) ≤ Wrsw i)
    {D : TermData} (hKC : ∀ c < Tables.nCommittedCols, D.KC.getD c 0 < 31) {t : Tree}
    (h : Budget.FlatShape coreProgram "check_opening_terminal"
      (List.zipWith (Budget.NamedWithin fs) (termNames D) (termBs fs Beqc K15 Bcs Brs)) t)
    {rd : Reader} {args rets : List E} (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (i : ι) :
    t.weight (ω i) ≤ ω i "check_opening_terminal" + (termWs Weqc W15 Wst Wcs Wrsw i).sum := by
  refine Budget.FlatShape.weight_le (ω i) _ h hv hb
    (by simp [termNames, termBs, termWs, Tables.nCommittedCols]) ?_
  intro j hT hW rd' t' args' rets' hv' hb' hTj
  rw [List.getElem_zipWith] at hTj
  obtain ⟨hn, htot⟩ := hTj
  have hj : j < 101 := by simpa [termWs, Tables.nCommittedCols] using hW
  by_cases h4 : j < 4
  · interval_cases j <;>
      simp only [termNames, termBs, termWs, List.append_assoc, List.cons_append,
        List.getElem_cons_zero, List.getElem_cons_succ] at hn htot ⊢
    · exact hEqcW i rd' t' args' rets' hn hv' hb'
    · exact hEqcW i rd' t' args' rets' hn hv' hb'
    · exact h15W i rd' t' args' rets' hn hv' hb' htot
    · exact hStW i rd' t' args' rets' hn hv' hb'
  by_cases h98 : j < 98
  · have e1 : (termNames D)[j]'(by simp [termNames, Tables.nCommittedCols]; omega) =
        Tables.lName "column_selector" (D.KC.getD (j - 4) 0) := by
      simp only [termNames, List.append_assoc]
      rw [List.getElem_append_right (by simp; omega), List.getElem_append_left
        (by simp [Tables.nCommittedCols]; omega)]
      simp
    have e2 : (termWs Weqc W15 Wst Wcs Wrsw i)[j]'hW = Wcs i := by
      simp only [termWs, List.append_assoc]
      rw [List.getElem_append_right (by simp; omega), List.getElem_append_left
        (by simp [Tables.nCommittedCols]; omega)]
      simp
    rw [e1] at hn
    rw [e2]
    exact hCsW i _ (hKC _ (by simp [Tables.nCommittedCols]; omega)) rd' t' args' rets' hn hv' hb'
  · have hj' : j = 98 ∨ j = 99 ∨ j = 100 := by omega
    rcases hj' with rfl | rfl | rfl <;>
      simp [termNames, termBs, termWs, Tables.nCommittedCols, List.getElem_append_right] at hn htot ⊢
    · exact hEqcW i rd' t' args' rets' hn hv' hb'
    · exact hrswW i rd' t' args' rets' hn hv' hb' htot
    · exact hEqcW i rd' t' args' rets' hn hv' hb'

/-- **`check_opening_terminal` is complete, placed, within a bound, by a tree within its weights**
(`check_opening_terminal_completeAtB` by a node of `Budget.FlatShape`): at each `ω i`, its frame's
weight, its four prefix chains' `Weqc i`, `check_opening_terminal_loop0`'s `W15 i`, `selector_tables`' `Wst i`, each
column selector's `Wcs i` and `ring_switch_weight`'s `Wrsw i`, the last two by their trees'
words (`h15W`, `hrswW`). -/
theorem check_opening_terminal_completeAtBW (κ : ℕ) (hκ : 6 ≤ κ) (B : TermBases)
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
    (h15W : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = name% «check_opening_terminal_loop0» →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ (32 * K15 + fs name% «check_opening_terminal_loop0») → t.weight (ω i) ≤ W15 i)
    (hrswW : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = "ring_switch_weight" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ fs "ring_switch_weight" + 2240 + Brs → t.weight (ω i) ≤ Wrsw i) :
    CompleteAtDTB fs cert κ "check_opening_terminal" Lin
      (termArgs B rm gmu gzcn glm gtau lamCl inner yr target gm) (Returns [])
      (fun t => ∀ i, Budget.WeighsLe coreProgram (ω i)
        (ω i "check_opening_terminal" + (termWs Weqc W15 Wst Wcs Wrsw i).sum) t)
      (fs "check_opening_terminal" + 177 + 4 * Beqc + (32 * K15 + fs name% «check_opening_terminal_loop0») +
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
  refine (completeAt_flatDepRBT find_term term_not_loop κ Lin _ [] term_body' term_flat term_addrs
    (by decide +kernel)
    [35, 35, 35, 41, 31] (fun _ => termOwn D) (fun _ => ?_)
    (fun fp => termKids Lin D (fp + fs "check_opening_terminal")) (termNames D)
    (termBs fs Beqc K15 Bcs Brs) (fun fp => termKids_names Lin D _)
    (fun fp => ?_)
    (fun fp outs _ => termKids_regions Lin D _ hreg' f1 f2 f3 f4 outs)
    (fun fp outs _ rd hl hB hLin hLo => ?_) (fun fp outs hlen' ho rd hl hB hLin _ => ?_)).mono
    (le_of_eq ?_) fun t ht i rd' _ _ hv hb =>
      term_weight_le ω Weqc W15 Wst Wcs Wrsw hEqcW hStW hCsW h15W hrswW hKC31 ht hv hb i
  · simp only [termOwn, List.forall₂_cons, eqChain_length, piW_length,
      List.Forall₂.nil, and_true]
    have hol : out.point.length = τ + 6 := by rw [hopl, Tables.qkeccakSlotBits_eq]
    show bus.point.length + 1 ≤ 35 ∧ chis.length + 1 ≤ 35 ∧ layout.logMemory + 1 ≤ 35 ∧
      out.point.length + 1 ≤ 41 ∧ oodPoint.length + 1 ≤ 31
    omega
  · refine termKids_completeB κ hκ Lin D _ hreg' hbus f7 f4 f1 f5 f2 f3 hgmu hgzc hglm hgtau hlm1
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
  · exact term_sigma B Lin (fp + fs "check_opening_terminal") outs rd (hpre rd hl hLin)
      (hchis rd hl hLin) hgzc (by omega) hreg hbus hfin (by rw [hlen', termKids_length]) ho hB
  · rw [termBs_sum]
    simp only [List.sum_cons, List.sum_nil]
    omega


end
end LeanVM.Guest.B1.VerifySub
