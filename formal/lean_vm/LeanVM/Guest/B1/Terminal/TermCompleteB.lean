/-
  LeanVM.Guest.B1.Terminal.TermCompleteB

  **`check_opening_terminal` is complete, placed, within a bound** (`CompleteAtB`): its frame, its
  five buffers (`177` words) and its 101 callees' bounds, before the memory.
-/

module

public import LeanVM.Guest.B1.Terminal.TermComplete
public import LeanVM.Guest.B1.Terminal.KidsDepB
public import LeanVM.Guest.B1.Ring.CompleteB
public import LeanVM.Guest.Memory.LoopPre

/-!
# `check_opening_terminal`, within a bound

`check_opening_terminal_completeAtB`: `check_opening_terminal_completeAt` with the size at most

  `fs "check_opening_terminal" + 177 + 4·Beqc + (32·K15 + fs "__loop14")
    + (fs "selector_tables" + 512) + 94·Bcs + (fs "ring_switch_weight" + 2240 + Brs)`

(`completeAt_flatDepRB`, the callees within `termBs`, `termKids_completeB`). The pure callees'
words are fs-generic hypotheses, in the forms the words certificates give at `B2C.fs`:

* `hEqc`: `eq_prefix_chain` within `Beqc` (`TotalLe`, constant; its certificate: `184`), four calls;
* `hL15`: `__loop14`'s run within `K15` per unit of its end's exponent and its one phantom frame
  (`TotalLeOn … LoopPre`, as `Count.wSKt_totalLeOn`; its certificate: `19`); its end is `g^m`,
  `m ≤ 32`, so `32·K15` and its frame (its frame alone when skipped, `m = 1`);
* `hCsF`: each `column_selector__L{κ}`, `κ < 31`, has its frame within `Bcs` (it has no buffer and
  no callee: `cs_completeAtB`), `94` calls;
* `hrs`: `rs_eq_run` on `c ≤ 34` coordinates within `Brs` (`TotalLeOn`; it has no words
  certificate), through `ring_switch_weight` (`rsw_completeAtB`, its chain `64·(τ + 7) ≤ 2240`);
* `selector_tables` within its frame and buffer (B1-c's `selector_tables_completeAtB`: `512`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## The callees within their bounds -/

/-- **A prefix chain, complete, placed, within `Beqc`** (`eqc_kid_complete`), `eq_prefix_chain`'s
words at most `Beqc`. -/
theorem eqc_kid_completeB (κ : ℕ) (hκ : 6 ≤ κ) {b ba bb : ℕ} {s : E} {as bs : List E} {cg : E}
    {L : Main.Layout} (hn : as.length ≤ 40) (hbs : bs.length = as.length) (hcg : cg = gen ^ as.length)
    (hrd : ∀ rd, LowDef κ rd → MemL rd L → ReadsAt rd (ofK (addressOfIndex ba)) as ∧ ReadsAt rd (ofK (addressOfIndex bb)) bs)
    (hR : ∀ i, (ba ≤ i ∧ i < ba + as.length) ∨ (bb ≤ i ∧ i < bb + as.length) → RegionL L i)
    {Beqc : ℕ} (hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ => Beqc) :
    CompleteAtB fs cert κ "eq_prefix_chain" ((b, eqChain s as bs) :: L)
      [ofK (addressOfIndex b), s, ofK (addressOfIndex ba), ofK (addressOfIndex bb), cg]
          (Returns []) Beqc := by
  refine (completeAtDTB_of_relIn eqc_pure List.mem_cons_self
    (fun rd t rets' hn hv hb => hEqc rd t _ rets' hn hv hb) fun rd hl hm => ?_).toCompleteAtB
  have hm0 : ReadsAt rd (ofK (addressOfIndex b)) (eqChain s as bs) := hm _ List.mem_cons_self
  have hmL : MemL rd L := fun q hq => hm q (List.mem_cons_of_mem _ hq)
  obtain ⟨ha, hb⟩ := hrd rd hl hmL
  subst hcg
  refine eqc_relIn hn (fun i hi => ?_) ((eq_prefix_chain_holds rd _ _).mpr
    ⟨rfl, low_rc hκ hl hn, as.length, by omega, rfl, as, bs, rfl, hbs, ha, hb, fun j hj => ?_⟩)
  · rcases hi with hi | hi
    · exact regionL_head hi.1 (by rw [eqChain_length]; omega)
    · exact regionL_cons _ (hR i hi)
  · have := hm0 j (by rw [eqChain_length]; omega)
    simpa [eqChain] using this

/-- **The public input's chain's loop, complete, placed, within `m·K15` and its frame**
(`l15_kid_complete`), `__loop14`'s run's words at most `K15` per unit of its end's exponent and its
one phantom frame. -/
theorem l15_kid_completeB (κ : ℕ) {b bp m : ℕ} {rm glm : E} {ps : List E} {L : Main.Layout}
    (hm2 : 2 ≤ m) (hmo : m < 2 ^ 64 - 1) (hglm : glm = gen ^ m) (hps : m ≤ ps.length)
    (hrd : ∀ rd, LowDef κ rd → MemL rd L → ReadsAt rd (ofK (addressOfIndex bp)) ps)
    (hR : ∀ i, bp ≤ i ∧ i < bp + m → RegionL L i) {K15 : ℕ}
    (hL15 : TotalLeOn coreProgram fs "__loop14" LoopPre
      fun a => logG (a.getD 1 0) * K15 + fs "__loop14") :
    CompleteAtB fs cert κ "__loop14" ((b, piW rm ps m) :: L)
      [word 2 0, glm, ofK (addressOfIndex b), ofK (addressOfIndex bp)] (Returns [])
      (m * K15 + fs "__loop14") := by
  have hpre : LoopPre [word 2 0, glm, ofK (addressOfIndex b), ofK (addressOfIndex bp)] :=
    ⟨1, m, by show word 2 0 = _; rw [word_gen, ← gen_pow_eq_ofK, pow_one],
      by show glm = _; rw [hglm, gen_pow_eq_ofK], by omega, hmo⟩
  have hlog : logG glm = m := by rw [hglm, gen_pow_eq_ofK, logG_spec hmo]
  refine (completeAtDTB_of_relIn (B := m * K15 + fs "__loop14") l15_pure List.mem_cons_self
    (fun rd t rets' hn hv hb => le_of_le_of_eq (hL15 rd t _ rets' hn hpre hv hb)
      (by show logG glm * K15 + fs "__loop14" = m * K15 + fs "__loop14"; rw [hlog]))
    fun rd hl hm => ?_).toCompleteAtB
  have hm0 : ReadsAt rd (ofK (addressOfIndex b)) (piW rm ps m) := hm _ List.mem_cons_self
  have hmL : MemL rd L := fun q hq => hm q (List.mem_cons_of_mem _ hq)
  have hstep : ∀ k, 1 ≤ k → k < m →
      (piW rm ps m).getD (k + 1) 0 = (piW rm ps m).getD k 0 * (ps.take m).getD k 0 := by
    intro k hk1 hkm
    have e : (ps.take m).getD k 0 = ps.getD k 0 := by
      simp [List.getD_eq_getElem?_getD, hkm]
    rw [piW_getD (by omega), piW_getD (by omega), ite_neg' (by omega), ite_neg' (by omega),
      Finset.prod_Ico_succ_top (by omega), e, mul_assoc]
  have h := l15_relIn (piW_length rm ps m) (by simp; omega) hm0 (readsAt_take (hrd rd hl hmL) m) hstep
    (R := RegionL ((b, piW rm ps m) :: L)) (fun i hi => by
      rcases hi with hi | hi
      · exact regionL_head hi.1 (by rw [piW_length]; omega)
      · exact regionL_cons _ (hR i hi)) (m - 2) 1 (by omega) le_rfl
  rw [← hglm, pow_one, ← word_gen] at h
  exact h

/-- **The terminal's callees' bounds**: the four prefix chains `Beqc`, `__loop14` `32·K15` and its
frame (its frame alone when skipped), `selector_tables` its frame and buffers, each column selector `Bcs`,
`ring_switch_weight` its frame, its chain (`64·35`) and `rs_eq_run`'s `Brs`. -/
def termBs (fs : String → ℕ) (Beqc K15 Bcs Brs : ℕ) : List ℕ :=
  [Beqc, Beqc, (32 * K15 + fs "__loop14"), fs "selector_tables" + 512] ++
    List.replicate Tables.nCommittedCols Bcs ++ [Beqc, fs "ring_switch_weight" + 2240 + Brs, Beqc]

theorem termBs_sum (fs : String → ℕ) (Beqc K15 Bcs Brs : ℕ) :
    (termBs fs Beqc K15 Bcs Brs).sum = 4 * Beqc + (32 * K15 + fs "__loop14") +
      (fs "selector_tables" + 512) + 94 * Bcs + (fs "ring_switch_weight" + 2240 + Brs) := by
  simp only [termBs, List.sum_append, List.sum_cons, List.sum_nil, List.sum_replicate,
    smul_eq_mul, Tables.nCommittedCols]
  omega

set_option maxHeartbeats 1000000 in
/-- **The terminal's callees are complete, placed, within `termBs`** (`termKids_complete`). -/
theorem termKids_completeB (κ : ℕ) (hκ : 6 ≤ κ) (Lin : Main.Layout) (D : TermData) (b0 : ℕ)
    (hreg : ∀ i, TermRegion D.B D.zs.length D.chis.length D.τ D.ood.length i → RegionL Lin i)
    (hzl : D.zs.length ≤ 34) (hcl : D.chis.length ≤ 34) (hxl : D.x.length ≤ 32)
    (hτ : D.τ + 6 ≤ 34) (hol : D.outPt.length = D.τ + 6) (hrl : D.ringPoint.length = D.τ + 6)
    (hcf : D.coeffs.length = 64) (hgmu : D.gmu = gen ^ D.zs.length)
    (hgz : D.gzcn = gen ^ D.chis.length) (hglm : D.glm = gen ^ D.m) (hgtau : D.gtau = gen ^ D.τ)
    (_hm1 : 1 ≤ D.m) (hm : D.m ≤ 32) (hKC : ∀ c < Tables.nCommittedCols, D.KC.getD c 0 < 31)
    (hOF : ∀ c < Tables.nCommittedCols, D.OF.getD c 0 < 2 ^ 32 ∧ 2 ^ D.KC.getD c 0 ∣ D.OF.getD c 0)
    (hrd : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex D.B.zeta)) D.zs ∧
      ReadsAt rd (ofK (addressOfIndex D.B.chi)) D.chis ∧ ReadsAt rd (ofK (addressOfIndex D.B.zv))
          D.outPt ∧
      ReadsAt rd (ofK (addressOfIndex D.B.pt1)) (p1Of D.x))
    (hodl : D.ood.length ≤ 30) (hgm : D.gm = gen ^ D.ood.length)
    (hrdO : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex D.B.oz)) D.ood)
    {Beqc K15 Bcs Brs : ℕ} (hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ => Beqc)
    (hL15 : TotalLeOn coreProgram fs "__loop14" LoopPre
      fun a => logG (a.getD 1 0) * K15 + fs "__loop14")
    (hCsF : ∀ κ' < 31, fs (Tables.lName "column_selector" κ') ≤ Bcs)
    (hrs : ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a => a.getD 3 0 = gen ^ c)
      fun _ => Brs) :
    KidsDepB fs cert κ (termKids Lin D b0) (termBs fs Beqc K15 Bcs Brs) := by
  have hpl : (p1Of D.x).length = 40 := p1Of_length (by simp only [termPointCap]; omega)
  have hpt : (padPoint D.x).length = 40 := padPoint_length (by simp only [termPointCap]; omega)
  have hw64 : word 64 0 = gen ^ 6 := word_two_pow (a := 6) (by decide)
  unfold termKids termBs
  refine KidsDepB.append (KidsDepB.append ?_ ?_) ?_
  · refine ⟨fun pv => ⟨fun _ => ?_, fun h => by simp at h⟩, fun pv => ⟨fun _ => ?_, fun h => by simp at h⟩,
      fun pv => ⟨fun ht => ?_, fun _ => Nat.le_add_left _ _⟩,
      fun pv => ⟨fun _ => ?_, fun h => by simp at h⟩, trivial⟩
    · exact eqc_kid_completeB κ hκ (by omega) (by simp; omega) hgmu
        (fun rd hl hm => ⟨(hrd rd hl hm).1, readsAt_take (hrd rd hl hm).2.2.2 _⟩)
        (fun i hi => hreg i (by
          rcases hi with hi | hi
          · exact Or.inl hi
          · simp only [TermRegion]; omega)) hEqc
    · exact eqc_kid_completeB κ hκ (by omega) (by simp; omega) hgz
        (fun rd hl hm => ⟨(hrd rd hl hm).2.1, readsAt_take (hrd rd hl hm).2.2.2 _⟩)
        (fun i hi => hreg i (by simp only [TermRegion]; omega)) hEqc
    · have hne : word 2 0 + D.glm ≠ 0 := by simpa using ht
      have hm2 : 2 ≤ D.m := by
        by_contra h
        apply hne
        rw [hglm, show D.m = 1 by omega, word_gen, pow_one]
        exact e_add_self _
      exact (l15_kid_completeB κ hm2 (by omega) hglm (by omega)
        (fun rd hl hm => (hrd rd hl hm).2.2.2)
        (fun i hi => hreg i (by simp only [TermRegion]; omega)) hL15).mono le_rfl
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ hm) _)
    · exact ((Tables.selector_tables_completeAtB fs cert κ _ _ _ _ (by simp [pt32]; omega)
        (by simp [pt132]; omega)).toCompleteAtB).mono le_rfl (by simp)
  · have h : KidsDepB fs cert κ ((List.range Tables.nCommittedCols).map (selKid D))
        (List.replicate ((List.range Tables.nCommittedCols).map (selKid D)).length Bcs) := by
      refine kidsDepB_replicate fun k hk pv => ?_
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
      exact (cs_completeAtB κ (by omega) (hKC c hc) (hOF c hc).1 (hOF c hc).2
        (by simp [pt32]; omega) (by simp [pt132]; omega)).mono le_rfl (hCsF _ (hKC c hc))
    rwa [List.length_map, List.length_range] at h
  · refine ⟨fun pv => ⟨fun _ => ?_, fun h => by simp at h⟩,
      fun pv => ⟨fun _ => ?_, fun h => by simp at h⟩,
      fun pv => ⟨fun _ => ?_, fun h => by simp at h⟩, trivial⟩
    · have e : D.gtau * word 64 0 = gen ^ D.outPt.length := by rw [hgtau, hw64, ← pow_add, hol]
      show CompleteAtB fs cert κ "eq_prefix_chain" _
        [ofK (addressOfIndex (b0 + 105)), word 1 0, ofK (addressOfIndex D.B.zv), ofK
            (addressOfIndex D.B.pt1),
          D.gtau * word 64 0] (Returns []) _
      exact eqc_kid_completeB κ hκ (by omega) (by simp; omega) e
        (fun rd hl hm => ⟨(hrd rd hl hm).2.2.1, readsAt_take (hrd rd hl hm).2.2.2 _⟩)
        (fun i hi => hreg i (by simp only [TermRegion]; omega)) hEqc
    · have e1 : ofK (addressOfIndex D.B.zv) * word 549755813888 0 = ofK (addressOfIndex (D.B.zv +
        39)) := by
        rw [show (549755813888 : ℕ) = 2 ^ 39 by norm_num, word_two_pow (by decide), ofK_gpow_mul_gen]
      have e2 : D.gtau * word 64 0 = gen ^ (D.τ + 6) := by rw [hgtau, hw64, ← pow_add]
      show CompleteAtB fs cert κ "ring_switch_weight" _
        [ofK (addressOfIndex D.B.zv) * word 549755813888 0, ofK (addressOfIndex D.B.pt1), ofK
            (addressOfIndex D.B.ct),
          D.gtau * word 64 0] _ _
      rw [e1, e2]
      exact (rsw_completeAtB κ (by omega) hrl (by simp; omega) hcf (hrs _ hτ)).mono le_rfl
        (by omega)
    · exact eqc_kid_completeB κ hκ (by omega) (by simp; omega) hgm
        (fun rd hl hm => ⟨hrdO rd hl hm, readsAt_take (hrd rd hl hm).2.2.2 _⟩)
        (fun i hi => hreg i (by simp only [TermRegion]; omega)) hEqc

/-! ## The terminal -/

/-- The terminal's bound (`check_opening_terminal_completeAtB`'s). -/
def termBound (fs : String → ℕ) (Beqc K15 Bcs Brs : ℕ) : ℕ :=
  fs "check_opening_terminal" + 177 + 4 * Beqc + (32 * K15 + fs "__loop14") +
    (fs "selector_tables" + 448) + 94 * Bcs + (fs "ring_switch_weight" + 2240 + Brs)

set_option maxHeartbeats 1000000 in
/-- **`check_opening_terminal` is complete, placed, within a bound**
(`check_opening_terminal_completeAt` with its size at most
`fs "check_opening_terminal" + 177 + 4·Beqc + (32·K15 + fs "__loop14") + (fs "selector_tables"
+ 512) + 94·Bcs + (fs "ring_switch_weight" + 2240 + Brs)` at every frame pointer, before the
memory): its frame, its buffers (`35 + 35 + 35 + 41 + 31`) and its callees' bounds (`termBs`), the pure
callees' words by the hypotheses `hEqc`, `hL15`, `hCsF`, `hrs`. -/
theorem check_opening_terminal_completeAtB (κ : ℕ) (hκ : 6 ≤ κ) (B : TermBases)
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
    (hL15 : TotalLeOn coreProgram fs "__loop14" LoopPre
      fun a => logG (a.getD 1 0) * K15 + fs "__loop14")
    (hCsF : ∀ κ' < 31, fs (Tables.lName "column_selector" κ') ≤ Bcs)
    (hrs : ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a => a.getD 3 0 = gen ^ c)
      fun _ => Brs) :
    CompleteAtB fs cert κ "check_opening_terminal" Lin
      (termArgs B rm gmu gzcn glm gtau lamCl inner yr target gm) (Returns [])
      (fs "check_opening_terminal" + 177 + 4 * Beqc + (32 * K15 + fs "__loop14") +
        (fs "selector_tables" + 512) + 94 * Bcs + (fs "ring_switch_weight" + 2240 + Brs)) := by
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  swap
  · intro fp
    exact ⟨0, [], [], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
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
  refine (completeAt_flatDepRB find_term term_not_loop κ Lin _ [] term_body' term_flat term_addrs
    (by decide +kernel)
    [35, 35, 35, 41, 31] (fun _ => termOwn D) (fun _ => ?_)
    (fun fp => termKids Lin D (fp + fs "check_opening_terminal")) (termBs fs Beqc K15 Bcs Brs)
    (fun fp => ?_)
    (fun fp outs _ => termKids_regions Lin D _ hreg' f1 f2 f3 f4 outs)
    (fun fp outs _ rd hl hB hLin hLo => ?_) (fun fp outs hlen' ho rd hl hB hLin _ => ?_)).mono le_rfl
    (le_of_eq ?_)
  · simp only [termOwn, List.forall₂_cons, eqChain_length, piW_length,
      List.Forall₂.nil, and_true]
    have hol : out.point.length = τ + 6 := by rw [hopl, Tables.qkeccakSlotBits_eq]
    show bus.point.length + 1 ≤ 35 ∧ chis.length + 1 ≤ 35 ∧ layout.logMemory + 1 ≤ 35 ∧
      out.point.length + 1 ≤ 41 ∧ oodPoint.length + 1 ≤ 31
    omega
  · refine termKids_completeB κ hκ Lin D _ hreg' hbus f7 f4 f1 f5 f2 f3 hgmu hgzc hglm hgtau hlm1
      hlm32 (fun c hc => ?_) (fun c hc => ?_)
      (fun rd hl hm => ?_) f8 f9 (fun rd hl hm => ?_) hEqc hL15 hCsF hrs
    · have := hK c hc; show KC.getD c 0 < 31; omega
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
