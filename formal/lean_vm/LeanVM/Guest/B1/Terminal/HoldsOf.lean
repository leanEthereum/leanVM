/-
  LeanVM.Guest.B1.Terminal.HoldsOf

  **`check_opening_terminal` is sound** (G:3460-3547; TRIAGE #70), given its callees' meanings.
-/

module

public import LeanVM.Guest.B1.Terminal.Support
public import LeanVM.Guest.B1.Ring.Interface

/-!
# `check_opening_terminal`, assembled

The body is the template (`termFound`); its head gives the chains, the slot points, the public
input's chain, the base `kappa_base` and the selector tables, its selectors' blocks each committed
column's selector (`Terminal/Support`, the offsets aligned by `stackOffsets_dvd`), its claims'
blocks the sum of the claims' terms at their powers of `λ` (`claimsT_sound`), each its batched
weight (`claimTerm_eq`), and its tail the outputs' claim, the ring switch's and the out-of-domain
claim's chain, seeded with the next power of `λ` (`chain_value_seed`); with `stackWeight_eq` the
last check is the WHIR terminal.

The callees' meanings are hypotheses here (`eq_prefix_chain_Spec`, `ring_switch_weight_Spec`,
discharged in `Terminal/Holds`), as are B1-c's selectors (`column_selector_Spec`,
`selector_tables_Spec`); `column_selector`'s holds on a memory image of at most `2^32` words.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier Finset

@[expose] public section

theorem kapT_noRet (src adj r : ℕ) : Stmt.noRetList (kapT src adj r).1 = true := by
  unfold kapT; split <;> rfl

theorem selBlockT_noRet (c : ℕ) : Stmt.noRetList (selBlockT c) = true := by
  simp only [selBlockT, noRetList_append, selKap, kapT_noRet]; rfl

theorem claimT_noRet (j r acc lr : ℕ) : Stmt.noRetList (claimT j r acc lr).1 = true := by
  unfold claimT
  split <;> simp only [noRetList_append, claimKap, kapT_noRet] <;> rfl

theorem claimsT_noRet :
    ∀ (js : List ℕ) (r acc lr : ℕ), Stmt.noRetList (claimsT js r acc lr).1 = true
  | [], _, _, _ => rfl
  | j :: js, r, acc, lr => by
    simp only [claimsT, noRetList_append, claimsT_noRet js, claimT_noRet, Bool.and_true]

theorem getD_take_nat {l : List ℕ} {n k : ℕ} (h : k < n) : (l.take n).getD k 0 = l.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The base's words are the `g`-powers of its exponents. -/
theorem kb_words {lm : ℕ} {hs : List ℕ} (hl : hs.length = 6) {i : ℕ} (hi : i < 8) :
    (1 :: gen ^ lm :: hs.map (gen ^ ·))[i]'(by simp [hl]; omega) =
      gen ^ ([0, lm] ++ hs).getD i 0 := by
  have e : (1 :: gen ^ lm :: hs.map (gen ^ ·)) = ([0, lm] ++ hs).map (gen ^ ·) := by
    simp
  simp only [e, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by simp [hl]; omega)]

/-- The base's eight loads. -/
theorem kb_loads {rd : Reader} {p : E} {σ : Val} (k0 : LoadHolds rd p 0 (σ (.n 35)))
    (k1 : LoadHolds rd p 1 (σ (.n 36))) (k2 : LoadHolds rd p 2 (σ (.n 37)))
    (k3 : LoadHolds rd p 3 (σ (.n 38))) (k4 : LoadHolds rd p 4 (σ (.n 39)))
    (k5 : LoadHolds rd p 5 (σ (.n 40))) (k6 : LoadHolds rd p 6 (σ (.n 41)))
    (k7 : LoadHolds rd p 7 (σ (.n 42))) : ∀ i < 8, LoadHolds rd p i (σ (.n (kbV i)))
  | 0, _ => k0
  | 1, _ => k1
  | 2, _ => k2
  | 3, _ => k3
  | 4, _ => k4
  | 5, _ => k5
  | 6, _ => k6
  | 7, _ => k7
  | _ + 8, h => absurd h (by omega)


/-- The claims kept before `j + 1`. -/
theorem poolRank_succ {j : ℕ} (hj : j < 159) :
    poolRank (j + 1) = poolRank j + if termKind j < 4 then 1 else 0 := by
  unfold poolRank
  rw [List.range_succ, List.filter_append, List.length_append]
  congr 1
  have h5 := termKind_lt hj
  by_cases h : termKind j = 4
  · have hm := (claimCol_out hj).mpr h
    have hk : ¬ termKind j < 4 := by omega
    simp only [List.filter_cons, List.filter_nil, hm, not_true_eq_false, decide_false,
      Bool.false_eq_true, ↓reduceIte, hk, List.length_nil]
  · have hm : Tables.claimColumns.getD j 0 ∉ keccakOutputColumns :=
      fun hm ↦ h ((claimCol_out hj).mp hm)
    have hk : termKind j < 4 := by omega
    simp only [List.filter_cons, List.filter_nil, hm, not_false_eq_true, decide_true,
      ↓reduceIte, hk, List.length_singleton]

/-- **`check_opening_terminal` is sound**, given its callees' meanings and B1-c's selectors, on a
memory image of at most `2^32` words. -/
theorem check_opening_terminal_holds_of (hep : eq_prefix_chain_Spec)
    (hrsw : ring_switch_weight_Spec) (hcs : Tables.column_selector_Spec)
    (hst : Tables.selector_tables_Spec) {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) :
    check_opening_terminal_Spec Lm.read := by
  intro args rets h
  obtain ⟨fn, hf, hpar0, hbody⟩ := termFound
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem hf args rets).mp h
  rw [hpar0] at hpar
  simp only [termParams, List.map_cons, List.map_nil] at hpar
  subst hpar
  rw [hbody, termT, holdsList_append, holdsList_append, holdsList_append] at hb
  simp only [termHeadT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨-, e21, hcz, -, e23, hcr, e24, e25, -, -, -, l28, e29, l29, e30, e31, e32, -, hloop, e33,
    l34, k0, k1, k2, k3, k4, k5, k6, k7, hstc, hb⟩ := hb
  change Stmt.HoldsList _ _ σ ((List.range Tables.nCommittedCols).map selBlockT).flatten _ _ at hb
  rw [holdsList_range_flatten Tables.nCommittedCols selBlockT selBlockT_noRet] at hb
  obtain ⟨hsels, hb⟩ := hb
  rw [holdsList_noRet termClaims.1 (claimsT_noRet _ _ _ _)] at hb
  obtain ⟨hcl, hb⟩ := hb
  rw [termClaims_end] at hb
  simp only [termTailT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    Nat.reduceAdd] at hb
  obtain ⟨-, e1695, e1696, e1697, hco, e1698, e1699, e1700, e1701, hrw, e1703, l1704, e1705,
    e1706, e1707, e1708, -, e1710, hood, e1711, l1712, e1713, e1714, afin, hret⟩ := hb
  refine ⟨hret.symm, ?_⟩
  intro layout bus claims out lam ringPoint coeffs oodPoint x hpre
  simp only [TermPre] at hpre
  obtain ⟨hT, hPC, -, hP, hSL, hSL28, hlm1, -, hbus40, hHL, -, hglm, hgtau, hkbR, hgt, hlamC,
    hoc, hopl, hoz, hrpl, hrp, hcfl, hct, hxl, hpt, hpt1, hodl, hodR, hgm⟩ := hpre
  obtain ⟨chis, hzR, hgmu, hchR, hgzc, hchL, -, hcols, hpts⟩ := hT
  obtain ⟨hkap, hOr⟩ := hPC
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  -- names
  set kappas := columnKappas layout.logMemory Tables.guestLogBytecode layout.tableLogHeights
    with hkdef
  set KC := Tables.committedKappas kappas with hKCdef
  set τ := layout.tableLogHeights.getD opKeccak 0 with hτ
  have hKC : KC = (List.range Tables.nCommittedCols).map fun c ↦
      (0 :: layout.logMemory :: layout.tableLogHeights).getD (Tables.colKappaSrc c) 0 +
        Tables.colKappaAdj c :=
    Tables.committedKappas_columnKappas layout.logMemory layout.tableLogHeights hHL
  have hKClen : KC.length = Tables.nCommittedCols := Tables.committedKappas_length _ hkap
  have hLdef : layout.stackLog = max Whir.minLogStack (stackOffsets KC).2 := by
    rw [hSL, placementsOf_snd]
  have hK : ∀ c < Tables.nCommittedCols, KC.getD c 0 ≤ layout.stackLog := fun c hc ↦ by
    have := size_le_stackOffsets KC (i := c) (by omega); rw [hLdef]; omega
  have hO : ∀ c, (stackOffsets KC).1.getD c 0 < 2 ^ layout.stackLog := fun c ↦
    lt_of_lt_of_le (stackOffsets_lt KC c) (Nat.pow_le_pow_right (by decide) (by rw [hLdef]; omega))
  -- the base
  have hkb : ∀ i < 8, σ (.n (kbV i)) = gen ^ kbExp layout i := by
    intro i hi
    have hk := kb_loads k0 k1 k2 k3 k4 k5 k6 k7 i hi
    have hr := hkbR i (by simp [hHL]; omega)
    rw [kb_words hHL hi] at hr
    exact loadHolds_unique hk hr
  have hKCv : ∀ c < Tables.nCommittedCols, KC.getD c 0 =
      kbExp layout (Tables.colKappaSrc c) + Tables.colKappaAdj c := fun c hc ↦ by
    rw [hKC, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]
    rfl
  have hsrc8 : ∀ c, Tables.colKappaSrc c < 8 := fun c ↦ by
    unfold Tables.colKappaSrc; split_ifs <;> omega
  have hkapc : ∀ c < Tables.nCommittedCols,
      σ (.n (kbV (Tables.colKappaSrc c))) * gen ^ Tables.colKappaAdj c = gen ^ KC.getD c 0 :=
    fun c hc ↦ by rw [hkb _ (hsrc8 c), hKCv c hc, pow_add]
  have hoff' : ∀ c < Tables.nCommittedCols,
      LoadHolds Lm.read (σ (.n 10)) c (gen ^ (stackOffsets KC).1.getD c 0) := fun c hc ↦ by
    have hl : c < (stackOffsets KC).1.length := by rw [stackOffsets_length]; omega
    have := hOr c (by simpa using hl)
    rw [List.getElem_map] at this
    rw [List.getD_eq_getElem _ _ hl]; exact this
  have hselc := fun c (hc : c < Tables.nCommittedCols) ↦ sel_value hcs hst hμ Lm (hsels c hc) hstc
    hgt (hkapc c hc) (hoff' c hc) (stackOffsets_dvd KC c) (hK c hc) hSL28 (hO c) hxl hpt hpt1
  -- sizes
  have hk5 : kappas.take 5 = [layout.logMemory, layout.logMemory, layout.logMemory,
      Tables.guestLogBytecode, τ + 6] := kappas_small hHL
  have hksmall : ∀ c < 5, kappas.getD c 0 =
      [layout.logMemory, layout.logMemory, layout.logMemory, Tables.guestLogBytecode,
        τ + 6].getD c 0 := fun c hc ↦ by
    rw [← hk5, getD_take_nat hc]
  have hK4 : KC.getD 4 0 = τ + 6 := by
    rw [committedKappas_small hkap (by decide), hksmall 4 (by decide)]; rfl
  have hmem : ∀ c < 3, KC.getD c 0 = layout.logMemory := fun c hc ↦ by
    rw [committedKappas_small hkap (by omega), hksmall c (by omega)]
    interval_cases c <;> rfl
  have hK4L := hK 4 (by decide)
  rw [hK4] at hK4L
  have hxl40 : x.length ≤ termPointCap := by simp only [termPointCap]; omega
  have hpl40 : ((padPoint x).map (1 + ·)).length = termPointCap := by
    simp [padPoint_length hxl40]
  -- the chains
  rw [e21, word_one] at hcz
  rw [e23, word_one] at hcr
  have hzc := chain_value ((hep _ _ _).mp hcz) hgmu hbus40 hzR hxl40 hpt1
  have hrc := chain_value ((hep _ _ _).mp hcr) hgzc (by omega) hchR hxl40 hpt1
  -- the slot points
  have hs1 : ∀ k < 6, valOf Lm.read (σ (.n 24)) k = x.getD (τ + k) 0 := fun k hk ↦ by
    have l := readsAt_getD hpt (k := τ + k)
      (by rw [padPoint_length hxl40]; simp only [termPointCap]; omega)
    rw [← loadHolds_mul_gen_pow, ← hgtau, ← e24] at l
    rw [valOf_eq l, padPoint_getD]
  have hs0 : ∀ k < 6, valOf Lm.read (σ (.n 25)) k = 1 + x.getD (τ + k) 0 := fun k hk ↦ by
    have l := readsAt_getD hpt1 (k := τ + k) (by rw [hpl40]; simp only [termPointCap]; omega)
    rw [← loadHolds_mul_gen_pow, ← hgtau, ← e25] at l
    rw [valOf_eq l, x1_getD hxl40 (by simp only [termPointCap]; omega)]
  -- the public input's chain
  have hlmL : layout.logMemory ≤ layout.stackLog := by
    have := hK 0 (by decide); rw [hmem 0 (by decide)] at this; exact this
  have hstep : ∀ k, 1 ≤ k → k < layout.logMemory →
      PiStep Lm.read (σ (.n 26)) (σ (.n 14)) (gen ^ k) := by
    intro k hk1 hk2
    have hne : σ (.n 31) ≠ 0 := by
      rw [e31, e30, word_gen, hglm]
      intro h0
      have := gen_pow_inj_le (a := 1) (b := layout.logMemory) (by omega) (by omega)
        (by rw [pow_one]; exact e_add_eq_zero_iff.mp h0)
      omega
    have hc : coreProgram.Rel Lm.read "__loop14"
        (gen ^ 1 :: [σ (.n 6), σ (.n 26), σ (.n 14)]) [] := by
      rw [pow_one, ← word_gen, ← e32]; exact hloop hne
    exact loop_sound (P := coreProgram) (f := "__loop14") (ps := [σ (.n 6), σ (.n 26), σ (.n 14)])
      (N := σ (.n 6)) (B := PiStep Lm.read (σ (.n 26)) (σ (.n 14))) (m := layout.logMemory)
      (fun d y h ↦ loop15_step d y _ _ _ h) hglm (by unfold ordG; omega) 1 hc k hk1 hk2
  have hx1_0 := loadHolds_unique l28 (readsAt_getD hpt1 (k := 0) (by rw [hpl40]; decide))
  have h1 : LoadHolds Lm.read (σ (.n 26)) 1 (σ (.n 3) + ((padPoint x).map (1 + ·)).getD 0 0) := by
    rw [← hx1_0, ← e29]; exact l29
  have hpi := piChain_value hpt1 (m := layout.logMemory)
    (by rw [hpl40]; simp only [termPointCap]; omega) h1 hstep layout.logMemory hlm1 le_rfl
  rw [e33, hglm, loadHolds_mul_gen_pow, Nat.add_zero] at l34
  have h34 : σ (.n 34) = eqEval (σ (.n 3) :: List.replicate (layout.logMemory - 1) 0)
      (x.take layout.logMemory) := by
    rw [loadHolds_unique l34 hpi, x1_getD hxl40 (by decide), ← piChain_eq hlm1 (by omega)]
    refine congrArg (_ * ·) (prod_congr rfl fun i hi ↦ ?_)
    rw [x1_getD hxl40 (by have := (mem_Ico.mp hi).2; simp only [termPointCap]; omega)]
  -- the claims' points and the batching powers
  have hclen : claims.length = 159 := by
    rw [← List.length_map (f := (·.column)), hcols, claimColumns_eq]; simp
  have hptj : ∀ j < 159, (claims.map (·.point))[j]? = some (claims.getD j default).point :=
    fun j hj ↦ by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega),
        List.getD_eq_getElem _ _ (by omega)]
      rfl
  rw [termClaims, List.range_eq_range'] at hcl
  obtain ⟨hsum, hlamO, -⟩ := claimsT_sound (C := coreProgram.Rel Lm.read) hkb (rk := poolRank)
    hlamC 159 0 claimsStart 15 9 (fun j hj ↦ poolRank_succ (by omega))
    (by rw [hlamC]; simp [poolRank]) hcl
  rw [show (claimsT (List.range' 0 159) claimsStart 15 9).2 = (1694, 1692, 1693) by
    rw [← termClaims_end, termClaims, List.range_eq_range']] at hsum hlamO
  simp only [zero_add] at hsum hlamO
  have hmem0 : (layout.placement memory0).variableCount = layout.logMemory := by
    have := placement_committed hkap hP (cc := 0) (by decide)
    rw [committedCols_getD (by decide)] at this
    rw [show memory0 = 0 from rfl, show colOfCommitted 0 = 0 from rfl] at *
    rw [this, hmem 0 (by decide)]
  have T : ClaimsCtx Lm.read σ layout kappas claims bus.point chis x (σ (.n 3)) :=
    { hkap := hkap, hKC := hKC, hP := hP, hx := hxl, hL := hSL28, hK := hK,
      hq := stackOffsets_dvd KC 4, hK4 := hK4,
      hlane := fun g h1 h2 ↦ kappas_keccak hHL (by omega) (by omega), hmem := hmem,
      hlm := hlm1, hmem0 := hmem0, hcols := hcols, hzs := hbus40, hchis := hchL,
      hpz := fun j hj ↦ (hpts j _ (hptj j (by omega))).2.1 hj,
      hpc := fun j h1 h2 ↦ (hpts j _ (hptj j (by omega))).2.2.1 h1 h2,
      hpp := fun j h1 h2 ↦ (hpts j _ (hptj j h2)).2.2.2 h1,
      hlen := fun j hj ↦ (hpts j _ (hptj j (by omega))).1 hj,
      hsel := fun c hc ↦ hselc c hc,
      hzc := fun n h1 h2 ↦ hzc n h1 (by rw [hxl]; exact h2),
      hrc := fun n h1 h2 ↦ hrc n h1 (by rw [hxl]; exact h2),
      hs1 := hs1, hs0 := hs0, hpi := h34 }
  -- the tail: the outputs' claim and the ring switch's
  have hq4 := placement_committed hkap hP (cc := 4) (by decide)
  rw [committedCols_getD (by decide), show colOfCommitted 4 = 4 from rfl] at hq4
  have hw64 : word 64 0 = gen ^ 6 := word_two_pow (a := 6) (by decide)
  have h1697 : σ (.n 1697) = gen ^ out.point.length := by
    rw [e1697, e1696, hw64, hgtau, ← pow_add, hopl, Tables.qkeccakSlotBits_eq]
  rw [e1695, word_one, h1697] at hco
  have hoL : out.point.length = τ + 6 := by rw [hopl, Tables.qkeccakSlotBits_eq]
  have hoc' := chain_value ((hep _ _ _).mp hco) rfl (by omega) hoz hxl40 hpt1
  rw [e1703, hgtau, loadHolds_mul_gen_pow] at l1704
  have h1704 : σ (.n 1704) = eqEval out.point (x.take (τ + 6)) := by
    rw [eq_valOf l1704, show τ + 6 = out.point.length from hoL.symm, hoc' _ le_rfl (by omega),
      List.take_of_length_le le_rfl]
  obtain ⟨n, hn, hng, rs, ps, cs, hrsl, hpsl, hcsl, hrsR, hpsR, hcsR, hret'⟩ :=
    hrsw _ _ _ hrw
  have hn6 : n = τ + 6 := by
    rw [e1701, e1700, hw64, hgtau, ← pow_add] at hng
    exact gen_pow_inj_le (by omega) (by omega) hng.symm
  subst hn6
  rw [e1699, e1698, show (549755813888 : ℕ) = 2 ^ 39 from rfl, word_two_pow (by decide)] at hrsR
  have hrs : rs = ringPoint :=
    readsAt_unique hrsR hrp (by rw [hrsl, hrpl, Tables.qkeccakSlotBits_eq])
  have hps : ps = ((padPoint x).map (1 + ·)).take (τ + 6) :=
    readsAt_unique hpsR (readsAt_take hpt1 _)
      (by rw [hpsl, List.length_take, hpl40]; simp only [termPointCap]; omega)
  have hcs : cs = coeffs := readsAt_unique hcsR hct (by rw [hcsl, hcfl])
  simp only [List.cons.injEq, and_true] at hret'
  rw [hrs, hps, hcs, map_one_take (by omega)] at hret'
  -- the out-of-domain claim, its chain seeded with the next power of `λ`
  rw [e1710, hlamO, hlamC, hgm] at hood
  have hodc := chain_value_seed ((hep _ _ _).mp hood) (A := oodPoint) (by rw [hodl])
    (by omega) hodR hxl40 hpt1
  rw [e1711, hgm, loadHolds_mul_gen_pow, Nat.add_zero] at l1712
  have h1712 : σ (.n 1712) = lam ^ (1 + poolRank 159) * lam * eqEval oodPoint x := by
    rw [eq_valOf l1712, hodc _ (by rw [hodl]) (by rw [hxl]), List.take_of_length_le hodl.le,
      List.take_of_length_le hxl.le]
  -- the terminal check
  have hfin : σ (.n 1714) = σ (.n 17) := e_add_eq_zero_iff.mp afin
  rw [stackWeight_eq layout out ringPoint coeffs oodPoint lam x hcols, ← hfin, e1714, e1713, h1712,
    e1708, hsum, e1707, e1706, e1705, hret', h1704, hlamO]
  rw [sum_congr rfl fun j hj ↦ claimTerm_eq T (mem_range.mp hj),
    ringClaim_eq (show layout.placement qkeccak = _ from hq4) hxl,
    wOf_committed (by rw [hoc]; exact hq4) (by rw [hoL, hK4]) hxl (hK 4 (by decide)),
    hselc 4 (by decide), hK4]
  ring

end
end LeanVM.Guest.B1.VerifySub
