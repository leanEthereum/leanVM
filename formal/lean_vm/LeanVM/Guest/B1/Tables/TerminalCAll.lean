/-
  LeanVM.Guest.B1.Tables.TerminalCAll

  `check_opening_terminal` complete (TRIAGE #42, #43): its segments in sequence over the honest
  memory, the check from the opening's acceptance.
-/

module

public import LeanVM.Guest.B1.Tables.TerminalCTail

/-!
# `check_opening_terminal`, complete

`check_opening_terminal_rel`: under the terminal's precondition (`TermPre`), each claim's point
of its column's log (`hlens`, the conjunct `TermPreAcc` adds), the opening accepting the stacked
weight and the honest memory (`TermMem`), `check_opening_terminal` holds. The segments complete
in sequence; `terminal_val` gives the value the check compares, and the acceptance makes it hold.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig

@[expose] public section

section
variable {rd : Reader}

/-- A prefix chain has a word at every index up to its length. -/
theorem chain_word {ch s a b : E} {n : ℕ} (hn : n < 33)
    (h : MeaningEqPrefixChain rd [ch, s, a, b, gen ^ n] []) {i : ℕ} (hi : i ≤ n) :
    ∃ v, LoadHolds rd ch i v := by
  obtain ⟨-, m, hm, hN, as, bs, -, -, -, -, hc⟩ := h
  have hmn : m = n := (gen_pow_inj (by omega) hm hN).symm
  exact ⟨_, hc i (by omega)⟩

/-- `Completes`, the block's relation recorded in its postcondition. -/
theorem Completes.withHolds {C : CallRel} {lo hi : ℕ} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : Completes C rd lo hi ss σ P) : Completes C rd lo hi ss σ (fun σ' => P σ' ∧
      Ext lo hi σ σ' ∧ ∀ (next : Prop) (kret : List E → Prop), next → Stmt.HoldsList C rd σ' ss next kret) :=
  let ⟨σ', he, hp, hh⟩ := h; ⟨σ', he, ⟨hp, he, hh⟩, hh⟩

theorem claimV_mono : ∀ j < 112, claimV.getD j 0 ≤ claimV.getD (j + 1) 0 := by decide +kernel

theorem claims_below : ∀ j < 112,
    numBelowB (claimV.getD (j + 1) 0) (Stmt.valsList (claimBlk j)) = true := by decide +kernel

theorem sel_below : ∀ c < 92, numBelowB (36 + 3 * (c + 1)) (Stmt.valsList (selBlk c)) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- **`check_opening_terminal`'s body completes** under its precondition, each claim's
point of its column's log, the opening accepting the stacked weight, and the honest memory. -/
theorem term_body_complete {layout : Layout} {bus : BusResult} {claims : List ColumnClaim}
    {lam : E} {fp cs : List E} {w : WhirEnd}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 p17 p19 p21 p25 p1750 : E}
    (hpre : TermPre TCtx PCtx rd layout bus claims lam fp cs w
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16])
    (hlens : ∀ j (p : List E), (claims.map (·.point))[j]? = some p →
      p.length = (layout.placements.getD (claimColumns.getD j 0) default).vars)
    (hacc : w.Accepts (stackWeight layout claims fp cs lam))
    (hM : TermMem rd [p17, p19, p21, p25, p1750]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16]) :
    ∃ σ : Val, (Fn.params Data.core14).map σ =
        [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16] ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (Fn.body Data.core14) False (fun rs => rs = []) ∧
      σ (.n 17) = p17 ∧ σ (.n 19) = p19 ∧ σ (.n 21) = p21 ∧ σ (.n 25) = p25 ∧
      σ (.n 1750) = p1750 := by
  have hpre' := hpre
  obtain ⟨hT, hP, -, hglm, hgtau, hlp, hzv, hct, hpt, hin, hyr, hst, hpl, hsl, hμ28, hlm1, hbp,
    hxl, hfpl, hcsl⟩ := hpre
  obtain ⟨chis, hzeta, hgmu, hchi, hgzcn, hchl, hcl, hcols, hpts⟩ := hT
  obtain ⟨hkl, hkap, hoff⟩ := hP
  have hM' := hM
  obtain ⟨c17, c19, c21, -, -, hrs, -⟩ := hM'
  generalize hkps : columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights = kps
    at hkl hkap hoff hpl hsl
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℕ, ∀ c, K c = (committedKappas kps).getD c 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : ℕ → ℕ, ∀ c, O c = offAt kps c := ⟨_, fun _ => rfl⟩
  have hcl92 : (committedKappas kps).length = 92 := committedKappas_length _ hkl
  have hlog : log2Ceil (stackTotal kps) ≤ layout.stackLog := by
    rw [hsl, placementsOf_snd]; exact le_max_right _ _
  have hKμ : ∀ c < 92, K c ≤ layout.stackLog := fun c hc => by
    rw [hK]
    exact le_trans (le_log2Ceil_of_two_pow_le
      (stackTotal_eq kps ▸ single_le_sum_map _ c (by omega))) hlog
  have hOμ : ∀ c < 92, O c < 2 ^ layout.stackLog := fun c hc => by
    have h1 := stackOffsets_bound (committedKappas kps) (c := c) (by omega)
    have h2 := Nat.one_le_two_pow (n := (committedKappas kps).getD c 0)
    rw [← stackTotal_eq] at h1
    have htot : stackTotal kps ≤ 2 ^ layout.stackLog :=
      le_trans (le_two_pow_log2Ceil _) (Nat.pow_le_pow_right (by norm_num) hlog)
    rw [hO, offAt]
    omega
  have hrO : ∀ c < 92, LoadHolds rd a9 c (gen ^ O c) := fun c hc => by
    rw [hO]; exact readsAt_map_iff.mp hoff c (by rw [stackOffsets_length, hcl92]; exact hc)
  have hrK : ∀ c < 92, LoadHolds rd a10 c (gen ^ K c) := fun c hc => by
    rw [hK]; exact readsAt_map_iff.mp hkap c (by rw [hcl92]; exact hc)
  have hdvd : ∀ c < 92, 2 ^ K c ∣ O c := fun c hc => by
    rw [hK, hO, offAt]; exact stackOffsets_dvd _ (by omega)
  have hX : ∀ k < 42, LoadHolds rd a13 k (w.point.getD k 0) := pt_reads (by omega) hpt
  have hK0 : ∀ c < 3, K c = layout.logMemory := fun c hc => by
    rw [hK, committedKappas_getD _ hkl (by omega), blockCols_lo c (by omega), ← hkps,
      columnKappas_mem _ _ _ (by omega)]
  have hK5 : K 5 = layout.tableLogHeights.getD opBlake2s 0 + 8 := by
    rw [hK, committedKappas_getD _ hkl (by omega), qflock_col.2.2, ← hkps]
    exact columnKappas_qflock _ _ _
  have hlm28 : layout.logMemory ≤ 28 := by
    have := hKμ 0 (by omega); rw [hK0 0 (by omega)] at this; omega
  have hτ : layout.tableLogHeights.getD opBlake2s 0 + 8 ≤ layout.stackLog := by
    have := hKμ 5 (by omega); rwa [hK5] at this
  have hlam : ∀ j < 112, LoadHolds rd a8 j (lam ^ (j + 1)) := fun j hj => by
    have := (readsAt_iff_getD.mp hlp) j (by rw [length_powersFrom', hcl]; exact hj)
    rwa [powersFrom_getD _ _ _ _ (by rw [hcl]; exact hj), ← pow_succ'] at this
  -- each claim's facts
  have hcf : ∀ j < 112, ∃ p : List E, (claims.map (·.point))[j]? = some p ∧
      p.length = kps.getD (claimColumns.getD j 0) 0 := fun j hj => by
    have hjl : j < claims.length := by rw [hcl]; exact hj
    refine ⟨claims[j].point, by simp [hjl], ?_⟩
    have := hlens j claims[j].point (by simp [hjl])
    rw [this, hpl, placementsOf_getD kps (by have := (claim_cols j hj).1; omega)]
    split <;> rfl
  -- the arguments along the valuations
  set args := [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16]
  have hσ0 : Fixes (Val.ofArgs args) (argFix args) := fun p hp => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp; rfl
  have ag : ∀ {hi : ℕ} {σ' : Val}, Ext 17 hi (Val.ofArgs args) σ' → ∀ i < 17,
      σ' (.n i) = args.getD i 0 := fun he i hi => by rw [he.apply (Or.inl hi)]; rfl
  -- the claims
  have hclaimC : ∀ j < 112, ∀ σ : Val, (σ (.n 5) = a5 ∧ σ (.n 7) = a7 ∧ σ (.n 8) = a8 ∧
      σ (.n 10) = a10 ∧ σ (.n 13) = a13 ∧ σ (.n 17) = p17 ∧ σ (.n 19) = p19 ∧ σ (.n 21) = p21) →
      Completes (coreProgram.Rel rd) rd (claimV.getD j 0) (claimV.getD (j + 1) 0) (claimBlk j) σ
        (fun σ' => σ' (.n 5) = a5 ∧ σ' (.n 7) = a7 ∧ σ' (.n 8) = a8 ∧
      σ' (.n 10) = a10 ∧ σ' (.n 13) = a13 ∧ σ' (.n 17) = p17 ∧ σ' (.n 19) = p19 ∧ σ' (.n 21) = p21) := by
    intro j hj σ ⟨i5, i7, i8, i10, i13, i17, i19, i21⟩
    obtain ⟨p, hp, hplen⟩ := hcf j hj
    obtain ⟨hcpl, hpz, hpr, hpp⟩ := hpts j p hp
    obtain ⟨hc110, hlimb, hnon⟩ := claim_cols j hj
    have i312 := (claim_idx j hj).1
    have keep : ∀ {σ' : Val}, Ext (claimV.getD j 0) (claimV.getD (j + 1) 0) σ σ' →
        σ' (.n 5) = a5 ∧ σ' (.n 7) = a7 ∧ σ' (.n 8) = a8 ∧
      σ' (.n 10) = a10 ∧ σ' (.n 13) = a13 ∧ σ' (.n 17) = p17 ∧ σ' (.n 19) = p19 ∧
        σ' (.n 21) = p21 := fun he => ⟨he.get (by omega) i5, he.get (by omega) i7,
      he.get (by omega) i8, he.get (by omega) i10, he.get (by omega) i13, he.get (by omega) i17,
      he.get (by omega) i19, he.get (by omega) i21⟩
    have hkind : claimKind j = 0 ∨ claimKind j = 1 ∨ claimKind j = 2 ∨ claimKind j = 3 := by
      unfold claimKind; split_ifs <;> simp
    rcases hkind with hk0 | hk1 | hk2 | hk3
    · have hj5 : j < 5 := by unfold claimKind at hk0; split_ifs at hk0; omega
      obtain ⟨-, hcc, -, hbc⟩ := hnon (by omega)
      have hKp : K (claimCol j) = p.length := by rw [hK, committedKappas_getD _ hkl hcc, hbc, hplen]
      have hle : p.length ≤ bus.point.length := by
        have := congrArg List.length (hpz hj5); rw [List.length_take] at this; omega
      obtain ⟨low, llow⟩ := chain_word hbp (by rw [← hgmu]; exact c17) hle
      refine (c_claim_lo hj (Or.inl hk0) σ i7 i8 i10 (by simp only [hk0, ↓reduceIte]; exact i17)
        (hcpl (by unfold nPooled nClaims; omega)) llow (by rw [← hKp]; exact hrK _ hcc)
        (hlam j hj)).withExt.mono le_rfl le_rfl fun σ' ⟨_, he⟩ => keep he
    · have hjr : 5 ≤ j ∧ j < 109 := by unfold claimKind at hk1; split_ifs at hk1 <;> omega
      obtain ⟨-, hcc, -, hbc⟩ := hnon (by omega)
      have hKp : K (claimCol j) = p.length := by rw [hK, committedKappas_getD _ hkl hcc, hbc, hplen]
      have hle : p.length ≤ chis.length := by
        have := congrArg List.length (hpr hjr.1 (by unfold nPooled nClaims; omega))
        rw [List.length_take] at this; omega
      obtain ⟨low, llow⟩ := chain_word (n := chis.length) (by omega) (by rw [← hgzcn]; exact c19) hle
      refine (c_claim_lo hj (Or.inr hk1) σ i7 i8 i10
        (by simp only [hk1, show (1 : ℕ) ≠ 0 from by decide, ↓reduceIte]; exact i19)
        (hcpl (by unfold nPooled nClaims; omega)) llow (by rw [← hKp]; exact hrK _ hcc)
        (hlam j hj)).withExt.mono le_rfl le_rfl fun σ' ⟨_, he⟩ => keep he
    · have hjr : 81 ≤ j ∧ j < 99 := by unfold claimKind at hk2; split_ifs at hk2 <;> omega
      obtain ⟨-, -, h82, h100⟩ := hlimb hk2
      have hkc : kps.getD (claimColumns.getD j 0) 0 = layout.tableLogHeights.getD opBlake2s 0 := by
        rw [← hkps, show claimColumns.getD j 0 = 73 + (claimColumns.getD j 0 - 73) by omega,
          columnKappas_blake _ _ _ (by omega)]
        rfl
      rw [hkc] at hplen
      obtain ⟨low, llow⟩ := chain_word (n := layout.tableLogHeights.getD opBlake2s 0) (by omega)
        (by rw [← hgtau]; exact c21) (le_of_eq hplen)
      refine (c_claim_q hj hk2 σ (Y := fun k => w.point.getD k 0) i7 i8 i10 i13 i21
        (fun t ht => hX t (by omega)) (hcpl (by unfold nPooled nClaims; omega)) llow
        (by rw [hplen, ← hK5]; exact hrK 5 (by omega)) (hlam j hj)).withExt.mono le_rfl le_rfl
        fun σ' ⟨_, he⟩ => keep he
    · have hjr : 109 ≤ j := by unfold claimKind at hk3; split_ifs at hk3 <;> omega
      obtain ⟨-, hcv, hcol⟩ := claimKind_pi hjr hj
      obtain ⟨-, hcc, -, -⟩ := hnon (by omega)
      refine (c_claim_pi hj hk3 σ i5 i8 i10
        (by rw [hglm, ← hK0 (claimCol j) (by omega)]; exact hrK _ hcc) (hlam j hj)).withExt.mono
        le_rfl le_rfl fun σ' ⟨_, he⟩ => keep he
  -- the segments before the check
  obtain ⟨-, m, hm, hmN, zs, ps, -, -, -, -, c, -, hrows⟩ := hrs
  have hmτ : m = layout.tableLogHeights.getD opBlake2s 0 + 8 := by
    rw [hgtau, ← pow_add] at hmN
    exact (gen_pow_inj (by omega) hm hmN).symm
  have hM'' := hM
  obtain ⟨-, -, -, -, -, hrs', h1750⟩ := hM''
  have Pre : Completes (coreProgram.Rel rd) rd 17 2081 (tPre ++ (((List.range 92).map selBlk).flatten ++
      (((List.range 112).map claimBlk).flatten ++ (tPostA ++ (((List.range 64).map rinitBlk).flatten ++
        (tPostB ++ ((List.range 64).map rsBlk).flatten)))))) (Val.ofArgs args) (fun σ' =>
        σ' (.n 17) = p17 ∧ σ' (.n 19) = p19 ∧ σ' (.n 21) = p21 ∧ σ' (.n 25) = p25 ∧
          σ' (.n 1750) = p1750) := by
    refine Completes.append (m := 36) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
      (c_tpre hM (n := layout.logMemory) hlm1 (by omega) hglm (X := fun k => w.point.getD k 0)
        (fun k hk => hX k (by omega)) (Val.ofArgs args) hσ0).withExt fun σ1 e1 ⟨q1, _⟩ => ?_
    have E1 := e1
    refine Completes.append (m := 312) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
      (Completes.flatten (st := fun c => 36 + 3 * c)
        (Inv := fun _ σ => σ (.n 9) = a9 ∧ σ (.n 10) = a10 ∧ σ (.n 13) = a13) 92
        (fun _ _ => by omega) (fun c hc => numBelow_of_B (sel_below c hc))
        (fun c hc σ ⟨h9, h10, h13⟩ => by
          rw [show 36 + 3 * (c + 1) = 36 + 3 * c + 3 by ring]
          refine (c_sel (K := K c) (O := O c) (le_trans (hKμ c hc) hμ28)
            (lt_of_lt_of_le (hOμ c hc) (Nat.pow_le_pow_right (by norm_num) hμ28)) (hdvd c hc)
            (hrO c hc) (hrK c hc) (zs := (List.range 28).map fun k => w.point.getD k 0)
            (by simp) (fun k hk => by
              simp only [List.getElem_map, List.getElem_range]
              exact hX k (by simp at hk; omega)) σ h9 h10 h13 (by omega)).withExt.mono le_rfl
            le_rfl fun σ' ⟨_, he⟩ => ⟨he.get (by omega) h9, he.get (by omega) h10,
              he.get (by omega) h13⟩) σ1
        ⟨ag E1 9 (by omega), ag E1 10 (by omega), ag E1 13 (by omega)⟩).withExt
      fun σ2 e2 ⟨_, _⟩ => ?_
    have E2 := E1.trans e2 (by omega) (by omega)
    refine Completes.append (m := 1737) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
      (Completes.flatten (st := fun j => claimV.getD j 0) (Inv := fun _ σ => σ (.n 5) = a5 ∧
          σ (.n 7) = a7 ∧ σ (.n 8) = a8 ∧ σ (.n 10) = a10 ∧ σ (.n 13) = a13 ∧ σ (.n 17) = p17 ∧
          σ (.n 19) = p19 ∧ σ (.n 21) = p21) 112 claimV_mono
        (fun j hj => numBelow_of_B (claims_below j hj)) hclaimC σ2
        ⟨ag E2 5 (by omega), ag E2 7 (by omega), ag E2 8 (by omega), ag E2 10 (by omega),
          ag E2 13 (by omega), e2.get (by omega) (q1.get (by simp)),
          e2.get (by omega) (q1.get (by simp)), e2.get (by omega) (q1.get (by simp))⟩).withExt
      fun σ3 e3 ⟨_, _⟩ => ?_
    have E3 := E2.trans e3 (by omega) (by omega)
    refine Completes.append (m := 1751) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
      (c_tpostA (p1750 := p1750) σ3 (ag E3 6 (by omega)) (ag E3 10 (by omega)) (by
        have := hrK 5 (by omega)
        rwa [hK5, pow_add, ← hgtau, ← word_g8] at this)).withExt fun σ4 e4 ⟨q4, _⟩ => ?_
    have E4 := E3.trans e4 (by omega) (by omega)
    refine Completes.append (m := 1815) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
      (c_rinit σ4 q4 h1750).withExt fun σ5 e5 ⟨_, _⟩ => ?_
    have E5 := E4.trans e5 (by omega) (by omega)
    refine Completes.append (m := 1826) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
      (c_tpostB σ5 (ag E5 6 (by omega)) (ag E5 11 (by omega)) (ag E5 13 (by omega))
        (e5.get (by omega) q4) hrs').withExt fun σ6 e6 ⟨q6, _⟩ => ?_
    have E6 := E5.trans e6 (by omega) (by omega)
    have hsq : sqI (args.getD 6 0 * word 256 0 0) 6 = gen ^ (64 * m) := by
      show sqI (a6 * word 256 0 0) 6 = _
      rw [word_g8, hgtau, ← pow_add, ← hmτ, sqI_gen]; norm_num
    have t1 : ∀ {k : ℕ} {v : E} {σ' : Val}, Ext 1826 2081 σ6 σ' → k < 36 → σ1 (.n k) = v →
        σ' (.n k) = v := fun he hk h =>
      he.get (by omega) (e6.get (by omega) (e5.get (by omega) (e4.get (by omega) (e3.get (by omega)
        (e2.get (by omega) h)))))
    refine (c_rs σ6 (ag E6 12 (by omega)) q6 (cs := fun k => cs.getD k 0)
      (fun k hk => (readsAt_iff_getD.mp hct) k (by omega)) (R := fun k =>
        ringRow (c.getD k 0) (zs.take m) (ps.take m) k) (fun k hk => ?_)).withExt.mono le_rfl le_rfl
      fun σ' ⟨_, he⟩ => ⟨t1 he (by omega) (q1.get (by simp)), t1 he (by omega) (q1.get (by simp)),
        t1 he (by omega) (q1.get (by simp)), t1 he (by omega) (q1.get (by simp)),
        he.get (by omega) (e6.get (by omega) (e5.get (by omega) q4))⟩
    rw [hsq]
    exact lh_back (hrows (by omega) m le_rfl k hk) rfl
  -- the value the check compares
  obtain ⟨σ7, e7, ⟨⟨k17, k19, k21, k25, k1750⟩, _, hh7⟩, _⟩ := Completes.withHolds Pre
  have hall := hh7 True (fun rs => rs = []) trivial
  have hfl : [tPre, ((List.range 92).map selBlk).flatten, ((List.range 112).map claimBlk).flatten,
      tPostA, ((List.range 64).map rinitBlk).flatten, tPostB,
      ((List.range 64).map rsBlk).flatten].flatten = tPre ++ (((List.range 92).map selBlk).flatten ++
      (((List.range 112).map claimBlk).flatten ++ (tPostA ++ (((List.range 64).map rinitBlk).flatten ++
        (tPostB ++ ((List.range 64).map rsBlk).flatten))))) := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [← hfl, holdsList_flatten_noRet _ (by decide +kernel)] at hall
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true] at hall
  obtain ⟨g0, g1, g2, -, g4, g5, g6⟩ := hall
  rw [holdsList_range_flatten 92 selBlk (fun _ => rfl), and_true] at g1
  rw [holdsList_range_flatten 112 claimBlk claimBlk_noRet, and_true] at g2
  rw [holdsList_range_flatten 64 rinitBlk (fun _ => rfl), and_true] at g4
  rw [holdsList_range_flatten 64 rsBlk (fun k => by unfold rsBlk; split <;> rfl), and_true] at g6
  have hp : [σ7 (.n 0), σ7 (.n 1), σ7 (.n 2), σ7 (.n 3), σ7 (.n 4), σ7 (.n 5), σ7 (.n 6),
      σ7 (.n 7), σ7 (.n 8), σ7 (.n 9), σ7 (.n 10), σ7 (.n 11), σ7 (.n 12), σ7 (.n 13), σ7 (.n 14),
      σ7 (.n 15), σ7 (.n 16)] = args := by
    rw [ag e7 0 (by omega), ag e7 1 (by omega), ag e7 2 (by omega), ag e7 3 (by omega),
      ag e7 4 (by omega), ag e7 5 (by omega), ag e7 6 (by omega), ag e7 7 (by omega),
      ag e7 8 (by omega), ag e7 9 (by omega), ag e7 10 (by omega), ag e7 11 (by omega),
      ag e7 12 (by omega), ag e7 13 (by omega), ag e7 14 (by omega), ag e7 15 (by omega),
      ag e7 16 (by omega)]
    rfl
  have hv := terminal_val hpre' hp g0 g1 g2 g4 g5 (fun k hk => (g6 k hk))
  -- the check
  obtain ⟨σ8, e8, -, hh8⟩ := c_tend (C := coreProgram.Rel rd) (rd := rd) σ7 (ag e7 15 (by omega))
    (ag e7 16 (by omega)) (by show (_ + _) * a15 = a16; rw [hv, hyr, hst]; exact hacc)
  rw [core14_body, core14_params]
  refine ⟨σ8, ?_, ?_, e8.get (by omega) k17, e8.get (by omega) k19, e8.get (by omega) k21,
    e8.get (by omega) k25, e8.get (by omega) k1750⟩
  · simp only [List.map_cons, List.map_nil]
    rw [e8.apply (Or.inl (by omega)), e8.apply (Or.inl (by omega)), e8.apply (Or.inl (by omega)),
      e8.apply (Or.inl (by omega)), e8.apply (Or.inl (by omega)), e8.apply (Or.inl (by omega)),
      e8.apply (Or.inl (by omega)), e8.apply (Or.inl (by omega)), e8.apply (Or.inl (by omega)),
      e8.apply (Or.inl (by omega)), e8.apply (Or.inl (by omega)), e8.apply (Or.inl (by omega)),
      e8.apply (Or.inl (by omega)), e8.apply (Or.inl (by omega)), e8.apply (Or.inl (by omega)),
      e8.apply (Or.inl (by omega)), e8.apply (Or.inl (by omega))]
    exact hp
  · have hb : tSegs.flatten = (tPre ++ (((List.range 92).map selBlk).flatten ++
        (((List.range 112).map claimBlk).flatten ++ (tPostA ++ (((List.range 64).map rinitBlk).flatten ++
          (tPostB ++ ((List.range 64).map rsBlk).flatten)))))) ++ tEnd := by
      simp only [tSegs, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
    rw [hb, holdsList_append, holdsList_append]
    exact (holdsList_frame (numBelow_of_B (by decide +kernel)) e8.agree _ _).mp
      (hh7 _ _ (hh8 _ _ (by simp [Stmt.HoldsList, Stmt.Holds])))

/-- **`check_opening_terminal` holds** (TRIAGE #42, #43) under its precondition, each claim's
point of its column's log, the opening accepting the stacked weight, and the honest memory. -/
theorem check_opening_terminal_rel {layout : Layout} {bus : BusResult} {claims : List ColumnClaim}
    {lam : E} {fp cs : List E} {w : WhirEnd}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 p17 p19 p21 p25 p1750 : E}
    (hpre : TermPre TCtx PCtx rd layout bus claims lam fp cs w
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16])
    (hlens : ∀ j (p : List E), (claims.map (·.point))[j]? = some p →
      p.length = (layout.placements.getD (claimColumns.getD j 0) default).vars)
    (hacc : w.Accepts (stackWeight layout claims fp cs lam))
    (hM : TermMem rd [p17, p19, p21, p25, p1750]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16]) :
    coreProgram.Rel rd "check_opening_terminal"
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16] [] := by
  obtain ⟨σ, hp, hh, -⟩ := term_body_complete hpre hlens hacc hM
  exact (rel_iff_sem find_check_opening_terminal _ _).mpr ⟨σ, hp, hh⟩

/-- **`check_opening_terminal` is complete** (TRIAGE #42, #43): `CompleteTerm`'s statement over
`TermMem`, with each claim's point of its column's log (the conjunct `TermPreAcc` adds to
`TermPre`). -/
theorem check_opening_terminal_complete (rd : Reader) :
    ∀ ptrs layout bus claims lam flockPoint coeffs (w : WhirEnd) args,
      TermPre TCtx PCtx rd layout bus claims lam flockPoint coeffs w args →
      (∀ j (p : List E), (claims.map (·.point))[j]? = some p →
        p.length = (layout.placements.getD (claimColumns.getD j 0) default).vars) →
      w.Accepts (stackWeight layout claims flockPoint coeffs lam) → TermMem rd ptrs args →
        coreProgram.Rel rd "check_opening_terminal" args [] := by
  intro ptrs layout bus claims lam fp cs w args hpre hlens hacc hM
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, rfl⟩ :=
    args17 (P := TermPre TCtx PCtx rd layout bus claims lam fp cs w)
    (fun l hl hP => by
      rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7,
          _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15,
          _ | ⟨a16, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
      all_goals first | exact hP.elim | exact absurd rfl hl) hpre
  match ptrs, hM with
  | [p17, p19, p21, p25, p1750], hM => exact check_opening_terminal_rel hpre hlens hacc hM

end

end
end LeanVM.Guest.B1

