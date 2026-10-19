/-
  LeanVM.Guest.B1.Tables.VtPlLoads

  `verify_tables`' placed form: every load reads the caller's words or a buffer.
-/

module

public import LeanVM.Guest.B1.Tables.VtPlFacts

/-!
# The loads, placed

Each class of `vt_loads`: an argument's words in `Lin` (`addr_in_region`), a `HeapBuf` below
its size, a selector's chains at `g^(μ - κ)`, an index chain at its block's log-height, a sort
rank's side, log-height, offset and square at its block (read back from the honest
`sort_order`), the sum-check's slots and the cursor after them, a table's challenge product and
equality prefix at `g^(n - τ)` and `g^τ`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- A load reads the caller's words or the buffers. -/
def VtLoadOk (Lin B : Main.Layout) (σ : Val) (q : V × ℕ) : Prop :=
  ∃ i, (σ q.1).limb 0 * Parameters.gpow q.2 = Parameters.gpow i ∧ (RegionL Lin i ∨ RegionL B i)

section
variable {rd : Reader} {σ : Val}

/-- A selector's pointer facts. -/
theorem vt_sel_facts (h : VtHolds rd σ) {i : ℕ} (hi : i < 65) :
    LoadHolds rd (σ (.n 9)) (selBlk.getD i 0) (σ (.n (selVal.getD i 0))) ∧
      σ (.n 6) = σ (.n (selVal.getD i 0 + 5)) * σ (.n (selVal.getD i 0)) ∧
      σ (.n (selVal.getD i 0 + 22)) = σ (.n (selVal.getD i 0 + 15)) * σ (.n (selVal.getD i 0 + 5)) ∧
      σ (.n (selVal.getD i 0 + 24)) = σ (.n (selVal.getD i 0 + 16)) * σ (.n (selVal.getD i 0 + 5)) := by
  obtain ⟨kr, hb⟩ := h.slice _ _ (sel_blocks i hi)
  simp only [selT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and, word_one,
    List.map_cons, List.map_nil] at hb
  obtain ⟨l0, -, -, m6, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, m22, -, m24, -, -, -⟩ := hb
  exact ⟨l0, m6, m22, m24⟩

/-- A side's rank `0`'s pointer facts. -/
theorem vt_rank0_facts (h : VtHolds rd σ) {k v so sd : ℕ}
    (heq : stmtsEqb (vtRank0 v so sd) ((vtPre.drop k).take 14) = true) :
    LoadHolds rd (σ (.n 24)) so (σ (.n v)) ∧ σ (.n (v + 5)) = σ (.n 25) * σ (.n v) ∧
      σ (.n (v + 8)) = σ (.n 9) * σ (.n v) ∧ LoadHolds rd (σ (.n (v + 8))) 0 (σ (.n (v + 9))) ∧
      σ (.n (v + 11)) = σ (.n 128) * σ (.n v) ∧ σ (.n (v + 12)) = σ (.n 10) * σ (.n (v + 9)) := by
  obtain ⟨kr, hb⟩ := h.slice _ _ heq
  simp only [vtRank0, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at hb
  obtain ⟨l0, -, -, m5, -, -, -, m8, l9, -, m11, -, m12, -⟩ := hb
  exact ⟨l0, m5, m8, l9, m11, m12⟩

/-- A side's rank `≥ 1`'s pointer facts. -/
theorem vt_rankN_facts (h : VtHolds rd σ) {k v pk pg pgo so sd : ℕ}
    (heq : stmtsEqb (vtRankN v pk pg pgo so sd) ((vtPre.drop k).take 19) = true) :
    LoadHolds rd (σ (.n 24)) so (σ (.n v)) ∧ σ (.n (v + 5)) = σ (.n 25) * σ (.n v) ∧
      σ (.n (v + 8)) = σ (.n 9) * σ (.n v) ∧ LoadHolds rd (σ (.n (v + 8))) 0 (σ (.n (v + 9))) ∧
      σ (.n (v + 21)) = σ (.n 128) * σ (.n v) ∧ σ (.n (v + 22)) = σ (.n 10) * σ (.n (v + 9)) := by
  obtain ⟨kr, hb⟩ := h.slice _ _ heq
  simp only [vtRankN] at hb
  rw [Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList,
    Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList,
    Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, holds_ite_noRet _ _ _ rfl rfl] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, implies_true] at hb
  obtain ⟨l0, -, -, m5, -, -, -, m8, l9, -, -, -, -, -, m21, -, m22, -, -⟩ := hb
  exact ⟨l0, m5, m8, l9, m21, m22⟩

/-- A table's pointer facts. -/
theorem vt_tab_facts (h : VtHolds rd σ) {dS g mS q pcS pc ppS pp t : ℕ}
    (e1 : stmtsEqb [.atom (.load (.n g) (.n 7) (t + 1))] ((vtPre.drop dS).take 1) = true)
    (e2 : stmtsEqb [.atom (.mul (.n 4554) (.n q) (.n g))] ((vtPre.drop mS).take 1) = true)
    (e3 : stmtsEqb [.atom (.mul (.n pc) (.n 4639) (.n q))] ((vtPre.drop pcS).take 1) = true)
    (e4 : stmtsEqb [.atom (.mul (.n pp) (.n 4655) (.n g))] ((vtPre.drop ppS).take 1) = true) :
    LoadHolds rd (σ (.n 7)) (t + 1) (σ (.n g)) ∧ σ (.n 4554) = σ (.n q) * σ (.n g) ∧
      σ (.n pc) = σ (.n 4639) * σ (.n q) ∧ σ (.n pp) = σ (.n 4655) * σ (.n g) :=
  ⟨h.atom _ _ e1, h.atom _ _ e2, h.atom _ _ e3, h.atom _ _ e4⟩

end

theorem le_foldl_max : ∀ (l : List ℕ) (a x : ℕ), x ∈ l → x ≤ l.foldl max a
  | [], _, _, hx => absurd hx (by simp)
  | y :: l, a, x, hx => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right a x) (le_foldl_max_init l (max a x))
    · exact le_foldl_max l _ x hx
where
  le_foldl_max_init : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a
    | [], _ => le_rfl
    | y :: l, a => le_trans (le_max_left a y) (le_foldl_max_init l (max a y))

/-- **The blocks' log-heights are at most `μ`.** -/
theorem vtKs_le {logMem n μ : ℕ} {τ : ℕ → ℕ} (hlm : logMem ≤ μ) (h18 : 18 ≤ μ) (hn : n ≤ μ)
    (hτ : ∀ t < 6, τ t ≤ n) {b : ℕ} (hb : b < 102) : vtKs logMem τ b ≤ μ := by
  obtain ⟨h8, ha⟩ := vt_src_bound b hb
  unfold vtKs
  generalize blockKappaSrc.getD b 0 = s at h8 ha
  rcases ha with ha | ⟨ha, rfl⟩
  · rw [ha]
    interval_cases s <;> simp <;> first | omega | exact le_trans (hτ _ (by omega)) hn
  · rw [ha]; simp; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Every load reads the caller's words or a buffer.** -/
theorem vt_placed_loads {κ : ℕ} {rd : Reader} {σ : Val} {Lin : Main.Layout} {b : ℕ}
    {logMem n : ℕ} {rowsN : List ℕ} {point xs chis claims cpw : List E} {alphas : List E}
    {c sq dims rows bk fpw pool cplen : ℕ} {τ ks : ℕ → ℕ} {own : List (List E)}
    {cvr : ℕ → Digest} {cl ch : ℕ → E}
    (hτd : τ = fun t => log2Ceil (rowsN.getD t 0)) (hksd : ks = vtKs logMem τ)
    (hownd : own = vtOwnW ks point logMem n cvr (ofK (Parameters.gpow c)) cl ch chis)
    (h : VtHolds rd σ) (hlow : LowDef κ rd) (hLin : MemL rd Lin) (hlm32 : logMem ≤ 32)
    (hrl : rowsN.length = 6) (hτ29 : ∀ t < 6, τ t < 29) (hal : alphas.length = 4)
    (hτn : ∀ t < 6, τ t ≤ n) (hnμ : n ≤ point.length) (hxl : xs.length = 5 + 3 * n + 104)
    (hcl : claims.length = nClaims) (hcpl : cpw.length = nPooled) (hlmμ : logMem ≤ point.length)
    (h18 : 18 ≤ point.length) (hμ33 : point.length < 33)
    (h2 : σ (.n 2) = ofK (Parameters.gpow c)) (h6 : σ (.n 6) = gen ^ point.length)
    (h7 : σ (.n 7) = ofK (Parameters.gpow dims)) (h8 : σ (.n 8) = ofK (Parameters.gpow rows))
    (h9 : σ (.n 9) = ofK (Parameters.gpow bk)) (h10 : σ (.n 10) = ofK (Parameters.gpow sq))
    (h11 : σ (.n 11) = ofK (Parameters.gpow fpw)) (h13 : σ (.n 13) = ofK (Parameters.gpow pool))
    (h14 : σ (.n 14) = ofK (Parameters.gpow cplen))
    (hptr : ∀ i < 205, σ (.n (vtAllocVar.getD i 0)) = vtPtr b n i) (h4554 : σ (.n 4554) = gen ^ n)
    (hallX : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow c)) xs)
    (hallD : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun m ↦ gen ^ log2Ceil m))
    (hallR : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat))
    (hallK : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow bk))
      (blockKappas (gen ^ logMem) (rowsN.map fun m ↦ gen ^ log2Ceil m)))
    (hallF : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas))
    (hallP : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow pool)) claims)
    (hallC : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow cplen)) cpw)
    (hallS : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow sq)) ((List.range 34).map fun j => gen ^ 2 ^ j))
    (hB : MemL rd (bufL b (vtSizes n) own)) :
    ∀ q ∈ vtPre.filterMap Stmt.loadS, VtLoadOk Lin (bufL b (vtSizes n) own) σ q := by
  subst hksd
  have hks : ∀ b' < 102, vtKs logMem τ b' ≤ point.length := fun b' hb' => vtKs_le hlmμ h18 hnμ hτn hb'
  have hks34 : ∀ b' < 102, vtKs logMem τ b' < 34 := vtKs_lt hlm32 hτ29
  have hbkR : ∀ b' < 102, LoadHolds rd (ofK (Parameters.gpow bk)) b' (gen ^ vtKs logMem τ b') := by
    intro b' hb'
    have := readsAt_getD0 (hallK rd hlow hLin) (k := b') (by simp [blockKappas]; exact hb')
    rwa [vt_bk_get hrl hb', ← hτd] at this
  have hdR : ∀ t < 6, LoadHolds rd (ofK (Parameters.gpow dims)) (t + 1) (gen ^ τ t) := fun t ht => by
    have := (hallD rd hlow hLin) (t + 1) (by simp; omega)
    simp only [List.getElem_cons_succ, List.getElem_map] at this
    rw [hτd]; dsimp only; rw [List.getD_eq_getElem _ _ (by omega)]; exact this
  rw [hownd] at hB
  have hbuf0 := vt_own_reads (i := 0) hB (by omega)
  have hbuf202 := vt_own_reads (i := 202) hB (by omega)
  rw [vtOwnW_0] at hbuf0
  rw [vtOwnW_202] at hbuf202
  obtain ⟨a0, a1, a2, a11, a15, a202, a203, a204, z0, z1, z2, z11, z15⟩ := vt_allocVar_fixed
  have p25 : σ (.n 25) = vtPtr b n 1 := by rw [← hptr 1 (by omega), a1]
  have p24 : σ (.n 24) = vtPtr b n 0 := by rw [← hptr 0 (by omega), a0]
  have p128 : σ (.n 128) = vtPtr b n 2 := by rw [← hptr 2 (by omega), a2]
  have p4636 : σ (.n 4636) = vtPtr b n 202 := by rw [← hptr 202 (by omega), a202]
  have p4639 : σ (.n 4639) = vtPtr b n 203 := by rw [← hptr 203 (by omega), a203]
  have p4655 : σ (.n 4655) = vtPtr b n 204 := by rw [← hptr 204 (by omega), a204]
  -- regions
  have linA : ∀ {a : ℕ} {ws : List E}, (∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow a)) ws) → ∀ {k : ℕ} {e : ℕ} (off : ℕ),
      σ (.n k) = ofK (Parameters.gpow a) * gen ^ e → e + off < ws.length →
      VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n k, off) := by
    intro a ws hall k e off hk he
    obtain ⟨i, hi, hr⟩ := addr_in_region hall hlow hLin (j := e + off) he
    refine ⟨i, ?_, Or.inl hr⟩
    show (σ (.n k)).limb 0 * Parameters.gpow off = Parameters.gpow i
    rw [hk, addr_gen, Nat.add_assoc, ← addr_k]; exact hi
  have ownA : ∀ {k : ℕ} (j e off : ℕ), σ (.n k) = vtPtr b n j * gen ^ e → j < 205 →
      e + off < (vtSizes n).getD j 0 → VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n k, off) :=
    by
      intro k j e off hk hj he
      refine ⟨(bases b (vtSizes n)).getD j 0 + (e + off), ?_, Or.inr ?_⟩
      · show (σ (.n k)).limb 0 * _ = _
        rw [hk]; exact vtPtr_addr b n j e off
      · rw [hownd]; exact vt_own_region hj he
  have g0 : ∀ {x : E}, x = x * gen ^ 0 := fun {x} => by simp
  -- a rank
  have rankOK : ∀ {v blk P5 P8 P11 P12 : ℕ}, σ (.n v) = gen ^ blk → blk < 102 →
      σ (.n P5) = σ (.n 25) * σ (.n v) → σ (.n P8) = σ (.n 9) * σ (.n v) →
      LoadHolds rd (σ (.n P8)) 0 (σ (.n (v + 9))) → σ (.n P11) = σ (.n 128) * σ (.n v) →
      σ (.n P12) = σ (.n 10) * σ (.n (v + 9)) →
      VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n P5, 0) ∧ VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n P8, 0) ∧
        VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n P11, 0) ∧
        VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n P12, 0) := by
    intro v blk P5 P8 P11 P12 hv hblk m5 m8 l9 m11 m12
    have e9 : σ (.n (v + 9)) = gen ^ vtKs logMem τ blk := by
      rw [m8, h9, hv, loadHolds_mul_gen_pow, Nat.add_zero] at l9
      exact loadHolds_unique l9 (hbkR blk hblk)
    refine ⟨ownA 1 blk 0 (by rw [m5, p25, hv]) (by omega) (by rw [vtSizes_lo n (by omega), z1]; omega),
      linA hallK 0 (by rw [m8, h9, hv]) (by simp [blockKappas]; omega),
      ownA 2 blk 0 (by rw [m11, p128, hv]) (by omega) (by rw [vtSizes_lo n (by omega), z2]; omega),
      linA hallS 0 (by rw [m12, h10, e9]) (by simp; exact hks34 blk hblk)⟩
  -- a table
  have tabOK : ∀ {dS g mS q pcS pc ppS pp t : ℕ}, t < 6 →
      stmtsEqb [.atom (.load (.n g) (.n 7) (t + 1))] ((vtPre.drop dS).take 1) = true →
      stmtsEqb [.atom (.mul (.n 4554) (.n q) (.n g))] ((vtPre.drop mS).take 1) = true →
      stmtsEqb [.atom (.mul (.n pc) (.n 4639) (.n q))] ((vtPre.drop pcS).take 1) = true →
      stmtsEqb [.atom (.mul (.n pp) (.n 4655) (.n g))] ((vtPre.drop ppS).take 1) = true →
      VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n pc, 0) ∧ VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n pp, 0) := by
    intro dS g mS q pcS pc ppS pp t ht e1 e2 e3 e4
    obtain ⟨ld, mq, mpc, mpp⟩ := vt_tab_facts h e1 e2 e3 e4
    rw [h7] at ld
    have eg : σ (.n g) = gen ^ τ t := loadHolds_unique ld (hdR t ht)
    have eq : σ (.n q) = gen ^ (n - τ t) := by
      rw [h4554, eg] at mq
      have hτt := hτn t ht
      refine mul_right_cancel₀ (pow_ne_zero (τ t) vt_gen_ne_zero) ?_
      rw [← mq, ← pow_add, Nat.sub_add_cancel hτt]
    refine ⟨ownA 203 (n - τ t) 0 (by rw [mpc, p4639, eq]) (by omega) (by rw [vtSizes_203]; omega),
      ownA 204 (τ t) 0 (by rw [mpp, p4655, eg]) (by omega)
        (by rw [vtSizes_204]; have := hτn t ht; omega)⟩
  intro q hq
  have hb := List.all_eq_true.mp vt_loads q hq
  obtain ⟨⟨path, tag, k⟩, off⟩ := q
  match path, tag, hb with
  | _ :: _, _, hb => simp [vtLoadB] at hb
  | [], _ + 1, hb => simp [vtLoadB] at hb
  | [], 0, hb =>
    show VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n k, off)
    rcases vtLoadN_cases (k := k) (off := off) hb with ⟨t, ht, rfl, hoff⟩ | ⟨rfl, hk⟩ |
      ⟨rfl, hoff⟩ | ⟨rfl, hoff⟩ | ⟨t, ht, rfl, hoff⟩
    · simp only [vtArgPairs, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hoff ⊢
      · exact linA hallX off (h2.trans g0) (by rw [hxl]; omega)
      · exact linA hallD off (h7.trans g0) (by simp [hrl]; omega)
      · exact linA hallR off (h8.trans g0) (by simp [hrl]; omega)
      · exact linA hallK off (h9.trans g0) (by simp [blockKappas]; omega)
      · exact linA hallF off (h11.trans g0) (by rw [length_eqKernel, hal]; omega)
      · exact linA hallP off (h13.trans g0) (by rw [hcl]; show 0 + off < 112; omega)
      · exact linA hallC off (h14.trans g0) (by rw [hcpl]; show 0 + off < 109; omega)
    · rcases hk with hk | rfl | rfl | hk | hk
      · simp only [vtTabPtrs, List.mem_cons, List.not_mem_nil, or_false] at hk
        have T0 := tabOK (t := 0) (dS := 4374) (g := 4660) (mS := 4855) (q := 5141) (pcS := 4856) (pc := 5142)
          (ppS := 4858) (pp := 5144) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        have T1 := tabOK (t := 1) (dS := 4862) (g := 5148) (mS := 5383) (q := 5669) (pcS := 5384) (pc := 5670)
          (ppS := 5386) (pp := 5672) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        have T2 := tabOK (t := 2) (dS := 5391) (g := 5677) (mS := 5660) (q := 5946) (pcS := 5661) (pc := 5947)
          (ppS := 5663) (pp := 5949) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        have T3 := tabOK (t := 3) (dS := 5668) (g := 5954) (mS := 6183) (q := 6469) (pcS := 6184) (pc := 6470)
          (ppS := 6186) (pp := 6472) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        have T4 := tabOK (t := 4) (dS := 6191) (g := 6477) (mS := 6685) (q := 6971) (pcS := 6686) (pc := 6972)
          (ppS := 6688) (pp := 6974) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        have T5 := tabOK (t := 5) (dS := 6693) (g := 6979) (mS := 7846) (q := 8132) (pcS := 7847) (pc := 8133)
          (ppS := 7849) (pp := 8135) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact T0.1
        · exact T0.2
        · exact T1.1
        · exact T1.2
        · exact T2.1
        · exact T2.2
        · exact T3.1
        · exact T3.2
        · exact T4.1
        · exact T4.2
        · exact T5.1
        · exact T5.2
      · -- the memory's index chain
        have m30 : σ (.n 1930) = σ (.n 1925) * σ (.n 1893) :=
          h.atom 1656 (.mul (.n 1930) (.n 1925) (.n 1893)) (by decide +kernel)
        have l93 := (vt_sel_facts h (i := 1) (by omega)).1
        rw [h9] at l93
        have k1 : vtKs logMem τ 1 = logMem := by unfold vtKs; rfl
        have e93 : σ (.n 1893) = gen ^ logMem := by
          rw [← k1]; exact loadHolds_unique l93 (hbkR 1 (by omega))
        refine ownA 11 logMem 0 (by rw [m30, ← a11, hptr 11 (by omega), e93]) (by omega)
          (by rw [vtSizes_lo n (by omega), z11]; omega)
      · -- the bytecode's index chain
        have m34 : σ (.n 2034) = σ (.n 2029) * σ (.n 1997) :=
          h.atom 1764 (.mul (.n 2034) (.n 2029) (.n 1997)) (by decide +kernel)
        have l97 := (vt_sel_facts h (i := 2) (by omega)).1
        rw [h9] at l97
        have k2 : vtKs logMem τ 2 = 18 := by unfold vtKs; rfl
        have e97 : σ (.n 1997) = gen ^ 18 := by
          rw [← k2]; exact loadHolds_unique l97 (hbkR 2 (by omega))
        refine ownA 15 18 0 (by rw [m34, ← a15, hptr 15 (by omega), e97]) (by omega)
          (by rw [vtSizes_lo n (by omega), z15]; omega)
      · -- a selector
        rw [vtSelPtrs_eq] at hk
        obtain ⟨i, hi, hk⟩ := List.mem_flatMap.mp hk
        have hi65 := List.mem_range.mp hi
        obtain ⟨sb2, sz1, sz2, -, av1, av2, hblk⟩ := vt_selBuf i hi65
        obtain ⟨l0, m6, m22, m24⟩ := vt_sel_facts h hi65
        rw [h9] at l0
        have ev := loadHolds_unique l0 (hbkR _ hblk)
        have hkμ := hks _ hblk
        have e5 : σ (.n (selVal.getD i 0 + 5)) = gen ^ (point.length - vtKs logMem τ (selBlk.getD i 0)) := by
          rw [h6, ev] at m6
          refine mul_right_cancel₀ (b := gen ^ vtKs logMem τ (selBlk.getD i 0))
            (pow_ne_zero _ vt_gen_ne_zero) ?_
          rw [← m6, ← pow_add, Nat.sub_add_cancel hkμ]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · refine ownA (selBuf i + 1) _ 0 (by rw [m22, ← av1, hptr _ (by omega), e5]) (by omega)
            (by rw [vtSizes_lo n (by omega), sz1]; omega)
        · refine ownA (selBuf i + 2) _ 0 (by rw [m24, ← av2, hptr _ (by omega), e5]) (by omega)
            (by rw [vtSizes_lo n (by omega), sz2]; omega)
      · -- a sort rank
        rw [vtRankPtrs_eq] at hk
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
          List.mem_range] at hk
        have pushV : ∀ r < 37, ∀ {v : ℕ}, LoadHolds rd (σ (.n 24)) r (σ (.n v)) →
            σ (.n v) = gen ^ (pushOrd (vtKs logMem τ)).getD r 0 := fun r hr v hl => by
          rw [p24] at hl
          have := readsAt_getD0 hbuf0 (k := r) (by simp [sortW]; omega)
          rw [sortW_get _ (by omega), ite_pos' hr] at this
          exact loadHolds_unique hl this
        have countV : ∀ r < 28, ∀ {v so : ℕ}, so = 74 + r → LoadHolds rd (σ (.n 24)) so (σ (.n v)) →
            σ (.n v) = gen ^ (74 + (countOrd (vtKs logMem τ)).getD r 0) := fun r hr v so hso hl => by
          subst hso
          rw [p24] at hl
          have := readsAt_getD0 hbuf0 (k := 74 + r) (by simp [sortW]; omega)
          rw [sortW_get _ (by omega), ite_neg' (by omega), ite_pos' (by omega),
            show 74 + r - 74 = r by omega] at this
          exact loadHolds_unique hl this
        obtain ⟨pl0, pm5, pm8, pl9, pm11, pm12⟩ := vt_rank0_facts h vt_push_rank0
        obtain ⟨cl0, cm5, cm8, cl9, cm11, cm12⟩ := vt_rank0_facts h vt_count_rank0
        have RP0 := rankOK (pushV 0 (by omega) pl0) (by have := pushOrd_lt (vtKs logMem τ) (r := 0) (by omega); omega)
          pm5 pm8 pl9 pm11 pm12
        have RC0 := rankOK (countV 0 (by omega) rfl cl0)
          (by have := countOrd_lt (vtKs logMem τ) (r := 0) (by omega); omega) cm5 cm8 cl9 cm11 cm12
        rcases hk with (hk | ⟨q, hq, hk⟩) | ⟨q, hq, hk⟩
        · rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact RP0.1
          · exact RP0.2.1
          · exact RP0.2.2.1
          · exact RP0.2.2.2
          · exact RC0.1
          · exact RC0.2.1
          · exact RC0.2.2.1
          · exact RC0.2.2.2
        · obtain ⟨l0, m5, m8, l9, m21, m22⟩ := vt_rankN_facts h (vt_push_ranks q hq)
          have R := rankOK (pushV (q + 1) (by omega) l0)
            (by have := pushOrd_lt (vtKs logMem τ) (r := q + 1) (by omega); omega) m5 m8 l9 m21 m22
          rcases hk with rfl | rfl | rfl | rfl
          · exact R.1
          · exact R.2.1
          · exact R.2.2.1
          · exact R.2.2.2
        · obtain ⟨l0, m5, m8, l9, m21, m22⟩ := vt_rankN_facts h (vt_count_ranks q hq)
          have R := rankOK (countV (q + 1) (by omega) (by omega) l0)
            (by have := countOrd_lt (vtKs logMem τ) (r := q + 1) (by omega); omega) m5 m8 l9 m21 m22
          rcases hk with rfl | rfl | rfl | rfl
          · exact R.1
          · exact R.2.1
          · exact R.2.2.1
          · exact R.2.2.2
    · -- the slots
      have m46 : σ (.n 4646) = σ (.n 4554) * σ (.n 4554) := h.atom 4358 (.mul (.n 4646) (.n 4554) (.n 4554)) (by decide +kernel)
      have m47 : σ (.n 4647) = σ (.n 4646) * σ (.n 4646) := h.atom 4359 (.mul (.n 4647) (.n 4646) (.n 4646)) (by decide +kernel)
      have m48 : σ (.n 4648) = σ (.n 4636) * σ (.n 4647) := h.atom 4360 (.mul (.n 4648) (.n 4636) (.n 4647)) (by decide +kernel)
      refine ownA 202 (4 * n) off ?_ (by omega) (by rw [vtSizes_202]; omega)
      rw [m48, m47, m46, h4554, p4636, ← pow_add, ← pow_add]; congr 2; ring
    · have m46 : σ (.n 4646) = σ (.n 4554) * σ (.n 4554) := h.atom 4358 (.mul (.n 4646) (.n 4554) (.n 4554)) (by decide +kernel)
      have m47 : σ (.n 4647) = σ (.n 4646) * σ (.n 4646) := h.atom 4359 (.mul (.n 4647) (.n 4646) (.n 4646)) (by decide +kernel)
      have m48 : σ (.n 4648) = σ (.n 4636) * σ (.n 4647) := h.atom 4360 (.mul (.n 4648) (.n 4636) (.n 4647)) (by decide +kernel)
      have l51 : LoadHolds rd (σ (.n 4648)) 2 (σ (.n 4651)) := h.atom 4363 (.load (.n 4651) (.n 4648) 2) (by decide +kernel)
      rw [m48, m47, m46, h4554, p4636, ← pow_add, ← pow_add, loadHolds_mul_gen_pow,
        show n + n + (n + n) + 2 = 4 * n + 2 by ring] at l51
      have e51 := loadHolds_unique l51 (zcRoundsW_get hbuf202 (r := n) le_rfl).2.2.1
      exact linA hallX off e51 (by rw [hxl]; omega)
    · rw [vtAllocPairs_eq] at ht
      obtain ⟨i, hi, hti⟩ := List.mem_iff_getElem.mp ht
      simp only [List.length_zip, List.length_append, vtSzPre_length] at hi
      have hi205 : i < 205 := by
        have : vtAllocVar.length = 205 := by decide
        omega
      rw [← hti, List.getElem_zip] at hoff ⊢
      dsimp only at hoff ⊢
      rw [← List.getD_eq_getElem _ 0]
      have hoff' : off < (vtSizes 0).getD i 0 := by
        rw [vtSizes_split, List.getD_eq_getElem _ _ (by simp [vtSzPre_length]; omega)]; exact hoff
      exact ownA i 0 off ((hptr i hi205).trans g0) hi205
        (by have := vtSizes_mono n hi205; simp only [Nat.zero_add]; omega)

end
end LeanVM.Guest.B1.VerifySub
