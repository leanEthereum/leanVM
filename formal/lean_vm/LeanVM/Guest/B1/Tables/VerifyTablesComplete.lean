/-
  LeanVM.Guest.B1.Tables.VerifyTablesComplete

  `verify_tables` is complete, placed (`CompleteTablesAt`).
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCHelp
public import LeanVM.Guest.B1.Tables.VerifyTablesCTail
public import LeanVM.Guest.B1.Tables.VerifyTablesSound
public import LeanVM.Guest.B1.Tables.VtCKids
public import LeanVM.Guest.B1.Tables.VtCAir
public import LeanVM.Guest.B1.Tables.VtSortC
public import LeanVM.Guest.B1.Tables.VtZcC
public import LeanVM.Guest.B1.Tables.VtCEv
public import LeanVM.Guest.B1.Tables.VtCGlue4
public import LeanVM.Protocol.Whir.Sound.Weights

/-!
# `verify_tables`, placed

From the run of `tablesSeg` read back (`tablesSeg_trace`), the honest buffers (`vtOwnW`) and the
callees (`vtKids`), the windows chained over the whole body give the valuation `completeAt_flatD`
asks for.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

theorem vtPre_flat : vtPre.all Stmt.flat = true := by decide +kernel

theorem vtPre_addrs : vtPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem vtPre_length : vtPre.length = 7899 := by decide +kernel

theorem vt_not_loop : coreProgram.loop "verify_tables" = false := by decide +kernel

theorem exists_eq_foldl_max (f : ℕ → ℕ) : ∀ m, 0 < m → ∃ t < m, f t = ((List.range m).map f).foldl max 0
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | m + 1, _ => by
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨t, ht, he⟩ := exists_eq_foldl_max f m hm
      rcases le_total (((List.range m).map f).foldl max 0) (f m) with h | h
      · exact ⟨m, by omega, by rw [max_eq_right h]⟩
      · exact ⟨t, by omega, by rw [max_eq_left h, he]⟩

theorem prodE_take_map (ch : ℕ → E) {n j : ℕ} (hj : j ≤ n) :
    prodE (((List.range n).map ch).take j) = ∏ i ∈ Finset.range j, ch i := by
  rw [prodE_eq_prod, List.length_take, List.length_map, List.length_range, min_eq_left hj]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take, List.getElem_map, List.getElem_range]

theorem eqEval_take {point chis : List E} {k : ℕ} (hp : k ≤ point.length) (hc : k ≤ chis.length) :
    eqEval (point.take k) (chis.take k) = ∏ j ∈ Finset.range k, (1 + point.getD j 0 + chis.getD j 0) := by
  rw [LeanVM.Protocol.Whir.Sound.eqEval_eq_prod _ _ (by simp [List.length_take]; omega), Fin.prod_univ_eq_prod_range
    (fun j => 1 + (point.take k).getD j 0 + (chis.take k).getD j 0)]
  rw [List.length_take, min_eq_left hp]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hj', ↓reduceIte]

/-- The alloc values' positions: the first five, the two index chains, the table sumcheck's three,
and the selectors' three each. -/
def selIdx (i : ℕ) : ℕ := if i < 8 then 0 else if i < 11 then 1 else if i < 15 then 2 else (i - 16) / 3 + 3
def selK (i : ℕ) : ℕ := if i < 8 then i - 5 else if i < 11 then i - 8 else if i < 15 then i - 12 else (i - 16) % 3

theorem vt_alloc_cover : ∀ i < 205, (i < 5 ∨ i = 11 ∨ i = 15 ∨ 202 ≤ i) ∨
    (selIdx i < 65 ∧ selK i < 3 ∧ selBuf (selIdx i) + selK i = i) := by decide +kernel

theorem vt_alloc_sel : ∀ j < 65, ∀ k < 3, vtAllocVar.getD (selBuf j + k) 0 =
    selVal.getD j 0 + [12, 15, 16].getD k 0 := by decide +kernel

theorem selPost_stable {point : List E} {ks off : ℕ → ℕ} {ptr : ℕ → E} {i m : ℕ} {σ1 σ2 : Val}
    (hm : selVal.getD i 0 + 27 ≤ m) (hag : ∀ k < m, σ2 (.n k) = σ1 (.n k))
    (hp : SelPost point ks off ptr i σ1) : SelPost point ks off ptr i σ2 := by
  unfold SelPost at hp ⊢; simp +contextual (disch := omega) only [hag]; exact hp

theorem selVal_le : ∀ i < 65, selVal.getD i 0 + 27 ≤ 4554 := by decide +kernel

/-- An index chain's end, read at `p·g^m`. -/
theorem idx_val {rd : Reader} {p : E} {m : ℕ} {point : List E} (hm : m ≤ point.length) (hm42 : m < 42)
    (hp : ReadsAt rd p (idxChainW point m)) {v : E} (hv : LoadHolds rd (p * gen ^ m) 0 v) :
    v = indexMle (point.take m) := by
  rw [loadHolds_gen_pow_mul, Nat.add_zero] at hv
  have := hp m (by simp [idxChainW]; omega)
  simp only [idxChainW, List.getElem_map, List.getElem_range, le_refl, ↓reduceIte] at this
  rw [loadHolds_unique hv this, indexMle_eq, List.length_take, min_eq_left hm]
  exact Finset.prod_congr rfl fun t ht => by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (Finset.mem_range.mp ht)]

theorem evVal_lt : ∀ j < 104, evVal.getD j 0 < 8140 := by decide +kernel

theorem airStart_lt : ∀ t < 6, airStart.getD t 0 + 1 ≤ 7854 := by decide

section
variable {rd : Reader}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **Statements `0 ..< 4273`**: the prelude, the block order, the padding weights, `idxc_tab`, the
selectors and the bus's sums and reads. -/
theorem vt_pre4273 {κ : ℕ} (hκ : 7 ≤ κ) (hlow : LowDef κ rd) {σ : Val}
    {cur zeta bk sq fpw pool cplen dims rowsP bv mF bF m0 m1 m2 : E} {point : List E} {logMem : ℕ}
    {rowsN : List ℕ} {cv : Digest} {ptr : ℕ → E}
    (hcv : (σ (.n 0), σ (.n 1)) = digestScalars cv) (h2 : σ (.n 2) = cur) (h5 : σ (.n 5) = zeta)
    (h6 : σ (.n 6) = gen ^ point.length) (h7 : σ (.n 7) = dims) (h8 : σ (.n 8) = rowsP)
    (h9 : σ (.n 9) = bk) (h10 : σ (.n 10) = sq) (h11 : σ (.n 11) = fpw) (h13 : σ (.n 13) = pool)
    (h14 : σ (.n 14) = cplen)
    (hrl : rowsN.length = 6) (hτ : ∀ t < 6, log2Ceil (rowsN.getD t 0) < 29)
    (hτp : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ point.length) (h16 : 16 ≤ logMem) (h32 : logMem ≤ 32)
    (hlmp : logMem ≤ point.length) (h18p : 18 ≤ point.length) (hpl : point.length < 33)
    (hso1 : ∀ r < 37, LoadHolds rd (ptr 0) r
      (gen ^ (stackOrder ((List.range 37).map (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))))).getD r 0))
    (hso2 : ∀ r < 28, LoadHolds rd (ptr 0) (74 + r)
      (gen ^ (74 + (stackOrder ((List.range 28).map fun i =>
        vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) (74 + i))).getD r 0)))
    (hside : ∀ b < 102, LoadHolds rd (ptr 1) b (word (vtBlockSide b) 0 0))
    (hbk : ∀ b < 102, LoadHolds rd bk b (gen ^ vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) b))
    (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (hoff1 : ∀ i < 37, LoadHolds rd (ptr 2) i (gen ^ (stackOffsets ((List.range 37).map
      (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)))).1.getD i 0))
    (hoff2 : ∀ i < 28, LoadHolds rd (ptr 2) (74 + i) (gen ^ (stackOffsets ((List.range 28).map fun i =>
      vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) (74 + i))).1.getD i 0))
    (hdims : ReadsAt rd dims (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n))
    (hrows : ReadsAt rd rowsP (rowsN.map eOfNat)) (hz : ReadsAt rd zeta point)
    (hidx : ∀ t < 34, LoadHolds rd (ptr 3) t (1 + gen ^ 2 ^ t))
    (hm : ∀ i < 65, SelMem rd bk (ptr 2) point (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
      (selOff (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))) ptr i)
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v)
    (hpI2 : ReadsAt rd (ptr 11) (idxChainW point logMem))
    (hb1 : LoadHolds rd (ptr 4) 1 ((idxChainW point logMem).getD logMem 0))
    (hpI3 : ReadsAt rd (ptr 15) (idxChainW point 18)) (hb2 : LoadHolds rd (ptr 4) 2 ((idxChainW point 18).getD 18 0))
    (hcur : ReadsAt rd cur [m0, m1, m2, mF, bF]) (hpool : ReadsAt rd pool [m0, m1, m2, mF, bF])
    (hcpl : ∀ j < 4, LoadHolds rd cplen j (gen ^ logMem)) (hcpl4 : LoadHolds rd cplen 4 (gen ^ 18)) :
    Completes (coreProgram.Rel rd) rd 19 4554
      ((vtPre.drop 0).take ((213 + (1225 + (67 + 69))) + ((3 + (28 + (11 + (28 + (80 + (28 + 56)))))) +
        ((2798 - 1808) + (28 + (571 + ((4206 - 3397) + (28 + (4273 - 4234))))))))) σ (fun σ' =>
      σ' (.n 19) = σ (.n 0) ∧ σ' (.n 20) = σ (.n 1) ∧ σ' (.n 21) = σ (.n 16) ∧
        σ' (.n 22) = σ (.n 17) ∧ σ' (.n 23) = σ (.n 18) ∧ σ' (.n 24) = ptr 0 ∧ σ' (.n 25) = ptr 1 ∧
        σ' (.n 128) = ptr 2 ∧ σ' (.n 1732) = bv ∧
        (∀ t < 6, σ' (.n (1739 + 14 * t)) =
          paddingWeight (point.take (log2Ceil (rowsN.getD t 0))) (rowsN.getD t 0)) ∧
        σ' (.n 1817) = ptr 3 ∧ σ' (.n 1852) = ptr 4 ∧ σ' (.n 1925) = ptr 11 ∧ σ' (.n 2029) = ptr 15 ∧
        (∀ i < 65, SelPost point (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
          (selOff (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))) ptr i σ') ∧
        σ' (.n 1937) = m0 ∧ σ' (.n 1955) = m1 ∧ σ' (.n 1973) = m2 ∧ σ' (.n 3359) = mF ∧
        σ' (.n 3409) = bF ∧
        (σ' (.n 3422), σ' (.n 3423)) = digestScalars (obsCv (obsCv (obsAll cv [m0, m1, m2]) mF) bF)) := by
  have hk1 : vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) (selBlk.getD 1 0) = logMem := by
    simp [vtKs, blockKappaSrc, blockKappaAdj, selBlk]
  have hk2 : vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) (selBlk.getD 2 0) = 18 := by
    simp [vtKs, blockKappaSrc, blockKappaAdj, selBlk]
  have k38 : vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) 38 = logMem := by
    simp [vtKs, blockKappaSrc, blockKappaAdj]
  have k39 : vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) 39 = 18 := by
    simp [vtKs, blockKappaSrc, blockKappaAdj]
  have hks := vtKs_lt h32 hτ
  have hcur3 : ReadsAt rd cur [m0, m1, m2] := fun k hk => by
    have hk' : k < 3 := by simpa using hk
    have := hcur k (by simp; omega)
    interval_cases k <;> exact this
  have hpool3 : ReadsAt rd pool [m0, m1, m2] := fun k hk => by
    have hk' : k < 3 := by simpa using hk
    have := hpool k (by simp; omega)
    interval_cases k <;> exact this
  refine (vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
    (vt_phaseA vt_sort_complete hκ hlow (bv := bv) hks h5 h7 h8 h9 h10 hso1 hso2 hside hbk hsq hoff1 hoff2
      hdims hrows hz hrl hτ hτp hidx)
    (by vt_stable) fun σ1 e1 p1 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_phaseB1 vt_sel_complete vt_glue1 vt_glue2 vt_glue3 (by omega) hlow (σ := σ1) (cv := cv)
        (by rw [Ext.app' e1 2 (by norm_num), h2]) (by rw [Ext.app' e1 5 (by norm_num), h5])
        (by rw [Ext.app' e1 6 (by norm_num), h6]) (by rw [Ext.app' e1 9 (by norm_num), h9])
        (by rw [Ext.app' e1 10 (by norm_num), h10]) (by rw [Ext.app' e1 11 (by norm_num), h11])
        (by rw [Ext.app' e1 13 (by norm_num), h13]) (by rw [Ext.app' e1 14 (by norm_num), h14])
        (by rw [p1.1, p1.2.1, hcv]) p1.2.2.2.2.2.2.2.1 p1.2.2.2.2.2.2.2.2.2.2
        hpl hz hsq hm hfpw hidx hk1 hk2 (by omega) hlmp h32 h18p hpI2 hb1 hpI3 hb2 hcur3 hpool3
        (fun j hj => hcpl j (by omega)))
      (fun σ1 σ2 hag hp => by
        obtain ⟨q1, q2, q3⟩ := hp
        refine ⟨by rw [hag _ (by norm_num), q1], fun i hi => selPost_stable (m := 2077)
          (by interval_cases i <;> decide) hag (q2 i hi), ?_⟩
        simp only [hag _ (by norm_num : 1925 < 2077), hag _ (by norm_num : 1937 < 2077),
          hag _ (by norm_num : 1955 < 2077), hag _ (by norm_num : 1973 < 2077),
          hag _ (by norm_num : 1986 < 2077), hag _ (by norm_num : 1987 < 2077),
          hag _ (by norm_num : 2029 < 2077)]
        exact q3) fun σ2 e2 p2 =>
    vt_phaseB2 vt_sel_complete vt_glue4 (by omega) hlow (σ := σ2) (cv := obsAll cv [m0, m1, m2])
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h2)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h5)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h6)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h9)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h10)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h11)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h13)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h14)
      (by simp (disch := omega) only [Ext.app' e2]; exact p1.2.2.2.2.2.2.2.1)
      p2.1 p2.2.2.2.2.2.2.1 hpl hz hsq hm hbk hks hfpw (hcur 3 (by norm_num)) (hcur 4 (by norm_num))
      (fun j hj => ⟨_, hpool j (by simp; omega)⟩) (hpool 3 (by norm_num)) (hpool 4 (by norm_num))
      (by rw [k38]; exact hcpl 3 (by norm_num)) (by rw [k39]; exact hcpl4) ⟨_, hb1⟩ ⟨_, hb2⟩).mono
    le_rfl le_rfl ?_
  rintro σ' ⟨⟨c19, c20, c21, c22, c23, q24, q25, q128, b0, hpw, q1817⟩, ⟨q1852, s3, q25', q37, q55, q73, -, q29⟩,
    r1, r36, q59, q09, q22, r2, r64⟩
  refine ⟨c19, c20, c21, c22, c23, q24, q25, q128, b0, fun t ht => (hpw t ht).2, q1817, q1852, q25', q29,
    fun i hi => ?_, q37, q55, q73, q59, q09, q22⟩
  by_cases a3 : i < 3
  · exact s3 i a3
  by_cases a36 : i < 36
  · simpa [show 3 + (i - 3) = i by omega] using r1 (i - 3) (by omega)
  by_cases a37 : i < 37
  · obtain rfl : i = 36 := by omega
    exact r36
  by_cases a64 : i < 64
  · simpa [show 37 + (i - 37) = i by omega] using r2 (i - 37) (by omega)
  · obtain rfl : i = 64 := by omega
    exact r64

end

section
variable {rd : Reader}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- **The whole body completes** on the run read back: its returns, `g^n`, the pointers. -/
theorem vt_body {κ : ℕ} (hκ : 7 ≤ κ) (hlow : LowDef κ rd) {σ : Val}
    {cur zeta bk sq fpw pool cplen dims rowsP beta chiP bv mF bF m0 m1 m2 v0 v1 v2 : E}
    {point alphas : List E} {logMem : ℕ} {rowsN : List ℕ} {cv pi : Digest} {ptr : ℕ → E}
    {bytecode : List K} {cl : ℕ → E} {cvr : ℕ → Digest} {wsr : ℕ → List E} {ch : ℕ → E}
    {evss : List (List E)}
    (hcv : (σ (.n 0), σ (.n 1)) = digestScalars cv) (h2 : σ (.n 2) = cur) (h3 : σ (.n 3) = (digestScalars pi).1)
    (h4 : σ (.n 4) = (digestScalars pi).2) (h5 : σ (.n 5) = zeta)
    (h6 : σ (.n 6) = gen ^ point.length) (h7 : σ (.n 7) = dims) (h8 : σ (.n 8) = rowsP)
    (h9 : σ (.n 9) = bk) (h10 : σ (.n 10) = sq) (h11 : σ (.n 11) = fpw) (h12 : σ (.n 12) = beta)
    (h13 : σ (.n 13) = pool) (h14 : σ (.n 14) = cplen) (h15 : σ (.n 15) = chiP) (h16 : σ (.n 16) = v0)
    (h17 : σ (.n 17) = v1) (h18 : σ (.n 18) = v2)
    (hb : bytecode.length = 2 ^ 22) (hal : alphas.length = 4)
    (hrl : rowsN.length = 6) (hτ : ∀ t < 6, log2Ceil (rowsN.getD t 0) < 29)
    (hτp : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ point.length) (hlm16 : 16 ≤ logMem) (h32 : logMem ≤ 32)
    (hlmp : logMem ≤ point.length) (h18p : 18 ≤ point.length) (hpl : point.length < 33)
    (hso1 : ∀ r < 37, LoadHolds rd (ptr 0) r (gen ^ (stackOrder ((List.range 37).map (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))))).getD r 0))
    (hso2 : ∀ r < 28, LoadHolds rd (ptr 0) (74 + r)
      (gen ^ (74 + (stackOrder ((List.range 28).map fun i => (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (74 + i))).getD r 0)))
    (hside : ∀ b < 102, LoadHolds rd (ptr 1) b (word (vtBlockSide b) 0 0))
    (hbk : ∀ b < 102, LoadHolds rd bk b (gen ^ (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) b))
    (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (hoff1 : ∀ i < 37, LoadHolds rd (ptr 2) i (gen ^ (stackOffsets ((List.range 37).map (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))))).1.getD i 0))
    (hoff2 : ∀ i < 28, LoadHolds rd (ptr 2) (74 + i)
      (gen ^ (stackOffsets ((List.range 28).map fun i => (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (74 + i))).1.getD i 0))
    (hdims : ReadsAt rd dims (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n))
    (hrows : ReadsAt rd rowsP (rowsN.map eOfNat)) (hz : ReadsAt rd zeta point)
    (hidx : ∀ t < 34, LoadHolds rd (ptr 3) t (1 + gen ^ 2 ^ t))
    (hm : ∀ i < 65, SelMem rd bk (ptr 2) point (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (selOff (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)))) ptr i)
    (hfpwR : ReadsAt rd fpw (eqKernel alphas))
    (hpI2 : ReadsAt rd (ptr 11) (idxChainW point logMem))
    (hb1 : LoadHolds rd (ptr 4) 1 ((idxChainW point logMem).getD logMem 0))
    (hpI3 : ReadsAt rd (ptr 15) (idxChainW point 18)) (hb2 : LoadHolds rd (ptr 4) 2 ((idxChainW point 18).getD 18 0))
    (hcur : ReadsAt rd cur [m0, m1, m2, mF, bF]) (hpool : ReadsAt rd pool [m0, m1, m2, mF, bF])
    (hcpl : ∀ j < 4, LoadHolds rd cplen j (gen ^ logMem)) (hcpl4 : LoadHolds rd cplen 4 (gen ^ 18))
    (hcl0 : cl 0 = dot ((powers (challengeOf (sqCv (obsAll cv [m0, m1, m2, mF, bF]))) (vtNC + 3)).drop vtNC) (busVal (layoutOf bytecode logMem rowsN) alphas beta point [v0, v1, v2] [m0, m1, m2] mF bF bv).totals)
    (hcvr0 : cvr 0 = sqCv (obsAll cv [m0, m1, m2, mF, bF]))
    (hrnd : ∀ r < vtN (layoutOf bytecode logMem rowsN), RunsTo (roundPoly 4 (cl r) none) (cvr r) (wsr r) (cl (r + 1), ch r) (cvr (r + 1)))
    (hshape : evss.map List.length = vtEvalVars.map List.length) (hflat : evss.flatten.length = 104)
    (hfin : (ttVal ((powers (challengeOf (sqCv (obsAll cv [m0, m1, m2, mF, bF]))) (vtNC + 3)).take vtNC) ((powers (challengeOf (sqCv (obsAll cv [m0, m1, m2, mF, bF]))) (vtNC + 3)).drop vtNC)
      ((List.range (vtN (layoutOf bytecode logMem rowsN))).map ch).reverse (vtRows (layoutOf bytecode logMem rowsN) (busVal (layoutOf bytecode logMem rowsN) alphas beta point [v0, v1, v2] [m0, m1, m2] mF bF bv) ((List.range (vtN (layoutOf bytecode logMem rowsN))).map ch).reverse) evss 0 0 []).1 = cl (vtN (layoutOf bytecode logMem rowsN)))
    (hxs5 : ReadsAt rd (cur * gen ^ 5) ((List.range (vtN (layoutOf bytecode logMem rowsN))).flatMap wsr ++ evss.flatten))
    (hchi : ReadsAt rd chiP ((List.range (vtN (layoutOf bytecode logMem rowsN))).map ch).reverse)
    (hpR : ReadsAt rd (ptr 202) (zcRoundsW cvr cur cl (vtN (layoutOf bytecode logMem rowsN))))
    (hpC : ReadsAt rd (ptr 203) (zcCprodW ch (vtN (layoutOf bytecode logMem rowsN))))
    (hpP : ReadsAt rd (ptr 204) (zcPeqW point ((List.range (vtN (layoutOf bytecode logMem rowsN))).map ch).reverse (vtN (layoutOf bytecode logMem rowsN))))
    (hpoolE : ∀ j < 104, LoadHolds rd pool (5 + j) (evss.flatten.getD j 0))
    (h109 : LoadHolds rd pool 109 (ofK ((digestScalars pi).1.limb 0) +
      challengeOf (sqCv (obsAll (cvr (vtN (layoutOf bytecode logMem rowsN))) evss.flatten)) * (ofK ((digestScalars pi).1.limb 0) + ofK ((digestScalars pi).2.limb 0))))
    (h110 : LoadHolds rd pool 110 (ofK ((digestScalars pi).1.limb 1) +
      challengeOf (sqCv (obsAll (cvr (vtN (layoutOf bytecode logMem rowsN))) evss.flatten)) * (ofK ((digestScalars pi).1.limb 1) + ofK ((digestScalars pi).2.limb 1))))
    (h111 : LoadHolds rd pool 111 0)
    (hcplT : ∀ t < 6, ∀ j < evCnt.getD t 0, LoadHolds rd cplen (5 + (evFirst.getD t 0 + j))
      (gen ^ log2Ceil (rowsN.getD t 0))) :
    Completes (coreProgram.Rel rd) rd 19 8179 ((vtPre.drop 0).take ((((213 + (1225 + (67 + 69))) + ((3 + (28 + (11 + (28 + (80 + (28 + 56)))))) + ((2798 - 1808) + (28 + (571 + ((4206 - 3397) + (28 + (4273 - 4234)))))))) + (101 + (1 + (16 * 15 + ((4863 - 4615) + (16 * 15 + ((5392 - 5103) + (16 * 8 + ((5669 - 5520) + (16 * 15 + ((6192 - 5909) + (16 * 14 + ((6694 - 6416) + (16 * 37 + ((7854 - 7286)))))))))))))))) + 45)) σ
      (fun σ' => (∀ i < 65, SelPost point (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (selOff (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)))) ptr i σ') ∧ σ' (.n 24) = ptr 0 ∧
        σ' (.n 25) = ptr 1 ∧ σ' (.n 128) = ptr 2 ∧ σ' (.n 1817) = ptr 3 ∧ σ' (.n 1852) = ptr 4 ∧
        σ' (.n 1925) = ptr 11 ∧ σ' (.n 2029) = ptr 15 ∧ σ' (.n 4636) = ptr 202 ∧ σ' (.n 4639) = ptr 203 ∧
        σ' (.n 4655) = ptr 204 ∧ σ' (.n 4554) = gen ^ vtN (layoutOf bytecode logMem rowsN) ∧
        σ' (.n 8171) = (digestScalars (sqCv (obsAll (cvr (vtN (layoutOf bytecode logMem rowsN))) evss.flatten))).1 ∧
        σ' (.n 8172) = (digestScalars (sqCv (obsAll (cvr (vtN (layoutOf bytecode logMem rowsN))) evss.flatten))).2 ∧
        σ' (.n 8175) = cur * gen ^ (5 + 3 * vtN (layoutOf bytecode logMem rowsN)) * gen ^ 104 ∧ σ' (.n 8176) = gen ^ vtN (layoutOf bytecode logMem rowsN) ∧
        σ' (.n 8177) = bv ∧ σ' (.n 8178) = challengeOf (sqCv (obsAll (cvr (vtN (layoutOf bytecode logMem rowsN))) evss.flatten))) := by
  set L := layoutOf bytecode logMem rowsN with hL
  set τs : ℕ → ℕ := (fun t => log2Ceil (rowsN.getD t 0)) with hτs
  set n := vtN (layoutOf bytecode logMem rowsN) with hn
  set chis := ((List.range (vtN (layoutOf bytecode logMem rowsN))).map ch).reverse with hchis
  have hheights : L.tableLogHeights = (List.range 6).map τs := by
    show rowsN.map log2Ceil = _
    apply List.ext_getElem (by simp [hrl])
    intro t h1 h2
    simp only [List.getElem_map, List.getElem_range, hτs]
    rw [List.getD_eq_getElem _ _ (by simpa [hrl] using h1)]
  have hnf : n = ((List.range 6).map τs).foldl max 0 := by rw [hn, vtN, hheights]
  have hτn : ∀ t < 6, τs t ≤ n := fun t ht => by
    rw [hnf]; exact vt_le_foldl_max _ 0 _ (Or.inl (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))
  obtain ⟨tmax, htm, htmx⟩ := exists_eq_foldl_max τs 6 (by norm_num)
  have hnp : n ≤ point.length := by rw [hnf, ← htmx]; exact hτp tmax htm
  have hdimsT : ∀ t < 6, LoadHolds rd dims (t + 1) (gen ^ τs t) := fun t ht => by
    have := hdims (t + 1) (by simp; omega)
    simp only [List.getElem_cons_succ, List.getElem_map] at this
    have e : τs t = log2Ceil rowsN[t] := by simp only [hτs]; rw [List.getD_eq_getElem _ _ (by omega)]
    rw [e]; exact this
  have hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v := fun i hi =>
    ⟨_, hfpwR i (by rw [length_eqKernel, hal]; norm_num; omega)⟩
  have hws5 : ReadsAt rd (cur * gen ^ 5) ((List.range n).flatMap wsr) := (Main.readsAt_append'.mp hxs5).1
  have hwsl : ((List.range n).flatMap wsr).length = 3 * n := by
    rw [List.length_flatMap]
    have : ∀ r ∈ List.range n, (wsr r).length = 3 := fun r hr =>
      RunsTo.roundPoly4_inv (hrnd r (List.mem_range.mp hr))
    rw [List.map_congr_left this]; simp [Nat.mul_comm]
  have hev : ReadsAt rd (cur * gen ^ (5 + 3 * n)) evss.flatten := by
    have := (Main.readsAt_append'.mp hxs5).2
    rwa [hwsl, mul_assoc, ← pow_add] at this
  have hcvE : cvE (cvr n) (fun j => evss.flatten.getD j 0) 104 = obsAll (cvr n) evss.flatten := by
    rw [cvE]; congr 1
    apply List.ext_getElem (by simp [hflat])
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ h2]
  have hk1 : (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (selBlk.getD 1 0) = logMem := by simp [vtKs, blockKappaSrc, blockKappaAdj, selBlk]
  have hk2 : (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (selBlk.getD 2 0) = 18 := by simp [vtKs, blockKappaSrc, blockKappaAdj, selBlk]
  have stQ1 : ∀ (P : Val → Prop), (∀ σ1 σ2 : Val, (∀ k < 4554, σ2 (.n k) = σ1 (.n k)) → P σ1 → P σ2) →
      ∀ m, 4554 ≤ m → ∀ σ1 σ2 : Val, (∀ k < m, σ2 (.n k) = σ1 (.n k)) → P σ1 → P σ2 :=
    fun P hP m hm σ1 σ2 hag => hP σ1 σ2 fun k hk => hag k (by omega)
  have hP2 : CeExEval := fun t ρ χ xi hxi => ceEx_eval t ρ χ xi hxi
  have hP4 : PushTotalEval := fun hsh => pushTotalEx_eval hsh
  have hP5 : PullTotalEval := fun hsh => pullTotalEx_eval hsh
  have hP6 : CountTotalEval := fun hsh => countTotalEx_eval hsh
  have hpool3 : ReadsAt rd pool [m0, m1, m2] := fun k hk => by
    have hk' : k < 3 := by simpa using hk
    have := hpool k (by simp; omega)
    interval_cases k <;> exact this
  have hs1 : selVal.getD 1 0 = 1893 := rfl
  have hs2 : selVal.getD 2 0 = 1997 := rfl
  have X1 := vt_pre4273 hκ hlow (bv := bv) (mF := mF) (bF := bF) (m0 := m0) (m1 := m1) (m2 := m2) (cv := cv)
    (ptr := ptr) hcv h2 h5 h6 h7 h8 h9 h10 h11 h13 h14 hrl hτ hτp hlm16 h32 hlmp h18p hpl hso1 hso2 hside hbk hsq
    hoff1 hoff2 hdims hrows hz hidx hm hfpw hpI2 hb1 hpI3 hb2 hcur hpool hcpl hcpl4
  have X := vt_consH (hi := 8140) (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel)) X1
    (fun σ1 σ2 hag ⟨c19, c20, c21, c22, c23, q24, q25, q128, b0, hpw, q1817, q1852, q1925, q2029, hsel, q37,
      q55, q73, q59, q09, q22⟩ => ⟨by rw [hag _ (by norm_num)]; exact c19, by rw [hag _ (by norm_num)]; exact c20,
      by rw [hag _ (by norm_num)]; exact c21, by rw [hag _ (by norm_num)]; exact c22,
      by rw [hag _ (by norm_num)]; exact c23, by rw [hag _ (by norm_num)]; exact q24,
      by rw [hag _ (by norm_num)]; exact q25, by rw [hag _ (by norm_num)]; exact q128,
      by rw [hag _ (by norm_num)]; exact b0, fun t ht => by rw [hag _ (by omega)]; exact hpw t ht,
      by rw [hag _ (by norm_num)]; exact q1817, by rw [hag _ (by norm_num)]; exact q1852,
      by rw [hag _ (by norm_num)]; exact q1925, by rw [hag _ (by norm_num)]; exact q2029,
      fun i hi => selPost_stable (selVal_le i hi) hag (hsel i hi), by rw [hag _ (by norm_num)]; exact q37,
      by rw [hag _ (by norm_num)]; exact q55, by rw [hag _ (by norm_num)]; exact q73,
      by rw [hag _ (by norm_num)]; exact q59, by rw [hag _ (by norm_num)]; exact q09,
      by rw [hag _ (by norm_num), hag _ (by norm_num)]; exact q22⟩)
    fun σ3 e3 q1 hh3 => by
      obtain ⟨c19, c20, c21, c22, c23, q24, q25, q128, b0, hpw, q1817, q1852, q1925, q2029, hsel, q37,
        q55, q73, q59, q09, q22⟩ := q1
      have hvh : VtHoldsAt 4273 rd σ3 := ⟨_, hh3 True (fun _ => True) trivial⟩
      have e12 : σ3 (.n 12) = beta := by rw [Ext.app' e3 12 (by norm_num), h12]
      have e11 : σ3 (.n 11) = fpw := by rw [Ext.app' e3 11 (by norm_num), h11]
      have e13 : σ3 (.n 13) = pool := by rw [Ext.app' e3 13 (by norm_num), h13]
      have a1 := hvh.atom 1656 (.mul (.n 1930) (.n 1925) (.n 1893)) (by decide +kernel)
      have a2 := hvh.atom 1657 (.load (.n 1931) (.n 1930) 0) (by decide +kernel)
      have a3 := hvh.atom 1658 (.load (.n 1931) (.n 1852) 1) (by decide +kernel)
      have b1 := hvh.atom 1764 (.mul (.n 2034) (.n 2029) (.n 1997)) (by decide +kernel)
      have b2 := hvh.atom 1765 (.load (.n 2035) (.n 2034) 0) (by decide +kernel)
      have b3 := hvh.atom 1766 (.load (.n 2035) (.n 1852) 2) (by decide +kernel)
      simp only [Atom.Holds] at a1 a2 a3 b1 b2 b3
      have g1893 : σ3 (.n 1893) = gen ^ logMem := by
        have := (hsel 1 (by norm_num)).2.1; rw [hs1, hk1] at this; exact this
      have g1997 : σ3 (.n 1997) = gen ^ 18 := by
        have := (hsel 2 (by norm_num)).2.1; rw [hs2, hk2] at this; exact this
      rw [a1, q1925, g1893] at a2
      rw [b1, q2029, g1997] at b2
      have hidx1 := idx_val hlmp (by omega) hpI2 a2
      have hidx2 := idx_val h18p (by norm_num) hpI3 b2
      have hm3 : ReadsAt rd (σ3 (.n 13)) [σ3 (.n 1937), σ3 (.n 1955), σ3 (.n 1973)] := by
        rw [e13, q37, q55, q73]; exact hpool3
      have tot := vt_totals_c hP4 hP5 hP6 hb hrl hal hvh (by rw [e11]; exact hfpwR) a3 b3 hm3
        (fun i hi => by rw [vt_sel_push hb logMem hrl hi]; exact (hsel i (by omega)).1)
        (fun j hj => by rw [vt_sel_count hb logMem hrl hj]; exact (hsel (37 + j) (by omega)).1)
        hpw hidx1 hidx2
      rw [e12, c21, c22, c23, h16, h17, h18, q37, q55, q73, q59, q09, b0] at tot
      have hcl0' : cl 0 = challengeOf (sqCv (obsCv (obsCv (obsAll cv [m0, m1, m2]) mF) bF)) ^ 2 * σ3 (.n 3326) +
          challengeOf (sqCv (obsCv (obsCv (obsAll cv [m0, m1, m2]) mF) bF)) ^ 3 * σ3 (.n 3705) +
          challengeOf (sqCv (obsCv (obsCv (obsAll cv [m0, m1, m2]) mF) bF)) ^ 4 * σ3 (.n 4553) := by
        rw [hcl0, tot]; exact vt_target_dot _ _ _ _
      exact vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
        (vt_zc_complete κ (by omega) rd hlow σ3 dims chiP zeta cur (ptr 202) (ptr 203) (ptr 204)
          (σ3 (.n 3326)) (σ3 (.n 3705)) (σ3 (.n 4553)) point chis τs n
          (obsCv (obsCv (obsAll cv [m0, m1, m2]) mF) bF) cl cvr wsr ch
          (by rw [Ext.app' e3 7 (by norm_num), h7]) (by rw [Ext.app' e3 6 (by norm_num), h6])
          (by rw [Ext.app' e3 2 (by norm_num), h2]) (by rw [Ext.app' e3 15 (by norm_num), h15])
          (by rw [Ext.app' e3 5 (by norm_num), h5]) q22 rfl rfl rfl hdimsT hτn
          ⟨tmax, htm, htmx.trans hnf.symm⟩ hnp hpl hz hchi rfl hcl0' hcvr0 hrnd hws5 hpR hpC hpP)
        (by vt_stable) fun σ4 e4 z4 =>
        vt_phaseD vt_ev_complete vt_air_complete (σ := σ4) (cur := cur * gen ^ (5 + 3 * n)) (pool := pool)
          (cplen := cplen) (fpw := fpw) (dims := dims) (pC := ptr 203) (pP := ptr 204) (n := n) (τ := τs)
          (ws := fun j => evss.flatten.getD j 0) (cv0 := cvr n)
          (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3]; exact h7)
          (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3]; exact h11)
          (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3]; exact h13)
          (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3]; exact h14)
          z4.1 z4.2.2.2.2.1 z4.2.2.2.2.2.1 z4.2.2.2.2.2.2.2.1 z4.2.2.2.2.2.2.1 hdimsT hτn hfpw
          (fun t ht => ⟨_, hpC (n - τs t) (by simp only [zcCprodW, List.length_map, List.length_range]; omega)⟩)
          (fun t ht => ⟨_, hpP (τs t) (by simp only [zcPeqW, List.length_map, List.length_range]; have := hτn t ht; omega)⟩)
          (fun j hj => ⟨by have := hev j (by omega); rwa [List.getD_eq_getElem _ _ (by omega)], hpoolE j hj⟩)
          hcplT
  have XR := X.mono (P := _) (Q := fun σ' => (∀ i < 65, SelPost point (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (selOff (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)))) ptr i σ') ∧
      σ' (.n 24) = ptr 0 ∧ σ' (.n 25) = ptr 1 ∧ σ' (.n 128) = ptr 2 ∧ σ' (.n 1817) = ptr 3 ∧
      σ' (.n 1852) = ptr 4 ∧ σ' (.n 1925) = ptr 11 ∧ σ' (.n 2029) = ptr 15 ∧ σ' (.n 4636) = ptr 202 ∧
      σ' (.n 4639) = ptr 203 ∧ σ' (.n 4655) = ptr 204 ∧ σ' (.n 4554) = gen ^ n ∧
      σ' (.n 4651) = cur * gen ^ (5 + 3 * n) ∧ σ' (.n 4652) = cl n ∧ σ' (.n 1732) = bv ∧
      σ' (.n 1937) = m0 ∧ σ' (.n 1955) = m1 ∧ σ' (.n 1973) = m2 ∧
      (∀ k < 5, σ' (.n (4622 + k)) = (challengeOf (sqCv (obsAll cv [m0, m1, m2, mF, bF]))) ^ k) ∧
      (∀ j < 104, σ' (.n (evVal.getD j 0)) = evss.flatten.getD j 0) ∧
      (σ' (.n 7569), σ' (.n 7570)) = digestScalars (obsAll (cvr n) evss.flatten)) le_rfl le_rfl
    (fun σ' ⟨⟨_, _, _, _, _, q24, q25, q128, b0, _, q1817, q1852, q1925, q2029, hsel, q37, q55, q73, _, _, _⟩,
      ⟨z54, _, zxi, z36, z39, z55, _, z51, z52⟩, ⟨dev, dst⟩⟩ =>
      ⟨hsel, q24, q25, q128, q1817, q1852, q1925, q2029, z36, z39, z55, z54, z51, z52, b0, q37, q55, q73,
        zxi, dev, by rw [← hcvE]; exact dst⟩)
  refine (vt_consH (hi := 8179) (Q := fun σ'' =>
      σ'' (.n 8171) = (digestScalars (sqCv (obsAll (cvr n) evss.flatten))).1 ∧
      σ'' (.n 8172) = (digestScalars (sqCv (obsAll (cvr n) evss.flatten))).2 ∧
      σ'' (.n 8175) = cur * gen ^ (5 + 3 * n) * gen ^ 104 ∧ σ'' (.n 8176) = gen ^ n ∧ σ'' (.n 8177) = bv ∧
      σ'' (.n 8178) = challengeOf (sqCv (obsAll (cvr n) evss.flatten))) (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel)) XR
    (fun σ1 σ2 hag ⟨hsel, q24, q25, q128, q1817, q1852, q1925, q2029, z36, z39, z55, z54, z51, z52, b0, q37,
      q55, q73, zxi, dev, dst⟩ => ⟨fun i hi => selPost_stable (m := 8140) (by have := selVal_le i hi; omega)
        hag (hsel i hi), by rw [hag _ (by norm_num)]; exact q24, by rw [hag _ (by norm_num)]; exact q25,
        by rw [hag _ (by norm_num)]; exact q128, by rw [hag _ (by norm_num)]; exact q1817,
        by rw [hag _ (by norm_num)]; exact q1852, by rw [hag _ (by norm_num)]; exact q1925,
        by rw [hag _ (by norm_num)]; exact q2029, by rw [hag _ (by norm_num)]; exact z36,
        by rw [hag _ (by norm_num)]; exact z39, by rw [hag _ (by norm_num)]; exact z55,
        by rw [hag _ (by norm_num)]; exact z54, by rw [hag _ (by norm_num)]; exact z51,
        by rw [hag _ (by norm_num)]; exact z52, by rw [hag _ (by norm_num)]; exact b0,
        by rw [hag _ (by norm_num)]; exact q37, by rw [hag _ (by norm_num)]; exact q55,
        by rw [hag _ (by norm_num)]; exact q73, fun k hk => by rw [hag _ (by omega)]; exact zxi k hk,
        fun j hj => by rw [hag _ (evVal_lt j hj)]; exact dev j hj,
        by rw [hag _ (by norm_num), hag _ (by norm_num)]; exact dst⟩)
    fun σ5 e5 r5 hh5 => ?_).mono le_rfl le_rfl ?_
  · obtain ⟨hsel, q24, q25, q128, q1817, q1852, q1925, q2029, z36, z39, z55, z54, z51, z52, b0, q37,
      q55, q73, zxi, dev, dst⟩ := r5
    have hvh : VtHoldsAt 7854 rd σ5 := ⟨_, hh5 True (fun _ => True) trivial⟩
    have f3 : σ5 (.n 3) = (digestScalars pi).1 := by rw [Ext.app' e5 3 (by norm_num), h3]
    have f4 : σ5 (.n 4) = (digestScalars pi).2 := by rw [Ext.app' e5 4 (by norm_num), h4]
    have f7 : σ5 (.n 7) = dims := by rw [Ext.app' e5 7 (by norm_num), h7]
    have f11 : σ5 (.n 11) = fpw := by rw [Ext.app' e5 11 (by norm_num), h11]
    have f12 : σ5 (.n 12) = beta := by rw [Ext.app' e5 12 (by norm_num), h12]
    have f13 : σ5 (.n 13) = pool := by rw [Ext.app' e5 13 (by norm_num), h13]
    have a3 := hvh.atom 1658 (.load (.n 1931) (.n 1852) 1) (by decide +kernel)
    have b3 := hvh.atom 1766 (.load (.n 2035) (.n 1852) 2) (by decide +kernel)
    simp only [Atom.Holds] at a3 b3
    have htau : ∀ t < 6, σ5 (.n (airTau.getD t 0)) = gen ^ log2Ceil (rowsN.getD t 0) := fun t ht => by
      have := hvh.atom _ _ (by rw [take_drop_take _ (airStart_lt t ht)]; exact (air_blocks t ht).2.2)
      simp only [Atom.Holds] at this
      rw [f7] at this
      exact loadHolds_unique this (hdimsT t ht)
    have hev_eq : vtEvalVars.map (·.map fun k => σ5 (.n k)) = evss := by
      refine flatten_shape_eq _ _ (by rw [hshape]; simp [List.map_map]) ?_
      rw [vt_evss_flatten]
      apply List.ext_getElem (by simp [evWords, hflat])
      intro j h1 h2
      simp only [evWords, List.getElem_map, List.getElem_range]
      rw [dev j (by simpa [evWords] using h1), List.getD_eq_getElem _ _ h2]
    have fin := vt_final_c hP2 hb hrl hal hvh (by rw [f11]; exact hfpwR) a3 b3
      (by rw [f13, q37, q55, q73]; exact hpool3)
      (fun i hi => by rw [vt_sel_push hb logMem hrl hi]; exact (hsel i (by omega)).1)
      (fun j hj => by rw [vt_sel_count hb logMem hrl hj]; exact (hsel (37 + j) (by omega)).1)
      (rs := (List.range n).map ch) (by rw [List.length_map, List.length_range]) hnp z54 htau
      (fun j hj => by
        rw [z39, prodE_take_map ch hj]
        have := hpC j (by simp only [zcCprodW, List.length_map, List.length_range]; omega)
        simpa [zcCprodW] using this)
      (fun k hk => by
        rw [z55, eqEval_take (by omega) (by simp; omega)]
        have := hpP k (by simp only [zcPeqW, List.length_map, List.length_range]; omega)
        simpa [zcPeqW] using this)
      zxi [v0, v1, v2] [m0, m1, m2] mF bF bv
    rw [f12, hev_eq, hfin] at fin
    have heq : σ5 (.n 8139) = σ5 (.n 4652) := by rw [fin, z52]
    refine (vt_c_tail (cvR := obsAll (cvr n) evss.flatten) dst heq
      (by rw [f3]; exact (isCanonical128_digestScalars pi).1)
      (by rw [f4]; exact (isCanonical128_digestScalars pi).2)
      (by rw [f13, f3, f4]; exact h109) (by rw [f13, f3, f4]; exact h110) (by rw [f13]; exact h111)).mono
      le_rfl le_rfl fun σ'' ⟨t1, t2, t3, t4, t5, t6⟩ => ⟨t1, t2, by rw [t3, z51], by rw [t4, z54],
        by rw [t5, b0], t6⟩
  · rintro σ' ⟨⟨hsel, q24, q25, q128, q1817, q1852, q1925, q2029, z36, z39, z55, z54, -⟩, t1, t2, t3, t4, t5, t6⟩
    exact ⟨hsel, q24, q25, q128, q1817, q1852, q1925, q2029, z36, z39, z55, z54, t1, t2, t3, t4, t5, t6⟩

end


end
end LeanVM.Guest.B1.VerifySub
