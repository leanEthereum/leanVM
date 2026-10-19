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

end
end LeanVM.Guest.B1.VerifySub
