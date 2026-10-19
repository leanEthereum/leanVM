/-
  LeanVM.Guest.B1.Tables.VerifyTablesCChain

  `verify_tables`' completeness: the windows chained, phase by phase.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesC1
public import LeanVM.Guest.B1.Tables.VerifyTablesCGlue
public import LeanVM.Guest.B1.Tables.VerifyTablesCKids

/-!
# The chain

`vt_cons`: a window completing on its values, then from any valuation it reaches (its facts
holding) the windows after it; the first window's facts, stable under the later windows (which
change only values above it), hold at the end. `vt_phaseA`: the prelude, the block order, the
padding weights and `idxc_tab`, statements `0 ..< 1574`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- **Two windows in sequence**, the first's facts kept. -/
theorem vt_cons {C : CallRel} {rd : Reader} {a l1 l2 lo mid hi : ℕ} {σ : Val} {P Q : Val → Prop}
    (hlo : lo ≤ mid) (hhi : mid ≤ hi) (hnb : NumBelow mid (Stmt.valsList ((vtPre.drop a).take l1)))
    (h1 : Completes C rd lo mid ((vtPre.drop a).take l1) σ P)
    (hP : ∀ σ1 σ2 : Val, (∀ k < mid, σ2 (.n k) = σ1 (.n k)) → P σ1 → P σ2)
    (h2 : ∀ σ', Ext lo mid σ σ' → P σ' → Completes C rd mid hi ((vtPre.drop (a + l1)).take l2) σ' Q) :
    Completes C rd lo hi ((vtPre.drop a).take (l1 + l2)) σ (fun σ'' => P σ'' ∧ Q σ'') := by
  rw [List.take_add, List.drop_drop]
  refine Completes.append hlo hhi hnb h1 fun σ' he hp => ?_
  obtain ⟨σ'', he', hq, hh⟩ := h2 σ' he hp
  exact ⟨σ'', he', ⟨hP σ' σ'' (fun k hk => he'.apply (Or.inl hk)) hp, hq⟩, hh⟩

/-- Facts on values below a bound are kept by valuations agreeing below it. -/
macro "vt_stable" : tactic =>
  `(tactic| (intro σ1 σ2 hag hp; simp +contextual (disch := omega) only [hag]; exact hp))

section
variable {rd : Reader}

set_option maxRecDepth 100000 in
/-- **Statements `0 ..< 1574`**: the arguments copied, the three pointers of the block order
hinted, the side table stored, the block order certified, the padding weights and `idxc_tab`. -/
theorem vt_phaseA (hS : VtSortComplete) {κ : ℕ} (hκ : 7 ≤ κ) (hlow : LowDef κ rd) {σ : Val}
    {p24 p25 p128 p1817 dims rowsP zeta bk sq bv : E} {ks : ℕ → ℕ} {logMem : ℕ} {rowsN : List ℕ}
    {point : List E} (hks : ∀ b < 102, ks b < 34)
    (h5 : σ (.n 5) = zeta) (h7 : σ (.n 7) = dims) (h8 : σ (.n 8) = rowsP) (h9 : σ (.n 9) = bk)
    (h10 : σ (.n 10) = sq)
    (hso1 : ∀ r < 37, LoadHolds rd p24 r (gen ^ (stackOrder ((List.range 37).map ks)).getD r 0))
    (hso2 : ∀ r < 28, LoadHolds rd p24 (74 + r)
      (gen ^ (74 + (stackOrder ((List.range 28).map fun i => ks (74 + i))).getD r 0)))
    (hside : ∀ b < 102, LoadHolds rd p25 b (word (vtBlockSide b) 0 0))
    (hbk : ∀ b < 102, LoadHolds rd bk b (gen ^ ks b))
    (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (hoff1 : ∀ i < 37, LoadHolds rd p128 i (gen ^ (stackOffsets ((List.range 37).map ks)).1.getD i 0))
    (hoff2 : ∀ i < 28, LoadHolds rd p128 (74 + i)
      (gen ^ (stackOffsets ((List.range 28).map fun i => ks (74 + i))).1.getD i 0))
    (hdims : ReadsAt rd dims (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n))
    (hrows : ReadsAt rd rowsP (rowsN.map eOfNat)) (hz : ReadsAt rd zeta point) (hrl : rowsN.length = 6)
    (hτ : ∀ t < 6, log2Ceil (rowsN.getD t 0) < 29)
    (hτp : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ point.length)
    (hidx : ∀ t < 34, LoadHolds rd p1817 t (1 + gen ^ 2 ^ t)) :
    Completes (coreProgram.Rel rd) rd 19 1852 ((vtPre.drop 0).take (213 + (1225 + (67 + 69)))) σ
      (fun σ' => σ' (.n 19) = σ (.n 0) ∧ σ' (.n 20) = σ (.n 1) ∧ σ' (.n 21) = σ (.n 16) ∧
        σ' (.n 22) = σ (.n 17) ∧ σ' (.n 23) = σ (.n 18) ∧ σ' (.n 24) = p24 ∧ σ' (.n 25) = p25 ∧
        σ' (.n 128) = p128 ∧ σ' (.n 1732) = bv ∧
        (∀ t < 6, σ' (.n (1733 + 14 * t)) = gen ^ log2Ceil (rowsN.getD t 0) ∧
          σ' (.n (1739 + 14 * t)) =
            paddingWeight (point.take (log2Ceil (rowsN.getD t 0))) (rowsN.getD t 0)) ∧
        σ' (.n 1817) = p1817) := by
  refine (vt_cons (Q := fun σ'' => True ∧ ((σ'' (.n 1732) = bv ∧
        ∀ t < 6, σ'' (.n (1733 + 14 * t)) = gen ^ log2Ceil (rowsN.getD t 0) ∧
          σ'' (.n (1739 + 14 * t)) =
            paddingWeight (point.take (log2Ceil (rowsN.getD t 0))) (rowsN.getD t 0)) ∧
        σ'' (.n 1817) = p1817))
    (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
    (vt_c_pre (p24 := p24) (p128 := p128) hside) (by vt_stable) fun σ1 e1 p1 => ?_).mono le_rfl le_rfl ?_
  · obtain ⟨-, -, -, -, -, q24, q25, q128⟩ := p1
    refine vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (hS κ hκ rd hlow ks hks σ1 p24 p25 bk sq p128 q24 q25 (by rw [e1.apply (by omega), h9])
        (by rw [e1.apply (by omega), h10]) q128 hso1 hso2 hside hbk hsq hoff1 hoff2)
      (fun _ _ _ _ => trivial) fun σ2 e2 _ => ?_
    refine vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_c0 (bv := bv) (by omega) hlow (by rw [e2.apply (by omega), e1.apply (by omega), h7])
        (by rw [e2.apply (by omega), e1.apply (by omega), h8])
        (by rw [e2.apply (by omega), e1.apply (by omega), h5]) hdims hrows hz hrl hτ hτp)
      (by vt_stable) fun σ3 _ _ => vt_c_idxc hidx
  · rintro σ' ⟨⟨c19, c20, c21, c22, c23, q24, q25, q128⟩, -, ⟨b0, hpw⟩, hi⟩
    exact ⟨c19, c20, c21, c22, c23, q24, q25, q128, b0, hpw, hi⟩

end

/-! ## The selectors -/

/-- What selector `i` reads: its block's log-height `k` and offset `off i` fitting the point, the
two in `block_kappa` and `block_off_g`, and its three buffers at `ptr (selBuf i + ·)`. -/
def SelMem (rd : Reader) (bk offP : E) (point : List E) (ks off : ℕ → ℕ) (ptr : ℕ → E) (i : ℕ) : Prop :=
  ks (selBlk.getD i 0) ≤ point.length ∧ off i < 2 ^ point.length ∧ 2 ^ ks (selBlk.getD i 0) ∣ off i ∧
    LoadHolds rd bk (selBlk.getD i 0) (gen ^ ks (selBlk.getD i 0)) ∧
    LoadHolds rd offP (selBlk.getD i 0) (gen ^ off i) ∧
    ReadsAt rd (ptr (selBuf i)) ((List.range 34).map fun j => bitE ((off i).testBit j)) ∧
    ReadsAt rd (ptr (selBuf i + 1)) ((List.range (point.length - ks (selBlk.getD i 0) + 1)).map fun t =>
      ∏ j ∈ Finset.range t, (1 + bitE ((off i).testBit (ks (selBlk.getD i 0) + j)) +
        point.getD (ks (selBlk.getD i 0) + j) 0)) ∧
    ReadsAt rd (ptr (selBuf i + 2)) ((List.range (point.length - ks (selBlk.getD i 0) + 1)).map fun t =>
      ∏ j ∈ Finset.range t, (1 + bitE ((off i).testBit (ks (selBlk.getD i 0) + j)) *
        (gen ^ 2 ^ (ks (selBlk.getD i 0) + j) + 1)))

/-- What selector `i` leaves: its `eqAbove`, `g^k` and the three pointers. -/
def SelPost (point : List E) (ks off : ℕ → ℕ) (ptr : ℕ → E) (i : ℕ) (σ : Val) : Prop :=
  σ (.n (selVal.getD i 0 + 23)) = ({ vars := ks (selBlk.getD i 0), index := off i } : Placement).eqAbove point ∧
    σ (.n (selVal.getD i 0)) = gen ^ ks (selBlk.getD i 0) ∧ σ (.n (selVal.getD i 0 + 12)) = ptr (selBuf i) ∧
    σ (.n (selVal.getD i 0 + 15)) = ptr (selBuf i + 1) ∧ σ (.n (selVal.getD i 0 + 16)) = ptr (selBuf i + 2)

set_option maxRecDepth 100000 in
theorem sel_nb : ∀ i < 65, numBelowB (selVal.getD i 0 + 27)
    (Stmt.valsList ((vtPre.drop (selStmt.getD i 0)).take 28)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtGaps_nb : vtGaps.all (fun g => numBelowB g.2.2.2
    (Stmt.valsList ((vtPre.drop g.1).take (g.2.1 - g.1)))) = true := by decide +kernel

theorem sel_mono : ∀ i < 65, ∀ j < 65, i ≤ j →
    selStmt.getD i 0 ≤ selStmt.getD j 0 ∧ selVal.getD i 0 ≤ selVal.getD j 0 := by decide +kernel

theorem sel_adj : ∀ i < 64, selStmt.getD i 0 + 28 ≤ selStmt.getD (i + 1) 0 ∧
    selVal.getD i 0 + 27 ≤ selVal.getD (i + 1) 0 := by decide +kernel

theorem sel_lo : ∀ i < 65, 129 ≤ selVal.getD i 0 := by decide +kernel

section
variable {rd : Reader}

/-- **Selector `i` completes.** -/
theorem vt_c_sel (hSel : VtSelComplete) {κ : ℕ} (hκ : 6 ≤ κ) (hlow : LowDef κ rd) {σ : Val}
    {zeta bk sq offP : E} {point : List E} {ks off : ℕ → ℕ} {ptr : ℕ → E} (hpl : point.length < 33)
    (hz : ReadsAt rd zeta point) (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j)) {i : ℕ} (hi : i < 65)
    (hm : SelMem rd bk offP point ks off ptr i) (h5 : σ (.n 5) = zeta) (h6 : σ (.n 6) = gen ^ point.length)
    (h9 : σ (.n 9) = bk) (h10 : σ (.n 10) = sq) (h128 : σ (.n 128) = offP) :
    Completes (coreProgram.Rel rd) rd (selVal.getD i 0) (selVal.getD i 0 + 27)
      ((vtPre.drop (selStmt.getD i 0)).take 28) σ (SelPost point ks off ptr i) := by
  obtain ⟨hk, hoff, hdvd, hbk, hoffP, h12, h15, h16⟩ := hm
  exact hSel i hi κ hκ rd hlow σ zeta bk sq offP _ _ _ point _ _ h5 h6 h9 h10 h128 hk hpl hoff hdvd hbk
    hoffP hz hsq h12 h15 h16

/-- `vt_c_sel` at literal positions. -/
theorem vt_c_sel' (hSel : VtSelComplete) {κ : ℕ} (hκ : 6 ≤ κ) (hlow : LowDef κ rd) {σ : Val}
    {zeta bk sq offP : E} {point : List E} {ks off : ℕ → ℕ} {ptr : ℕ → E} (hpl : point.length < 33)
    (hz : ReadsAt rd zeta point) (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j)) {i : ℕ} (hi : i < 65)
    (hm : SelMem rd bk offP point ks off ptr i) {lo st : ℕ} (hlo : selVal.getD i 0 = lo)
    (hst : selStmt.getD i 0 = st) (h5 : σ (.n 5) = zeta) (h6 : σ (.n 6) = gen ^ point.length)
    (h9 : σ (.n 9) = bk) (h10 : σ (.n 10) = sq) (h128 : σ (.n 128) = offP) :
    Completes (coreProgram.Rel rd) rd lo (lo + 27) ((vtPre.drop st).take 28) σ (SelPost point ks off ptr i) := by
  rw [← hlo, ← hst]; exact vt_c_sel hSel hκ hlow hpl hz hsq hi hm h5 h6 h9 h10 h128

/-- **A run of selectors, each followed by a pure window**, from selector `i0`. -/
theorem vt_sel_run (hSel : VtSelComplete) {κ : ℕ} (hκ : 6 ≤ κ) (hlow : LowDef κ rd)
    {zeta bk sq offP : E} {point : List E} {ks off : ℕ → ℕ} {ptr : ℕ → E} (hpl : point.length < 33)
    (hz : ReadsAt rd zeta point) (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (hm : ∀ i < 65, SelMem rd bk offP point ks off ptr i) :
    ∀ (d i0 : ℕ), (∀ j < d, i0 + j < 64 ∧ (selStmt.getD (i0 + j) 0 + 28, selStmt.getD (i0 + j + 1) 0,
      selVal.getD (i0 + j) 0 + 27, selVal.getD (i0 + j + 1) 0) ∈ vtGaps) → i0 < 65 →
    ∀ σ : Val, σ (.n 5) = zeta → σ (.n 6) = gen ^ point.length → σ (.n 9) = bk → σ (.n 10) = sq →
      σ (.n 128) = offP →
      Completes (coreProgram.Rel rd) rd (selVal.getD i0 0) (selVal.getD (i0 + d) 0)
        ((vtPre.drop (selStmt.getD i0 0)).take (selStmt.getD (i0 + d) 0 - selStmt.getD i0 0)) σ
        (fun σ' => ∀ j < d, SelPost point ks off ptr (i0 + j) σ')
  | 0, i0, _, _, σ, _, _, _, _, _ => by
    simp only [Nat.add_zero, Nat.sub_self, List.take_zero]
    exact completes_nil _ _ σ fun j hj => absurd hj (Nat.not_lt_zero j)
  | d + 1, i0, hrun, hi0, σ, h5, h6, h9, h10, h128 => by
    obtain ⟨h0, hg⟩ := hrun 0 (by omega)
    simp only [Nat.add_zero] at h0 hg
    have hadj := sel_adj i0 h0
    have hmo := sel_mono (i0 + 1) (by omega) (i0 + 1 + d) (by have := (hrun d (by omega)).1; omega) (by omega)
    have hlo := sel_lo i0 hi0
    rw [show i0 + (d + 1) = i0 + 1 + d by omega,
      show selStmt.getD (i0 + 1 + d) 0 - selStmt.getD i0 0 =
        (28 + (selStmt.getD (i0 + 1) 0 - (selStmt.getD i0 0 + 28))) +
          (selStmt.getD (i0 + 1 + d) 0 - selStmt.getD (i0 + 1) 0) by omega]
    refine (vt_cons (P := fun σ'' => SelPost point ks off ptr i0 σ'' ∧ True)
      (Q := fun σ'' => ∀ j < d, SelPost point ks off ptr (i0 + 1 + j) σ'')
      (mid := selVal.getD (i0 + 1) 0) (by omega) hmo.2 ?_ ?_ ?_ fun σ' e _ => ?_).mono le_rfl le_rfl ?_
    · rw [List.take_add, valsList_append]
      exact NumBelow.append ((numBelow_of_B (sel_nb i0 hi0)).mono hadj.2)
        (by rw [List.drop_drop]; exact numBelow_of_B (List.all_eq_true.mp vtGaps_nb _ hg))
    · exact vt_cons (by omega) hadj.2 (numBelow_of_B (sel_nb i0 hi0))
        (vt_c_sel hSel hκ hlow hpl hz hsq hi0 (hm i0 hi0) h5 h6 h9 h10 h128)
        (fun σ1 σ2 hag hp => by
          unfold SelPost at hp ⊢; simp +contextual (disch := omega) only [hag]; exact hp)
        fun σ' _ _ => vt_c_gap hg σ'
    · intro σ1 σ2 hag hp
      exact ⟨by unfold SelPost at hp ⊢; simp +contextual (disch := omega) only [hag]; exact hp.1, trivial⟩
    · rw [show selStmt.getD i0 0 + (28 + (selStmt.getD (i0 + 1) 0 - (selStmt.getD i0 0 + 28))) =
        selStmt.getD (i0 + 1) 0 by omega]
      exact vt_sel_run hSel hκ hlow hpl hz hsq hm d (i0 + 1)
        (fun j hj => by
          have := hrun (j + 1) (by omega)
          rw [show i0 + (j + 1) = i0 + 1 + j by omega] at this; exact this) (by omega) σ'
        (by rw [e.apply (by omega), h5]) (by rw [e.apply (by omega), h6]) (by rw [e.apply (by omega), h9])
        (by rw [e.apply (by omega), h10]) (by rw [e.apply (by omega), h128])
    · rintro σ'' ⟨⟨hp0, -⟩, hr⟩ j hj
      rcases j with _ | j
      · simpa using hp0
      · have := hr j (by omega)
        rw [show i0 + 1 + j = i0 + (j + 1) by omega] at this; exact this

end

theorem Ext.app' {lo hi : ℕ} {σ σ' : Val} (h : Ext lo hi σ σ') (k : ℕ) (hk : k < lo) : σ' (.n k) = σ (.n k) :=
  h.apply (Or.inl hk)

section
variable {rd : Reader}

set_option maxRecDepth 100000 in
/-- **Statements `1574 ..< 1808`**: `block_index_mle` hinted, the selectors `0`, `1`, `2` with the
boundary block, the memory block and the bytecode block between them. -/
theorem vt_phaseB1 (hSel : VtSelComplete) (hG1 : VtGlue1) (hG2 : VtGlue2) (hG3 : VtGlue3) {κ : ℕ}
    (hκ : 6 ≤ κ) (hlow : LowDef κ rd) {σ : Val}
    {cur zeta bk sq fpw pool cplen idxc offP pbim pI2 pI3 m0 m1 m2 : E} {point : List E} {logMem : ℕ}
    {cv : Digest} {ks off : ℕ → ℕ} {ptr : ℕ → E}
    (h2 : σ (.n 2) = cur) (h5 : σ (.n 5) = zeta) (h6 : σ (.n 6) = gen ^ point.length) (h9 : σ (.n 9) = bk)
    (h10 : σ (.n 10) = sq) (h11 : σ (.n 11) = fpw) (h13 : σ (.n 13) = pool) (h14 : σ (.n 14) = cplen)
    (hcv : (σ (.n 19), σ (.n 20)) = digestScalars cv) (h128 : σ (.n 128) = offP) (h1817 : σ (.n 1817) = idxc)
    (hpl : point.length < 33) (hz : ReadsAt rd zeta point) (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (hm : ∀ i < 65, SelMem rd bk offP point ks off ptr i) (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v)
    (hidxc : ∀ t < 34, LoadHolds rd idxc t (1 + gen ^ 2 ^ t))
    (hk1 : ks (selBlk.getD 1 0) = logMem) (hk2 : ks (selBlk.getD 2 0) = 18) (h0lm : 0 < logMem)
    (hlmp : logMem ≤ point.length) (hlm32 : logMem ≤ 32) (h18p : 18 ≤ point.length)
    (hpI2 : ReadsAt rd pI2 (idxChainW point logMem))
    (hb1 : LoadHolds rd pbim 1 ((idxChainW point logMem).getD logMem 0))
    (hpI3 : ReadsAt rd pI3 (idxChainW point 18)) (hb2 : LoadHolds rd pbim 2 ((idxChainW point 18).getD 18 0))
    (hcur : ReadsAt rd cur [m0, m1, m2]) (hpool : ReadsAt rd pool [m0, m1, m2])
    (hcpl : ∀ j < 3, LoadHolds rd cplen j (gen ^ logMem)) :
    Completes (coreProgram.Rel rd) rd 1852 2077
      ((vtPre.drop 1574).take (3 + (28 + (11 + (28 + (80 + (28 + 56))))))) σ (fun σ' =>
        σ' (.n 1852) = pbim ∧ (∀ i < 3, SelPost point ks off ptr i σ') ∧ σ' (.n 1925) = pI2 ∧
          σ' (.n 1937) = m0 ∧ σ' (.n 1955) = m1 ∧ σ' (.n 1973) = m2 ∧
          (σ' (.n 1986), σ' (.n 1987)) = digestScalars (obsAll cv [m0, m1, m2]) ∧ σ' (.n 2029) = pI3) := by
  have stS : ∀ i lo, selVal.getD i 0 = lo → ∀ σ1 σ2 : Val, (∀ k < lo + 27, σ2 (.n k) = σ1 (.n k)) →
      SelPost point ks off ptr i σ1 → SelPost point ks off ptr i σ2 := fun i lo hlo σ1 σ2 hag hp => by
    subst hlo; unfold SelPost at hp ⊢; simp +contextual (disch := omega) only [hag]; exact hp
  refine (vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel)) (vt_c_bim pbim)
    (by vt_stable) fun σ1 e1 p1 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_c_sel' hSel hκ hlow hpl hz hsq (by norm_num : 0 < 65) (hm 0 (by norm_num)) (by decide) (by decide)
        (by rw [Ext.app' e1 5 (by norm_num), h5]) (by rw [Ext.app' e1 6 (by norm_num), h6])
        (by rw [Ext.app' e1 9 (by norm_num), h9]) (by rw [Ext.app' e1 10 (by norm_num), h10])
        (by rw [Ext.app' e1 128 (by norm_num), h128])) (stS 0 1855 (by decide)) fun σ2 e2 p2 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (hG1 rd σ2 fpw (by rw [Ext.app' e2 11 (by norm_num), Ext.app' e1 11 (by norm_num), h11]) hfpw)
      (fun _ _ _ _ => trivial) fun σ3 e3 _ =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_c_sel' hSel hκ hlow hpl hz hsq (by norm_num : 1 < 65) (hm 1 (by norm_num)) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h6)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h9)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h10)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h128)) (stS 1 1893 (by decide)) fun σ4 e4 p4 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (hG2 rd σ4 cur fpw pool cplen zeta idxc pbim pI2 m0 m1 m2 point logMem cv
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h2)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h1817)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2]; exact p1)
        (by rw [← hk1]; exact (show selVal.getD 1 0 = 1893 by decide) ▸ p4.2.1)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact hcv)
        h0lm hlmp hz hidxc hpI2 hb1 hfpw hcur hpool hcpl hlm32) (by vt_stable) fun σ5 e5 _ =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_c_sel' hSel hκ hlow hpl hz hsq (by norm_num : 2 < 65) (hm 2 (by norm_num)) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h6)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h9)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h10)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h128))
      (stS 2 1997 (by decide)) fun σ6 e6 p6 =>
    hG3 rd σ6 fpw zeta idxc pbim pI3 point
      (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
      (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11)
      (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h1817)
      (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2]; exact p1)
      (by rw [← hk2]; exact (show selVal.getD 2 0 = 1997 by decide) ▸ p6.2.1) h18p hz hidxc hpI3 hb2 hfpw).mono le_rfl le_rfl ?_
  rintro σ' ⟨q1, q2, -, q4, ⟨q25, q37, q55, q73, q86⟩, q6, q29⟩
  refine ⟨q1, fun i hi => ?_, q25, q37, q55, q73, q86, q29⟩
  interval_cases i
  · exact q2
  · exact q4
  · exact q6

end

section
variable {rd : Reader}

/-- `vt_sel_run` at literal positions. -/
theorem vt_sel_run' (hSel : VtSelComplete) {κ : ℕ} (hκ : 6 ≤ κ) (hlow : LowDef κ rd)
    {zeta bk sq offP : E} {point : List E} {ks off : ℕ → ℕ} {ptr : ℕ → E} (hpl : point.length < 33)
    (hz : ReadsAt rd zeta point) (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (hm : ∀ i < 65, SelMem rd bk offP point ks off ptr i) (d i0 : ℕ)
    (hrun : ∀ j < d, i0 + j < 64 ∧ (selStmt.getD (i0 + j) 0 + 28, selStmt.getD (i0 + j + 1) 0,
      selVal.getD (i0 + j) 0 + 27, selVal.getD (i0 + j + 1) 0) ∈ vtGaps) (hi0 : i0 < 65)
    {lo hi st en : ℕ} (hlo : selVal.getD i0 0 = lo) (hhi : selVal.getD (i0 + d) 0 = hi)
    (hst : selStmt.getD i0 0 = st) (hen : selStmt.getD (i0 + d) 0 = en)
    {σ : Val} (h5 : σ (.n 5) = zeta) (h6 : σ (.n 6) = gen ^ point.length) (h9 : σ (.n 9) = bk)
    (h10 : σ (.n 10) = sq) (h128 : σ (.n 128) = offP) :
    Completes (coreProgram.Rel rd) rd lo hi ((vtPre.drop st).take (en - st)) σ
      (fun σ' => ∀ j < d, SelPost point ks off ptr (i0 + j) σ') := by
  rw [← hlo, ← hhi, ← hst, ← hen]
  exact vt_sel_run hSel hκ hlow hpl hz hsq hm d i0 hrun hi0 σ h5 h6 h9 h10 h128

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **Statements `1808 ..< 4273`**: the selectors `3 ..< 37` with the pure windows after them,
the push side's padding and the pull side, the selectors `37 ..< 65` with theirs. -/
theorem vt_phaseB2 (hSel : VtSelComplete) (hG4 : VtGlue4) {κ : ℕ} (hκ : 6 ≤ κ) (hlow : LowDef κ rd)
    {σ : Val} {cur zeta bk sq fpw pool cplen offP pbim mF bF : E} {point : List E} {cv : Digest}
    {ks off : ℕ → ℕ} {ptr : ℕ → E}
    (h2 : σ (.n 2) = cur) (h5 : σ (.n 5) = zeta) (h6 : σ (.n 6) = gen ^ point.length) (h9 : σ (.n 9) = bk)
    (h10 : σ (.n 10) = sq) (h11 : σ (.n 11) = fpw) (h13 : σ (.n 13) = pool) (h14 : σ (.n 14) = cplen)
    (h128 : σ (.n 128) = offP) (h1852 : σ (.n 1852) = pbim)
    (hcv : (σ (.n 1986), σ (.n 1987)) = digestScalars cv)
    (hpl : point.length < 33) (hz : ReadsAt rd zeta point) (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (hm : ∀ i < 65, SelMem rd bk offP point ks off ptr i)
    (hbk : ∀ b < 102, LoadHolds rd bk b (gen ^ ks b)) (hks : ∀ b < 102, ks b < 34)
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v) (hc3 : LoadHolds rd cur 3 mF) (hc4 : LoadHolds rd cur 4 bF)
    (hp3 : ∀ j < 3, ∃ v, LoadHolds rd pool j v) (hpm : LoadHolds rd pool 3 mF) (hpb : LoadHolds rd pool 4 bF)
    (hl3 : LoadHolds rd cplen 3 (gen ^ ks 38)) (hl4 : LoadHolds rd cplen 4 (gen ^ ks 39))
    (hb1 : ∃ v, LoadHolds rd pbim 1 v) (hb2 : ∃ v, LoadHolds rd pbim 2 v) :
    Completes (coreProgram.Rel rd) rd 2077 4554
      ((vtPre.drop 1808).take ((2798 - 1808) + (28 + (571 + ((4206 - 3397) + (28 + (4273 - 4234))))))) σ
      (fun σ' => (∀ j < 33, SelPost point ks off ptr (3 + j) σ') ∧ SelPost point ks off ptr 36 σ' ∧
        σ' (.n 3359) = mF ∧ σ' (.n 3409) = bF ∧
        (σ' (.n 3422), σ' (.n 3423)) = digestScalars (obsCv (obsCv cv mF) bF) ∧
        (∀ j < 27, SelPost point ks off ptr (37 + j) σ') ∧ SelPost point ks off ptr 64 σ') := by
  have stS : ∀ i lo, selVal.getD i 0 = lo → ∀ σ1 σ2 : Val, (∀ k < lo + 27, σ2 (.n k) = σ1 (.n k)) →
      SelPost point ks off ptr i σ1 → SelPost point ks off ptr i σ2 := fun i lo hlo σ1 σ2 hag hp => by
    subst hlo; unfold SelPost at hp ⊢; simp +contextual (disch := omega) only [hag]; exact hp
  have stR : ∀ i0 d lo, (∀ j < d, selVal.getD (i0 + j) 0 + 27 ≤ lo) → ∀ σ1 σ2 : Val,
      (∀ k < lo, σ2 (.n k) = σ1 (.n k)) → (∀ j < d, SelPost point ks off ptr (i0 + j) σ1) →
      ∀ j < d, SelPost point ks off ptr (i0 + j) σ2 := fun i0 d lo hb σ1 σ2 hag hp j hj => by
    have hb' := hb j hj
    have := hp j hj
    unfold SelPost at this ⊢; simp +contextual (disch := omega) only [hag]; exact this
  refine (vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
    (vt_sel_run' hSel hκ hlow hpl hz hsq hm 33 3 (by decide +kernel) (by norm_num) (by decide) (by decide)
      (by decide) (by decide) h5 h6 h9 h10 h128)
    (stR 3 33 3034 (by decide)) fun σ1 e1 _ =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_c_sel' hSel hκ hlow hpl hz hsq (by norm_num : 36 < 65) (hm 36 (by norm_num)) (by decide) (by decide)
        (by rw [Ext.app' e1 5 (by norm_num), h5]) (by rw [Ext.app' e1 6 (by norm_num), h6])
        (by rw [Ext.app' e1 9 (by norm_num), h9]) (by rw [Ext.app' e1 10 (by norm_num), h10])
        (by rw [Ext.app' e1 128 (by norm_num), h128])) (stS 36 3034 (by decide)) fun σ2 e2 _ =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (hG4 κ hκ rd hlow σ2 cur bk fpw pool cplen pbim mF bF ks cv
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h2)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h9)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h11)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h13)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h14)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h1852)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact hcv)
        hbk hks hfpw hc3 hc4 hp3 hpm hpb hl3 hl4 hb1 hb2) (by vt_stable) fun σ3 e3 _ =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_sel_run' hSel hκ hlow hpl hz hsq hm 27 37 (by decide +kernel) (by norm_num) (by decide) (by decide)
        (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h6)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h9)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h10)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h128))
      (stR 37 27 4488 (by decide)) fun σ4 e4 _ =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_c_sel' hSel hκ hlow hpl hz hsq (by norm_num : 64 < 65) (hm 64 (by norm_num)) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h6)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h9)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h10)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h128))
      (stS 64 4488 (by decide)) fun σ5 _ _ =>
    vt_c_gap (by decide +kernel) σ5).mono le_rfl le_rfl ?_
  rintro σ' ⟨q1, q2, ⟨q59, q09, q22⟩, q3, q4, -⟩
  exact ⟨q1, q2, q59, q09, q22, q3, q4⟩

end

end
end LeanVM.Guest.B1.VerifySub
