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
open LeanVM.Protocol LeanVM.Protocol.Verifier
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

end
end LeanVM.Guest.B1.VerifySub
