/-
  LeanVM.Guest.B1.VerifySub.Stack

  `verify_sub`'s stack: the committed columns' placement, the stack's log and the size selector it
  dispatches on.
-/

module

public import LeanVM.Guest.B1.VerifySub.LanesK
public import LeanVM.Guest.B1.Placement.Kappas

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem word_pow_eq {a : ℕ} (h : a < 64) : word (2 ^ a) 0 0 = ofK (Parameters.addressOfIndex
    a) := by
  rw [word_two_pow h, gen_pow_eq_ofK]

/-- A range check against `g^(K-1)` (`K ≤ 64`) on a memory of at least `64` words. -/
theorem rc_lt {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ) {x y t1 t2 : E} {a : ℕ}
    (ha : a < 64) (h1 : LoadHolds L.read x 0 t1) (hk : word (2 ^ a) 0 0 = x * y)
    (h2 : LoadHolds L.read y 0 t2) : ∃ e < a + 1, x = gen ^ e := by
  have h64 : a + 1 ≤ 2 ^ κ := le_trans (show a + 1 ≤ 2 ^ 6 by omega)
    (Nat.pow_le_pow_right (by decide) hκ6)
  obtain ⟨e, he, hx⟩ := (rangeCheck_iff hκ L x (K := a + 1) (by omega) h64).mp
    ⟨y, t1, t2, h1, by rw [Nat.add_sub_cancel, ← word_pow_eq (by omega)]; exact hk, h2⟩
  exact ⟨e, he, by rw [hx, gen_pow_eq_ofK]⟩

/-- **The stack** (G:3534-3539): the placement certified, the stack's log `μ ∈ [20, 32]`, the size
selector `g^(μ - 20)` dispatched on, and the committed columns' logs below `33`. -/
theorem vs_stack {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ) {C : CallRel}
    (hLe : CallRel.Le C (coreProgram.Rel L.read)) (hcpS : Tables.certify_placement_Spec L.read)
    {bytecode : List K}
    (hbl : bytecode.length = 2 ^ 23) {σ : Val} (F : VsFront bytecode C L.read σ)
    (hexp : ExpTables L.read (σ (.n 4)))
    (hcp : C "certify_placement" [σ (.n 139), σ (.n 4)] [σ (.n 1682), σ (.n 1683)])
    (hl2 : C "log2_ceil_in_the_exponent__L16_L34" [σ (.n 1682), σ (.n 4)] [σ (.n 1684)])
    (e1686 : σ (.n 1686) = σ (.n 1684) * word 14347465658197868555 0 0)
    (r1 : LoadHolds L.read (σ (.n 1686)) 0 (σ (.n 1689)) ∧ word 4096 0 0 = σ (.n 1686) * σ (.n 1688) ∧
      LoadHolds L.read (σ (.n 1688)) 0 (σ (.n 1690))) :
    B1.Whir.minOpenLog ≤ (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog ∧
      (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog ≤ 32 ∧
      σ (.n 1686) = gen ^ ((Tables.layoutOf bytecode F.logMem F.rowsN).stackLog - B1.Whir.minOpenLog) ∧
      Tables.PCtx L.read (columnKappas F.logMem 19 (Tables.tableHeightsOf F.rowsN)) (σ (.n 1683)) ∧
      Tables.KappasBelow (columnKappas F.logMem 19 (Tables.tableHeightsOf F.rowsN)) := by
  have hsL := tableHeights_length _ F.hrowsL
  -- the placement
  obtain ⟨hsq, hrk, -⟩ := expTablesAt_of hexp
  have e178 : Tables.rankKeysAt = 178 := rfl
  rw [e178] at hrk
  obtain ⟨off, hrets, hP⟩ := hcpS F.logMem (Tables.tableHeightsOf F.rowsN) _ _ _ F.hm32 hsL F.hh33
    F.hkb hsq hrk (hLe _ _ _ hcp)
  simp only [List.cons.injEq, and_true, Tables.guestLogBytecode] at hrets hP
  obtain ⟨e1682, rfl⟩ := hrets
  -- the stack's log
  have hT := sl_stackTotal_lt F.hm32 hsL F.hh33
  have hr2 := (log2_holds.2 hκ hκ6 L _ _ hexp _).1 (hLe _ _ _ hl2)
  rw [e1682, meaningLog2CeilExp_pow (by norm_num) (lt_trans hT (by norm_num))] at hr2
  simp only [List.cons.injEq, and_true] at hr2
  obtain ⟨hm34, hret⟩ := hr2
  rw [← stackLog_eq hbl] at hret hm34
  set μ := (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog with hμ
  -- the size selector
  obtain ⟨e, he, hx⟩ := rc_lt hκ hκ6 L (a := 12) (by omega) r1.1 (by simpa using r1.2.1) r1.2.2
  have hμe : μ = e + 20 := size_sel_eq hm34 he (by rw [← hret, ← e1686, hx])
  refine ⟨by unfold B1.Whir.minOpenLog; omega, by omega,
    by rw [hx]; congr 1; unfold B1.Whir.minOpenLog; omega, hP, Tables.hypKappa_holds _ hP.1 ?_⟩
  have : max 16 (log2Ceil (Tables.stackTotal (columnKappas F.logMem 19
    (Tables.tableHeightsOf F.rowsN)))) ≤ 32 := by rw [← stackLog_eq hbl]; omega
  omega

/-- The Keccak table's height is at most `26` once every committed column's log is below `33`:
its column `q_keccak` has the log `τ + 6`. -/
theorem tau_le_of_kappasBelow {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6)
    (hKB : Tables.KappasBelow (columnKappas logMem 19 hs)) : hs.getD 5 0 ≤ 26 := by
  have hck := Tables.committedKappas_columnKappas logMem hs hl
  have k5 := hKB 5 (by decide)
  simp only [Tables.guestLogBytecode] at hck
  rw [hck, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; decide),
    List.getElem_map, List.getElem_range,
    show Tables.colKappaSrc 5 = 7 from rfl, show Tables.colKappaAdj 5 = 6 from rfl] at k5
  clear * - k5 hl
  obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ : ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
    match hs, hl with
    | [h0, h1, h2, h3, h4, h5], _ => exact ⟨_, _, _, _, _, _, rfl⟩
  simp only [List.getD_cons_succ, List.getD_cons_zero] at k5 ⊢
  omega

end
end LeanVM.Guest.B1.VerifySub
