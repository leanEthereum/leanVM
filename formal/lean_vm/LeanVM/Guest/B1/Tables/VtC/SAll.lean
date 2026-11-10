/-
  LeanVM.Guest.B1.Tables.VtC.SAll

  `verify_tables`' statements before the bus sides (`0 ..< 769`) hold on the honest valuation.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SP2

/-!
# Statements `0 ..< 769` (G:2109-2228)

`vtS_complete`: for the memory's log-size `lm ≤ 32`, the bus point (`|point| < 33`) and the
tables' heights `τ t = max (log2Ceil (n t)) floor < 33`, `τ t ≤ |point|`, on a memory defined
below `2^14` holding `dims_g` (`g^lm` and the heights), `table_rows`, the exponent tables, the
bus point, the group buffers, `idxc_tab`, `zeta1` and the shared tables, the oracle returning
`padding_weight`'s outcomes and `plus_one_run`'s `0`: every statement before the bus sides holds,
and the values later statements read are the honest ones.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

local notation "σv" => vtσ rd w args

theorem vtTauList_getD {τ : ℕ → ℕ} {t : ℕ} (ht : t < 6) : (vtTauList τ).getD t 0 = τ t := by
  rw [List.getD_eq_getElem _ _ (by simp [vtTauList]; exact ht)]
  simp [vtTauList]

/-- **`verify_tables`' statements `0 ..< 769` complete.** -/
theorem vtS_complete (hl : args.length = 20) (hlow : LowDefB 14 rd) {lm : ℕ} (hlm : lm ≤ 32)
    (point : List E) (hμ33 : point.length < 33) (τ n : ℕ → ℕ)
    (hτ : ∀ t < 6, τ t = max (log2Ceil (n t)) (tableLogFloors.getD t 0))
    (hτ33 : ∀ t < 6, τ t < 33) (hτμ : ∀ t < 6, τ t ≤ point.length)
    -- the arguments' buffers
    (hz : TbReadsAt rd (σv (.n 8)) point) (h9 : σv (.n 9) = gen ^ point.length)
    (hdims : TbReadsAt rd (σv (.n 10)) (gen ^ lm :: (vtTauList τ).map (gen ^ ·)))
    (hrows : ∀ t < 6, LoadHolds rd (σv (.n 11)) t (eOfNat (n t)))
    (hE : ExpTablesAt rd (σv (.n 12)))
    -- the own buffers
    (hkeyW : TbReadsAt rd (w 36) (vtGKeyW lm τ)) (hszW : TbReadsAt rd (w 37) (vtGSizeW lm τ))
    (hbaseW : TbReadsAt rd (w 38) (vtGBaseW lm τ)) (hordW : TbReadsAt rd (w 39) (vtGOrdW lm τ))
    (hidxc : TbReadsAt rd (w 668) vtIdxcW) (hz1 : TbReadsAt rd (w 703) (point.map (1 + ·)))
    (hrun : ∀ t < 6, RunTables rd (w 705 * gen ^ (288 * t)) (w 706 * gen ^ (144 * t))
      (point.length - τ t) (point.drop (τ t)) ((point.map (1 + ·)).drop (τ t))
      ((gSquaresList.drop (τ t)).take (point.length - τ t)))
    -- the callees' returns
    (hwp : ∀ t < 6, w (vtPadV t) = paddingWeight (point.take (τ t)) (n t) ∧
      w (vtPadV t + 1) = PadLead (τ t) (n t) ∧ w (vtPadV t + 2) = PadRest (τ t) (n t))
    (hw704 : w 704 = 0) :
    (∀ s ∈ (vtPre.drop 0).take 769, VSH (coreProgram.Rel rd) rd σv s) ∧
      (∀ i < 5, σv (.n (20 + i)) = σv (.n i)) ∧ (∀ i < 3, σv (.n (25 + i)) = σv (.n (17 + i))) ∧
      (∀ i < 8, σv (.n (28 + i)) = gen ^ ([0, lm] ++ vtTauList τ).getD i 0) ∧
      (∀ i < 4, σv (.n (36 + i)) = w (36 + i)) ∧
      (∀ x < 54, σv (.n (vtBoffV x)) =
        gen ^ (stackOffsets ((List.range 54).map (vtKap lm τ))).1.getD x 0) ∧
      (∀ x < 45, σv (.n (vtBoffV (108 + x))) =
        gen ^ (stackOffsets ((List.range 45).map fun c ↦ vtKap lm τ (108 + c))).1.getD x 0) ∧
      (∀ t < 6, σv (.n (vtPadV t)) = paddingWeight (point.take (τ t)) (n t)) ∧
      (∀ t < 6, σv (.n (vtShLen t)) = gen ^ (point.length - τ t)) ∧
      σv (.n 581) = w 581 ∧ σv (.n 668) = w 668 ∧ σv (.n 703) = w 703 ∧
      σv (.n 705) = w 705 ∧ σv (.n 706) = w 706 := by
  have hτ' : ∀ t < 6, τ t < 33 := hτ33
  obtain ⟨h1, hcp, hcc, hkb, hal, hP, hC⟩ :=
    vtS_sort hl hlow hlm hτ' hdims hE hkeyW hszW hbaseW hordW
  have hkbt : ∀ t < 6, σv (.n (30 + t)) = gen ^ τ t := by
    intro t ht
    have := hkb (2 + t) (by omega)
    rw [show 28 + (2 + t) = 30 + t by omega] at this
    rw [this]
    rw [show 2 + t = t + 1 + 1 by omega]
    simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
    rw [vtTauList_getD ht]
  obtain ⟨h2, hpw, hsl, e581, e668, e703, e705, e706⟩ := vtS_p2 hl hlow point hμ33 τ n hτ hτ33
    hτμ hkbt hz h9 hrows hE.1 hwp hidxc hz1 hw704 hrun
  exact ⟨forall_slice_join (a := 0) (l1 := 566) (l2 := 203) h1 h2, hcp, hcc, hkb, hal, hP, hC,
    hpw, hsl, e581, e668, e703, e705, e706⟩

end

end
end LeanVM.Guest.B1.Tables
