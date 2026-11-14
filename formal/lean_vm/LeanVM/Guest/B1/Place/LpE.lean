/-
  LeanVM.Guest.B1.Place.LpE

  `level_positions` complete placed at every specialization by a tree popping nothing whose every node is exact on
  the memory, at an optional words bound.
-/

module

public import LeanVM.Guest.B1.Place.LpBound

/-!
# `level_positions`, placed and exact

`CompleteAtPOE`: `CompleteAtPO` by a tree popping nothing whose every node is exact on the memory; `LpAtOE`: `LpAtO`
so. `level_positions_completeAtE` (no bound) and `level_positions_completeAtBE` (every words bound of its trees,
frames below `2^32`): every entry of `lpTable` is `LpAtOE`, by `lp_placedE`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- **`CompleteAtPO` by a tree popping nothing whose every node is exact on the memory.** -/
def CompleteAtPOE (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Lin : ℕ → Layout) (args rets : List E) (Lout : ℕ → Layout) (Bd : Option ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout), Within (Lout fp ++ Lown) fp n ∧ DisjL (Lout fp ++ Lown) ∧
    (∀ B ∈ Bd, n ≤ B) ∧ ∀ rd, LowDef k rd → MemL rd (Lout fp ++ Lown ++ Lin fp) →
      RelAtInPE coreProgram fs cert rd (ExactAt coreProgram rd) (RegionL (Lin fp)) (RegionL (Lout fp)) fp n f args
        rets []

theorem CompleteAtPOE.toPO {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String} {Lin : ℕ → Layout}
    {args rets : List E} {Lout : ℕ → Layout} {Bd : Option ℕ} (h : CompleteAtPOE fs cert k f Lin args rets Lout Bd) :
    CompleteAtPO fs cert k f Lin args rets Lout Bd := fun fp =>
  let ⟨n, Lown, hW, hD, hB, hr⟩ := h fp
  ⟨n, Lown, hW, hD, hB, fun rd hl hm => RelAtInT.relAtIn (hr rd hl hm)⟩

/-- **`LpAtO` by a tree popping nothing whose every node is exact on the memory.** -/
def LpAtOE (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name loop : String) (S d cd : ℕ)
    (Bd : Option ℕ) : Prop :=
  ∀ (w0 : E) (cap : List E) (ep ew : ℕ) (tabs : E) (Lin : ℕ → Layout), cap.length = 5 →
    (∀ fp, ∀ k < S * (128 / d), RegionL (Lin fp) (ep + k) ∧ RegionL (Lin fp) (ew + k)) →
    (∀ fp, ∀ t < 128, ∃ i, tabs.limb 0 * addressOfIndex t = addressOfIndex i ∧
      RegionL (Lin fp) i) →
    (∀ fp rd, LowDef κ rd → MemL rd (Lin fp) →
      LpMem cert S d cd (lpDecPos fs name loop S d cd fp) w0 cap (ofK (addressOfIndex ep))
        (ofK (addressOfIndex ew)) tabs rd) →
    CompleteAtPOE fs cert κ name Lin
      (w0 :: cap ++ [ofK (addressOfIndex ep), ofK (addressOfIndex ew), tabs])
      ((⟨cap, []⟩ : Fs).squeezeN (S - 1)).2.cap (lpRuns fs cert name loop S d cd w0 cap) Bd

theorem LpAtOE.toO {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {name loop : String} {S d cd : ℕ}
    {Bd : Option ℕ} (h : LpAtOE fs cert κ name loop S d cd Bd) : Arm.LpAtO fs cert κ name loop S d cd Bd :=
  fun w0 cap ep ew tabs Lin hcl hreg hregt hmem => (h w0 cap ep ew tabs Lin hcl hreg hregt hmem).toPO

/-- **`level_positions` is complete placed and exact at every specialization.** -/
theorem level_positions_completeAtE (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    (hfit : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 7 ≤ κ) :
    ∀ e ∈ lpTable, LpAtOE fs cert κ e.1 e.2.2.1 e.2.1 e.2.2.2.1 e.2.2.2.2 none := by
  intro e he
  obtain ⟨hlp, hl⟩ := lpTable_ok e he
  obtain ⟨hS, hSo, hSB, hpw, hmem⟩ := lpTable_facts e he
  have hdec := qwDecodeAtDE_holds hfit hcons hκ _ hmem
  intro w0 cap ep ew tabs Lin hcl hreg hregt hmemL fp
  obtain ⟨Lown, hW, hD, hR⟩ := lp_placedE fs cert κ hlp hl hS hSo hSB hpw hdec hcl fp
    (fun k hk ↦ hreg fp k hk) (hregt fp) (fun rd hlow hm ↦ hmemL fp rd hlow hm)
  exact ⟨lpN fs e.1 e.2.2.1 e.2.1 e.2.2.2.1 e.2.2.2.2, Lown, hW, hD, fun B hB ↦ absurd hB (by simp), hR⟩

/-- **`level_positions` placed and exact within every words bound of its trees**, frames below `2^32`. -/
theorem level_positions_completeAtBE (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    (hfit : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 7 ≤ κ)
    (hfs : ∀ f, fs f < 2 ^ 32) :
    ∀ e ∈ lpTable, ∀ B, TotalLe coreProgram fs e.1 (fun _ ↦ B) →
      LpAtOE fs cert κ e.1 e.2.2.1 e.2.1 e.2.2.2.1 e.2.2.2.2 (some B) := by
  intro e he B hT
  obtain ⟨hlp, hl⟩ := lpTable_ok e he
  obtain ⟨hS, hSo, hSB, hpw, hmem⟩ := lpTable_facts e he
  have hdec := qwDecodeAtDE_holds hfit hcons hκ _ hmem
  have hb := lp_bound κ hlp hl hS hSo hSB hpw hdec hfs hT
  intro w0 cap ep ew tabs Lin hcl hreg hregt hmemL fp
  obtain ⟨Lown, hW, hD, hR⟩ := lp_placedE fs cert κ hlp hl hS hSo hSB hpw hdec hcl fp
    (fun k hk ↦ hreg fp k hk) (hregt fp) (fun rd hlow hm ↦ hmemL fp rd hlow hm)
  exact ⟨lpN fs e.1 e.2.2.1 e.2.1 e.2.2.2.1 e.2.2.2.2, Lown, hW, hD,
    fun B' hB' ↦ by cases hB'; exact hb, hR⟩

end
end LeanVM.Guest.B1
