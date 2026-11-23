/-
  LeanVM.Guest.B1.Place.LpAtE

  `level_positions`' placed statement by a tree popping nothing whose every node is exact on the memory.
-/

module

public import LeanVM.Guest.B1.Place.Lp
public import LeanVM.Guest.B1.Main.RelAtInE

/-!
# `level_positions`' exact statement

`CompleteAtPOE`: `CompleteAtPO` by a tree popping nothing whose every node is exact on the memory; `LpAtOE`: the
helper's placed statement so.
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

end
end LeanVM.Guest.B1
