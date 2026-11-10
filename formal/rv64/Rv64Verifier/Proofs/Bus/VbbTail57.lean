import Rv64Verifier.Proofs.Bus.VbbTail56

/-!
# `verify_bus_balance`'s side loop: the block loop, all blocks

One block from its head (`blkIter`: `blkHead`, `coStage`, `cellStage`, `cdChecks`, `padStage`,
`accA`, `accB`), and the loop from block `k` past the last (`blkLoop`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Contracts

/-- The callees of the block loop. -/
structure BlkCallees : Prop where
  term : Layout.TermSpec
  addScaled : Layout.AddScaledSpec
  mul : MulSpec
  evaluate : TableSumcheck.FormEvaluateSpecE

theorem blkIter (hC : BlkCallees) {s z h e t₀ : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (hPb : n = 0 ∨ heapNext z ≤ P.toNat)
    (Ih : Inv s h) (hzh : heapNext z ≤ heapNext h) (En : Entry s z h e i sd point P n)
    (B : Blk s z h e t₀ i sd point P n forms tot k)
    (hk : k < min sd.2.1.tables.length sd.1.length) (hpc : t₀.pc = 0x800078f0) :
    ∃ t, Reaches Image.code t₀ t ∧ (Dead Image.code t ∨
      (Blk s z h e t i sd point P n forms tot (k + 1) ∧
        ((k + 1 < min sd.2.1.tables.length sd.1.length ∧ t.pc = 0x800078f0) ∨
          (k + 1 = min sd.2.1.tables.length sd.1.length ∧ t.pc = 0x80007b24)))) := by
  obtain ⟨t₄, r₄, hd | ⟨p₄, H⟩⟩ := blkHead hC.term hpre hsz Ih En B hk hpc
  · exact ⟨t₄, r₄, Or.inl hd⟩
  obtain ⟨t₅, r₅, hd | ⟨p₅, F⟩⟩ := coStage hC.addScaled hpre hsz Ih hzh En B hk H p₄
  · exact ⟨t₅, r₄.trans r₅, Or.inl hd⟩
  obtain ⟨t₆, r₆, hd | ⟨p₆, D⟩⟩ := cellStage hC.addScaled hpre hsz hPb En B hk H F p₅
  · exact ⟨t₆, r₄.trans (r₅.trans r₆), Or.inl hd⟩
  obtain ⟨t₇, r₇, hd | ⟨Q₇, hc⟩⟩ := cdChecks hpre hsz En B hk D p₆
  · exact ⟨t₇, r₄.trans (r₅.trans (r₆.trans r₇)), Or.inl hd⟩
  obtain ⟨t₈, r₈, hd | ⟨Q₈, p₈, hpad⟩⟩ := padStage hC.mul hpre hsz Ih hzh En Q₇ hc
  · exact ⟨t₈, r₄.trans (r₅.trans (r₆.trans (r₇.trans r₈))), Or.inl hd⟩
  obtain ⟨t₉, r₉, hd | ⟨p₉, V⟩⟩ := accA hC.mul hC.evaluate hpre hsz En Q₈ p₈ hpad
  · exact ⟨t₉, r₄.trans (r₅.trans (r₆.trans (r₇.trans (r₈.trans r₉)))), Or.inl hd⟩
  obtain ⟨t, r, hd | hB⟩ := accB hC.mul hpre hsz hPb En B hk V p₉
  · exact ⟨t, r₄.trans (r₅.trans (r₆.trans (r₇.trans (r₈.trans (r₉.trans r))))), Or.inl hd⟩
  · exact ⟨t, r₄.trans (r₅.trans (r₆.trans (r₇.trans (r₈.trans (r₉.trans r))))), Or.inr hB⟩

/-- From block `k` past the last. -/
theorem blkLoop (hC : BlkCallees) {s z h e : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (hPb : n = 0 ∨ heapNext z ≤ P.toNat)
    (Ih : Inv s h) (hzh : heapNext z ≤ heapNext h) (En : Entry s z h e i sd point P n) :
    ∀ d k t, k + d + 1 = min sd.2.1.tables.length sd.1.length →
      Blk s z h e t i sd point P n forms tot k → t.pc = 0x800078f0 →
      ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨
        (Blk s z h e t' i sd point P n forms tot (min sd.2.1.tables.length sd.1.length) ∧
          t'.pc = 0x80007b24)) := by
  intro d
  induction d with
  | zero =>
    intro k t hd B hpc
    obtain ⟨t', hr, hd' | ⟨B', ⟨hlt, -⟩ | ⟨he, hpc'⟩⟩⟩ :=
      blkIter hC hpre hsz hPb Ih hzh En B (by omega) hpc
    · exact ⟨t', hr, Or.inl hd'⟩
    · omega
    · rw [he] at B'; exact ⟨t', hr, Or.inr ⟨B', hpc'⟩⟩
  | succ d ih =>
    intro k t hd B hpc
    obtain ⟨t', hr, hd' | ⟨B', ⟨-, hpc'⟩ | ⟨he, -⟩⟩⟩ :=
      blkIter hC hpre hsz hPb Ih hzh En B (by omega) hpc
    · exact ⟨t', hr, Or.inl hd'⟩
    · obtain ⟨t'', hr', ht''⟩ := ih (k + 1) t' (by omega) B' hpc'
      exact ⟨t'', hr.trans hr', ht''⟩
    · omega

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
