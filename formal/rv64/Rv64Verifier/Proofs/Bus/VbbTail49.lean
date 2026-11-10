import Rv64Verifier.Proofs.Bus.VbbTail48

/-!
# `verify_bus_balance`'s side loop: the block's form

From `0x80007984` (`Hd`) through the coordinates' loop (`coLoop`) to `0x80007a08`, the block's form
at `S - 296` is `blockFormRust` of block `k` (`Bf`, `coStage`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The loop, from `j` coordinates to the last, or out. -/
theorem coLoop (hAS : Layout.AddScaledSpec) {s z h e t₀ v₀ : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n k : Nat} (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z)
    (hzt : heapNext z ≤ heapNext t₀) (htv : heapNext t₀ ≤ heapNext v₀) (Ih : Inv s h)
    (hzh : heapNext z ≤ heapNext h) (En : Entry s z h e i sd point P n)
    (hro : FormRowsRO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (blkAddr s i k) 1)
    (hv10 : v₀.getReg .x10 = vecPtr s (blkAddr s i k) + 16)
    (hv13 : v₀.getReg .x13 = e.getMem (s.getReg .x2 - 1264))
    (hv18 : v₀.getReg .x18 = e.getMem (s.getReg .x2 - 1248) + 1)
    (hv9 : v₀.getReg .x9 = coBound (e.getMem (s.getReg .x2 - 1248)) (vecLen s (blkAddr s i k)).toNat)
    (hc : (vecLen s (blkAddr s i k)).toNat < 2 ^ 60) :
    ∀ d j t, j + d + 1 = (vecLen s (blkAddr s i k)).toNat → CoI s z h t₀ v₀ t i sd k j →
      j ≤ (e.getMem (s.getReg .x2 - 1248)).toNat → t.pc = 0x800079bc →
      ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨
        (CoI s z h t₀ v₀ t' i sd k (vecLen s (blkAddr s i k)).toNat ∧ t'.pc = 0x80007a08)) := by
  intro d
  induction d with
  | zero =>
    intro j t hd S hjw hpc
    obtain ⟨t', hr, hd' | ⟨S', -, ⟨hlt, -⟩ | ⟨he, hpc'⟩⟩⟩ := coIter hAS hpre hsz hzt htv Ih hzh En hro
      hv10 hv13 hv18 hv9 hc S (by omega) hjw hpc
    · exact ⟨t', hr, Or.inl hd'⟩
    · omega
    · rw [he] at S'; exact ⟨t', hr, Or.inr ⟨S', hpc'⟩⟩
  | succ d ih =>
    intro j t hd S hjw hpc
    obtain ⟨t', hr, hd' | ⟨S', hjw', ⟨-, hpc'⟩ | ⟨he, -⟩⟩⟩ := coIter hAS hpre hsz hzt htv Ih hzh En
      hro hv10 hv13 hv18 hv9 hc S (by omega) hjw hpc
    · exact ⟨t', hr, Or.inl hd'⟩
    · obtain ⟨t'', hr', ht''⟩ := ih (j + 1) t' (by omega) S' hjw' hpc'
      exact ⟨t'', hr.trans hr', ht''⟩
    · omega

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
