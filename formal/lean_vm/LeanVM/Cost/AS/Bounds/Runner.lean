module

public import LeanVM.Cost.AS.Bounds.Newton
import all LeanVM.Protocol.Extraction.Fast.RunVec

/-!
# Bounds: the candidate run of the agreement-set extractor

**`candidateRunner_cost`**: the runner's tables and one stack (`Fast.candidateRunner`, compiled on
demand by the finish), at the layout's sizes: at most
`(74κ + 121)·2^κ + (74ℓ + 121)·2^ℓ + 73ℓ + 357 + (runnerStepPrice κ ℓ + 41)·stepCapLite + 45·2^κ +
1800`.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

theorem candidateRunner_cost
    (hP : Includes P Auto.LeanVM.Extraction.Fast.candidateRunner.c505.costDeps)
    (prog : Semantics.LeanIsaProgram) (input : PublicInput) (layout : LayoutLite)
    (hm : layout.logMemory ≤ 30) (hb : layout.logBytecode ≤ 30)
    (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 30) (hl : layout.tableLogHeights.length ≤ 6)
    (hidx : ∀ c, (layout.placement c).index < 2 ^ 63) (q : Vector K (2 ^ layout.stackLog)) :
    machineCost P Auto.LeanVM.Extraction.Fast.candidateRunner.c505.costIdx
        [encodeValue prog, encodeValue input, encodeValue layout, encodeValue q] ≤
      (74 * layout.logMemory + 121) * 2 ^ layout.logMemory +
        (74 * prog.logSize + 121) * 2 ^ prog.logSize + 73 * prog.logSize + 357 +
        (runnerStepPrice layout.logMemory prog.logSize + 41) * stepCapLite layout +
        45 * 2 ^ layout.logMemory + 1800 := by
  have hls : prog.logSize ≤ 30 := prog.logSize_le
  have hcap := stepCapLite_le layout hm hb hh hl
  rw [Auto.LeanVM.Extraction.Fast.candidateRunner.c505.costEq P hP,
    limbs_of_lt (by omega : layout.logMemory < 2 ^ 64)]
  have h1 := powTable_cost P (by includes) layout.logMemory (by omega)
  have h2 := powTable_cost P (by includes) prog.logSize (by omega)
  have h3 := pcFinal_cost P (by includes) prog
  have h4 := stepCapLite_cost P (by includes) layout hm hb hh hl
  have h5 := candidateExecutionVec_cost P (by includes) (powTable layout.logMemory)
    (powTable prog.logSize) prog input layout (by omega) hidx (Registers.final prog)
    (stepCapLite layout) (lt_of_le_of_lt hcap (by norm_num)) q
    (runnerStepPrice layout.logMemory prog.logSize)
    (fun r ↦ by
      have := stepVec_cost P (by includes) (powTable layout.logMemory) (powTable prog.logSize)
        (wordTable_powTable (by omega)) (wordTable_powTable (by omega)) prog (by omega)
        (memoryVec layout q) r
      rw [powTable_size, powTable_size, Nat.log2_two_pow, Nat.log2_two_pow] at this
      unfold runnerStepPrice
      omega)
  split_ifs <;> omega

end

end LeanVM.Cost.Bounds.AS
