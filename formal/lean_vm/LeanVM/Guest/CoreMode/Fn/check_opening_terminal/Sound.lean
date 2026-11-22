/-
  LeanVM.Guest.CoreMode.Fn.check_opening_terminal.Sound

  `check_opening_terminal`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its exponent and dimension facts, from what `verify_sub` hands it (`TermQ`).
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.CoreMode.Fn.check_opening_terminal.TermQ
public import LeanVM.Guest.CoreMode.Fn.check_opening_terminal.Data

namespace LeanVM.Guest.CoreMode.Own.check_opening_terminal

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its exponent facts** (`termQ_all`, `expH_of_front`). -/
theorem expFacts_ok : ∀ c ∈ expFacts, ExpOk c := by
  intro c hc r hr J hJ σ bufs kids hJt fn hf v hv
  have hn := (expFacts_cot hc).1
  rw [hn] at hJt hf
  have hp := term_fn hf
  have hT := termQ_all hr J hJ _ σ bufs kids hJt rfl fn hf
  rw [hp] at hT hv
  exact expH_of_front hT hc hv

/-- **Its dimension facts** (`termQ_all`, `dimH_of_front`). -/
theorem dimFacts_ok : ∀ c ∈ dimFacts, DimOk c := by
  intro c hc r hr J hJ σ bufs kids hJt fn hf vk vb hvk hvb
  have hn := (dimFacts_cot hc).1
  rw [hn] at hJt hf
  have hp := term_fn hf
  have hT := termQ_all hr J hJ _ σ bufs kids hJt rfl fn hf
  rw [hp] at hT hvk hvb
  exact dimH_of_front hT hc hvk hvb

end

end LeanVM.Guest.CoreMode.Own.check_opening_terminal
