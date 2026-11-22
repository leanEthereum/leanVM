/-
  LeanVM.Guest.CoreMode.Fn.gkr_layers.Sound

  `gkr_layers`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its exponent facts.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.CoreMode.Fn.verify_bus_gkr.ResGkrQ
public import LeanVM.Guest.CoreMode.Fn.gkr_layers.Data
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layers__L»

namespace LeanVM.Guest.CoreMode.Own.gkr_layers

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its `n_four` and `rem_g`, below `4`** (`GlsQ`). -/
theorem expFacts_ok : ∀ c ∈ expFacts, ExpOk c := by
  intro c hc r hr J hJ σ bufs kids hJt fn hf v hv
  obtain ⟨o, ho, i, hi, rfl⟩ : ∃ o < 2, ∃ i, (i = 3 ∨ i = 4) ∧ c = (B1.Tables.glcLsN o, i, none, 4) := by
    simp only [expFacts, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    exacts [⟨0, by omega, 3, Or.inl rfl, rfl⟩, ⟨0, by omega, 4, Or.inr rfl, rfl⟩,
      ⟨1, by omega, 3, Or.inl rfl, rfl⟩, ⟨1, by omega, 4, Or.inr rfl, rfl⟩]
  dsimp only at hJt hf hv ⊢
  obtain ⟨fn', hf', hp', -⟩ := B1.Tables.glcFnCheck_sound (B1.Tables.glc_layers_check o ho).1
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  rw [hp', glcPar9_eq] at hv
  obtain ⟨n, rr, q, h3, hn4, h4, hrr, -⟩ := glsQ_all hr J hJ o ho σ bufs kids hJt
  rcases hi with rfl | rfl
  · obtain rfl : V.n (valf% «gkr_layers» "n_four") = v := Option.some.inj hv
    exact ⟨n, hn4, h3⟩
  · obtain rfl : V.n (valf% «gkr_layers» "rem_g") = v := Option.some.inj hv
    exact ⟨rr, hrr, h4⟩

end

end LeanVM.Guest.CoreMode.Own.gkr_layers
