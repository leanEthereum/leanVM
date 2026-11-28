/-
  LeanVM.Guest.B1.VsC.VsHonRet

  The honest return rule's values, index by index.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonBw

/-!
# The honest return rule, index by index

At `y := x.honCtx N ec bp bp1`: the rule is causal (constant), agrees with `honRet` where it is `some`, and gives
`FrontRet`, `Ret1`'s constants, `RetFs`, `Ret3`, `D3.Ok`'s `rvk`, `r3810`'s native value and `ro`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link LeanVM.Guest.B1.Stack
open LeanVM.Guest.B1.Link (pkSqueeze)
open LeanVM.Prover.Exec (allocBase)
open LeanVM.Guest.B1.VerifySub (qkeccakVarsCap keccakTauMin keccakTauMax)

@[expose] public section

attribute [local semireducible] VsCtx.lay

namespace VsCtx

section
variable {x : VsCtx} {N : NatOpen} {ec : ℕ → ℕ} {bp bp1 : ℕ}

theorem honCtx_hret : CausalRule (x.honCtx N ec bp bp1).ret := fun _ _ _ _ => rfl

/-- `honRet` off its indices. -/
theorem honRet_none {y : VsCtx} {L : LinkNat} {i : ℕ} (h1 : i < 752 ∨ 1298 < i ∨ (799 < i ∧ i < 1071) ∨
    (773 < i ∧ i < 797) ∨ (753 < i ∧ i < 767) ∨ (1077 < i ∧ i < 1286) ∨ (1292 < i ∧ i < 1296)) :
    honRet y L i = none := by
  unfold honRet
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem honCtx_ret_O {i : ℕ} (h1 : i < 752 ∨ 1298 < i ∨ (799 < i ∧ i < 1071) ∨
    (773 < i ∧ i < 797) ∨ (753 < i ∧ i < 767) ∨ (1077 < i ∧ i < 1286) ∨ (1292 < i ∧ i < 1296)) (σ : ℕ → E) :
    (x.honCtx N ec bp bp1).ret i σ = x.honRetO N bp bp1 i := by
  show honRetR x N bp bp1 i σ = _
  unfold honRetR
  rw [honRet_none h1]

/-- **The rule agrees with `honRet`** at the honest context. -/
theorem honCtx_honRet : ∀ i v, honRet (x.honCtx N ec bp bp1) N.L i = some v →
    ∀ σ, (x.honCtx N ec bp bp1).ret i σ = v := by
  intro i v h σ
  have e : honRet (x.honCtx N ec bp bp1) N.L i = honRet (x.withBw N) N.L i := by with_unfolding_all rfl
  show honRetR x N bp bp1 i σ = v
  unfold honRetR
  rw [← e, h]

/-- Evaluate `honRetO` at a numeral: its conditions by `simp`'s arithmetic, then the value up to the context. -/
macro "hon_eval" : tactic => `(tactic| (simp only [honRetO] <;> with_unfolding_all rfl))

theorem honCtx_retFs : (x.honCtx N ec bp bp1).RetFs := by
  refine ⟨fun j hj σ => ?_, fun j hj σ => ?_⟩
  · rw [honCtx_ret_O (by omega)]
    interval_cases j <;> hon_eval
  · rw [honCtx_ret_O (by omega)]
    interval_cases j <;> hon_eval

theorem honCtx_ret1F : (x.honCtx N ec bp bp1).Ret1F := by
  show FrontRet _ _ _ _ _
  refine ⟨fun σ => ?_, fun σ => ?_, fun t ht σ => ?_⟩
  · rw [honCtx_ret_O (by omega)]; hon_eval
  · rw [honCtx_ret_O (by omega)]; hon_eval
  · interval_cases t <;>
      exact ⟨by rw [honCtx_ret_O (by decide)]; hon_eval, by rw [honCtx_ret_O (by decide)]; hon_eval,
        by rw [honCtx_ret_O (by decide)]; hon_eval⟩

theorem honCtx_r484 : ∀ σ, (x.honCtx N ec bp bp1).ret 484 σ = gen ^ chunkCount (widthOf (x.honCtx N ec bp bp1).lay) :=
  fun σ => by rw [honCtx_ret_O (by omega)]; hon_eval

theorem honCtx_r485 : ∀ σ, (x.honCtx N ec bp bp1).ret 485 σ = gen ^ (x.honCtx N ec bp bp1).lay.stackLog :=
  fun σ => by rw [honCtx_ret_O (by omega)]; hon_eval

theorem honCtx_r486 : ∀ σ, (x.honCtx N ec bp bp1).ret 486 σ =
    ptrAt (csOffsAt ((x.honCtx N ec bp bp1).fpc + B2C.fs "certify_stack")) :=
  fun σ => by rw [honCtx_ret_O (by omega)]; hon_eval

theorem honCtx_r487 : ∀ σ, (x.honCtx N ec bp bp1).ret 487 σ =
    ptrAt (csOffsAt ((x.honCtx N ec bp bp1).fpc + B2C.fs "certify_stack") + 52) :=
  fun σ => by rw [honCtx_ret_O (by omega)]; hon_eval

theorem honCtx_r680 : ∀ j < 5, ∀ σ, (x.honCtx N ec bp bp1).ret (680 + j) σ =
    (pkSqueeze x.pk [x.omN.getD 2 0, x.omN.getD 3 0, x.omN.getD 4 0, x.omN.getD 5 0, x.omN.getD 6 0]).2.getD j 0 := by
  intro j hj σ
  rw [honCtx_ret_O (by omega)]
  interval_cases j <;> hon_eval

theorem honCtx_ret3 : (x.honCtx N ec bp bp1).Ret3 := by
  refine ⟨fun t h1 h5 σ => ?_, fun σ => by rw [honCtx_ret_O (by omega)]; hon_eval⟩
  interval_cases t <;>
    exact ⟨by rw [honCtx_ret_O (by decide)]; hon_eval, by rw [honCtx_ret_O (by decide)]; hon_eval,
      by rw [honCtx_ret_O (by decide)]; hon_eval⟩

theorem honCtx_rvk : ∀ j < 7, ∀ σ, (x.honCtx N ec bp bp1).ret (2915 + j) σ =
    (vkRets N.s' (ptrAt (x.natBm N.L + 144)) N.xs.length N.kw).getD j 0 := by
  intro j hj σ
  rw [honCtx_ret_O (by omega)]
  interval_cases j <;> hon_eval

theorem honCtx_r3810 : ∀ σ, (x.honCtx N ec bp bp1).ret 3810 σ =
    ringTarget (rsW N.ks N.L.msg (ringRho N.S)) (ringF N.S) (ringG N.S) :=
  fun σ => by rw [honCtx_ret_O (by omega)]; hon_eval

theorem honCtx_ro : ∀ j < 6, ∀ σ, (x.honCtx N ec bp bp1).ret (3991 + j) σ =
    (osRets N.wE bp bp1 (x.honIe N)).getD j 0 := by
  intro j hj σ
  rw [honCtx_ret_O (by omega)]
  interval_cases j <;> hon_eval

end

end VsCtx

end
end LeanVM.Guest.B1.VsC
