/-
  LeanVM.Guest.CoreMode.Fn.log2_ceil_in_the_exponent.Sound

  `log2_ceil_in_the_exponent`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its divisors,
  `g_N` nonzero from `g^(2^L) = g_N · g^e` on the carried tables (`log2_holds`).
-/

module

public import LeanVM.Guest.EndExecCoreFn
public import LeanVM.Guest.CoreMode.Fn.log2_ceil_in_the_exponent.Data
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«log2_ceil_in_the_exponent__L»

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Res (Kd carried cvars pinK kOf scanCall pin siteC witAtomC carryG carry_all)
open LeanVM.Protocol.Verifier (gen)

public section

/-! ## `log2_ceil_in_the_exponent`'s `g_N` -/

/-- `g_N ≠ 0` at an honest instance of a `log2_ceil_in_the_exponent` specialization. -/
theorem nzVal_lce {name : String} {fl : ℕ} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hps : f.params = [.n (valf% «log2_ceil_in_the_exponent» "g_N"), .n (valf% «log2_ceil_in_the_exponent» "g_squares")]) (hc : (name, 1, Kd.tab) ∈ carried)
    (hspec : B1.log2_ceil_in_the_exponent_SpecP coreProgram name fl) : NzVal name (.n (valf% «log2_ceil_in_the_exponent» "g_N")) := by
  intro r hr I hI σ bufs kids hIt
  have ht := (carryQ_all hr I hI name σ bufs kids hIt f hfind _ hc rfl (.n (valf% «log2_ceil_in_the_exponent» "g_squares")) (by rw [hps]; rfl)).1
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  have hrel := Tree.Valid.rel _ hv
  obtain ⟨fn', hf', hpar, -⟩ := hv
  obtain rfl : f = fn' := Option.some.inj (hfind.symm.trans hf')
  rw [hps] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have h23 : 23 ≤ r.κ := twentyThree_le_logMem _
  obtain ⟨L, -, -, ⟨e, -, he⟩, -⟩ := (hspec (by omega) (by omega) r.img _ _ ht rets).mp hrel
  intro h0
  rw [h0, zero_mul] at he
  exact Value.gen_pow_ne_zero _ he

theorem nzVal_lce0 : NzVal "log2_ceil_in_the_exponent__L0_L34" (.n (valf% «log2_ceil_in_the_exponent» "g_N")) :=
  nzVal_lce B1.find_lce_L0 rfl (by decide) B1.log2_holds.1

theorem nzVal_lce16 : NzVal "log2_ceil_in_the_exponent__L16_L34" (.n (valf% «log2_ceil_in_the_exponent» "g_N")) :=
  nzVal_lce B1.find_lce_L16 rfl (by decide) B1.log2_holds.2

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.log2_ceil_in_the_exponent

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its divisors, nonzero.** -/
theorem nzs_ok : ∀ c ∈ nzs, NzOk c := by
  simp only [nzs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨nzVal_lce0, nzVal_lce16⟩

end

end LeanVM.Guest.CoreMode.Own.log2_ceil_in_the_exponent
