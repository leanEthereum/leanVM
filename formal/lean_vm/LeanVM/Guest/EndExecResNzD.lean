/-
  LeanVM.Guest.EndExecResNzD

  The listed nonzero values on the deployed guest, at the honest instances of b2c's aligned tree:
  `certify_stack`'s rank `1` key, `child_claim_list_mono_last__L0`'s region and
  `log2_ceil_in_the_exponent__L16_L34`'s `g_N`, `verify_sub`'s link cycle and vanishing counts.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.EndExecResNz
public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.CoreMode.Gen.MonoWalkOk
public import LeanVM.Guest.CoreMode.Gen.FnData
public import LeanVM.Guest.CoreMode.Fn.certify_stack.SoundA
public import LeanVM.Guest.CoreMode.Fn.verify_sub.Nz
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«log2_ceil_in_the_exponent__L»
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono_last__L»

/-!
# The listed nonzero values, deployed

The registry's nonzero values (`CoreMode.FnReg.nzs`) at every honest instance (`NzValA`), the bus
era's `nzVal_ml0` and `nzVal_lce16` on b2c's aligned tree: the last claims' region by the gap walk
(`monoQ_allA`, `mono_ok`); `g_N` from `g^(2^L) = g_N · g^e` (`B1.log2_holds`) on the exponent
tables its caller carries (`carryQ_allA`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Res (Kd carried)

public section

variable {al : String → Bool} {D : Ref → RefD}

/-- **The last claims' region at every honest instance of the empty rest** is nonzero. -/
theorem nzValA_ml0 :
    NzValA al D name% «child_claim_list_mono_last__L0» (.n (valf% «child_claim_list_mono_last» "region")) := by
  intro r hR hr I hI σ bufs kids ht
  obtain ⟨-, -, -, -, -, h, -⟩ := (monoQ_allA mono_ok hR hr I hI _ σ bufs kids ht).2.1 (by decide)
  exact h

/-- **`g_N` at every honest instance of `log2_ceil_in_the_exponent__L16_L34`** is nonzero. -/
theorem nzValA_lce16 :
    NzValA al D name% «log2_ceil_in_the_exponent__L16_L34» (.n (valf% «log2_ceil_in_the_exponent» "g_N")) := by
  intro r hR hr I hI σ bufs kids hIt
  have hps : (fn% «log2_ceil_in_the_exponent__L16_L34»).params =
      [.n (valf% «log2_ceil_in_the_exponent» "g_N"), .n 1] := rfl
  have hc : (name% «log2_ceil_in_the_exponent__L16_L34», 1, Kd.tab) ∈ carried := by decide
  have ht := (carryQ_allA hR I hI _ σ bufs kids hIt _ B1.find_lce_L16 _ hc rfl
    (.n 1) (by rw [hps]; rfl)).1
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI hIt
  have hrel := Tree.Valid.rel _ hv
  obtain ⟨fn', hf', hpar, -⟩ := hv
  obtain rfl : fn% «log2_ceil_in_the_exponent__L16_L34» = fn' := Option.some.inj (B1.find_lce_L16.symm.trans hf')
  rw [hps] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  have hκ : r.κ ≤ 28 := hr.log
  have h23 : 23 ≤ r.κ := by rw [hR.κ]; exact twentyThree_le_logMem _
  obtain ⟨L, -, -, ⟨e, -, he⟩, -⟩ := (B1.log2_holds (by omega) (by omega) r.img _ _ ht rets).mp hrel
  intro h0
  rw [h0, zero_mul] at he
  exact Value.gen_pow_ne_zero _ he

/-- **Every listed nonzero value** is nonzero at every honest instance. -/
theorem nzs_okA : ∀ p ∈ CoreMode.FnReg.nzs, NzValA al D p.1 p.2 := by
  intro p hp
  simp only [CoreMode.FnReg.nzs, CoreMode.Own.certify_stack.nzs, CoreMode.Own.child_claim_list_mono_last.nzs,
    CoreMode.Own.log2_ceil_in_the_exponent.nzs, CoreMode.Own.verify_sub.nzs, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact nzValA_cs182
  · exact nzValA_ml0
  · exact nzValA_lce16
  · exact nzValA_vs240
  · exact nzValA_vs652

end

end LeanVM.Guest.EndExec
