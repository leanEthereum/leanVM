/-
  Rv64mc.Proof.Field.ClmulLowT

  `clmul_low` is total: it returns `ClmulLow.Post`'s value (`Spec.Field.ClmulLow`), over any program holding its
  template, given its constant table in the static data (`DataRef.InData`, which the image's `env.data` gives). The
  partial proof (`ClmulLow.lean`) ported by `rv_autoT`; the table's load is a static data word, in a window and
  aligned by `Windows.data_ok`.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Field.ClmulLow
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Field.ClmulLowT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field Rv64mc.Proof.Field.ClmulLow
open Rv64mc.Gen.Verifier.Field.ClmulLow (Link tmpl d_c8_d07a1b83_words)

/-- **The total contract of `clmul_low`**: `ClmulLow.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) ClmulLow.Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hdata : DataRef.InData env [(L.d_c8_d07a1b83, d_c8_d07a1b83_words)]) {need : Nat} (hn : 48 ≤ need) :
    specT env p i need := by
  have hd := hdata.words (List.mem_singleton_self _)
  have hmem : (L.d_c8_d07a1b83.hi + L.d_c8_d07a1b83.lo, 0x8888888888888888#64) ∈ env.data := by
    simpa [d_c8_d07a1b83_words] using hdata _ (List.mem_singleton_self _) 0 (by simp [d_c8_d07a1b83_words])
  rv_autoT hp
  all_goals try first | exact (hpre_7.data_ok _ hmem).1 | exact (hpre_7.data_ok _ hmem).2
  simp only [Model.clmulLow, classMask_0, classMask_1, classMask_2, classMask_3]
  ac_rfl

end Rv64mc.Proof.Field.ClmulLowT

/-- info: 'Rv64mc.Proof.Field.ClmulLowT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ClmulLowT.total
