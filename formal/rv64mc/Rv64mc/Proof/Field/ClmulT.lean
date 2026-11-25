/-
  Rv64mc.Proof.Field.ClmulT

  `clmul` is total: it returns `Clmul.Post`'s product (`Spec.Field.Clmul`), over any program holding its template,
  from `clmul_low`'s total contract (`ClmulLowT`). The partial proof (`Clmul.lean`) ported by `rv_autoT`.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Field.Clmul
import Rv64mc.Proof.Field.ClmulLowT

namespace Rv64mc.Proof.Field.ClmulT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.Clmul (Link tmpl)

/-- **The total contract of `clmul`**: `Clmul.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) Clmul.Post

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needL : Nat} (hn : 80 + needL ≤ need) (hlow : ClmulLowT.specT env p L.clmulLow.idx needL) :
    specT env p i need := by
  rv_autoT hp with [hL] using [hlow]
  · rw [Model.clmul, lo128_join]
  · generalize hc : Model.clmulLow _ _ = c
    have hc' : c = Model.clmulLow (regs .x10).reverse (regs .x11).reverse := by
      rw [← hc]
      congr 1 <;> rw [← reverse_net] <;> simp only [swapBits, bswap]
    rw [Model.clmul, hi128_join, ← hc', ← reverse_net]
    simp only [swapBits, bswap]

end Rv64mc.Proof.Field.ClmulT

/-- info: 'Rv64mc.Proof.Field.ClmulT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ClmulT.total
