/-
  LeanVM.Guest.B1.Ring.Interface

  B1 of the ring switch: the meanings of `ring_switch_target` and `ring_switch_weight`, and the
  statements that their core IR computes them.
-/

module

public import LeanVM.Guest.B1.Eq.Meaning

/-!
# The ring switch (TRIAGE G #64-66): the interface

The ring switch (`ringSwitch`, `ring_switch.rs`) turns the 64 claims on `q_keccak`'s bit
slices into one claim on the committed column: the target `ringTarget s f g` and the weight
`W(r') = ringWeight point r' (ringCoefficients f g)`, over the sixteen challenges, `f` then `g`.

| function | meaning |
| --- | --- |
| `ring_psi` (inline) | `ringPsi v g`: the inner stage `Σ_b g_b v^(2^b)` |
| `ring_switch_target` | `ringTarget s f g`, eight rows a loop iteration, Horner in `w_p = 1/z_p` |
| `ring_switch_weight` | `ringWeight point (1 + point1) c_table`, the products by `rs_eq_run` |

`verify_sub` builds `c_table`: `ringCoefficients f g`.

Both functions write scratch buffers (`HeapBuf`) whose words their relations read back, so
their converse holds only over a memory holding the honest scratch; it is stated with
`verify_sub`'s completeness.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `ring_switch_target` -/

/-- **`ring_switch_target(slices, map_challenges)`** (TRIAGE #64, #65): the 64 slices `s` at
`slices` and the sixteen map challenges `f ++ g` at `map_challenges`; it returns
`ringTarget s f g`. -/
def MeaningRingTarget (rd : Reader) : List E → List E → Prop
  | [sl, mc], rets =>
      ∃ s ch : List E, s.length = kBits ∧ ch.length = 2 * ringMapWidth ∧ ReadsAt rd sl s ∧
        ReadsAt rd mc ch ∧ rets = [ringTarget s (ch.take ringMapWidth) (ch.drop ringMapWidth)]
  | _, _ => False

/-- `ring_switch_target`'s core IR computes its meaning. -/
def ring_switch_target_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "ring_switch_target" args rets → MeaningRingTarget rd args rets

/-! ## `ring_switch_weight` -/

/-- **`ring_switch_weight(z_vals, point1, c_table, qkeccakv_g)`** (TRIAGE #66):
`qkeccakv_g = g^n`, `n < 64`; the `n` words `r` at `z_vals`, the `n` words `p₁` at `point1` (the
opening point's `1 + r'`), the 64 coefficients `c` at `c_table`; it returns
`ringWeight r (p₁.map (1 + ·)) c`. -/
def MeaningRingWeight (rd : Reader) : List E → List E → Prop
  | [zv, p1, ct, ng], rets =>
      ∃ n < 64, ng = gen ^ n ∧ ∃ rs ps cs : List E, rs.length = n ∧ ps.length = n ∧
        cs.length = kBits ∧ ReadsAt rd zv rs ∧ ReadsAt rd p1 ps ∧ ReadsAt rd ct cs ∧
        rets = [ringWeight rs (ps.map (1 + ·)) cs]
  | _, _ => False

/-- `ring_switch_weight`'s core IR computes its meaning. -/
def ring_switch_weight_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "ring_switch_weight" args rets → MeaningRingWeight rd args rets

end
end LeanVM.Guest.B1.VerifySub
