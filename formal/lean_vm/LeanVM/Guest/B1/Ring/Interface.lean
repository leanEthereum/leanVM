/-
  LeanVM.Guest.B1.Ring.Interface

  B1 of the ring switch: the meanings of `ring_switch_target` and `ring_switch_weight`, and the
  statements that their core IR computes them.
-/

module

public import LeanVM.Guest.B1.Eq.Meaning

/-!
# The ring switch (TRIAGE G #64-66): the interface

The ring switch (`ringSwitch`, V:2124) turns the 64 claims on `q_keccak`'s bit slices into one
claim on the committed column: the target `Σ_i g^i Φ(s_i)` and the weight
`W(r') = ringWeight point r' (ringCoefficients challenges)` (V:2103-2128).

| function | G | meaning |
| --- | --- | --- |
| `ring_map` (inline) | 2948-2955 | `phiMap` (V:2103): six stages `a ↦ a + f_p·a^(2^shift)` |
| `ring_switch_target` | 2958-2974 | `polyEval (s.map (phiMap · challenges)) g` (V:2128), eight rows a loop iteration (`__loop13`) |
| `ring_switch_weight` | 2977-2986 | `ringWeight point (1 + point1) c_table` (V:2109), the products by `rs_eq_run` |

`verify_sub` builds `c_table` (G:3458-3465): `ringCoefficients challenges` (V:2117).

Both functions write scratch buffers (`HeapBuf`) whose words their relations read back, so
their converse holds only over a memory holding the honest scratch; it is stated with
`verify_sub`'s completeness.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `ring_switch_target` -/

/-- **`ring_switch_target(slices, map_challenges)`** (G:3097-3114; TRIAGE #64, #65): the 64
slices `s` at `slices` and the six map challenges at `map_challenges`; it returns
`Σ_i g^i Φ(s_i)` (`polyEval (s.map (phiMap · challenges)) gen`, V:2128). -/
def MeaningRingTarget (rd : Reader) : List E → List E → Prop
  | [sl, mc], rets =>
      ∃ s ch : List E, s.length = kBits ∧ ch.length = ringMapShifts.length ∧ ReadsAt rd sl s ∧
        ReadsAt rd mc ch ∧ rets = [polyEval (s.map (phiMap · ch)) gen]
  | _, _ => False

/-- `ring_switch_target`'s core IR computes its meaning. -/
def ring_switch_target_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "ring_switch_target" args rets → MeaningRingTarget rd args rets

/-! ## `ring_switch_weight` -/

/-- **`ring_switch_weight(z_vals, point1, c_table, qkeccakv_g)`** (G:3117-3126; TRIAGE #66):
`qkeccakv_g = g^n`, `n < 64`; the `n` words `r` at `z_vals`, the `n` words `p₁` at `point1` (the
opening point's `1 + r'`), the 64 coefficients `c` at `c_table`; it returns
`ringWeight r (p₁.map (1 + ·)) c` (V:2109). -/
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
