import Whir.CausalPrefix

/-! The cumulative RBR state uses the actual causal-prefix provider, including
the final tail scalar with no following prover reply. -/
namespace Whir.PCSRoundByRoundCausalEvents
open Concrete Protocol CausalGame CausalProbability

/-- Consolidated actual bad-event invariance, without acceptance, availability,
or a supplied cover. The existing provider derives every coordinate case. -/
theorem bad_set_future (input : Public) (strategy : Strategy)
    (valid : input.config.valid = true) (r q : Coordinate input.config)
    (t : Tape input.config) (x : Sample q) (later : position r < position q) :
    CausalBadEvents.Bad input strategy r (set q t x) ↔ CausalBadEvents.Bad input strategy r t :=
  CausalPrefix.event_set_future input strategy valid r q t x later

#print axioms bad_set_future
end Whir.PCSRoundByRoundCausalEvents
