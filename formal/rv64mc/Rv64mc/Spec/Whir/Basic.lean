/-
  Rv64mc.Spec.Whir.Basic

  What the WHIR family's contracts share: words of the image's constant tables (`DataWords`, read from
  `Env.data`, so in place wherever `env.Static` holds, at every call's entry and return).
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Spec.Whir

open RiscvZkvm.Rv64

/-- **The words `ws` from `a` are constants of the image**: word `k` at `a + 8k`, each in `env.data`. -/
def DataWords (env : Env) (a : Word) (ws : List Word) : Prop :=
  ∀ k (h : k < ws.length), (a + BitVec.ofNat 64 (8 * k), ws[k]) ∈ env.data

/-- A constant word is in place in every state where `env.Static` holds. -/
theorem DataWords.getMem {env : Env} {a : Word} {ws : List Word} (h : DataWords env a ws) {m : MachineState}
    (hs : env.Static m) {k : Nat} (hk : k < ws.length) : m.getMem (a + BitVec.ofNat 64 (8 * k)) = ws[k] :=
  env.static_data m hs _ (h k hk)

end Rv64mc.Spec.Whir
