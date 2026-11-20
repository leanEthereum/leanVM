/-
  Rv64mc.Spec.Whir.Basic

  What the WHIR family's contracts share:

  * words of the image's constant tables (`DataWords`, read from `Env.data`, so in place wherever `env.Static`
    holds, at every call's entry and return);
  * a `Result<E, VerifierError>` returned through the caller's slot (`sret`, in `a0`): `ResultEAt`, `Ok` with the
    value's limbs where the mirror returns, `Err` where it fails, and the slot as what the call writes (`SretOut`).
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Field

namespace Rv64mc.Spec.Whir

open RiscvZkvm.Rv64 LeanVM.Parameters

/-- **The words `ws` from `a` are constants of the image**: word `k` at `a + 8k`, each in `env.data`. -/
def DataWords (env : Env) (a : Word) (ws : List Word) : Prop :=
  ∀ k (h : k < ws.length), (a + BitVec.ofNat 64 (8 * k), ws[k]) ∈ env.data

/-- A constant word is in place in every state where `env.Static` holds. -/
theorem DataWords.getMem {env : Env} {a : Word} {ws : List Word} (h : DataWords env a ws) {m : MachineState}
    (hs : env.Static m) {k : Nat} (hk : k < ws.length) : m.getMem (a + BitVec.ofNat 64 (8 * k)) = ws[k] :=
  env.static_data m hs _ (h k hk)

/-- **The `Result<E, VerifierError>` at `a`**: `Ok` with `v`'s limbs where the mirror returns `some v`, `Err`
    where it fails. -/
def ResultEAt (m : MachineState) (a : Word) : Option E → Prop
  | some v => m.getMem (a + BitVec.ofNat 64 Layouts.ResultE.tagOffset) = BitVec.ofNat 64 Layouts.ResultE.Ok.tag ∧
      EAt m (a + BitVec.ofNat 64 Layouts.ResultE.Ok.f0) (Model.limbs v)
  | none => m.getMem (a + BitVec.ofNat 64 Layouts.ResultE.tagOffset) = BitVec.ofNat 64 Layouts.ResultE.Err.tag

/-- A function returning through `sret` (in `a0`) writes the `n` bytes of its slot. -/
def SretOut (n : Nat) (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) n b

end Rv64mc.Spec.Whir
