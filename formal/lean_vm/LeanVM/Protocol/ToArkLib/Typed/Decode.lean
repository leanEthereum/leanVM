/-
  LeanVM.Protocol.ToArkLib.Typed.Decode

  A typed front component whose first move is a prover message, read on the wire: the verifier
  decodes the wire message into the message and runs the component's verdict on it. Knowledge
  soundness transports at the same errors. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Typed.Component

/-!
# Decoding the first message

`sendFirst M rest r ors smp` is a slot whose first move is a prover message of type `M`, the same
slot after any message. A component `D` on it reads its first message on the wire as
`D.decode dec enc`: the wire message `m' : M'` is decoded into `dec s m'` before `D`'s verdict
reads it, and the honest prover encodes its message with `enc`.

`Security.decode`: a security of `D` at errors constant across the first message is a security of
the decoded component at the same errors, with `D`'s extractor read on the decoded message.
-/

namespace LeanVM.Protocol.Typed

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp

@[expose] public section

/-- A slot whose first move is a prover message of type `M`, then the same slot whatever it is. -/
abbrev sendFirst (M : Type) (rest : Oracle.TypeTree.{0}) (r : rest.RoleDecoration)
    (ors : rest.OracleDecoration) (smp : Samplers rest r) : Slot :=
  ⟨.public M fun _ ↦ rest, ⟨.sender, fun _ ↦ r⟩, ⟨PUnit.unit, fun _ ↦ ors⟩, fun _ ↦ smp⟩

variable {ι : Type} {O : ι → Type} {S T W : Type} {M M' : Type} {rest : Oracle.TypeTree.{0}}
  {r : rest.RoleDecoration} {ors : rest.OracleDecoration} {smp : Samplers rest r}

/-- The component reading its first message on the wire: the verdict decodes it, the honest
prover encodes it. -/
def Def.decode (D : Def O S W T W (sendFirst M rest r ors smp)) (dec : S → M' → M)
    (enc : S → M → M') : Def O S W T W (sendFirst M' rest r ors smp) where
  verdict s p := D.verdict s ⟨dec s p.1, p.2⟩
  prover so w := do
    let x ← D.prover so w
    return ⟨enc so.1 x.1, x.2⟩

/-- **The transport**: a security at errors constant across the first message is a security of
the decoded component at the same errors, the extractor read on the decoded message. -/
def Security.decode {D : Def O S W T W (sendFirst M rest r ors smp)}
    {relIn : Set ((S × ∀ i, O i) × W)} {relOut : Set ((T × ∀ i, O i) × W)} {e : Errors rest r}
    (Sec : Security D relIn relOut fun _ ↦ e) (dec : S → M' → M) (enc : S → M → M') :
    Security (D.decode dec enc) relIn relOut fun _ ↦ e where
  extractor s o m' := Sec.extractor s o (dec s m')
  prover_preserving s o := ⟨fun m' h w hw ↦ (Sec.prover_preserving s o).1 (dec s m') h w hw,
    fun m' ↦ (Sec.prover_preserving s o).2 (dec s m')⟩
  local_bound s o m' := Sec.local_bound s o (dec s m')
  terminal s o :=
    { witnessEquiv := fun path ↦ (Sec.terminal s o).witnessEquiv ⟨dec s path.1, path.2⟩
      knowledge_iff := fun path w ↦ (Sec.terminal s o).knowledge_iff ⟨dec s path.1, path.2⟩ w }

end
end LeanVM.Protocol.Typed
