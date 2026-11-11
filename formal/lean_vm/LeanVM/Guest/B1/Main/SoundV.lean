/-
  LeanVM.Guest.B1.Main.SoundV

  `main`, soundly, its witness decoded from the frame map (the witness convention of G6,
  2026-10-23): every witness a function of a valuation, the memory and the frame map.
-/

module

public import LeanVM.Guest.B1.Main.SoundVX
public import LeanVM.Guest.B1.Sig.XmssLoop2

/-!
# `main`, its witness decoded from the frame map

`decWitV σ rd V piOf` is `decWit` with the callees' witness functions read off the frame map `V`:
a raw leanXMSS signature off its `__loop2` iteration's valuation (`Sig.xmssSigOf`: the check is
inline there), a leanSPHINCS one off its check's with `main`'s byte table (`Sig.sphincsSigOf`), the DA matrix off `da_verify`'s and its
callees' (`Da.dvWit`), a child proof by `piOf` off `verify_sub`'s (B1-d), the batching's hints off
`aggregate_claims`' valuation and the memory (`aggHints`). It mentions no hash and no verifier.

`main_sound_V bytecode piOf` (G6's `MainSoundV bytecode (fun σ rd V ↦ decWitV σ rd V piOf)`):
under any call relation `C` that unfolds at `V` and lies below `coreProgram.Rel`, a run of
`main`'s body gives the statement of the public input's digest, held by `decWitV σ rd V piOf`.
`main_sound_V_of_sub`: it holds given `SubSoundW bytecode piOf`, `verify_sub`'s statement with its
proof named by `piOf` (the form B1-d's `verify_sub_sound_w_Spec` takes): `SoundVX`'s
`main_sound_VX` at the leanXMSS segment's proof (`Sig.verify_lean_xmss_sound_holds`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- **`main`'s witness, decoded from the frame map `V`.** -/
noncomputable def decWitV (σ : Val) (rd : Reader) (V : FrameMap)
    (piOf : Reader → Val → FrameMap → Proof) : NodeWitness :=
  decWit σ rd (fun args => Sig.xmssSigOf (V "__loop2" args []))
    (fun p => Sig.sphincsSigOf (V "verify_sig_lean_sphincs" [p, σ (.n 47)] []) V)
    (fun args rets => Da.dvWit (V "da_verify" args rets) V)
    (fun args => piOf rd (V "verify_sub" args []) V)
    (fun args => aggHints rd (V "aggregate_claims" args []))

/-- **`main`, soundly, its witness decoded from the frame map** (G6's `MainSoundV`). -/
def main_sound_V (bytecode : List K) (piOf : Reader → Val → FrameMap → Proof) : Prop :=
  bytecode.length = 2 ^ bytecodeVars → ∀ (rd : Reader), MemOk rd → ∀ (C : CallRel) (V : FrameMap),
    UnfoldsV rd C V → CallRel.Le C (coreProgram.Rel rd) → ∀ (D : Digest) (σ : Val),
      LoadHolds rd 1 0 (digestHalves D).1 → LoadHolds rd 1 1 (digestHalves D).2 →
      Stmt.HoldsList C rd σ Data.core0.body False (fun rs ↦ rs = []) →
        statementDigest (decSeed σ) (decStmt σ rd) = D ∧
          NodeRelation bytecode (decSeed σ) (decStmt σ rd) (decWitV σ rd V piOf)

/-- **`main` is sound, its witness decoded from the frame map**, given `verify_sub`'s statement
with its proof named. -/
theorem main_sound_V_of_sub {bytecode : List K} {piOf : Reader → Val → FrameMap → Proof}
    (hv : SubSoundW bytecode piOf) : main_sound_V bytecode piOf :=
  main_sound_VX Sig.verify_lean_xmss_sound_holds hv

end
end LeanVM.Guest.B1.Main
