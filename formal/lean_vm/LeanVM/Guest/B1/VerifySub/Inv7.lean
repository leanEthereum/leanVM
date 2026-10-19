/-
  LeanVM.Guest.B1.VerifySub.Inv7

  `verify_sub` complete on an accepting proof within the deployed limits.
-/

module

public import LeanVM.Guest.B1.VerifySub.Inv6
public import LeanVM.Guest.B1.VerifySub.CPlaced8

/-!
# `verify_sub` is complete on an accepted proof

`verify_sub_completeAtB_of_accepts`: when the deferring verifier accepts `π` for `pi` under `seed`
and the claims `c`, with a stack log of at least 22 and at most 8192 stream words, and the
opening agrees at the cap along its run (`CapOk`, carried by the limits), `verify_sub` is
complete, uniformly and placed, on the exponent tables and `c`'s cells at `defer_out`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {bytecode : List K}

/-- **`verify_sub` is complete on an accepted proof** within the deployed limits. -/
theorem verify_sub_completeAtB_of_accepts {κ : ℕ} (hκ : 7 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {Bs : VsBounds} (hG : CompleteGkrAtB fs cert κ Bs.gkr)
    (hT : CompleteTablesAtB fs cert κ bytecode TCtx Bs.tab) (hF : CompleteFlockAtB fs cert κ Bs.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl) (hO : CompleteOpenAtB fs cert κ CapOk Bs.op)
    (hE : CompleteTermAtB fs cert κ TCtx PCtx Bs.term)
    (hb : bytecode.length = 2 ^ 22) {seed pi : Digest} {c : FixedClaims}
    {π : Proof} (h : verifyDeferred bytecode seed pi c π = true)
    (hlo : ∀ layout r, announced bytecode π.stream = some (layout, r) → 22 ≤ layout.stackLog)
    (hst : π.stream.length ≤ 8192)
    (hcap : ∀ D : VsData, D.Ok bytecode → D.seed = seed → D.pi = pi → D.proof = π →
      CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os D.target)
    (lpA sqA outA : ℕ) :
    CompleteAtB fs cert κ "verify_sub" (expL lpA sqA ++ [(outA, Node.fixedCells c)])
      [(digestScalars pi).1, (digestScalars pi).2, (digestScalars seed).1, (digestScalars seed).2,
        ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA), ofK (Parameters.gpow outA)]
      (Returns []) (vsBound fs Bs) := by
  obtain ⟨D, hok, htok, rfl, rfl, rfl, hp⟩ := vs_inversion hb h hlo hst
  exact verify_sub_completeAtB hκ hG hT hF hPl hO hE hb hok htok (hcap D hok rfl rfl hp) lpA sqA outA

/-- **`verify_sub` is complete on an accepted proof** within the deployed limits. -/
theorem verify_sub_completeAt_of_accepts {κ : ℕ} (hκ : 7 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    (hG : CompleteGkrAt fs cert κ) (hT : CompleteTablesAt fs cert κ bytecode TCtx)
    (hF : CompleteFlockAt fs cert κ) (hPl : CompletePlaceAt fs cert κ PCtx)
    (hO : CompleteOpenAt fs cert κ CapOk) (hE : CompleteTermAt fs cert κ TCtx PCtx)
    (hb : bytecode.length = 2 ^ 22) {seed pi : Digest} {c : FixedClaims}
    {π : Proof} (h : verifyDeferred bytecode seed pi c π = true)
    (hlo : ∀ layout r, announced bytecode π.stream = some (layout, r) → 22 ≤ layout.stackLog)
    (hst : π.stream.length ≤ 8192)
    (hcap : ∀ D : VsData, D.Ok bytecode → D.seed = seed → D.pi = pi → D.proof = π →
      CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os D.target)
    (lpA sqA outA : ℕ) :
    CompleteAtD fs cert κ "verify_sub" (expL lpA sqA ++ [(outA, Node.fixedCells c)])
      [(digestScalars pi).1, (digestScalars pi).2, (digestScalars seed).1, (digestScalars seed).2,
        ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA), ofK (Parameters.gpow outA)]
      (Returns []) := by
  obtain ⟨D, hok, htok, rfl, rfl, rfl, hp⟩ := vs_inversion hb h hlo hst
  exact verify_sub_completeAt hκ hG hT hF hPl hO hE hb hok htok (hcap D hok rfl rfl hp) lpA sqA outA

end
end LeanVM.Guest.B1.VerifySub
