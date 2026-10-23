/-
  LeanVMTests.Protocol.Whir.Params.Deployed

  Controls for the certified codes of the deployed WHIR ladders: the certificates check, the
  bound is tight at `2^-128` for the weakest shapes, a halved slack or a dropped query breaks it,
  a wrong square-root bracket is rejected, and the result feeds `stackedSpec`.
-/

import LeanVM.Protocol.Whir.Params.Deployed

/-!
# Deployed WHIR code controls

* **Inhabitant.** `defaultCert` and the table's certificates check (`Cert.OK`), so
  `deployedCodes` is built from the certificates and not from the fallback.
* **Tightness.** The weakest shape `(μ, R) = (15, 2)` (about `2^-128.16`, level 0's query group)
  checks at `2^-128` and fails at `2^-129`; so does `(16, 3)` (about `2^-128.43`, level 1's fold
  group), the weakest before the query counts of leanVM `127510d1` (`b977f5fa`).
* **Slack.** Halving the slack of level 1 of `(16, 3)` (`e = 16 → 8`) breaks its fold group:
  ArkLib's exception count grows like `η^-3`; halving that of level 0 of `(15, 2)` (`e = 34 → 17`)
  breaks its fold group too.
* **Queries.** Dropping one of the 111 queries of level 0 of `(15, 2)`, or one of the 37 of
  level 1 of `(16, 3)`, breaks its query group.
* **Bracket.** Moving the bracket of `√ρ₋` up by one step is rejected.
* **Use.** `deployed_spec_hyps` supplies the code hypotheses of `stackedSpec` at
  `εmax = 2^-128`.
-/

namespace LeanVMTests.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.Whir.Params LeanVM.Protocol.EndToEnd

/-! ## Inhabitants -/

example : defaultCert.OK := defaultCert_ok

example : certOf 16 3 1 = ⟨6, 6, 16, 136360984252⟩ := rfl

example : (certOf 16 3 1).OK := by decide +kernel

example : (certOf 28 4 5).OK := by decide +kernel

/-! ## Tightness at `2^-128` -/

example : shapeOK 128 15 2 = true := by decide +kernel

example : shapeOK 129 15 2 = false := by decide +kernel

example : shapeOK 128 16 3 = true := by decide +kernel

example : shapeOK 129 16 3 = false := by decide +kernel

/-! ## Load-bearing slack and query count -/

/-- The fold group of level 1 of `(16, 3)` at the table's slack `16 / 2^22`. -/
example : (certOf 16 3 1).FoldOK 128 4 := by decide +kernel

/-- Halving the slack breaks it. -/
example : ¬ (Cert.mk 6 6 8 136360984252).FoldOK 128 4 := by decide +kernel

/-- The query group of level 1 of `(16, 3)` with its 37 queries. -/
example : (certOf 16 3 1).QueryOK 128 (certOf 16 3 2) 37 := by decide +kernel

/-- One query fewer breaks it. -/
example : ¬ (certOf 16 3 1).QueryOK 128 (certOf 16 3 2) 36 := by decide +kernel

/-- The fold group of level 0 of `(15, 2)` at the table's slack `34 / 2^22`. -/
example : certOf 15 2 0 = ⟨9, 2, 34, 549218680575⟩ := rfl

example : (certOf 15 2 0).FoldOK 128 6 := by decide +kernel

/-- Halving the slack breaks it. -/
example : ¬ (Cert.mk 9 2 17 549218680575).FoldOK 128 6 := by decide +kernel

/-- The query group of level 0 of `(15, 2)` with its 111 queries (`verifier.py:912` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`). -/
example : (certOf 15 2 0).QueryOK 128 (certOf 15 2 1) 111 := by decide +kernel

/-- One query fewer breaks it. -/
example : ¬ (certOf 15 2 0).QueryOK 128 (certOf 15 2 1) 110 := by decide +kernel

/-! ## The bracket -/

example : ¬ (Cert.mk 6 6 16 136360984253).OK := by decide +kernel

/-! ## Feeding the specification -/

/-- `stackedSpec` at `εmax = 2^-128` for every admissible shape. -/
noncomputable example {μ R : ℕ} (h : Whir.Admissible μ R) {level : Whir.Level}
    {rest : List Whir.Level} (hc : deriveConfig μ R = some (level :: rest))
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine μ c.1) (T : ENNReal) :
    LeanVM.Protocol.Compile.Spec (verifyStackedOpening μ R claims)
      (fun h ↦ StackedPre μ R (deployedCodes μ R 0) claims (LeanVM.Protocol.Compile.commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128)
      (eBatch claims.length (deployedCodes μ R 0)) T :=
  have hs := deployed_spec_hyps h hc
  stackedSpec claims hcl hc hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2 T

end LeanVMTests.Protocol.Whir.Params
