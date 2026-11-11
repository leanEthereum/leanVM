/-
  LeanVMTests.Protocol.Whir.Params.Deployed

  Controls for the certified codes of the deployed WHIR ladders: the certificates check, the
  bound is tight at `2^-128`, level 0's slack is the largest that checks, a halved slack or a
  dropped query breaks it, a wrong square-root bracket is rejected, and the result feeds
  `stackedSpec`.
-/

import LeanVM.Protocol.Whir.Params.Deployed

/-!
# Deployed WHIR code controls

* **Inhabitant.** `defaultCert` and the table's certificates check (`Cert.OK`), so
  `deployedCodes` is built from the certificates and not from the fallback.
* **Tightness.** Every shape checks at `2^-128` and fails at `2^-129` (level 0's query group, at
  its limit): the smallest, `(16, 2)` and `(16, 3)`, and the largest, `(28, 4)`.
* **Level 0's slack is the largest.** One unit more at level 0 of `(16, 2)` (`e = 14336 → 14337`)
  or of `(28, 4)` (`e = 13059 → 13060`) breaks its query group. Level 0's list bound at `(28, 4)`
  is `642`, the largest, within the survivor bound `2^12` of `shapeOK`.
* **Slack.** Halving the slack of level 1 of `(16, 3)` (`e = 16 → 8`) breaks its fold group:
  ArkLib's exception count grows like `η^-3`; at level 0 of `(16, 2)` a slack of `40` breaks its
  fold group too.
* **Queries.** Dropping one of the 112 queries of level 0 of `(16, 2)`, or one of the 37 of
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

example : shapeOK 128 16 2 = true := by decide +kernel

example : shapeOK 129 16 2 = false := by decide +kernel

example : shapeOK 128 16 3 = true := by decide +kernel

example : shapeOK 129 16 3 = false := by decide +kernel

example : shapeOK 128 28 4 = true := by decide +kernel

example : shapeOK 129 28 4 = false := by decide +kernel

/-! ## Level 0's slack is the largest -/

example : certOf 28 4 0 = ⟨22, 4, 13059, 274877874175⟩ := rfl

/-- The query group of level 0 of `(28, 4)` with its 56 queries, at the table's slack. -/
example : (certOf 28 4 0).QueryOK 128 (certOf 28 4 1) 56 := by decide +kernel

/-- One unit of slack more breaks it. -/
example : ¬ (Cert.mk 22 4 13060 274877874175).QueryOK 128 (certOf 28 4 1) 56 := by decide +kernel

/-- At `(16, 2)` too. -/
example : ¬ (Cert.mk 10 2 14337 549487312863).QueryOK 128 (certOf 16 2 1) 112 := by decide +kernel

/-- Level 0's list bound at `(28, 4)`, the largest. -/
example : (certOf 28 4 0).listHi = 642 := by decide +kernel

/-! ## Load-bearing slack and query count -/

/-- The fold group of level 1 of `(16, 3)` at the table's slack `16 / 2^22`. -/
example : (certOf 16 3 1).FoldOK 128 4 := by decide +kernel

/-- Halving the slack breaks it. -/
example : ¬ (Cert.mk 6 6 8 136360984252).FoldOK 128 4 := by decide +kernel

/-- The query group of level 1 of `(16, 3)` with its 37 queries. -/
example : (certOf 16 3 1).QueryOK 128 (certOf 16 3 2) 37 := by decide +kernel

/-- One query fewer breaks it. -/
example : ¬ (certOf 16 3 1).QueryOK 128 (certOf 16 3 2) 36 := by decide +kernel

/-- The fold group of level 0 of `(16, 2)` at the table's slack `14336 / 2^22`. -/
example : certOf 16 2 0 = ⟨10, 2, 14336, 549487312863⟩ := rfl

example : (certOf 16 2 0).FoldOK 128 6 := by decide +kernel

/-- A slack of `40` breaks it. -/
example : ¬ (Cert.mk 10 2 40 549487312863).FoldOK 128 6 := by decide +kernel

/-- The query group of level 0 of `(16, 2)` with its 112 queries (`WHIR_QUERIES`,
`crates/verifier/src/whir.rs:20` at leanVM `aca3ea6a`). -/
example : (certOf 16 2 0).QueryOK 128 (certOf 16 2 1) 112 := by decide +kernel

/-- One query fewer breaks it. -/
example : ¬ (certOf 16 2 0).QueryOK 128 (certOf 16 2 1) 111 := by decide +kernel

/-! ## The bracket -/

example : ¬ (Cert.mk 6 6 16 136360984253).OK := by decide +kernel

/-! ## Feeding the specification -/

/-- `stackedSpec` at `εmax = 2^-128` for every admissible shape. -/
noncomputable example {μ R : ℕ} (h : Whir.Admissible μ R) {level : Whir.Level}
    {rest : List Whir.Level} (hc : Whir.ladder μ R = some (level :: rest))
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine μ c.1) (T : ENNReal) :
    LeanVM.Protocol.Compile.Spec (verifyStackedOpening μ R claims)
      (fun h ↦ StackedPre μ R (deployedCodes μ R 0) claims (LeanVM.Protocol.Compile.commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128)
      (eBatch claims.length (deployedCodes μ R 0)) T :=
  have hs := deployed_spec_hyps h hc
  stackedSpec claims hcl hc hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2 T

end LeanVMTests.Protocol.Whir.Params
