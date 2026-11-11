/-
  LeanVM.Guest.B1.Main.KidCoverAt

  A child's statement digest in the uniform placed form: the pure `statement_digest`.
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Digest.StatementComplete

/-!
# A child's statement digest, placed

* `statement_completeAt`: the pure digest, from its completeness on every memory holding the
  caller's words;
* `statementDigest_of_parts`: a statement's digest from its header cells and deferred cells.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD Returns completeAt_of_rel_pureD)
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Node
open LeanVM.Guest.Value.Keccak (cellsBytes)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-! ## The pure digests -/

set_option maxRecDepth 100000 in
theorem sd_pure : coreProgram.PureIn ["statement_digest"] := by
  intro g hg fn hf
  rw [List.mem_singleton] at hg
  subst hg
  rw [find_statement_digest, Option.some.injEq] at hf
  subst hf
  decide +kernel

/-- **`statement_digest` is complete, placed**, on every memory holding the caller's words
`MeaningStatementDigest` reads. -/
theorem statement_completeAt {κ : ℕ} {Lin : Layout} {args rets : List E}
    (h : ∀ rd, MemL rd Lin → MeaningStatementDigest rd args rets) :
    CompleteAtD fs cert κ "statement_digest" Lin args (Returns rets) :=
  completeAt_of_rel_pureD sd_pure (List.mem_singleton_self _)
    (fun rd hm => statement_digest_complete rd args rets (h rd hm)) κ

/-- **A statement's digest from its parts**: the header cells' bytes and the 24 deferred cells. -/
theorem statementDigest_of_parts {seed : Digest} {s : NodeStatement}
    {s0 s1 x0 x1 y0 y1 d0 d1 : E} {defer : List E} (hseed : digestBytes seed = cellsBytes [s0, s1])
    (hx : digestBytes (claimListDigest xmssPublicKeyBytes s.claims.xmss) = cellsBytes [x0, x1])
    (hs : digestBytes (claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs) = cellsBytes [y0, y1])
    (hda : digestBytes s.claims.daDigest = cellsBytes [d0, d1])
    (hdef : s.deferredClaim.cells = defer) (hlen : defer.length = 24) :
    statementDigest seed s = keccak256 (stmtBytes [s0, s1, x0, x1, y0, y1, d0, d1] defer) := by
  unfold statementDigest statementPreimage paddedDeferredClaimCells stmtBytes
  rw [hseed, hx, hs, hda, hdef, hlen,
    show cellsBytes [s0, s1, x0, x1, y0, y1, d0, d1] = cellsBytes [s0, s1] ++ cellsBytes [x0, x1] ++
      cellsBytes [y0, y1] ++ cellsBytes [d0, d1] by simp [cellsBytes]]
  simp

end
end LeanVM.Guest.B1.Main
