/-
  LeanVM.Guest.B1.Main.CalleesAt

  What `main`'s placed completeness assumes of the functions it calls that other groups prove:
  each one's uniform placed completeness (`CompleteRelD`) on its honest precondition.
-/

module

public import LeanVM.Guest.B1.Main.LoopAt
public import LeanVM.Guest.B1.Main.Callees
public import LeanVM.Guest.B1.Digest.Statement
public import LeanVM.Guest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Da.ListDigest
public import LeanVM.Guest.B1.Sig.Sphincs
public import LeanVM.Guest.Hints
public import LeanVM.Guest.B1.VerifySub.CPlaced3

/-!
# The callees of `main`, placed

`CalleesAt fs cert κ VsGood`: for each function another group proves, `CompleteRelD` at `κ` on
the precondition its Rel-level completeness takes, with the function's own buffers (scratch
tables, internal `HeapBuf`s) left to it:

* the signature verifiers: their meanings;
* `statement_digest` (`SdPreAt sig cells`), `da_list_digest` (`DaListPreAt claims`): their
  meanings with the words read from memory given;
* `claim_list_digest`, `child_claim_list_digest` (`ClPreAt`, `CclPreAt`): for the claims' cells
  (and the child's table indices) given, the squares table and the meaning without the windows'
  scratch table;
* `cover_da_root` (`CoverPreAt i`): for the DA slot `i`, its meaning with the slot count at most
  `2^16`;
* `da_verify` (`DaVerifyPreAt`): for a witness opening the claim, the squares table and the claim's
  cells returned;
* `verify_sub`: for every run of the deferring verifier `VsGood` admits (group 6's `VsData`, the
  run of an accepted proof within the deployed limits), group 6's `verify_sub_completeAt` shape:
  the exponent tables and the run's fixed claims at the caller's words `vsExtL`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (CompleteRelD CompleteAtD Returns Meaning_verify_lean_xmss Meaning_verify_sig_lean_sphincs
  Meaning_statement_digest Meaning_da_list_digest)
open LeanVM.Guest.B1.Digest (SquaresAt CellsAt)

@[expose] public section

/-- `claim_list_digest`'s precondition, for the claims' cells `cs`: the squares table, `n < 2^16`
canonical claims at `ptr`, their digest returned. -/
def ClPreAt (cs : List E) (rd : Reader) : List E → List E → Prop
  | [ptr, ng, gsq], [d0, d1] => SquaresAt rd gsq ∧ ∃ n < 2 ^ 16, ng = gen ^ n ∧
      cs.length = 4 * n ∧ CellsAt rd ptr cs ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
        (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))
  | _, _ => False

/-- `child_claim_list_digest`'s precondition, for the table indices `off` and the claims' cells
`cs`: the squares table, the region's size at most `2^16`, `n < 2^16` canonical claims read at
their table indices and marking their slots. -/
def CclPreAt (off : ℕ → ℕ) (cs : List E) (rd : Reader) : List E → List E → Prop
  | [entries, cover, base, origin, limit, ng, gsq], [d0, d1] => SquaresAt rd gsq ∧
      (∃ L ≤ 2 ^ 16, limit = gen ^ L) ∧ ∃ n < 2 ^ 16, ng = gen ^ n ∧
        cs.length = 4 * n ∧ Digest.ChildReads rd entries cover base origin limit off cs n ∧
        (∀ c ∈ cs, IsCanonical128 c) ∧ (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))
  | _, _ => False

/-- `statement_digest`'s precondition, for the signer set's digest `sig` and the deferred cells
`cells`: the statement's digest of the seed, `sig` read at `sigp`, the DA list's digest and
`cells` read at `dp`. -/
def SdPreAt (sig : Digest) (cells : List E) (rd : Reader) : List E → List E → Prop
  | [seed0, seed1, sigp, da0, da1, dp], [d0, d1] => ∃ (seed da : Digest),
      cells.length = Digest.deferStmtCells ∧ (seed0, seed1) = digestScalars seed ∧
      LoadHolds rd sigp 0 (digestScalars sig).1 ∧ LoadHolds rd sigp 1 (digestScalars sig).2 ∧
      (da0, da1) = digestScalars da ∧ CellsAt rd dp cells ∧
      (d0, d1) = digestScalars (stmtDigestOf seed sig da cells)
  | _, _ => False

/-- `da_list_digest`'s precondition, for the claims `claims`: at most `16` of them at `roots`,
their list digest returned. -/
def DaListPreAt (claims : List DaClaim) (rd : Reader) : List E → List E → Prop
  | [roots, ng], [d0, d1] => claims.length ≤ 16 ∧ ng = gen ^ claims.length ∧
      LeanVM.Guest.B1.DaClaimsAt rd roots claims ∧ (d0, d1) = digestScalars (daListDigest claims)
  | _, _ => False

/-- `cover_da_root`'s precondition, for the DA slot `i`: slot `i` of `M ≤ 2^16` slots holds the
mark, and the claim of DA slot `i` is returned. -/
def CoverPreAt (i : ℕ) (rd : Reader) : List E → List E → Prop
  | [roots, cover, nslots, mark], [r0, r1, r2, r3] => ∃ M, M ≤ 2 ^ 16 ∧ i < M ∧
      nslots = gen ^ M ∧ LoadHolds rd (cover * gen ^ i) 0 mark ∧
      CellsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3]
  | _, _ => False

/-- `da_verify`'s precondition, for the claim `(root, vd)`: the squares table, the claim's cells
returned. -/
def DaVerifyPreAt (root vd : Digest) (rd : Reader) : List E → List E → Prop
  | [gsq], [r0, r1, v0, v1] => SquaresAt rd gsq ∧ (r0, r1) = digestScalars root ∧
      (v0, v1) = digestScalars vd
  | _, _ => False

/-- **The callees of `main` other groups prove, complete uniformly and placed** at `κ`. -/
structure CalleesAt (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    (VsGood : VerifySub.VsData → Prop) : Prop where
  verify_lean_xmss : CompleteRelD fs cert κ "verify_lean_xmss" Meaning_verify_lean_xmss
  verify_sig_lean_sphincs :
    CompleteRelD fs cert κ "verify_sig_lean_sphincs" Meaning_verify_sig_lean_sphincs
  statement_digest : ∀ sig cells, CompleteRelD fs cert κ "statement_digest" (SdPreAt sig cells)
  da_list_digest : ∀ claims, CompleteRelD fs cert κ "da_list_digest" (DaListPreAt claims)
  cover_da_root : ∀ i, CompleteRelD fs cert κ "cover_da_root" (CoverPreAt i)
  claim_list_digest : ∀ cs, CompleteRelD fs cert κ "claim_list_digest" (ClPreAt cs)
  child_claim_list_digest : ∀ off cs,
    CompleteRelD fs cert κ "child_claim_list_digest" (CclPreAt off cs)
  da_verify : ∀ (wt : Da.Witness) (root vd : Digest), wt.Opens root vd →
    CompleteRelD fs cert κ "da_verify" (DaVerifyPreAt root vd)
  verify_sub : ∀ D, VsGood D → ∀ lpA sqA outA : ℕ, CompleteAtD fs cert κ "verify_sub"
    (VerifySub.vsExtL lpA sqA outA D) [(digestScalars D.pi).1, (digestScalars D.pi).2,
      (digestScalars D.seed).1, (digestScalars D.seed).2, ofK (gpow lpA), ofK (gpow sqA),
      ofK (gpow outA)] (Returns [])

end
end LeanVM.Guest.B1.Main
