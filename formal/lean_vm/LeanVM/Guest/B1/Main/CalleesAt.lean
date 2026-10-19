/-
  LeanVM.Guest.B1.Main.CalleesAt

  What `main`'s placed completeness assumes of the functions it calls that other groups prove:
  each one's uniform placed completeness by bounded trees (`CompleteRelB`) on its honest
  precondition, within the bounds `CalleeBounds`.
-/

module

public import LeanVM.Guest.B1.Main.LoopAt
public import LeanVM.Guest.B1.Main.WeightAt
public import LeanVM.Guest.B1.VerifySub.StaticW
public import LeanVM.Guest.B1.Main.Callees
public import LeanVM.Guest.B1.Digest.Statement
public import LeanVM.Guest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Da.ListDigest
public import LeanVM.Guest.B1.Sig.Sphincs
public import LeanVM.Guest.Hints
public import LeanVM.Guest.B1.VerifySub.CPlaced3

/-!
# The callees of `main`, placed

`CalleesAt fs cert κ VsGood Bd`: for each function another group proves, `CompleteRelB` at `κ`
on the precondition its Rel-level completeness takes, within its bound in `Bd` (a constant, or a
function of the claims' count for the lists), with the function's own buffers (scratch tables,
internal `HeapBuf`s) left to it:

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
  run of an accepted proof within the deployed limits), group 6's
  `verify_sub_completeAtB_of_accepts` shape: the exponent tables and the run's fixed claims at the
  caller's words `vsExtL`, within a constant (group 6's `vsBound`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (CompleteRelB CompleteAtB Returns Meaning_verify_lean_xmss Meaning_verify_sig_lean_sphincs
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

/-- A completeness within the weights at every frame weight, at the weights `w θ`. -/
theorem CompleteAtW.reindex {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String} {Lin : Layout}
    {args : List E} {Out : List E → Layout → Prop} {B : ℕ} {Bw : (String → ℕ) → ℕ}
    (h : CompleteAtW fs cert (fun θ : String → ℕ => θ) κ f Lin args Out B Bw) {Θ : Type} (w : Θ → String → ℕ) :
    CompleteAtW fs cert w κ f Lin args Out B fun θ => Bw (w θ) := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, a, b, c, d, e, f', g, hwt⟩ := hr rd hl hm
    ⟨t, a, b, c, d, e, f', g, fun θ => hwt (w θ)⟩⟩

/-- **The bounds of `main`'s callees' trees**: constants for a signature verification, a
statement's digest, a DA slot's cover and a child's `verify_sub`; by the claims' count for a DA
list's digest, a claim list's and a child's claim list's; by the matrix's rows for the direct DA
claim's check, its weight by the frame weight and the rows. -/
structure CalleeBounds where
  xmss : ℕ
  sphincs : ℕ
  sd : ℕ
  daList : ℕ → ℕ
  cover : ℕ
  cl : ℕ → ℕ
  ccl : ℕ → ℕ
  daVerify : ℕ → ℕ
  daVerifyW : (String → ℕ) → ℕ → ℕ
  vs : ℕ
  vsW : (String → ℕ) → VerifySub.VsStat → ℕ

/-- **The callees of `main` other groups prove, complete uniformly and placed** at `κ`, by trees
within `Bd`. -/
structure CalleesAt (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    (VsGood : VerifySub.VsData → Prop) (Bd : CalleeBounds) : Prop where
  verify_lean_xmss : CompleteRelB fs cert κ "verify_lean_xmss" Meaning_verify_lean_xmss Bd.xmss
  verify_sig_lean_sphincs :
    CompleteRelB fs cert κ "verify_sig_lean_sphincs" Meaning_verify_sig_lean_sphincs Bd.sphincs
  statement_digest : ∀ sig cells,
    CompleteRelB fs cert κ "statement_digest" (SdPreAt sig cells) Bd.sd
  da_list_digest : ∀ claims,
    CompleteRelB fs cert κ "da_list_digest" (DaListPreAt claims) (Bd.daList claims.length)
  cover_da_root : ∀ i, CompleteRelB fs cert κ "cover_da_root" (CoverPreAt i) Bd.cover
  claim_list_digest : ∀ cs,
    CompleteRelB fs cert κ "claim_list_digest" (ClPreAt cs) (Bd.cl (cs.length / 4))
  child_claim_list_digest : ∀ off cs,
    CompleteRelB fs cert κ "child_claim_list_digest" (CclPreAt off cs) (Bd.ccl (cs.length / 4))
  da_verify : ∀ (wt : Da.Witness) (root vd : Digest), wt.Opens root vd → ∀ (args rets : List E) (Lin : Layout),
    (∀ rd, LowDef κ rd → MemL rd Lin → DaVerifyPreAt root vd rd args rets) →
    CompleteAtW fs cert (fun θ : String → ℕ => θ) κ "da_verify" Lin args (Returns rets)
      (Bd.daVerify wt.rows.length) fun θ => Bd.daVerifyW θ wt.rows.length
  verify_sub : ∀ D, VsGood D → ∀ lpA sqA outA : ℕ, ∀ {Θ : Type} (w : Θ → String → ℕ)
    (c : Θ → VerifySub.VsStat), (∀ θ, VerifySub.VsStatOk (w θ) (c θ)) → CompleteAtW fs cert w κ "verify_sub"
    (VerifySub.vsExtL lpA sqA outA D) [(digestScalars D.pi).1, (digestScalars D.pi).2,
      (digestScalars D.seed).1, (digestScalars D.seed).2, ofK (gpow lpA), ofK (gpow sqA),
      ofK (gpow outA)] (Returns []) Bd.vs fun θ => Bd.vsW (w θ) (c θ)

end
end LeanVM.Guest.B1.Main
