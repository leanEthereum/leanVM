/-
  LeanVM.Guest.B1.Main.CalleesAt

  What `main`'s placed completeness assumes of the functions it calls that other groups prove:
  each one's uniform placed completeness (`CompleteRel`) on its honest precondition.
-/

module

public import LeanVM.Guest.B1.Main.LoopAt
public import LeanVM.Guest.B1.Main.Callees
public import LeanVM.Guest.B1.Digest.Statement
public import LeanVM.Guest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Da.ListDigest
public import LeanVM.Guest.B1.Sig.Sphincs
public import LeanVM.Guest.Hints

/-!
# The callees of `main`, placed

`CalleesAt fs cert κ bytecode`: for each function another group proves, `CompleteRel` at `κ` on
the precondition its Rel-level completeness takes, with the function's own buffers (scratch
tables, internal `HeapBuf`s) left to it:

* the signature verifiers, `statement_digest`, `da_list_digest`: their meanings;
* `claim_list_digest`, `child_claim_list_digest` (`ClPre`, `CclPre`): the squares table and the
  meaning without the windows' scratch table;
* `cover_da_root` (`CoverPre`): its meaning with the slot count at most `2^16`;
* `da_verify` (`DaVerifyPre`): the squares table and a witness opening the returned claim;
* `verify_sub` (`VsPre`): the exponent tables, and a proof the deferring verifier accepts for the
  child's public input under the seed, within the deployed stack log and stream limits, its fixed
  claims at `out`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (CompleteRel Meaning_verify_lean_xmss Meaning_verify_sig_lean_sphincs
  Meaning_statement_digest Meaning_da_list_digest)
open LeanVM.Guest.B1.Digest (SquaresAt CellsAt)

@[expose] public section

/-- `claim_list_digest`'s precondition: the squares table, `n < 2^16` canonical claims at `ptr`,
their digest returned. -/
def ClPre (rd : Reader) : List E → List E → Prop
  | [ptr, ng, gsq], [d0, d1] => SquaresAt rd gsq ∧ ∃ n < 2 ^ 16, ng = gen ^ n ∧ ∃ cs : List E,
      cs.length = 4 * n ∧ CellsAt rd ptr cs ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
        (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))
  | _, _ => False

/-- `child_claim_list_digest`'s precondition: the squares table, the region's size at most `2^16`,
`n < 2^16` canonical claims read at their table indices and marking their slots. -/
def CclPre (rd : Reader) : List E → List E → Prop
  | [entries, cover, base, origin, limit, ng, gsq], [d0, d1] => SquaresAt rd gsq ∧
      (∃ L ≤ 2 ^ 16, limit = gen ^ L) ∧ ∃ n < 2 ^ 16, ng = gen ^ n ∧ ∃ (off : ℕ → ℕ) (cs : List E),
        cs.length = 4 * n ∧ Digest.ChildReads rd entries cover base origin limit off cs n ∧
        (∀ c ∈ cs, IsCanonical128 c) ∧ (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))
  | _, _ => False

/-- `cover_da_root`'s precondition: slot `i` of `M ≤ 2^16` slots holds the mark, and the claim of
DA slot `i` is returned. -/
def CoverPre (rd : Reader) : List E → List E → Prop
  | [roots, cover, nslots, mark], [r0, r1, r2, r3] => ∃ i M, M ≤ 2 ^ 16 ∧ i < M ∧
      nslots = gen ^ M ∧ LoadHolds rd (cover * gen ^ i) 0 mark ∧
      CellsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3]
  | _, _ => False

/-- `da_verify`'s precondition: the squares table, and a witness opening the returned claim. -/
def DaVerifyPre (rd : Reader) : List E → List E → Prop
  | [gsq], [r0, r1, v0, v1] => SquaresAt rd gsq ∧ ∃ (root vd : Digest) (w : Da.Witness),
      w.Opens root vd ∧ (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd
  | _, _ => False

/-- The deployed limits on a child's proof (`Limits.stackLog`, `Limits.stream`). -/
def ProofLimits (bytecode : List K) (π : Proof) : Prop :=
  (∀ layout r, announced bytecode π.stream = some (layout, r) →
    22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28) ∧ π.stream.length ≤ Hints.streamCap

/-- `verify_sub`'s precondition: the exponent tables, and a proof the deferring verifier accepts
for the public input `pi` under the seed, within the deployed limits, its fixed claims at `out`. -/
def VsPre (bytecode : List K) (rd : Reader) : List E → List E → Prop
  | [pi0, pi1, s0, s1, glp, gsq, out], [] => ExpTables rd glp gsq ∧
      ∃ (pi seed : Digest) (fresh : FixedClaims) (π : Proof), (pi0, pi1) = digestScalars pi ∧
        (s0, s1) = digestScalars seed ∧ verifyDeferred bytecode seed pi fresh π = true ∧
        ProofLimits bytecode π ∧ ReadsAt rd out (fixedCells fresh)
  | _, _ => False

/-- **The callees of `main` other groups prove, complete uniformly and placed** at `κ`. -/
structure CalleesAt (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (bytecode : List K) :
    Prop where
  verify_lean_xmss : CompleteRel fs cert κ "verify_lean_xmss" Meaning_verify_lean_xmss
  verify_sig_lean_sphincs :
    CompleteRel fs cert κ "verify_sig_lean_sphincs" Meaning_verify_sig_lean_sphincs
  statement_digest : CompleteRel fs cert κ "statement_digest" Meaning_statement_digest
  da_list_digest : CompleteRel fs cert κ "da_list_digest" Meaning_da_list_digest
  cover_da_root : CompleteRel fs cert κ "cover_da_root" CoverPre
  claim_list_digest : CompleteRel fs cert κ "claim_list_digest" ClPre
  child_claim_list_digest : CompleteRel fs cert κ "child_claim_list_digest" CclPre
  da_verify : CompleteRel fs cert κ "da_verify" DaVerifyPre
  verify_sub : CompleteRel fs cert κ "verify_sub" (VsPre bytecode)

end
end LeanVM.Guest.B1.Main
