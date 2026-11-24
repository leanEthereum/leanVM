/-
  LeanVM.Guest.B1.Digest.Statement

  B1 for `statement_digest`: the statement's digest, byte for byte.
-/

module

public import LeanVM.Guest.B1.Digest.Interface
import LeanVM.Guest.B1.Digest.StatementLink

/-!
# `statement_digest`

`statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da_0, da_1, defer)` hashes 32 cells: the
eight header cells, then the 24 deferred cells read at `defer`, and returns the first two cells of
the digest. Its core function is its reference function (`sd_linked`), whose meaning is the
statement's (`sdRef_sem`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Ref

@[expose] public section

/-- **`statement_digest`'s core IR is its meaning.** -/
theorem statement_digest_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "statement_digest" args rets ↔ MeaningStatementDigest rd args rets :=
  (rel_iff_sem find_statement_digest _ _).trans <|
    (Map.check_sem_iff sd_linked _ _).trans (sdRef_sem rd _ _)

/-- **`statement_digest` computes the statement's digest.** -/
theorem statement_digest_sound : statement_digest_sound_Spec :=
  fun rd args rets => (statement_digest_iff rd args rets).mp

/-- **`statement_digest` is complete.** -/
theorem statement_digest_complete : statement_digest_complete_Spec :=
  fun rd args rets => (statement_digest_iff rd args rets).mpr

end
end LeanVM.Guest.B1.Digest
