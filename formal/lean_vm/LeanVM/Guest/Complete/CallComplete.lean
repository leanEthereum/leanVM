module

public import LeanVM.Guest.Exact.Every
public import LeanVM.Guest.Memory.Tree
public import LeanVM.Guest.Memory.LowDef
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.B1.VerifySub.Interface
public import Statement.LeanVmGuestProver

/-!
# Layout-free completeness of a call, and `verify_sub`'s as a hypothesis

Hotwire's executor aligns some allocations (`allocBase`), so the bus era's placed completeness
(`CompleteAtD`, over the old allocator's layout) is not restored. A call's completeness is stated
here without a layout: from any base `b`, the call needs memory to hold its own words `W` within
`[b, b + n)` (its stores and the heap words its hints write: stores are loads of write-once memory),
and on every memory holding them, its inputs (`Pre`) and the low region the range checks read, it
has a valid tree, its buffers' sizes those of its body, satisfying `Post` (`CallCompletes`). The
placed (aligned) form is rebuilt over the executor's layout from it.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Guest.B1

@[expose] public section

/-- Runs of words in memory: each a first word's index and its words. -/
abbrev Words : Type := List (ℕ × List E)

/-- The memory holds each run, word `k` of a run from index `i` at `g^(i + k)`. -/
def HoldsWords (rd : Reader) (W : Words) : Prop :=
  ∀ q ∈ W, ReadsAt rd (ofK (addressOfIndex q.1)) q.2

/-- The runs lie in `[b, b + n)` and are pairwise disjoint. -/
def WordsIn (W : Words) (b n : ℕ) : Prop :=
  (∀ q ∈ W, b ≤ q.1 ∧ q.1 + q.2.length ≤ b + n) ∧
    W.Pairwise fun q q' => q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1

/-- **A call completes, layout-free**: from every base `b`, its own words `W` lie in `[b, b + n)`,
and on every memory defined on its first `2^k` words, holding `W` and satisfying `Pre`, the call of
`f` on `args` has a valid tree returning `rets`, its buffers its body's, satisfying `Post`. -/
def CallCompletes (k : ℕ) (f : String) (args rets : List E) (Pre : Reader → Prop)
    (Post : Reader → Tree → Prop) : Prop :=
  ∀ b, ∃ (n : ℕ) (W : Words), WordsIn W b n ∧
    ∀ rd, LowDef k rd → HoldsWords rd W → Pre rd →
      ∃ t : Tree, t.name = f ∧ t.Valid coreProgram rd args rets ∧ t.BufsOk coreProgram ∧ Post rd t

/-- **What `verify_sub`'s completeness asks of a child**: `AcceptableChild`'s conjuncts but the
deferred claim's shape, which `verify_sub` does not read. -/
def VsChildOk (bytecode : List K) (seed : Digest) (c : Child) : Prop :=
  verifyDeferred bytecode seed (statementDigest seed c.statement) c.freshClaim c.proof = true ∧
    (∀ layout r, announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog) ∧
    c.proof.stream.length ≤ Coverage.childStreamCap ∧
    ∀ step ∈ Limits.queryStepsOf
        (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed c.statement))
        (Coverage.childVerifierStart seed c),
      Limits.OpeningsAgree step.1 step.2

theorem vsChildOk_of_acceptable {bytecode : List K} {seed : Digest} {c : Child}
    (h : AcceptableChild bytecode seed c) : VsChildOk bytecode seed c :=
  ⟨h.verifies, h.stackLogAtLeastMinimum, h.streamWithinCap, h.capsAgree⟩

/-- `verify_sub`'s arguments as `main` passes them for child `c`: the halves of its statement's
digest and of the seed, the exponent table at `gsq`, the fresh claim's destination `out`. -/
def vsArgs (seed : Digest) (c : Child) (gsq out : E) : List E :=
  [(digestHalves (statementDigest seed c.statement)).1, (digestHalves (statementDigest seed c.statement)).2,
    (digestHalves seed).1, (digestHalves seed).2, gsq, out]

end
end LeanVM.Guest.Complete
