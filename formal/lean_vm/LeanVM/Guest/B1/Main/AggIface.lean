/-
  LeanVM.Guest.B1.Main.AggIface

  `aggregate_claims`' statement: at a valuation of its body, the batching program accepts the
  stream of the children whose words the memory holds, with the hints read off the valuation.
-/

module

public import LeanVM.Guest.B1.Main.Interface
public import LeanVM.Guest.B1.Digest.Steps
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims»

/-!
# `aggregate_claims`: its statement

`aggHints rd σ`: the batching's hints, read off `aggregate_claims`' valuation and the memory: the
proof of work's nonce `bc_sumcheck_msgs[0]`, the `BYTECODE_VARS` rounds after it, the split
program's value `bc_star_hint`.

`MeaningAggregateClaimsW rd h args rets`: for `n_children_g = g^m`, `1 ≤ m ≤ 16`, with the window
tables at `tabs`, `aggregate_claims` returns nothing and writes at `defer_stmt` a claim of
`BYTECODE_VARS` coordinates which, for every list of `m` children whose words the memory holds
(`ChildWordsAt`) and every stacked program of `BYTECODE_VARS` deferred variables, is the outcome of
the batching program (`Batch.nodeBatchingProgram`, the one `DeferredClaimBatched` runs) on their
stream and the hints `h`.

`AggregateClaimsSound`: every valuation of `aggregate_claims`' body under a call relation below
`coreProgram.Rel` gives the meaning with the hints `aggHints rd σ`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- The sumcheck's rounds `aggregate_claims` hints, read off the memory at `bc_sumcheck_msgs`. -/
noncomputable def aggRounds (rd : Reader) (σ : Val) : List (E × E) :=
  (List.range bytecodeVars).map fun k => (memAt rd (σ (.n (val% «aggregate_claims» "bc_msgs"))) (1 + 2 * k),
    memAt rd (σ (.n (val% «aggregate_claims» "bc_msgs"))) (2 + 2 * k))

/-- **`aggregate_claims`' hints**, read off its valuation and the memory: the proof of work's nonce,
`bc_sumcheck_msgs`' first word, the rounds after it, the split program's value `bc_star_hint`. -/
noncomputable def aggHints (rd : Reader) (σ : Val) : BatchingHints :=
  ⟨memAt rd (σ (.n (val% «aggregate_claims» "bc_msgs"))) 0, aggRounds rd σ,
    σ (.n (val% «aggregate_claims» "bytecode_star"))⟩

/-- **`aggregate_claims`, its hints named**: for `n_children_g = g^m`, `1 ≤ m ≤ 16`, with the
window tables at `tabs`, it returns nothing, and the claim written at `defer_stmt` is the outcome
of the batching program on the stream of every list of `m` children whose words the memory holds,
for every stacked program of `BYTECODE_VARS` deferred variables. -/
def MeaningAggregateClaimsW (rd : Reader) (h : BatchingHints) : List E → List E → Prop
  | [ncg, cpi, cfresh, ccarried, dst, tabs], rets => WinTabs rd tabs →
      ∀ m, 1 ≤ m → m ≤ 16 → ncg = gen ^ m →
      rets = [] ∧ ∃ out : DeferredBytecodeClaim,
        out.bytecodePoint.length = bytecodeVars ∧ ReadsAt rd dst out.cells ∧
        ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) →
          ∀ bytecode : List K, deferredVariableCount bytecode = bytecodeVars →
            Batch.runBatching (m := Id) keccakF1600 (Batch.nodeBatchingProgram (· = out) bytecode cs)
              ⟨Batch.batchingStream cs h, []⟩ = true
  | _, _ => False

/-- **`aggregate_claims` is sound**: on a memory image, a valuation of its body under a call
relation below `coreProgram.Rel` gives its meaning with the hints read off the valuation. -/
def AggregateClaimsSound : Prop :=
  ∀ {C : CallRel} {rd : Reader}, MemOk rd → CallRel.Le C (coreProgram.Rel rd) →
    ∀ {σ : Val} {args rets : List E}, (fn% «aggregate_claims»).params.map σ = args →
      Stmt.HoldsList C rd σ (Fn.body fn% «aggregate_claims») False (fun rs => rs = rets) →
        MeaningAggregateClaimsW rd (aggHints rd σ) args rets

end
end LeanVM.Guest.B1.Main
