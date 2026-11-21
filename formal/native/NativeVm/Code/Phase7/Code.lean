module

public import NativeVm.Code.Phase7.LevelKit
public import NativeVm.Code.Phase7.Glue
public import NativeVm.Code.Phase7.Sumcheck
public import NativeVm.Code.Phase7.Point
public import NativeVm.Code.Phase7.BasisEval
public import NativeVm.Code.Phase7.FinalW

/-!
# The stacked opening's levels: the code

`levelC`, a non-final level (`levelM`): the level's parameters, the fold rounds, `μ` and the
queries' depth, the next commitment, the high part, the out-of-domain sample, the queries, `λ`,
the openings, the query weights, the subspace table, the batched value, the glued claims, the next
index (`incC`). `finalC`, the final level (`finalM`): the parameters, the fold rounds, `μ`, the
folded polynomial's `2^μ + fold` elements (count by `cntC`), the queries, the openings, the
subspace table, the queries' check, the sumcheck from the running claim (copied by `clmC`), the
point, the basis at it, the weight's check.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native

/-- The next level's index and the levels left (`r15` too). -/
def incC : Stmt := blk [ldW, ldw .rax cIdx, I (.addi .rax 1), stw cIdx .rax, ldw .r15 cN,
  I (.subi .r15 1), stw cN .r15]

/-- **A non-final level.** -/
def levelC : Stmt := blk [paramsC, nextC, foldRoundsC, muC, commitC, readScalarsC cFold hiO,
  I (.movi .rsi 15), Transcript.grind, sampleChallengesC cMu spO, readTo (tmpO + 28),
  I (.movi .rsi 17), Transcript.grind, sampleQueriesC, sampleTo (tmpO + 26),
  queryC, powC, tableC, batchC, glueC, incC]

/-- `cJ := 2^μ + fold` (`μ` at `cMu`, `fold` at `cFold`): the folded polynomial's count. -/
def cntC : Stmt := blk [ldW, ldw .rcx cMu, I (.movi .rax 1), I (.shlcl .rax), ldw .rdx cFold,
  I (.add .rax .rdx), stw cJ .rax]

/-- WHIR's running claim to the sumcheck's pair `tmpO + 14`. -/
def clmC : Stmt := blk ([ldW] ++ ldA whirR.off ++ stA (tmpO + 14))

/-- **The final level.** -/
def finalC : Stmt := blk [paramsC, foldRoundsC, muC, cntC, readScalarsC cJ hiO,
  I (.movi .rsi 17), Transcript.grind, sampleQueriesC, queryC, tableC, finalCheckC, clmC,
  sumcheckC, pointC, basisEvalC, finalWC]

end NativeVm.Code.P7
