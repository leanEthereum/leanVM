import LeanVM.Guest.B1.Bits.GPowerP
import LeanVM.Guest.B1.Bits.MeaningP
import LeanVM.Guest.B1.Bits.QueryWindowsAll
import LeanVM.Guest.B1.Bits.QueryWindowsCompleteAll
import LeanVM.Guest.B1.Fs.Message
import LeanVM.Guest.B1.Whir.DataAll
import LeanVM.Guest.B1.Whir.HelperAll
import LeanVM.Guest.B1.Whir.HelperTables
import LeanVM.Guest.B1.Whir.Round
import LeanVM.Guest.B1.Whir.RoundComplete
import LeanVM.Guest.B1.Whir.Loops
import LeanVM.Guest.B1.Whir.SqLoop
import LeanVM.Guest.B1.Whir.ResLoop
import LeanVM.Guest.B1.Whir.LpSound
import LeanVM.Guest.B1.Whir.LqSound
import LeanVM.Guest.B1.Whir.LrSound
import LeanVM.Guest.B1.Sig.Bytes
import LeanVM.Guest.B1.Sig.Codeword
import LeanVM.Guest.B1.Sig.CodewordComplete
import LeanVM.Guest.B1.Sig.CompleteBasic
import LeanVM.Guest.B1.Sig.CompleteKit
import LeanVM.Guest.B1.Sig.CwComplete
import LeanVM.Guest.B1.Sig.CwKeep
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Sig.Digest80
import LeanVM.Guest.B1.Sig.Frame
import LeanVM.Guest.B1.Sig.FwdComplete
import LeanVM.Guest.B1.Sig.InterfaceP
import LeanVM.Guest.B1.Sig.KMsgComplete
import LeanVM.Guest.B1.Sig.KSeqComplete
import LeanVM.Guest.B1.Sig.KeccakMsg
import LeanVM.Guest.B1.Sig.Merkle
import LeanVM.Guest.B1.Sig.MerkleComplete
import LeanVM.Guest.B1.Sig.SeqComplete
import LeanVM.Guest.B1.Sig.Shapes
import LeanVM.Guest.B1.Sig.Shifts
import LeanVM.Guest.B1.Sig.SpWotsArms
import LeanVM.Guest.B1.Sig.SpWotsCheck
import LeanVM.Guest.B1.Sig.SpWotsComplete
import LeanVM.Guest.B1.Sig.SpWotsCompleteR
import LeanVM.Guest.B1.Sig.SpWotsCompleteStmt
import LeanVM.Guest.B1.Sig.SpWotsData
import LeanVM.Guest.B1.Sig.SpWotsData0
import LeanVM.Guest.B1.Sig.SpWotsData1
import LeanVM.Guest.B1.Sig.SpWotsGroupComplete
import LeanVM.Guest.B1.Sig.SpWotsGroups
import LeanVM.Guest.B1.Sig.SpWotsLayout
import LeanVM.Guest.B1.Sig.SpWotsRen0
import LeanVM.Guest.B1.Sig.SpWotsRen1
import LeanVM.Guest.B1.Sig.SpWotsRen2
import LeanVM.Guest.B1.Sig.SpWotsRen3
import LeanVM.Guest.B1.Sig.SpWotsRenDefs
import LeanVM.Guest.B1.Sig.SpWotsSound
import LeanVM.Guest.B1.Sig.SpWotsStepComplete
import LeanVM.Guest.B1.Sig.SpWotsT
import LeanVM.Guest.B1.Sig.SphincsAdrs
import LeanVM.Guest.B1.Sig.SphincsBottomComplete
import LeanVM.Guest.B1.Sig.SphincsBridge
import LeanVM.Guest.B1.Sig.SphincsBridgeCells
import LeanVM.Guest.B1.Sig.SphincsBytes
import LeanVM.Guest.B1.Sig.SphincsBytesComplete
import LeanVM.Guest.B1.Sig.SphincsComplete
import LeanVM.Guest.B1.Sig.SphincsCompleteBlocks
import LeanVM.Guest.B1.Sig.SphincsCompleteConv
import LeanVM.Guest.B1.Sig.SphincsCompleteHolds
import LeanVM.Guest.B1.Sig.SphincsCompleteSpec
import LeanVM.Guest.B1.Sig.SphincsData
import LeanVM.Guest.B1.Sig.SphincsData0
import LeanVM.Guest.B1.Sig.SphincsData1
import LeanVM.Guest.B1.Sig.SphincsData2
import LeanVM.Guest.B1.Sig.SphincsDigestComplete
import LeanVM.Guest.B1.Sig.SphincsDigestData
import LeanVM.Guest.B1.Sig.SphincsDigestT
import LeanVM.Guest.B1.Sig.SphincsFields
import LeanVM.Guest.B1.Sig.SphincsFieldsComplete
import LeanVM.Guest.B1.Sig.SphincsForsComplete
import LeanVM.Guest.B1.Sig.SphincsForsT
import LeanVM.Guest.B1.Sig.SphincsGlue
import LeanVM.Guest.B1.Sig.SphincsHash
import LeanVM.Guest.B1.Sig.SphincsHtComplete
import LeanVM.Guest.B1.Sig.SphincsLayersComplete
import LeanVM.Guest.B1.Sig.SphincsLoads
import LeanVM.Guest.B1.Sig.SphincsPathComplete
import LeanVM.Guest.B1.Sig.SphincsSig
import LeanVM.Guest.B1.Sig.SphincsSound
import LeanVM.Guest.B1.Sig.SphincsSoundAddrs
import LeanVM.Guest.B1.Sig.SphincsSoundBlocks
import LeanVM.Guest.B1.Sig.SphincsSoundDigest
import LeanVM.Guest.B1.Sig.SphincsSoundFors
import LeanVM.Guest.B1.Sig.SphincsSoundHt
import LeanVM.Guest.B1.Sig.SphincsSoundKey
import LeanVM.Guest.B1.Sig.SphincsSoundLayer
import LeanVM.Guest.B1.Sig.SphincsSoundPath
import LeanVM.Guest.B1.Sig.SphincsSoundWots
import LeanVM.Guest.B1.Sig.SphincsStagesComplete
import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.SphincsTopComplete
import LeanVM.Guest.B1.Sig.WotsArm
import LeanVM.Guest.B1.Sig.WotsComplete
import LeanVM.Guest.B1.Sig.WotsCongr
import LeanVM.Guest.B1.Sig.WotsGroup
import LeanVM.Guest.B1.Sig.WotsGroupComplete
import LeanVM.Guest.B1.Sig.WotsSound
import LeanVM.Guest.B1.Sig.WotsT
import LeanVM.Guest.B1.Sig.XmssBound
import LeanVM.Guest.B1.Sig.XmssCore
import LeanVM.Guest.B1.Sig.XmssGroups
import LeanVM.Guest.B1.Sig.XmssLayer
import LeanVM.Guest.B1.Sig.XmssLoop2
import LeanVM.Guest.B1.Sig.XmssScheme
import LeanVM.Guest.B1.Sig.XmssSegArms
import LeanVM.Guest.B1.Sig.XmssSegCodeC
import LeanVM.Guest.B1.Sig.XmssSegComplete
import LeanVM.Guest.B1.Sig.XmssSegCoreC
import LeanVM.Guest.B1.Sig.XmssSegCwC
import LeanVM.Guest.B1.Sig.XmssSegData
import LeanVM.Guest.B1.Sig.XmssSegData1
import LeanVM.Guest.B1.Sig.XmssSegData10
import LeanVM.Guest.B1.Sig.XmssSegData11
import LeanVM.Guest.B1.Sig.XmssSegData12
import LeanVM.Guest.B1.Sig.XmssSegData13
import LeanVM.Guest.B1.Sig.XmssSegData14
import LeanVM.Guest.B1.Sig.XmssSegData15
import LeanVM.Guest.B1.Sig.XmssSegData16
import LeanVM.Guest.B1.Sig.XmssSegData17
import LeanVM.Guest.B1.Sig.XmssSegData18
import LeanVM.Guest.B1.Sig.XmssSegData19
import LeanVM.Guest.B1.Sig.XmssSegData2
import LeanVM.Guest.B1.Sig.XmssSegData20
import LeanVM.Guest.B1.Sig.XmssSegData21
import LeanVM.Guest.B1.Sig.XmssSegData22
import LeanVM.Guest.B1.Sig.XmssSegData23
import LeanVM.Guest.B1.Sig.XmssSegData24
import LeanVM.Guest.B1.Sig.XmssSegData25
import LeanVM.Guest.B1.Sig.XmssSegData26
import LeanVM.Guest.B1.Sig.XmssSegData27
import LeanVM.Guest.B1.Sig.XmssSegData28
import LeanVM.Guest.B1.Sig.XmssSegData29
import LeanVM.Guest.B1.Sig.XmssSegData3
import LeanVM.Guest.B1.Sig.XmssSegData30
import LeanVM.Guest.B1.Sig.XmssSegData31
import LeanVM.Guest.B1.Sig.XmssSegData32
import LeanVM.Guest.B1.Sig.XmssSegData33
import LeanVM.Guest.B1.Sig.XmssSegData34
import LeanVM.Guest.B1.Sig.XmssSegData4
import LeanVM.Guest.B1.Sig.XmssSegData5
import LeanVM.Guest.B1.Sig.XmssSegData6
import LeanVM.Guest.B1.Sig.XmssSegData7
import LeanVM.Guest.B1.Sig.XmssSegData8
import LeanVM.Guest.B1.Sig.XmssSegData9
import LeanVM.Guest.B1.Sig.XmssSegDigestC
import LeanVM.Guest.B1.Sig.XmssSegEnds
import LeanVM.Guest.B1.Sig.XmssSegLayerC
import LeanVM.Guest.B1.Sig.XmssSegPath
import LeanVM.Guest.B1.Sig.XmssSegPathC
import LeanVM.Guest.B1.Sig.XmssSegSound
import LeanVM.Guest.B1.Sig.XmssSegStepC
import LeanVM.Guest.B1.Sig.XmssSegT
import LeanVM.Guest.B1.Sig.XmssSegWinSpec
import LeanVM.Guest.B1.Sig.XmssStep
import LeanVM.Guest.B1.Sig.XmssT
import LeanVM.Guest.B1.Sig.XmssWindows

import LeanVM.Guest.B1.Merkle.Cap
import LeanVM.Guest.B1.Merkle.CapAllP
import LeanVM.Guest.B1.Merkle.Climb
import LeanVM.Guest.B1.Merkle.Meaning
import LeanVM.Guest.B1.Opening.FoldAlg
import LeanVM.Guest.B1.Opening.Interface
import LeanVM.Guest.B1.Opening.Meaning
import LeanVM.Guest.B1.Opening.NovelEval
import LeanVM.Guest.B1.Opening.NovelSum
import LeanVM.Guest.B1.Opening.QueriesCap
import LeanVM.Guest.B1.Opening.QueriesComplete1
import LeanVM.Guest.B1.Opening.QueriesComplete2
import LeanVM.Guest.B1.Opening.QueriesFlat
import LeanVM.Guest.B1.Opening.QueriesFlatC
import LeanVM.Guest.B1.Opening.QueriesHonest
import LeanVM.Guest.B1.Opening.QueriesLeaf
import LeanVM.Guest.B1.Opening.QueriesMain
import LeanVM.Guest.B1.Opening.QueriesMainW
import LeanVM.Guest.B1.Opening.QueriesPath
import LeanVM.Guest.B1.Opening.QueriesPlaced1
import LeanVM.Guest.B1.Opening.QueriesRow
import LeanVM.Guest.B1.Opening.QueriesSound
import LeanVM.Guest.B1.Opening.QueriesT
import LeanVM.Guest.B1.Opening.QueriesW
import LeanVM.Guest.B1.Opening.QueriesWalk
import LeanVM.Guest.B1.Opening.Residual
import LeanVM.Guest.B1.Opening.WalkDefs
import LeanVM.Guest.B1.Opening.WalkMatch
import LeanVM.Guest.B1.Opening.WalkPath
import LeanVM.Guest.B1.Opening.Witness
import LeanVM.Guest.B1.Sumcheck.MeaningP
import LeanVM.Guest.B1.Sumcheck.Run
import LeanVM.Guest.B1.Fs.TailRoundP
import LeanVM.Guest.B1.Fs.Templates
import LeanVM.Guest.B1.Whir.Bases
import LeanVM.Guest.B1.Whir.CAtoms
import LeanVM.Guest.B1.Whir.CBlk
import LeanVM.Guest.B1.Whir.CCaps
import LeanVM.Guest.B1.Whir.CDisp
import LeanVM.Guest.B1.Whir.CFinB
import LeanVM.Guest.B1.Whir.CFinEval
import LeanVM.Guest.B1.Whir.CFinO
import LeanVM.Guest.B1.Whir.CFinPt
import LeanVM.Guest.B1.Whir.CFinR
import LeanVM.Guest.B1.Whir.CFinRs
import LeanVM.Guest.B1.Whir.CHead
import LeanVM.Guest.B1.Whir.CInv
import LeanVM.Guest.B1.Whir.CInvLadder
import LeanVM.Guest.B1.Whir.CInvLast
import LeanVM.Guest.B1.Whir.CInvLevel
import LeanVM.Guest.B1.Whir.CInvRound
import LeanVM.Guest.B1.Whir.CLevel
import LeanVM.Guest.B1.Whir.CLoop
import LeanVM.Guest.B1.Whir.CLvB
import LeanVM.Guest.B1.Whir.CLvCommit
import LeanVM.Guest.B1.Whir.CLvLam
import LeanVM.Guest.B1.Whir.CLvMsg
import LeanVM.Guest.B1.Whir.CRounds
import LeanVM.Guest.B1.Whir.CRoundsA
import LeanVM.Guest.B1.Whir.CSqLoop
import LeanVM.Guest.B1.Whir.CTail
import LeanVM.Guest.B1.Whir.CVal
import LeanVM.Guest.B1.Whir.Commit
import LeanVM.Guest.B1.Whir.CompleteIface
import LeanVM.Guest.B1.Whir.Config
import LeanVM.Guest.B1.Whir.FinishSplit
import LeanVM.Guest.B1.Whir.Flat
import LeanVM.Guest.B1.Whir.Flatness
import LeanVM.Guest.B1.Whir.Folds
import LeanVM.Guest.B1.Whir.HelperT
import LeanVM.Guest.B1.Whir.HsScale
import LeanVM.Guest.B1.Whir.HsScaleCert
import LeanVM.Guest.B1.Whir.Interface
import LeanVM.Guest.B1.Whir.InterfaceW
import LeanVM.Guest.B1.Whir.Lam
import LeanVM.Guest.B1.Whir.LastRun
import LeanVM.Guest.B1.Whir.LevelB
import LeanVM.Guest.B1.Whir.LevelRun
import LeanVM.Guest.B1.Whir.LevelSpec
import LeanVM.Guest.B1.Whir.MatPlan
import LeanVM.Guest.B1.Whir.NameNums
import LeanVM.Guest.B1.Whir.Names
import LeanVM.Guest.B1.Whir.OodW
import LeanVM.Guest.B1.Whir.OqKey
import LeanVM.Guest.B1.Whir.Point
import LeanVM.Guest.B1.Whir.QOpen
import LeanVM.Guest.B1.Whir.RateCfg
import LeanVM.Guest.B1.Whir.RateFree
import LeanVM.Guest.B1.Whir.ResQuery
import LeanVM.Guest.B1.Whir.Residuals
import LeanVM.Guest.B1.Whir.Run
import LeanVM.Guest.B1.Whir.Split
import LeanVM.Guest.B1.Whir.Squeezes
import LeanVM.Guest.B1.Whir.TableKeys
import LeanVM.Guest.B1.Whir.TableKeysLp
import LeanVM.Guest.B1.Whir.TableKeysLq
import LeanVM.Guest.B1.Whir.TableKeysLr
import LeanVM.Guest.B1.Whir.TableMem
import LeanVM.Guest.B1.Whir.TailRun
import LeanVM.Guest.B1.Whir.Template
import LeanVM.Guest.B1.Whir.Vanish
import LeanVM.Guest.B1.Whir.VanishCert
import LeanVM.Guest.B1.Whir.Witness

import LeanVM.Guest.B1.Opening.WalkBody0
import LeanVM.Guest.B1.Opening.WalkBody1
import LeanVM.Guest.B1.Opening.WalkBody2
import LeanVM.Guest.B1.Opening.QueriesBody0
import LeanVM.Guest.B1.Opening.QueriesBody1
import LeanVM.Guest.B1.Opening.QueriesBody2
import LeanVM.Guest.B1.Opening.QueriesBody3
import LeanVM.Guest.B1.Bits.QueryWindowsBody0
import LeanVM.Guest.B1.Bits.QueryWindowsBody1

import LeanVM.Guest.B1.Eq.EqTree
import LeanVM.Guest.B1.Eq.MeaningP
import LeanVM.Guest.B1.Tables.Base
import LeanVM.Guest.B1.Tables.Basic
import LeanVM.Guest.B1.Tables.CoordPadding
import LeanVM.Guest.B1.Tables.GroupCert
import LeanVM.Guest.B1.Tables.InterfaceP
import LeanVM.Guest.B1.Tables.RunF
import LeanVM.Guest.B1.Tables.Squares
import LeanVM.Guest.B1.Tables.VtC.Agree
import LeanVM.Guest.B1.Tables.VtC.BStack
import LeanVM.Guest.B1.Selectors.IndexMle
import LeanVM.Guest.B1.Selectors.InterfaceP
import LeanVM.Guest.B1.Selectors.LayoutBasic
import LeanVM.Guest.B1.Gkr.EvalC
import LeanVM.Guest.B1.Gkr.Fs
import LeanVM.Guest.B1.Gkr.InterfaceP
import LeanVM.Guest.B1.Gkr.Round
import LeanVM.Guest.B1.Gkr.Spec
import LeanVM.Guest.B1.Gkr.SpecInv
import LeanVM.Guest.B1.KeccakGkr.Algebra
import LeanVM.Guest.B1.KeccakGkr.EqFrame
import LeanVM.Guest.B1.KeccakGkr.EqTreeC
import LeanVM.Guest.B1.KeccakGkr.FoldMath
import LeanVM.Guest.B1.KeccakGkr.FsComplete
import LeanVM.Guest.B1.KeccakGkr.InterfaceP
import LeanVM.Guest.B1.KeccakGkr.KFormMath
import LeanVM.Guest.B1.KeccakGkr.LayerCBlock
import LeanVM.Guest.B1.KeccakGkr.LayerRmfe
import LeanVM.Guest.B1.KeccakGkr.LayerSpec
import LeanVM.Guest.B1.KeccakGkr.Lib
import LeanVM.Guest.B1.KeccakGkr.Mask
import LeanVM.Guest.B1.KeccakGkr.ShiftMath
import LeanVM.Guest.B1.KeccakGkr.VkSpec
import LeanVM.Guest.B1.Da.DualMath
import LeanVM.Guest.B1.Main.FramesP
import LeanVM.Guest.B1.Main.IterK
import LeanVM.Guest.B1.Main.Plan
import LeanVM.Guest.B1.Main.RelAtW
import LeanVM.Guest.B1.Terminal.Blocks
import LeanVM.Guest.B1.Terminal.Claims
import LeanVM.Guest.B1.Terminal.EqMath
import LeanVM.Guest.B1.Terminal.InterfaceP
import LeanVM.Guest.B1.Terminal.Layout
import LeanVM.Guest.B1.Terminal.Sum
import LeanVM.Guest.B1.Terminal.Template
import LeanVM.Guest.B1.Terminal.Weights
import LeanVM.Guest.B1.Placement.Common
import LeanVM.Guest.B1.Placement.CompleteBase
import LeanVM.Guest.B1.Placement.InterfaceP
import LeanVM.Guest.B1.Placement.Kappas
import LeanVM.Guest.B1.Ring.TargetMath
import LeanVM.Guest.B1.Fwd.Canon
import LeanVM.Guest.B1.Fwd.Eval
import LeanVM.Guest.B1.Fwd.FlatIte
import LeanVM.Guest.B1.Fwd.NotStored
import LeanVM.Guest.B1.VerifySub.NZRun
import LeanVM.Guest.B1.VerifySub.Sizes
import LeanVM.Guest.B1.Common.Atoms
import LeanVM.Guest.B1.Common.Basic
import LeanVM.Guest.B1.Common.Loops
import LeanVM.Guest.B1.Common.MemSize
import LeanVM.Guest.B1.Common.Phase
import LeanVM.Guest.B1.Common.Run
import LeanVM.Guest.B1.Common.Sponge
import LeanVM.Guest.B1.Bits.Templates

/-! **B1's per-function proofs read their own function's core module alone.** A proof stated for
every program that finds its function (`Finds`, `CoreFind.lean`), or a check of one function's
body, imports the core module holding that function (its pack, `Guest/Pack/P<k>/Core.lean`, or its
own, `Guest/Pack/<key>/Core*.lean`) and no other core IR: not the glue (`Data.Core`, `CoreData`,
`Data.Names`, `CoreNames`), not another pack (the names, `Data.NameStrings`, are allowed). So an
edit of one function rebuilds the proofs of its pack and the glue, not the others' proofs. This
module fails to build if a listed module's imports reach other core IR. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let idx : Std.HashMap Name Nat := (names.zipIdx.toList).foldl (fun m (n, i) => m.insert n i) {}
  let closure (m : Name) : NameSet := Id.run do
    let mut seen : NameSet := {}
    let mut todo := [m]
    while !todo.isEmpty do
      let x := todo.head!
      todo := todo.tail!
      for i in (idx.get? x).map (data[·]!.imports) |>.getD #[] do
        unless seen.contains i.module do
          seen := seen.insert i.module
          todo := i.module :: todo
    return seen
  -- each family's modules (by prefix, or numbered: `pre` followed by digits), the functions whose
  -- core modules they may read (`none`: generated data over core packs, any),
  -- and the family's glue modules, which state its proofs at `coreProgram`
  let W := `LeanVM.Guest.B1.Whir
  let Q := `LeanVM.Guest.B1.Bits
  -- single modules (not their numbered siblings), and the functions whose core modules each may read
  let single : List (Name × List Name) := [
    (`LeanVM.Guest.B1.Merkle.Cap, []),
    (`LeanVM.Guest.B1.Merkle.CapAllP, [`verify_merkle_cap__L2, `verify_merkle_cap__L3, `verify_merkle_cap__L4, `verify_merkle_cap__L5, `verify_merkle_cap__L6, `verify_merkle_cap__L7, `verify_merkle_cap__L8]),
    (`LeanVM.Guest.B1.Merkle.Climb, []),
    (`LeanVM.Guest.B1.Merkle.Meaning, []),
    (`LeanVM.Guest.B1.Opening.FoldAlg, []),
    (`LeanVM.Guest.B1.Opening.Interface, []),
    (`LeanVM.Guest.B1.Opening.Meaning, []),
    (`LeanVM.Guest.B1.Opening.NovelEval, []),
    (`LeanVM.Guest.B1.Opening.NovelSum, []),
    (`LeanVM.Guest.B1.Opening.QueriesCap, []),
    (`LeanVM.Guest.B1.Opening.QueriesComplete1, []),
    (`LeanVM.Guest.B1.Opening.QueriesComplete2, []),
    (`LeanVM.Guest.B1.Opening.QueriesFlat, []),
    (`LeanVM.Guest.B1.Opening.QueriesFlatC, []),
    (`LeanVM.Guest.B1.Opening.QueriesHonest, []),
    (`LeanVM.Guest.B1.Opening.QueriesLeaf, []),
    (`LeanVM.Guest.B1.Opening.QueriesMain, []),
    (`LeanVM.Guest.B1.Opening.QueriesMainW, []),
    (`LeanVM.Guest.B1.Opening.QueriesPath, []),
    (`LeanVM.Guest.B1.Opening.QueriesPlaced1, []),
    (`LeanVM.Guest.B1.Opening.QueriesRow, []),
    (`LeanVM.Guest.B1.Opening.QueriesSound, []),
    (`LeanVM.Guest.B1.Opening.QueriesT, []),
    (`LeanVM.Guest.B1.Opening.QueriesW, []),
    (`LeanVM.Guest.B1.Opening.QueriesWalk, []),
    (`LeanVM.Guest.B1.Opening.Residual, []),
    (`LeanVM.Guest.B1.Opening.WalkDefs, []),
    (`LeanVM.Guest.B1.Opening.WalkMatch, []),
    (`LeanVM.Guest.B1.Opening.WalkPath, []),
    (`LeanVM.Guest.B1.Opening.Witness, []),
    (`LeanVM.Guest.B1.Sumcheck.MeaningP, []),
    (`LeanVM.Guest.B1.Sumcheck.Run, []),
    (`LeanVM.Guest.B1.Fs.TailRoundP, [`opening_tail_round]),
    (`LeanVM.Guest.B1.Fs.Templates, []),
    (`LeanVM.Guest.B1.Whir.Bases, []),
    (`LeanVM.Guest.B1.Whir.CAtoms, [`opening_round]),
    (`LeanVM.Guest.B1.Whir.CBlk, []),
    (`LeanVM.Guest.B1.Whir.CCaps, []),
    (`LeanVM.Guest.B1.Whir.CDisp, [`opening_round]),
    (`LeanVM.Guest.B1.Whir.CFinB, []),
    (`LeanVM.Guest.B1.Whir.CFinEval, []),
    (`LeanVM.Guest.B1.Whir.CFinO, []),
    (`LeanVM.Guest.B1.Whir.CFinPt, []),
    (`LeanVM.Guest.B1.Whir.CFinR, []),
    (`LeanVM.Guest.B1.Whir.CFinRs, []),
    (`LeanVM.Guest.B1.Whir.CHead, []),
    (`LeanVM.Guest.B1.Whir.CInv, []),
    (`LeanVM.Guest.B1.Whir.CInvLadder, []),
    (`LeanVM.Guest.B1.Whir.CInvLast, [`opening_tail_round]),
    (`LeanVM.Guest.B1.Whir.CInvLevel, []),
    (`LeanVM.Guest.B1.Whir.CInvRound, []),
    (`LeanVM.Guest.B1.Whir.CLevel, [`opening_round]),
    (`LeanVM.Guest.B1.Whir.CLoop, []),
    (`LeanVM.Guest.B1.Whir.CLvB, [`opening_round]),
    (`LeanVM.Guest.B1.Whir.CLvCommit, [`opening_round]),
    (`LeanVM.Guest.B1.Whir.CLvLam, [`opening_round]),
    (`LeanVM.Guest.B1.Whir.CLvMsg, []),
    (`LeanVM.Guest.B1.Whir.CRounds, []),
    (`LeanVM.Guest.B1.Whir.CRoundsA, [`opening_round]),
    (`LeanVM.Guest.B1.Whir.CSqLoop, []),
    (`LeanVM.Guest.B1.Whir.CTail, [`opening_round, `opening_tail_round]),
    (`LeanVM.Guest.B1.Whir.CVal, []),
    (`LeanVM.Guest.B1.Whir.Commit, []),
    (`LeanVM.Guest.B1.Whir.CompleteIface, []),
    (`LeanVM.Guest.B1.Whir.Config, []),
    (`LeanVM.Guest.B1.Whir.FinishSplit, []),
    (`LeanVM.Guest.B1.Whir.Flat, []),
    (`LeanVM.Guest.B1.Whir.Flatness, []),
    (`LeanVM.Guest.B1.Whir.Folds, []),
    (`LeanVM.Guest.B1.Whir.HelperT, []),
    (`LeanVM.Guest.B1.Whir.HsScale, []),
    (`LeanVM.Guest.B1.Whir.HsScaleCert, []),
    (`LeanVM.Guest.B1.Whir.Interface, []),
    (`LeanVM.Guest.B1.Whir.InterfaceW, []),
    (`LeanVM.Guest.B1.Whir.Lam, []),
    (`LeanVM.Guest.B1.Whir.LastRun, [`opening_tail_round]),
    (`LeanVM.Guest.B1.Whir.LevelB, []),
    (`LeanVM.Guest.B1.Whir.LevelRun, []),
    (`LeanVM.Guest.B1.Whir.LevelSpec, []),
    (`LeanVM.Guest.B1.Whir.MatPlan, []),
    (`LeanVM.Guest.B1.Whir.NameNums, []),
    (`LeanVM.Guest.B1.Whir.Names, []),
    (`LeanVM.Guest.B1.Whir.OodW, []),
    (`LeanVM.Guest.B1.Whir.OqKey, []),
    (`LeanVM.Guest.B1.Whir.Point, []),
    (`LeanVM.Guest.B1.Whir.QOpen, []),
    (`LeanVM.Guest.B1.Whir.RateCfg, []),
    (`LeanVM.Guest.B1.Whir.RateFree, []),
    (`LeanVM.Guest.B1.Whir.ResQuery, []),
    (`LeanVM.Guest.B1.Whir.Residuals, []),
    (`LeanVM.Guest.B1.Whir.Run, []),
    (`LeanVM.Guest.B1.Whir.Split, []),
    (`LeanVM.Guest.B1.Whir.Squeezes, []),
    (`LeanVM.Guest.B1.Whir.TableKeys, []),
    (`LeanVM.Guest.B1.Whir.TableKeysLp, []),
    (`LeanVM.Guest.B1.Whir.TableKeysLq, []),
    (`LeanVM.Guest.B1.Whir.TableKeysLr, []),
    (`LeanVM.Guest.B1.Whir.TableMem, []),
    (`LeanVM.Guest.B1.Whir.TailRun, [`opening_tail_round]),
    (`LeanVM.Guest.B1.Whir.Template, []),
    (`LeanVM.Guest.B1.Whir.Vanish, []),
    (`LeanVM.Guest.B1.Whir.VanishCert, []),
    (`LeanVM.Guest.B1.Whir.Witness, []),
    (`LeanVM.Guest.B1.Eq.EqTree, []),
    (`LeanVM.Guest.B1.Eq.MeaningP, []),
    (`LeanVM.Guest.B1.Tables.Base, []),
    (`LeanVM.Guest.B1.Tables.Basic, []),
    (`LeanVM.Guest.B1.Tables.CoordPadding, []),
    (`LeanVM.Guest.B1.Tables.GroupCert, []),
    (`LeanVM.Guest.B1.Tables.InterfaceP, []),
    (`LeanVM.Guest.B1.Tables.RunF, []),
    (`LeanVM.Guest.B1.Tables.Squares, []),
    (`LeanVM.Guest.B1.Tables.VtC.Agree, []),
    (`LeanVM.Guest.B1.Tables.VtC.BStack, []),
    (`LeanVM.Guest.B1.Selectors.IndexMle, []),
    (`LeanVM.Guest.B1.Selectors.InterfaceP, []),
    (`LeanVM.Guest.B1.Selectors.LayoutBasic, []),
    (`LeanVM.Guest.B1.Gkr.EvalC, []),
    (`LeanVM.Guest.B1.Gkr.Fs, []),
    (`LeanVM.Guest.B1.Gkr.InterfaceP, []),
    (`LeanVM.Guest.B1.Gkr.Round, []),
    (`LeanVM.Guest.B1.Gkr.Spec, []),
    (`LeanVM.Guest.B1.Gkr.SpecInv, []),
    (`LeanVM.Guest.B1.KeccakGkr.Algebra, []),
    (`LeanVM.Guest.B1.KeccakGkr.EqFrame, []),
    (`LeanVM.Guest.B1.KeccakGkr.EqTreeC, []),
    (`LeanVM.Guest.B1.KeccakGkr.FoldMath, []),
    (`LeanVM.Guest.B1.KeccakGkr.FsComplete, []),
    (`LeanVM.Guest.B1.KeccakGkr.InterfaceP, []),
    (`LeanVM.Guest.B1.KeccakGkr.KFormMath, []),
    (`LeanVM.Guest.B1.KeccakGkr.LayerCBlock, []),
    (`LeanVM.Guest.B1.KeccakGkr.LayerRmfe, []),
    (`LeanVM.Guest.B1.KeccakGkr.LayerSpec, []),
    (`LeanVM.Guest.B1.KeccakGkr.Lib, []),
    (`LeanVM.Guest.B1.KeccakGkr.Mask, []),
    (`LeanVM.Guest.B1.KeccakGkr.ShiftMath, []),
    (`LeanVM.Guest.B1.KeccakGkr.VkSpec, []),
    (`LeanVM.Guest.B1.Da.DualMath, []),
    (`LeanVM.Guest.B1.Main.FramesP, []),
    (`LeanVM.Guest.B1.Main.IterK, []),
    (`LeanVM.Guest.B1.Main.Plan, []),
    (`LeanVM.Guest.B1.Main.RelAtW, []),
    (`LeanVM.Guest.B1.Terminal.Blocks, []),
    (`LeanVM.Guest.B1.Terminal.Claims, []),
    (`LeanVM.Guest.B1.Terminal.EqMath, []),
    (`LeanVM.Guest.B1.Terminal.InterfaceP, []),
    (`LeanVM.Guest.B1.Terminal.Layout, []),
    (`LeanVM.Guest.B1.Terminal.Sum, []),
    (`LeanVM.Guest.B1.Terminal.Template, []),
    (`LeanVM.Guest.B1.Terminal.Weights, []),
    (`LeanVM.Guest.B1.Placement.Common, []),
    (`LeanVM.Guest.B1.Placement.CompleteBase, []),
    (`LeanVM.Guest.B1.Placement.InterfaceP, []),
    (`LeanVM.Guest.B1.Placement.Kappas, []),
    (`LeanVM.Guest.B1.Ring.TargetMath, []),
    (`LeanVM.Guest.B1.Fwd.Canon, []),
    (`LeanVM.Guest.B1.Fwd.Eval, []),
    (`LeanVM.Guest.B1.Fwd.FlatIte, []),
    (`LeanVM.Guest.B1.Fwd.NotStored, []),
    (`LeanVM.Guest.B1.VerifySub.NZRun, []),
    (`LeanVM.Guest.B1.VerifySub.Sizes, []),
    (`LeanVM.Guest.B1.Common.Atoms, []),
    (`LeanVM.Guest.B1.Common.Basic, []),
    (`LeanVM.Guest.B1.Common.Loops, []),
    (`LeanVM.Guest.B1.Common.MemSize, []),
    (`LeanVM.Guest.B1.Common.Phase, []),
    (`LeanVM.Guest.B1.Common.Run, []),
    (`LeanVM.Guest.B1.Common.Sponge, []),
    (`LeanVM.Guest.B1.Bits.Templates, [])]
  let families : List (Name × Option (List Name) × List Name) := [
    (Q ++ `GPowerP, some [`g_power_of_word], []),
    (Q ++ `MeaningP, some [], []),
    (Q ++ `QueryWindowsT, some [], []), (Q ++ `QueryWindowsLib, some [], []),
    (Q ++ `QueryWindows, some [], []), (Q ++ `QueryWindowsHonest, some [], []),
    (Q ++ `QueryWindowsComplete, some [], []),
    (`LeanVM.Guest.B1.Fs.Message, some [], []),
    (`LeanVM.Guest.B1.Sig, some [`main_loop2, `sp_wots, `verify_sig_lean_sphincs],
      [`LeanVM.Guest.B1.Sig.Interface]),
    (W ++ `DataSpecP, some [], []), (W ++ `Data, none, []), (W ++ `HelperData, none, []),
    (`LeanVM.Guest.B1.Opening.WalkBody, none, []), (`LeanVM.Guest.B1.Opening.QueriesBody, none, []),
    (Q ++ `QueryWindowsBody, none, []),
    (W ++ `HelperTables, some [], []),
    (W ++ `Round, some [], []), (W ++ `RoundSound, some [`opening_round], []),
    (W ++ `RoundComplete, some [`opening_round], []),
    (W ++ `Loops, some [], []), (W ++ `SqLoop, some [], []), (W ++ `ResLoop, some [], []),
    (W ++ `LpSound, some [], []), (W ++ `LqSound, some [], []), (W ++ `LrSound, some [], [])] ++
    single.map fun (m, ks) ↦ (m, some ks, [])
  let numbered (pre m : Name) : Bool := !single.any (·.1 == pre) && match pre, m with
    | .str p s, .str q r => p == q && s.isPrefixOf r && r.length > s.length &&
        (r.toList.drop s.length).all Char.isDigit
    | _, _ => false
  let glue := [`LeanVM.Guest.Data.Core, `LeanVM.Guest.Data.Names, `LeanVM.Guest.CoreData,
    `LeanVM.Guest.CoreNames]
  -- a core module, and the one that holds function `k`
  let isCore (d : Name) : Bool := (`LeanVM.Guest.Pack).isPrefixOf d && match d with
    | .str _ s => s.startsWith "Core"
    | _ => false
  let home (k : Name) : Option Name :=
    (env.getModuleIdxFor? (`LeanVM.Guest.Fn ++ k ++ `core)).map (names[·.toNat]!)
  for (pre, keys, exempt) in families do
    for m in names do
      unless (pre.isPrefixOf m || numbered pre m) && !exempt.contains m do continue
      let bad := (closure m).toList.filter fun d ↦ glue.any (·.isPrefixOf d) ||
        (isCore d && !(keys.map fun ks ↦ ks.any fun k ↦
          (`LeanVM.Guest.Pack ++ k).isPrefixOf d || home k == some d).getD true)
      unless bad.isEmpty do
        throwError m!"{m} imports {bad}: a per-function proof reads its own functions' core modules \
          only (see `LeanVM/Guest/B1/FnFirewall.lean`)"
