import SphincsSecurity
import Lean

/-!
Component dependency audit. `lake env lean scripts/Taint.lean` writes `taint.txt`, one line per local declaration with its module, the component-specific definitions of `Statement.lean` it references directly and the ones it reaches transitively, as bit sets: 1 the one-time signature, 2 the few-time signature, 4 the hypertree. A module whose transitive set never contains 1 is untouched by a change of the one-time signature.
-/

open Lean

namespace TaintAudit

def otsSeeds : Array Name := #[``SphincsSecurity.winternitzBits, ``SphincsSecurity.chainLength, ``SphincsSecurity.numChains,
  ``SphincsSecurity.targetSum, ``SphincsSecurity.Digit, ``SphincsSecurity.ChainStep, ``SphincsSecurity.Encoding,
  ``SphincsSecurity.TargetSum.sum, ``SphincsSecurity.TargetSum.Valid, ``SphincsSecurity.TargetSum.digitsPerHalf,
  ``SphincsSecurity.TargetSum.digitOffset, ``SphincsSecurity.TargetSum.digestEncoding, ``SphincsSecurity.TargetSum.decodeDigest,
  ``SphincsSecurity.encodingAttemptLimit, ``SphincsSecurity.HashDomain.chain, ``SphincsSecurity.HashDomain.encoding,
  ``SphincsSecurity.Concrete.chainWalk, ``SphincsSecurity.Concrete.recoverChain, ``SphincsSecurity.Concrete.oneTimePublicKey,
  ``SphincsSecurity.Concrete.encode, ``SphincsSecurity.Concrete.otsSignFrom, ``SphincsSecurity.Concrete.otsSign,
  ``SphincsSecurity.Concrete.otsLeaf, ``SphincsSecurity.Concrete.leafPayload, ``SphincsSecurity.Concrete.leafHash]

def ftsSeeds : Array Name := #[``SphincsSecurity.ftsTreeHeight, ``SphincsSecurity.ftsTrees, ``SphincsSecurity.FtsTree,
  ``SphincsSecurity.IndexGroup, ``SphincsSecurity.FtsLeaf, ``SphincsSecurity.digestAttemptLimit, ``SphincsSecurity.HashDomain.ftsLeaf,
  ``SphincsSecurity.HashDomain.ftsNode, ``SphincsSecurity.HashDomain.ftsRoots, ``SphincsSecurity.HashDomain.message,
  ``SphincsSecurity.messageDigestBits, ``SphincsSecurity.MessageDigest, ``SphincsSecurity.truncateMessageDigest,
  ``SphincsSecurity.Concrete.ftsLeafOfNat, ``SphincsSecurity.Concrete.ftsIndexOf, ``SphincsSecurity.Concrete.lastIndexGroup,
  ``SphincsSecurity.Concrete.ftsLeafHash, ``SphincsSecurity.Concrete.ftsNode, ``SphincsSecurity.Concrete.ftsRootsPayload,
  ``SphincsSecurity.Concrete.ftsKey, ``SphincsSecurity.Concrete.ftsOpen, ``SphincsSecurity.Concrete.ftsFold,
  ``SphincsSecurity.Concrete.ftsRecover, ``SphincsSecurity.Concrete.messageDigestPayload, ``SphincsSecurity.Concrete.messageDigest,
  ``SphincsSecurity.Concrete.digestIndex, ``SphincsSecurity.Concrete.digestLeaves, ``SphincsSecurity.Concrete.Admissible,
  ``SphincsSecurity.Concrete.signAttempt, ``SphincsSecurity.Concrete.signDigestLoop]

def treeSeeds : Array Name := #[``SphincsSecurity.numLayers, ``SphincsSecurity.totalHeight, ``SphincsSecurity.maxLayerHeight,
  ``SphincsSecurity.PathIndex, ``SphincsSecurity.layerHeight, ``SphincsSecurity.topLayer, ``SphincsSecurity.middleLayer,
  ``SphincsSecurity.bottomLayer, ``SphincsSecurity.heightAbove, ``SphincsSecurity.heightBelow, ``SphincsSecurity.HashDomain.leaf,
  ``SphincsSecurity.HashDomain.node, ``SphincsSecurity.Concrete.treeIndexAt, ``SphincsSecurity.Concrete.leafIndexAt,
  ``SphincsSecurity.Concrete.leafOfNat, ``SphincsSecurity.Concrete.nodePayload, ``SphincsSecurity.Concrete.treeNode,
  ``SphincsSecurity.Concrete.treeRoot, ``SphincsSecurity.Concrete.treePath, ``SphincsSecurity.Concrete.treeFold,
  ``SphincsSecurity.Concrete.signaturePath, ``SphincsSecurity.Concrete.verifyLayers, ``SphincsSecurity.Concrete.layerMessage,
  ``SphincsSecurity.Concrete.signLayer, ``SphincsSecurity.Concrete.layerOfPath, ``SphincsSecurity.Concrete.flattenPaths,
  ``SphincsSecurity.Concrete.rootTree]

def tagOf (n : Name) : Nat :=
  (if otsSeeds.contains n then 1 else 0) + (if ftsSeeds.contains n then 2 else 0) + (if treeSeeds.contains n then 4 else 0)

def isLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some j => (env.header.moduleNames[j.toNat]!).toString.startsWith "SphincsSecurity"
  | none => false

def usedOf (ci : ConstantInfo) : Array Name :=
  let a := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some v => a ++ v.getUsedConstants
  | none => a

partial def trans (env : Environment) (memo : IO.Ref (Std.HashMap Name Nat)) (n : Name) : IO Nat := do
  if let some t := (← memo.get).get? n then return t
  -- provisional entry breaks cycles through auxiliary definitions
  memo.modify (·.insert n (tagOf n))
  let mut t := tagOf n
  if let some ci := env.find? n then
    for c in usedOf ci do
      if isLocal env c then
        t := t ||| (← trans env memo c)
      else
        t := t ||| tagOf c
  memo.modify (·.insert n t)
  return t

end TaintAudit

open TaintAudit Elab Command in
run_cmd do
  let env ← getEnv
  for n in otsSeeds ++ ftsSeeds ++ treeSeeds do
    if (env.find? n).isNone then logWarning m!"unknown seed {n}"
  let memo ← IO.mkRef ({} : Std.HashMap Name Nat)
  let mut out : String := ""
  for (n, ci) in env.constants.toList do
    if !isLocal env n then continue
    let some j := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[j.toNat]!
    let mut direct := 0
    for c in usedOf ci do direct := direct ||| tagOf c
    let t ← trans env memo n
    out := out ++ s!"{m}|{n}|{direct}|{t}\n"
  IO.FS.writeFile "taint.txt" out
  logInfo "done"
