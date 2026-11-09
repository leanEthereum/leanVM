import LeanVM.Cost.Decoder.Frames

/-!
# Tests: the signature and proof readers off arrays, against the readers they restate

The compiled readers off arrays (`xmssSigOfNC`, `sphincsSigOfNC`, `vsPiOfNC`, the tables
`readerTabs` passed as a value) give the restated readers' values (`xmssSigOfN`, `sphincsSigOfN`,
`vsPiOfN`) on a valuation whose cells hold powers of `g` (every frame that valuation), and cost
less than those readers compiled as they were (`…OldC`: the tables literals named at each use, consecutive cells by
`g^k`, the loop's arguments and each query's position recomputed). On these inputs (each value of
the valuation a `g^k` computed, so its reads dominate): leanXMSS `612868 → 199178`, leanSPHINCS
`470905 → 459392` (its four frames the one valuation; the old compiled `sphincsSigOfN` builds
`sp_wots`' tables at each call); the tables are built once per decoding at `16721` (`readerTabsC`).
The child proof's reader is checked for its value only, against `vsPiOfA whirTabs`, which
`vsPiOfA_tabs` proves is `vsPiOfN`: the restated `vsPiOfN` reads each position's bits off the
windows by `gLog7`, a search of `128` powers of `g` per bit, too slow to run here.
-/

namespace LeanVMTests.Cost.DecoderReaders

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Fast
open LeanVM.Protocol.Verifier

/-- A compiled function's value and price on `vs`, in the program of the bodies `deps`. -/
def runOn (deps : List (ℕ × Term)) (i : ℕ) (vs : List MachineValue) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody (MachineProgram.ofList deps) 100000 i vs

/-- A valuation whose value `v` is `g^(v mod 61)`. -/
def powSigma (v : V) : E := ofK (LeanVM.Parameters.addressOfIndex (v.idx % 61))
cost_compile powSigmaC := powSigma

/-- A memory of `0`/`1` words, read at a constant price: `1` where the address's lane is a
multiple of `3`. -/
def bitReader (a : K) : Option E := some (if a.lane.toNat % 3 = 0 then 1 else 0)
cost_compile bitReaderC := bitReader

/-- Every frame the valuation `powSigma`. -/
def powFrames (_ : ℕ) (_ _ : List E) : Val := powSigma
cost_compile powFramesC := powFrames

/-- A cursor's length. -/
def cursor5 (_ _ : E) : ℕ := 5
cost_compile cursor5C := cursor5

-- the readers as they were compiled
cost_compile xmssOldC := xmssSigOfN
set_option maxRecDepth 100000 in
cost_compile sphincsOldC := sphincsSigOfN

def sigmaV : MachineValue := .closure powSigmaC.costIdx []
def rdV : MachineValue := .closure bitReaderC.costIdx []
def vnV : MachineValue := .closure powFramesC.costIdx []
def clV : MachineValue := .closure cursor5C.costIdx []

def xmssNew := runOn (xmssSigOfNC.costDeps ++ powSigmaC.costDeps) xmssSigOfNC.costIdx
  [encodeValue xmssTabs, sigmaV]
def xmssOld := runOn (xmssOldC.costDeps ++ powSigmaC.costDeps) xmssOldC.costIdx [sigmaV]

def sphincsNew := runOn (sphincsSigOfNC.costDeps ++ powSigmaC.costDeps) sphincsSigOfNC.costIdx
  [encodeValue spTabs, sigmaV, sigmaV, sigmaV, sigmaV]
def sphincsOld := runOn (sphincsOldC.costDeps ++ powSigmaC.costDeps ++ powFramesC.costDeps)
  sphincsOldC.costIdx [sigmaV, vnV]

def vsDeps := powSigmaC.costDeps ++ bitReaderC.costDeps ++ powFramesC.costDeps ++ cursor5C.costDeps
def vsNew := runOn (vsPiOfNC.costDeps ++ vsDeps) vsPiOfNC.costIdx
  [encodeValue whirTabs, rdV, sigmaV, vnV, clV]

#guard (xmssNew.map (·.1)) == some (encodeValue (xmssSigOfN powSigma))
#guard (xmssOld.map (·.1)) == some (encodeValue (xmssSigOfN powSigma))
#guard (sphincsNew.map (·.1)) == some (encodeValue (sphincsSigOfN powSigma powFrames))
#guard (sphincsOld.map (·.1)) == some (encodeValue (sphincsSigOfN powSigma powFrames))
#guard (vsNew.map (·.1)) == some (encodeValue (vsPiOfA whirTabs bitReader powSigma powFrames cursor5))
example : vsPiOfA whirTabs bitReader powSigma powFrames cursor5 =
    vsPiOfN bitReader powSigma powFrames cursor5 :=
  vsPiOfA_tabs _ _ _ _

/-- The second run is cheaper. -/
def cheaper : Option (MachineValue × ℕ) → Option (MachineValue × ℕ) → Bool
  | some (_, a), some (_, b) => decide (b < a)
  | _, _ => false

#guard cheaper xmssOld xmssNew
#guard cheaper sphincsOld sphincsNew

end LeanVMTests.Cost.DecoderReaders
